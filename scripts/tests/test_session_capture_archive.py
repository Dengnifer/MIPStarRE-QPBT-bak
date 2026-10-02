"""Focused tests for lossless session-capture archival and reading."""

from __future__ import annotations

import gzip
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
ARCHIVER = ROOT / "local/bin/archive_session_captures.py"
DEFAULT_MANIFEST = Path("results/telemetry/session-capture-archive-manifest.jsonl")
sys.path.insert(0, str(ROOT / "local/bin"))
import telemetry


def git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


class SessionCaptureArchiveTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q", "-b", "main")
        (self.repo / "local").mkdir()
        captures = self.repo / "results/telemetry/sessions"
        captures.mkdir(parents=True)
        self.payloads = {
            "failed.jsonl": b'{"type":"error","message":"adverse evidence"}\n',
            "ok.jsonl": (
                b'{"type":"thread.started","thread_id":"fixture"}\n'
                b'{"type":"turn.completed","usage":{"input_tokens":7}}\n'
            ),
        }
        for name, data in self.payloads.items():
            (captures / name).write_bytes(data)
        git(self.repo, "add", ".")
        git(
            self.repo,
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "fixture",
        )
        self.source_commit = git(self.repo, "rev-parse", "HEAD")

    def run_archiver(
        self,
        command: str,
        *,
        manifest: Path = DEFAULT_MANIFEST,
        prior_manifests: tuple[Path, ...] = (),
    ) -> subprocess.CompletedProcess[str]:
        arguments = [
            sys.executable,
            str(ARCHIVER),
            "--repo-root",
            str(self.repo),
            "--manifest",
            str(manifest),
        ]
        for prior_manifest in prior_manifests:
            arguments.extend(("--prior-manifest", str(prior_manifest)))
        arguments.append(command)
        return subprocess.run(
            arguments,
            check=False,
            capture_output=True,
            text=True,
        )

    def commit(self, message: str) -> str:
        git(self.repo, "add", "-A")
        git(
            self.repo,
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            message,
        )
        return git(self.repo, "rev-parse", "HEAD")

    def test_create_is_deterministic_and_recovers_every_git_blob(self) -> None:
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        summary = json.loads(created.stdout)
        self.assertEqual(summary["files"], len(self.payloads))
        self.assertEqual(summary["source_commit"], self.source_commit)

        manifest = self.repo / DEFAULT_MANIFEST
        rows = [json.loads(line) for line in manifest.read_text().splitlines()]
        paths = [row["source_path"] for row in rows]
        self.assertEqual(paths, sorted(paths))
        for row in rows:
            source = Path(row["source_path"])
            archive = self.repo / row["archive_path"]
            expected = self.payloads[source.name]
            self.assertFalse((self.repo / source).exists())
            self.assertEqual(gzip.decompress(archive.read_bytes()), expected)
            blob = git(self.repo, "rev-parse", f"{self.source_commit}:{source.as_posix()}")
            self.assertEqual(row["source_blob"], blob)

        verified = self.run_archiver("verify")
        self.assertEqual(verified.returncode, 0, verified.stderr)
        self.assertEqual(json.loads(verified.stdout), summary)

    def test_two_successive_batches_require_and_verify_the_prior_manifest(self) -> None:
        first = self.run_archiver("create")
        self.assertEqual(first.returncode, 0, first.stderr)
        self.commit("archive first batch")

        later_payload = b'{"type":"turn.completed","batch":2}\n'
        later_source = self.repo / "results/telemetry/sessions/later.jsonl"
        later_source.write_bytes(later_payload)
        second_source_commit = self.commit("add second batch")
        later_manifest = Path("results/telemetry/session-capture-archives-later.jsonl")

        missing_prior = self.run_archiver("create", manifest=later_manifest)
        self.assertNotEqual(missing_prior.returncode, 0)
        self.assertIn("archive coverage mismatch across supplied manifests", missing_prior.stderr)
        self.assertTrue(later_source.is_file())
        self.assertFalse((self.repo / later_manifest).exists())
        self.assertFalse(later_source.with_name(later_source.name + ".gz").exists())

        created = self.run_archiver(
            "create",
            manifest=later_manifest,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertEqual(created.returncode, 0, created.stderr)
        summary = json.loads(created.stdout)
        self.assertEqual(summary["manifests"], 2)
        self.assertEqual(summary["files"], len(self.payloads) + 1)
        self.assertEqual(
            [batch["source_commit"] for batch in summary["batches"]],
            [self.source_commit, second_source_commit],
        )
        self.assertFalse(later_source.exists())
        later_archive = self.repo / f"{later_source.relative_to(self.repo)}.gz"
        self.assertEqual(gzip.decompress(later_archive.read_bytes()), later_payload)

        verified = self.run_archiver(
            "verify",
            manifest=later_manifest,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertEqual(verified.returncode, 0, verified.stderr)
        self.assertEqual(json.loads(verified.stdout), summary)

    def test_verify_rejects_archive_collision_across_manifests(self) -> None:
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        duplicate_manifest = Path("results/telemetry/session-capture-archive-copy.jsonl")
        (self.repo / duplicate_manifest).write_bytes((self.repo / DEFAULT_MANIFEST).read_bytes())

        verified = self.run_archiver(
            "verify",
            manifest=duplicate_manifest,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("archive path collision across supplied manifests", verified.stderr)

    def test_verify_rejects_unmanifested_archive_with_bounded_diagnostic(self) -> None:
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        captures = self.repo / "results/telemetry/sessions"
        for index in range(7):
            (captures / f"orphan-{index}.jsonl.gz").write_bytes(gzip.compress(b"orphan"))

        verified = self.run_archiver("verify")
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("extra=7 [", verified.stderr)
        self.assertIn("... (+2 more)", verified.stderr)
        self.assertNotIn("orphan-6.jsonl.gz", verified.stderr)

    def test_verify_rejects_truncated_archive(self) -> None:
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        archive = self.repo / "results/telemetry/sessions/ok.jsonl.gz"
        archive.write_bytes(archive.read_bytes()[:-4])
        verified = self.run_archiver("verify")
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("archive size mismatch", verified.stderr)

    def test_reader_matches_raw_compressed_and_registry_fallback(self) -> None:
        raw = self.repo / "capture.jsonl"
        raw.write_bytes(self.payloads["ok.jsonl"])
        compressed = raw.with_name(raw.name + ".gz")
        compressed.write_bytes(gzip.compress(raw.read_bytes(), compresslevel=9, mtime=0))
        self.assertEqual(telemetry.read_jsonl(raw), telemetry.read_jsonl(compressed))

        raw.unlink()
        self.assertEqual(telemetry.resolve_jsonl_path(raw), compressed)
        self.assertEqual(telemetry.read_jsonl(raw), telemetry.read_jsonl(compressed))
        self.assertEqual(telemetry.jsonl_stem(compressed), "capture")

    def test_reader_rejects_truncated_gzip_instead_of_returning_empty(self) -> None:
        path = self.repo / "damaged.jsonl.gz"
        path.write_bytes(gzip.compress(self.payloads["ok.jsonl"], mtime=0)[:-5])
        with self.assertRaisesRegex(ValueError, "damaged compressed JSONL"):
            telemetry.read_jsonl(path)

    def test_session_summarize_uses_archived_fallback(self) -> None:
        raw = self.repo / "archived.jsonl"
        archive = raw.with_name(raw.name + ".gz")
        archive.write_bytes(gzip.compress(self.payloads["ok.jsonl"], mtime=0))
        registry = self.repo / "registry.jsonl"
        process = subprocess.run(
            [
                sys.executable,
                str(ROOT / "local/bin/telemetry.py"),
                "--repo-root",
                str(self.repo),
                "session-summarize",
                str(raw),
                "--no-rollout-scan",
                "--append-to",
                str(registry),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(process.returncode, 0, process.stderr)
        row = json.loads(process.stdout)
        self.assertEqual(row["name"], "archived")
        self.assertEqual(Path(row["capture"]), Path("archived.jsonl.gz"))
        self.assertEqual(row["thread_id"], "fixture")

    def test_session_summarize_rejects_damaged_archive_without_registry_row(self) -> None:
        raw = self.repo / "damaged.jsonl"
        archive = raw.with_name(raw.name + ".gz")
        archive.write_bytes(gzip.compress(self.payloads["ok.jsonl"], mtime=0)[:-3])
        registry = self.repo / "registry.jsonl"
        process = subprocess.run(
            [
                sys.executable,
                str(ROOT / "local/bin/telemetry.py"),
                "--repo-root",
                str(self.repo),
                "session-summarize",
                str(raw),
                "--no-rollout-scan",
                "--append-to",
                str(registry),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(process.returncode, 4)
        self.assertIn("damaged compressed JSONL", process.stderr)
        self.assertFalse(registry.exists())


if __name__ == "__main__":
    unittest.main()
