"""Focused tests for lossless session-capture archival and reading."""

from __future__ import annotations

import gzip
import hashlib
import json
import lzma
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
ARCHIVER = ROOT / "local/bin/archive_session_captures.py"
DEFAULT_MANIFEST = Path("results/telemetry/session-capture-archive-manifest.jsonl")
NATIVE_MANIFEST = Path("results/telemetry/native-evidence-archives-issue777.jsonl")
NATIVE_SCOPE = "issue-777-retired-native-evidence"
NATIVE_PATHS = (
    Path("results/telemetry/native-reviews/pr432-5c62-01a0a695/reports.jsonl"),
    Path("results/telemetry/native-reviews/pr460-terminal-01a0aebe/evidence.jsonl"),
    Path("results/telemetry/native-audits/pr453-integration-01a0a4e0/evidence.jsonl"),
    Path(
        "results/telemetry/native-audits/"
        "pr460-current-disposition-01a0aea6/evidence.jsonl"
    ),
)
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
        self.native_payloads = {
            path: f'{{"kind":"native","path":"{path}"}}\n'.encode()
            for path in NATIVE_PATHS
        }
        for path, data in self.native_payloads.items():
            source = self.repo / path
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes(data)
        self.unselected_native = Path(
            "results/telemetry/native-audits/"
            "pr453-integration-01a0a4e0/admission.jsonl"
        )
        self.unselected_payload = b'{"kind":"admission","preserve":true}\n'
        (self.repo / self.unselected_native).write_bytes(self.unselected_payload)
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
        scope: str | None = None,
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
        if scope is not None:
            arguments.extend(("--scope", scope))
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

    def ensure_repack_population(self, total: int = 22) -> None:
        """Add enough distinct session captures for the fixed 20-file repack."""
        captures = self.repo / "results/telemetry/sessions"
        for index in range(len(self.payloads), total):
            name = f"bulk-{index:02d}.jsonl"
            payload = (
                json.dumps(
                    {
                        "index": index,
                        "payload": (f"value-{index}-" * (index + 10)),
                        "type": "fixture",
                    },
                    sort_keys=True,
                )
                + "\n"
            ).encode()
            self.payloads[name] = payload
            (captures / name).write_bytes(payload)
        self.source_commit = self.commit("add bounded repack fixtures")

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
        for path, expected in self.native_payloads.items():
            self.assertEqual((self.repo / path).read_bytes(), expected)
            self.assertFalse((self.repo / f"{path}.gz").exists())
        self.assertEqual(
            (self.repo / self.unselected_native).read_bytes(),
            self.unselected_payload,
        )

        verified = self.run_archiver("verify")
        self.assertEqual(verified.returncode, 0, verified.stderr)
        self.assertEqual(json.loads(verified.stdout), summary)

    def test_explicit_native_scope_coexists_with_legacy_batch(self) -> None:
        first = self.run_archiver("create")
        self.assertEqual(first.returncode, 0, first.stderr)
        legacy_manifest = self.repo / DEFAULT_MANIFEST
        legacy_manifest_bytes = legacy_manifest.read_bytes()
        native_source_commit = self.commit("archive session fixtures")

        created = self.run_archiver(
            "create",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
            scope=NATIVE_SCOPE,
        )
        self.assertEqual(created.returncode, 0, created.stderr)
        summary = json.loads(created.stdout)
        self.assertEqual(summary["manifests"], 2)
        self.assertEqual(summary["files"], len(self.payloads) + len(NATIVE_PATHS))
        self.assertEqual(legacy_manifest.read_bytes(), legacy_manifest_bytes)

        rows = [
            json.loads(line)
            for line in (self.repo / NATIVE_MANIFEST).read_text().splitlines()
        ]
        self.assertEqual([row["source_path"] for row in rows], sorted(map(str, NATIVE_PATHS)))
        for row in rows:
            self.assertEqual(row["schema_version"], 2)
            self.assertEqual(row["source_scope"], NATIVE_SCOPE)
            self.assertEqual(row["source_commit"], native_source_commit)
            source = Path(row["source_path"])
            archive = self.repo / row["archive_path"]
            self.assertFalse((self.repo / source).exists())
            self.assertEqual(gzip.decompress(archive.read_bytes()), self.native_payloads[source])
            self.assertEqual(
                telemetry.read_jsonl(self.repo / source),
                telemetry.read_jsonl(archive),
            )

        self.assertEqual(
            (self.repo / self.unselected_native).read_bytes(),
            self.unselected_payload,
        )
        self.assertFalse((self.repo / f"{self.unselected_native}.gz").exists())

        verified = self.run_archiver(
            "verify",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertEqual(verified.returncode, 0, verified.stderr)
        self.assertEqual(json.loads(verified.stdout), summary)

    def test_native_scope_rejects_manifest_omitting_selected_file(self) -> None:
        first = self.run_archiver("create")
        self.assertEqual(first.returncode, 0, first.stderr)
        self.commit("archive session fixtures")
        created = self.run_archiver(
            "create",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
            scope=NATIVE_SCOPE,
        )
        self.assertEqual(created.returncode, 0, created.stderr)

        manifest = self.repo / NATIVE_MANIFEST
        lines = manifest.read_bytes().splitlines(keepends=True)
        manifest.write_bytes(b"".join(lines[:-1]))
        verified = self.run_archiver(
            "verify",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("manifest coverage mismatch", verified.stderr)
        self.assertIn("missing=1 [", verified.stderr)

    def test_native_scope_rejects_unmanifested_native_archive(self) -> None:
        first = self.run_archiver("create")
        self.assertEqual(first.returncode, 0, first.stderr)
        self.commit("archive session fixtures")
        created = self.run_archiver(
            "create",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
            scope=NATIVE_SCOPE,
        )
        self.assertEqual(created.returncode, 0, created.stderr)

        orphan = self.repo / "results/telemetry/native-audits/orphan/evidence.jsonl.gz"
        orphan.parent.mkdir(parents=True)
        orphan.write_bytes(gzip.compress(b'{"orphan":true}\n'))
        verified = self.run_archiver(
            "verify",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("archive coverage mismatch across supplied manifests", verified.stderr)
        self.assertIn("extra=1 [results/telemetry/native-audits/orphan", verified.stderr)

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

    def test_verify_rejects_mixed_format_source_collision(self) -> None:
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        mixed_manifest = Path("results/telemetry/session-capture-archive-xz-copy.jsonl")
        rows = [
            json.loads(line)
            for line in (self.repo / DEFAULT_MANIFEST).read_text().splitlines()
        ]
        for row in rows:
            raw = self.payloads[Path(row["source_path"]).name]
            archived = lzma.compress(
                raw,
                format=lzma.FORMAT_XZ,
                check=lzma.CHECK_CRC64,
                preset=6,
            )
            del row["gzip_compresslevel"]
            del row["gzip_mtime"]
            row.update(
                {
                    "archive_bytes": len(archived),
                    "archive_path": row["source_path"] + ".xz",
                    "archive_sha256": hashlib.sha256(archived).hexdigest(),
                    "format": "xz",
                    "schema_version": 3,
                    "xz_check": "crc64",
                    "xz_preset": 6,
                }
            )
            (self.repo / row["archive_path"]).write_bytes(archived)
        (self.repo / mixed_manifest).write_text(
            "".join(
                json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
                for row in rows
            )
        )

        verified = self.run_archiver(
            "verify",
            manifest=mixed_manifest,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("source path collision across supplied manifests", verified.stderr)

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

    def test_reader_matches_raw_gzip_xz_and_registry_fallback(self) -> None:
        raw = self.repo / "capture.jsonl"
        raw.write_bytes(self.payloads["ok.jsonl"])
        self.assertEqual(telemetry.read_jsonl(raw)[0][0]["type"], "thread.started")

        compressed = raw.with_name(raw.name + ".gz")
        compressed.write_bytes(gzip.compress(raw.read_bytes(), compresslevel=9, mtime=0))
        expected = telemetry.read_jsonl(compressed)
        raw.unlink()
        self.assertEqual(telemetry.resolve_jsonl_path(raw), compressed)
        self.assertEqual(telemetry.read_jsonl(raw), expected)
        self.assertEqual(telemetry.jsonl_stem(compressed), "capture")

        compressed.unlink()
        xz = raw.with_name(raw.name + ".xz")
        xz.write_bytes(
            lzma.compress(
                self.payloads["ok.jsonl"],
                format=lzma.FORMAT_XZ,
                check=lzma.CHECK_CRC64,
                preset=6,
            )
        )
        self.assertEqual(telemetry.resolve_jsonl_path(raw), xz)
        self.assertEqual(telemetry.read_jsonl(raw), expected)
        self.assertEqual(telemetry.jsonl_stem(xz), "capture")

    def test_reader_rejects_truncated_gzip_instead_of_returning_empty(self) -> None:
        path = self.repo / "damaged.jsonl.gz"
        path.write_bytes(gzip.compress(self.payloads["ok.jsonl"], mtime=0)[:-5])
        with self.assertRaisesRegex(ValueError, "damaged compressed JSONL"):
            telemetry.read_jsonl(path)

    def test_reader_rejects_truncated_xz_and_duplicate_representations(self) -> None:
        raw = self.repo / "damaged.jsonl"
        xz = raw.with_name(raw.name + ".xz")
        encoded = lzma.compress(
            self.payloads["ok.jsonl"],
            format=lzma.FORMAT_XZ,
            check=lzma.CHECK_CRC64,
            preset=6,
        )
        xz.write_bytes(encoded[:-5])
        with self.assertRaisesRegex(ValueError, "damaged compressed JSONL"):
            telemetry.read_jsonl(raw)

        xz.write_bytes(encoded)
        gzip_path = raw.with_name(raw.name + ".gz")
        gzip_path.write_bytes(gzip.compress(self.payloads["ok.jsonl"], mtime=0))
        with self.assertRaisesRegex(ValueError, "multiple JSONL representations"):
            telemetry.resolve_jsonl_path(raw)

    def test_repack_xz_preserves_sources_and_legacy_rows(self) -> None:
        self.ensure_repack_population()
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        manifest = self.repo / DEFAULT_MANIFEST
        original_lines = manifest.read_bytes().splitlines(keepends=True)
        original_rows = [json.loads(line) for line in original_lines]
        original_by_path = {row["source_path"]: row for row in original_rows}
        original_line_by_path = {
            row["source_path"]: line for row, line in zip(original_rows, original_lines)
        }
        expected_selected = {
            row["source_path"]
            for row in sorted(
                original_rows,
                key=lambda row: (-row["archive_bytes"], row["archive_path"]),
            )[:20]
        }
        self.commit("archive repack fixtures")

        native_created = self.run_archiver(
            "create",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
            scope=NATIVE_SCOPE,
        )
        self.assertEqual(native_created.returncode, 0, native_created.stderr)
        native_manifest = self.repo / NATIVE_MANIFEST
        native_manifest_bytes = native_manifest.read_bytes()
        operation_commit = self.commit("archive native fixtures")

        repacked = self.run_archiver(
            "repack-xz",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertEqual(repacked.returncode, 0, repacked.stderr)
        summary = json.loads(repacked.stdout)
        self.assertEqual(summary["operation_commit"], operation_commit)
        self.assertEqual(summary["repacked_files"], 20)
        self.assertEqual(summary["xz_check"], "crc64")
        self.assertEqual(summary["xz_preset"], 6)
        self.assertEqual(summary["formats"]["xz"]["files"], 20)
        self.assertEqual(summary["formats"]["gzip"]["files"], 6)
        self.assertEqual(
            summary["recovered_bytes"],
            summary["repacked_gzip_bytes"] - summary["repacked_xz_bytes"],
        )
        self.assertEqual(native_manifest.read_bytes(), native_manifest_bytes)

        new_lines = manifest.read_bytes().splitlines(keepends=True)
        new_rows = [json.loads(line) for line in new_lines]
        self.assertEqual([row["source_path"] for row in new_rows], sorted(original_by_path))
        for row, line in zip(new_rows, new_lines):
            source_path = row["source_path"]
            original = original_by_path[source_path]
            for key in (
                "source_blob",
                "source_bytes",
                "source_commit",
                "source_mode",
                "source_path",
                "source_sha256",
            ):
                self.assertEqual(row[key], original[key])
            if source_path in expected_selected:
                self.assertEqual(row["schema_version"], 3)
                self.assertEqual(row["format"], "xz")
                self.assertEqual(row["xz_check"], "crc64")
                self.assertEqual(row["xz_preset"], 6)
                self.assertNotIn("gzip_compresslevel", row)
                old_archive = self.repo / original["archive_path"]
                new_archive = self.repo / row["archive_path"]
                self.assertFalse(old_archive.exists())
                self.assertEqual(
                    lzma.decompress(new_archive.read_bytes(), format=lzma.FORMAT_XZ),
                    self.payloads[Path(source_path).name],
                )
                self.assertEqual(
                    telemetry.read_jsonl(self.repo / source_path),
                    telemetry.read_jsonl(new_archive),
                )
            else:
                self.assertEqual(line, original_line_by_path[source_path])
                self.assertEqual(row["schema_version"], 1)
                self.assertEqual(row["format"], "gzip")

        verified = self.run_archiver(
            "verify",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertEqual(verified.returncode, 0, verified.stderr)
        verified_summary = json.loads(verified.stdout)
        self.assertEqual(verified_summary["formats"], summary["formats"])

        selected_row = next(row for row in new_rows if row["format"] == "xz")
        raw = self.payloads[Path(selected_row["source_path"]).name]
        duplicate = self.repo / (selected_row["source_path"] + ".gz")
        duplicate.write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
        collision = self.run_archiver(
            "verify",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertNotEqual(collision.returncode, 0)
        self.assertIn("archive coverage mismatch across supplied manifests", collision.stderr)
        duplicate.unlink()

        original_manifest = manifest.read_bytes()
        strict_rows = [json.loads(line) for line in original_manifest.splitlines()]
        xz_index = next(index for index, row in enumerate(strict_rows) if row["format"] == "xz")
        strict_rows[xz_index]["xz_preset"] = 5
        manifest.write_text(
            "".join(
                json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
                for row in strict_rows
            )
        )
        noncanonical = self.run_archiver(
            "verify",
            manifest=NATIVE_MANIFEST,
            prior_manifests=(DEFAULT_MANIFEST,),
        )
        self.assertNotEqual(noncanonical.returncode, 0)
        self.assertIn("noncanonical XZ parameters", noncanonical.stderr)
        manifest.write_bytes(original_manifest)

    def test_repack_verifies_existing_archives_before_mutation(self) -> None:
        self.ensure_repack_population()
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        manifest = self.repo / DEFAULT_MANIFEST
        manifest_bytes = manifest.read_bytes()
        first_row = json.loads(manifest_bytes.splitlines()[0])
        archive = self.repo / first_row["archive_path"]
        archive.write_bytes(archive.read_bytes() + b"tampered")
        self.commit("commit corrupt archive fixture")

        repacked = self.run_archiver("repack-xz")
        self.assertNotEqual(repacked.returncode, 0)
        self.assertIn("archive size mismatch", repacked.stderr)
        self.assertEqual(manifest.read_bytes(), manifest_bytes)
        self.assertEqual(list((self.repo / "results/telemetry/sessions").glob("*.xz")), [])

    def test_verify_rejects_unsupported_gzip_format_parameters_and_path(self) -> None:
        created = self.run_archiver("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        manifest = self.repo / DEFAULT_MANIFEST
        original = manifest.read_bytes()

        cases = (
            ("format", "zip", "unsupported format"),
            ("gzip_compresslevel", 8, "noncanonical gzip parameters"),
            ("archive_path", "wrong.jsonl.gz", "noncanonical archive path"),
        )
        for key, value, diagnostic in cases:
            with self.subTest(key=key):
                rows = [json.loads(line) for line in original.splitlines()]
                rows[0][key] = value
                manifest.write_text(
                    "".join(
                        json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
                        for row in rows
                    )
                )
                verified = self.run_archiver("verify")
                self.assertNotEqual(verified.returncode, 0)
                self.assertIn(diagnostic, verified.stderr)
                manifest.write_bytes(original)

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
