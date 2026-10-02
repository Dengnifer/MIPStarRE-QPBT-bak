#!/usr/bin/env python3
"""Create and verify deterministic archives of historical session captures."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from collections.abc import Iterator
from pathlib import Path
from typing import Any


REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
CAPTURE_DIRECTORY = Path("results/telemetry/sessions")
MANIFEST_DEFAULT = Path("results/telemetry/session-capture-archive-manifest.jsonl")
SCHEMA_VERSION = 1
GZIP_LEVEL = 9
GZIP_MTIME = 0
MAX_COMPRESSION_WORKERS = 8
MANIFEST_FIELDS = {
    "archive_bytes",
    "archive_path",
    "archive_sha256",
    "format",
    "gzip_compresslevel",
    "gzip_mtime",
    "schema_version",
    "source_blob",
    "source_bytes",
    "source_commit",
    "source_mode",
    "source_path",
    "source_sha256",
}


class ArchiveError(Exception):
    """A recoverable archive validation failure."""


def git(repo: Path, *args: str) -> bytes:
    """Run Git without interpreting repository data as shell input."""
    process = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=False,
        capture_output=True,
    )
    if process.returncode != 0:
        diagnostic = process.stderr.decode("utf-8", errors="replace").strip()
        raise ArchiveError(f"git {' '.join(args)} failed: {diagnostic}")
    return process.stdout


def git_blobs(repo: Path, entries: list[dict[str, Any]]) -> Iterator[bytes]:
    """Yield blob bytes through one persistent ``git cat-file --batch`` process."""
    process = subprocess.Popen(
        ["git", "-C", str(repo), "cat-file", "--batch"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if process.stdin is None or process.stdout is None or process.stderr is None:
        process.kill()
        raise ArchiveError("could not open pipes for git cat-file --batch")
    try:
        for entry in entries:
            process.stdin.write((entry["source_blob"] + "\n").encode("ascii"))
            process.stdin.flush()
            header = process.stdout.readline().rstrip(b"\n").split()
            if (
                len(header) != 3
                or header[0].decode("ascii", errors="replace") != entry["source_blob"]
                or header[1] != b"blob"
            ):
                raise ArchiveError(
                    f"unexpected git cat-file response for {entry['source_path']}: "
                    f"{b' '.join(header).decode('ascii', errors='replace')}"
                )
            try:
                size = int(header[2])
            except ValueError as error:
                raise ArchiveError(
                    f"invalid Git blob size for {entry['source_path']}"
                ) from error
            raw = process.stdout.read(size)
            terminator = process.stdout.read(1)
            if len(raw) != size or terminator != b"\n":
                raise ArchiveError(f"truncated Git blob stream for {entry['source_path']}")
            yield raw
        process.stdin.close()
        returncode = process.wait()
        if returncode != 0:
            diagnostic = process.stderr.read().decode("utf-8", errors="replace").strip()
            raise ArchiveError(f"git cat-file --batch failed: {diagnostic}")
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def deterministic_gzip(data: bytes) -> bytes:
    """Return a filename-free gzip member with fixed time and compression level."""
    output = io.BytesIO()
    with gzip.GzipFile(
        filename="",
        mode="wb",
        compresslevel=GZIP_LEVEL,
        fileobj=output,
        mtime=GZIP_MTIME,
    ) as handle:
        handle.write(data)
    return output.getvalue()


def resolve_commit(repo: Path, ref: str) -> str:
    return git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}").decode().strip()


def source_entries(repo: Path, commit: str) -> list[dict[str, Any]]:
    """List raw capture blobs at ``commit`` in stable path order."""
    output = git(
        repo,
        "ls-tree",
        "-r",
        "-z",
        "-l",
        "--full-tree",
        commit,
        "--",
        str(CAPTURE_DIRECTORY),
    )
    entries = []
    for record in output.split(b"\0"):
        if not record:
            continue
        header, raw_path = record.split(b"\t", 1)
        mode, object_type, blob, size = header.decode("ascii").split()
        path = raw_path.decode("utf-8", errors="strict")
        if not path.endswith(".jsonl"):
            continue
        if object_type != "blob" or not mode.startswith("100"):
            raise ArchiveError(f"capture is not a regular Git blob: {path}")
        entries.append(
            {
                "source_blob": blob,
                "source_bytes": int(size),
                "source_mode": mode,
                "source_path": path,
            }
        )
    entries.sort(key=lambda entry: entry["source_path"])
    if not entries:
        raise ArchiveError(f"no raw captures found at {commit}")
    return entries


def manifest_bytes(rows: list[dict[str, Any]]) -> bytes:
    lines = [
        json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
        for row in rows
    ]
    return ("\n".join(lines) + "\n").encode("utf-8")


def write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("wb") as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())


def read_manifest(path: Path) -> list[dict[str, Any]]:
    try:
        data = path.read_bytes()
    except OSError as error:
        raise ArchiveError(f"cannot read manifest {path}: {error}") from error
    if not data.endswith(b"\n"):
        raise ArchiveError(f"manifest has no trailing newline: {path}")
    rows = []
    for line_number, raw in enumerate(data.splitlines(), 1):
        try:
            row = json.loads(raw)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise ArchiveError(f"malformed manifest line {line_number}: {error}") from error
        if not isinstance(row, dict):
            raise ArchiveError(f"manifest line {line_number} is not an object")
        if set(row) != MANIFEST_FIELDS:
            missing = sorted(MANIFEST_FIELDS - set(row))
            extra = sorted(set(row) - MANIFEST_FIELDS)
            raise ArchiveError(
                f"manifest line {line_number} has wrong fields; missing={missing}, extra={extra}"
            )
        rows.append(row)
    if not rows:
        raise ArchiveError("archive manifest is empty")
    return rows


def validate_row_shape(row: dict[str, Any], line_number: int) -> None:
    if row["schema_version"] != SCHEMA_VERSION:
        raise ArchiveError(f"manifest line {line_number} has unsupported schema version")
    if row["format"] != "gzip":
        raise ArchiveError(f"manifest line {line_number} has unsupported format")
    if row["gzip_compresslevel"] != GZIP_LEVEL or row["gzip_mtime"] != GZIP_MTIME:
        raise ArchiveError(f"manifest line {line_number} has noncanonical gzip parameters")
    if not isinstance(row["source_bytes"], int) or row["source_bytes"] < 0:
        raise ArchiveError(f"manifest line {line_number} has invalid source size")
    if not isinstance(row["archive_bytes"], int) or row["archive_bytes"] < 0:
        raise ArchiveError(f"manifest line {line_number} has invalid archive size")
    if row["archive_path"] != row["source_path"] + ".gz":
        raise ArchiveError(f"manifest line {line_number} has a noncanonical archive path")
    for key in ("source_sha256", "archive_sha256"):
        value = row[key]
        if not isinstance(value, str) or len(value) != 64:
            raise ArchiveError(f"manifest line {line_number} has invalid {key}")


def verify_manifest(repo: Path, manifest: Path) -> dict[str, Any]:
    """Verify every archive against its immutable source commit and blob."""
    rows = read_manifest(manifest)
    commits = {row["source_commit"] for row in rows}
    if len(commits) != 1:
        raise ArchiveError("manifest must bind one immutable source commit")
    source_commit = next(iter(commits))
    expected_entries = source_entries(repo, source_commit)
    expected = {entry["source_path"]: entry for entry in expected_entries}

    paths = [row["source_path"] for row in rows]
    if len(paths) != len(set(paths)):
        raise ArchiveError("manifest contains duplicate source paths")
    if paths != sorted(paths):
        raise ArchiveError("manifest source paths are not sorted")
    if set(paths) != set(expected):
        missing = sorted(set(expected) - set(paths))
        extra = sorted(set(paths) - set(expected))
        raise ArchiveError(f"manifest coverage mismatch; missing={missing}, extra={extra}")

    ordered_entries = []
    for line_number, row in enumerate(rows, 1):
        validate_row_shape(row, line_number)
        entry = expected[row["source_path"]]
        for key in ("source_blob", "source_bytes", "source_mode"):
            if row[key] != entry[key]:
                raise ArchiveError(
                    f"manifest line {line_number} disagrees with Git for {row['source_path']}"
                )
        ordered_entries.append(entry)

    total_source = 0
    total_archive = 0
    archive_paths = set()
    for row, raw in zip(rows, git_blobs(repo, ordered_entries)):
        if len(raw) != row["source_bytes"] or sha256(raw) != row["source_sha256"]:
            raise ArchiveError(f"source binding failed for {row['source_path']}")

        archive = repo / row["archive_path"]
        if archive.is_symlink() or not archive.is_file():
            raise ArchiveError(f"archive is missing or not a regular file: {row['archive_path']}")
        archived = archive.read_bytes()
        if len(archived) != row["archive_bytes"]:
            raise ArchiveError(f"archive size mismatch: {row['archive_path']}")
        if sha256(archived) != row["archive_sha256"]:
            raise ArchiveError(f"archive SHA-256 mismatch: {row['archive_path']}")
        try:
            decoded = gzip.decompress(archived)
        except (EOFError, OSError) as error:
            raise ArchiveError(f"damaged gzip archive {row['archive_path']}: {error}") from error
        if decoded != raw:
            raise ArchiveError(f"decoded bytes differ from Git blob: {row['archive_path']}")
        if deterministic_gzip(raw) != archived:
            raise ArchiveError(f"archive is not the canonical deterministic gzip: {archive}")
        if (repo / row["source_path"]).exists():
            raise ArchiveError(f"raw historical capture remains in the tree: {row['source_path']}")

        archive_paths.add(row["archive_path"])
        total_source += len(raw)
        total_archive += len(archived)

    actual_archives = {
        str(path.relative_to(repo))
        for path in (repo / CAPTURE_DIRECTORY).rglob("*.jsonl.gz")
        if path.is_file() and not path.is_symlink()
    }
    if actual_archives != archive_paths:
        missing = sorted(archive_paths - actual_archives)
        extra = sorted(actual_archives - archive_paths)
        raise ArchiveError(f"archive coverage mismatch; missing={missing}, extra={extra}")

    return {
        "archive_bytes": total_archive,
        "files": len(rows),
        "manifest_sha256": sha256(manifest.read_bytes()),
        "saved_bytes": total_source - total_archive,
        "source_bytes": total_source,
        "source_commit": source_commit,
    }


def stage_archive(
    repo: Path, staging: Path, indexed_entry: tuple[int, dict[str, Any]], source_commit: str
) -> dict[str, Any]:
    """Compress one checked-out source capture into its deterministic staging path."""
    index, entry = indexed_entry
    source = repo / entry["source_path"]
    if source.is_symlink() or not source.is_file():
        raise ArchiveError(f"source capture is missing or not a regular file: {source}")
    raw = source.read_bytes()
    if len(raw) != entry["source_bytes"]:
        raise ArchiveError(f"source size changed for {entry['source_path']}")
    archived = deterministic_gzip(raw)
    write_bytes(staging / f"{index:06d}.jsonl.gz", archived)
    return {
        "archive_bytes": len(archived),
        "archive_path": entry["source_path"] + ".gz",
        "archive_sha256": sha256(archived),
        "format": "gzip",
        "gzip_compresslevel": GZIP_LEVEL,
        "gzip_mtime": GZIP_MTIME,
        "schema_version": SCHEMA_VERSION,
        "source_blob": entry["source_blob"],
        "source_bytes": len(raw),
        "source_commit": source_commit,
        "source_mode": entry["source_mode"],
        "source_path": entry["source_path"],
        "source_sha256": sha256(raw),
    }


def create_archives(repo: Path, source_ref: str, manifest: Path) -> dict[str, Any]:
    source_commit = resolve_commit(repo, source_ref)
    if resolve_commit(repo, "HEAD") != source_commit:
        raise ArchiveError("archive creation requires --source-ref to equal HEAD")
    if manifest.exists():
        raise ArchiveError(f"manifest already exists: {manifest}")
    if subprocess.run(
        ["git", "-C", str(repo), "diff", "--quiet", source_commit, "--", str(CAPTURE_DIRECTORY)],
        check=False,
    ).returncode != 0:
        raise ArchiveError("tracked session captures differ from the source commit")

    entries = source_entries(repo, source_commit)
    final_archives = [repo / (entry["source_path"] + ".gz") for entry in entries]
    existing = [path for path in final_archives if path.exists() or path.is_symlink()]
    if existing:
        raise ArchiveError(f"archive destination already exists: {existing[0]}")

    staging_parent = repo / manifest.parent
    staging_parent.mkdir(parents=True, exist_ok=True)
    rows = []
    with tempfile.TemporaryDirectory(prefix=".session-archive-", dir=staging_parent) as directory:
        staging = Path(directory)
        workers = min(MAX_COMPRESSION_WORKERS, len(entries), os.cpu_count() or 1)
        with ThreadPoolExecutor(max_workers=workers) as executor:
            rows.extend(
                executor.map(
                    lambda item: stage_archive(repo, staging, item, source_commit),
                    enumerate(entries),
                )
            )

        staged_manifest = staging / "manifest.jsonl"
        write_bytes(staged_manifest, manifest_bytes(rows))
        for index, path in enumerate(final_archives):
            path.parent.mkdir(parents=True, exist_ok=True)
            os.replace(staging / f"{index:06d}.jsonl.gz", path)
        manifest.parent.mkdir(parents=True, exist_ok=True)
        os.replace(staged_manifest, manifest)

    for entry in entries:
        source = repo / entry["source_path"]
        if source.is_symlink() or not source.is_file():
            raise ArchiveError(f"source capture disappeared before archival: {source}")
        source.unlink()

    return verify_manifest(repo, manifest)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Create or verify deterministic historical session-capture archives."
    )
    result.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT_DEFAULT,
        help="repository root (default: inferred from this script)",
    )
    result.add_argument(
        "--manifest",
        type=Path,
        default=MANIFEST_DEFAULT,
        help=f"manifest path relative to the repository (default: {MANIFEST_DEFAULT})",
    )
    commands = result.add_subparsers(dest="command", required=True)
    create = commands.add_parser("create", help="archive every tracked historical capture")
    create.add_argument("--source-ref", default="HEAD", help="immutable preimage ref")
    commands.add_parser("verify", help="verify manifest coverage and exact recovery")
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    repo = args.repo_root.resolve()
    manifest = args.manifest
    if not manifest.is_absolute():
        manifest = repo / manifest
    try:
        if args.command == "create":
            summary = create_archives(repo, args.source_ref, manifest)
        else:
            summary = verify_manifest(repo, manifest)
    except (ArchiveError, OSError, subprocess.SubprocessError) as error:
        print(f"archive_session_captures.py: error: {error}", file=sys.stderr)
        return 1
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
