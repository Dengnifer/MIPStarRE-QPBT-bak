#!/usr/bin/env python3
"""Create, verify and repack deterministic archives of historical JSONL evidence."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import lzma
import os
import subprocess
import sys
import tempfile
import zlib
from concurrent.futures import ThreadPoolExecutor
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import Any


REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
CAPTURE_DIRECTORY = Path("results/telemetry/sessions")
MANIFEST_DEFAULT = Path("results/telemetry/session-capture-archive-manifest.jsonl")
SESSION_CAPTURE_SCOPE = "session-captures"
NATIVE_EVIDENCE_SCOPE = "issue-777-retired-native-evidence"
NATIVE_EVIDENCE_PATHS = (
    Path("results/telemetry/native-reviews/pr432-5c62-01a0a695/reports.jsonl"),
    Path("results/telemetry/native-reviews/pr460-terminal-01a0aebe/evidence.jsonl"),
    Path("results/telemetry/native-audits/pr453-integration-01a0a4e0/evidence.jsonl"),
    Path(
        "results/telemetry/native-audits/"
        "pr460-current-disposition-01a0aea6/evidence.jsonl"
    ),
)
ARCHIVE_DIRECTORIES = (
    CAPTURE_DIRECTORY,
    Path("results/telemetry/native-reviews"),
    Path("results/telemetry/native-audits"),
)
LEGACY_SCHEMA_VERSION = 1
SCOPED_SCHEMA_VERSION = 2
XZ_SCHEMA_VERSION = 3
GZIP_LEVEL = 9
GZIP_MTIME = 0
XZ_PRESET = 6
XZ_CHECK = "crc64"
XZ_REPACK_COUNT = 20
MAX_COMPRESSION_WORKERS = 8
MAX_XZ_WORKERS = 2
PATH_DIAGNOSTIC_LIMIT = 5
COMMON_MANIFEST_FIELDS = {
    "archive_bytes",
    "archive_path",
    "archive_sha256",
    "format",
    "schema_version",
    "source_blob",
    "source_bytes",
    "source_commit",
    "source_mode",
    "source_path",
    "source_sha256",
}
LEGACY_MANIFEST_FIELDS = COMMON_MANIFEST_FIELDS | {
    "gzip_compresslevel",
    "gzip_mtime",
}
SCOPED_MANIFEST_FIELDS = LEGACY_MANIFEST_FIELDS | {"source_scope"}
XZ_MANIFEST_FIELDS = COMMON_MANIFEST_FIELDS | {"xz_check", "xz_preset"}


class ArchiveError(Exception):
    """A recoverable archive validation failure."""


@dataclass(frozen=True)
class VerifiedManifest:
    """One independently verified archive batch and its covered paths."""

    path: Path
    rows: tuple[dict[str, Any], ...]
    summary: dict[str, Any]


@dataclass(frozen=True)
class StagedRepack:
    """One validated gzip-to-XZ replacement staged for publication."""

    batch_index: int
    row_index: int
    old_path: Path
    new_path: Path
    staged_path: Path
    backup_path: Path
    row: dict[str, Any]


@dataclass(frozen=True)
class StagedManifest:
    """One manifest update with its original bytes retained for rollback."""

    path: Path
    staged_path: Path
    backup_path: Path


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


def path_summary(paths: set[str]) -> str:
    """Render a bounded count-and-sample diagnostic for a path set."""
    ordered = sorted(paths)
    if not ordered:
        return "0"
    examples = ", ".join(ordered[:PATH_DIAGNOSTIC_LIMIT])
    remainder = len(ordered) - PATH_DIAGNOSTIC_LIMIT
    suffix = f", ... (+{remainder} more)" if remainder > 0 else ""
    return f"{len(ordered)} [{examples}{suffix}]"


def display_path(repo: Path, path: Path) -> str:
    """Prefer a repository-relative path in summaries and diagnostics."""
    try:
        return str(path.relative_to(repo))
    except ValueError:
        return str(path)


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


def deterministic_xz(data: bytes) -> bytes:
    """Return canonical XZ bytes using preset 6 and a CRC64 integrity check."""
    if not lzma.is_check_supported(lzma.CHECK_CRC64):
        raise ArchiveError("the local LZMA library does not support XZ CRC64")
    return lzma.compress(
        data,
        format=lzma.FORMAT_XZ,
        check=lzma.CHECK_CRC64,
        preset=XZ_PRESET,
    )


def resolve_commit(repo: Path, ref: str) -> str:
    return git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}").decode().strip()


def scope_pathspecs(scope: str) -> tuple[Path, ...]:
    """Return the fixed Git pathspecs for a supported archival scope."""
    if scope == SESSION_CAPTURE_SCOPE:
        return (CAPTURE_DIRECTORY,)
    if scope == NATIVE_EVIDENCE_SCOPE:
        return NATIVE_EVIDENCE_PATHS
    raise ArchiveError(f"unsupported archive source scope: {scope}")


def source_entries(repo: Path, commit: str, scope: str) -> list[dict[str, Any]]:
    """List raw evidence blobs in ``scope`` at ``commit`` in stable path order."""
    pathspecs = scope_pathspecs(scope)
    output = git(
        repo,
        "ls-tree",
        "-r",
        "-z",
        "-l",
        "--full-tree",
        commit,
        "--",
        *(str(path) for path in pathspecs),
    )
    entries = []
    for record in output.split(b"\0"):
        if not record:
            continue
        header, raw_path = record.split(b"\t", 1)
        mode, object_type, blob, size = header.decode("ascii").split()
        path = raw_path.decode("utf-8", errors="strict")
        if scope == SESSION_CAPTURE_SCOPE and not path.endswith(".jsonl"):
            continue
        if object_type != "blob" or not mode.startswith("100"):
            raise ArchiveError(f"archival source is not a regular Git blob: {path}")
        entries.append(
            {
                "source_blob": blob,
                "source_bytes": int(size),
                "source_mode": mode,
                "source_path": path,
            }
        )
    entries.sort(key=lambda entry: entry["source_path"])
    if scope == NATIVE_EVIDENCE_SCOPE:
        expected_paths = {str(path) for path in NATIVE_EVIDENCE_PATHS}
        actual_paths = {entry["source_path"] for entry in entries}
        if actual_paths != expected_paths:
            missing = expected_paths - actual_paths
            extra = actual_paths - expected_paths
            raise ArchiveError(
                f"source scope {scope} mismatch at {commit}; "
                f"missing={path_summary(missing)}, extra={path_summary(extra)}"
            )
    if not entries:
        raise ArchiveError(f"no raw evidence found in scope {scope} at {commit}")
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
            raise ArchiveError(
                f"malformed manifest {path} line {line_number}: {error}"
            ) from error
        if not isinstance(row, dict):
            raise ArchiveError(f"manifest {path} line {line_number} is not an object")
        rows.append(row)
    if not rows:
        raise ArchiveError(f"archive manifest is empty: {path}")
    return rows


def validate_row_shape(row: dict[str, Any], line_number: int) -> str:
    schema_version = row.get("schema_version")
    if schema_version == LEGACY_SCHEMA_VERSION:
        expected_fields = LEGACY_MANIFEST_FIELDS
        scope = SESSION_CAPTURE_SCOPE
        expected_format = "gzip"
    elif schema_version == SCOPED_SCHEMA_VERSION:
        expected_fields = SCOPED_MANIFEST_FIELDS
        scope = row.get("source_scope")
        expected_format = "gzip"
        if scope != NATIVE_EVIDENCE_SCOPE:
            raise ArchiveError(
                f"manifest line {line_number} has unsupported source scope: {scope}"
            )
    elif schema_version == XZ_SCHEMA_VERSION:
        expected_fields = XZ_MANIFEST_FIELDS
        scope = SESSION_CAPTURE_SCOPE
        expected_format = "xz"
    else:
        raise ArchiveError(f"manifest line {line_number} has unsupported schema version")
    if set(row) != expected_fields:
        missing = sorted(expected_fields - set(row))
        extra = sorted(set(row) - expected_fields)
        raise ArchiveError(
            f"manifest line {line_number} has wrong fields; "
            f"missing={missing}, extra={extra}"
        )
    if row["format"] != expected_format:
        raise ArchiveError(f"manifest line {line_number} has unsupported format")
    if expected_format == "gzip":
        if (
            row["gzip_compresslevel"] != GZIP_LEVEL
            or row["gzip_mtime"] != GZIP_MTIME
        ):
            raise ArchiveError(
                f"manifest line {line_number} has noncanonical gzip parameters"
            )
        archive_suffix = ".gz"
    else:
        if row["xz_preset"] != XZ_PRESET or row["xz_check"] != XZ_CHECK:
            raise ArchiveError(
                f"manifest line {line_number} has noncanonical XZ parameters"
            )
        archive_suffix = ".xz"
    if not isinstance(row["source_bytes"], int) or row["source_bytes"] < 0:
        raise ArchiveError(f"manifest line {line_number} has invalid source size")
    if not isinstance(row["archive_bytes"], int) or row["archive_bytes"] < 0:
        raise ArchiveError(f"manifest line {line_number} has invalid archive size")
    for key in ("source_blob", "source_commit", "source_mode", "source_path", "archive_path"):
        if not isinstance(row[key], str) or not row[key]:
            raise ArchiveError(f"manifest line {line_number} has invalid {key}")
    if row["archive_path"] != row["source_path"] + archive_suffix:
        raise ArchiveError(f"manifest line {line_number} has a noncanonical archive path")
    for key in ("source_sha256", "archive_sha256"):
        value = row[key]
        if (
            not isinstance(value, str)
            or len(value) != 64
            or any(character not in "0123456789abcdef" for character in value)
        ):
            raise ArchiveError(f"manifest line {line_number} has invalid {key}")
    return scope


def decode_archive(row: dict[str, Any], archived: bytes) -> bytes:
    """Decode one validated manifest row, rejecting damaged compressed bytes."""
    try:
        if row["format"] == "gzip":
            return gzip.decompress(archived)
        return lzma.decompress(archived, format=lzma.FORMAT_XZ)
    except (EOFError, gzip.BadGzipFile, lzma.LZMAError, OSError, zlib.error) as error:
        raise ArchiveError(
            f"damaged {row['format']} archive {row['archive_path']}: {error}"
        ) from error


def canonical_archive(row: dict[str, Any], raw: bytes) -> bytes:
    """Recreate the canonical compressed representation for one manifest row."""
    if row["format"] == "gzip":
        return deterministic_gzip(raw)
    return deterministic_xz(raw)


def summarize_formats(rows: tuple[dict[str, Any], ...] | list[dict[str, Any]]) -> dict[str, Any]:
    """Count files and compressed bytes by archive format."""
    summary: dict[str, dict[str, int]] = {}
    for row in rows:
        values = summary.setdefault(row["format"], {"archive_bytes": 0, "files": 0})
        values["archive_bytes"] += row["archive_bytes"]
        values["files"] += 1
    return {name: summary[name] for name in sorted(summary)}


def verify_manifest_batch(repo: Path, manifest: Path) -> VerifiedManifest:
    """Verify one batch against its complete immutable source scope."""
    rows = read_manifest(manifest)
    scopes = {
        validate_row_shape(row, line_number)
        for line_number, row in enumerate(rows, 1)
    }
    if len(scopes) != 1:
        raise ArchiveError(f"manifest mixes source scopes: {manifest}")
    scope = next(iter(scopes))

    commits = {row["source_commit"] for row in rows}
    if len(commits) != 1:
        raise ArchiveError(f"manifest must bind one immutable source commit: {manifest}")
    source_commit = next(iter(commits))
    expected_entries = source_entries(repo, source_commit, scope)
    expected = {entry["source_path"]: entry for entry in expected_entries}

    paths = [row["source_path"] for row in rows]
    if len(paths) != len(set(paths)):
        raise ArchiveError(f"manifest contains duplicate source paths: {manifest}")
    if paths != sorted(paths):
        raise ArchiveError(f"manifest source paths are not sorted: {manifest}")
    if set(paths) != set(expected):
        missing = set(expected) - set(paths)
        extra = set(paths) - set(expected)
        raise ArchiveError(
            f"manifest coverage mismatch for {display_path(repo, manifest)}; "
            f"missing={path_summary(missing)}, extra={path_summary(extra)}"
        )

    ordered_entries = []
    for line_number, row in enumerate(rows, 1):
        entry = expected[row["source_path"]]
        for key in ("source_blob", "source_bytes", "source_mode"):
            if row[key] != entry[key]:
                raise ArchiveError(
                    f"manifest line {line_number} disagrees with Git for {row['source_path']}"
                )
        ordered_entries.append(entry)

    total_source = 0
    total_archive = 0
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
        decoded = decode_archive(row, archived)
        if decoded != raw:
            raise ArchiveError(f"decoded bytes differ from Git blob: {row['archive_path']}")
        if canonical_archive(row, raw) != archived:
            raise ArchiveError(
                f"archive is not the canonical deterministic {row['format']}: {archive}"
            )
        if (repo / row["source_path"]).exists():
            raise ArchiveError(f"raw historical capture remains in the tree: {row['source_path']}")

        total_source += len(raw)
        total_archive += len(archived)

    return VerifiedManifest(
        path=manifest,
        rows=tuple(rows),
        summary={
            "archive_bytes": total_archive,
            "files": len(rows),
            "formats": summarize_formats(rows),
            "manifest_sha256": sha256(manifest.read_bytes()),
            "saved_bytes": total_source - total_archive,
            "source_bytes": total_source,
            "source_commit": source_commit,
        },
    )


def actual_archive_paths(repo: Path) -> set[str]:
    """Return every recognized archive path, including non-regular orphans."""
    paths = set()
    for directory in ARCHIVE_DIRECTORIES:
        root = repo / directory
        if root.exists():
            for pattern in ("*.jsonl.gz", "*.jsonl.xz"):
                paths.update(
                    str(path.relative_to(repo)) for path in root.rglob(pattern)
                )
    return paths


def verify_archive_union(repo: Path, expected_archives: set[str]) -> None:
    """Require the supplied manifests to cover the complete checked-out archive union."""
    actual_archives = actual_archive_paths(repo)
    if actual_archives != expected_archives:
        missing = expected_archives - actual_archives
        extra = actual_archives - expected_archives
        raise ArchiveError(
            "archive coverage mismatch across supplied manifests; "
            f"missing={path_summary(missing)}, extra={path_summary(extra)}"
        )


def verified_manifest_batches(repo: Path, manifests: list[Path]) -> list[VerifiedManifest]:
    """Return verified batches after complete, collision-free global coverage."""
    if not manifests:
        raise ArchiveError("at least one archive manifest is required")

    normalized = [path.resolve() for path in manifests]
    if len(normalized) != len(set(normalized)):
        raise ArchiveError("the same archive manifest was supplied more than once")

    verified: list[VerifiedManifest] = []
    archive_owners: dict[str, Path] = {}
    source_owners: dict[str, Path] = {}
    for manifest in manifests:
        batch = verify_manifest_batch(repo, manifest)
        for row in batch.rows:
            archive_path = row["archive_path"]
            owner = archive_owners.get(archive_path)
            if owner is not None:
                raise ArchiveError(
                    "archive path collision across supplied manifests; "
                    f"path={archive_path}, first={display_path(repo, owner)}, "
                    f"second={display_path(repo, manifest)}"
                )
            archive_owners[archive_path] = manifest
            source_path = row["source_path"]
            source_owner = source_owners.get(source_path)
            if source_owner is not None:
                raise ArchiveError(
                    "source path collision across supplied manifests; "
                    f"path={source_path}, first={display_path(repo, source_owner)}, "
                    f"second={display_path(repo, manifest)}"
                )
            source_owners[source_path] = manifest
        verified.append(batch)

    verify_archive_union(repo, set(archive_owners))
    return verified


def verify_manifests(repo: Path, manifests: list[Path]) -> dict[str, Any]:
    """Verify independent batches and summarize complete global coverage."""
    verified = verified_manifest_batches(repo, manifests)
    if len(verified) == 1:
        return verified[0].summary

    formats: dict[str, dict[str, int]] = {}
    for batch in verified:
        for name, values in batch.summary["formats"].items():
            combined = formats.setdefault(name, {"archive_bytes": 0, "files": 0})
            combined["archive_bytes"] += values["archive_bytes"]
            combined["files"] += values["files"]

    return {
        "archive_bytes": sum(batch.summary["archive_bytes"] for batch in verified),
        "batches": [
            {
                "manifest": display_path(repo, batch.path),
                **batch.summary,
            }
            for batch in verified
        ],
        "files": sum(batch.summary["files"] for batch in verified),
        "formats": {name: formats[name] for name in sorted(formats)},
        "manifests": len(verified),
        "saved_bytes": sum(batch.summary["saved_bytes"] for batch in verified),
        "source_bytes": sum(batch.summary["source_bytes"] for batch in verified),
    }


def verify_manifest(
    repo: Path, manifest: Path, prior_manifests: list[Path] | None = None
) -> dict[str, Any]:
    """Verify the selected batch together with any explicitly supplied prior batches."""
    return verify_manifests(repo, [*(prior_manifests or []), manifest])


def stage_archive(
    repo: Path,
    staging: Path,
    indexed_entry: tuple[int, dict[str, Any]],
    source_commit: str,
    scope: str,
) -> dict[str, Any]:
    """Compress one checked-out source file into its deterministic staging path."""
    index, entry = indexed_entry
    source = repo / entry["source_path"]
    if source.is_symlink() or not source.is_file():
        raise ArchiveError(f"source capture is missing or not a regular file: {source}")
    raw = source.read_bytes()
    if len(raw) != entry["source_bytes"]:
        raise ArchiveError(f"source size changed for {entry['source_path']}")
    archived = deterministic_gzip(raw)
    write_bytes(staging / f"{index:06d}.jsonl.gz", archived)
    row = {
        "archive_bytes": len(archived),
        "archive_path": entry["source_path"] + ".gz",
        "archive_sha256": sha256(archived),
        "format": "gzip",
        "gzip_compresslevel": GZIP_LEVEL,
        "gzip_mtime": GZIP_MTIME,
        "schema_version": (
            LEGACY_SCHEMA_VERSION
            if scope == SESSION_CAPTURE_SCOPE
            else SCOPED_SCHEMA_VERSION
        ),
        "source_blob": entry["source_blob"],
        "source_bytes": len(raw),
        "source_commit": source_commit,
        "source_mode": entry["source_mode"],
        "source_path": entry["source_path"],
        "source_sha256": sha256(raw),
    }
    if scope == NATIVE_EVIDENCE_SCOPE:
        row["source_scope"] = scope
    return row


def create_archives(
    repo: Path,
    source_ref: str,
    manifest: Path,
    prior_manifests: list[Path] | None = None,
    scope: str = SESSION_CAPTURE_SCOPE,
) -> dict[str, Any]:
    prior_manifests = prior_manifests or []
    if manifest.resolve() in {path.resolve() for path in prior_manifests}:
        raise ArchiveError("the new manifest is also listed as a prior manifest")
    if prior_manifests:
        verify_manifests(repo, prior_manifests)
    else:
        verify_archive_union(repo, set())

    source_commit = resolve_commit(repo, source_ref)
    if resolve_commit(repo, "HEAD") != source_commit:
        raise ArchiveError("archive creation requires --source-ref to equal HEAD")
    if manifest.exists():
        raise ArchiveError(f"manifest already exists: {manifest}")
    pathspecs = scope_pathspecs(scope)
    if subprocess.run(
        [
            "git",
            "-C",
            str(repo),
            "diff",
            "--quiet",
            source_commit,
            "--",
            *(str(path) for path in pathspecs),
        ],
        check=False,
    ).returncode != 0:
        raise ArchiveError(f"tracked archival sources differ in scope {scope}")

    entries = source_entries(repo, source_commit, scope)
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
                    lambda item: stage_archive(repo, staging, item, source_commit, scope),
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

    return verify_manifest(repo, manifest, prior_manifests)


def require_clean_worktree(repo: Path) -> str:
    """Require a clean checkout and return the immutable operation commit."""
    status = git(repo, "status", "--porcelain=v1", "--untracked-files=all")
    if status:
        first = status.decode("utf-8", errors="replace").splitlines()[0]
        raise ArchiveError(f"XZ repack requires a clean worktree; first change: {first}")
    return resolve_commit(repo, "HEAD")


def updated_manifest_bytes(
    batch: VerifiedManifest, updates: dict[int, dict[str, Any]]
) -> tuple[bytes, list[dict[str, Any]]]:
    """Replace selected rows while preserving every unaffected line byte-for-byte."""
    original_lines = batch.path.read_bytes().splitlines(keepends=True)
    if len(original_lines) != len(batch.rows):
        raise ArchiveError(f"manifest line count changed during repack: {batch.path}")
    rows = list(batch.rows)
    for row_index, row in updates.items():
        rows[row_index] = row
        original_lines[row_index] = manifest_bytes([row])
    return b"".join(original_lines), rows


def stage_xz_repack(
    repo: Path,
    staging: Path,
    target: tuple[int, int, int, dict[str, Any]],
) -> StagedRepack:
    """Stage one canonical XZ replacement from its verified immutable Git blob."""
    order, batch_index, row_index, row = target
    raw = git(repo, "cat-file", "blob", row["source_blob"])
    if len(raw) != row["source_bytes"] or sha256(raw) != row["source_sha256"]:
        raise ArchiveError(f"source binding failed during repack: {row['source_path']}")

    old_path = repo / row["archive_path"]
    old_bytes = old_path.read_bytes()
    if len(old_bytes) != row["archive_bytes"] or sha256(old_bytes) != row["archive_sha256"]:
        raise ArchiveError(f"gzip archive changed during repack: {row['archive_path']}")

    archived = deterministic_xz(raw)
    new_row = dict(row)
    del new_row["gzip_compresslevel"]
    del new_row["gzip_mtime"]
    new_row.update(
        {
            "archive_bytes": len(archived),
            "archive_path": row["source_path"] + ".xz",
            "archive_sha256": sha256(archived),
            "format": "xz",
            "schema_version": XZ_SCHEMA_VERSION,
            "xz_check": XZ_CHECK,
            "xz_preset": XZ_PRESET,
        }
    )
    validate_row_shape(new_row, row_index + 1)
    if decode_archive(new_row, archived) != raw:
        raise ArchiveError(f"staged XZ bytes do not recover {row['source_path']}")
    if canonical_archive(new_row, raw) != archived:
        raise ArchiveError(f"staged XZ bytes are not canonical: {row['source_path']}")

    new_path = repo / new_row["archive_path"]
    if new_path.exists() or new_path.is_symlink():
        raise ArchiveError(f"XZ archive destination already exists: {new_row['archive_path']}")
    staged_path = staging / "archives" / f"{order:02d}.jsonl.xz"
    backup_path = staging / "originals" / f"{order:02d}.jsonl.gz"
    write_bytes(staged_path, archived)
    write_bytes(backup_path, old_bytes)
    return StagedRepack(
        batch_index=batch_index,
        row_index=row_index,
        old_path=old_path,
        new_path=new_path,
        staged_path=staged_path,
        backup_path=backup_path,
        row=new_row,
    )


def validate_staged_repack(
    repo: Path,
    batches: list[VerifiedManifest],
    replacements: list[StagedRepack],
    staging: Path,
) -> tuple[list[StagedManifest], list[list[dict[str, Any]]]]:
    """Validate prospective manifests and archive-union coverage before publication."""
    updates: dict[int, dict[int, dict[str, Any]]] = {}
    for replacement in replacements:
        updates.setdefault(replacement.batch_index, {})[replacement.row_index] = (
            replacement.row
        )

    staged_manifests = []
    prospective_rows = []
    for batch_index, batch in enumerate(batches):
        batch_updates = updates.get(batch_index, {})
        if not batch_updates:
            prospective_rows.append(list(batch.rows))
            continue
        new_bytes, rows = updated_manifest_bytes(batch, batch_updates)
        staged_path = staging / "manifests" / f"{batch_index:02d}.jsonl"
        backup_path = staging / "manifest-originals" / f"{batch_index:02d}.jsonl"
        write_bytes(staged_path, new_bytes)
        write_bytes(backup_path, batch.path.read_bytes())
        if read_manifest(staged_path) != rows:
            raise ArchiveError(f"staged manifest does not match intended rows: {batch.path}")
        staged_manifests.append(
            StagedManifest(
                path=batch.path,
                staged_path=staged_path,
                backup_path=backup_path,
            )
        )
        prospective_rows.append(rows)

    current_paths = actual_archive_paths(repo)
    old_paths = {str(replacement.old_path.relative_to(repo)) for replacement in replacements}
    new_paths = {str(replacement.new_path.relative_to(repo)) for replacement in replacements}
    expected_paths = {
        row["archive_path"] for rows in prospective_rows for row in rows
    }
    prospective_paths = (current_paths - old_paths) | new_paths
    if prospective_paths != expected_paths:
        missing = expected_paths - prospective_paths
        extra = prospective_paths - expected_paths
        raise ArchiveError(
            "staged archive coverage mismatch; "
            f"missing={path_summary(missing)}, extra={path_summary(extra)}"
        )
    if len(expected_paths) != sum(len(rows) for rows in prospective_rows):
        raise ArchiveError("staged archive path collision across supplied manifests")
    return staged_manifests, prospective_rows


def publish_xz_repack(
    repo: Path,
    manifests: list[Path],
    replacements: list[StagedRepack],
    staged_manifests: list[StagedManifest],
) -> dict[str, Any]:
    """Publish validated replacements with rollback for ordinary filesystem failures."""
    installed: list[StagedRepack] = []
    replaced_manifests: list[StagedManifest] = []
    removed: list[StagedRepack] = []
    try:
        for replacement in replacements:
            replacement.new_path.parent.mkdir(parents=True, exist_ok=True)
            os.replace(replacement.staged_path, replacement.new_path)
            installed.append(replacement)
        for staged_manifest in staged_manifests:
            os.replace(staged_manifest.staged_path, staged_manifest.path)
            replaced_manifests.append(staged_manifest)
        for replacement in replacements:
            replacement.old_path.unlink()
            removed.append(replacement)
        return verify_manifests(repo, manifests)
    except BaseException as error:
        rollback_errors = []
        for staged_manifest in reversed(replaced_manifests):
            try:
                os.replace(staged_manifest.backup_path, staged_manifest.path)
            except OSError as rollback_error:
                rollback_errors.append(str(rollback_error))
        for replacement in reversed(removed):
            try:
                os.replace(replacement.backup_path, replacement.old_path)
            except OSError as rollback_error:
                rollback_errors.append(str(rollback_error))
        for replacement in reversed(installed):
            try:
                replacement.new_path.unlink(missing_ok=True)
            except OSError as rollback_error:
                rollback_errors.append(str(rollback_error))
        if rollback_errors:
            raise ArchiveError(
                "XZ repack failed and rollback was incomplete: "
                + "; ".join(rollback_errors)
            ) from error
        raise


def repack_largest_session_archives_xz(
    repo: Path, manifest: Path, prior_manifests: list[Path] | None = None
) -> dict[str, Any]:
    """Repack exactly the 20 largest gzip session captures as canonical XZ."""
    operation_commit = require_clean_worktree(repo)
    manifests = [*(prior_manifests or []), manifest]
    batches = verified_manifest_batches(repo, manifests)
    all_rows = [row for batch in batches for row in batch.rows]
    existing_xz = [row["archive_path"] for row in all_rows if row["format"] == "xz"]
    if existing_xz:
        raise ArchiveError(
            "bounded XZ repack already has XZ rows; refusing to select another set"
        )

    candidates = []
    for batch_index, batch in enumerate(batches):
        for row_index, row in enumerate(batch.rows):
            if validate_row_shape(row, row_index + 1) != SESSION_CAPTURE_SCOPE:
                continue
            if row["format"] == "gzip":
                candidates.append((batch_index, row_index, row))
    candidates.sort(key=lambda item: (-item[2]["archive_bytes"], item[2]["archive_path"]))
    if len(candidates) < XZ_REPACK_COUNT:
        raise ArchiveError(
            f"XZ repack requires {XZ_REPACK_COUNT} gzip session captures; "
            f"found {len(candidates)}"
        )
    selected = candidates[:XZ_REPACK_COUNT]
    targets = [
        (order, batch_index, row_index, row)
        for order, (batch_index, row_index, row) in enumerate(selected)
    ]

    staging_parent = repo / manifest.parent
    with tempfile.TemporaryDirectory(
        prefix=".session-xz-repack-", dir=staging_parent
    ) as directory:
        staging = Path(directory)
        workers = min(MAX_XZ_WORKERS, len(targets), os.cpu_count() or 1)
        with ThreadPoolExecutor(max_workers=workers) as executor:
            replacements = list(
                executor.map(lambda target: stage_xz_repack(repo, staging, target), targets)
            )
        staged_manifests, _ = validate_staged_repack(
            repo, batches, replacements, staging
        )
        summary = publish_xz_repack(
            repo, manifests, replacements, staged_manifests
        )

    gzip_bytes = sum(row["archive_bytes"] for _, _, row in selected)
    xz_bytes = sum(replacement.row["archive_bytes"] for replacement in replacements)
    summary.update(
        {
            "operation_commit": operation_commit,
            "recovered_bytes": gzip_bytes - xz_bytes,
            "repacked_files": len(replacements),
            "repacked_gzip_bytes": gzip_bytes,
            "repacked_xz_bytes": xz_bytes,
            "selection": "20-largest-gzip-session-captures",
            "selected": [
                {
                    "gzip_bytes": old_row["archive_bytes"],
                    "source_path": old_row["source_path"],
                    "xz_bytes": replacement.row["archive_bytes"],
                }
                for (_, _, old_row), replacement in zip(selected, replacements)
            ],
            "xz_check": XZ_CHECK,
            "xz_preset": XZ_PRESET,
        }
    )
    return summary


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Create, verify or repack deterministic historical JSONL archives."
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
    result.add_argument(
        "--prior-manifest",
        type=Path,
        action="append",
        default=[],
        help="prior batch manifest relative to the repository; repeat for multiple batches",
    )
    commands = result.add_subparsers(dest="command", required=True)
    create = commands.add_parser("create", help="archive one fixed historical source scope")
    create.add_argument("--source-ref", default="HEAD", help="immutable preimage ref")
    create.add_argument(
        "--scope",
        choices=(SESSION_CAPTURE_SCOPE, NATIVE_EVIDENCE_SCOPE),
        default=SESSION_CAPTURE_SCOPE,
        help="fixed source selection (default: session-captures)",
    )
    commands.add_parser("verify", help="verify manifest coverage and exact recovery")
    commands.add_parser(
        "repack-xz",
        help="repack exactly the 20 largest gzip session captures as canonical XZ",
    )
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    repo = args.repo_root.resolve()
    manifest = args.manifest
    if not manifest.is_absolute():
        manifest = repo / manifest
    prior_manifests = []
    for prior_manifest in args.prior_manifest:
        if not prior_manifest.is_absolute():
            prior_manifest = repo / prior_manifest
        prior_manifests.append(prior_manifest)
    try:
        if args.command == "create":
            summary = create_archives(
                repo,
                args.source_ref,
                manifest,
                prior_manifests,
                args.scope,
            )
        elif args.command == "repack-xz":
            summary = repack_largest_session_archives_xz(
                repo,
                manifest,
                prior_manifests,
            )
        else:
            summary = verify_manifest(repo, manifest, prior_manifests)
    except (ArchiveError, OSError, subprocess.SubprocessError) as error:
        print(f"archive_session_captures.py: error: {error}", file=sys.stderr)
        return 1
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
