# Palomar session-archive multi-batch recovery - 2026-10-02

Issue #777's second archive creation installed ten deterministic gzip files and
removed their raw working copies, then failed because verification compared the
selected second manifest with every archive in the checkout. The 2,101 archives
from the already verified first batch remained intact. The repair adds explicit
prior-manifest verification and exact global union coverage.

## Immutable batch verification

The repaired verifier ran against the interrupted real checkout with:

```text
python3 local/bin/archive_session_captures.py \
  --manifest results/telemetry/session-capture-archives-palomar-20261002-later.jsonl \
  --prior-manifest results/telemetry/session-capture-archive-manifest.jsonl \
  verify
```

It exited zero in 153.62 seconds with maximum RSS 522,068 KiB. For every row it
checked complete raw-capture coverage at the row's immutable source commit,
source blob/mode/size/SHA-256, archive size/SHA-256, canonical deterministic
gzip bytes and byte-for-byte decompression. The supplied manifests' union was
exactly every checked-out `.jsonl.gz` path, with no collision or orphan.

Initial batch:

- Source commit: `36805f1d0ea3c6aae93bb99a7a2f250b1dda3c38`
- Files: 2,101
- Source bytes: 2,024,852,261
- Archive bytes: 459,282,582
- Manifest SHA-256:
  `84b34ebfa108e2c3325916447dff23c512e115d598c6a7e897da2cc931a56037`

Later batch:

- Source commit: `f1d489516967e9a694935a8706051bc5bc56e8a8`
- Files: 10
- Source bytes: 15,132,788
- Archive bytes: 2,788,751
- Manifest SHA-256:
  `d02461dfd48a7d1fa180808ed2b4795a7fcf49cb309fc99aca0014df42a5c207`

Combined totals: 2,111 files, 2,039,985,049 source bytes and 462,071,333
archive bytes.

The complete archive representation saves 1,577,913,716 checked-out bytes
relative to the immutable raw captures.

## Candidate source size

A checkout of the complete staged index made with `git checkout-index`
contained 6,195 regular files totaling 517,947,774 bytes under the pinned
Palomar verifier's exact `tree_size` implementation. The 524,288,000-byte cap
therefore retained 6,340,226 bytes of headroom.

## Focused regression

`python3 -m unittest -v scripts.tests.test_session_capture_archive` ran 9 tests
with 0 failures, 0 errors and 0 skips. The suite includes two successive source
commits and archive batches, pre-mutation refusal without the prior manifest,
successful creation with it, independent attribution, global re-verification,
orphan and collision rejection, archive tampering, raw/gzip reader equivalence
and damaged gzip rejection.
