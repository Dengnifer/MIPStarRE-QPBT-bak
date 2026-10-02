# Palomar hosted profile and actual Challenge audit — 2026-10-02

The goal remains active. No submission, registry contact or companion CI dispatch
occurred. Primary source is still the merged module pilot; all new compact work
and bulk module preparation remain unmerged.

## Published Challenge prototype

PR #775 is at `b01bcd297b8063699f0f321e3ef17485f399b0ee`.
The standalone artifact is992 physical lines/52483UTF8bytes, SHA256
`4600b1c3e2409edf2a68df53a2055516c99646e42750f966cf02e60437700de3`.
It compiles on4.32; it has exactly the four theorem holes and the registered
fixed-field selector value hole. Exact native comparison and supported-version
replay remain pending. The final hook suite reported **908 total tests,9 skipped,
899 executed**, not908 executed passes. Author774 cost2931s and terminated0.
An1800s read-only Astra Ultra/hard scout now audits the actual hash-bound artifact
against the paper, the original statements and the selector contract; this is
not canonical PR approval and cannot certify the pending native checks.

## Module preparation

P2 #747 completed at `0e47e03cc7433bea42a9fc1727783b408fddc110`, parentP1
`69e8b969b37e4c5af4fe60a24fa3defa1cca0482`. It changed exactly109owned files,
with109/109 normalized mathematical-byte equality and normal commit hooks;
worktree clean, no full build/push/PR. Audit SHA256
`b8347e2ae800a480d66d278b8997b40d6081a203add6ea53ce58f1e4b2ddfd4b`.
Actual external dispatch cost572s. P3 #748 is admitted for1200s preparation only,
85owned paths on P2, with the same no-build/no-publication boundary. Full new-
version gates still depend on #756 and preceding packets.

## Official execution profile

Authenticated upstream `scripts/verification_profile.py` explicitly accepts
`palomar-standard-v1` in `load_profile`. Local pure resolution gives GitHub-hosted
`ubuntu-24.04`,350min budget,19800execution seconds,20GiB minimum workspace,
15032385536minimum memory bytes, and profile digest
`eb97b7b548c5d016967434818f0ed48a215e7fdc15528f564ab21ff2927cfd69`.
Use that explicit input with both reusable-workflow/pipeline pins fixed at
`65f0154ed776cd26c224254aa57b379137f28b0d`. The default profile is Namespace;
it must not be silently used. No account/machine change is needed for this route.

## Integration decision

After #756 merges, reconcile the full compact stack in #775 and subject its
whole diff to canonical CI plus independent exact-head review. Parent work stays
open until the integrated commit lands normally. See design-decisions.md and
#27 for the preserved scope/cost decision. No adverse #755 finding is folded away.
