# Completion estimate catch-up: verified publication

- Session: `orc-168-20260906-02`; owner-authorized routine report operation for #168.
- Canonical comment: https://github.com/Dengnifer/MIPStarRE-A/issues/168#issuecomment-5557970241
- Comment ID: `5557970241`; server `created_at`: `2026-09-06T08:15:59Z`,
  or `2026-09-06T16:15:59+08:00` in `Asia/Shanghai`.
- GitHub issue title remains exactly `Completion estimate (6-hourly)`.
- One POST was made through the primary checkout's `local/bin/gh_common.py.api`.
  The paginated comments reread found exactly one catch-up marker. A separate
  `GET issues/comments/5557970241` confirmed its ID, server timestamp and exact body.

## Report and pinned inputs

The original two visible report lines and 197-site count-based calculation are
preserved. A hidden marker supplies the stable idempotency key. The exact body is
represented below as a JSON string; escapes denote the original Unicode characters
and newlines, not literal backslash characters in the published comment.

```json
"<!-- mipstarre-estimate-catchup issue=168 transition=20260906-six-hourly -->\n**2026-09-06 08:15Z \u2014 implemented \u2248 68% \u00b7 days to go \u2248 1.3**\n<sub>63 of 197 sites open on main (ba29932); 17 proved in open PRs; trailing-24h rate 49 sites/day.</sub>\n"
```

- Actual GitHub main, obtained through `git/ref/heads/main` and checked again
  immediately before publication: `ba299326ebde0d9f94fc9b4e9b557ce776e8f1cf`.
- Sampling time: `2026-09-06T08:15:29.179039+00:00`; trailing-24-hour cutoff:
  `2026-09-05T08:15:29.179039+00:00`.
- Previous revision selected by the installed estimator's `git rev-list -1 --before`
  method on pinned main: `f5979e7f6c20b330a9a29f1c88754dd1d639a35c`.
- Current count: 63 lines containing `sorry` across QPBT Lean files; previous count: 112.
  The count was also checked with `git grep -c sorry` on pinned main.
- Closed: `197 - 63 = 134`; implemented: integer `134 * 100 / 197 = 68%`.
  Rate: `112 - 63 = 49` sites/day; days: `round(63 / 49, 1) = 1.3`.
- All 20 actual open PRs were obtained using the paginated API. Their exact head SHAs
  were checked again before posting. Every head was available locally; none was skipped.
- Open-PR count: 17 unique removed `sorry` lines, deduplicated by source file and
  removed line text across `git diff -U0 PINNED_MAIN...PINNED_PR_HEAD`, exactly as in
  the installed estimator. These are the estimator's count-based proof-site figures,
  not an independent proof or review certification.

Machine-readable report row, also retained as `estimate-row.jsonl` in the cache:

```json
{"ts":"2026-09-06T08:15:34Z","main":"ba29932","denominator":197,"open_sites":63,"closed_sites":134,"percent":68,"open_sites_24h_ago":112,"rate_per_day":49,"days_to_go":"1.3","sites_in_open_prs_dedup":17}
```

## Timing and preserved state

- The prior report is comment `5555652742`, server-created at `2026-09-06T00:00:28Z`
  (`08:00:28` local). The cadence transition was planned to leave a nominal 10-hour
  gap from the old 08:00-local slot to the new 18:00-local slot. From the actual prior
  server timestamp to that new slot, the interval is 9h 59m 32s (35,972 seconds).
- The actual interval from that prior report to this catch-up is **8h 15m 31s**
  (29,731 seconds), measured from the two GitHub server timestamps.
- Installed row, reread before and after publication:

```cron
0 */6 * * * /home/drx/bin/estimate.sh >> /home/drx/.cache/mipstarre-dev/watchdog/cron.log 2>&1
```

- Next scheduled run: **September 6, 2026, 10:00 UTC / 18:00 Asia/Shanghai**.
  This is a schedule calculation, not a claim that the future execution succeeded.
- `timedatectl` and `/etc/timezone` both confirm `Asia/Shanghai`. There is no `TZ`
  or `CRON_TZ` row in the crontab. `cron.service` is active/running and reports no
  service environment override. The prior session's more extensive timezone checks
  are preserved in its evidence artifact.
- The entire crontab is unchanged, including the three unrelated jobs at minutes
  17, 37 and 47. No cron installation, title edit or recurring script edit occurred.
- All seven old comments retain their exact IDs, bodies, `created_at` and `updated_at`.
  The issue body is unchanged. The recurring report wording and formula are unchanged.
- Installed script SHA-256 before and after:
  `cc85236a9db85fc5e2a3b348db2df2902ecd5f581b299067ea8993f7b13e5c88`.
- Issue pointer SHA-256 before and after:
  `c02efad74c4db35b2450beec922eb590d202b34c5b436bff0b6acc15059f5d21`.
- Prior owned evidence `results/telemetry/estimate-six-hourly-20260906-orc-168-01.md`
  remains byte-identical with SHA-256
  `6e84fd9547f174adf851e7e59c350d5115cb706934737656f22779b6cebd923c`.

## Evidence and operational boundaries

Detailed records are under:

`/home/drx/.cache/mipstarre-dev/watchdog/estimate-catchup-168-20260906/`

They include `catchup.py`, the exact `body.md`, original and reread issue/comments
JSON, pinned main and open-PR API responses, per-file counts, per-PR removed lines,
the deduplicated set, the one-shot POST journal and response, the independent comment
GET, before/after local-state hashes, `prepared.json`, and `verification.json`.
The helper locks this operation, adopts an existing marker, and refuses a second POST
after an ambiguous recorded attempt. No old comment is PATCHed.

All GitHub calls used the PRIMARY helper at
`/home/drx/MIPStarRE-qpbt/local/bin/gh_common.py`; the external estimator containing
raw `gh` calls was read but not executed. GitHub API processes alone received the
per-command proxy `http://127.0.0.1:7895`. No broad relay proxy, model peer, model
probe, credential read/snapshot, proof/source edit, build, dispatch, or commit ran.

No primary telemetry append was attempted while the #252 integration restorer was
active. The standalone machine-readable row and this worktree report retain the
measurement without racing the primary restore. Any later primary import must be
coordinated with that restorer and deduplicated by the canonical comment ID; this
session neither modified primary telemetry nor requested another report publication.
Session-registry and final-message capture remain the dispatcher's responsibility.
