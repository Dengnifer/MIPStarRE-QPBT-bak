# Worker occupancy enforcement, 2026-09-08

The owner requires at least `ceil(0.8*(k-1))` useful active subagents almost all the time. At total capacity 10, main occupies one slot and workers have nine slots with a floor of eight. There is no additional reservation.

The previous allocation correction did not enforce replenishment. Its activity command recorded counts, while the persistent trigger merely queued prompts behind a long main turn. Independent observations confirmed that activity could fall to two despite available capacity.

Meta guided main to maintain an approved successor queue and delegate refill mechanics. Main selected all work and retained assignment, review and merge authority. The delegate started at 08:16:37Z. The attached receipts record actual natural completions and successor tool output, including recovery delays; configuration and queue acceptance are not counted as recovery. The primary coordinator acknowledged continuing refill ownership in its own receipt recorded at 08:49:30Z, effective at 08:46:37.885Z. The older delegate receipt lagged that acknowledgment; both snapshots are retained. Main also extended the delegate to cover the transfer.

See `summary.json` for the bounded measurements, exact transition times and the handoff receipt as observed at archive time. The compact journals preserve worker identities and turn IDs without raw prompts, credentials or model content. Historical unclosed turns without recent activity are excluded. Six sampler regression tests cover completion, resume, stale activity, inherited history, interruption and root-scoped incremental reads.

These observations measure current worker activity, not endpoint request concurrency or mathematical productivity. They establish bounded behavior and retain limitations rather than asserting a guarantee about all future work. Session records are in `owner-sessions.jsonl`; unavailable per-helper usage remains null. Main owns normal telemetry publication.
