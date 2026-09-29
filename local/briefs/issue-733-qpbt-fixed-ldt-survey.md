# Issue 733: QPBT source improvements with LDT fixed

Status: prepared; not admitted. This is an independent mathematical scout, not authority to implement.

Owner instruction (2026-09-29): "the scout and report should include the improvements that improves the qpbt part of the source paper, with the ldt part frozen, and pick a most significant one to implement, after the current implementation done".

This instruction extends the older two-improvement stopping rule. Finish #729 under its existing target and ownership. Survey and select one additional QPBT-only improvement; implement it only after #729 is complete. The final report #730 and requested final goal pause follow that additional implementation.

## Source and frozen inputs

Read local/personas/scout.md, AGENTS.md, the current owner briefing, and this later instruction. Read the primary source first: references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex and 14_analysis_of_the_pauli_basis_test.tex; use references/neexp-paper/07_a_self_test_for_the_pauli_basis.tex as secondary. Then read the active blueprint, Lean, and accepted scouts727-01 through06 (05 is the final prior numerical plan).

Freeze LDT as a black-box input: same theorem, hypotheses, constants, sample parameters, and error function on BOTH sides of every QPBT improvement. Trace a symbolic input error first; separate any gain from how QPBT processes that input from a gain to LDT itself or its instantiation. No edits under MIPStarRE/LDT, its exports, LDT blueprint, or paper mirrors. Native LDT PR731 is merged atfac99fdf22bbdbb83a2376ca48cd679dc7d13750; its MIPStarRE/LDT tree isddd92480c55bbabba5a96af96064fc792a5eb68c.

The immutable starting QPBT baseline is4526886890dc72886bc81032366557082267ef78, containing the proved explicit raw/qubit baseline and merged native LDT. Current #729 work will add separate state/operator extraction, coefficient/degree separation, and stronger LDT import; its required target is min(4,10^14*(md)^4*E_b), b=1/67108864, plus deltaQld100 b and both qubit counterparts. Treat those planned mechanisms as reserved/already selected, not a new improvement. Do not read or modify live A/B/D worktrees. Before later implementation, main must supply the completed exact #729 head; mathematical scout calculations do not certify that future head.

## Deliverable

Produce a source-grounded inventory of QPBT-only improvements with LDT fixed. For each: source label and immutable narrow passage, mathematical assumptions, original bound, proposed bound and a derivation or precise missing step, effect on the final headline (including prefactor and exponent), actual Lean consumers, same-witness/raw-effect/range-projection obligations, implementation cost and risk. Cover the prior deferred commutation, Schmidt-mirror pasting, direct-passing triangle, projective rounding, coefficient/dimension, extraction and transfer candidates; include further candidates the source actually supports. Explain why each is or is not an improvement to the paper's QPBT argument, rather than only to our conservative formalization envelope. A printed existential exponent must not be described as a printed explicit number.

Select exactly ONE additional improvement beyond #729, prioritizing the largest justified effect on QPBT exponents and scaling, with a feasible concrete proof plan. Compare it against every other viable candidate. Distinguish one localized improvement from a bundle of independent changes; do not present an unverified product of projected gains as established. Do not silently adopt a weaker target because a convenient scalar lemma compiles. If a source defect or unresolved mathematical obstruction prevents a proposed claim, state it with the relevant assumptions and construction.

Give two comparisons: the source argument with identical LDT input, and the expected additional effect after the current #729 quantitative result with its LDT dependency still fixed. Do not count the factor8 extraction gain a second time. Explicitly separate already-implemented/current work, genuinely new candidates, bookkeeping-only gains, source corrections, and rejected unsupported arguments. For the chosen candidate, identify the affected proved baseline, exact theorem signatures/domain to preserve, minimal file ownership and a bounded implementation plan. The baseline must precede the improvement; #729 may supply it when its actual proved statements suffice.

Return a full mathematical report and concise recommendation. Main will check it, create a separate concrete implementation issue blocked by #729 and #733, and assign Lean writing to Sol. No implementation, publication, Git mutation, external messages, children, permission/account/key changes, foreign-project access, or comparator changes by this scout. Temporary read-only mathematical probes may use the prepared private build environment, but no repository source change. All proof-integrity and source-faithfulness rules remain binding.

## Admission requirements

Astra ultra, primary space-3 only, --job-class hard with reason "owner 2026-09-29: fixed-LDT source-paper QPBT survey and mathematical selection". Use primary local/bin/dispatch.sh. Proposed work budget1800s, hard timeout2400s; actual admission must set absolute deadlines, confirm a free account slot and the exact source/worktree, and require a checkpoint within10 minutes. This preparation grants no slot. Retain earlier scout and implementation costs; this is a new owner-authorized survey with its own actual cost, not a reset of #729.
