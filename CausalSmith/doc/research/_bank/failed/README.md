# Failed Bank

Stage -0.5 NO-PASS, **or** Stage 0.5 REJECT on correctness/structure (not on
novelty — novelty-only rejections live in `../downgraded/`).

Entries here are pipeline-diagnostic. Scientific value is usually low — the
math was wrong, the proposal was incoherent, or the derivation collapsed
before producing reusable artifacts. We still bank them because they:

- expose Stage -0.5 / Stage 0.5 / scaffold / Codex failure modes;
- contribute to the proposal→derivation tier-drift statistic;
- prevent the same incoherent angle from being re-proposed.

Per-entry metadata: see `../README.md`. For failed entries, `gap_reasons[]`
and `proof_attempt_summary` are the load-bearing fields; `reusable_artifacts[]`
is usually empty and that is fine.
