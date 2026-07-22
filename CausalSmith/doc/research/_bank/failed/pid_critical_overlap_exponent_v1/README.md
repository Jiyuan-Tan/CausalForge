---
qid: pid_critical_overlap_exponent
spec: v1
topic: "Sharp partial identification of CATT under bounded overlap violation via a critical overlap exponent controlling interval-width growth near e(x)=0 or 1."
novelty_target: flagship
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "Pipeline/env failure before proposal review: active copy logged `Stage -1.1 emitted no parseable JSON` and never produced a proposal."
  - "BROKEN_envbug copy showed a state-machine bug: D-1.2 and D-0.5 were skipped, then D0 ran with `conjectures: []`."
reusable_artifacts:
  - path: "(lost with BROKEN_envbug scratch directory; see transcript if needed)"
    kind: literature_map
    one_line: "Reusable literature map: Crump-Hotz-Imbens-Mitnik 2009, Khan-Tamer 2010, Manski 1990, Li-Morgan-Zaslavsky 2018, Lee-Weidner 2021, Imbens-Manski 2004, Stoye 2009, Rothe 2017, Ma-Wang 2020, Aronow-Lee 2013, Miratrix-Wager-Zubizarreta 2018, Manski-Pepper 2000."
seeds_burned: []
proof_attempt_summary: |
  This run should not be read as a mathematical rejection of the overlap-exponent topic. The live copy failed at D-1.1 JSON parsing; the earlier BROKEN_envbug copy harvested a useful literature map but then skipped the proposal and proposal-review stages, allowing D0 to run with no conjectures. Treat this as a pipeline failure and, if revisiting the topic, restart from the literature map rather than resuming the banked state.
banked_on: "2026-05-24"
---

# pid_critical_overlap_exponent / v1 — Failed

**Topic.** Sharp partial identification of CATT under bounded overlap violation via a critical overlap exponent controlling interval-width growth near e(x)=0 or 1.

**Novelty target.** flagship

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** Past attempt failed as a pipeline/env issue: Stage -1.1 emitted no parseable JSON in the active copy; the BROKEN_envbug copy showed D-1.2/D-0.5 skipped and D0 ran with zero conjectures.

## Key files

- `pid_critical_overlap_exponent_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_critical_overlap_exponent_v1_proposal.tex` — final proposal version.
- `pid_critical_overlap_exponent_v1.tex` — derivation note (if Stage 0 ran).
- `pid_critical_overlap_exponent_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_critical_overlap_exponent_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
