---
qid: pid_rdd_flow_manipulation
spec: v1
topic: "Flagship computational upgrade of the banked bounded-manipulation RDD partial-ID result: replace the closed-form single-cutoff envelope by a strongly-polynomial min-cost-flow / total-unimodularity algorithm for sharp covariate-conditional manipulation bounds across many cutoff neighborhoods, with an explicit dual certificate recovering the parent interval as the one-cutoff case."
novelty_target: flagship
supersedes:
  parent_qid: "pid_rdd_manipulation_bounded"
  parent_spec: "v1"
  parent_tier: "candidates"  # tier retired 2026-07-18; parent re-tiered to _bank/downgraded/
  upgrade_axis: "computation"
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: unknown
reraise_status: retry
gap_reasons:
  - "Upgrade: N-upgrade-thin -- graph/TU upgrade attempted, but fixed-slice equivalence and dual certificate are not algebraically valid as stated."
  - "Conjecture 1: N-promissory-object -- flagship sharp envelope over M_ext is advertised, but Section 9 computes only one fixed lambda,m slice, not the global lower/upper envelope from primitives."
  - "Conjecture 1: N-thin-anchor -- flagship comparison cites GRR 2020, Bertanha 2020, and Cattaneo et al. 2021 by bibkey only without precise location anchors."
  - "Theorem 1: C-wellposed -- LP carry-flow equations and graph balances do not match; graph permits flows not represented by displayed LP."
  - "Theorem 2: C-sanity -- displayed dual certificate contradicts complementary slackness and has sign/arithmetic inconsistency."
reusable_artifacts:
  - path: "pid_rdd_flow_manipulation_v1_gaps.json"
    kind: literature_map
    one_line: "Useful RDD computation map: GRR 2020, Rosenman et al. 2019, Bertanha 2020, Cattaneo-Keele-Titiunik-Vazquez-Bare 2021, Chernozhukov-Lee-Rosen 2013, Orlin 1993."
  - path: "pid_rdd_flow_manipulation_v1_reviews/angle4_v5.json"
    kind: counterexample
    one_line: "Reviewer identifies the exact graph-balance and dual-certificate contradictions; use before attempting another flow/TU RDD proposal."
  - path: "pid_rdd_flow_manipulation_v1_proposal.tex"
    kind: other
    one_line: "Final failed proposal; reusable mainly as a warning that fixed-slice flow is not enough for a flagship global endpoint algorithm."
seeds_burned: []
proof_attempt_summary: |
  Attempted a computation-axis flagship upgrade of the bounded-manipulation RDD parent: many-neighborhood sharp endpoints via flow/TU machinery and an explicit dual certificate. The topic was better targeted than the network-IV run, and the reviewer accepted the broad literature gap, but the proposed algorithm never became fully constructive: retained-mass search, global endpoint envelope, graph balances, and the worked dual certificate remained under-specified or inconsistent. Treat this as a proposal-math failure; a future attempt should hand-derive the finite graph convention and one complete global-envelope example before invoking thmsmith.
banked_on: "2026-05-24"
---

# pid_rdd_flow_manipulation / v1 â€” Failed

**Topic.** Flagship computational upgrade of the banked bounded-manipulation RDD partial-ID result: replace the closed-form single-cutoff envelope by a strongly-polynomial min-cost-flow / total-unimodularity algorithm for sharp covariate-conditional manipulation bounds across many cutoff neighborhoods, with an explicit dual certificate recovering the parent interval as the one-cutoff case.

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -0.5 NO-PASS after 5 angles: RDD min-cost-flow computation upgrade had plausible literature gap but failed proposal review because finite endpoint search, retained-mass candidates, and active-budget dual certificate remained under-specified.

**Supersedes.** pid_rdd_manipulation_bounded_v1 (tier=candidates, upgrade_axis=computation). The parent now lives in `_bank/downgraded/` (the `candidates` tier was retired 2026-07-18 and the parent re-graded subfield) and remains an independent reference; this entry is the flagship upgrade.

## Key files

- `pid_rdd_flow_manipulation_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `pid_rdd_flow_manipulation_v1_proposal.tex` â€” final proposal version.
- `pid_rdd_flow_manipulation_v1.tex` â€” derivation note (if Stage 0 ran).
- `pid_rdd_flow_manipulation_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_rdd_flow_manipulation_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
