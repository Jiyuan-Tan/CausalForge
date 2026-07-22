---
qid: eid_data_fusion_k_source
spec: v1
topic: "Sharp identifiability of an interventional causal effect from a heterogeneous collection of k partially-overlapping observational distributions under a selection-diagram constraint set: a closed-form iff identifiability characterization extending Bareinboim-Pearl (2014, 2016) data fusion from two sources to k sources, with a polynomial-time decision algorithm in the size of the diagram and an explicit counterexample witness construction certifying non-identifiability when the iff fails, recovering Bareinboim-Pearl as the k=2 special case"
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # D0.5 unanimously rejected on NOVELTY (tier floor), not correctness. Verbatim/near-verbatim:
  - "Novelty tier floor: assessed tier is at most subfield, below novelty_target=flagship, because the note proves a finite chain-rule certificate closure under assumed singleton source clauses and explicitly disclaims a flagship comparison with published data-fusion algorithms."
  - "Main novelty claim: the chain-refined certificate is a useful source-cover closure, but its key algebra is the ordinary finite chain rule plus assumed singleton source invariances, so the current artifact does not establish a flagship-level regime opening."
  - "Theorem 2: the strict-extension result is only relative to the note's exact source-cover certificate, not to a named published identification algorithm or open problem, so the assessed tier is below novelty_target=flagship."
  - "Comparison with closest literature: the note names Lee-Ghassami-Shpitser 2024 / systematic-selection / DoSearch / gID but does not show the chain-product class is outside, sharper than, or an open subcase of those published identification frameworks."
  - "Correctness (mostly pass): one repairable gap in attempt 2 — Theorem 2's strict-extension proof asserted P*_x(W1..Wr)=P*(W1..Wr|X=x) for root X without ruling out bidirected confounding between X and post-X variables; attempt 3 added the missing no-bidirected-edge/randomized-root condition."
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a flagship closed-form iff identifiability characterization for k-source
  data fusion extending Bareinboim-Pearl, with a poly-time decision algorithm and a
  non-identifiability counterexample witness. Structure and correctness held across all
  three D0.5 attempts (one repairable Theorem-2 confounding gap was patched in attempt 3
  by adding the no-bidirected-edge/randomized-root condition), but the flagship claim
  collapsed: the proven kernel is a finite chain-rule source-cover certificate closure
  under assumed singleton typed source invariances — a clean but subfield-tier result
  inside the existing ID/data-fusion framework, which the producer's own note self-disclaims
  as non-flagship. What remains open is the actual flagship deliverable: a theorem-level
  separation / strict-extension / equivalence frontier against a named published framework
  (Lee-Ghassami-Shpitser 2024, systematic-selection, DoSearch, gID).
banked_on: "2026-05-20"
---

# eid_data_fusion_k_source / v1 — Downgraded

**Topic.** Sharp identifiability of an interventional causal effect from a heterogeneous collection of k partially-overlapping observational distributions under a selection-diagram constraint set: a closed-form iff identifiability characterization extending Bareinboim-Pearl (2014, 2016) data fusion from two sources to k sources, with a polynomial-time decision algorithm in the size of the diagram and an explicit counterexample witness construction certifying non-identifiability when the iff fails, recovering Bareinboim-Pearl as the k=2 special case

**Novelty target.** flagship

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REJECT

**Banking reason.** 3 angles ACCEPT -0.5 flagship, all REJECT 0.5: derivation yielded source-cover soundness + chain-refinement counterexample, structurally a finite-chain-rule certificate inside Bareinboim-Pearl framework. Producer self-disclaimed flagship status in its own note. Reviewer correctly flagged below flagship floor.

## Key files

- `eid_data_fusion_k_source_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_data_fusion_k_source_v1_proposal.tex` — final proposal version.
- `eid_data_fusion_k_source_v1.tex` — derivation note (if D0 ran).
- `eid_data_fusion_k_source_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `eid_data_fusion_k_source_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
