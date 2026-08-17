---
qid: exp_exposure_ambiguity_design_frontier
spec: v1
topic: "Design-inclusive minimax estimation of the total treatment effect under finite exposure-mapping ambiguity. For fixed pbar in (0,1) and every admissible n, the primitive experiment is indexed by `(n,E,pbar)`: E is a finite latent menu of arbitrary finite-valued exposure mappings, potential outcomes are fixed bounded tables measurable under some menu member, the experimenter chooses any exact-treated-count assignment law, and the estimator is arbitrary. The ambient graph is ancillary once E is fixed and matters in graph-local subclasses only through the resulting menu. The delivered kernel gives a lossless sign reduction, an exact primal–dual perspective saddle, equality of the minimax risk and finite-program frontier, a converse for every design and estimator, and recovery of an attaining exact-budget design and multilinear rule. The collision sandwich has sharp universal constants. For every fixed pbar, persistent cardinality-two witnesses have equal mapping-wise labeled conflict-graph multisets and common singleton-oracle risk 5/6 but robust risks 1 and 5/4, producing exact adaptation and robust-risk gaps of 1/4. An unconditional joint-exposure-signature theorem gives an exact collision LP, optimizer lifting, a congestion-R cover, and polynomial computation in the stated logarithmic-signature regime. No interference proves locality and polynomial orbit tables alone do not control congestion, while an explicit dense radius-one split-graph family proves persistent graph-local conflict-graph nonrepresentability. Bounded-degree or sparse-natural separation and broader primitive compression conditions remain open. Classical finite minimax equality is not claimed as novel. The closest accepted-bank SNIPE and bipartite results concern, respectively, one known neighborhood model under Bernoulli assignment and a conservative graph-only variance envelope, not this latent-menu exact-count unrestricted saddle."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "A natural sparse or bounded-degree latent-menu family with a matched frontier, a calibrated many-coordinate lower bound, or a substantive ambiguity-free characterization remains open."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The persistent separation is an n=2 replication: every growing witness is a labeled type blow-up observed through the same two selector cells."
  - "The collision sandwich is badly calibrated on no interference: inf C_n = Theta(n^-1), L_n = Theta(n^-1/2), and inf U_n = 2, so both sides miss the frontier by a factor of order sqrt(n)."
  - "The R_n compression theorem exactly computes a collision surrogate and has no natural positive instance in the note; its polynomial regime is demonstrated only by engineered small-signature witnesses."
  - "Comparator positioning establishes a distinct latent-menu scope, but not a head-on matched frontier over a natural family comparable to the accepted SNIPE result."
reusable_artifacts:
  - discovery/core.json  # canonical 15-result mathematical specification and comparator map
  - discovery/writeup.tex  # complete informal proofs, exact finite saddle, and counterexamples
  - discovery/solve_thm_exposure_signature_compression_and_local_boundaries.json  # final structural solve record
  - discovery/proof_archive/  # content-addressed D-stage proof attempts and certificates
  - formalization/plan.json  # discarded F-stage decomposition; useful only as orientation for a future upgrade
seeds_burned: []
proof_attempt_summary: |
  Discovery produced a sound exact finite decision formulation, sign reduction, primal-dual
  minimax saddle, oracle-adaptation counterexamples, collision bounds, and signature-compression
  results. Formalization reached F2/F2.5 scaffolding but was stopped before proof filling; all partial
  Lean files were removed. The field-tier promise collapsed because the persistent and graph-local
  witnesses reduce to engineered two-signature replications, the collision sandwich fails to recover
  even the no-interference rate, and no natural scalable compression regime or matched natural-family
  frontier was obtained. A future upgrade should begin with a genuinely many-coordinate lower bound or
  a sparse/bounded-degree latent-menu family, not resume the discarded scaffold unchanged.
banked_on: "2026-08-08"
---

# exp_exposure_ambiguity_design_frontier / v1 — Downgraded

**Topic.** Design-inclusive minimax estimation of the total treatment effect under finite exposure-mapping ambiguity. For fixed pbar in (0,1) and every admissible n, the primitive experiment is indexed by `(n,E,pbar)`: E is a finite latent menu of arbitrary finite-valued exposure mappings, potential outcomes are fixed bounded tables measurable under some menu member, the experimenter chooses any exact-treated-count assignment law, and the estimator is arbitrary. The ambient graph is ancillary once E is fixed and matters in graph-local subclasses only through the resulting menu. The delivered kernel gives a lossless sign reduction, an exact primal–dual perspective saddle, equality of the minimax risk and finite-program frontier, a converse for every design and estimator, and recovery of an attaining exact-budget design and multilinear rule. The collision sandwich has sharp universal constants. For every fixed pbar, persistent cardinality-two witnesses have equal mapping-wise labeled conflict-graph multisets and common singleton-oracle risk 5/6 but robust risks 1 and 5/4, producing exact adaptation and robust-risk gaps of 1/4. An unconditional joint-exposure-signature theorem gives an exact collision LP, optimizer lifting, a congestion-R cover, and polynomial computation in the stated logarithmic-signature regime. No interference proves locality and polynomial orbit tables alone do not control congestion, while an explicit dense radius-one split-graph family proves persistent graph-local conflict-graph nonrepresentability. Bounded-degree or sparse-natural separation and broader primitive compression conditions remain open. Classical finite minimax equality is not claimed as novel. The closest accepted-bank SNIPE and bipartite results concern, respectively, one known neighborhood model under Bernoulli assignment and a conservative graph-only variance envelope, not this latent-menu exact-count unrestricted saddle.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Sound latent-menu minimax framework, but field novelty is not delivered: witnesses are engineered two-signature replications, the collision sandwich is rate-loose at no interference, and no natural scalable compression regime is proved.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The achieved tier was re-audited after D0.5 by both the main orchestrator and a fresh managed
Sol-high validity auditor, independently of the pipeline's field-tier labels. Both classified the
result as sound but subfield and found no bounded repair capable of restoring field tier. The user
then requested termination, downgrade banking, and removal of the incomplete Lean formalization.
