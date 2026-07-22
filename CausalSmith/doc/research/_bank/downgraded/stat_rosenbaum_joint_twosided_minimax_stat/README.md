---
qid: stat_rosenbaum_joint_twosided_minimax
spec: stat
topic: "Joint two-sided Rosenbaum sensitivity calibration from a shared least-favorable assignment law (bridge: matched-study Gamma-sensitivity x minimax multiple testing), using the banked stat_rosenbaum_lf_family_minimax_stat result only as substrate: construct a computable level-indexed primal-dual calibration for heterogeneous matched sets that is operational without a known-Q oracle; prove finite-sample validity against every Gamma-bounded assignment law; characterize the exact (alpha,Gamma,design) region where the joint two-sided sensitivity bound strictly improves the conventional Bonferroni-doubled pair of one-sided bounds, including exact equality at Gamma=1 and the verified strict gap 0.158 at Gamma=2; prove when the least-favorable support switches and give an algorithm/certificate usable by sensitivitymv and senfm and by two-sided sensitivity reporting. The field-level headline must be the implementable joint procedure plus its strict-improvement theorem and published-workflow comparison; the banked finite all-tests LP, pair NP theorem, support-switch examples, and oracle design-sensitivity ceiling are lemmas and must not be resubmitted as the novelty claim."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "C-definitional-unfold: Permitting exhaustive serial visitation and transcript output makes finite exact calibration and a finite parameter-cell partition follow directly from finite vertex enumeration and comparisons of finitely many rational functions; the stated question has no nontrivial algorithmic guarantee."
  - "C-wellposed: The ban on retaining an in-memory Cartesian-product array is representation-dependent and has no RAM/Turing memory model, workspace bound, or output-size criterion, so it does not define a mathematical algorithmic property."
  - "N-no-stat-frontier-advance: The finite counterexample and exact-value hardness result provide neither a new causal estimand estimator with a rate or limit law nor a sharper/first statistical bound, so the Stat kernel is below the requested field-tier frontier."
reusable_artifacts:
  - discovery/proto_core.json
  - discovery/proposal.tex
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/writeup.pdf
  - discovery/solve_thm_opposite_tail_capability_separation_and_hardness.json
  - discovery/solve_prop_gamma_two_gap_witness.json
  - discovery/gaps.json
  - reviews/angle0_v6.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run proved and repeatedly audited a useful capability/hardness package: an all-Gamma>1 nonmonotone least-favorable witness, exact separation from score-monotone candidates, a moment-representation obstruction, exact-value #P-hardness, Gamma=1 equality, and finite positive/loss fixtures. The field-tier operational headline did not survive review because its serial-enumeration certificate was definitionally finite without a nontrivial machine-model guarantee, and the package did not establish a new statistical rate, limit law, estimator, or sharper inference bound. Reopening should target one of those new theorem objectives rather than resume prose-level revision.
banked_on: "2026-07-17"
---

# stat_rosenbaum_joint_twosided_minimax / stat — Downgraded

**Topic.** Joint two-sided Rosenbaum sensitivity calibration from a shared least-favorable assignment law (bridge: matched-study Gamma-sensitivity x minimax multiple testing), using the banked stat_rosenbaum_lf_family_minimax_stat result only as substrate: construct a computable level-indexed primal-dual calibration for heterogeneous matched sets that is operational without a known-Q oracle; prove finite-sample validity against every Gamma-bounded assignment law; characterize the exact (alpha,Gamma,design) region where the joint two-sided sensitivity bound strictly improves the conventional Bonferroni-doubled pair of one-sided bounds, including exact equality at Gamma=1 and the verified strict gap 0.158 at Gamma=2; prove when the least-favorable support switches and give an algorithm/certificate usable by sensitivitymv and senfm and by two-sided sensitivity reporting. The field-level headline must be the implementable joint procedure plus its strict-improvement theorem and published-workflow comparison; the banked finite all-tests LP, pair NP theorem, support-switch examples, and oracle design-sensitivity ceiling are lemmas and must not be resubmitted as the novelty claim.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** V6 reviewer assessed the sound capability and hardness kernel at letter tier; field advancement requires a new machine-model complexity or statistical-performance theorem.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

- `discovery/proto_core.json` and `discovery/proposal.tex` are the restored, reviewed v6 source artifacts. Their SHA-256 hashes at banking were `d39c98763b93ae6bde4dffc13db6a3d35b78bce835e4509e57c473a828918737` and `bf23883f04c02b30b91c6b65261ac0bbfb93554fd3e5814c7cabe5b48491bf7c`, respectively.
- The active v7 producer was interrupted after touching `proto_core.json`; banking restored the archived v6 copy before moving the run.
- `discovery/core.json` and `discovery/writeup.*` are the last clean canonical D0 checkpoint and remain valuable proof substrate, but they predate the final v6 proposal review and are not an aligned derivation of v6.
- `reusable: not_reusable` applies to resuming this same operational field claim. `reraise_status: re-raise` records that the sound kernel may support a new run only after adding a genuinely new complexity or statistical-performance theorem.
