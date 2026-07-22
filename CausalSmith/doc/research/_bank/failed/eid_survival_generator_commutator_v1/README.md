---
qid: eid_survival_generator_commutator
spec: v1
topic: "Continuous-time illness-death separable-effects generator commutator. Hand object: states 0=healthy, 1=nonterminal event, 2=death; disease component A=[[-alpha,alpha,0],[0,0,0],[0,0,0]] and death component B=[[-beta,0,beta],[0,-gamma,gamma],[0,0,0]], giving [A,B]_{0,2}=alpha*(gamma-beta) and local death-probability discrepancy t^2*alpha*(gamma-beta)/2+o(t^2)."
novelty_target: flagship
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Stage -1.1 rejected the topic as already-solved: the hand object is the second-order noncommutativity term for two finite-state continuous-time Markov generators."
  - "The reviewer identified the proof as the standard Taylor/Baker-Campbell-Hausdorff expansion for exp(t(A+B)) - exp(tA)exp(tB), followed by direct substitution of the illness-death generators."
  - "Aalen-Johansen/product-integral theory already supplies the Markov multistate generator-to-transition-probability semantics."
  - "Separable-effects illness-death papers already supply the causal estimand layer, leaving only standard Markov-semigroup algebra plus separable-effect definition unfolding."
  # collapsed and why. Source: eid_survival_generator_commutator_v1_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  - "eid_survival_generator_commutator_v1_gaps.json: concise negative literature/anchor check for why the generator commutator is not a flagship causal-identification gap."
  - "eid_survival_generator_commutator_v1_pipeline.jsonl: exact Stage -1.1 already-solved verdict and suggested alternative directions."
  - "Hand matrix object A,B and coefficient alpha*(gamma-beta)/2: reusable only as a toy sanity check for future non-Markov or partially observed illness-death topics."
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a non-do-calculus survival/separable-effects topic using an explicit three-state continuous-time generator commutator as the nonroutine object. Stage -1.1 rejected it before proposal drafting because the claimed coefficient is already standard BCH/Markov-semigroup algebra once the primitive generators are known, and the causal layer is separable-effect definition reuse. A future retry would need partial observation, unknown generators, or a genuinely causal identification problem rather than computing a known generator commutator.
banked_on: "2026-05-25"
---

# eid_survival_generator_commutator / v1 â€” Failed

**Topic.** Continuous-time illness-death separable-effects generator commutator with an explicit three-state generator certificate.

**Novelty target.** flagship

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -1.1 already-solved rejection: the generator certificate is the standard BCH/Markov semigroup commutator term plus separable-effect definition unfolding, not an unresolved causal-identification gap.

## Key files

- `eid_survival_generator_commutator_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `eid_survival_generator_commutator_v1_proposal.tex` â€” final proposal version.
- `eid_survival_generator_commutator_v1.tex` â€” derivation note (if Stage 0 ran).
- `eid_survival_generator_commutator_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_survival_generator_commutator_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

Reflection:

- Pipeline bug: none in the meaningful attempt; Stage -1.1 cleanly rejected and removed the active heartbeat.
- Topic choice: failed the pre-anchor in practice; the concrete object was real but already solved by standard Markov semigroup algebra.
- Proposer angle quality: no D-1.2 proposal was reached because the topic itself was already-solved.
- Reviewer strictness: appropriate; the reviewer applied exactly the requested rejection rule for standard machinery.
- Solver/math weakness: none; this was a topic-selection failure before D0.
