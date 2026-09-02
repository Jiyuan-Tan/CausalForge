# Substrate requirement: finite-smooth-effect-prior-bayes-information

## Goal

Build a reusable smooth compactly supported scalar prior and finite-experiment information-calculus layer that supplies explicit native-real Bayes-risk lower bounds through observation-dependent van Trees.

## Provides (API contract)

- A concrete one-parameter family of nonnegative compactly supported `C¹` probability densities on a bounded real interval, together with an explicit derivative representative.
- Proofs of normalization, support strictly inside a chosen ambient interval, endpoint vanishing, positivity on the support interior, absolute continuity, and all prior-score measurability/integrability facts needed by `Causalean.Stat.Limit.ObservationDependentVanTrees`.
- An exact formula or explicit reusable upper bound for the prior Fisher information under scaling; in particular expose a form bounded by `40 / a^2` for a positive bandwidth `a`.
- Finite-sum helpers for a finite dominated experiment: likelihood normalization and derivative-centering, guarded likelihood score, Fisher information as a finite real sum, and integration of a pointwise Fisher bound against the smooth prior.
- A theorem assembling a lower bound of the form `sensitivityLower^2 / (likelihoodInfoUpper + priorInfoUpper)` from verified observation-dependent van-Trees regularity, plus a convenient specialization using the canonical scaled prior. The API must compose with `Causalean.Stat.Minimax.FiniteKernelBayes` without `ENNReal` conversion.

## Statement / milestones

For every bandwidth `a > 0`, define an explicit polynomial or standard smooth bump density `w_a` and derivative `dw_a`, supported in a compact subinterval of a declared ambient interval. Prove that its integral is one, that it is nonnegative and `C¹`, that its topological support and endpoint behavior satisfy the observation-dependent van-Trees hypotheses, and that its guarded prior-score square is integrable. Calculate its scale law and prove `priorInformation w_a dw_a ≤ 40 / a^2` (an exact smaller constant is welcome when it implies this bound).

For a finite observation type with counting measure and likelihood mass `p θ x` with derivative representative `dp θ x`, prove reusable finite-sum forms of density normalization, derivative centering, and Fisher information. From a pointwise bound `fisherInformation p dp θ ≤ I` on the prior support, derive the prior-averaged likelihood-information bound `≤ I`.

Finally, package the analytic bookkeeping around `Causalean.Stat.Limit.ObservationDependentVanTrees.observation_dependent_van_trees`: given the model-specific likelihood/target absolute-continuity identities and verified joint finite-sum integrability, a sensitivity integral lower bound `s`, a likelihood-information upper bound `I`, and positivity of the denominator, conclude a native-real Bayes squared-risk lower bound at least `s^2 / (I + 40 / a^2)`. The theorem must not assume the desired Bayes-risk conclusion or any minimax claim.

## Standard reference

The construction is the classical compactly supported beta/polynomial test prior used in the van Trees (Bayesian Cramér--Rao) inequality. Scaling a fixed density gives Fisher information proportional to the inverse squared bandwidth; finite dominated experiments reduce all likelihood-information identities to finite sums.

## Intended reuse

The immediate consumer uses bandwidth on the order of `n^(-1/3)`, a finite scalar effect experiment, an observation-dependent target, and then transfers the resulting real Bayes lower bound through the already promoted finite-kernel and Rao--Blackwell bridges. The prior, scaling law, finite-information lemmas, and van-Trees assembly must remain useful for unrelated finite experiments.

## May assume / must derive

May assume a positive bandwidth; a finite observation carrier; model-specific likelihood and target functions with their derivative representatives; the absolute-continuity/differentiation hypotheses genuinely belonging to that model; explicit finite-sum integrability hypotheses when not automatic; a proved pointwise likelihood-information upper bound; and a proved sensitivity lower bound.

Must derive the concrete prior's normalization, nonnegativity, compact support, endpoint behavior, positivity on its support interior, derivative identity, absolute continuity, prior-score integrability, and Fisher-information scale bound. Must also derive the finite counting-measure normalization/centering and averaged-information consequences from their primitive finite-sum hypotheses, and derive the stated Bayes-risk fraction from the promoted observation-dependent van-Trees theorem and the supplied upper/lower bounds.

## Non-goals (optional)

- Do not define multiarm schedules, effect triples, response types, assignment mechanisms, contrasts, binomial fiber counts, asymptotic rates, or the paper's `rho2` minimax value.
- Do not bake the paper's `n`, `n^(-1/3)`, `1 - n^(-1/3)`, or `n / (1 - n^(-2/3)/4)` expressions into the generic headline; those are consumer-side instantiations.
- Do not import any `CausalSmith/*_Research` module or assume a Bayes/minimax lower-bound conclusion.
- No `sorry`, `admit`, `native_decide`, or custom axioms may remain.

## Known building blocks (optional)

- `Causalean.Stat.Limit.ObservationDependentVanTrees.{Basic,IntegrationByParts,GuardedInformation,WeightedL2,Main}`
- `Causalean.Stat.Minimax.FiniteKernelBayes`
- interval integrals, polynomial derivatives, compact support, and `AbsolutelyContinuousOnInterval` from Mathlib
- counting measure and finite-sum integral identities
