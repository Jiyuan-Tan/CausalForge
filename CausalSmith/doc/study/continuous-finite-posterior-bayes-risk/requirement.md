# Substrate requirement: continuous-finite-posterior-bayes-risk

## Goal

Build a reusable native-real bridge from a continuous prior mixed through finite kernels to finite posterior squared-loss Bayes risk, including guarded posterior means, exact square completion, and transfer of an integrated risk lower bound.

## Provides (API contract)

- Joint, marginal, and posterior weights for finite latent-state and observation kernels under either a `FiniteDesign` prior or a continuous prior mixed into a finite design, with explicit zero-marginal guards.
- Exact finite-sum disintegration identities for the joint law and posterior numerator, including normalization on positive-mass observation fibers.
- A real posterior-mean estimator for a real target, and an exact squared-loss completion/Pythagorean identity for every estimator.
- A theorem identifying the infimum over all real estimators with the posterior residual Bayes risk; provide both finite-design and continuously mixed finite-kernel forms.
- Compatibility lemmas using `Causalean.Stat.inducedFiniteDesign` and `realBayesRisk_eq_inducedFiniteDesignBayesRisk`, so an integrated squared-error lower bound can be transferred to the corresponding native-real finite-design Bayes risk without `ENNReal`.

## Statement / milestones

For finite latent type `S` and finite observation type `X`, a normalized nonnegative finite prior `ν : FiniteDesign S`, a Markov observation kernel `L : S → X`, and a real target `t : S → X → ℝ` (allowing the target to depend on the observation), define

- `jointMass s x = ν.p s * L(s,{x})`,
- `observationMass x = ∑ s, jointMass s x`,
- a guarded posterior weight `jointMass s x / observationMass x`, zero when the marginal vanishes,
- the guarded posterior mean of `t s x`.

Prove nonnegativity, total mass one, positive-fiber posterior normalization, zero-fiber safety, and finite-sum disintegration. For every estimator `T : X → ℝ`, prove the exact identity

`risk(T) = posteriorResidual + ∑ x, observationMass x * (T x - posteriorMean x)^2`,

and deduce that the posterior mean minimizes squared risk and that the infimum over all estimators equals `posteriorResidual`.

Next take a probability measure `π` on a possibly continuous parameter type and a Markov kernel `K : Θ → S`. Reuse `Causalean.Stat.inducedFiniteDesign` to prove that mixing any finite-state/observation squared loss through `π` and `K` equals the same loss under the induced finite design. Provide a compositional theorem: if an observation-dependent continuous-prior integral is definitionally or provably equal to every estimator's induced finite risk and a generic van-Trees result lower-bounds that integral by `B`, then `B` is at most the finite-design Bayes-risk infimum. Keep the equality/compatibility premise explicit rather than assuming the desired Bayes-risk lower bound.

## Standard reference

This is finite Bayes conditioning and the conditional-mean projection theorem for squared loss. The square-completion identity is the finite form of conditional variance decomposition; integrating a finite Markov kernel against a prior and exchanging a finite sum with the integral gives the induced-prior identity.

## Intended reuse

The immediate consumer mixes a smooth scalar prior into a finite effect-count state, observes a finite binomial/count statistic, applies an observation-dependent van-Trees bound, and then lifts the resulting scalar Bayes lower bound to a finite schedule minimax game. The posterior and induced-design layer must remain generic for unrelated finite experiments.

## May assume / must derive

May assume finite latent and observation carriers; a valid `FiniteDesign` prior; valid Markov kernels; a probability measure for the continuous prior; real targets and estimators; standard measurability needed to form kernels/integrals; and a separately proved compatibility equality between a consumer's continuous integral and the generic mixed finite risk.

Must derive all joint/marginal/posterior normalization identities, guarded zero-fiber behavior, posterior numerator identity, exact square completion, posterior-mean optimality, the Bayes-risk infimum equality, continuous-mixture/induced-design interchange, and the order-theoretic transfer from a per-estimator integrated lower bound to the finite Bayes-risk infimum.

## Non-goals (optional)

- Do not define effect triples, Bernoulli/binomial masses, multiarm schedules, assignment mechanisms, bandwidths, asymptotic rates, or paper-specific constants.
- Do not import any `CausalSmith/*_Research` module or duplicate the existing `FiniteKernelBayes` mixture/minimax results.
- Do not assume the posterior-mean optimality conclusion, the desired Bayes-risk lower bound, or a minimax theorem as a hypothesis.
- No `sorry`, `admit`, `native_decide`, or custom axioms may remain.

## Known building blocks (optional)

- `Causalean.Stat.Minimax.FiniteKernelBayes`, especially `inducedFiniteDesign`, `inducedFiniteDesign_p`, `inducedFiniteDesign_expectedLoss_eq_mixedKernelLoss`, and `realBayesRisk_eq_inducedFiniteDesignBayesRisk`
- `Causalean.Stat.FiniteRaoBlackwell.Posterior`
- finite sums, `Measure.count`, `integral_finsetSum`, and elementary real square completion
- `Causalean.Stat.Limit.ObservationDependentVanTrees.Main`
