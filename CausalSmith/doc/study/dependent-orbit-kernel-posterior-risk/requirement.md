# Substrate requirement: dependent-orbit-kernel-posterior-risk

## Goal

Build reusable native-real posterior-risk and conditional-barycenter bounds for finite experiments whose observation type depends on a finite design/allocation index.

## Provides (API contract)

- A dependent finite observation model with finite state type `Θ`, design index `B`, observation family `X : B → Type`, normalized nonnegative likelihood `P : Θ → ∀ b, X b → ℝ`, and real target `τ : Θ → ℝ`, compatible with `Causalean.Stat.Minimax.FiniteSquaredLoss`.
- For any finite prior on `Θ`, dependent predictive mass, predictive target numerator, guarded posterior mean, and posterior residual risk at each `b`, with exact finite-sum square completion.
- A theorem identifying each design-index posterior residual with the infimum over decisions on `X b`, and a theorem that the infimum over `b` of these residuals lower-bounds the dependent finite experiment's minimax value.
- A generic conditional-barycenter/Jensen layer: from nonnegative weights `w b x g`, occupancy equations `∑ g, w b x g = π.p b`, and grid values `γ g`, define the guarded barycenter decision and bound its risk by the corresponding randomized grid-action risk.
- A minimax-compatible upper-bound corollary: if the randomized grid-action risk is at most `u` statewise, then the dependent experiment's minimax value is at most `u`.
- Zero-design-mass and zero-predictive-mass fibers must be handled explicitly and safely; no full-support assumptions.

## Statement / milestones

Let `Θ` and `B` be finite and nonempty, with `X b` finite for every `b`. Assume

`P θ b x ≥ 0` and `∑ x, P θ b x = 1` for all `θ,b`,

and let `ν : FiniteDesign Θ`, `τ : Θ → ℝ`. Define

`predictiveMass b x = ∑ θ, ν.p θ * P θ b x`,

`predictiveTarget b x = ∑ θ, ν.p θ * P θ b x * τ θ`,

the guarded posterior mean `predictiveTarget / predictiveMass`, and the posterior residual at `b`. Prove, for every decision `δ : X b → ℝ`, the exact square-completion identity and hence posterior-residual optimality. Deduce a theorem of the form

```lean
sInf (Set.range posteriorResidual) ≤
  Causalean.Stat.minimaxValue
    (Causalean.Stat.Minimax.FiniteSquaredLoss.risk P τ)
```

or an equivalent API that composes directly with that risk. The proof must average the per-`b` posterior inequality under an arbitrary design; it must not assume the minimax conclusion.

For the upper layer, let `G` be finite, `γ : G → ℝ`, `π : FiniteDesign B`, and `w : ∀ b, X b → G → ℝ`, with `w ≥ 0` and `∑ g, w b x g = π.p b` for every `b,x`. Define the guarded conditional barycenter

`δ b x = if π.p b = 0 then d else (∑ g, γ g * w b x g) / π.p b`.

Prove for every state `θ` and target value `τ θ`:

```lean
∑ b, π.p b * ∑ x, P θ b x * (δ b x - τ θ)^2 ≤
  ∑ b, ∑ x, ∑ g, P θ b x * w b x g * (γ g - τ θ)^2
```

and derive the corresponding worst-case/minimax upper-bound corollary when the right side is uniformly bounded. If a bounded decision interval is part of the existing `FiniteSquaredLoss.Procedure`, also prove barycenter range preservation from bounds on `d` and `γ`.

## Standard reference

The lower layer is finite Bayesian decision theory: posterior mean minimizes squared loss, followed by averaging over a randomized design and the elementary fact that an average is at least the minimum component. The upper layer is conditional Jensen for a randomized finite action followed by statewise-to-minimax comparison.

## Intended reuse

The immediate consumer has allocation orbits `b` and dependent count observations `X b`; it identifies a rational posterior certificate with the lower theorem and a rational grid barycenter with the upper theorem. The module must remain generic for stratified experiments, adaptive finite observation families, and other dependent finite decision problems.

## May assume / must derive

May assume finite/nonempty carriers, likelihood nonnegativity and normalization, a valid finite prior/design, nonnegative barycenter weights, the occupancy equations, and an externally proved statewise randomized-action risk bound.

Must derive predictive normalization, zero-fiber safety, posterior square completion, posterior-mean optimality, the lower minimax transport, barycenter range preservation where needed, the dependent Jensen inequality, and the upper minimax transport. Use sigma types internally if useful, but expose dependent-family statements.

## Non-goals (optional)

- Do not define response schedules, allocation/count vectors, orbit likelihoods, `orbitGameValue`, `lowerCertificate`, rational grid programs, contrast constants, or paper-specific certificate formulas.
- Do not import any `CausalSmith/*_Research` module.
- Do not duplicate generic finite squared-loss saddle existence or rational LP duality.
- No `sorry`, `admit`, `native_decide`, or custom axioms may remain.

## Known building blocks (optional)

- `Causalean.Stat.Minimax.FiniteSquaredLoss.{Core,Mixing,Saddle}`
- `Causalean.Stat.Minimax.FinitePosteriorBayesRisk`
- `Causalean.Stat.FiniteRaoBlackwell.DesignPushforward`
- dependent sums (`Sigma`), finite sums, guarded division, and real square completion
