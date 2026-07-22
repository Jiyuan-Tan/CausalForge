# Substrate requirement: measure_moment_residual_envelope

## Goal
The MEASURE-level sharp envelope for the L² residual of `y²` on `span{1,y}`: over all probability measures `μ` on `[0,1]` with fixed second moment `∫ y² dμ = v²`, the supremum of the residual `r(μ) = l2ResidualQuadratic μ` equals the closed-form `ρ(v)` and is ATTAINED (an `IsLUB`), by an explicit three-point law; plus the unique-interior-root property of the defining quartic.

## Provides (API contract)
- `rhoEnvelope (v : ℝ) : ℝ` — the closed form `ρ(v)` (reuse `Causalean.Stat.Nonparametric.MomentEnvelope.momentEnvelope` at the maximizing root).
- `rho_envelope_isLUB : IsLUB {r | ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∀ y ∈ … supp ⊆ [0,1]) ∧ ∫ y² dμ = v² ∧ r = l2ResidualQuadratic μ} (rhoEnvelope v)` — sup over admissible MEASURES = ρ(v), i.e. both the upper bound (r(μ) ≤ ρ(v) for every admissible μ) AND attainment by the extremal three-point measure.
- `interior_quartic_unique_root : ∃! μ_v ∈ Set.Ioo (v²) v, envelopeQuartic … μ_v = 0` — the unique interior root of the defining quartic (the FOC maximizer).
- `rho_envelope_attained : ∃ μ, IsProbabilityMeasure μ ∧ supp ⊆ [0,1] ∧ ∫ y² dμ = v² ∧ l2ResidualQuadratic μ = rhoEnvelope v` — the extremal three-point law realizing ρ(v).

## Statement / milestones
For `v ∈ (0,1)`, `q = v²`:
1. UPPER BOUND (measure-level): every probability measure μ on [0,1] with `∫ y² dμ = q` has `l2ResidualQuadratic μ ≤ ρ(v)` — bridge the measure-level `l2ResidualQuadratic` (= r(μ), from `L2ResidualQuadratic`) to `MomentEnvelope.momentResidual_le_envelope` (the moment-level bound) via the measure's moments.
2. ATTAINMENT: the explicit three-point law on `{0, x_v, 1}` (weights from `MomentEnvelope`) is admissible (prob measure, supp ⊆ [0,1], second moment q) and realizes `ρ(v)`.
3. IsLUB: 1+2 give `IsLUB … (ρ v)`.
4. Unique interior quartic root (reuse/lift `MomentEnvelope`'s FOC + strict monotonicity of the log-derivative).

## Standard reference
Hausdorff moment problem / extremal-measure (Markov–Krein) theory; the three-point extremal law is the classical optimizer for a moment-constrained residual. See Karlin–Studden, *Tchebycheff Systems*, or Shohat–Tamarkin, *The Problem of Moments*.

## Intended reuse
Consumed by the CausalSmith research run `stat_neyman_regret_minimax`: `rho_envelope_closed_form` / `oeq:closed-form-frontier` (the class-frontier `K = sup_ν κ_ν` closed form rests on ρ(v) being the measure-level sup, attained).

## May assume / must derive
May assume: `v ∈ (0,1)`. Must derive: the measure-level upper bound (from the moment-level `MomentEnvelope` result via the measure's moments), the attainment by the three-point law, the `IsLUB`, and the quartic-root uniqueness. REUSE `Causalean.Stat.Nonparametric.MomentEnvelope` (`momentEnvelope`, `momentResidual_le_envelope`, `momentEnvelope_hasDerivAt`, the extremal weights) and `Causalean.Stat.Nonparametric.L2ResidualQuadratic` (`l2ResidualQuadratic` = r(μ)); do NOT re-derive the moment-level algebra.

## Known building blocks
`Causalean.Stat.Nonparametric.MomentEnvelope`, `Causalean.Stat.Nonparametric.L2ResidualQuadratic`; `IsLUB`/`csSup`; three-point `Measure` construction (`Measure.sum`/weighted `dirac`).

## Target module
Causalean.Stat.Nonparametric.MeasureMomentResidualEnvelope
