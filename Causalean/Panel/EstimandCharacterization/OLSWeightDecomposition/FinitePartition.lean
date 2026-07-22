/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Słoczyński (2022): finite-partition OLS weights with heterogeneous effects

Pure finite-cell algebra for the Słoczyński saturated-OLS weight formulas.
Formalizes:

* `prop:po-estimand-sloczynski-ols-finite-weights` — the saturated OLS
  estimand decomposes as `Σ ω_g τ_g`, `ω_g ∝ π_g p_g (1−p_g)`.
* `prop:po-estimand-sloczynski-ols-equal-groups` (finite half) — if every
  `p_g = 1/2`, the overlap weights collapse to the cell probabilities.
* `prop:po-estimand-sloczynski-ols-homogeneous` (saturated half) — if
  `τ` is constant, the OLS estimand is that constant.

The opposite-group ATT/ATU representation
(`ass:po-estimand-sloczynski-ols-opposite-group`,
`prop:po-estimand-sloczynski-ols-opposite-group`,
`prop:po-estimand-sloczynski-ols-equal-groups` ATT/ATU half,
`prop:po-estimand-sloczynski-ols-homogeneous` ATT/ATU half) is recorded
as a separate algebraic structure `OppositeGroupRepr`.

This file is pure finite-cell algebra. The symbols `π`, `p`, and `τ` stand for
cell probabilities, treated shares, and cell-level effects in the finite
partition. Their probability-space interpretation — including
`τ_g = E[Y(1)−Y(0) ∣ G=g]` built from potential outcomes under the finite-cell
bridge condition — is supplied by `bridge_finite_residualized_eq_overlap` in
`OverlapWeightedATE.lean`, where `partitionOf` instantiates this structure from
a probability space. See
`prop:po-estimand-sloczynski-ols-finite-weights` and
`Causalean/Panel/EstimandCharacterization/OLSWeightDecomposition/OverlapWeightedATE.lean`.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/sloczynski_ols_heterogeneous.md`.
Source LaTeX:
`doc/basic_concepts/po/estimand_characterization/sloczynski_ols_heterogeneous.tex`.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! # Słoczyński Finite Partition Algebra

This file formalizes the finite-cell algebra behind Słoczyński's saturated
ordinary least squares weights with heterogeneous treatment effects. It defines
`FinitePartition`, `cellOverlap`, `overlapWeight`, and
`overlapWeightedATE`, proves the normalized-weight identity
`finite_weights_eq_sum`, and records the equal-share and homogeneous-effect
collapses. It also defines `perTreatedWeight` and `perUntreatedWeight` for the
per-observation leverage interpretation, and `OppositeGroupRepr` for the
separate ATT/ATU opposite-group representation with the derived theorem
`represents`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace OLSWeightDecomposition

open Finset

/-- Słoczyński finite covariate partition. Carries cell probabilities
`π_g`, treatment shares `p_g`, and conditional treatment effects `τ_g`,
together with the side conditions used by the saturated-OLS algebra:
`π` is a probability vector, `p_g ∈ [0,1]`, and the overlap denominator
`Σ π_g p_g (1−p_g)` is positive. -/
structure FinitePartition (𝒢 : Type*) [Fintype 𝒢] where
  /-- Cell probability `π_g = ℙ(G=g)`. -/
  π : 𝒢 → ℝ
  /-- Within-cell treated share `p_g = ℙ(D=1 ∣ G=g)`. -/
  p : 𝒢 → ℝ
  /-- Within-cell conditional treatment effect `τ_g = E[Y(1)−Y(0) ∣ G=g]`. -/
  τ : 𝒢 → ℝ
  /-- `π` takes nonnegative values. -/
  π_nonneg : ∀ g, 0 ≤ π g
  /-- `π` sums to 1. -/
  π_sum_one : ∑ g, π g = 1
  /-- Treatment shares are nonnegative. -/
  p_nonneg : ∀ g, 0 ≤ p g
  /-- Treatment shares are at most 1. -/
  p_le_one : ∀ g, p g ≤ 1
  /-- Saturated-overlap relevance: `Σ π_g p_g (1−p_g) > 0`. -/
  overlap_pos : 0 < ∑ g, π g * (p g * (1 - p g))

namespace FinitePartition

/-- Within-cell treatment variance `p_g (1 − p_g)`. -/
def cellOverlap {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢) (g : 𝒢) : ℝ :=
  P.p g * (1 - P.p g)

/-- Numerator `Σ_g π_g · p_g (1−p_g) · τ_g` of the saturated-OLS estimand
in finite-cell form. -/
def overlapNumerator {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢) : ℝ :=
  ∑ g, P.π g * P.cellOverlap g * P.τ g

/-- Denominator `Σ_g π_g · p_g (1−p_g)` of the saturated-OLS estimand
in finite-cell form. Positive by `overlap_pos`. -/
def overlapDenominator {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢) : ℝ :=
  ∑ g, P.π g * P.cellOverlap g

/-- Normalized weight `ω_g = π_g p_g (1−p_g) / Σ_h π_h p_h (1−p_h)`. -/
noncomputable def overlapWeight {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) : ℝ :=
  (P.π g * P.cellOverlap g) / P.overlapDenominator

/-- Saturated-OLS estimand in finite-cell form,
`β_sat = (Σ π·p(1−p)·τ) / (Σ π·p(1−p))`. -/
noncomputable def overlapWeightedATE {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) : ℝ :=
  P.overlapNumerator / P.overlapDenominator

variable {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢)

/-- The denominator is positive. Restated from `overlap_pos`. -/
theorem overlapDenominator_pos : 0 < P.overlapDenominator := by
  simpa [overlapDenominator, cellOverlap, mul_assoc] using P.overlap_pos

/-- The overlap weights sum to one. Direct from positivity of the
denominator and pulling the common denominator out of the sum. -/
theorem omega_sum_eq_one : ∑ g, P.overlapWeight g = 1 := by
  have hD : P.overlapDenominator ≠ 0 := P.overlapDenominator_pos.ne'
  have hsum : ∑ g, P.overlapWeight g = P.overlapDenominator / P.overlapDenominator := by
    simp [overlapWeight, overlapDenominator, Finset.sum_div]
  rw [hsum, div_self hD]

/-- **Finite-partition OLS weights**
(`prop:po-estimand-sloczynski-ols-finite-weights`). The saturated-OLS
estimand equals `Σ ω_g τ_g` with the normalized overlap weights. -/
theorem finite_weights_eq_sum :
    P.overlapWeightedATE = ∑ g, P.overlapWeight g * P.τ g := by
  simp only [overlapWeightedATE, overlapNumerator, overlapWeight, Finset.sum_div]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  ring

/-- Equal-cell-share weight collapse: if `p_g = 1/2` for every cell, the
normalized overlap weight reduces to the cell probability `π_g`. -/
theorem equal_groups_weight_eq_pi
    (h : ∀ g, P.p g = 1 / 2) (g : 𝒢) :
    P.overlapWeight g = P.π g := by
  have hcell : ∀ g', P.cellOverlap g' = (1 : ℝ) / 4 := by
    intro g'
    simp [cellOverlap, h g']
    ring
  have hden : P.overlapDenominator = (1 : ℝ) / 4 := by
    have hsum : ∑ g', P.π g' * P.cellOverlap g' = ∑ g', P.π g' * ((1 : ℝ)/4) := by
      refine Finset.sum_congr rfl (fun g' _ => ?_)
      rw [hcell g']
    rw [overlapDenominator, hsum, ← Finset.sum_mul, P.π_sum_one, one_mul]
  simp [overlapWeight, hcell, hden]

/-- **Equal-cell-share collapse to unweighted average**
(finite half of `prop:po-estimand-sloczynski-ols-equal-groups`).
If every cell has `p_g = 1/2`, then
`β_sat = Σ π_g τ_g`. -/
theorem equal_groups_collapses
    (h : ∀ g, P.p g = 1 / 2) :
    P.overlapWeightedATE = ∑ g, P.π g * P.τ g := by
  rw [P.finite_weights_eq_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [P.equal_groups_weight_eq_pi h g]

/-- **Homogeneous-effect collapse**
(saturated half of `prop:po-estimand-sloczynski-ols-homogeneous`).
If `τ_g = τ₀` for every cell, then `β_sat = τ₀`. -/
theorem homogeneous_collapses
    {τ₀ : ℝ} (h : ∀ g, P.τ g = τ₀) :
    P.overlapWeightedATE = τ₀ := by
  have hD : P.overlapDenominator ≠ 0 := P.overlapDenominator_pos.ne'
  have hnum : P.overlapNumerator = τ₀ * P.overlapDenominator := by
    simp only [overlapNumerator, overlapDenominator, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [h g]; ring
  rw [overlapWeightedATE, hnum, mul_div_assoc, div_self hD, mul_one]

/-- **Per-treated-observation leverage factor** in cell `g`.

The paper (Słoczyński 2022, Remark `rem:po-estimand-sloczynski-ols-group-size`)
notes that in the overlap-weighted OLS formula each treated observation in
cell `g` contributes a leverage factor of `1 − p_g` (the untreated share),
while each untreated observation contributes `p_g` (the treated share).
This definition makes the first factor explicit; see
`perTreatedWeight_antitone`, `perUntreatedWeight_monotone`, and
`cellOverlap_eq_perWeights_mul` for the main monotonicity claims. -/
noncomputable def perTreatedWeight {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) : ℝ := 1 - P.p g

/-- **Per-untreated-observation leverage factor** in cell `g`.

Each untreated observation in cell `g` contributes a leverage factor of
`p_g` (the treated share). Cells with more treated units (high `p_g`) give
each untreated unit a larger per-observation weight; cells with fewer
treated units (low `p_g`) give each untreated unit a smaller weight.
See `perUntreatedWeight_monotone`. -/
noncomputable def perUntreatedWeight {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) : ℝ := P.p g

/-- The cell overlap variance is the product of the two per-observation
leverage factors: `p_g (1−p_g) = perUntreatedWeight_g · perTreatedWeight_g`.
This links the finite-cell denominator directly to the paper's per-unit
weight interpretation. -/
theorem cellOverlap_eq_perWeights_mul {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) :
    P.cellOverlap g = P.perUntreatedWeight g * P.perTreatedWeight g := by
  unfold cellOverlap perUntreatedWeight perTreatedWeight
  ring

/-- **Headline monotonicity — smaller treated group gets larger per-treated weight**
(`rem:po-estimand-sloczynski-ols-group-size`).

The per-treated-observation leverage factor `1 − p_g` is *antitone* in
`p_g`: if cell `g` has a higher treated share than cell `h` (i.e. `p_g ≤ p_h`),
then each treated unit in `g` carries a larger leverage factor than each
treated unit in `h` (`perTreatedWeight P h ≤ perTreatedWeight P g`).

In words: the *minority* treatment-status group in a cell receives the
larger per-observation weight. A cell where almost everyone is treated
(`p_g ≈ 1`) downweights each treated observation to near 0; a cell where
almost no one is treated (`p_g ≈ 0`) upweights each treated observation
toward 1.

This formalizes the paper's title insight ("Smaller Groups Get Larger
Weights") for the treated side. -/
theorem perTreatedWeight_antitone {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) {g h : 𝒢}
    (hph : P.p g ≤ P.p h) :
    P.perTreatedWeight h ≤ P.perTreatedWeight g := by
  simp only [perTreatedWeight]
  linarith

/-- **Monotonicity — larger treated group gives larger per-untreated weight**
(`rem:po-estimand-sloczynski-ols-group-size`, untreated side).

The per-untreated-observation leverage factor `p_g` is *monotone* in `p_g`:
if cell `g` has a lower treated share than cell `h` (i.e. `p_g ≤ p_h`),
then each untreated unit in `h` carries a larger leverage factor than each
untreated unit in `g` (`perUntreatedWeight P g ≤ perUntreatedWeight P h`).

Symmetrically to `perTreatedWeight_antitone`: the minority
untreated group in a cell receives the larger per-observation weight. -/
theorem perUntreatedWeight_monotone {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) {g h : 𝒢}
    (hph : P.p g ≤ P.p h) :
    P.perUntreatedWeight g ≤ P.perUntreatedWeight h := by
  simp only [perUntreatedWeight]
  exact hph

end FinitePartition

/-- Słoczyński's two-component ATT/ATU representation
(`ass:po-estimand-sloczynski-ols-opposite-group`).

The conventional (single-dummy) OLS treatment coefficient is *assumed* to
admit Słoczyński's two-component causal representation
`β_ols = w₁·τ_ATT + w₀·τ_ATU` with `w₁ + w₀ = 1` (field `twoComponent`,
`weights_sum_one`). This is the paper's genuine structural assumption: per
`rem:po-estimand-sloczynski-ols-no-covariate-caveat` it is recorded
*separately* and must NOT be derived from the saturated-overlap formula
(`β_sat = Σ ω_g τ_g`), which is a different, non-saturated estimand — they
disagree numerically in general. The **equal-dispersion** case then imposes
the opposite-group weight `w₁ = 1 − ρ` (field `equalDispersion`); `w₀ = ρ`
follows from `weights_sum_one` (lemma `w0_eq_rho`).

The opposite-group identity `β_ols = (1−ρ)·τ_ATT + ρ·τ_ATU`
is not a structure field: it is the *derived* theorem `represents`,
matching Proposition `prop:po-estimand-sloczynski-ols-opposite-group`, whose
proof is exactly the substitution `w₁ = 1−ρ`, `w₀ = ρ` into the two-component
representation. The general weight formula in terms of conditional
treatment-variance dispersion is not specified by the source and so is not
formalized; the equal-dispersion weights are the substantive content the
paper highlights. -/
structure OppositeGroupRepr where
  /-- Treated share `ρ = ℙ(D=1)`. -/
  ρ : ℝ
  /-- ATT, `τ_ATT = E[Y(1)−Y(0) | D=1]`. -/
  τ_ATT : ℝ
  /-- ATU, `τ_ATU = E[Y(1)−Y(0) | D=0]`. -/
  τ_ATU : ℝ
  /-- OLS coefficient on `D`. -/
  β_ols : ℝ
  /-- General two-component weight on `τ_ATT`. -/
  w₁ : ℝ
  /-- General two-component weight on `τ_ATU`. -/
  w₀ : ℝ
  /-- `ρ` is a probability — nonnegative side. -/
  ρ_nonneg : 0 ≤ ρ
  /-- `ρ` is a probability — `≤ 1` side. -/
  ρ_le_one : ρ ≤ 1
  /-- **Structural assumption** (Słoczyński two-component representation,
  `ass:po-estimand-sloczynski-ols-opposite-group`): the OLS coefficient is a
  convex-style combination of the group-status effects. This is genuinely
  weaker than the opposite-group conclusion — it does not fix the weights. -/
  twoComponent : β_ols = w₁ * τ_ATT + w₀ * τ_ATU
  /-- The two weights sum to one. -/
  weights_sum_one : w₁ + w₀ = 1
  /-- **Equal-dispersion specialization**: the ATT weight equals the untreated
  share `1 − ρ` (`ass:po-estimand-sloczynski-ols-opposite-group`). -/
  equalDispersion : w₁ = 1 - ρ

namespace OppositeGroupRepr

/-- ATE expressed as `ρ τ_ATT + (1−ρ) τ_ATU`
(`def:po-estimand-sloczynski-ols-att-atu`). -/
def tau_ATE (R : OppositeGroupRepr) : ℝ := R.ρ * R.τ_ATT + (1 - R.ρ) * R.τ_ATU

variable (R : OppositeGroupRepr)

/-- The untreated weight in the equal-dispersion case is the treated share `ρ`,
forced by `w₁ + w₀ = 1` and `w₁ = 1 − ρ`. -/
theorem w0_eq_rho : R.w₀ = R.ρ := by
  have h := R.weights_sum_one
  rw [R.equalDispersion] at h; linarith

/-- **Słoczyński opposite-group identity**
(`prop:po-estimand-sloczynski-ols-opposite-group`) — derived rather than
assumed. Substituting the equal-dispersion weights `w₁ = 1−ρ`, `w₀ = ρ`
into the two-component representation gives
`β_ols = (1−ρ)·τ_ATT + ρ·τ_ATU`: the treated-group effect receives the
untreated share as its weight, and vice versa. -/
theorem represents : R.β_ols = (1 - R.ρ) * R.τ_ATT + R.ρ * R.τ_ATU := by
  rw [R.twoComponent, R.equalDispersion, R.w0_eq_rho]

/-- **Equal-group-size collapse to the ATE**
(top half of `prop:po-estimand-sloczynski-ols-equal-groups`).
If `ρ = 1/2`, the opposite-group OLS coefficient equals the ATE. -/
theorem equal_groups_eq_ATE (h : R.ρ = 1 / 2) :
    R.β_ols = R.tau_ATE := by
  rw [R.represents, tau_ATE, h]; ring

/-- **Homogeneous-effect collapse for the opposite-group representation**
(ATT/ATU half of `prop:po-estimand-sloczynski-ols-homogeneous`).
If `τ_ATT = τ_ATU = τ₀`, then `β_ols = τ₀` regardless of `ρ`. -/
theorem homogeneous_eq_constant
    {τ₀ : ℝ} (hT : R.τ_ATT = τ₀) (hU : R.τ_ATU = τ₀) :
    R.β_ols = τ₀ := by
  rw [R.represents, hT, hU]; ring

end OppositeGroupRepr

end OLSWeightDecomposition
end Panel.EstimandCharacterization
end Causalean
