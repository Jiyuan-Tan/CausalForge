/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.CLT

/-!
# Centered/normalized network field for a super-population mean

To make the abstract m-dependent network CLT (`networkSum_clt`) usable for a concrete *mean*-type
estimand we must first turn raw network-dependent outcomes `Y i : Ω → ℝ` (with a common mean and a
positive sum-variance `s² = Var(∑ᵢ Yᵢ)`) into a `NetworkDependence` field whose summand is the
*standardized* contribution `Xᵢ = (Yᵢ − E[Yᵢ]) / s`.  This file performs that construction.

The only nontrivial field obligation is `indep`: the standardized tuple `fun k ∈ A => Xₖ` is an
affine, measurable function of the outcome tuple `fun k ∈ A => Yₖ`, so the outcome-level
m-dependence (non-adjacent outcome tuples independent) transfers to the standardized field by
`IndepFun.comp`.  The remaining structure data (the reflexive/symmetric network and measurability)
is inherited verbatim from the outcome-level hypotheses.

The three field hypotheses required by `networkSum_clt` — mean-zero, unit total variance, and the
uniform summand bound — are *derived* (not re-assumed) in `Hypotheses.lean`; the final CLT corollary
`networkMean_clt` lives in `MeanCLT.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace Causalean.Experimentation.SuperPopulation.MeanCLT

open Causalean.Experimentation.SuperPopulation Causalean.SteinMethod

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ω] {μ : Measure Ω}
variable (Y : V → Ω → ℝ) (adj : V → V → Prop) [DecidableRel adj]
variable (hrefl : ∀ i, adj i i) (hsymm : ∀ i j, adj i j → adj j i)
variable (hmeasY : ∀ i, Measurable (Y i))
variable (hindepY : ∀ A B : Finset V, (∀ a ∈ A, ∀ b ∈ B, ¬ adj a b) →
    IndepFun (fun ω => fun k : A => Y k ω) (fun ω => fun k : B => Y k ω) μ)

/-- The **centered/normalized network field** for a super-population mean.  From raw outcomes
`Y i : Ω → ℝ` carrying a reflexive/symmetric measurable m-dependent network and a normalizer `s`
(intended `s = √Var(∑ᵢ Yᵢ)`), build the `NetworkDependence` whose summand is the standardized
contribution `Xᵢ = (Yᵢ − E[Yᵢ]) / s`.

The network relation, its decidability, reflexivity, symmetry, and the per-summand measurability are
inherited from the outcome-level data.  The independence field (non-adjacent standardized tuples are
independent) is *transferred* from the outcome m-dependence `hindepY` via `IndepFun.comp`, because
each standardized tuple `fun k ∈ A => Xₖ` is the affine measurable image
`v ↦ fun k => (v k − E[Yₖ])/s` of the outcome tuple `fun k ∈ A => Yₖ`. -/
noncomputable def centeredNormalizedField (s : ℝ) : NetworkDependence V Ω μ where
  X i ω := (Y i ω - ∫ x, Y i x ∂μ) / s
  adj := adj
  decAdj := inferInstance
  refl := hrefl
  symm := hsymm
  meas i := ((hmeasY i).sub measurable_const).div_const s
  indep A B hAB := by
    -- Transfer the outcome m-dependence through the affine measurable standardization map
    -- `v ↦ fun k => (v k − E[Yₖ]) / s` via `IndepFun.comp`.
    have h := hindepY A B hAB
    let φ : (A → ℝ) → (A → ℝ) := fun v k => (v k - ∫ x, Y (k : V) x ∂μ) / s
    let ψ : (B → ℝ) → (B → ℝ) := fun v k => (v k - ∫ x, Y (k : V) x ∂μ) / s
    have hφ : Measurable φ := by
      exact measurable_pi_lambda φ fun k => by
        have hc : Measurable (fun _ : A → ℝ => ∫ x, Y (k : V) x ∂μ) :=
          measurable_const
        simpa [φ] using
          ((measurable_pi_apply k).sub hc).div_const s
    have hψ : Measurable ψ := by
      exact measurable_pi_lambda ψ fun k => by
        have hc : Measurable (fun _ : B → ℝ => ∫ x, Y (k : V) x ∂μ) :=
          measurable_const
        simpa [ψ] using
          ((measurable_pi_apply k).sub hc).div_const s
    simpa only [φ, ψ, Function.comp] using h.comp hφ hψ

/-- Defining unfolding of the standardized summand: the `X` field of `centeredNormalizedField`
evaluated at unit `i` and sample `ω` is `(Yᵢ ω − E[Yᵢ]) / s`. -/
@[simp] theorem centeredNormalizedField_X (s : ℝ) (i : V) (ω : Ω) :
    (centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).X i ω
      = (Y i ω - ∫ x, Y i x ∂μ) / s := rfl

/-- The network relation of `centeredNormalizedField` is the supplied outcome network `adj`. -/
@[simp] theorem centeredNormalizedField_adj (s : ℝ) :
    (centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).adj = adj := rfl

end Causalean.Experimentation.SuperPopulation.MeanCLT
