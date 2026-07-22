/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the continuous-covariate version

The structure-agnostic lower bound (`ChiSquaredCore.minimax_lower_bound`) is
stated for a *finite* covariate `Fin K × Bool`, where the nuisances are constant on each
cell.  In the paper the covariate `X` is continuous and the nuisances are
*piecewise-constant* on cells.  The within-cell **position** of `X` is **ancillary**: its
conditional law given the cell is the *same* for every DGP in the class, so it carries no
information about the ATE.

We model the continuous experiment as the finite-cell `n`-sample law tensored with `n`
independent ancillary within-cell draws from an arbitrary probability space `(W, ρ)`:

  * null      `QfalseCont = Qfalse ⊗ ρ^⊗n`,
  * alternative `QtrueCont = Qtrue ⊗ ρ^⊗n`.

Tensoring both hypotheses with the **common** factor `ρ^⊗n` does not change the
χ²-divergence (`Causalean.Stat.chiSqDiv_prod_ancillary`: `χ²(μ⊗ρ‖ν⊗ρ) = χ²(μ‖ν)`), so the
finite-cell indistinguishability `χ²(Qtrue‖Qfalse) ≤ 1` transfers verbatim to the richer
continuous experiment (`chiSqDiv_QtrueCont_QfalseCont_le_one`).  The two-point method then
gives the identical `1/4` lower bound (`two_point_lower_bound_continuous`):
**no** estimator built from the continuous-covariate data can beat the doubly-robust
product rate, because the extra within-cell information is ancillary.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore

/-! # Continuous Covariates

This file lifts the finite-cell structure-agnostic ATE lower bound to a continuous-covariate
experiment with ancillary within-cell variation. The law `ancillaryLaw` models independent
within-cell draws, while `QfalseCont` and `QtrueCont` tensor that common ancillary factor with
the finite null and mixed alternative laws.

The probability-measure lemmas `QfalseCont_isProb` and `QtrueCont_isProb` set up the product
experiment. The theorem `chiSqDiv_QtrueCont_QfalseCont_le_one` transfers finite-cell
chi-squared indistinguishability through the common ancillary factor, and
`tvDist_QfalseCont_QtrueCont_le_half` gives the corresponding total-variation bound. The final
statement `two_point_lower_bound_continuous` is a two-hypothesis miss-probability lower bound
for estimators that observe both the finite cell data and ancillary continuous positions. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

variable {K n : ℕ} {α β : ℝ} {W : Type*} [MeasurableSpace W]

/-- Joint law of the ancillary within-cell positions in the `n`-sample experiment. -/
noncomputable def ancillaryLaw (ρ : Measure W) (n : ℕ) : Measure (Fin n → W) :=
  Measure.pi (fun _ => ρ)

/-- The ancillary `n`-sample law is a probability measure when the one-draw law is a probability
measure. -/
instance ancillaryLaw_isProb (ρ : Measure W) [IsProbabilityMeasure ρ] (n : ℕ) :
    IsProbabilityMeasure (ancillaryLaw ρ n) := by
  unfold ancillaryLaw; infer_instance

/-- Continuous-covariate null law, pairing the finite-cell null sample with ancillary
positions. -/
noncomputable def QfalseCont (K n : ℕ) [NeZero K] (ρ : Measure W) :
    Measure ((Fin n → Obs (Fin K × Bool)) × (Fin n → W)) :=
  (Qfalse K n).prod (ancillaryLaw ρ n)

/-- Continuous-covariate alternative law, pairing the finite-cell mixture with ancillary
positions. -/
noncomputable def QtrueCont [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + 2 * β ≤ 1 / 2)
    (n : ℕ) (ρ : Measure W) :
    Measure ((Fin n → Obs (Fin K × Bool)) × (Fin n → W)) :=
  (Qtrue hα hβ hαβ n).prod (ancillaryLaw ρ n)

/-- The continuous-covariate null law is a probability measure. -/
theorem QfalseCont_isProb [NeZero K] (ρ : Measure W) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (QfalseCont K n ρ) := by
  haveI : IsProbabilityMeasure (Qfalse K n) := Qfalse_isProb K n
  unfold QfalseCont; infer_instance

/-- The continuous-covariate alternative law is a probability measure in the valid parameter
regime. -/
theorem QtrueCont_isProb [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + 2 * β ≤ 1 / 2)
    (ρ : Measure W) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (QtrueCont (K := K) hα hβ hαβ n ρ) := by
  haveI : IsProbabilityMeasure (Qtrue (K := K) hα hβ hαβ n) := Qtrue_isProb hα hβ hαβ n
  unfold QtrueCont; infer_instance

/-- The continuous-covariate alternative is chi-squared close to the null in the finite-cell regime.

The common ancillary within-cell factor cancels, so the finite-cell indistinguishability bound
transfers verbatim. -/
theorem chiSqDiv_QtrueCont_QfalseCont_le_one [NeZero K] (ρ : Measure W) [IsProbabilityMeasure ρ]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hγ : 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ^ 2 ≤ (K : ℝ) * Real.log 2) :
    chiSqDiv (QtrueCont hα hβ hαβ n ρ) (QfalseCont K n ρ) ≤ 1 := by
  haveI : IsProbabilityMeasure (Qtrue (K := K) hα hβ hαβ n) := Qtrue_isProb hα hβ hαβ n
  haveI : IsProbabilityMeasure (Qfalse K n) := Qfalse_isProb K n
  have hac : Qtrue (K := K) hα hβ hαβ n ≪ Qfalse K n :=
    absolutelyContinuous_of_singleton_pos _ _ Qfalse_singleton_ne_zero
  unfold QtrueCont QfalseCont
  rw [chiSqDiv_prod_ancillary (Qtrue hα hβ hαβ n) (Qfalse K n) (ancillaryLaw ρ n) hac
    (Integrable.of_finite)]
  exact chiSqDiv_Qtrue_Qfalse_le_one hα hβ hαβ hγ hreg

/-- The squared density deviation for the continuous experiment is integrable under the null.

It is almost everywhere the finite-cell squared deviation pulled back through the first projection,
so finiteness of the cell space gives integrability. -/
theorem integrable_sq_rnDeriv_QtrueCont_QfalseCont [NeZero K] (ρ : Measure W)
    [IsProbabilityMeasure ρ] (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2) :
    Integrable
      (fun z => (((QtrueCont hα hβ hαβ n ρ).rnDeriv (QfalseCont K n ρ) z).toReal - 1) ^ 2)
      (QfalseCont K n ρ) := by
  haveI : IsProbabilityMeasure (Qtrue (K := K) hα hβ hαβ n) := Qtrue_isProb hα hβ hαβ n
  haveI : IsProbabilityMeasure (Qfalse K n) := Qfalse_isProb K n
  haveI : IsProbabilityMeasure (QfalseCont K n ρ) := QfalseCont_isProb ρ
  haveI : Nonempty (Fin K × Bool) := by
    haveI : NeZero K := ‹_›; exact ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩, true)⟩
  haveI : Nonempty (Fin n → Obs (Fin K × Bool)) := ⟨fun _ => Classical.arbitrary _⟩
  have hac : Qtrue (K := K) hα hβ hαβ n ≪ Qfalse K n :=
    absolutelyContinuous_of_singleton_pos _ _ Qfalse_singleton_ne_zero
  -- The finite-cell squared deviation `g`, on the finite type `Fin n → Obs (Fin K × Bool)`.
  set g : (Fin n → Obs (Fin K × Bool)) → ℝ :=
    fun x => (((Qtrue hα hβ hαβ n).rnDeriv (Qfalse K n) x).toReal - 1) ^ 2 with hg_def
  -- Product density factorizes: `dQtrueCont/dQfalseCont z = (dQtrue/dQfalse z.1)·(dρⁿ/dρⁿ z.2)`.
  have hfac : (QtrueCont hα hβ hαβ n ρ).rnDeriv (QfalseCont K n ρ)
      =ᵐ[QfalseCont K n ρ]
        fun z => (Qtrue hα hβ hαβ n).rnDeriv (Qfalse K n) z.1
                  * (ancillaryLaw ρ n).rnDeriv (ancillaryLaw ρ n) z.2 := by
    unfold QtrueCont QfalseCont
    exact rnDeriv_prod_eq (Qtrue hα hβ hαβ n) (Qfalse K n) (ancillaryLaw ρ n) (ancillaryLaw ρ n)
      hac (Measure.AbsolutelyContinuous.refl _)
  -- The ancillary self-density is a.e. `1`, lifted to the product via `snd`.
  have hself : (fun z : (Fin n → Obs (Fin K × Bool)) × (Fin n → W) =>
      (ancillaryLaw ρ n).rnDeriv (ancillaryLaw ρ n) z.2)
        =ᵐ[QfalseCont K n ρ] fun _ => (1 : ℝ≥0∞) := by
    have hsnd : MeasureTheory.Measure.QuasiMeasurePreserving
        (Prod.snd : (Fin n → Obs (Fin K × Bool)) × (Fin n → W) → (Fin n → W))
        (QfalseCont K n ρ) (ancillaryLaw ρ n) := by
      unfold QfalseCont
      exact Measure.quasiMeasurePreserving_snd
    exact hsnd.ae_eq_comp (g := fun w => (ancillaryLaw ρ n).rnDeriv (ancillaryLaw ρ n) w)
      (g' := fun _ => (1 : ℝ≥0∞)) (ancillaryLaw ρ n).rnDeriv_self
  -- Combine: the squared deviation a.e. equals `g ∘ fst`.
  have hae : (fun z => (((QtrueCont hα hβ hαβ n ρ).rnDeriv (QfalseCont K n ρ) z).toReal - 1) ^ 2)
      =ᵐ[QfalseCont K n ρ] fun z => g z.1 := by
    filter_upwards [hfac, hself] with z hz hz1
    rw [hz, hz1, mul_one, hg_def]
  refine Integrable.congr ?_ hae.symm
  -- `g ∘ fst` is measurable.
  have hgmeas : Measurable g :=
    (((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub measurable_const).pow_const 2)
  have hmeas : AEStronglyMeasurable (fun z => g z.1) (QfalseCont K n ρ) :=
    (hgmeas.comp measurable_fst).aestronglyMeasurable
  -- `g ≥ 0` (it's a square) and bounded by its finite max.
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max g
  refine (integrable_const (g x₀)).mono' hmeas (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hg_def]; positivity)]
  exact hx₀ z.1

/-- The continuous-covariate null and alternative are indistinguishable up to total variation
one half.

The ancillary within-cell positions do not help separate the two hypotheses. -/
theorem tvDist_QfalseCont_QtrueCont_le_half [NeZero K] (ρ : Measure W) [IsProbabilityMeasure ρ]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hγ : 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ^ 2 ≤ (K : ℝ) * Real.log 2) :
    tvDist (QfalseCont K n ρ) (QtrueCont hα hβ hαβ n ρ) ≤ 1 / 2 := by
  haveI : IsProbabilityMeasure (QtrueCont (K := K) hα hβ hαβ n ρ) :=
    QtrueCont_isProb (K := K) hα hβ hαβ ρ
  haveI : IsProbabilityMeasure (QfalseCont K n ρ) := QfalseCont_isProb ρ
  have hac : QtrueCont hα hβ hαβ n ρ ≪ QfalseCont K n ρ := by
    unfold QtrueCont QfalseCont
    exact (absolutelyContinuous_of_singleton_pos _ _ Qfalse_singleton_ne_zero).prod
      (Measure.AbsolutelyContinuous.refl _)
  have hint := integrable_sq_rnDeriv_QtrueCont_QfalseCont (K := K) (n := n) ρ hα hβ hαβ
  have hchi := chiSqDiv_QtrueCont_QfalseCont_le_one (K := K) (n := n) ρ hα hβ hαβ hγ hreg
  rw [tvDist_symm]
  calc tvDist (QtrueCont hα hβ hαβ n ρ) (QfalseCont K n ρ)
      ≤ (1 / 2) * Real.sqrt (chiSqDiv (QtrueCont hα hβ hαβ n ρ) (QfalseCont K n ρ)) :=
        tvDist_le_half_sqrt_chiSqDiv _ _ hac hint
    _ ≤ (1 / 2) * Real.sqrt 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.sqrt_le_sqrt hchi
    _ = 1 / 2 := by rw [Real.sqrt_one]; ring

/-- Every measurable estimator in the continuous-covariate experiment has the
same two-point lower bound.

The arbitrary within-cell ancillary space cannot improve estimation because it has the same law
under the null and alternative hypotheses. Formally this is a two-hypothesis
max-miss bound for the displayed null and alternative laws; it does not quantify
over a continuous nuisance class or invoke `minimaxMiss`. -/
theorem two_point_lower_bound_continuous [NeZero K]
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hγ : 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ^ 2 ≤ (K : ℝ) * Real.log 2)
    {est : ((Fin n → Obs (Fin K × Bool)) × (Fin n → W)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ max ((QtrueCont hα hβ hαβ n ρ).real
                {x | β * (α + β) / (1 - 4 * β ^ 2) ≤ |est x - 2 * β * (α + β) / (1 - 4 * β ^ 2)|})
              ((QfalseCont K n ρ).real
                {x | β * (α + β) / (1 - 4 * β ^ 2) ≤ |est x - 0|}) := by
  haveI : IsProbabilityMeasure (QtrueCont (K := K) hα hβ hαβ n ρ) :=
    QtrueCont_isProb (K := K) hα hβ hαβ ρ
  haveI : IsProbabilityMeasure (QfalseCont K n ρ) := QfalseCont_isProb ρ
  have hac : QtrueCont hα hβ hαβ n ρ ≪ QfalseCont K n ρ := by
    unfold QtrueCont QfalseCont
    exact (absolutelyContinuous_of_singleton_pos _ _ Qfalse_singleton_ne_zero).prod
      (Measure.AbsolutelyContinuous.refl _)
  have hint := integrable_sq_rnDeriv_QtrueCont_QfalseCont (K := K) (n := n) ρ hα hβ hαβ
  have hchi := chiSqDiv_QtrueCont_QfalseCont_le_one (K := K) (n := n) ρ hα hβ hαβ hγ hreg
  -- Separation `2s ≤ |θ₀ − θ₁|` with `θ₁ = 0`.
  have hsep : 2 * (β * (α + β) / (1 - 4 * β ^ 2))
      ≤ |2 * β * (α + β) / (1 - 4 * β ^ 2) - 0| := by
    have hβ4 : β ≤ 1 / 4 := by linarith
    have hden : (0 : ℝ) < 1 - 4 * β ^ 2 := by nlinarith
    have hnum : (0 : ℝ) ≤ 2 * β * (α + β) := by
      have : (0 : ℝ) ≤ α + β := by linarith
      positivity
    rw [sub_zero, abs_of_nonneg (div_nonneg hnum hden.le)]
    apply le_of_eq; ring
  have hkey := two_point_lower_bound_of_chiSqDiv_le (P₀ := QtrueCont hα hβ hαβ n ρ)
    (P₁ := QfalseCont K n ρ) hest (θ₀ := 2 * β * (α + β) / (1 - 4 * β ^ 2)) (θ₁ := 0)
    (s := β * (α + β) / (1 - 4 * β ^ 2)) hsep hac hint (c := 1) hchi
  -- `(1 - (1/2)·√1)/2 = 1/4`.
  have hval : (1 - (1 / 2) * Real.sqrt 1) / 2 = 1 / 4 := by
    rw [Real.sqrt_one]; norm_num
  rwa [hval] at hkey

end Causalean.Estimation.MinimaxATE
