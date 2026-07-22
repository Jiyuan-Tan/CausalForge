/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — the sharp (calibrated) partial-identification set

The Zhao–Small–Bhattacharya bounds of `Bounds.lean` (the sup/inf of the candidate IPW mean over the
odds-ratio box `MSMSet Λ`) are valid but *not sharp*: the box ignores a restriction implied by the
observed data. As Dorn–Guo (2022) show, the only additional constraint a candidate complete propensity
`ẽ` must satisfy to be data-compatible is the **calibration** (balancing) identity

    E[ Z / ẽ | σ(X) ] = 1   a.e.

(the true complete propensity satisfies it by the tower property — it conditions on `Y(1)`). Imposing
it cuts the ambiguity set down to the **calibrated set** `MSMSetCalib Λ`, whose candidate-mean range is
the *sharp* partial-identification interval `[msmLowerCalib Λ, msmUpperCalib Λ]`.

This file establishes the sharp set and its two defining properties:
* it is **valid** — the estimand `E[Y(1)]` lies in the sharp interval (the truth `e₀` is calibrated and
  in the box, hence a feasible candidate), and
* it is **tighter** than the ZSB bound — `MSMSetCalib Λ ⊆ MSMSet Λ`, so the sharp interval is contained
  in the ZSB interval of `Bounds.lean`.

**Scope.** This characterizes the sharp identified *set* (Dorn–Guo Corollary on the variational
problems). The quantile-balancing, cutoff-selection, lower-bound, and Gaussian files downstream evaluate
these endpoints under their respective cutoff-existence and distributional hypotheses.
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.Setup

/-! # Sharp calibrated marginal-sensitivity set

This file defines the calibrated treated-arm MSM ambiguity set and proves its
basic validity properties. It introduces `Calibrated`, `MSMSetCalib`,
`msmUpperCalib`, and `msmLowerCalib`; proves that the true complete propensity is
calibrated and therefore belongs to the calibrated set when the MSM assumption
holds; proves validity of the sharp interval via `Y1mean_mem_Icc_calib`; and
shows that calibrated bounds are tighter than the uncalibrated ZSB bounds.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- **Calibration (data-compatibility).** A candidate complete propensity `ẽ` is *calibrated* if the
inverse-propensity weighting of the treatment indicator averages to one within every covariate
stratum: `E[ Z / ẽ | σ(X) ] = 1` a.e. This is the only restriction on `ẽ`
beyond the odds-ratio box implied by the observed-data distribution. -/
def Calibrated (etilde : P.Ω → ℝ) : Prop :=
  P.μ[fun ω => S.dVar.indicator true ω / etilde ω | S.sigmaX] =ᵐ[P.μ] (fun _ => 1)

/-- **The calibrated (sharp) MSM ambiguity set:** odds-ratio-box members that also satisfy
calibration. -/
def MSMSetCalib (Λ : ℝ) : Set (P.Ω → ℝ) :=
  { etilde | etilde ∈ S.MSMSet Λ ∧ S.Calibrated etilde }

/-- The **sharp upper bound:** the supremum of the candidate mean over the calibrated set. -/
noncomputable def msmUpperCalib (Λ : ℝ) : ℝ := sSup (S.candMean '' S.MSMSetCalib Λ)

/-- The **sharp lower bound:** the infimum of the candidate mean over the calibrated set. -/
noncomputable def msmLowerCalib (Λ : ℝ) : ℝ := sInf (S.candMean '' S.MSMSetCalib Λ)

/-- **The true complete propensity is calibrated.** `E[Z / e₀ | σ(X)] = 1` a.e., where
`e₀ = P[D=1 | σ(X, Y(1))]`. By the tower property (`σ(X) ⊆ σ(X, Y(1))`):
`E[Z/e₀ | σX] = E[ E[Z/e₀ | σ(X,Y(1))] | σX] = E[ (1/e₀)·E[Z|σ(X,Y(1))] | σX] = E[ e₀/e₀ | σX] = 1`.
Uses the same condExp pull-out + cancellation as the IPW bridge in `Setup.lean`. -/
theorem completeProp_calibrated
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hpos : ∀ᵐ ω ∂P.μ, 0 < S.completeProp ω)
    (hint : Integrable (fun ω => S.dVar.indicator true ω / S.completeProp ω) P.μ) :
    S.Calibrated S.completeProp := by
  classical
  set A : P.Ω → ℝ := S.dVar.indicator true with hA_def
  set e : P.Ω → ℝ := S.completeProp with he_def
  -- `σ(X) ≤ σ(X, Y(1))`.
  have hX_le : S.sigmaX ≤ S.sigmaXY1 := by
    rw [POBackdoorSystem.sigmaX, POBackdoorSystem.sigmaXY1]
    exact le_sup_left
  -- `1/e` is `σ(X,Y(1))`-strongly measurable (`e = condExp` is).
  have he_smeas : StronglyMeasurable[S.sigmaXY1] e := by
    rw [he_def]; exact stronglyMeasurable_condExp
  have hinv_smeas : StronglyMeasurable[S.sigmaXY1] (fun ω => 1 / e ω) :=
    (measurable_const.div he_smeas.measurable).stronglyMeasurable
  -- Integrability of `A` and `(1/e)·A` (= `A/e`).
  have hA_int : Integrable A P.μ := S.dVar.integrable_indicator true
  have hinvA_int : Integrable (fun ω => (1 / e ω) * A ω) P.μ := by
    refine hint.congr (Filter.Eventually.of_forall ?_)
    intro ω
    simp [hA_def, he_def, div_eq_inv_mul]
  -- Pull-out: `μ[(1/e)·A | σ(X,Y(1))] =ᵐ (1/e)·μ[A | σ(X,Y(1))] = (1/e)·e`.
  have he_cond : (P.μ[A | S.sigmaXY1]) = e := by rw [hA_def, he_def]; rfl
  have hpull :
      P.μ[fun ω => (1 / e ω) * A ω | S.sigmaXY1] =ᵐ[P.μ] (fun ω => (1 / e ω) * e ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaXY1) (μ := P.μ) hinv_smeas hinvA_int hA_int
    refine h.trans ?_
    rw [he_cond]
    rfl
  -- Cancel: `(1/e)·e = 1` a.e. from positivity.
  have hcancel : (fun ω => (1 / e ω) * e ω) =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hpos] with ω hω
    rw [he_def] at hω
    rw [he_def]
    field_simp
  -- So `μ[A/e | σ(X,Y(1))] =ᵐ 1`.
  have hinner : P.μ[fun ω => A ω / e ω | S.sigmaXY1] =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    have hrw : (fun ω => A ω / e ω) = (fun ω => (1 / e ω) * A ω) := by
      funext ω; rw [one_div, div_eq_inv_mul]
    rw [hrw]
    exact hpull.trans hcancel
  -- Tower: `μ[A/e | σX] =ᵐ μ[ μ[A/e | σ(X,Y(1))] | σX] =ᵐ μ[1 | σX] =ᵐ 1`.
  unfold POBackdoorSystem.Calibrated
  have htower :
      P.μ[fun ω => A ω / e ω | S.sigmaX]
        =ᵐ[P.μ] P.μ[P.μ[fun ω => A ω / e ω | S.sigmaXY1] | S.sigmaX] :=
    (MeasureTheory.condExp_condExp_of_le hX_le S.sigmaXY1_le).symm
  refine htower.trans ?_
  have hcongr :
      P.μ[P.μ[fun ω => A ω / e ω | S.sigmaXY1] | S.sigmaX]
        =ᵐ[P.μ] P.μ[(fun _ => (1 : ℝ)) | S.sigmaX] :=
    condExp_congr_ae hinner
  refine hcongr.trans ?_
  exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const S.sigmaX_le (1 : ℝ))

/-- The true complete propensity lies in the calibrated set when it satisfies MSM membership and
calibration. -/
theorem completeProp_mem_MSMSetCalib (Λ : ℝ)
    (hmem : S.completeProp ∈ S.MSMSet Λ) (hcalib : S.Calibrated S.completeProp) :
    S.completeProp ∈ S.MSMSetCalib Λ :=
  ⟨hmem, hcalib⟩

/-- **The sharp bound is valid:** `E[Y(1)]` lies in the calibrated (sharp) interval. -/
theorem Y1mean_mem_Icc_calib (Λ : ℝ)
    (hmem : S.completeProp ∈ S.MSMSetCalib Λ)
    (hbridge : S.candMean S.completeProp = S.Y1mean)
    (hbdd : BddBelow (S.candMean '' S.MSMSetCalib Λ))
    (hbdd' : BddAbove (S.candMean '' S.MSMSetCalib Λ)) :
    S.Y1mean ∈ Set.Icc (S.msmLowerCalib Λ) (S.msmUpperCalib Λ) := by
  have hmemImg : S.candMean S.completeProp ∈ S.candMean '' S.MSMSetCalib Λ :=
    Set.mem_image_of_mem _ hmem
  rw [Set.mem_Icc, ← hbridge]
  refine ⟨?_, ?_⟩
  · exact csInf_le hbdd hmemImg
  · exact le_csSup hbdd' hmemImg

/-- The calibrated set is a subset of the odds-ratio box. -/
theorem MSMSetCalib_subset (Λ : ℝ) : S.MSMSetCalib Λ ⊆ S.MSMSet Λ :=
  fun _ h => h.1

/-- **The sharp upper bound is tighter than the ZSB bound:** `msmUpperCalib Λ ≤ msmUpper Λ`. The
calibrated set is smaller, so its candidate-mean supremum can only decrease. -/
theorem msmUpperCalib_le_msmUpper (Λ : ℝ)
    (hne : (S.candMean '' S.MSMSetCalib Λ).Nonempty)
    (hbdd : BddAbove (S.candMean '' S.MSMSet Λ)) :
    S.msmUpperCalib Λ ≤ S.msmUpper Λ := by
  have hsub : S.MSMSetCalib Λ ⊆ S.MSMSet Λ := S.MSMSetCalib_subset Λ
  have himg : S.candMean '' S.MSMSetCalib Λ ⊆ S.candMean '' S.MSMSet Λ :=
    Set.image_mono hsub
  exact csSup_le_csSup hbdd hne himg

/-- **The sharp lower bound is tighter than the ZSB bound:** `msmLower Λ ≤ msmLowerCalib Λ`. -/
theorem msmLower_le_msmLowerCalib (Λ : ℝ)
    (hne : (S.candMean '' S.MSMSetCalib Λ).Nonempty)
    (hbdd : BddBelow (S.candMean '' S.MSMSet Λ)) :
    S.msmLower Λ ≤ S.msmLowerCalib Λ := by
  have hsub : S.MSMSetCalib Λ ⊆ S.MSMSet Λ := S.MSMSetCalib_subset Λ
  have himg : S.candMean '' S.MSMSetCalib Λ ⊆ S.candMean '' S.MSMSet Λ :=
    Set.image_mono hsub
  exact csInf_le_csInf hbdd hne himg

end POBackdoorSystem

end PO
end Causalean
