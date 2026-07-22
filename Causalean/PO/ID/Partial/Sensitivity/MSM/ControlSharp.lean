/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — the sharp (calibrated) set for the control mean `E[Y(0)]`

The `D=0` reflection of `Sharp.lean`. The data-compatibility constraint cutting the
ZSB box `MSMSet0 Λ` down to the sharp identified set is the **calibration** identity

    E[ (1−Z) / ẽ | σ(X) ] = 1   a.e.

(the true complete control propensity satisfies it by the tower property — it
conditions on `Y(0)`). This file establishes the calibrated set `MSMSetCalib0 Λ`,
its validity (`E[Y(0)]` lies in the sharp interval), and that it is tighter than the
ZSB control interval of `ControlSetup.lean`. Feeds the ATE interval (`ATE.lean`).
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlSetup

/-! # Sharp marginal-sensitivity set for the control mean

This file mirrors the treated-arm sharp MSM construction for `E[Y(0)]`. It
defines the calibrated control ambiguity set, proves that the true control mean
lies in the resulting sharp interval, and relates the calibrated set to the
wider uncalibrated control box.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- **Calibration (control arm).** A candidate complete control propensity `ẽ` is
*calibrated* if `E[ (1−Z) / ẽ | σ(X) ] = 1` a.e., where `1−Z = 1_{D=0}`. -/
def Calibrated0 (etilde : P.Ω → ℝ) : Prop :=
  P.μ[fun ω => S.dVar.indicator false ω / etilde ω | S.sigmaX] =ᵐ[P.μ] (fun _ => 1)

/-- **The calibrated (sharp) control MSM ambiguity set.** -/
def MSMSetCalib0 (Λ : ℝ) : Set (P.Ω → ℝ) :=
  { etilde | etilde ∈ S.MSMSet0 Λ ∧ S.Calibrated0 etilde }

/-- The **sharp control upper bound:** the supremum of the candidate mean over the
calibrated set. -/
noncomputable def msmUpperCalib0 (Λ : ℝ) : ℝ := sSup (S.candMean0 '' S.MSMSetCalib0 Λ)

/-- The **sharp control lower bound:** the infimum of the candidate mean over the
calibrated set. -/
noncomputable def msmLowerCalib0 (Λ : ℝ) : ℝ := sInf (S.candMean0 '' S.MSMSetCalib0 Λ)

/-- **The true complete control propensity is calibrated.** `E[(1−Z) / e₀ | σ(X)] = 1`
a.e., where `e₀ = P[D=0 | σ(X, Y(0))]`. The `D=0` reflection of `completeProp_calibrated`. -/
theorem completeProp0_calibrated
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hpos : ∀ᵐ ω ∂P.μ, 0 < S.completeProp0 ω)
    (hint : Integrable (fun ω => S.dVar.indicator false ω / S.completeProp0 ω) P.μ) :
    S.Calibrated0 S.completeProp0 := by
  classical
  set A : P.Ω → ℝ := S.dVar.indicator false with hA_def
  set e : P.Ω → ℝ := S.completeProp0 with he_def
  have hX_le : S.sigmaX ≤ S.sigmaXY0 := by
    rw [POBackdoorSystem.sigmaX, POBackdoorSystem.sigmaXY0]
    exact le_sup_left
  have he_smeas : StronglyMeasurable[S.sigmaXY0] e := by
    rw [he_def]; exact stronglyMeasurable_condExp
  have hinv_smeas : StronglyMeasurable[S.sigmaXY0] (fun ω => 1 / e ω) :=
    (measurable_const.div he_smeas.measurable).stronglyMeasurable
  have hA_int : Integrable A P.μ := S.dVar.integrable_indicator false
  have hinvA_int : Integrable (fun ω => (1 / e ω) * A ω) P.μ := by
    refine hint.congr (Filter.Eventually.of_forall ?_)
    intro ω
    simp [hA_def, he_def, div_eq_inv_mul]
  have he_cond : (P.μ[A | S.sigmaXY0]) = e := by rw [hA_def, he_def]; rfl
  have hpull :
      P.μ[fun ω => (1 / e ω) * A ω | S.sigmaXY0] =ᵐ[P.μ] (fun ω => (1 / e ω) * e ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaXY0) (μ := P.μ) hinv_smeas hinvA_int hA_int
    refine h.trans ?_
    rw [he_cond]
    rfl
  have hcancel : (fun ω => (1 / e ω) * e ω) =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hpos] with ω hω
    rw [he_def] at hω
    rw [he_def]
    field_simp
  have hinner : P.μ[fun ω => A ω / e ω | S.sigmaXY0] =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    have hrw : (fun ω => A ω / e ω) = (fun ω => (1 / e ω) * A ω) := by
      funext ω; rw [one_div, div_eq_inv_mul]
    rw [hrw]
    exact hpull.trans hcancel
  unfold POBackdoorSystem.Calibrated0
  have htower :
      P.μ[fun ω => A ω / e ω | S.sigmaX]
        =ᵐ[P.μ] P.μ[P.μ[fun ω => A ω / e ω | S.sigmaXY0] | S.sigmaX] :=
    (MeasureTheory.condExp_condExp_of_le hX_le S.sigmaXY0_le).symm
  refine htower.trans ?_
  have hcongr :
      P.μ[P.μ[fun ω => A ω / e ω | S.sigmaXY0] | S.sigmaX]
        =ᵐ[P.μ] P.μ[(fun _ => (1 : ℝ)) | S.sigmaX] :=
    condExp_congr_ae hinner
  refine hcongr.trans ?_
  exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const S.sigmaX_le (1 : ℝ))

/-- The true complete control propensity lies in the calibrated set. -/
theorem completeProp0_mem_MSMSetCalib0 (Λ : ℝ)
    (hmem : S.completeProp0 ∈ S.MSMSet0 Λ) (hcalib : S.Calibrated0 S.completeProp0) :
    S.completeProp0 ∈ S.MSMSetCalib0 Λ :=
  ⟨hmem, hcalib⟩

/-- **The sharp control bound is valid:** `E[Y(0)]` lies in the calibrated interval. -/
theorem Y0mean_mem_Icc_calib (Λ : ℝ)
    (hmem : S.completeProp0 ∈ S.MSMSetCalib0 Λ)
    (hbridge : S.candMean0 S.completeProp0 = S.Y0mean)
    (hbdd : BddBelow (S.candMean0 '' S.MSMSetCalib0 Λ))
    (hbdd' : BddAbove (S.candMean0 '' S.MSMSetCalib0 Λ)) :
    S.Y0mean ∈ Set.Icc (S.msmLowerCalib0 Λ) (S.msmUpperCalib0 Λ) := by
  have hmemImg : S.candMean0 S.completeProp0 ∈ S.candMean0 '' S.MSMSetCalib0 Λ :=
    Set.mem_image_of_mem _ hmem
  rw [Set.mem_Icc, ← hbridge]
  refine ⟨?_, ?_⟩
  · exact csInf_le hbdd hmemImg
  · exact le_csSup hbdd' hmemImg

/-- The calibrated control set is a subset of the odds-ratio box. -/
theorem MSMSetCalib0_subset (Λ : ℝ) : S.MSMSetCalib0 Λ ⊆ S.MSMSet0 Λ :=
  fun _ h => h.1

/-- **The sharp control upper bound is tighter than the ZSB bound.** -/
theorem msmUpperCalib0_le_msmUpper0 (Λ : ℝ)
    (hne : (S.candMean0 '' S.MSMSetCalib0 Λ).Nonempty)
    (hbdd : BddAbove (S.candMean0 '' S.MSMSet0 Λ)) :
    S.msmUpperCalib0 Λ ≤ S.msmUpper0 Λ := by
  have hsub : S.MSMSetCalib0 Λ ⊆ S.MSMSet0 Λ := S.MSMSetCalib0_subset Λ
  have himg : S.candMean0 '' S.MSMSetCalib0 Λ ⊆ S.candMean0 '' S.MSMSet0 Λ :=
    Set.image_mono hsub
  exact csSup_le_csSup hbdd hne himg

/-- **The sharp control lower bound is tighter than the ZSB bound.** -/
theorem msmLower0_le_msmLowerCalib0 (Λ : ℝ)
    (hne : (S.candMean0 '' S.MSMSetCalib0 Λ).Nonempty)
    (hbdd : BddBelow (S.candMean0 '' S.MSMSet0 Λ)) :
    S.msmLower0 Λ ≤ S.msmLowerCalib0 Λ := by
  have hsub : S.MSMSetCalib0 Λ ⊆ S.MSMSet0 Λ := S.MSMSetCalib0_subset Λ
  have himg : S.candMean0 '' S.MSMSetCalib0 Λ ⊆ S.candMean0 '' S.MSMSet0 Λ :=
    Set.image_mono hsub
  exact csInf_le_csInf hbdd hne himg

end POBackdoorSystem

end PO
end Causalean
