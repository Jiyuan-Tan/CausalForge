/- Copyright (c) 2026 Jiyuan Tan. All rights reserved. -/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RandomizedLeCam

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Stat

private lemma bind_risk_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (K : X → Measure ℝ) (hK : Measurable K)
    (hprob : ∀ x, IsProbabilityMeasure (K x))
    (hclip : ∀ x, K x (Set.Icc (-2 : ℝ) 2)ᶜ = 0)
    (θ : ℝ) (hθ : |θ| ≤ 2) :
    ∫ z, |z - θ| ∂μ.bind K = ∫ x, (∫ z, |z - θ| ∂K x) ∂μ := by
  exact Causalean.Mathlib.MeasureTheory.integral_bind hK
    (integrable_abs_sub_bind_of_clipped μ K hK hprob hclip θ hθ)

private lemma bind_risk_le_four {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (K : X → Measure ℝ) (hK : Measurable K)
    (hprob : ∀ x, IsProbabilityMeasure (K x))
    (hclip : ∀ x, K x (Set.Icc (-2 : ℝ) 2)ᶜ = 0)
    (θ : ℝ) (hθ : |θ| ≤ 2) :
    ∫ x, (∫ z, |z - θ| ∂K x) ∂μ ≤ 4 := by
  letI : ∀ x, IsProbabilityMeasure (K x) := hprob
  letI : IsProbabilityMeasure (μ.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hprob)
  rw [← bind_risk_eq μ K hK hprob hclip θ hθ]
  have hi := integrable_abs_sub_bind_of_clipped μ K hK hprob hclip θ hθ
  have hsupp : ∀ᵐ z ∂μ.bind K, z ∈ Set.Icc (-2 : ℝ) 2 := by
    change Set.Icc (-2 : ℝ) 2 ∈ ae (μ.bind K)
    rw [mem_ae_iff, Measure.bind_apply measurableSet_Icc.compl hK.aemeasurable]
    simp [hclip]
  calc
    ∫ z, |z - θ| ∂μ.bind K ≤ ∫ _z, (4 : ℝ) ∂μ.bind K := by
      apply integral_mono_ae hi (integrable_const 4)
      filter_upwards [hsupp] with z hz
      rcases abs_le.mp hθ with ⟨hθ0, hθ1⟩
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    _ = 4 := by simp

/-- If every admissible release has output TV at most one half on two class
members, the actual inf-sup randomized risk is at least one eighth of their
separation. -/
lemma dpMinimaxRisk_two_point {d n : ℕ} (epsN delN : ℝ)
    (C : CateLaw d → Prop) (x0 : Fin d → ℝ) (P0 P1 : CateLaw d)
    (hP0 : C P0) (hP1 : C P1) (hiid0 : IidSampling P0) (hiid1 : IidSampling P1)
    (hr0 : |P0.mu1 x0 - P0.mu0 x0| ≤ 2)
    (hr1 : |P1.mu1 x0 - P1.mu0 x0| ≤ 2)
    (heps : 0 ≤ epsN) (hdel : 0 ≤ delN)
    (hout : ∀ M : {M : (Fin n → CateObs d) → Measure ℝ //
      CentralDP n epsN delN M ∧ ∀ s, M s (Set.Icc (-2 : ℝ) 2)ᶜ = 0},
      tvDist ((Measure.pi fun _ : Fin n => P0.dataMeasure).bind M.1)
        ((Measure.pi fun _ : Fin n => P1.dataMeasure).bind M.1) ≤ 1 / 2) :
    |(P1.mu1 x0 - P1.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| / 8 ≤
      dpMinimaxRisk n epsN delN C x0 := by
  let p0 : {P : CateLaw d // C P ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2} :=
    ⟨P0, hP0, hiid0, hr0⟩
  let p1 : {P : CateLaw d // C P ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2} :=
    ⟨P1, hP1, hiid1, hr1⟩
  let M0 : (Fin n → CateObs d) → Measure ℝ := fun _ => Measure.dirac 0
  have hM0 : CentralDP n epsN delN M0 ∧
      ∀ s, M0 s (Set.Icc (-2 : ℝ) 2)ᶜ = 0 := by
    constructor
    · refine ⟨fun _ => inferInstance, measurable_const, ?_⟩
      intro D D' _hdata _hdata' hadj B hB
      have hm : (M0 D).real B ≤ Real.exp epsN * (M0 D').real B := by
        dsimp [M0]
        apply le_mul_of_one_le_left measureReal_nonneg
        exact Real.one_le_exp heps
      exact hm.trans (le_add_of_nonneg_right hdel)
    · intro s
      simp [M0]
  letI : Nonempty {M : (Fin n → CateObs d) → Measure ℝ //
      CentralDP n epsN delN M ∧ ∀ s, M s (Set.Icc (-2 : ℝ) 2)ᶜ = 0} :=
    ⟨⟨M0, hM0⟩⟩
  rw [dpMinimaxRisk]
  refine le_ciInf fun M => ?_
  letI : IsProbabilityMeasure P0.dataMeasure := hiid0.1
  letI : IsProbabilityMeasure P1.dataMeasure := hiid1.1
  letI : ∀ s, IsProbabilityMeasure (M.1 s) := M.2.1.1
  letI : IsProbabilityMeasure (Measure.pi fun _ : Fin n => P0.dataMeasure) := inferInstance
  letI : IsProbabilityMeasure (Measure.pi fun _ : Fin n => P1.dataMeasure) := inferInstance
  let μ0 := (Measure.pi fun _ : Fin n => P0.dataMeasure).bind M.1
  let μ1 := (Measure.pi fun _ : Fin n => P1.dataMeasure).bind M.1
  letI : IsProbabilityMeasure μ0 :=
    isProbabilityMeasure_bind M.2.1.2.1.aemeasurable (ae_of_all _ M.2.1.1)
  letI : IsProbabilityMeasure μ1 :=
    isProbabilityMeasure_bind M.2.1.2.1.aemeasurable (ae_of_all _ M.2.1.1)
  have hi0 := integrable_abs_sub_bind_of_clipped
    (Measure.pi fun _ : Fin n => P0.dataMeasure) M.1 M.2.1.2.1 M.2.1.1 M.2.2
      (P0.mu1 x0 - P0.mu0 x0) hr0
  have hi1 := integrable_abs_sub_bind_of_clipped
    (Measure.pi fun _ : Fin n => P1.dataMeasure) M.1 M.2.1.2.1 M.2.1.1 M.2.2
      (P1.mu1 x0 - P1.mu0 x0) hr1
  have hLC := output_two_point_L1_lower μ0 μ1
    (P0.mu1 x0 - P0.mu0 x0) (P1.mu1 x0 - P1.mu0 x0) hi0 hi1 (hout M)
  have hbdd : BddAbove (Set.range fun P :
      {P : CateLaw d // C P ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2} =>
      ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂M.1 s)
        ∂Measure.pi fun _ : Fin n => P.1.dataMeasure) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨P, rfl⟩
    letI : IsProbabilityMeasure P.1.dataMeasure := P.2.2.1.1
    letI : IsProbabilityMeasure (Measure.pi fun _ : Fin n => P.1.dataMeasure) := inferInstance
    exact bind_risk_le_four (Measure.pi fun _ : Fin n => P.1.dataMeasure)
      M.1 M.2.1.2.1 M.2.1.1 M.2.2 _ P.2.2.2
  have h0 := le_ciSup hbdd p0
  have h1 := le_ciSup hbdd p1
  rw [bind_risk_eq (Measure.pi fun _ : Fin n => P0.dataMeasure)
      M.1 M.2.1.2.1 M.2.1.1 M.2.2 _ hr0,
    bind_risk_eq (Measure.pi fun _ : Fin n => P1.dataMeasure)
      M.1 M.2.1.2.1 M.2.1.1 M.2.2 _ hr1] at hLC
  exact hLC.trans (max_le h0 h1)

end CausalSmith.Stat.DpCateMinimax
