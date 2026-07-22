/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateWitness

/-!
# Private local-polynomial upper endpoint

This file turns the explicit private local-polynomial witness into the certified
upper endpoint while avoiding the `PrivateUpperBound`/`PrivateMechanism` import cycle.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal

noncomputable section

/-- A measurable post-processing map whose values are clipped to `[-2,2]` gives a
release measure supported on `[-2,2]`.  This is the support step used after the
local-polynomial solve. -/
private lemma map_clip_support {α : Type} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc (-2 : ℝ) 2) :
    (μ.map f) (Set.Icc (-2 : ℝ) 2)ᶜ = 0 := by
  rw [Measure.map_apply hf measurableSet_Icc.compl]
  have hempty : f ⁻¹' (Set.Icc (-2 : ℝ) 2)ᶜ = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim (hx (hrange x))
    · intro hx
      exact hx.elim
  rw [hempty, measure_empty]

/-- Any admissible clipped central-DP mechanism bounds the infimum defining
`dpMinimaxRisk` by its own worst-case risk. -/
private lemma dpMinimaxRisk_le_of_witness {d n : ℕ} {epsN delN R : ℝ}
    {C : CateLaw d → Prop} {x0 : Fin d → ℝ}
    (M : (Fin n → CateObs d) → Measure ℝ)
    (hDP : CentralDP n epsN delN M)
    (hclip : ∀ s, (M s) (Set.Icc (-2 : ℝ) 2)ᶜ = 0)
    (hR : (⨆ P : {P : CateLaw d // C P ∧ IidSampling P ∧
              |P.mu1 x0 - P.mu0 x0| ≤ 2},
            ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(M s))
              ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure)) ≤ R) :
    dpMinimaxRisk n epsN delN C x0 ≤ R := by
  unfold dpMinimaxRisk
  have hbdd : BddBelow (Set.range (fun
      T : {T : (Fin n → CateObs d) → Measure ℝ //
        CentralDP n epsN delN T ∧
          (∀ s, (T s) (Set.Icc (-2 : ℝ) 2)ᶜ = 0)} =>
      ⨆ P : {P : CateLaw d // C P ∧ IidSampling P ∧
          |P.mu1 x0 - P.mu0 x0| ≤ 2},
        ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(T.1 s))
          ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨T, rfl⟩
    apply Real.iSup_nonneg
    intro P
    positivity
  exact (ciInf_le hbdd ⟨M, hDP, hclip⟩).trans hR

-- @node: lem:private-local-polynomial-upper-bound
/-- **Private local-polynomial upper endpoint (crux).** For all sufficiently large
`n` there is an EXPLICIT armwise privatized local-polynomial mechanism `M` (a
central-DP admissible probability kernel, clipped to the estimand range `[-2,2]`)
that WITNESSES the upper endpoint: its worst-case absolute-error risk over the
frozen positive-density Hölder CATE class (restricted to genuine i.i.d. probability
laws with in-range estimand, matching `dpMinimaxRisk`'s domain) is bounded by
`C{n^{-β/(2β+d)} ∨ (n ε_n)^{-β/(β+d)}}`; hence the minimax value satisfies
`R_n^{DP} ≤ C{n^{-β/(2β+d)} ∨ (n ε_n)^{-β/(β+d)}}`. -/
lemma private_local_polynomial_upper_bound {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
      ∀ᶠ n : ℕ in Filter.atTop,
      (∃ M : (Fin n → CateObs d) → Measure ℝ,
          IsArmwisePrivatizedLocalPoly n beta r0 (eps n) x0 M ∧
          CentralDP n (eps n) (del n) M ∧
          (∀ s, (M s) (Set.Icc (-2 : ℝ) 2)ᶜ = 0) ∧
          (⨆ P : {P : CateLaw d //
                HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P
                  ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2},
              ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(M s))
                ∂(Measure.pi fun _ : Fin n => (P.1).dataMeasure))
            ≤ C * max ((n : ℝ) ^ (-(beta / (2 * beta + (d : ℝ)))))
                (((n : ℝ) * eps n) ^ (-(beta / (beta + (d : ℝ)))))) ∧
      dpMinimaxRisk n (eps n) (del n)
          (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
        ≤ C * max ((n : ℝ) ^ (-(beta / (2 * beta + (d : ℝ)))))
              (((n : ℝ) * eps n) ^ (-(beta / (beta + (d : ℝ))))) := by
  obtain ⟨C, hC, hconstruction⟩ :=
    explicit_private_local_poly_witness alpha beta gamma L e0 f0 f1 r0 x0 hreg hd
  refine ⟨C, hC, fun eps del hbudget => ?_⟩
  filter_upwards [hconstruction eps del hbudget] with n hn
  obtain ⟨M, hshape, hDP, hclip, hrisk⟩ := hn
  refine ⟨⟨M, hshape, hDP, hclip, hrisk⟩, ?_⟩
  exact dpMinimaxRisk_le_of_witness M hDP hclip hrisk

end

end CausalSmith.Stat.DpCateMinimax
