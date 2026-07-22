/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional-expectation lemmas under `CondIndepFun`

* `condExp_sup_comap_eq_of_condIndep` — drop-of-conditioning: if `g ⟂ f | m`,
  conditioning `h ∘ g` on `m ⊔ σ(f)` equals conditioning on `m` alone.
* `condExp_mul_of_condIndep` — product factorization: `μ[(u∘f)(v∘g)|m] =ᵐ μ[u∘f|m]·μ[v∘g|m]`.
* `condIndepFun_weak_union_of_prodMk` — weak union via `prodMk`: `W ⟂ (V,A)|m ⟹ W ⟂ V|(m⊔σA)`.
* `condIndepFun_prodMk_of_measurable_left` — extension by an `m`-measurable function.
* `condIndepFun_contraction_of_prodMk` — contraction via a product right side.
-/

import Mathlib.Probability.Independence.Conditional

/-! # Conditional Expectations Under Conditional Independence

This file proves conditional-expectation identities implied by conditional
independence, including drop-of-conditioning, product factorization, weak union, and
contraction. These measure-theoretic facts supply the graph-independent conditional
independence algebra used by causal identification proofs.

The central exported lemmas are `condExp_sup_comap_eq_of_condIndep_comap` and
`condExp_sup_comap_eq_of_condIndep` for removing irrelevant conditioning
variables, `condExp_mul_of_condIndep` for factoring a product's conditional
expectation, `condIndepFun_weak_union_of_prodMk` for weak union,
`condIndepFun_prodMk_of_measurable_left` for adjoining an `m`-measurable
coordinate, and `condIndepFun_contraction_of_prodMk` for semigraphoid
contraction. -/

namespace Causalean

open MeasureTheory

open scoped MeasureTheory ProbabilityTheory

private def supPiGen {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  generatePiSystem
    ({s : Set Ω | @MeasurableSet Ω m₁ s} ∪ {s : Set Ω | @MeasurableSet Ω m₂ s})

private lemma supPiGen_isPiSystem {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem (supPiGen m₁ m₂) := by
  exact isPiSystem_generatePiSystem _

private lemma sup_eq_generateFrom_supPiGen {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    m₁ ⊔ m₂ = MeasurableSpace.generateFrom (supPiGen m₁ m₂) := by
  rw [supPiGen, generateFrom_generatePiSystem_eq]
  rw [← MeasurableSpace.generateFrom_sup_generateFrom]
  rw [show MeasurableSpace.generateFrom {s : Set Ω | @MeasurableSet Ω m₁ s} = m₁ from
    (@MeasurableSpace.generateFrom_measurableSet Ω m₁)]
  rw [show MeasurableSpace.generateFrom {s : Set Ω | @MeasurableSet Ω m₂ s} = m₂ from
    (@MeasurableSpace.generateFrom_measurableSet Ω m₂)]

private def supRects {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {R | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ A ∩ B = R}

private lemma supRects_isPiSystem {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem (supRects m₁ m₂) := by
  intro R hR Q hQ _hne
  rcases hR with ⟨A₁, B₁, hA₁, hB₁, rfl⟩
  rcases hQ with ⟨A₂, B₂, hA₂, hB₂, rfl⟩
  refine ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, ?_⟩
  ext ω
  simp [and_left_comm, and_assoc]

private lemma supPiGen_subset_rects {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω}
    {t : Set Ω} (ht : t ∈ supPiGen m₁ m₂) :
    ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ A ∩ B = t := by
  change t ∈
    generatePiSystem
      ({s : Set Ω | @MeasurableSet Ω m₁ s} ∪ {s : Set Ω | @MeasurableSet Ω m₂ s}) at ht
  have hsub :
      ({s : Set Ω | @MeasurableSet Ω m₁ s} ∪
          {s : Set Ω | @MeasurableSet Ω m₂ s}) ⊆ supRects m₁ m₂ := by
    intro u hu
    rcases hu with hu | hu
    · exact ⟨u, Set.univ, hu, MeasurableSet.univ, by simp⟩
    · exact ⟨Set.univ, u, MeasurableSet.univ, hu, by simp⟩
  exact generatePiSystem_subset_self (supRects_isPiSystem m₁ m₂) (generatePiSystem_mono hsub ht)

private theorem setIntegral_condExp_indep_indicator_one
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {S A F : Set Ω}
    (hS : MeasurableSet[MeasurableSpace.comap g inferInstance] S)
    (hA : MeasurableSet[m] A)
    (hF : MeasurableSet[MeasurableSpace.comap f inferInstance] F) :
    ∫ x in A ∩ F, (μ⟦S | m⟧) x ∂μ =
      ∫ x in A ∩ F, S.indicator (fun _ : Ω => (1 : ℝ)) x ∂μ := by
  let oneF : Ω → ℝ := F.indicator (fun _ => (1 : ℝ))
  let oneS : Ω → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hS_meas : MeasurableSet S := hg.comap_le S hS
  have hF_meas : MeasurableSet F := hf.comap_le F hF
  have hSF_meas : MeasurableSet (S ∩ F) := hS_meas.inter hF_meas
  have hF_int : MeasureTheory.Integrable oneF μ := by
    refine (MeasureTheory.integrable_indicator_iff hF_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  have hceS_sm : StronglyMeasurable[m] (μ⟦S | m⟧) := by
    exact MeasureTheory.stronglyMeasurable_condExp
  have hceS_bound : ∀ᵐ ω ∂μ, ‖(μ⟦S | m⟧) ω‖ ≤ (1 : ℝ) := by
    have h_nonneg : 0 ≤ᵐ[μ] μ⟦S | m⟧ := by
      refine MeasureTheory.condExp_nonneg (MeasureTheory.ae_of_all μ fun ω => ?_)
      by_cases hω : ω ∈ S <;> simp [hω]
    have h_le_one : μ⟦S | m⟧ ≤ᵐ[μ] (fun _ : Ω => (1 : ℝ)) := by
      have h_ind_le : oneS ≤ᵐ[μ] (fun _ : Ω => (1 : ℝ)) := by
        exact MeasureTheory.ae_of_all μ fun ω => by
          by_cases hω : ω ∈ S <;> simp [oneS, hω]
      have hmono := MeasureTheory.condExp_mono (μ := μ) (m := m)
        (f := oneS) (g := fun _ : Ω => (1 : ℝ)) ?_
        (MeasureTheory.integrable_const (1 : ℝ)) h_ind_le
      · filter_upwards [hmono] with ω hω
        simpa [MeasureTheory.condExp_const hm (1 : ℝ)] using hω
      · refine (MeasureTheory.integrable_indicator_iff hS_meas).2 ?_
        exact MeasureTheory.integrableOn_const
    filter_upwards [h_nonneg, h_le_one] with ω h0 h1
    rw [Real.norm_of_nonneg h0]
    exact h1
  have hprod_int :
      MeasureTheory.Integrable (fun ω => (μ⟦S | m⟧) ω * oneF ω) μ := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
    · exact (hceS_sm.mono hm).aestronglyMeasurable.mul hF_int.aestronglyMeasurable
    · filter_upwards [hceS_bound] with ω hω
      by_cases hωF : ω ∈ F
      · simpa [oneF, hωF, Real.norm_eq_abs] using hω
      · simp [oneF, hωF]
  have hpull :
      μ[fun ω => (μ⟦S | m⟧) ω * oneF ω | m]
        =ᵐ[μ] (μ⟦S | m⟧) * μ[oneF | m] := by
    exact MeasureTheory.condExp_stronglyMeasurable_mul_of_bound hm hceS_sm hF_int 1 hceS_bound
  have hCIsets :
      (μ⟦S ∩ F | m⟧) =ᵐ[μ] (μ⟦S | m⟧) * (μ⟦F | m⟧) := by
    have hCond : ProbabilityTheory.CondIndep m (MeasurableSpace.comap g inferInstance)
        (MeasurableSpace.comap f inferInstance) hm μ := by
      exact (ProbabilityTheory.condIndepFun_iff_condIndep (m' := m) (hm' := hm)
        (f := g) (g := f) (μ := μ)).mp hCI
    exact (ProbabilityTheory.condIndep_iff (m' := m)
      (m₁ := MeasurableSpace.comap g inferInstance)
      (m₂ := MeasurableSpace.comap f inferInstance)
      (hm' := hm) (μ := μ) hg.comap_le hf.comap_le).mp hCond S F hS hF
  have hSF_int :
      MeasureTheory.Integrable ((S ∩ F).indicator (fun _ : Ω => (1 : ℝ))) μ := by
    refine (MeasureTheory.integrable_indicator_iff hSF_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  calc
    ∫ x in A ∩ F, (μ⟦S | m⟧) x ∂μ
        = ∫ x in A, F.indicator (fun x => (μ⟦S | m⟧) x) x ∂μ := by
          rw [MeasureTheory.integral_indicator hF_meas]
          rw [Measure.restrict_restrict hF_meas]
          rw [Set.inter_comm]
    _ = ∫ x in A, (fun ω => (μ⟦S | m⟧) ω * oneF ω) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_fun (hm _ hA) ?_
          intro x _hx
          by_cases hxF : x ∈ F <;> simp [oneF, hxF]
    _ = ∫ x in A, μ[fun ω => (μ⟦S | m⟧) ω * oneF ω | m] x ∂μ := by
          rw [MeasureTheory.setIntegral_condExp hm hprod_int hA]
    _ = ∫ x in A, (fun ω => (μ⟦S | m⟧) ω * (μ⟦F | m⟧) ω) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae (hm _ hA) ?_
          exact hpull.mono fun x hx _ => hx
    _ = ∫ x in A, (μ⟦S ∩ F | m⟧) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae (hm _ hA) ?_
          exact hCIsets.symm.mono fun x hx _ => hx
    _ = ∫ x in A, (S ∩ F).indicator (fun _ : Ω => (1 : ℝ)) x ∂μ := by
          rw [MeasureTheory.setIntegral_condExp (m := m) (m₀ := mΩ) (μ := μ)
            (f := (S ∩ F).indicator (fun _ : Ω => (1 : ℝ))) hm hSF_int hA]
    _ = ∫ x in A, F.indicator oneS x ∂μ := by
          refine MeasureTheory.setIntegral_congr_fun (hm _ hA) ?_
          intro x _hx
          by_cases hxS : x ∈ S <;> by_cases hxF : x ∈ F <;> simp [oneS, hxS, hxF]
    _ = ∫ x in A ∩ F, oneS x ∂μ := by
          rw [MeasureTheory.integral_indicator hF_meas]
          rw [Measure.restrict_restrict hF_meas]
          rw [Set.inter_comm]
    _ = ∫ x in A ∩ F, S.indicator (fun _ : Ω => (1 : ℝ)) x ∂μ := rfl

private theorem setIntegral_condExp_indep_indicator
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {S A F : Set Ω}
    (hS : MeasurableSet[MeasurableSpace.comap g inferInstance] S)
    (hA : MeasurableSet[m] A)
    (hF : MeasurableSet[MeasurableSpace.comap f inferInstance] F) (c : ℝ) :
    ∫ x in A ∩ F, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ =
      ∫ x in A ∩ F, S.indicator (fun _ : Ω => c) x ∂μ := by
  let oneS : Ω → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hsmul_fun : (fun ω => c • oneS ω) = S.indicator (fun _ : Ω => c) := by
    ext ω
    by_cases hω : ω ∈ S <;> simp [oneS, hω]
  have hsmul_ae : (fun ω => c • oneS ω) =ᵐ[μ] S.indicator (fun _ : Ω => c) := by
    exact MeasureTheory.ae_of_all μ fun ω => congrFun hsmul_fun ω
  have hce : μ[S.indicator (fun _ : Ω => c) | m]
      =ᵐ[μ] fun ω => c * (μ⟦S | m⟧) ω := by
    have h1 : μ[S.indicator (fun _ : Ω => c) | m]
        =ᵐ[μ] μ[fun ω => c • oneS ω | m] := by
      exact (MeasureTheory.condExp_congr_ae hsmul_ae).symm
    have h2 := MeasureTheory.condExp_smul (μ := μ) (c := c) (f := oneS) (m := m)
    refine h1.trans ?_
    filter_upwards [h2] with ω hω
    simpa [oneS, Pi.smul_apply, smul_eq_mul] using hω
  calc
    ∫ x in A ∩ F, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ
        = ∫ x in A ∩ F, (fun ω => c * (μ⟦S | m⟧) ω) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae ((hm _ hA).inter (hf.comap_le _ hF)) ?_
          exact hce.mono fun x hx _ => hx
    _ = c * ∫ x in A ∩ F, (μ⟦S | m⟧) x ∂μ := by
          rw [MeasureTheory.integral_const_mul]
    _ = c * ∫ x in A ∩ F, oneS x ∂μ := by
          rw [setIntegral_condExp_indep_indicator_one hm hf hg hCI hS hA hF]
    _ = ∫ x in A ∩ F, (fun ω => c * oneS ω) x ∂μ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ∫ x in A ∩ F, S.indicator (fun _ : Ω => c) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_fun ((hm _ hA).inter (hf.comap_le _ hF)) ?_
          intro x _hx
          simpa [Pi.smul_apply, smul_eq_mul] using congrFun hsmul_fun x

private theorem condExp_indicator_sup_comap_eq_of_condIndep
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {S : Set Ω}
    (hS : MeasurableSet[MeasurableSpace.comap g inferInstance] S) (c : ℝ) :
    μ[S.indicator (fun _ : Ω => c) | m ⊔ MeasurableSpace.comap f inferInstance]
      =ᵐ[μ] μ[S.indicator (fun _ : Ω => c) | m] := by
  let mf : MeasurableSpace Ω := MeasurableSpace.comap f inferInstance
  let M : MeasurableSpace Ω := m ⊔ mf
  have hmM : M ≤ mΩ := by
    dsimp [M, mf]
    exact sup_le hm hf.comap_le
  haveI : MeasureTheory.SigmaFinite (μ.trim hmM) := by infer_instance
  have hS_meas : @MeasurableSet Ω mΩ S := hg.comap_le S hS
  have hY_int : MeasureTheory.Integrable (S.indicator (fun _ : Ω => c)) μ := by
    refine (MeasureTheory.integrable_indicator_iff hS_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  have hce_int : ∀ R, @MeasurableSet Ω M R → μ R < ⊤ →
      MeasureTheory.IntegrableOn (μ[S.indicator (fun _ : Ω => c) | m]) R μ := by
    intro R _hR _hμR
    exact MeasureTheory.integrable_condExp.integrableOn
  have hset : ∀ R, @MeasurableSet Ω M R →
      ∫ x in R, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ =
        ∫ x in R, S.indicator (fun _ : Ω => c) x ∂μ := by
    refine MeasurableSpace.induction_on_inter (m := M)
      (s := supPiGen m (MeasurableSpace.comap f inferInstance))
      (C := fun R _ => ∫ x in R, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ =
        ∫ x in R, S.indicator (fun _ : Ω => c) x ∂μ)
      (h_eq := ?_) (h_inter := ?_) ?empty ?basic ?compl ?iUnion
    · dsimp [M, mf]
      exact sup_eq_generateFrom_supPiGen m (MeasurableSpace.comap f inferInstance)
    · exact supPiGen_isPiSystem m (MeasurableSpace.comap f inferInstance)
    · simp
    · intro R hR
      rcases supPiGen_subset_rects
          (m₁ := m) (m₂ := MeasurableSpace.comap f inferInstance) hR with
        ⟨A, F, hA, hF, hAF⟩
      rw [← hAF]
      exact setIntegral_condExp_indep_indicator hm hf hg hCI hS hA hF c
    · intro R hR hEq
      have hRΩ : @MeasurableSet Ω mΩ R := hmM _ hR
      calc
        ∫ x in Rᶜ, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ
            = ∫ x, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ -
                ∫ x in R, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ := by
              rw [MeasureTheory.setIntegral_compl hRΩ MeasureTheory.integrable_condExp]
        _ = ∫ x, S.indicator (fun _ : Ω => c) x ∂μ -
                ∫ x in R, S.indicator (fun _ : Ω => c) x ∂μ := by
              rw [MeasureTheory.integral_condExp hm, hEq]
        _ = ∫ x in Rᶜ, S.indicator (fun _ : Ω => c) x ∂μ := by
              rw [MeasureTheory.setIntegral_compl hRΩ hY_int]
    · intro Rs hdisj hRs hEq
      have hRsΩ : ∀ i, @MeasurableSet Ω mΩ (Rs i) := fun i => hmM _ (hRs i)
      calc
        ∫ x in ⋃ i, Rs i, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ
            = ∑' i, ∫ x in Rs i, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ := by
              rw [MeasureTheory.integral_iUnion hRsΩ hdisj
                MeasureTheory.integrable_condExp.integrableOn]
        _ = ∑' i, ∫ x in Rs i, S.indicator (fun _ : Ω => c) x ∂μ := by
              congr 1
              ext i
              exact hEq i
        _ = ∫ x in ⋃ i, Rs i, S.indicator (fun _ : Ω => c) x ∂μ := by
              rw [MeasureTheory.integral_iUnion hRsΩ hdisj hY_int.integrableOn]
  have hce_sm_M :
      @MeasureTheory.AEStronglyMeasurable Ω ℝ _ M _ (μ[S.indicator (fun _ : Ω => c) | m]) μ := by
    exact ((MeasureTheory.stronglyMeasurable_condExp (m := m) (μ := μ)
      (f := S.indicator (fun _ : Ω => c))).mono (show m ≤ M by
        dsimp [M]
        exact le_sup_left)).aestronglyMeasurable
  have huniq := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hmM hY_int hce_int
    (fun R hR _ => hset R hR) hce_sm_M
  simpa [M, mf] using huniq.symm

/-- If `g` is conditionally independent of `f` given `m`, conditioning a
`σ(g)`-measurable integrable real function on `m ⊔ σ(f)` is the same as
conditioning it on `m`, up to μ-a.e. equality. -/
theorem condExp_sup_comap_eq_of_condIndep_comap
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {Y : Ω → ℝ}
    (hY_meas :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ (MeasurableSpace.comap g inferInstance) Y)
    (hY_int : MeasureTheory.Integrable Y μ) :
    μ[Y | m ⊔ MeasurableSpace.comap f inferInstance] =ᵐ[μ] μ[Y | m] := by
  let mf : MeasurableSpace Ω := MeasurableSpace.comap f inferInstance
  let mg : MeasurableSpace Ω := MeasurableSpace.comap g inferInstance
  let M : MeasurableSpace Ω := m ⊔ mf
  have hmM : M ≤ mΩ := by
    dsimp [M, mf]
    exact sup_le hm hf.comap_le
  have hmg : mg ≤ mΩ := by
    dsimp [mg]
    exact hg.comap_le
  haveI : MeasureTheory.SigmaFinite (μ.trim hm) := by infer_instance
  haveI : MeasureTheory.SigmaFinite (μ.trim hmM) := by infer_instance
  haveI : MeasureTheory.SigmaFinite (μ.trim hmg) := by infer_instance
  let T_M : (Ω →₁[μ] ℝ) →L[ℝ] Ω →₁[μ] ℝ :=
    MeasureTheory.condExpL1CLM ℝ hmM μ
  let T_m : (Ω →₁[μ] ℝ) →L[ℝ] Ω →₁[μ] ℝ :=
    MeasureTheory.condExpL1CLM ℝ hm μ
  have hL1 :
      T_M (hY_int.toL1 Y) = T_m (hY_int.toL1 Y) := by
    have hP_ind :
        ∀ (c : ℝ) {s : Set Ω} (hs : MeasurableSet[mg] s) (hμs : μ s < ⊤),
          T_M (@MeasureTheory.Lp.simpleFunc.indicatorConst Ω ℝ mΩ _
              (1 : ENNReal) μ s (hmg s hs) hμs.ne c)
            =
          T_m (@MeasureTheory.Lp.simpleFunc.indicatorConst Ω ℝ mΩ _
              (1 : ENNReal) μ s (hmg s hs) hμs.ne c) := by
      intro c s hs hμs
      have hsΩ : @MeasurableSet Ω mΩ s := hmg s hs
      have hs_int : MeasureTheory.Integrable (s.indicator (fun _ : Ω => c)) μ := by
        refine (MeasureTheory.integrable_indicator_iff (μ := μ) hsΩ).2 ?_
        exact MeasureTheory.integrableOn_const
      have hind_eq :
          @MeasureTheory.Lp.simpleFunc.indicatorConst Ω ℝ mΩ _
              (1 : ENNReal) μ s (hmg s hs) hμs.ne c
            = hs_int.toL1 (s.indicator (fun _ : Ω => c)) := by
        apply MeasureTheory.Lp.ext
        refine (@MeasureTheory.indicatorConstLp_coeFn Ω ℝ mΩ (1 : ENNReal) μ _
          s (hmg s hs) hμs.ne c).trans ?_
        exact hs_int.coeFn_toL1.symm
      rw [hind_eq]
      apply MeasureTheory.Lp.ext
      have hM := MeasureTheory.condExp_ae_eq_condExpL1CLM hmM hs_int
      have hm' := MeasureTheory.condExp_ae_eq_condExpL1CLM hm hs_int
      have hdrop :
          μ[s.indicator (fun _ : Ω => c) | M]
            =ᵐ[μ] μ[s.indicator (fun _ : Ω => c) | m] := by
        dsimp [M, mf]
        exact condExp_indicator_sup_comap_eq_of_condIndep hm hf hg hCI hs c
      exact hM.symm.trans (hdrop.trans hm')
    have hP_add :
        ∀ ⦃u v : Ω → ℝ⦄, ∀ hu : MeasureTheory.MemLp u 1 μ,
          ∀ hv : MeasureTheory.MemLp v 1 μ,
          @StronglyMeasurable Ω ℝ _ mg u →
          @StronglyMeasurable Ω ℝ _ mg v →
          Disjoint (Function.support u) (Function.support v) →
          T_M (hu.toLp u) = T_m (hu.toLp u) →
          T_M (hv.toLp v) = T_m (hv.toLp v) →
          T_M (hu.toLp u + hv.toLp v) = T_m (hu.toLp u + hv.toLp v) := by
      intro u v hu hv _hu_meas _hv_meas _hdisj hu_eq hv_eq
      simp [T_M, T_m, map_add, hu_eq, hv_eq]
    have hP_closed :
        IsClosed {u : @MeasureTheory.lpMeas Ω ℝ ℝ _ _ _ mg mΩ (1 : ENNReal) μ |
          T_M (u : @MeasureTheory.Lp Ω ℝ mΩ _ (1 : ENNReal) μ) =
          T_m (u : @MeasureTheory.Lp Ω ℝ mΩ _ (1 : ENNReal) μ)} := by
      exact isClosed_eq (T_M.continuous.comp continuous_subtype_val)
        (T_m.continuous.comp continuous_subtype_val)
    exact MeasureTheory.Lp.induction_stronglyMeasurable hmg (by norm_num)
      (fun u : Ω →₁[μ] ℝ => T_M u = T_m u) hP_ind hP_add hP_closed
      (hY_int.toL1 Y) (hY_meas.aestronglyMeasurable.congr hY_int.coeFn_toL1.symm)
  have hM := MeasureTheory.condExp_ae_eq_condExpL1CLM hmM hY_int
  have hm' := MeasureTheory.condExp_ae_eq_condExpL1CLM hm hY_int
  have hL1_ae :
      (T_M (hY_int.toL1 Y) : Ω → ℝ) =ᵐ[μ]
        (T_m (hY_int.toL1 Y) : Ω → ℝ) := by
    rw [hL1]
  exact hM.trans (hL1_ae.trans hm'.symm)

/-- Drop-of-conditioning for conditional expectation under conditional independence.

If `g ⟂ f | m` (as `CondIndepFun m f g`) and `h` is a measurable real-valued function,
then conditioning `h ∘ g` on the enlarged σ-algebra `m ⊔ σ(f)` gives the same value
(μ-a.e.) as conditioning on `m` alone.

This is the core Step-1 maneuver in the backdoor ATE proof.  The proof reduces
the concrete `h ∘ g` case to the private `σ(g)`-measurable drop-of-conditioning
helper above. -/
theorem condExp_sup_comap_eq_of_condIndep
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {h : β → ℝ} (hh : Measurable h)
    (hhg : MeasureTheory.Integrable (fun ω => h (g ω)) μ) :
    μ[fun ω => h (g ω) | m ⊔ MeasurableSpace.comap f inferInstance]
      =ᵐ[μ] μ[fun ω => h (g ω) | m] := by
  have hg_comap :
      @Measurable Ω β (MeasurableSpace.comap g inferInstance) _ g := by
    exact Measurable.of_comap_le le_rfl
  have hY_meas :
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (MeasurableSpace.comap g inferInstance) (fun ω => h (g ω)) := by
    exact (hh.comp hg_comap).stronglyMeasurable
  exact condExp_sup_comap_eq_of_condIndep_comap hm hf hg hCI hY_meas hhg

/-- **Conditional-independence factorization of a product's conditional
expectation.**

If `f ⟂ g | m` (as `CondIndepFun m hm f g μ`) and `u ∘ f`, `v ∘ g` are
integrable (with their product also integrable), then

    μ[(u ∘ f) · (v ∘ g) | m] =ᵐ[μ] μ[u ∘ f | m] · μ[v ∘ g | m].

This is the core step of the backdoor ATE proof: with `f = factualD`,
`g = Y(d)`, `u = 1_{· = d}`, `v = id`, it yields

    μ[1_{D=d} · Y(d) | σ(X)] =ᵐ μ[1_{D=d} | σ(X)] · μ[Y(d) | σ(X)].

Proof structure:
1. Tower on `m ≤ m ⊔ σ(g)` (via `condExp_condExp_of_le`):
   `μ[uf·vg | m] =ᵐ μ[μ[uf·vg | m ⊔ σ(g)] | m]`.
2. `m ⊔ σ(g)`-pullout of `v ∘ g` (`condExp_mul_of_stronglyMeasurable_right`):
   `μ[uf·vg | m ⊔ σ(g)] =ᵐ μ[uf | m ⊔ σ(g)] · (v ∘ g)`.
3. Drop conditioning with `condExp_sup_comap_eq_of_condIndep` (requires
   `hCI.symm`): `μ[uf | m ⊔ σ(g)] =ᵐ μ[uf | m]`.
4. `m`-pullout of `μ[uf|m]` (`condExp_mul_of_stronglyMeasurable_left`):
   `μ[μ[uf|m] · vg | m] =ᵐ μ[uf|m] · μ[vg | m]`.

Upstream Mathlib candidate, currently complete modulo the drop-of-conditioning
helper above. -/
theorem condExp_mul_of_condIndep
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm f g μ)
    {u : α → ℝ} {v : β → ℝ} (hu : Measurable u) (hv : Measurable v)
    (huf : MeasureTheory.Integrable (fun ω => u (f ω)) μ)
    (hvg : MeasureTheory.Integrable (fun ω => v (g ω)) μ)
    (huv : MeasureTheory.Integrable (fun ω => u (f ω) * v (g ω)) μ) :
    μ[fun ω => u (f ω) * v (g ω) | m]
      =ᵐ[μ] (μ[fun ω => u (f ω) | m]) * (μ[fun ω => v (g ω) | m]) := by
  let mg : MeasurableSpace Ω := m ⊔ MeasurableSpace.comap g inferInstance
  have hm_g : mg ≤ mΩ := by
    dsimp [mg]
    exact sup_le hm hg.comap_le
  haveI : MeasureTheory.IsFiniteMeasure (μ.trim hm_g) :=
    MeasureTheory.isFiniteMeasure_trim hm_g
  haveI : MeasureTheory.SigmaFinite (μ.trim hm_g) := inferInstance
  have hg_mg : @Measurable Ω β mg _ g := by
    exact Measurable.of_comap_le le_sup_right
  have hvg_mg :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ mg (fun ω => v (g ω)) := by
    exact (hv.comp hg_mg).stronglyMeasurable
  have huv' :
      MeasureTheory.Integrable ((fun ω => u (f ω)) * (fun ω => v (g ω))) μ := by
    simpa [Pi.mul_apply] using huv
  have htower :
      μ[fun ω => u (f ω) * v (g ω) | m]
        =ᵐ[μ] μ[μ[fun ω => u (f ω) * v (g ω) | mg] | m] := by
    exact (MeasureTheory.condExp_condExp_of_le
      (f := fun ω => u (f ω) * v (g ω)) (m₁ := m) (m₂ := mg) (m₀ := mΩ)
      le_sup_left hm_g).symm
  have hinner :
      μ[fun ω => u (f ω) * v (g ω) | mg]
        =ᵐ[μ] μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω)) := by
    simpa [Pi.mul_apply] using
      (MeasureTheory.condExp_mul_of_stronglyMeasurable_right (m := mg)
        (f := fun ω => u (f ω)) (g := fun ω => v (g ω)) hvg_mg huv' huf)
  have hdrop :
      μ[fun ω => u (f ω) | mg] =ᵐ[μ] μ[fun ω => u (f ω) | m] := by
    dsimp [mg]
    exact condExp_sup_comap_eq_of_condIndep hm hg hf hCI hu huf
  have hinner_outer :
      μ[μ[fun ω => u (f ω) * v (g ω) | mg] | m]
        =ᵐ[μ] μ[μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω)) | m] := by
    exact MeasureTheory.condExp_congr_ae hinner
  have hdrop_mul :
      μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω))
        =ᵐ[μ] μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) := by
    exact hdrop.mul (Filter.EventuallyEq.refl (MeasureTheory.ae μ) (fun ω => v (g ω)))
  have hdrop_outer :
      μ[μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω)) | m]
        =ᵐ[μ] μ[μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) | m] := by
    exact MeasureTheory.condExp_congr_ae hdrop_mul
  have hprod_ae :
      μ[fun ω => u (f ω) * v (g ω) | mg]
        =ᵐ[μ] μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) :=
    hinner.trans hdrop_mul
  have hprod_int :
      MeasureTheory.Integrable (μ[fun ω => u (f ω) | m] * (fun ω => v (g ω))) μ := by
    exact (MeasureTheory.integrable_condExp (m := mg)
      (f := fun ω => u (f ω) * v (g ω)) (μ := μ)).congr hprod_ae
  have hce_sm :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ m (μ[fun ω => u (f ω) | m]) := by
    exact MeasureTheory.stronglyMeasurable_condExp
  have hpull :
      μ[μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) | m]
        =ᵐ[μ] μ[fun ω => u (f ω) | m] * μ[fun ω => v (g ω) | m] := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := m)
      (f := μ[fun ω => u (f ω) | m]) (g := fun ω => v (g ω))
      hce_sm hprod_int hvg
  exact htower.trans (hinner_outer.trans (hdrop_outer.trans hpull))

/-- **Weak union for `CondIndepFun`**: from `W ⟂ (V, A) | m`, conclude
`W ⟂ V | (m ⊔ comap A)`.

The proof reduces to the conditional-expectation indicator characterization:
condition first on `m ⊔ σ(V,A)`, pull out the V-indicator, drop the extra
conditioning from the W-indicator using `condExp_sup_comap_eq_of_condIndep`,
and tower back to `m ⊔ σ(A)`. -/
theorem condIndepFun_weak_union_of_prodMk
    {Ω α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {W : Ω → α} {V : Ω → β} {A : Ω → γ}
    (hW : Measurable W) (hV : Measurable V) (hA : Measurable A)
    (hCI : ProbabilityTheory.CondIndepFun m hm W (fun ω => (V ω, A ω)) μ) :
    ProbabilityTheory.CondIndepFun (m ⊔ MeasurableSpace.comap A inferInstance)
      (sup_le hm hA.comap_le) W V μ := by
  let mA : MeasurableSpace Ω := m ⊔ MeasurableSpace.comap A inferInstance
  let pair : Ω → β × γ := fun ω => (V ω, A ω)
  let mVA : MeasurableSpace Ω := m ⊔ MeasurableSpace.comap pair inferInstance
  have hpair : @Measurable Ω (β × γ) mΩ _ pair := hV.prod hA
  have hmVA : mVA ≤ mΩ := by
    dsimp [mVA]
    exact sup_le hm hpair.comap_le
  have hpair_mVA : @Measurable Ω (β × γ) mVA _ pair := by
    exact Measurable.of_comap_le le_sup_right
  have hV_mVA : @Measurable Ω β mVA _ V := by
    exact measurable_fst.comp hpair_mVA
  have hA_pair :
      @Measurable Ω γ (MeasurableSpace.comap pair inferInstance) _ A := by
    exact measurable_snd.comp (Measurable.of_comap_le le_rfl)
  have hmA_le_mVA : mA ≤ mVA := by
    dsimp [mA, mVA]
    exact sup_le le_sup_left (le_trans hA_pair.comap_le le_sup_right)
  have hCI_A : ProbabilityTheory.CondIndepFun m hm W A μ := by
    simpa [Function.comp_def] using
      (hCI.comp measurable_id measurable_snd)
  rw [ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul hW hV]
  intro s t hs ht
  let S : Set Ω := W ⁻¹' s
  let T : Set Ω := V ⁻¹' t
  let oneS : Ω → ℝ := S.indicator (fun _ => (1 : ℝ))
  let oneT : Ω → ℝ := T.indicator (fun _ => (1 : ℝ))
  have hS_meas : @MeasurableSet Ω mΩ S := hW hs
  have hT_meas : @MeasurableSet Ω mΩ T := hV ht
  have hS_int : MeasureTheory.Integrable oneS μ := by
    refine (MeasureTheory.integrable_indicator_iff hS_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  have hT_int : MeasureTheory.Integrable oneT μ := by
    refine (MeasureTheory.integrable_indicator_iff hT_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  have hST_int : MeasureTheory.Integrable (oneS * oneT) μ := by
    have hST_set_int :
        MeasureTheory.Integrable ((S ∩ T).indicator (fun _ : Ω => (1 : ℝ))) μ := by
      refine (MeasureTheory.integrable_indicator_iff (hS_meas.inter hT_meas)).2 ?_
      exact MeasureTheory.integrableOn_const
    exact hST_set_int.congr (MeasureTheory.ae_of_all μ fun ω => by
      by_cases hωS : ω ∈ S <;> by_cases hωT : ω ∈ T <;> simp [oneS, oneT, hωS, hωT])
  have hT_mVA :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ mVA oneT := by
    exact MeasureTheory.stronglyMeasurable_const.indicator (hV_mVA ht)
  have hdrop_mVA :
      μ[oneS | mVA] =ᵐ[μ] μ[oneS | m] := by
    have hs_ind_meas :
        Measurable (s.indicator (fun _ : α => (1 : ℝ))) :=
      measurable_const.indicator hs
    simpa [mVA, pair, oneS, S] using
      (condExp_sup_comap_eq_of_condIndep hm hpair hW hCI
        (h := s.indicator (fun _ : α => (1 : ℝ))) hs_ind_meas hS_int)
  have hdrop_mA :
      μ[oneS | mA] =ᵐ[μ] μ[oneS | m] := by
    have hs_ind_meas :
        Measurable (s.indicator (fun _ : α => (1 : ℝ))) :=
      measurable_const.indicator hs
    simpa [mA, oneS, S] using
      (condExp_sup_comap_eq_of_condIndep hm hA hW hCI_A
        (h := s.indicator (fun _ : α => (1 : ℝ))) hs_ind_meas hS_int)
  have htower :
      μ[oneS * oneT | mA] =ᵐ[μ] μ[μ[oneS * oneT | mVA] | mA] := by
    exact (MeasureTheory.condExp_condExp_of_le
      (f := oneS * oneT) (m₁ := mA) (m₂ := mVA) (m₀ := mΩ)
      hmA_le_mVA hmVA).symm
  have hinner :
      μ[oneS * oneT | mVA] =ᵐ[μ] μ[oneS | mVA] * oneT := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_right (m := mVA)
      (f := oneS) (g := oneT) hT_mVA hST_int hS_int
  have hinner_drop :
      μ[oneS * oneT | mVA] =ᵐ[μ] μ[oneS | m] * oneT :=
    hinner.trans (hdrop_mVA.mul (Filter.EventuallyEq.rfl))
  have hinner_outer :
      μ[μ[oneS * oneT | mVA] | mA]
        =ᵐ[μ] μ[μ[oneS | m] * oneT | mA] :=
    MeasureTheory.condExp_congr_ae hinner_drop
  have hprod_int :
      MeasureTheory.Integrable (μ[oneS | m] * oneT) μ := by
    exact (MeasureTheory.integrable_condExp (m := mVA)
      (f := oneS * oneT) (μ := μ)).congr hinner_drop
  have hceS_mA :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ mA (μ[oneS | m]) := by
    exact MeasureTheory.stronglyMeasurable_condExp.mono le_sup_left
  have hpull :
      μ[μ[oneS | m] * oneT | mA]
        =ᵐ[μ] μ[oneS | m] * μ[oneT | mA] := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := mA)
      (f := μ[oneS | m]) (g := oneT) hceS_mA hprod_int hT_int
  have hsets :
      μ⟦W ⁻¹' s ∩ V ⁻¹' t | mA⟧
        =ᵐ[μ] μ[oneS * oneT | mA] := by
    rw [show W ⁻¹' s ∩ V ⁻¹' t = S ∩ T by rfl]
    rw [show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
    rfl
  calc
    μ⟦W ⁻¹' s ∩ V ⁻¹' t | mA⟧
        =ᵐ[μ] μ[oneS * oneT | mA] := hsets
    _ =ᵐ[μ] μ[μ[oneS * oneT | mVA] | mA] := htower
    _ =ᵐ[μ] μ[μ[oneS | m] * oneT | mA] := hinner_outer
    _ =ᵐ[μ] μ[oneS | m] * μ[oneT | mA] := hpull
    _ =ᵐ[μ] μ[oneS | mA] * μ[oneT | mA] := by
      exact hdrop_mA.symm.mul (Filter.EventuallyEq.rfl)
    _ =ᵐ[μ] μ⟦W ⁻¹' s | mA⟧ * μ⟦V ⁻¹' t | mA⟧ := by
      rfl

/-- **Extension of `CondIndepFun` by an `m`-measurable function**.

If `W ⟂ Z | m` and `X` is `m`-measurable, then `(W, X) ⟂ Z | m`.

Proof uses `condIndepFun_iff_condExp_inter_preimage_eq_mul` to reduce to the
indicator product identity for measurable rectangles, pulls out the
`m`-measurable indicator `1_{X⁻¹(B_X)}` on both sides, applies `_hCI` on the
W-Z part, and extends from the π-system of rectangles via `CondIndepSets.condIndep'`. -/
theorem condIndepFun_prodMk_of_measurable_left
    {Ω α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {W : Ω → α} {X : Ω → β} {Z : Ω → γ}
    (_hW : Measurable W) (_hZ : Measurable Z) (_hX : Measurable X)
    (_hX_m : Measurable[m] X)
    (_hCI : ProbabilityTheory.CondIndepFun m hm W Z μ) :
    ProbabilityTheory.CondIndepFun m hm (fun ω => (W ω, X ω)) Z μ := by
  let pair : Ω → α × β := fun ω => (W ω, X ω)
  let rects : Set (Set (α × β)) :=
    Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {t : Set β | MeasurableSet t}
  let zsets : Set (Set γ) := {t : Set γ | MeasurableSet t}
  let pPair : Set (Set Ω) :=
    {q | ∃ s : Set α, MeasurableSet s ∧
      ∃ u : Set β, MeasurableSet u ∧ pair ⁻¹' (s ×ˢ u) = q}
  let pZ : Set (Set Ω) := {q | ∃ r : Set γ, r ∈ zsets ∧ Z ⁻¹' r = q}
  have hpair_meas : Measurable pair := _hW.prod _hX
  have hpPair_pi : IsPiSystem pPair := by
    simpa [pPair] using (isPiSystem_prod (α := α) (β := β)).comap pair
  have hpZ_pi : IsPiSystem pZ := by
    simpa [pZ, zsets] using (MeasurableSpace.isPiSystem_measurableSet (α := γ)).comap Z
  have hpPair_meas : ∀ s ∈ pPair, MeasurableSet s := by
    rintro _ ⟨s, hs, u, hu, rfl⟩
    exact hpair_meas (hs.prod hu)
  have hpZ_meas : ∀ s ∈ pZ, MeasurableSet s := by
    rintro _ ⟨r, hr, rfl⟩
    exact _hZ (by simpa [zsets] using hr)
  have hrect : ProbabilityTheory.CondIndepSets m hm pPair pZ μ := by
    rw [ProbabilityTheory.condIndepSets_iff m hm pPair pZ hpPair_meas hpZ_meas μ]
    intro t1 t2 ht1 ht2
    rcases ht1 with ⟨s, hs_meas, u, hu_meas, rfl⟩
    rcases ht2 with ⟨v, hv, rfl⟩
    have hv_meas : MeasurableSet v := by simpa [zsets] using hv
    let A : Set Ω := W ⁻¹' s
    let B : Set Ω := X ⁻¹' u
    let C : Set Ω := Z ⁻¹' v
    have hB_m : MeasurableSet[m] B := _hX_m hu_meas
    have hB_sm : StronglyMeasurable[m] (B.indicator (fun _ : Ω => (1 : ℝ))) :=
      MeasureTheory.stronglyMeasurable_const.indicator hB_m
    have hB_bound : ∀ᵐ ω ∂μ, ‖B.indicator (fun _ : Ω => (1 : ℝ)) ω‖ ≤
        (1 : ℝ) := by
      exact MeasureTheory.ae_of_all μ fun ω => by
        rw [Set.indicator]
        split_ifs <;> simp
    have hAC_int :
        MeasureTheory.Integrable ((A ∩ C).indicator (fun _ : Ω => (1 : ℝ))) μ := by
      refine (MeasureTheory.integrable_indicator_iff ?_).2 MeasureTheory.integrableOn_const
      exact (_hW hs_meas).inter (_hZ hv_meas)
    have hA_int :
        MeasureTheory.Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) μ := by
      refine (MeasureTheory.integrable_indicator_iff ?_).2 MeasureTheory.integrableOn_const
      exact _hW hs_meas
    have hpull_AC :
        μ[B.indicator (fun _ : Ω => (1 : ℝ)) *
            (A ∩ C).indicator (fun _ : Ω => (1 : ℝ)) | m]
          =ᵐ[μ] B.indicator (fun _ : Ω => (1 : ℝ)) *
            μ[(A ∩ C).indicator (fun _ : Ω => (1 : ℝ)) | m] :=
      MeasureTheory.condExp_stronglyMeasurable_mul_of_bound hm hB_sm hAC_int 1 hB_bound
    have hpull_A :
        μ[B.indicator (fun _ : Ω => (1 : ℝ)) *
            A.indicator (fun _ : Ω => (1 : ℝ)) | m]
          =ᵐ[μ] B.indicator (fun _ : Ω => (1 : ℝ)) *
            μ[A.indicator (fun _ : Ω => (1 : ℝ)) | m] :=
      MeasureTheory.condExp_stronglyMeasurable_mul_of_bound hm hB_sm hA_int 1 hB_bound
    have hCIeq :=
      (ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul _hW _hZ).mp
        _hCI s v hs_meas hv_meas
    have hleft :
        μ⟦((A ∩ B) ∩ C) | m⟧
          =ᵐ[μ] μ[B.indicator (fun _ : Ω => (1 : ℝ)) *
            (A ∩ C).indicator (fun _ : Ω => (1 : ℝ)) | m] := by
      rw [show ((A ∩ B) ∩ C) = B ∩ (A ∩ C) by
        ext ω
        simp [and_left_comm, and_assoc]]
      rw [show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
    have hpair :
        μ⟦(A ∩ B) | m⟧
          =ᵐ[μ] μ[B.indicator (fun _ : Ω => (1 : ℝ)) *
            A.indicator (fun _ : Ω => (1 : ℝ)) | m] := by
      rw [show (A ∩ B) = B ∩ A by
        ext ω
        simp [and_comm]]
      rw [show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
    calc
      μ⟦pair ⁻¹' (s ×ˢ u) ∩ Z ⁻¹' v | m⟧
          =ᵐ[μ] μ⟦((A ∩ B) ∩ C) | m⟧ := by
            rfl
      _ =ᵐ[μ] μ[B.indicator (fun _ : Ω => (1 : ℝ)) *
            (A ∩ C).indicator (fun _ : Ω => (1 : ℝ)) | m] := hleft
      _ =ᵐ[μ] B.indicator (fun _ : Ω => (1 : ℝ)) *
            μ[(A ∩ C).indicator (fun _ : Ω => (1 : ℝ)) | m] := hpull_AC
      _ =ᵐ[μ] B.indicator (fun _ : Ω => (1 : ℝ)) * (μ⟦A | m⟧ * μ⟦C | m⟧) := by
        exact hCIeq.mono fun ω hω => by simp [A, C, hω]
      _ =ᵐ[μ] (B.indicator (fun _ : Ω => (1 : ℝ)) * μ⟦A | m⟧) * μ⟦C | m⟧ := by
        exact MeasureTheory.ae_of_all μ fun ω => by
          simp only [Pi.mul_apply]
          ring
      _ =ᵐ[μ] μ[B.indicator (fun _ : Ω => (1 : ℝ)) *
            A.indicator (fun _ : Ω => (1 : ℝ)) | m] * μ⟦C | m⟧ := by
        exact hpull_A.symm.mul (Filter.EventuallyEq.rfl)
      _ =ᵐ[μ] μ⟦A ∩ B | m⟧ * μ⟦C | m⟧ := by
        exact hpair.symm.mul (Filter.EventuallyEq.rfl)
      _ =ᵐ[μ] μ⟦pair ⁻¹' (s ×ˢ u) | m⟧ * μ⟦Z ⁻¹' v | m⟧ := by
        rfl
  rw [ProbabilityTheory.condIndepFun_iff_condIndep]
  have hpPair_eq : pPair = (fun r : Set (α × β) => pair ⁻¹' r) '' rects := by
    ext q
    constructor
    · rintro ⟨s, hs, u, hu, hq⟩
      exact ⟨s ×ˢ u, ⟨s, hs, u, hu, rfl⟩, hq⟩
    · rintro ⟨r, ⟨s, hs, u, hu, rfl⟩, hq⟩
      exact ⟨s, hs, u, hu, hq⟩
  have hgenPair : (inferInstance : MeasurableSpace (α × β)).comap pair =
      MeasurableSpace.generateFrom pPair := by
    rw [hpPair_eq, ← generateFrom_prod, MeasurableSpace.comap_generateFrom]
  have hgenZ : (inferInstance : MeasurableSpace γ).comap Z =
      MeasurableSpace.generateFrom pZ := by
    rw [show (inferInstance : MeasurableSpace γ) = MeasurableSpace.generateFrom zsets by
      exact (MeasurableSpace.generateFrom_measurableSet (α := γ)).symm]
    rw [MeasurableSpace.comap_generateFrom]
    rfl
  rw [hgenPair, hgenZ]
  exact ProbabilityTheory.CondIndepSets.condIndep' hpPair_meas hpZ_meas hpPair_pi hpZ_pi hrect

/-- **Contraction for `CondIndepFun` via a product right side.**

If `X ⟂ Y | (m ⊔ σ(W))` and `X ⟂ W | m`, then
`X ⟂ (Y, W) | m`.  This is the generic semigraphoid contraction step
packaged for downstream projection wrappers. -/
theorem condIndepFun_contraction_of_prodMk
    {Ω α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {X : Ω → α} {Y : Ω → β} {W : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    (h1 : ProbabilityTheory.CondIndepFun
      (m ⊔ MeasurableSpace.comap W inferInstance)
      (sup_le hm hW.comap_le) X Y μ)
    (h2 : ProbabilityTheory.CondIndepFun m hm X W μ) :
    ProbabilityTheory.CondIndepFun m hm X (fun ω => (Y ω, W ω)) μ := by
  let pair : Ω → β × γ := fun ω => (Y ω, W ω)
  let xsets : Set (Set Ω) := {q | ∃ s : Set α, MeasurableSet s ∧ X ⁻¹' s = q}
  let pairsets : Set (Set Ω) :=
    {q | ∃ t : Set β, MeasurableSet t ∧
      ∃ u : Set γ, MeasurableSet u ∧ pair ⁻¹' (t ×ˢ u) = q}
  have hpair_meas : Measurable pair := hY.prod hW
  have hpX_pi : IsPiSystem xsets := by
    simpa [xsets] using (MeasurableSpace.isPiSystem_measurableSet (α := α)).comap X
  have hpPair_pi : IsPiSystem pairsets := by
    simpa [pairsets] using (isPiSystem_prod (α := β) (β := γ)).comap pair
  have hpX_meas : ∀ s ∈ xsets, MeasurableSet s := by
    rintro _ ⟨s, hs, rfl⟩
    exact hX hs
  have hpPair_meas : ∀ s ∈ pairsets, MeasurableSet s := by
    rintro _ ⟨t, ht, u, hu, rfl⟩
    exact hpair_meas (ht.prod hu)
  have hrect : ProbabilityTheory.CondIndepSets m hm xsets pairsets μ := by
    rw [ProbabilityTheory.condIndepSets_iff m hm xsets pairsets hpX_meas hpPair_meas μ]
    intro t1 t2 ht1 ht2
    rcases ht1 with ⟨s, hs_meas, rfl⟩
    rcases ht2 with ⟨t, ht_meas, u, hu_meas, rfl⟩
    let A : Set Ω := X ⁻¹' s
    let B : Set Ω := Y ⁻¹' t
    let C : Set Ω := W ⁻¹' u
    let oneA : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
    let oneB : Ω → ℝ := B.indicator (fun _ => (1 : ℝ))
    let oneC : Ω → ℝ := C.indicator (fun _ => (1 : ℝ))
    let mW : MeasurableSpace Ω := m ⊔ MeasurableSpace.comap W inferInstance
    have hA_meas : @MeasurableSet Ω mΩ A := hX hs_meas
    have hB_meas : @MeasurableSet Ω mΩ B := hY ht_meas
    have hC_meas : @MeasurableSet Ω mΩ C := hW hu_meas
    have hmW : mW ≤ mΩ := by
      dsimp [mW]
      exact sup_le hm hW.comap_le
    have hm_le_mW : m ≤ mW := by
      dsimp [mW]
      exact le_sup_left
    have hC_mW : @MeasurableSet Ω mW C := by
      dsimp [mW, C]
      exact Measurable.of_comap_le le_sup_right hu_meas
    have hC_sm : @MeasureTheory.StronglyMeasurable Ω ℝ _ mW oneC :=
      MeasureTheory.stronglyMeasurable_const.indicator hC_mW
    have hceA_m : @MeasureTheory.StronglyMeasurable Ω ℝ _ m (μ[oneA | m]) :=
      MeasureTheory.stronglyMeasurable_condExp
    have hceA_m_mW : @MeasureTheory.StronglyMeasurable Ω ℝ _ mW (μ[oneA | m]) :=
      hceA_m.mono hm_le_mW
    have hA_int : MeasureTheory.Integrable oneA μ := by
      refine (MeasureTheory.integrable_indicator_iff hA_meas).2 ?_
      exact MeasureTheory.integrableOn_const
    have hB_int : MeasureTheory.Integrable oneB μ := by
      refine (MeasureTheory.integrable_indicator_iff hB_meas).2 ?_
      exact MeasureTheory.integrableOn_const
    have hC_int : MeasureTheory.Integrable oneC μ := by
      refine (MeasureTheory.integrable_indicator_iff hC_meas).2 ?_
      exact MeasureTheory.integrableOn_const
    have hAB_int : MeasureTheory.Integrable (oneA * oneB) μ := by
      refine ((MeasureTheory.integrable_indicator_iff (hA_meas.inter hB_meas)).2
        (MeasureTheory.integrableOn_const (μ := μ) (s := A ∩ B) (C := (1 : ℝ)))).congr ?_
      exact MeasureTheory.ae_of_all μ fun ω => by
        by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [oneA, oneB, hωA, hωB]
    have hBC_int : MeasureTheory.Integrable (oneB * oneC) μ := by
      refine ((MeasureTheory.integrable_indicator_iff (hB_meas.inter hC_meas)).2
        (MeasureTheory.integrableOn_const (μ := μ) (s := B ∩ C) (C := (1 : ℝ)))).congr ?_
      exact MeasureTheory.ae_of_all μ fun ω => by
        by_cases hωB : ω ∈ B <;> by_cases hωC : ω ∈ C <;> simp [oneB, oneC, hωB, hωC]
    have hABC_int : MeasureTheory.Integrable ((oneA * oneB) * oneC) μ := by
      refine ((MeasureTheory.integrable_indicator_iff ((hA_meas.inter hB_meas).inter hC_meas)).2
        (MeasureTheory.integrableOn_const (μ := μ) (s := (A ∩ B) ∩ C) (C := (1 : ℝ)))).congr ?_
      exact MeasureTheory.ae_of_all μ fun ω => by
        by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> by_cases hωC : ω ∈ C <;>
          simp [oneA, oneB, oneC, hωA, hωB, hωC]
    have hCI1 :=
      (ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mp
        h1 s t hs_meas ht_meas
    have hCI2 :=
      (ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul hX hW).mp
        h2 s u hs_meas hu_meas
    have hdropA :
        μ[oneA | mW] =ᵐ[μ] μ[oneA | m] := by
      have hs_ind_meas : Measurable (s.indicator (fun _ : α => (1 : ℝ))) :=
        measurable_const.indicator hs_meas
      simpa [mW, oneA, A] using
        (condExp_sup_comap_eq_of_condIndep hm hW hX h2
          (h := s.indicator (fun _ : α => (1 : ℝ))) hs_ind_meas hA_int)
    have hpullC_AB :
        μ[(oneA * oneB) * oneC | mW] =ᵐ[μ] μ[oneA * oneB | mW] * oneC := by
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_right (m := mW)
        (f := oneA * oneB) (g := oneC) hC_sm hABC_int hAB_int
    have hpullC_B :
        μ[oneB * oneC | mW] =ᵐ[μ] μ[oneB | mW] * oneC := by
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_right (m := mW)
        (f := oneB) (g := oneC) hC_sm hBC_int hB_int
    have hAB_mW :
        μ[oneA * oneB | mW] =ᵐ[μ] μ[oneA | mW] * μ[oneB | mW] := by
      have hsets :
          μ⟦X ⁻¹' s ∩ Y ⁻¹' t | mW⟧ =ᵐ[μ] μ[oneA * oneB | mW] := by
        rw [show X ⁻¹' s ∩ Y ⁻¹' t = A ∩ B by rfl]
        rw [show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
        rfl
      exact hsets.symm.trans hCI1
    have hAB_mW_drop :
        μ[oneA * oneB | mW] =ᵐ[μ] μ[oneA | m] * μ[oneB | mW] :=
      hAB_mW.trans (hdropA.mul (Filter.EventuallyEq.rfl))
    have hABC_tower :
        μ[(oneA * oneB) * oneC | m] =ᵐ[μ]
          μ[μ[(oneA * oneB) * oneC | mW] | m] := by
      exact (MeasureTheory.condExp_condExp_of_le
        (f := (oneA * oneB) * oneC) (m₁ := m) (m₂ := mW) (m₀ := mΩ)
        hm_le_mW hmW).symm
    have hinner_ABC :
        μ[μ[(oneA * oneB) * oneC | mW] | m] =ᵐ[μ]
          μ[(μ[oneA | m] * μ[oneB | mW]) * oneC | m] := by
      exact MeasureTheory.condExp_congr_ae (hpullC_AB.trans
        (hAB_mW_drop.mul (Filter.EventuallyEq.rfl)))
    have hpullA :
        μ[(μ[oneA | m] * μ[oneB | mW]) * oneC | m] =ᵐ[μ]
          μ[oneA | m] * μ[μ[oneB | mW] * oneC | m] := by
      have hint :
          MeasureTheory.Integrable ((μ[oneA | m] * μ[oneB | mW]) * oneC) μ := by
        exact (MeasureTheory.integrable_condExp (m := mW)
          (f := (oneA * oneB) * oneC) (μ := μ)).congr
            (hpullC_AB.trans (hAB_mW_drop.mul (Filter.EventuallyEq.rfl)))
      have hint_assoc :
          MeasureTheory.Integrable (μ[oneA | m] * (μ[oneB | mW] * oneC)) μ :=
        hint.congr (MeasureTheory.ae_of_all μ fun ω => by ring_nf)
      have hB_mW_C_int :
          MeasureTheory.Integrable (μ[oneB | mW] * oneC) μ :=
        (MeasureTheory.integrable_condExp (m := mW) (f := oneB * oneC) (μ := μ)).congr
          hpullC_B
      calc
        μ[(μ[oneA | m] * μ[oneB | mW]) * oneC | m]
            =ᵐ[μ] μ[μ[oneA | m] * (μ[oneB | mW] * oneC) | m] := by
              refine MeasureTheory.condExp_congr_ae ?_
              exact MeasureTheory.ae_of_all μ fun ω => by ring_nf
        _ =ᵐ[μ] μ[oneA | m] * μ[μ[oneB | mW] * oneC | m] :=
          MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := m)
            (f := μ[oneA | m]) (g := μ[oneB | mW] * oneC) hceA_m hint_assoc
            hB_mW_C_int
    have hBC_tower :
        μ[oneB * oneC | m] =ᵐ[μ] μ[μ[oneB * oneC | mW] | m] := by
      exact (MeasureTheory.condExp_condExp_of_le
        (f := oneB * oneC) (m₁ := m) (m₂ := mW) (m₀ := mΩ)
        hm_le_mW hmW).symm
    have hBC_inner :
        μ[μ[oneB * oneC | mW] | m] =ᵐ[μ] μ[μ[oneB | mW] * oneC | m] :=
      MeasureTheory.condExp_congr_ae hpullC_B
    have hleft_sets :
        μ⟦X ⁻¹' s ∩ pair ⁻¹' (t ×ˢ u) | m⟧
          =ᵐ[μ] μ[(oneA * oneB) * oneC | m] := by
      rw [show X ⁻¹' s ∩ pair ⁻¹' (t ×ˢ u) = (A ∩ B) ∩ C by
        ext ω
        simp [A, B, C, pair, and_assoc]]
      rw [show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
      refine MeasureTheory.condExp_congr_ae ?_
      exact MeasureTheory.ae_of_all μ fun ω => by
        by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> by_cases hωC : ω ∈ C <;>
          simp [oneA, oneB, oneC, hωA, hωB, hωC]
    have hpair_sets :
        μ⟦pair ⁻¹' (t ×ˢ u) | m⟧ =ᵐ[μ] μ[oneB * oneC | m] := by
      rw [show pair ⁻¹' (t ×ˢ u) = B ∩ C by
        ext ω
        simp [B, C, pair]]
      rw [show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
      rfl
    calc
      μ⟦X ⁻¹' s ∩ pair ⁻¹' (t ×ˢ u) | m⟧
          =ᵐ[μ] μ[(oneA * oneB) * oneC | m] := hleft_sets
      _ =ᵐ[μ] μ[μ[(oneA * oneB) * oneC | mW] | m] := hABC_tower
      _ =ᵐ[μ] μ[(μ[oneA | m] * μ[oneB | mW]) * oneC | m] := hinner_ABC
      _ =ᵐ[μ] μ[oneA | m] * μ[μ[oneB | mW] * oneC | m] := hpullA
      _ =ᵐ[μ] μ[oneA | m] * μ[μ[oneB * oneC | mW] | m] := by
        exact (Filter.EventuallyEq.rfl).mul (MeasureTheory.condExp_congr_ae hpullC_B.symm)
      _ =ᵐ[μ] μ[oneA | m] * μ[oneB * oneC | m] := by
        exact (Filter.EventuallyEq.rfl).mul hBC_tower.symm
      _ =ᵐ[μ] μ⟦X ⁻¹' s | m⟧ * μ⟦pair ⁻¹' (t ×ˢ u) | m⟧ := by
        exact (Filter.EventuallyEq.rfl).mul hpair_sets.symm
  rw [ProbabilityTheory.condIndepFun_iff_condIndep]
  have hpX_eq : xsets = (fun r : Set α => X ⁻¹' r) '' {s : Set α | MeasurableSet s} := by
    ext q
    constructor
    · rintro ⟨s, hs, hq⟩
      exact ⟨s, hs, hq⟩
    · rintro ⟨s, hs, hq⟩
      exact ⟨s, hs, hq⟩
  have hpPair_eq :
      pairsets = (fun r : Set (β × γ) => pair ⁻¹' r) ''
        Set.image2 (· ×ˢ ·) {t : Set β | MeasurableSet t} {u : Set γ | MeasurableSet u} := by
    ext q
    constructor
    · rintro ⟨t, ht, u, hu, hq⟩
      exact ⟨t ×ˢ u, ⟨t, ht, u, hu, rfl⟩, hq⟩
    · rintro ⟨r, ⟨t, ht, u, hu, rfl⟩, hq⟩
      exact ⟨t, ht, u, hu, hq⟩
  have hgenX : (inferInstance : MeasurableSpace α).comap X =
      MeasurableSpace.generateFrom xsets := by
    rw [show (inferInstance : MeasurableSpace α) =
      MeasurableSpace.generateFrom {s : Set α | MeasurableSet s} by
        exact (MeasurableSpace.generateFrom_measurableSet (α := α)).symm]
    rw [MeasurableSpace.comap_generateFrom]
    rfl
  have hgenPair : (inferInstance : MeasurableSpace (β × γ)).comap pair =
      MeasurableSpace.generateFrom pairsets := by
    rw [hpPair_eq, ← generateFrom_prod, MeasurableSpace.comap_generateFrom]
  rw [hgenX, hgenPair]
  exact ProbabilityTheory.CondIndepSets.condIndep' hpX_meas hpPair_meas hpX_pi hpPair_pi hrect

end Causalean
