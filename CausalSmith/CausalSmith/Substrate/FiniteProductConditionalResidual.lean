import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Conditional residuals for finite products

This file gives a finite-partition proof that coordinate observations from a
finite i.i.d. product remain conditionally independent after conditioning on
their coordinatewise finite-valued designs.  It also identifies a useful
zero-conditional-mean consequence for residuals centered on every design
fiber.
-/

namespace CausalSmith.Substrate.FiniteProductConditionalResidual

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {ι S Z : Type*}
  [Fintype ι] [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace Z] [StandardBorelSpace Z]

noncomputable def finiteIIDProduct
    (μ : Measure Z) [IsProbabilityMeasure μ] : Measure (ι → Z) :=
  Measure.pi (fun _ : ι => μ)

noncomputable instance finiteIIDProduct.instIsProbabilityMeasure
    (μ : Measure Z) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (finiteIIDProduct (ι := ι) μ) := by
  unfold finiteIIDProduct
  infer_instance

def finiteProductDesign (D : Z → S) (ω : ι → Z) : ι → S :=
  fun i => D (ω i)

noncomputable def finiteProductDesignSigma (D : Z → S) :
    MeasurableSpace (ι → Z) :=
  MeasurableSpace.comap (finiteProductDesign D) inferInstance

def finiteProductResidual (r : Z → ℝ) (i : ι) (ω : ι → Z) : ℝ :=
  r (ω i)

lemma finiteProductDesign_measurable (D : Z → S) (hD : Measurable D) :
    Measurable (finiteProductDesign (ι := ι) D) := by
  rw [measurable_pi_iff]
  exact fun i => hD.comp (measurable_pi_apply i)

lemma finiteProductDesignSigma_le (D : Z → S) (hD : Measurable D) :
    finiteProductDesignSigma (ι := ι) D ≤
      (inferInstance : MeasurableSpace (ι → Z)) :=
  (finiteProductDesign_measurable D hD).comap_le

private lemma condExp_eq_zero_of_finite_fiber_integral_zero
    {Ω T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (Y : Ω → T) (hY : Measurable Y)
    (f : Ω → ℝ) (hf : Integrable f ν)
    (hfiber : ∀ t : T, ∫ ω in Y ⁻¹' {t}, f ω ∂ν = 0) :
    ν[f | MeasurableSpace.comap Y inferInstance] =ᵐ[ν] 0 := by
  have hzero :
      (fun _ : Ω => (0 : ℝ)) =ᵐ[ν]
        ν[f | MeasurableSpace.comap Y
          (inferInstance : MeasurableSpace T)] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hY.comap_le hf ?_ ?_ ?_
    · intro t _ _
      exact integrableOn_zero
    · intro t ht _
      rcases ht with ⟨u, hu, rfl⟩
      rw [integral_zero]
      classical
      let U : Finset T := Finset.univ.filter (· ∈ u)
      rw [show Y ⁻¹' u = ⋃ y ∈ U, Y ⁻¹' {y} by
        ext ω
        simp [U]]
      rw [integral_biUnion_finset]
      · simp [hfiber]
      · intro y _
        exact hY (measurableSet_singleton y)
      · exact Set.pairwiseDisjoint_fiber Y U
      · intro y _
        exact hf.integrableOn
    · exact stronglyMeasurable_zero.aestronglyMeasurable
  exact hzero.symm

private noncomputable def finiteCondProb
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (ν : Measure Ω) (Y : Ω → T) (A : Set Ω) (t : T) : ℝ :=
  (ν.real (Y ⁻¹' {t}))⁻¹ * ν.real ((Y ⁻¹' {t}) ∩ A)

private lemma finiteCondProb_le_one
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (ν : Measure Ω) [IsFiniteMeasure ν] (Y : Ω → T)
    (A : Set Ω) (t : T) :
    finiteCondProb ν Y A t ≤ 1 := by
  unfold finiteCondProb
  by_cases hzero : ν.real (Y ⁻¹' {t}) = 0
  · simp [hzero]
  · rw [inv_mul_le_one₀
      (lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero))]
    exact measureReal_mono (Set.inter_subset_left)

private lemma finiteCondProb_nonneg
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (ν : Measure Ω) (Y : Ω → T) (A : Set Ω) (t : T) :
    0 ≤ finiteCondProb ν Y A t :=
  mul_nonneg (inv_nonneg.mpr measureReal_nonneg) measureReal_nonneg

private lemma condExp_indicator_finite_comap
    {Ω T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (Y : Ω → T) (hY : Measurable Y)
    (A : Set Ω) (hA : MeasurableSet A) :
    ν[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap Y inferInstance] =ᵐ[ν]
      fun ω => finiteCondProb ν Y A (Y ω) := by
  let q : T → ℝ := finiteCondProb ν Y A
  have hq : Measurable q := measurable_of_finite q
  have hqm : StronglyMeasurable[
      MeasurableSpace.comap Y (inferInstance : MeasurableSpace T)] (q ∘ Y) :=
    (hq.comp (comap_measurable Y)).stronglyMeasurable
  have hqΩ : StronglyMeasurable (q ∘ Y) :=
    (hq.comp hY).stronglyMeasurable
  have hq_int : Integrable (q ∘ Y) ν := by
    apply Integrable.of_bound hqΩ.aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · change -1 ≤ finiteCondProb ν Y A (Y ω)
      exact (by norm_num : (-1 : ℝ) ≤ 0).trans
        (finiteCondProb_nonneg ν Y A (Y ω))
    · exact finiteCondProb_le_one ν Y A (Y ω)
  have hind : Integrable (A.indicator fun _ => (1 : ℝ)) ν :=
    (integrable_const 1).indicator hA
  have hversion :
      (q ∘ Y) =ᵐ[ν]
        ν[A.indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap Y
            (inferInstance : MeasurableSpace T)] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hY.comap_le hind
    · intro t _ _
      exact hq_int.integrableOn
    · intro t ht _
      rcases ht with ⟨u, hu, rfl⟩
      classical
      let U : Finset T := Finset.univ.filter (· ∈ u)
      rw [show Y ⁻¹' u = ⋃ y ∈ U, Y ⁻¹' {y} by
        ext ω
        simp [U]]
      rw [integral_biUnion_finset, integral_biUnion_finset]
      · apply Finset.sum_congr rfl
        intro y hy
        have heq :
            (q ∘ Y) =ᵐ[ν.restrict (Y ⁻¹' {y})] fun _ => q y := by
          filter_upwards [ae_restrict_mem
            (hY (measurableSet_singleton y))] with ω hω
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
          exact congrArg q hω
        rw [integral_congr_ae heq, integral_const]
        change ((ν.restrict (Y ⁻¹' {y})) Set.univ).toReal * q y =
          ∫ x in Y ⁻¹' {y}, A.indicator (fun _ => (1 : ℝ)) x ∂ν
        rw [Measure.restrict_apply_univ]
        rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
        unfold q finiteCondProb
        change ν.real (Y ⁻¹' {y}) *
            ((ν.real (Y ⁻¹' {y}))⁻¹ *
              ν.real ((Y ⁻¹' {y}) ∩ A)) =
          ((ν.restrict (Y ⁻¹' {y})) A).toReal
        rw [Measure.restrict_apply hA, Set.inter_comm A]
        change ν.real (Y ⁻¹' {y}) *
            ((ν.real (Y ⁻¹' {y}))⁻¹ *
              ν.real ((Y ⁻¹' {y}) ∩ A)) =
          ν.real ((Y ⁻¹' {y}) ∩ A)
        by_cases hz : ν.real (Y ⁻¹' {y}) = 0
        · have hz' : ν.real ((Y ⁻¹' {y}) ∩ A) = 0 :=
            le_antisymm
              ((measureReal_mono Set.inter_subset_left).trans hz.le)
              measureReal_nonneg
          simp [hz, hz']
        · field_simp
      · intro y _
        exact hY (measurableSet_singleton y)
      · exact Set.pairwiseDisjoint_fiber Y U
      · intro y _
        exact hind.integrableOn
      · intro y _
        exact hY (measurableSet_singleton y)
      · exact Set.pairwiseDisjoint_fiber Y U
      · intro y _
        exact hq_int.integrableOn
    · exact hqm.aestronglyMeasurable
  exact hversion.symm

private lemma ae_fiber_measure_ne_zero
    {Ω T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [MeasurableSpace Ω]
    (ν : Measure Ω) (Y : Ω → T) (hY : Measurable Y) :
    ∀ᵐ ω ∂ν, ν (Y ⁻¹' {Y ω}) ≠ 0 := by
  let N : Finset T := Finset.univ.filter fun t => ν (Y ⁻¹' {t}) = 0
  have hnull : ν (⋃ t ∈ N, Y ⁻¹' {t}) = 0 := by
    rw [measure_biUnion_finset]
    · simp [N]
    · exact Set.pairwiseDisjoint_fiber Y N
    · intro t _
      exact hY (measurableSet_singleton t)
  apply ae_iff.2
  apply measure_mono_null _ hnull
  intro ω hω
  simp only [Set.mem_setOf_eq, not_not] at hω
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨Y ω, ⟨(by simp [N, hω]), rfl⟩⟩

private lemma finiteCondProb_iInter
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (D : Z → S) (hD : Measurable D)
    (r : Z → ℝ) (hr : Measurable r)
    (I : Finset ι) (sets : ι → Set ℝ)
    (hsets : ∀ i ∈ I, MeasurableSet (sets i))
    (ω : ι → Z)
    (hpositive :
      finiteIIDProduct (ι := ι) μ
        (finiteProductDesign D ⁻¹' {finiteProductDesign D ω}) ≠ 0) :
    finiteCondProb (finiteIIDProduct (ι := ι) μ)
        (finiteProductDesign D)
        (⋂ i ∈ I, finiteProductResidual r i ⁻¹' sets i)
        (finiteProductDesign D ω) =
      ∏ i ∈ I,
        finiteCondProb (finiteIIDProduct (ι := ι) μ)
          (finiteProductDesign D)
          (finiteProductResidual r i ⁻¹' sets i)
          (finiteProductDesign D ω) := by
  classical
  letI : IsProbabilityMeasure (finiteIIDProduct (ι := ι) μ) := by
    unfold finiteIIDProduct
    infer_instance
  let F : ι → Set Z := fun i => D ⁻¹' {D (ω i)}
  let G : ι → Set Z := fun i =>
    if i ∈ I then F i ∩ r ⁻¹' sets i else F i
  have hF : ∀ i, MeasurableSet (F i) :=
    fun i => hD (measurableSet_singleton (D (ω i)))
  have hG : ∀ i, MeasurableSet (G i) := by
    intro i
    by_cases hi : i ∈ I
    · simp only [G, hi, if_pos]
      exact (hF i).inter (hr (hsets i hi))
    · simp [G, hi, hF i]
  have hfiber :
      finiteProductDesign D ⁻¹' {finiteProductDesign D ω} =
        Set.univ.pi F := by
    ext ω'
    simp [finiteProductDesign, F, funext_iff]
  have hinter :
      (finiteProductDesign D ⁻¹' {finiteProductDesign D ω}) ∩
          (⋂ i ∈ I, finiteProductResidual r i ⁻¹' sets i) =
        Set.univ.pi G := by
    ext ω'
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_coe,
      Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨hdesign, hevents⟩ i
      by_cases hi : i ∈ I
      · simp only [G, hi, if_pos, Set.mem_inter_iff,
          Set.mem_preimage]
        exact ⟨by
          simpa [finiteProductDesign, F, funext_iff] using
            congrFun hdesign i, hevents i hi⟩
      · simp only [G, hi, if_neg]
        simpa [finiteProductDesign, F, funext_iff] using
          congrFun hdesign i
    · intro hGω
      constructor
      · funext i
        have hi := hGω i
        by_cases hmem : i ∈ I
        · have hi' : ω' i ∈ F i ∩ r ⁻¹' sets i := by
            simpa [G, hmem] using hi
          simpa [F] using hi'.1
        · have hi' : ω' i ∈ F i := by
            simpa [G, hmem] using hi
          simpa [F] using hi'
      · intro i hi
        have hi' : ω' i ∈ F i ∩ r ⁻¹' sets i := by
          simpa [G, hi] using hGω i
        simpa [finiteProductResidual] using hi'.2
  have hμF :
      (finiteIIDProduct (ι := ι) μ).real
          (finiteProductDesign D ⁻¹' {finiteProductDesign D ω}) =
        ∏ i, μ.real (F i) := by
    rw [hfiber]
    simp only [finiteIIDProduct, Measure.pi_pi, measureReal_def,
      ENNReal.toReal_prod]
  have hμG :
      (finiteIIDProduct (ι := ι) μ).real
          ((finiteProductDesign D ⁻¹' {finiteProductDesign D ω}) ∩
            (⋂ i ∈ I, finiteProductResidual r i ⁻¹' sets i)) =
        ∏ i, μ.real (G i) := by
    rw [hinter]
    simp only [finiteIIDProduct, Measure.pi_pi, measureReal_def,
      ENNReal.toReal_prod]
  let a : ι → ℝ := fun i => μ.real (F i)
  let b : ι → ℝ := fun i => μ.real (F i ∩ r ⁻¹' sets i)
  have hprod_ne : (∏ i, a i) ≠ 0 := by
    rw [← hμF]
    exact (ENNReal.toReal_ne_zero.mpr
      ⟨hpositive, measure_ne_top _ _⟩)
  have ha : ∀ i, a i ≠ 0 := by
    rw [Finset.prod_ne_zero_iff] at hprod_ne
    exact fun i => hprod_ne i (Finset.mem_univ i)
  have hsingle (i : ι) (hi : i ∈ I) :
      finiteCondProb (finiteIIDProduct (ι := ι) μ)
          (finiteProductDesign D)
          (finiteProductResidual r i ⁻¹' sets i)
          (finiteProductDesign D ω) =
        (a i)⁻¹ * b i := by
    let H : ι → Set Z := fun j =>
      if j = i then F j ∩ r ⁻¹' sets i else F j
    have hH : ∀ j, MeasurableSet (H j) := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [H, if_pos]
        exact (hF i).inter (hr (hsets i hi))
      · simp [H, hji, hF j]
    have hinteri :
        (finiteProductDesign D ⁻¹' {finiteProductDesign D ω}) ∩
            (finiteProductResidual r i ⁻¹' sets i) =
          Set.univ.pi H := by
      ext ω'
      simp only [Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · rintro ⟨hdesign, hevent⟩ j
        by_cases hji : j = i
        · subst j
          simp only [H, if_pos, Set.mem_inter_iff]
          exact ⟨by
            simpa [finiteProductDesign, F, funext_iff] using
              congrFun hdesign i, hevent⟩
        · simp only [H, hji, if_neg]
          simpa [finiteProductDesign, F, funext_iff] using
            congrFun hdesign j
      · intro hHω
        constructor
        · funext j
          by_cases hji : j = i
          · subst j
            have hj : ω' i ∈ F i ∩ r ⁻¹' sets i := by
              simpa [H] using hHω i
            simpa [F] using hj.1
          · have hj : ω' j ∈ F j := by
              simpa [H, hji] using hHω j
            simpa [F] using hj
        · have hj : ω' i ∈ F i ∩ r ⁻¹' sets i := by
            simpa [H] using hHω i
          simpa [finiteProductResidual] using hj.2
    have hμH :
        (finiteIIDProduct (ι := ι) μ).real
            ((finiteProductDesign D ⁻¹' {finiteProductDesign D ω}) ∩
              (finiteProductResidual r i ⁻¹' sets i)) =
          ∏ j, μ.real (H j) := by
      rw [hinteri]
      simp only [finiteIIDProduct, Measure.pi_pi, measureReal_def,
        ENNReal.toReal_prod]
    unfold finiteCondProb
    rw [hμF, hμH]
    simp only [a, b, H, apply_ite]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem
      (Finset.mem_univ i)]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem
      (Finset.mem_univ i)]
    simp only [if_pos]
    have hrest_eq :
        (∏ j ∈ Finset.univ \ {i},
            if j = i then μ.real (F j ∩ r ⁻¹' sets i)
            else μ.real (F j)) =
          ∏ j ∈ Finset.univ \ {i}, μ.real (F j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro hji
        exact (Finset.mem_sdiff.mp hj).2 (by simpa [hji])
      simp [hji]
    rw [hrest_eq]
    have hrest : (∏ j ∈ Finset.univ \ {i}, μ.real (F j)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact ha j
    field_simp [ha i, hrest]
  rw [Finset.prod_congr rfl (fun i hi => hsingle i hi)]
  unfold finiteCondProb
  rw [hμF, hμG]
  simp only [G, a, b, apply_ite]
  rw [show (∏ i, if i ∈ I then μ.real (F i ∩ r ⁻¹' sets i)
        else μ.real (F i)) =
      (∏ i ∈ I, b i) * ∏ i ∈ Finset.univ \ I, a i by
    let K : ι → ℝ := fun i =>
      if i ∈ I then μ.real (F i ∩ r ⁻¹' sets i) else μ.real (F i)
    have hd : Disjoint I (Finset.univ \ I) := by
      refine Finset.disjoint_left.mpr ?_
      intro i hi hi'
      exact (Finset.mem_sdiff.mp hi').2 hi
    have hu : I ∪ (Finset.univ \ I) = Finset.univ := by
      ext i
      simp
    change (∏ i, K i) =
      (∏ i ∈ I, b i) * ∏ i ∈ Finset.univ \ I, a i
    calc
      (∏ i, K i) = ∏ i ∈ I ∪ (Finset.univ \ I), K i := by rw [hu]
      _ = (∏ i ∈ I, K i) * ∏ i ∈ Finset.univ \ I, K i :=
        Finset.prod_union hd
      _ = (∏ i ∈ I, b i) * ∏ i ∈ Finset.univ \ I, a i := by
        congr 1
        · apply Finset.prod_congr rfl
          intro i hi
          simp [K, hi, b]
        · apply Finset.prod_congr rfl
          intro i hi
          have hi' : i ∉ I := (Finset.mem_sdiff.mp hi).2
          simp [K, hi', a]]
  rw [show (∏ i, μ.real (F i)) =
      (∏ i ∈ I, a i) * ∏ i ∈ Finset.univ \ I, a i by
    have hd : Disjoint I (Finset.univ \ I) := by
      refine Finset.disjoint_left.mpr ?_
      intro i hi hi'
      exact (Finset.mem_sdiff.mp hi').2 hi
    have hu : I ∪ (Finset.univ \ I) = Finset.univ := by
      ext i
      simp
    simp only [a]
    calc
      (∏ i, μ.real (F i)) =
          ∏ i ∈ I ∪ (Finset.univ \ I), μ.real (F i) := by rw [hu]
      _ = (∏ i ∈ I, μ.real (F i)) *
          ∏ i ∈ Finset.univ \ I, μ.real (F i) :=
        Finset.prod_union hd]
  rw [Finset.prod_mul_distrib]
  change ((∏ i ∈ I, a i) * ∏ i ∈ Finset.univ \ I, a i)⁻¹ *
      ((∏ i ∈ I, b i) * ∏ i ∈ Finset.univ \ I, a i) =
    (∏ i ∈ I, (a i)⁻¹) * ∏ i ∈ I, b i
  rw [Finset.prod_inv_distrib]
  have houtside : (∏ i ∈ Finset.univ \ I, a i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ha i
  have hinside : (∏ i ∈ I, a i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ha i
  field_simp [houtside, hinside]

private lemma integral_residual_on_product_design_fiber
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (D : Z → S) (hD : Measurable D)
    (r : Z → ℝ) (hr : Measurable r) (hr_int : Integrable r μ)
    (hfiber : ∀ s : S, ∫ z in D ⁻¹' {s}, r z ∂μ = 0)
    (i : ι) (svec : ι → S) :
    ∫ ω in finiteProductDesign D ⁻¹' {svec},
        finiteProductResidual r i ω ∂finiteIIDProduct (ι := ι) μ = 0 := by
  classical
  let F : ι → Set Z := fun j => D ⁻¹' {svec j}
  have hF : ∀ j, MeasurableSet (F j) :=
    fun j => hD (measurableSet_singleton (svec j))
  have hset :
      finiteProductDesign D ⁻¹' {svec} = Set.univ.pi F := by
    ext ω
    simp [finiteProductDesign, F, funext_iff]
  rw [hset]
  change ∫ ω, finiteProductResidual r i ω ∂
      ((Measure.pi (fun _ : ι => μ)).restrict (Set.univ.pi F)) = 0
  rw [Measure.restrict_pi_pi]
  change ∫ ω, r (ω i) ∂Measure.pi (fun j => μ.restrict (F j)) = 0
  rw [← integral_map (measurable_pi_apply i).aemeasurable
      hr.aestronglyMeasurable, Measure.pi_map_eval]
  rw [integral_smul_measure]
  simp only [smul_eq_mul]
  change (∏ j ∈ Finset.univ.erase i,
      (μ.restrict (F j)) Set.univ).toReal *
        (∫ x in D ⁻¹' {svec i}, r x ∂μ) = 0
  rw [hfiber]
  simp

lemma finiteProductResidual_measurable (r : Z → ℝ) (hr : Measurable r)
    (i : ι) :
    Measurable (finiteProductResidual r i) :=
  hr.comp (measurable_pi_apply i)

lemma finiteProductResidual_integrable
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (r : Z → ℝ) (hr_int : Integrable r μ) (i : ι) :
    Integrable (finiteProductResidual r i) (finiteIIDProduct (ι := ι) μ) := by
  unfold finiteProductResidual finiteIIDProduct
  exact integrable_comp_eval hr_int

theorem finiteProductConditionalResidual
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (D : Z → S) (hD : Measurable D)
    (r : Z → ℝ) (hr : Measurable r) (hr_int : Integrable r μ)
    (hfiber :
      ∀ s : S, ∫ z in D ⁻¹' {s}, r z ∂μ = 0) :
    (∀ i : ι, ∀ᵐ ω ∂(finiteIIDProduct (ι := ι) μ).trim
        (finiteProductDesignSigma_le D hD),
      ∫ ω', finiteProductResidual r i ω'
        ∂ProbabilityTheory.condExpKernel
          (mΩ := inferInstance) (finiteIIDProduct (ι := ι) μ)
            (finiteProductDesignSigma (ι := ι) D) ω = 0) ∧
    ProbabilityTheory.iCondIndepFun
      (finiteProductDesignSigma (ι := ι) D)
      (finiteProductDesignSigma_le D hD)
      (finiteProductResidual r) (μ := finiteIIDProduct (ι := ι) μ) := by
  classical
  let ν := finiteIIDProduct (ι := ι) μ
  let Y := finiteProductDesign (ι := ι) D
  have hY : Measurable Y := finiteProductDesign_measurable D hD
  have hm : finiteProductDesignSigma (ι := ι) D ≤
      (inferInstance : MeasurableSpace (ι → Z)) :=
    finiteProductDesignSigma_le D hD
  letI : IsProbabilityMeasure ν := by
    unfold ν finiteIIDProduct
    infer_instance
  constructor
  · intro i
    have hri : Integrable (finiteProductResidual r i) ν :=
      finiteProductResidual_integrable μ r hr_int i
    have hce :
        ν[finiteProductResidual r i |
          finiteProductDesignSigma (ι := ι) D] =ᵐ[ν] 0 := by
      apply condExp_eq_zero_of_finite_fiber_integral_zero
        ν Y hY (finiteProductResidual r i) hri
      intro svec
      exact integral_residual_on_product_design_fiber
        μ D hD r hr hr_int hfiber i svec
    have hce_trim :
        ν[finiteProductResidual r i |
          finiteProductDesignSigma (ι := ι) D] =ᵐ[ν.trim hm] 0 := by
      exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
        stronglyMeasurable_condExp stronglyMeasurable_zero hce
    have hk := condExp_ae_eq_trim_integral_condExpKernel hm hri
    exact hk.symm.trans hce_trim
  · rw [ProbabilityTheory.iCondIndepFun_iff_condExp_inter_preimage_eq_mul
      (fun _ : ι => (inferInstance : MeasurableSpace ℝ))
      (finiteProductResidual r)
      (fun i => finiteProductResidual_measurable r hr i)]
    intro I sets hsets
    have hset_meas :
        MeasurableSet
          (⋂ i ∈ I, finiteProductResidual r i ⁻¹' sets i) := by
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro hi
      exact (finiteProductResidual_measurable r hr i) (hsets i hi)
    have hleft :
        ν⟦⋂ i ∈ I, finiteProductResidual r i ⁻¹' sets i |
          finiteProductDesignSigma (ι := ι) D⟧ =ᵐ[ν]
        fun ω => finiteCondProb ν Y
          (⋂ i ∈ I, finiteProductResidual r i ⁻¹' sets i) (Y ω) := by
      simpa [Y, finiteProductDesignSigma] using
        condExp_indicator_finite_comap ν Y hY
          (⋂ i ∈ I, finiteProductResidual r i ⁻¹' sets i) hset_meas
    have hright :
        ∀ i ∈ I,
          ν⟦finiteProductResidual r i ⁻¹' sets i |
            finiteProductDesignSigma (ι := ι) D⟧ =ᵐ[ν]
            fun ω => finiteCondProb ν Y
              (finiteProductResidual r i ⁻¹' sets i) (Y ω) := by
      intro i hi
      exact condExp_indicator_finite_comap ν Y hY
        (finiteProductResidual r i ⁻¹' sets i)
        ((finiteProductResidual_measurable r hr i) (hsets i hi))
    have hright_all :
        ∀ᵐ ω ∂ν, ∀ i ∈ I,
          (ν⟦finiteProductResidual r i ⁻¹' sets i |
            finiteProductDesignSigma (ι := ι) D⟧) ω =
            finiteCondProb ν Y
              (finiteProductResidual r i ⁻¹' sets i) (Y ω) := by
      exact (ae_ball_iff (Set.to_countable (I : Set ι))).mpr
        (fun i hi => hright i hi)
    filter_upwards [hleft, hright_all,
      ae_fiber_measure_ne_zero ν Y hY] with ω hleftω hrightω hpos
    rw [hleftω]
    simp only [Finset.prod_apply]
    rw [Finset.prod_congr rfl (fun i hi => hrightω i hi)]
    exact finiteCondProb_iInter μ D hD r hr I sets hsets ω
      (by simpa [ν, Y] using hpos)

end CausalSmith.Substrate.FiniteProductConditionalResidual
