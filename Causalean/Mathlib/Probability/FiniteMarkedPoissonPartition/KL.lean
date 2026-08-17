import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic
import Causalean.Mathlib.InformationTheory.KLBind
import Causalean.Mathlib.InformationTheory.ProductKLLeCam
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Relative entropy of finite Poisson experiments

This file packages a finite measure as a Poisson count with mean equal to its
mass times a scalar intensity and conditionally i.i.d. points from its
normalisation.  It states the extended-real KL identity for two equal-mass
finite intensity measures and the monotone upper-bound form used in testing
arguments.  A shared independent real mark law is carried throughout.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

private noncomputable def finiteSampleKernel
    (P : Measure X) [IsProbabilityMeasure P] : Kernel ℕ (FiniteSample X) where
  toFun n := Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P)
  measurable' := Measurable.of_discrete

private instance finiteSampleKernel_isMarkov
    (P : Measure X) [IsProbabilityMeasure P] : IsMarkovKernel (finiteSampleKernel P) where
  isProbabilityMeasure n := by
    rw [finiteSampleKernel]
    exact Measure.isProbabilityMeasure_map
      (measurable_fixedSizeEmbed n).aemeasurable

private lemma measurableEmbedding_fixedSizeEmbed (n : ℕ) :
    MeasurableEmbedding (fixedSizeEmbed (X := X) n) where
  injective x y h := by simpa [fixedSizeEmbed] using h
  measurable := measurable_fixedSizeEmbed n
  measurableSet_image' := by
    intro s hs
    change MeasurableSet[⨅ a, MeasurableSpace.map
        (@Sigma.mk ℕ (fun k ↦ Fin k → X) a) inferInstance]
      (@Sigma.mk ℕ (fun k ↦ Fin k → X) n '' s)
    simp only [MeasurableSpace.measurableSet_iInf]
    intro a
    change MeasurableSet
      ((@Sigma.mk ℕ (fun k ↦ Fin k → X) a) ⁻¹'
        (@Sigma.mk ℕ (fun k ↦ Fin k → X) n '' s))
    by_cases h : a = n
    · subst a
      have hinj : Function.Injective
          (@Sigma.mk ℕ (fun k ↦ Fin k → X) n) := by
        intro x y hxy
        simpa using hxy
      rw [hinj.preimage_image]
      exact hs
    · rw [Set.preimage_image_sigmaMk_of_ne h]
      exact MeasurableSet.empty

private lemma finitePoissonSampleLaw_eq_bind
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    finitePoissonSampleLaw P lam = (poissonMeasure lam).bind (finiteSampleKernel P) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_countable']
  symm
  calc
    ∑' n : ℕ, (finiteSampleKernel P n) s * poissonMeasure lam {n}
        = ∑' n : ℕ,
            ((finitePoissonSampleLaw P lam).restrict
              (FiniteSample.count ⁻¹' ({n} : Set ℕ))) s := by
          congr 1
          funext n
          rw [finitePoissonSampleLaw_restrict_count_eq, Measure.smul_apply]
          simp only [smul_eq_mul]
          exact mul_comm _ _
    _ = finitePoissonSampleLaw P lam s := by
      rw [← Measure.sum_apply _ hs, ← Measure.restrict_iUnion]
      · rw [show (⋃ n : ℕ, FiniteSample.count ⁻¹' ({n} : Set ℕ)) = Set.univ by
          ext x
          simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_univ, iff_true]
          exact ⟨x.count, rfl⟩, Measure.restrict_univ]
      · intro i j hij
        exact (Set.disjoint_singleton.mpr hij).preimage FiniteSample.count
      · intro n
        exact measurable_finiteSample_count
          (MeasurableSet.singleton n)

private lemma klDiv_pi_const
    (n : ℕ) (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    InformationTheory.klDiv
        (Measure.pi fun _ : Fin n ↦ P)
        (Measure.pi fun _ : Fin n ↦ Q) =
      (n : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  by_cases hn : n = 0
  · subst n
    have heq : (Measure.pi fun _ : Fin 0 ↦ P) =
        (Measure.pi fun _ : Fin 0 ↦ Q) := by
      apply Measure.pi_eq
      intro s hs
      simp
    rw [heq]
    simp
  by_cases htop : InformationTheory.klDiv P Q = ∞
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let i : Fin n := ⟨0, hnpos⟩
    have hle := Causalean.Mathlib.InformationTheory.Measure.klDiv_map_le
      (μ := Measure.pi fun _ : Fin n ↦ P)
      (ν := Measure.pi fun _ : Fin n ↦ Q) (measurable_pi_apply i)
    rw [(measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin n ↦ Q) i).map_eq, htop] at hle
    have hpi : InformationTheory.klDiv
        (Measure.pi fun _ : Fin n ↦ P)
        (Measure.pi fun _ : Fin n ↦ Q) = ∞ := top_unique hle
    rw [hpi, htop]
    exact (ENNReal.mul_top (by positivity)).symm
  · obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp htop
    have htensor := Causalean.Mathlib.InformationTheory.productKL_tensorization
      n P Q hac hint
    apply (ENNReal.toReal_eq_toReal_iff' htensor.product_ne_top ?_).mp
    · simpa [ENNReal.toReal_mul] using
        Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite
          n P Q hac hint
    · exact ENNReal.mul_ne_top (by simp) htop

private lemma klDiv_prod_common_right
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] :
    InformationTheory.klDiv (P.prod R) (Q.prod R) =
      InformationTheory.klDiv P Q := by
  rw [← Measure.compProd_const, ← Measure.compProd_const]
  exact Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_left
    P Q (Kernel.const X R)

private lemma klDiv_finiteSampleKernel
    (n : ℕ) (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    InformationTheory.klDiv (finiteSampleKernel P n) (finiteSampleKernel Q n) =
      (n : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  change InformationTheory.klDiv
      (Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P))
      (Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ Q)) = _
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
    (measurableEmbedding_fixedSizeEmbed n)]
  exact klDiv_pi_const n P Q

private lemma poissonPMFReal_succ_mul (r : ℝ≥0) (n : ℕ) :
    (n + 1 : ℝ) * poissonPMFReal r (n + 1) =
      (r : ℝ) * poissonPMFReal r n := by
  rw [poissonPMFReal, poissonPMFReal, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

private lemma poissonPMF_succ_mul (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 1) =
      (r : ℝ≥0∞) * poissonPMF r n := by
  change ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r (n + 1)) =
    (r : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r n)
  have h := congrArg ENNReal.ofReal (poissonPMFReal_succ_mul r n)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] at h
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one] at h
  simpa using h

private lemma poisson_lintegral_natCast (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r = (r : ℝ≥0∞) := by
  rw [lintegral_countable']
  simp_rw [poissonMeasure_singleton_eq_poissonPMF]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  simp_rw [poissonPMF_succ_mul]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

private lemma finiteSampleKernel_count_fibre
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    finiteSampleKernel P n {s | s.count = n}ᶜ = 0 := by
  change Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P)
    {s | s.count = n}ᶜ = 0
  change Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P)
    (FiniteSample.count ⁻¹' ({n} : Set ℕ))ᶜ = 0
  rw [Measure.map_apply (measurable_fixedSizeEmbed n)
    ((measurable_finiteSample_count (MeasurableSet.singleton n)).compl)]
  have hpre : fixedSizeEmbed n ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      (Set.univ : Set (Fin n → X)) := by
    ext x
    simp [fixedSizeEmbed, FiniteSample.count]
  rw [Set.preimage_compl, hpre]
  simp

private lemma finiteSampleKernel_ac
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (n : ℕ) : finiteSampleKernel P n ≪ finiteSampleKernel Q n := by
  change Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P) ≪
    Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ Q)
  exact (Causalean.Mathlib.InformationTheory.pi_iid_absolutelyContinuous
    P Q hPQ n).map (measurable_fixedSizeEmbed n)

private lemma klDiv_finiteMarkedPoissonSampleLaw_of_ac
    [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] (t : ℝ≥0)
    (hPQ : P ≪ Q) :
    InformationTheory.klDiv
        (finiteMarkedPoissonSampleLaw P R t)
        (finiteMarkedPoissonSampleLaw Q R t) =
      (t : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  have hprod : P.prod R ≪ Q.prod R := hPQ.prod .rfl
  unfold finiteMarkedPoissonSampleLaw
  rw [finitePoissonSampleLaw_eq_bind, finitePoissonSampleLaw_eq_bind]
  calc
    InformationTheory.klDiv
        ((poissonMeasure t).bind (finiteSampleKernel (P.prod R)))
        ((poissonMeasure t).bind (finiteSampleKernel (Q.prod R))) =
        ∫⁻ n, InformationTheory.klDiv
          (finiteSampleKernel (P.prod R) n)
          (finiteSampleKernel (Q.prod R) n) ∂poissonMeasure t :=
      Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
        (m := poissonMeasure t) (κ := finiteSampleKernel (P.prod R))
        (η := finiteSampleKernel (Q.prod R)) (proj := FiniteSample.count)
        measurable_finiteSample_count
        ((measurable_fst.eq (measurable_finiteSample_count.comp measurable_snd)).setOf)
        (ae_of_all _ fun n ↦ finiteSampleKernel_count_fibre (P.prod R) n)
        (ae_of_all _ fun n ↦ finiteSampleKernel_count_fibre (Q.prod R) n)
        (ae_of_all _ fun n ↦ finiteSampleKernel_ac (P.prod R) (Q.prod R) hprod n)
    _ = (t : ℝ≥0∞) * InformationTheory.klDiv P Q := by
      simp_rw [klDiv_finiteSampleKernel, klDiv_prod_common_right]
      rw [lintegral_mul_const _ (by fun_prop), poisson_lintegral_natCast]

private lemma absolutelyContinuous_of_map_measurableEmbedding
    {Y : Type*} [MeasurableSpace Y] {μ ν : Measure X} {f : X → Y}
    (hf : MeasurableEmbedding f) (hmap : μ.map f ≪ ν.map f) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hνs
  have himage : MeasurableSet (f '' s) := hf.measurableSet_image' hs
  have hmap_zero : ν.map f (f '' s) = 0 := by
    rw [hf.map_apply ν (f '' s), hf.injective.preimage_image]
    exact hνs
  have := hmap hmap_zero
  rwa [hf.map_apply μ (f '' s), hf.injective.preimage_image] at this

private lemma poissonMeasure_singleton_one_ne_zero {t : ℝ≥0} (ht : t ≠ 0) :
    poissonMeasure t ({1} : Set ℕ) ≠ 0 := by
  rw [poissonMeasure_singleton_eq_poissonPMF t 1]
  change ENNReal.ofReal (poissonPMFReal t 1) ≠ 0
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (poissonPMFReal_pos (pos_of_ne_zero ht)))

private lemma poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  ext s hs
  rw [poissonMeasure, Measure.sum_apply _ hs]
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro n hn
    rw [Measure.smul_apply, smul_eq_mul]
    simp [zero_pow hn]
  · simp

private lemma finiteMarkedPoissonSampleLaw_zero
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] :
    finiteMarkedPoissonSampleLaw P R 0 =
      finiteMarkedPoissonSampleLaw Q R 0 := by
  unfold finiteMarkedPoissonSampleLaw
  rw [finitePoissonSampleLaw_eq_bind, finitePoissonSampleLaw_eq_bind,
    poissonMeasure_zero]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [lintegral_dirac' _ (Kernel.measurable_coe _ hs)]
  have heq : (Measure.pi fun _ : Fin 0 ↦ P.prod R) =
      (Measure.pi fun _ : Fin 0 ↦ Q.prod R) := by
    apply Measure.pi_eq
    intro u hu
    simp
  change (Measure.map (fixedSizeEmbed 0) (Measure.pi fun _ : Fin 0 ↦ P.prod R)) s =
    (Measure.map (fixedSizeEmbed 0) (Measure.pi fun _ : Fin 0 ↦ Q.prod R)) s
  rw [heq]

private lemma absolutelyContinuous_of_finiteMarkedPoissonSampleLaw
    [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] {t : ℝ≥0} (ht : t ≠ 0)
    (hfull : finiteMarkedPoissonSampleLaw P R t ≪
      finiteMarkedPoissonSampleLaw Q R t) : P ≪ Q := by
  let c : ℝ≥0∞ := poissonMeasure t ({1} : Set ℕ)
  have hc : c ≠ 0 := poissonMeasure_singleton_one_ne_zero ht
  have hrest := hfull.restrict
    (FiniteSample.count ⁻¹' ({1} : Set ℕ))
  unfold finiteMarkedPoissonSampleLaw at hrest
  rw [finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq] at hrest
  have hmaps :
      Measure.map (fixedSizeEmbed 1)
          (Measure.pi fun _ : Fin 1 ↦ P.prod R) ≪
        Measure.map (fixedSizeEmbed 1)
          (Measure.pi fun _ : Fin 1 ↦ Q.prod R) := by
    exact (Measure.absolutelyContinuous_smul hc).trans <|
      hrest.trans Measure.smul_absolutelyContinuous
  have hpi : (Measure.pi fun _ : Fin 1 ↦ P.prod R) ≪
      (Measure.pi fun _ : Fin 1 ↦ Q.prod R) :=
    absolutelyContinuous_of_map_measurableEmbedding
      (measurableEmbedding_fixedSizeEmbed 1) hmaps
  have hprod := hpi.map (measurable_pi_apply (0 : Fin 1))
  rw [(measurePreserving_eval (fun _ : Fin 1 ↦ P.prod R) (0 : Fin 1)).map_eq,
    (measurePreserving_eval (fun _ : Fin 1 ↦ Q.prod R) (0 : Fin 1)).map_eq] at hprod
  have hfst := hprod.map measurable_fst
  simpa [Measure.map_fst_prod, measure_univ] using hfst

private lemma klDiv_finiteMarkedPoissonSampleLaw
    [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] (t : ℝ≥0) :
    InformationTheory.klDiv
        (finiteMarkedPoissonSampleLaw P R t)
        (finiteMarkedPoissonSampleLaw Q R t) =
      (t : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  by_cases hPQ : P ≪ Q
  · exact klDiv_finiteMarkedPoissonSampleLaw_of_ac P Q R t hPQ
  by_cases ht : t = 0
  · subst t
    rw [finiteMarkedPoissonSampleLaw_zero P Q R]
    simp
  have hfull : ¬finiteMarkedPoissonSampleLaw P R t ≪
      finiteMarkedPoissonSampleLaw Q R t := by
    intro h
    exact hPQ (absolutelyContinuous_of_finiteMarkedPoissonSampleLaw P Q R ht h)
  rw [InformationTheory.klDiv_of_not_ac hfull,
    InformationTheory.klDiv_of_not_ac hPQ]
  exact (ENNReal.mul_top (by simpa)).symm

/-- The total mass of a finite measure as a nonnegative real. -/
noncomputable def finiteMeasureMass (ν : Measure X) [IsFiniteMeasure ν] : ℝ≥0 :=
  (ν Set.univ).toNNReal

/-- Normalise a nonzero finite measure to a probability measure, using the
supplied probability law only on the zero-measure branch. -/
noncomputable def normalizedFiniteMeasure (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀] : Measure X := by
  classical
  exact if h : ν = 0 then P₀ else (ν Set.univ)⁻¹ • ν

/-- The normalisation of a finite measure is a probability measure, including
the explicit fallback on the zero branch. -/
instance normalizedFiniteMeasure_isProbabilityMeasure
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀] :
    IsProbabilityMeasure (normalizedFiniteMeasure ν P₀) := by
  classical
  rw [normalizedFiniteMeasure]
  split_ifs with hν
  · infer_instance
  · rw [isProbabilityMeasure_iff, Measure.smul_apply _ _ Set.univ]
    have hmass : ν Set.univ ≠ 0 := by
      exact fun h ↦ hν (Measure.measure_univ_eq_zero.mp h)
    exact ENNReal.inv_mul_cancel hmass (ne_of_lt (measure_lt_top ν Set.univ))

private lemma finiteMeasureMass_smul_normalizedFiniteMeasure
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀] (hν : ν ≠ 0) :
    finiteMeasureMass ν • normalizedFiniteMeasure ν P₀ = ν := by
  ext s hs
  rw [normalizedFiniteMeasure, dif_neg hν, Measure.smul_apply,
    Measure.smul_apply]
  change ((finiteMeasureMass ν : ℝ≥0) : ℝ≥0∞) * ((ν Set.univ)⁻¹ * ν s) = ν s
  rw [finiteMeasureMass, ENNReal.coe_toNNReal (ne_of_lt (measure_lt_top ν Set.univ)),
    ← mul_assoc, ENNReal.mul_inv_cancel]
  · simp
  · exact fun h ↦ hν (Measure.measure_univ_eq_zero.mp h)
  · exact ne_of_lt (measure_lt_top ν Set.univ)

/-- The marked Poisson experiment generated by finite intensity measure `ν`
has count mean `lam * ν(univ)` and conditionally i.i.d. points from the
normalisation of `ν`, with independent marks from `R`. -/
noncomputable def finiteMeasureMarkedPoissonLaw
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure (FiniteSample (X × ℝ)) :=
  finiteMarkedPoissonSampleLaw (normalizedFiniteMeasure ν P₀) R
    (lam * finiteMeasureMass ν)

/-- A finite-measure marked Poisson experiment is a probability measure. -/
instance finiteMeasureMarkedPoissonLaw_isProbabilityMeasure
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    IsProbabilityMeasure (finiteMeasureMarkedPoissonLaw ν P₀ R lam) := by
  unfold finiteMeasureMarkedPoissonLaw
  infer_instance

/-- The count in the finite-measure marked Poisson experiment is Poisson with
mean `lam` times the total mass of the intensity measure. -/
lemma finiteMeasureMarkedPoissonLaw_map_count
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure.map FiniteSample.count (finiteMeasureMarkedPoissonLaw ν P₀ R lam) =
      poissonMeasure (lam * finiteMeasureMass ν) := by
  exact finiteMarkedPoissonSampleLaw_map_count
    (normalizedFiniteMeasure ν P₀) R (lam * finiteMeasureMass ν)

/-- Fix [a nonnegative Poisson rate `lam`](hyp:lam) and suppose [the finite
intensity measures `ν₀` and `ν₁` have equal total mass](hyp:hmass). Then, for a
common baseline probability measure `P₀` and mark law `R`, [the KL divergence
between the finite-measure marked Poisson experiments generated by `ν₀` and by
`ν₁` equals `lam` times the KL divergence between `ν₀` and `ν₁`](goal). -/
lemma klDiv_finiteMeasureMarkedPoissonLaw
    [StandardBorelSpace X]
    (ν₀ ν₁ : Measure X) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (lam : ℝ≥0) (hmass : ν₀ Set.univ = ν₁ Set.univ) :
    InformationTheory.klDiv
        (finiteMeasureMarkedPoissonLaw ν₀ P₀ R lam)
        (finiteMeasureMarkedPoissonLaw ν₁ P₀ R lam) =
      (lam : ℝ≥0∞) * InformationTheory.klDiv ν₀ ν₁ := by
  by_cases hν₀ : ν₀ = 0
  · subst ν₀
    have hν₁ : ν₁ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa using hmass.symm
    subst ν₁
    simp [finiteMeasureMarkedPoissonLaw, finiteMeasureMass,
      normalizedFiniteMeasure]
  have hν₁ : ν₁ ≠ 0 := by
    intro h
    apply hν₀
    apply Measure.measure_univ_eq_zero.mp
    simpa [h] using hmass
  have hm : finiteMeasureMass ν₀ = finiteMeasureMass ν₁ := by
    simp only [finiteMeasureMass]
    rw [hmass]
  unfold finiteMeasureMarkedPoissonLaw
  rw [← hm, klDiv_finiteMarkedPoissonSampleLaw]
  have hrecover₀ := finiteMeasureMass_smul_normalizedFiniteMeasure ν₀ P₀ hν₀
  have hrecover₁ := finiteMeasureMass_smul_normalizedFiniteMeasure ν₁ P₀ hν₁
  have hrecover₁' : finiteMeasureMass ν₀ • normalizedFiniteMeasure ν₁ P₀ = ν₁ := by
    rw [hm]
    exact hrecover₁
  have hKL : InformationTheory.klDiv ν₀ ν₁ =
      (finiteMeasureMass ν₀ : ℝ≥0∞) * InformationTheory.klDiv
        (normalizedFiniteMeasure ν₀ P₀) (normalizedFiniteMeasure ν₁ P₀) := by
    calc
      InformationTheory.klDiv ν₀ ν₁ = InformationTheory.klDiv
          (finiteMeasureMass ν₀ • normalizedFiniteMeasure ν₀ P₀)
          (finiteMeasureMass ν₀ • normalizedFiniteMeasure ν₁ P₀) := by
        exact congrArg₂ InformationTheory.klDiv hrecover₀.symm hrecover₁'.symm
      _ = _ := InformationTheory.klDiv_smul_same (finiteMeasureMass ν₀)
  calc
    ((lam * finiteMeasureMass ν₀ : ℝ≥0) : ℝ≥0∞) *
          InformationTheory.klDiv
            (normalizedFiniteMeasure ν₀ P₀) (normalizedFiniteMeasure ν₁ P₀) =
        (lam : ℝ≥0∞) * ((finiteMeasureMass ν₀ : ℝ≥0∞) *
          InformationTheory.klDiv
            (normalizedFiniteMeasure ν₀ P₀) (normalizedFiniteMeasure ν₁ P₀)) := by
      simp only [ENNReal.coe_mul]
      rw [mul_assoc]
    _ = (lam : ℝ≥0∞) * InformationTheory.klDiv ν₀ ν₁ := by
      rw [hKL]

/-- A one-point finite-measure KL bound transfers directly to the corresponding
marked Poisson experiments after multiplication by the scalar intensity. -/
lemma klDiv_finiteMeasureMarkedPoissonLaw_le
    [StandardBorelSpace X]
    (ν₀ ν₁ : Measure X) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (lam : ℝ≥0) (B : ℝ≥0∞)
    (hmass : ν₀ Set.univ = ν₁ Set.univ)
    (hKL : InformationTheory.klDiv ν₀ ν₁ ≤ B) :
    InformationTheory.klDiv
        (finiteMeasureMarkedPoissonLaw ν₀ P₀ R lam)
        (finiteMeasureMarkedPoissonLaw ν₁ P₀ R lam) ≤
      (lam : ℝ≥0∞) * B := by
  rw [klDiv_finiteMeasureMarkedPoissonLaw ν₀ ν₁ P₀ R lam hmass]
  exact mul_le_mul_right hKL (lam : ℝ≥0∞)

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
