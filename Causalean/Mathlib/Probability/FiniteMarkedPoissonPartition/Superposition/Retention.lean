import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Superposition.Canonical
import Mathlib.Probability.Independence.InfinitePi

/-!
# Retained mark-ordered prefixes

This file gives the measurable retained-prefix map for a finite marked Poisson
sample and proves that, conditional on having enough points, forgetting the
marks of the smallest-mark prefix has the exact independent product law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

/-- Retain the first `n` observations after sorting by marks and forget their
marks; `x₀` supplies an irrelevant value outside the event `n ≤ count`. -/
noncomputable def retainedObservations (x₀ : X) (n : ℕ)
    (s : FiniteSample (X × ℝ)) : Fin n → X :=
  if h : n ≤ s.count then
    fun k => ((orderByMarks s).points
      (Fin.cast (orderByMarks_count s).symm (Fin.castLE h k))).1
  else fun _ => x₀

private noncomputable def prefixPointOr {Y : Type*} [MeasurableSpace Y]
    (y₀ : Y) (n : ℕ) (k : Fin n) (s : FiniteSample Y) : Y :=
  if h : n ≤ s.count then s.points (Fin.castLE h k) else y₀

private lemma measurable_prefixPointOr {Y : Type*} [MeasurableSpace Y]
    (y₀ : Y) (n : ℕ) (k : Fin n) :
    Measurable (prefixPointOr y₀ n k : FiniteSample Y → Y) := by
  intro t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet
    ((fun x : Fin m → Y => if h : n ≤ m then x (Fin.castLE h k) else y₀) ⁻¹' t)
  by_cases h : n ≤ m
  · simp only [dif_pos h]
    exact ht.preimage (measurable_pi_apply (Fin.castLE h k))
  · simp only [dif_neg h]
    exact measurable_const ht

/-- Retaining and forgetting marks is a measurable map to an `n`-tuple. -/
lemma measurable_retainedObservations (x₀ : X) (n : ℕ) :
    Measurable (retainedObservations x₀ n :
      FiniteSample (X × ℝ) → (Fin n → X)) := by
  apply measurable_pi_lambda
  intro k
  have h := (measurable_prefixPointOr (x₀, 0) n k).fst.comp
    measurable_orderByMarks
  convert h using 1
  funext c
  unfold retainedObservations prefixPointOr
  by_cases hn : n ≤ c.count <;> simp [hn]

private lemma map_finPrefix_pi (P : Measure X) [IsProbabilityMeasure P]
    {n m : ℕ} (h : n ≤ m) :
    Measure.map (fun x : Fin m → X => fun k : Fin n => x (Fin.castLE h k))
        (Measure.pi (fun _ : Fin m => P)) =
      Measure.pi (fun _ : Fin n => P) := by
  let p : Fin m → Prop := fun i => i.val < n
  let e : Subtype p ≃ Fin n :=
    { toFun := fun i => ⟨i.1.val, i.2⟩
      invFun := fun k => ⟨Fin.castLE h k, k.isLt⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        rfl
      right_inv := by
        intro k
        apply Fin.ext
        rfl }
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin m => P) p
  have hfst :
      MeasurePreserving
        (fun x : Fin m → X =>
          ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => X) p) x).1)
        (Measure.pi (fun _ : Fin m => P))
        (Measure.pi (fun _ : Subtype p => P)) :=
    measurePreserving_fst.comp hsplit
  have hreindex :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) e)
        (Measure.pi (fun _ : Subtype p => P))
        (Measure.pi (fun _ : Fin n => P)) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => P) e
  have hc := hreindex.comp hfst
  rw [← hc.map_eq]
  congr 1

private lemma map_perm_finPrefix_pi (P : Measure X) [IsProbabilityMeasure P]
    {n m : ℕ} (h : n ≤ m) (e : Fin m ≃ Fin m) :
    Measure.map (fun x : Fin m → X => fun k : Fin n => x (e (Fin.castLE h k)))
        (Measure.pi (fun _ : Fin m => P)) =
      Measure.pi (fun _ : Fin n => P) := by
  have hfun : (fun x : Fin m → X => fun k : Fin n => x (e (Fin.castLE h k))) =
      (fun x : Fin m → X => fun k : Fin n => x (Fin.castLE h k)) ∘
        MeasurableEquiv.piCongrLeft (fun _ : Fin m => X) e.symm := by
    funext x k
    simp only [Function.comp_apply]
    conv_rhs =>
      rw [show Fin.castLE h k = e.symm (e (Fin.castLE h k)) by simp,
        MeasurableEquiv.piCongrLeft_apply_apply]
  have hreindex :
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : Fin m => X) e.symm)
          (Measure.pi (fun _ : Fin m => P)) =
        Measure.pi (fun _ : Fin m => P) := by
    simpa using (measurePreserving_piCongrLeft
      (fun _ : Fin m => P) e.symm).map_eq
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hreindex,
    map_finPrefix_pi]

private noncomputable def markOrderPermutation {m : ℕ} (r : Fin m → ℝ) :
    Fin m ≃ Fin m := by
  let s : FiniteSample (Unit × ℝ) := fixedSizeEmbed m (fun i => ((), r i))
  let f : Fin m → Fin m := fun k =>
    (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨?_, rfl⟩)
  intro a b hab
  apply ((markedKeys s).orderIsoOfFin (markedKeys_card s)).injective
  apply Subtype.ext
  have ha := markedKey_decode s
    (((markedKeys s).orderIsoOfFin (markedKeys_card s) a).2)
  have hb := markedKey_decode s
    (((markedKeys s).orderIsoOfFin (markedKeys_card s) b).2)
  rw [← ha, ← hb]
  change toLex (r (f a), f a) = toLex (r (f b), f b)
  rw [hab]

private lemma retainedObservations_fixedSizeEmbed_eq
    (x₀ : X) {n m : ℕ} (h : n ≤ m) (z : Fin m → X × ℝ) :
    retainedObservations x₀ n (fixedSizeEmbed m z) =
      fun k => (z ((markOrderPermutation (fun i => (z i).2)) (Fin.castLE h k))).1 := by
  funext k
  unfold retainedObservations
  rw [dif_pos (show n ≤ (fixedSizeEmbed m z).count from h)]
  simp only [fixedSizeEmbed, FiniteSample.count]
  change (z (ofLex (((markedKeys (fixedSizeEmbed m z)).orderIsoOfFin
    (markedKeys_card (fixedSizeEmbed m z)) (Fin.castLE h k)).1)).2).1 = _
  have hkeys : markedKeys (fixedSizeEmbed m z) =
      markedKeys (fixedSizeEmbed m (fun i => ((), (z i).2))) := by
    change Finset.univ.image (fun i => toLex ((z i).2, i)) =
      Finset.univ.image (fun i => toLex ((z i).2, i))
    rfl
  simp only [markOrderPermutation, Equiv.ofBijective_apply]
  cases hkeys
  rfl

private lemma map_retainedObservations_fixedSizeEmbed_pi
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (x₀ : X) {n m : ℕ} (h : n ≤ m) :
    Measure.map (retainedObservations x₀ n)
        (Measure.map (fixedSizeEmbed m)
          (Measure.pi (fun _ : Fin m => P.prod R))) =
      Measure.pi (fun _ : Fin n => P) := by
  let split := MeasurableEquiv.arrowProdEquivProdArrow X ℝ (Fin m)
  have hsplit := measurePreserving_arrowProdEquivProdArrow X ℝ (Fin m)
    (fun _ : Fin m => P) (fun _ : Fin m => R)
  have hsplit_inv := (MeasurePreserving.symm split hsplit).map_eq
  have hretfix : Measurable (retainedObservations x₀ n ∘ fixedSizeEmbed m) :=
    (measurable_retainedObservations x₀ n).comp (measurable_fixedSizeEmbed m)
  have htotal : Measurable
      ((retainedObservations x₀ n ∘ fixedSizeEmbed m) ∘ split.symm) :=
    hretfix.comp split.symm.measurable
  rw [Measure.map_map (measurable_retainedObservations x₀ n)
      (measurable_fixedSizeEmbed m), ← hsplit_inv,
    Measure.map_map hretfix split.symm.measurable]
  ext A hA
  rw [Measure.map_apply htotal hA,
    Measure.prod_apply_symm (hA.preimage htotal)]
  have hsection : ∀ r : Fin m → ℝ,
      (Measure.pi (fun _ : Fin m => P))
          ((fun x => (x, r)) ⁻¹'
            (((retainedObservations x₀ n ∘ fixedSizeEmbed m) ∘ split.symm) ⁻¹' A)) =
        (Measure.pi (fun _ : Fin n => P)) A := by
    intro r
    rw [← map_perm_finPrefix_pi P h (markOrderPermutation r),
      Measure.map_apply (by fun_prop) hA]
    congr 1
    ext x
    rw [Set.mem_preimage]
    change retainedObservations x₀ n
        (fixedSizeEmbed m (fun i => (x i, r i))) ∈ A ↔ _
    rw [retainedObservations_fixedSizeEmbed_eq x₀ h]
    rfl
  simp_rw [hsection]
  simp

/-- On the event that at least `n` points exist, retaining the `n` smallest
atomless independent marks and forgetting marks gives the event probability
times the exact product law `P^n`. -/
lemma map_retainedObservations_restrict_count_ge
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ) :
    Measure.map (retainedObservations x₀ n)
        ((finiteMarkedPoissonSampleLaw P R lam).restrict
          (FiniteSample.count ⁻¹' Ici n)) =
      (poissonMeasure lam) (Ici n) • Measure.pi (fun _ : Fin n => P) := by
  let μ := finiteMarkedPoissonSampleLaw P R lam
  have hdecomp :
      μ.restrict (FiniteSample.count ⁻¹' Ici n) =
        Measure.sum (fun m : (Ici n : Set ℕ) =>
          μ.restrict (FiniteSample.count ⁻¹' ({m.1} : Set ℕ))) := by
    rw [← Set.biUnion_preimage_singleton]
    exact Measure.restrict_biUnion (Set.to_countable (Ici n))
      (pairwiseDisjoint_fiber FiniteSample.count (Ici n))
      (fun m => measurable_finiteSample_count (measurableSet_singleton m))
  rw [hdecomp, Measure.map_sum
    ((measurable_retainedObservations x₀ n).aemeasurable)]
  simp_rw [show ∀ m : (Ici n : Set ℕ),
      Measure.map (retainedObservations x₀ n)
          (μ.restrict (FiniteSample.count ⁻¹' ({m.1} : Set ℕ))) =
        (poissonMeasure lam) ({m.1} : Set ℕ) •
          Measure.pi (fun _ : Fin n => P) by
    intro m
    rw [show μ = finiteMarkedPoissonSampleLaw P R lam by rfl,
      finiteMarkedPoissonSampleLaw_restrict_count_eq,
      Measure.map_smul,
      map_retainedObservations_fixedSizeEmbed_pi P R x₀ m.2]]
  ext A hA
  simp only [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right]
  congr 1
  simpa using (tsum_measure_preimage_singleton
    (μ := poissonMeasure lam) (s := Ici n) (f := id) (Set.to_countable (Ici n))
    (fun m _ => measurableSet_singleton m))

/-- If the event of at least `n` points has positive probability, normalising
the restricted retained-prefix law gives exactly `P^n`. -/
lemma normalized_map_retainedObservations_restrict_count_ge
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ)
    (hpos : (poissonMeasure lam) (Ici n) ≠ 0) :
    ((poissonMeasure lam) (Ici n))⁻¹ •
        Measure.map (retainedObservations x₀ n)
          ((finiteMarkedPoissonSampleLaw P R lam).restrict
            (FiniteSample.count ⁻¹' Ici n)) =
      Measure.pi (fun _ : Fin n => P) := by
  rw [map_retainedObservations_restrict_count_ge]
  rw [← mul_smul, ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), one_smul]

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
