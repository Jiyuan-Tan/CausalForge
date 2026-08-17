import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition
import Mathlib.Data.Prod.Lex
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Probability.Independence.InfinitePi

/-!
# Finite superposition and mark ordering

This file concatenates a finite family of cell configurations, sorts a marked
configuration by its real marks using the original index as a deterministic
tie-breaker, and proves the resulting maps are measurable. Canonical laws and
retained-prefix laws are supplied by the companion modules.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Superpose finitely many finite sequences by enumerating their dependent
disjoint union of coordinates. -/
noncomputable def superpose (q : ι → FiniteSample (X × ℝ)) :
    FiniteSample (X × ℝ) := by
  classical
  let S := Σ j : ι, Fin (q j).count
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  exact ⟨Fintype.card S, fun k =>
    let u := e.symm k
    (q u.1).points u.2⟩

/-- The count after finite superposition is the sum of the cell counts. -/
lemma superpose_count (q : ι → FiniteSample (X × ℝ)) :
    (superpose q).count = ∑ j, (q j).count := by
  classical
  change Fintype.card (Σ j : ι, Fin (q j).count) = _
  simp

private def countFiber {Y : Type*} [MeasurableSpace Y] (c : ι → ℕ) :
    Set (ι → FiniteSample Y) :=
  {q | ∀ j, (q j).count = c j}

private lemma measurableSet_countFiber {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) : MeasurableSet (countFiber (Y := Y) c) := by
  rw [show countFiber (Y := Y) c =
      ⋂ j : ι, (fun q : ι → FiniteSample Y => (q j).count) ⁻¹' {c j} by
    ext q
    simp [countFiber]]
  exact MeasurableSet.iInter fun j =>
    (measurable_finiteSample_count.comp (measurable_pi_apply j))
      (measurableSet_singleton (c j))

private noncomputable def pointsOfCount {Y : Type*} [MeasurableSpace Y]
    (n : ℕ) (s : {s : FiniteSample Y // s.count = n}) : Fin n → Y :=
  fun k => s.1.points (Fin.cast s.2.symm k)

private lemma measurable_pointsOfCount {Y : Type*} [MeasurableSpace Y] (n : ℕ) :
    Measurable (pointsOfCount n : {s : FiniteSample Y // s.count = n} → Fin n → Y) := by
  apply measurable_pi_lambda
  intro k t ht
  let A : Set (FiniteSample Y) :=
    fixedSizeEmbed n '' ((fun x : Fin n → Y => x k) ⁻¹' t)
  have hA : MeasurableSet A := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet (fixedSizeEmbed m ⁻¹' A)
    by_cases hmn : m = n
    · subst m
      have hk : Measurable (fun x : Fin n → Y => x k) := measurable_pi_apply k
      have heq : fixedSizeEmbed n ⁻¹' A = (fun x : Fin n → Y => x k) ⁻¹' t := by
        ext x
        constructor
        · rintro ⟨y, hy, hxy⟩
          have hyx : y = x := by
            exact eq_of_heq (Sigma.mk.inj hxy).2
          simpa [hyx] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [heq]
      exact ht.preimage hk
    · have hempty : fixedSizeEmbed m ⁻¹' A = (∅ : Set (Fin m → Y)) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨y, -, heq⟩
        exact hmn (congrArg Sigma.fst heq).symm
      rw [hempty]
      exact MeasurableSet.empty
  have hpre : (fun s : {s : FiniteSample Y // s.count = n} =>
      pointsOfCount n s k) ⁻¹' t = Subtype.val ⁻¹' A := by
    ext s
    rcases s with ⟨⟨m, x⟩, hs⟩
    change m = n at hs
    subst m
    simp [pointsOfCount, A, fixedSizeEmbed]
    change x (Fin.cast _ k) ∈ t ↔ x k ∈ t
    rw [Fin.cast_eq_self]
  rw [hpre]
  exact hA.preimage measurable_subtype_coe

private noncomputable def fixedCountSuperpose {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) (x : ∀ j, Fin (c j) → Y) : FiniteSample Y := by
  classical
  let S := Σ j : ι, Fin (c j)
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  exact ⟨Fintype.card S, fun k => x (e.symm k).1 (e.symm k).2⟩

private lemma measurable_fixedCountSuperpose {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) : Measurable (fixedCountSuperpose (Y := Y) c) := by
  classical
  unfold fixedCountSuperpose
  apply (measurable_fixedSizeEmbed _).comp
  apply measurable_pi_lambda
  intro k
  let u := (Fintype.equivFin (Σ j : ι, Fin (c j))).symm k
  exact (measurable_pi_apply u.2).comp (measurable_pi_apply u.1)

private noncomputable def fiberPoints {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) (q : countFiber (Y := Y) c) : ∀ j, Fin (c j) → Y :=
  fun j => pointsOfCount (c j) ⟨q.1 j, q.2 j⟩

private lemma measurable_fiberPoints {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) : Measurable (fiberPoints (Y := Y) c) := by
  apply measurable_pi_lambda
  intro j
  apply (measurable_pointsOfCount (Y := Y) (c j)).comp
  exact ((measurable_pi_apply j).comp measurable_subtype_coe).subtype_mk

private lemma fixedCountSuperpose_eq_superpose
    (q : ι → FiniteSample (X × ℝ)) (c : ι → ℕ)
    (hc : (fun j => (q j).count) = c) :
    fixedCountSuperpose c
      (fun j k => (q j).points (Fin.cast (congrFun hc j).symm k)) = superpose q := by
  classical
  subst c
  rfl

private lemma fixedCountSuperpose_fiberPoints
    (c : ι → ℕ) (q : countFiber (Y := X × ℝ) c) :
    fixedCountSuperpose c (fiberPoints c q) = superpose q.1 := by
  classical
  let hc : (fun j => (q.1 j).count) = c := funext q.2
  simpa only [fiberPoints, pointsOfCount] using
    fixedCountSuperpose_eq_superpose q.1 c hc

/-- Finite superposition is measurable. -/
lemma measurable_superpose :
    Measurable (superpose : (ι → FiniteSample (X × ℝ)) → FiniteSample (X × ℝ)) := by
  intro s hs
  rw [show superpose ⁻¹' s =
      ⋃ c : ι → ℕ, Subtype.val ''
        ((fun q : countFiber (Y := X × ℝ) c =>
          fixedCountSuperpose c (fiberPoints c q)) ⁻¹' s) by
    ext q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hq
      let c : ι → ℕ := fun j => (q j).count
      refine ⟨c, ⟨q, fun _ => rfl⟩, ?_, rfl⟩
      rw [fixedCountSuperpose_fiberPoints]
      exact hq
    · rintro ⟨c, q', hq', rfl⟩
      rw [fixedCountSuperpose_fiberPoints] at hq'
      exact hq']
  apply MeasurableSet.iUnion
  intro c
  apply (measurableSet_countFiber (Y := X × ℝ) c).subtype_image
  exact hs.preimage
    ((measurable_fixedCountSuperpose c).comp (measurable_fiberPoints c))

/-- The finite set of `(mark, originalIndex)` keys used to order a marked
sample; the index makes all keys distinct even on the tie event. -/
noncomputable def markedKeys (s : FiniteSample (X × ℝ)) :
    Finset (ℝ ×ₗ Fin s.count) := by
  classical
  exact Finset.univ.image (fun k => toLex ((s.points k).2, k))

private lemma markedKeys_card (s : FiniteSample (X × ℝ)) :
    (markedKeys s).card = s.count := by
  classical
  rw [markedKeys, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg (fun z : ℝ ×ₗ Fin s.count => (ofLex z).2) h

private lemma markedKey_decode (s : FiniteSample (X × ℝ))
    {z : ℝ ×ₗ Fin s.count} (hz : z ∈ markedKeys s) :
    toLex ((s.points (ofLex z).2).2, (ofLex z).2) = z := by
  classical
  have hz' : z ∈ Finset.univ.image (fun i => toLex ((s.points i).2, i)) := by
    simpa only [markedKeys] using hz
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz'
  rw [← hi]
  rfl

/-- Order a finite marked sequence increasingly by mark, breaking mark ties by
the original coordinate index. -/
noncomputable def orderByMarks (s : FiniteSample (X × ℝ)) :
    FiniteSample (X × ℝ) := by
  classical
  let t := markedKeys s
  have hcard : t.card = s.count := by simpa [t] using markedKeys_card s
  exact ⟨s.count, fun k =>
    s.points (ofLex (t.orderIsoOfFin hcard k).1).2⟩

/-- Ordering by marks preserves the sample count. -/
@[simp] lemma orderByMarks_count (s : FiniteSample (X × ℝ)) :
    (orderByMarks s).count = s.count := by
  rfl

/-- The mark-ordering map is measurable. -/
lemma measurable_orderByMarks :
    Measurable (orderByMarks : FiniteSample (X × ℝ) → FiniteSample (X × ℝ)) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs ⊢
  intro n
  change MeasurableSet (fixedSizeEmbed n ⁻¹' (orderByMarks ⁻¹' s))
  rw [show fixedSizeEmbed n ⁻¹' (orderByMarks ⁻¹' s) =
      ⋃ f : Fin n → Fin n,
        {x : Fin n → X × ℝ |
            StrictMono (fun k => toLex ((x (f k)).2, f k))} ∩
          (fun x : Fin n → X × ℝ => fun k => x (f k)) ⁻¹'
            (fixedSizeEmbed n ⁻¹' s) by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx
      let q : FiniteSample (X × ℝ) := fixedSizeEmbed n x
      let e := (markedKeys q).orderIsoOfFin (markedKeys_card q)
      let f : Fin n → Fin n := fun k => (ofLex (e k).1).2
      refine ⟨f, ?_, ?_⟩
      · intro a b hab
        have ha := markedKey_decode q (e a).2
        have hb := markedKey_decode q (e b).2
        change toLex ((x (f a)).2, f a) < toLex ((x (f b)).2, f b)
        have ha' : toLex ((x (f a)).2, f a) = (e a).1 := by
          simpa [q, e, f] using ha
        have hb' : toLex ((x (f b)).2, f b) = (e b).1 := by
          simpa [q, e, f] using hb
        rw [ha', hb']
        exact e.strictMono hab
      · simpa [q, e, f, orderByMarks] using hx
    · rintro ⟨f, hfmono, hx⟩
      let q : FiniteSample (X × ℝ) := fixedSizeEmbed n x
      have hkeys : (fun k => toLex ((x (f k)).2, f k)) =
          (markedKeys q).orderEmbOfFin (markedKeys_card q) := by
        apply Finset.orderEmbOfFin_unique (markedKeys_card q)
        · intro k
          rw [markedKeys]
          refine Finset.mem_image.mpr ⟨f k, Finset.mem_univ _, ?_⟩
          rfl
        · exact hfmono
      have hpoints : orderByMarks q =
          fixedSizeEmbed n (fun k => x (f k)) := by
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext k
          change x (ofLex (((markedKeys q).orderEmbOfFin (markedKeys_card q)) k)).2 =
            x (f k)
          rw [← hkeys]
          rfl
      rw [hpoints]
      exact hx]
  apply MeasurableSet.iUnion
  intro f
  apply MeasurableSet.inter
  · cases n with
    | zero =>
        convert MeasurableSet.univ
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Subsingleton.strictMono _
    | succ m =>
        rw [show {x : Fin (m + 1) → X × ℝ |
              StrictMono (fun k => toLex ((x (f k)).2, f k))} =
            ⋂ i : Fin m, {x |
              toLex ((x (f i.castSucc)).2, f i.castSucc) <
                toLex ((x (f i.succ)).2, f i.succ)} by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_iInter]
          exact Fin.strictMono_iff_lt_succ]
        apply MeasurableSet.iInter
        intro i
        simp only [Prod.Lex.toLex_lt_toLex]
        measurability
  · have hg : Measurable
        (fun x : Fin n → X × ℝ => fun k => x (f k)) :=
      measurable_pi_lambda _ fun k => measurable_pi_apply (f k)
    have hsn : MeasurableSet (fixedSizeEmbed n ⁻¹' s) := hs n
    exact hsn.preimage hg

/-- The canonical finite marked Poisson configuration law stores the atoms in
increasing mark order.  It is the measurable image of the raw conditionally
i.i.d. marked sequence law. -/
noncomputable def canonicalMarkedPoissonSampleLaw
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure (FiniteSample (X × ℝ)) :=
  Measure.map orderByMarks (finiteMarkedPoissonSampleLaw P R lam)

/-- The canonical mark-ordered configuration law is a probability measure. -/
instance canonicalMarkedPoissonSampleLaw_isProbabilityMeasure
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    IsProbabilityMeasure (canonicalMarkedPoissonSampleLaw P R lam) := by
  unfold canonicalMarkedPoissonSampleLaw
  exact Measure.isProbabilityMeasure_map measurable_orderByMarks.aemeasurable

/-- Superpose finitely many cell configurations and put the resulting atoms in
their canonical increasing-mark order. -/
noncomputable def superposeByMarks
    (q : ι → FiniteSample (X × ℝ)) : FiniteSample (X × ℝ) :=
  orderByMarks (superpose q)

/-- Mark-ordered finite superposition is measurable. -/
lemma measurable_superposeByMarks :
    Measurable (superposeByMarks :
      (ι → FiniteSample (X × ℝ)) → FiniteSample (X × ℝ)) := by
  exact measurable_orderByMarks.comp measurable_superpose
/-- Marks in the ordered sequence are nondecreasing. -/
lemma orderByMarks_monotone_marks (s : FiniteSample (X × ℝ))
    {a b : Fin s.count} (hab : a ≤ b) :
    ((orderByMarks s).points (Fin.cast (orderByMarks_count s).symm a)).2 ≤
      ((orderByMarks s).points (Fin.cast (orderByMarks_count s).symm b)).2 := by
  classical
  change
    (s.points (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) a).1)).2).2 ≤
      (s.points (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) b).1)).2).2
  have hkey (k : Fin s.count) :
      (s.points (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2).2 =
        (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).1 := by
    exact congrArg (fun z : ℝ ×ₗ Fin s.count => (ofLex z).1)
      (markedKey_decode s
        (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).2))
  rw [hkey a, hkey b]
  exact Prod.Lex.monotone_fst _ _
    (((markedKeys s).orderIsoOfFin (markedKeys_card s)).monotone hab)

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
