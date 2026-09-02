import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.Splitting
import Mathlib.Data.Prod.Lex
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.Independence.InfinitePi

/-!
# Finite superposition and canonical mark ordering

This file concatenates a finite family of cell configurations and sorts a
marked configuration by its real marks, using the original index only to break
null-event ties. It establishes the measurable canonical configuration law and
its inverse-in-law relationship with partition restriction.
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

/-- The `n` points of a finite sample that is known to have exactly `n` of them, read off as
an `n`-tuple. -/
noncomputable def pointsOfCount {Y : Type*} [MeasurableSpace Y]
    (n : ℕ) (s : {s : FiniteSample Y // s.count = n}) : Fin n → Y :=
  fun k => s.1.points (Fin.cast s.2.symm k)

/-- Reading the `n` points off a finite sample of known size `n` is a measurable map into the
space of `n`-tuples. -/
@[fun_prop]
lemma measurable_pointsOfCount {Y : Type*} [MeasurableSpace Y] (n : ℕ) :
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
      have hk : Measurable (fun x : Fin n → Y => x k) := by fun_prop
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

/-- Concatenate one tuple of points per index into a single finite sample, given the per-index
point counts `c`. -/
noncomputable def fixedCountSuperpose {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) (x : ∀ j, Fin (c j) → Y) : FiniteSample Y := by
  classical
  let S := Σ j : ι, Fin (c j)
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  exact ⟨Fintype.card S, fun k => x (e.symm k).1 (e.symm k).2⟩

/-- Concatenating a family of point tuples of fixed sizes into one finite sample is a
measurable map. -/
@[fun_prop]
lemma measurable_fixedCountSuperpose {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) : Measurable (fixedCountSuperpose (Y := Y) c) := by
  classical
  unfold fixedCountSuperpose
  apply (measurable_fixedSizeEmbed _).comp
  apply measurable_pi_lambda
  intro k
  let u := (Fintype.equivFin (Σ j : ι, Fin (c j))).symm k
  exact (measurable_pi_apply u.2).comp (measurable_pi_apply u.1)

/-- On the event that each component sample has exactly `c j` points, read off the points of
every component as a family of tuples. -/
noncomputable def fiberPoints {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) (q : countFiber (Y := Y) c) : ∀ j, Fin (c j) → Y :=
  fun j => pointsOfCount (c j) ⟨q.1 j, q.2 j⟩

/-- Reading off the points of every component sample on the fixed-count event is a measurable
map. -/
@[fun_prop]
lemma measurable_fiberPoints {Y : Type*} [MeasurableSpace Y]
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
  exact fixedCountSuperpose_eq_superpose q.1 c hc

/-- Finite superposition is measurable. -/
@[fun_prop]
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

/-- The number of lexicographic mark-and-index keys equals the number of
marked observations in the finite sample. -/
lemma markedKeys_card (s : FiniteSample (X × ℝ)) :
    (markedKeys s).card = s.count := by
  classical
  rw [markedKeys, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg (fun z : ℝ ×ₗ Fin s.count => (ofLex z).2) h

/-- A key belonging to the mark-ordering set is recovered by decoding its
stored original index and rebuilding its mark-and-index pair. -/
lemma markedKey_decode (s : FiniteSample (X × ℝ))
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
@[fun_prop]
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
          exact ha
        have hb' : toLex ((x (f b)).2, f b) = (e b).1 := by
          exact hb
        rw [ha', hb']
        exact e.strictMono hab
      · simpa [q, e, f, orderByMarks, fixedSizeEmbed, FiniteSample.count,
          FiniteSample.points] using hx
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
        (fun x : Fin n → X × ℝ => fun k => x (f k)) := by fun_prop
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
@[fun_prop]
lemma measurable_superposeByMarks :
    Measurable (superposeByMarks :
      (ι → FiniteSample (X × ℝ)) → FiniteSample (X × ℝ)) := by
  exact measurable_orderByMarks.comp measurable_superpose

private lemma superpose_restrictPartition_count
    (p : FiniteMeasurablePartition X ι) (s : FiniteSample (X × ℝ)) :
    (superpose (p.restrictPartition s)).count = s.count := by
  classical
  rw [superpose_count]
  simp only [FiniteMeasurablePartition.restrictPartition,
    FiniteMeasurablePartition.restrictCell, FiniteSample.count]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin s.count)))
    (t := (Finset.univ : Finset ι))
    (f := fun k => p.cell (s.points k).1)
    (fun k _ => Finset.mem_univ (p.cell (s.points k).1))
  have hcard : (Finset.univ : Finset (Fin s.count)).card = s.count := Finset.card_fin _
  rw [hcard] at h
  simpa only [FiniteMeasurablePartition.cellIndices, FiniteSample.count] using h.symm

private lemma superpose_restrictPartition_point_mem
    (p : FiniteMeasurablePartition X ι) (s : FiniteSample (X × ℝ))
    (k : Fin (superpose (p.restrictPartition s)).count) :
    ∃ l : Fin s.count,
      (superpose (p.restrictPartition s)).points k = s.points l := by
  classical
  let S := Σ j : ι, Fin (p.restrictPartition s j).count
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let u := e.symm k
  refine ⟨(p.cellIndices u.1 s).orderIsoOfFin rfl u.2, ?_⟩
  rfl

private lemma point_mem_superpose_restrictPartition
    (p : FiniteMeasurablePartition X ι) (s : FiniteSample (X × ℝ))
    (l : Fin s.count) :
    ∃ k : Fin (superpose (p.restrictPartition s)).count,
      (superpose (p.restrictPartition s)).points k = s.points l := by
  classical
  let j := p.cell (s.points l).1
  have hl : l ∈ p.cellIndices j s := by
    simp [FiniteMeasurablePartition.cellIndices, j]
  let a : Fin (p.restrictPartition s j).count :=
    (Finset.orderIsoOfFin (s := p.cellIndices j s) rfl).symm ⟨l, hl⟩
  let e := Fintype.equivFin (Σ j : ι, Fin (p.restrictPartition s j).count)
  refine ⟨e ⟨j, a⟩, ?_⟩
  have ha : (p.restrictPartition s j).points a = s.points l := by
    change s.points
        ((p.cellIndices j s).orderIsoOfFin rfl a) = s.points l
    rw [show (p.cellIndices j s).orderIsoOfFin rfl a = ⟨l, hl⟩ by
      exact (p.cellIndices j s).orderIsoOfFin rfl |>.apply_symm_apply ⟨l, hl⟩]
  change (p.restrictPartition s (e.symm (e ⟨j, a⟩)).1).points
      (e.symm (e ⟨j, a⟩)).2 = s.points l
  rw [e.symm_apply_apply]
  exact ha

private noncomputable def sampleMarks (s : FiniteSample (X × ℝ)) : Finset ℝ := by
  classical
  exact Finset.univ.image fun k => (s.points k).2

private lemma sampleMarks_card_of_pairwise_distinct
    (s : FiniteSample (X × ℝ))
    (h : ∀ i j : Fin s.count, i ≠ j → (s.points i).2 ≠ (s.points j).2) :
    (sampleMarks s).card = s.count := by
  classical
  rw [sampleMarks, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    by_contra hne
    exact (h i j hne) hij

private lemma orderByMarks_monotone_marks'
    (s : FiniteSample (X × ℝ)) {a b : Fin s.count} (hab : a ≤ b) :
    ((orderByMarks s).points a).2 ≤ ((orderByMarks s).points b).2 := by
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

private lemma orderByMarks_strictMono_marks
    (s : FiniteSample (X × ℝ))
    (h : ∀ i j : Fin s.count, i ≠ j → (s.points i).2 ≠ (s.points j).2) :
    StrictMono (fun k : Fin s.count => ((orderByMarks s).points k).2) := by
  classical
  intro a b hab
  refine lt_of_le_of_ne (orderByMarks_monotone_marks' s (le_of_lt hab)) ?_
  let f : Fin s.count → Fin s.count := fun k =>
    (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2
  have hf : Function.Injective f := by
    intro i j hij
    apply ((markedKeys s).orderIsoOfFin (markedKeys_card s)).injective
    apply Subtype.ext
    have hi := markedKey_decode s
      (((markedKeys s).orderIsoOfFin (markedKeys_card s) i).2)
    have hj := markedKey_decode s
      (((markedKeys s).orderIsoOfFin (markedKeys_card s) j).2)
    rw [← hi, ← hj]
    change toLex ((s.points (f i)).2, f i) =
      toLex ((s.points (f j)).2, f j)
    rw [hij]
  exact h (f a) (f b) (hf.ne hab.ne)

private lemma orderByMarks_eq_of_same_points
    (s t : FiniteSample (X × ℝ)) (hcount : s.count = t.count)
    (hst : ∀ i : Fin s.count, ∃ j : Fin t.count, s.points i = t.points j)
    (hts : ∀ j : Fin t.count, ∃ i : Fin s.count, s.points i = t.points j)
    (hdist : ∀ i j : Fin t.count, i ≠ j → (t.points i).2 ≠ (t.points j).2) :
    orderByMarks s = orderByMarks t := by
  classical
  rcases s with ⟨m, x⟩
  rcases t with ⟨n, y⟩
  change m = n at hcount
  subst n
  change (⟨m, _⟩ : FiniteSample (X × ℝ)) = ⟨m, _⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    have hsmark : sampleMarks (⟨m, x⟩ : FiniteSample (X × ℝ)) =
        sampleMarks (⟨m, y⟩ : FiniteSample (X × ℝ)) := by
      ext r
      simp only [sampleMarks, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        obtain ⟨j, hij⟩ := hst i
        exact ⟨j, (congrArg Prod.snd hij).symm⟩
      · rintro ⟨j, rfl⟩
        obtain ⟨i, hij⟩ := hts j
        exact ⟨i, congrArg Prod.snd hij⟩
    let f : Fin m → Fin m := fun i => Classical.choose (hst i)
    have hf_spec (i : Fin m) : x i = y (f i) := Classical.choose_spec (hst i)
    have hf_surj : Function.Surjective f := by
      intro j
      obtain ⟨i, hij⟩ := hts j
      refine ⟨i, ?_⟩
      by_contra hne
      exact hdist (f i) j hne
        ((congrArg Prod.snd (hf_spec i)).symm.trans (congrArg Prod.snd hij))
    have hf_bij : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).2 ⟨hf_surj, rfl⟩
    have hs_dist : ∀ i j : Fin m, i ≠ j → (x i).2 ≠ (x j).2 := by
      intro i j hij heq
      apply hij
      apply hf_bij.1
      by_contra hne
      exact hdist (f i) (f j) hne
        ((congrArg Prod.snd (hf_spec i)).symm.trans
          (heq.trans (congrArg Prod.snd (hf_spec j))))
    have hcard := sampleMarks_card_of_pairwise_distinct
      (⟨m, y⟩ : FiniteSample (X × ℝ)) hdist
    have hxenum : (fun k : Fin m =>
        ((orderByMarks (⟨m, x⟩ : FiniteSample (X × ℝ))).points k).2) =
        (sampleMarks (⟨m, y⟩ : FiniteSample (X × ℝ))).orderEmbOfFin hcard := by
      apply Finset.orderEmbOfFin_unique hcard
      · intro k
        rw [← hsmark]
        refine Finset.mem_image.mpr ⟨
          (ofLex (((markedKeys (⟨m, x⟩ : FiniteSample (X × ℝ))).orderIsoOfFin
            (markedKeys_card _) k).1)).2, Finset.mem_univ _, ?_⟩
        rfl
      · exact orderByMarks_strictMono_marks
          (⟨m, x⟩ : FiniteSample (X × ℝ)) hs_dist
    have hyenum : (fun k : Fin m =>
        ((orderByMarks (⟨m, y⟩ : FiniteSample (X × ℝ))).points k).2) =
        (sampleMarks (⟨m, y⟩ : FiniteSample (X × ℝ))).orderEmbOfFin hcard := by
      apply Finset.orderEmbOfFin_unique hcard
      · intro k
        refine Finset.mem_image.mpr ⟨
          (ofLex (((markedKeys (⟨m, y⟩ : FiniteSample (X × ℝ))).orderIsoOfFin
            (markedKeys_card _) k).1)).2, Finset.mem_univ _, ?_⟩
        rfl
      · exact orderByMarks_strictMono_marks
          (⟨m, y⟩ : FiniteSample (X × ℝ)) hdist
    funext k
    let ix := (ofLex (((markedKeys (⟨m, x⟩ : FiniteSample (X × ℝ))).orderIsoOfFin
      (markedKeys_card _) k).1)).2
    let iy := (ofLex (((markedKeys (⟨m, y⟩ : FiniteSample (X × ℝ))).orderIsoOfFin
      (markedKeys_card _) k).1)).2
    obtain ⟨j, hj⟩ := hst ix
    have hmark : (x ix).2 = (y iy).2 :=
      congrFun (hxenum.trans hyenum.symm) k
    have hjiy : j = iy := by
      by_contra hne
      exact hdist j iy hne ((congrArg Prod.snd hj).symm.trans hmark)
    change x ix = y iy
    simpa [hjiy, FiniteSample.points] using hj

private lemma orderByMarks_point_mem (s : FiniteSample (X × ℝ))
    (k : Fin (orderByMarks s).count) :
    ∃ l : Fin s.count, (orderByMarks s).points k = s.points l := by
  exact ⟨(ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2, rfl⟩

private lemma point_mem_orderByMarks (s : FiniteSample (X × ℝ))
    (l : Fin s.count) :
    ∃ k : Fin (orderByMarks s).count, (orderByMarks s).points k = s.points l := by
  classical
  let f : Fin s.count → Fin s.count := fun k =>
    (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2
  have hf : Function.Injective f := by
    intro i j hij
    apply ((markedKeys s).orderIsoOfFin (markedKeys_card s)).injective
    apply Subtype.ext
    have hi := markedKey_decode s
      (((markedKeys s).orderIsoOfFin (markedKeys_card s) i).2)
    have hj := markedKey_decode s
      (((markedKeys s).orderIsoOfFin (markedKeys_card s) j).2)
    rw [← hi, ← hj]
    change toLex ((s.points (f i)).2, f i) =
      toLex ((s.points (f j)).2, f j)
    rw [hij]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, rfl⟩
  obtain ⟨k, hk⟩ := hf_bij.2 l
  refine ⟨k, ?_⟩
  change s.points (f k) = s.points l
  rw [hk]

private lemma orderByMarks_eq_self_of_strictMono_marks
    (s : FiniteSample (X × ℝ))
    (h : StrictMono (fun k : Fin s.count => (s.points k).2)) :
    orderByMarks s = s := by
  classical
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    have hkeys : (fun k : Fin s.count => toLex ((s.points k).2, k)) =
        (markedKeys s).orderEmbOfFin (markedKeys_card s) := by
      apply Finset.orderEmbOfFin_unique (markedKeys_card s)
      · intro k
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      · intro a b hab
        simp only [Prod.Lex.toLex_lt_toLex]
        exact Or.inl (h hab)
    funext k
    change s.points
        (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2 =
      s.points k
    congr 1
    have hk := congrFun hkeys k
    exact congrArg (fun z : ℝ ×ₗ Fin s.count => (ofLex z).2) hk.symm

private lemma restrictCell_orderByMarks_commute
    (p : FiniteMeasurablePartition X ι) (j : ι)
    (s : FiniteSample (X × ℝ))
    (hdist : ∀ i k : Fin s.count, i ≠ k →
      (s.points i).2 ≠ (s.points k).2) :
    p.restrictCell j (orderByMarks s) = orderByMarks (p.restrictCell j s) := by
  classical
  let f : Fin s.count → Fin s.count := fun k =>
    (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2
  have hf : Function.Injective f := by
    intro a b hab
    apply ((markedKeys s).orderIsoOfFin (markedKeys_card s)).injective
    apply Subtype.ext
    have ha := markedKey_decode s
      (((markedKeys s).orderIsoOfFin (markedKeys_card s) a).2)
    have hb := markedKey_decode s
      (((markedKeys s).orderIsoOfFin (markedKeys_card s) b).2)
    rw [← ha, ← hb]
    change toLex ((s.points (f a)).2, f a) =
      toLex ((s.points (f b)).2, f b)
    rw [hab]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, rfl⟩
  let eall : Fin s.count ≃ Fin s.count := Equiv.ofBijective f hf_bij
  let u := p.cellIndices j (orderByMarks s)
  let t := p.cellIndices j s
  have hmem (k : Fin s.count) : k ∈ u ↔ eall k ∈ t := by
    constructor
    · intro hk
      have hk' : p.cell ((orderByMarks s).points k).1 = j := by
        exact (Finset.mem_filter.mp (show k ∈ u from hk)).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change p.cell (s.points (f k)).1 = j
      exact hk'
    · intro hk
      have hk' : p.cell (s.points (eall k)).1 = j :=
        (Finset.mem_filter.mp (show eall k ∈ t from hk)).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change p.cell (s.points (f k)).1 = j at hk'
      exact hk'
  let ecells : {k // k ∈ u} ≃ {k // k ∈ t} :=
    Equiv.subtypeEquiv eall hmem
  have hcount : (p.restrictCell j (orderByMarks s)).count =
      (p.restrictCell j s).count := by
    change u.card = t.card
    simpa using Fintype.card_congr ecells
  have hforward : ∀ i : Fin (p.restrictCell j (orderByMarks s)).count,
      ∃ k : Fin (p.restrictCell j s).count,
        (p.restrictCell j (orderByMarks s)).points i =
          (p.restrictCell j s).points k := by
    intro i
    let ui : {k // k ∈ u} := u.orderIsoOfFin rfl i
    let ti : {k // k ∈ t} := ecells ui
    let k : Fin t.card := (t.orderIsoOfFin rfl).symm ti
    refine ⟨k, ?_⟩
    change s.points (f (u.orderIsoOfFin rfl i).1) =
      s.points (t.orderIsoOfFin rfl k)
    congr 1
    calc
      f (u.orderIsoOfFin rfl i).1 = ti.1 := rfl
      _ = (t.orderIsoOfFin rfl k).1 :=
        congrArg Subtype.val ((t.orderIsoOfFin rfl).apply_symm_apply ti).symm
  have hbackward : ∀ k : Fin (p.restrictCell j s).count,
      ∃ i : Fin (p.restrictCell j (orderByMarks s)).count,
        (p.restrictCell j (orderByMarks s)).points i =
          (p.restrictCell j s).points k := by
    intro k
    let ti : {l // l ∈ t} := t.orderIsoOfFin rfl k
    let ui : {l // l ∈ u} := ecells.symm ti
    let i : Fin u.card := (u.orderIsoOfFin rfl).symm ui
    refine ⟨i, ?_⟩
    change s.points (f (u.orderIsoOfFin rfl i).1) =
      s.points (t.orderIsoOfFin rfl k)
    congr 1
    exact Subtype.ext_iff.mp (ecells.apply_eq_iff_eq_symm_apply.mpr
      ((u.orderIsoOfFin rfl).apply_symm_apply ui))
  have hdistCell : ∀ a b : Fin (p.restrictCell j s).count, a ≠ b →
      ((p.restrictCell j s).points a).2 ≠
        ((p.restrictCell j s).points b).2 := by
    intro a b hab
    apply hdist
    intro heq
    apply hab
    exact (t.orderIsoOfFin rfl).injective (Subtype.ext heq)
  have hsorted : orderByMarks (p.restrictCell j (orderByMarks s)) =
      orderByMarks (p.restrictCell j s) :=
    orderByMarks_eq_of_same_points _ _ hcount hforward hbackward hdistCell
  rw [← hsorted]
  symm
  apply orderByMarks_eq_self_of_strictMono_marks
  exact (orderByMarks_strictMono_marks s hdist).comp
    (u.orderEmbOfFin rfl).strictMono

private lemma restrictPartition_orderByMarks_commute
    (p : FiniteMeasurablePartition X ι) (s : FiniteSample (X × ℝ))
    (hdist : ∀ i k : Fin s.count, i ≠ k →
      (s.points i).2 ≠ (s.points k).2) :
    p.restrictPartition (orderByMarks s) =
      fun j => orderByMarks (p.restrictCell j s) := by
  funext j
  exact restrictCell_orderByMarks_commute p j s hdist

private lemma superposeByMarks_restrictPartition_orderByMarks
    (p : FiniteMeasurablePartition X ι) (s : FiniteSample (X × ℝ))
    (hdist : ∀ i j : Fin s.count, i ≠ j → (s.points i).2 ≠ (s.points j).2) :
    superposeByMarks (p.restrictPartition (orderByMarks s)) = orderByMarks s := by
  unfold superposeByMarks
  calc
    orderByMarks (superpose (p.restrictPartition (orderByMarks s))) =
        orderByMarks (orderByMarks s) := by
      apply orderByMarks_eq_of_same_points
      · exact superpose_restrictPartition_count p (orderByMarks s)
      · exact superpose_restrictPartition_point_mem p (orderByMarks s)
      · exact point_mem_superpose_restrictPartition p (orderByMarks s)
      · intro i j hij
        exact (orderByMarks_strictMono_marks s hdist).injective.ne hij
    _ = orderByMarks s := by
      apply orderByMarks_eq_of_same_points
      · rfl
      · exact orderByMarks_point_mem s
      · exact point_mem_orderByMarks s
      · exact hdist

private lemma measurableSet_marks_pairwise_distinct :
    MeasurableSet {s : FiniteSample (X × ℝ) |
      ∀ i j : Fin s.count, i ≠ j → (s.points i).2 ≠ (s.points j).2} := by
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet {x : Fin n → X × ℝ |
    ∀ i j, i ≠ j → (x i).2 ≠ (x j).2}
  rw [show {x : Fin n → X × ℝ |
      ∀ i j, i ≠ j → (x i).2 ≠ (x j).2} =
      ⋂ i, ⋂ j, ⋂ (_h : i ≠ j), {x | (x i).2 ≠ (x j).2} by
    ext x
    simp]
  measurability

private lemma iidStreamLaw_marks_pairwise_distinct
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R] :
    ∀ᵐ z : ℕ → X × ℝ ∂iidStreamLaw (P.prod R),
      ∀ i j, i ≠ j → (z i).2 ≠ (z j).2 := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · subst j
    exact Filter.Eventually.of_forall fun _ h => (h rfl).elim
  · have hind : (fun z : ℕ → X × ℝ => (z i).2) ⟂ᵢ[iidStreamLaw (P.prod R)]
        (fun z => (z j).2) := by
      exact (iIndepFun_infinitePi (P := fun _ : ℕ => P.prod R)
        (X := fun _ => Prod.snd) (fun _ => measurable_snd)).indepFun hij
    have hmarg (k : ℕ) :
        Measure.map (fun z : ℕ → X × ℝ => (z k).2)
          (iidStreamLaw (P.prod R)) = R := by
      rw [show (fun z : ℕ → X × ℝ => (z k).2) =
          Prod.snd ∘ (fun z : ℕ → X × ℝ => z k) by rfl,
        ← Measure.map_map measurable_snd (by fun_prop)]
      unfold iidStreamLaw
      rw [Measure.infinitePi_map_eval, Measure.map_snd_prod, measure_univ, one_smul]
    have hpair :
        Measure.map (fun z : ℕ → X × ℝ => ((z i).2, (z j).2))
          (iidStreamLaw (P.prod R)) = R.prod R := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map
          ((by fun_prop : Measurable (fun z : ℕ → X × ℝ => (z i).2)).aemeasurable)
          ((by fun_prop : Measurable (fun z : ℕ → X × ℝ => (z j).2)).aemeasurable)).mp
            hind,
        hmarg i, hmarg j]
    have hdiag : R.prod R (diagonal ℝ) = 0 := by
      rw [Measure.prod_apply measurableSet_diagonal]
      simp [diagonal]
    have hne : ∀ᵐ z : ℕ → X × ℝ ∂iidStreamLaw (P.prod R),
        (z i).2 ≠ (z j).2 := by
      apply compl_mem_ae_iff.2
      rw [← hdiag, ← hpair, Measure.map_apply (by fun_prop) measurableSet_diagonal]
      rfl
    exact hne.mono fun _ hz _ => hz

/-- Atomless independent marks are pairwise distinct with probability one in
the finite marked Poisson sample. -/
lemma finiteMarkedPoissonSampleLaw_marks_pairwise_distinct
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R] (lam : ℝ≥0) :
    finiteMarkedPoissonSampleLaw P R lam
        {s | ∀ i j : Fin s.count, i ≠ j → (s.points i).2 ≠ (s.points j).2} = 1 := by
  rw [← mem_ae_iff_prob_eq_one measurableSet_marks_pairwise_distinct]
  unfold finiteMarkedPoissonSampleLaw finitePoissonSampleLaw
  apply (mem_ae_map_iff measurable_streamToFiniteSample.aemeasurable
    measurableSet_marks_pairwise_distinct).2
  have hstream := iidStreamLaw_marks_pairwise_distinct P R
  have hsource : ∀ᵐ z : ℕ × (ℕ → X × ℝ)
      ∂poissonIIDStreamLaw (P.prod R) lam,
      ∀ i j, i ≠ j → (z.2 i).2 ≠ (z.2 j).2 := by
    unfold poissonIIDStreamLaw
    exact (measurePreserving_snd.quasiMeasurePreserving.ae hstream)
  exact hsource.mono fun z hz i j hij =>
    hz i.val j.val (fun h => hij (Fin.ext h))

/-- Restricting the canonical global configuration gives exactly the product
of independent canonical cell configurations. -/
lemma map_restrictPartition_canonicalMarkedPoissonSampleLaw
    [StandardBorelSpace X]
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R] (lam : ℝ≥0) :
    Measure.map p.restrictPartition (canonicalMarkedPoissonSampleLaw P R lam) =
      Measure.pi (fun j : ι =>
        canonicalMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
          (lam * p.cellMass P j)) := by
  let μ := finiteMarkedPoissonSampleLaw P R lam
  let f : (i : ι) → FiniteSample (X × ℝ) → FiniteSample (X × ℝ) :=
    fun _ => orderByMarks
  have hf : Measurable (fun q : ι → FiniteSample (X × ℝ) =>
      fun j => f j (q j)) := by fun_prop
  have hdistinct :=
    finiteMarkedPoissonSampleLaw_marks_pairwise_distinct P R lam
  rw [← mem_ae_iff_prob_eq_one measurableSet_marks_pairwise_distinct] at hdistinct
  unfold canonicalMarkedPoissonSampleLaw
  rw [Measure.map_map p.measurable_restrictPartition measurable_orderByMarks]
  have hcomm :
      Measure.map (p.restrictPartition ∘ orderByMarks) μ =
        Measure.map ((fun q j => f j (q j)) ∘ p.restrictPartition) μ := by
    apply Measure.map_congr
    filter_upwards [hdistinct] with s hs
    exact restrictPartition_orderByMarks_commute p s hs
  rw [show finiteMarkedPoissonSampleLaw P R lam = μ by rfl, hcomm]
  rw [← Measure.map_map hf p.measurable_restrictPartition]
  rw [show μ = finiteMarkedPoissonSampleLaw P R lam by rfl,
    FiniteMeasurablePartition.map_restrictPartition_finiteMarkedPoissonSampleLaw]
  rw [Measure.pi_map_pi]
  intro j
  exact measurable_orderByMarks.aemeasurable

/-- Restriction followed by mark-ordered superposition is the identity in law
on the canonical marked Poisson configuration. -/
lemma map_superposeByMarks_map_restrictPartition
    [StandardBorelSpace X]
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R] (lam : ℝ≥0) :
    Measure.map superposeByMarks
        (Measure.map p.restrictPartition
          (canonicalMarkedPoissonSampleLaw P R lam)) =
      canonicalMarkedPoissonSampleLaw P R lam := by
  unfold canonicalMarkedPoissonSampleLaw
  rw [Measure.map_map measurable_superposeByMarks p.measurable_restrictPartition,
    Measure.map_map
      (measurable_superposeByMarks.comp p.measurable_restrictPartition)
      measurable_orderByMarks]
  apply Measure.map_congr
  have hdistinct := finiteMarkedPoissonSampleLaw_marks_pairwise_distinct P R lam
  have hae : {s : FiniteSample (X × ℝ) |
      ∀ i j : Fin s.count, i ≠ j → (s.points i).2 ≠ (s.points j).2} ∈
        ae (finiteMarkedPoissonSampleLaw P R lam) :=
    (mem_ae_iff_prob_eq_one measurableSet_marks_pairwise_distinct).2 hdistinct
  exact Filter.Eventually.mono hae fun s hs =>
    superposeByMarks_restrictPartition_orderByMarks p s hs

/-- **Superposition recovers the canonical global law.** Under [nonnegative intensity
`lam`](hyp:lam), and independently for each cell `j` of the finite measurable partition `p`, draw a
canonical marked Poisson configuration with base measure `p.cellObservationLaw P j`, mark
distribution `R`, and intensity `lam` times the `P`-mass of cell `j`; [merging these per-cell
configurations by increasing mark (mark-ordered superposition) has exactly the law of the canonical
marked Poisson configuration with base measure `P`, mark distribution `R`, and intensity
`lam`](goal). -/
lemma map_superposeByMarks_canonicalCellLaws
    [StandardBorelSpace X]
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R] (lam : ℝ≥0) :
    Measure.map superposeByMarks
        (Measure.pi (fun j : ι =>
          canonicalMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
            (lam * p.cellMass P j))) =
      canonicalMarkedPoissonSampleLaw P R lam := by
  rw [← map_restrictPartition_canonicalMarkedPoissonSampleLaw p P R lam]
  exact map_superposeByMarks_map_restrictPartition p P R lam

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
