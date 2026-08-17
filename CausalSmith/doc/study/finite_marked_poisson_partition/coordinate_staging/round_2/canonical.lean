import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Superposition.Ordering

/-!
# Canonical marked Poisson configurations

This file gives the mark-ordered version of a finite marked Poisson sample.
It proves that independent restrictions to a finite partition and measurable
mark-ordered superposition are inverse in law when the mark distribution has no
atoms.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/- The ordering module keeps these implementation lemmas private.  The
canonical-law proof needs the same facts after the module boundary, so they are
restated privately here rather than promoted as part of the public API. -/

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
  simpa [FiniteMeasurablePartition.cellIndices] using h.symm

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
    simpa [hjiy] using hj

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
    (R : Measure ℝ) [IsProbabilityMeasure R] [NoAtoms R] :
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
    (R : Measure ℝ) [IsProbabilityMeasure R] [NoAtoms R] (lam : ℝ≥0) :
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
    (R : Measure ℝ) [IsProbabilityMeasure R] [NoAtoms R] (lam : ℝ≥0) :
    Measure.map p.restrictPartition (canonicalMarkedPoissonSampleLaw P R lam) =
      Measure.pi (fun j : ι =>
        canonicalMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
          (lam * p.cellMass P j)) := by
  let μ := finiteMarkedPoissonSampleLaw P R lam
  let f : (i : ι) → FiniteSample (X × ℝ) → FiniteSample (X × ℝ) :=
    fun _ => orderByMarks
  have hf : Measurable (fun q : ι → FiniteSample (X × ℝ) =>
      fun j => f j (q j)) :=
    measurable_pi_lambda _ fun j =>
      measurable_orderByMarks.comp (measurable_pi_apply j)
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
    (R : Measure ℝ) [IsProbabilityMeasure R] [NoAtoms R] (lam : ℝ≥0) :
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

/-- Superposing independent canonical cell configurations recovers the
canonical global configuration law exactly. -/
lemma map_superposeByMarks_canonicalCellLaws
    [StandardBorelSpace X]
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NoAtoms R] (lam : ℝ≥0) :
    Measure.map superposeByMarks
        (Measure.pi (fun j : ι =>
          canonicalMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
            (lam * p.cellMass P j))) =
      canonicalMarkedPoissonSampleLaw P R lam := by
  rw [← map_restrictPartition_canonicalMarkedPoissonSampleLaw p P R lam]
  exact map_superposeByMarks_map_restrictPartition p P R lam

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
