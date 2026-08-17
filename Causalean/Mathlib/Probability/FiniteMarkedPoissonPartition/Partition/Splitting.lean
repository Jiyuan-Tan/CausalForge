import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Poisson splitting across a finite partition

This file proves the exact joint law of the restrictions of a finite marked
Poisson sample to the cells of a finite measurable partition.  The proof
tracks the complete vector of cell counts and combines the multinomial count
allocation with the conditional product laws within cells.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

namespace FiniteMeasurablePartition

private noncomputable def wordHistogram {n : ℕ} (w : Fin n → ι) (j : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun k => w k = j).card

private noncomputable def histogramWords (n : ℕ) (c : ι → ℕ) : Finset (Fin n → ι) := by
  classical
  exact Finset.univ.filter fun w => ∀ j, wordHistogram w j = c j

private lemma sum_wordHistogram {n : ℕ} (w : Fin n → ι) :
    ∑ j, wordHistogram w j = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset ι))
    (f := w) (fun x _ => Finset.mem_univ (w x))
  simpa [wordHistogram] using h.symm

private def wordOfEquiv (c : ι → ℕ) {n : ℕ}
    (e : (Σ j, Fin (c j)) ≃ Fin n) : Fin n → ι :=
  fun k => (e.symm k).1

private lemma wordOfEquiv_fiber_ncard (c : ι → ℕ) {n : ℕ}
    (e : (Σ j, Fin (c j)) ≃ Fin n) (j : ι) :
    Set.ncard {k : Fin n | wordOfEquiv c e k = j} = c j := by
  let A : Set (Σ j, Fin (c j)) := {u | u.1 = j}
  have hA : A = (fun k : Fin (c j) =>
      (⟨j, k⟩ : Σ j, Fin (c j))) '' Set.univ := by
    ext u
    constructor
    · intro hu
      rcases u with ⟨i, k⟩
      change i = j at hu
      subst i
      exact ⟨k, Set.mem_univ _, rfl⟩
    · rintro ⟨k, -, rfl⟩
      rfl
  have hpre : {k : Fin n | wordOfEquiv c e k = j} = e '' A := by
    ext k
    constructor
    · intro hk
      exact ⟨e.symm k, hk, e.apply_symm_apply k⟩
    · rintro ⟨u, hu, rfl⟩
      simpa [wordOfEquiv, A] using hu
  rw [hpre, Set.ncard_image_of_injective A e.injective, hA,
    Set.ncard_image_of_injective Set.univ (by
      intro a b hab
      exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2),
    Set.ncard_univ, Nat.card_fin]

private lemma wordOfEquiv_histogram (c : ι → ℕ) {n : ℕ}
    (e : (Σ j, Fin (c j)) ≃ Fin n) (j : ι) :
    wordHistogram (wordOfEquiv c e) j = c j := by
  classical
  calc
    wordHistogram (wordOfEquiv c e) j =
        Fintype.card {k : Fin n // wordOfEquiv c e k = j} := by
      rw [wordHistogram, Fintype.card_subtype]
    _ = Nat.card {k : Fin n // wordOfEquiv c e k = j} :=
      Nat.card_eq_fintype_card.symm
    _ = Set.ncard {k : Fin n | wordOfEquiv c e k = j} :=
      Nat.card_coe_set_eq _
    _ = c j := wordOfEquiv_fiber_ncard c e j

private lemma histogramWords_card (n : ℕ) (c : ι → ℕ)
    (hc : ∑ j, c j = n) :
    (histogramWords n c).card = Nat.multinomial Finset.univ c := by
  classical
  let e : (Σ j : ι, Fin (c j)) ≃ Fin n :=
    Fintype.equivOfCardEq (by simpa using hc)
  let w₀ : Fin n → ι := wordOfEquiv c e
  have hw₀ (j : ι) : wordHistogram w₀ j = c j :=
    wordOfEquiv_histogram c e j
  let H : Set (Fin n → ι) := {w | ∀ j, wordHistogram w j = c j}
  letI : Fintype (Equiv.Perm (Fin n))ᵈᵐᵃ :=
    Fintype.ofEquiv (Equiv.Perm (Fin n)) DomMulAct.mk
  have horbit : MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ w₀ = H := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      intro j
      rw [← hw₀ j]
      unfold wordHistogram
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv
        (DomMulAct.mk.symm g : Equiv.Perm (Fin n)) (by
        intro k
        simp [DomMulAct.smul_apply])
    · intro hw
      have hcard (j : ι) :
          Fintype.card {k : Fin n // w₀ k = j} =
            Fintype.card {k : Fin n // w k = j} := by
        rw [Fintype.card_subtype, Fintype.card_subtype]
        exact (hw₀ j).trans (hw j).symm
      let g : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv fun j =>
        Fintype.equivOfCardEq (hcard j)
      refine ⟨DomMulAct.mk g.symm, ?_⟩
      funext k
      change (DomMulAct.mk g.symm • w₀) k = w k
      rw [DomMulAct.smul_apply]
      change w₀ (g.symm k) = w k
      symm
      have hg := Equiv.ofFiberEquiv_map (fun j =>
        Fintype.equivOfCardEq (hcard j)) (g.symm k)
      change w (g (g.symm k)) = w₀ (g.symm k) at hg
      simpa using hg
  have hcardH : Fintype.card H = (histogramWords n c).card := by
    rw [Fintype.card_subtype]
    congr 1
  have horbitCard : Fintype.card H * ∏ j, (c j).factorial = n.factorial := by
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (Equiv.Perm (Fin n))ᵈᵐᵃ w₀
    have hstab : Fintype.card
        (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ w₀) =
        ∏ j, (c j).factorial := by
      rw [show Fintype.card
          (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ w₀) =
          Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} by
        apply Fintype.card_congr
        exact Equiv.subtypeEquiv DomMulAct.mk.symm
          (fun g => DomMulAct.mem_stabilizer_iff),
        DomMulAct.stabilizer_card w₀]
      congr 2 with j
      rw [Fintype.card_subtype]
      change (wordHistogram w₀ j).factorial = (c j).factorial
      exact congrArg Nat.factorial (hw₀ j)
    have hdom : Fintype.card (Equiv.Perm (Fin n))ᵈᵐᵃ = n.factorial := by
      rw [← Fintype.card_congr (DomMulAct.mk :
        Equiv.Perm (Fin n) ≃ (Equiv.Perm (Fin n))ᵈᵐᵃ),
        Fintype.card_perm, Fintype.card_fin]
    have horbitCardEq : Fintype.card
        (MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ w₀) = Fintype.card H :=
      Fintype.card_congr (Equiv.setCongr horbit)
    rw [horbitCardEq, hstab, hdom] at hos
    exact hos
  have hmulti := Nat.multinomial_spec Finset.univ c
  rw [hc] at hmulti
  rw [← hcardH]
  apply Nat.eq_of_mul_eq_mul_right (Nat.prod_factorial_pos Finset.univ c)
  simpa [mul_comm] using horbitCard.trans hmulti.symm

private lemma pi_smul {α : ι → Type*} [∀ j, MeasurableSpace (α j)]
    (a : ι → ℝ≥0∞) (μ : (j : ι) → Measure (α j)) [∀ j, SigmaFinite (μ j)]
    [∀ j, SigmaFinite (a j • μ j)] :
    Measure.pi (fun j => a j • μ j) =
      (∏ j, a j) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  exact Finset.prod_mul_distrib.symm

private lemma pi_map_piCurry {κ : ι → Type*} [∀ j, Fintype (κ j)]
    {α : (j : ι) → κ j → Type*}
    [∀ j k, MeasurableSpace (α j k)]
    (μ : (j : ι) → (k : κ j) → Measure (α j k))
    [∀ j k, IsProbabilityMeasure (μ j k)] :
    Measure.map (MeasurableEquiv.piCurry α)
        (Measure.pi (fun u : Σ j, κ j => μ u.1 u.2)) =
      Measure.pi (fun j => Measure.pi (μ j)) := by
  simpa only [Measure.infinitePi_eq_pi] using
    Measure.infinitePi_map_piCurry μ

private noncomputable def wordIndices {n : ℕ} (w : Fin n → ι) (j : ι) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k => w k = j

private lemma wordIndices_card {n : ℕ} (w : Fin n → ι) (j : ι) :
    (wordIndices w j).card = wordHistogram w j := by
  rfl

private noncomputable def wordFiberEquiv {n : ℕ} (w : Fin n → ι) (j : ι) :
    Fin (wordHistogram w j) ≃ {k : Fin n // w k = j} := by
  classical
  exact ((wordIndices w j).orderIsoOfFin (wordIndices_card w j).symm).toEquiv.trans
    (Equiv.subtypeEquiv (Equiv.refl _) (by simp [wordIndices]))

private noncomputable def wordUnshuffleEquiv {n : ℕ} (w : Fin n → ι) :
    (Σ j : ι, Fin (wordHistogram w j)) ≃ Fin n := by
  classical
  exact (Equiv.sigmaCongrRight fun j =>
    wordFiberEquiv w j).trans
      (Equiv.sigmaFiberEquiv w)

private noncomputable def wordEquiv {n : ℕ} (w : Fin n → ι) :
    Fin n ≃ Σ j : ι, Fin (wordHistogram w j) :=
  (wordUnshuffleEquiv w).symm

private lemma wordUnshuffleEquiv_apply {n : ℕ} (w : Fin n → ι)
    (j : ι) (k : Fin (wordHistogram w j)) :
    wordUnshuffleEquiv w ⟨j, k⟩ =
      (wordIndices w j).orderIsoOfFin (wordIndices_card w j).symm k := by
  rfl

private lemma wordEquiv_fst {n : ℕ} (w : Fin n → ι) (k : Fin n) :
    (wordEquiv w k).1 = w k := by
  classical
  let u := wordEquiv w k
  have hp := (wordFiberEquiv w u.1 u.2).property
  change w (wordUnshuffleEquiv w u) = u.1 at hp
  have hu : wordUnshuffleEquiv w u = k :=
    (wordUnshuffleEquiv w).apply_symm_apply k
  rw [hu] at hp
  exact hp.symm

private noncomputable def gatherWord {Y : Type*} [MeasurableSpace Y]
    {n : ℕ} (w : Fin n → ι) (z : Fin n → Y) :
    ∀ j, Fin (wordHistogram w j) → Y :=
  fun j k => z (wordUnshuffleEquiv w ⟨j, k⟩)

private lemma gatherWord_apply {Y : Type*} [MeasurableSpace Y]
    {n : ℕ} (w : Fin n → ι) (z : Fin n → Y)
    (j : ι) (k : Fin (wordHistogram w j)) :
    gatherWord w z j k = z (wordUnshuffleEquiv w ⟨j, k⟩) := by
  rfl

private lemma measurable_gatherWord {Y : Type*} [MeasurableSpace Y]
    {n : ℕ} (w : Fin n → ι) :
    Measurable (gatherWord (Y := Y) w) := by
  have hfun : gatherWord (Y := Y) w =
      MeasurableEquiv.piCurry
        (fun j : ι => fun _ : Fin (wordHistogram w j) => Y) ∘
        MeasurableEquiv.piCongrLeft
          (fun _ : Σ j : ι, Fin (wordHistogram w j) => Y) (wordEquiv w) := by
    funext z j k
    simp only [Function.comp_apply]
    rw [MeasurableEquiv.piCurry_apply]
    change z (wordUnshuffleEquiv w ⟨j, k⟩) =
      (Equiv.piCongrLeft (fun _ : Σ j, Fin (wordHistogram w j) => Y)
        (wordEquiv w)) z ⟨j, k⟩
    rw [Equiv.piCongrLeft_apply]
    simp [wordEquiv]
    exact (eq_rec_constant _ _).symm
  rw [hfun]
  exact (MeasurableEquiv.piCurry _).measurable.comp
    (MeasurableEquiv.piCongrLeft _ (wordEquiv w)).measurable

private lemma map_gatherWord_pi {Y : Type*} [MeasurableSpace Y]
    {n : ℕ} (w : Fin n → ι) (Q : ι → Measure Y)
    [∀ j, IsProbabilityMeasure (Q j)] :
    Measure.map (gatherWord w) (Measure.pi fun k : Fin n => Q (w k)) =
      Measure.pi fun j => Measure.pi fun _ : Fin (wordHistogram w j) => Q j := by
  let e := wordEquiv w
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Σ j : ι, Fin (wordHistogram w j) => Y) e
  have hreindex : Measure.map reindex (Measure.pi fun k : Fin n => Q (w k)) =
      Measure.pi fun u : Σ j : ι, Fin (wordHistogram w j) => Q u.1 := by
    have hμ : (fun k : Fin n => Q (w k)) =
        (fun k : Fin n => Q (e k).1) := by
      funext k
      rw [wordEquiv_fst]
    rw [hμ]
    exact Measure.pi_map_piCongrLeft e
      (fun u : Σ j : ι, Fin (wordHistogram w j) => Q u.1)
  have hfun : gatherWord (Y := Y) w =
      MeasurableEquiv.piCurry
        (fun j : ι => fun _ : Fin (wordHistogram w j) => Y) ∘
        reindex := by
    funext z j k
    simp only [Function.comp_apply]
    rw [MeasurableEquiv.piCurry_apply]
    change z (wordUnshuffleEquiv w ⟨j, k⟩) =
      (Equiv.piCongrLeft (fun _ : Σ j, Fin (wordHistogram w j) => Y)
        e) z ⟨j, k⟩
    rw [Equiv.piCongrLeft_apply]
    simp [e, wordEquiv]
    exact (eq_rec_constant _ _).symm
  rw [hfun, ← Measure.map_map
    (MeasurableEquiv.piCurry _).measurable reindex.measurable,
    hreindex]
  simpa using pi_map_piCurry
    (fun j : ι => fun _ : Fin (wordHistogram w j) => Q j)

private lemma restrict_prod_cellSet
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (j : ι) :
    (P.prod R).restrict (p.cellSet j ×ˢ (Set.univ : Set ℝ)) =
      (p.cellMass P j : ℝ≥0∞) • (p.cellObservationLaw P j).prod R := by
  rw [← Measure.restrict_prod_eq_prod_univ]
  congr 1
  by_cases hj : P (p.cellSet j) = 0
  · rw [Measure.restrict_eq_zero.2 hj]
    have hm : p.cellMass P j = 0 := by
      simp [cellMass, hj]
    simp [hm]
  · rw [cellObservationLaw, dif_neg hj]
    have hcoe : (p.cellMass P j : ℝ≥0∞) = P (p.cellSet j) := by
      exact ENNReal.coe_toNNReal (measure_ne_top P _)
    rw [hcoe, Measure.prod_smul_left, smul_smul,
      ENNReal.mul_inv_cancel hj (measure_ne_top P _), one_smul]

private noncomputable def fixedPartitionEmbed {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) (z : ∀ j, Fin (c j) → Y) :
    ι → FiniteSample Y :=
  fun j => fixedSizeEmbed (c j) (z j)

private lemma measurable_fixedPartitionEmbed {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) : Measurable (fixedPartitionEmbed (Y := Y) c) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_fixedSizeEmbed (c j)).comp (measurable_pi_apply j)

private def partitionCountFiber {Y : Type*} [MeasurableSpace Y] (c : ι → ℕ) :
    Set (ι → FiniteSample Y) :=
  {q | ∀ j, (q j).count = c j}

private lemma measurableSet_partitionCountFiber {Y : Type*} [MeasurableSpace Y]
    (c : ι → ℕ) : MeasurableSet (partitionCountFiber (Y := Y) c) := by
  rw [show partitionCountFiber (Y := Y) c =
      ⋂ j : ι, (fun q : ι → FiniteSample Y => (q j).count) ⁻¹' {c j} by
    ext q
    simp [partitionCountFiber]]
  exact MeasurableSet.iInter fun j =>
    (measurable_finiteSample_count.comp (measurable_pi_apply j))
      (measurableSet_singleton (c j))

private def wordEvent (p : FiniteMeasurablePartition X ι) {n : ℕ}
    (w : Fin n → ι) : Set (Fin n → X × ℝ) :=
  Set.univ.pi fun k => p.cellSet (w k) ×ˢ (Set.univ : Set ℝ)

private lemma measurableSet_wordEvent (p : FiniteMeasurablePartition X ι)
    {n : ℕ} (w : Fin n → ι) : MeasurableSet (wordEvent p w) := by
  exact MeasurableSet.univ_pi fun k =>
    (p.measurableSet_cellSet (w k)).prod MeasurableSet.univ

private lemma mem_wordEvent_iff (p : FiniteMeasurablePartition X ι)
    {n : ℕ} (w : Fin n → ι) (z : Fin n → X × ℝ) :
    z ∈ wordEvent p w ↔ ∀ k, p.cell (z k).1 = w k := by
  simp [wordEvent, cellSet]

private lemma cellIndices_fixedSizeEmbed_eq_wordIndices
    (p : FiniteMeasurablePartition X ι) {n : ℕ} (w : Fin n → ι)
    (z : Fin n → X × ℝ) (hz : z ∈ wordEvent p w) (j : ι) :
    p.cellIndices j (fixedSizeEmbed n z) = wordIndices w j := by
  classical
  ext k
  have hk := (mem_wordEvent_iff p w z).1 hz k
  unfold cellIndices wordIndices
  simp only [fixedSizeEmbed, FiniteSample.points]
  constructor
  · intro h
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hk]
    exact (Finset.mem_filter.1 h).2
  · intro h
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hk]
    exact (Finset.mem_filter.1 h).2

private noncomputable def restrictFinset {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (t : Finset (Fin n)) (z : Fin n → Y) : FiniteSample Y :=
  ⟨t.card, fun k => z (t.orderIsoOfFin rfl k)⟩

private lemma restrictFinset_congr {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (s t : Finset (Fin n)) (h : s = t) (z : Fin n → Y) :
    restrictFinset s z = restrictFinset t z := by
  subst t
  rfl

private lemma restrictPartition_fixedSizeEmbed_of_mem_wordEvent
    (p : FiniteMeasurablePartition X ι) {n : ℕ} (w : Fin n → ι)
    (z : Fin n → X × ℝ) (hz : z ∈ wordEvent p w) :
    p.restrictPartition (fixedSizeEmbed n z) =
      fixedPartitionEmbed (wordHistogram w) (gatherWord w z) := by
  classical
  funext j
  rw [restrictPartition, restrictCell]
  have hleft :
      (⟨(p.cellIndices j (fixedSizeEmbed n z)).card, fun k =>
        (fixedSizeEmbed n z).points
          ((p.cellIndices j (fixedSizeEmbed n z)).orderIsoOfFin rfl k)⟩ :
          FiniteSample (X × ℝ)) =
        restrictFinset (p.cellIndices j (fixedSizeEmbed n z)) z := rfl
  rw [hleft]
  have hright :
      fixedPartitionEmbed (wordHistogram w) (gatherWord w z) j =
        restrictFinset (wordIndices w j) z := by
    unfold fixedPartitionEmbed fixedSizeEmbed restrictFinset
    rw [Sigma.ext_iff]
    constructor
    · change wordHistogram w j = (wordIndices w j).card
      exact (wordIndices_card w j).symm
    · rw [Fin.heq_fun_iff (wordIndices_card w j).symm]
      intro k
      change gatherWord w z j k =
        z ((wordIndices w j).orderIsoOfFin (wordIndices_card w j).symm k)
      rw [gatherWord_apply, wordUnshuffleEquiv_apply]
  rw [hright]
  exact restrictFinset_congr _ _
    (cellIndices_fixedSizeEmbed_eq_wordIndices p w z hz j) z

private lemma map_fixed_word
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    {n : ℕ} (w : Fin n → ι) :
    Measure.map (p.restrictPartition ∘ fixedSizeEmbed n)
        ((Measure.pi fun _ : Fin n => P.prod R).restrict (wordEvent p w)) =
      (∏ k : Fin n, (p.cellMass P (w k) : ℝ≥0∞)) •
        Measure.map (fixedPartitionEmbed (wordHistogram w))
          (Measure.pi fun j : ι =>
            Measure.pi fun _ : Fin (wordHistogram w j) =>
              (p.cellObservationLaw P j).prod R) := by
  let Q : ι → Measure (X × ℝ) := fun j => (p.cellObservationLaw P j).prod R
  letI (k : Fin n) : IsFiniteMeasure
      ((p.cellMass P (w k) : ℝ≥0∞) • Q (w k)) :=
    ⟨by
      rw [Measure.smul_apply, measure_univ]
      exact ENNReal.coe_lt_top⟩
  letI (k : Fin n) : SigmaFinite
      ((p.cellMass P (w k) : ℝ≥0∞) • Q (w k)) :=
    IsFiniteMeasure.toSigmaFinite _
  have hrest :
      (Measure.pi fun _ : Fin n => P.prod R).restrict (wordEvent p w) =
        (∏ k : Fin n, (p.cellMass P (w k) : ℝ≥0∞)) •
          Measure.pi (fun k : Fin n => Q (w k)) := by
    rw [wordEvent, Measure.restrict_pi_pi]
    simp_rw [restrict_prod_cellSet p P R]
    exact pi_smul
      (fun k : Fin n => (p.cellMass P (w k) : ℝ≥0∞))
      (fun k : Fin n => Q (w k))
  have hmaps :
      Measure.map (p.restrictPartition ∘ fixedSizeEmbed n)
          ((Measure.pi fun _ : Fin n => P.prod R).restrict (wordEvent p w)) =
        Measure.map (fixedPartitionEmbed (wordHistogram w) ∘ gatherWord w)
          ((Measure.pi fun _ : Fin n => P.prod R).restrict (wordEvent p w)) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (measurableSet_wordEvent p w)] with z hz
    exact restrictPartition_fixedSizeEmbed_of_mem_wordEvent p w z hz
  rw [hmaps, hrest, Measure.map_smul,
    ← Measure.map_map (measurable_fixedPartitionEmbed (wordHistogram w))
      (measurable_gatherWord w), map_gatherWord_pi w Q]

private lemma restrictCell_count_eq_card_cellIndices
    (p : FiniteMeasurablePartition X ι) (s : FiniteSample (X × ℝ)) (j : ι) :
    (p.restrictCell j s).count = (p.cellIndices j s).card := by
  simp [restrictCell, FiniteSample.count]

private lemma sum_restrictCell_count
    (p : FiniteMeasurablePartition X ι) (s : FiniteSample (X × ℝ)) :
    ∑ j, (p.restrictCell j s).count = s.count := by
  classical
  simp_rw [restrictCell_count_eq_card_cellIndices]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin s.count)))
    (t := (Finset.univ : Finset ι))
    (f := fun k => p.cell (s.points k).1)
    (fun k _ => Finset.mem_univ (p.cell (s.points k).1))
  simpa [cellIndices] using h.symm

private lemma fixedSizeEmbed_preimage_partitionCountFiber
    (p : FiniteMeasurablePartition X ι) (n : ℕ) (c : ι → ℕ) :
    fixedSizeEmbed n ⁻¹'
        (p.restrictPartition ⁻¹' partitionCountFiber (Y := X × ℝ) c) =
      ⋃ w ∈ histogramWords n c, wordEvent p w := by
  classical
  ext z
  simp only [Set.mem_preimage, Set.mem_iUnion]
  constructor
  · intro hz
    let w : Fin n → ι := fun k => p.cell (z k).1
    refine ⟨w, ?_, ?_⟩
    · simp only [histogramWords, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      have hj := hz j
      rw [restrictPartition, restrictCell_count_eq_card_cellIndices] at hj
      exact hj
    · exact (mem_wordEvent_iff p w z).2 fun k => rfl
  · rintro ⟨w, hw, hz⟩
    intro j
    rw [restrictPartition, restrictCell_count_eq_card_cellIndices]
    have hhist := (Finset.mem_filter.1 hw).2 j
    rw [cellIndices_fixedSizeEmbed_eq_wordIndices p w z hz j]
    exact (wordIndices_card w j).trans hhist

private lemma pairwise_disjoint_wordEvent (p : FiniteMeasurablePartition X ι)
    (n : ℕ) : Pairwise (Function.onFun Disjoint
      (fun w : Fin n → ι => wordEvent p w)) := by
  classical
  intro w v hwv
  apply Set.disjoint_left.2
  intro z hzw hzv
  have hne : ∃ k, w k ≠ v k := by
    by_contra h
    apply hwv
    funext k
    exact not_ne_iff.mp (not_exists.mp h k)
  obtain ⟨k, hk⟩ := hne
  exact hk (((mem_wordEvent_iff p w z).1 hzw k).symm.trans
    ((mem_wordEvent_iff p v z).1 hzv k))

private lemma prod_cellMass_word_eq {n : ℕ} {c : ι → ℕ}
    (p : FiniteMeasurablePartition X ι) (P : Measure X)
    (w : Fin n → ι) (hw : w ∈ histogramWords n c) :
    ∏ k : Fin n, (p.cellMass P (w k) : ℝ≥0∞) =
      ∏ j : ι, (p.cellMass P j : ℝ≥0∞) ^ c j := by
  classical
  rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin n)) w
    (fun k => (p.cellMass P (w k) : ℝ≥0∞))]
  apply Finset.prod_congr rfl
  intro j _
  have hhist := (Finset.mem_filter.1 hw).2 j
  have hfactor : (∏ k ∈ (Finset.univ.filter fun k : Fin n => w k = j),
      (p.cellMass P (w k) : ℝ≥0∞)) =
      (p.cellMass P j : ℝ≥0∞) ^ wordHistogram w j := by
    rw [wordHistogram]
    calc
      (∏ k ∈ (Finset.univ.filter fun k : Fin n => w k = j),
          (p.cellMass P (w k) : ℝ≥0∞)) =
          ∏ _k ∈ (Finset.univ.filter fun k : Fin n => w k = j),
            (p.cellMass P j : ℝ≥0∞) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [(Finset.mem_filter.1 hk).2]
      _ = (p.cellMass P j : ℝ≥0∞) ^
          (Finset.univ.filter fun k : Fin n => w k = j).card := by
        rw [Finset.prod_const]
  rw [hfactor]
  rw [hhist]

private lemma map_fixed_histogram
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (n : ℕ) (c : ι → ℕ) :
    Measure.map (p.restrictPartition ∘ fixedSizeEmbed n)
        ((Measure.pi fun _ : Fin n => P.prod R).restrict
          (⋃ w ∈ histogramWords n c, wordEvent p w)) =
      (((histogramWords n c).card : ℝ≥0∞) *
          (∏ j : ι, (p.cellMass P j : ℝ≥0∞) ^ c j)) •
        Measure.map (fixedPartitionEmbed c)
          (Measure.pi fun j : ι =>
            Measure.pi fun _ : Fin (c j) =>
              (p.cellObservationLaw P j).prod R) := by
  let T := histogramWords n c
  let ν := Measure.map (fixedPartitionEmbed c)
    (Measure.pi fun j : ι =>
      Measure.pi fun _ : Fin (c j) => (p.cellObservationLaw P j).prod R)
  rw [Measure.restrict_biUnion_finset
    (fun w hw v hv hwv => pairwise_disjoint_wordEvent p n hwv)
    (fun w => measurableSet_wordEvent p w)]
  rw [Measure.map_sum
    ((p.measurable_restrictPartition.comp (measurable_fixedSizeEmbed n)).aemeasurable)]
  apply Measure.ext
  intro s hs
  rw [Measure.sum_apply _ hs, Measure.smul_apply, tsum_fintype]
  change (∑ w : ↥(histogramWords n c),
      Measure.map (p.restrictPartition ∘ fixedSizeEmbed n)
        ((Measure.pi fun _ : Fin n => P.prod R).restrict (wordEvent p w)) s) =
    (((histogramWords n c).card : ℝ≥0∞) *
      ∏ j : ι, (p.cellMass P j : ℝ≥0∞) ^ c j) * ν s
  have hterm : ∀ w ∈ histogramWords n c,
      Measure.map (p.restrictPartition ∘ fixedSizeEmbed n)
          ((Measure.pi fun _ : Fin n => P.prod R).restrict (wordEvent p w)) s =
        (∏ j : ι, (p.cellMass P j : ℝ≥0∞) ^ c j) * ν s := by
    intro w hw
    rw [map_fixed_word p P R w, Measure.smul_apply,
      prod_cellMass_word_eq p P w hw]
    have hc : wordHistogram w = c := by
      funext j
      exact (Finset.mem_filter.1 hw).2 j
    subst c
    rfl
  simp_rw [fun w : ↥(histogramWords n c) => hterm w w.property]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [ν, mul_assoc]

private lemma map_restrictPartition_restrict_partitionCountFiber
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (lam : ℝ≥0) (c : ι → ℕ) :
    (Measure.map p.restrictPartition
        (finiteMarkedPoissonSampleLaw P R lam)).restrict
          (partitionCountFiber (Y := X × ℝ) c) =
      ((poissonMeasure lam ({∑ j, c j} : Set ℕ) *
          ((histogramWords (∑ j, c j) c).card : ℝ≥0∞)) *
          (∏ j : ι, (p.cellMass P j : ℝ≥0∞) ^ c j)) •
        Measure.map (fixedPartitionEmbed c)
          (Measure.pi fun j : ι =>
            Measure.pi fun _ : Fin (c j) =>
              (p.cellObservationLaw P j).prod R) := by
  let N := ∑ j, c j
  let B := partitionCountFiber (Y := X × ℝ) c
  let A := p.restrictPartition ⁻¹' B
  have hA : MeasurableSet A :=
    (measurableSet_partitionCountFiber c).preimage p.measurable_restrictPartition
  have hsub : A ⊆ FiniteSample.count ⁻¹' ({N} : Set ℕ) := by
    intro s hs
    change s.count = N
    rw [← sum_restrictCell_count p s]
    apply Finset.sum_congr rfl
    intro j _
    exact hs j
  rw [Measure.restrict_map p.measurable_restrictPartition
    (measurableSet_partitionCountFiber c)]
  change Measure.map p.restrictPartition
    ((finiteMarkedPoissonSampleLaw P R lam).restrict A) = _
  rw [← Measure.restrict_restrict_of_subset hsub,
    finiteMarkedPoissonSampleLaw_restrict_count_eq,
    Measure.restrict_smul, Measure.map_smul]
  rw [Measure.restrict_map (measurable_fixedSizeEmbed N) hA]
  rw [Measure.map_map p.measurable_restrictPartition
    (measurable_fixedSizeEmbed N)]
  change poissonMeasure lam ({N} : Set ℕ) •
      Measure.map (p.restrictPartition ∘ fixedSizeEmbed N)
        ((Measure.pi fun _ : Fin N => P.prod R).restrict
          (fixedSizeEmbed N ⁻¹' A)) = _
  rw [show fixedSizeEmbed N ⁻¹' A =
      ⋃ w ∈ histogramWords N c, wordEvent p w by
    exact fixedSizeEmbed_preimage_partitionCountFiber p N c,
    map_fixed_histogram p P R N c]
  simp only [smul_smul]
  congr 1
  simp [N, mul_assoc]

private lemma pi_cellLaws_restrict_partitionCountFiber
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (lam : ℝ≥0) (c : ι → ℕ) :
    (Measure.pi fun j : ι =>
        finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
          (lam * p.cellMass P j)).restrict
        (partitionCountFiber (Y := X × ℝ) c) =
      (∏ j : ι,
          poissonMeasure (lam * p.cellMass P j) ({c j} : Set ℕ)) •
        Measure.map (fixedPartitionEmbed c)
          (Measure.pi fun j : ι =>
            Measure.pi fun _ : Fin (c j) =>
              (p.cellObservationLaw P j).prod R) := by
  have hB : partitionCountFiber (Y := X × ℝ) c =
      Set.univ.pi (fun j : ι =>
        FiniteSample.count ⁻¹' ({c j} : Set ℕ)) := by
    ext q
    simp [partitionCountFiber]
  letI (j : ι) : IsProbabilityMeasure
      (Measure.map (fixedSizeEmbed (c j))
        (Measure.pi fun _ : Fin (c j) =>
          (p.cellObservationLaw P j).prod R)) :=
    Measure.isProbabilityMeasure_map
      (measurable_fixedSizeEmbed (c j)).aemeasurable
  letI (j : ι) : IsFiniteMeasure
      (poissonMeasure (lam * p.cellMass P j) ({c j} : Set ℕ) •
        Measure.map (fixedSizeEmbed (c j))
          (Measure.pi fun _ : Fin (c j) =>
            (p.cellObservationLaw P j).prod R)) :=
    ⟨by
      rw [Measure.smul_apply, measure_univ]
      simpa using measure_lt_top
        (poissonMeasure (lam * p.cellMass P j)) ({c j} : Set ℕ)⟩
  letI (j : ι) : SigmaFinite
      (poissonMeasure (lam * p.cellMass P j) ({c j} : Set ℕ) •
        Measure.map (fixedSizeEmbed (c j))
          (Measure.pi fun _ : Fin (c j) =>
            (p.cellObservationLaw P j).prod R)) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [hB, Measure.restrict_pi_pi]
  simp_rw [finiteMarkedPoissonSampleLaw_restrict_count_eq]
  rw [pi_smul]
  congr 1
  symm
  exact Measure.pi_map_pi
    (fun j : ι => (measurable_fixedSizeEmbed (c j)).aemeasurable)

private lemma poisson_multinomial_coefficient
    (lam : ℝ≥0) (q : ι → ℝ≥0) (hq : ∑ j, q j = 1) (c : ι → ℕ) :
    (poissonMeasure lam ({∑ j, c j} : Set ℕ) *
        ((histogramWords (∑ j, c j) c).card : ℝ≥0∞)) *
        (∏ j : ι, (q j : ℝ≥0∞) ^ c j) =
      ∏ j : ι, poissonMeasure (lam * q j) ({c j} : Set ℕ) := by
  classical
  have hcard : (histogramWords (∑ j, c j) c).card =
      Nat.multinomial Finset.univ c :=
    histogramWords_card (∑ j, c j) c rfl
  simp_rw [poissonMeasure_singleton]
  rw [hcard]
  change (ENNReal.ofReal (poissonPMFReal lam (∑ j, c j)) *
      (Nat.multinomial Finset.univ c : ℝ≥0∞)) *
      ∏ j : ι, (q j : ℝ≥0∞) ^ c j =
    ∏ j : ι, ENNReal.ofReal (poissonPMFReal (lam * q j) (c j))
  have hreal :
      poissonPMFReal lam (∑ j, c j) *
          (Nat.multinomial Finset.univ c : ℝ) *
          ∏ j : ι, (q j : ℝ) ^ c j =
        ∏ j : ι, poissonPMFReal (lam * q j) (c j) := by
    unfold poissonPMFReal
    push_cast
    simp_rw [mul_pow]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum Finset.univ c (lam : ℝ),
      ← Real.exp_sum]
    have hqR : ∑ j : ι, (q j : ℝ) = 1 := by
      exact_mod_cast hq
    have hexp : ∑ j : ι, -((lam : ℝ) * (q j : ℝ)) = -(lam : ℝ) := by
      rw [show (fun j : ι => -((lam : ℝ) * (q j : ℝ))) =
          fun j => -(lam : ℝ) * (q j : ℝ) by
        funext j
        ring]
      rw [← Finset.mul_sum, hqR, mul_one]
    rw [hexp]
    have hmulti := Nat.multinomial_spec Finset.univ c
    have hmultiR := congrArg (fun n : ℕ => (n : ℝ)) hmulti
    push_cast at hmultiR
    field_simp
    rw [← hmultiR]
    ring
  have hof := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun j _ => poissonPMFReal_nonneg)] at hof
  have hp : 0 ≤ poissonPMFReal lam (∑ j, c j) := poissonPMFReal_nonneg
  have hqpow : ∀ j : ι, 0 ≤ (q j : ℝ) ^ c j := fun j => by positivity
  rw [ENNReal.ofReal_mul (mul_nonneg hp (Nat.cast_nonneg _)),
    ENNReal.ofReal_mul hp, ENNReal.ofReal_natCast,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => hqpow j)] at hof
  simp_rw [ENNReal.ofReal_pow (NNReal.coe_nonneg _)] at hof
  simp only [ENNReal.ofReal_coe_nnreal] at hof
  exact hof

/-- Restricting the marked Poisson sample to all cells gives exactly the
product of independent cell experiments, with cell intensity equal to the
global intensity times the cell probability. -/
lemma map_restrictPartition_finiteMarkedPoissonSampleLaw
    [StandardBorelSpace X]
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure.map p.restrictPartition (finiteMarkedPoissonSampleLaw P R lam) =
      Measure.pi (fun j : ι =>
        finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
          (lam * p.cellMass P j)) := by
  /-
  Proof route for the filler: disintegrate both sides over the complete cell-count
  vector `c : ι → ℕ`.  On a fixed global count, partition the i.i.d. tuple
  by its classifier word; each word with histogram `c` pushes forward to the
  same product of the fixed-size within-cell laws, up to coordinate
  reindexing.  Count the words in that histogram fibre and combine its
  multinomial factor with the scalar Poisson mass.  The resulting coefficient
  is the product of the cell Poisson masses.  Treat zero-mass cells before
  cancelling cell masses.  `Measure.pi_map_piCongrLeft` and
  `measurePreserving_piCongrLeft` are the intended permutation tools.
  -/
  let μ := Measure.map p.restrictPartition
    (finiteMarkedPoissonSampleLaw P R lam)
  let ν := Measure.pi (fun j : ι =>
    finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
      (lam * p.cellMass P j))
  have hrest (c : ι → ℕ) :
      μ.restrict (partitionCountFiber (Y := X × ℝ) c) =
        ν.restrict (partitionCountFiber (Y := X × ℝ) c) := by
    rw [show μ = Measure.map p.restrictPartition
        (finiteMarkedPoissonSampleLaw P R lam) by rfl,
      map_restrictPartition_restrict_partitionCountFiber p P R lam c]
    rw [show ν = Measure.pi (fun j : ι =>
        finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
          (lam * p.cellMass P j)) by rfl,
      pi_cellLaws_restrict_partitionCountFiber p P R lam c]
    rw [poisson_multinomial_coefficient lam (p.cellMass P)
      (p.sum_cellMass P) c]
  have hdis : Pairwise (Function.onFun Disjoint
      (fun c : ι → ℕ => partitionCountFiber (Y := X × ℝ) c)) := by
    intro c d hcd
    apply Set.disjoint_left.2
    intro q hqc hqd
    apply hcd
    funext j
    exact (hqc j).symm.trans (hqd j)
  have hcover : ⋃ c : ι → ℕ, partitionCountFiber (Y := X × ℝ) c = Set.univ := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨fun j => (q j).count, fun _ => rfl⟩
  change μ = ν
  calc
    μ = μ.restrict Set.univ := by rw [Measure.restrict_univ]
    _ = μ.restrict (⋃ c : ι → ℕ,
        partitionCountFiber (Y := X × ℝ) c) := by rw [hcover]
    _ = Measure.sum (fun c : ι → ℕ =>
        μ.restrict (partitionCountFiber (Y := X × ℝ) c)) := by
      exact Measure.restrict_iUnion hdis measurableSet_partitionCountFiber
    _ = Measure.sum (fun c : ι → ℕ =>
        ν.restrict (partitionCountFiber (Y := X × ℝ) c)) := by
      congr 1
      funext c
      exact hrest c
    _ = ν.restrict (⋃ c : ι → ℕ,
        partitionCountFiber (Y := X × ℝ) c) := by
      exact (Measure.restrict_iUnion hdis measurableSet_partitionCountFiber).symm
    _ = ν.restrict Set.univ := by rw [hcover]
    _ = ν := Measure.restrict_univ

end FiniteMeasurablePartition

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
