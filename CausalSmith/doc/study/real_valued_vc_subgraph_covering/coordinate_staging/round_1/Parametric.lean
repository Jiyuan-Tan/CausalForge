import Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Algebra
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Parametric and VC-indicator covering interfaces

This module supplies the bounded finite-dimensional linear-parameter class and
the composition of a polynomial-entropy real class with a measurable finite-VC
family of indicators.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory
open Causalean.Stat.Concentration
open scoped BigOperators

universe u v w

variable {𝒳 : Type u} [MeasurableSpace 𝒳]

/-- The box of coefficient vectors whose coordinates have absolute value at
most `B`. -/
def CoeffBox (K : Type w) (B : ℝ) :=
  {θ : K → ℝ // ∀ k, |θ k| ≤ B}

/-- Evaluation of a finite-dimensional linear parameter against a fixed
feature family. -/
def linearParameterClass {K : Type w} [Fintype K]
    (φ : K → 𝒳 → ℝ) (B : ℝ) (θ : CoeffBox K B) (x : 𝒳) : ℝ :=
  ∑ k, θ.1 k * φ k x

/-- A finite-dimensional linear class has pseudo-dimension bounded by the
number of coordinates (the stated `+1` leaves room for the affine threshold). -/
theorem linearParameterClass_hasPseudoDimAtMost
    {K : Type w} [Fintype K]
    (φ : K → 𝒳 → ℝ) (B : ℝ) :
    HasPseudoDimAtMost (linearParameterClass φ B) (Fintype.card K + 1) := by
  classical
  intro n T
  unfold Finset.vcDim
  refine Finset.sup_le fun s hs => ?_
  rw [Finset.mem_shatterer] at hs
  by_contra hcard
  have hcard_lt : Fintype.card K + 1 < s.card := by omega
  let v : {i // i ∈ s} → Option K → ℝ := fun i q =>
    match q with
    | none => -(T i.1).2
    | some k => φ k (T i.1).1
  have hvdep : ¬ LinearIndependent ℝ v := by
    intro hv
    have hle := hv.fintype_card_le_finrank
    rw [Module.finrank_pi, Fintype.card_option, Fintype.card_coe] at hle
    omega
  obtain ⟨a, ha0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hvdep
  let g : {i // i ∈ s} → ℝ :=
    if 0 < a i0 then a else fun i => -a i
  have hg0 : ∑ i, g i • v i = 0 := by
    dsimp [g]
    split_ifs
    · exact ha0
    · calc
        ∑ i, (-a i) • v i = ∑ i, -(a i • v i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact neg_smul (a i) (v i)
        _ = -(∑ i, a i • v i) := by rw [Finset.sum_neg_distrib]
        _ = 0 := by rw [ha0, neg_zero]
  have hgi0 : 0 < g i0 := by
    dsimp [g]
    split_ifs with h
    · exact h
    · dsimp
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hi0)
  let g0 : Fin n → ℝ := fun i => if hi : i ∈ s then g ⟨i, hi⟩ else 0
  let t : Finset (Fin n) := s.filter fun i => 0 < g0 i
  have hts : t ⊆ s := Finset.filter_subset _ _
  obtain ⟨u, hu_growth, hsu⟩ := hs hts
  obtain ⟨θ, hθ⟩ :=
    (mem_growthFamily_iff.mp hu_growth)
  have hlabel (i : {i // i ∈ s}) :
      subgraphClassifier (linearParameterClass φ B) θ (T i.1) = true ↔ 0 < g i := by
    rw [← restrictionPattern_mem_iff (p := subgraphClassifier
      (linearParameterClass φ B) θ) (S := T) (j := i.1), hθ]
    have hi_mem : i.1 ∈ u ↔ i.1 ∈ t := by
      constructor
      · intro hiu
        have : i.1 ∈ s ∩ u := Finset.mem_inter.mpr ⟨i.2, hiu⟩
        rwa [hsu] at this
      · intro hit
        have : i.1 ∈ s ∩ u := by rwa [hsu]
        exact (Finset.mem_inter.mp this).2
    rw [hi_mem]
    simp only [t, Finset.mem_filter, i.2, true_and]
    simp [g0, i.2]
  let e : {i // i ∈ s} → ℝ := fun i =>
    linearParameterClass φ B θ (T i.1).1 - (T i.1).2
  have he_pos (i : {i // i ∈ s}) (hi : 0 < g i) : 0 < e i := by
    have hlt : (T i.1).2 < linearParameterClass φ B θ (T i.1).1 := by
      simpa [subgraphClassifier] using (hlabel i).2 hi
    dsimp [e]
    linarith
  have he_nonpos (i : {i // i ∈ s}) (hi : ¬ 0 < g i) : e i ≤ 0 := by
    have hnot : ¬ (T i.1).2 < linearParameterClass φ B θ (T i.1).1 := by
      simpa [subgraphClassifier] using (hlabel i).not.mpr hi
    dsimp [e]
    linarith
  have hprod_nonneg (i : {i // i ∈ s}) : 0 ≤ g i * e i := by
    by_cases hi : 0 < g i
    · exact (mul_pos hi (he_pos i hi)).le
    · have hgle : g i ≤ 0 := le_of_not_gt hi
      exact mul_nonneg_of_nonpos_of_nonpos hgle (he_nonpos i hi)
  have hprod_pos : 0 < g i0 * e i0 := mul_pos hgi0 (he_pos i0 hgi0)
  have hsum_pos : 0 < ∑ i, g i * e i := by
    exact Finset.sum_pos' (fun i _ => hprod_nonneg i)
      ⟨i0, Finset.mem_univ _, hprod_pos⟩
  have hsum_zero : ∑ i, g i * e i = 0 := by
    have hcoord (q : Option K) : ∑ i, g i * v i q = 0 := by
      have := congrFun hg0 q
      simpa [Pi.smul_apply, smul_eq_mul] using this
    rw [show (∑ i, g i * e i) =
        ∑ q : Option K, (match q with | none => 1 | some k => θ.1 k) *
          ∑ i, g i * v i q by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      change g i * ((∑ k, θ.1 k * φ k (T i.1).1) - (T i.1).2) = _
      rw [mul_sub, Finset.mul_sum]
      simp only [Fintype.sum_option, v]
      ring]
    simp only [hcoord, mul_zero, Finset.sum_const_zero]
  linarith

/-- A bounded coefficient box acting on finitely many bounded measurable
features has uniform polynomial `L²` entropy. -/
theorem linearParameterClass_hasPolynomialL2Cover
    {K : Type w} [Fintype K] [Nonempty K]
    (φ : K → 𝒳 → ℝ) {B M : ℝ}
    (hB : 0 < B) (hM : 0 < M)
    (hmeas : ∀ k, Measurable (φ k))
    (hφ : ∀ k x, |φ k x| ≤ M) :
    HasPolynomialL2Cover (linearParameterClass φ B)
      ((Fintype.card K : ℝ) * B * M) := by
  letI : Nonempty (CoeffBox K B) :=
    ⟨⟨fun _ => 0, fun _ => by simpa using hB.le⟩⟩
  apply (linearParameterClass_hasPseudoDimAtMost φ B).hasPolynomialL2Cover
  · intro θ
    exact Finset.measurable_sum Finset.univ fun k _ =>
      measurable_const.mul (hmeas k)
  · have hcard : (0 : ℝ) < Fintype.card K := by
      exact_mod_cast Fintype.card_pos
    positivity
  · intro θ x
    calc
      |linearParameterClass φ B θ x| ≤ ∑ k, |θ.1 k * φ k x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |θ.1 k| * |φ k x| := by simp only [abs_mul]
      _ ≤ ∑ _k : K, B * M := by
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul (θ.2 k) (hφ k x) (abs_nonneg _) hB.le
      _ = (Fintype.card K : ℝ) * B * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring_nf

/-- A Boolean family has VC dimension at most `d` when every finite sample
growth family has VC dimension at most `d`. -/
def HasVCAtMost {κ : Type w} (π : κ → 𝒳 → Bool) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (S : Fin n → 𝒳), (growthFamily π S).vcDim ≤ d

private theorem indicatorClass_hasPseudoDimAtMost
    {κ : Type w} (π : κ → 𝒳 → Bool) (d : ℕ)
    (hπvc : HasVCAtMost π d) :
    HasPseudoDimAtMost (fun j x => if π j x then 1 else 0) d := by
  classical
  intro n T
  unfold Finset.vcDim
  refine Finset.sup_le fun s hs => ?_
  rw [Finset.mem_shatterer] at hs
  obtain ⟨uTop, huTop, hTop⟩ := hs (Finset.Subset.rfl)
  obtain ⟨jTop, hjTop⟩ := mem_growthFamily_iff.mp huTop
  obtain ⟨uBot, huBot, hBot⟩ := hs (Finset.empty_subset s)
  obtain ⟨jBot, hjBot⟩ := mem_growthFamily_iff.mp huBot
  have hupper (i : Fin n) (hi : i ∈ s) : (T i).2 < 1 := by
    have hiTop : i ∈ uTop := by
      have : i ∈ s ∩ uTop := by rwa [hTop]
      exact (Finset.mem_inter.mp this).2
    have htrue :
        subgraphClassifier (fun j x => if π j x then 1 else 0) jTop (T i) = true := by
      rw [← restrictionPattern_mem_iff (p := subgraphClassifier
        (fun j x => if π j x then 1 else 0) jTop) (S := T) (j := i), hjTop]
      exact hiTop
    have hlt : (T i).2 < if π jTop (T i).1 then 1 else 0 := by
      simpa [subgraphClassifier] using htrue
    cases hπi : π jTop (T i).1 <;> simp [hπi] at hlt ⊢ <;> linarith
  have hlower (i : Fin n) (hi : i ∈ s) : 0 ≤ (T i).2 := by
    have hiBot : i ∉ uBot := by
      intro hiu
      have : i ∈ s ∩ uBot := Finset.mem_inter.mpr ⟨hi, hiu⟩
      rw [hBot] at this
      exact Finset.notMem_empty i this
    have hfalse :
        subgraphClassifier (fun j x => if π j x then 1 else 0) jBot (T i) ≠ true := by
      intro htrue
      apply hiBot
      rw [← hjBot, restrictionPattern_mem_iff]
      exact htrue
    have hnot : ¬ (T i).2 < if π jBot (T i).1 then 1 else 0 := by
      simpa [subgraphClassifier] using hfalse
    cases hπi : π jBot (T i).1 <;> simp [hπi] at hnot ⊢ <;> linarith
  have hmiddle (j : κ) (i : Fin n) (hi : i ∈ s) :
      subgraphClassifier (fun j x => if π j x then 1 else 0) j (T i) = true ↔
        π j (T i).1 = true := by
    cases hπi : π j (T i).1
    · simp [subgraphClassifier, hπi, hlower i hi]
    · simp [subgraphClassifier, hπi, hupper i hi]
  have hshπ : (growthFamily π (fun i => (T i).1)).Shatters s := by
    intro t ht
    obtain ⟨u, hu, hsu⟩ := hs ht
    obtain ⟨j, hj⟩ := mem_growthFamily_iff.mp hu
    refine ⟨restrictionPattern (π j) (fun i => (T i).1), ?_, ?_⟩
    · rw [mem_growthFamily_iff]
      exact ⟨j, rfl⟩
    · ext i
      by_cases hi : i ∈ s
      · have hpiu :
            i ∈ restrictionPattern (π j) (fun i => (T i).1) ↔ i ∈ u := by
          rw [restrictionPattern_mem_iff, ← hmiddle j i hi,
            ← restrictionPattern_mem_iff, hj]
        have hut : i ∈ u ↔ i ∈ t := by
          constructor
          · intro hiu
            have : i ∈ s ∩ u := Finset.mem_inter.mpr ⟨hi, hiu⟩
            rwa [hsu] at this
          · intro hit
            have : i ∈ s ∩ u := by rwa [hsu]
            exact (Finset.mem_inter.mp this).2
        simp only [Finset.mem_inter, hi, true_and]
        exact hpiu.trans hut
      · simp only [Finset.mem_inter, hi, false_and]
        exact (iff_false_intro fun hit => hi (ht hit)).symm
  exact hshπ.card_le_vcDim.trans (hπvc n fun i => (T i).1)

/-- Multiplying a polynomial-entropy real class by a measurable finite-VC
family of indicators preserves uniform polynomial `L²` entropy. -/
theorem HasPolynomialL2Cover.mulIndicator
    {ι : Type v} {κ : Type w} {F : ι → 𝒳 → ℝ} {π : κ → 𝒳 → Bool}
    {U : ℝ} {d : ℕ}
    (hF : HasPolynomialL2Cover F U)
    (hπmeas : ∀ j, MeasurableSet {x | π j x = true})
    (hπvc : HasVCAtMost π d) :
    HasPolynomialL2Cover
      (fun p : ι × κ => fun x => F p.1 x * if π p.2 x then 1 else 0) U := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · letI : IsEmpty κ := hκ
    refine ⟨hF.envelope_pos, ?_, ?_, ?_⟩
    · intro p
      exact isEmptyElim p.2
    · intro p
      exact isEmptyElim p.2
    · refine ⟨1, 0, le_rfl, ?_⟩
      intro Q hQ ε hε hε1
      classical
      refine ⟨∅, by simp, ?_⟩
      intro p
      exact isEmptyElim p.2
  · letI : Nonempty κ := hκ
    have hindicator : HasPolynomialL2Cover
        (fun j x => if π j x then 1 else 0) 1 :=
      (indicatorClass_hasPseudoDimAtMost π d hπvc).hasPolynomialL2Cover
        (fun j => Measurable.ite (hπmeas j) measurable_const measurable_const)
        (by norm_num) (by
          intro j x
          cases π j x <;> simp)
    simpa using hF.mul hindicator

end Causalean.Stat.Concentration
