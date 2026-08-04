import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearClass
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Mathlib.Algebra.Order.Chebyshev

/-!
# Canonical local-linear weights and the estimator error expansion

Defines the canonical local-linear weight scheme, the complete-block index and
unit sets, and the per-unit estimation error, then develops the error
expansion, unbiasedness, and the global second-moment identity for the SNIPE
score together with the weight-energy and centred-moment lemmas.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- When the block size divides the population size, every unit is active. -/
lemma activeCount_eq_of_dvd
    (n d : ℕ) (hdiv : d ∣ n) :
    activeCount n d = n := by
  simp only [activeCount, blockCount]
  exact Nat.div_mul_cancel hdiv

/-- In a complete block design, every unit’s neighborhood contains exactly the block size number of units. -/
lemma blockGraph_nbhd_card
    (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n) (i : Fin n) :
    (nbhd (blockGraph n d) i).card = d := by
  have hactive : activeCount n d = n := activeCount_eq_of_dvd n d hdiv
  have hq : i.val / d < n / d := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    simpa [Nat.div_mul_cancel hdiv] using i.isLt
  rw [show nbhd (blockGraph n d) i =
      Finset.univ.filter (fun j : Fin n => j.val / d = i.val / d) by
    ext j
    simp [nbhd, blockGraph, hactive, i.isLt, j.isLt]]
  have hcard :
      (Finset.univ : Finset (Fin d)).card =
        (Finset.univ.filter
          (fun j : Fin n => j.val / d = i.val / d)).card := by
    apply Finset.card_bij
        (fun k _ => (⟨(i.val / d) * d + k.val, by
          calc
            (i.val / d) * d + k.val <
                (i.val / d) * d + d := Nat.add_lt_add_left k.isLt _
            _ = (i.val / d + 1) * d := by
              rw [Nat.add_mul]
              omega
            _ ≤ (n / d) * d := Nat.mul_le_mul_right d hq
            _ = n := Nat.div_mul_cancel hdiv⟩ : Fin n))
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Nat.add_comm, Nat.mul_comm (i.val / d) d,
        Nat.add_mul_div_left k.val (i.val / d) (by omega),
        Nat.div_eq_of_lt k.isLt]
      omega
    · intro k₁ hk₁ k₂ hk₂ heq
      have hv := Fin.ext_iff.mp heq
      exact Fin.ext (Nat.add_left_cancel hv)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hmod : j.val % d < d := Nat.mod_lt _ (by omega)
      refine ⟨⟨j.val % d, hmod⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only
      rw [← hj]
      simpa [Nat.mul_comm] using Nat.div_add_mod j.val d
  simpa using hcard.symm

/-- Constructs canonical local-linear weights for the complete block graph, satisfying the required locality, mean-zero, and moment conditions. -/
noncomputable def canonicalLocLinWeights
    (n d β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n) :
    LocLinWeights (blockGraph n d) d β p (le_of_lt hp0) (le_of_lt hp1) := by
  classical
  have hm : 0 < blockCount n d := by
    rcases hdiv with ⟨m, rfl⟩
    simp only [blockCount]
    have hm : 0 < m := by
      by_contra hz
      have : m = 0 := Nat.eq_zero_of_not_pos hz
      subst m
      simp at hn
    have hdm : d ≤ d * m := by
      simpa using Nat.mul_le_mul_left d hm
    have hdpos : 0 < d := by omega
    simp [hdpos, hdm, hm]
  let bidx : Fin n → Fin (Fintype.card (Fin n) / d) := fun i =>
    ⟨i.val / d, by
      simp only [Fintype.card_fin]
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [Nat.div_mul_cancel hdiv] using i.isLt⟩
  refine
    { weight := fun i z =>
        snipeScore (fun j i => decide (blockGraph n d j i)) β p i z
      blockIndex := bidx
      complete_block := ?_
      local_dep := ?_
      mean_zero := ?_
      moment_one := ?_ }
  · intro i j
    simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and,
      blockGraph, bidx, Fin.ext_iff]
    have hactive : activeCount n d = n := activeCount_eq_of_dvd n d hdiv
    simp [hactive, i.isLt, j.isLt]
  · intro i z z' hzz
    simp only [snipeScore]
    apply Finset.sum_congr rfl
    intro r hr
    apply congrArg
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.prod_congr rfl
    intro j hj
    have hjN : j ∈ nbhd (blockGraph n d) i := by
      have hSB :
          S ⊆ nbhdB (fun j i => decide (blockGraph n d j i)) i :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have := hSB hj
      simpa [nbhdB, nbhd] using this
    rw [hzz j hjN]
  · intro i
    exact snipeScore_mean_zero
      (fun j i => decide (blockGraph n d j i)) β p
      hp0 hp1 i
  · intro i S hS hSN hScard
    apply snipeScore_raw_moment
      (fun j i => decide (blockGraph n d j i)) β p
      hp0 hp1 i S hS
    · simpa [nbhdB, nbhd] using hSN
    · rw [show nbhdB (fun j i => decide (blockGraph n d j i)) i =
          nbhd (blockGraph n d) i by
        ext j
        simp [nbhdB, nbhd]]
      simpa [blockGraph_nbhd_card n d hd hdiv i] using hScard

/-- Defines the units in a block as the active population units with the specified block index. -/
noncomputable def completeBlockUnits
    (n d : ℕ) (b : Fin (blockCount n d)) : Finset (Fin n) :=
  Finset.univ.filter
    (fun i => i.val < activeCount n d ∧ i.val / d = b.val)

/-- Returns the first population unit in the specified complete block. -/
def blockFirstUnit
    (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (b : Fin (blockCount n d)) : Fin n :=
  ⟨b.val * d, by
    have hb : b.val < n / d := by simpa [blockCount] using b.isLt
    calc
      b.val * d < (n / d) * d := Nat.mul_lt_mul_of_pos_right hb (by omega)
      _ = n := Nat.div_mul_cancel hdiv⟩

/-- Assigns each population unit to its complete-block index. -/
def completeBlockIndex
    (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n) (i : Fin n) :
    Fin (blockCount n d) :=
  ⟨i.val / d, by
    simp only [blockCount]
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    simpa [Nat.div_mul_cancel hdiv] using i.isLt⟩

/-- Every population unit belongs to the complete block selected by its block index. -/
lemma mem_completeBlockIndex
    (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n) (i : Fin n) :
    i ∈ completeBlockUnits n d (completeBlockIndex n d hd hdiv i) := by
  have hactive : activeCount n d = n := activeCount_eq_of_dvd n d hdiv
  simp [completeBlockUnits, completeBlockIndex, hactive, i.isLt]

/-- Defines a unit-and-subset contribution to estimation error as the weighted observed monomial minus its target. -/
noncomputable def locLinUnitError
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : V → V → Prop} {d β : ℕ} {p : ℝ}
    {hp0 : 0 ≤ p} {hp1 : p ≤ 1}
    (w : LocLinWeights G d β p hp0 hp1)
    (i : V) (S : Finset V) (z : V → Bool) : ℝ :=
  w.weight i z * (∏ j ∈ S, if z j then (1 : ℝ) else 0) -
    if S.Nonempty then 1 else 0

/-- The local-linear estimator’s error equals the population average of coefficient-weighted unit errors over all local subsets. -/
lemma locLinEstimator_error_expansion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (M : LocLinSchedClass G d β B) (z : V → Bool) :
    locLinEstimator G d β p hp0 hp1 w z
          (obsOutcome G M.coef z) -
        tte G M.coef =
      (Fintype.card V : ℝ)⁻¹ *
        ∑ i : V, ∑ S ∈ (nbhd G i).powerset,
          M.coef i S * locLinUnitError w i S z := by
  classical
  unfold locLinEstimator obsOutcome tte potentialOutcome locLinUnitError
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  rw [show
      (∑ S ∈ (nbhd G i).powerset,
        w.weight i z *
          (M.coef i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0)) =
      ∑ S ∈ (nbhd G i).powerset,
        M.coef i S *
          (w.weight i z * ∏ j ∈ S, if z j then (1 : ℝ) else 0) by
    apply Finset.sum_congr rfl
    intro S hS
    ring]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hSne : S.Nonempty
  · have htrue :
        (∏ j ∈ S, if (fun _ : V => true) j then (1 : ℝ) else 0) = 1 := by
      simp
    have hfalse :
        (∏ j ∈ S, if (fun _ : V => false) j then (1 : ℝ) else 0) = 0 := by
      obtain ⟨j, hj⟩ := hSne
      exact Finset.prod_eq_zero hj (by simp)
    rw [htrue, hfalse, if_pos hSne]
    ring
  · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    subst S
    simp

/-- Under Bernoulli assignment, valid local-linear weights yield an unbiased estimator of the total treatment effect. -/
lemma locLinEstimator_unbiased
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (M : LocLinSchedClass G d β B) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
        (fun _ => hp1)).Unbiased
      (fun z =>
        locLinEstimator G d β p hp0 hp1 w z
          (obsOutcome G M.coef z))
      (tte G M.coef) := by
  classical
  unfold FiniteDesign.Unbiased
  rw [show (fun z =>
      locLinEstimator G d β p hp0 hp1 w z
          (obsOutcome G M.coef z)) =
      fun z => tte G M.coef +
        (Fintype.card V : ℝ)⁻¹ *
          ∑ i : V, ∑ S ∈ (nbhd G i).powerset,
            M.coef i S * locLinUnitError w i S z by
    funext z
    rw [← locLinEstimator_error_expansion G d β B p hp0 hp1 w M z]
    ring]
  rw [FiniteDesign.E_add, FiniteDesign.E_const,
    FiniteDesign.E_const_mul, FiniteDesign.E_sum]
  rw [show
      (∑ i : V,
        (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
          (fun _ => hp1)).E
          (fun z => ∑ S ∈ (nbhd G i).powerset,
            M.coef i S * locLinUnitError w i S z)) = 0 by
    apply Finset.sum_eq_zero
    intro i hi
    rw [FiniteDesign.E_sum]
    apply Finset.sum_eq_zero
    intro S hS
    rw [FiniteDesign.E_const_mul]
    by_cases hcard : S.card ≤ effBeta β d
    · rw [show
          (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
            (fun _ => hp1)).E (locLinUnitError w i S) = 0 by
        unfold locLinUnitError
        rw [FiniteDesign.E_sub, FiniteDesign.E_const]
        by_cases hSne : S.Nonempty
        · rw [if_pos hSne,
            w.moment_one i S hSne (Finset.mem_powerset.mp hS) hcard]
          ring
        · rw [if_neg hSne]
          simpa [Finset.not_nonempty_iff_eq_empty.mp hSne] using w.mean_zero i]
      ring
    · have hβcard : effBeta β d < S.card := Nat.lt_of_not_ge hcard
      have hc : M.coef i S = 0 := M.low_order i S (by
        simp only [effBeta] at hβcard
        omega)
      rw [hc]
      simp]
  ring

/-- The expectation of a centered Bernoulli monomial times a raw monomial has the stated product-form value. -/
lemma E_global_centeredMonomial_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z =>
        (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) *
          ∏ j ∈ T, ((if z j then (1 : ℝ) else 0) - p)) =
      if S = T then (p * (1 - p)) ^ S.card else 0 := by
  let x : Bool → ℝ := fun b => (if b then 1 else 0) - p
  rw [show (fun z : V → Bool =>
      (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) *
        ∏ j ∈ T, ((if z j then (1 : ℝ) else 0) - p)) =
      (fun z => ∏ j,
        (if j ∈ S then x (z j) else 1) *
          (if j ∈ T then x (z j) else 1)) by
    funext z
    rw [Finset.prod_mul_distrib]
    simp [x]]
  rw [E_global_coordinate_prod p hp0 hp1
    (fun j b =>
      (if j ∈ S then x b else 1) *
        (if j ∈ T then x b else 1))]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    have hfactor (j : V) :
        p * ((if j ∈ S then x true else 1) *
              (if j ∈ S then x true else 1)) +
            (1 - p) * ((if j ∈ S then x false else 1) *
              (if j ∈ S then x false else 1)) =
          if j ∈ S then p * (1 - p) else 1 := by
      by_cases hj : j ∈ S <;> simp [hj, x] <;> ring
    simp_rw [hfactor]
    rw [Finset.prod_ite_mem]
    simp
  · rw [if_neg hST]
    have hdiff :
        ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S) := by
      by_contra h
      apply hST
      ext j
      constructor
      · intro hjS
        by_contra hjT
        exact h ⟨j, Or.inl ⟨hjS, hjT⟩⟩
      · intro hjT
        by_contra hjS
        exact h ⟨j, Or.inr ⟨hjT, hjS⟩⟩
    obtain ⟨j, hj⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rcases hj with hj | hj
    · simp [hj.1, hj.2, x]
      ring
    · simp [hj.1, hj.2, x]
      ring

/-- The global second moment of the SNIPE score equals its stated block-energy expression. -/
lemma snipeScore_sq_expectation_global
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Bool) (β : ℕ) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (i : V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).E
        (fun z => snipeScore G β p i z ^ 2) =
      blockEnergy β p (nbhdB G i).card := by
  let N := nbhdB G i
  let v := p * (1 - p)
  have hv : v ≠ 0 :=
    mul_ne_zero hp0.ne' (sub_pos.mpr hp1).ne'
  simp only [snipeScore, pow_two, Finset.sum_mul, Finset.mul_sum,
    FiniteDesign.E_sum]
  have hmoment (r q : ℕ) (S T : Finset V) :
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
        (fun z =>
          (bernoulliContrast p q / v ^ q *
              (∏ j ∈ T, ((if z j then (1 : ℝ) else 0) - p))) *
            (bernoulliContrast p r / v ^ r *
              (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)))) =
        (bernoulliContrast p q / v ^ q) *
          (bernoulliContrast p r / v ^ r) *
            (if T = S then v ^ T.card else 0) := by
    calc
      _ = (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E
          (fun z =>
            ((bernoulliContrast p q / v ^ q) *
              (bernoulliContrast p r / v ^ r)) *
                ((∏ j ∈ T, ((if z j then (1 : ℝ) else 0) - p)) *
                  (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)))) := by
        apply FiniteDesign.E_congr
        intro z
        ring
      _ = _ := by
        rw [FiniteDesign.E_const_mul,
          E_global_centeredMonomial_mul p (le_of_lt hp0) (le_of_lt hp1)]
  dsimp [v] at hmoment
  simp_rw [hmoment]
  simp [blockEnergy]
  apply Finset.sum_congr rfl
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hrle : r ≤ effBeta β (nbhdB G i).card :=
    (Finset.mem_Icc.mp hr).2
  rw [show
      (∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
        ∑ q ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
          if S ⊆ nbhdB G i ∧ S.card = q then
            bernoulliContrast p q / (p * (1 - p)) ^ q *
              (bernoulliContrast p r / (p * (1 - p)) ^ r) *
                (p * (1 - p)) ^ S.card
          else 0) =
      ∑ _S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
        bernoulliContrast p r / (p * (1 - p)) ^ r *
          (bernoulliContrast p r / (p * (1 - p)) ^ r) *
            (p * (1 - p)) ^ r by
    apply Finset.sum_congr rfl
    intro S hS
    have hSmem := Finset.mem_filter.mp hS
    have hSsub := Finset.mem_powerset.mp hSmem.1
    have hScard := hSmem.2
    rw [Finset.sum_eq_single r]
    · simp [hSsub, hScard, hr]
    · intro q hq hqr
      simp [hScard, hqr.symm]
    · intro hnot
      exact (hnot hr).elim]
  rw [show
      (nbhdB G i).powerset.filter (fun S => S.card = r) =
        (nbhdB G i).powersetCard r by
    ext S
    simp [Finset.mem_powersetCard]]
  rw [Finset.sum_const, Finset.card_powersetCard]
  simp only [nsmul_eq_mul]
  field_simp

/-- The total expected squared energy of canonical local-linear weights equals the stated multiple of block energy. -/
lemma canonicalLocLinWeights_energy
    (n d β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (i : Fin n) :
    (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).E
      (fun z =>
        (canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv).weight i z ^ 2) =
      blockEnergy β p d := by
  classical
  change
    (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).E
        (fun z =>
          snipeScore (fun j i => decide (blockGraph n d j i)) β p i z ^ 2) =
      blockEnergy β p d
  rw [snipeScore_sq_expectation_global
    (hp0 := hp0) (hp1 := hp1)]
  congr 1
  rw [show nbhdB (fun j i => decide (blockGraph n d j i)) i =
      nbhd (blockGraph n d) i by
    ext j
    simp [nbhdB, nbhd]]
  exact blockGraph_nbhd_card n d hd hdiv i

/-- Canonical local-linear weights have the stated centered moments for the specified local subsets. -/
lemma locLinWeight_centered_moment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (i : V) (S : Finset V) (hSne : S.Nonempty)
    (hSN : S ⊆ nbhd G i) (hScard : S.card ≤ effBeta β d) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z => w.weight i z *
        ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) =
      bernoulliContrast p S.card := by
  classical
  rw [show (fun z => w.weight i z *
      ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) =
      (fun z => ∑ T ∈ S.powerset,
        (-p) ^ (S.card - T.card) *
          (w.weight i z *
            ∏ j ∈ T, if z j then (1 : ℝ) else 0)) by
    funext z
    have hprod :
        (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) =
          ∑ T ∈ S.powerset,
            (-p) ^ (S.card - T.card) *
              ∏ j ∈ T, if z j then (1 : ℝ) else 0 := by
      rw [show
          (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) =
            ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) + (-p)) by
        apply Finset.prod_congr rfl
        intro j hj
        ring]
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T hT
      have hsub := Finset.mem_powerset.mp hT
      rw [Finset.prod_const, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hsub]
      ring
    rw [hprod, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    ring]
  rw [FiniteDesign.E_sum]
  simp_rw [FiniteDesign.E_const_mul]
  rw [show
      (∑ T ∈ S.powerset,
        (-p) ^ (S.card - T.card) *
          (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
            (fun _ => hp1)).E
            (fun z => w.weight i z *
              ∏ j ∈ T, if z j then (1 : ℝ) else 0)) =
      ∑ T ∈ S.powerset,
        if T.Nonempty then (-p) ^ (S.card - T.card) else 0 by
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hTne : T.Nonempty
    · rw [if_pos hTne,
        w.moment_one i T hTne
          ((Finset.mem_powerset.mp hT).trans hSN)]
      · ring
      · exact (Finset.card_le_card (Finset.mem_powerset.mp hT)).trans hScard
    · rw [if_neg hTne]
      have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
      subst T
      rw [show
          (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
            (fun _ => hp1)).E
              (fun z => w.weight i z *
                ∏ j ∈ (∅ : Finset V), if z j then (1 : ℝ) else 0) = 0 by
        simpa using w.mean_zero i]
      ring]
  rw [show
      (∑ T ∈ S.powerset,
        if T.Nonempty then (-p) ^ (S.card - T.card) else 0) =
      (1 - p) ^ S.card - (-p) ^ S.card by
    rw [show
        (∑ T ∈ S.powerset,
          if T.Nonempty then (-p) ^ (S.card - T.card) else 0) =
        (∑ T ∈ S.powerset, (-p) ^ (S.card - T.card)) -
          (-p) ^ S.card by
      rw [← Finset.sum_filter]
      have hfilter :
          S.powerset.filter (fun T => T.Nonempty) =
            S.powerset.erase ∅ := by
        ext T
        simp [Finset.nonempty_iff_ne_empty, and_comm]
      rw [hfilter]
      have herase := Finset.sum_erase_add
        (s := S.powerset)
        (f := fun T => (-p) ^ (S.card - T.card))
        (Finset.mem_powerset.mpr (empty_subset S))
      simp only [Finset.card_empty, Nat.sub_zero] at herase
      linarith]
    rw [show
        (∑ T ∈ S.powerset, (-p) ^ (S.card - T.card)) =
          (1 - p) ^ S.card by
      rw [← Finset.prod_const (s := S) (1 - p)]
      rw [show (∏ _j ∈ S, (1 - p)) =
          ∏ _j ∈ S, ((1 : ℝ) + (-p)) by
        apply Finset.prod_congr rfl
        intro j hj
        ring]
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T hT
      have hsub := Finset.mem_powerset.mp hT
      rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hsub]
      simp]]
  rfl

/-- The canonical local-linear weight paired with a SNIPE score has the stated expectation. -/
lemma locLinWeight_snipeScore_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) [DecidableRel G]
    (d β : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (i : V) (hcard : (nbhd G i).card = d) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z => w.weight i z *
        snipeScore (fun j i => decide (G j i)) β p i z) =
      blockEnergy β p d := by
  classical
  have hN :
      nbhdB (fun j i => decide (G j i)) i = nbhd G i := by
    ext j
    simp [nbhdB, nbhd]
  simp only [snipeScore, Finset.mul_sum, FiniteDesign.E_sum]
  simp_rw [mul_left_comm, FiniteDesign.E_const_mul]
  rw [show
      (∑ r ∈ Finset.Icc 1
          (effBeta β
            (nbhdB (fun j i => decide (G j i)) i).card),
        ∑ S ∈
          (nbhdB (fun j i => decide (G j i)) i).powerset.filter
            (fun S => S.card = r),
          bernoulliContrast p r /
              (p * (1 - p)) ^ r *
            (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
              (fun _ => hp1)).E
              (fun z => w.weight i z *
                ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p))) =
      blockEnergy β p d by
    rw [hN, hcard]
    unfold blockEnergy
    apply Finset.sum_congr rfl
    intro r hr
    have hrle : r ≤ effBeta β d := (Finset.mem_Icc.mp hr).2
    rw [show
        (∑ S ∈ (nbhd G i).powerset.filter (fun S => S.card = r),
          bernoulliContrast p r / (p * (1 - p)) ^ r *
            (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
              (fun _ => hp1)).E
              (fun z => w.weight i z *
                ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p))) =
        ∑ _S ∈ (nbhd G i).powersetCard r,
          bernoulliContrast p r / (p * (1 - p)) ^ r *
            bernoulliContrast p r by
      rw [show
          (nbhd G i).powerset.filter (fun S => S.card = r) =
            (nbhd G i).powersetCard r by
        ext S
        simp [Finset.mem_powersetCard]]
      apply Finset.sum_congr rfl
      intro S hS
      have hSmem := Finset.mem_powersetCard.mp hS
      have hSne : S.Nonempty := Finset.card_pos.mp (by
        have := (Finset.mem_Icc.mp hr).1
        omega)
      have hdeg : S.card ≤ effBeta β d := by
        simpa [hSmem.2] using hrle
      congr 1
      simpa [hSmem.2] using (locLinWeight_centered_moment
        (G := G) (d := d) (β := β) (p := p)
        (hp0 := hp0) (hp1 := hp1) (w := w) (i := i) (S := S)
        (hSne := hSne) (hSN := hSmem.1) (hScard := hdeg))]
    rw [Finset.sum_const, Finset.card_powersetCard, hcard]
    simp only [nsmul_eq_mul]
    ring]

end CausalSmith.Experimentation.SnipeDegreeFrontier
