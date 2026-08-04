import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearClass
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part2
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part3

/-!
# The block-schedule error and the blockwise risk decomposition

Defines the eligible block sets and the block-schedule estimation error, proves
it is mean zero and depends only on its own block, and decomposes the
local-linear risk at a schedule into a sum of blockwise contributions.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Defines eligible block sets. -/
noncomputable def eligibleBlockSets
    {V : Type*} [Fintype V] [DecidableEq V]
    (d β : ℕ) (block : Finset V) : Finset (Finset V) :=
  block.powerset.filter (fun S => S.card ≤ effBeta β d)

/-- Defines block schedule error. -/
noncomputable def blockScheduleError
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : V → V → Prop} {d β : ℕ} {B p : ℝ}
    {hp0 : 0 ≤ p} {hp1 : p ≤ 1}
    (w : LocLinWeights G d β p hp0 hp1)
    (M : LocLinSchedClass G d β B)
    (block : Finset V) (z : V → Bool) : ℝ :=
  ∑ i ∈ block, ∑ S ∈ eligibleBlockSets d β block,
    M.coef i S * locLinUnitError w i S z

/-- Establishes the stated mathematical result for loc lin unit error mean zero. -/
lemma locLinUnitError_mean_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (i : V) (S : Finset V)
    (hSN : S ⊆ nbhd G i) (hScard : S.card ≤ effBeta β d) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E (locLinUnitError w i S) = 0 := by
  unfold locLinUnitError
  rw [FiniteDesign.E_sub, FiniteDesign.E_const]
  by_cases hSne : S.Nonempty
  · rw [if_pos hSne, w.moment_one i S hSne hSN hScard]
    ring
  · rw [if_neg hSne]
    simpa [Finset.not_nonempty_iff_eq_empty.mp hSne] using w.mean_zero i

/-- Establishes the stated mathematical result for block schedule error mean zero. -/
lemma blockScheduleError_mean_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (M : LocLinSchedClass G d β B)
    (block : Finset V)
    (hblock : ∀ i ∈ block, block = nbhd G i) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E (blockScheduleError w M block) = 0 := by
  classical
  unfold blockScheduleError
  rw [FiniteDesign.E_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [FiniteDesign.E_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [FiniteDesign.E_const_mul]
  rw [locLinUnitError_mean_zero G d β p hp0 hp1 w i S]
  · ring
  · have hsub : S ⊆ block :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    simpa [hblock i hi] using hsub
  · exact (Finset.mem_filter.mp hS).2

/-- Establishes the stated mathematical result for block schedule error local. -/
lemma blockScheduleError_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (M : LocLinSchedClass G d β B)
    (block : Finset V)
    (hblock : ∀ i ∈ block, block = nbhd G i)
    (z z' : V → Bool) (hzz : ∀ j ∈ block, z j = z' j) :
    blockScheduleError w M block z =
      blockScheduleError w M block z' := by
  classical
  unfold blockScheduleError
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro S hS
  congr 1
  unfold locLinUnitError
  have hw : w.weight i z = w.weight i z' := by
    apply w.local_dep i z z'
    intro j hj
    exact hzz j (by simpa [hblock i hi] using hj)
  rw [hw]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  rw [hzz j]
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 hj

/-- Establishes the stated mathematical result for complete block units disjoint. -/
lemma completeBlockUnits_disjoint
    (n d : ℕ) (b c : Fin (blockCount n d)) (hbc : b ≠ c) :
    Disjoint (completeBlockUnits n d b) (completeBlockUnits n d c) := by
  rw [Finset.disjoint_left]
  intro i hib hic
  apply hbc
  apply Fin.ext
  exact ((Finset.mem_filter.mp hib).2.2).symm.trans
    (Finset.mem_filter.mp hic).2.2

/-- Establishes the stated mathematical result for sum complete block units. -/
lemma sum_completeBlockUnits
    (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (f : Fin n → ℝ) :
    ∑ b : Fin (blockCount n d), ∑ i ∈ completeBlockUnits n d b, f i =
      ∑ i : Fin n, f i := by
  classical
  have hactive : activeCount n d = n := activeCount_eq_of_dvd n d hdiv
  let idx : Fin n → Fin (blockCount n d) := fun i =>
    ⟨i.val / d, by
      simp only [blockCount]
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [Nat.div_mul_cancel hdiv] using i.isLt⟩
  unfold completeBlockUnits
  simp_rw [hactive]
  simp only [Finset.sum_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (idx i)]
  · simp [idx, i.isLt]
  · intro b hb hbi
    have hne : b.val ≠ i.val / d := by
      intro h
      apply hbi
      apply Fin.ext
      simpa [idx] using h
    have hne' : i.val / d ≠ b.val := Ne.symm hne
    simp [i.isLt, hne']
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Establishes the stated mathematical result for complete block schedule error mul zero. -/
lemma completeBlock_scheduleError_mul_zero
    (n d β : ℕ) (B p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1)
    (M : LocLinSchedClass (blockGraph n d) d β B)
    (b c : Fin (blockCount n d)) (hbc : b ≠ c) :
    (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z =>
        blockScheduleError w M (completeBlockUnits n d b) z *
          blockScheduleError w M (completeBlockUnits n d c) z) = 0 := by
  classical
  let Db : ∀ _i : Fin n, FiniteDesign Bool :=
    fun _ => coinDesign p hp0 hp1
  have hbLocal :
      ∀ z z' : Fin n → Bool,
        (∀ i ∈ completeBlockUnits n d b, z i = z' i) →
        blockScheduleError w M (completeBlockUnits n d b) z =
          blockScheduleError w M (completeBlockUnits n d b) z' := by
    intro z z' hzz
    exact blockScheduleError_local
      (blockGraph n d) d β B p hp0 hp1 w M
      (completeBlockUnits n d b)
      (fun i hi => completeBlockUnits_eq_nbhd n d hdiv b i hi)
      z z' hzz
  have hcLocal :
      ∀ z z' : Fin n → Bool,
        (∀ i ∉ completeBlockUnits n d b, z i = z' i) →
        blockScheduleError w M (completeBlockUnits n d c) z =
          blockScheduleError w M (completeBlockUnits n d c) z' := by
    intro z z' hzz
    apply blockScheduleError_local
      (blockGraph n d) d β B p hp0 hp1 w M
      (completeBlockUnits n d c)
      (fun i hi => completeBlockUnits_eq_nbhd n d hdiv c i hi)
    intro i hic
    exact hzz i (fun hib =>
      Finset.disjoint_left.mp
        (completeBlockUnits_disjoint n d b c hbc) hib hic)
  change (prodDesign Db).E
      (fun z =>
        blockScheduleError w M (completeBlockUnits n d b) z *
          blockScheduleError w M (completeBlockUnits n d c) z) = 0
  rw [FiniteDesign.E_prod_block_mul Db
    (completeBlockUnits n d b)
    (blockScheduleError w M (completeBlockUnits n d b))
    (blockScheduleError w M (completeBlockUnits n d c))
    hbLocal hcLocal]
  rw [show
      (prodDesign Db).E
          (blockScheduleError w M (completeBlockUnits n d b)) = 0 by
    change
      (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
        (fun _ => hp1)).E
          (blockScheduleError w M (completeBlockUnits n d b)) = 0
    exact blockScheduleError_mean_zero
      (blockGraph n d) d β B p hp0 hp1 w M
      (completeBlockUnits n d b)
      (fun i hi => completeBlockUnits_eq_nbhd n d hdiv b i hi)]
  ring

/-- Establishes the stated mathematical result for e complete block schedule error sum sq. -/
lemma E_completeBlock_scheduleError_sum_sq
    (n d β : ℕ) (B p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1)
    (M : LocLinSchedClass (blockGraph n d) d β B) :
    (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z =>
        (∑ b : Fin (blockCount n d),
          blockScheduleError w M (completeBlockUnits n d b) z) ^ 2) =
      ∑ b : Fin (blockCount n d),
        (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
          (fun _ => hp1)).E
          (fun z => blockScheduleError w M
            (completeBlockUnits n d b) z ^ 2) := by
  classical
  let Db := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => hp0) (fun _ => hp1)
  rw [show (fun z =>
      (∑ b : Fin (blockCount n d),
        blockScheduleError w M (completeBlockUnits n d b) z) ^ 2) =
      (fun z =>
        ∑ b : Fin (blockCount n d),
          ∑ c : Fin (blockCount n d),
            blockScheduleError w M (completeBlockUnits n d b) z *
              blockScheduleError w M (completeBlockUnits n d c) z) by
    funext z
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]]
  rw [FiniteDesign.E_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [FiniteDesign.E_sum, Finset.sum_eq_single b]
  · simp [pow_two]
  · intro c hc hcb
    exact completeBlock_scheduleError_mul_zero
      n d β B p hp0 hp1 hd hdiv w M b c (Ne.symm hcb)
  · intro hb'
    exact (hb' (Finset.mem_univ b)).elim

/-- Establishes the stated mathematical result for schedule inner eq eligible. -/
lemma schedule_inner_eq_eligible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (M : LocLinSchedClass G d β B)
    (i : V) (block : Finset V) (hblock : block = nbhd G i)
    (z : V → Bool) :
    ∑ S ∈ (nbhd G i).powerset,
        M.coef i S * locLinUnitError w i S z =
      ∑ S ∈ eligibleBlockSets d β block,
        M.coef i S * locLinUnitError w i S z := by
  classical
  subst block
  unfold eligibleBlockSets
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hcard : S.card ≤ effBeta β d
  · simp [hcard]
  · have hzero : M.coef i S = 0 := by
      apply M.low_order i S
      omega
    simp [hcard, hzero]

/-- Establishes the stated mathematical result for sum block schedule error eq total. -/
lemma sum_blockScheduleError_eq_total
    (n d β : ℕ) (B p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1)
    (M : LocLinSchedClass (blockGraph n d) d β B)
    (z : Fin n → Bool) :
    ∑ b : Fin (blockCount n d),
        blockScheduleError w M (completeBlockUnits n d b) z =
      ∑ i : Fin n, ∑ S ∈ (nbhd (blockGraph n d) i).powerset,
        M.coef i S * locLinUnitError w i S z := by
  classical
  rw [← sum_completeBlockUnits n d hd hdiv
    (fun i => ∑ S ∈ (nbhd (blockGraph n d) i).powerset,
      M.coef i S * locLinUnitError w i S z)]
  apply Finset.sum_congr rfl
  intro b hb
  unfold blockScheduleError
  apply Finset.sum_congr rfl
  intro i hi
  exact (schedule_inner_eq_eligible
    (blockGraph n d) d β B p hp0 hp1 w M i
    (completeBlockUnits n d b)
    (completeBlockUnits_eq_nbhd n d hdiv b i hi) z).symm

/-- Establishes the stated mathematical result for loc lin risk at block decomposition. -/
lemma locLinRiskAt_block_decomposition
    (n d β : ℕ) (B p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1)
    (M : LocLinSchedClass (blockGraph n d) d β B) :
    locLinRiskAt (blockGraph n d) d β B p hp0 hp1 w M =
      (n : ℝ)⁻¹ ^ 2 *
        ∑ b : Fin (blockCount n d),
          (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
            (fun _ => hp1)).E
            (fun z => blockScheduleError w M
              (completeBlockUnits n d b) z ^ 2) := by
  classical
  unfold locLinRiskAt FiniteDesign.mse
  rw [show (fun z =>
      (locLinEstimator (blockGraph n d) d β p hp0 hp1 w z
          (obsOutcome (blockGraph n d) M.coef z) -
        tte (blockGraph n d) M.coef) ^ 2) =
      (fun z =>
        ((n : ℝ)⁻¹ *
          ∑ b : Fin (blockCount n d),
            blockScheduleError w M (completeBlockUnits n d b) z) ^ 2) by
    funext z
    rw [locLinEstimator_error_expansion
      (blockGraph n d) d β B p hp0 hp1 w M z]
    simp only [Fintype.card_fin]
    rw [sum_blockScheduleError_eq_total
      n d β B p hp0 hp1 hd hdiv w M z]]
  rw [show (fun z =>
      ((n : ℝ)⁻¹ *
        ∑ b : Fin (blockCount n d),
          blockScheduleError w M (completeBlockUnits n d b) z) ^ 2) =
      (fun z => (n : ℝ)⁻¹ ^ 2 *
        (∑ b : Fin (blockCount n d),
          blockScheduleError w M (completeBlockUnits n d b) z) ^ 2) by
    funext z
    ring]
  rw [FiniteDesign.E_const_mul,
    E_completeBlock_scheduleError_sum_sq
      n d β B p hp0 hp1 hd hdiv w M]

end CausalSmith.Experimentation.SnipeDegreeFrontier
