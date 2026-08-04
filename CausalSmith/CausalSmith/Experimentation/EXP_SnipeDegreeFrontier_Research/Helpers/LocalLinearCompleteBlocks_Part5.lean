import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearClass
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part2
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part3
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part4

/-!
# Exact worst-case local-linear risk via extreme block schedules

Bounds each blockwise squared error by the block extremal value, constructs the
extreme block schedule attaining it, and evaluates the worst-case local-linear
risk exactly in terms of the blockwise extremal values.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Establishes the stated mathematical result for block schedule error sq le extremal. -/
lemma blockScheduleError_sq_le_extremal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (B p : ℝ)
    (hB : 0 < B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1)
    (M : LocLinSchedClass G d β B)
    (block : Finset V)
    (hblock : ∀ i ∈ block, block = nbhd G i) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
        (fun z => blockScheduleError w M block z ^ 2) ≤
      B ^ 2 * blockExtremal G d β p hp0 hp1 w block := by
  classical
  let D := bernoulliDesign (fun _ : V => p)
    (fun _ => hp0) (fun _ => hp1)
  let J : V → Finset (Finset V) :=
    fun _ => eligibleBlockSets d β block
  have hJ : ∀ i, (J i).Nonempty := by
    intro i
    refine ⟨∅, ?_⟩
    simp [J, eligibleBlockSets]
  have ha :
      ∀ i ∈ block, ∑ S ∈ J i, |M.coef i S| ≤ B := by
    intro i hi
    calc
      ∑ S ∈ J i, |M.coef i S| ≤
          ∑ S ∈ (nbhd G i).powerset, |M.coef i S| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          have hsub : S ⊆ block :=
            Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
          have : S ⊆ nbhd G i := by simpa [← hblock i hi] using hsub
          exact Finset.mem_powerset.mpr this
        · intro S hS hnot
          exact abs_nonneg _
      _ ≤ B := M.mass_le i
  obtain ⟨c, hcJ, hcBound⟩ :=
    absSum_rows_quadratic_exists_signed_extreme
      D block J hJ B hB M.coef ha
      (fun i S => locLinUnitError w i S) (fun _ => 0)
  let choice : (V → Bool) × (V → Finset V) :=
    (fun i => (c i).1, fun i => (c i).2)
  have hchoice :
      choice ∈ Finset.univ.filter (fun choice =>
        ∀ i ∈ block,
          choice.2 i ⊆ block ∧
            (choice.2 i).card ≤ effBeta β d) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    have hc := hcJ i hi
    exact ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hc).1,
      (Finset.mem_filter.mp hc).2⟩
  have hextreme :
      D.E (fun z =>
          (∑ i ∈ block,
            (if (c i).1 then (1 : ℝ) else -1) * B *
              locLinUnitError w i (c i).2 z) ^ 2) =
        B ^ 2 *
          D.E (fun z =>
            (∑ i ∈ block,
              (if (c i).1 then (1 : ℝ) else -1) *
                locLinUnitError w i (c i).2 z) ^ 2) := by
    rw [show (fun z =>
        (∑ i ∈ block,
          (if (c i).1 then (1 : ℝ) else -1) * B *
            locLinUnitError w i (c i).2 z) ^ 2) =
      (fun z => B ^ 2 *
        (∑ i ∈ block,
          (if (c i).1 then (1 : ℝ) else -1) *
            locLinUnitError w i (c i).2 z) ^ 2) by
      funext z
      rw [show
          (∑ i ∈ block,
            (if (c i).1 then (1 : ℝ) else -1) * B *
              locLinUnitError w i (c i).2 z) =
          B * ∑ i ∈ block,
            (if (c i).1 then (1 : ℝ) else -1) *
              locLinUnitError w i (c i).2 z by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
      ring]
    rw [FiniteDesign.E_const_mul]
  calc
    D.E (fun z => blockScheduleError w M block z ^ 2) ≤
        D.E (fun z =>
          (∑ i ∈ block,
            (if (c i).1 then (1 : ℝ) else -1) * B *
              locLinUnitError w i (c i).2 z) ^ 2) := by
      simpa [D, J, blockScheduleError] using hcBound
    _ = B ^ 2 *
        D.E (fun z =>
          (∑ i ∈ block,
            (if (c i).1 then (1 : ℝ) else -1) *
              locLinUnitError w i (c i).2 z) ^ 2) := hextreme
    _ ≤ B ^ 2 * blockExtremal G d β p hp0 hp1 w block := by
      apply mul_le_mul_of_nonneg_left
      · unfold blockExtremal
        dsimp only
        convert Finset.le_sup'
          (f := fun choice =>
            D.E (fun z =>
              (∑ i ∈ block, (if choice.1 i then (1 : ℝ) else -1) *
                (w.weight i z *
                  (∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0) -
                    if (choice.2 i).Nonempty then 1 else 0)) ^ 2))
          hchoice using 1
      · positivity

/-- Defines extreme block schedule. -/
noncomputable def extremeBlockSchedule
    (n d β : ℕ) (B : ℝ) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (choice :
      Fin (blockCount n d) → (Fin n → Bool) × (Fin n → Finset (Fin n)))
    (hchoice : ∀ b i, i ∈ completeBlockUnits n d b →
      (choice b).2 i ⊆ completeBlockUnits n d b ∧
        ((choice b).2 i).card ≤ effBeta β d)
    (hB : 0 ≤ B) :
    LocLinSchedClass (blockGraph n d) d β B := by
  classical
  let idx := completeBlockIndex n d hd hdiv
  let coef : Fin n → Finset (Fin n) → ℝ := fun i S =>
    if S = (choice (idx i)).2 i then
      (if (choice (idx i)).1 i then (1 : ℝ) else -1) * B
    else 0
  refine
    { coef := coef
      supported := ?_
      low_order := ?_
      mass_le := ?_ }
  · intro i S hS
    by_cases heq : S = (choice (idx i)).2 i
    · exfalso
      apply hS
      subst S
      have hc := hchoice (idx i) i
        (mem_completeBlockIndex n d hd hdiv i)
      exact hc.1.trans (by
        rw [completeBlockUnits_eq_nbhd n d hdiv (idx i) i
          (mem_completeBlockIndex n d hd hdiv i)])
    · simp [coef, heq]
  · intro i S hcard
    by_cases heq : S = (choice (idx i)).2 i
    · have hc := (hchoice (idx i) i
        (mem_completeBlockIndex n d hd hdiv i)).2
      subst S
      omega
    · simp [coef, heq]
  · intro i
    have hmem :
        (choice (idx i)).2 i ∈ (nbhd (blockGraph n d) i).powerset := by
      apply Finset.mem_powerset.mpr
      exact (hchoice (idx i) i
        (mem_completeBlockIndex n d hd hdiv i)).1.trans (by
          rw [completeBlockUnits_eq_nbhd n d hdiv (idx i) i
            (mem_completeBlockIndex n d hd hdiv i)])
    rw [Finset.sum_eq_single ((choice (idx i)).2 i)]
    · cases hs : (choice (idx i)).1 i <;>
        simp [coef, hs, abs_of_nonneg hB]
    · intro S hS hne
      simp [coef, hne]
    · intro hnot
      exact (hnot hmem).elim

/-- Establishes the stated mathematical result for extreme block schedule block error. -/
lemma extremeBlockSchedule_blockError
    (n d β : ℕ) (B p : ℝ) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1)
    (choice :
      Fin (blockCount n d) → (Fin n → Bool) × (Fin n → Finset (Fin n)))
    (hchoice : ∀ b i, i ∈ completeBlockUnits n d b →
      (choice b).2 i ⊆ completeBlockUnits n d b ∧
        ((choice b).2 i).card ≤ effBeta β d)
    (hB : 0 ≤ B) (b : Fin (blockCount n d)) (z : Fin n → Bool) :
    blockScheduleError w
        (extremeBlockSchedule n d β B hd hdiv choice hchoice hB)
        (completeBlockUnits n d b) z =
      B * ∑ i ∈ completeBlockUnits n d b,
        (if (choice b).1 i then (1 : ℝ) else -1) *
          locLinUnitError w i ((choice b).2 i) z := by
  classical
  unfold blockScheduleError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hidx : completeBlockIndex n d hd hdiv i = b := by
    apply Fin.ext
    exact (Finset.mem_filter.mp hi).2.2
  rw [Finset.sum_eq_single ((choice b).2 i)]
  · simp only [extremeBlockSchedule, hidx, if_pos rfl]
    simp only [if_true]
    ring
  · intro S hS hne
    simp [extremeBlockSchedule, hidx, hne]
  · intro hnot
    have hc := hchoice b i hi
    have hmem : (choice b).2 i ∈ eligibleBlockSets d β
        (completeBlockUnits n d b) := by
      simp [eligibleBlockSets, hc.1, hc.2]
    exact (hnot hmem).elim

/-- Establishes the stated mathematical result for exists block extremal choice. -/
lemma exists_blockExtremal_choice
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1) (block : Finset V) :
    ∃ choice : (V → Bool) × (V → Finset V),
      (∀ i ∈ block,
        choice.2 i ⊆ block ∧
          (choice.2 i).card ≤ effBeta β d) ∧
      blockExtremal G d β p hp0 hp1 w block =
        (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
          (fun _ => hp1)).E
          (fun z =>
            (∑ i ∈ block, (if choice.1 i then (1 : ℝ) else -1) *
              locLinUnitError w i (choice.2 i) z) ^ 2) := by
  classical
  unfold blockExtremal
  dsimp only
  let candidates : Finset ((V → Bool) × (V → Finset V)) :=
    Finset.univ.filter (fun choice =>
      ∀ i ∈ block,
        choice.2 i ⊆ block ∧ (choice.2 i).card ≤ effBeta β d)
  have hne : candidates.Nonempty := by
    refine ⟨(fun _ => false, fun _ => ∅), ?_⟩
    simp [candidates]
  obtain ⟨choice, hmem, hmax⟩ :=
    Finset.exists_mem_eq_sup' hne (fun choice =>
      (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
        (fun _ => hp1)).E
        (fun z =>
          (∑ i ∈ block, (if choice.1 i then (1 : ℝ) else -1) *
            (w.weight i z *
              (∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0) -
                if (choice.2 i).Nonempty then 1 else 0)) ^ 2))
  refine ⟨choice, ?_, ?_⟩
  · simpa [candidates] using hmem
  · simpa [candidates, locLinUnitError] using hmax

/-- Establishes the stated mathematical result for loc lin worst risk exact block extremal. -/
lemma locLinWorstRisk_exact_blockExtremal
    (n d β : ℕ) (B p : ℝ)
    (hB : 0 < B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1) :
    locLinWorstRisk (blockGraph n d) d β B p hp0 hp1 w =
      B ^ 2 / (n : ℝ) ^ 2 *
        ∑ b : Fin (blockCount n d),
          blockExtremal (blockGraph n d) d β p hp0 hp1 w
            (completeBlockUnits n d b) := by
  classical
  let R : ℝ :=
    B ^ 2 / (n : ℝ) ^ 2 *
      ∑ b : Fin (blockCount n d),
        blockExtremal (blockGraph n d) d β p hp0 hp1 w
          (completeBlockUnits n d b)
  have hupper (M : LocLinSchedClass (blockGraph n d) d β B) :
      locLinRiskAt (blockGraph n d) d β B p hp0 hp1 w M ≤ R := by
    rw [locLinRiskAt_block_decomposition
      n d β B p hp0 hp1 hn hd hdiv w M]
    have hsum :
        ∑ b : Fin (blockCount n d),
            (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
              (fun _ => hp1)).E
              (fun z => blockScheduleError w M
                (completeBlockUnits n d b) z ^ 2) ≤
          ∑ b : Fin (blockCount n d),
            B ^ 2 *
              blockExtremal (blockGraph n d) d β p hp0 hp1 w
                (completeBlockUnits n d b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact blockScheduleError_sq_le_extremal
        (blockGraph n d) d β B p hB hp0 hp1 w M
        (completeBlockUnits n d b)
        (fun i hi => completeBlockUnits_eq_nbhd n d hdiv b i hi)
    have hinv : 0 ≤ (n : ℝ)⁻¹ ^ 2 := sq_nonneg _
    calc
      (n : ℝ)⁻¹ ^ 2 *
          ∑ b : Fin (blockCount n d),
            (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
              (fun _ => hp1)).E
              (fun z => blockScheduleError w M
                (completeBlockUnits n d b) z ^ 2) ≤
          (n : ℝ)⁻¹ ^ 2 *
            ∑ b : Fin (blockCount n d),
              B ^ 2 *
                blockExtremal (blockGraph n d) d β p hp0 hp1 w
                  (completeBlockUnits n d b) :=
        mul_le_mul_of_nonneg_left hsum hinv
      _ = R := by
        dsimp [R]
        rw [← Finset.mul_sum]
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        field_simp
  have hexists :
      ∀ b : Fin (blockCount n d),
        ∃ choice : (Fin n → Bool) × (Fin n → Finset (Fin n)),
          (∀ i ∈ completeBlockUnits n d b,
            choice.2 i ⊆ completeBlockUnits n d b ∧
              (choice.2 i).card ≤ effBeta β d) ∧
          blockExtremal (blockGraph n d) d β p hp0 hp1 w
              (completeBlockUnits n d b) =
            (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
              (fun _ => hp1)).E
              (fun z =>
                (∑ i ∈ completeBlockUnits n d b,
                  (if choice.1 i then (1 : ℝ) else -1) *
                    locLinUnitError w i (choice.2 i) z) ^ 2) :=
    fun b => exists_blockExtremal_choice
      (blockGraph n d) d β p hp0 hp1 w (completeBlockUnits n d b)
  let choice :
      Fin (blockCount n d) → (Fin n → Bool) × (Fin n → Finset (Fin n)) :=
    fun b => (hexists b).choose
  have hchoice :
      ∀ b i, i ∈ completeBlockUnits n d b →
        (choice b).2 i ⊆ completeBlockUnits n d b ∧
          ((choice b).2 i).card ≤ effBeta β d := by
    intro b i hi
    exact (hexists b).choose_spec.1 i hi
  have hchoiceMax (b : Fin (blockCount n d)) :
      blockExtremal (blockGraph n d) d β p hp0 hp1 w
          (completeBlockUnits n d b) =
        (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
          (fun _ => hp1)).E
          (fun z =>
            (∑ i ∈ completeBlockUnits n d b,
              (if (choice b).1 i then (1 : ℝ) else -1) *
                locLinUnitError w i ((choice b).2 i) z) ^ 2) :=
    (hexists b).choose_spec.2
  let Mstar :=
    extremeBlockSchedule n d β B hd hdiv choice hchoice hB.le
  have hMstar :
      locLinRiskAt (blockGraph n d) d β B p hp0 hp1 w Mstar = R := by
    rw [locLinRiskAt_block_decomposition
      n d β B p hp0 hp1 hn hd hdiv w Mstar]
    have hblock (b : Fin (blockCount n d)) :
        (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
          (fun _ => hp1)).E
          (fun z => blockScheduleError w Mstar
            (completeBlockUnits n d b) z ^ 2) =
          B ^ 2 *
            blockExtremal (blockGraph n d) d β p hp0 hp1 w
              (completeBlockUnits n d b) := by
      rw [show
          blockScheduleError w Mstar (completeBlockUnits n d b) =
            fun z => B * ∑ i ∈ completeBlockUnits n d b,
              (if (choice b).1 i then (1 : ℝ) else -1) *
                locLinUnitError w i ((choice b).2 i) z by
        funext z
        exact extremeBlockSchedule_blockError
          n d β B p hd hdiv hp0 hp1 w choice hchoice hB.le b z]
      rw [show (fun z =>
          (B * ∑ i ∈ completeBlockUnits n d b,
            (if (choice b).1 i then (1 : ℝ) else -1) *
              locLinUnitError w i ((choice b).2 i) z) ^ 2) =
        (fun z => B ^ 2 *
          (∑ i ∈ completeBlockUnits n d b,
            (if (choice b).1 i then (1 : ℝ) else -1) *
              locLinUnitError w i ((choice b).2 i) z) ^ 2) by
        funext z
        ring]
      rw [FiniteDesign.E_const_mul, ← hchoiceMax b]
    rw [show
        (∑ b : Fin (blockCount n d),
          (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
            (fun _ => hp1)).E
            (fun z => blockScheduleError w Mstar
              (completeBlockUnits n d b) z ^ 2)) =
        ∑ b : Fin (blockCount n d),
          B ^ 2 *
            blockExtremal (blockGraph n d) d β p hp0 hp1 w
              (completeBlockUnits n d b) by
      apply Finset.sum_congr rfl
      intro b hb
      exact hblock b]
    dsimp [R]
    rw [← Finset.mul_sum]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  apply le_antisymm
  · unfold locLinWorstRisk
    apply csSup_le
    · exact ⟨locLinRiskAt (blockGraph n d) d β B p hp0 hp1 w Mstar,
        ⟨Mstar, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨M, rfl⟩
      exact hupper M
  · unfold locLinWorstRisk
    apply le_csSup
    · refine ⟨R, ?_⟩
      intro r hr
      rcases hr with ⟨M, rfl⟩
      exact hupper M
    · exact ⟨Mstar, hMstar⟩

/-- Establishes the stated mathematical result for complete block benchmark algebra. -/
lemma completeBlock_benchmark_algebra
    (n d : ℕ) (B A : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n) :
    B ^ 2 / (n : ℝ) ^ 2 *
        ∑ _b : Fin (blockCount n d), (d : ℝ) ^ 2 * A =
      B ^ 2 * A / blockCount n d := by
  have hq : 0 < blockCount n d := by
    rcases hdiv with ⟨q, rfl⟩
    simp only [blockCount]
    have hq : 0 < q := by
      by_contra hz
      have : q = 0 := Nat.eq_zero_of_not_pos hz
      subst q
      simp at hn
    have hd0 : 0 < d := by omega
    simp [hd0, hq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  have hncast :
      (n : ℝ) = (blockCount n d : ℝ) * (d : ℝ) := by
    norm_cast
    simpa [blockCount, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
  rw [hncast]
  have hqr : (blockCount n d : ℝ) ≠ 0 := by positivity
  have hdr : (d : ℝ) ≠ 0 := by positivity
  field_simp

/-- A population unit's complete-block index is unchanged when the population size, block
size, divisibility condition, and unit are replaced by equal values. -/
add_decl_doc completeBlockIndex.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
