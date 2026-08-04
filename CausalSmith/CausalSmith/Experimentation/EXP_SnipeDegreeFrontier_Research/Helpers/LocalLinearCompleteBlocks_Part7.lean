import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearClass
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part2
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part3
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part4
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part5
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part6

/-!
# The sparse orthogonal-complement witness

Constructs the orthogonal block perturbation and the associated witness weights,
computes their energy and distance, and derives the witness upper bound on the
blockwise extremal value.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Defines orthogonal block perturb. -/
noncomputable def orthogonalBlockPerturb
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (i : Fin n) (z : Fin n → Bool) : ℝ :=
  if hhigh : β < d then
    if i = blockFirstUnit n d hd hdiv (completeBlockIndex n d hd hdiv i) then
      Real.sqrt
          (2 * (d : ℝ) * blockEnergy β p d /
            (p * (1 - p)) ^ d) *
        ∏ j ∈ completeBlockUnits n d (completeBlockIndex n d hd hdiv i),
          ((if z j then (1 : ℝ) else 0) - p)
    else 0
  else 0

/-- Defines orthogonal witness weights. -/
noncomputable def orthogonalWitnessWeights
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n) :
    LocLinWeights (blockGraph n d) d β p
      (le_of_lt hp0) (le_of_lt hp1) := by
  classical
  let w0 := canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv
  refine
    { weight := fun i z =>
        w0.weight i z +
          orthogonalBlockPerturb n d β p hβ hp0 hp1 hn hd hdiv i z
      blockIndex := w0.blockIndex
      complete_block := w0.complete_block
      local_dep := ?_
      mean_zero := ?_
      moment_one := ?_ }
  · intro i z z' hzz
    rw [w0.local_dep i z z' hzz]
    congr 1
    unfold orthogonalBlockPerturb
    split_ifs with hhigh hfirst
    · congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [hzz j]
      have hi :=
        mem_completeBlockIndex n d hd hdiv i
      simpa [completeBlockUnits_eq_nbhd n d hdiv
        (completeBlockIndex n d hd hdiv i) i hi] using hj
    · rfl
    · rfl
  · intro i
    rw [FiniteDesign.E_add, w0.mean_zero i]
    suffices
        (bernoulliDesign (fun _ : Fin n => p)
          (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
          (orthogonalBlockPerturb n d β p hβ hp0 hp1 hn hd hdiv i) = 0 by
      linarith
    unfold orthogonalBlockPerturb
    split_ifs with hhigh hfirst
    · rw [FiniteDesign.E_const_mul]
      rw [show
          (bernoulliDesign (fun _ : Fin n => p)
            (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
            (fun z =>
              ∏ j ∈ completeBlockUnits n d
                  (completeBlockIndex n d hd hdiv i),
                ((if z j then (1 : ℝ) else 0) - p)) = 0 by
        simpa using E_global_centered_mul_raw_eq_zero p
          (le_of_lt hp0) (le_of_lt hp1)
          (completeBlockUnits n d (completeBlockIndex n d hd hdiv i))
          ∅ (Finset.empty_subset _)
          (by
            rw [Finset.card_empty,
              completeBlockUnits_card n d hd hdiv]
            omega)]
      ring
    · simp
    · simp
  · intro i S hSne hSN hScard
    rw [show (fun z =>
        (w0.weight i z +
          orthogonalBlockPerturb n d β p hβ hp0 hp1 hn hd hdiv i z) *
            ∏ j ∈ S, if z j then (1 : ℝ) else 0) =
      (fun z =>
        w0.weight i z * (∏ j ∈ S, if z j then (1 : ℝ) else 0) +
          orthogonalBlockPerturb n d β p hβ hp0 hp1 hn hd hdiv i z *
            ∏ j ∈ S, if z j then (1 : ℝ) else 0) by
      funext z
      ring]
    rw [FiniteDesign.E_add,
      w0.moment_one i S hSne hSN hScard]
    suffices
        (bernoulliDesign (fun _ : Fin n => p)
          (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
          (fun z =>
            orthogonalBlockPerturb n d β p hβ hp0 hp1 hn hd hdiv i z *
              ∏ j ∈ S, if z j then (1 : ℝ) else 0) = 0 by
      linarith
    unfold orthogonalBlockPerturb
    split_ifs with hhigh hfirst
    · rw [show (fun z : Fin n → Bool =>
          (Real.sqrt
              (2 * (d : ℝ) * blockEnergy β p d /
                (p * (1 - p)) ^ d) *
            ∏ j ∈ completeBlockUnits n d
                (completeBlockIndex n d hd hdiv i),
              ((if z j then (1 : ℝ) else 0) - p)) *
            ∏ j ∈ S, if z j then (1 : ℝ) else 0) =
        (fun z : Fin n → Bool =>
          Real.sqrt
              (2 * (d : ℝ) * blockEnergy β p d /
                (p * (1 - p)) ^ d) *
            ((∏ j ∈ completeBlockUnits n d
                (completeBlockIndex n d hd hdiv i),
                ((if z j then (1 : ℝ) else 0) - p)) *
              ∏ j ∈ S, if z j then (1 : ℝ) else 0)) by
        funext z
        ring]
      rw [FiniteDesign.E_const_mul,
        E_global_centered_mul_raw_eq_zero p
          (le_of_lt hp0) (le_of_lt hp1)
          (completeBlockUnits n d (completeBlockIndex n d hd hdiv i)) S]
      · ring
      · have hi := mem_completeBlockIndex n d hd hdiv i
        simpa [completeBlockUnits_eq_nbhd n d hdiv
          (completeBlockIndex n d hd hdiv i) i hi] using hSN
      · rw [completeBlockUnits_card n d hd hdiv]
        have hsβ : S.card ≤ β :=
          hScard.trans (by simp [effBeta])
        omega
    · simp
    · simp

/-- Establishes the stated mathematical result for orthogonal block perturb energy. -/
lemma orthogonalBlockPerturb_energy
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (hhigh : β < d) (i : Fin n) :
    (bernoulliDesign (fun _ : Fin n => p)
      (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
      (fun z =>
        orthogonalBlockPerturb n d β p hβ hp0 hp1 hn hd hdiv i z ^ 2) =
      if i = blockFirstUnit n d hd hdiv
          (completeBlockIndex n d hd hdiv i) then
        2 * (d : ℝ) * blockEnergy β p d
      else 0 := by
  classical
  simp only [orthogonalBlockPerturb, dif_pos hhigh]
  split_ifs with hfirst
  · let block :=
      completeBlockUnits n d (completeBlockIndex n d hd hdiv i)
    let v := p * (1 - p)
    have hv : 0 < v := mul_pos hp0 (sub_pos.mpr hp1)
    have hA : 0 < blockEnergy β p d :=
      blockEnergy_pos β d p hβ hd hp0 hp1
    have hfrac :
        0 ≤ 2 * (d : ℝ) * blockEnergy β p d / v ^ d := by
      positivity
    change
      (bernoulliDesign (fun _ : Fin n => p)
        (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
        (fun z =>
          (Real.sqrt
              (2 * (d : ℝ) * blockEnergy β p d / v ^ d) *
            ∏ j ∈ block, ((if z j then (1 : ℝ) else 0) - p)) ^ 2) =
        2 * (d : ℝ) * blockEnergy β p d
    rw [show (fun z : Fin n → Bool =>
        (Real.sqrt
            (2 * (d : ℝ) * blockEnergy β p d / v ^ d) *
          ∏ j ∈ block, ((if z j then (1 : ℝ) else 0) - p)) ^ 2) =
      (fun z : Fin n → Bool =>
        (Real.sqrt
          (2 * (d : ℝ) * blockEnergy β p d / v ^ d)) ^ 2 *
          ((∏ j ∈ block,
            ((if z j then (1 : ℝ) else 0) - p)) *
           (∏ j ∈ block,
            ((if z j then (1 : ℝ) else 0) - p)))) by
      funext z
      ring]
    rw [FiniteDesign.E_const_mul,
      E_global_centeredMonomial_mul p
        (le_of_lt hp0) (le_of_lt hp1) block block,
      if_pos rfl, Real.sq_sqrt hfrac]
    rw [show block.card = d by
      exact completeBlockUnits_card n d hd hdiv _]
    dsimp [v]
    have hvpow : (p * (1 - p)) ^ d ≠ 0 :=
      pow_ne_zero d (mul_ne_zero hp0.ne' (sub_pos.mpr hp1).ne')
    field_simp [hvpow]
  · simp

/-- Establishes the stated mathematical result for orthogonal witness weights distance energy. -/
lemma orthogonalWitnessWeights_distance_energy
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (hhigh : β < d) :
    ∑ i : Fin n,
      (bernoulliDesign (fun _ : Fin n => p)
        (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
        (fun z =>
          ((orthogonalWitnessWeights
              n d β p hβ hp0 hp1 hn hd hdiv).weight i z -
            (canonicalLocLinWeights
              n d β p hp0 hp1 hn hd hdiv).weight i z) ^ 2) =
      (blockCount n d : ℝ) * (2 * (d : ℝ) * blockEnergy β p d) := by
  classical
  rw [← sum_completeBlockUnits n d hd hdiv
    (fun i =>
      (bernoulliDesign (fun _ : Fin n => p)
        (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
        (fun z =>
          ((orthogonalWitnessWeights
              n d β p hβ hp0 hp1 hn hd hdiv).weight i z -
            (canonicalLocLinWeights
              n d β p hp0 hp1 hn hd hdiv).weight i z) ^ 2))]
  rw [show
      (∑ b : Fin (blockCount n d),
        ∑ i ∈ completeBlockUnits n d b,
          (bernoulliDesign (fun _ : Fin n => p)
            (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
            (fun z =>
              ((orthogonalWitnessWeights
                  n d β p hβ hp0 hp1 hn hd hdiv).weight i z -
                (canonicalLocLinWeights
                  n d β p hp0 hp1 hn hd hdiv).weight i z) ^ 2)) =
      ∑ _b : Fin (blockCount n d),
        2 * (d : ℝ) * blockEnergy β p d by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_eq_single (blockFirstUnit n d hd hdiv b)]
    · have hidx :
          completeBlockIndex n d hd hdiv
              (blockFirstUnit n d hd hdiv b) = b := by
        apply Fin.ext
        change b.val * d / d = b.val
        rw [Nat.mul_comm]
        exact Nat.mul_div_cancel_left b.val (by omega : 0 < d)
      simp only [orthogonalWitnessWeights, add_sub_cancel_left]
      rw [orthogonalBlockPerturb_energy
        n d β p hβ hp0 hp1 hn hd hdiv hhigh]
      simp [hidx]
    · intro i hi hne
      simp only [orthogonalWitnessWeights, add_sub_cancel_left]
      rw [orthogonalBlockPerturb_energy
        n d β p hβ hp0 hp1 hn hd hdiv hhigh]
      have hidx : completeBlockIndex n d hd hdiv i = b := by
        apply Fin.ext
        exact (Finset.mem_filter.mp hi).2.2
      simp [hidx, hne]
    · intro hnot
      exact (hnot
        (blockFirstUnit_mem_completeBlockUnits n d hd hdiv b)).elim]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- Establishes the stated mathematical result for monomial mul sq energy le. -/
lemma monomial_mul_sq_energy_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (u : (V → Bool) → ℝ) (S : Finset V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z =>
        (u z * ∏ j ∈ S, if z j then (1 : ℝ) else 0) ^ 2) ≤
      (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
        (fun _ => hp1)).E (fun z => u z ^ 2) := by
  let D := bernoulliDesign (fun _ : V => p)
    (fun _ => hp0) (fun _ => hp1)
  have hpoint (z : V → Bool) :
      (u z * ∏ j ∈ S, if z j then (1 : ℝ) else 0) ^ 2 ≤ u z ^ 2 := by
    have hm0 :
        0 ≤ ∏ j ∈ S, if z j then (1 : ℝ) else 0 := by
      apply Finset.prod_nonneg
      intro j hj
      split <;> positivity
    have hm1 :
        (∏ j ∈ S, if z j then (1 : ℝ) else 0) ≤ 1 := by
      apply Finset.prod_le_one
      · intro j hj
        split <;> positivity
      · intro j hj
        split <;> simp_all
    have hmsq :
        (∏ j ∈ S, if z j then (1 : ℝ) else 0) ^ 2 ≤ 1 :=
      by simpa [pow_two] using mul_self_le_mul_self hm0 hm1
    nlinarith [sq_nonneg (u z)]
  have hn := D.E_nonneg (fun z => sub_nonneg.mpr (hpoint z))
  rw [FiniteDesign.E_sub] at hn
  exact sub_nonneg.mp hn

/-- Establishes the stated mathematical result for orthogonal witness block extremal upper. -/
lemma orthogonalWitness_blockExtremal_upper
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (hhigh : β < d) (b : Fin (blockCount n d)) :
    blockExtremal (blockGraph n d) d β p
        (le_of_lt hp0) (le_of_lt hp1)
        (orthogonalWitnessWeights n d β p hβ hp0 hp1 hn hd hdiv)
        (completeBlockUnits n d b) ≤
      (d : ℝ) ^ 2 * blockEnergy β p d +
        2 * Real.sqrt ((d : ℝ) ^ 2 * blockEnergy β p d) *
          Real.sqrt (2 * (d : ℝ) * blockEnergy β p d) +
        2 * (d : ℝ) * blockEnergy β p d := by
  classical
  let D := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)
  let w0 := canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv
  let w := orthogonalWitnessWeights n d β p hβ hp0 hp1 hn hd hdiv
  let i0 := blockFirstUnit n d hd hdiv b
  unfold blockExtremal
  dsimp only
  apply Finset.sup'_le
  intro choice hchoiceMem
  have hchoice :
      ∀ i ∈ completeBlockUnits n d b,
        choice.2 i ⊆ completeBlockUnits n d b ∧
          (choice.2 i).card ≤ effBeta β d := by
    simpa using hchoiceMem
  let f : (Fin n → Bool) → ℝ := fun z =>
    ∑ i ∈ completeBlockUnits n d b,
      (if choice.1 i then (1 : ℝ) else -1) *
        locLinUnitError w0 i (choice.2 i) z
  let g : (Fin n → Bool) → ℝ := fun z =>
    ∑ i ∈ completeBlockUnits n d b,
      (if choice.1 i then (1 : ℝ) else -1) *
        (orthogonalBlockPerturb n d β p hβ hp0 hp1 hn hd hdiv i z *
          ∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0)
  have hf :
      D.E (fun z => f z ^ 2) ≤
        (d : ℝ) ^ 2 * blockEnergy β p d := by
    calc
      D.E (fun z => f z ^ 2) ≤
          blockExtremal (blockGraph n d) d β p
            (le_of_lt hp0) (le_of_lt hp1) w0
            (completeBlockUnits n d b) := by
        unfold blockExtremal
        dsimp only
        convert Finset.le_sup'
          (f := fun choice =>
            D.E (fun z =>
              (∑ i ∈ completeBlockUnits n d b,
                (if choice.1 i then (1 : ℝ) else -1) *
                  locLinUnitError w0 i (choice.2 i) z) ^ 2))
          hchoiceMem using 1
      _ ≤ (d : ℝ) ^ 2 * blockEnergy β p d :=
        canonical_completeBlock_blockExtremal_upper
          n d β p hp0 hp1 hn hd hdiv b
  have hgfun :
      g = fun z =>
        (if choice.1 i0 then (1 : ℝ) else -1) *
          (orthogonalBlockPerturb
              n d β p hβ hp0 hp1 hn hd hdiv i0 z *
            ∏ j ∈ choice.2 i0, if z j then (1 : ℝ) else 0) := by
    funext z
    dsimp [g, i0]
    rw [Finset.sum_eq_single (blockFirstUnit n d hd hdiv b)]
    · intro i hi hne
      have hidx : completeBlockIndex n d hd hdiv i = b := by
        apply Fin.ext
        exact (Finset.mem_filter.mp hi).2.2
      have hnot :
          i ≠ blockFirstUnit n d hd hdiv
            (completeBlockIndex n d hd hdiv i) := by
        simpa [hidx] using hne
      simp [orthogonalBlockPerturb, hhigh, hnot]
    · intro hnot
      exact (hnot
        (blockFirstUnit_mem_completeBlockUnits n d hd hdiv b)).elim
  have hg :
      D.E (fun z => g z ^ 2) ≤
        2 * (d : ℝ) * blockEnergy β p d := by
    rw [hgfun]
    have hmono := monomial_mul_sq_energy_le p
      (le_of_lt hp0) (le_of_lt hp1)
      (orthogonalBlockPerturb
        n d β p hβ hp0 hp1 hn hd hdiv i0) (choice.2 i0)
    have hsign :
        (fun z =>
          ((if choice.1 i0 then (1 : ℝ) else -1) *
            (orthogonalBlockPerturb
                n d β p hβ hp0 hp1 hn hd hdiv i0 z *
              ∏ j ∈ choice.2 i0, if z j then (1 : ℝ) else 0)) ^ 2) =
        (fun z =>
          (orthogonalBlockPerturb
              n d β p hβ hp0 hp1 hn hd hdiv i0 z *
            ∏ j ∈ choice.2 i0, if z j then (1 : ℝ) else 0) ^ 2) := by
      funext z
      split <;> ring
    rw [hsign]
    calc
      D.E (fun z =>
          (orthogonalBlockPerturb
              n d β p hβ hp0 hp1 hn hd hdiv i0 z *
            ∏ j ∈ choice.2 i0, if z j then (1 : ℝ) else 0) ^ 2) ≤
          D.E (fun z =>
            orthogonalBlockPerturb
              n d β p hβ hp0 hp1 hn hd hdiv i0 z ^ 2) := hmono
      _ = 2 * (d : ℝ) * blockEnergy β p d := by
        rw [orthogonalBlockPerturb_energy
          n d β p hβ hp0 hp1 hn hd hdiv hhigh]
        have hidx :
            completeBlockIndex n d hd hdiv i0 = b := by
          apply Fin.ext
          dsimp [i0]
          change b.val * d / d = b.val
          rw [Nat.mul_comm]
          exact Nat.mul_div_cancel_left b.val (by omega : 0 < d)
        simp [i0, hidx]
  have hA : 0 < blockEnergy β p d :=
    blockEnergy_pos β d p hβ hd hp0 hp1
  have hA0 : 0 ≤ (d : ℝ) ^ 2 * blockEnergy β p d :=
    mul_nonneg (sq_nonneg _) hA.le
  have hG0 : 0 ≤ 2 * (d : ℝ) * blockEnergy β p d :=
    mul_nonneg (by positivity) hA.le
  have hadd := finiteDesign_E_add_sq_le D f g
    ((d : ℝ) ^ 2 * blockEnergy β p d)
    (2 * (d : ℝ) * blockEnergy β p d) hf hg hA0 hG0
  convert hadd using 1
  apply FiniteDesign.E_congr
  intro z
  congr 1
  dsimp [f, g, w, w0, orthogonalWitnessWeights, locLinUnitError]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The first unit of a complete block is unchanged when the population size, block size,
divisibility condition, and block label are replaced by equal values. -/
add_decl_doc blockFirstUnit.congr_simp

/-- The canonical local-linear weights for complete blocks are unchanged when all design,
block-structure, and admissibility inputs are replaced by equal values. -/
add_decl_doc canonicalLocLinWeights.congr_simp

/-- The orthogonal block perturbation is unchanged when its design parameters, block
conditions, unit, and assignment are replaced by equal values. -/
add_decl_doc orthogonalBlockPerturb.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
