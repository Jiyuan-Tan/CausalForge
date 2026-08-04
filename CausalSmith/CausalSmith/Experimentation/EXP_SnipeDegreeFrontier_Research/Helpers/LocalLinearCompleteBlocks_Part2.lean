import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearClass
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part1

/-!
# The complete-block extremal value: lower and upper bounds

Identifies the units of a complete block with a graph neighbourhood and pins the
blockwise extremal value from both sides, the upper bound being attained by the
canonical weights.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Establishes the stated mathematical result for block extremal all empty le. -/
lemma blockExtremal_all_empty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) (d β : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights G d β p hp0 hp1) (block : Finset V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
        (fun z => (∑ i ∈ block, w.weight i z) ^ 2) ≤
      blockExtremal G d β p hp0 hp1 w block := by
  classical
  unfold blockExtremal
  dsimp only
  convert Finset.le_sup'
    (s := Finset.univ.filter (fun choice =>
      ∀ i ∈ block,
        choice.2 i ⊆ block ∧ (choice.2 i).card ≤ effBeta β d))
    (f := fun choice =>
      (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
        (fun _ => hp1)).E
          (fun z =>
            (∑ i ∈ block, (if choice.1 i then (1 : ℝ) else -1) *
              (w.weight i z *
                (∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0) -
                  if (choice.2 i).Nonempty then 1 else 0)) ^ 2))
    (b := ((fun _ => true), (fun _ => ∅)))
    (by simp) using 1
  apply FiniteDesign.E_congr
  intro z
  simp

/-- Establishes the stated mathematical result for block first unit mem complete block units. -/
lemma blockFirstUnit_mem_completeBlockUnits
    (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (b : Fin (blockCount n d)) :
    blockFirstUnit n d hd hdiv b ∈ completeBlockUnits n d b := by
  have hactive : activeCount n d = n := activeCount_eq_of_dvd n d hdiv
  simp only [completeBlockUnits, Finset.mem_filter, Finset.mem_univ,
    true_and, blockFirstUnit]
  constructor
  · rw [hactive]
    exact (blockFirstUnit n d hd hdiv b).isLt
  · rw [Nat.mul_div_left]
    omega

/-- Establishes the stated mathematical result for complete block units eq nbhd. -/
lemma completeBlockUnits_eq_nbhd
    (n d : ℕ) (hdiv : d ∣ n)
    (b : Fin (blockCount n d)) (i : Fin n)
    (hi : i ∈ completeBlockUnits n d b) :
    completeBlockUnits n d b = nbhd (blockGraph n d) i := by
  have hactive : activeCount n d = n := activeCount_eq_of_dvd n d hdiv
  have hib := (Finset.mem_filter.mp hi).2.2
  ext j
  simp [completeBlockUnits, nbhd, blockGraph, hactive, i.isLt, j.isLt, hib]

/-- Establishes the stated mathematical result for complete block units card. -/
lemma completeBlockUnits_card
    (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (b : Fin (blockCount n d)) :
    (completeBlockUnits n d b).card = d := by
  rw [completeBlockUnits_eq_nbhd n d hdiv b
    (blockFirstUnit n d hd hdiv b)
    (blockFirstUnit_mem_completeBlockUnits n d hd hdiv b)]
  exact blockGraph_nbhd_card n d hd hdiv _

/-- Establishes the stated mathematical result for snipe score eq of nbhd eq. -/
lemma snipeScore_eq_of_nbhd_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) [DecidableRel G]
    (β : ℕ) (p : ℝ) (i k : V)
    (hN : nbhd G i = nbhd G k) :
    snipeScore (fun j i => decide (G j i)) β p i =
      snipeScore (fun j i => decide (G j i)) β p k := by
  classical
  have hNB :
      nbhdB (fun j i => decide (G j i)) i =
        nbhdB (fun j i => decide (G j i)) k := by
    ext j
    simpa [nbhdB, nbhd] using Finset.ext_iff.mp hN j
  unfold snipeScore
  rw [hNB]

/-- Establishes the stated mathematical result for complete block block extremal lower. -/
lemma completeBlock_blockExtremal_lower
    (n d β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p
      (le_of_lt hp0) (le_of_lt hp1))
    (b : Fin (blockCount n d)) :
    (d : ℝ) ^ 2 * blockEnergy β p d ≤
      blockExtremal (blockGraph n d) d β p
        (le_of_lt hp0) (le_of_lt hp1) w
        (completeBlockUnits n d b) := by
  classical
  let D := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)
  let i₀ := blockFirstUnit n d hd hdiv b
  let g : (Fin n → Bool) → ℝ :=
    snipeScore (fun j i => decide (blockGraph n d j i)) β p i₀
  have hi₀ : i₀ ∈ completeBlockUnits n d b :=
    blockFirstUnit_mem_completeBlockUnits n d hd hdiv b
  have hblockcard : (completeBlockUnits n d b).card = d :=
    completeBlockUnits_card n d hd hdiv b
  have hN₀ :
      nbhd (blockGraph n d) i₀ = completeBlockUnits n d b :=
    (completeBlockUnits_eq_nbhd n d hdiv b i₀ hi₀).symm
  have hgg : D.E (fun z => g z ^ 2) = blockEnergy β p d := by
    dsimp [D, g]
    rw [snipeScore_sq_expectation_global
      (hp0 := hp0) (hp1 := hp1)]
    congr 1
    rw [show
        nbhdB (fun j i => decide (blockGraph n d j i)) i₀ =
          nbhd (blockGraph n d) i₀ by
      ext j
      simp [nbhdB, nbhd]]
    rw [hN₀, hblockcard]
  have hpair (i : Fin n) (hi : i ∈ completeBlockUnits n d b) :
      D.E (fun z => w.weight i z * g z) = blockEnergy β p d := by
    have hNi :
        nbhd (blockGraph n d) i = completeBlockUnits n d b :=
      (completeBlockUnits_eq_nbhd n d hdiv b i hi).symm
    have hscore :
        snipeScore (fun j i => decide (blockGraph n d j i)) β p i = g := by
      dsimp [g]
      exact snipeScore_eq_of_nbhd_eq
        (blockGraph n d) β p i i₀ (hNi.trans hN₀.symm)
    rw [← hscore]
    exact locLinWeight_snipeScore_pair
      (blockGraph n d) d β p (le_of_lt hp0) (le_of_lt hp1)
      w i (by rw [hNi, hblockcard])
  have hsumPair :
      D.E (fun z => (∑ i ∈ completeBlockUnits n d b, w.weight i z) * g z) =
        (d : ℝ) * blockEnergy β p d := by
    rw [show (fun z =>
        (∑ i ∈ completeBlockUnits n d b, w.weight i z) * g z) =
      (fun z => ∑ i ∈ completeBlockUnits n d b,
        w.weight i z * g z) by
      funext z
      rw [Finset.sum_mul]]
    rw [FiniteDesign.E_sum]
    rw [show
        (∑ i ∈ completeBlockUnits n d b,
          D.E (fun z => w.weight i z * g z)) =
        ∑ _i ∈ completeBlockUnits n d b, blockEnergy β p d by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpair i hi]
    rw [Finset.sum_const, hblockcard]
    simp
  have hsq :
      D.E (fun z =>
        ((∑ i ∈ completeBlockUnits n d b, w.weight i z) -
          (d : ℝ) * g z) ^ 2) =
        D.E (fun z =>
          (∑ i ∈ completeBlockUnits n d b, w.weight i z) ^ 2) -
          (d : ℝ) ^ 2 * blockEnergy β p d := by
    rw [show (fun z =>
        ((∑ i ∈ completeBlockUnits n d b, w.weight i z) -
          (d : ℝ) * g z) ^ 2) =
      (fun z =>
        (∑ i ∈ completeBlockUnits n d b, w.weight i z) ^ 2 -
          2 * (d : ℝ) *
            ((∑ i ∈ completeBlockUnits n d b, w.weight i z) * g z) +
          (d : ℝ) ^ 2 * g z ^ 2) by
      funext z
      ring]
    rw [FiniteDesign.E_add, FiniteDesign.E_sub,
      FiniteDesign.E_const_mul, FiniteDesign.E_const_mul,
      hsumPair, hgg]
    ring
  have hnneg := D.E_nonneg (fun z => sq_nonneg
    ((∑ i ∈ completeBlockUnits n d b, w.weight i z) -
      (d : ℝ) * g z))
  rw [hsq] at hnneg
  have hlower :
      (d : ℝ) ^ 2 * blockEnergy β p d ≤
        D.E (fun z =>
          (∑ i ∈ completeBlockUnits n d b, w.weight i z) ^ 2) := by
    linarith
  exact hlower.trans (by
    simpa [D] using blockExtremal_all_empty_le
      (blockGraph n d) d β p (le_of_lt hp0) (le_of_lt hp1) w
      (completeBlockUnits n d b))

/-- Establishes the stated mathematical result for canonical complete block block extremal upper. -/
lemma canonical_completeBlock_blockExtremal_upper
    (n d β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (b : Fin (blockCount n d)) :
    blockExtremal (blockGraph n d) d β p
        (le_of_lt hp0) (le_of_lt hp1)
        (canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv)
        (completeBlockUnits n d b) ≤
      (d : ℝ) ^ 2 * blockEnergy β p d := by
  classical
  let D := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)
  let w := canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv
  let i₀ := blockFirstUnit n d hd hdiv b
  let g : (Fin n → Bool) → ℝ := w.weight i₀
  have hi₀ : i₀ ∈ completeBlockUnits n d b :=
    blockFirstUnit_mem_completeBlockUnits n d hd hdiv b
  have hblockcard : (completeBlockUnits n d b).card = d :=
    completeBlockUnits_card n d hd hdiv b
  have hN₀ :
      nbhd (blockGraph n d) i₀ = completeBlockUnits n d b :=
    (completeBlockUnits_eq_nbhd n d hdiv b i₀ hi₀).symm
  have hweight (i : Fin n) (hi : i ∈ completeBlockUnits n d b) :
      w.weight i = g := by
    dsimp [w, g, canonicalLocLinWeights]
    exact snipeScore_eq_of_nbhd_eq
      (blockGraph n d) β p i i₀
      ((completeBlockUnits_eq_nbhd n d hdiv b i hi).symm.trans
        hN₀.symm)
  have hgg : D.E (fun z => g z ^ 2) = blockEnergy β p d := by
    dsimp [D, g, w]
    exact canonicalLocLinWeights_energy n d β p hp0 hp1 hn hd hdiv i₀
  unfold blockExtremal
  dsimp only
  apply Finset.sup'_le
  intro choice hchoice
  have hc :
      ∀ i ∈ completeBlockUnits n d b,
        choice.2 i ⊆ completeBlockUnits n d b ∧
          (choice.2 i).card ≤ effBeta β d := by
    simpa using hchoice
  let f : (Fin n → Bool) → ℝ := fun z =>
    ∑ i ∈ completeBlockUnits n d b,
      (if choice.1 i then (1 : ℝ) else -1) *
        ∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0
  let L : ℝ :=
    ∑ i ∈ completeBlockUnits n d b,
      (if choice.1 i then (1 : ℝ) else -1) *
        if (choice.2 i).Nonempty then 1 else 0
  have hmean : D.E (fun z => g z * f z) = L := by
    rw [show (fun z => g z * f z) =
        (fun z => ∑ i ∈ completeBlockUnits n d b,
          (if choice.1 i then (1 : ℝ) else -1) *
            (g z *
              ∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0)) by
      funext z
      dsimp [f]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [FiniteDesign.E_sum]
    simp_rw [FiniteDesign.E_const_mul]
    dsimp [L]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [← hweight i hi]
    by_cases hSne : (choice.2 i).Nonempty
    · rw [if_pos hSne]
      exact w.moment_one i (choice.2 i) hSne
        (((hc i hi).1).trans (by
          rw [completeBlockUnits_eq_nbhd n d hdiv b i hi]))
        (hc i hi).2
    · rw [if_neg hSne]
      have hSe : choice.2 i = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hSne
      rw [hSe]
      simpa using w.mean_zero i
  have hfsq (z : Fin n → Bool) : f z ^ 2 ≤ (d : ℝ) ^ 2 := by
    have habs : |f z| ≤ (d : ℝ) := by
      calc
        |f z| ≤
            ∑ i ∈ completeBlockUnits n d b,
              |(if choice.1 i then (1 : ℝ) else -1) *
                ∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0| := by
          dsimp [f]
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ completeBlockUnits n d b, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          have hsign :
              |(if choice.1 i then (1 : ℝ) else -1)| = 1 := by
            by_cases h : choice.1 i <;> simp [h]
          rw [hsign, one_mul]
          have hmono0 :
              0 ≤ ∏ j ∈ choice.2 i,
                if z j then (1 : ℝ) else 0 := by
            apply Finset.prod_nonneg
            intro j hj
            by_cases hz : z j <;> simp [hz]
          rw [abs_of_nonneg hmono0]
          apply Finset.prod_le_one
          · intro j hj
            by_cases hz : z j <;> simp [hz]
          · intro j hj
            by_cases hz : z j <;> simp [hz]
        _ = (d : ℝ) := by
          rw [Finset.sum_const, hblockcard]
          simp
    have hd0 : 0 ≤ (d : ℝ) := by positivity
    have hmul := mul_self_le_mul_self (abs_nonneg (f z)) habs
    simpa [pow_two] using hmul
  have hgf :
      D.E (fun z => (g z * f z) ^ 2) ≤
        (d : ℝ) ^ 2 * blockEnergy β p d := by
    have hpoint (z : Fin n → Bool) :
        0 ≤ (d : ℝ) ^ 2 * g z ^ 2 - (g z * f z) ^ 2 := by
      have := hfsq z
      nlinarith [sq_nonneg (g z)]
    have hn := D.E_nonneg hpoint
    rw [FiniteDesign.E_sub, FiniteDesign.E_const_mul, hgg] at hn
    linarith
  have hvar :
      D.E (fun z => (g z * f z - L) ^ 2) ≤
        D.E (fun z => (g z * f z) ^ 2) := by
    rw [show (fun z => (g z * f z - L) ^ 2) =
        (fun z => (g z * f z) ^ 2 - 2 * L * (g z * f z) + L ^ 2) by
      funext z
      ring]
    rw [FiniteDesign.E_add, FiniteDesign.E_sub,
      FiniteDesign.E_const_mul, FiniteDesign.E_const, hmean]
    nlinarith [sq_nonneg L]
  calc
    D.E (fun z =>
      (∑ i ∈ completeBlockUnits n d b,
        (if choice.1 i then (1 : ℝ) else -1) *
          (w.weight i z *
            (∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0) -
              if (choice.2 i).Nonempty then 1 else 0)) ^ 2) =
        D.E (fun z => (g z * f z - L) ^ 2) := by
      apply FiniteDesign.E_congr
      intro z
      congr 1
      dsimp [f, L]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hweight i hi]
      ring
    _ ≤ D.E (fun z => (g z * f z) ^ 2) := hvar
    _ ≤ (d : ℝ) ^ 2 * blockEnergy β p d := hgf

end CausalSmith.Experimentation.SnipeDegreeFrontier
