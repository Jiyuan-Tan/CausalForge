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
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part7

/-!
# Excess of the complete-block extremal value, and score relabelling

Bounds the excess of the blockwise extremal value over its canonical value by the
weight distance, and records the invariance of the SNIPE score under relabelling.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Establishes the stated mathematical result for complete block extremal excess le distance. -/
lemma completeBlockExtremal_excess_le_distance
    (n d β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p
      (le_of_lt hp0) (le_of_lt hp1)) :
    ∑ b : Fin (blockCount n d),
        (blockExtremal (blockGraph n d) d β p
            (le_of_lt hp0) (le_of_lt hp1) w
            (completeBlockUnits n d b) -
          (d : ℝ) ^ 2 * blockEnergy β p d) ≤
      2 * Real.sqrt ((d : ℝ) ^ 2 * blockEnergy β p d) *
          Real.sqrt (blockCount n d : ℝ) *
          Real.sqrt ((d : ℝ) *
            ∑ i : Fin n,
              (bernoulliDesign (fun _ : Fin n => p)
                (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
                (fun z =>
                  (w.weight i z -
                    (canonicalLocLinWeights
                      n d β p hp0 hp1 hn hd hdiv).weight i z) ^ 2)) +
        (d : ℝ) *
          ∑ i : Fin n,
            (bernoulliDesign (fun _ : Fin n => p)
              (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
              (fun z =>
                (w.weight i z -
                  (canonicalLocLinWeights
                    n d β p hp0 hp1 hn hd hdiv).weight i z) ^ 2) := by
  classical
  let D := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)
  let w0 := canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv
  let e : Fin (blockCount n d) → ℝ := fun b =>
    ∑ i ∈ completeBlockUnits n d b,
      D.E (fun z => (w.weight i z - w0.weight i z) ^ 2)
  let Etotal : ℝ :=
    ∑ i : Fin n, D.E (fun z => (w.weight i z - w0.weight i z) ^ 2)
  have he0 (b : Fin (blockCount n d)) : 0 ≤ e b := by
    dsimp [e]
    apply Finset.sum_nonneg
    intro i hi
    exact D.E_nonneg (fun z => sq_nonneg _)
  have hEtot : ∑ b : Fin (blockCount n d), e b = Etotal := by
    dsimp [e, Etotal]
    exact sum_completeBlockUnits n d hd hdiv
      (fun i => D.E (fun z => (w.weight i z - w0.weight i z) ^ 2))
  have hsqrt :
      ∑ b : Fin (blockCount n d), Real.sqrt ((d : ℝ) * e b) ≤
        Real.sqrt (blockCount n d : ℝ) *
          Real.sqrt ((d : ℝ) * Etotal) := by
    calc
      ∑ b : Fin (blockCount n d), Real.sqrt ((d : ℝ) * e b) =
          ∑ b ∈ (Finset.univ : Finset (Fin (blockCount n d))),
            (1 : ℝ) * Real.sqrt ((d : ℝ) * e b) := by simp
      _ ≤ Real.sqrt
            (∑ b ∈ (Finset.univ : Finset (Fin (blockCount n d))),
              (1 : ℝ) ^ 2) *
          Real.sqrt
            (∑ b ∈ (Finset.univ : Finset (Fin (blockCount n d))),
              Real.sqrt ((d : ℝ) * e b) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (Fin (blockCount n d)))
          (fun _ => (1 : ℝ))
          (fun b => Real.sqrt ((d : ℝ) * e b))
      _ = Real.sqrt (blockCount n d : ℝ) *
          Real.sqrt ((d : ℝ) * Etotal) := by
        congr 2
        · simp
        · rw [show
            (∑ b ∈ (Finset.univ : Finset (Fin (blockCount n d))),
              Real.sqrt ((d : ℝ) * e b) ^ 2) =
              ∑ b : Fin (blockCount n d), (d : ℝ) * e b by
            apply Finset.sum_congr rfl
            intro b hb
            rw [Real.sq_sqrt (mul_nonneg (by positivity) (he0 b))]]
          rw [← Finset.mul_sum, hEtot]
  calc
    ∑ b : Fin (blockCount n d),
        (blockExtremal (blockGraph n d) d β p
            (le_of_lt hp0) (le_of_lt hp1) w
            (completeBlockUnits n d b) -
          (d : ℝ) ^ 2 * blockEnergy β p d) ≤
        ∑ b : Fin (blockCount n d),
          (2 * Real.sqrt ((d : ℝ) ^ 2 * blockEnergy β p d) *
              Real.sqrt ((d : ℝ) * e b) +
            (d : ℝ) * e b) := by
      apply Finset.sum_le_sum
      intro b hb
      have h := blockExtremal_le_of_weight_distance
        n d β p hp0 hp1 hn hd hdiv w b
      dsimp [e, D, w0] at h ⊢
      linarith
    _ = 2 * Real.sqrt ((d : ℝ) ^ 2 * blockEnergy β p d) *
          (∑ b : Fin (blockCount n d),
            Real.sqrt ((d : ℝ) * e b)) +
        (d : ℝ) * Etotal := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hEtot]
    _ ≤ 2 * Real.sqrt ((d : ℝ) ^ 2 * blockEnergy β p d) *
          (Real.sqrt (blockCount n d : ℝ) *
            Real.sqrt ((d : ℝ) * Etotal)) +
        (d : ℝ) * Etotal := by
      gcongr
    _ = 2 * Real.sqrt ((d : ℝ) ^ 2 * blockEnergy β p d) *
          Real.sqrt (blockCount n d : ℝ) *
          Real.sqrt ((d : ℝ) * Etotal) +
        (d : ℝ) * Etotal := by ring

/-- Establishes the stated mathematical result for snipe score relabel. -/
lemma snipeScore_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) [DecidableRel G]
    (π : V ≃ V) (hG : ∀ j i, G (π j) (π i) ↔ G j i)
    (β : ℕ) (p : ℝ) (i : V) (z : V → Bool) :
    snipeScore (fun j i => decide (G j i)) β p (π i)
        (fun j => z (π.symm j)) =
      snipeScore (fun j i => decide (G j i)) β p i z := by
  classical
  let N := nbhdB (fun j i => decide (G j i)) i
  have hN :
      nbhdB (fun j i => decide (G j i)) (π i) =
        N.map π.toEmbedding := by
    ext k
    simp only [nbhdB, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro hk
      refine ⟨π.symm k, ?_, by simp⟩
      dsimp [N]
      simp only [nbhdB, Finset.mem_filter, Finset.mem_univ, true_and]
      apply decide_eq_true_eq.mpr
      exact (hG (π.symm k) i).mp
        (decide_eq_true_eq.mp (by simpa using hk))
    · rintro ⟨j, hj, rfl⟩
      dsimp [N] at hj
      simp only [nbhdB, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      apply decide_eq_true_eq.mpr
      exact (hG j i).mpr (decide_eq_true_eq.mp hj)
  unfold snipeScore
  rw [hN]
  change
    (∑ r ∈ Finset.Icc 1 (effBeta β (N.map π.toEmbedding).card),
      (bernoulliContrast p r / (p * (1 - p)) ^ r) *
        ∑ S ∈ (N.map π.toEmbedding).powerset.filter
            (fun S => S.card = r),
          ∏ j ∈ S,
            ((if z (π.symm j) then (1 : ℝ) else 0) - p)) =
      ∑ r ∈ Finset.Icc 1 (effBeta β N.card),
        (bernoulliContrast p r / (p * (1 - p)) ^ r) *
          ∑ S ∈ N.powerset.filter (fun S => S.card = r),
            ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)
  rw [Finset.card_map]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply Finset.sum_bij
      (fun S (_hS :
        S ∈ (N.map π.toEmbedding).powerset.filter
          (fun S => S.card = r)) =>
        S.map π.symm.toEmbedding)
  · intro S hS
    have hSmem := Finset.mem_filter.mp hS
    have hSsub := Finset.mem_powerset.mp hSmem.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro j hj
      obtain ⟨k, hkS, hkj⟩ := Finset.mem_map.mp hj
      subst j
      have hkMap := hSsub hkS
      obtain ⟨j, hjN, hjk⟩ := Finset.mem_map.mp hkMap
      have : j = π.symm k := by
        apply π.injective
        simpa using hjk
      simpa [this] using hjN
    · simpa using hSmem.2
  · intro S hS T hT hmap
    apply Finset.map_injective
      (f := π.symm.toEmbedding)
    exact hmap
  · intro T hT
    refine ⟨T.map π.toEmbedding, ?_, ?_⟩
    · have hTmem := Finset.mem_filter.mp hT
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powerset.mpr
        intro k hk
        obtain ⟨j, hjT, rfl⟩ := Finset.mem_map.mp hk
        exact Finset.mem_map.mpr ⟨j,
          Finset.mem_powerset.mp hTmem.1 hjT, rfl⟩
      · simpa using hTmem.2
    · ext j
      simp
  · intro S hS
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro j hj
    simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
