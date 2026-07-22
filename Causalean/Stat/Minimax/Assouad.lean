/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Assouad's lemma — the hypercube minimax lower bound

Where Le Cam (`LeCam.lean`) packs *two* hypotheses and Fano (`Fano.lean`) packs
*many pairwise-separated* ones, **Assouad's lemma** packs a hypercube
`{P τ : τ ∈ (Fin d → Bool)}` indexed by the `d`-dimensional Boolean cube, in which
*each coordinate* is an independent two-point test.  This converts a `d`-fold product
structure into a `d`-fold sum of testing lower bounds, yielding rates that grow with
the dimension `d`.

A "cube estimator" `est : Ω → (Fin d → Bool)` decodes each coordinate.  Its expected
**Hamming risk** at vertex `τ` is

  `hammingRisk P est τ = ∑ⱼ (P τ).real {ω | est ω j ≠ τ j}`,

the expected number of mis-decoded coordinates.  Assouad's lemma states that, *on
average over the cube*,

  `(d / 2) · (1 − β) ≤ (1 / |cube|) ∑_τ hammingRisk P est τ`,

where `β` bounds the total variation `tvDist (P τ) (P (flip j τ))` between any vertex
and its `j`-th neighbour.  Equivalently, **some** vertex forces Hamming risk
`≥ (d/2)(1 − β)`.

The proof is the coordinate-flip averaging argument: pairing each vertex `τ` with its
`j`-flip `flip j τ` via an involution, the two coordinate-`j` error masses are
`(P τ).real S + (P (flip j τ)).real Sᶜ` for `S = {ω | est ω j ≠ τ j}`, which the
elementary testing bound `one_sub_tvDist_le_test` lower-bounds by
`1 − tvDist (P τ) (P (flip j τ))`.  Summing over the cube and over coordinates and
dividing by `|cube|` gives the result.  Like Fano, this is proven **unconditionally**
— no entropy or product-measure machinery — with the divergence entering only through
`tvDist`.

## Main results

* `flipBit`, `flipPerm` — flip the `j`-th coordinate of a cube vertex (an involution).
* `hammingRisk` — expected number of mis-decoded coordinates.
* `assouad_average` — `(d/2)(1 − β) ≤` average Hamming risk over the cube.
* `assouad_exists` — some vertex forces Hamming risk `≥ (d/2)(1 − β)`.
-/

import Causalean.Stat.Minimax.LeCam

/-! # Assouad hypercube bound

This module proves Assouad's minimax lower bound for experiments indexed by a
Boolean hypercube.  It defines the coordinate flip operations `flipBit` and
`flipPerm`, the Hamming-risk functional `hammingRisk`, and proves the
coordinate pairing lemmas culminating in `assouad_average` and
`assouad_exists`, which turn uniform total-variation control between neighboring
vertices into average and worst-case Hamming-risk lower bounds.
-/

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- Flip the `j`-th coordinate of a cube vertex `τ : Fin d → Bool`. -/
def flipBit (j : Fin d) (τ : Fin d → Bool) : Fin d → Bool :=
  Function.update τ j (!τ j)

/-- Flipping a coordinate changes that coordinate to the opposite Boolean value. -/
@[simp] theorem flipBit_self (j : Fin d) (τ : Fin d → Bool) : flipBit j τ j = !τ j :=
  Function.update_self _ _ _

/-- Flipping the same coordinate twice is the identity. -/
theorem flipBit_involutive (j : Fin d) : Function.Involutive (flipBit j) := by
  intro τ
  funext k
  by_cases h : k = j
  · subst h; simp [flipBit]
  · simp [flipBit, Function.update_of_ne h]

/-- The coordinate flip as a permutation of the cube, used to reindex sums. -/
def flipPerm (j : Fin d) : Equiv.Perm (Fin d → Bool) :=
  ⟨flipBit j, flipBit j, flipBit_involutive j, flipBit_involutive j⟩

/-- The coordinate-flip permutation acts by flipping that coordinate. -/
@[simp] theorem flipPerm_apply (j : Fin d) (τ : Fin d → Bool) :
    flipPerm j τ = flipBit j τ := rfl

/-- The expected **Hamming risk** of a cube estimator at vertex `τ`:
the expected number of coordinates it decodes incorrectly. -/
noncomputable def hammingRisk (P : (Fin d → Bool) → Measure Ω)
    (est : Ω → Fin d → Bool) (τ : Fin d → Bool) : ℝ :=
  ∑ j, (P τ).real {ω | est ω j ≠ τ j}

variable (P : (Fin d → Bool) → Measure Ω) [∀ τ, IsProbabilityMeasure (P τ)]
  (est : Ω → Fin d → Bool)

/-- Coordinate-decoding error sets are measurable, being complements of the
measurable level sets `{ω | est ω j = b}`. -/
theorem measurableSet_decode_ne (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    (j : Fin d) (b : Bool) : MeasurableSet {ω | est ω j ≠ b} := by
  have h : {ω | est ω j ≠ b} = {ω | est ω j = b}ᶜ := by ext ω; simp
  rw [h]; exact (hmeas j b).compl

/-- The `j`-th decoding-error set at the flipped vertex is the complement of the
one at `τ`: the estimator's `j`-th bit either matches `τ j` or its flip, never both. -/
theorem decode_ne_flip_compl (j : Fin d) (τ : Fin d → Bool) :
    {ω | est ω j ≠ (flipBit j τ) j} = {ω | est ω j ≠ τ j}ᶜ := by
  have boollem : ∀ a b : Bool, (a ≠ !b) ↔ (a = b) := by decide
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, flipBit_self, not_not]
  exact boollem (est ω j) (τ j)

/-- **Per-coordinate pair bound.** For each vertex `τ`, the coordinate-`j` error mass
at `τ` plus the one at its `j`-flip is at least `1 − tvDist (P τ) (P (flip j τ))`.
This is the two-point testing bound applied to the `j`-th decoded bit. -/
theorem hammingRisk_pair_ge (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    (j : Fin d) (τ : Fin d → Bool) :
    1 - tvDist (P τ) (P (flipBit j τ))
      ≤ (P τ).real {ω | est ω j ≠ τ j}
        + (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j} := by
  have hS : MeasurableSet {ω | est ω j ≠ τ j} := measurableSet_decode_ne est hmeas j (τ j)
  rw [decode_ne_flip_compl est j τ]
  exact one_sub_tvDist_le_test (μ := P τ) (ν := P (flipBit j τ)) hS

/-- **Per-coordinate lower bound.** Summed over the cube, the coordinate-`j` error mass
is at least half the cube-sum of `1 − tvDist (P τ) (P (flip j τ))`, via pairing each
vertex with its `j`-flip (an involution that preserves the sum). -/
theorem sum_decode_ge (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    (j : Fin d) :
    ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ)))
      ≤ 2 * ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by
  -- Reindexing by the `j`-flip permutation leaves the cube-sum invariant.
  have hreindex :
      ∑ τ, (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j}
        = ∑ τ, (P τ).real {ω | est ω j ≠ τ j} :=
    Equiv.sum_comp (flipPerm j) (fun σ => (P σ).real {ω | est ω j ≠ σ j})
  calc ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ)))
      ≤ ∑ τ, ((P τ).real {ω | est ω j ≠ τ j}
            + (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j}) :=
        Finset.sum_le_sum (fun τ _ => hammingRisk_pair_ge P est hmeas j τ)
    _ = (∑ τ, (P τ).real {ω | est ω j ≠ τ j})
          + ∑ τ, (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j} :=
        Finset.sum_add_distrib
    _ = 2 * ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by rw [hreindex]; ring

/-- **Assouad's lemma (average form).** If every vertex is within total variation `β`
of each of its `d` neighbours, the average Hamming risk over the cube is at least
`(d / 2)(1 − β)`.  Choosing the dimension `d` large and the per-coordinate divergence
`β` small forces a large number of mis-decoded coordinates. -/
theorem assouad_average (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    {β : ℝ} (hβ : ∀ j τ, tvDist (P τ) (P (flipBit j τ)) ≤ β) :
    (d / 2 : ℝ) * (1 - β)
      ≤ (∑ τ, hammingRisk P est τ) / (Fintype.card (Fin d → Bool)) := by
  set C : ℝ := (Fintype.card (Fin d → Bool) : ℝ) with hC
  have hCnat : 0 < Fintype.card (Fin d → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have hCpos : (0 : ℝ) < C := by rw [hC]; exact_mod_cast hCnat
  -- Per coordinate: `C·(1−β)/2 ≤ ∑_τ (coordinate-j error mass)`.
  have hG : ∀ j, C * (1 - β) / 2 ≤ ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by
    intro j
    have hcoord := sum_decode_ge P est hmeas j
    have hβsum : C * (1 - β) ≤ ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ))) := by
      have h1 : ∑ _τ : Fin d → Bool, (1 - β)
          ≤ ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ))) :=
        Finset.sum_le_sum (fun τ _ => by linarith [hβ j τ])
      have h2 : ∑ _τ : Fin d → Bool, (1 - β) = C * (1 - β) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hC]
      linarith [h1, h2]
    linarith [hβsum, hcoord]
  -- Sum the coordinate bounds, then divide by the cube size.
  have hswap : ∑ τ, hammingRisk P est τ
      = ∑ j, ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by
    simp_rw [hammingRisk]; rw [Finset.sum_comm]
  have hfinal : (d : ℝ) * (C * (1 - β) / 2) ≤ ∑ τ, hammingRisk P est τ := by
    rw [hswap]
    have h2 : (d : ℝ) * (C * (1 - β) / 2) = ∑ _j : Fin d, (C * (1 - β) / 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h2]
    exact Finset.sum_le_sum (fun j _ => hG j)
  rw [le_div_iff₀ hCpos]
  have hrw : (d / 2 : ℝ) * (1 - β) * C = (d : ℝ) * (C * (1 - β) / 2) := by ring
  rw [hrw]; exact hfinal

/-- **Assouad's lemma (existence form).** Under the same hypotheses, *some* vertex `τ`
forces Hamming risk at least `(d / 2)(1 − β)`: no cube estimator can decode every
vertex's coordinates reliably when neighbouring laws are statistically close. -/
theorem assouad_exists (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    {β : ℝ} (hβ : ∀ j τ, tvDist (P τ) (P (flipBit j τ)) ≤ β) :
    ∃ τ, (d / 2 : ℝ) * (1 - β) ≤ hammingRisk P est τ := by
  set C : ℝ := (Fintype.card (Fin d → Bool) : ℝ) with hC
  have hCnat : 0 < Fintype.card (Fin d → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have hCpos : (0 : ℝ) < C := by rw [hC]; exact_mod_cast hCnat
  have havg := assouad_average P est hmeas hβ
  rw [← hC] at havg
  by_contra hcon
  push_neg at hcon
  have hstrict : ∑ τ, hammingRisk P est τ < C * ((d / 2 : ℝ) * (1 - β)) := by
    calc ∑ τ, hammingRisk P est τ
        < ∑ _τ : Fin d → Bool, ((d / 2 : ℝ) * (1 - β)) :=
          Finset.sum_lt_sum_of_nonempty ⟨fun _ => false, Finset.mem_univ _⟩
            (fun τ _ => hcon τ)
      _ = C * ((d / 2 : ℝ) * (1 - β)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hC]
  rw [le_div_iff₀ hCpos] at havg
  nlinarith [havg, hstrict]

end Causalean.Stat
