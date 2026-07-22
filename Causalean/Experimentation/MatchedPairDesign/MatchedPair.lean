/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bai (2022): the matched-pair design

This file formalizes the fixed-pair matched-pair randomization design from Bai (2022), "Optimality
of Matched-Pair Designs in Randomized Controlled Trials" (American Economic Review).  Units are
organized into pairs indexed by `P`; within each pair the two members occupy the two positions
`Bool`, and the experiment treats exactly one position per pair, chosen by an independent fair coin.
This is a product of pair-level fair-coin designs, read so that the coin selects the treated
position.  It is not independent assignment over the `2|P|` units: within each size-two stratum
exactly one unit is treated.

This file records the matched-pair design and its **inclusion structure**: each unit is treated with
probability `½`; the two units of a pair are *perfectly negatively dependent* (exactly one is
treated); and units in different pairs are treated independently.  It does not compare alternative
pairings or prove an optimal matching theorem.
-/

import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Mathlib.Tactic.NormNum

/-! # Matched-pair designs

Matched-pair designs organize units into pairs indexed by `P`, with the two members of each pair
represented by positions `Bool`.  The assignment `z p` is a pair-level fair coin selecting the
treated position, so this is not independent assignment over the `2|P|` units: each size-two stratum
treats exactly one unit.

This file defines the fair coin `pairCoinDesign`, the product design `matchedPairDesign`, and the
treatment indicator `mpTreatInd`.  The main inclusion results prove within-pair exclusivity,
first-order inclusion probability `1/2`, perfect within-pair negative dependence, and cross-pair
independence with joint probability `1/4`.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace MatchedPairDesign

open DesignBased

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The per-pair fair coin: `true` means the `true` position is treated, and `false` means the
`false` position is treated. -/
noncomputable def pairCoinDesign : FiniteDesign Bool :=
  coinDesign ((1 : ℝ) / 2) (by norm_num) (by norm_num)

/-- The **matched-pair design**: each pair `p` independently treats one of its two positions by a
fair coin.  The assignment `z p : Bool` is the treated position in pair `p`; the other position is
control.  This is a size-two stratified design with one treated unit per stratum, represented in the
smaller assignment space of treated positions rather than as independent unit-level assignments. -/
noncomputable def matchedPairDesign : FiniteDesign (P → Bool) :=
  prodDesign (fun _ : P => pairCoinDesign)

/-- The matched-pair design is the product of the independent pair-level fair coins. -/
lemma matchedPairDesign_eq_prod_pairCoin :
    matchedPairDesign (P := P) = prodDesign (fun _ : P => pairCoinDesign) := rfl

/-- The treatment indicator of the unit at position `b` of pair `p` under assignment `z`: `1` if the
coin selected position `b`, else `0`. -/
def mpTreatInd (p : P) (b : Bool) (z : P → Bool) : ℝ := if z p = b then 1 else 0

omit [Fintype P] [DecidableEq P] in
/-- **Within-pair exclusivity.** Exactly one position of each pair is treated: the two units'
indicators sum to one on every assignment. -/
lemma mpTreatInd_within (p : P) (z : P → Bool) :
    mpTreatInd p true z + mpTreatInd p false z = 1 := by
  unfold mpTreatInd
  cases z p <;> simp

/-- **First-order inclusion probability.** Every unit is treated with probability `½`. -/
lemma matchedPairDesign_E_mpTreatInd (p : P) (b : Bool) :
    (matchedPairDesign (P := P)).E (mpTreatInd p b) = 1 / 2 := by
  change (prodDesign (fun _ : P => pairCoinDesign)).E
      (fun z => (fun c : Bool => if c = b then (1 : ℝ) else 0) (z p)) = 1 / 2
  rw [FiniteDesign.E_prod_apply (fun _ : P => pairCoinDesign) p
      (fun c : Bool => if c = b then (1 : ℝ) else 0)]
  unfold pairCoinDesign
  rw [coinDesign_E]
  cases b <;> norm_num

/-- **Within-pair negative dependence.** The two units of a pair are never treated together, so the
product of their indicators has expectation zero — perfect negative dependence. -/
lemma matchedPairDesign_E_mpTreatInd_within (p : P) :
    (matchedPairDesign (P := P)).E (fun z => mpTreatInd p true z * mpTreatInd p false z) = 0 := by
  have hzero : ∀ z : P → Bool, mpTreatInd p true z * mpTreatInd p false z = 0 := by
    intro z
    unfold mpTreatInd
    cases z p <;> simp
  rw [(matchedPairDesign (P := P)).E_congr hzero]
  exact (matchedPairDesign (P := P)).E_const 0

/-- **Cross-pair independence.** Units in distinct pairs `p ≠ p'` are treated independently, so the
joint treatment probability factors as `½ · ½ = ¼`. -/
lemma matchedPairDesign_E_mpTreatInd_cross (p p' : P) (h : p ≠ p') (b b' : Bool) :
    (matchedPairDesign (P := P)).E (fun z => mpTreatInd p b z * mpTreatInd p' b' z) = 1 / 4 := by
  change (prodDesign (fun _ : P => pairCoinDesign)).E
      (fun z => (fun c : Bool => if c = b then (1 : ℝ) else 0) (z p) *
        (fun c : Bool => if c = b' then (1 : ℝ) else 0) (z p')) = 1 / 4
  rw [FiniteDesign.E_prod_apply₂
      (fun _ : P => pairCoinDesign) h
      (fun c : Bool => if c = b then (1 : ℝ) else 0)
      (fun c : Bool => if c = b' then (1 : ℝ) else 0)]
  unfold pairCoinDesign
  rw [coinDesign_E, coinDesign_E]
  cases b <;> cases b' <;> norm_num

end MatchedPairDesign
end Experimentation
end Causalean
