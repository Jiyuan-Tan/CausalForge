import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenter
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable

/-!
# Exact block-local linear constant and representer characterization

The population at each index is the standard disjoint union of complete
directed blocks.  The theorem states the exact finite minimax constant, the
finite extreme-point risk formula, the asymptotic excess criterion, and the
distance-two non-necessity witness.
-/

open scoped BigOperators Topology
open Filter Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

/-- The units in a typed active block. -/
noncomputable def blockUnits
    (n d : ℕ) (b : Fin (blockCount n d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < activeCount n d ∧ i.val / d = b.val)

/-- The canonical complete-block score viewed on the global assignment. -/
noncomputable def canonicalBlockScore
    (n d β : ℕ) (p : ℝ) (i : Fin n) (z : Fin n → Bool) : ℝ :=
  by
    classical
    exact snipeScore
      (fun j i => decide (blockGraph n d j i)) β p i z

/-- Worst-risk ratio relative to the exact block benchmark. -/
noncomputable def locLinRiskRatio
    (n d β : ℕ) (B p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1) : ℝ :=
  locLinWorstRisk (blockGraph n d) d β B p hp0 hp1 w /
    (B ^ 2 * blockEnergy β p d / blockCount n d)

/-- Normalized sum of per-block extremal excesses. -/
noncomputable def normalizedBlockExcess
    (n d β : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1) : ℝ :=
  ((blockCount n d : ℝ) * d ^ 2 * blockEnergy β p d)⁻¹ *
    ∑ b : Fin (blockCount n d),
      (blockExtremal (blockGraph n d) d β p hp0 hp1 w (blockUnits n d b) -
        d ^ 2 * blockEnergy β p d)

/-- Normalized average squared distance from canonical SNIPE weights. -/
noncomputable def normalizedWeightDistance
    (n d β : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1) : ℝ :=
  ((n : ℝ) * blockEnergy β p d)⁻¹ *
    ∑ i : Fin n,
      (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0) (fun _ => hp1)).E
        (fun z => (w.weight i z - canonicalBlockScore n d β p i z) ^ 2)

/-- Distance to a caller-supplied relabeling of the symmetric canonical
complete-block score. -/
noncomputable def normalizedWeightDistanceRelabeled
    (n d β : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : LocLinWeights (blockGraph n d) d β p hp0 hp1)
    (π : Fin n ≃ Fin n) : ℝ :=
  ((n : ℝ) * blockEnergy β p d)⁻¹ *
    ∑ i : Fin n,
      (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0) (fun _ => hp1)).E
        (fun z =>
          (w.weight i z -
            canonicalBlockScore n d β p (π i) (fun j => z (π.symm j))) ^ 2)

/-- When the population splits exactly into complete blocks of size `d` (so `d` divides
`n`), a local-linear weighting's worst-case risk relative to the exact block benchmark
equals one plus the normalized total of the per-block extremal excesses. In other words,
the risk ratio exceeds one by exactly the amount — measured in units of the benchmark —
by which the blocks' worst-case contributions overshoot the benchmark value they would
attain under the canonical block weights.

This turns the finite minimax constant into a per-block accounting identity: bounding the
block excesses bounds the ratio, and the ratio is one exactly when the excesses cancel. -/
lemma locLinRiskRatio_eq_one_add_normalizedBlockExcess
    (n d β : ℕ) (B p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1) (hB : 0 < B)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p
      (le_of_lt hp0) (le_of_lt hp1)) :
    locLinRiskRatio n d β B p (le_of_lt hp0) (le_of_lt hp1) w =
      1 + normalizedBlockExcess n d β p
        (le_of_lt hp0) (le_of_lt hp1) w := by
  rw [locLinRiskRatio, locLinWorstRisk_exact_blockExtremal
    n d β B p hB (le_of_lt hp0) (le_of_lt hp1) hn hd hdiv w]
  unfold normalizedBlockExcess
  rw [show blockUnits n d = completeBlockUnits n d by rfl]
  have hA : 0 < blockEnergy β p d :=
    blockEnergy_pos β d p hβ hd hp0 hp1
  have hq : 0 < blockCount n d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv)
      (Nat.zero_lt_of_lt hd)
  have hncast :
      (n : ℝ) = (blockCount n d : ℝ) * (d : ℝ) := by
    norm_cast
    simpa [blockCount, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
  rw [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  rw [hncast]
  have hBr : B ≠ 0 := hB.ne'
  have hAr : blockEnergy β p d ≠ 0 := hA.ne'
  have hqr : (blockCount n d : ℝ) ≠ 0 := by positivity
  have hdr : (d : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Establishes the stated mathematical result for normalized sqrt excess identity. -/
lemma normalized_sqrt_excess_identity
    (q d n : ℕ) (A E : ℝ)
    (hq : 1 ≤ q) (hd : 1 ≤ d) (hn : n = q * d)
    (hA : 0 < A) (hE : 0 ≤ E) :
    ((q : ℝ) * (d : ℝ) ^ 2 * A)⁻¹ *
        (2 * Real.sqrt ((d : ℝ) ^ 2 * A) *
            Real.sqrt (q : ℝ) * Real.sqrt ((d : ℝ) * E) +
          (d : ℝ) * E) =
      2 * Real.sqrt (((n : ℝ) * A)⁻¹ * E) +
        ((n : ℝ) * A)⁻¹ * E := by
  have hqr : 0 < (q : ℝ) := by positivity
  have hdr : 0 < (d : ℝ) := by positivity
  have hnr : (n : ℝ) = (q : ℝ) * (d : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by rw [hnr]; positivity
  have hsqrtq : Real.sqrt (q : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hqr).ne'
  have hsqrtd : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hdr).ne'
  have hsqrtA : Real.sqrt A ≠ 0 :=
    (Real.sqrt_pos.2 hA).ne'
  rw [Real.sqrt_mul (sq_nonneg (d : ℝ)) A,
    Real.sqrt_sq_eq_abs, abs_of_pos hdr]
  have hsqrtqd :
      Real.sqrt (q : ℝ) * Real.sqrt ((d : ℝ) * E) =
        Real.sqrt ((n : ℝ) * E) := by
    rw [← Real.sqrt_mul hqr.le]
    congr 1
    rw [hnr]
    ring
  rw [show
      2 * ((d : ℝ) * Real.sqrt A) * Real.sqrt (q : ℝ) *
          Real.sqrt ((d : ℝ) * E) =
        2 * (d : ℝ) * Real.sqrt A * Real.sqrt ((n : ℝ) * E) by
    rw [← hsqrtqd]
    ring]
  rw [Real.sqrt_mul hnpos.le E]
  rw [show ((n : ℝ) * A)⁻¹ * E = E / ((n : ℝ) * A) by
    field_simp]
  rw [Real.sqrt_div hE ((n : ℝ) * A),
    Real.sqrt_mul hnpos.le A]
  rw [hnr]
  rw [Real.sqrt_mul hqr.le (d : ℝ)]
  have hsqrtq_sq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt hqr.le
  have hsqrtd_sq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt hdr.le
  have hsqrtA_sq : Real.sqrt A ^ 2 = A :=
    Real.sq_sqrt hA.le
  field_simp [hsqrtq, hsqrtd, hsqrtA]
  rw [← hsqrtq_sq, ← hsqrtd_sq, ← hsqrtA_sq]
  simp only [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Establishes the stated mathematical result for canonical block score relabel within blocks. -/
lemma canonicalBlockScore_relabel_within_blocks
    (n d β : ℕ) (p : ℝ) (hdiv : d ∣ n)
    (π : Fin n ≃ Fin n)
    (hπ : ∀ i, (π i).val / d = i.val / d)
    (i : Fin n) (z : Fin n → Bool) :
    canonicalBlockScore n d β p (π i) (fun j => z (π.symm j)) =
      canonicalBlockScore n d β p i z := by
  classical
  unfold canonicalBlockScore
  apply snipeScore_relabel (blockGraph n d) π
  intro j k
  have hactive : activeCount n d = n :=
    activeCount_eq_of_dvd n d hdiv
  simp only [blockGraph, hactive, j.isLt, k.isLt, (π j).isLt, (π k).isLt,
    true_and]
  rw [hπ j, hπ k]

/-- Establishes the stated mathematical result for risk ratio tendsto iff normalized block excess. -/
lemma riskRatio_tendsto_iff_normalizedBlockExcess
    (β : ℕ) (p B : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hB : 0 < B)
    (n d : ℕ → ℕ)
    (hn : ∀ t, 1 ≤ n t) (hd : ∀ t, 1 ≤ d t)
    (hdiv : ∀ t, d t ∣ n t)
    (w : ∀ t, LocLinWeights (blockGraph (n t) (d t)) (d t) β p
      (le_of_lt hp0) (le_of_lt hp1)) :
    Tendsto (fun t => locLinRiskRatio (n t) (d t) β B p
        (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 1) ↔
    Tendsto (fun t => normalizedBlockExcess (n t) (d t) β p
        (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 0) := by
  have hid (t : ℕ) :
      locLinRiskRatio (n t) (d t) β B p
          (le_of_lt hp0) (le_of_lt hp1) (w t) =
        1 + normalizedBlockExcess (n t) (d t) β p
          (le_of_lt hp0) (le_of_lt hp1) (w t) :=
    locLinRiskRatio_eq_one_add_normalizedBlockExcess
      (n t) (d t) β B p hβ hp0 hp1 hB
      (hn t) (hd t) (hdiv t) (w t)
  constructor
  · intro h
    have hs := h.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    convert hs using 1
    · funext t
      rw [hid t]
      ring
    · ring
  · intro h
    have hs :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add h
    convert hs using 1
    · funext t
      exact hid t
    · ring

/-- Establishes the stated mathematical result for normalized weight distance tendsto implies risk ratio. -/
lemma normalizedWeightDistance_tendsto_implies_riskRatio
    (β : ℕ) (p B : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hB : 0 < B)
    (n d : ℕ → ℕ)
    (hn : ∀ t, 1 ≤ n t) (hd : ∀ t, 1 ≤ d t)
    (hdiv : ∀ t, d t ∣ n t)
    (w : ∀ t, LocLinWeights (blockGraph (n t) (d t)) (d t) β p
      (le_of_lt hp0) (le_of_lt hp1))
    (hdist :
      Tendsto (fun t => normalizedWeightDistance (n t) (d t) β p
        (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 0)) :
    Tendsto (fun t => locLinRiskRatio (n t) (d t) β B p
        (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 1) := by
  let x : ℕ → ℝ := fun t =>
    normalizedWeightDistance (n t) (d t) β p
      (le_of_lt hp0) (le_of_lt hp1) (w t)
  let y : ℕ → ℝ := fun t =>
    normalizedBlockExcess (n t) (d t) β p
      (le_of_lt hp0) (le_of_lt hp1) (w t)
  have hx : Tendsto x atTop (𝓝 0) := hdist
  have hy0 (t : ℕ) : 0 ≤ y t := by
    dsimp [y, normalizedBlockExcess]
    apply mul_nonneg
    · apply inv_nonneg.mpr
      exact mul_nonneg
        (mul_nonneg (by positivity) (sq_nonneg _))
        (blockEnergy_pos β (d t) p hβ (hd t) hp0 hp1).le
    · apply Finset.sum_nonneg
      intro b hb
      exact sub_nonneg.mpr (by
        simpa [blockUnits, completeBlockUnits] using
          completeBlock_blockExtremal_lower
            (n t) (d t) β p hp0 hp1 (hn t) (hd t) (hdiv t)
            (w t) b)
  have hyupper (t : ℕ) :
      y t ≤ 2 * Real.sqrt (x t) + x t := by
    let A := blockEnergy β p (d t)
    let Etotal :=
      ∑ i : Fin (n t),
        (bernoulliDesign (fun _ : Fin (n t) => p)
          (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
          (fun z =>
            ((w t).weight i z -
              (canonicalLocLinWeights (n t) (d t) β p hp0 hp1
                (hn t) (hd t) (hdiv t)).weight i z) ^ 2)
    have hA : 0 < A :=
      blockEnergy_pos β (d t) p hβ (hd t) hp0 hp1
    have hq : 1 ≤ blockCount (n t) (d t) := by
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
        (Nat.div_pos
          (Nat.le_of_dvd (Nat.zero_lt_of_lt (hn t)) (hdiv t))
          (Nat.zero_lt_of_lt (hd t))))
    have hE : 0 ≤ Etotal := by
      dsimp [Etotal]
      apply Finset.sum_nonneg
      intro i hi
      exact (bernoulliDesign (fun _ : Fin (n t) => p)
        (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E_nonneg
        (fun z => sq_nonneg _)
    have hraw := completeBlockExtremal_excess_le_distance
      (n t) (d t) β p hp0 hp1 (hn t) (hd t) (hdiv t) (w t)
    have hden :
        0 ≤ ((blockCount (n t) (d t) : ℝ) *
          (d t : ℝ) ^ 2 * A)⁻¹ := by positivity
    calc
      y t =
          ((blockCount (n t) (d t) : ℝ) *
            (d t : ℝ) ^ 2 * A)⁻¹ *
            ∑ b : Fin (blockCount (n t) (d t)),
              (blockExtremal (blockGraph (n t) (d t)) (d t) β p
                  (le_of_lt hp0) (le_of_lt hp1) (w t)
                  (completeBlockUnits (n t) (d t) b) -
                (d t : ℝ) ^ 2 * A) := by
        rfl
      _ ≤ ((blockCount (n t) (d t) : ℝ) *
            (d t : ℝ) ^ 2 * A)⁻¹ *
          (2 * Real.sqrt ((d t : ℝ) ^ 2 * A) *
              Real.sqrt (blockCount (n t) (d t) : ℝ) *
              Real.sqrt ((d t : ℝ) * Etotal) +
            (d t : ℝ) * Etotal) :=
        mul_le_mul_of_nonneg_left (by simpa [A, Etotal] using hraw) hden
      _ = 2 * Real.sqrt (x t) + x t := by
        rw [normalized_sqrt_excess_identity
          (blockCount (n t) (d t)) (d t) (n t) A Etotal
          hq (hd t) (by
            simpa [blockCount, Nat.mul_comm] using
              (Nat.div_mul_cancel (hdiv t)).symm) hA hE]
        rfl
  have hsqrt :
      Tendsto (fun t => Real.sqrt (x t)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp hx
  have hu :
      Tendsto (fun t => 2 * Real.sqrt (x t) + x t) atTop (𝓝 0) := by
    convert (hsqrt.const_mul 2).add hx using 1 <;> ring
  have hy : Tendsto y atTop (𝓝 0) :=
    squeeze_zero hy0 hyupper hu
  have hrisk :
      (fun t => locLinRiskRatio (n t) (d t) β B p
        (le_of_lt hp0) (le_of_lt hp1) (w t)) =
      fun t => 1 + y t := by
    funext t
    exact locLinRiskRatio_eq_one_add_normalizedBlockExcess
      (n t) (d t) β B p hβ hp0 hp1 hB
      (hn t) (hd t) (hdiv t) (w t)
  rw [hrisk]
  convert
    ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hy) using 1 <;>
    ring

/-- Establishes the stated mathematical result for orthogonal witness normalized distance eq two. -/
lemma orthogonalWitness_normalized_distance_eq_two
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (hhigh : β < d) :
    normalizedWeightDistance n d β p
        (le_of_lt hp0) (le_of_lt hp1)
        (orthogonalWitnessWeights n d β p hβ hp0 hp1 hn hd hdiv) = 2 := by
  classical
  unfold normalizedWeightDistance canonicalBlockScore
  rw [show
      (∑ i : Fin n,
        (bernoulliDesign (fun _ : Fin n => p)
          (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
          (fun z =>
            ((orthogonalWitnessWeights
                n d β p hβ hp0 hp1 hn hd hdiv).weight i z -
              snipeScore
                (fun j i => decide (blockGraph n d j i)) β p i z) ^ 2)) =
      (blockCount n d : ℝ) *
        (2 * (d : ℝ) * blockEnergy β p d) by
    exact orthogonalWitnessWeights_distance_energy
      n d β p hβ hp0 hp1 hn hd hdiv hhigh]
  have hA : 0 < blockEnergy β p d :=
    blockEnergy_pos β d p hβ hd hp0 hp1
  have hq : 0 < blockCount n d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv)
      (Nat.zero_lt_of_lt hd)
  have hncast :
      (n : ℝ) = (blockCount n d : ℝ) * (d : ℝ) := by
    norm_cast
    simpa [blockCount, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
  rw [hncast]
  have hqr : (blockCount n d : ℝ) ≠ 0 := by positivity
  have hdr : (d : ℝ) ≠ 0 := by positivity
  have hAr : blockEnergy β p d ≠ 0 := hA.ne'
  field_simp

/-- Establishes the stated mathematical result for orthogonal witness normalized relabel distance eq two. -/
lemma orthogonalWitness_normalized_relabel_distance_eq_two
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (hhigh : β < d)
    (π : Fin n ≃ Fin n)
    (hπ : ∀ i, (π i).val / d = i.val / d) :
    normalizedWeightDistanceRelabeled n d β p
        (le_of_lt hp0) (le_of_lt hp1)
        (orthogonalWitnessWeights n d β p hβ hp0 hp1 hn hd hdiv) π = 2 := by
  unfold normalizedWeightDistanceRelabeled
  rw [show
      (∑ i : Fin n,
        (bernoulliDesign (fun _ : Fin n => p)
          (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
          (fun z =>
            ((orthogonalWitnessWeights
                n d β p hβ hp0 hp1 hn hd hdiv).weight i z -
              canonicalBlockScore n d β p (π i)
                (fun j => z (π.symm j))) ^ 2)) =
      ∑ i : Fin n,
        (bernoulliDesign (fun _ : Fin n => p)
          (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
          (fun z =>
            ((orthogonalWitnessWeights
                n d β p hβ hp0 hp1 hn hd hdiv).weight i z -
              canonicalBlockScore n d β p i z) ^ 2) by
    apply Finset.sum_congr rfl
    intro i hi
    apply FiniteDesign.E_congr
    intro z
    rw [canonicalBlockScore_relabel_within_blocks
      n d β p hdiv π hπ i z]]
  exact orthogonalWitness_normalized_distance_eq_two
    n d β p hβ hp0 hp1 hn hd hdiv hhigh

/-- Establishes the stated mathematical result for orthogonal witness risk ratio tendsto one. -/
lemma orthogonalWitness_riskRatio_tendsto_one
    (β : ℕ) (p B : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hB : 0 < B)
    (n d : ℕ → ℕ)
    (hn : ∀ t, 1 ≤ n t) (hd : ∀ t, 1 ≤ d t)
    (hdiv : ∀ t, d t ∣ n t)
    (hdtop : Tendsto d atTop atTop) :
    Tendsto (fun t =>
      locLinRiskRatio (n t) (d t) β B p
        (le_of_lt hp0) (le_of_lt hp1)
        (orthogonalWitnessWeights (n t) (d t) β p hβ hp0 hp1
          (hn t) (hd t) (hdiv t))) atTop (𝓝 1) := by
  let w : ∀ t, LocLinWeights (blockGraph (n t) (d t)) (d t) β p
      (le_of_lt hp0) (le_of_lt hp1) := fun t =>
    orthogonalWitnessWeights (n t) (d t) β p hβ hp0 hp1
      (hn t) (hd t) (hdiv t)
  let x : ℕ → ℝ := fun t => ((d t : ℝ))⁻¹
  have hdreal : Tendsto (fun t => (d t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdtop
  have hx : Tendsto x atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hdreal
  have hx2 : Tendsto (fun t => 2 * x t) atTop (𝓝 0) := by
    convert hx.const_mul 2 using 1 <;> ring
  have hsqrt :
      Tendsto (fun t => Real.sqrt (2 * x t)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp hx2
  have hu :
      Tendsto (fun t => 1 + 2 * Real.sqrt (2 * x t) + 2 * x t)
        atTop (𝓝 1) := by
    convert
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
          (hsqrt.const_mul 2) |>.add hx2) using 1 <;> ring
  have hhigh : ∀ᶠ t in atTop, β < d t := by
    filter_upwards [tendsto_atTop.1 hdtop (β + 1)] with t ht
    omega
  have hlower (t : ℕ) :
      1 ≤ locLinRiskRatio (n t) (d t) β B p
        (le_of_lt hp0) (le_of_lt hp1) (w t) := by
    rw [locLinRiskRatio_eq_one_add_normalizedBlockExcess
      (n t) (d t) β B p hβ hp0 hp1 hB
      (hn t) (hd t) (hdiv t) (w t)]
    have hcoef :
        0 ≤ ((blockCount (n t) (d t) : ℝ) * (d t : ℝ) ^ 2 *
          blockEnergy β p (d t))⁻¹ := by
      apply inv_nonneg.mpr
      exact mul_nonneg
        (mul_nonneg (by positivity) (sq_nonneg _))
        (blockEnergy_pos β (d t) p hβ (hd t) hp0 hp1).le
    unfold normalizedBlockExcess
    rw [show blockUnits (n t) (d t) =
      completeBlockUnits (n t) (d t) by rfl]
    have hsum :
        0 ≤ ∑ b : Fin (blockCount (n t) (d t)),
          (blockExtremal (blockGraph (n t) (d t)) (d t) β p
              (le_of_lt hp0) (le_of_lt hp1) (w t)
              (completeBlockUnits (n t) (d t) b) -
            (d t : ℝ) ^ 2 * blockEnergy β p (d t)) := by
      apply Finset.sum_nonneg
      intro b hb
      exact sub_nonneg.mpr
        (completeBlock_blockExtremal_lower
          (n t) (d t) β p hp0 hp1 (hn t) (hd t) (hdiv t) (w t) b)
    nlinarith [mul_nonneg hcoef hsum]
  have hupper :
      ∀ᶠ t in atTop,
        locLinRiskRatio (n t) (d t) β B p
            (le_of_lt hp0) (le_of_lt hp1) (w t) ≤
          1 + 2 * Real.sqrt (2 * x t) + 2 * x t := by
    filter_upwards [hhigh] with t hdt
    rw [locLinRiskRatio_eq_one_add_normalizedBlockExcess
      (n t) (d t) β B p hβ hp0 hp1 hB
      (hn t) (hd t) (hdiv t) (w t)]
    unfold normalizedBlockExcess
    rw [show blockUnits (n t) (d t) =
      completeBlockUnits (n t) (d t) by rfl]
    let A := blockEnergy β p (d t)
    let C :=
      2 * Real.sqrt ((d t : ℝ) ^ 2 * A) *
          Real.sqrt (2 * (d t : ℝ) * A) +
        2 * (d t : ℝ) * A
    have hA : 0 < A :=
      blockEnergy_pos β (d t) p hβ (hd t) hp0 hp1
    have hb (b : Fin (blockCount (n t) (d t))) :
        blockExtremal (blockGraph (n t) (d t)) (d t) β p
            (le_of_lt hp0) (le_of_lt hp1) (w t)
            (completeBlockUnits (n t) (d t) b) -
            (d t : ℝ) ^ 2 * A ≤ C := by
      have hbound := orthogonalWitness_blockExtremal_upper
        (n t) (d t) β p hβ hp0 hp1 (hn t) (hd t) (hdiv t) hdt b
      dsimp [w, A, C] at hbound ⊢
      linarith
    have hsum :
        ∑ b : Fin (blockCount (n t) (d t)),
          (blockExtremal (blockGraph (n t) (d t)) (d t) β p
              (le_of_lt hp0) (le_of_lt hp1) (w t)
              (completeBlockUnits (n t) (d t) b) -
            (d t : ℝ) ^ 2 * A) ≤
          (blockCount (n t) (d t) : ℝ) * C := by
      calc
        _ ≤ ∑ _b : Fin (blockCount (n t) (d t)), C := by
          apply Finset.sum_le_sum
          intro b hbmem
          exact hb b
        _ = _ := by simp
    have hq : 1 ≤ blockCount (n t) (d t) := by
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
        (Nat.div_pos
          (Nat.le_of_dvd (Nat.zero_lt_of_lt (hn t)) (hdiv t))
          (Nat.zero_lt_of_lt (hd t))))
    have hid := normalized_sqrt_excess_identity
      1 (d t) (d t) A (2 * A) (by omega) (hd t)
      (by simp) hA (by positivity)
    have hq0 : (blockCount (n t) (d t) : ℝ) ≠ 0 := by positivity
    have hd0 : (d t : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt (hd t)))
    calc
      1 + ((blockCount (n t) (d t) : ℝ) *
            (d t : ℝ) ^ 2 * A)⁻¹ *
          ∑ b : Fin (blockCount (n t) (d t)),
            (blockExtremal (blockGraph (n t) (d t)) (d t) β p
                (le_of_lt hp0) (le_of_lt hp1) (w t)
                (completeBlockUnits (n t) (d t) b) -
              (d t : ℝ) ^ 2 * A) ≤
          1 + ((blockCount (n t) (d t) : ℝ) *
            (d t : ℝ) ^ 2 * A)⁻¹ *
            ((blockCount (n t) (d t) : ℝ) * C) := by
        gcongr
      _ = 1 + ((d t : ℝ) ^ 2 * A)⁻¹ * C := by
        field_simp [hq0, hd0, hA.ne']
      _ = 1 + 2 * Real.sqrt (2 * x t) + 2 * x t := by
        have hCeq :
            C =
              2 * Real.sqrt ((d t : ℝ) ^ 2 * A) *
                  Real.sqrt (1 : ℝ) *
                  Real.sqrt ((d t : ℝ) * (2 * A)) +
                (d t : ℝ) * (2 * A) := by
          dsimp [C]
          rw [show
            2 * (d t : ℝ) * A = (d t : ℝ) * (2 * A) by ring,
            Real.sqrt_one]
          ring
        rw [hCeq]
        simp only [Real.sqrt_one, mul_one]
        simp only [Nat.cast_one, one_mul, Real.sqrt_one, mul_one] at hid
        rw [hid]
        have hin :
            ((d t : ℝ) * A)⁻¹ * (2 * A) =
              2 * (d t : ℝ)⁻¹ := by
          field_simp [hd0, hA.ne']
        rw [hin]
        dsimp [x]
        ring
  exact Filter.Tendsto.squeeze'
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    hu (Eventually.of_forall hlower) hupper

/-- Exact finite minimaxity and the full asymptotic representer
characterization on complete blocks. -/
-- @node: thm:sharp-local-linear-constant-and-representers
theorem sharp_local_linear_constant_and_representers
    (β : ℕ) (p B : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hB : 0 < B)
    (n d : ℕ → ℕ)
    (D : ∀ t, FiniteDesign (Fin (n t) → Bool))
    (hn : ∀ t, 1 ≤ n t) (hd : ∀ t, 1 ≤ d t)
    (hdiv : ∀ t, d t ∣ n t)
    (hD : ∀ t, IsProductBernoulli (D t) p) :
    (∀ t,
      locLinMinimaxRisk (blockGraph (n t) (d t)) (d t) β B p
          (le_of_lt hp0) (le_of_lt hp1) =
        B ^ 2 * blockEnergy β p (d t) / blockCount (n t) (d t) ∧
      B ^ 2 * blockEnergy β p (d t) / blockCount (n t) (d t) =
        B ^ 2 * (d t : ℝ) * blockEnergy β p (d t) / n t) ∧
    (∀ t (w : LocLinWeights (blockGraph (n t) (d t)) (d t) β p
        (le_of_lt hp0) (le_of_lt hp1)),
      locLinWorstRisk (blockGraph (n t) (d t)) (d t) β B p
          (le_of_lt hp0) (le_of_lt hp1) w =
        B ^ 2 / (n t : ℝ) ^ 2 *
          ∑ b : Fin (blockCount (n t) (d t)),
            blockExtremal (blockGraph (n t) (d t)) (d t) β p
              (le_of_lt hp0) (le_of_lt hp1) w (blockUnits (n t) (d t) b) ∧
      ∀ b : Fin (blockCount (n t) (d t)),
        (d t : ℝ) ^ 2 * blockEnergy β p (d t) ≤
          blockExtremal (blockGraph (n t) (d t)) (d t) β p
            (le_of_lt hp0) (le_of_lt hp1) w (blockUnits (n t) (d t) b)) ∧
    (∀ w : ∀ t, LocLinWeights (blockGraph (n t) (d t)) (d t) β p
        (le_of_lt hp0) (le_of_lt hp1),
      Tendsto (fun t => locLinRiskRatio (n t) (d t) β B p
          (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 1) ↔
      Tendsto (fun t => normalizedBlockExcess (n t) (d t) β p
          (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 0)) ∧
    (∀ w : ∀ t, LocLinWeights (blockGraph (n t) (d t)) (d t) β p
        (le_of_lt hp0) (le_of_lt hp1),
      Tendsto (fun t => normalizedWeightDistance (n t) (d t) β p
          (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 0) →
      Tendsto (fun t => locLinRiskRatio (n t) (d t) β B p
          (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 1)) ∧
    (Tendsto d atTop atTop →
      ∃ w : ∀ t, LocLinWeights (blockGraph (n t) (d t)) (d t) β p
          (le_of_lt hp0) (le_of_lt hp1),
        Tendsto (fun t => locLinRiskRatio (n t) (d t) β B p
            (le_of_lt hp0) (le_of_lt hp1) (w t)) atTop (𝓝 1) ∧
        ∀ᶠ t in atTop,
          normalizedWeightDistance (n t) (d t) β p
              (le_of_lt hp0) (le_of_lt hp1) (w t) = 2 ∧
          ∀ π : Fin (n t) ≃ Fin (n t),
            (∀ i, (π i).val / d t = i.val / d t) →
            normalizedWeightDistanceRelabeled (n t) (d t) β p
              (le_of_lt hp0) (le_of_lt hp1) (w t) π = 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    constructor
    · exact locLinMinimaxRisk_exact
        (n t) (d t) β B p hβ hB hp0 hp1 (hn t) (hd t) (hdiv t)
    · have hncast :
          (n t : ℝ) =
            (blockCount (n t) (d t) : ℝ) * (d t : ℝ) := by
        norm_cast
        simpa [blockCount, Nat.mul_comm] using
          (Nat.div_mul_cancel (hdiv t)).symm
      rw [hncast]
      have hq : (blockCount (n t) (d t) : ℝ) ≠ 0 := by
        have : 0 < blockCount (n t) (d t) := by
          exact Nat.div_pos
            (Nat.le_of_dvd (Nat.zero_lt_of_lt (hn t)) (hdiv t))
            (Nat.zero_lt_of_lt (hd t))
        positivity
      have hdr : (d t : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt (hd t)))
      field_simp
  · intro t w
    constructor
    · exact locLinWorstRisk_exact_blockExtremal
        (n t) (d t) β B p hB
        (le_of_lt hp0) (le_of_lt hp1)
        (hn t) (hd t) (hdiv t) w
    · intro b
      exact completeBlock_blockExtremal_lower
        (n t) (d t) β p hp0 hp1
        (hn t) (hd t) (hdiv t) w b
  · intro w
    exact riskRatio_tendsto_iff_normalizedBlockExcess
      β p B hβ hp0 hp1 hB n d hn hd hdiv w
  · intro w hdist
    exact normalizedWeightDistance_tendsto_implies_riskRatio
      β p B hβ hp0 hp1 hB n d hn hd hdiv w hdist
  · intro hdtop
    let w : ∀ t, LocLinWeights (blockGraph (n t) (d t)) (d t) β p
        (le_of_lt hp0) (le_of_lt hp1) := fun t =>
      orthogonalWitnessWeights (n t) (d t) β p hβ hp0 hp1
        (hn t) (hd t) (hdiv t)
    refine ⟨w, ?_, ?_⟩
    · exact orthogonalWitness_riskRatio_tendsto_one
        β p B hβ hp0 hp1 hB n d hn hd hdiv hdtop
    · have hhigh : ∀ᶠ t in atTop, β < d t := by
        filter_upwards [tendsto_atTop.1 hdtop (β + 1)] with t ht
        omega
      filter_upwards [hhigh] with t hdt
      constructor
      · exact orthogonalWitness_normalized_distance_eq_two
          (n t) (d t) β p hβ hp0 hp1
          (hn t) (hd t) (hdiv t) hdt
      · intro π hπ
        exact orthogonalWitness_normalized_relabel_distance_eq_two
          (n t) (d t) β p hβ hp0 hp1
          (hn t) (hd t) (hdiv t) hdt π hπ
-- @realizes \Psi_{b,t}(finite block extreme-point risk functional)

end CausalSmith.Experimentation.SnipeDegreeFrontier
