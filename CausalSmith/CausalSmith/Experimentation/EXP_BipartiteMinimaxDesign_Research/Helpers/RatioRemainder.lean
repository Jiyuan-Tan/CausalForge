/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hájek ratio-remainder identity for the bipartite minimax design

The scaled Hájek-minus-linear-score remainder `√n·(τ̂_H − τ) − n^{-1/2}·∑ᵢ ηᵢ` is the second-order
term of the two-arm ratio expansion.  Per arm it factors as `(G_arm/√n)·(n − D_arm)/D_arm`; on the
event where the denominator ratio is at least `1/2` the last factor is bounded by `2`, giving the
capped product bound consumed by the tightness assembly (`THeteroClt.lean`).
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.NumeratorMoment
import Causalean.Experimentation.DesignBased.RatioLinearization

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open scoped BigOperators Topology
open Finset
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

/-- Neighborhood-SUTVA exposure identity (treated arm): `T_i(z)·Y_i(z) = T_i(z)·Y_i^1`, because on
`{T_i = 1}` the treatment vector is all-treated on `N_i`, so `Y_i(z) = Y_i^1` by interference. -/
lemma expT_mul_Yfun_eq (E : BipartiteExperiment I O) (hBI : BipartiteInterference E)
    (z : I → Bool) (i : O) :
    E.expT z i * E.Yfun i z = E.expT z i * E.Y1 i := by
  by_cases hzero : E.expT z i = 0
  · simp [hzero]
  · have hfac : ∀ k ∈ E.N i, (if z k then (1 : ℝ) else 0) ≠ 0 := by
      rw [BipartiteExperiment.expT] at hzero
      exact Finset.prod_ne_zero_iff.mp hzero
    have hall : ∀ k ∈ E.N i, z k = true := by
      intro k hk
      specialize hfac k hk
      split at hfac <;> simp_all
    have hy : E.Yfun i z = E.Yfun i (fun _ => true) := hBI i z (fun _ => true) hall
    rw [hy]
    rfl

/-- Neighborhood-SUTVA exposure identity (control arm): `C_i(z)·Y_i(z) = C_i(z)·Y_i^0`. -/
lemma expC_mul_Yfun_eq (E : BipartiteExperiment I O) (hBI : BipartiteInterference E)
    (z : I → Bool) (i : O) :
    E.expC z i * E.Yfun i z = E.expC z i * E.Y0 i := by
  by_cases hzero : E.expC z i = 0
  · simp [hzero]
  · have hfac : ∀ k ∈ E.N i, (if z k then (0 : ℝ) else 1) ≠ 0 := by
      rw [BipartiteExperiment.expC] at hzero
      exact Finset.prod_ne_zero_iff.mp hzero
    have hall : ∀ k ∈ E.N i, z k = false := by
      intro k hk
      specialize hfac k hk
      split at hfac <;> simp_all
    have hy : E.Yfun i z = E.Yfun i (fun _ => false) := hBI i z (fun _ => false) hall
    rw [hy]
    rfl

/-- **Capped Hájek ratio-remainder bound.**  When both denominator sums are at least `card O / 2`
(so both Hájek arms are on their nonzero branch and `card O / D_arm ≤ 2`), the scaled
Hájek-minus-linear-score remainder is bounded by the sum over arms of
`2 · |G_arm/√(card O)| · |D_arm/card O − 1|`. -/
lemma hajek_remainder_capped_bound (E : BipartiteExperiment I O) (p : I → ℝ) (z : I → Bool)
    (hBI : BipartiteInterference E)
    (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hcard : 0 < Fintype.card O)
    (hD1 : (Fintype.card O : ℝ) / 2 ≤ ∑ i, E.expT z i / E.piT p i)
    (hD0 : (Fintype.card O : ℝ) / 2 ≤ ∑ i, E.expC z i / E.piC p i) :
    |Real.sqrt (Fintype.card O) * (E.hajekEstimator p z - E.tau)
        - (Real.sqrt (Fintype.card O))⁻¹ * ∑ i, E.linScore p z i|
      ≤ 2 * |(Real.sqrt (Fintype.card O))⁻¹ * treatNumerator E p z|
            * |(Fintype.card O : ℝ)⁻¹ * (∑ i, E.expT z i / E.piT p i) - 1|
        + 2 * |(Real.sqrt (Fintype.card O))⁻¹ * ctrlNumerator E p z|
            * |(Fintype.card O : ℝ)⁻¹ * (∑ i, E.expC z i / E.piC p i) - 1| := by
  let n : ℝ := Fintype.card O
  let sn : ℝ := Real.sqrt (Fintype.card O)
  let D1 : ℝ := ∑ i, E.expT z i / E.piT p i
  let D0 : ℝ := ∑ i, E.expC z i / E.piC p i
  let A1 : ℝ := ∑ i, E.expT z i * E.Yfun i z / E.piT p i
  let A0 : ℝ := ∑ i, E.expC z i * E.Yfun i z / E.piC p i
  let G1 : ℝ := treatNumerator E p z
  let G0 : ℝ := ctrlNumerator E p z
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hsn_sq : sn ^ 2 = n := by
    dsimp [sn, n]
    rw [Real.sq_sqrt]
    positivity
  have hsnpos : 0 < sn := by
    dsimp [sn]
    rw [Real.sqrt_pos]
    exact_mod_cast hcard
  have hsn0 : sn ≠ 0 := ne_of_gt hsnpos
  have hD1pos : 0 < D1 := by
    apply lt_of_lt_of_le (show 0 < n / 2 by linarith)
    simpa [D1, n] using hD1
  have hD0pos : 0 < D0 := by
    apply lt_of_lt_of_le (show 0 < n / 2 by linarith)
    simpa [D0, n] using hD0
  have hD10 : D1 ≠ 0 := ne_of_gt hD1pos
  have hD00 : D0 ≠ 0 := ne_of_gt hD0pos
  have hcap1 : n / D1 ≤ 2 := by
    apply (div_le_iff₀ hD1pos).2
    nlinarith [hD1]
  have hcap0 : n / D0 ≤ 2 := by
    apply (div_le_iff₀ hD0pos).2
    nlinarith [hD0]
  have hA1 : A1 = ∑ i, E.expT z i * E.Y1 i / E.piT p i := by
    dsimp [A1]
    apply Finset.sum_congr rfl
    intro i hi
    rw [expT_mul_Yfun_eq E hBI z i]
  have hA0 : A0 = ∑ i, E.expC z i * E.Y0 i / E.piC p i := by
    dsimp [A0]
    apply Finset.sum_congr rfl
    intro i hi
    rw [expC_mul_Yfun_eq E hBI z i]
  have hcenter1 : A1 - E.mu1 * D1 = G1 := by
    change A1 - E.mu1 * D1 = G1
    rw [hA1]
    change (∑ i, E.expT z i * E.Y1 i / E.piT p i) -
      E.mu1 * (∑ i, E.expT z i / E.piT p i) = treatNumerator E p z
    calc
      (∑ i, E.expT z i * E.Y1 i / E.piT p i) -
          E.mu1 * (∑ i, E.expT z i / E.piT p i) =
          (∑ i, E.expT z i * E.Y1 i / E.piT p i) -
            ∑ i, E.mu1 * (E.expT z i / E.piT p i) := by rw [Finset.mul_sum]
      _ = ∑ i, (E.expT z i * E.Y1 i / E.piT p i -
          E.mu1 * (E.expT z i / E.piT p i)) := by rw [Finset.sum_sub_distrib]
      _ = treatNumerator E p z := by
        unfold treatNumerator
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hcenter0 : A0 - E.mu0 * D0 = G0 := by
    change A0 - E.mu0 * D0 = G0
    rw [hA0]
    change (∑ i, E.expC z i * E.Y0 i / E.piC p i) -
      E.mu0 * (∑ i, E.expC z i / E.piC p i) = ctrlNumerator E p z
    calc
      (∑ i, E.expC z i * E.Y0 i / E.piC p i) -
          E.mu0 * (∑ i, E.expC z i / E.piC p i) =
          (∑ i, E.expC z i * E.Y0 i / E.piC p i) -
            ∑ i, E.mu0 * (E.expC z i / E.piC p i) := by rw [Finset.mul_sum]
      _ = ∑ i, (E.expC z i * E.Y0 i / E.piC p i -
          E.mu0 * (E.expC z i / E.piC p i)) := by rw [Finset.sum_sub_distrib]
      _ = ctrlNumerator E p z := by
        unfold ctrlNumerator
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hsum1 : ∑ i, (E.Y1 i - E.mu1) = 0 := by
    have hn : (Fintype.card O : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hcard
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ]
    unfold BipartiteExperiment.mu1
    simp only [nsmul_eq_mul]
    calc
      (∑ i, E.Y1 i) - (Fintype.card O : ℝ) *
          ((Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y1 i) =
          (∑ i, E.Y1 i) * (1 - (Fintype.card O : ℝ) *
            (Fintype.card O : ℝ)⁻¹) := by ring
      _ = 0 := by rw [mul_inv_cancel₀ hn]; ring
  have hsum0 : ∑ i, (E.Y0 i - E.mu0) = 0 := by
    have hn : (Fintype.card O : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hcard
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ]
    unfold BipartiteExperiment.mu0
    simp only [nsmul_eq_mul]
    calc
      (∑ i, E.Y0 i) - (Fintype.card O : ℝ) *
          ((Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y0 i) =
          (∑ i, E.Y0 i) * (1 - (Fintype.card O : ℝ) *
            (Fintype.card O : ℝ)⁻¹) := by ring
      _ = 0 := by rw [mul_inv_cancel₀ hn]; ring
  have hscore : ∑ i, E.linScore p z i = G1 - G0 := by
    have htreated : ∑ i, (E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1) = G1 := by
      change (∑ i, (E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1)) =
        treatNumerator E p z
      calc
        ∑ i, (E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1) =
            ∑ i, (E.expT z i / E.piT p i * (E.Y1 i - E.mu1) -
              (E.Y1 i - E.mu1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = treatNumerator E p z - ∑ i, (E.Y1 i - E.mu1) := by
          rw [Finset.sum_sub_distrib]
          rfl
        _ = treatNumerator E p z := by rw [hsum1, sub_zero]
    have hcontrol : ∑ i, (E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0) = G0 := by
      change (∑ i, (E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0)) =
        ctrlNumerator E p z
      calc
        ∑ i, (E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0) =
            ∑ i, (E.expC z i / E.piC p i * (E.Y0 i - E.mu0) -
              (E.Y0 i - E.mu0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ctrlNumerator E p z - ∑ i, (E.Y0 i - E.mu0) := by
          rw [Finset.sum_sub_distrib]
          rfl
        _ = ctrlNumerator E p z := by rw [hsum0, sub_zero]
    unfold BipartiteExperiment.linScore
    rw [Finset.sum_sub_distrib, htreated, hcontrol]
  have hhajek : E.hajekEstimator p z = A1 / D1 - A0 / D0 := by
    dsimp [BipartiteExperiment.hajekEstimator, BipartiteExperiment.hajekDenominators]
    simp [A1, A0, D1, D0, hD1pos, hD0pos]
  -- Each arm's capped remainder is the promoted general
  -- `Causalean.Experimentation.DesignBased.ratio_remainder_capped_bound`, instantiated with the
  -- arm's numerator/denominator/target and the centered-numerator identity `Gₐ = Aₐ − μₐ·Dₐ`.
  have harm1 : |sn * (A1 / D1 - E.mu1) - sn⁻¹ * G1| ≤ 2 * |sn⁻¹ * G1| * |n⁻¹ * D1 - 1| :=
    ratio_remainder_capped_bound hnpos hsn_sq hD1pos hcap1 hcenter1.symm
  have harm0 : |sn * (A0 / D0 - E.mu0) - sn⁻¹ * G0| ≤ 2 * |sn⁻¹ * G0| * |n⁻¹ * D0 - 1| :=
    ratio_remainder_capped_bound hnpos hsn_sq hD0pos hcap0 hcenter0.symm
  have hmain : sn * (E.hajekEstimator p z - E.tau) - sn⁻¹ * ∑ i, E.linScore p z i =
      (sn * (A1 / D1 - E.mu1) - sn⁻¹ * G1) - (sn * (A0 / D0 - E.mu0) - sn⁻¹ * G0) := by
    rw [hhajek, BipartiteExperiment.tau, hscore]
    ring
  change |sn * (E.hajekEstimator p z - E.tau) - sn⁻¹ * ∑ i, E.linScore p z i| ≤
    2 * |sn⁻¹ * G1| * |n⁻¹ * D1 - 1| + 2 * |sn⁻¹ * G0| * |n⁻¹ * D0 - 1|
  rw [hmain]
  calc
    |(sn * (A1 / D1 - E.mu1) - sn⁻¹ * G1) - (sn * (A0 / D0 - E.mu0) - sn⁻¹ * G0)| ≤
        |sn * (A1 / D1 - E.mu1) - sn⁻¹ * G1| + |sn * (A0 / D0 - E.mu0) - sn⁻¹ * G0| := by
      rw [sub_eq_add_neg]
      calc
        |(sn * (A1 / D1 - E.mu1) - sn⁻¹ * G1) + -(sn * (A0 / D0 - E.mu0) - sn⁻¹ * G0)| ≤
            |sn * (A1 / D1 - E.mu1) - sn⁻¹ * G1| + |-(sn * (A0 / D0 - E.mu0) - sn⁻¹ * G0)| :=
          abs_add_le _ _
        _ = |sn * (A1 / D1 - E.mu1) - sn⁻¹ * G1| + |sn * (A0 / D0 - E.mu0) - sn⁻¹ * G0| := by
          rw [abs_neg]
    _ ≤ 2 * |sn⁻¹ * G1| * |n⁻¹ * D1 - 1| + 2 * |sn⁻¹ * G0| * |n⁻¹ * D0 - 1| :=
      add_le_add harm1 harm0

end CausalSmith.Experimentation.BipartiteMinimaxDesign
