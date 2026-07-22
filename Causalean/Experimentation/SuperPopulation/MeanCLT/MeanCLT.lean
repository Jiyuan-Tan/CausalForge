/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.MeanCLT.Hypotheses

/-!
# Asymptotic normality of a centered super-population network sum

This is the consumer-facing bridge that makes the abstract m-dependent network CLT
(`Causalean.Experimentation.SuperPopulation.networkSum_clt`) usable for raw network-dependent
outcomes with positive sum-variance.  It proves standardized asymptotic normality for the centered
network sum, subtracting the sum of the individual outcome means; a sample-mean formulation requires
an additional external common-mean or normalization rewrite.

`networkMean_clt` assembles the pieces: it builds the standardized field
(`centeredNormalizedField`), discharges the engine's three hypotheses (mean-zero, unit total
variance, uniform bound — proved in `Hypotheses.lean`), derives the summand-size negligibility
`B n → 0` from the population-level smallness `card(Vₙ)·(cₙ/sₙ)³ → 0` (using that a positive
sum-variance forces a nonempty population), feeds `networkSum_clt`, and rewrites the engine's
pushforward CDF into the studentized probability set
`{ω | (∑ᵢ Yₙ ᵢ − ∑ᵢ E[Yₙ ᵢ]) / sₙ ≤ t}`.

The reduction follows `Causalean.Experimentation.DesignBased.prodDesign_clt`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators

namespace Causalean.Experimentation.SuperPopulation.MeanCLT

open Causalean.Experimentation.SuperPopulation Causalean.SteinMethod

/-- **Asymptotic normality of a centered super-population network sum.** A network sum, centered by
subtracting the sum of the individual outcome means and divided by its positive standard deviation,
has the standard normal limiting distribution when dependence is local, centered outcomes are
uniformly bounded, and the bound is negligible relative to the aggregate variance.

The hypotheses are:

* a reflexive, symmetric, **bounded-degree** (`≤ m`) network `adj n`;
* outcome m-dependence: non-adjacent outcome tuples are independent (`hindepY`);
* square-integrability of every outcome (`MemLp (Y n i) 2`);
* a positive sum-variance with `sₙ² = Var(∑ᵢ Yₙ ᵢ)` (`hs2`, `hs_pos`);
* uniformly **bounded centered outcomes** `|Yₙ ᵢ − E[Yₙ ᵢ]| ≤ cₙ`;
* the standard **negligibility** `card(Vₙ)·(cₙ/sₙ)³ → 0`.

Then the standardized network sum converges in distribution to the standard normal:
`(μ n).real {ω | (∑ᵢ Yₙ ᵢ ω − ∑ᵢ E[Yₙ ᵢ]) / sₙ ≤ t} → Φ(t)`, with
`Φ(t) = (gaussianReal 0 1).real (Iic t)`.

Obtained as a corollary of `networkSum_clt` applied to the standardized field
`centeredNormalizedField`. -/
theorem networkMean_clt
    {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (Y : ∀ n, V n → Ω n → ℝ)
    (adj : ∀ n, V n → V n → Prop) [∀ n, DecidableRel (adj n)]
    (hrefl : ∀ n i, adj n i i) (hsymm : ∀ n i j, adj n i j → adj n j i)
    (hmeasY : ∀ n i, Measurable (Y n i))
    (hindepY : ∀ n, ∀ A B : Finset (V n), (∀ a ∈ A, ∀ b ∈ B, ¬ adj n a b) →
      IndepFun (fun ω => fun k : A => Y n k ω) (fun ω => fun k : B => Y n k ω) (μ n))
    (m : ℕ) (hdeg : ∀ n i, (Finset.univ.filter (fun j => adj n i j)).card ≤ m)
    (hL2 : ∀ n i, MemLp (Y n i) 2 (μ n))
    (s : ℕ → ℝ) (hs_pos : ∀ n, 0 < s n)
    (hs2 : ∀ n, (s n) ^ 2 = variance (fun ω => ∑ i, Y n i ω) (μ n))
    (c : ℕ → ℝ) (hc : ∀ n i ω, |Y n i ω - ∫ x, Y n i x ∂(μ n)| ≤ c n)
    (hsmall : Tendsto (fun n => (Fintype.card (V n) : ℝ) * (c n / s n) ^ 3) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto
      (fun n => (μ n).real
        {ω | (∑ i, Y n i ω - ∑ i, ∫ x, Y n i x ∂(μ n)) / s n ≤ t})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic t))) := by
  classical
  let F : ∀ n, NetworkDependence (V n) (Ω n) (μ n) :=
    fun n => centeredNormalizedField (Y n) (adj n) (hrefl n) (hsymm n)
      (hmeasY n) (hindepY n) (s n)
  let B : ℕ → ℝ := fun n => 2 * c n / s n
  have hdeg' : ∀ n i, ((F n).toDepGraph.nbhd i).card ≤ m := by
    intro n i
    change (Finset.univ.filter (fun j => adj n i j)).card ≤ m
    exact hdeg n i
  have hΩne : ∀ n, Nonempty (Ω n) := by
    intro n
    by_contra hΩ
    haveI : IsEmpty (Ω n) := not_nonempty_iff.mp hΩ
    have hzero : μ n = 0 := by
      ext S
      have hS : S = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hS]
    exact (MeasureTheory.IsProbabilityMeasure.ne_zero (μ n)) hzero
  have hne : ∀ n, Nonempty (V n) := by
    intro n
    by_contra hV
    haveI : IsEmpty (V n) := not_nonempty_iff.mp hV
    have hsum : (fun ω => ∑ i, Y n i ω) = (0 : Ω n → ℝ) := by
      funext ω
      exact Fintype.sum_empty (fun i => Y n i ω)
    have hs2zero : (s n) ^ 2 = 0 := by
      rw [hs2 n, hsum]
      exact variance_zero (μ n)
    have hs2pos : 0 < (s n) ^ 2 := sq_pos_of_pos (hs_pos n)
    nlinarith
  have hcard : ∀ n, 1 ≤ Fintype.card (V n) := by
    intro n
    exact Fintype.card_pos_iff.mpr (hne n)
  have hc_nonneg : ∀ n, 0 ≤ c n := by
    intro n
    obtain ⟨i⟩ := hne n
    obtain ⟨ω⟩ := hΩne n
    exact le_trans (abs_nonneg _) (hc n i ω)
  have hB : ∀ n, 0 ≤ B n := by
    intro n
    exact div_nonneg (mul_nonneg zero_le_two (hc_nonneg n)) (le_of_lt (hs_pos n))
  have hbound : ∀ n i ω, |(F n).X i ω| ≤ B n := by
    intro n i ω
    exact centeredNormalizedField_abs_le (Y n) (adj n) (hrefl n) (hsymm n)
      (hmeasY n) (hindepY n) (s n) (hs_pos n) (c n) (hc n) i ω
  have hNB3 : Tendsto (fun n => (Fintype.card (V n) : ℝ) * (B n) ^ 3)
      atTop (𝓝 0) := by
    have hfac : (fun n => (Fintype.card (V n) : ℝ) * (B n) ^ 3)
        = (fun n => 8 * ((Fintype.card (V n) : ℝ) * (c n / s n) ^ 3)) := by
      funext n
      dsimp [B]
      ring
    rw [hfac]
    simpa using hsmall.const_mul 8
  have hB0 : Tendsto B atTop (𝓝 0) := by
    have hB3_0 : Tendsto (fun n => (B n) ^ 3) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => pow_nonneg (hB n) 3) (fun n => ?_) hNB3
      have hcardR : (1 : ℝ) ≤ (Fintype.card (V n) : ℝ) := by
        exact_mod_cast hcard n
      exact le_mul_of_one_le_left (pow_nonneg (hB n) 3) hcardR
    have hroot : Tendsto (fun n => ((B n) ^ 3) ^ ((3 : ℕ)⁻¹ : ℝ)) atTop
        (𝓝 0) := by
      simpa using (Real.continuousAt_rpow_const 0 ((3 : ℕ)⁻¹ : ℝ)
        (Or.inr (by positivity))).tendsto.comp hB3_0
    exact hroot.congr
      (fun n => Real.pow_rpow_inv_natCast (hB n) (by norm_num : (3 : ℕ) ≠ 0))
  have hmean : ∀ n i, ∫ ω, (F n).X i ω ∂(μ n) = 0 := by
    intro n i
    exact centeredNormalizedField_integral_eq_zero (Y n) (adj n) (hrefl n)
      (hsymm n) (hmeasY n) (hindepY n) (hL2 n) (s n) i
  have hvar : ∀ n, ∫ ω, (depSum (F n).X ω) ^ 2 ∂(μ n) = 1 := by
    intro n
    exact centeredNormalizedField_sq_integral (Y n) (adj n) (hrefl n)
      (hsymm n) (hmeasY n) (hindepY n) (hL2 n) (s n) (hs_pos n) (hs2 n)
  have hclt := networkSum_clt μ F m hdeg' B hB hbound hB0 hNB3 hmean hvar t
  refine hclt.congr (fun n => ?_)
  have hWmeas : Measurable (depSum (F n).X) := by
    exact Finset.measurable_sum _ (fun i _ => (F n).meas i)
  have hset : (depSum (F n).X) ⁻¹' Set.Iic t =
      {ω | (∑ i, Y n i ω - ∑ i, ∫ x, Y n i x ∂(μ n)) / s n ≤ t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    dsimp [depSum, F]
    have hsum : (∑ i, (Y n i ω - ∫ x, Y n i x ∂(μ n)) / s n)
        = (∑ i, Y n i ω - ∑ i, ∫ x, Y n i x ∂(μ n)) / s n := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
    rw [hsum]
  rw [← hset, MeasureTheory.map_measureReal_apply hWmeas measurableSet_Iic]

end Causalean.Experimentation.SuperPopulation.MeanCLT
