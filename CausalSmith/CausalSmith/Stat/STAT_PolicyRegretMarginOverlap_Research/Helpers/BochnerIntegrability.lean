/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.FeasibleERM
import Causalean.Mathlib.MeasureTheory.SupCountableDense

/-!
# Discharging the Bochner integrability side conditions (`bochner_integrability_gate`)

This file discharges the `hBochner` regularity hypothesis previously assumed on
`feasible_upper` / `crude_localized_master_bound`: eventually in `n`, for every law in the
class, the selected regret loss and the localized/offset empirical-process suprema over the
policy class are measurable, `BddAbove`, and integrable against the `n`-fold product data
measure.

The measurability of the supremum over the (uncountable) policy class is obtained by
reducing it to the countable pointwise-dense skeleton `Π₀` carried by `PolicyClassVC`,
using the paper-agnostic machinery
`Causalean.Mathlib.MeasureTheory.integrable_sSup_image_of_countable_dense`.
The reduction requires sequential continuity of the process in the policy argument along
skeleton sequences, which is the dominated-convergence content proved here
(`lawRegret_tendsto_of_skeleton`, `pooledCrossfitProcess_tendsto_of_skeleton`,
`foldSubCentered_tendsto_of_skeleton`).
-/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open Causalean.Mathlib.MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- `|1{b} - 1{c}| ≤ 1` for booleans (local reproof of the ClipBias private helper). -/
private lemma boolIndicator_diff_abs_le_one (b c : Bool) :
    |boolIndicator b - boolIndicator c| ≤ 1 := by
  cases b <;> cases c <;> norm_num [boolIndicator]

/-! ## Phase 1 — sequential continuity along pointwise-dense skeleton sequences

Each is a dominated-convergence statement: a pointwise-dense skeleton sequence
`seq j → π` (everywhere, hence a.e.) drives the population welfare/centering integrals to
their limits, the finite-sample averages being eventually exactly equal at the (finitely
many) evaluation points. -/

private lemma centeringIntegral_tendsto_of_skeleton (P : ObservedLaw 𝒳)
    [IsProbabilityMeasure P.dataMeasure]
    (h : Policy 𝒳 → Observation 𝒳 → ℝ) (B : ℝ)
    (hbound : ∀ (π : Policy 𝒳) (O : Observation 𝒳), |h π O| ≤ B)
    (hmeas : ∀ ρ : Policy 𝒳, Measurable ρ → Measurable (h ρ))
    (hcompat : PolicyCompatible h)
    (π : Policy 𝒳) (seq : ℕ → Policy 𝒳) (hseqmeas : ∀ j, Measurable (seq j))
    (hseq : ∀ x, ∀ᶠ j in Filter.atTop, seq j x = π x) :
    Filter.Tendsto (fun j => ∫ O, h (seq j) O ∂P.dataMeasure) Filter.atTop
      (nhds (∫ O, h π O ∂P.dataMeasure)) := by
  rcases hcompat with ⟨G, hG⟩
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ => B) ?_ (MeasureTheory.integrable_const B) ?_ ?_
  · intro j
    exact (hmeas (seq j) (hseqmeas j)).aestronglyMeasurable
  · intro j
    exact Filter.Eventually.of_forall fun O => by
      simpa only [Real.norm_eq_abs] using hbound (seq j) O
  · exact Filter.Eventually.of_forall fun O => by
      have heq : (fun j => h (seq j) O) =ᶠ[Filter.atTop] (fun _ => h π O) := by
        filter_upwards [hseq O.X] with j hj
        rw [hG (seq j) O, hG π O, hj]
      exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

/-- Welfare-regret continuity along a pointwise-convergent skeleton sequence: if
`seq j x = π x` eventually for every `x`, then `lawRegret P (seq j) → lawRegret P π`.
(`welfare = ∫ boolIndicator(π x)·τ x dP_X` converges by dominated convergence with
dominating function `|τ| ≤ 2`.) -/
lemma lawRegret_tendsto_of_skeleton (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P)
    (π : Policy 𝒳) (seq : ℕ → Policy 𝒳)
    (hπmeas : Measurable π) (hseqmeas : ∀ j, Measurable (seq j))
    (hseq : ∀ x, ∀ᶠ j in Filter.atTop, seq j x = π x) :
    Filter.Tendsto (fun j => lawRegret P (seq j)) Filter.atTop
      (nhds (lawRegret P π)) := by
  rcases hwf with ⟨_hPprob, hPXprob, _hmap, hτmeas, _hpropmeas, _hmu0meas,
    _hmu1meas, hτeq, _hprop, _hceA, _hceY1, _hceY0⟩
  letI : IsProbabilityMeasure P.PX := hPXprob
  have hτbound : ∀ x, |P.contrast x| ≤ (2 : ℝ) := by
    intro x
    have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
    have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
    calc
      |P.contrast x| = |P.mu1 x - P.mu0 x| := by rw [hτeq]
      _ ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hmu1 hmu0
      _ = (2 : ℝ) := by norm_num
  have hwelfare :
      Filter.Tendsto
        (fun j => ∫ x, boolIndicator (seq j x) * P.contrast x ∂P.PX)
        Filter.atTop
        (nhds (∫ x, boolIndicator (π x) * P.contrast x ∂P.PX)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => (2 : ℝ)) ?_ (MeasureTheory.integrable_const 2) ?_ ?_
    · intro j
      exact
        (((measurable_of_finite boolIndicator).comp (hseqmeas j)).mul hτmeas).aestronglyMeasurable
    · intro j
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        have hb : |boolIndicator (seq j x)| ≤ (1 : ℝ) := by
          cases seq j x <;> simp [boolIndicator]
        nlinarith [mul_le_mul hb (hτbound x) (abs_nonneg (P.contrast x))
          (by norm_num : (0 : ℝ) ≤ 1)]
    · exact Filter.Eventually.of_forall fun x => by
        have heq :
            (fun j => boolIndicator (seq j x) * P.contrast x) =ᶠ[Filter.atTop]
              (fun _ => boolIndicator (π x) * P.contrast x) := by
          filter_upwards [hseq x] with j hj
          rw [hj]
        exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  simpa only [lawRegret, regret, welfare] using
    hwelfare.const_sub (welfare P.PX P.contrast (optimalPolicy P.contrast))

/-- Pooled cross-fit process continuity along a pointwise-convergent skeleton sequence, for
a uniformly bounded, policy-compatible, measurable increment `g`.  The finite-sample average
`n⁻¹ ∑ᵢ g(assign i)(seq j)(sample i)` is eventually exactly equal to its `π`-value (each of
the finitely many evaluation points stabilizes), and each centering integral
`∫ g(assign i)(seq j) dP` converges by dominated convergence (dominating constant `B`). -/
lemma pooledCrossfitProcess_tendsto_of_skeleton {n K : ℕ} (P : ObservedLaw 𝒳)
    [IsProbabilityMeasure P.dataMeasure]
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ (k : Fin K) (π : Policy 𝒳) (O : Observation 𝒳), |g k π O| ≤ B)
    (hcompat : ∀ k : Fin K, PolicyCompatible (g k))
    (hmeas : ∀ (k : Fin K) (ρ : Policy 𝒳), Measurable ρ → Measurable (g k ρ))
    (assign : Fin n → Fin K) (sample : Fin n → Observation 𝒳)
    (π : Policy 𝒳) (seq : ℕ → Policy 𝒳) (hseqmeas : ∀ j, Measurable (seq j))
    (hseq : ∀ x, ∀ᶠ j in Filter.atTop, seq j x = π x) :
    Filter.Tendsto (fun j => pooledCrossfitProcess P g assign sample (seq j))
      Filter.atTop (nhds (pooledCrossfitProcess P g assign sample π)) := by
  have hsum :
      Filter.Tendsto
        (fun j => ∑ i : Fin n,
          (g (assign i) (seq j) (sample i) -
            ∫ O, g (assign i) (seq j) O ∂P.dataMeasure))
        Filter.atTop
        (nhds (∑ i : Fin n,
          (g (assign i) π (sample i) -
            ∫ O, g (assign i) π O ∂P.dataMeasure))) := by
    apply tendsto_finset_sum
    intro i _hi
    have heval :
        Filter.Tendsto (fun j => g (assign i) (seq j) (sample i)) Filter.atTop
          (nhds (g (assign i) π (sample i))) := by
      rcases hcompat (assign i) with ⟨G, hG⟩
      have heq :
          (fun j => g (assign i) (seq j) (sample i)) =ᶠ[Filter.atTop]
            (fun _ => g (assign i) π (sample i)) := by
        filter_upwards [hseq (sample i).X] with j hj
        rw [hG (seq j) (sample i), hG π (sample i), hj]
      exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
    have hcenter := centeringIntegral_tendsto_of_skeleton P (g (assign i)) B
      (hbound (assign i)) (hmeas (assign i)) (hcompat (assign i)) π seq hseqmeas hseq
    exact heval.sub hcenter
  simpa only [pooledCrossfitProcess] using hsum.const_mul ((n : ℝ)⁻¹)

/-- Fold-subsample centered process continuity along a pointwise-convergent skeleton
sequence (same dominated-convergence content as `pooledCrossfitProcess_tendsto_of_skeleton`,
specialized to a single fold's subsample average).  This is the building block for the
`foldOffsetSubSup` integrability conjunct. -/
lemma foldSubCentered_tendsto_of_skeleton {n K : ℕ} (P : ObservedLaw 𝒳)
    [IsProbabilityMeasure P.dataMeasure]
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ (k : Fin K) (π : Policy 𝒳) (O : Observation 𝒳), |g k π O| ≤ B)
    (hcompat : ∀ k : Fin K, PolicyCompatible (g k))
    (hmeas : ∀ (k : Fin K) (ρ : Policy 𝒳), Measurable ρ → Measurable (g k ρ))
    (assign : Fin n → Fin K) (k : Fin K)
    (sample : foldIndex assign k → Observation 𝒳)
    (π : Policy 𝒳) (seq : ℕ → Policy 𝒳) (hseqmeas : ∀ j, Measurable (seq j))
    (hseq : ∀ x, ∀ᶠ j in Filter.atTop, seq j x = π x) :
    Filter.Tendsto
      (fun j => ((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (g k (seq j) (sample i) - ∫ O, g k (seq j) O ∂P.dataMeasure))
      Filter.atTop
      (nhds (((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure))) := by
  have hsum :
      Filter.Tendsto
        (fun j => ∑ i : foldIndex assign k,
          (g k (seq j) (sample i) - ∫ O, g k (seq j) O ∂P.dataMeasure))
        Filter.atTop
        (nhds (∑ i : foldIndex assign k,
          (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure))) := by
    apply tendsto_finset_sum
    intro i _hi
    have heval :
        Filter.Tendsto (fun j => g k (seq j) (sample i)) Filter.atTop
          (nhds (g k π (sample i))) := by
      rcases hcompat k with ⟨G, hG⟩
      have heq :
          (fun j => g k (seq j) (sample i)) =ᶠ[Filter.atTop]
            (fun _ => g k π (sample i)) := by
        filter_upwards [hseq (sample i).X] with j hj
        rw [hG (seq j) (sample i), hG π (sample i), hj]
      exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
    have hcenter := centeringIntegral_tendsto_of_skeleton P (g k) B
      (hbound k) (hmeas k) (hcompat k) π seq hseqmeas hseq
    exact heval.sub hcenter
  exact hsum.const_mul ((Fintype.card (foldIndex assign k) : ℝ)⁻¹)

/-! ## Phase 2 — discharge of the four Bochner side conditions

`bochner_discharge` proves the exact `hBochner` hypothesis previously assumed on
`crude_localized_master_bound` / `feasible_upper`, from the primitive regularity data
(finite-VC dense skeleton, bounded/measurable cross-fit nuisances, positive clip schedule).
The measurable/integrable supremum conjuncts go through the paper-agnostic
`Causalean.Mathlib.MeasureTheory.integrable_sSup_image_of_countable_dense` applied to the
truncated increment (uniform envelope `36/q`), then transported to the untruncated process
by the a.e.-equalities `pooledOffsetSup_trunc_eq_original_ae_36` /
`foldOffsetSubSup_trunc_eq_original_ae_36`. -/

private lemma abs_integral_le_bound (P : ObservedLaw 𝒳)
    (f : Observation 𝒳 → ℝ) (B : ℝ) [IsProbabilityMeasure P.dataMeasure]
    (hB : 0 ≤ B) (hbound : ∀ O, |f O| ≤ B) :
    |∫ O, f O ∂P.dataMeasure| ≤ B := by
  have hnorm : ‖∫ O, f O ∂P.dataMeasure‖ ≤ B * P.dataMeasure.real Set.univ := by
    exact norm_integral_le_of_norm_le_const (μ := P.dataMeasure) (f := f) (C := B)
      (Filter.Eventually.of_forall (by simpa [Real.norm_eq_abs] using hbound))
  simpa [Real.norm_eq_abs] using hnorm

private lemma abs_centered_average_le {ι : Type*} [Fintype ι]
    (P : ObservedLaw 𝒳) (h : ι → Observation 𝒳 → ℝ)
    (sample : ι → Observation 𝒳) (B : ℝ) [IsProbabilityMeasure P.dataMeasure]
    (hB : 0 ≤ B) (hbound : ∀ i O, |h i O| ≤ B) :
    |((Fintype.card ι : ℝ)⁻¹) * ∑ i, (h i (sample i) - ∫ O, h i O ∂P.dataMeasure)|
      ≤ 2 * B := by
  classical
  let m := Fintype.card ι
  let S : ℝ := ∑ i, (h i (sample i) - ∫ O, h i O ∂P.dataMeasure)
  have hint : ∀ i, |∫ O, h i O ∂P.dataMeasure| ≤ B := fun i =>
    abs_integral_le_bound P (h i) B hB (hbound i)
  have hterm : ∀ i, |h i (sample i) - ∫ O, h i O ∂P.dataMeasure| ≤ 2 * B := by
    intro i
    calc
      |h i (sample i) - ∫ O, h i O ∂P.dataMeasure|
          ≤ |h i (sample i)| + |∫ O, h i O ∂P.dataMeasure| := abs_sub _ _
      _ ≤ B + B := add_le_add (hbound i _) (hint i)
      _ = 2 * B := by ring
  by_cases hm : m = 0
  · have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp hm
    simp [m, hm, hB]
  · have hmposNat : 0 < m := Nat.pos_of_ne_zero hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
    have hsum : |S| ≤ (m : ℝ) * (2 * B) := by
      calc
        |S| = |∑ i, (h i (sample i) - ∫ O, h i O ∂P.dataMeasure)| := rfl
        _ ≤ ∑ i, |h i (sample i) - ∫ O, h i O ∂P.dataMeasure| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i, 2 * B := Finset.sum_le_sum (fun i _ => hterm i)
        _ = (m : ℝ) * (2 * B) := by simp [m]
    have hnon : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr hmpos.le
    have habs : |(m : ℝ)⁻¹ * S| ≤ (m : ℝ)⁻¹ * ((m : ℝ) * (2 * B)) := by
      calc
        |(m : ℝ)⁻¹ * S| = (m : ℝ)⁻¹ * |S| := by rw [abs_mul, abs_of_nonneg hnon]
        _ ≤ (m : ℝ)⁻¹ * ((m : ℝ) * (2 * B)) :=
          mul_le_mul_of_nonneg_left hsum hnon
    have hcalc : (m : ℝ)⁻¹ * ((m : ℝ) * (2 * B)) = 2 * B := by
      field_simp [ne_of_gt hmpos]
    simpa [m, S, hcalc] using habs

private lemma measurable_pooled_offset_eval {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (π : Policy 𝒳) (hmeas : ∀ k, Measurable (g k π)) :
    Measurable (fun sample : Fin n → Observation 𝒳 =>
      max 0 (2 * |pooledCrossfitProcess P g assign sample π| - lawRegret P π / 4)) := by
  have hp : Measurable (fun sample : Fin n → Observation 𝒳 =>
      pooledCrossfitProcess P g assign sample π) := by
    unfold pooledCrossfitProcess
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact ((hmeas (assign i)).comp (measurable_pi_apply i)).sub measurable_const
  have hpabs : Measurable (fun sample : Fin n → Observation 𝒳 =>
      |pooledCrossfitProcess P g assign sample π|) := by
    simpa [Real.norm_eq_abs] using hp.norm
  exact measurable_const.max ((measurable_const.mul hpabs).sub measurable_const)

private lemma measurable_fold_offset_eval {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (k : Fin K) (π : Policy 𝒳) (hmeas : ∀ k, Measurable (g k π)) :
    Measurable (fun sample : foldIndex assign k → Observation 𝒳 =>
      max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i, (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)| - lawRegret P π / 4)) := by
  have hp : Measurable (fun sample : foldIndex assign k → Observation 𝒳 =>
      ((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i, (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)) := by
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact ((hmeas k).comp (measurable_pi_apply i)).sub measurable_const
  have hpabs : Measurable (fun sample : foldIndex assign k → Observation 𝒳 =>
      |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i, (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)|) := by
    simpa [Real.norm_eq_abs] using hp.norm
  exact measurable_const.max ((measurable_const.mul hpabs).sub measurable_const)

private lemma abs_lawWelfare_le_two' (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    |lawWelfare P π| ≤ (2 : ℝ) := by
  rcases hwf with ⟨_hPprob, hPXprob, _hmap, hτmeas, _hpropmeas, _hmu0meas,
    _hmu1meas, hτeq, _hprop, _hceA, _hceY1, _hceY0⟩
  letI : IsProbabilityMeasure P.PX := hPXprob
  have hτbound : ∀ x, |P.contrast x| ≤ (2 : ℝ) := by
    intro x
    have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
    have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
    calc
      |P.contrast x| = |P.mu1 x - P.mu0 x| := by rw [hτeq]
      _ ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hmu1 hmu0
      _ = (2 : ℝ) := by norm_num
  have hnorm : ‖∫ x, boolIndicator (π x) * P.contrast x ∂P.PX‖
      ≤ (2 : ℝ) * P.PX.real Set.univ := by
    apply norm_integral_le_of_norm_le_const (μ := P.PX)
      (f := fun x => boolIndicator (π x) * P.contrast x) (C := (2 : ℝ))
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    have hb : |boolIndicator (π x)| ≤ (1 : ℝ) := by cases π x <;> simp [boolIndicator]
    nlinarith [mul_le_mul hb (hτbound x) (abs_nonneg (P.contrast x))
      (by norm_num : (0 : ℝ) ≤ 1)]
  simpa [lawWelfare, Real.norm_eq_abs] using hnorm

private lemma lawRegret_le_four (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    lawRegret P π ≤ (4 : ℝ) := by
  have hoptm : Measurable (lawOptimalPolicy P) := lawOptimalPolicy_measurable P hwf
  have hopt := abs_lawWelfare_le_two' P (lawOptimalPolicy P) hwf hbdd hoptm
  have hpi := abs_lawWelfare_le_two' P π hwf hbdd hπ
  have hmain : lawWelfare P (lawOptimalPolicy P) - lawWelfare P π ≤ (4 : ℝ) := by
    linarith [(abs_le.mp hopt).2, (abs_le.mp hpi).1]
  simpa [lawRegret, regret, lawWelfare, lawOptimalPolicy] using hmain

private lemma measurable_empirical_score {n K : ℕ} (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (hμ0meas : ∀ k, Measurable (muHat0 k))
    (hμ1meas : ∀ k, Measurable (muHat1 k)) (hemeas : ∀ k, Measurable (eHat k))
    (π : Policy 𝒳) (hπ : Measurable π) :
    Measurable (fun sample : Fin n → Observation 𝒳 =>
      empiricalWelfareScore q muHat0 muHat1 eHat assign sample π) := by
  have hsum : Measurable (fun sample : Fin n → Observation 𝒳 =>
      ∑ i : Fin n, boolIndicator (π (sample i).X) *
        clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i)) (eHat (assign i))
          (sample i)) := by
    apply Finset.measurable_sum
    intro i _
    have hX := measurable_observation_X.comp (measurable_pi_apply i :
      Measurable (fun sample : Fin n → Observation 𝒳 => sample i))
    have hind : Measurable (fun sample : Fin n → Observation 𝒳 =>
        boolIndicator (π (sample i).X)) :=
      (measurable_of_finite boolIndicator).comp (hπ.comp hX)
    have hO : Measurable (fun sample : Fin n → Observation 𝒳 => sample i) :=
      measurable_pi_apply i
    have hA : Measurable (fun sample : Fin n → Observation 𝒳 =>
        boolIndicator (sample i).A) := measurable_boolIndicator_observation_A.comp hO
    have hY : Measurable (fun sample : Fin n → Observation 𝒳 => (sample i).Y) :=
      measurable_observation_Y.comp hO
    have hμ0 := (hμ0meas (assign i)).comp hX
    have hμ1 := (hμ1meas (assign i)).comp hX
    have hcp := (measurable_clippedPropensity q (hemeas (assign i))).comp hX
    have hscore : Measurable (fun sample : Fin n → Observation 𝒳 =>
        clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i)) (eHat (assign i))
          (sample i)) := by
      unfold clippedAIPWScore
      exact ((hμ1.sub hμ0).add ((hA.div hcp).mul (hY.sub hμ1))).sub
        (((measurable_const.sub hA).div (measurable_const.sub hcp)).mul (hY.sub hμ0))
    exact hind.mul hscore
  simpa [empiricalWelfareScore] using hsum.const_mul ((n : ℝ)⁻¹)

private lemma feasible_near_nonempty {n K : ℕ} (q : ℝ) (enum : ℕ → Policy 𝒳)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (sample : Fin n → Observation 𝒳) (hn : 0 < n) :
    ({j : ℕ | ∀ j',
      empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j') ≤
        empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j) + (n : ℝ)⁻¹}).Nonempty := by
  let score : ℕ → ℝ := fun j =>
    empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j)
  let Γ : Fin n → ℝ := fun i =>
    clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i)) (eHat (assign i)) (sample i)
  have hscore_le : ∀ j, score j ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |Γ i| := by
    intro j
    have hterm : ∀ i : Fin n, boolIndicator (enum j (sample i).X) * Γ i ≤ |Γ i| := by
      intro i
      cases enum j (sample i).X <;> simp [boolIndicator, le_abs_self]
    have hsum : ∑ i : Fin n, boolIndicator (enum j (sample i).X) * Γ i
        ≤ ∑ i : Fin n, |Γ i| := Finset.sum_le_sum (fun i _ => hterm i)
    have hinv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    simpa [score, empiricalWelfareScore, Γ] using mul_le_mul_of_nonneg_left hsum hinv
  let S : Set ℝ := Set.range score
  have hSnon : S.Nonempty := Set.range_nonempty score
  have hSbdd : BddAbove S := by
    refine ⟨(n : ℝ)⁻¹ * ∑ i : Fin n, |Γ i|, ?_⟩
    rintro y ⟨j, rfl⟩
    exact hscore_le j
  have hinv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
  rcases exists_lt_of_lt_csSup hSnon (sub_lt_self _ hinv_pos) with ⟨a, ⟨j, rfl⟩, hj⟩
  refine ⟨j, fun j' => ?_⟩
  have hj' : score j' ≤ sSup S := le_csSup hSbdd ⟨j', rfl⟩
  have hsup : sSup S ≤ score j + (n : ℝ)⁻¹ := by linarith
  simpa [score] using hj'.trans hsup

private lemma measurable_feasible_regret {n K : ℕ} (P : ObservedLaw 𝒳) (q : ℝ)
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (assign : Fin n → Fin K) (policySet : Set (Policy 𝒳)) (dPi : ℕ)
    (hvc : PolicyClassVC policySet dPi) (henum : ∀ j, enum j ∈ policySet)
    (hμ0meas : ∀ k, Measurable (muHat0 k))
    (hμ1meas : ∀ k, Measurable (muHat1 k)) (hemeas : ∀ k, Measurable (eHat k))
    (hn : 0 < n) :
    Measurable (fun s : Fin n → Observation 𝒳 =>
      lawRegret P (feasibleERM q enum muHat0 muHat1 eHat assign s)) := by
  classical
  let score : ℕ → (Fin n → Observation 𝒳) → ℝ := fun j sample =>
    empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j)
  let near : (Fin n → Observation 𝒳) → ℕ → Prop := fun sample j =>
    ∀ j', score j' sample ≤ score j sample + (n : ℝ)⁻¹
  let sel : (Fin n → Observation 𝒳) → ℕ := fun sample => sInf {j | near sample j}
  have hscore : ∀ j, Measurable (score j) := fun j =>
    measurable_empirical_score q muHat0 muHat1 eHat assign hμ0meas hμ1meas hemeas
      (enum j) (hvc.1 (enum j) (henum j))
  have hnear : ∀ j, MeasurableSet {sample : Fin n → Observation 𝒳 | near sample j} := by
    intro j
    simpa [near, Set.setOf_forall] using MeasurableSet.iInter (fun j' =>
      measurableSet_le (hscore j') ((hscore j).add measurable_const))
  have hsel_fiber : ∀ j, MeasurableSet {sample : Fin n → Observation 𝒳 | sel sample = j} := by
    intro j
    have hlower : MeasurableSet {sample : Fin n → Observation 𝒳 |
        ∀ k : ℕ, k < j → ¬ near sample k} := by
      simpa [Set.setOf_forall] using MeasurableSet.iInter (fun k => by
        by_cases hk : k < j
        · simpa [hk, Set.compl_setOf] using (hnear k).compl
        · simp [hk])
    have hchar : {sample : Fin n → Observation 𝒳 | sel sample = j} =
        {sample | near sample j ∧ ∀ k : ℕ, k < j → ¬ near sample k} := by
      ext sample
      let A : Set ℕ := {m | near sample m}
      have hA : A.Nonempty := by
        simpa [A, near, score] using feasible_near_nonempty q enum muHat0 muHat1 eHat assign sample hn
      constructor
      · intro hs
        constructor
        · have hm : near sample (sel sample) := by simpa [sel, A] using Nat.sInf_mem hA
          rwa [hs] at hm
        · intro k hk hnk
          have hle : sInf A ≤ k := Nat.sInf_le (by simpa [A] using hnk)
          have hsInf : sInf A = j := hs
          omega
      · rintro ⟨hj, hno⟩
        change sInf A = j
        apply le_antisymm
        · exact Nat.sInf_le (by simpa [A] using hj)
        · apply le_of_not_gt
          intro hlt
          exact hno (sInf A) hlt (by simpa [A] using Nat.sInf_mem hA)
    rw [hchar]
    exact (hnear j).inter hlower
  have hsel : Measurable sel := measurable_to_countable' hsel_fiber
  have hreg : Measurable (fun j : ℕ => lawRegret P (enum j)) := measurable_of_countable _
  simpa [feasibleERM, sel, near, score] using hreg.comp hsel

private lemma clipped_score_abs_le_six (q : ℝ) (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (O : Observation 𝒳)
    (hbn : ∀ x, muHat0 x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) (hY : O.Y ∈ Set.Icc (-1 : ℝ) 1) :
    |clippedAIPWScore q muHat0 muHat1 eHat O| ≤ 6 / q := by
  let cp := clippedPropensity q eHat O.X
  have hcp : q ≤ cp ∧ cp ≤ 1 - q := by
    unfold cp clippedPropensity
    exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
  have hcp_pos : 0 < cp := hq.trans_le hcp.1
  have hcp' : 0 < 1 - cp := by linarith [hcp.2]
  have hinv : cp⁻¹ ≤ q⁻¹ := by rw [inv_le_inv₀ hcp_pos hq]; exact hcp.1
  have hinv' : (1 - cp)⁻¹ ≤ q⁻¹ := by
    rw [inv_le_inv₀ hcp' hq]
    linarith [hcp.2]
  have habs : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 → |z| ≤ (1 : ℝ) := fun z hz =>
    abs_le.mpr ⟨hz.1, hz.2⟩
  have hμ0 := habs (muHat0 O.X) (hbn O.X).1
  have hμ1 := habs (muHat1 O.X) (hbn O.X).2
  have hY' := habs O.Y hY
  have hbool : |boolIndicator O.A| ≤ (1 : ℝ) := by cases O.A <;> simp [boolIndicator]
  have hbool' : |1 - boolIndicator O.A| ≤ (1 : ℝ) := by cases O.A <;> simp [boolIndicator]
  have hc : |muHat1 O.X - muHat0 O.X| ≤ (2 : ℝ) := by
    calc _ ≤ |muHat1 O.X| + |muHat0 O.X| := abs_sub _ _
         _ ≤ 1 + 1 := add_le_add hμ1 hμ0
         _ = 2 := by norm_num
  have hd1 : |O.Y - muHat1 O.X| ≤ (2 : ℝ) := by
    calc _ ≤ |O.Y| + |muHat1 O.X| := abs_sub _ _
         _ ≤ 1 + 1 := add_le_add hY' hμ1
         _ = 2 := by norm_num
  have hd0 : |O.Y - muHat0 O.X| ≤ (2 : ℝ) := by
    calc _ ≤ |O.Y| + |muHat0 O.X| := abs_sub _ _
         _ ≤ 1 + 1 := add_le_add hY' hμ0
         _ = 2 := by norm_num
  have ht1 : |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)| ≤ 2 / q := by
    calc
      _ = |boolIndicator O.A| * cp⁻¹ * |O.Y - muHat1 O.X| := by
        rw [abs_mul, abs_div, abs_of_pos hcp_pos, div_eq_mul_inv]
      _ ≤ 1 * q⁻¹ * 2 := by gcongr
      _ = 2 / q := by ring
  have ht0 : |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| ≤ 2 / q := by
    calc
      _ = |1 - boolIndicator O.A| * (1 - cp)⁻¹ * |O.Y - muHat0 O.X| := by
        rw [abs_mul, abs_div, abs_of_pos hcp', div_eq_mul_inv]
      _ ≤ 1 * q⁻¹ * 2 := by gcongr
      _ = 2 / q := by ring
  unfold clippedAIPWScore
  calc
    |muHat1 O.X - muHat0 O.X + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X) -
        ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
        ≤ |muHat1 O.X - muHat0 O.X| +
          |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)| +
          |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
            calc _ ≤ |muHat1 O.X - muHat0 O.X +
                (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)| +
                |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := abs_sub _ _
                 _ ≤ _ := by gcongr; exact abs_add_le _ _
    _ ≤ 2 + 2 / q + 2 / q := by gcongr
    _ ≤ 6 / q := by
      have h2 : (2 : ℝ) ≤ 2 / q := by rw [le_div_iff₀ hq]; linarith
      have h6 : (6 : ℝ) / q = 2 / q + 2 / q + 2 / q := by ring
      linarith

/-- Discharges the four Bochner integrability/`BddAbove` side conditions (`hBochner`) of the
feasible achievability bound: eventually in `n`, for every law in the class, the selected
regret loss is integrable, and the pooled/fold localized offset-process suprema over the
policy class are integrable, `BddAbove`, and (per fold) integrable. -/
lemma bochner_discharge {K : ℕ}
    (α γ Cm u0 Co co underlineP : ℝ)
    (policySet : Set (Policy 𝒳)) (dPi : ℕ)
    (enum : ℕ → Policy 𝒳)
    (muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ)
    (assign : (m : ℕ) → Fin m → Fin K)
    (qSeq : ℕ → ℝ)
    (hvc : PolicyClassVC policySet dPi)
    (hskel : DenseSkeleton enum policySet)
    (hbn : ∀ k : Fin K,
      BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k))
    (hμ0meas : ∀ n k, Measurable (muHat0 n k))
    (hμ1meas : ∀ n k, Measurable (muHat1 n k))
    (hemeas : ∀ n k, Measurable (eHat n k))
    (hq_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < qSeq n)
    (hq_half : ∀ᶠ n : ℕ in Filter.atTop, qSeq n ≤ 1 / 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P →
          let g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
            clippedPolicyIncrement P (qSeq n) (muHat0 n) (muHat1 n) (eHat n)
          Integrable (fun sample : Fin n → Observation 𝒳 =>
              lawRegret P
                (feasibleERM (qSeq n) enum (muHat0 n) (muHat1 n) (eHat n)
                  (assign n) sample))
            (Measure.pi (fun _ : Fin n => P.dataMeasure)) ∧
          Integrable (fun sample : Fin n → Observation 𝒳 =>
              sSup ((fun π =>
                max 0 (2 * |pooledCrossfitProcess P g (assign n) sample π| -
                  lawRegret P π / 4)) '' policySet))
            (Measure.pi (fun _ : Fin n => P.dataMeasure)) ∧
          (∀ sample : Fin n → Observation 𝒳,
              BddAbove ((fun π =>
                max 0 (2 * |pooledCrossfitProcess P g (assign n) sample π| -
                  lawRegret P π / 4)) '' policySet)) ∧
          (∀ k : Fin K,
            Integrable
              (fun sample : foldIndex (assign n) k → Observation 𝒳 =>
                foldOffsetSubSup P g (assign n) policySet k sample)
              (Measure.pi (fun _ : foldIndex (assign n) k => P.dataMeasure))) := by
  classical
  filter_upwards [hq_pos, hq_half,
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hqpos hqhalf hn
  intro P hLaw
  letI : IsProbabilityMeasure P.dataMeasure := hLaw.wf.1
  intro g
  let q : ℝ := qSeq n
  let B : ℝ := (36 : ℝ) / q
  let gT : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrementTrunc P q B (muHat0 n) (muHat1 n) (eHat n)
  have hqn : 0 < q := by simpa [q] using hqpos
  have hq1 : q ≤ 1 / 2 := by simpa [q] using hqhalf
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbn' : ∀ k x, (muHat0 n) k x ∈ Set.Icc (-1 : ℝ) 1 ∧
      (muHat1 n) k x ∈ Set.Icc (-1 : ℝ) 1 := fun k x => hbn k n x
  have hgTmeas : ∀ k (ρ : Policy 𝒳), Measurable ρ → Measurable (gT k ρ) := by
    intro k ρ hρ
    exact clippedPolicyIncrementTrunc_measurable P q B (muHat0 n) (muHat1 n) (eHat n)
      k ρ hLaw.wf hρ (hμ0meas n k) (hμ1meas n k) (hemeas n k)
  have hgTbound : ∀ k π O, |gT k π O| ≤ B := by
    intro k π O
    exact clippedPolicyIncrementTrunc_bound P q B (muHat0 n) (muHat1 n) (eHat n) k π O hB
  obtain ⟨Pi0, hPi0count, hPi0sub, hPi0dense⟩ := hvc.2.1
  have hpoolbound : ∀ sample π, |pooledCrossfitProcess P gT (assign n) sample π| ≤ 2 * B := by
    intro sample π
    simpa [pooledCrossfitProcess] using
      (abs_centered_average_le P (fun i O => gT (assign n i) π O) sample B hB
        (fun i O => hgTbound (assign n i) π O))
  have hfoldbound : ∀ (k : Fin K) (sample : foldIndex (assign n) k → Observation 𝒳)
      (π : Policy 𝒳),
      |((Fintype.card (foldIndex (assign n) k) : ℝ)⁻¹) *
          ∑ i, (gT k π (sample i) - ∫ O, gT k π O ∂P.dataMeasure)| ≤ 2 * B := by
    intro k sample π
    exact abs_centered_average_le P (fun _ O => gT k π O) sample B hB
      (fun _ O => hgTbound k π O)
  have hregnonneg : ∀ π ∈ policySet, 0 ≤ lawRegret P π := by
    intro π hπ
    exact lawRegret_nonneg P π hLaw.wf hLaw.bdd (hvc.1 π hπ)
  have hoffbound : ∀ (sample : Fin n → Observation 𝒳), ∀ π ∈ policySet,
      |max 0 (2 * |pooledCrossfitProcess P gT (assign n) sample π| - lawRegret P π / 4)|
        ≤ 4 * B + 1 := by
    intro sample π hπ
    rw [abs_of_nonneg (le_max_left _ _)]
    apply max_le
    · nlinarith [hB]
    · nlinarith [hpoolbound sample π, hregnonneg π hπ]
  have hfoldoffbound : ∀ (k : Fin K) (sample : foldIndex (assign n) k → Observation 𝒳),
      ∀ π ∈ policySet,
      |max 0 (2 * |((Fintype.card (foldIndex (assign n) k) : ℝ)⁻¹) *
          ∑ i, (gT k π (sample i) - ∫ O, gT k π O ∂P.dataMeasure)| - lawRegret P π / 4)|
        ≤ 4 * B + 1 := by
    intro k sample π hπ
    rw [abs_of_nonneg (le_max_left _ _)]
    apply max_le
    · nlinarith [hB]
    · nlinarith [hfoldbound k sample π, hregnonneg π hπ]
  have hIntRegret : Integrable (fun sample : Fin n → Observation 𝒳 =>
      lawRegret P (feasibleERM q enum (muHat0 n) (muHat1 n) (eHat n) (assign n) sample))
      (Measure.pi (fun _ : Fin n => P.dataMeasure)) := by
    refine Integrable.of_bound
      (measurable_feasible_regret P q enum (muHat0 n) (muHat1 n) (eHat n) (assign n)
        policySet dPi hvc hskel.1 (hμ0meas n) (hμ1meas n) (hemeas n)
        (Nat.pos_of_ne_zero (by omega))).aestronglyMeasurable 4 ?_
    filter_upwards with sample
    have hmem := hskel.1 (sInf {j : ℕ | ∀ j',
      empiricalWelfareScore q (muHat0 n) (muHat1 n) (eHat n) (assign n) sample (enum j') ≤
        empiricalWelfareScore q (muHat0 n) (muHat1 n) (eHat n) (assign n) sample (enum j) +
          (n : ℝ)⁻¹})
    exact (abs_le.mpr ⟨
      le_trans (by norm_num) (lawRegret_nonneg P _ hLaw.wf hLaw.bdd (hvc.1 _ hmem)),
      lawRegret_le_four P _ hLaw.wf hLaw.bdd (hvc.1 _ hmem)⟩)
  have hIntPoolT : Integrable (fun sample : Fin n → Observation 𝒳 =>
      sSup ((fun π => max 0 (2 * |pooledCrossfitProcess P gT (assign n) sample π| -
        lawRegret P π / 4)) '' policySet))
      (Measure.pi (fun _ : Fin n => P.dataMeasure)) := by
    refine integrable_sSup_image_of_countable_dense _ policySet Pi0 _ (4 * B + 1)
      (by nlinarith [hB]) hPi0count ?_ ?_ hoffbound
    · intro π hπ
      exact measurable_pooled_offset_eval P gT (assign n) π
        (fun k => hgTmeas k π (hvc.1 π (hPi0sub hπ)))
    · intro sample
      refine sSup_image_eq_of_dense_tendsto _ policySet Pi0 hPi0sub
        (bddAbove_image_of_bound policySet _ (4 * B + 1) hoffbound sample) ?_
      intro π hπ
      rcases hPi0dense π hπ with ⟨seq, hseq, hseqconv⟩
      refine ⟨seq, hseq, ?_⟩
      have hp := pooledCrossfitProcess_tendsto_of_skeleton P gT B hB hgTbound
        (fun k => clippedPolicyIncrementTrunc_compatible P q B (muHat0 n) (muHat1 n) (eHat n) k)
        hgTmeas (assign n) sample π seq
        (fun j => hvc.1 (seq j) (hPi0sub (hseq j))) hseqconv
      have hr := lawRegret_tendsto_of_skeleton P hLaw.wf hLaw.bdd π seq
        (hvc.1 π hπ) (fun j => hvc.1 (seq j) (hPi0sub (hseq j))) hseqconv
      exact (tendsto_const_nhds.max ((hp.abs.const_mul 2).sub (hr.div_const 4)))
  have hIntFoldT : ∀ k : Fin K, Integrable
      (fun sample : foldIndex (assign n) k → Observation 𝒳 =>
        foldOffsetSubSup P gT (assign n) policySet k sample)
      (Measure.pi (fun _ : foldIndex (assign n) k => P.dataMeasure)) := by
    intro k
    unfold foldOffsetSubSup
    refine integrable_sSup_image_of_countable_dense _ policySet Pi0 _ (4 * B + 1)
      (by nlinarith [hB]) hPi0count ?_ ?_ (hfoldoffbound k)
    · intro π hπ
      exact measurable_fold_offset_eval P gT (assign n) k π
        (fun k' => hgTmeas k' π (hvc.1 π (hPi0sub hπ)))
    · intro sample
      refine sSup_image_eq_of_dense_tendsto _ policySet Pi0 hPi0sub
        (bddAbove_image_of_bound policySet _ (4 * B + 1) (hfoldoffbound k) sample) ?_
      intro π hπ
      rcases hPi0dense π hπ with ⟨seq, hseq, hseqconv⟩
      refine ⟨seq, hseq, ?_⟩
      have hp := foldSubCentered_tendsto_of_skeleton P gT B hB hgTbound
        (fun k => clippedPolicyIncrementTrunc_compatible P q B (muHat0 n) (muHat1 n) (eHat n) k)
        hgTmeas (assign n) k sample π seq
        (fun j => hvc.1 (seq j) (hPi0sub (hseq j))) hseqconv
      have hr := lawRegret_tendsto_of_skeleton P hLaw.wf hLaw.bdd π seq
        (hvc.1 π hπ) (fun j => hvc.1 (seq j) (hPi0sub (hseq j))) hseqconv
      exact (tendsto_const_nhds.max ((hp.abs.const_mul 2).sub (hr.div_const 4)))
  -- Uniform-in-`π` bound on the UNTRUNCATED pooled process, for a fixed sample.
  have hpool_untrunc : ∀ (sample : Fin n → Observation 𝒳) (π : Policy 𝒳),
      |pooledCrossfitProcess P g (assign n) sample π|
        ≤ (n : ℝ)⁻¹ * ∑ i : Fin n,
            |clippedAIPWScore q (muHat0 n (assign n i)) (muHat1 n (assign n i))
              (eHat n (assign n i)) (sample i)| + 6 / q := by
    intro sample π
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h6q : (0 : ℝ) ≤ 6 / q := le_of_lt (div_pos (by norm_num) hqn)
    set Γ : Fin n → ℝ := fun i =>
      clippedAIPWScore q (muHat0 n (assign n i)) (muHat1 n (assign n i))
        (eHat n (assign n i)) (sample i) with hΓ
    have hscore_ae : ∀ k : Fin K, ∀ᵐ O ∂P.dataMeasure,
        |clippedAIPWScore q (muHat0 n k) (muHat1 n k) (eHat n k) O| ≤ 6 / q := by
      intro k
      filter_upwards [hLaw.bdd.1] with O hO
      exact clipped_score_abs_le_six q (muHat0 n k) (muHat1 n k) (eHat n k) O
        (hbn' k) hqn hq1 hO
    have hgeq : ∀ (k : Fin K) (O : Observation 𝒳),
        g k π O = (boolIndicator (π O.X) - boolIndicator (lawOptimalPolicy P O.X)) *
          clippedAIPWScore q (muHat0 n k) (muHat1 n k) (eHat n k) O := fun k O => rfl
    have hterm : ∀ i : Fin n,
        |g (assign n i) π (sample i) - ∫ O, g (assign n i) π O ∂P.dataMeasure|
          ≤ |Γ i| + 6 / q := by
      intro i
      have hb : |boolIndicator (π (sample i).X) -
          boolIndicator (lawOptimalPolicy P (sample i).X)| ≤ 1 :=
        boolIndicator_diff_abs_le_one _ _
      have h1 : |g (assign n i) π (sample i)| ≤ |Γ i| := by
        rw [hgeq, abs_mul, hΓ]
        calc |boolIndicator (π (sample i).X) -
                boolIndicator (lawOptimalPolicy P (sample i).X)| *
              |clippedAIPWScore q (muHat0 n (assign n i)) (muHat1 n (assign n i))
                (eHat n (assign n i)) (sample i)|
            ≤ 1 * |clippedAIPWScore q (muHat0 n (assign n i)) (muHat1 n (assign n i))
                (eHat n (assign n i)) (sample i)| :=
              mul_le_mul_of_nonneg_right hb (abs_nonneg _)
          _ = |Γ i| := by rw [one_mul, hΓ]
      have h2 : |∫ O, g (assign n i) π O ∂P.dataMeasure| ≤ 6 / q := by
        have hae : ∀ᵐ O ∂P.dataMeasure, ‖g (assign n i) π O‖ ≤ 6 / q := by
          filter_upwards [hscore_ae (assign n i)] with O hO
          rw [Real.norm_eq_abs, hgeq, abs_mul]
          have hbO : |boolIndicator (π O.X) -
              boolIndicator (lawOptimalPolicy P O.X)| ≤ 1 :=
            boolIndicator_diff_abs_le_one _ _
          calc |boolIndicator (π O.X) - boolIndicator (lawOptimalPolicy P O.X)| *
                |clippedAIPWScore q (muHat0 n (assign n i)) (muHat1 n (assign n i))
                  (eHat n (assign n i)) O|
              ≤ 1 * (6 / q) :=
                mul_le_mul hbO hO (abs_nonneg _) (by norm_num)
            _ = 6 / q := one_mul _
        have hnorm := norm_integral_le_of_norm_le_const (μ := P.dataMeasure) hae
        have huniv : P.dataMeasure.real Set.univ = 1 := by
          simp [MeasureTheory.measureReal_def, measure_univ]
        rw [huniv, mul_one, Real.norm_eq_abs] at hnorm
        exact hnorm
      calc |g (assign n i) π (sample i) - ∫ O, g (assign n i) π O ∂P.dataMeasure|
          ≤ |g (assign n i) π (sample i)| + |∫ O, g (assign n i) π O ∂P.dataMeasure| :=
            abs_sub _ _
        _ ≤ |Γ i| + 6 / q := add_le_add h1 h2
    have hsum_bound :
        |∑ i : Fin n, (g (assign n i) π (sample i) -
            ∫ O, g (assign n i) π O ∂P.dataMeasure)|
          ≤ ∑ i : Fin n, (|Γ i| + 6 / q) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hterm i))
    have hsplit : ∑ i : Fin n, (|Γ i| + 6 / q)
        = (∑ i : Fin n, |Γ i|) + (n : ℝ) * (6 / q) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [pooledCrossfitProcess, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    calc (n : ℝ)⁻¹ *
          |∑ i : Fin n, (g (assign n i) π (sample i) -
            ∫ O, g (assign n i) π O ∂P.dataMeasure)|
        ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, (|Γ i| + 6 / q) :=
          mul_le_mul_of_nonneg_left hsum_bound (by positivity)
      _ = (n : ℝ)⁻¹ * ((∑ i : Fin n, |Γ i|) + (n : ℝ) * (6 / q)) := by rw [hsplit]
      _ = (n : ℝ)⁻¹ * ∑ i : Fin n, |Γ i| + 6 / q := by
          field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [q] using hIntRegret
  · exact hIntPoolT.congr (pooledOffsetSup_trunc_eq_original_ae_36 P q (muHat0 n)
      (muHat1 n) (eHat n) (assign n) policySet hLaw.wf hLaw.bdd hbn' hqn hq1)
  · intro sample
    refine ⟨2 * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        |clippedAIPWScore q (muHat0 n (assign n i)) (muHat1 n (assign n i))
          (eHat n (assign n i)) (sample i)| + 6 / q), ?_⟩
    rintro y ⟨π, hπ, rfl⟩
    have hp := hpool_untrunc sample π
    have hreg : 0 ≤ lawRegret P π := hregnonneg π hπ
    have h6q : (0 : ℝ) ≤ 6 / q := le_of_lt (div_pos (by norm_num) hqn)
    have hsumnn : (0 : ℝ) ≤ (n : ℝ)⁻¹ * ∑ i : Fin n,
        |clippedAIPWScore q (muHat0 n (assign n i)) (muHat1 n (assign n i))
          (eHat n (assign n i)) (sample i)| := by positivity
    apply max_le
    · linarith
    · linarith
  · intro k
    exact (hIntFoldT k).congr (foldOffsetSubSup_trunc_eq_original_ae_36 P q (muHat0 n)
      (muHat1 n) (eHat n) (assign n) policySet k hLaw.wf hLaw.bdd hbn' hqn hq1)

end CausalSmith.Stat.PolicyRegretMarginOverlap
