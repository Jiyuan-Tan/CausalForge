/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balanced base-law sanity check

This file contains the symmetric-base sanity check and its balanced tangent
witness, separated from `NeymanAlgebra` so the algebra file stays small.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.NeymanAlgebra
import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ExtremalProduct

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics Filter
open scoped BigOperators Topology

-- @node: badFirst_measurable
/-- The event that some realized propensity coordinate differs from a fixed
constant is measurable. -/
lemma badFirst_measurable (T : ℕ) (c : ℝ) :
    MeasurableSet {path : Fin T → NeymanRecord | ∃ t : Fin T, (path t).1 ≠ c} := by
  classical
  simpa [Set.setOf_exists] using
    (MeasurableSet.iUnion fun t : Fin T =>
      (measurableSet_singleton c).compl.preimage
        (measurable_fst.comp (measurable_pi_apply t)))

-- @node: stepKernel_const_first
/-- A one-step kernel emitted at propensity `c` has first record coordinate `c`
almost surely. -/
lemma stepKernel_const_first (nu : Measure (ℝ × ℝ)) (c : ℝ) :
    ∀ᵐ r ∂stepKernel nu c, r.1 = c := by
  rw [MeasureTheory.ae_iff]
  rw [stepKernel]
  let S : Set NeymanRecord := {r | ¬r.1 = c}
  have hs : MeasurableSet S := by
    dsimp [S]
    exact (measurableSet_singleton c).compl.preimage measurable_fst
  apply le_antisymm
  · calc
      (nu.bind fun yo =>
          (Causalean.Mathlib.Probability.bernoulliLaw c).bind fun a =>
            Measure.dirac (c, a, if a = 1 then yo.2 else yo.1)) S
          ≤ ∫⁻ yo, ((Causalean.Mathlib.Probability.bernoulliLaw c).bind fun a =>
            Measure.dirac (c, a, if a = 1 then yo.2 else yo.1)) S ∂nu :=
            Measure.bind_apply_le _ hs
      _ ≤ ∫⁻ _yo, (0 : ENNReal) ∂nu := by
        apply lintegral_mono
        intro yo
        have hinner :
            ((Causalean.Mathlib.Probability.bernoulliLaw c).bind fun a =>
              Measure.dirac (c, a, if a = 1 then yo.2 else yo.1)) S = 0 := by
          apply le_antisymm
          · calc
              ((Causalean.Mathlib.Probability.bernoulliLaw c).bind fun a =>
                  Measure.dirac (c, a, if a = 1 then yo.2 else yo.1)) S
                  ≤ ∫⁻ a,
                    (Measure.dirac (c, a, if a = 1 then yo.2 else yo.1)) S
                      ∂(Causalean.Mathlib.Probability.bernoulliLaw c) :=
                    Measure.bind_apply_le _ hs
              _ = 0 := by simp [S]
          · exact zero_le _
        exact le_of_eq hinner
      _ = 0 := by simp
  · exact zero_le _

-- @node: snocRecord_measurable
/-- Appending a record to a finite history is measurable as a function of the new
record. -/
lemma snocRecord_measurable {T : ℕ} (hist : Fin T → NeymanRecord) :
    Measurable (fun r : NeymanRecord => (Fin.snoc hist r : Fin (T + 1) → NeymanRecord)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simpa [Fin.snoc_last] using (measurable_id : Measurable (fun r : NeymanRecord => r))
  · intro j
    simp [Fin.snoc_castSucc]

-- @node: pathLaw_const_policy_first
/-- Under the constant policy `c`, every realized propensity coordinate in
`pathLaw` is `c` almost surely. -/
lemma pathLaw_const_policy_first (nu : Measure (ℝ × ℝ)) (c : ℝ) :
    ∀ T : ℕ, ∀ᵐ path ∂pathLaw nu (fun _ _ => c) T, ∀ t : Fin T, (path t).1 = c := by
  intro T
  induction T with
  | zero =>
      simp [pathLaw]
  | succ T ih =>
      rw [MeasureTheory.ae_iff]
      let S : Set (Fin (T + 1) → NeymanRecord) :=
        {path | ¬ ∀ t : Fin (T + 1), (path t).1 = c}
      have hS_eq :
          S = {path : Fin (T + 1) → NeymanRecord | ∃ t : Fin (T + 1), (path t).1 ≠ c} := by
        ext path
        simp [S]
      have hS_meas : MeasurableSet S := by
        rw [hS_eq]
        exact badFirst_measurable (T + 1) c
      rw [pathLaw]
      apply le_antisymm
      · calc
          ((pathLaw nu (fun x x_1 => c) T).bind fun hist =>
              Measure.map (Fin.snoc hist) (stepKernel nu c)) S
              ≤ ∫⁻ hist, (Measure.map (Fin.snoc hist) (stepKernel nu c)) S
                  ∂pathLaw nu (fun x x_1 => c) T :=
                Measure.bind_apply_le _ hS_meas
          _ ≤ ∫⁻ _hist, (0 : ENNReal) ∂pathLaw nu (fun x x_1 => c) T := by
            apply lintegral_mono_ae
            filter_upwards [ih] with hist hhist
            apply le_of_eq
            rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
            refine
              (MeasureTheory.ae_map_iff (snocRecord_measurable hist).aemeasurable
                hS_meas.compl).2 ?_
            filter_upwards [stepKernel_const_first nu c] with r hr
            intro hmem
            have hnot : Fin.snoc hist r ∉ S := by
              intro hbad
              apply hbad
              intro i
              refine Fin.lastCases ?_ ?_ i
              · simpa [Fin.snoc_last] using hr
              · intro j
                simpa [Fin.snoc_castSucc] using hhist j
            exact hnot hmem
          _ = 0 := by simp
      · exact zero_le _

-- @node: balanced_diagonal_threePoint_mtan_witness
/-- A diagonal coupling of a symmetric three-point law on `{0, 1/2, 1}` gives a
balanced `M_tan` law (equal arm root second moments) with positive local
complexity.  (Self-contained bounded-outcome construction; independent of the
removed closed-form-frontier envelope.) -/
lemma balanced_diagonal_threePoint_mtan_witness :
    ∃ nu : Measure (ℝ × ℝ), MTan nu
      ∧ rootSecondMoment nu 0 = rootSecondMoment nu 1
      ∧ 0 < localComplexity nu := by
  exact extremalProduct_balanced_mtan_positive_complexity (1 / 2 : ℝ)
    (by norm_num) (by norm_num)

-- @node: prop:balanced-base-law
/-- Balanced base-law sanity check: when `m₀ = m₁` the oracle allocation is `1/2`
and the fixed `π_t = 1/2` design has zero cumulative regret; yet there exist
balanced `M_tan` instances with strictly positive local complexity. -/
lemma balanced_base_law :
    (∀ (nu : Measure (ℝ × ℝ)) (Alg : AdaptiveAlgorithm) (T : ℕ),
        MTan nu → rootSecondMoment nu 0 = rootSecondMoment nu 1 →
        (∀ (t : ℕ) (hist : Fin t → NeymanRecord), Alg.policy t hist = 1 / 2) →
        oracleAllocation nu = 1 / 2 ∧ cumulativeNeymanRegret Alg nu T = 0)
      ∧ (∃ nu : Measure (ℝ × ℝ), MTan nu
          ∧ rootSecondMoment nu 0 = rootSecondMoment nu 1
          ∧ 0 < localComplexity nu) := by
  constructor
  · intro nu Alg T hnu hbal _hfixed
    have halloc : oracleAllocation nu = 1 / 2 := by
      rw [oracleAllocation_eq_root_ratio]
      have hmpos : 0 < rootSecondMoment nu 1 := hnu.interiorMoments 1
      rw [hbal]
      field_simp [ne_of_gt hmpos]
      ring_nf
    constructor
    · exact halloc
    · have hpol : Alg.policy = fun _ _ => (1 / 2 : ℝ) := by
        funext t hist
        exact _hfixed t hist
      have hpi :
          ∀ᵐ path ∂pathLaw nu Alg.policy T, ∀ t : Fin T, (path t).1 = 1 / 2 := by
        simpa [hpol] using pathLaw_const_policy_first nu (1 / 2 : ℝ) T
      apply integral_eq_zero_of_ae
      filter_upwards [hpi] with path hpath
      simp [hpath, neymanGap, halloc]
  · exact balanced_diagonal_threePoint_mtan_witness

end CausalSmith.Stat.NeymanRegretMinimax
