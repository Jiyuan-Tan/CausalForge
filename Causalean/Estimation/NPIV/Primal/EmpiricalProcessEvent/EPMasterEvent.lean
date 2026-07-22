/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEvents

/-!
States the explicit-rate empirical-process master event for the NPIV primal
estimator. The module packages the localized deviation and
centered-regularizer bounds in the form consumed by the rate proof.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## EP inequality and centred-regulariser bound (explicit-rate form)

The two helpers below are the post-substitution forms of two displays in
the proof sketch of `thm:est-trae-rate-theorem`
(`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`):

* `ep_inequality_from_localized` — proof-sketch line 308: the EP step
  controls the population weak-norm excess via the **empirical**
  regulariser difference `λ(‖h*‖²_{A(n)} − ‖ĥ‖²_{A(n)})`, with the
  regulariser term carried with coefficient `1` (it comes for free from
  the empirical sup-min optimality of `ĥ_n`).

* `centred_regulariser_bound_from_localized` — proof-sketch line 345:
  the centred (empirical-vs-population) regulariser gap
  `λ((‖h*‖²_{A(n)} − ‖ĥ‖²_{A(n)}) − (‖h*‖² − ‖ĥ‖²))` is controlled by
  the localized rate.

Both displays use the **fold-A empirical norm**
`‖h‖²_{A(n)} = (split.n₁ n)⁻¹ ∑_{i ∈ foldA n} h(X_i)²`, matching
`is_estimator.opt`.  All bounds are stated at the fold-A sample size
`split.n₁ n`; the bundles passed in are at that size, so
`criticalRadius (regime.bundle_*.regime.ψ (split.n₁ n))` is the per-fold
critical radius.

The hypothesis `1 ≤ split.n₁ n` excludes the degenerate case of an empty
fold (where `(0:ℝ)⁻¹ = 0` and the bound is vacuous but doesn't reflect
the inequality of interest).  By `split.grow` this hypothesis holds for
all sufficiently large `n`. -/

private lemma measure_iInter_nat_ge_one_sub_tsum_of_ge
    [IsProbabilityMeasure μ]
    {E : ℕ → Set Ω} {a : ℕ → ENNReal}
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hE : ∀ n, μ (E n) ≥ 1 - a n) :
    μ (⋂ n, E n) ≥ 1 - ∑' n, a n := by
  have hE_compl : ∀ n, μ (E n)ᶜ ≤ a n := by
    intro n
    have hone_le : (1 : ENNReal) ≤ a n + μ (E n) :=
      tsub_le_iff_left.mp (hE n)
    rw [measure_compl (hE_meas n) (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hbad_subset : (⋂ n, E n)ᶜ ⊆ ⋃ n, (E n)ᶜ := by
    simp
  have hbad_le : μ (⋂ n, E n)ᶜ ≤ ∑' n, a n := by
    calc
      μ (⋂ n, E n)ᶜ ≤ μ (⋃ n, (E n)ᶜ) := measure_mono hbad_subset
      _ ≤ ∑' n, μ (E n)ᶜ := measure_iUnion_le fun n => (E n)ᶜ
      _ ≤ ∑' n, a n := ENNReal.tsum_le_tsum hE_compl
  have hA_meas : MeasurableSet (⋂ n, E n) := MeasurableSet.iInter hE_meas
  rw [measure_compl hA_meas (measure_ne_top _ _), measure_univ] at hbad_le
  have hone_le : (1 : ENNReal) ≤ (∑' n, a n) + μ (⋂ n, E n) :=
    tsub_le_iff_right.mp hbad_le
  exact tsub_le_iff_left.mpr hone_le

private lemma measure_inter_ge_one_sub_add_of_ge
    [IsProbabilityMeasure μ]
    {A B : Set Ω} {a b : ENNReal}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (hA : μ A ≥ 1 - a) (hB : μ B ≥ 1 - b) :
    μ (A ∩ B) ≥ 1 - (a + b) := by
  have hA_compl : μ Aᶜ ≤ a := by
    have hone_le : (1 : ENNReal) ≤ a + μ A := tsub_le_iff_left.mp hA
    rw [measure_compl hA_meas (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hB_compl : μ Bᶜ ≤ b := by
    have hone_le : (1 : ENNReal) ≤ b + μ B := tsub_le_iff_left.mp hB
    rw [measure_compl hB_meas (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hbad_le : μ (A ∩ B)ᶜ ≤ a + b := by
    rw [Set.compl_inter]
    exact (measure_union_le Aᶜ Bᶜ).trans (add_le_add hA_compl hB_compl)
  have hAB_meas : MeasurableSet (A ∩ B) := hA_meas.inter hB_meas
  rw [measure_compl hAB_meas (measure_ne_top _ _), measure_univ] at hbad_le
  have hone_le : (1 : ENNReal) ≤ (a + b) + μ (A ∩ B) :=
    tsub_le_iff_right.mp hbad_le
  exact tsub_le_iff_left.mpr hone_le

/-- Closedness witnesses attain the population adversarial value.  Local
private copy used here to avoid importing `EPPerN.lean`, which depends on
this master event. -/
private lemma population_inner_eq_closedness_witness
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F)
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf)) :
    2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ
      = (S.weakNorm
          (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2 := by
  haveI := S.isFiniteMeasure
  haveI := S.Qbar_L2_hasProj
  have h_inner_int :
      inner ℝ (S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh)))
              (S.qL2 (TC.F_subset hf))
        = ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                f (S.zOf (S.W ω)) ∂μ :=
    S.T_inner_eq_integral S.h₀_mem (TC.H_subset hh) (TC.F_subset hf)
  have h_moment :
      ∫ ω, S.m (S.W ω) f ∂μ
        = ∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ :=
    S.primal_moment f (TC.F_subset hf)
  have hh₀f_int : Integrable
      (fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh S.h₀ S.h₀_mem f (TC.F_subset hf)
    simpa [mul_comm] using this
  have hhf_int : Integrable
      (fun ω => h (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh h (TC.H_subset hh) f (TC.F_subset hf)
    simpa [mul_comm] using this
  have h_int_diff :
      ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
              f (S.zOf (S.W ω)) ∂μ
        = (∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ := by
    have : (fun ω => (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                      f (S.zOf (S.W ω)))
              = fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))
                          - h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) := by
      funext ω; ring
    rw [this]
    exact integral_sub hh₀f_int hhf_int
  have h_diff_eq_inner :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = inner ℝ (S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh)))
                  (S.qL2 (TC.F_subset hf)) := by
    rw [h_moment, h_inner_int, h_int_diff]
  have h_qL2_self :
      inner ℝ (S.qL2 (TC.F_subset hf)) (S.qL2 (TC.F_subset hf))
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(S.toQbarL2 f (TC.F_subset hf)).coeFn_toLp]
      with ω hω
    simp [OperatorSystem.qL2, hω, pow_two]
  have h_diff_eq_int_fsq :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [h_diff_eq_inner, hcl, h_qL2_self]
  have h_T_neg :
      S.T (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)
        = - S.qL2 (TC.F_subset hf) := by
    rw [S.T_sub]
    have hcl' :
        S.T (S.hL2 S.h₀_mem) - S.T (S.hL2 (TC.H_subset hh))
          = S.qL2 (TC.F_subset hf) := by
      rw [← S.T_sub]; exact hcl
    rw [← hcl']
    abel
  have h_weak_eq_intf :
      (S.weakNorm (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [OperatorSystem.weakNorm, h_T_neg, norm_neg]
    have : ‖S.qL2 (TC.F_subset hf)‖ ^ 2
            = inner ℝ (S.qL2 (TC.F_subset hf))
                      (S.qL2 (TC.F_subset hf)) := by
      rw [real_inner_self_eq_norm_sq]
    rw [this, h_qL2_self]
  rw [h_weak_eq_intf]
  linarith [h_diff_eq_int_fsq]

/-- Population adversarial inner objectives are bounded by the weak residual
norm squared.  This is the deterministic inequality
`2⟨a,q⟩ - ‖q‖² ≤ ‖a‖²`, written in the NPIV integral notation. -/
private lemma population_inner_le_weak
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F) :
    2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ
      ≤ (S.weakNorm
          (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2 := by
  haveI := S.isFiniteMeasure
  haveI := S.Qbar_L2_hasProj
  let a := S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
  let q := S.qL2 (TC.F_subset hf)
  have h_inner_int :
      inner ℝ a q
        = ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                f (S.zOf (S.W ω)) ∂μ := by
    simpa [a, q] using
      S.T_inner_eq_integral S.h₀_mem (TC.H_subset hh) (TC.F_subset hf)
  have h_moment :
      ∫ ω, S.m (S.W ω) f ∂μ
        = ∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ :=
    S.primal_moment f (TC.F_subset hf)
  have hh₀f_int : Integrable
      (fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh S.h₀ S.h₀_mem f (TC.F_subset hf)
    simpa [mul_comm] using this
  have hhf_int : Integrable
      (fun ω => h (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh h (TC.H_subset hh) f (TC.F_subset hf)
    simpa [mul_comm] using this
  have h_int_diff :
      ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
              f (S.zOf (S.W ω)) ∂μ
        = (∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ := by
    have : (fun ω => (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                      f (S.zOf (S.W ω)))
              = fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))
                          - h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) := by
      funext ω; ring
    rw [this]
    exact integral_sub hh₀f_int hhf_int
  have h_diff_eq_inner :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = inner ℝ a q := by
    rw [h_moment, h_inner_int, h_int_diff]
  have h_qL2_self :
      inner ℝ q q = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(S.toQbarL2 f (TC.F_subset hf)).coeFn_toLp]
      with ω hω
    simp [q, OperatorSystem.qL2, hω, pow_two]
  have hweak :
      (S.weakNorm (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2
        = ‖a‖ ^ 2 := by
    rw [OperatorSystem.weakNorm, S.T_sub]
    have hneg :
        S.T (S.hL2 (TC.H_subset hh)) - S.T (S.hL2 S.h₀_mem) = -a := by
      dsimp [a]
      rw [S.T_sub]
      abel
    rw [hneg, norm_neg]
  have hhilbert : 2 * inner ℝ a q - inner ℝ q q ≤ ‖a‖ ^ 2 := by
    have hsq : 0 ≤ ‖a - q‖ ^ 2 := sq_nonneg ‖a - q‖
    rw [norm_sub_sq_real] at hsq
    have hqnorm : inner ℝ q q = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
    nlinarith
  rw [hweak]
  nlinarith [h_diff_eq_inner, h_qL2_self, hhilbert]

private lemma population_inner_eq_closedness_inner
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F)
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed)) :
    2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ
      =
        2 * inner ℝ (S.qL2 (TC.F_subset hf_closed))
            (S.qL2 (TC.F_subset hf))
          - inner ℝ (S.qL2 (TC.F_subset hf))
              (S.qL2 (TC.F_subset hf)) := by
  haveI := S.isFiniteMeasure
  haveI := S.Qbar_L2_hasProj
  let q_closed := S.qL2 (TC.F_subset hf_closed)
  let q := S.qL2 (TC.F_subset hf)
  have h_inner_int :
      inner ℝ q_closed q
        = ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                f (S.zOf (S.W ω)) ∂μ := by
    dsimp [q_closed, q]
    rw [← hcl]
    simpa using
      S.T_inner_eq_integral S.h₀_mem (TC.H_subset hh) (TC.F_subset hf)
  have h_moment :
      ∫ ω, S.m (S.W ω) f ∂μ
        = ∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ :=
    S.primal_moment f (TC.F_subset hf)
  have hh₀f_int : Integrable
      (fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh S.h₀ S.h₀_mem f (TC.F_subset hf)
    simpa [mul_comm] using this
  have hhf_int : Integrable
      (fun ω => h (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh h (TC.H_subset hh) f (TC.F_subset hf)
    simpa [mul_comm] using this
  have h_int_diff :
      ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
              f (S.zOf (S.W ω)) ∂μ
        = (∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ := by
    have : (fun ω => (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                      f (S.zOf (S.W ω)))
              = fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))
                          - h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) := by
      funext ω; ring
    rw [this]
    exact integral_sub hh₀f_int hhf_int
  have h_diff_eq_inner :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = inner ℝ q_closed q := by
    rw [h_moment, h_inner_int, h_int_diff]
  have h_qL2_self :
      inner ℝ q q = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(S.toQbarL2 f (TC.F_subset hf)).coeFn_toLp]
      with ω hω
    simp [q, OperatorSystem.qL2, hω, pow_two]
  nlinarith [h_diff_eq_inner, h_qL2_self]

/-- Population curvature at the closedness critic.  For a fixed candidate
`h`, the closedness witness `f_closed` is the population maximizer of the
quadratic adversarial criterion, and the drop at any critic `f` is exactly
the squared `L²` critic gap.

This is the Lean form of the second-order identity used in the proof of
Lemma 11 in Bennett--Kallus--Mao--Newey--Syrgkanis--Uehara. -/
lemma population_closedness_critic_gap_eq
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F)
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed)) :
    (2 * (∫ ω, S.m (S.W ω) f_closed ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) *
            f_closed (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f_closed (S.zOf (S.W ω))) ^ 2 ∂μ)
      - (2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) *
            f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ)
      =
        ‖S.qL2 (TC.F_subset hf_closed) - S.qL2 (TC.F_subset hf)‖ ^ 2 := by
  let qc := S.qL2 (TC.F_subset hf_closed)
  let q := S.qL2 (TC.F_subset hf)
  have hclosed :=
    population_inner_eq_closedness_inner
      (S := S) (TC := TC) (hh := hh)
      (hf_closed := hf_closed) (hf := hf_closed) hcl
  have hf_eq :=
    population_inner_eq_closedness_inner
      (S := S) (TC := TC) (hh := hh)
      (hf_closed := hf_closed) (hf := hf) hcl
  have hqc_self : inner ℝ qc qc = ‖qc‖ ^ 2 := real_inner_self_eq_norm_sq qc
  have hq_self : inner ℝ q q = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
  have hnorm : ‖qc - q‖ ^ 2 = ‖qc‖ ^ 2 + ‖q‖ ^ 2 - 2 * inner ℝ qc q := by
    rw [norm_sub_sq_real]
    ring
  rw [hclosed, hf_eq, hnorm]
  dsimp [qc, q] at hqc_self hq_self
  nlinarith [hqc_self, hq_self]

/-- Deterministic argmax-localization bridge.  If `f_emp` empirically
beats the closedness witness for the same candidate `h`, and the
population-vs-empirical loss difference is controlled by `R`, then the
empirical critic is within squared `L²` distance `R` of the closedness
witness.

This is the formal bridge missing from a direct use of
`supObjective_attained`: the arbitrary empirical maximizer becomes
localized by population curvature plus empirical optimality. -/
lemma empirical_critic_argmax_localized
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    [IsProbabilityMeasure μ]
    {lambda : ℝ} {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f_emp : S.𝒵 → ℝ} (hf_emp : f_emp ∈ TC.F)
    {n : ℕ} {ω : Ω} {R : ℝ}
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed))
    (hopt :
      innerObjective S sample split lambda h f_closed n ω
        ≤ innerObjective S sample split lambda h f_emp n ω)
    (hdev :
      (2 * (∫ ω', S.m (S.W ω') f_closed ∂μ)
          - 2 * (∫ ω', h (S.xOf (S.W ω')) *
              f_closed (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_closed (S.zOf (S.W ω'))) ^ 2 ∂μ)
        - (2 * (∫ ω', S.m (S.W ω') f_emp ∂μ)
          - 2 * (∫ ω', h (S.xOf (S.W ω')) *
              f_emp (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_emp (S.zOf (S.W ω'))) ^ 2 ∂μ)
        ≤ innerObjective S sample split lambda h f_closed n ω
            - innerObjective S sample split lambda h f_emp n ω
          + R) :
      ‖S.qL2 (TC.F_subset hf_closed) - S.qL2 (TC.F_subset hf_emp)‖ ^ 2
        ≤ R := by
  have hgap :=
    population_closedness_critic_gap_eq
      (S := S) (TC := TC) (hh := hh)
      (hf_closed := hf_closed) (hf := hf_emp) hcl
  rw [← hgap]
  linarith [hdev, hopt]

/-! ### Objective-level master event (raw localized gap)

`ep_master_event_from_localized` is the Ω-side concentration ingredient
consumed by `ep_inequality_from_localized` in `EPPerN.lean`.  Its
conclusion is the raw localized objective modulus:

    population_excess(ĥ_n, h*_λ) ≤
      empirical_sup_excess(ĥ_n, h*_λ) + localized_envelope.

This is deliberately not the final EP inequality: without the estimator
optimality hypothesis, the empirical sup-objective excess remains on
the RHS.  `EPPerN.lean` uses `is_estimator.opt` to remove exactly that
term.  This keeps the master event non-vacuous; the later discharge
step absorbs this explicit rate into the final TRAE population shape.

The proof intersects the three localized Ω-events for the `HF`, `mF`, and
`F` empirical-process pieces, then performs the deterministic bridge from
inner objectives to `supObjective` using the max-order fields carried by
`LocalizedRegimes`, followed by the all-`n` geometric union bound on Ω. -/

private lemma innerObjective_eq_fin_sum
    {S : OperatorSystem Ω μ}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ)
    (n : ℕ) (ω : Ω) :
    innerObjective S sample split lambda h f n ω
      = ((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            innerIntegrand S lambda h f (sample.Z (k : ℕ) ω) := by
  rw [innerObjective, OneShotSplit.foldA, Finset.card_range]
  rw [← Fin.sum_univ_eq_sum_range]

private lemma population_regularized_le_innerObjective_add_deviation
    {S : OperatorSystem Ω μ}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ)
    (n : ℕ) (ω : Ω)
    {Rm RHF RF : ℝ}
    (hmF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
        - ∫ ω', S.m (S.W ω') f ∂μ| ≤ Rm)
    (hHF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ| ≤ RHF)
    (hF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF) :
    2 * (∫ ω', S.m (S.W ω') f ∂μ)
        - 2 * (∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ)
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
        + lambda *
            (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
              (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
      ≤ innerObjective S sample split lambda h f n ω
        + (2 * Rm + 2 * RHF + RF) := by
  let mEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
  let mPop : ℝ := ∫ ω', S.m (S.W ω') f ∂μ
  let hfEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n),
        h (S.xOf (sample.Z (k : ℕ) ω)) *
          f (S.zOf (sample.Z (k : ℕ) ω))
  let hfPop : ℝ :=
    ∫ ω', h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ
  let fEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
  let fPop : ℝ := ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
  let hReg : ℝ :=
    lambda *
      (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
        (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
  have hm_abs : -Rm ≤ mEmp - mPop ∧ mEmp - mPop ≤ Rm := by
    simpa [mEmp, mPop] using abs_le.mp hmF
  have hHF_abs : -RHF ≤ hfEmp - hfPop ∧ hfEmp - hfPop ≤ RHF := by
    simpa [hfEmp, hfPop] using abs_le.mp hHF
  have hF_abs : -RF ≤ fEmp - fPop ∧ fEmp - fPop ≤ RF := by
    simpa [fEmp, fPop] using abs_le.mp hF
  have hinner :
      innerObjective S sample split lambda h f n ω
        = 2 * mEmp - 2 * hfEmp - fEmp + hReg := by
    rw [innerObjective_eq_fin_sum]
    have hsum :
        (∑ k : Fin (split.n₁ n),
            innerIntegrand S lambda h f (sample.Z (k : ℕ) ω))
          =
            2 * (∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f)
            - 2 * (∑ k : Fin (split.n₁ n),
                h (S.xOf (sample.Z (k : ℕ) ω)) *
                  f (S.zOf (sample.Z (k : ℕ) ω)))
            - (∑ k : Fin (split.n₁ n),
                (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2)
            + lambda * (∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2) := by
      simp only [innerIntegrand, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      abel_nf
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      rw [← Finset.smul_sum]
      abel_nf
      ring_nf
    rw [hsum]
    simp only [mEmp, hfEmp, fEmp, hReg]
    ring_nf
  rw [hinner]
  dsimp [mPop, hfPop, fPop, hReg]
  nlinarith [hm_abs.1, hm_abs.2, hHF_abs.1, hHF_abs.2,
    hF_abs.1, hF_abs.2]

private lemma innerObjective_le_population_regularized_add_deviation
    {S : OperatorSystem Ω μ}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ)
    (n : ℕ) (ω : Ω)
    {Rm RHF RF : ℝ}
    (hmF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
        - ∫ ω', S.m (S.W ω') f ∂μ| ≤ Rm)
    (hHF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ| ≤ RHF)
    (hF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF) :
    innerObjective S sample split lambda h f n ω
      ≤ 2 * (∫ ω', S.m (S.W ω') f ∂μ)
        - 2 * (∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ)
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
        + lambda *
            (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
              (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
        + (2 * Rm + 2 * RHF + RF) := by
  let mEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
  let mPop : ℝ := ∫ ω', S.m (S.W ω') f ∂μ
  let hfEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n),
        h (S.xOf (sample.Z (k : ℕ) ω)) *
          f (S.zOf (sample.Z (k : ℕ) ω))
  let hfPop : ℝ :=
    ∫ ω', h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ
  let fEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
  let fPop : ℝ := ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
  let hReg : ℝ :=
    lambda *
      (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
        (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
  have hm_abs : -Rm ≤ mEmp - mPop ∧ mEmp - mPop ≤ Rm := by
    simpa [mEmp, mPop] using abs_le.mp hmF
  have hHF_abs : -RHF ≤ hfEmp - hfPop ∧ hfEmp - hfPop ≤ RHF := by
    simpa [hfEmp, hfPop] using abs_le.mp hHF
  have hF_abs : -RF ≤ fEmp - fPop ∧ fEmp - fPop ≤ RF := by
    simpa [fEmp, fPop] using abs_le.mp hF
  have hinner :
      innerObjective S sample split lambda h f n ω
        = 2 * mEmp - 2 * hfEmp - fEmp + hReg := by
    rw [innerObjective_eq_fin_sum]
    have hsum :
        (∑ k : Fin (split.n₁ n),
            innerIntegrand S lambda h f (sample.Z (k : ℕ) ω))
          =
            2 * (∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f)
            - 2 * (∑ k : Fin (split.n₁ n),
                h (S.xOf (sample.Z (k : ℕ) ω)) *
                  f (S.zOf (sample.Z (k : ℕ) ω)))
            - (∑ k : Fin (split.n₁ n),
                (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2)
            + lambda * (∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2) := by
      simp only [innerIntegrand, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      abel_nf
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      rw [← Finset.smul_sum]
      abel_nf
      ring_nf
    rw [hsum]
    simp only [mEmp, hfEmp, fEmp, hReg]
    ring_nf
  rw [hinner]
  dsimp [mPop, hfPop, fPop, hReg]
  nlinarith [hm_abs.1, hm_abs.2, hHF_abs.1, hHF_abs.2,
    hF_abs.1, hF_abs.2]

/-- Componentwise version of `empirical_critic_argmax_localized`.

The hypotheses are exactly the per-critic localized deviations already
available from the single-index `m∘F`, `H·F`, and `F²` events.  No
closedness or linearity of the critic class beyond the paper's closedness
witness is added here. -/
lemma empirical_critic_argmax_localized_from_components
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    [IsProbabilityMeasure μ]
    {lambda : ℝ} {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f_emp : S.𝒵 → ℝ} (hf_emp : f_emp ∈ TC.F)
    {n : ℕ} {ω : Ω}
    {Rm_closed RHF_closed RF_closed Rm_emp RHF_emp RF_emp : ℝ}
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed))
    (hopt :
      innerObjective S sample split lambda h f_closed n ω
        ≤ innerObjective S sample split lambda h f_emp n ω)
    (hmF_closed :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f_closed
        - ∫ ω', S.m (S.W ω') f_closed ∂μ| ≤ Rm_closed)
    (hHF_closed :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f_closed (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f_closed (S.zOf (S.W ω')) ∂μ|
          ≤ RHF_closed)
    (hF_closed :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f_closed (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f_closed (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF_closed)
    (hmF_emp :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f_emp
        - ∫ ω', S.m (S.W ω') f_emp ∂μ| ≤ Rm_emp)
    (hHF_emp :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f_emp (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f_emp (S.zOf (S.W ω')) ∂μ|
          ≤ RHF_emp)
    (hF_emp :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f_emp (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f_emp (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF_emp) :
      ‖S.qL2 (TC.F_subset hf_closed) - S.qL2 (TC.F_subset hf_emp)‖ ^ 2
        ≤ (2 * Rm_closed + 2 * RHF_closed + RF_closed)
          + (2 * Rm_emp + 2 * RHF_emp + RF_emp) := by
  let D_closed : ℝ := 2 * Rm_closed + 2 * RHF_closed + RF_closed
  let D_emp : ℝ := 2 * Rm_emp + 2 * RHF_emp + RF_emp
  have hclosed_upper :
      2 * (∫ ω', S.m (S.W ω') f_closed ∂μ)
          - 2 * (∫ ω',
              h (S.xOf (S.W ω')) * f_closed (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_closed (S.zOf (S.W ω'))) ^ 2 ∂μ
          + lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
        ≤ innerObjective S sample split lambda h f_closed n ω + D_closed := by
    simpa [D_closed] using
      population_regularized_le_innerObjective_add_deviation
        split lambda h f_closed n ω hmF_closed hHF_closed hF_closed
  have hemp_upper :
      innerObjective S sample split lambda h f_emp n ω
        ≤ 2 * (∫ ω', S.m (S.W ω') f_emp ∂μ)
          - 2 * (∫ ω',
              h (S.xOf (S.W ω')) * f_emp (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_emp (S.zOf (S.W ω'))) ^ 2 ∂μ
          + lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
          + D_emp := by
    simpa [D_emp] using
      innerObjective_le_population_regularized_add_deviation
        split lambda h f_emp n ω hmF_emp hHF_emp hF_emp
  apply empirical_critic_argmax_localized
      (S := S) (TC := TC) (sample := sample) (split := split)
      (lambda := lambda) (hh := hh) (hf_closed := hf_closed)
      (hf_emp := hf_emp) (n := n) (ω := ω)
      (R := D_closed + D_emp) hcl hopt
  linarith [hclosed_upper, hemp_upper]

/-- **Master localized empirical-process event for the primal NPIV analysis.**

Produces a single Ω-event `Aζ_master` of mass `≥ 1 − ζ` on which, for
every `n` with `1 ≤ split.n₁ n`, the population weak-objective excess
plus the empirical regularizer excess is bounded by the empirical
sup-objective excess plus the localized envelope. The envelope combines the
localized regimes for the weak-norm class, the regularizer class, and their
interaction, so downstream lemmas can consume one event rather than three
separate concentration statements. -/
theorem ep_master_event_from_localized
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    (is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat)
    (sc : SourceCondition S β)
    (tb : TikhonovBiasBound S β lambda sc)
    [IsProbabilityMeasure μ]
    (regimes : ∀ n, LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    {ζ : ℝ} (hζ_pos : 0 < ζ) (hζ_lt : ζ < 1) :
    ∃ Aζ_master : Set Ω,
      MeasurableSet Aζ_master ∧ μ Aζ_master ≥ 1 - ENNReal.ofReal ζ ∧
      ∀ ω ∈ Aζ_master, ∀ n : ℕ, 1 ≤ split.n₁ n →
        ((S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
              - S.hL2 S.h₀_mem)) ^ 2
          + lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h_hat n ω (S.xOf (sample.Z (k : ℕ) ω))) ^ 2))
          - ((S.weakNorm
              (S.hL2 tb.h_lambda_star_mem
                - S.hL2 S.h₀_mem)) ^ 2
            + lambda *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2))
        ≤ supObjective S TC sample split lambda (h_hat n ω) n ω
            - supObjective S TC sample split lambda tb.h_lambda_star_fun n ω
      + (16 * delta n *
                criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
              + 16 * delta n *
                criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
              + 8 * delta n *
                criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
              + (4 * (regimes n).bundle_HF.regime.b
                  + 4 * (regimes n).bundle_mF.regime.b
                  + 2 * (regimes n).bundle_F.regime.b) *
                  Real.sqrt
                    (2 * Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)
                      / (split.n₁ n))) := by
  classical
  let ε : ℕ → ℝ := fun n => ζ * ((1 / 2 : ℝ) ^ (n + 1))
  let η : ℕ → ℝ := fun n => ε n / 4
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    exact mul_pos hζ_pos (pow_pos (by norm_num) _)
  have hε_le_one : ∀ n, ε n ≤ 1 := by
    intro n
    have hζ_le : ζ ≤ 1 := le_of_lt hζ_lt
    have hpow_le_one : ((1 / 2 : ℝ) ^ (n + 1)) ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hpow_nonneg : 0 ≤ ((1 / 2 : ℝ) ^ (n + 1)) := by positivity
    nlinarith
  have hη_pos : ∀ n, 0 < η n := by
    intro n
    dsimp [η]
    positivity
  have hη_le_one : ∀ n, η n ≤ 1 := by
    intro n
    dsimp [η]
    nlinarith [hε_le_one n]
  let EHF : ℕ → Set Ω := fun n =>
    if hn : 0 < split.n₁ n then
      (localized_omega_event_for_HF (regimes n) hn (hη_pos n) (hη_le_one n)).choose
    else Set.univ
  let EmF : ℕ → Set Ω := fun n =>
    if hn : 0 < split.n₁ n then
      (localized_omega_event_for_mF (regimes n) hn (hη_pos n) (hη_le_one n)).choose
    else Set.univ
  let EF : ℕ → Set Ω := fun n =>
    if hn : 0 < split.n₁ n then
      (localized_omega_event_for_F (regimes n) hn (hη_pos n) (hη_le_one n)).choose
    else Set.univ
  let En : ℕ → Set Ω := fun n => EHF n ∩ EmF n ∩ EF n
  have hEHF_meas : ∀ n, MeasurableSet (EHF n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EHF, hn] using
        (localized_omega_event_for_HF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.1
    · simp [EHF, hn]
  have hEmF_meas : ∀ n, MeasurableSet (EmF n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EmF, hn] using
        (localized_omega_event_for_mF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.1
    · simp [EmF, hn]
  have hEF_meas : ∀ n, MeasurableSet (EF n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EF, hn] using
        (localized_omega_event_for_F (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.1
    · simp [EF, hn]
  have hEHF_mass : ∀ n, μ (EHF n) ≥ 1 - ENNReal.ofReal (η n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EHF, hn] using
        (localized_omega_event_for_HF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.2.1
    · simp [EHF, hn]
  have hEmF_mass : ∀ n, μ (EmF n) ≥ 1 - ENNReal.ofReal (η n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EmF, hn] using
        (localized_omega_event_for_mF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.2.1
    · simp [EmF, hn]
  have hEF_mass : ∀ n, μ (EF n) ≥ 1 - ENNReal.ofReal (η n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EF, hn] using
        (localized_omega_event_for_F (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.2.1
    · simp [EF, hn]
  have hEn_meas : ∀ n, MeasurableSet (En n) := by
    intro n
    exact ((hEHF_meas n).inter (hEmF_meas n)).inter (hEF_meas n)
  have hEn_mass : ∀ n, μ (En n) ≥ 1 - ENNReal.ofReal (ε n) := by
    intro n
    have h12 :
        μ (EHF n ∩ EmF n)
          ≥ 1 - (ENNReal.ofReal (η n) + ENNReal.ofReal (η n)) :=
      measure_inter_ge_one_sub_add_of_ge (hEHF_meas n) (hEmF_meas n)
        (hEHF_mass n) (hEmF_mass n)
    have h123 :
        μ ((EHF n ∩ EmF n) ∩ EF n)
          ≥ 1 -
            ((ENNReal.ofReal (η n) + ENNReal.ofReal (η n))
              + ENNReal.ofReal (η n)) :=
      measure_inter_ge_one_sub_add_of_ge
        ((hEHF_meas n).inter (hEmF_meas n)) (hEF_meas n)
        h12 (hEF_mass n)
    have hη_nonneg : 0 ≤ η n := le_of_lt (hη_pos n)
    have htriple_eq :
        (ENNReal.ofReal (η n) + ENNReal.ofReal (η n))
            + ENNReal.ofReal (η n)
          = ENNReal.ofReal (η n + η n + η n) := by
      rw [← ENNReal.ofReal_add hη_nonneg hη_nonneg]
      rw [← ENNReal.ofReal_add (add_nonneg hη_nonneg hη_nonneg) hη_nonneg]
    have htriple_le :
        (ENNReal.ofReal (η n) + ENNReal.ofReal (η n))
            + ENNReal.ofReal (η n)
          ≤ ENNReal.ofReal (ε n) := by
      rw [htriple_eq]
      apply ENNReal.ofReal_le_ofReal
      dsimp [η]
      nlinarith [hε_pos n]
    simpa [En, Set.inter_assoc] using
      (tsub_le_tsub_left htriple_le 1).trans h123
  have htsum_ε : (∑' n, ENNReal.ofReal (ε n)) ≤ ENNReal.ofReal ζ := by
    have hterm :
        (fun n => ENNReal.ofReal (ε n))
          =
        fun n => ENNReal.ofReal ζ * (2⁻¹ : ENNReal) ^ (n + 1) := by
      funext n
      rw [show ε n = ζ * (1 / 2 : ℝ) ^ (n + 1) by rfl]
      rw [ENNReal.ofReal_mul (le_of_lt hζ_pos)]
      simp [one_div, ENNReal.inv_pow]
    rw [hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    have hgeom : (2⁻¹ : ENNReal) * (1 - 2⁻¹)⁻¹ = 1 := by
      rw [ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' (2 : ENNReal)))
        (by norm_num : (2 : ENNReal) ≠ ⊤)
    rw [hgeom, mul_one]
  let Aζ_master : Set Ω := ⋂ n, En n
  refine ⟨Aζ_master, MeasurableSet.iInter hEn_meas, ?_, ?_⟩
  · exact (tsub_le_tsub_left htsum_ε 1).trans
      (measure_iInter_nat_ge_one_sub_tsum_of_ge hEn_meas hEn_mass)
  · intro ω hω n _hn
    have hn_pos : 0 < split.n₁ n := lt_of_lt_of_le zero_lt_one _hn
    have hωn : ω ∈ En n := Set.mem_iInter.mp hω n
    have hωHF : ω ∈ EHF n := hωn.1.1
    have hωmF : ω ∈ EmF n := hωn.1.2
    have hωF : ω ∈ EF n := hωn.2
    have hωHF_event :
        ω ∈ (localized_omega_event_for_HF (regimes n) hn_pos
          (hη_pos n) (hη_le_one n)).choose := by
      simpa [EHF, hn_pos] using hωHF
    have hωmF_event :
        ω ∈ (localized_omega_event_for_mF (regimes n) hn_pos
          (hη_pos n) (hη_le_one n)).choose := by
      simpa [EmF, hn_pos] using hωmF
    have hωF_event :
        ω ∈ (localized_omega_event_for_F (regimes n) hn_pos
          (hη_pos n) (hη_le_one n)).choose := by
      simpa [EF, hn_pos] using hωF
    obtain ⟨f_h, hf_h, hcl_h⟩ :=
      (regimes n).closedness (h_hat n ω) (is_estimator.mem_H n ω)
    obtain ⟨f_star, hf_star, hstar_sup_le_inner⟩ :=
      (regimes n).supObjective_attained split n ω
        tb.h_lambda_star_fun (regimes n).realizability
    have hinner_le_sup :
        innerObjective S sample split lambda (h_hat n ω) f_h n ω
          ≤ supObjective S TC sample split lambda (h_hat n ω) n ω :=
      (regimes n).inner_le_supObjective split n ω
        (h_hat n ω) (is_estimator.mem_H n ω) f_h hf_h
    have hlog : 1 / η n = 4 * (2 : ℝ) ^ (n + 1) / ζ := by
      dsimp [η, ε]
      simp only [one_div]
      rw [inv_pow]
      field_simp [ne_of_gt hζ_pos,
        pow_ne_zero (n + 1) (show (2 : ℝ) ≠ 0 by norm_num)]
    have hHF_h :=
      (localized_omega_event_for_HF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωHF_event (h_hat n ω) (is_estimator.mem_H n ω) f_h hf_h
    have hmF_h :=
      (localized_omega_event_for_mF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωmF_event f_h hf_h
    have hF_h :=
      (localized_omega_event_for_F (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωF_event f_h hf_h
    have hHF_star :=
      (localized_omega_event_for_HF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωHF_event tb.h_lambda_star_fun (regimes n).realizability
        f_star hf_star
    have hmF_star :=
      (localized_omega_event_for_mF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωmF_event f_star hf_star
    have hF_star :=
      (localized_omega_event_for_F (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωF_event f_star hf_star
    rw [hlog] at hHF_h hmF_h hF_h hHF_star hmF_star hF_star
    let rHF : ℝ :=
      4 * delta n * criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
        + (regimes n).bundle_HF.regime.b *
          Real.sqrt (2 * Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)
            / (split.n₁ n))
    let rmF : ℝ :=
      4 * delta n * criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
        + (regimes n).bundle_mF.regime.b *
          Real.sqrt (2 * Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)
            / (split.n₁ n))
    let rF : ℝ :=
      4 * delta n * criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
        + (regimes n).bundle_F.regime.b *
          Real.sqrt (2 * Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)
            / (split.n₁ n))
    have hupper_h :
        2 * (∫ ω', S.m (S.W ω') f_h ∂μ)
            - 2 * (∫ ω',
                (h_hat n ω) (S.xOf (S.W ω')) *
                  f_h (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_h (S.zOf (S.W ω'))) ^ 2 ∂μ
            + lambda *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ *
                  ∑ k : Fin (split.n₁ n),
                    ((h_hat n ω) (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
          ≤ innerObjective S sample split lambda (h_hat n ω) f_h n ω
            + (2 * rmF + 2 * rHF + rF) := by
      exact population_regularized_le_innerObjective_add_deviation
        split lambda (h_hat n ω) f_h n ω hmF_h hHF_h hF_h
    have hupper_star :
        innerObjective S sample split lambda tb.h_lambda_star_fun f_star n ω
          ≤ 2 * (∫ ω', S.m (S.W ω') f_star ∂μ)
            - 2 * (∫ ω',
                tb.h_lambda_star_fun (S.xOf (S.W ω')) *
                  f_star (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_star (S.zOf (S.W ω'))) ^ 2 ∂μ
            + lambda *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ *
                  ∑ k : Fin (split.n₁ n),
                    (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
            + (2 * rmF + 2 * rHF + rF) := by
      exact innerObjective_le_population_regularized_add_deviation
        split lambda tb.h_lambda_star_fun f_star n ω
        hmF_star hHF_star hF_star
    have hpop_h_eq :
        2 * (∫ ω', S.m (S.W ω') f_h ∂μ)
            - 2 * (∫ ω',
                (h_hat n ω) (S.xOf (S.W ω')) *
                  f_h (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_h (S.zOf (S.W ω'))) ^ 2 ∂μ
          =
            (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 S.h₀_mem)) ^ 2 :=
      population_inner_eq_closedness_witness
        (hh := is_estimator.mem_H n ω) (hf := hf_h) hcl_h
    have hpop_star_le :
        2 * (∫ ω', S.m (S.W ω') f_star ∂μ)
            - 2 * (∫ ω',
                tb.h_lambda_star_fun (S.xOf (S.W ω')) *
                  f_star (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_star (S.zOf (S.W ω'))) ^ 2 ∂μ
          ≤
            (S.weakNorm
              (S.hL2 tb.h_lambda_star_mem
                - S.hL2 S.h₀_mem)) ^ 2 :=
      population_inner_le_weak
        (hh := (regimes n).realizability) (hf := hf_star)
    linarith [hupper_h, hupper_star, hpop_h_eq, hpop_star_le,
      hinner_le_sup, hstar_sup_le_inner]

end Primal
end NPIV
end Estimation
end Causalean
