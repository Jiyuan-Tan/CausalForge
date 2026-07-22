/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized uniform deviation

Assembles the **localized uniform deviation** bound: a high-probability,
radius-localized empirical-process inequality controlled by a critical radius.
The argument chains:

1. **Symmetrization** (`expectation_le_rademacher` from FoML).
2. **Critical radius** (`subRoot_homogeneity`,
   `localRademacher_le_critical_radius`).
3. **McDiarmid-on-sup** (`mcdiarmid_inequality_pos'`,
   `uniformDeviation_bounded_difference`, or the packaged
   `uniform_deviation_tail_bound_separable_of_pos`).

The regime carries the sub-root envelope `ψ` directly on the centred loss
class instead of on a parameter class composed with a Lipschitz `φ`. Callers
that want to derive a loss-class envelope from a parameter-class envelope plus
a Lipschitz link should use the contraction infrastructure as a separate input
to this localized-deviation theorem.

The McDiarmid step (3) is **quarantined inside the proof body**: the
headline theorem `localized_uniform_deviation` is named without
"mcdiarmid" because the public statement is the localized-deviation bound, not
the particular concentration inequality used to prove it.

References:
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Theorem 3.3.
* Wainwright, *High-Dimensional Statistics*, Cambridge 2019, Chapter 14.
-/

import Causalean.Stat.Concentration.Rademacher.LocalRademacher
import Causalean.Stat.Concentration.Rademacher.Symmetrization
import Causalean.Stat.Concentration.TailBounds.McDiarmid
import Causalean.Stat.Concentration.UniformDeviation.BoundedDifference
import FoML.Main

/-! # Localized Uniform Deviation

This file assembles localized high-probability empirical-process deviation
bounds for bounded loss classes.  The structure `LocalizedRegime` packages the
uniform boundedness and sub-root Rademacher envelope assumptions,
`localized_uniform_deviation` proves the fixed-radius critical-radius bound, and
`localized_uniform_deviation_sharp` performs the peeling step that yields the
uniform sharp form `O(ρ * norm(F i) + ρ^2)` over a bounded class. -/

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory ProbabilityTheory

section LocalizedRegime

/-- The localized regime packages the assumptions needed for a critical-radius
uniform-deviation bound: a bounded function class and a sub-root upper envelope
on the localized Rademacher complexity.

    * `|F i (X ω)| ≤ b` is the boundedness needed by McDiarmid on the
      centred loss class itself.
    * `ψ` is a sub-root upper envelope on the population Rademacher
      complexity of `starHullZeroOut F norm r` (uniformly in `n`).

    The envelope `ψ` lives directly on the loss class. Callers wanting to
    derive a loss-class envelope from a parameter-class envelope plus a
    Lipschitz link can combine this regime with the contraction results in
    `Stat/Concentration/Contraction.lean`. -/
structure LocalizedRegime (Ω ι 𝒳 : Type*) [MeasurableSpace Ω]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳) where
  /-- Uniform bound on the loss class. -/
  b : ℝ
  /-- The bound is non-negative. -/
  b_nonneg : 0 ≤ b
  /-- The boundedness hypothesis: `|F i (X ω)| ≤ b` for all `i, ω`. -/
  bound : ∀ i ω, |F i (X ω)| ≤ b
  /-- Sub-root upper envelope on the localized Rademacher complexity,
      indexed by sample size `n` so that `ψ n` is the envelope at size `n`. -/
  ψ : ℕ → ℝ → ℝ
  /-- `ψ n` is sub-root for every `n`. -/
  ψ_subRoot : ∀ n, SubRoot (ψ n)
  /-- For each `n`, `ψ n` upper-bounds the Rademacher complexity of
      the radius-`r` star-hull ball. -/
  ψ_ub : ∀ n, RademacherUpperBound F norm μ X n (ψ n)

end LocalizedRegime

section LocalizedUniformDeviation

variable {Ω ι 𝒳 : Type*} [MeasurableSpace Ω]

/-- With high probability over the sample, every function whose `norm` is at
most `r` has empirical mean within a critical-radius bound of its population
mean.

    Under the `LocalizedRegime` bundle, with probability at least `1 - δ`
    over the sample, the empirical-vs-population deviation of `F i`
    is uniformly bounded for every `i` of `norm`-radius at most `r`,
    by the localized rate

        4 · r · δ_n  +  b · √(2 log(1/δ) / n),

    where `δ_n = criticalRadius R.ψ` is the population critical radius.

    The constants are illustrative (the `4` is loose by a factor of 2);
    the *shape* `r · δ_n + δ_n²` (recovered when `r ≍ δ_n`) is what
    matters for downstream callers.

    The public statement is named for the localized-deviation conclusion; the
    proof uses the available bounded-difference concentration ingredient
    internally. -/
theorem localized_uniform_deviation
    [MeasurableSpace 𝒳] [Nonempty 𝒳] -- FoML measurability prerequisites for `F` and `X`.
    [Nonempty ι] [Countable ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hX : Measurable X) -- FoML tail-bound prerequisite for the composed class.
    (hF_meas : ∀ i, Measurable (F i)) -- Measurability of the localized class.
    (R : LocalizedRegime Ω ι 𝒳 F norm μ X) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr_lb : criticalRadius (R.ψ n) ≤ r)
    (hcrit_pos : 0 < criticalRadius (R.ψ n)) -- Needed by `subRoot_homogeneity`.
    (hcrit_fp : R.ψ n (criticalRadius (R.ψ n)) ≤ (criticalRadius (R.ψ n)) ^ 2)
    -- Boundedness needed for the bridge lemma's `BddAbove` hypothesis.
    (hrad_bdd : ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
      BddAbove (Set.range fun p : starHullParam ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r p (S k)|))
    -- Integrability of the upper empirical Rademacher process; consumed by
    -- the bridge lemma `rademacherComplexity_zeroOut_le_starHullZeroOut`.
    (hrad_int : Integrable
      (fun ω : Fin n → Ω =>
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω))
      (Measure.pi (fun _ => μ))) :
    ∃ E : Set (Fin n → Ω), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι, norm (F i) ≤ r →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]|
          ≤ 4 * r * criticalRadius (R.ψ n)
            + R.b * Real.sqrt (2 * Real.log (1 / δ) / n) := by
  -- Proof outline:
  -- 1. (Symmetrization) `expectation_le_rademacher` ⇒
  --    𝔼[uniformDeviation n F μ X (X ∘ ·)] ≤ 2 · rademacherComplexity n F μ X.
  -- 2. (Localization) For `i` with `norm (F i) ≤ r`,
  --    `(1, i) ∈ starHullParam ι` and `starHullZeroOut F norm r (1, i) = F i`.
  --    Hence the rademacher sup over `{i : norm (F i) ≤ r}` is dominated
  --    by `rademacherComplexity n (starHullZeroOut F norm r) μ X`.
  -- 3. (Critical radius) `R.ψ_ub n r` gives the star-hull
  --    Rademacher bound by `R.ψ r`.
  --    Past the critical radius, `subRoot_homogeneity (R.ψ_subRoot)` ⇒
  --    `R.ψ r ≤ r · criticalRadius R.ψ`.
  -- 4. (McDiarmid) `uniformDeviation_bounded_difference` + `mcdiarmid_inequality_pos'`
  --    or `uniform_deviation_tail_bound_separable_of_pos` give a
  --    `b · √(2 log(1/δ)/n)` deviation around the mean with prob ≥ 1−δ.
  -- 5. Combine: deviation ≤ 𝔼-bound + McDiarmid slack
  --    ≤ 2·r·δ_n + b·√(...) ≤ 4·r·δ_n + b·√(...).
  classical
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let fΩ : ι → Ω → ℝ := fun i ω => if norm (F i) ≤ r then F i (X ω) else 0
  have hf_meas : ∀ i, Measurable (fΩ i) := by
    intro i
    by_cases hi : norm (F i) ≤ r
    · simpa [fΩ, hi] using (hF_meas i).comp hX
    · simp [fΩ, hi]
  have hf_bdd : ∀ i ω, |fΩ i ω| ≤ R.b := by
    intro i ω
    by_cases hi : norm (F i) ≤ r
    · simpa [fΩ, hi] using R.bound i ω
    · simpa [fΩ, hi] using R.b_nonneg
  have hcrit_nonneg : 0 ≤ criticalRadius (R.ψ n) := criticalRadius_nonneg (R.ψ n)
  have hr_nonneg : 0 ≤ r := le_trans hcrit_nonneg hr_lb
  by_cases hb0 : R.b = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ i hi
      have hzero : (fun ω' => F i (X ω')) = fun _ => (0 : ℝ) := by
        funext ω'
        have habs : |F i (X ω')| = 0 := by
          apply le_antisymm
          · simpa [hb0] using R.bound i ω'
          · exact abs_nonneg _
        exact abs_eq_zero.mp habs
      have hsample_zero : (Finset.univ.sum fun k : Fin n => F i (X (ω k))) = 0 := by
        simp [congrFun hzero]
      have hmean_zero : μ[fun ω' => F i (X ω')] = 0 := by
        simp [hzero]
      have hrc_nonneg : 0 ≤ r * criticalRadius (R.ψ n) :=
        mul_nonneg hr_nonneg hcrit_nonneg
      calc
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]| = 0 := by
              simp [hsample_zero, hmean_zero]
        _ ≤ 4 * r * criticalRadius (R.ψ n)
            + R.b * Real.sqrt (2 * Real.log (1 / δ) / n) := by
              have hsqrt_nonneg :
                  0 ≤ Real.sqrt (2 * Real.log (1 / δ) / n) := Real.sqrt_nonneg _
              nlinarith [hrc_nonneg, hsqrt_nonneg]
  · have hb_pos : 0 < R.b := lt_of_le_of_ne R.b_nonneg (Ne.symm hb0)
    let ε : ℝ := R.b * Real.sqrt (2 * Real.log (1 / δ) / n)
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hε_nonneg : 0 ≤ ε := by
      dsimp [ε]
      positivity
    have htail := uniform_deviation_tail_bound_countable_of_pos
      (μ := μ) (n := n) (f := fΩ) hf_meas (X := id) measurable_id
      (b := R.b) hb_pos hf_bdd (ε := ε) hε_nonneg
    let bad : Set (Fin n → Ω) :=
      {ω | 2 • rademacherComplexity n fΩ μ id + ε ≤
        uniformDeviation n fΩ μ id (id ∘ ω)}
    let E : Set (Fin n → Ω) := badᶜ
    have hbad_meas : MeasurableSet bad := by
      exact measurableSet_le measurable_const
        ((uniformDeviation_measurable (n := n) (f := fΩ)
          (μ := μ) id hf_meas).comp measurable_id)
    have hE_meas : MeasurableSet E := hbad_meas.compl
    have hbad_le_delta : Measure.pi (fun _ : Fin n => μ) bad ≤ ENNReal.ofReal δ := by
      have hbad_toReal : (Measure.pi (fun _ : Fin n => μ) bad).toReal ≤ δ := by
        have hle_exp := htail
        have hexp_le : Real.exp (-ε ^ 2 * n / (2 * R.b ^ 2)) ≤ δ := by
          have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
            apply Real.log_nonneg
            have : (1 : ℝ) ≤ 1 / δ := by
              rw [le_div_iff₀ hδ]
              simpa using hδ'
            exact this
          have hsqrt_sq : (Real.sqrt (2 * Real.log (1 / δ) / n)) ^ 2 =
              2 * Real.log (1 / δ) / n := by
            rw [Real.sq_sqrt]
            positivity
          have hcalc : -ε ^ 2 * n / (2 * R.b ^ 2) = Real.log δ := by
            dsimp [ε]
            rw [mul_pow, hsqrt_sq]
            field_simp [hb_pos.ne', hn_pos.ne']
            ring_nf
            rw [Real.log_inv δ]
            ring
          rw [hcalc, Real.exp_log hδ]
        exact hle_exp.trans hexp_le
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (le_of_lt hδ)]
      exact hbad_toReal
    have hE_prob : Measure.pi (fun _ : Fin n => μ) E ≥ 1 - ENNReal.ofReal δ := by
      dsimp [E]
      rw [measure_compl hbad_meas (measure_ne_top _ _), measure_univ]
      exact tsub_le_tsub_left hbad_le_delta 1
    -- Derive the local Rademacher bound from the bridge + R.ψ_ub.
    have hrad_local :
        rademacherComplexity n
            (fun i ω => if norm (F i) ≤ r then F i (X ω) else 0) μ id
          ≤ R.ψ n r :=
      (rademacherComplexity_zeroOut_le_starHullZeroOut F norm μ X n
        (fun S σ => hrad_bdd S σ) hrad_int).trans (R.ψ_ub n r hr_nonneg)
    have hrad_crit :
        rademacherComplexity n fΩ μ id ≤ r * criticalRadius (R.ψ n) := by
      exact le_trans (by simpa [fΩ] using hrad_local)
        (subRoot_homogeneity (R.ψ_subRoot n) hcrit_pos hr_lb hcrit_fp)
    refine ⟨E, hE_meas, hE_prob, ?_⟩
    intro ω hω i hi
    have hgood : ¬ (2 • rademacherComplexity n fΩ μ id + ε ≤
        uniformDeviation n fΩ μ id (id ∘ ω)) := by
      simpa [E, bad] using hω
    have hdev_lt :
        uniformDeviation n fΩ μ id ω < 2 * (r * criticalRadius (R.ψ n)) + ε := by
      have hnot : uniformDeviation n fΩ μ id ω <
          2 • rademacherComplexity n fΩ μ id + ε := by
        rw [not_le] at hgood
        simpa [Function.comp_def] using hgood
      have hrad_two :
          2 • rademacherComplexity n fΩ μ id + ε ≤
            2 * (r * criticalRadius (R.ψ n)) + ε := by
        simpa [two_nsmul, fΩ] using
          add_le_add_right
            (mul_le_mul_of_nonneg_left hrad_crit (by norm_num : (0 : ℝ) ≤ 2)) ε
      exact hnot.trans_le hrad_two
    have hpoint_le_dev :
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ i (ω k))
          - μ[fun ω' => fΩ i (id ω')]|
          ≤ uniformDeviation n fΩ μ id ω := by
      dsimp [uniformDeviation]
      apply le_ciSup (f := fun j : ι =>
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))
          - μ[fun ω' => fΩ j (id ω')]|)
      rw [bddAbove_def]
      use 2 * R.b
      intro y hy
      rcases hy with ⟨j, rfl⟩
      have hsample :
          |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))| ≤ R.b := by
        calc
          _ = (n : ℝ)⁻¹ * |Finset.univ.sum fun k : Fin n => fΩ j (ω k)| := by
            rw [abs_mul, abs_of_nonneg]
            exact inv_nonneg.mpr (Nat.cast_nonneg _)
          _ ≤ (n : ℝ)⁻¹ * (Finset.univ.sum fun _ : Fin n => R.b) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                (Finset.sum_le_sum fun k _ => hf_bdd j (ω k))
            · positivity
          _ = R.b := by
            simp
            field_simp [hn_pos.ne']
      have hmean : |μ[fun ω' => fΩ j (id ω')]| ≤ R.b := by
        calc
          _ ≤ ∫ ω', |fΩ j (id ω')| ∂μ := abs_integral_le_integral_abs
          _ ≤ ∫ _ω', R.b ∂μ := by
            apply integral_mono
            · exact Integrable.of_bound ((hf_meas j).abs.aestronglyMeasurable) R.b
                (by
                  filter_upwards with ω'
                  simpa [Real.norm_eq_abs] using hf_bdd j ω')
            · exact integrable_const R.b
            · intro ω'
              exact hf_bdd j ω'
          _ = R.b := by simp
      calc
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))
            - μ[fun ω' => fΩ j (id ω')]| ≤
            |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))|
              + |μ[fun ω' => fΩ j (id ω')]| := abs_sub _ _
        _ ≤ 2 * R.b := by linarith
    have hmain :
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ i (ω k))
          - μ[fun ω' => fΩ i (id ω')]|
          ≤ 4 * r * criticalRadius (R.ψ n) + ε := by
      have hpoint := hpoint_le_dev.trans (le_of_lt hdev_lt)
      have hrc_nonneg : 0 ≤ r * criticalRadius (R.ψ n) :=
        mul_nonneg hr_nonneg hcrit_nonneg
      nlinarith
    simpa [fΩ, hi, ε] using hmain

/-- **Sharp localized uniform deviation.**

    This is the reusable Foster--Syrgkanis Lemma 29 peeling layer over
    `localized_uniform_deviation`.  It takes a fixed sample size `n`, a
    diameter cap `Rmax`, and a critical-radius slack absorption hypothesis
    `hδ_dom`.  The conclusion is uniform over the whole class with the sharp
    localized shape

        `O(ρ_n · norm(F i) + ρ_n²)`,

    where `ρ_n` is any caller-supplied upper bound on
    `criticalRadius (R.ψ n)`.  This form is convenient for downstream
    rate theorems whose public critical radius is an explicit upper bound
    rather than the exact fixed point.

    The caller is responsible for proving the FS lower-bound condition in
    `hδ_dom`; in applications this is where assumptions such as
    `δ_n ≳ √((log log n + log(1/ζ)) / n)` are consumed. -/
theorem localized_uniform_deviation_sharp
    [MeasurableSpace 𝒳] [Nonempty 𝒳]
    [Nonempty ι] [Countable ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hX : Measurable X)
    (hF_meas : ∀ i, Measurable (F i))
    (R : LocalizedRegime Ω ι 𝒳 F norm μ X)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (n : ℕ) (hn : 0 < n)
    {ρ Rmax : ℝ}
    (hcrit_le_ρ : criticalRadius (R.ψ n) ≤ ρ)
    (hρ_pos : 0 < ρ)
    (hRmax_lb : ρ ≤ Rmax)
    (hcrit_pos : 0 < criticalRadius (R.ψ n))
    (hcrit_fp : R.ψ n (criticalRadius (R.ψ n)) ≤ (criticalRadius (R.ψ n)) ^ 2)
    (hrad_bdd : ∀ r : ℝ, ρ ≤ r →
      ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
        BddAbove (Set.range fun p : starHullParam ι =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)|))
    (hrad_int : ∀ r : ℝ, ρ ≤ r →
      Integrable
        (fun ω : Fin n → Ω =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω))
        (Measure.pi (fun _ => μ)))
    (hδ_dom : ∀ K : ℕ,
      Rmax ≤ ρ * (2 : ℝ) ^ K →
      R.b * Real.sqrt
          (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / n)
        ≤ ρ ^ 2) :
    ∃ E : Set (Fin n → Ω), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι,
        0 ≤ norm (F i) →
        norm (F i) ≤ Rmax →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]|
          ≤ 8 * ρ * norm (F i) + 5 * ρ ^ 2 := by
  classical
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
  have hRmax_nonneg : 0 ≤ Rmax := le_trans hρ_nonneg hRmax_lb
  obtain ⟨K, hK⟩ : ∃ K : ℕ, Rmax ≤ ρ * (2 : ℝ) ^ K := by
    rcases pow_unbounded_of_one_lt (Rmax / ρ) (by norm_num : (1 : ℝ) < 2) with
      ⟨K, hK⟩
    refine ⟨K, ?_⟩
    rw [div_lt_iff₀ hρ_pos] at hK
    linarith [hK]
  let η : ℝ := δ / (2 * ((K : ℝ) + 1))
  let slack : ℝ :=
    R.b * Real.sqrt (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / n)
  have hη_pos : 0 < η := by
    have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
    exact div_pos hδ hden
  have hη_le_one : η ≤ 1 := by
    have hden_pos : 0 < 2 * ((K : ℝ) + 1) := by positivity
    have hden_ge_one : 1 ≤ 2 * ((K : ℝ) + 1) := by
      have hK_nonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      nlinarith
    dsimp [η]
    rw [div_le_iff₀ hden_pos]
    nlinarith [hδ']
  have hEk_per_shell :
      ∀ k : Fin (K + 1),
        ∃ E_k : Set (Fin n → Ω), MeasurableSet E_k ∧
          Measure.pi (fun _ : Fin n => μ) E_k ≥ 1 - ENNReal.ofReal η ∧
          ∀ ω ∈ E_k, ∀ i : ι,
            norm (F i) ≤ ρ * (2 : ℝ) ^ (k : ℕ) →
              |(n : ℝ)⁻¹ * (Finset.univ.sum fun j : Fin n => F i (X (ω j)))
                  - μ[fun ω' => F i (X ω')]|
                ≤ 4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * ρ + slack := by
    intro k
    have hρ_le_shell : ρ ≤ ρ * (2 : ℝ) ^ (k : ℕ) := by
      have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      simpa using mul_le_mul_of_nonneg_left hpow_one hρ_nonneg
    have hr_lb : criticalRadius (R.ψ n) ≤ ρ * (2 : ℝ) ^ (k : ℕ) :=
      hcrit_le_ρ.trans hρ_le_shell
    rcases localized_uniform_deviation F norm μ X hX hF_meas R hη_pos hη_le_one n hn
        (r := ρ * (2 : ℝ) ^ (k : ℕ))
        hr_lb hcrit_pos hcrit_fp
        (hrad_bdd (ρ * (2 : ℝ) ^ (k : ℕ)) hρ_le_shell)
        (hrad_int (ρ * (2 : ℝ) ^ (k : ℕ)) hρ_le_shell) with
      ⟨E_k, hE_k_meas, hE_k_prob, hE_k_bound⟩
    refine ⟨E_k, hE_k_meas, hE_k_prob, ?_⟩
    intro ω hω i hi
    have h := hE_k_bound ω hω i hi
    have hshell_nonneg : 0 ≤ ρ * (2 : ℝ) ^ (k : ℕ) := by positivity
    have hcrit_le :
        4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * criticalRadius (R.ψ n)
          ≤ 4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * ρ := by
      nlinarith [hcrit_le_ρ, hshell_nonneg]
    calc
      |(n : ℝ)⁻¹ * (Finset.univ.sum fun j : Fin n => F i (X (ω j)))
          - μ[fun ω' => F i (X ω')]|
          ≤ 4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * criticalRadius (R.ψ n)
              + R.b * Real.sqrt (2 * Real.log (1 / η) / n) := h
      _ ≤ 4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * ρ + slack := by
        have hη_inv : 1 / η = 2 * ((K : ℝ) + 1) / δ := by
          dsimp [η]
          field_simp [ne_of_gt hδ]
        dsimp [slack]
        rw [hη_inv]
        linarith
  let μπ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let Ek : Fin (K + 1) → Set (Fin n → Ω) := fun k => (hEk_per_shell k).choose
  let Etot : Set (Fin n → Ω) := ⋂ k, Ek k
  have hEk_meas : ∀ k, MeasurableSet (Ek k) := by
    intro k
    exact (hEk_per_shell k).choose_spec.1
  have hEtot_meas : MeasurableSet Etot := by
    exact MeasurableSet.iInter hEk_meas
  have hEk_compl_le : ∀ k, μπ ((Ek k)ᶜ) ≤ ENNReal.ofReal η := by
    intro k
    have hprob : μπ (Ek k) ≥ 1 - ENNReal.ofReal η :=
      (hEk_per_shell k).choose_spec.2.1
    have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal η + μπ (Ek k) := by
      simpa [add_comm] using (tsub_le_iff_right.mp hprob)
    rw [measure_compl (hEk_meas k) (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr hone_le
  have hbad_subset : Etotᶜ ⊆ ⋃ k, (Ek k)ᶜ := by
    simp [Etot, Ek]
  have hbad_le : μπ (Etotᶜ) ≤ ENNReal.ofReal δ := by
    calc
      μπ (Etotᶜ) ≤ μπ (⋃ k, (Ek k)ᶜ) := measure_mono hbad_subset
      _ ≤ ∑ k : Fin (K + 1), μπ ((Ek k)ᶜ) :=
        measure_iUnion_fintype_le μπ fun k => (Ek k)ᶜ
      _ ≤ ∑ _k : Fin (K + 1), ENNReal.ofReal η := by
        exact Finset.sum_le_sum fun k _hk => hEk_compl_le k
      _ = (K + 1 : ℕ) * ENNReal.ofReal η := by simp
      _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ)) * ENNReal.ofReal η := by
        have hcoe :
            ((K : ENNReal) + 1) = ENNReal.ofReal ((K : ℝ) + 1) := by
          calc
            ((K : ENNReal) + 1)
                = ENNReal.ofReal (K : ℝ) + ENNReal.ofReal (1 : ℝ) := by simp
            _ = ENNReal.ofReal ((K : ℝ) + 1) :=
                (ENNReal.ofReal_add (Nat.cast_nonneg K) (by norm_num)).symm
        simpa [Nat.cast_add, Nat.cast_one] using
          congrArg (fun x => x * ENNReal.ofReal η) hcoe
      _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * η) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (((K + 1 : ℕ) : ℝ)))]
      _ = ENNReal.ofReal (δ / 2) := by
        congr 1
        dsimp [η]
        have hcast : (((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1) := by norm_num
        rw [hcast]
        field_simp
      _ ≤ ENNReal.ofReal δ := by
        exact ENNReal.ofReal_le_ofReal (by linarith [hδ])
  have hEtot_prob : μπ Etot ≥ 1 - ENNReal.ofReal δ := by
    rw [measure_compl hEtot_meas (measure_ne_top _ _), measure_univ] at hbad_le
    have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal δ + μπ Etot :=
      tsub_le_iff_right.mp hbad_le
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  refine ⟨Etot, hEtot_meas, hEtot_prob, ?_⟩
  intro ω hω i hi_nonneg hi_diam
  have hShell_select :
      ∃ k₀ : Fin (K + 1),
        norm (F i) ≤ ρ * (2 : ℝ) ^ (k₀ : ℕ) ∧
        4 * (ρ * (2 : ℝ) ^ (k₀ : ℕ)) * ρ
          ≤ 8 * ρ * norm (F i) + 4 * ρ ^ 2 := by
    have htop : norm (F i) ≤ ρ * (2 : ℝ) ^ K := hi_diam.trans hK
    by_cases hsmall : norm (F i) ≤ ρ
    · let kzero : Fin (K + 1) := ⟨0, Nat.succ_pos K⟩
      refine ⟨kzero, ?_, ?_⟩
      · change norm (F i) ≤ ρ * (2 : ℝ) ^ (0 : ℕ)
        rw [pow_zero, mul_one]
        exact hsmall
      · change 4 * (ρ * (2 : ℝ) ^ (0 : ℕ)) * ρ
            ≤ 8 * ρ * norm (F i) + 4 * ρ ^ 2
        rw [pow_zero, mul_one]
        nlinarith [hρ_nonneg, hi_nonneg, sq_nonneg ρ]
    · let p : ℕ → Prop := fun j => norm (F i) ≤ ρ * (2 : ℝ) ^ j
      have hex : ∃ j, p j := ⟨K, htop⟩
      let j0 : ℕ := Nat.find hex
      have hj0_spec : p j0 := Nat.find_spec hex
      have hj0_pos : 0 < j0 := by
        by_contra hj0_not
        have hj0_zero : j0 = 0 := Nat.eq_zero_of_not_pos hj0_not
        have : norm (F i) ≤ ρ := by
          change norm (F i) ≤ ρ * (2 : ℝ) ^ j0 at hj0_spec
          rw [hj0_zero, pow_zero, mul_one] at hj0_spec
          exact hj0_spec
        exact hsmall this
      have hj0_le_K : j0 ≤ K := Nat.find_min' hex htop
      refine ⟨⟨j0, Nat.lt_succ_of_le hj0_le_K⟩, hj0_spec, ?_⟩
      have hprev_not : ¬ p (j0 - 1) := by
        have hlt : j0 - 1 < j0 := Nat.sub_one_lt (Nat.ne_of_gt hj0_pos)
        exact Nat.find_min hex hlt
      have hprev_lt : ρ * (2 : ℝ) ^ (j0 - 1) < norm (F i) := not_le.mp hprev_not
      have hr_le_normF : ρ * (2 : ℝ) ^ j0 ≤ 2 * norm (F i) := by
        have hj0_eq : j0 = (j0 - 1) + 1 := by omega
        have hpow : (2 : ℝ) ^ j0 = (2 : ℝ) ^ (j0 - 1) * 2 := by
          conv_lhs => rw [hj0_eq, pow_succ]
        rw [hpow]
        nlinarith
      nlinarith
  rcases hShell_select with ⟨k₀, hk₀_radius, hk₀_rate⟩
  have hY_in_Ek : ω ∈ Ek k₀ := Set.iInter_subset (fun k => Ek k) k₀ hω
  have hdev := (hEk_per_shell k₀).choose_spec.2.2 ω hY_in_Ek i hk₀_radius
  have hslack : slack ≤ ρ ^ 2 := by
    simpa [slack] using hδ_dom K hK
  nlinarith [hdev, hk₀_rate, hslack]

end LocalizedUniformDeviation

end Concentration
end Stat
end Causalean
