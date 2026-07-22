/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized uniform deviation, in expectation (and offset form)

The localized-deviation theorem `localized_uniform_deviation` packages a
*high-probability* empirical-process bound for all functions inside a radius
ball by composing

1. **Symmetrization** (`expectation_le_rademacher`, FoML),
2. **Critical radius** (`localRademacher_le_critical_radius`),
3. **McDiarmid-on-sup** (the tail step).

Several downstream rate arguments need the bound *in expectation* rather
than with high probability — and, for self-localizing peeling arguments,
in the *offset* (positive-part) form.  This file isolates the first two
steps (symmetrization + critical radius), stopping *before* the McDiarmid
tail step, to expose:

* `localized_uniform_deviation_expectation` — the fixed-radius
  in-expectation envelope `𝔼[supₙₒᵣₘ≤ᵣ |(Pₙ−P)F i|] ≤ 2·r·δₙ`, `δₙ` the
  critical radius;
* `localized_offset_expectation` — the self-localizing offset
  positive-part envelope `𝔼[supᵢ {2|(Pₙ−P)F i| − Δᵢ/4}_+]`, bounded via the
  high-probability sharp bound, the deterministic Young/AM-GM offset
  optimisation `OffsetPeeling.offset_peeling_coeff`, and a bounded
  bad-event tail split, given a caller-supplied margin coupling
  `norm(F i) ≤ A·Δᵢ^κ`.

Both are general empirical-process facts for a `LocalizedRegime`; the
margin-coupled / VC specializations that turn `norm`-radius into a
problem-specific regret radius `Δ` are supplied by the caller.

References:
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Theorem 3.3.
* Foster, Syrgkanis, *Orthogonal statistical learning*,
  Ann. Statist. 51 (2023) 879–908 (offset / self-localizing form).
-/

import Causalean.Stat.Concentration.UniformDeviation.UniformDeviationLocalized
import Causalean.Mathlib.Analysis.OffsetPeeling

/-!
# Localized uniform deviation, in expectation

This file isolates the expectation-level pieces of localized uniform-deviation
arguments before the bounded-difference tail step.  The theorem
`localized_uniform_deviation_expectation` bounds the expected fixed-radius
empirical supremum by the critical-radius envelope, while
`localized_offset_expectation` gives the self-localizing positive-part offset
bound used in downstream margin-coupled empirical-process rates.
-/

namespace Causalean
namespace Stat
namespace Concentration

open Causalean.Mathlib.OffsetPeeling

open MeasureTheory ProbabilityTheory

variable {Ω ι 𝒳 : Type*} [MeasurableSpace Ω]

/-- The expected uniform deviation over a fixed localized radius is bounded by
twice the radius times the critical radius.

    Steps 1–2 of the localized-deviation argument (symmetrization + critical radius),
    stopping before the McDiarmid tail step.  For the radius-`r`
    zero-out localization of the class `F`, the expected uniform
    deviation is bounded by `2·r·δₙ`, where `δₙ = criticalRadius (R.ψ n)`
    is the population critical radius.

    This is the in-expectation analogue of `localized_uniform_deviation`;
    callers wanting an in-expectation localized envelope (instead of a
    high-probability one) consume this directly. -/
theorem localized_uniform_deviation_expectation
    [MeasurableSpace 𝒳] [Nonempty 𝒳]
    [Nonempty ι] [Countable ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hX : Measurable X)
    (hF_meas : ∀ i, Measurable (F i))
    (R : LocalizedRegime Ω ι 𝒳 F norm μ X)
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr_lb : criticalRadius (R.ψ n) ≤ r)
    (hcrit_pos : 0 < criticalRadius (R.ψ n))
    (hcrit_fp : R.ψ n (criticalRadius (R.ψ n)) ≤ (criticalRadius (R.ψ n)) ^ 2)
    (hrad_int : Integrable
      (fun ω : Fin n → Ω =>
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω))
      (Measure.pi (fun _ => μ))) :
    ∫ ω, uniformDeviation n
        (fun i (ω' : Ω) => if norm (F i) ≤ r then F i (X ω') else 0) μ id (id ∘ ω)
      ∂(Measure.pi (fun _ : Fin n => μ))
      ≤ 2 * r * criticalRadius (R.ψ n) := by
  -- Outline (lines 144-281 of `localized_uniform_deviation`, expectation half only):
  -- 1. (Symmetrization) `expectation_le_rademacher` applied to the bounded
  --    localized class `fΩ i ω = if norm (F i) ≤ r then F i (X ω) else 0`
  --    (envelope `R.b`, sample map `id`) gives
  --      𝔼[uniformDeviation n fΩ μ id] ≤ 2 · rademacherComplexity n fΩ μ id.
  -- 2. (Localization) `rademacherComplexity_zeroOut_le_starHullZeroOut` ⇒
  --      rademacherComplexity n fΩ μ id
  --        ≤ rademacherComplexity n (starHullZeroOut F norm r) μ X
  --        = localRademacherComplexity F norm μ X n r.
  -- 3. (Critical radius) `localRademacher_le_critical_radius`
  --    (with `R.ψ_subRoot n`, `R.ψ_ub n`, `hr_lb`, `hcrit_pos`, `hcrit_fp`) ⇒
  --      localRademacherComplexity F norm μ X n r ≤ r · criticalRadius (R.ψ n).
  -- Combine: 𝔼[uniformDeviation] ≤ 2 · r · criticalRadius (R.ψ n).
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
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsymm :
      (∫ ω, uniformDeviation n fΩ μ id (id ∘ ω)
        ∂(Measure.pi (fun _ : Fin n => μ)))
        ≤ 2 • rademacherComplexity n fΩ μ id :=
    uniform_deviation_expectation_le_two_smul_rademacher_complexity
      (μ := μ) (n := n) (f := fΩ) hn id
      (fun i => by simpa [Function.comp_def] using hf_meas i)
      R.b_nonneg hf_bdd
  have hrad_bridge :
      rademacherComplexity n fΩ μ id
        ≤ rademacherComplexity n (starHullZeroOut F norm r) μ X := by
    unfold rademacherComplexity
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun ω => by
        unfold empiricalRademacherComplexity
        refine mul_nonneg ?_ ?_
        · positivity
        · refine Finset.sum_nonneg ?_
          intro σ _
          refine Real.iSup_nonneg ?_
          intro i
          exact abs_nonneg _
    · exact hrad_int
    · exact Filter.Eventually.of_forall fun ω => by
        unfold empiricalRademacherComplexity
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum ?_
        intro σ _
        refine Real.iSup_le ?_ ?_
        · intro i
          let p : starHullParam ι := (⟨(1 : ℝ), by simp [Set.mem_Icc]⟩, i)
          have hbddX : BddAbove (Set.range fun p : starHullParam ι =>
              |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                starHullZeroOut F norm r p ((X ∘ ω) k)|) := by
            rw [bddAbove_def]
            use R.b
            intro y hy
            rcases hy with ⟨p, rfl⟩
            have hterm : ∀ k : Fin n,
                |(σ k : ℝ) * starHullZeroOut F norm r p ((X ∘ ω) k)| ≤ R.b := by
              intro k
              have hzero :
                  |starHullZeroOut F norm r p ((X ∘ ω) k)| ≤ R.b := by
                unfold starHullZeroOut
                by_cases hp : norm (starHullEval F p) ≤ r
                · simp only [hp, ↓reduceIte, starHullEval, Function.comp_apply, abs_mul]
                  calc
                    |p.1.val| * |F p.2 (X (ω k))|
                        = p.1.val * |F p.2 (X (ω k))| := by
                          rw [abs_of_nonneg p.1.property.1]
                    _ ≤ 1 * R.b := by
                          exact mul_le_mul p.1.property.2 (R.bound p.2 (ω k))
                            (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
                    _ = R.b := by ring
                · simpa [hp] using R.b_nonneg
              calc
                |(σ k : ℝ) * starHullZeroOut F norm r p ((X ∘ ω) k)|
                    = |(σ k : ℝ)| * |starHullZeroOut F norm r p ((X ∘ ω) k)| := by
                      rw [abs_mul]
                _ = |starHullZeroOut F norm r p ((X ∘ ω) k)| := by
                      rw [Signs.apply_abs', one_mul]
                _ ≤ R.b := hzero
            calc
              |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                  starHullZeroOut F norm r p ((X ∘ ω) k)|
                  = (n : ℝ)⁻¹ *
                    |∑ k : Fin n, (σ k : ℝ) *
                      starHullZeroOut F norm r p ((X ∘ ω) k)| := by
                    rw [abs_mul, abs_of_nonneg]
                    exact inv_nonneg.mpr (Nat.cast_nonneg _)
              _ ≤ (n : ℝ)⁻¹ * (Finset.univ.sum fun _ : Fin n => R.b) := by
                    apply mul_le_mul_of_nonneg_left
                    · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                        (Finset.sum_le_sum fun k _ => hterm k)
                    · positivity
              _ = R.b := by
                    simp
                    field_simp [hn_pos.ne']
          have hsum :
              ∑ k : Fin n, (σ k : ℝ) * fΩ i ((id ∘ ω) k)
                = ∑ k : Fin n, (σ k : ℝ) *
                  starHullZeroOut F norm r p ((X ∘ ω) k) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            have hp : starHullZeroOut F norm r p ((X ∘ ω) k)
                = fΩ i ((id ∘ ω) k) := by
              unfold fΩ starHullZeroOut
              rw [starHullEval_one]
              rfl
            rw [hp]
          rw [hsum]
          exact le_ciSup hbddX p
        · refine Real.iSup_nonneg ?_
          intro i
          exact abs_nonneg _
  have hrad_crit :
      rademacherComplexity n (starHullZeroOut F norm r) μ X
        ≤ r * criticalRadius (R.ψ n) := by
    simpa [localRademacherComplexity] using
      (localRademacher_le_critical_radius
        (F := F) (norm := norm) (μ := μ) (X := X) (n := n)
        (hψ := R.ψ_subRoot n) (hub := R.ψ_ub n)
        (r := r) hr_lb hcrit_pos hcrit_fp)
  have hrad :
      rademacherComplexity n fΩ μ id ≤ r * criticalRadius (R.ψ n) :=
    hrad_bridge.trans hrad_crit
  calc
    (∫ ω, uniformDeviation n
        (fun i (ω' : Ω) => if norm (F i) ≤ r then F i (X ω') else 0) μ id (id ∘ ω)
      ∂(Measure.pi (fun _ : Fin n => μ)))
        = ∫ ω, uniformDeviation n fΩ μ id (id ∘ ω)
          ∂(Measure.pi (fun _ : Fin n => μ)) := by
          rfl
    _ ≤ 2 • rademacherComplexity n fΩ μ id := hsymm
    _ ≤ 2 * (r * criticalRadius (R.ψ n)) := by
          simpa [two_nsmul] using
            mul_le_mul_of_nonneg_left hrad (by norm_num : (0 : ℝ) ≤ 2)
    _ = 2 * r * criticalRadius (R.ψ n) := by ring

/-- The expected positive part of the localized offset process is controlled by
a critical-radius term plus a small bad-event tail.

    The self-localizing offset form of the localized deviation bound,
    assembled from three existing pieces:

    * the high-probability sharp localized deviation
      `localized_uniform_deviation_sharp`, which gives, on a `1-δ` event,
      `|(Pₙ−P)F i| ≤ 8·ρ·norm(F i) + 5·ρ²` uniformly over the class
      (`ρ` an upper bound on the critical radius);
    * the deterministic Young/AM-GM offset optimisation
      `OffsetPeeling.offset_peeling_coeff`, which bounds
      `{a·t^κ − c·t}_+ ≤ offsetPeelingConstantC c κ · a^{1/(1−κ)}`;
    * a bounded bad-event tail split (the integrand is `≤ 4·R.b`).

    With a caller-supplied margin coupling `norm(F i) ≤ A·(Δ i)^κ` linking
    the localization radius `norm` to a problem radius `Δ` (the regret), the
    offset positive part has expectation bounded by

        `offsetPeelingConstantC (1/8) κ · (16·ρ·A)^{1/(1−κ)} + 10·ρ² + 4·R.b·δ`.

    The caller chooses `ρ` = the VC critical-radius rate and `δ` = a
    polynomially-small failure probability to obtain a clean
    `(B²/n)^{A_α}(log n)^p`-type rate (with `A_α` determined by `κ`). -/
theorem localized_offset_expectation
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
        ≤ ρ ^ 2)
    -- Class is uniformly within the diameter cap (so the sharp bound applies to every `i`).
    (hnorm_nonneg : ∀ i, 0 ≤ norm (F i))
    (hnorm_le : ∀ i, norm (F i) ≤ Rmax)
    -- Problem radius `Δ` (the regret) and the margin coupling `norm(F i) ≤ A·(Δ i)^κ`.
    (Δ : ι → ℝ) (κ A : ℝ) (hκ_pos : 0 < κ) (hκ_lt : κ < 1) (hA_nonneg : 0 ≤ A)
    (hΔ_nonneg : ∀ i, 0 ≤ Δ i)
    (hcoupling : ∀ i, norm (F i) ≤ A * (Δ i) ^ κ) :
    ∫ ω, (⨆ i : ι, max 0
        (2 * |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]| - Δ i / 4))
      ∂(Measure.pi (fun _ : Fin n => μ))
      ≤ offsetPeelingConstantC (1 / 8) κ * (16 * ρ * A) ^ (1 / (1 - κ))
          + 10 * ρ ^ 2 + 4 * R.b * δ := by
  -- Outline:
  -- 1. Obtain the `1-δ` good event `E` from `localized_uniform_deviation_sharp`
  --    (all the sharp-bound hypotheses are present); on `E`, for every `i`,
  --    `|dev_i| ≤ 8·ρ·norm(F i) + 5·ρ²`.
  -- 2. On `E`, using the coupling `norm(F i) ≤ A·(Δ i)^κ`:
  --      2|dev_i| − Δ i/4 ≤ (16ρA·(Δ i)^κ − (Δ i)/8) + (10ρ² − (Δ i)/8),
  --    so `max 0 (·) ≤ max 0 (16ρA·(Δ i)^κ − (Δ i)/8) + max 0 (10ρ² − (Δ i)/8)`
  --    (split `max 0 (x+y) ≤ max 0 x + max 0 y`).
  --    `offset_peeling_coeff (c:=1/8) (θ:=κ) (a:=16ρA) (t:=Δ i)` bounds the first
  --    by `offsetPeelingConstantC (1/8) κ · (16ρA)^{1/(1−κ)}`; the second `≤ 10ρ²`.
  --    Hence on `E` the integrand `⨆ i, {…}_+` ≤ that constant (uniform in `i`).
  -- 3. Off `E` (prob ≤ δ): `|dev_i| ≤ 2·R.b`, so the integrand `≤ 4·R.b`.
  -- 4. Split the integral over `E`/`Eᶜ`: the integrand is bounded (hence integrable),
  --    and `∫ ≤ (good const)·1 + 4·R.b·δ`.
  classical
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let μπ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  have hsharp := localized_uniform_deviation_sharp
    (F := F) (norm := norm) (μ := μ) (X := X)
    hX hF_meas R hδ hδ' n hn
    hcrit_le_ρ hρ_pos hRmax_lb hcrit_pos hcrit_fp hrad_bdd hrad_int hδ_dom
  rcases hsharp with ⟨E, hE_meas, hE_prob, hE_bound⟩
  let dev : ι → (Fin n → Ω) → ℝ := fun i ω =>
    (n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
      - μ[fun ω' => F i (X ω')]
  let g : (Fin n → Ω) → ℝ := fun ω =>
    ⨆ i : ι, max 0 (2 * |dev i ω| - Δ i / 4)
  let Cgood : ℝ :=
    offsetPeelingConstantC (1 / 8) κ * (16 * ρ * A) ^ (1 / (1 - κ))
      + 10 * ρ ^ 2
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
  have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
  have h16ρA_nonneg : 0 ≤ 16 * ρ * A := by positivity
  have hCgood_nonneg : 0 ≤ Cgood := by
    dsimp [Cgood]
    have hC :
        0 ≤ offsetPeelingConstantC (1 / 8) κ :=
      offsetPeelingConstantC_nonneg (1 / 8) κ (by norm_num) hκ_nonneg hκ_lt
    have hpow : 0 ≤ (16 * ρ * A) ^ (1 / (1 - κ)) :=
      Real.rpow_nonneg h16ρA_nonneg _
    nlinarith [mul_nonneg hC hpow, sq_nonneg ρ]
  have hdev_global : ∀ ω i, |dev i ω| ≤ 2 * R.b := by
    intro ω i
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsample :
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))|
          ≤ R.b := by
      calc
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))|
            = (n : ℝ)⁻¹ *
                |Finset.univ.sum fun k : Fin n => F i (X (ω k))| := by
              rw [abs_mul, abs_of_nonneg]
              exact inv_nonneg.mpr (Nat.cast_nonneg _)
        _ ≤ (n : ℝ)⁻¹ * (Finset.univ.sum fun _ : Fin n => R.b) := by
              apply mul_le_mul_of_nonneg_left
              · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                  (Finset.sum_le_sum fun k _ => R.bound i (ω k))
              · positivity
        _ = R.b := by
              simp
              field_simp [hn_pos.ne']
    have hmean : |μ[fun ω' => F i (X ω')]| ≤ R.b := by
      have hFiX_meas : Measurable (fun ω' : Ω => F i (X ω')) :=
        (hF_meas i).comp hX
      calc
        |μ[fun ω' => F i (X ω')]| ≤
            ∫ ω', |F i (X ω')| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _ω', R.b ∂μ := by
              apply integral_mono
              · exact Integrable.of_bound hFiX_meas.abs.aestronglyMeasurable R.b
                  (by
                    filter_upwards with ω'
                    simpa [Real.norm_eq_abs] using R.bound i ω')
              · exact integrable_const R.b
              · intro ω'
                exact R.bound i ω'
        _ = R.b := by simp
    dsimp [dev]
    calc
      |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
          - μ[fun ω' => F i (X ω')]| ≤
          |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))|
            + |μ[fun ω' => F i (X ω')]| := abs_sub _ _
      _ ≤ 2 * R.b := by linarith
  have hglobal : ∀ ω, g ω ≤ 4 * R.b := by
    intro ω
    dsimp [g]
    refine Real.iSup_le ?_ (by nlinarith [R.b_nonneg])
    intro i
    refine max_le (by nlinarith [R.b_nonneg]) ?_
    have hdev := hdev_global ω i
    have hΔ := hΔ_nonneg i
    nlinarith
  have hgood_point : ∀ ω ∈ E, g ω ≤ Cgood := by
    intro ω hω
    dsimp [g]
    refine Real.iSup_le ?_ hCgood_nonneg
    intro i
    have hdev_good : |dev i ω| ≤ 8 * ρ * norm (F i) + 5 * ρ ^ 2 := by
      simpa [dev] using hE_bound ω hω i (hnorm_nonneg i) (hnorm_le i)
    have hpow_nonneg : 0 ≤ (Δ i) ^ κ :=
      Real.rpow_nonneg (hΔ_nonneg i) κ
    have hcoupled :
        8 * ρ * norm (F i) ≤ 8 * ρ * (A * (Δ i) ^ κ) := by
      exact mul_le_mul_of_nonneg_left (hcoupling i) (by positivity)
    have hd_le :
        |dev i ω| ≤ 8 * ρ * (A * (Δ i) ^ κ) + 5 * ρ ^ 2 :=
      hdev_good.trans (add_le_add hcoupled (le_refl _))
    let x : ℝ := 16 * ρ * A * (Δ i) ^ κ - (1 / 8 : ℝ) * Δ i
    let y : ℝ := 10 * ρ ^ 2 - (1 / 8 : ℝ) * Δ i
    have harg :
        2 * |dev i ω| - Δ i / 4 ≤ x + y := by
      dsimp [x, y]
      nlinarith [hd_le]
    have hsplit : max 0 (x + y) ≤ max 0 x + max 0 y := by
      exact max_le
        (add_nonneg (le_max_left 0 x) (le_max_left 0 y))
        (add_le_add (le_max_right 0 x) (le_max_right 0 y))
    have hpeel :
        max 0 x ≤
          offsetPeelingConstantC (1 / 8) κ * (16 * ρ * A) ^ (1 / (1 - κ)) := by
      dsimp [x]
      simpa [mul_assoc, div_eq_mul_inv] using
        (offset_peeling_coeff (1 / 8) κ (16 * ρ * A) (Δ i)
          (by norm_num) hκ_pos hκ_lt h16ρA_nonneg (hΔ_nonneg i))
    have hy : max 0 y ≤ 10 * ρ ^ 2 := by
      dsimp [y]
      refine max_le ?_ ?_
      · nlinarith [sq_nonneg ρ]
      · have hΔ8 : 0 ≤ (1 / 8 : ℝ) * Δ i := by
          exact mul_nonneg (by norm_num) (hΔ_nonneg i)
        nlinarith
    calc
      max 0 (2 * |dev i ω| - Δ i / 4)
          ≤ max 0 (x + y) := max_le_max_left 0 harg
      _ ≤ max 0 x + max 0 y := hsplit
      _ ≤ Cgood := by
            dsimp [Cgood]
            nlinarith [hpeel, hy]
  have hbad_prob : μπ (Eᶜ) ≤ ENNReal.ofReal δ := by
    have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal δ + μπ E := by
      simpa [add_comm, μπ] using (tsub_le_iff_right.mp hE_prob)
    rw [measure_compl hE_meas (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr hone_le
  have hbad_real : μπ.real (Eᶜ) ≤ δ := by
    rw [measureReal_def]
    have htop₁ : μπ (Eᶜ) ≠ ⊤ := measure_ne_top _ _
    have htop₂ : ENNReal.ofReal δ ≠ ⊤ := ENNReal.ofReal_ne_top
    have h := (ENNReal.toReal_le_toReal htop₁ htop₂).mpr hbad_prob
    simpa [ENNReal.toReal_ofReal (le_of_lt hδ)] using h
  have hdev_meas : ∀ i, Measurable (dev i) := by
    intro i
    dsimp [dev]
    fun_prop
  have hg_meas : Measurable g := by
    dsimp [g]
    exact Measurable.iSup fun i => by
      fun_prop
  have hg_nonneg : ∀ ω, 0 ≤ g ω := by
    intro ω
    dsimp [g]
    exact Real.iSup_nonneg fun i => le_max_left _ _
  have hg_int : Integrable g μπ := by
    refine Integrable.of_bound hg_meas.aestronglyMeasurable (4 * R.b) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg ω)]
    exact hglobal ω
  let H : (Fin n → Ω) → ℝ := fun ω =>
    Cgood + (4 * R.b) * (Eᶜ).indicator (fun _ : Fin n → Ω => (1 : ℝ)) ω
  have hH_int : Integrable H μπ := by
    dsimp [H]
    exact (integrable_const Cgood).add
      (((integrable_const (1 : ℝ)).indicator hE_meas.compl).const_mul (4 * R.b))
  have hpoint : ∀ ω, g ω ≤ H ω := by
    intro ω
    by_cases hω : ω ∈ E
    · have hg := hgood_point ω hω
      dsimp [H]
      rw [Set.indicator_of_notMem]
      · linarith
      · simpa using hω
    · have hg := hglobal ω
      dsimp [H]
      rw [Set.indicator_of_mem]
      · nlinarith [hCgood_nonneg]
      · simpa using hω
  have hInt_le : ∫ ω, g ω ∂μπ ≤ ∫ ω, H ω ∂μπ :=
    integral_mono hg_int hH_int hpoint
  have hH_eval :
      ∫ ω, H ω ∂μπ =
        Cgood + (4 * R.b) * μπ.real (Eᶜ) := by
    dsimp [H]
    rw [integral_add]
    · rw [integral_const, integral_const_mul]
      rw [show (fun _ : Fin n → Ω => (1 : ℝ)) = 1 from rfl,
        integral_indicator_one hE_meas.compl]
      simp [μπ]
    · exact integrable_const Cgood
    · exact ((integrable_const (1 : ℝ)).indicator hE_meas.compl).const_mul (4 * R.b)
  have hH_bound :
      ∫ ω, H ω ∂μπ ≤ Cgood + 4 * R.b * δ := by
    rw [hH_eval]
    have h4Rb_nonneg : 0 ≤ 4 * R.b := by nlinarith [R.b_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left hbad_real h4Rb_nonneg]
  calc
    ∫ ω, (⨆ i : ι, max 0
        (2 * |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]| - Δ i / 4))
      ∂(Measure.pi (fun _ : Fin n => μ))
        = ∫ ω, g ω ∂μπ := by
            rfl
    _ ≤ ∫ ω, H ω ∂μπ := hInt_le
    _ ≤ Cgood + 4 * R.b * δ := hH_bound
    _ = offsetPeelingConstantC (1 / 8) κ * (16 * ρ * A) ^ (1 / (1 - κ))
          + 10 * ρ ^ 2 + 4 * R.b * δ := by
        rfl

end Concentration
end Stat
end Causalean
