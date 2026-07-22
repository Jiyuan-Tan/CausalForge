/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized Rademacher complexity

The localized Rademacher complexity restricts the supremum to functions
of small `norm`-radius. The headline argument:

1. **Star-hull lifting**: localizing in `F` is dominated by localizing in
   `starHull F`, which is convenient because the star hull is closed
   under non-negative rescaling.
2. **Sub-root envelope**: a sub-root `ψ` upper-bounds the Rademacher
   complexity of `starHull F ∩ ball(0, r)`.
3. **Critical radius**: `criticalRadius ψ` is the fixed point at which
   the linear bound `ψ(r) ≤ r · δ_n` (`subRoot_homogeneity`) kicks in.

Combining (1)–(3) gives `localRademacherComplexity F norm μ X n r ≤
r · δ_n` for every `r ≥ δ_n` — the **localized inequality** that drives
fast rates.

## Definition (zero-out form, `starHullParam` index)

We define `localRademacherComplexity F norm μ X n r` as the FoML
`rademacherComplexity` of the zero-out family
`starHullZeroOut F norm r : starHullParam ι → 𝒳 → ℝ` (defined in
`CriticalRadius.lean`), which sends `(α, i) ↦ α • F i` if
`norm (α • F i) ≤ r` and to the zero function otherwise.

The `starHullParam ι := Set.Icc (0:ℝ) 1 × ι` index replaces the earlier
subtype `starHullIndex F = {f // f ∈ starHull F}` (which had no
countable dense parameterisation when `F` was countable). The
parameterised form admits clean monotonicity arguments through
`starHullEval`.

The zero-out form fixes the monotonicity direction:

* **Non-negativity**: each empirical Rademacher term is a non-negative
  expression in the absolute-value form, so the integral is non-negative.
* **Monotonicity in `r`**: as `r` increases, more parameters switch from
  the zero function to `α • F i`, which can only increase the empirical
  Rademacher complexity (the supremum over an expanding family of
  values).

The zero-out form sidesteps the lack of `Fintype` on the localised set
`{ p : starHullParam ι // norm (starHullEval F p) ≤ r }` (which would
otherwise be required to feed the FoML `rademacherComplexity` definition
directly).

Reference:
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Theorem 3.3.
-/

import Causalean.Stat.Concentration.Rademacher.StarHull
import Causalean.Stat.Concentration.UniformDeviation.CriticalRadius
import Causalean.Stat.Concentration.Rademacher.Rademacher

/-! # Local Rademacher Complexity

This file develops local Rademacher complexity for star-hull neighborhoods of a
function class, using the zero-out parameterization
`starHullZeroOut F norm r : starHullParam ι → 𝒳 → ℝ`.

The main definition is `localRademacherComplexity`, the Rademacher complexity
of the localized star-hull class at radius `r`. The supporting lemmas establish
non-negativity, radius monotonicity, pointwise zero-out comparison, and the
bridge from an ordinary `ι`-indexed zero-out class to the star-hull
parameterization.

The headline theorem `localRademacher_le_critical_radius` consumes a
`RademacherUpperBound` and a `SubRoot` envelope to show that, above the critical
radius, the localized Rademacher complexity is bounded by
`r * criticalRadius ψ`. This is the local-complexity step used in uniform
deviation bounds. -/

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory

section LocalRademacher

variable {Ω ι 𝒳 : Type*} [MeasurableSpace Ω]

/-- The **localized Rademacher complexity** of a function family `F`,
    evaluated at radius `r` and norm `norm`. Defined via the *zero-out*
    re-indexing: each parameter `(α, i) : starHullParam ι` contributes
    `α • F i` if `norm (α • F i) ≤ r`, and the constant `0` otherwise. -/
noncomputable def localRademacherComplexity
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳) (n : ℕ) (r : ℝ) : ℝ :=
  rademacherComplexity n (starHullZeroOut F norm r) μ X

/-- The localized Rademacher complexity is non-negative.

    Follows from the pointwise non-negativity of
    `empiricalRademacherComplexity` (each `⨆`-summand is an absolute
    value) plus `MeasureTheory.integral_nonneg`. -/
lemma localRademacherComplexity_nonneg
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳) (n : ℕ) (r : ℝ) :
    0 ≤ localRademacherComplexity F norm μ X n r := by
  unfold localRademacherComplexity rademacherComplexity
  apply MeasureTheory.integral_nonneg
  intro ω
  unfold empiricalRademacherComplexity
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro σ _
    refine Real.iSup_nonneg ?_
    intro p
    exact abs_nonneg _

/-! ### Pointwise comparison helper

The proof of `localRademacherComplexity_mono_r` factors through a
**per-sample** monotonicity of `empiricalRademacherComplexity`:

If for every parameter `p : starHullParam ι` and every sample-coordinate
`k : Fin n`, the map applied to `(p, S k)` is dominated in absolute
value, then the empirical Rademacher complexity inherits the bound.

The key inequality used is `|x| ≤ |y|` ⇒ `iSup` monotone (over the
absolute-value sup). For the zero-out family, the dominance
`|starHullZeroOut F norm r₁| ≤ |starHullZeroOut F norm r₂|` for `r₁ ≤ r₂`
holds pointwise: when `norm (...) ≤ r₁` the two are equal; otherwise the
`r₁`-side is zero. -/

/-- **Per-σ, per-`i` inner-expression bound implies empirical
    Rademacher comparison.**

    The hypothesis is deliberately stated on each signed empirical inner
    expression. A pointwise bound `|f i x| ≤ |g i x|` is not sufficient, because
    sign cancellation in the inner sum can reverse the comparison. -/
lemma empiricalRademacherComplexity_mono_of_inner
    {ι' : Type*} [Nonempty ι'] {n : ℕ}
    (f g : ι' → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (hbdd_g : ∀ σ : Signs n,
      BddAbove (Set.range fun i =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * g i (S k)|))
    (h : ∀ σ : Signs n, ∀ i : ι',
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)|
        ≤ |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * g i (S k)|) :
    empiricalRademacherComplexity n f S
      ≤ empiricalRademacherComplexity n g S := by
  unfold empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine Real.iSup_le ?_ ?_
  · intro i
    exact le_trans (h σ i) (le_ciSup (hbdd_g σ) i)
  · refine Real.iSup_nonneg ?_
    intro i
    exact abs_nonneg _

/-- **Per-`(p, σ, S)` zero-out inner-expression bound.** For `r₁ ≤ r₂`,
    the inner expression of `empiricalRademacherComplexity` for the
    zero-out family at `r₁` is dominated in absolute value by that at
    `r₂`. This is the precise ingredient the helper above consumes for
    `localRademacherComplexity_mono_r`. -/
lemma abs_inner_starHullZeroOut_mono
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    {n : ℕ} (S : Fin n → 𝒳) (σ : Signs n) (p : starHullParam ι) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        starHullZeroOut F norm r₁ p (S k)|
      ≤ |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        starHullZeroOut F norm r₂ p (S k)| := by
  -- Three-way case split on `norm (starHullEval F p)` vs `r₁, r₂`.
  -- Cases (A) `≤ r₁` and (C) `> r₂`: both inner sums are equal pointwise
  -- (either both zero, or both `α • F i`). Case (B) `r₁ < · ≤ r₂`: LHS
  -- inner sum is `0` (every k is zeroed), so |LHS| = 0 ≤ |RHS|.
  by_cases h₁ : norm (starHullEval F p) ≤ r₁
  · have h₂ : norm (starHullEval F p) ≤ r₂ := le_trans h₁ hr
    apply le_of_eq
    have hsum :
        ∑ k : Fin n, (σ k : ℝ) * starHullZeroOut F norm r₁ p (S k)
          = ∑ k : Fin n, (σ k : ℝ) * starHullZeroOut F norm r₂ p (S k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [starHullZeroOut, h₁, h₂]
    rw [hsum]
  · -- LHS evaluates to 0 since every coordinate is zeroed out
    have hlhs :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r₁ p (S k) = 0 := by
      have : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          (σ k : ℝ) * starHullZeroOut F norm r₁ p (S k) = 0 := by
        intro k _
        simp [starHullZeroOut, h₁]
      rw [Finset.sum_eq_zero this]
      ring
    rw [hlhs]
    simp only [abs_zero, Int.reduceNeg, abs_mul, abs_inv, Nat.abs_cast, ge_iff_le]
    positivity

/-- **Pointwise monotonicity of the zero-out family in the radius.**
    For `r₁ ≤ r₂`, `|starHullZeroOut F norm r₁ p x| ≤ |starHullZeroOut F norm r₂ p x|`
    coordinatewise. -/
lemma abs_starHullZeroOut_mono
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) (p : starHullParam ι) (x : 𝒳) :
    |starHullZeroOut F norm r₁ p x| ≤ |starHullZeroOut F norm r₂ p x| := by
  unfold starHullZeroOut
  by_cases h₁ : norm (starHullEval F p) ≤ r₁
  · -- both branches active and equal
    have h₂ : norm (starHullEval F p) ≤ r₂ := le_trans h₁ h
    simp [h₁, h₂]
  · -- LHS is 0 in absolute value; RHS is non-negative
    simp [h₁]

/-- **Pointwise dominance by the inclusion.** The zero-out family is
    dominated coordinatewise (in absolute value) by the un-localised
    inclusion `starHullEval F`. -/
lemma abs_starHullZeroOut_le_starHullEval
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (r : ℝ) (p : starHullParam ι) (x : 𝒳) :
    |starHullZeroOut F norm r p x| ≤ |starHullEval F p x| := by
  unfold starHullZeroOut
  by_cases h : norm (starHullEval F p) ≤ r
  · simp [h]
  · simp [h]

/-- The localized Rademacher complexity is monotone in the radius.

    Pointwise per-`ω`: empirical Rademacher complexities are ordered by
    `empiricalRademacherComplexity_mono_of_abs_le` and
    `abs_starHullZeroOut_mono`. Lifting to the integral requires
    integrability of the upper function (the larger radius gives the
    larger empirical Rademacher process), which is the
    `hint` hypothesis. -/
lemma localRademacherComplexity_mono_r
    [Nonempty ι] (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳) (n : ℕ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂)
    (hbdd : ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
      BddAbove (Set.range fun p : starHullParam ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r₂ p (S k)|))
    (hint : Integrable
      (fun ω : Fin n → Ω =>
        empiricalRademacherComplexity n (starHullZeroOut F norm r₂) (X ∘ ω))
      (Measure.pi (fun _ => μ))) :
    localRademacherComplexity F norm μ X n r₁
      ≤ localRademacherComplexity F norm μ X n r₂ := by
  unfold localRademacherComplexity rademacherComplexity
  apply MeasureTheory.integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun ω => by
      unfold empiricalRademacherComplexity
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro σ _
        refine Real.iSup_nonneg ?_
        intro p
        exact abs_nonneg _
  · exact hint
  · exact Filter.Eventually.of_forall fun ω =>
      empiricalRademacherComplexity_mono_of_inner
        (starHullZeroOut F norm r₁) (starHullZeroOut F norm r₂) (X ∘ ω)
        (fun σ => hbdd (X ∘ ω) σ)
        (fun σ p => abs_inner_starHullZeroOut_mono F norm h (X ∘ ω) σ p)

/-- **Upper-bound consumption.** A `RademacherUpperBound ψ` directly
    bounds the localized Rademacher complexity by `ψ r` for every
    `r ≥ 0` — by definition, since `RademacherUpperBound` is stated in
    terms of `starHullZeroOut`, the same integrand defining
    `localRademacherComplexity`. -/
lemma localRademacherComplexity_le_upperBound
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ}
    {μ : Measure Ω} {X : Ω → 𝒳} {n : ℕ}
    {ψ : ℝ → ℝ} (hub : RademacherUpperBound F norm μ X n ψ)
    {r : ℝ} (hr : 0 ≤ r) :
    localRademacherComplexity F norm μ X n r ≤ ψ r := by
  unfold localRademacherComplexity
  exact hub r hr

/-- **Localized inequality (headline).** Past the critical radius, the
    localized Rademacher complexity is bounded by `r · δ_n`. This is the
    workhorse inequality consumed by `localized_uniform_deviation`.

    The proof chains `localRademacherComplexity_le_upperBound` with
    `subRoot_homogeneity`. The fixed-point witness for `criticalRadius ψ`
    is supplied as `hcrit_fp : ψ (criticalRadius ψ) ≤ criticalRadius ψ ^ 2`
    (clients typically derive this from a sub-root regularity argument
    that places the critical radius inside `{δ | ψ δ ≤ δ²}`). -/
theorem localRademacher_le_critical_radius
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ}
    {μ : Measure Ω} {X : Ω → 𝒳} {n : ℕ}
    {ψ : ℝ → ℝ} (hψ : SubRoot ψ)
    (hub : RademacherUpperBound F norm μ X n ψ)
    {r : ℝ} (hr : criticalRadius ψ ≤ r)
    (hcrit_pos : 0 < criticalRadius ψ)
    (hcrit_fp : ψ (criticalRadius ψ) ≤ criticalRadius ψ ^ 2) :
    localRademacherComplexity F norm μ X n r ≤ r * criticalRadius ψ := by
  have h_r_nn : 0 ≤ r := le_trans (criticalRadius_nonneg ψ) hr
  have h₁ : localRademacherComplexity F norm μ X n r ≤ ψ r :=
    localRademacherComplexity_le_upperBound hub h_r_nn
  have h₂ : ψ r ≤ r * criticalRadius ψ :=
    subRoot_homogeneity hψ hcrit_pos hr hcrit_fp
  exact le_trans h₁ h₂

/-- **Bridge lemma: `ι`-indexed zero-out class ≤ `starHullParam ι`-indexed zero-out class.**

    The function family `fun i ω => if norm (F i) ≤ r then F i (X ω) else 0`
    (indexed by `ι`, with sample map `id` and no `X`-composition in the
    Rademacher index) is the `(1, ·)` slice of `starHullZeroOut F norm r`
    post-composed with `X`:

        starHullZeroOut F norm r (⟨1, _⟩, i) (X ω)
          = if norm (F i) ≤ r then F i (X ω) else 0

    Hence the empirical sup over `i : ι` is bounded by the empirical sup
    over `p : starHullParam ι`, giving a matching Rademacher inequality
    after taking expectations. -/
lemma rademacherComplexity_zeroOut_le_starHullZeroOut
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    (n : ℕ) {r : ℝ}
    (hbdd : ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
      BddAbove (Set.range fun p : starHullParam ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r p (S k)|))
    (hint : Integrable
      (fun ω : Fin n → Ω =>
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω))
      (Measure.pi (fun _ => μ))) :
    rademacherComplexity n
        (fun i ω => if norm (F i) ≤ r then F i (X ω) else 0) μ id
      ≤ rademacherComplexity n (starHullZeroOut F norm r) μ X := by
  -- The LHS integrand is `empiricalRademacherComplexity n f (id ∘ ω)` where
  -- `f i x = if norm (F i) ≤ r then F i x else 0`. For any sample path
  -- `S = X ∘ ω`, the function `f i (S k) = starHullZeroOut F norm r (⟨1, _⟩, i) (S k)`,
  -- so the sup over `i : ι` is dominated by the sup over `p : starHullParam ι`.
  -- The integral inequality then follows from pointwise dominance plus integrability.
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
  · exact hint
  · exact Filter.Eventually.of_forall fun ω => by
      unfold empiricalRademacherComplexity
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum ?_
      intro σ _
      refine Real.iSup_le ?_ ?_
      · intro i
        let p : starHullParam ι := (⟨(1 : ℝ), by simp [Set.mem_Icc]⟩, i)
        have hsum :
            ∑ k : Fin n, (σ k : ℝ) *
                (if norm (F i) ≤ r then F i (X ((id ∘ ω) k)) else 0)
              = ∑ k : Fin n, (σ k : ℝ) *
                starHullZeroOut F norm r p ((X ∘ ω) k) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          have hp : starHullZeroOut F norm r p ((X ∘ ω) k)
              = if norm (F i) ≤ r then F i (X ((id ∘ ω) k)) else 0 := by
            unfold starHullZeroOut
            rw [starHullEval_one]
            rfl
          rw [hp]
        rw [hsum]
        exact le_ciSup (hbdd (X ∘ ω) σ) p
      · refine Real.iSup_nonneg ?_
        intro i
        exact abs_nonneg _

end LocalRademacher

end Concentration
end Stat
end Causalean
