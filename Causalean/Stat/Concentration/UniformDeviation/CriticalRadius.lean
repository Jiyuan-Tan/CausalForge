/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Critical radius and sub-root functions

The **critical radius** `δ_n` of a non-negative function `ψ : ℝ → ℝ` is
the smallest `δ > 0` with `ψ δ ≤ δ²`. Under the Bartlett--Bousquet--Mendelson
sub-root condition used in this file, `ψ` is non-negative and non-decreasing
on non-negative radii, and `ψ(r)/r` is non-increasing on positive radii. The
critical radius encapsulates the "fixed-point" scale at which
empirical-process fluctuations equal their target scale.

## Design choice

We define the critical radius **deterministically / population-wise**:
`ψ` is a deterministic upper envelope on
`rademacherComplexity n F μ X` over `starHull F ∩ ball(0, r)`, and
`criticalRadius ψ` does **not** depend on the sample. Sample-pathwise critical
radii can be connected to this API by first proving a deterministic envelope
for the sample-dependent complexity bound of interest.

Reference:
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Lemma 3.2 and Definition 3.1.
-/

import Causalean.Stat.Concentration.Rademacher.StarHull
import Causalean.Stat.Concentration.Rademacher.Rademacher

/-! # Critical radius

This file defines deterministic critical radii for sub-root envelopes of local
Rademacher complexity. It provides star-hull localization helpers
(`starHullBall`, `starHullZeroOut`, `starHullZeroOutScaleCoeff`), the envelope
predicate `RademacherUpperBound`, the critical-radius definition
`criticalRadius`, the sub-root predicate `SubRoot`, fixed-point and positivity
lemmas for the critical radius, and the boundedness helper
`starHullZeroOut_bddAbove_of_bound`.
-/

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory

section CriticalRadius

variable {Ω ι 𝒳 : Type*} [MeasurableSpace Ω]

/-- The intersection of the star hull with a `norm`-ball of radius `r`. -/
def starHullBall (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) (r : ℝ) :
    Set (𝒳 → ℝ) :=
  starHull F ∩ {f | norm f ≤ r}

/-- The **zero-out** family on the `starHullParam` index: each parameter
    `(α, i)` is mapped to `α • F i` if its norm is at most `r`, and to
    the zero function otherwise. This is the localized star-hull family used
    by the local Rademacher-complexity envelope. -/
noncomputable def starHullZeroOut
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) (r : ℝ) :
    starHullParam ι → 𝒳 → ℝ :=
  fun p x => if norm (starHullEval F p) ≤ r then starHullEval F p x else 0

private lemma ciSup_mul_const_of_Icc {A : Type*} [Nonempty A]
    (c : A → ℝ) (b : ℝ) (hc_le : ∀ a, c a ≤ 1) (hb : 0 ≤ b) :
    (⨆ a : A, c a * b) = (⨆ a : A, c a) * b := by
  classical
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hc_le a
  have hcb_bdd : BddAbove (Set.range fun a : A => c a * b) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨a, rfl⟩
    calc
      c a * b ≤ 1 * b := mul_le_mul_of_nonneg_right (hc_le a) hb
      _ = b := one_mul b
  apply le_antisymm
  · refine ciSup_le ?_
    intro a
    exact mul_le_mul_of_nonneg_right (le_ciSup hc_bdd a) hb
  · by_cases hb0 : b = 0
    · simp [hb0]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hsup_le : (⨆ a : A, c a) ≤ (⨆ a : A, c a * b) / b := by
        refine ciSup_le ?_
        intro a
        exact (le_div_iff₀ hbpos).mpr (le_ciSup hcb_bdd a)
      exact (le_div_iff₀ hbpos).mp hsup_le

/-- The largest active star-hull scalar for a fixed base index. -/
noncomputable def starHullZeroOutScaleCoeff
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) (r : ℝ) (i : ι) : ℝ :=
  ⨆ a : Set.Icc (0 : ℝ) 1,
    if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0

/-- The star-hull zero-out scale coefficient is at most one. -/
lemma starHullZeroOutScaleCoeff_le_one
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) (r : ℝ) (i : ι) :
    starHullZeroOutScaleCoeff F norm r i ≤ 1 := by
  classical
  let c : Set.Icc (0 : ℝ) 1 → ℝ := fun a =>
    if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0
  change (⨆ a : Set.Icc (0 : ℝ) 1, c a) ≤ 1
  refine ciSup_le ?_
  intro a
  dsimp [c]
  split_ifs
  · exact a.property.2
  · norm_num

/-- The inner Rademacher term for a fixed star-hull scalar factors into that
scalar, or zero when the radius test fails. -/
lemma starHullZeroOut_inner_term_eq
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) (r : ℝ)
    {n : ℕ} (ω : Fin n → 𝒳) (σ : Signs n)
    (a : Set.Icc (0 : ℝ) 1) (i : ι) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        starHullZeroOut F norm r (a, i) (ω k)| =
      (if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0) *
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)| := by
  by_cases h : norm (starHullEval F (a, i)) ≤ r
  · have ha_nonneg : 0 ≤ (a : ℝ) := a.property.1
    have hsum :
        (∑ k : Fin n, (σ k : ℝ) * ((a : ℝ) * F i (ω k))) =
          (a : ℝ) * ∑ k : Fin n, (σ k : ℝ) * F i (ω k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    simp only [starHullZeroOut, h, if_true, starHullEval]
    rw [hsum]
    have hrearr :
        (n : ℝ)⁻¹ * ((a : ℝ) * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)) =
          (a : ℝ) * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)) := by
      ring
    rw [hrearr, abs_mul, abs_of_nonneg ha_nonneg]
  · simp [starHullZeroOut, h]

/-- Supremizing over the star-hull scalar collapses to the largest active
coefficient times the base-class inner Rademacher term. -/
lemma starHullZeroOut_inner_sup_eq
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) (r : ℝ)
    {n : ℕ} (ω : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    (⨆ a : Set.Icc (0 : ℝ) 1,
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        starHullZeroOut F norm r (a, i) (ω k)|) =
      starHullZeroOutScaleCoeff F norm r i *
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)| := by
  classical
  simp_rw [starHullZeroOut_inner_term_eq F norm r ω σ]
  exact ciSup_mul_const_of_Icc
    (fun a : Set.Icc (0 : ℝ) 1 =>
      if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0)
    _ (by
      intro a
      dsimp
      split_ifs
      · exact a.property.2
      · norm_num)
    (abs_nonneg _)

/-- **Deterministic upper envelope on the localized Rademacher
    complexity.** For every radius `r ≥ 0`, the population Rademacher
    complexity of the zero-out family on the radius-`r` star-hull ball
    is at most `ψ r`.

    The predicate is stated directly in terms of `starHullZeroOut`, so it can
    be applied to any local-Rademacher argument whose localized class is built
    by zeroing out star-hull parameters outside the radius. The structural
    homogeneity of `starHullEval`, parametrized by `(α, i) ∈ [0,1] × ι`, is
    what lets a sub-root envelope on the base class `F` control this localized
    family. -/
def RademacherUpperBound
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳) (n : ℕ) (ψ : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    rademacherComplexity n (starHullZeroOut F norm r) μ X ≤ ψ r

/-- The **critical radius** of `ψ`: the infimum over `δ > 0` with
    `ψ δ ≤ δ²`. Defined via `sInf`; if the set is empty (e.g. `ψ` grows
    faster than `δ²` everywhere), the value is `0` by Mathlib convention. -/
noncomputable def criticalRadius (ψ : ℝ → ℝ) : ℝ :=
  sInf {δ | 0 < δ ∧ ψ δ ≤ δ ^ 2}

/-- The critical radius is non-negative. -/
lemma criticalRadius_nonneg (ψ : ℝ → ℝ) : 0 ≤ criticalRadius ψ := by
  rw [criticalRadius]
  by_cases hS : ({δ : ℝ | 0 < δ ∧ ψ δ ≤ δ ^ 2} : Set ℝ).Nonempty
  · refine le_csInf hS ?_
    rintro δ ⟨hδ, _⟩
    exact le_of_lt hδ
  · have hEmpty : ({δ : ℝ | 0 < δ ∧ ψ δ ≤ δ ^ 2} : Set ℝ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty]
    simp

/-- Any `δ > 0` with `ψ δ ≤ δ²` upper-bounds the critical radius. -/
lemma criticalRadius_le {ψ : ℝ → ℝ} {δ : ℝ}
    (h₀ : 0 < δ) (h₁ : ψ δ ≤ δ ^ 2) :
    criticalRadius ψ ≤ δ := by
  rw [criticalRadius]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro η ⟨hη, _⟩
    exact le_of_lt hη
  · exact ⟨h₀, h₁⟩

/-- A radius envelope is sub-root when it is non-negative and non-decreasing
    on non-negative radii, and its value divided by the radius is
    non-increasing as the positive radius grows.

    This is the radius-parameterized Bartlett--Bousquet--Mendelson sub-root
    condition used by the local-Rademacher critical-radius lemmas in this file:
    non-negativity controls the envelope scale, monotonicity gives the
    one-sided squeeze needed for continuity, and the non-increasing ratio
    transfers a fixed-point bound at `δ*` to all larger radii. -/
def SubRoot (ψ : ℝ → ℝ) : Prop :=
  (∀ r ≥ 0, 0 ≤ ψ r) ∧
  (∀ r₁ r₂, 0 ≤ r₁ → r₁ ≤ r₂ → ψ r₁ ≤ ψ r₂) ∧
  (∀ r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → ψ r₁ / r₁ ≥ ψ r₂ / r₂)

/-- **Sub-root inequality.** If `ψ` is sub-root and `δ*` satisfies
    `ψ δ* ≤ δ*²`, then for every `r ≥ δ*`,

        ψ r  ≤  r · δ*.

    This is the lemma local-Rademacher arguments cite: it converts the
    fixed-point bound `ψ(δ*) ≤ δ*²` into a *linear* bound on `ψ` for
    radii past the critical radius. -/
lemma subRoot_homogeneity {ψ : ℝ → ℝ} (h : SubRoot ψ)
    {δ_star r : ℝ}
    (hδ_star : 0 < δ_star) (hr : δ_star ≤ r) (hcrit : ψ δ_star ≤ δ_star ^ 2) :
    ψ r ≤ r * δ_star := by
  obtain ⟨_, _, hRatio⟩ := h
  have hr_pos : 0 < r := lt_of_lt_of_le hδ_star hr
  have hRatio' : ψ r / r ≤ ψ δ_star / δ_star := hRatio δ_star r hδ_star hr
  have hδ_bound : ψ δ_star / δ_star ≤ δ_star := by
    rw [div_le_iff₀ hδ_star]
    simpa [pow_two] using hcrit
  have hmain : ψ r / r ≤ δ_star := le_trans hRatio' hδ_bound
  have hmul := mul_le_mul_of_nonneg_right hmain (le_of_lt hr_pos)
  rwa [div_mul_cancel₀ _ (ne_of_gt hr_pos), mul_comm] at hmul

/-- **Sub-root continuity.** If `ψ` is sub-root, then `ψ` is continuous on the
    open ray `(0, ∞)`. The non-increasing ratio condition `ψ(r)/r ↘` supplies
    the linear squeeze bounds, while monotonicity of `ψ` supplies the opposite
    side of the squeeze. -/
lemma subRoot_continuousOn_Ioi {ψ : ℝ → ℝ} (h : SubRoot ψ) :
    ContinuousOn ψ (Set.Ioi (0 : ℝ)) := by
  obtain ⟨_, hMono, hRatio⟩ := h
  rw [(isOpen_Ioi).continuousOn_iff]
  intro r₀ hr₀
  have hr₀pos : 0 < r₀ := hr₀
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · refine Filter.Tendsto.squeeze' (f := ψ)
      (g := fun r : ℝ => r * (ψ r₀ / r₀)) (h := fun _ : ℝ => ψ r₀) ?_ ?_ ?_ ?_
    · simpa [ContinuousWithinAt, Pi.mul_apply, mul_div_cancel₀ _ (ne_of_gt hr₀pos)] using
        ((continuous_id.mul continuous_const).continuousWithinAt :
          ContinuousWithinAt (fun r : ℝ => r * (ψ r₀ / r₀)) (Set.Iic r₀) r₀)
    · exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => ψ r₀) (nhdsWithin r₀ (Set.Iic r₀)) (nhds (ψ r₀)))
    · have hpos_eventually :
          ∀ᶠ r in nhdsWithin r₀ (Set.Iic r₀), 0 < r :=
        Filter.Eventually.filter_mono inf_le_left (isOpen_Ioi.mem_nhds hr₀)
      filter_upwards [self_mem_nhdsWithin, hpos_eventually]
        with r hrle hrpos
      have hratio : ψ r₀ / r₀ ≤ ψ r / r := hRatio r r₀ hrpos hrle
      rw [le_div_iff₀ hrpos] at hratio
      simpa [mul_comm] using hratio
    · have hpos_eventually :
          ∀ᶠ r in nhdsWithin r₀ (Set.Iic r₀), 0 < r :=
        Filter.Eventually.filter_mono inf_le_left (isOpen_Ioi.mem_nhds hr₀)
      filter_upwards [self_mem_nhdsWithin, hpos_eventually] with r hrle hrpos
      exact hMono r r₀ (le_of_lt hrpos) hrle
  · refine Filter.Tendsto.squeeze' (f := ψ)
      (g := fun _ : ℝ => ψ r₀) (h := fun r : ℝ => r * (ψ r₀ / r₀)) ?_ ?_ ?_ ?_
    · exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => ψ r₀) (nhdsWithin r₀ (Set.Ici r₀)) (nhds (ψ r₀)))
    · simpa [ContinuousWithinAt, Pi.mul_apply, mul_div_cancel₀ _ (ne_of_gt hr₀pos)] using
        ((continuous_id.mul continuous_const).continuousWithinAt :
          ContinuousWithinAt (fun r : ℝ => r * (ψ r₀ / r₀)) (Set.Ici r₀) r₀)
    · filter_upwards [self_mem_nhdsWithin] with r hle
      exact hMono r₀ r (le_of_lt hr₀pos) hle
    · filter_upwards [self_mem_nhdsWithin] with r hle
      have hrpos : 0 < r := lt_of_lt_of_le hr₀pos hle
      have hratio : ψ r / r ≤ ψ r₀ / r₀ := hRatio r₀ r hr₀pos hle
      rw [div_le_iff₀ hrpos] at hratio
      simpa [mul_comm] using hratio

/-- **Fixed-point property at the critical radius.** If `ψ` is sub-root
    and there exists a witness `r₀ > 0` with `ψ r₀ ≤ r₀²`, then the
    critical radius itself satisfies `ψ (criticalRadius ψ) ≤ (criticalRadius ψ)²`,
    provided `0 < criticalRadius ψ`.

    Proof sketch: by sub-root continuity (see `subRoot_continuousOn_Ioi`)
    the function `r ↦ ψ r - r²` is continuous on `(0, ∞)`, and the set
    `{δ | 0 < δ ∧ ψ δ ≤ δ²}` is closed from the right; the infimum is
    therefore attained (it is a limit of a decreasing sequence in a closed
    set). -/
lemma criticalRadius_fp_of_subRoot {ψ : ℝ → ℝ} (h : SubRoot ψ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hψ_r₀ : ψ r₀ ≤ r₀ ^ 2)
    (hpos : 0 < criticalRadius ψ) :
    ψ (criticalRadius ψ) ≤ (criticalRadius ψ) ^ 2 := by
  let c := criticalRadius ψ
  let S : Set ℝ := {δ | 0 < δ ∧ ψ δ ≤ δ ^ 2}
  have hS_nonempty : S.Nonempty := ⟨r₀, hr₀, hψ_r₀⟩
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro δ ⟨hδ, _⟩
    exact le_of_lt hδ
  have hc_closure : c ∈ closure S := by
    change sInf S ∈ closure S
    exact csInf_mem_closure hS_nonempty hS_bdd
  haveI : (nhdsWithin c S).NeBot :=
    (mem_closure_iff_nhdsWithin_neBot.mp hc_closure)
  have hcpos : 0 < c := hpos
  have hcont : ContinuousAt ψ c :=
    ((isOpen_Ioi).continuousOn_iff.mp (subRoot_continuousOn_Ioi h)) hcpos
  have hψ_tendsto :
      Filter.Tendsto ψ (nhdsWithin c S) (nhds (ψ c)) :=
    hcont.continuousWithinAt
  have hsq_tendsto :
      Filter.Tendsto (fun δ : ℝ => δ ^ 2) (nhdsWithin c S) (nhds (c ^ 2)) := by
    simpa [ContinuousWithinAt] using
      ((continuous_id.pow 2).continuousWithinAt :
        ContinuousWithinAt (fun δ : ℝ => δ ^ 2) S c)
  have hev : ∀ᶠ δ in nhdsWithin c S, ψ δ ≤ δ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδ.2
  exact le_of_tendsto_of_tendsto hψ_tendsto hsq_tendsto hev

/-- **Positivity of the critical radius.** If `ψ` is sub-root, has a
    witness `r₀ > 0` with `ψ r₀ ≤ r₀²`, and grows faster than `δ²` near
    the origin (there exists `ε ∈ (0, r₀)` with `ε² < ψ ε`), then
    `criticalRadius ψ > 0`.

    Design note: the hypothesis `ε ^ 2 < ψ ε` (strict inequality) is
    used rather than `ε ^ 2 ≤ ψ ε` because the definition of
    `criticalRadius` uses `ψ δ ≤ δ²` (non-strict), so strict
    positivity at `ε` rules `ε` out of the infimum set and gives the
    lower bound `criticalRadius ψ ≥ ε > 0`.  This matches BBM 2005 §3,
    where the growth condition is stated as `ψ(δ)/δ → ∞` as `δ → 0⁺`;
    the existential here is the finite-witness version of that condition.

    Proof sketch: since `ε` is not in `{δ | 0 < δ ∧ ψ δ ≤ δ²}` and
    every element of that set is `≥ ε` by continuity+intermediate value
    (using `subRoot_continuousOn_Ioi`), the infimum is `≥ ε > 0`. -/
lemma criticalRadius_pos_of_subRoot {ψ : ℝ → ℝ} (h : SubRoot ψ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hψ_r₀ : ψ r₀ ≤ r₀ ^ 2)
    (hgrows : ∃ ε > 0, ε < r₀ ∧ ε ^ 2 < ψ ε) :
    0 < criticalRadius ψ := by
  obtain ⟨ε, hεpos, hεlt, hεgrow⟩ := hgrows
  let S : Set ℝ := {δ | 0 < δ ∧ ψ δ ≤ δ ^ 2}
  have hS_nonempty : S.Nonempty := ⟨r₀, hr₀, hψ_r₀⟩
  have hlower : ∀ δ ∈ S, ε ≤ δ := by
    intro δ hδ
    by_contra hnot
    have hδlt : δ < ε := lt_of_not_ge hnot
    obtain ⟨_, _, hRatio⟩ := h
    have hratio : ψ δ / δ ≥ ψ ε / ε :=
      hRatio δ ε hδ.1 (le_of_lt hδlt)
    have hε_lt_ratio : ε < ψ ε / ε := by
      rw [lt_div_iff₀ hεpos]
      simpa [pow_two] using hεgrow
    have hδ_lt_ratio : δ < ψ δ / δ :=
      lt_of_lt_of_le (lt_trans hδlt hε_lt_ratio) hratio
    rw [lt_div_iff₀ hδ.1] at hδ_lt_ratio
    have hδ_sq_lt : δ ^ 2 < ψ δ := by
      simpa [pow_two] using hδ_lt_ratio
    exact (not_le_of_gt hδ_sq_lt) hδ.2
  have hcrit_ge : ε ≤ criticalRadius ψ := by
    rw [criticalRadius]
    change ε ≤ sInf S
    exact le_csInf hS_nonempty hlower
  exact lt_of_lt_of_le hεpos hcrit_ge

/-- The signed empirical average over the zero-out star hull is bounded above by
the uniform bound on the base family: if `|F i x| ≤ b` for every index and point,
then for any sample and sign vector the family of signed averages indexed by
star-hull parameters has `b` as an upper bound.

This discharges the `BddAbove` side condition (`hrad_bdd`) that the localized
uniform-deviation bound demands of the empirical star-hull Rademacher process,
from a uniform bound on the base class. The bound `b` holds at *every* point `x`
(not only at the sampled points), which is what the supremum over all
star-hull parameters requires. -/
lemma starHullZeroOut_bddAbove_of_bound
    {𝒳 ι : Type*} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b)
    (m : ℕ) (r : ℝ) (S_fin : Fin m → 𝒳) (σ : Signs m) :
    BddAbove (Set.range fun p : starHullParam ι =>
      |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
        starHullZeroOut F norm r p (S_fin k)|) := by
  classical
  refine ⟨b, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hzero_abs : ∀ x, |starHullZeroOut F norm r p x| ≤ b := by
    intro x
    by_cases hp : norm (starHullEval F p) ≤ r
    · have ha_nonneg : 0 ≤ (p.1 : ℝ) := p.1.property.1
      have ha_le : (p.1 : ℝ) ≤ 1 := p.1.property.2
      calc
        |starHullZeroOut F norm r p x| = |(p.1 : ℝ) * F p.2 x| := by
          simp [starHullZeroOut, hp, starHullEval]
        _ = |(p.1 : ℝ)| * |F p.2 x| := abs_mul _ _
        _ = (p.1 : ℝ) * |F p.2 x| := by rw [abs_of_nonneg ha_nonneg]
        _ ≤ (p.1 : ℝ) * b := by
          exact mul_le_mul_of_nonneg_left (hbound p.2 x) ha_nonneg
        _ ≤ 1 * b := by
          exact mul_le_mul_of_nonneg_right ha_le hb
        _ = b := one_mul b
    · simp [starHullZeroOut, hp, hb]
  by_cases hm0 : m = 0
  · subst m
    simp [hb]
  · have hm_pos_nat : 0 < m := Nat.pos_of_ne_zero hm0
    have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    calc
      |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut F norm r p (S_fin k)|
          = (m : ℝ)⁻¹ *
              |∑ k : Fin m, (σ k : ℝ) *
                starHullZeroOut F norm r p (S_fin k)| := by
            rw [abs_mul, abs_of_nonneg]
            exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ (m : ℝ)⁻¹ * ∑ _k : Fin m, b := by
            apply mul_le_mul_of_nonneg_left
            · calc
                |∑ k : Fin m, (σ k : ℝ) *
                    starHullZeroOut F norm r p (S_fin k)|
                    ≤ ∑ k : Fin m,
                        |(σ k : ℝ) * starHullZeroOut F norm r p (S_fin k)| :=
                      Finset.abs_sum_le_sum_abs _ _
                _ = ∑ k : Fin m, |starHullZeroOut F norm r p (S_fin k)| := by
                      apply Finset.sum_congr rfl
                      intro k _hk
                      rw [abs_mul, Signs.apply_abs']
                      simp
                _ ≤ ∑ _k : Fin m, b :=
                      Finset.sum_le_sum fun k _hk => hzero_abs (S_fin k)
            · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ = b := by
            simp
            field_simp [ne_of_gt hm_pos]

end CriticalRadius

end Concentration
end Stat
end Causalean
