/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Quantile function (generalized inverse of a cdf)

Causal-agnostic statistical primitive: a lower generalized inverse of
Mathlib's `cdf` for a real measure. For probability measures this is the usual
left-continuous quantile function:

    quantile μ τ := sInf {x : ℝ | τ ≤ cdf μ x}.

Mathlib provides `ProbabilityTheory.cdf μ : StieltjesFunction ℝ` (monotone,
right-continuous, with limits 0 / 1) but has **no** generalized inverse; this
file supplies it together with the key order characterisation

    quantile μ τ ≤ x  ↔  τ ≤ cdf μ x       (for `0 < τ < 1`),

i.e. the Galois-style connection between the cdf and its inverse.  This is the
foundation for quantile treatment effects (`PO/ID/Exact/QTE/QuantileEffect.lean`)
and the quantile form of Lee trimming.

The interior restriction `0 < τ < 1` is intrinsic: for `τ ≤ 0` the defining set
is all of `ℝ` (so `sInf = 0` is meaningless) and for `τ ≥ 1` it can be empty in
the continuous, full-support case.  These are exactly the degenerate quantiles.
File is project-agnostic and a candidate for upstream contribution to Mathlib.
-/

import Mathlib.Probability.CDF

/-! # Quantile Function

This file defines the lower quantile function of a real probability measure as
the generalized inverse of its cumulative distribution function. It proves the
basic order characterization that connects cumulative distribution functions and
their quantiles away from the degenerate endpoints. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set Filter Topology

variable (μ : Measure ℝ)

/-- The defining super-level set of the cdf, `{x | τ ≤ cdf μ x}`. -/
def quantileSet (τ : ℝ) : Set ℝ := {x : ℝ | τ ≤ cdf μ x}

/-- The (lower) quantile function: the left-continuous generalized inverse of
the cdf, `quantile μ τ = inf {x : ℝ | τ ≤ cdf μ x}`. -/
noncomputable def quantile (τ : ℝ) : ℝ := sInf (quantileSet μ τ)

variable {μ}

/-- The super-level set is up-closed (monotonicity of the cdf). -/
lemma quantileSet_up_closed {τ x x' : ℝ} (hx : x ∈ quantileSet μ τ) (hxx' : x ≤ x') :
    x' ∈ quantileSet μ τ :=
  le_trans hx (monotone_cdf μ hxx')

/-- For `0 < τ`, the super-level set is bounded below: since `cdf μ → 0` at
`-∞`, any point where the cdf already drops below `τ` is a lower bound. -/
lemma bddBelow_quantileSet {τ : ℝ} (hτ : 0 < τ) : BddBelow (quantileSet μ τ) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot μ).eventually_lt_const hτ)
  refine ⟨N, fun s hs => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact absurd hs (not_le.mpr (hN s hlt.le))

/-- For `τ < 1`, the super-level set is nonempty: since `cdf μ → 1` at `+∞`,
some point has cdf above `τ`. -/
lemma nonempty_quantileSet {τ : ℝ} (hτ : τ < 1) : (quantileSet μ τ).Nonempty := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_cdf_atTop μ).eventually_const_lt hτ)
  exact ⟨N, (hN N le_rfl).le⟩

/-- **Key membership lemma.**  For interior `τ ∈ (0,1)`, the quantile lands in
the super-level set: `τ ≤ cdf μ (quantile μ τ)`.  This is where
right-continuity of the cdf is used. -/
lemma le_cdf_quantile {τ : ℝ} (hτ1 : τ < 1) :
    τ ≤ cdf μ (quantile μ τ) := by
  set a := quantile μ τ with ha
  have hne : (quantileSet μ τ).Nonempty := nonempty_quantileSet hτ1
  -- Every point strictly above the inf lies in the (up-closed) super-level set.
  have hgt : ∀ x, a < x → τ ≤ cdf μ x := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
    exact quantileSet_up_closed hs hsx.le
  -- Right-continuity: cdf μ → cdf μ a along `𝓝[Ioi a] a`.
  have htends : Tendsto (cdf μ) (𝓝[Ioi a] a) (𝓝 (cdf μ a)) :=
    ((cdf μ).right_continuous a).mono_left (nhdsWithin_mono a Ioi_subset_Ici_self)
  -- Along that filter we stay in the super-level set, so the limit dominates τ.
  have hev : ∀ᶠ x in 𝓝[Ioi a] a, τ ≤ cdf μ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hgt x hx
  exact ge_of_tendsto htends hev

/-- **Galois connection (one direction).** If the quantile lies at or below
`x`, then the cdf has already reached level `τ` at `x`. -/
lemma le_cdf_of_quantile_le {τ x : ℝ} (hτ1 : τ < 1)
    (hx : quantile μ τ ≤ x) : τ ≤ cdf μ x :=
  le_trans (le_cdf_quantile hτ1) (monotone_cdf μ hx)

/-- **Galois connection (other direction).**  If the cdf reaches `τ` at `x`,
then the quantile is at or below `x`. -/
lemma quantile_le_of_le_cdf {τ x : ℝ} (hτ0 : 0 < τ) (hx : τ ≤ cdf μ x) :
    quantile μ τ ≤ x :=
  csInf_le (bddBelow_quantileSet hτ0) hx

/-- **Quantile / cdf Galois connection** for interior `τ ∈ (0,1)`:

    quantile μ τ ≤ x  ↔  τ ≤ cdf μ x. -/
theorem quantile_le_iff {τ x : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    quantile μ τ ≤ x ↔ τ ≤ cdf μ x :=
  ⟨le_cdf_of_quantile_le hτ1, quantile_le_of_le_cdf hτ0⟩

/-- The quantile function is monotone in the probability level `τ` on `(0,1)`. -/
lemma quantile_mono {τ τ' : ℝ} (hτ0 : 0 < τ) (hτ'1 : τ' < 1) (hττ' : τ ≤ τ') :
    quantile μ τ ≤ quantile μ τ' :=
  quantile_le_of_le_cdf hτ0 (le_trans hττ' (le_cdf_quantile hτ'1))

end Causalean.Stat
