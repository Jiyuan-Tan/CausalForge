/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Inference for interval-identified parameters: coverage vocabulary

Every interval-identification theorem in this library produces a *population
sandwich* `L ≤ θ₀ ≤ U` (Manski, Balke–Pearl, Lee, Proxy, …; see
`SandwichInterval.lean`).  Turning such bounds into a **confidence interval**
forces a choice that does not arise under point identification: should the random
interval cover the whole identified set `[L, U]`, or only the (single, unknown)
true value `θ₀ ∈ [L, U]`?  These are the two coverage notions of the partial-ID
inference literature:

* **Coverage of the identified set** (Horowitz–Manski 2000): the random interval
  contains all of `[L, U]`.  Formalized here as `RandomCoversIcc`.
* **Coverage of the parameter** (Imbens–Manski 2004): the random interval
  contains the point `θ₀`.  Formalized here as `RandomCoversPoint`.

As Imbens–Manski (2004, Lemma 1) observe, when `[L, U]` is not a singleton the
two notions genuinely differ, and confidence sets for the *point* are weakly
*smaller* than those for the *set*.  The easy direction — set coverage implies
point coverage, so a set-honest interval is automatically point-honest — is
`randomCoversIcc_subset_randomCoversPoint` below.

This file is pure measure theory: it has no dependency on the potential-outcome
framework, mirroring `PartialID/Basic.lean`.

## Main definitions

* `RandomCoversPoint A B θ` — the event that the random interval `[A ω, B ω]`
  contains the fixed value `θ`.
* `RandomCoversIcc A B L U` — the event that `[A ω, B ω]` contains the whole
  interval `[L, U]`.

## Main results

* `randomCoversIcc_subset_randomCoversPoint` — for `θ ∈ [L, U]`, set coverage
  implies point coverage (the easy half of Imbens–Manski Lemma 1).
* `honest_ci_set_cover` — the **abstract honest-CI lemma**: if the lower endpoint
  overshoots after widening with probability `≤ δ_L` and the upper endpoint
  undershoots after widening with probability `≤ δ_U`, then the widened interval
  `[L̂ − w_L, Û + w_U]` covers `[L, U]` with probability `≥ 1 − δ_L − δ_U`
  (a one-line union bound over the two one-sided endpoint-failure events).
* `honest_ci_point_cover` — the parameter-coverage corollary obtained by composing
  the previous two results.
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Coverage Vocabulary for Interval-Identified Parameters

This file defines the two coverage events used for confidence intervals around an
interval-identified scalar parameter: coverage of a fixed parameter value and
coverage of the whole identified interval. `RandomCoversPoint A B theta` is the
sample event that the random interval `[A omega, B omega]` contains `theta`;
`RandomCoversIcc A B L U` is the event that it contains the whole population
identified interval `[L, U]`.

The theorem `randomCoversIcc_subset_randomCoversPoint` records the elementary
Horowitz-Manski to Imbens-Manski implication: set coverage implies point
coverage for every true value inside `[L, U]`. The endpoint lemmas
`lowerOvershoot_subset_absMiss` and `upperUndershoot_subset_absMiss`, together
with `randomCoversIcc_compl_subset`, isolate the two one-sided failure events
used by concentration-based intervals. The abstract theorems
`honest_ci_set_cover` and `honest_ci_point_cover` then prove honest set and
parameter coverage from upper bounds on those endpoint miss probabilities. -/

namespace Causalean.PartialID.Inference

open MeasureTheory

variable {Ω : Type*}

/-- **Coverage of the parameter** (Imbens–Manski notion).  The event that the
random interval `[A ω, B ω]` contains the fixed real value `θ`.

This is a *sampling-level* object — a (random) subset of the sample space `Ω`,
indexed by the data-dependent endpoints `A, B` — not to be confused with the
*population* identified set `PartialID.IdentifiedInterval`.  Even under point
identification (`L = U`, identified set a singleton), this remains the coverage
event of the random confidence interval, which is the whole point of inference. -/
def RandomCoversPoint (A B : Ω → ℝ) (θ : ℝ) : Set Ω :=
  {ω | A ω ≤ θ ∧ θ ≤ B ω}

/-- **Coverage of the identified set** (Horowitz–Manski notion).  The event that
the random interval `[A ω, B ω]` contains the whole population interval `[L, U]`.
Equivalently `A ω ≤ L` and `U ≤ B ω`. -/
def RandomCoversIcc (A B : Ω → ℝ) (L U : ℝ) : Set Ω :=
  {ω | A ω ≤ L ∧ U ≤ B ω}

/-- **Set coverage ⟹ point coverage** (the easy half of Imbens–Manski 2004,
Lemma 1).  If the true value `θ` lies in the identified set `[L, U]`, then every
sample realization whose random interval covers all of `[L, U]` also covers `θ`.
Consequently a confidence interval that is honest for the *set* is automatically
honest for the *parameter* — which is why parameter-coverage intervals can be no
larger, and generically strictly smaller. -/
theorem randomCoversIcc_subset_randomCoversPoint (A B : Ω → ℝ) {L U θ : ℝ}
    (hθ : θ ∈ Set.Icc L U) :
    RandomCoversIcc A B L U ⊆ RandomCoversPoint A B θ := by
  rintro ω ⟨hAL, hUB⟩
  exact ⟨hAL.trans hθ.1, hθ.2.trans hUB⟩

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
/-- The complement of the set-coverage event is contained in the union of the
two one-sided endpoint-failure events: lower overshoot after widening or upper
undershoot after widening. -/
theorem randomCoversIcc_compl_subset {lo hi : Ω → ℝ} {L U wL wU : ℝ} :
    (RandomCoversIcc (fun ω => lo ω - wL) (fun ω => hi ω + wU) L U)ᶜ
      ⊆ {ω | L < lo ω - wL} ∪ {ω | hi ω + wU < U} := by
  intro ω hω
  simp only [RandomCoversIcc, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
  rcases hω with hL | hU
  · left
    exact hL
  · right
    exact hU

/-- A lower endpoint overshoot after widening implies the corresponding
two-sided absolute-deviation miss. -/
theorem lowerOvershoot_subset_absMiss {lo : Ω → ℝ} {L wL : ℝ} :
    {ω | L < lo ω - wL} ⊆ {ω | wL ≤ |lo ω - L|} := by
  intro ω hω
  change L < lo ω - wL at hω
  have : wL < lo ω - L := by linarith
  exact (le_of_lt this).trans (le_abs_self _)

/-- An upper endpoint undershoot after widening implies the corresponding
two-sided absolute-deviation miss. -/
theorem upperUndershoot_subset_absMiss {hi : Ω → ℝ} {U wU : ℝ} :
    {ω | hi ω + wU < U} ⊆ {ω | wU ≤ |hi ω - U|} := by
  intro ω hω
  change hi ω + wU < U at hω
  have : wU < U - hi ω := by linarith
  refine (le_of_lt this).trans ?_
  rw [abs_sub_comm]
  exact le_abs_self _

/-- **Abstract honest confidence interval (set coverage).**  Let `lo`, `hi` be the
(random) lower/upper endpoint estimators of the population bounds `L`, `U`.
Suppose the two one-sided endpoint-failure events have controlled probability:

    μ{ L < lo − w_L } ≤ δ_L,    μ{ hi + w_U < U } ≤ δ_U.

Then the widened random interval `[lo − w_L, hi + w_U]` covers the entire
identified set `[L, U]` with probability at least `1 − δ_L − δ_U`.

This is a conservative partial-ID analogue of the Horowitz–Manski (2000)
confidence region, proved by a single union bound over the two
one-sided endpoint-failure events. It is stated
abstractly in the miss probabilities so that any concentration inequality
(Hoeffding, Bernstein, …) can be plugged in; see `Inference/IntervalCI.lean`. -/
theorem honest_ci_set_cover {lo hi : Ω → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    {L U wL wU δL δU : ℝ}
    (hML : μ.real {ω | L < lo ω - wL} ≤ δL)
    (hMU : μ.real {ω | hi ω + wU < U} ≤ δU) :
    1 - δL - δU ≤
      μ.real (RandomCoversIcc (fun ω => lo ω - wL) (fun ω => hi ω + wU) L U) := by
  set A : Ω → ℝ := fun ω => lo ω - wL with hA
  set B : Ω → ℝ := fun ω => hi ω + wU with hB
  set C : Set Ω := RandomCoversIcc A B L U with hC
  have hAmeas : Measurable A := hlo.sub_const _
  have hBmeas : Measurable B := hhi.add_const _
  have hCmeas : MeasurableSet C := by
    refine (measurableSet_le hAmeas measurable_const).inter
      (measurableSet_le measurable_const hBmeas)
  -- The complement is covered by the two one-sided endpoint-failure events.
  have hsub : Cᶜ ⊆ {ω | L < lo ω - wL} ∪ {ω | hi ω + wU < U} :=
    randomCoversIcc_compl_subset
  -- Union bound on the complement.
  have hcompl_le : μ.real Cᶜ ≤ δL + δU := by
    calc μ.real Cᶜ
        ≤ μ.real ({ω | L < lo ω - wL} ∪ {ω | hi ω + wU < U}) :=
          measureReal_mono hsub
      _ ≤ μ.real {ω | L < lo ω - wL} + μ.real {ω | hi ω + wU < U} :=
          measureReal_union_le _ _
      _ ≤ δL + δU := add_le_add hML hMU
  -- Convert to a lower bound on the coverage probability.
  have hcompleq : μ.real Cᶜ = 1 - μ.real C := by
    rw [measureReal_compl hCmeas, probReal_univ]
  linarith [hcompleq, hcompl_le]

/-- **Abstract honest confidence interval (parameter coverage).**  Under the same
endpoint-miss hypotheses as `honest_ci_set_cover`, if the true value `θ₀` lies in
the identified set `[L, U]`, then the widened random interval `[lo − w_L, hi + w_U]`
covers `θ₀` with probability at least `1 − δ_L − δ_U`.

Obtained by composing `honest_ci_set_cover` with
`randomCoversIcc_subset_randomCoversPoint`: covering the set is sufficient for
covering any point of it.  This is the conservative (Horowitz–Manski-style)
parameter confidence interval; the sharper Imbens–Manski interval, which replaces
the two-sided half-widths by one-sided critical values when `U − L > 0`, is in
`Inference/ImbensManski.lean`. -/
theorem honest_ci_point_cover {lo hi : Ω → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    {L U wL wU δL δU θ : ℝ} (hθ : θ ∈ Set.Icc L U)
    (hML : μ.real {ω | L < lo ω - wL} ≤ δL)
    (hMU : μ.real {ω | hi ω + wU < U} ≤ δU) :
    1 - δL - δU ≤
      μ.real (RandomCoversPoint (fun ω => lo ω - wL) (fun ω => hi ω + wU) θ) := by
  refine le_trans (honest_ci_set_cover hlo hhi hML hMU) ?_
  exact measureReal_mono
    (randomCoversIcc_subset_randomCoversPoint (fun ω => lo ω - wL) (fun ω => hi ω + wU) hθ)

end Causalean.PartialID.Inference
