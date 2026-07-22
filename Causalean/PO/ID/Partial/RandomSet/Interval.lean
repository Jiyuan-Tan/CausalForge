/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Interval random sets and their selection (Aumann) expectation

Tier-0 random-set substrate for partial identification.  The data of an interval
random set is a pair of measurable endpoint functions `L, U : Ω → ℝ` with
`L ω ≤ U ω`, viewed as the set-valued map `ω ↦ [L ω, U ω]`.

The two facts a partial-identification sharpness proof needs are:

* **Measurable selection** — every measurable selection of `[L, U]` is
  `L + t·(U − L)` for a measurable `t : Ω → [0,1]`, and conversely.  For
  interval-valued maps this is elementary (the divide-by-width construction); no
  Kuratowski–Ryll-Nardzewski selection theorem is required.
* **Selection (Aumann) expectation** — the set of integrals of integrable
  selections equals `[∫L, ∫U]`.  The `⊇` direction uses a *constant* `t`, so no
  atomlessness / Lyapunov convexity is needed.

Endpoints are reported through `sInf`/`sSup` (matching the
`SandwichInterval` convention) so the eventual support-function generalisation is
a drop-in rather than a rewrite.

## Main results

* `isSelection_iff_exists_param` — selection ↔ `L + t·(U−L)` parametrisation.
* `selectionExpectation_eq_Icc` — selection expectation `= [∫L, ∫U]`.
* `sInf_selectionExpectation` / `sSup_selectionExpectation` — sharp endpoints as
  inf/sup over selections.

Out of scope (flagged for later): the conditional selection expectation
`E[X∣𝒢] = [E[L∣𝒢], E[U∣𝒢]]`, and the support-function / Artstein / CLR-inference
layers.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Interval Random Sets and Aumann Expectations

This file treats an interval-valued random set as measurable lower and upper
endpoint functions and characterizes its measurable selections. It proves that
the selection, or Aumann, expectation of the interval random set is the interval
whose endpoints are the expectations of the lower and upper endpoint functions.

Main declarations:
* `randomInterval` and `IsSelection` encode interval-valued random sets and
  their measurable selections.
* `isSelection_iff_exists_param` parametrizes every selection as
  `L + t * (U - L)` with measurable `t : Ω -> [0,1]`.
* `selectionExpectation_eq_Icc` identifies the Aumann expectation with
  `[∫ L, ∫ U]`.
* `sInf_selectionExpectation` and `sSup_selectionExpectation` recover the sharp
  lower and upper endpoints from the set of selection integrals.
-/

open MeasureTheory

namespace Causalean.PartialID.RandomSet

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L U : Ω → ℝ}

/-- The interval-valued random closed set `ω ↦ [L ω, U ω]`. -/
def randomInterval (L U : Ω → ℝ) : Ω → Set ℝ := fun ω => Set.Icc (L ω) (U ω)

/-- `f` is a measurable everywhere-selection of the interval random set `[L, U]`:
it is measurable and `L ω ≤ f ω ≤ U ω` for every `ω`. -/
def IsSelection (L U f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∀ ω, f ω ∈ Set.Icc (L ω) (U ω)

/-- The lower endpoint is always a selection, so the random set has a measurable
selection. -/
theorem isSelection_left (hL : Measurable L) (hLU : ∀ ω, L ω ≤ U ω) :
    IsSelection L U L :=
  ⟨hL, fun ω => ⟨le_rfl, hLU ω⟩⟩

/-- **Measurable selection of an interval random set.**  A function `f` is a
selection of `[L, U]` iff `f = L + t·(U − L)` for some measurable
`t : Ω → [0,1]`.  Elementary — no Kuratowski–Ryll-Nardzewski. -/
theorem isSelection_iff_exists_param (hL : Measurable L) (hU : Measurable U)
    (hLU : ∀ ω, L ω ≤ U ω) (f : Ω → ℝ) :
    IsSelection L U f ↔
      ∃ t : Ω → ℝ, Measurable t ∧ (∀ ω, t ω ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ ω, f ω = L ω + t ω * (U ω - L ω) := by
  constructor
  · rintro ⟨hf, hmem⟩
    refine ⟨fun ω => (f ω - L ω) * (U ω - L ω)⁻¹,
      (hf.sub hL).mul (hU.sub hL).inv, ?_, ?_⟩
    · intro ω
      simp only [Set.mem_Icc, ← div_eq_mul_inv]
      obtain ⟨hlf, hfu⟩ := hmem ω
      rcases (hLU ω).lt_or_eq with hlt | heq
      · have hw : (0 : ℝ) < U ω - L ω := by linarith
        refine ⟨div_nonneg (by linarith) (le_of_lt hw), ?_⟩
        rw [div_le_one hw]; linarith
      · have hw : U ω - L ω = 0 := by rw [heq]; ring
        rw [hw, div_zero]
        exact ⟨le_rfl, zero_le_one⟩
    · intro ω
      obtain ⟨hlf, hfu⟩ := hmem ω
      rcases (hLU ω).lt_or_eq with hlt | heq
      · have hw : (U ω - L ω) ≠ 0 := by
          have : (0 : ℝ) < U ω - L ω := by linarith
          exact ne_of_gt this
        field_simp
        ring
      · have hwL : L ω = U ω := heq
        have : f ω = L ω := le_antisymm (by rw [hwL]; exact hfu) hlf
        rw [this, ← heq]; ring
  · rintro ⟨t, ht, htmem, hfeq⟩
    have hfm : f = fun ω => L ω + t ω * (U ω - L ω) := funext hfeq
    refine ⟨by rw [hfm]; exact hL.add (ht.mul (hU.sub hL)), ?_⟩
    intro ω
    obtain ⟨ht0, ht1⟩ := htmem ω
    rw [hfeq ω]
    constructor
    · nlinarith [hLU ω]
    · nlinarith [hLU ω]

/-- The selection (Aumann) expectation of the interval random set `[L, U]`: the
set of integrals of integrable measurable selections. -/
def selectionExpectation (L U : Ω → ℝ) (μ : Measure Ω) : Set ℝ :=
  {r | ∃ f, IsSelection L U f ∧ Integrable f μ ∧ ∫ ω, f ω ∂μ = r}

/-- Monotonicity of the endpoint integrals (used to order the reported bounds). -/
theorem integral_le_integral_of_le (hLint : Integrable L μ) (hUint : Integrable U μ)
    (hLU : ∀ ω, L ω ≤ U ω) : (∫ ω, L ω ∂μ) ≤ ∫ ω, U ω ∂μ :=
  integral_mono_ae hLint hUint (ae_of_all _ hLU)

/-- **Selection expectation `= [∫L, ∫U]`.**  The `⊆` direction is integral
monotonicity; the `⊇` direction realises every intermediate value with a
*constant* `t ∈ [0,1]`, so no atomlessness is needed. -/
theorem selectionExpectation_eq_Icc (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    selectionExpectation L U μ = Set.Icc (∫ ω, L ω ∂μ) (∫ ω, U ω ∂μ) := by
  ext r
  simp only [selectionExpectation, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨f, ⟨hfmeas, hfmem⟩, hfint, hfr⟩
    have hLf : (∫ ω, L ω ∂μ) ≤ ∫ ω, f ω ∂μ :=
      integral_mono_ae hLint hfint (ae_of_all _ (fun ω => (hfmem ω).1))
    have hfU : (∫ ω, f ω ∂μ) ≤ ∫ ω, U ω ∂μ :=
      integral_mono_ae hfint hUint (ae_of_all _ (fun ω => (hfmem ω).2))
    rw [hfr] at hLf hfU
    exact ⟨hLf, hfU⟩
  · rintro ⟨hLr, hrU⟩
    set a := ∫ ω, L ω ∂μ with ha
    set b := ∫ ω, U ω ∂μ with hb
    rcases (integral_le_integral_of_le hLint hUint hLU).lt_or_eq with hlt | heq
    · set c := (r - a) / (b - a) with hc
      have hba : (0 : ℝ) < b - a := by linarith
      have hc0 : 0 ≤ c := div_nonneg (by linarith) (le_of_lt hba)
      have hc1 : c ≤ 1 := by rw [hc, div_le_one hba]; linarith
      refine ⟨fun ω => L ω + c * (U ω - L ω),
        ⟨hL.add (measurable_const.mul (hU.sub hL)), fun ω => ?_⟩,
        hLint.add ((hUint.sub hLint).const_mul c), ?_⟩
      · refine ⟨?_, ?_⟩
        · nlinarith [hLU ω]
        · nlinarith [hLU ω]
      · beta_reduce
        rw [integral_add (f := L) (g := fun ω => c * (U ω - L ω)) hLint
            ((hUint.sub hLint).const_mul c),
          integral_const_mul, integral_sub hUint hLint, ← ha, ← hb, hc]
        field_simp
        ring
    · refine ⟨L, isSelection_left hL hLU, hLint, ?_⟩
      rw [← ha]
      linarith

/-- Sharp lower endpoint as the infimum over selections: `sInf = ∫L`. -/
theorem sInf_selectionExpectation (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    sInf (selectionExpectation L U μ) = ∫ ω, L ω ∂μ := by
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU]
  exact csInf_Icc (integral_le_integral_of_le hLint hUint hLU)

/-- Sharp upper endpoint as the supremum over selections: `sSup = ∫U`. -/
theorem sSup_selectionExpectation (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    sSup (selectionExpectation L U μ) = ∫ ω, U ω ∂μ := by
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU]
  exact csSup_Icc (integral_le_integral_of_le hLint hUint hLU)

end Causalean.PartialID.RandomSet
