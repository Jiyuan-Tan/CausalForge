/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Potential outcomes under an exposure mapping

Each assignment `z ∈ Ω` induces a fixed *randomization potential outcome* `yr i z` for
unit `i`; these are fixed features of the finite population, not random.  Aronow & Samii's
**Condition 1 (properly specified exposure mapping)** says interference acts only through
the exposure: if `expo i z = expo i z'` then `yr i z = yr i z'`.  Equivalently, the
randomization potential outcome factors through the exposure, `yr i z = y i (expo i z)`
for exposure-indexed potential outcomes `y : ι → Δ → ℝ`.

We take that factored form as primitive: `Yobs y f θ i z = y i (expo f θ i z)` is unit
`i`'s observed outcome under assignment `z`.  **Condition 2 (consistency)** then holds as a
lemma: `Yobs i z = ∑_d 1(expo i = d) · y i d`.
-/

import Causalean.Experimentation.DesignBased.Exposure

/-! # Potential outcomes under exposure mappings

Exposure-indexed potential outcomes factor observed outcomes through a finite assignment's exposure.

`ProperlySpecified` states that randomization potential outcomes factor through the exposure
mapping, while `Yobs` evaluates the exposure-indexed potential outcome at the realized exposure.
The lemmas `Yobs_eq_sum`, `expoInd_mul_Yobs`, `expoInd_mul_Yobs_sq`, and
`expoInd₂_mul_Yobs` provide the consistency and on-event substitution identities used by
Horvitz-Thompson and variance calculations.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [DecidableEq Δ]

/-- A properly specified exposure mapping: the randomization potential outcome `yr`
factors through the exposure via exposure-indexed potential outcomes `y`. -/
def ProperlySpecified (y : ι → Δ → ℝ) (yr : ι → Ω → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) : Prop :=
  ∀ i z, yr i z = y i (expo f θ i z)

/-- Observed outcome of unit `i` under assignment `z`: `y i (expo i z)`. -/
def Yobs (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (z : Ω) : ℝ :=
  y i (expo f θ i z)

variable [Fintype Δ]

omit [Fintype Ω] in
/-- **Condition 2 (consistency).** The observed outcome equals the sum over exposures of
the exposure indicator times the exposure-indexed potential outcome. -/
lemma Yobs_eq_sum (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (z : Ω) :
    Yobs y f θ i z = ∑ d, expoInd f θ i d z * y i d := by
  unfold Yobs expoInd FiniteDesign.ind
  rw [Finset.sum_eq_single (expo f θ i z)
      (fun d _ hd => by rw [if_neg (fun h => hd h.symm), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp

omit [Fintype Ω] [Fintype Δ] in
/-- On the event `expo i = d`, the observed outcome agrees with the potential outcome
`y i d`; hence `1(expo i = d)·Yobs i = 1(expo i = d)·y i d`. -/
lemma expoInd_mul_Yobs (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) (z : Ω) :
    expoInd f θ i d z * Yobs y f θ i z = expoInd f θ i d z * y i d := by
  unfold expoInd FiniteDesign.ind Yobs
  by_cases h : expo f θ i z = d <;> simp [h]

omit [Fintype Ω] [Fintype Δ] in
/-- Squared on-event substitution: `1(expo i = d)·(Yobs i)² = 1(expo i = d)·(y i d)²`. -/
lemma expoInd_mul_Yobs_sq (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) (z : Ω) :
    expoInd f θ i d z * (Yobs y f θ i z) ^ 2 = expoInd f θ i d z * (y i d) ^ 2 := by
  unfold expoInd FiniteDesign.ind Yobs
  by_cases h : expo f θ i z = d <;> simp [h]

omit [Fintype Ω] [Fintype Δ] in
/-- Joint-event substitution for cross terms: the product of two exposure indicators lets the
observed outcome for unit `i` be replaced by its potential-outcome value. -/
lemma expoInd₂_mul_Yobs (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i j : ι) (di dj : Δ) (z : Ω) :
    expoInd f θ i di z * expoInd f θ j dj z * Yobs y f θ i z
      = expoInd f θ i di z * expoInd f θ j dj z * y i di := by
  unfold expoInd FiniteDesign.ind Yobs
  by_cases h : expo f θ i z = di <;> simp [h]

end DesignBased
end Experimentation
end Causalean
