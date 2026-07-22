/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.DesignCore
import Mathlib.Data.Fintype.BigOperators

/-!
# Sävje–Aronow–Hudgens (2021): EATE estimand and the Horvitz–Thompson estimator

The setup for "Average treatment effects in the presence of unknown interference"
(Sävje, Aronow & Hudgens, *Annals of Statistics* 49(2), 2021).  A finite sample of units `U`
is assigned a binary treatment vector `z : U → Bool` by a randomization design.  Each unit's
outcome `y i z` may depend on the *entire* assignment `z` — units interfere — but the form of
the interference is unknown.

This file fixes the primitives:

* the **interference indicator** `Interferes y ℓ i` (changing `ℓ`'s treatment changes `i`'s
  outcome under some assignment, plus the reflexive case `ℓ = i`), its symmetric closure
  `InterfDep y i j` (some `ℓ` interferes with both `i` and `j`), and the average interference
  dependence `dbar` (the paper's `d̄`, the basis for the "restricted interference" assumption);
* the **assignment-conditional unit-level effect** `tau y i z = y i (z with iᵗʰ coord 1) −
  y i (z with iᵗʰ coord 0)`, its average `ACATE` (assignment-conditional ATE), and the
  **expected average treatment effect** `EATE = E[ACATE(Z)]` (Definition: the design average of
  the assignment-conditional ATE);
* the **Horvitz–Thompson estimator** `htEst`.

The key structural fact proven here is `y_eq_of_agree_on_interferers`: a unit's outcome depends
only on the treatments of the units that interfere with it — the bridge that turns
"`InterfDep` fails" into "the two HT summands depend on disjoint coordinate blocks", which the
disjoint-block independence lemma then turns into a vanishing covariance.
-/

open scoped BigOperators Classical
open Finset

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-! ### Interference structure -/

/-- **Interference indicator.** Unit `ℓ` *interferes with* unit `i` if changing `ℓ`'s treatment
changes `i`'s outcome under some assignment, or if `ℓ = i` (a unit always interferes with itself).
`y i z` is unit `i`'s outcome under the full assignment `z`. -/
def Interferes (y : U → (U → Bool) → ℝ) (ℓ i : U) : Prop :=
  ℓ = i ∨ ∃ z : U → Bool, y i z ≠ y i (Function.update z ℓ (! z ℓ))

/-- **Interference dependence.** Units `i` and `j` are interference dependent if some unit `ℓ`
interferes with both — i.e. they may be affected by a common treatment. The paper's `d̄_{ij}`. -/
def InterfDep (y : U → (U → Bool) → ℝ) (i j : U) : Prop :=
  ∃ ℓ : U, Interferes y ℓ i ∧ Interferes y ℓ j

/-- The (unnormalized) count `∑ᵢ ∑ⱼ 1[InterfDep i j]` of interference-dependent ordered pairs. -/
noncomputable def dbarCount (y : U → (U → Bool) → ℝ) : ℝ :=
  ∑ i : U, ∑ j : U, if InterfDep y i j then (1 : ℝ) else 0

/-- **Average interference dependence** `d̄ = n⁻¹ ∑ᵢ ∑ⱼ 1[InterfDep i j]` — the paper's basic
measure of the amount of interference. For a nonempty population, `d̄ = 1` under no interference;
`d̄ = n` when every pair is interference dependent. "Restricted interference" is the assumption
`d̄ = o(n)`. -/
noncomputable def dbar (y : U → (U → Bool) → ℝ) : ℝ :=
  dbarCount y / (Fintype.card U : ℝ)

/-! ### Estimand: EATE -/

/-- **Assignment-conditional unit-level treatment effect.** `τ_i(z_{-i}) = y_i(1; z_{-i}) −
y_i(0; z_{-i})`, the effect of changing unit `i`'s own treatment with all others held at `z`.
Encoded on the full assignment via `Function.update`; it does not depend on `z i`. -/
def tau (y : U → (U → Bool) → ℝ) (i : U) (z : U → Bool) : ℝ :=
  y i (Function.update z i true) - y i (Function.update z i false)

/-- **Assignment-conditional average treatment effect** `ACATE(z) = n⁻¹ ∑ᵢ τ_i(z_{-i})`. -/
noncomputable def ACATE (y : U → (U → Bool) → ℝ) (z : U → Bool) : ℝ :=
  (∑ i : U, tau y i z) / (Fintype.card U : ℝ)

/-- **Expected average treatment effect** (Definition, Sävje–Aronow–Hudgens 2021):
`EATE = E[ACATE(Z)]`, the design average of the assignment-conditional ATE.  It generalizes the
conventional ATE — under no interference `ACATE(z)` is constant in `z`, so the marginalization is
inconsequential and `EATE = ATE`. -/
noncomputable def EATE (D : FiniteDesign (U → Bool)) (y : U → (U → Bool) → ℝ) : ℝ :=
  D.E (ACATE y)

/-! ### The Horvitz–Thompson estimator -/

/-- The `i`ᵗʰ Horvitz–Thompson summand `Z_i Y_i / p_i − (1 − Z_i) Y_i / (1 − p_i)`, with
`Z_i = 1[z i]` and `Y_i = y i z`. -/
noncomputable def htSummand (p : U → ℝ) (y : U → (U → Bool) → ℝ) (i : U) (z : U → Bool) : ℝ :=
  (if z i then (1 : ℝ) else 0) * y i z / p i
    - (if z i then (0 : ℝ) else 1) * y i z / (1 - p i)

/-- **Horvitz–Thompson estimator** `htEst = n⁻¹ ∑ᵢ [Z_i Y_i / p_i − (1 − Z_i) Y_i / (1 − p_i)]`,
with `p i` the marginal treatment probability of unit `i`. -/
noncomputable def htEst (p : U → ℝ) (y : U → (U → Bool) → ℝ) (z : U → Bool) : ℝ :=
  (∑ i : U, htSummand p y i z) / (Fintype.card U : ℝ)

/-! ### Outcome depends only on interferers -/

/-- Flipping the treatment of a unit `ℓ` that does **not** interfere with `i` (and `ℓ ≠ i`) never
changes `i`'s outcome: the negation of `Interferes` unfolds to this pointwise invariance. -/
lemma y_update_eq_of_not_interferes {y : U → (U → Bool) → ℝ} {ℓ i : U}
    (h : ¬ Interferes y ℓ i) (z : U → Bool) :
    y i z = y i (Function.update z ℓ (! z ℓ)) := by
  by_contra hne
  exact h (Or.inr ⟨z, hne⟩)

/-- **A unit's outcome depends only on the units that interfere with it.** If two assignments `z`
and `z'` agree on every unit that interferes with `i`, then `y i z = y i z'`.  This is the bridge
from the interference structure to disjoint-block independence: when `i` and `j` are not
interference dependent, their interferer sets are disjoint, so the two HT summands depend on
disjoint coordinate blocks. -/
theorem y_eq_of_agree_on_interferers (y : U → (U → Bool) → ℝ) (i : U) (z z' : U → Bool)
    (h : ∀ ℓ : U, Interferes y ℓ i → z ℓ = z' ℓ) :
    y i z = y i z' := by
  -- Auxiliary: changing `z` to `z'` over a finset `S` of differing, non-interfering coordinates.
  -- We induct on the finset of coordinates where `z` and `z'` differ; `z` is generalized so the
  -- induction hypothesis applies to the updated assignment `w`.
  suffices H : ∀ S : Finset U, ∀ z : U → Bool,
      (∀ ℓ : U, z ℓ ≠ z' ℓ → ℓ ∈ S) →
      (∀ ℓ ∈ S, z ℓ ≠ z' ℓ → ¬ Interferes y ℓ i) →
      y i z = y i z' by
    refine H Finset.univ z (fun ℓ _ => Finset.mem_univ ℓ) (fun ℓ _ hne => ?_)
    intro hint
    exact hne (h ℓ hint)
  intro S
  induction S using Finset.induction with
  | empty =>
    intro z hsub _
    have hzz' : z = z' := by
      funext ℓ
      by_contra hne
      exact (Finset.notMem_empty ℓ) (hsub ℓ hne)
    rw [hzz']
  | @insert a S ha ih =>
    intro z hsub hnint
    -- Define `w`: equal to `z'` at `a`, equal to `z` elsewhere.
    set w : U → Bool := Function.update z a (z' a) with hw
    -- Step 1: `y i z = y i w` (flipping the non-interferer coordinate `a`, if `z a ≠ z' a`).
    have step1 : y i z = y i w := by
      by_cases hza : z a = z' a
      · -- `a` not a differing coordinate; `w = z`.
        have : w = z := by
          rw [hw]; funext x
          by_cases hx : x = a
          · subst hx; rw [Function.update_self, hza]
          · rw [Function.update_of_ne hx]
        rw [this]
      · -- `a` differs, hence `¬ Interferes y a i`; `w = update z a (! z a)`.
        have haint : ¬ Interferes y a i := hnint a (Finset.mem_insert_self a S) hza
        have hflip : w = Function.update z a (! z a) := by
          rw [hw]; congr 1
          -- `z' a = ! z a` since they are distinct Bools.
          cases hzv : z a <;> cases hz'v : z' a <;>
            simp_all
        rw [hflip]
        exact y_update_eq_of_not_interferes haint z
    -- Step 2: `y i w = y i z'` by induction; `w` and `z'` differ only on `S`.
    have hsub' : ∀ ℓ : U, w ℓ ≠ z' ℓ → ℓ ∈ S := by
      intro ℓ hℓ
      have hℓa : ℓ ≠ a := by
        rintro rfl; rw [hw, Function.update_self] at hℓ; exact hℓ rfl
      have : w ℓ = z ℓ := by rw [hw, Function.update_of_ne hℓa]
      rw [this] at hℓ
      rcases Finset.mem_insert.mp (hsub ℓ hℓ) with h' | h'
      · exact absurd h' hℓa
      · exact h'
    have hnint' : ∀ ℓ ∈ S, w ℓ ≠ z' ℓ → ¬ Interferes y ℓ i := by
      intro ℓ hℓS hℓ
      have hℓa : ℓ ≠ a := fun hh => ha (hh ▸ hℓS)
      have hwz : w ℓ = z ℓ := by rw [hw, Function.update_of_ne hℓa]
      rw [hwz] at hℓ
      exact hnint ℓ (Finset.mem_insert_of_mem hℓS) hℓ
    rw [step1]
    exact ih w hsub' hnint'

end UnknownInterference
end Experimentation
end Causalean
