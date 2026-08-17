/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# The minimax value of a statistical decision problem

This module packages the object `inf over estimators of sup over the model class of the risk`
and its elementary order API. The estimator family and the model class enter as bare index
types, so a run instantiates them at whatever subtype carries its admissibility and
membership conditions.

Provided here: `worstCaseRisk` (the supremum of one estimator's risk over the class),
`minimaxValue` (the infimum of that over the estimators), the four facts every minimax
argument needs about them — nonnegativity, "any admissible estimator is an upper bound",
"a bound uniform over admissible estimators is a lower bound", "shrinking the class cannot
raise the value" — a two-point reduction stated directly against the minimax value, and
bridges to the equivalent set-comprehension spelling `sInf {r | ∃ e, ...}`.

Conventions for degenerate problems. Real suprema and infima are only conditionally
complete, so an empty index or an unbounded range evaluates to the junk value zero.
This module keeps that convention rather than hiding it, because zero is the conservative
value here: it makes an empty estimator family or an empty model class yield minimax value
zero, which can never certify a positive lower bound. (Contrast `coverageInfOrOne` in
`Causalean/Stat/Minimax/HonestConfidenceSet.lean`, where the guarantee runs the other way
and the safe vacuous value is one.) Accordingly the lemmas below carry explicit
`Nonempty` / `BddAbove` / `BddBelow` hypotheses, and each comes with a `_of_nonneg`
companion that discharges those hypotheses from nonnegativity of the risk, which is what
squared-error, absolute-error and regret losses supply for free.

Everything is stated over `ℝ`. A problem whose loss lives in `ℝ≥0∞` needs none of this
packaging: that order is a complete lattice, so `iInf_le`, `le_iInf`, `le_iSup` and
`iSup_le` apply with no side conditions at all.
-/

namespace Causalean.Stat

variable {E E' Θ Θ' : Sort*}

/-- The worst-case risk of a single estimator: the largest risk it incurs anywhere in the
model class. The estimator is held fixed and the supremum runs over the class.

If the class is empty, or if the estimator's risk is unbounded over the class, this is zero
by the real-supremum convention; `le_worstCaseRisk` therefore asks for an explicit bound. -/
noncomputable def worstCaseRisk (risk : E → Θ → ℝ) (e : E) : ℝ :=
  ⨆ θ : Θ, risk e θ

/-- The minimax risk of a decision problem: the smallest worst-case risk that any admissible
estimator achieves. Admissibility is expressed by the choice of the estimator index type, so
instantiating it at a subtype restricts the infimum to the estimators satisfying that
subtype's condition.

If there are no admissible estimators this is zero by the real-infimum convention. -/
noncomputable def minimaxValue (risk : E → Θ → ℝ) : ℝ :=
  ⨅ e : E, worstCaseRisk risk e

section Degenerate

/-- Over an empty model class the worst-case risk of every estimator is zero. -/
@[simp]
theorem worstCaseRisk_of_isEmpty_class [IsEmpty Θ] (risk : E → Θ → ℝ) (e : E) :
    worstCaseRisk risk e = 0 :=
  Real.iSup_of_isEmpty _

/-- When no estimator is admissible the minimax value is zero, so no positive lower bound on
the minimax value can hold vacuously. -/
@[simp]
theorem minimaxValue_of_isEmpty_estimators [IsEmpty E] (risk : E → Θ → ℝ) :
    minimaxValue risk = 0 :=
  Real.iInf_of_isEmpty _

/-- When the model class consists of a single law, the worst-case risk is just the risk at
that law. This covers decision problems that minimise a functional of the estimator alone,
with no adversarial choice of model. -/
theorem worstCaseRisk_of_unique [Unique Θ] (risk : E → Θ → ℝ) (e : E) :
    worstCaseRisk risk e = risk e default :=
  ciSup_unique

end Degenerate

section Nonneg

/-- A worst-case risk is nonnegative as soon as the risk is, with no boundedness or
nonemptiness caveat: an empty class or an unbounded risk both give the value zero. -/
theorem worstCaseRisk_nonneg {risk : E → Θ → ℝ} {e : E} (hr : ∀ θ, 0 ≤ risk e θ) :
    0 ≤ worstCaseRisk risk e :=
  Real.iSup_nonneg hr

/-- The minimax value of a nonnegative-risk problem is nonnegative, with no boundedness or
nonemptiness caveat. Squared-error, absolute-error and regret losses all qualify. -/
theorem minimaxValue_nonneg {risk : E → Θ → ℝ} (hr : ∀ e θ, 0 ≤ risk e θ) :
    0 ≤ minimaxValue risk :=
  Real.iInf_nonneg fun e => worstCaseRisk_nonneg (hr e)

/-- For a nonnegative risk the worst-case risks are bounded below by zero, which is the
side condition the infimum over estimators needs. -/
theorem bddBelow_range_worstCaseRisk {risk : E → Θ → ℝ} (hr : ∀ e θ, 0 ≤ risk e θ) :
    BddBelow (Set.range (worstCaseRisk risk)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨e, rfl⟩
  exact worstCaseRisk_nonneg (hr e)

end Nonneg

section Bounds

/-- The risk at any single model in the class is at most the estimator's worst-case risk,
provided that estimator's risk is bounded over the class. -/
theorem le_worstCaseRisk {risk : E → Θ → ℝ} {e : E}
    (hbdd : BddAbove (Set.range (risk e))) (θ : Θ) :
    risk e θ ≤ worstCaseRisk risk e :=
  le_ciSup hbdd θ

/-- A bound holding at every model in a nonempty class bounds the worst-case risk. -/
theorem worstCaseRisk_le [Nonempty Θ] {risk : E → Θ → ℝ} {e : E} {c : ℝ}
    (h : ∀ θ, risk e θ ≤ c) :
    worstCaseRisk risk e ≤ c :=
  ciSup_le h

/-- **Any admissible estimator is an upper bound.** Exhibiting one estimator and bounding
its worst-case risk bounds the minimax value, which is how achievability half of a minimax
rate is certified. The hypothesis rules out a worst-case risk that decreases without bound
across the estimator family. -/
theorem minimaxValue_le_worstCaseRisk {risk : E → Θ → ℝ}
    (hbdd : BddBelow (Set.range (worstCaseRisk risk))) (e : E) :
    minimaxValue risk ≤ worstCaseRisk risk e :=
  ciInf_le hbdd e

/-- For a nonnegative risk, any admissible estimator is an upper bound on the minimax value
with no further side condition, since zero already bounds the worst-case risks below. -/
theorem minimaxValue_le_worstCaseRisk_of_nonneg {risk : E → Θ → ℝ}
    (hr : ∀ e θ, 0 ≤ risk e θ) (e : E) :
    minimaxValue risk ≤ worstCaseRisk risk e :=
  minimaxValue_le_worstCaseRisk (bddBelow_range_worstCaseRisk hr) e

/-- **A bound uniform over admissible estimators is a lower bound.** If every admissible
estimator has worst-case risk at least `c`, the minimax value is at least `c`. This is the
converse half of a minimax rate; it needs at least one admissible estimator to exist,
since otherwise the minimax value is zero by convention. -/
theorem le_minimaxValue [Nonempty E] {risk : E → Θ → ℝ} {c : ℝ}
    (h : ∀ e, c ≤ worstCaseRisk risk e) :
    c ≤ minimaxValue risk :=
  le_ciInf h

/-- **Two-point reduction to the minimax value.** Fix two models `θ₀` and `θ₁` from the
parameter class. If [every estimator's risk is bounded above across the parameter
class](hyp:hbdd) and [for each estimator, the larger of its risks at the two fixed models
is at least `c`](hyp:htwo), then [the minimax value of the problem is at least `c`](goal).

This is the step that turns a Le Cam or divergence-based testing bound, which produces
exactly such a two-model statement, into a statement about the minimax value. Each
estimator's risk must be bounded over the class for its supremum to be meaningful. -/
theorem le_minimaxValue_of_two_point [Nonempty E] {risk : E → Θ → ℝ} {c : ℝ} (θ₀ θ₁ : Θ)
    (hbdd : ∀ e, BddAbove (Set.range (risk e)))
    (htwo : ∀ e, c ≤ max (risk e θ₀) (risk e θ₁)) :
    c ≤ minimaxValue risk :=
  le_minimaxValue fun e =>
    (htwo e).trans (max_le (le_worstCaseRisk (hbdd e) θ₀) (le_worstCaseRisk (hbdd e) θ₁))

end Bounds

section Restriction

/-- Comparing two model classes at a fixed estimator: if every model of the first class is
matched, through the map, by a model of the second class whose risk is at least as large,
the worst-case risk over the first class is at most that over the second. The second class
must bound the estimator's risk, and the first must be nonempty; see
`worstCaseRisk_mono_class_of_nonneg` for the version that drops the nonemptiness. -/
theorem worstCaseRisk_mono_class [Nonempty Θ] {risk : E → Θ → ℝ} {risk' : E → Θ' → ℝ}
    {e : E} (φ : Θ → Θ')
    (hbdd : BddAbove (Set.range (risk' e)))
    (hle : ∀ θ, risk e θ ≤ risk' e (φ θ)) :
    worstCaseRisk risk e ≤ worstCaseRisk risk' e :=
  worstCaseRisk_le fun θ => (hle θ).trans (le_worstCaseRisk hbdd (φ θ))

/-- Version of `worstCaseRisk_mono_class` for a nonnegative larger risk: no nonemptiness
assumption on the smaller class is needed, because an empty class contributes worst-case
risk zero, which the larger nonnegative worst-case risk already dominates. -/
theorem worstCaseRisk_mono_class_of_nonneg {risk : E → Θ → ℝ} {risk' : E → Θ' → ℝ}
    {e : E} (φ : Θ → Θ')
    (hbdd : BddAbove (Set.range (risk' e))) (hr' : ∀ θ', 0 ≤ risk' e θ')
    (hle : ∀ θ, risk e θ ≤ risk' e (φ θ)) :
    worstCaseRisk risk e ≤ worstCaseRisk risk' e := by
  cases isEmpty_or_nonempty Θ with
  | inl _ => simpa using worstCaseRisk_nonneg hr'
  | inr _ => exact worstCaseRisk_mono_class φ hbdd hle

/-- **Comparison of two minimax problems.** If every admissible estimator of the second
problem is matched by an estimator of the first whose worst-case risk is no larger, the
first minimax value is at most the second. Both restricting the model class and enlarging
the estimator family are instances; the boundedness hypothesis is on the first problem's
worst-case risks, and the second problem must have at least one estimator. -/
theorem minimaxValue_le_minimaxValue [Nonempty E'] {risk : E → Θ → ℝ} {risk' : E' → Θ' → ℝ}
    (hbdd : BddBelow (Set.range (worstCaseRisk risk)))
    (h : ∀ e' : E', ∃ e : E, worstCaseRisk risk e ≤ worstCaseRisk risk' e') :
    minimaxValue risk ≤ minimaxValue risk' := by
  refine le_minimaxValue fun e' => ?_
  obtain ⟨e, he⟩ := h e'
  exact (minimaxValue_le_worstCaseRisk hbdd e).trans he

/-- **Restricting the model class cannot raise the minimax value.** If each model of the
smaller class sits, through the map, inside the larger class with no larger risk, then the
minimax value over the smaller class is at most the minimax value over the larger one — the
same estimators face a weaker adversary. This is the standard step that transfers a
published converse proved on a convenient subclass to the full class. -/
theorem minimaxValue_mono_class [Nonempty E] [Nonempty Θ] {risk : E → Θ → ℝ}
    {risk' : E → Θ' → ℝ} (φ : Θ → Θ')
    (hbddBelow : BddBelow (Set.range (worstCaseRisk risk)))
    (hbdd : ∀ e, BddAbove (Set.range (risk' e)))
    (hle : ∀ e θ, risk e θ ≤ risk' e (φ θ)) :
    minimaxValue risk ≤ minimaxValue risk' :=
  minimaxValue_le_minimaxValue hbddBelow
    fun e => ⟨e, worstCaseRisk_mono_class φ (hbdd e) (hle e)⟩

/-- For a map `φ` embedding the parameter class of the first problem into that of the
second, if [the first problem's risk is nonnegative](hyp:hr), [the second problem's risk is
nonnegative](hyp:hr'), [each estimator's risk is bounded above across the second parameter
class](hyp:hbdd), and [the first risk at any model is dominated by the second risk at that
model's image under `φ`](hyp:hle), then [the minimax value of the first problem is at most
that of the second](goal).

Version of `minimaxValue_mono_class` for nonnegative risks. Nonnegativity supplies both
the lower bound on the smaller problem's worst-case risks and the empty-class case, so the
only remaining side condition is that each estimator's risk be bounded over the larger
class. Squared-error and absolute-error losses meet the nonnegativity hypotheses by
inspection. -/
theorem minimaxValue_mono_class_of_nonneg [Nonempty E] {risk : E → Θ → ℝ}
    {risk' : E → Θ' → ℝ} (φ : Θ → Θ')
    (hr : ∀ e θ, 0 ≤ risk e θ) (hr' : ∀ e θ', 0 ≤ risk' e θ')
    (hbdd : ∀ e, BddAbove (Set.range (risk' e)))
    (hle : ∀ e θ, risk e θ ≤ risk' e (φ θ)) :
    minimaxValue risk ≤ minimaxValue risk' :=
  minimaxValue_le_minimaxValue (bddBelow_range_worstCaseRisk hr)
    fun e => ⟨e, worstCaseRisk_mono_class_of_nonneg φ (hbdd e) (hr' e) (hle e)⟩

end Restriction

section SetSpelling

/-- The worst-case risk is the supremum of the set of risks the estimator attains across the
class. Rewriting handle for arguments phrased on the set of attained risks. -/
theorem worstCaseRisk_eq_sSup_range (risk : E → Θ → ℝ) (e : E) :
    worstCaseRisk risk e = sSup (Set.range (risk e)) :=
  rfl

/-- The minimax value is the infimum of the set of worst-case risks the admissible
estimators attain. Rewriting handle for arguments phrased on that set. -/
theorem minimaxValue_eq_sInf_range (risk : E → Θ → ℝ) :
    minimaxValue risk = sInf (Set.range (worstCaseRisk risk)) :=
  rfl

variable {A B : Type*}

/-- The minimax value over the estimators satisfying an admissibility condition, written as
the infimum of the set of worst-case risks the admissible estimators attain. This is the
bridge for developments that state admissibility by a predicate rather than by a subtype
while leaving the inner supremum as it stands. -/
theorem minimaxValue_subtype_eq_sInf_worstCaseRisk {Adm : A → Prop} (risk : A → Θ → ℝ) :
    minimaxValue (fun (e : Subtype Adm) => risk e.1)
      = sInf {r : ℝ | ∃ e, Adm e ∧ r = worstCaseRisk risk e} := by
  rw [minimaxValue_eq_sInf_range]
  congr 1
  ext r
  simp only [Set.mem_range, Set.mem_setOf_eq, Subtype.exists]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩

/-- The worst-case risk over a class carved out by a membership condition, written as the
supremum of the set of risks attained on the class. This is the bridge to the spelling that
states the class by a predicate rather than by a subtype. -/
theorem worstCaseRisk_subtype_eq_sSup_setOf {Cls : B → Prop} (risk : A → B → ℝ) (e : A) :
    worstCaseRisk (fun (a : A) (θ : Subtype Cls) => risk a θ.1) e
      = sSup {q : ℝ | ∃ θ, Cls θ ∧ q = risk e θ} := by
  rw [worstCaseRisk, iSup]
  congr 1
  ext q
  simp only [Set.mem_range, Set.mem_setOf_eq, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩

/-- The minimax value over an admissible-estimator condition and a model-class condition,
written with set comprehensions instead of subtypes: the infimum of the set of worst-case
risks attained by admissible estimators, each of which is the supremum of the set of risks
attained on the class. Runs that spell their minimax risk this way rewrite with this lemma
and then use the rest of this file. -/
theorem minimaxValue_subtype_eq_sInf_setOf (Adm : A → Prop) (Cls : B → Prop)
    (risk : A → B → ℝ) :
    minimaxValue (fun (e : Subtype Adm) (θ : Subtype Cls) => risk e.1 θ.1)
      = sInf {r : ℝ | ∃ e, Adm e ∧ r = sSup {q : ℝ | ∃ θ, Cls θ ∧ q = risk e θ}} := by
  rw [minimaxValue_subtype_eq_sInf_worstCaseRisk
    (risk := fun (a : A) (θ : Subtype Cls) => risk a θ.1)]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, worstCaseRisk_subtype_eq_sSup_setOf]

end SetSpelling

end Causalean.Stat
