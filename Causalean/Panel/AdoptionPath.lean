/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Staggered-adoption path helpers

Shared helpers for adoption paths encoded as `WithTop (Fin T)`, where `⊤`
represents the never-treated path.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.WithBot

/-! # Adoption Path Helpers

This file provides finite-period adoption-path predicates for staggered-treatment
designs, including eventual treatment, never treatment, and whether adoption has
occurred by a period. The never-treated path is represented as an infinite
adoption date, so absorbing treatment remains zero in every finite period for
such units.

These paper-agnostic helpers are shared by staggered-adoption modules:
Sun-Abraham path helpers wrap these declarations, and Goodman-Bacon uses the
same raw infinite-date encoding for proof stability. -/

namespace Causalean
namespace Panel
namespace AdoptionPath

/-- A finite adoption path, embedded in `WithTop (Fin T)`. -/
def finite {T : ℕ} (g : Fin T) : WithTop (Fin T) :=
  (g : WithTop (Fin T))

/-- Embedding a finite adoption period into the shared adoption-path type is
definitionally the ordinary finite-period inclusion. -/
@[simp] theorem finite_eq {T : ℕ} (g : Fin T) :
    finite g = (g : WithTop (Fin T)) := rfl

/-- Adoption-date predicate `A ≤ t`, i.e. adoption has occurred by period `t`. -/
def le {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop :=
  a ≤ (t : WithTop (Fin T))

/-- The treated-by-period predicate is exactly the order comparison with the
finite period viewed as an adoption date. -/
@[simp] theorem le_eq {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) :
    le a t = (a ≤ (t : WithTop (Fin T))) := rfl

/-- Adoption-date predicate `t < A`, i.e. the path is untreated at period `t`. -/
def lt {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop :=
  (t : WithTop (Fin T)) < a

/-- The untreated-before-adoption predicate is exactly the strict order
comparison with the finite period viewed as an adoption date. -/
@[simp] theorem lt_eq {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) :
    lt a t = ((t : WithTop (Fin T)) < a) := rfl

/-- The path is finite, i.e. eventually treated. -/
def isFinite {T : ℕ} (a : WithTop (Fin T)) : Prop :=
  a ≠ ⊤

/-- A path is eventually treated exactly when its adoption date is not infinite. -/
@[simp] theorem isFinite_eq {T : ℕ} (a : WithTop (Fin T)) :
    isFinite a = (a ≠ ⊤) := rfl

/-- The path is infinite, i.e. never treated. -/
def isInfinite {T : ℕ} (a : WithTop (Fin T)) : Prop :=
  a = ⊤

/-- A path is never treated exactly when its adoption date is infinite. -/
@[simp] theorem isInfinite_eq {T : ℕ} (a : WithTop (Fin T)) :
    isInfinite a = (a = ⊤) := rfl

/-- A path is never treated when its adoption date is infinite. -/
def isNeverTreated {T : ℕ} (h : WithTop (Fin T)) : Prop :=
  isInfinite h

/-- The Sun-Abraham-compatible never-treated name is the infinite adoption-date
predicate. -/
@[simp] theorem isNeverTreated_eq {T : ℕ} (h : WithTop (Fin T)) :
    isNeverTreated h = (h = ⊤) := rfl

/-- `h < ∞`, the path is eventually treated. -/
def isEventuallyTreated {T : ℕ} (h : WithTop (Fin T)) : Prop :=
  isFinite h

/-- The Sun-Abraham-compatible eventually-treated name is the finite
adoption-date predicate. -/
@[simp] theorem isEventuallyTreated_eq {T : ℕ} (h : WithTop (Fin T)) :
    isEventuallyTreated h = (h ≠ ⊤) := rfl

open Classical in
/-- Absorbing treatment path `1{h < ∞ and h ≤ t}`. Since `⊤ ≤ t` is false,
the never-treated path is untreated in every finite period. -/
noncomputable def absorbingTreatment {T : ℕ} (h : WithTop (Fin T)) (t : Fin T) : ℝ :=
  if le h t then 1 else 0

/-- The absorbing treatment path is one exactly when the adoption date is no
later than the finite period. -/
@[simp] theorem absorbingTreatment_eq {T : ℕ} (h : WithTop (Fin T)) (t : Fin T) :
    absorbingTreatment h t = if h ≤ (t : WithTop (Fin T)) then 1 else 0 := by
  unfold absorbingTreatment le
  by_cases hle : h ≤ (t : WithTop (Fin T)) <;> simp [hle]

/-- If `t < A`, then adoption has not occurred by `t`. -/
theorem not_le_of_lt {T : ℕ} {a : WithTop (Fin T)} {t : Fin T}
    (hlt : lt a t) : ¬ le a t := by
  intro hle
  unfold lt at hlt
  unfold le at hle
  rw [WithTop.lt_def] at hlt
  rw [WithTop.le_def] at hle
  rcases hle with htop | hle
  · exact WithTop.coe_ne_top htop
  rcases hlt with hlt_top | hlt_fin
  · rcases hlt_top with ⟨_, ha_top⟩
    rcases hle with ⟨c, _d, _hcd, ha, _ht⟩
    exact WithTop.top_ne_coe (ha_top.symm.trans ha)
  · rcases hlt_fin with ⟨c, d, hcd, ht_c, ha_d⟩
    rcases hle with ⟨c', d', hc'd', ha_c', ht_d'⟩
    have hd_eq : d = c' := WithTop.coe_injective (ha_d.symm.trans ha_c')
    have hc_eq : c = d' := WithTop.coe_injective (ht_c.symm.trans ht_d')
    subst d
    subst d'
    have hlt_nat : c.val < c'.val := (Fin.val_fin_lt).2 hcd
    have hle_nat : c'.val ≤ c.val := (Fin.val_fin_le).2 hc'd'
    omega

/-- Never-treated paths are untreated in every finite period. -/
theorem lt_of_isInfinite {T : ℕ} {a : WithTop (Fin T)} {t : Fin T}
    (ha : isInfinite a) : lt a t := by
  subst a
  exact (WithTop.coe_lt_top _ : (t : WithTop (Fin T)) < ⊤)

end AdoptionPath
end Panel
end Causalean
