/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Basic

/-! # Treatment Paths and Finite-Memory Histories

This file defines `TreatmentPath`, the assignment of an action to each
unit-time pair, and the finite-memory history constructors used by the panel
potential-outcomes layer. `History` uses an explicit boundary treatment for
lags before the observed panel starts, `HistoryDefault` uses the typeclass
default boundary value, and `BinaryHistory` specializes to binary treatment
with zero as the boundary value. -/

namespace Causalean
namespace Panel

/-- A treatment path: each unit `i : I` and time index `t : T` is assigned
an action in `A`, representing the realized assignment `D_{it}`. -/
def TreatmentPath (I T A : Type*) : Type _ := I → T → A

namespace TreatmentPath

variable {I A : Type*} {T₀ : ℕ}

/-- Finite-memory history of length `p+1` ending at time `t`, with the
boundary convention "out-of-range = baseline" for an explicit baseline
treatment value `a0 : A`.  Lag `k : Fin (p+1)` returns `D i ⟨t - k, _⟩`
when `k ≤ t.val`, and `a0` otherwise.  In the binary case
(`A := Fin 2`, baseline `0`) this is exactly
`H_{it}^{(p)} = (D_{it}, D_{i,t-1}, …, D_{i,t-p})` with the convention
`D_{is} = 0` for `s ∉ {1, …, T}`. -/
def History (a0 : A) (p : ℕ)
    (D : TreatmentPath I (Fin T₀) A) (i : I) (t : Fin T₀) :
    Fin (p + 1) → A := fun k =>
  if h : k.val ≤ t.val then
    D i ⟨t.val - k.val, by
      have : t.val - k.val ≤ t.val := Nat.sub_le _ _
      exact lt_of_le_of_lt this t.isLt⟩
  else
    a0

/-- Compatibility wrapper for code that deliberately wants the typeclass-provided
default value as the finite-history boundary treatment. -/
def HistoryDefault [Inhabited A] (p : ℕ)
    (D : TreatmentPath I (Fin T₀) A) (i : I) (t : Fin T₀) :
    Fin (p + 1) → A :=
  History (default : A) p D i t

/-- Binary finite-memory history with the conventional zero baseline. -/
def BinaryHistory (p : ℕ)
    (D : TreatmentPath I (Fin T₀) (Fin 2)) (i : I) (t : Fin T₀) :
    Fin (p + 1) → Fin 2 :=
  History 0 p D i t

/-- Lag `0` of the history is the contemporaneous treatment. -/
@[simp] lemma History_zero (a0 : A) (p : ℕ)
    (D : TreatmentPath I (Fin T₀) A) (i : I) (t : Fin T₀) :
    History a0 p D i t 0 = D i t := by
  unfold History
  simp

/-- Lag `0` of the default-boundary history is the contemporaneous treatment. -/
@[simp] lemma HistoryDefault_zero [Inhabited A] (p : ℕ)
    (D : TreatmentPath I (Fin T₀) A) (i : I) (t : Fin T₀) :
    HistoryDefault p D i t 0 = D i t := by
  simp [HistoryDefault]

/-- Lag `0` of the binary zero-baseline history is the contemporaneous treatment. -/
@[simp] lemma BinaryHistory_zero (p : ℕ)
    (D : TreatmentPath I (Fin T₀) (Fin 2)) (i : I) (t : Fin T₀) :
    BinaryHistory p D i t 0 = D i t := by
  simp [BinaryHistory]

end TreatmentPath

end Panel
end Causalean
