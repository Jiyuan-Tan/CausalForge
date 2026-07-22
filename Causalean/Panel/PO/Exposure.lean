/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exposure mappings

This file formalizes the exposure-mapping object used by the panel
potential-outcomes layer: a known function `E_r = e_r(D)` of realized
treatment paths, taking values in a cell-indexed exposure set `E_r`, together
with a baseline exposure `e_r^0`.

The exposure set `E_r` is allowed to depend on the cell `r : I × T`,
hence the dependent type signature.

-/

import Causalean.Panel.PO.TreatmentPath

/-! # Exposure Mappings

This file defines `Exposure`, a cell-specific map from a realized
`TreatmentPath` to a cell-dependent exposure type, and `BaselineExposure`, a
distinguished baseline exposure for each cell. These objects are the
potential-outcome interface between treatment histories and cell-level
responses. -/

namespace Causalean
namespace Panel

/-- An exposure mapping: a known function from realized treatment paths
to a cell-dependent exposure set `E r`. -/
def Exposure (I T A : Type*) (E : I × T → Type*) : Type _ :=
  (r : I × T) → TreatmentPath I T A → E r

/-- A baseline exposure: a distinguished element `e_r^0 ∈ E r` for every
cell `r`.  In the binary finite-memory case this is `(0, …, 0)`. -/
def BaselineExposure {I T : Type*} (E : I × T → Type*) : Type _ :=
  (r : I × T) → E r

/-! ### Comment on the binary finite-memory builder

A natural builder
`binaryHistoryExposure (p : ℕ) :
    Exposure I (Fin T₀) (Fin 2) (fun _ => Fin (p+1) → Fin 2)`
would just delegate to `TreatmentPath.BinaryHistory p D i t` (equivalently,
`TreatmentPath.History 0 p D i t`).  We do not ship it as a
named definition because the dependent-type signature
`E : I × T → Type*` is awkward to instantiate at a constant family —
downstream files can build the appropriate `Exposure` inline.  See
`Causalean.Panel.TreatmentPath.History` for the underlying primitive. -/

end Panel
end Causalean
