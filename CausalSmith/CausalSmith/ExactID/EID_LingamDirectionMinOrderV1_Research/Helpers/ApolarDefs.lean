/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Divided-power binary forms, apolar contraction, and the support annihilator

The three apolar primitives shared by the whole `EID_LingamDirectionMinOrderV1`
substrate: the divided-power binary form `f_r` of an order-`r` cumulant block, the
constant-coefficient differential operator `q(∂)` acting on a binary form, and the
squarefree degree-`n` support annihilator `Q_D = ∏_{ℓ ∈ D} ℓ^⊥` whose roots are the
finite loading slopes.  They sit at the base of the import DAG so that both the
apolar helper lemmas and the headline theorem in `TApolar.lean` can use them.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.Varieties
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-! ### Divided-power binary forms, apolar contraction, and the support annihilator

These realize the divided-power blocks `f_r`, the constant-coefficient differential
operator `q(∂)`, and the squarefree degree-`n` support annihilator
`Q_D = ∏_{ℓ ∈ D} ℓ^⊥` used in the common-contraction-kernel identity `ker = ⟨Q_D⟩`. -/

/-- Divided-power binary form of the order-`r` cumulant block:
`f_r(x, y) = Σ_{a=0}^r C(r,a) t_{r,a} x^{r-a} y^a` (with `x = X 0`, `y = X 1`). -/
noncomputable def dividedPowerBlock (t : CumVec ℂ) (r : ℕ) : MvPolynomial (Fin 2) ℂ :=
  ∑ a ∈ Finset.range (r + 1),
    MvPolynomial.C ((Nat.choose r a : ℂ) * t r a)
      * MvPolynomial.X 0 ^ (r - a) * MvPolynomial.X 1 ^ a

/-- Apply the constant-coefficient differential operator `q(∂)` (with
`∂ = (∂_x, ∂_y)`) to a binary form `f`: `q(∂) f = Σ_d (coeff_d q) ∂_x^{d 0} ∂_y^{d 1} f`. -/
noncomputable def diffApply (q f : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ d ∈ q.support,
    MvPolynomial.coeff d q •
      ((fun g => (MvPolynomial.pderiv (0 : Fin 2)) g)^[d 0]
        ((fun g => (MvPolynomial.pderiv (1 : Fin 2)) g)^[d 1] f))

/-- Squarefree degree-`n` **support annihilator** `Q_D = ∏_{j} ℓ_j^⊥`, the product
over all `n = m + 2` projective loading directions of the linear form perpendicular
to `u_j = (u_{j1}, u_{j2})`, namely `u_{j2} · X 0 - u_{j1} · X 1`. -/
noncomputable def supportAnnihilator {m : ℕ} (dirs : Fin (m + 2) → ℂ × ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  ∏ j : Fin (m + 2),
    (MvPolynomial.C (dirs j).2 * MvPolynomial.X 0 - MvPolynomial.C (dirs j).1 * MvPolynomial.X 1)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
