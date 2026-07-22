/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.PolynomialRetractDimension
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.AffineSpaceDimension

/-!
# Compatibility reexports for polynomial retract dimension

The polynomial-map and retract proofs are implemented in neutral substrate;
this file retains the paper namespace and method-style API.
-/

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension (IsPolynomialMap)

namespace IsPolynomialMap

/-- Proves the stated mathematical property of comp. -/
lemma comp {ι κ τ : Type*}
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (τ → ℂ)}
    (hg : IsPolynomialMap g) (hf : IsPolynomialMap f) :
    IsPolynomialMap (g ∘ f) :=
  Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.IsPolynomialMap.comp hg hf

/-- Gives the stated evaluation formula for eval comp. -/
lemma eval_comp {ι κ : Type*}
    {f : (ι → ℂ) → (κ → ℂ)} (hf : IsPolynomialMap f)
    (Q : MvPolynomial κ ℂ) :
    ∃ P : MvPolynomial ι ℂ, ∀ x,
      MvPolynomial.eval x P = MvPolynomial.eval (f x) Q :=
  Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.IsPolynomialMap.eval_comp hf Q

end IsPolynomialMap

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (isPolynomialMap_id polynomial_preimage_closed polynomial_fixedPoints_closed
   polynomial_range_closed_of_retract polynomial_image_closed_of_retract
   irreducible_image_polynomial_retract polynomialRetract_range_dimension)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
