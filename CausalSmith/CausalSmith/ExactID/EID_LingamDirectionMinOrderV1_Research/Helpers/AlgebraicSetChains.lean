/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.Irreducibility

/-!
# Compatibility reexports for affine algebraic-set chains

The reusable implementation now lives under
`Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension`.  These abbreviations
and reexports preserve the original paper namespace for downstream imports.
-/

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (affineZariskiClosure IsIrreducibleAffineClosed
   affineZariskiClosure_extensive affineZariskiClosure_mono
   affineZariskiClosure_idem affineZariskiClosure_eq_zeroLocus
   affineZariskiClosure_inter affineZariskiClosure_zero_of_polynomial
   vanishingIdeal_ne_top_of_nonempty nonempty_zeroLocus_of_prime
   irreducibleAffineClosed_iff_isPrime irreducible_zeroLocus_of_prime
   vanishingIdeal_strict_anti zeroLocus_strict_anti)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
