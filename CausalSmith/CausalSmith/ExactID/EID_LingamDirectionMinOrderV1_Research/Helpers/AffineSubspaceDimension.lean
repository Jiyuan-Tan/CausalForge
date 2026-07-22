/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.AffineSubspaceDimension
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.PolynomialRetractDimension

/-!
# Compatibility reexports for affine-subspace dimension

The general affine-linear proofs now live in neutral substrate.  This import
preserves every original paper-facing name.
-/

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (linearMap_isPolynomial affineLinearMap_isPolynomial
   affineSubspace_hasAffineZariskiDimension)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
