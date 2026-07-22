/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.LinearAlgebra.ConfluentVandermonde

/-!
# Compatibility reexports for confluent Vandermonde certificates

The reusable Hermite-evaluation matrix theory lives in Causalean. This module
preserves the paper-facing declaration names for downstream imports.
-/

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.LinearAlgebra
  (doubledExponent doubledExponent_injective doubledExponent_lt
   doubledCoefficientPolynomial coeff_doubledCoefficientPolynomial
   doubledCoefficientPolynomial_eq_zero_iff
   natDegree_doubledCoefficientPolynomial_lt confluentVandermonde
   doubledCoefficientPolynomial_eq_zero_of_eval_derivative
   det_confluentVandermonde_ne_zero pinnedExponent pinnedSucc
   pinnedSucc_injective pinnedSucc_ne_zero pinnedExponent_injective
   pinnedExponent_lt pinnedCoefficientPolynomial
   coeff_pinnedCoefficientPolynomial pinnedCoefficientPolynomial_eq_zero_iff
   natDegree_pinnedCoefficientPolynomial_lt pinnedConfluentVandermonde
   pinnedCoefficientPolynomial_eq_zero_of_eval_derivative
   det_pinnedConfluentVandermonde_ne_zero)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
