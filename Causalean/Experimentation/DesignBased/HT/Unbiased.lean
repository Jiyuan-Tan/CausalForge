/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Unbiasedness of the Horvitz–Thompson estimators

The expectation half of Aronow & Samii (2017) Lemma 4.1 and Proposition 4.4: under
positive generalized probabilities of exposure, the Horvitz–Thompson total, mean, and
effect estimators are exactly unbiased for the population total, mean, and average
causal effect.  These are pure linearity-of-expectation arguments: the inverse-probability
weight cancels the exposure probability `E[1(expo i = d)] = π_i(d)`.
-/

import Causalean.Experimentation.DesignBased.HT.Estimator

/-! # Horvitz-Thompson unbiasedness

Positive generalized exposure probabilities make the Horvitz-Thompson estimators exactly unbiased
under a finite randomization design.

The theorem `E_htTotal` proves the total estimator has expectation `∑ᵢ y i d`, because each
inverse-probability weight cancels `E[1(expo i = d)]`. The theorem `E_htMean` scales this to the
population mean `muTrue`, and `E_htEffect` proves unbiasedness of the exposure contrast estimator
`htEffect` for `tauTrue`.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [Fintype ι] [DecidableEq Δ]

/-- **Lemma 4.1 (expectation).** When every unit has nonzero probability of exposure `d`,
the Horvitz–Thompson total estimator is unbiased for the population total `∑ᵢ y i d`. -/
theorem E_htTotal (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (hpos : ∀ i, prop D f θ i d ≠ 0) :
    D.E (htTotal D y f θ d) = ∑ i, y i d := by
  have hfun : htTotal D y f θ d
      = (fun z => ∑ i, (y i d / prop D f θ i d) * expoInd f θ i d z) := by
    funext z
    rw [htTotal_eq]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hfun, FiniteDesign.E_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [FiniteDesign.E_const_mul, E_expoInd, div_mul_cancel₀ _ (hpos i)]

/-- When every unit has nonzero probability of exposure `d`, the Horvitz–Thompson mean
estimator is unbiased for `μ(d)`. -/
theorem E_htMean (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (hpos : ∀ i, prop D f θ i d ≠ 0) :
    D.E (htMean D y f θ d) = muTrue y d := by
  have hmean : htMean D y f θ d
      = (fun z => ((Fintype.card ι : ℝ)⁻¹) * htTotal D y f θ d z) := by
    funext z; rw [htMean, div_eq_inv_mul]
  rw [hmean, FiniteDesign.E_const_mul, E_htTotal D y f θ d hpos, muTrue, div_eq_inv_mul]

/-- **Proposition 4.4 (expectation).** When every unit has nonzero probability of each
contrast exposure, the Horvitz–Thompson effect estimator is unbiased for the average causal
effect `τ(dk,dl)`. -/
theorem E_htEffect (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hk : ∀ i, prop D f θ i dk ≠ 0) (hl : ∀ i, prop D f θ i dl ≠ 0) :
    D.E (htEffect D y f θ dk dl) = tauTrue y dk dl := by
  have hsub : htEffect D y f θ dk dl
      = (fun z => htMean D y f θ dk z - htMean D y f θ dl z) := by
    funext z; rw [htEffect]
  rw [hsub, FiniteDesign.E_sub, E_htMean D y f θ dk hk, E_htMean D y f θ dl hl, tauTrue]

end DesignBased
end Experimentation
end Causalean
