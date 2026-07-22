/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Horvitz–Thompson estimators under interference

The collection of units observed in exposure `d` is an unequal-probability,
without-replacement sample from the population, with known sampling probabilities
`prop D f θ i d`. The current estimator is the algebraic totalized
Horvitz-Thompson form: when an exposure probability is zero, Lean's division
sets that inverse-probability term to zero. Under positive exposure
probabilities it is the usual inverse-probability-weighted total estimator

    htTotal d z = ∑ i, 1(expo i z = d) · Yobs i z / prop i d.

Dividing by `N` gives the mean estimator `htMean`, and differencing two exposures gives the
average-effect estimator `htEffect dk dl`, which targets `τ(dk,dl) = μ(dk) − μ(dl)`.
-/

import Causalean.Experimentation.DesignBased.PotentialOutcome

/-! # Horvitz-Thompson estimators

Horvitz-Thompson estimators use inverse generalized exposure probabilities to estimate
finite-population exposure totals, means, and contrasts.

The main estimator is `htTotal`, the totalized inverse-probability-weighted estimator for exposure
`d`. Dividing by the number of units gives `htMean`, and differencing two exposure means gives
`htEffect`. The target functionals are `muTrue` and `tauTrue`. The lemma `htTotal_eq` rewrites the
estimator using the exposure-specific potential outcome `y i d`, a form used by the unbiasedness
and variance proofs.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [Fintype ι] [DecidableEq Δ]

/-- Totalized Horvitz–Thompson estimator of the total potential outcome under exposure `d`. -/
noncomputable def htTotal (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (z : Ω) : ℝ :=
  ∑ i, expoInd f θ i d z * Yobs y f θ i z / prop D f θ i d

/-- Population mean potential outcome under exposure `d`: `μ(d) = (1/N)∑ᵢ y i d`. -/
noncomputable def muTrue (y : ι → Δ → ℝ) (d : Δ) : ℝ :=
  (∑ i, y i d) / (Fintype.card ι : ℝ)

/-- Average causal effect of exposure `dk` versus `dl`: `τ = μ(dk) − μ(dl)`. -/
noncomputable def tauTrue (y : ι → Δ → ℝ) (dk dl : Δ) : ℝ :=
  muTrue y dk - muTrue y dl

/-- Horvitz–Thompson estimator of the mean potential outcome under exposure `d`. -/
noncomputable def htMean (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (z : Ω) : ℝ :=
  htTotal D y f θ d z / (Fintype.card ι : ℝ)

/-- Horvitz–Thompson estimator of the average causal effect of `dk` versus `dl`. -/
noncomputable def htEffect (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (z : Ω) : ℝ :=
  htMean D y f θ dk z - htMean D y f θ dl z

/-- The HT total written with the potential outcome `y i d` in place of the observed
outcome, valid termwise because the exposure indicator forces `Yobs i = y i d`. -/
lemma htTotal_eq (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (z : Ω) :
    htTotal D y f θ d z = ∑ i, expoInd f θ i d z * y i d / prop D f θ i d := by
  unfold htTotal
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [expoInd_mul_Yobs]

end DesignBased
end Experimentation
end Causalean
