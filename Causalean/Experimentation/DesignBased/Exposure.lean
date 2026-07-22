/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exposure mappings and the generalized probability of exposure

Following Aronow & Samii (2017), an *exposure mapping* `f : Ω → Θ → Δ` sends an
assignment vector `z` and a unit's traits `θ i` (e.g. its row in a network adjacency
matrix) to the *exposure* that unit receives.  The exposure unit `i` receives under
assignment `z` is `expo f θ i z = f z (θ i)`.

The *generalized probability of exposure* `prop D f θ i d = Pr[expo i = d]` is the
design probability that unit `i` is subject to exposure `d`; it is known exactly from
the design.  We also record the joint exposure probabilities `propPairSame` (both `i`
and `j` in exposure `d`) and `propPairCross` (`i` in `d`, `j` in `d'`), which drive the
Horvitz–Thompson variance formulas downstream.
-/

import Causalean.Experimentation.DesignBased.DesignCore

/-! # Exposure mappings and generalized exposure probabilities

Exposure mappings turn assignments and unit traits into treatment conditions, and generalized
exposure probabilities are the design probabilities of those conditions.

The basic declarations are `expo`, the indicator `expoInd`, the marginal probability `prop`, and
the joint probabilities `propPairSame` and `propPairCross`. The covariance lemmas
`Cov_expoInd_same` and `Cov_expoInd_cross` rewrite indicator covariances into those probabilities,
while `expoInd_mul_self_of_ne` and `propPairCross_self_of_ne` record that one unit cannot occupy two
distinct exposures in the same assignment. For finite exposure spaces, `sum_prop_eq_one` shows that
each unit's exposure probabilities sum to one.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*}

/-- The exposure unit `i` receives under assignment `z`: `f z (θ i)`. -/
def expo (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (z : Ω) : Δ := f z (θ i)

variable [DecidableEq Δ]

/-- Indicator that unit `i` is in exposure condition `d` under assignment `z`. -/
def expoInd (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) : Ω → ℝ :=
  FiniteDesign.ind (fun z => expo f θ i z = d)

/-- Generalized probability of exposure: `π_i(d) = Pr[expo i = d]`. -/
def prop (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) : ℝ :=
  D.Pr (fun z => expo f θ i z = d)

/-- Joint exposure probability `π_{ij}(d) = E[1(expo i = d)·1(expo j = d)]`. -/
def propPairSame (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i j : ι) (d : Δ) : ℝ :=
  D.E (fun z => expoInd f θ i d z * expoInd f θ j d z)

/-- Cross joint exposure probability `π_{ij}(d,d') = E[1(expo i = d)·1(expo j = d')]`. -/
def propPairCross (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i j : ι) (d d' : Δ) : ℝ :=
  D.E (fun z => expoInd f θ i d z * expoInd f θ j d' z)

/-- The generalized exposure probability is definitionally the expectation of the exposure
indicator. -/
@[simp] lemma prop_eq_E_expoInd (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) :
    prop D f θ i d = D.E (expoInd f θ i d) := rfl

/-- The generalized probability of exposure is the expectation of the exposure indicator. -/
@[simp] lemma E_expoInd (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) :
    D.E (expoInd f θ i d) = prop D f θ i d := rfl

/-- Covariance of two same-exposure indicators: `π_{ij}(d) − π_i(d)π_j(d)`. -/
lemma Cov_expoInd_same (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i j : ι) (d : Δ) :
    D.Cov (expoInd f θ i d) (expoInd f θ j d)
      = propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d := by
  unfold propPairSame
  rw [FiniteDesign.Cov_eq, E_expoInd, E_expoInd]

/-- Covariance of two cross-exposure indicators: `π_{ij}(d,d') − π_i(d)π_j(d')`. -/
lemma Cov_expoInd_cross (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i j : ι) (d d' : Δ) :
    D.Cov (expoInd f θ i d) (expoInd f θ j d')
      = propPairCross D f θ i j d d' - prop D f θ i d * prop D f θ j d' := by
  unfold propPairCross
  rw [FiniteDesign.Cov_eq, E_expoInd, E_expoInd]

omit [Fintype Ω] in
/-- A unit cannot be in two distinct exposures at once: the indicators are pointwise
disjoint. -/
lemma expoInd_mul_self_of_ne (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) {d d' : Δ} (hne : d ≠ d')
    (z : Ω) : expoInd f θ i d z * expoInd f θ i d' z = 0 := by
  unfold expoInd FiniteDesign.ind
  by_cases h : expo f θ i z = d
  · simp [h, hne]
  · simp [h]

/-- The self cross-exposure joint probability vanishes for distinct exposures. -/
lemma propPairCross_self_of_ne (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι)
    {d d' : Δ} (hne : d ≠ d') : propPairCross D f θ i i d d' = 0 := by
  unfold propPairCross
  rw [show (fun z => expoInd f θ i d z * expoInd f θ i d' z) = (fun _ => (0 : ℝ)) from
        funext (fun z => expoInd_mul_self_of_ne f θ i hne z)]
  exact D.E_const 0

variable [Fintype Δ]

/-- For each unit, the generalized probabilities of exposure sum to one across exposures. -/
lemma sum_prop_eq_one (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) :
    ∑ d, prop D f θ i d = 1 := by
  simp only [prop, FiniteDesign.Pr, FiniteDesign.E, FiniteDesign.ind]
  rw [Finset.sum_comm]
  have : ∀ z, ∑ d, D.p z * (if expo f θ i z = d then (1:ℝ) else 0) = D.p z := by
    intro z
    rw [← Finset.mul_sum]
    simp
  rw [Finset.sum_congr rfl (fun z _ => this z), D.p_sum]

end DesignBased
end Experimentation
end Causalean
