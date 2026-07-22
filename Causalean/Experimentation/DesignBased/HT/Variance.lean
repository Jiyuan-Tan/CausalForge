/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Randomization variance of the Horvitz–Thompson estimators

The variance half of Aronow & Samii (2017) Lemma 4.1 (`eq:total_variance`) and the
covariance of Proposition 4.4 (`eq:totals_covariance`).  The HT total is a finite linear
combination of exposure indicators, `htTotal d = ∑ᵢ (y i d / π_i d)·1(expo i = d)`, so its
variance is the double sum of indicator covariances (`Var_linear_comb` / `Cov_linear_comb`).
Splitting the diagonal recovers the paper's `π_i(1−π_i)` and `π_{ij}−π_iπ_j` form; the
diagonal of the cross-exposure covariance produces the famously unidentified `−∑ᵢ y_i(dk)y_i(dl)`
term, since a unit cannot be in two exposures at once.
-/

import Causalean.Experimentation.DesignBased.HT.Estimator

/-! # Horvitz-Thompson variance identities

Horvitz-Thompson randomization variance reduces to finite covariance sums over exposure
indicators.

The covariance-form theorem `Var_htTotal_cov` expands the variance of `htTotal` as a double sum of
indicator covariances, and `Var_htTotal` rewrites those terms into the marginal and joint exposure
probabilities. The companion theorems `Cov_htTotal_cov` and `Cov_htTotal` give the analogous
covariance formulas for two exposure totals, including the diagonal cross-exposure term that
appears when one unit cannot occupy two distinct exposures at once.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Δ]

omit [DecidableEq ι] in
/-- **Lemma 4.1 (variance), covariance form.** The variance of the HT total is the double
sum of inverse-probability-weighted indicator covariances. -/
theorem Var_htTotal_cov (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) :
    D.Var (htTotal D y f θ d)
      = ∑ i, ∑ j, (y i d / prop D f θ i d) * (y j d / prop D f θ j d)
          * D.Cov (expoInd f θ i d) (expoInd f θ j d) := by
  rw [show D.Var (htTotal D y f θ d)
        = D.Var (fun z => ∑ i, (y i d / prop D f θ i d) * expoInd f θ i d z) from
      D.Var_congr (fun z => by
        rw [htTotal_eq]; exact Finset.sum_congr rfl (fun i _ => by ring))]
  rw [FiniteDesign.Var_linear_comb]

/-- **Lemma 4.1 (variance), expanded form `eq:total_variance`.** Diagonal terms use
`Var[1(expo i = d)] = π_i(1−π_i)`, off-diagonal terms use
`Cov[1(expo i = d),1(expo j = d)] = π_{ij}(d) − π_i(d)π_j(d)`. -/
theorem Var_htTotal (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) :
    D.Var (htTotal D y f θ d)
      = (∑ i, prop D f θ i d * (1 - prop D f θ i d) * (y i d / prop D f θ i d) ^ 2)
        + ∑ i, ∑ j ∈ Finset.univ.erase i,
            (propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d)
              * ((y i d / prop D f θ i d) * (y j d / prop D f θ j d)) := by
  rw [Var_htTotal_cov, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · -- diagonal term j = i
    rw [FiniteDesign.Cov_self,
      show D.Var (expoInd f θ i d) = prop D f θ i d * (1 - prop D f θ i d) from
        FiniteDesign.Var_ind (D := D) (fun z => expo f θ i z = d)]
    ring
  · -- off-diagonal j ∈ erase i
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Cov_expoInd_same]; ring

omit [DecidableEq ι] in
/-- The covariance between two Horvitz-Thompson exposure totals is the double sum, over ordered
unit pairs, of the two inverse-probability outcome weights times the covariance of the
corresponding exposure indicators. -/
theorem Cov_htTotal_cov (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) :
    D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl)
      = ∑ i, ∑ j, (y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl)
          * D.Cov (expoInd f θ i dk) (expoInd f θ j dl) := by
  rw [D.Cov_congr
        (X' := fun z => ∑ i, (y i dk / prop D f θ i dk) * expoInd f θ i dk z)
        (Y' := fun z => ∑ j, (y j dl / prop D f θ j dl) * expoInd f θ j dl z)
        (fun z => by rw [htTotal_eq]; exact Finset.sum_congr rfl (fun i _ => by ring))
        (fun z => by rw [htTotal_eq]; exact Finset.sum_congr rfl (fun j _ => by ring))]
  rw [FiniteDesign.Cov_linear_comb]

/-- **Proposition 4.4 (covariance), expanded form `eq:totals_covariance`**. When the two
exposures are distinct and every unit has nonzero probability of both exposures, the diagonal
cross-indicator vanishes and yields the unidentified term `−∑ᵢ y_i(dk)y_i(dl)`. -/
theorem Cov_htTotal (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hne : dk ≠ dl)
    (hk : ∀ i, prop D f θ i dk ≠ 0) (hl : ∀ i, prop D f θ i dl ≠ 0) :
    D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl)
      = (∑ i, ∑ j ∈ Finset.univ.erase i,
            (propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
              * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl)))
        - ∑ i, y i dk * y i dl := by
  rw [Cov_htTotal_cov, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [show (∑ j ∈ Finset.univ.erase i,
        (propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
          * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl)))
        = (∑ j ∈ Finset.univ.erase i,
            (y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl)
              * D.Cov (expoInd f θ i dk) (expoInd f θ j dl)) from
      Finset.sum_congr rfl (fun j _ => by rw [Cov_expoInd_cross]; ring)]
  -- diagonal: peel the j = i term and reduce it to -(y i dk * y i dl)
  rw [Cov_expoInd_cross, propPairCross_self_of_ne D f θ i hne]
  have hki := hk i
  have hli := hl i
  field_simp
  ring

end DesignBased
end Experimentation
end Causalean
