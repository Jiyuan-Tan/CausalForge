/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.Matrix.DesignInverse
import Causalean.Stat.Nonparametric.LocalPoly.Rate.Conjugation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Explicit `Θ(Nh)` rate for the local-polynomial leverage `(M⁻¹)₀₀`

Explicit `Θ(Nh)` leverage-rate bounds for the local-polynomial design inverse, derived from
entrywise design-matrix concentration and population scaling.

This module converts the entrywise design-matrix concentration of
`Concentration.DesignInverse` into the **explicit interior local-polynomial leverage rate**:

* `localPoly_inv00_rate` — on the good design event (empirical moment matrix `M` entrywise within
  `η` of the population matrix `S`), the leverage `(M⁻¹)₀₀ ≤ 2·cInv/(Nh)`, i.e. the variance
  scale is `Θ(1/(Nh))`.
* `localPoly_leverage_bound` — the leverage product `√(M₀₀·(M⁻¹)₀₀) ≤ √(2·cInv·(cTop+1))`, a
  bandwidth-free constant, controlling the `ℓ¹` bias leverage.

The population matrix is supplied with its `Θ(Nh)` scale via the diagonal-conjugation
factorization `S = (Nh)·D·T·D` (`D = diagonal (h^j)`): `population_scaling_of_conj` turns a
bandwidth-free shape matrix `T` (invertible with bounded `(T⁻¹)₀₀` and `T₀₀`, supplied by the
integral-moment positive-definiteness of `LocalPoly.Rate.IntegralMoment`) into the leverage scaling
hypotheses `(S⁻¹)₀₀ ≤ cInv/(Nh)` and `S₀₀ ≤ cTop·(Nh)`. The entrywise-closeness hypothesis is the
good event whose probability is bounded by `designMatrix_inv_concentration`.
-/

namespace Causalean.Stat.Nonparametric

open Causalean.Stat.Concentration
open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- **`Θ(Nh)` leverage scaling from the change-of-variables factorization.** If the population
moment matrix factors as `S = (Nh)·D·T·D` with `D = diagonal (fun j => h^j)` (so `D₀₀ = 1`) and a
bandwidth-free shape matrix `T` that is invertible with `(T⁻¹)₀₀ ≤ cInv` and `T₀₀ ≤ cTop`, then `S`
is invertible and its intercept leverage scales as `(S⁻¹)₀₀ ≤ cInv/(Nh)` while its top weight
scales as `S₀₀ ≤ cTop·(Nh)`. This discharges the leverage-scaling hypotheses of the rate
capstones from the bandwidth-free shape matrix `T`. -/
theorem population_scaling_of_conj {N : ℕ} {h cInv cTop : ℝ}
    (hh : 0 < h) (hN : 0 < (N : ℝ))
    {T S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} (hT : IsUnit T.det)
    (hTinv00 : T⁻¹ 0 0 ≤ cInv) (hT00 : T 0 0 ≤ cTop)
    (hS : S = ((N : ℝ) * h) •
      (Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * T *
        Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)))) :
    IsUnit S.det ∧ S⁻¹ 0 0 ≤ cInv / ((N : ℝ) * h) ∧ S 0 0 ≤ cTop * ((N : ℝ) * h) := by
  let κ : ℝ := (N : ℝ) * h
  have hκ : κ ≠ 0 := (mul_pos hN hh).ne'
  have hd : ∀ i : Fin (p + 1), h ^ (i : ℕ) ≠ 0 := fun i => pow_ne_zero _ hh.ne'
  have hd0 : (fun j : Fin (p + 1) => h ^ (j : ℕ)) 0 = 1 := by
    simp
  obtain ⟨hdet, hinv00⟩ :=
    inv00_diag_conj (κ := κ) hκ hd hd0 hT hS
  have htop := top00_diag_conj (κ := κ) hd0 hS
  refine ⟨hdet, ?_, ?_⟩
  · rw [hinv00]
    have hκnonneg : 0 ≤ κ⁻¹ := inv_nonneg.mpr (mul_pos hN hh).le
    calc
      κ⁻¹ * T⁻¹ 0 0 ≤ κ⁻¹ * cInv := mul_le_mul_of_nonneg_left hTinv00 hκnonneg
      _ = cInv / ((N : ℝ) * h) := by
        simp [κ, div_eq_mul_inv, mul_comm]
  · rw [htop]
    have hκnonneg : 0 ≤ κ := (mul_pos hN hh).le
    calc
      κ * T 0 0 ≤ κ * cTop := mul_le_mul_of_nonneg_left hT00 hκnonneg
      _ = cTop * ((N : ℝ) * h) := by
        simp [κ, mul_comm]

/-- **Explicit `Θ(1/(Nh))` rate for the local-polynomial leverage.** On the good design event —
where every entry of the empirical moment matrix `M` is within `η` of the population matrix `S`,
with `S` invertible, its inverse row sums bounded by `c`, the perturbation scale small
(`c·(p+1)·η ≤ 1/2`), and the population intercept leverage at the `Θ(Nh)` scale
(`(S⁻¹)₀₀ ≤ cInv/(Nh)` and `2c²(p+1)η ≤ cInv/(Nh)`) — the empirical moment matrix `M` is invertible
and its intercept leverage obeys the explicit interior rate

`(M⁻¹)₀₀ ≤ 2·cInv/(Nh)`.

This is the variance-rate capstone for the local-polynomial upper bound: combined with
`localPoly_intercept_variance_le` it yields the `O((Nh)^{-1/2})` stochastic error. -/
theorem localPoly_inv00_rate {N : ℕ} {h c cInv η : ℝ}
    {S M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (_hNh : 0 < (N : ℝ) * h)
    (hS : IsUnit S.det) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hSrow : ∀ i, (∑ j, |S⁻¹ i j|) ≤ c)
    (hclose : ∀ j k, |M j k - S j k| ≤ η)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2)
    (hSinv00 : S⁻¹ 0 0 ≤ cInv / ((N : ℝ) * h))
    (hpert : 2 * c ^ 2 * ((p + 1 : ℕ) * η) ≤ cInv / ((N : ℝ) * h)) :
    IsUnit M.det ∧ M⁻¹ 0 0 ≤ 2 * (cInv / ((N : ℝ) * h)) := by
  obtain ⟨hMdet, hΔ⟩ := designInv00_perturb S M hS hc hη hSrow hclose hsmall
  refine ⟨hMdet, ?_⟩
  have hub := (abs_le.mp hΔ).2
  linarith [hub, hSinv00, hpert]

/-- **Bandwidth-free bound on the local-polynomial leverage product.** On the same good design
event, the geometric mean of the total weight `M₀₀` and the inverse leverage `(M⁻¹)₀₀` is bounded
by the bandwidth-free constant `√(2·cInv·(cTop+1))`:

`√(M₀₀·(M⁻¹)₀₀) ≤ √(2·cInv·(cTop+1))`.

The `Θ(Nh)` growth of `M₀₀ ≤ (cTop+1)·(Nh)` exactly cancels the `Θ(1/(Nh))` decay of
`(M⁻¹)₀₀`. Via `equivKernelWeight_abs_sum_sq_le` (`(∑ᵢ|Sᵢ|)² ≤ M₀₀·(M⁻¹)₀₀`) this controls the
`ℓ¹` bias leverage `∑ᵢ|Sᵢ|` by a bandwidth-free constant, the second leverage capstone used by
the upper-bound analysis. -/
theorem localPoly_leverage_bound {N : ℕ} {h c cInv cTop η : ℝ}
    {S M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hNh : 0 < (N : ℝ) * h)
    (hS : IsUnit S.det) (hc : 0 ≤ c) (hη : 0 ≤ η) (_hcInv : 0 ≤ cInv) (hcTop : 0 ≤ cTop)
    (hSrow : ∀ i, (∑ j, |S⁻¹ i j|) ≤ c)
    (hclose : ∀ j k, |M j k - S j k| ≤ η)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2)
    (hSinv00 : S⁻¹ 0 0 ≤ cInv / ((N : ℝ) * h))
    (hpert : 2 * c ^ 2 * ((p + 1 : ℕ) * η) ≤ cInv / ((N : ℝ) * h))
    (hS00 : S 0 0 ≤ cTop * ((N : ℝ) * h))
    (hηle : η ≤ (N : ℝ) * h)
    (hM00 : 0 ≤ M 0 0) (hMinv00 : 0 ≤ M⁻¹ 0 0) :
    Real.sqrt (M 0 0 * M⁻¹ 0 0) ≤ Real.sqrt (2 * cInv * (cTop + 1)) := by
  obtain ⟨_, hrate⟩ :=
    localPoly_inv00_rate hNh hS hc hη hSrow hclose hsmall hSinv00 hpert
  have hcl := (abs_le.mp (hclose 0 0)).2
  have hM00bd : M 0 0 ≤ (cTop + 1) * ((N : ℝ) * h) := by
    nlinarith [hS00, hcl, hηle]
  have hb0 : 0 ≤ (cTop + 1) * ((N : ℝ) * h) := by
    nlinarith [hcTop, hNh.le]
  have hprod : M 0 0 * M⁻¹ 0 0 ≤ 2 * cInv * (cTop + 1) := by
    have hmul := mul_le_mul hM00bd hrate hMinv00 hb0
    have hne : ((N : ℝ) * h) ≠ 0 := hNh.ne'
    calc
      M 0 0 * M⁻¹ 0 0 ≤
          ((cTop + 1) * ((N : ℝ) * h)) * (2 * (cInv / ((N : ℝ) * h))) := hmul
      _ = 2 * cInv * (cTop + 1) := by
        rw [div_eq_mul_inv]
        calc
          ((cTop + 1) * ((N : ℝ) * h)) *
              (2 * (cInv * (((N : ℝ) * h)⁻¹))) =
              (2 * cInv * (cTop + 1)) *
                (((N : ℝ) * h) * (((N : ℝ) * h)⁻¹)) := by
            ring
          _ = 2 * cInv * (cTop + 1) := by
            rw [mul_inv_cancel₀ hne]
            ring
  exact Real.sqrt_le_sqrt hprod

end Causalean.Stat.Nonparametric
