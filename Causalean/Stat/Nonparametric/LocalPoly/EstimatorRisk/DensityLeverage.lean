/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.Factorization
import Causalean.Stat.Nonparametric.LocalPoly.Rate

/-!
# Density-constant discharge of the local-polynomial leverage rate

Turns local-polynomial leverage hypotheses into explicit density and kernel-moment constants.

This module turns the abstract population-matrix leverage hypotheses for an interior
local-polynomial fit into explicit density and kernel-moment constants. The earlier
`LocalPoly.Rate.population_scaling_of_conj` reduced the leverage scaling to a bandwidth-free shape
matrix `T` with assumed `(T⁻¹)₀₀ ≤ cInv` and `T₀₀ ≤ cTop`; here those constants become
**explicit density + kernel-moment quantities**:

`cInv = (G⁻¹)₀₀ / cDesign`,   `cTop = CDesign · G₀₀`,

with `G = weightMomentMatrix p K` the pure kernel-moment matrix and density-window bounds supplying
the needed lower bound for the inverse rate and both lower/upper bounds for the leverage product.
The chain is:

`popDesignMatrix_factor`  (S = (Nh)·D T D, change of variables)
  → `DensityConstants`     ((T⁻¹)₀₀ ≤ (G⁻¹)₀₀/cDesign, T₀₀ ≤ CDesign·G₀₀ via Loewner sandwich)
  → diagonal-conjugation scaling  ((S⁻¹)₀₀ ≤ cInv/(Nh), S₀₀ ≤ cTop·(Nh))
  → `localPoly_inv00_rate` / `localPoly_leverage_bound`.

The resulting `localPoly_density_inv00_rate` and `localPoly_density_leverage_bound` carry no
hypothesis on the population matrix `S` other than the good design event (`M` entrywise within `η`
of `S`) and explicit small-perturbation scale constants.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- **Explicit `Θ(1/(Nh))` leverage rate from density + kernel-moment constants.** Let the kernel
`K ≥ 0` be supported in `[-1,1]`, with pure kernel-moment matrix `G = weightMomentMatrix p K`
positive definite, and the kernel shape matrix `T = weightMomentMatrix p (K·p(t+h·))` positive
definite; let the design density obey `0 < cDesign ≤ p` on the window `|a − t| ≤ h`, and
let `M` be entrywise within `η` of the population matrix `S = popDesignMatrix p N K p t h` whose
inverse rows are bounded by `c`. With the regime constants small (`c·(p+1)·η ≤ 1/2` and
`2c²(p+1)η ≤ cInv/(Nh)`, `cInv = (G⁻¹)₀₀/cDesign`), the empirical moment matrix `M` is invertible
and its intercept leverage obeys the explicit interior rate

`(M⁻¹)₀₀ ≤ 2·cInv/(Nh)`,

with `cInv` an explicit density + kernel-moment constant — no `S`-level invertibility or leverage
assumption remains. -/
theorem localPoly_density_inv00_rate {N : ℕ} {h cDesign η c t : ℝ} {K pdens : ℝ → ℝ}
    {M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hh : 0 < h) (hN : 0 < (N : ℝ)) (hcD : 0 < cDesign)
    (hKnn : ∀ u, 0 ≤ K u) (hKsupp : ∀ u, 1 < |u| → K u = 0)
    (hintT : ∀ j k : Fin (p + 1),
      Integrable (fun u => (K u * pdens (t + h * u)) * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hintG : ∀ j k : Fin (p + 1),
      Integrable (fun u => K u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hGpd : (weightMomentMatrix p K).PosDef)
    (hTpd : (weightMomentMatrix p (fun u => K u * pdens (t + h * u))).PosDef)
    (hlo : ∀ a, |a - t| ≤ h → cDesign ≤ pdens a)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hSrow : ∀ i, (∑ j, |(popDesignMatrix p N K pdens t h)⁻¹ i j|) ≤ c)
    (hclose : ∀ j k, |M j k - popDesignMatrix p N K pdens t h j k| ≤ η)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2)
    (hpert : 2 * c ^ 2 * ((p + 1 : ℕ) * η)
      ≤ ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h)) :
    IsUnit M.det
      ∧ M⁻¹ 0 0 ≤ 2 * (((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h)) := by
  set G := weightMomentMatrix p K with hG
  set T := weightMomentMatrix p (fun u => K u * pdens (t + h * u)) with hT
  set S := popDesignMatrix p N K pdens t h with hSdef
  -- Loewner sandwich (lower): `cDesign · (wᵀ G w) ≤ wᵀ T w`.
  have hsand_lower : ∀ w : Fin (p + 1) → ℝ,
      cDesign * (w ⬝ᵥ (G *ᵥ w)) ≤ w ⬝ᵥ (T *ᵥ w) := fun w =>
    weightMomentMatrix_quadForm_sandwich hcD.le hintT hintG
      (kernelDensity_lower_dom hh hKnn hKsupp hlo) w
  have hTinv00 : T⁻¹ 0 0 ≤ (weightMomentMatrix p K)⁻¹ 0 0 / cDesign :=
    inv00_le_of_quadForm_sandwich hTpd hGpd hcD hsand_lower
  have hTunit : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTpd.isUnit
  have hfactor : S = ((N : ℝ) * h) •
      (Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * T *
        Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ))) :=
    popDesignMatrix_factor N K pdens t h hh
  let κ : ℝ := (N : ℝ) * h
  have hκ : κ ≠ 0 := (mul_pos hN hh).ne'
  have hd : ∀ i : Fin (p + 1), h ^ (i : ℕ) ≠ 0 := fun i => pow_ne_zero _ hh.ne'
  have hd0 : (fun j : Fin (p + 1) => h ^ (j : ℕ)) 0 = 1 := by
    simp
  obtain ⟨hSunit, hSinv00_eq⟩ :=
    inv00_diag_conj (κ := κ) hκ hd hd0 hTunit hfactor
  have hSinv00 : S⁻¹ 0 0 ≤ ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h) := by
    rw [hSinv00_eq]
    have hκnonneg : 0 ≤ κ⁻¹ := inv_nonneg.mpr (mul_pos hN hh).le
    calc
      κ⁻¹ * T⁻¹ 0 0 ≤ κ⁻¹ * ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) :=
        mul_le_mul_of_nonneg_left hTinv00 hκnonneg
      _ = ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h) := by
        simp [κ, div_eq_mul_inv, mul_comm]
  exact localPoly_inv00_rate (mul_pos hN hh) hSunit hc hη hSrow hclose hsmall hSinv00 hpert

/-- **Bandwidth-free density bound on the local-polynomial leverage product.** Under the same
density + kernel-moment hypotheses as `localPoly_density_inv00_rate` (with the extra regime
condition `η ≤ Nh` and `0 ≤ M₀₀, 0 ≤ (M⁻¹)₀₀`), the geometric mean of the total weight and the
inverse leverage is bounded by the bandwidth-free density constant

`√(M₀₀·(M⁻¹)₀₀) ≤ √(2·cInv·(cTop+1))`,  `cInv = (G⁻¹)₀₀/cDesign`, `cTop = CDesign·G₀₀`.

Via `equivKernelWeight_abs_sum_sq_le` this controls the `ℓ¹` bias leverage `∑ᵢ|Sᵢ|` by a
bandwidth-free constant. -/
theorem localPoly_density_leverage_bound {N : ℕ} {h cDesign CDesign η c t : ℝ} {K pdens : ℝ → ℝ}
    {M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hh : 0 < h) (hN : 0 < (N : ℝ)) (hcD : 0 < cDesign) (hcCD : cDesign ≤ CDesign)
    (hKnn : ∀ u, 0 ≤ K u) (hKsupp : ∀ u, 1 < |u| → K u = 0)
    (hintT : ∀ j k : Fin (p + 1),
      Integrable (fun u => (K u * pdens (t + h * u)) * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hintG : ∀ j k : Fin (p + 1),
      Integrable (fun u => K u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hGpd : (weightMomentMatrix p K).PosDef)
    (hTpd : (weightMomentMatrix p (fun u => K u * pdens (t + h * u))).PosDef)
    (hlo : ∀ a, |a - t| ≤ h → cDesign ≤ pdens a)
    (hhi : ∀ a, |a - t| ≤ h → pdens a ≤ CDesign)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hSrow : ∀ i, (∑ j, |(popDesignMatrix p N K pdens t h)⁻¹ i j|) ≤ c)
    (hclose : ∀ j k, |M j k - popDesignMatrix p N K pdens t h j k| ≤ η)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2)
    (hpert : 2 * c ^ 2 * ((p + 1 : ℕ) * η)
      ≤ ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h))
    (hηle : η ≤ (N : ℝ) * h) (hM00 : 0 ≤ M 0 0) (hMinv00 : 0 ≤ M⁻¹ 0 0) :
    Real.sqrt (M 0 0 * M⁻¹ 0 0)
      ≤ Real.sqrt (2 * ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign)
          * (CDesign * (weightMomentMatrix p K) 0 0 + 1)) := by
  set G := weightMomentMatrix p K with hG
  set T := weightMomentMatrix p (fun u => K u * pdens (t + h * u)) with hT
  set S := popDesignMatrix p N K pdens t h with hSdef
  have hsand_lower : ∀ w : Fin (p + 1) → ℝ,
      cDesign * (w ⬝ᵥ (G *ᵥ w)) ≤ w ⬝ᵥ (T *ᵥ w) := fun w =>
    weightMomentMatrix_quadForm_sandwich hcD.le hintT hintG
      (kernelDensity_lower_dom hh hKnn hKsupp hlo) w
  have hsand_upper : ∀ w : Fin (p + 1) → ℝ,
      w ⬝ᵥ (T *ᵥ w) ≤ CDesign * (w ⬝ᵥ (G *ᵥ w)) := fun w =>
    weightMomentMatrix_quadForm_sandwich_upper (hcD.le.trans hcCD) hintT hintG
      (kernelDensity_upper_dom hh hKnn hKsupp hhi) w
  have hTinv00 : T⁻¹ 0 0 ≤ G⁻¹ 0 0 / cDesign :=
    inv00_le_of_quadForm_sandwich hTpd hGpd hcD hsand_lower
  have hT00 : T 0 0 ≤ CDesign * G 0 0 := entry00_le_of_quadForm_sandwich hsand_upper
  have hTunit : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTpd.isUnit
  have hfactor : S = ((N : ℝ) * h) •
      (Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * T *
        Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ))) :=
    popDesignMatrix_factor N K pdens t h hh
  obtain ⟨hSunit, hSinv00, hS00'⟩ :=
    population_scaling_of_conj hh hN hTunit hTinv00 hT00 hfactor
  -- nonnegativity of the density constants from positive (semi)definiteness of `G`.
  have hG00_nn : 0 ≤ G 0 0 := by
    have h := hGpd.posSemidef.dotProduct_mulVec_nonneg (Pi.single (0 : Fin (p + 1)) (1 : ℝ))
    rw [entry00_eq_quadForm G]; simpa using h
  have hGinv00_nn : 0 ≤ G⁻¹ 0 0 := by
    have h := hGpd.posSemidef.inv.dotProduct_mulVec_nonneg (Pi.single (0 : Fin (p + 1)) (1 : ℝ))
    rw [inv00_eq_quadForm G]; simpa using h
  have hcInv_nn : 0 ≤ G⁻¹ 0 0 / cDesign := div_nonneg hGinv00_nn hcD.le
  have hcTop_nn : 0 ≤ CDesign * G 0 0 := mul_nonneg (hcD.le.trans hcCD) hG00_nn
  exact localPoly_leverage_bound (mul_pos hN hh) hSunit hc hη hcInv_nn hcTop_nn
    hSrow hclose hsmall hSinv00 hpert hS00' hηle hM00 hMinv00

end Causalean.Stat.Nonparametric
