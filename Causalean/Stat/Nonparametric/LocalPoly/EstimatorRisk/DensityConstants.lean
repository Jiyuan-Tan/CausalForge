/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.SquareCompletion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Density constants for the local-polynomial kernel shape matrix

The bandwidth-free kernel shape matrix `T_{jk} = ∫ K(u) u^{j+k} p(t+hu) du` is the
positive-density-weighted Gram matrix of the centered monomials, and the pure kernel-moment
matrix `G_{jk} = ∫ K(u) u^{j+k} du` is its unit-density analogue. This file:

* defines `weightMomentMatrix p W` — the moment matrix `∫ W(u) u^{j+k} du` of an arbitrary weight
  `W : ℝ → ℝ`, with its Gram quadratic form `vᵀ (weightMomentMatrix p W) v = ∫ W(u) (∑ vⱼ uʲ)² du`;
* proves the **Loewner sandwich** `c·G ⪯ T ⪯ C·G` (on quadratic forms) from a *pointwise weight
  domination* `c·W_G ≤ W_T ≤ C·W_G`, which in turn follows from the design-density window bound
  `cDesign ≤ p ≤ CDesign` (the kernel weight `K ≥ 0` carries the densities);
* combines the sandwich with `SquareCompletion.inv00_le_of_quadForm_sandwich` to bound the shape
  matrix's intercept leverage and top weight by the **density constants**:

  `(T⁻¹)₀₀ ≤ (G⁻¹)₀₀ / cDesign`,   `T₀₀ ≤ CDesign · G₀₀`.

These discharge the `(T⁻¹)₀₀ ≤ cInv` and `T₀₀ ≤ cTop` hypotheses fed to
`population_scaling_of_conj`, leaving no S-level invertibility/leverage assumption.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- The **weight-`W` moment matrix** `(weightMomentMatrix p W)_{jk} = ∫ W(u) · u^j · u^k du` of the
centered monomials against the Lebesgue weight `W`. With `W = K · (p ∘ (t + h·)) ` this is the
kernel shape matrix `T`; with `W = K` it is the pure kernel-moment matrix `G`. -/
noncomputable def weightMomentMatrix (p : ℕ) (W : ℝ → ℝ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  Matrix.of (fun j k => ∫ u, W u * (u ^ (j : ℕ) * u ^ (k : ℕ)))

/-- **Gram quadratic form of the weight moment matrix.** `vᵀ (weightMomentMatrix p W) v =
∫ W(u) (∑ⱼ vⱼ uʲ)² du`. -/
theorem weightMomentMatrix_quadForm {W : ℝ → ℝ}
    (hint : ∀ j k : Fin (p + 1),
      Integrable (fun u => W u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (v : Fin (p + 1) → ℝ) :
    v ⬝ᵥ (weightMomentMatrix p W *ᵥ v)
      = ∫ u, W u * (∑ j, v j * u ^ (j : ℕ)) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, weightMomentMatrix, Matrix.of_apply]
  calc
    ∑ j : Fin (p + 1), v j * ∑ k : Fin (p + 1),
          (∫ u, W u * (u ^ (j : ℕ) * u ^ (k : ℕ))) * v k
        = ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * ∫ u, W u * (u ^ (j : ℕ) * u ^ (k : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
    _ = ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            ∫ u, (v j * v k) * (W u * (u ^ (j : ℕ) * u ^ (k : ℕ))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro k _
          exact (MeasureTheory.integral_const_mul (v j * v k)
            (fun u => W u * (u ^ (j : ℕ) * u ^ (k : ℕ)))).symm
    _ = ∑ j : Fin (p + 1),
            ∫ u, ∑ k : Fin (p + 1),
              (v j * v k) * (W u * (u ^ (j : ℕ) * u ^ (k : ℕ))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          symm
          rw [MeasureTheory.integral_finset_sum]
          intro k _
          exact (hint j k).const_mul (v j * v k)
    _ = ∫ u, ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * (W u * (u ^ (j : ℕ) * u ^ (k : ℕ))) := by
          symm
          rw [MeasureTheory.integral_finset_sum]
          intro j _
          exact integrable_finset_sum _ (fun k _ => (hint j k).const_mul (v j * v k))
    _ = ∫ u, W u * (∑ j, v j * u ^ (j : ℕ)) ^ 2 := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun u => by
              change (∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
                  (v j * v k) * (W u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
                = W u * (∑ j : Fin (p + 1), v j * u ^ (j : ℕ)) ^ 2
              rw [pow_two, Finset.sum_mul_sum]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro k _
              ring))

/-- The weight moment matrix is symmetric. -/
theorem weightMomentMatrix_isHermitian {W : ℝ → ℝ} :
    (weightMomentMatrix p W).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, weightMomentMatrix, Matrix.of_apply, star_trivial]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))

/-- **Loewner sandwich on quadratic forms from pointwise weight domination.** If the weights satisfy
`c · W_G(u) ≤ W_T(u)` pointwise (`c ≥ 0`) and both monomial integrands are integrable, then the
shape matrix dominates `c` times the pure matrix in the Loewner order:
`c · (vᵀ G v) ≤ vᵀ T v` for every `v`, where `T = weightMomentMatrix p W_T`, `G = weightMomentMatrix
p W_G`. -/
theorem weightMomentMatrix_quadForm_sandwich {WT WG : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hintT : ∀ j k : Fin (p + 1), Integrable (fun u => WT u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hintG : ∀ j k : Fin (p + 1), Integrable (fun u => WG u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hdom : ∀ u, c * WG u ≤ WT u)
    (v : Fin (p + 1) → ℝ) :
    c * (v ⬝ᵥ (weightMomentMatrix p WG *ᵥ v)) ≤ v ⬝ᵥ (weightMomentMatrix p WT *ᵥ v) := by
  have _hc := hc
  let s : ℝ → ℝ := fun u => ∑ j : Fin (p + 1), v j * u ^ (j : ℕ)
  have hsqG : Integrable (fun u => WG u * (s u) ^ 2) := by
    have e : (fun u => WG u * (s u) ^ 2)
        = (fun u => ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * (WG u * (u ^ (j : ℕ) * u ^ (k : ℕ)))) := by
      funext u
      dsimp [s]
      rw [pow_two, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [e]
    exact integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun k _ => (hintG j k).const_mul (v j * v k)))
  have hsqT : Integrable (fun u => WT u * (s u) ^ 2) := by
    have e : (fun u => WT u * (s u) ^ 2)
        = (fun u => ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * (WT u * (u ^ (j : ℕ) * u ^ (k : ℕ)))) := by
      funext u
      dsimp [s]
      rw [pow_two, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [e]
    exact integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun k _ => (hintT j k).const_mul (v j * v k)))
  rw [weightMomentMatrix_quadForm hintG v, weightMomentMatrix_quadForm hintT v]
  change c * (∫ u, WG u * (s u) ^ 2) ≤ ∫ u, WT u * (s u) ^ 2
  rw [← MeasureTheory.integral_const_mul c (fun u => WG u * (s u) ^ 2)]
  exact MeasureTheory.integral_mono (hsqG.const_mul c) hsqT (fun u => by
    calc
      c * (WG u * (s u) ^ 2) = (c * WG u) * (s u) ^ 2 := by ring
      _ ≤ WT u * (s u) ^ 2 := mul_le_mul_of_nonneg_right (hdom u) (sq_nonneg _))

/-- **Loewner sandwich on quadratic forms, upper direction.** If `W_T(u) ≤ C · W_G(u)` pointwise
(`C ≥ 0`) and both monomial integrands are integrable, then `vᵀ T v ≤ C · (vᵀ G v)` for every `v`,
where `T = weightMomentMatrix p W_T`, `G = weightMomentMatrix p W_G`. -/
theorem weightMomentMatrix_quadForm_sandwich_upper {WT WG : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hintT : ∀ j k : Fin (p + 1), Integrable (fun u => WT u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hintG : ∀ j k : Fin (p + 1), Integrable (fun u => WG u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hdom : ∀ u, WT u ≤ C * WG u)
    (v : Fin (p + 1) → ℝ) :
    v ⬝ᵥ (weightMomentMatrix p WT *ᵥ v) ≤ C * (v ⬝ᵥ (weightMomentMatrix p WG *ᵥ v)) := by
  have _hC := hC
  let s : ℝ → ℝ := fun u => ∑ j : Fin (p + 1), v j * u ^ (j : ℕ)
  have hsqT : Integrable (fun u => WT u * (s u) ^ 2) := by
    have e : (fun u => WT u * (s u) ^ 2)
        = (fun u => ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * (WT u * (u ^ (j : ℕ) * u ^ (k : ℕ)))) := by
      funext u
      dsimp [s]
      rw [pow_two, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [e]
    exact integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun k _ => (hintT j k).const_mul (v j * v k)))
  have hsqG : Integrable (fun u => WG u * (s u) ^ 2) := by
    have e : (fun u => WG u * (s u) ^ 2)
        = (fun u => ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * (WG u * (u ^ (j : ℕ) * u ^ (k : ℕ)))) := by
      funext u
      dsimp [s]
      rw [pow_two, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [e]
    exact integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun k _ => (hintG j k).const_mul (v j * v k)))
  rw [weightMomentMatrix_quadForm hintT v, weightMomentMatrix_quadForm hintG v]
  change (∫ u, WT u * (s u) ^ 2) ≤ C * (∫ u, WG u * (s u) ^ 2)
  rw [← MeasureTheory.integral_const_mul C (fun u => WG u * (s u) ^ 2)]
  exact MeasureTheory.integral_mono hsqT (hsqG.const_mul C) (fun u => by
    calc
      WT u * (s u) ^ 2 ≤ (C * WG u) * (s u) ^ 2 :=
        mul_le_mul_of_nonneg_right (hdom u) (sq_nonneg _)
      _ = C * (WG u * (s u) ^ 2) := by ring)

/-- **Pointwise weight domination from the design-density window bound.** If the kernel `K` is
nonnegative and supported in `[-1,1]` and the design density `p` obeys `cDesign ≤ p(a)` for every
`a` within bandwidth `h` of `t`, then `cDesign · K(u) ≤ K(u) · p(t + h·u)` for every `u`: on the
support `|u| ≤ 1` the argument `t + h·u` lies in the window, off the support both sides vanish. -/
theorem kernelDensity_lower_dom {K pdens : ℝ → ℝ} {t h cDesign : ℝ} (hh : 0 < h)
    (hKnn : ∀ u, 0 ≤ K u) (hKsupp : ∀ u, 1 < |u| → K u = 0)
    (hlo : ∀ a, |a - t| ≤ h → cDesign ≤ pdens a) :
    ∀ u, cDesign * K u ≤ K u * pdens (t + h * u) := by
  intro u
  by_cases hu : |u| ≤ 1
  · have hwin : |(t + h * u) - t| ≤ h := by
      calc
        |(t + h * u) - t| = |h * u| := by ring_nf
        _ = h * |u| := by rw [abs_mul, abs_of_pos hh]
        _ ≤ h * 1 := mul_le_mul_of_nonneg_left hu hh.le
        _ = h := by ring
    have hp : cDesign ≤ pdens (t + h * u) := hlo (t + h * u) hwin
    have := mul_le_mul_of_nonneg_right hp (hKnn u)
    linarith
  · have hlt : 1 < |u| := lt_of_not_ge hu
    have hK : K u = 0 := hKsupp u hlt
    simp [hK]

/-- **Pointwise weight domination, upper side.** Same hypotheses with an upper density bound
`p(a) ≤ CDesign` on the window give `K(u) · p(t + h·u) ≤ CDesign · K(u)` for every `u`. -/
theorem kernelDensity_upper_dom {K pdens : ℝ → ℝ} {t h CDesign : ℝ} (hh : 0 < h)
    (hKnn : ∀ u, 0 ≤ K u) (hKsupp : ∀ u, 1 < |u| → K u = 0)
    (hhi : ∀ a, |a - t| ≤ h → pdens a ≤ CDesign) :
    ∀ u, K u * pdens (t + h * u) ≤ CDesign * K u := by
  intro u
  by_cases hu : |u| ≤ 1
  · have hwin : |(t + h * u) - t| ≤ h := by
      calc
        |(t + h * u) - t| = |h * u| := by ring_nf
        _ = h * |u| := by rw [abs_mul, abs_of_pos hh]
        _ ≤ h * 1 := mul_le_mul_of_nonneg_left hu hh.le
        _ = h := by ring
    have hp : pdens (t + h * u) ≤ CDesign := hhi (t + h * u) hwin
    have := mul_le_mul_of_nonneg_right hp (hKnn u)
    linarith
  · have hlt : 1 < |u| := lt_of_not_ge hu
    have hK : K u = 0 := hKsupp u hlt
    simp [hK]

end Causalean.Stat.Nonparametric
