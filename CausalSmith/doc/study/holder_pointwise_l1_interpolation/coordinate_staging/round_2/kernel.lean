/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Defs
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Moment-cancelling product kernel (Milestone 1)

Milestone 1 of the Tsybakov interpolation primitive: a bounded, compactly
supported product kernel `K` on `[-1,1]^d` with total mass `1` and vanishing
moments up to order `m = ⌈γ⌉₊ - 1`.

* `exists_moment_cancelling_kernel_1d` — the 1-D building block: a continuous,
  `[-1,1]`-supported kernel `k` with `∫ k = 1` and `∫ uʲ k(u) du = 0` for
  `1 ≤ j ≤ m`. Obtained by the standard Vandermonde/Gram moment solve: take a
  fixed positive continuous weight vanishing at `±1` and multiply by a degree-`m`
  polynomial whose coefficients solve the nonsingular moment (Gram) system.
* `prodKernel_abs_le` — the tensorized kernel is bounded by `B ^ d` when `k` is
  bounded by `B`.

The multivariate mass-`1` / vanishing-moment consequences of tensorization are
derived at the point of use in `HolderInterpolation.lean` (Fubini over the product
Lebesgue measure), so this file only exposes the 1-D solve and the pointwise
bound.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators

/-- Coefficient-vector polynomial `u ↦ ∑ᵢ cᵢ uⁱ` of degree `≤ m`, used in the
Vandermonde/Gram moment solve for `exists_moment_cancelling_kernel_1d`. -/
private noncomputable def hpkPoly (m : ℕ) (c : Fin (m + 1) → ℝ) (u : ℝ) : ℝ :=
  ∑ i : Fin (m + 1), c i * u ^ (i : ℕ)

/-- The `(m+1)×(m+1)` Gram/Hankel matrix `Gⱼᵢ = ∫_{[-1,1]} u^{i+j} (1 - u²) du` of the
monomials `1, …, uᵐ` under the strictly positive weight `1 - u²` on `[-1,1]`. -/
private noncomputable def hpkGram (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun j i => ∫ u in Set.Icc (-1 : ℝ) 1, u ^ ((i : ℕ) + (j : ℕ)) * (1 - u ^ 2)

private theorem hpkPoly_continuous (m : ℕ) (c : Fin (m + 1) → ℝ) :
    Continuous (hpkPoly m c) := by
  unfold hpkPoly
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_pow _))

/-- Moment expansion: the weighted `j`-th moment of the coefficient polynomial equals
the corresponding row of the Gram matrix applied to the coefficient vector. -/
private theorem hpkExpand (m : ℕ) (c : Fin (m + 1) → ℝ) (J : Fin (m + 1)) :
    (∫ u in Set.Icc (-1 : ℝ) 1, u ^ (J : ℕ) * ((1 - u ^ 2) * hpkPoly m c u))
      = (hpkGram m).mulVec c J := by
  have hcont : ∀ i : Fin (m + 1),
      Continuous (fun u : ℝ => c i * (u ^ ((i : ℕ) + (J : ℕ)) * (1 - u ^ 2))) := by
    intro i
    exact continuous_const.mul
      ((continuous_pow _).mul (continuous_const.sub (continuous_pow 2)))
  have hpt : ∀ u : ℝ, u ^ (J : ℕ) * ((1 - u ^ 2) * hpkPoly m c u)
      = ∑ i : Fin (m + 1), c i * (u ^ ((i : ℕ) + (J : ℕ)) * (1 - u ^ 2)) := by
    intro u
    simp only [hpkPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]; ring
  simp_rw [hpt]
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => (hcont i).integrableOn_Icc)]
  simp_rw [MeasureTheory.integral_const_mul]
  simp only [Matrix.mulVec, dotProduct, hpkGram]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Injectivity of the Gram map: if all weighted moments `0 … m` of the coefficient
polynomial vanish, the coefficient vector is zero. Crux: the quadratic form
`∫ (1 - u²) p(u)² = 0` with a continuous nonnegative integrand forces `p ≡ 0` on
`(-1,1)`, hence the polynomial (finitely many roots) is zero. -/
private theorem hpkInjective (m : ℕ) (c : Fin (m + 1) → ℝ)
    (hc : (hpkGram m).mulVec c = 0) : c = 0 := by
  have hcont2 : ∀ j : Fin (m + 1),
      Continuous (fun u : ℝ => c j * (u ^ (j : ℕ) * ((1 - u ^ 2) * hpkPoly m c u))) := by
    intro j
    exact continuous_const.mul ((continuous_pow _).mul
      ((continuous_const.sub (continuous_pow 2)).mul (hpkPoly_continuous m c)))
  have hpt : ∀ u : ℝ, (1 - u ^ 2) * (hpkPoly m c u) ^ 2
      = ∑ j : Fin (m + 1), c j * (u ^ (j : ℕ) * ((1 - u ^ 2) * hpkPoly m c u)) := by
    intro u
    have hsum : ∑ j : Fin (m + 1), c j * (u ^ (j : ℕ) * ((1 - u ^ 2) * hpkPoly m c u))
        = (∑ j : Fin (m + 1), c j * u ^ (j : ℕ)) * ((1 - u ^ 2) * hpkPoly m c u) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hsum]
    change (1 - u ^ 2) * (hpkPoly m c u) ^ 2 = hpkPoly m c u * ((1 - u ^ 2) * hpkPoly m c u)
    ring
  have hquad : (∫ u in Set.Icc (-1 : ℝ) 1, (1 - u ^ 2) * (hpkPoly m c u) ^ 2) = 0 := by
    simp_rw [hpt]
    rw [MeasureTheory.integral_finset_sum _ (fun j _ => (hcont2 j).integrableOn_Icc)]
    apply Finset.sum_eq_zero
    intro j _
    rw [MeasureTheory.integral_const_mul, hpkExpand m c j, hc]
    simp
  -- The nonnegative continuous integrand with zero integral vanishes a.e., hence on `[-1,1]`.
  have hfcont : Continuous (fun u : ℝ => (1 - u ^ 2) * (hpkPoly m c u) ^ 2) :=
    (continuous_const.sub (continuous_pow 2)).mul ((hpkPoly_continuous m c).pow 2)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)]
      (fun u => (1 - u ^ 2) * (hpkPoly m c u) ^ 2) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ ?_)
    intro u hu
    have hle : (0 : ℝ) ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    exact mul_nonneg hle (sq_nonneg _)
  have hae : (fun u => (1 - u ^ 2) * (hpkPoly m c u) ^ 2)
      =ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hfcont.integrableOn_Icc).mp hquad
  have heqon : Set.EqOn (fun u => (1 - u ^ 2) * (hpkPoly m c u) ^ 2) 0
      (Set.Icc (-1 : ℝ) 1) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hae hfcont.continuousOn
      (by fun_prop)
  have hpoly0 : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, hpkPoly m c u = 0 := by
    intro u hu
    have hfu : (1 - u ^ 2) * (hpkPoly m c u) ^ 2 = 0 :=
      heqon (Set.Ioo_subset_Icc_self hu)
    have hwpos : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    have hsq : (hpkPoly m c u) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hfu with h | h
      · exact absurd h (ne_of_gt hwpos)
      · exact h
    exact (pow_eq_zero_iff (by norm_num)).mp hsq
  -- Realize as a polynomial with infinitely many roots, hence zero, hence `c = 0`.
  set P : Polynomial ℝ := ∑ i : Fin (m + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
    with hPdef
  have hPeval : ∀ u, P.eval u = hpkPoly m c u := by
    intro u
    simp only [hPdef, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, hpkPoly]
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ {x | P.IsRoot x} := by
      intro u hu
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hPeval u]
      exact hpoly0 u hu
    exact (Set.Ioo_infinite (by norm_num)).mono hsub
  funext i
  simp only [Pi.zero_apply]
  have hcoeff : P.coeff (i : ℕ) = c i := by
    simp only [hPdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.val_injective h.symm)
      rw [if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [← hcoeff, hPzero]
  simp

/-- A compactly supported one-dimensional kernel can be chosen to have unit total
mass while cancelling every polynomial moment through any prescribed finite order.

Construction: fix a continuous weight `w ≥ 0` on `[-1,1]` with `w(±1) = 0` and
full support (e.g. `w(u) = (1 - u²)`), and set `k = w · p` for a degree-`m`
polynomial `p`. The requirement `∫ uʲ w p = δ_{j0}` for `0 ≤ j ≤ m` is a linear
system in the coefficients of `p` whose matrix is the Gram/Hankel matrix of the
monomials `1, u, …, uᵐ` under the strictly positive measure `w · Leb⌞[-1,1]`; that
Gram matrix is positive-definite, hence invertible, so a solution `p` exists. -/
theorem exists_moment_cancelling_kernel_1d (m : ℕ) :
    ∃ k : ℝ → ℝ, Continuous k ∧ (∀ u : ℝ, 1 < |u| → k u = 0) ∧
      (∫ u in Set.Icc (-1 : ℝ) 1, k u) = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ m →
        (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0) := by
  -- Solve the Gram system `G c = e₀` by injectivity ⟹ surjectivity of a
  -- finite-dimensional endomorphism.
  have hsurj : Function.Surjective ((hpkGram m).mulVecLin) := by
    rw [← LinearMap.injective_iff_surjective, ← LinearMap.ker_eq_bot,
      Matrix.ker_mulVecLin_eq_bot_iff]
    exact fun v hv => hpkInjective m v hv
  obtain ⟨c, hc⟩ := hsurj (Pi.single 0 1)
  rw [Matrix.mulVecLin_apply] at hc
  -- The moment integrals of `k = max(1-u²,0) · p(u)` over `[-1,1]` equal the Gram rows.
  have hmom : ∀ J : Fin (m + 1),
      (∫ u in Set.Icc (-1 : ℝ) 1, u ^ (J : ℕ) * (max (1 - u ^ 2) 0 * hpkPoly m c u))
        = (hpkGram m).mulVec c J := by
    intro J
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (f := fun u => u ^ (J : ℕ) * (max (1 - u ^ 2) 0 * hpkPoly m c u))
      (g := fun u => u ^ (J : ℕ) * ((1 - u ^ 2) * hpkPoly m c u))
      (fun u hu => by
        dsimp only
        rw [max_eq_left (by nlinarith [hu.1, hu.2] : (0 : ℝ) ≤ 1 - u ^ 2)])]
    exact hpkExpand m c J
  refine ⟨fun u => max (1 - u ^ 2) 0 * hpkPoly m c u, ?_, ?_, ?_, ?_⟩
  · exact ((continuous_const.sub (continuous_pow 2)).max continuous_const).mul
      (hpkPoly_continuous m c)
  · intro u hu
    have h1 : (1 : ℝ) < u ^ 2 := by nlinarith [hu, sq_abs u, abs_nonneg u]
    dsimp only
    rw [max_eq_right (by linarith : (1 : ℝ) - u ^ 2 ≤ 0), zero_mul]
  · have h0 := hmom 0
    rw [hc, Pi.single_eq_same] at h0
    simp only [Fin.val_zero, pow_zero, one_mul] at h0
    simpa using h0
  · intro j hj1 hjm
    have hJ : j < m + 1 := by omega
    have h0 := hmom ⟨j, hJ⟩
    rw [hc, Pi.single_apply, if_neg (by
      intro h; rw [Fin.ext_iff] at h; simp at h; omega)] at h0
    simpa using h0

/-- A product kernel is uniformly bounded by the coordinatewise bound raised to the
dimension, whenever its one-dimensional factor has that bound. -/
theorem prodKernel_abs_le {d : ℕ} {k : ℝ → ℝ} {B : ℝ}
    (hB : ∀ u, |k u| ≤ B) (u : Fin d → ℝ) :
    |prodKernel k d u| ≤ B ^ d := by
  unfold prodKernel
  rw [Finset.abs_prod]
  calc ∏ i : Fin d, |k (u i)|
      ≤ ∏ _i : Fin d, B :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hB (u i))
    _ = B ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The total mass of a product kernel factorizes into the product of the
one-dimensional masses, so a unit-mass factor yields a unit-mass multivariate kernel. -/
theorem prodKernel_integral {d : ℕ} (k : ℝ → ℝ) :
    ∫ u, prodKernel k d u = (∫ t, k t) ^ d := by
  unfold prodKernel
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (fun _ : Fin d => k)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Each polynomial moment of a product kernel factorizes into the corresponding
one-dimensional moments, allowing any cancelled coordinate moment to cancel the
entire multivariate moment. -/
theorem prodKernel_moment {d : ℕ} (k : ℝ → ℝ) (ν : Fin d → ℕ) :
    (∫ u, (∏ i, u i ^ ν i) * prodKernel k d u) = ∏ i, ∫ t, t ^ ν i * k t := by
  unfold prodKernel
  have hfac : (fun u : Fin d → ℝ => (∏ i, u i ^ ν i) * ∏ i, k (u i))
      = fun u : Fin d → ℝ => ∏ i, (u i ^ ν i * k (u i)) := by
    funext u; rw [← Finset.prod_mul_distrib]
  rw [hfac]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
        (fun i : Fin d => fun t => t ^ ν i * k t)]

end Causalean.Stat.Nonparametric
