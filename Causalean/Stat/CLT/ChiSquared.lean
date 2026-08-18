/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The χ²_d distribution as the law of the squared norm of a standard Gaussian

The chi-squared distribution with `d` degrees of freedom is *defined* here as the
law of `‖W‖²` where `W` is the standard `d`-dimensional Gaussian
(`Causalean/Mathlib/StandardGaussian.lean`, `stdGaussian`).  This is the textbook
definition (sum of `d` independent squared standard normals) and is exactly the
target produced by whitening the multivariate-CLT Gaussian limit through a Wald
quadratic form (`Causalean/Stat/ChiSquaredWald.lean`).

The connection to the `Gamma(d/2, 1/2)` density (`ProbabilityTheory.gammaMeasure`)
is a separate, much deeper analytic fact and is *not* developed here; Mathlib has
no chi-squared distribution.

Key declarations:

* `chiSqDist d` — the χ²_d law on `ℝ`, `(stdGaussian (EuclideanSpace ℝ (Fin d))).map ‖·‖²`.
* `IsProbabilityMeasure (chiSqDist d)`.
* `stdGaussian_map_linearIsometryEquiv` — `stdGaussian` is invariant under linear
  isometry equivalences (proved via characteristic functions).
* `stdGaussian_map_normSq` — the law of `‖·‖²` under `stdGaussian E` depends only
  on `finrank E`, equalling `chiSqDist (finrank ℝ E)`.
* `noAtoms_chiSqDist` — `χ²_d` has no atoms for `d ≥ 1`.
-/
import Causalean.Stat.CLT.GaussianCharFunBridge
import Causalean.Mathlib.StandardGaussian

/-! # Chi-Squared Distribution

This file defines the chi-squared distribution with $d$ degrees of freedom as
the law of the squared norm of a standard $d$-dimensional Gaussian vector. It
establishes invariance and no-atom facts needed for Wald limit distributions.

The main declarations are `chiSqDist`, the probability-measure instance for
that law, `stdGaussian_map_linearIsometryEquiv`, the dimension-only identity
`stdGaussian_map_normSq`, and the no-atom theorems `noAtoms_pi_normSq` and
`noAtoms_chiSqDist`. -/

open MeasureTheory ProbabilityTheory Complex Causalean.Mathlib
open scoped RealInnerProductSpace

namespace Causalean.Stat

/-- The chi-squared distribution with `d` degrees of freedom: the law of the
squared norm of the standard `d`-dimensional Gaussian. -/
noncomputable def chiSqDist (d : ℕ) : Measure ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun w => ‖w‖ ^ 2)

/-- The chi-squared distribution is a probability law. -/
instance (d : ℕ) : IsProbabilityMeasure (chiSqDist d) := by
  unfold chiSqDist
  exact Measure.isProbabilityMeasure_map (by fun_prop)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **`stdGaussian` is invariant under linear isometry equivalences.**  Pushing
the standard Gaussian forward along an inner-product isometry yields the standard
Gaussian on the target.  Proved by matching characteristic functions: both sides
are centered Gaussians whose covariance form is the inner product (preserved by
the isometry). -/
theorem stdGaussian_map_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ι : E ≃ₗᵢ[ℝ] F) :
    (stdGaussian E).map ι = stdGaussian F := by
  set L : E →L[ℝ] F := (ι : E →L[ℝ] F) with hL
  have hmapL : (stdGaussian E).map ι = (stdGaussian E).map L := rfl
  haveI : IsGaussian ((stdGaussian E).map L) := by
    rw [← hmapL]; exact isGaussian_map_equiv ι.toContinuousLinearEquiv
  -- mean of the pushforward is `0`
  have hmean_map : ∫ x, x ∂((stdGaussian E).map L) = 0 := by
    have hstep : ∫ x, x ∂((stdGaussian E).map L) = L (∫ x, x ∂(stdGaussian E)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      exact ContinuousLinearMap.integral_comp_comm L IsGaussian.integrable_id
    rw [hstep, stdGaussian_mean, map_zero]
  refine Measure.ext_of_charFun ?_
  funext t
  have hmemLp : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hcoveq : covarianceBilin ((stdGaussian E).map L) t t
      = covarianceBilin (stdGaussian F) t t := by
    rw [covarianceBilin_map hmemLp, ι.adjoint_eq_symm, covarianceBilin_stdGaussian,
      covarianceBilin_stdGaussian]
    exact ι.symm.inner_map_map t t
  rw [hmapL, charFun_isGaussian_centered _ hmean_map t,
    charFun_isGaussian_centered _ stdGaussian_mean t, hcoveq]

/-- [The law of the squared norm under the standard Gaussian distribution on a
finite-dimensional real inner product space equals the chi-squared distribution
whose degrees of freedom is the space's dimension](goal). -/
theorem stdGaussian_map_normSq :
    (stdGaussian E).map (fun x => ‖x‖ ^ 2) = chiSqDist (Module.finrank ℝ E) := by
  classical
  set d := Module.finrank ℝ E with hd
  -- the standard orthonormal basis gives an isometry `E ≃ₗᵢ EuclideanSpace ℝ (Fin d)`
  set ι : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := (stdOrthonormalBasis ℝ E).repr with hι
  rw [chiSqDist, ← stdGaussian_map_linearIsometryEquiv ι,
    Measure.map_map (by fun_prop) (by fun_prop)]
  refine Measure.map_congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply]
  rw [ι.norm_map]

/-- The law of the sum of `n ≥ 1` squared independent standard normals has no
atoms.  The squared first coordinate already has an atomless law (its preimage
under squaring is finite, and `gaussianReal` is atomless), and adding the
independent remainder preserves atomlessness via Fubini. -/
theorem noAtoms_pi_normSq {n : ℕ} (hn : 1 ≤ n) :
    NullSingletonClass ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
      (fun w => ∑ i, (w i) ^ 2)) := by
  classical
  haveI hG : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  refine ⟨fun c => ?_⟩
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton c)]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- Split off coordinate `0` via the measure-preserving equiv.
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0
  -- The squared-norm level set is the preimage of a product level set.
  have hset : (fun w : Fin (m + 1) → ℝ => ∑ i, w i ^ 2) ⁻¹' {c}
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0) ⁻¹'
        {p : ℝ × (Fin m → ℝ) | p.1 ^ 2 + ∑ j, (p.2 j) ^ 2 = c} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      MeasurableEquiv.piFinSuccAbove_apply]
    rw [Fin.sum_univ_succAbove (fun i => w i ^ 2) 0]
    rfl
  rw [hset, hmp.measure_preimage_equiv]
  -- Integrate the atomless first coordinate; the inner fibre is finite.
  have hms : MeasurableSet {p : ℝ × (Fin m → ℝ) | p.1 ^ 2 + ∑ j, (p.2 j) ^ 2 = c} := by
    apply measurableSet_eq_fun <;> fun_prop
  rw [Measure.prod_apply_symm hms]
  -- Each fibre `{a | a^2 + s = c}` is finite, hence null under the atomless Gaussian.
  have hfib : ∀ y : Fin m → ℝ,
      (gaussianReal 0 1) ((fun a : ℝ => (a, y)) ⁻¹'
        {p : ℝ × (Fin m → ℝ) | p.1 ^ 2 + ∑ j, (p.2 j) ^ 2 = c}) = 0 := by
    intro y
    have hfin : {a : ℝ | a ^ 2 + ∑ j, (y j) ^ 2 = c}.Finite := by
      apply Set.Finite.subset
        ((Set.finite_singleton (-Real.sqrt (c - ∑ j, (y j) ^ 2))).insert
          (Real.sqrt (c - ∑ j, (y j) ^ 2)))
      intro a ha
      simp only [Set.mem_setOf_eq] at ha
      have hsq : a ^ 2 = c - ∑ j, (y j) ^ 2 := by linarith
      have hnn : 0 ≤ c - ∑ j, (y j) ^ 2 := by rw [← hsq]; positivity
      have : a = Real.sqrt (c - ∑ j, (y j) ^ 2) ∨ a = -Real.sqrt (c - ∑ j, (y j) ^ 2) := by
        rcases le_or_gt 0 a with h | h
        · left
          rw [← hsq, Real.sqrt_sq h]
        · right
          rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_neg h, neg_neg]
      simpa [Set.mem_insert_iff] using this
    have hset_eq : (fun a : ℝ => (a, y)) ⁻¹'
        {p : ℝ × (Fin m → ℝ) | p.1 ^ 2 + ∑ j, (p.2 j) ^ 2 = c}
        = {a : ℝ | a ^ 2 + ∑ j, (y j) ^ 2 = c} := by
      ext a; simp
    rw [hset_eq]
    exact hfin.measure_zero _
  simp_rw [hfib, lintegral_zero]

/-- **`χ²_d` has no atoms for `d ≥ 1`.** -/
theorem noAtoms_chiSqDist {d : ℕ} (hd : 1 ≤ d) : NullSingletonClass (chiSqDist d) := by
  rw [chiSqDist, stdGaussian_map_normSq_eq_pi]
  exact noAtoms_pi_normSq (by rwa [finrank_euclideanSpace_fin])

end Causalean.Stat
