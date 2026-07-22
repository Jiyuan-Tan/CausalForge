/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The standard Gaussian measure on a finite-dimensional inner-product space

This file constructs the standard Gaussian measure `stdGaussian E` on an arbitrary
finite-dimensional real inner-product space `E` (mean zero, covariance equal to the
inner product) and records three basic facts about it.

## Construction

Let `n := Module.finrank ℝ E` and fix the standard orthonormal basis
`b : OrthonormalBasis (Fin n) ℝ E`, whose `b.repr : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)`
is a linear isometry equivalence.  On `Fin n → ℝ` we take the product of standard real
Gaussians `Measure.pi (fun _ ↦ gaussianReal 0 1)`, push it through `toLp 2` to land on
`EuclideanSpace ℝ (Fin n)`, and finally pull it back to `E` along the isometry inverse
`b.repr.symm`.

## Main definitions / results

* `Causalean.Mathlib.stdGaussian E` — the standard Gaussian measure on `E`.
* instances `IsProbabilityMeasure (stdGaussian E)` and `IsGaussian (stdGaussian E)`.
* `Causalean.Mathlib.stdGaussian_mean` — its mean is `0`.
* `Causalean.Mathlib.covarianceBilin_stdGaussian` — its covariance bilinear form is the
  inner product: `covarianceBilin (stdGaussian E) u v = ⟪u, v⟫_ℝ`.
-/
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Independence.Basic

/-! # Standard Gaussian Measures

This file constructs the standard Gaussian probability measure on an arbitrary
finite-dimensional real inner-product space and proves its mean, Gaussianity, and
covariance form. It also identifies the law of the squared norm with the sum of
squared independent one-dimensional standard Gaussians. The construction gives
downstream statistical modules a basis-independent Gaussian law with covariance
equal to the inner product. -/

open MeasureTheory ProbabilityTheory InnerProductSpace WithLp
open scoped RealInnerProductSpace

namespace Causalean.Mathlib

attribute [local instance] Fintype.ofFinite

section Defs

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The chosen orthonormal basis of `E`. -/
private noncomputable def onb : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  stdOrthonormalBasis ℝ E

/-- The base product measure on `Fin n → ℝ`: `n` independent standard real Gaussians. -/
private noncomputable def piGaussian :
    Measure (Fin (Module.finrank ℝ E) → ℝ) :=
  Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)

/-- The product standard Gaussian transported to `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def euclideanStdGaussian :
    Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  (piGaussian E).map (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm

/-- The standard Gaussian measure on a finite-dimensional real inner-product space
`E`: covariance equal to the identity (inner product), mean zero. -/
noncomputable def stdGaussian : Measure E :=
  (euclideanStdGaussian E).map (onb E).repr.symm.toContinuousLinearEquiv

end Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The product of independent one-dimensional standard Gaussian laws is a probability
measure. -/
instance isProbabilityMeasure_piGaussian : IsProbabilityMeasure (piGaussian E) := by
  unfold piGaussian; infer_instance

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Each coordinate is `MemLp` of order 2 under the product measure. -/
private lemma memLp_eval (i : Fin (Module.finrank ℝ E)) :
    MemLp (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i) 2 (piGaussian E) := by
  have : MemLp id 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 2 (by simp)
  exact this.comp_measurePreserving (measurePreserving_eval _ i)

/-- The product standard Gaussian on `Fin n → ℝ` is Gaussian. -/
instance isGaussian_piGaussian : IsGaussian (piGaussian E) := by
  have hIndep : iIndepFun (fun (i : Fin (Module.finrank ℝ E))
      (ω : Fin (Module.finrank ℝ E) → ℝ) => ω i) (piGaussian E) :=
    iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hLaw : ∀ i, HasGaussianLaw
      (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i) (piGaussian E) := by
    intro i
    classical
    have hmap : (piGaussian E).map (fun ω => ω i) = gaussianReal 0 1 := by
      unfold piGaussian
      rw [show (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i)
          = Function.eval i from rfl, Measure.pi_map_eval]
      simp
    refine ⟨?_⟩
    rw [hmap]; infer_instance
  have hJoint : IsGaussian
      ((piGaussian E).map (fun ω => (fun i => ω i :
        Fin (Module.finrank ℝ E) → ℝ))) :=
    (hIndep.hasGaussianLaw hLaw).isGaussian_map
  simpa using hJoint

/-- The transported product standard Gaussian on Euclidean space is a probability measure. -/
instance isProbabilityMeasure_euclideanStdGaussian :
    IsProbabilityMeasure (euclideanStdGaussian E) := by
  unfold euclideanStdGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The standard Gaussian measure on the inner-product space is a probability measure. -/
instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) := by
  unfold stdGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The product standard Gaussian on `EuclideanSpace ℝ (Fin n)` is Gaussian. -/
instance isGaussian_euclideanStdGaussian : IsGaussian (euclideanStdGaussian E) := by
  unfold euclideanStdGaussian
  exact isGaussian_map_equiv _

/-- The standard Gaussian measure on the inner-product space is a Gaussian law. -/
instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  unfold stdGaussian
  exact isGaussian_map_equiv _

/-- Pushing the mean through a continuous linear equivalence. -/
private lemma integral_id_map_equiv {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    {μ : Measure F} (L : F ≃L[ℝ] G) :
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
  rw [integral_map (φ := L) (f := fun x => x) (by fun_prop)
    (aestronglyMeasurable_id.congr (by rfl))]
  exact L.integral_comp_comm (fun x => x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The mean of `piGaussian` is the zero vector. -/
private lemma integral_piGaussian : ∫ x, x ∂(piGaussian E) = 0 := by
  have hint : Integrable (id : (Fin (Module.finrank ℝ E) → ℝ) → _) (piGaussian E) :=
    (isGaussian_piGaussian (E := E)).integrable_id
  classical
  funext i
  have happly := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.proj i : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ) hint
  simp only [ContinuousLinearMap.proj_apply, id_eq, Pi.zero_apply] at happly ⊢
  rw [← happly]
  have hmap : (piGaussian E).map (fun ω => ω i) = gaussianReal 0 1 := by
    unfold piGaussian
    rw [show (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i)
        = Function.eval i from rfl, Measure.pi_map_eval]
    simp
  have heq : ∫ x, x i ∂(piGaussian E) = ∫ y, y ∂((piGaussian E).map (fun ω => ω i)) :=
    (integral_map (φ := fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i) (f := fun y : ℝ => y)
      (measurable_pi_apply i).aemeasurable (aestronglyMeasurable_id.congr (by rfl))).symm
  rw [heq, hmap]
  simp [integral_id_gaussianReal]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The mean of `euclideanStdGaussian` is the zero vector. -/
private lemma integral_euclideanStdGaussian : ∫ x, x ∂(euclideanStdGaussian E) = 0 := by
  unfold euclideanStdGaussian
  rw [integral_id_map_equiv, integral_piGaussian]
  simp

/-- The standard Gaussian measure on a finite-dimensional real inner-product space has mean
zero. -/
theorem stdGaussian_mean : ∫ x, x ∂(stdGaussian E) = 0 := by
  unfold stdGaussian
  rw [integral_id_map_equiv, integral_euclideanStdGaussian]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The variance of a single coordinate is `1`. -/
private lemma variance_eval (i : Fin (Module.finrank ℝ E)) :
    Var[fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i; piGaussian E] = 1 := by
  classical
  have hmap : (piGaussian E).map (fun ω => ω i) = gaussianReal 0 1 := by
    unfold piGaussian
    rw [show (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i)
        = Function.eval i from rfl, Measure.pi_map_eval]
    simp
  have hvm : Var[(id : ℝ → ℝ); (piGaussian E).map (fun ω => ω i)]
      = Var[(id : ℝ → ℝ) ∘ (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i); piGaussian E] :=
    variance_map (by fun_prop) (measurable_pi_apply i).aemeasurable
  rw [hmap] at hvm
  rw [show (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i)
      = (id : ℝ → ℝ) ∘ (fun ω => ω i) from rfl, ← hvm]
  simp [variance_id_gaussianReal]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The coordinatewise covariance of `piGaussian` is the Kronecker delta. -/
private lemma cov_eval (i j : Fin (Module.finrank ℝ E)) :
    cov[fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i,
      fun ω => ω j; piGaussian E] = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← variance_eval (E := E) i, covariance_self]
    exact (memLp_eval (E := E) i).aestronglyMeasurable.aemeasurable
  · rw [if_neg hij]
    have hIndep : iIndepFun (fun (i : Fin (Module.finrank ℝ E))
        (ω : Fin (Module.finrank ℝ E) → ℝ) => ω i) (piGaussian E) :=
      iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
    exact (hIndep.indepFun hij).covariance_eq_zero (memLp_eval (E := E) i)
      (memLp_eval (E := E) j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The covariance bilinear form of `euclideanStdGaussian` is the Euclidean inner product. -/
private lemma covarianceBilin_euclideanStdGaussian
    (x y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covarianceBilin (euclideanStdGaussian E) x y = ⟪x, y⟫ := by
  classical
  have hmemLp : ∀ i, MemLp (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i) 2 (piGaussian E) :=
    fun i => memLp_eval (E := E) i
  have hform : euclideanStdGaussian E
      = (piGaussian E).map (fun ω => WithLp.toLp 2 ((fun i => ω i) ·)) := rfl
  rw [hform, covarianceBilin_apply_pi hmemLp, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [cov_eval (E := E), if_pos rfl, mul_one, real_inner_comm]; rfl
  · intro j _ hji
    rw [cov_eval (E := E), if_neg (fun h => hji h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The covariance bilinear form of the standard Gaussian measure is the ambient inner
product. -/
theorem covarianceBilin_stdGaussian (u v : E) :
    covarianceBilin (stdGaussian E) u v = (inner ℝ u v : ℝ) := by
  have hmemLp : MemLp id 2 (euclideanStdGaussian E) :=
    (isGaussian_euclideanStdGaussian (E := E)).memLp_two_id
  set L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E :=
    (onb E).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap with hL
  have hmeas : stdGaussian E = (euclideanStdGaussian E).map L := rfl
  rw [hmeas, covarianceBilin_map hmemLp]
  have hadj : L.adjoint = ((onb E).repr : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    rw [hL]
    have h := (onb E).repr.symm.adjoint_eq_symm
    simp only [LinearIsometryEquiv.symm_symm] at h
    convert h using 2
  rw [hadj, covarianceBilin_euclideanStdGaussian]
  exact (onb E).repr.inner_map_map u v

/-- **Product-of-1-D-Gaussians model for the squared norm.**  The law of `‖·‖²`
under `stdGaussian E` is the law of the sum of squared coordinates under a
product of `finrank ℝ E` independent standard real Gaussians.  This exposes the
explicit product structure (otherwise hidden behind the orthonormal-basis
construction) needed to prove atomlessness of the χ² law. -/
theorem stdGaussian_map_normSq_eq_pi :
    (stdGaussian E).map (fun x => ‖x‖ ^ 2)
      = (Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)).map
          (fun w => ∑ i, (w i) ^ 2) := by
  -- `stdGaussian = euclideanStdGaussian.map repr.symm`, and `repr.symm` is an isometry
  rw [stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have h1 : (fun x => ‖x‖ ^ 2) ∘ ⇑(onb E).repr.symm.toContinuousLinearEquiv
      = fun y => ‖y‖ ^ 2 := by
    funext y
    simp only [Function.comp_apply]
    rw [show (onb E).repr.symm.toContinuousLinearEquiv y = (onb E).repr.symm y from rfl,
      (onb E).repr.symm.norm_map]
  rw [h1, euclideanStdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  refine Measure.map_congr (ae_of_all _ fun w => ?_)
  simp only [Function.comp_apply]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  congr 1

end Causalean.Mathlib
