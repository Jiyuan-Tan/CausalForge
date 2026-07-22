/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.PopulationTarget
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Conditional expectations as squared-loss population targets

This file is part of the causal-application layer of `Causalean.ML`: files under
`Causalean/ML/CausalApplication/` may import causal and estimation modules, while the
`Causalean/ML/` core remains causal-free.

The ML population-target keystone
(`square_loss_population_target_of_isL2Projection`) is stated for a function whose
residual is orthogonal to every function of the covariate (`IsL2Projection`).
Here we connect that to Mathlib's `condExp`: the conditional mean `E[Y ∣ X]` is
exactly such a projection.  This lets a known causal nuisance (defined via
`condExp`, as in `Estimation.ATE.BackdoorEstimationSystem.μ_compat`) be recognized
as the ML squared-loss population minimizer, and vice versa.
-/

namespace Causalean.ML.Causal

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- The covariate sigma-algebra records exactly the information carried by the
covariate in a joint covariate-response observation. -/
def covarSigma : MeasurableSpace (X × ℝ) := MeasurableSpace.comap Prod.fst inferInstance

/-- The covariate sigma-algebra is a sub-sigma-algebra of the full joint
observation sigma-algebra. -/
lemma covarSigma_le : covarSigma (X := X) ≤ (inferInstance : MeasurableSpace (X × ℝ)) := by
  exact measurable_fst.comap_le

/-- A conditional mean of the response given the covariate is an L² projection of
the response onto functions of the covariate.

Equivalently, the residual from this regression function is uncorrelated with
every integrable covariate-only function. -/
theorem isL2Projection_of_condExp
    (P : Measure (X × ℝ)) [IsFiniteMeasure P] {m : X → ℝ} (hm : Measurable m)
    (hY : Integrable (fun z => z.2) P)
    (hcond : (fun z => m z.1)
      =ᵐ[P] (P[fun z => z.2 | covarSigma (X := X)])) :
    Causalean.ML.IsL2Projection P m := by
  intro g hgm hg
  have hF : covarSigma (X := X) ≤ (inferInstance : MeasurableSpace (X × ℝ)) :=
    covarSigma_le (X := X)
  have hfst : Measurable[covarSigma (X := X)] (fun z : X × ℝ => z.1) := by
    rw [measurable_iff_comap_le]
    exact le_rfl
  have hM_sm : StronglyMeasurable[covarSigma (X := X)] (fun z : X × ℝ => m z.1) := by
    exact (hm.comp hfst).stronglyMeasurable
  have hG_sm : StronglyMeasurable[covarSigma (X := X)] (fun z : X × ℝ => g z.1) := by
    exact (hgm.comp hfst).stronglyMeasurable
  have hM_int : Integrable (fun z : X × ℝ => m z.1) P := by
    exact (MeasureTheory.integrable_condExp (μ := P) (m := covarSigma (X := X))
      (f := fun z : X × ℝ => z.2)).congr hcond.symm
  have hres_int : Integrable (fun z : X × ℝ => z.2 - m z.1) P := hY.sub hM_int
  have hM_ce :
      P[(fun z : X × ℝ => m z.1) | covarSigma (X := X)] =
        (fun z : X × ℝ => m z.1) := by
    exact MeasureTheory.condExp_of_stronglyMeasurable hF hM_sm hM_int
  have hres_ce :
      P[(fun z : X × ℝ => z.2 - m z.1) | covarSigma (X := X)] =ᵐ[P] 0 := by
    calc
      P[(fun z : X × ℝ => z.2 - m z.1) | covarSigma (X := X)]
          =ᵐ[P] P[(fun z : X × ℝ => z.2) | covarSigma (X := X)] -
              P[(fun z : X × ℝ => m z.1) | covarSigma (X := X)] :=
        MeasureTheory.condExp_sub (μ := P) (m := covarSigma (X := X)) hY hM_int
      _ =ᵐ[P] P[(fun z : X × ℝ => z.2) | covarSigma (X := X)] -
              (fun z : X × ℝ => m z.1) := by
        rw [hM_ce]
      _ =ᵐ[P] 0 := by
        filter_upwards [hcond] with z hz
        change P[(fun z : X × ℝ => z.2) | covarSigma (X := X)] z - m z.1 = 0
        rw [← hz]
        simp
  have hprod_ce :
      P[(fun z : X × ℝ => (z.2 - m z.1) * g z.1) | covarSigma (X := X)] =ᵐ[P] 0 := by
    calc
      P[(fun z : X × ℝ => (z.2 - m z.1) * g z.1) | covarSigma (X := X)]
          =ᵐ[P]
            P[(fun z : X × ℝ => z.2 - m z.1) | covarSigma (X := X)] *
              (fun z : X × ℝ => g z.1) :=
        MeasureTheory.condExp_mul_of_stronglyMeasurable_right (μ := P)
          (m := covarSigma (X := X))
          (f := fun z : X × ℝ => z.2 - m z.1) (g := fun z : X × ℝ => g z.1)
          hG_sm hg hres_int
      _ =ᵐ[P] 0 := by
        filter_upwards [hres_ce] with z hz
        change P[(fun z : X × ℝ => z.2 - m z.1) | covarSigma (X := X)] z *
          g z.1 = 0
        rw [hz]
        simp
  calc
    ∫ z, (z.2 - m z.1) * g z.1 ∂P =
        ∫ z, (P[(fun z : X × ℝ => (z.2 - m z.1) * g z.1) |
          covarSigma (X := X)]) z ∂P := by
      exact (MeasureTheory.integral_condExp hF (μ := P)
        (f := fun z : X × ℝ => (z.2 - m z.1) * g z.1)).symm
    _ = ∫ z, (0 : ℝ) ∂P := by
      exact integral_congr_ae hprod_ce
    _ = 0 := by
      simp

/-- An L² projection of the response onto functions of the covariate is a
conditional mean of the response given the covariate.

Together with the forward direction, this gives the full equivalence connecting
the squared-loss population target to the regression-function nuisance. -/
theorem condExp_of_isL2Projection
    (P : Measure (X × ℝ)) [IsFiniteMeasure P] {m : X → ℝ} (hm : Measurable m)
    (hY : Integrable (fun z => z.2) P) (hmint : Integrable (fun z => m z.1) P)
    (hproj : Causalean.ML.IsL2Projection P m) :
    (fun z => m z.1) =ᵐ[P] (P[fun z => z.2 | covarSigma (X := X)]) := by
  have hF : covarSigma (X := X) ≤ (inferInstance : MeasurableSpace (X × ℝ)) :=
    covarSigma_le (X := X)
  haveI : IsFiniteMeasure (P.trim hF) := isFiniteMeasure_trim hF
  haveI : SigmaFinite (P.trim hF) := inferInstance
  have hfst : Measurable[covarSigma (X := X)] (fun z : X × ℝ => z.1) := by
    rw [measurable_iff_comap_le]
    exact le_rfl
  have hM_aesm :
      AEStronglyMeasurable[covarSigma (X := X)] (fun z : X × ℝ => m z.1) P := by
    exact (hm.comp hfst).stronglyMeasurable.aestronglyMeasurable
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hF hY
    (fun _s _hs _hfin => hmint.integrableOn) ?_ hM_aesm
  intro s hs hfin
  have hs_ambient : MeasurableSet s := hF _ hs
  change MeasurableSet[MeasurableSpace.comap Prod.fst inferInstance] s at hs
  obtain ⟨A, hA, hAeq⟩ := hs
  let g₀ : X → ℝ := Set.indicator A (fun _ => (1 : ℝ))
  have hg₀ : Measurable g₀ := by
    exact measurable_const.indicator hA
  have hres_int : Integrable (fun z : X × ℝ => z.2 - m z.1) P := hY.sub hmint
  have hprod_eq_indicator :
      (fun z : X × ℝ => (z.2 - m z.1) * g₀ z.1)
        = s.indicator (fun z : X × ℝ => z.2 - m z.1) := by
    funext z
    by_cases hz : z ∈ s
    · have hzA : z.1 ∈ A := by
        rw [← hAeq] at hz
        exact hz
      simp [g₀, Set.indicator_of_mem hz, Set.indicator_of_mem hzA]
    · have hzA : z.1 ∉ A := by
        intro hzA
        exact hz (by
          rw [← hAeq]
          exact hzA)
      simp [g₀, Set.indicator_of_notMem hz, Set.indicator_of_notMem hzA]
  have hg₀int : Integrable (fun z : X × ℝ => (z.2 - m z.1) * g₀ z.1) P := by
    simpa [hprod_eq_indicator] using hres_int.indicator hs_ambient
  have horth : ∫ z, (z.2 - m z.1) * g₀ z.1 ∂P = 0 := hproj g₀ hg₀ hg₀int
  have hres_set_zero : ∫ z in s, z.2 - m z.1 ∂P = 0 := by
    rw [← MeasureTheory.integral_indicator (μ := P) hs_ambient, ← hprod_eq_indicator]
    exact horth
  have hsubeq : ∫ z in s, z.2 ∂P - ∫ z in s, m z.1 ∂P = 0 := by
    rw [← MeasureTheory.integral_sub hY.integrableOn hmint.integrableOn]
    exact hres_set_zero
  exact (sub_eq_zero.mp hsubeq).symm

end Causalean.ML.Causal
