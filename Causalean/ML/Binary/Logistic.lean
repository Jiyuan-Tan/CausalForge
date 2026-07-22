/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-! # Logistic regression — convexity and existence

Binary logistic regression with score `⟪β, x⟫` and the score-space log-loss
`logisticScoreLoss`.  This file proves that the score-space loss and the
empirical logistic risk are convex, and that an empirical-risk minimizer exists
on any nonempty compact parameter set.
-/

namespace Causalean.ML

open BigOperators

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma hasDerivAt_softplus (x : ℝ) : HasDerivAt softplus (Real.sigmoid x) x := by
  unfold softplus
  have harg : 1 + Real.exp x ≠ 0 := by positivity
  have h := (Real.hasDerivAt_log harg).comp x
    ((hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_exp x))
  convert h using 1
  rw [Real.sigmoid_def]
  field_simp [Real.exp_ne_zero]
  ring_nf
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  ring

private theorem continuous_softplus : Continuous softplus := by
  exact continuous_iff_continuousAt.2 fun x => (hasDerivAt_softplus x).continuousAt

/-- The empirical logistic risk at coefficient `β`: average score-space log-loss
over the sample `Z`. -/
noncomputable def logisticEmpRisk (Z : ι → E × Bool) (β : E) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, logisticScoreLoss (Z i).2 (inner ℝ β (Z i).1)

/-- Softplus is convex. -/
theorem convexOn_softplus : ConvexOn ℝ Set.univ softplus := by
  have hdiff : Differentiable ℝ softplus := fun x => (hasDerivAt_softplus x).differentiableAt
  have hderiv : deriv softplus = Real.sigmoid :=
    funext fun x => (hasDerivAt_softplus x).deriv
  exact Monotone.convexOn_univ_of_deriv hdiff (by simpa [hderiv] using Real.sigmoid_monotone)

/-- The score-space logistic loss is convex in the score. -/
theorem convexOn_logisticScoreLoss (y : Bool) :
    ConvexOn ℝ Set.univ (fun t : ℝ => logisticScoreLoss y t) := by
  let lin : ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun t => -bool01 y * t
      map_add' := by
        intro a b
        ring
      map_smul' := by
        intro c a
        simp [smul_eq_mul]
        ring }
  have hlin : ConvexOn ℝ Set.univ (fun t : ℝ => -bool01 y * t) := by
    simpa [Function.comp_def, lin] using (convexOn_id convex_univ).comp_linearMap lin
  simpa [logisticScoreLoss, sub_eq_add_neg] using (convexOn_softplus.add hlin)

/-- The empirical logistic risk is convex in the coefficient. -/
theorem convexOn_logisticEmpRisk (Z : ι → E × Bool) :
    ConvexOn ℝ Set.univ (logisticEmpRisk Z) := by
  classical
  unfold logisticEmpRisk
  have hsummand : ∀ i : ι,
      ConvexOn ℝ Set.univ (fun β : E => logisticScoreLoss (Z i).2 (inner ℝ β (Z i).1)) := by
    intro i
    exact convexOn_comp_inner (convexOn_logisticScoreLoss (Z i).2) (Z i).1
  have hfin : ∀ t : Finset ι,
      ConvexOn ℝ Set.univ
        (fun β : E => t.sum fun i => logisticScoreLoss (Z i).2 (inner ℝ β (Z i).1)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simpa using
          (convexOn_const (𝕜 := ℝ) (E := E) (β := ℝ)
            (s := Set.univ) (0 : ℝ) convex_univ)
    | insert i t hi ht =>
        simpa [Finset.sum_insert hi, Pi.add_apply] using (hsummand i).add ht
  simpa [smul_eq_mul] using
    (hfin Finset.univ).smul (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card ι)))

/-- The empirical logistic risk is continuous. -/
theorem continuous_logisticEmpRisk (Z : ι → E × Bool) :
    Continuous (logisticEmpRisk Z) := by
  classical
  unfold logisticEmpRisk
  have hscore : ∀ y : Bool, Continuous (fun t : ℝ => logisticScoreLoss y t) := by
    intro y
    simpa [logisticScoreLoss] using
      continuous_softplus.sub (continuous_const.mul continuous_id)
  have hterm : ∀ i : ι,
      Continuous (fun β : E => logisticScoreLoss (Z i).2 (inner ℝ β (Z i).1)) := by
    intro i
    have hinner : Continuous (fun β : E => inner ℝ β (Z i).1) := by
      simpa using continuous_inner.comp (continuous_id.prodMk continuous_const)
    exact (hscore (Z i).2).comp hinner
  have hsum : Continuous (fun β : E =>
      ∑ i, logisticScoreLoss (Z i).2 (inner ℝ β (Z i).1)) := by
    exact continuous_finset_sum Finset.univ fun i _ => hterm i
  simpa using (continuous_const.mul hsum)

/-- A logistic-risk minimizer exists on any nonempty compact parameter set. -/
theorem logistic_exists_minimizer_on_compact (Z : ι → E × Bool)
    {Θset : Set E} (hne : Θset.Nonempty) (hcompact : IsCompact Θset) :
    ∃ βhat ∈ Θset, IsMinOn (logisticEmpRisk Z) Θset βhat :=
  exists_isMinOn_of_isCompact hne hcompact (continuous_logisticEmpRisk Z).continuousOn

end Causalean.ML
