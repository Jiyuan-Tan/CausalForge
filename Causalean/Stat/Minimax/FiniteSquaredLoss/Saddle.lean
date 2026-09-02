/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.FiniteSquaredLoss.Mixing
import Mathlib.Topology.Sion

/-!
# Sion saddle point and finite squared-loss minimax attainment

This module applies Sion's minimax theorem to convexified finite risk vectors and
finite priors, recovers an ordinary procedure by conditional Jensen, and bridges
the saddle value to Causalean's `minimaxValue` and `FiniteDesign.E` APIs.
-/

open scoped BigOperators
open Set

namespace Causalean.Stat.Minimax.FiniteSquaredLoss

open Causalean.Experimentation.DesignBased
open Causalean.Stat

variable {Theta R : Type*} [Fintype Theta] [Fintype R]
variable {X : R → Type*} [∀ r, Fintype (X r)]

/-- For nonempty finite state and design spaces, given [likelihood coefficients](hyp:P) and
[an ordered action interval](hyp:hlu), the convexified risk game [has an attaining saddle point consisting of a risk vector and
a finite prior](goal). -/
theorem convexified_risk_game_has_saddle [Nonempty Theta] [Nonempty R]
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    {l u : ℝ} (hlu : l ≤ u) :
    ∃ zstar ∈ convexHull ℝ (riskVector P tau '' procedureSet X l u),
      ∃ nustar ∈ stdSimplex ℝ Theta,
        IsSaddlePointOn
          (convexHull ℝ (riskVector P tau '' procedureSet X l u))
          (stdSimplex ℝ Theta) bayesPayoff zstar nustar := by
  /- Apply `Sion.exists_isSaddlePointOn`. The risk hull and prior simplex are
  nonempty, compact, and convex. The bilinear finite-sum payoff is continuous,
  convex in the risk vector, and concave in the prior. -/
  classical
  let K := convexHull ℝ (riskVector P tau '' procedureSet X l u)
  let S := stdSimplex ℝ Theta
  have hK_ne : K.Nonempty := by
    apply Set.Nonempty.convexHull
    exact (procedureSet_nonempty (X := X) hlu).image (riskVector P tau)
  have hS_ne : S.Nonempty :=
    ⟨Pi.single (Classical.choice inferInstance) 1,
      single_mem_stdSimplex ℝ (Classical.choice inferInstance)⟩
  apply Sion.exists_isSaddlePointOn hK_ne (convex_convexHull ℝ _)
    (isCompact_convexHull_riskVectors P tau l u)
  · intro nu hnu
    have hsec : Continuous (fun z ↦ bayesPayoff z nu) :=
      continuous_bayesPayoff.comp (continuous_id.prodMk continuous_const)
    exact hsec.continuousOn.lowerSemicontinuousOn
  · intro nu hnu
    apply ConvexOn.quasiconvexOn
    refine ⟨convex_convexHull ℝ _, ?_⟩
    intro z hz w hw a b ha hb hab
    simp only [bayesPayoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro theta htheta
    ring
  · exact convex_stdSimplex ℝ Theta
  · exact hS_ne
  · exact isCompact_stdSimplex ℝ Theta
  · intro z hz
    have hsec : Continuous (fun nu ↦ bayesPayoff z nu) :=
      continuous_bayesPayoff.comp (continuous_const.prodMk continuous_id)
    exact hsec.continuousOn.upperSemicontinuousOn
  · intro z hz
    apply ConcaveOn.quasiconcaveOn
    refine ⟨convex_stdSimplex ℝ Theta, ?_⟩
    intro nu hnu mu hmu a b ha hb hab
    simp only [bayesPayoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro theta htheta
    ring

/-- Given [nonnegative](hyp:hP) [likelihood coefficients](hyp:P), [an ordered action interval](hyp:hlu),
and [a saddle point in the feasible convexified game](hyp:hz,hnu,hs), its Bayes payoff
[equals Causalean's minimax value over ordinary bounded finite procedures](goal). -/
theorem saddle_value_eq_minimaxValue [Nonempty Theta] [Nonempty R]
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (hP : ∀ theta r x, 0 ≤ P theta r x) {l u : ℝ} (hlu : l ≤ u)
    {zstar nustar : Theta → ℝ}
    (hz : zstar ∈ convexHull ℝ (riskVector P tau '' procedureSet X l u))
    (hnu : nustar ∈ stdSimplex ℝ Theta)
    (hs : IsSaddlePointOn
      (convexHull ℝ (riskVector P tau '' procedureSet X l u))
      (stdSimplex ℝ Theta) bayesPayoff zstar nustar) :
    bayesPayoff zstar nustar = minimaxValue (risk P tau : Procedure X l u → Theta → ℝ) := by
  /- Recover a procedure dominated by `zstar`. Point-mass priors show all its
  state risks are at most the saddle value, giving minimax ≤ saddle. Conversely,
  the saddle lower inequality applies to every attainable risk vector; its prior
  average is at most that procedure's finite worst-case risk, so `le_minimaxValue`
  gives saddle ≤ minimax. Finiteness supplies all `BddAbove` obligations. -/
  classical
  let riskFn : Procedure X l u → Theta → ℝ := risk P tau
  obtain ⟨qz, hqz⟩ :=
    exists_procedure_risk_le_of_mem_convexHull P tau hP hlu hz
  have hz_le_value (theta : Theta) :
      zstar theta ≤ bayesPayoff zstar nustar := by
    have hpoint : Pi.single theta 1 ∈ stdSimplex ℝ Theta :=
      single_mem_stdSimplex ℝ theta
    have h := hs zstar hz (Pi.single theta 1) hpoint
    simpa [bayesPayoff, Pi.single_apply] using h
  have hqz_value (theta : Theta) :
      riskFn qz theta ≤ bayesPayoff zstar nustar :=
    (hqz theta).trans (hz_le_value theta)
  have hminimax_le :
      minimaxValue riskFn ≤ bayesPayoff zstar nustar := by
    calc
      minimaxValue riskFn ≤ worstCaseRisk riskFn qz :=
        minimaxValue_le_worstCaseRisk_of_nonneg
          (fun q theta ↦ risk_nonneg P tau hP q theta) qz
      _ ≤ bayesPayoff zstar nustar := worstCaseRisk_le hqz_value
  have hvalue_le :
      bayesPayoff zstar nustar ≤ minimaxValue riskFn := by
    apply @le_minimaxValue _ _ ⟨qz⟩
    intro q
    have hrisk_mem : riskVector P tau q.toAmbient ∈
        convexHull ℝ (riskVector P tau '' procedureSet X l u) := by
      apply subset_convexHull ℝ
      exact ⟨q.toAmbient, q.toAmbient_mem, rfl⟩
    have hs_q := hs (riskVector P tau q.toAmbient) hrisk_mem nustar hnu
    have hcoord (theta : Theta) :
        riskFn q theta ≤ worstCaseRisk riskFn q :=
      le_worstCaseRisk (Finite.bddAbove_range (riskFn q)) theta
    calc
      bayesPayoff zstar nustar ≤
          bayesPayoff (riskVector P tau q.toAmbient) nustar := hs_q
      _ = ∑ theta, nustar theta * riskFn q theta := by
        apply Finset.sum_congr rfl
        intro theta htheta
        rw [show riskVector P tau q.toAmbient theta = riskFn q theta by
          exact rawRisk_toAmbient P tau q theta]
      _ ≤ ∑ theta, nustar theta * worstCaseRisk riskFn q := by
        apply Finset.sum_le_sum
        intro theta htheta
        exact mul_le_mul_of_nonneg_left (hcoord theta) (hnu.1 theta)
      _ = worstCaseRisk riskFn q := by
        rw [← Finset.sum_mul, hnu.2, one_mul]
  exact le_antisymm hvalue_le hminimax_le

/-- **Finite bounded squared-loss minimax theorem.** In nonempty finite state and design
spaces, [an ordered real action interval](hyp:hlu) and [nonnegative](hyp:hP) [likelihood coefficients](hyp:P)
guarantee [an ordinary randomized design, bounded decision rule, and finite least-favorable
prior attaining both minimax saddle inequalities](goal). No likelihood normalization,
observation-space nonemptiness, or target-in-interval assumption is required. -/
theorem finite_bounded_squared_loss_has_saddle
    [Nonempty Theta] [Nonempty R]
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    {l u : ℝ} (hlu : l ≤ u)
    (hP : ∀ theta r x, 0 ≤ P theta r x) :
    ∃ qstar : FiniteDesign R,
      ∃ deltastar : ∀ r, X r → Set.Icc l u,
        ∃ nu : FiniteDesign Theta,
          (∀ theta,
            risk P tau ⟨qstar, deltastar⟩ theta ≤
              minimaxValue (risk P tau : Procedure X l u → Theta → ℝ)) ∧
          (∀ qprime : Procedure X l u,
            minimaxValue (risk P tau : Procedure X l u → Theta → ℝ) ≤
              nu.E (risk P tau qprime)) := by
  /- Obtain the Sion saddle, recover its dominated ordinary procedure, convert the
  prior-simplex point to `FiniteDesign`, rewrite the saddle value with
  `saddle_value_eq_minimaxValue`, and specialize the two saddle inequalities. -/
  classical
  obtain ⟨zstar, hz, nustar, hnu, hs⟩ :=
    convexified_risk_game_has_saddle P tau hlu
  obtain ⟨q, hq⟩ :=
    exists_procedure_risk_le_of_mem_convexHull P tau hP hlu hz
  let nu : FiniteDesign Theta := finiteDesignOfSimplex hnu
  have hvalue : bayesPayoff zstar nustar =
      minimaxValue (risk P tau : Procedure X l u → Theta → ℝ) :=
    saddle_value_eq_minimaxValue P tau hP hlu hz hnu hs
  refine ⟨q.design, q.decision, nu, ?_, ?_⟩
  · intro theta
    have hpoint : Pi.single theta 1 ∈ stdSimplex ℝ Theta :=
      single_mem_stdSimplex ℝ theta
    have hs_theta := hs zstar hz (Pi.single theta 1) hpoint
    calc
      risk P tau q theta ≤ zstar theta := hq theta
      _ = bayesPayoff zstar (Pi.single theta 1) := by
        simp [bayesPayoff, Pi.single_apply]
      _ ≤ bayesPayoff zstar nustar := hs_theta
      _ = minimaxValue (risk P tau : Procedure X l u → Theta → ℝ) := hvalue
  · intro qprime
    have hrisk_mem : riskVector P tau qprime.toAmbient ∈
        convexHull ℝ (riskVector P tau '' procedureSet X l u) := by
      apply subset_convexHull ℝ
      exact ⟨qprime.toAmbient, qprime.toAmbient_mem, rfl⟩
    have hs_q := hs (riskVector P tau qprime.toAmbient) hrisk_mem nustar hnu
    calc
      minimaxValue (risk P tau : Procedure X l u → Theta → ℝ) =
          bayesPayoff zstar nustar := hvalue.symm
      _ ≤ bayesPayoff (riskVector P tau qprime.toAmbient) nustar := hs_q
      _ = nu.E (risk P tau qprime) := by
        rw [← bayesPayoff_eq_E]
        apply Finset.sum_congr rfl
        intro theta htheta
        rw [show riskVector P tau qprime.toAmbient theta =
            risk P tau qprime theta by
          exact rawRisk_toAmbient P tau qprime theta]
        change nustar theta * risk P tau qprime theta =
          nustar theta * risk P tau qprime theta
        rfl

end Causalean.Stat.Minimax.FiniteSquaredLoss
