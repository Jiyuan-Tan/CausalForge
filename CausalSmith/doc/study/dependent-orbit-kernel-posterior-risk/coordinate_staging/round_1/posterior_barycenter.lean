/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.FiniteKernelBayes
import Causalean.Stat.Minimax.FiniteSquaredLoss.Core
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Posterior and barycenter bounds for dependent finite squared loss

This module provides posterior-residual minimax lower bounds and conditional-barycenter
minimax upper bounds for finite experiments whose observation type depends on the chosen
design index. Null predictive and design fibers are handled by guarded definitions, without
full-support assumptions.
-/

open scoped BigOperators

namespace Causalean.Stat.Minimax.FiniteSquaredLoss

/-- A dependent finite experiment assigns, at every state and design index, a nonnegative
normalized mass function on that design's observation type, together with a real target. -/
structure Model (Theta B : Type*) [Fintype Theta] [Fintype B]
    (X : B → Type*) [∀ b, Fintype (X b)] where
  /-- The observation likelihood at a state and design index. -/
  P : Theta → ∀ b, X b → ℝ
  /-- Every likelihood coefficient is nonnegative. -/
  P_nonneg : ∀ theta b x, 0 ≤ P theta b x
  /-- At every state and design index, the likelihood coefficients sum to one. -/
  P_sum : ∀ theta b, ∑ x, P theta b x = 1
  /-- The real estimand attached to each state. -/
  tau : Theta → ℝ

open Causalean.Experimentation.DesignBased
open Causalean.Stat
open Causalean.Stat.Minimax.FiniteSquaredLoss

variable {Theta B : Type*} [Fintype Theta] [Fintype B]
variable {X : B → Type*} [∀ b, Fintype (X b)]

/-- The prior predictive mass of an observation in one design-index fiber. -/
noncomputable def Model.predictiveMass (M : Model Theta B X) (nu : FiniteDesign Theta)
    (b : B) (x : X b) : ℝ :=
  ∑ theta, nu.p theta * M.P theta b x

/-- [The prior predictive probabilities within a fixed design sum to one](goal). -/
theorem Model.sum_predictiveMass (M : Model Theta B X) (nu : FiniteDesign Theta) (b : B) :
    ∑ x, M.predictiveMass nu b x = 1 := by
  classical
  unfold Model.predictiveMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.P_sum, mul_one]
  exact nu.p_sum

/-- [Every prior predictive probability is nonnegative](goal). -/
theorem Model.predictiveMass_nonneg (M : Model Theta B X) (nu : FiniteDesign Theta)
    (b : B) (x : X b) : 0 ≤ M.predictiveMass nu b x := by
  exact Finset.sum_nonneg fun theta _ => mul_nonneg (nu.p_nonneg theta) (M.P_nonneg theta b x)

/-- The predictive target numerator is the prior average of target times joint mass. -/
noncomputable def Model.predictiveTarget (M : Model Theta B X) (nu : FiniteDesign Theta)
    (b : B) (x : X b) : ℝ :=
  ∑ theta, nu.p theta * M.P theta b x * M.tau theta

/-- The guarded posterior mean is the predictive target divided by predictive mass on a
non-null fiber and is zero on a null fiber. -/
noncomputable def Model.posteriorMean (M : Model Theta B X) (nu : FiniteDesign Theta)
    (b : B) (x : X b) : ℝ :=
  if M.predictiveMass nu b x = 0 then 0
  else M.predictiveTarget nu b x / M.predictiveMass nu b x

/-- [A zero-mass predictive observation](hyp:hx) has [zero joint probability in every
state](goal). -/
theorem Model.joint_eq_zero_of_predictiveMass_eq_zero (M : Model Theta B X)
    (nu : FiniteDesign Theta) {b : B} {x : X b}
    (hx : M.predictiveMass nu b x = 0) (theta : Theta) :
    nu.p theta * M.P theta b x = 0 := by
  classical
  have hsum : (∑ theta', nu.p theta' * M.P theta' b x) = 0 := by
    simpa [Model.predictiveMass] using hx
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun theta' _ => mul_nonneg (nu.p_nonneg theta') (M.P_nonneg theta' b x))).mp
      hsum theta (Finset.mem_univ theta)

/-- [A zero-mass predictive observation](hyp:hx) has [zero target-weighted joint
probability](goal). -/
theorem Model.predictiveTarget_eq_zero_of_predictiveMass_eq_zero (M : Model Theta B X)
    (nu : FiniteDesign Theta) {b : B} {x : X b}
    (hx : M.predictiveMass nu b x = 0) :
    M.predictiveTarget nu b x = 0 := by
  classical
  unfold Model.predictiveTarget
  apply Finset.sum_eq_zero
  intro theta _
  rw [M.joint_eq_zero_of_predictiveMass_eq_zero nu hx theta, zero_mul]

/-- [Predictive probability times the guarded posterior mean equals the target-weighted joint
probability, including for null observations](goal). -/
theorem Model.predictiveMass_mul_posteriorMean (M : Model Theta B X)
    (nu : FiniteDesign Theta) (b : B) (x : X b) :
    M.predictiveMass nu b x * M.posteriorMean nu b x = M.predictiveTarget nu b x := by
  classical
  by_cases hx : M.predictiveMass nu b x = 0
  · rw [hx, zero_mul, M.predictiveTarget_eq_zero_of_predictiveMass_eq_zero nu hx]
  · rw [Model.posteriorMean, if_neg hx]
    exact mul_div_cancel₀ _ hx

/-- The posterior residual at a design index is the prior joint squared deviation from the
guarded posterior mean. -/
noncomputable def Model.posteriorResidual (M : Model Theta B X)
    (nu : FiniteDesign Theta) (b : B) : ℝ :=
  ∑ theta, nu.p theta *
    ∑ x, M.P theta b x * (M.posteriorMean nu b x - M.tau theta) ^ 2

/-- [Every design-specific posterior residual risk is nonnegative](goal). -/
theorem Model.posteriorResidual_nonneg (M : Model Theta B X)
    (nu : FiniteDesign Theta) (b : B) :
    0 ≤ M.posteriorResidual nu b := by
  unfold Model.posteriorResidual
  apply Finset.sum_nonneg
  intro theta _
  apply mul_nonneg (nu.p_nonneg theta)
  exact Finset.sum_nonneg fun x _ => mul_nonneg (M.P_nonneg theta b x) (sq_nonneg _)

/-- [The prior risk of any decision rule equals posterior residual risk plus its
predictive-probability-weighted squared distance from the posterior mean](goal). -/
theorem Model.squaredRisk_eq_posteriorResidual_add (M : Model Theta B X)
    (nu : FiniteDesign Theta) (b : B) (delta : X b → ℝ) :
    (∑ theta, nu.p theta *
        ∑ x, M.P theta b x * (delta x - M.tau theta) ^ 2) =
      M.posteriorResidual nu b +
        ∑ x, M.predictiveMass nu b x *
          (delta x - M.posteriorMean nu b x) ^ 2 := by
  classical
  calc
    (∑ theta, nu.p theta *
        ∑ x, M.P theta b x * (delta x - M.tau theta) ^ 2) =
        ∑ x, ∑ theta, nu.p theta * M.P theta b x *
          (delta x - M.tau theta) ^ 2 := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
    _ = (∑ x, ∑ theta, nu.p theta * M.P theta b x *
          (M.posteriorMean nu b x - M.tau theta) ^ 2) +
        ∑ x, M.predictiveMass nu b x *
          (delta x - M.posteriorMean nu b x) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      have hcenter :
          (∑ theta, nu.p theta * M.P theta b x *
            (M.posteriorMean nu b x - M.tau theta)) = 0 := by
        calc
          (∑ theta, nu.p theta * M.P theta b x *
              (M.posteriorMean nu b x - M.tau theta)) =
              ∑ theta, (nu.p theta * M.P theta b x * M.posteriorMean nu b x -
                nu.p theta * M.P theta b x * M.tau theta) := by
            apply Finset.sum_congr rfl
            intro theta _
            ring
          _ = (∑ theta, nu.p theta * M.P theta b x) * M.posteriorMean nu b x -
              ∑ theta, nu.p theta * M.P theta b x * M.tau theta := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
        change M.predictiveMass nu b x * M.posteriorMean nu b x -
          M.predictiveTarget nu b x = 0
        rw [M.predictiveMass_mul_posteriorMean]
        exact sub_self _
      -- Complete the square on this observation fiber; `hcenter` kills the cross term.
      calc
        (∑ theta, nu.p theta * M.P theta b x * (delta x - M.tau theta) ^ 2) =
            ∑ theta,
              (nu.p theta * M.P theta b x *
                  (M.posteriorMean nu b x - M.tau theta) ^ 2 +
                nu.p theta * M.P theta b x *
                  (delta x - M.posteriorMean nu b x) ^ 2 +
                (2 * (delta x - M.posteriorMean nu b x)) *
                  (nu.p theta * M.P theta b x *
                    (M.posteriorMean nu b x - M.tau theta))) := by
              apply Finset.sum_congr rfl
              intro theta _
              ring
        _ = (∑ theta, nu.p theta * M.P theta b x *
                  (M.posteriorMean nu b x - M.tau theta) ^ 2) +
              M.predictiveMass nu b x *
                (delta x - M.posteriorMean nu b x) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.sum_mul, ← Finset.mul_sum, hcenter, mul_zero]
              simp [Model.predictiveMass]
    _ = M.posteriorResidual nu b +
        ∑ x, M.predictiveMass nu b x *
          (delta x - M.posteriorMean nu b x) ^ 2 := by
      congr 1
      unfold Model.posteriorResidual
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]

/-- [The guarded posterior mean attains exactly the design-specific posterior residual
risk](goal). -/
theorem Model.squaredRisk_posteriorMean (M : Model Theta B X)
    (nu : FiniteDesign Theta) (b : B) :
    (∑ theta, nu.p theta *
        ∑ x, M.P theta b x *
          (M.posteriorMean nu b x - M.tau theta) ^ 2) =
      M.posteriorResidual nu b := by
  rfl

/-- [The posterior residual risk is no greater than the prior squared-loss risk of any real
decision rule for the same design](goal). -/
theorem Model.posteriorResidual_le_squaredRisk (M : Model Theta B X)
    (nu : FiniteDesign Theta) (b : B) (delta : X b → ℝ) :
    M.posteriorResidual nu b ≤
      ∑ theta, nu.p theta *
        ∑ x, M.P theta b x * (delta x - M.tau theta) ^ 2 := by
  rw [M.squaredRisk_eq_posteriorResidual_add]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun x _ =>
    mul_nonneg (M.predictiveMass_nonneg nu b x) (sq_nonneg _))

/-- [The smallest prior squared-loss risk over all real decision rules for a fixed design
equals its posterior residual risk](goal). -/
theorem Model.iInf_squaredRisk_eq_posteriorResidual (M : Model Theta B X)
    (nu : FiniteDesign Theta) (b : B) :
    (⨅ delta : X b → ℝ,
      ∑ theta, nu.p theta *
        ∑ x, M.P theta b x * (delta x - M.tau theta) ^ 2) =
      M.posteriorResidual nu b := by
  have hb : BddBelow (Set.range fun delta : X b → ℝ =>
      ∑ theta, nu.p theta *
        ∑ x, M.P theta b x * (delta x - M.tau theta) ^ 2) := by
    refine ⟨M.posteriorResidual nu b, ?_⟩
    rintro _ ⟨delta, rfl⟩
    exact M.posteriorResidual_le_squaredRisk nu b delta
  -- The posterior mean attains the universal lower bound.
  apply le_antisymm
  · calc
      (⨅ delta : X b → ℝ,
        ∑ theta, nu.p theta *
          ∑ x, M.P theta b x * (delta x - M.tau theta) ^ 2) ≤
          ∑ theta, nu.p theta *
            ∑ x, M.P theta b x *
              (M.posteriorMean nu b x - M.tau theta) ^ 2 :=
        ciInf_le hb (M.posteriorMean nu b)
      _ = M.posteriorResidual nu b := M.squaredRisk_posteriorMean nu b
  · exact le_ciInf fun delta => M.posteriorResidual_le_squaredRisk nu b delta

/-- [The least posterior residual across designs is no greater than the prior-average risk
of any bounded dependent procedure](goal). -/
theorem Model.sInf_posteriorResidual_le_priorRisk [Nonempty B]
    (M : Model Theta B X) (nu : FiniteDesign Theta) {l u : ℝ}
    (q : Procedure X l u) :
    sInf (Set.range (M.posteriorResidual nu)) ≤
      ∑ theta, nu.p theta * risk M.P M.tau q theta := by
  classical
  have hb : BddBelow (Set.range (M.posteriorResidual nu)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨b, rfl⟩
    exact M.posteriorResidual_nonneg nu b
  have hs_le (b : B) :
      sInf (Set.range (M.posteriorResidual nu)) ≤ M.posteriorResidual nu b :=
    csInf_le hb ⟨b, rfl⟩
  -- Average the per-design posterior inequality using the procedure's design law.
  calc
    sInf (Set.range (M.posteriorResidual nu)) =
        ∑ b, q.design.p b * sInf (Set.range (M.posteriorResidual nu)) := by
          rw [← Finset.sum_mul, q.design.p_sum, one_mul]
    _ ≤ ∑ b, q.design.p b *
        (∑ theta, nu.p theta *
          ∑ x, M.P theta b x * ((q.decision b x : ℝ) - M.tau theta) ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        ((hs_le b).trans (M.posteriorResidual_le_squaredRisk nu b
          (fun x => (q.decision b x : ℝ)))) (q.design.p_nonneg b)
    _ = ∑ theta, nu.p theta * risk M.P M.tau q theta := by
      unfold risk
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro theta _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- [An ordered action interval](hyp:hlu) makes [the least design-specific posterior residual
a lower bound on the dependent experiment's bounded squared-loss minimax value](goal). -/
theorem Model.sInf_posteriorResidual_le_minimaxValue [Nonempty Theta] [Nonempty B]
    (M : Model Theta B X) (nu : FiniteDesign Theta) {l u : ℝ} (hlu : l ≤ u) :
    sInf (Set.range (M.posteriorResidual nu)) ≤
      Causalean.Stat.minimaxValue (risk (l := l) (u := u) M.P M.tau) := by
  let _ : Nonempty (Procedure X l u) := procedure_nonempty hlu
  apply Causalean.Stat.le_minimaxValue
  intro q
  calc
    sInf (Set.range (M.posteriorResidual nu)) ≤
        ∑ theta, nu.p theta * risk M.P M.tau q theta :=
      M.sInf_posteriorResidual_le_priorRisk nu q
    _ ≤ ∑ theta, nu.p theta *
        Causalean.Stat.worstCaseRisk (risk M.P M.tau) q := by
      apply Finset.sum_le_sum
      intro theta _
      exact mul_le_mul_of_nonneg_left
        (Causalean.Stat.le_worstCaseRisk
          (Finite.bddAbove_range (risk M.P M.tau q)) theta) (nu.p_nonneg theta)
    _ = Causalean.Stat.worstCaseRisk (risk M.P M.tau) q := by
      rw [← Finset.sum_mul, nu.p_sum, one_mul]

open Causalean.Experimentation.DesignBased
open Causalean.Stat
open Causalean.Stat.Minimax.FiniteSquaredLoss

variable {Theta B G : Type*} [Fintype Theta] [Fintype B] [Fintype G]
variable {X : B → Type*}

/-- The guarded conditional barycenter uses the normalized grid weights on positive design
fibers and a caller-supplied default on zero-design-mass fibers. -/
noncomputable def conditionalBarycenter (pi : FiniteDesign B)
    (w : ∀ b, X b → G → ℝ) (gamma : G → ℝ) (d : ℝ)
    (b : B) (x : X b) : ℝ :=
  if pi.p b = 0 then d else (∑ g, gamma g * w b x g) / pi.p b

/-- [Nonnegative grid weights](hyp:hw) that [sum to the design probability](hyp:hocc) are
[zero individually](goal) [whenever that design has zero probability](hyp:hb). -/
theorem weight_eq_zero_of_designMass_eq_zero (pi : FiniteDesign B)
    (w : ∀ b, X b → G → ℝ) (hw : ∀ b x g, 0 ≤ w b x g)
    (hocc : ∀ b x, ∑ g, w b x g = pi.p b)
    {b : B} (hb : pi.p b = 0) (x : X b) (g : G) :
    w b x g = 0 := by
  classical
  have hsum : (∑ g', w b x g') = 0 := by
    rw [hocc b x, hb]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun g' _ => hw b x g')).mp hsum g (Finset.mem_univ g)

/-- [Nonnegative grid weights](hyp:hw) that [sum to the design probability](hyp:hocc), with
[the null-fiber default inside a closed interval](hyp:hd) and [all grid actions inside that
interval](hyp:hgamma), produce [a guarded conditional barycenter in the same interval](goal). -/
theorem conditionalBarycenter_mem_Icc (pi : FiniteDesign B)
    (w : ∀ b, X b → G → ℝ) (gamma : G → ℝ) (d : ℝ)
    (hw : ∀ b x g, 0 ≤ w b x g)
    (hocc : ∀ b x, ∑ g, w b x g = pi.p b)
    {l u : ℝ} (hd : d ∈ Set.Icc l u) (hgamma : ∀ g, gamma g ∈ Set.Icc l u)
    (b : B) (x : X b) :
    conditionalBarycenter pi w gamma d b x ∈ Set.Icc l u := by
  classical
  by_cases hb : pi.p b = 0
  · simpa [conditionalBarycenter, hb] using hd
  · have hbpos : 0 < pi.p b := lt_of_le_of_ne (pi.p_nonneg b) (Ne.symm hb)
    rw [conditionalBarycenter, if_neg hb]
    constructor
    · rw [le_div_iff₀ hbpos, ← hocc b x, Finset.mul_sum]
      exact Finset.sum_le_sum fun g _ =>
        mul_le_mul_of_nonneg_right (hgamma g).1 (hw b x g)
    · rw [div_le_iff₀ hbpos, ← hocc b x, Finset.mul_sum]
      exact Finset.sum_le_sum fun g _ =>
        mul_le_mul_of_nonneg_right (hgamma g).2 (hw b x g)

/-- [Nonnegative grid weights](hyp:hw) that [sum to the design probability](hyp:hocc) make
[design probability times the guarded barycenter's squared error no greater than the
corresponding weighted grid-action squared error](goal). -/
theorem designMass_mul_conditionalBarycenter_sq_le (pi : FiniteDesign B)
    (w : ∀ b, X b → G → ℝ) (gamma : G → ℝ) (d t : ℝ)
    (hw : ∀ b x g, 0 ≤ w b x g)
    (hocc : ∀ b x, ∑ g, w b x g = pi.p b)
    (b : B) (x : X b) :
    pi.p b * (conditionalBarycenter pi w gamma d b x - t) ^ 2 ≤
      ∑ g, w b x g * (gamma g - t) ^ 2 := by
  classical
  by_cases hb : pi.p b = 0
  · -- On a null fiber occupancy forces every nonnegative weight to vanish.
    simp [hb, conditionalBarycenter,
      weight_eq_zero_of_designMass_eq_zero pi w hw hocc hb]
  · have hmass :
        pi.p b * conditionalBarycenter pi w gamma d b x =
          ∑ g, gamma g * w b x g := by
      rw [conditionalBarycenter, if_neg hb, mul_div_cancel₀ _ hb]
    have hcenter :
        (∑ g, w b x g *
          (gamma g - conditionalBarycenter pi w gamma d b x)) = 0 := by
      calc
        (∑ g, w b x g *
            (gamma g - conditionalBarycenter pi w gamma d b x)) =
            ∑ g, (gamma g * w b x g -
              w b x g * conditionalBarycenter pi w gamma d b x) := by
                apply Finset.sum_congr rfl
                intro g _
                ring
        _ = (∑ g, gamma g * w b x g) -
            (∑ g, w b x g) * conditionalBarycenter pi w gamma d b x := by
              rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = 0 := by rw [hocc b x, ← hmass, sub_self]
    -- Expand around the weighted mean; the centered cross term is zero.
    have hsquare :
        (∑ g, w b x g * (gamma g - t) ^ 2) =
          pi.p b * (conditionalBarycenter pi w gamma d b x - t) ^ 2 +
            ∑ g, w b x g *
              (gamma g - conditionalBarycenter pi w gamma d b x) ^ 2 := by
      calc
        (∑ g, w b x g * (gamma g - t) ^ 2) =
            ∑ g, (w b x g *
                (gamma g - conditionalBarycenter pi w gamma d b x) ^ 2 +
              w b x g *
                (conditionalBarycenter pi w gamma d b x - t) ^ 2 +
              (2 * (conditionalBarycenter pi w gamma d b x - t)) *
                (w b x g *
                  (gamma g - conditionalBarycenter pi w gamma d b x))) := by
              apply Finset.sum_congr rfl
              intro g _
              ring
        _ = pi.p b * (conditionalBarycenter pi w gamma d b x - t) ^ 2 +
            ∑ g, w b x g *
              (gamma g - conditionalBarycenter pi w gamma d b x) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.sum_mul, ← Finset.mul_sum, hcenter, mul_zero,
                add_zero, hocc b x]
              ring
    rw [hsquare]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun g _ =>
      mul_nonneg (hw b x g) (sq_nonneg _))

/-- [Nonnegative grid weights](hyp:hw) that [sum to each design probability](hyp:hocc) make
[the statewise risk of the guarded conditional barycenter no greater than the randomized
grid-action risk](goal). -/
theorem Model.conditionalBarycenter_risk_le [∀ b, Fintype (X b)]
    (M : Model Theta B X)
    (pi : FiniteDesign B) (w : ∀ b, X b → G → ℝ)
    (gamma : G → ℝ) (d : ℝ)
    (hw : ∀ b x g, 0 ≤ w b x g)
    (hocc : ∀ b x, ∑ g, w b x g = pi.p b) (theta : Theta) :
    ∑ b, pi.p b * ∑ x, M.P theta b x *
        (conditionalBarycenter pi w gamma d b x - M.tau theta) ^ 2 ≤
      ∑ b, ∑ x, ∑ g,
        M.P theta b x * w b x g * (gamma g - M.tau theta) ^ 2 := by
  classical
  calc
    (∑ b, pi.p b * ∑ x, M.P theta b x *
        (conditionalBarycenter pi w gamma d b x - M.tau theta) ^ 2) =
        ∑ b, ∑ x, M.P theta b x *
          (pi.p b *
            (conditionalBarycenter pi w gamma d b x - M.tau theta) ^ 2) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ b, ∑ x, M.P theta b x *
        (∑ g, w b x g * (gamma g - M.tau theta) ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (designMass_mul_conditionalBarycenter_sq_le
          pi w gamma d (M.tau theta) hw hocc b x)
        (M.P_nonneg theta b x)
    _ = ∑ b, ∑ x, ∑ g,
        M.P theta b x * w b x g * (gamma g - M.tau theta) ^ 2 := by
      simp_rw [Finset.mul_sum, mul_assoc]

/-- Interval-bounded defaults and grid actions turn a guarded conditional barycenter into a
valid bounded dependent finite squared-loss procedure. -/
noncomputable def barycenterProcedure (pi : FiniteDesign B)
    [∀ b, Fintype (X b)]
    (w : ∀ b, X b → G → ℝ)
    (gamma : G → ℝ) (d : ℝ)
    (hw : ∀ b x g, 0 ≤ w b x g)
    (hocc : ∀ b x, ∑ g, w b x g = pi.p b)
    {l u : ℝ} (hd : d ∈ Set.Icc l u) (hgamma : ∀ g, gamma g ∈ Set.Icc l u) :
    Procedure X l u where
  design := pi
  decision b x := ⟨conditionalBarycenter pi w gamma d b x,
    conditionalBarycenter_mem_Icc pi w gamma d hw hocc hd hgamma b x⟩

/-- [Nonnegative grid weights](hyp:hw) that [sum to each design probability](hyp:hocc), with
[the null-fiber default inside the action interval](hyp:hd) and [all grid actions inside that
interval](hyp:hgamma), make [the bounded barycenter procedure's statewise risk no greater
than the randomized grid-action risk](goal). -/
theorem Model.risk_barycenterProcedure_le [∀ b, Fintype (X b)]
    (M : Model Theta B X)
    (pi : FiniteDesign B) (w : ∀ b, X b → G → ℝ)
    (gamma : G → ℝ) (d : ℝ)
    (hw : ∀ b x g, 0 ≤ w b x g)
    (hocc : ∀ b x, ∑ g, w b x g = pi.p b)
    {l u : ℝ} (hd : d ∈ Set.Icc l u) (hgamma : ∀ g, gamma g ∈ Set.Icc l u)
    (theta : Theta) :
    risk M.P M.tau (barycenterProcedure pi w gamma d hw hocc hd hgamma) theta ≤
      ∑ b, ∑ x, ∑ g,
        M.P theta b x * w b x g * (gamma g - M.tau theta) ^ 2 := by
  simpa [risk, barycenterProcedure] using
    M.conditionalBarycenter_risk_le pi w gamma d hw hocc theta

/-- [Nonnegative grid weights](hyp:hw) that [sum to each design probability](hyp:hocc), with
[the null-fiber default inside the action interval](hyp:hd), [all grid actions inside that
interval](hyp:hgamma), and [randomized grid-action risk uniformly bounded across
states](hyp:hrisk), imply [the dependent experiment's bounded squared-loss minimax value is
no greater than that bound](goal). -/
theorem Model.minimaxValue_le_of_randomizedGridRisk [Nonempty Theta]
    [∀ b, Fintype (X b)] (M : Model Theta B X) (pi : FiniteDesign B)
    (w : ∀ b, X b → G → ℝ) (gamma : G → ℝ) (d : ℝ)
    (hw : ∀ b x g, 0 ≤ w b x g)
    (hocc : ∀ b x, ∑ g, w b x g = pi.p b)
    {l u c : ℝ} (hd : d ∈ Set.Icc l u) (hgamma : ∀ g, gamma g ∈ Set.Icc l u)
    (hrisk : ∀ theta, ∑ b, ∑ x, ∑ g,
      M.P theta b x * w b x g * (gamma g - M.tau theta) ^ 2 ≤ c) :
    Causalean.Stat.minimaxValue (risk (l := l) (u := u) M.P M.tau) ≤ c := by
  let q : Procedure X l u :=
    barycenterProcedure pi w gamma d hw hocc hd hgamma
  calc
    Causalean.Stat.minimaxValue (risk (l := l) (u := u) M.P M.tau) ≤
        Causalean.Stat.worstCaseRisk (risk M.P M.tau) q :=
      Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        (fun q' theta => risk_nonneg M.P M.tau M.P_nonneg q' theta) q
    _ ≤ c := Causalean.Stat.worstCaseRisk_le fun theta =>
      (M.risk_barycenterProcedure_le pi w gamma d hw hocc hd hgamma theta).trans
        (hrisk theta)

end Causalean.Stat.Minimax.FiniteSquaredLoss
