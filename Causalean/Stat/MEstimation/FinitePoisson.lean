/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Finite positive-mean Poisson projections

This module defines a finite Poisson criterion composed with a linear design and
proves its continuity, existence and uniqueness of the pseudo-true maximizer,
and the equivalence between global optimality and vanishing directional scores.
-/

open scoped BigOperators Topology

namespace Causalean.Stat

/-- A point is the unique global maximizer of a real-valued criterion. -/
def IsUniqueGlobalMax {A : Type*} (f : A → ℝ) (x : A) : Prop :=
  (∀ y, f y ≤ f x) ∧ ∀ y, f y = f x → y = x

/-- A total choice of a global maximizer, defaulting to zero when none exists. -/
noncomputable def maximizerOrZero {A : Type*} [Zero A] (f : A → ℝ) : A :=
  by
    classical
    exact if h : ∃ x, ∀ y, f y ≤ f x then Classical.choose h else 0

-- @node: poissonCell_linear_coercive_bound
/-- A positive-mean Poisson cell log likelihood is bounded above by a linearly
coercive function. This is the elementary tail estimate used in the finite
Poisson maximizer existence argument. -/
lemma poissonCell_linear_coercive_bound (m x : ℝ) (hm : 0 < m) :
    m * x - Real.exp x ≤ (m + 1) ^ 2 / 2 - min m 1 * |x| := by
  have hc0 : 0 < min m 1 := lt_min hm zero_lt_one
  by_cases hx : x ≤ 0
  · rw [abs_of_nonpos hx]
    have he : 0 ≤ Real.exp x := (Real.exp_pos x).le
    have hc : min m 1 ≤ m := min_le_left _ _
    have hK : 0 ≤ (m + 1) ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
    nlinarith
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    have he := Real.pow_div_factorial_le_exp x hx0 2
    norm_num [Nat.factorial] at he
    have hc : min m 1 ≤ 1 := min_le_right _ _
    have hs : 0 ≤ (x - (m + 1)) ^ 2 := sq_nonneg _
    rw [abs_of_nonneg hx0]
    nlinarith

-- @node: poissonCell_strictConcave_midpoint
/-- Strict midpoint concavity of a positive-weight Poisson cell whenever the
two linear predictors differ. -/
lemma poissonCell_strictConcave_midpoint (q m x y : ℝ) (hq : 0 < q) (hxy : x ≠ y) :
    (q * (m * x - Real.exp x) + q * (m * y - Real.exp y)) / 2 <
      q * (m * ((x + y) / 2) - Real.exp ((x + y) / 2)) := by
  have hconv := strictConvexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) hxy
      (show 0 < (1 / 2 : ℝ) by norm_num) (show 0 < (1 / 2 : ℝ) by norm_num)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hconv
  have := mul_lt_mul_of_pos_left hconv hq
  have harg : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = (x + y) / 2 := by ring
  rw [harg] at this
  calc
    _ = q * (m * ((x + y) / 2) -
        (Real.exp x + Real.exp y) / 2) := by ring
    _ < q * (m * ((x + y) / 2) - Real.exp ((x + y) / 2)) := by
      nlinarith

-- @node: finitePoissonObjective
/-- A finite positive-mean Poisson criterion composed with a linear design. -/
noncomputable def finitePoissonObjective {E I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] (q m : I → ℝ) (A : E →ₗ[ℝ] (I → ℝ)) (x : E) : ℝ :=
  ∑ i, q i * (m i * A x i - Real.exp (A x i))

-- @node: finitePoissonObjective_continuous
/-- The finite Poisson criterion is continuous in its parameter whenever the
linear design acts on a finite-dimensional normed space. -/
lemma finitePoissonObjective_continuous {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype I] (q m : I → ℝ) (A : E →ₗ[ℝ] (I → ℝ)) :
    Continuous (finitePoissonObjective q m A) := by
  unfold finitePoissonObjective
  fun_prop

-- @node: finitePoissonObjective_exists_unique_max
/-- Positive weights and means together with a full-column-rank finite design
give existence and uniqueness of the Poisson pseudo-true parameter. -/
lemma finitePoissonObjective_exists_unique_max {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (q m : I → ℝ) (A : E →ₗ[ℝ] (I → ℝ))
    (hq : ∀ i, 0 < q i) (hm : ∀ i, 0 < m i) (hA : Function.Injective A) :
    ∃! x : E, ∀ y, finitePoissonObjective q m A y ≤ finitePoissonObjective q m A x := by
  let B : E →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x i => q i * min (m i) 1 * A x i
      map_add' := by
        intro x y
        funext i
        simp only [map_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c x
        funext i
        simp only [map_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
  have hB : Function.Injective B := by
    intro x y hxy
    apply hA
    funext i
    have hi := congrFun hxy i
    have hqi : q i ≠ 0 := ne_of_gt (hq i)
    have hci : min (m i) 1 ≠ 0 := ne_of_gt (lt_min (hm i) zero_lt_one)
    dsimp [B] at hi
    have hprod : 0 < q i * min (m i) 1 := mul_pos (hq i) (lt_min (hm i) zero_lt_one)
    nlinarith
  obtain ⟨K, hK, hanti⟩ := (LinearMap.injective_iff_antilipschitz B).mp hB
  let kappa : ℝ := K⁻¹
  have hkappa : 0 < kappa := inv_pos.mpr hK
  have hBnorm (x : E) : kappa * ‖x‖ ≤ ‖B x‖ := by
    have h := hanti x 0
    have hh := ENNReal.toReal_mono (by finiteness) h
    have h' : ‖x‖ ≤ (K : ℝ) * ‖B x‖ := by
      simpa [edist_dist, dist_eq_norm, ENNReal.toReal_mul] using hh
    change (K : ℝ)⁻¹ * ‖x‖ ≤ ‖B x‖
    calc
      (K : ℝ)⁻¹ * ‖x‖ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * ‖B x‖) :=
        mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hK.le)
      _ = ((K : ℝ)⁻¹ * (K : ℝ)) * ‖B x‖ := by ring
      _ = ‖B x‖ := by
        rw [inv_mul_cancel₀ (show (K : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hK)]
        simp
  let R : ℝ := max 0
      (((∑ i, q i * ((m i + 1) ^ 2 / 2)) - finitePoissonObjective q m A 0) / kappa + 1)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hbound (x : E) :
      finitePoissonObjective q m A x ≤
        (∑ i, q i * ((m i + 1) ^ 2 / 2)) - ‖B x‖ := by
    have hterm : ∀ i,
        q i * (m i * A x i - Real.exp (A x i)) ≤
          q i * ((m i + 1) ^ 2 / 2) - |B x i| := by
      intro i
      have hc := poissonCell_linear_coercive_bound (m i) (A x i) (hm i)
      have hqi := (hq i).le
      have habs : |B x i| = q i * min (m i) 1 * |A x i| := by
        dsimp [B]
        rw [abs_mul, abs_mul, abs_of_pos (hq i),
          abs_of_pos (lt_min (hm i) zero_lt_one)]
      rw [habs]
      nlinarith [mul_le_mul_of_nonneg_left hc hqi]
    calc
      finitePoissonObjective q m A x
          ≤ ∑ i, (q i * ((m i + 1) ^ 2 / 2) - |B x i|) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i, q i * ((m i + 1) ^ 2 / 2)) - ∑ i, |B x i| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ (∑ i, q i * ((m i + 1) ^ 2 / 2)) - ‖B x‖ := by
        gcongr
        rw [Pi.norm_def]
        have hnn : (Finset.univ.sup fun b => ‖B x b‖₊) ≤ ∑ i, ‖B x i‖₊ :=
          Finset.sup_le (fun i _ =>
            Finset.single_le_sum (fun j _ => zero_le ‖B x j‖₊) (Finset.mem_univ i))
        have hr := NNReal.coe_le_coe.mpr hnn
        simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hr
  let ball : Set E := Metric.closedBall 0 R
  letI : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨xstar, hxball, hxmax⟩ :=
    (ProperSpace.isCompact_closedBall (0 : E) R).exists_isMaxOn
      ⟨0, by simpa [ball, Metric.mem_closedBall, hR0]⟩
      (finitePoissonObjective_continuous q m A).continuousOn
  have hxglobal : ∀ y, finitePoissonObjective q m A y ≤
      finitePoissonObjective q m A xstar := by
    intro y
    by_cases hy : y ∈ ball
    · exact hxmax hy
    · have hyR : R < ‖y‖ := by
        simpa [ball, Metric.mem_closedBall, dist_eq_norm, not_le] using hy
      have hcoarse := hbound y
      have hanti' := hBnorm y
      have hRlower :
          ((∑ i, q i * ((m i + 1) ^ 2 / 2)) - finitePoissonObjective q m A 0) / kappa + 1 ≤ R :=
        le_max_right _ _
      have hzero_mem : (0 : E) ∈ ball := by
        simp [ball, Metric.mem_closedBall, hR0]
      have hxzero := hxmax hzero_mem
      have hKne : kappa ≠ 0 := ne_of_gt hkappa
      have htail :
          (∑ i, q i * ((m i + 1) ^ 2 / 2)) - kappa * ‖y‖ <
            finitePoissonObjective q m A 0 := by
        apply (sub_lt_iff_lt_add).2
        have := lt_of_le_of_lt hRlower hyR
        field_simp [hKne] at this ⊢
        nlinarith
      exact (hcoarse.trans (sub_le_sub_left hanti' _)).trans
        (htail.le.trans hxzero)
  refine ⟨xstar, hxglobal, ?_⟩
  intro y hymax
  by_contra hyne
  have hAy : A y ≠ A xstar := fun h => hyne (hA h)
  obtain ⟨i, hi⟩ : ∃ i, A y i ≠ A xstar i := by
    simpa only [Function.ne_iff] using hAy
  let mid : E := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • xstar
  have hstrictTerm :
      (q i * (m i * A y i - Real.exp (A y i)) +
          q i * (m i * A xstar i - Real.exp (A xstar i))) / 2 <
        q i * (m i * A mid i - Real.exp (A mid i)) := by
    have hcell := poissonCell_strictConcave_midpoint
      (q i) (m i) (A y i) (A xstar i) (hq i) hi
    dsimp [mid]
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have harg : (1 / 2 : ℝ) * A y i + (1 / 2 : ℝ) * A xstar i =
        (A y i + A xstar i) / 2 := by ring
    rw [harg]
    exact hcell
  have hmid :
      (finitePoissonObjective q m A y + finitePoissonObjective q m A xstar) / 2 <
        finitePoissonObjective q m A mid := by
    unfold finitePoissonObjective
    rw [← Finset.sum_add_distrib]
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_lt_sum
    · intro j hj
      by_cases hji : j = i
      · subst j
        exact (hstrictTerm.le)
      · have hconv := convexOn_exp.2 (Set.mem_univ (A y j))
            (Set.mem_univ (A xstar j))
            (show 0 ≤ (1 / 2 : ℝ) by norm_num)
            (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
        simp only [smul_eq_mul] at hconv
        have hqconv := mul_le_mul_of_nonneg_left hconv (hq j).le
        dsimp [mid]
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith
    · exact ⟨i, Finset.mem_univ i, hstrictTerm⟩
  have hy_eq : finitePoissonObjective q m A y = finitePoissonObjective q m A xstar := by
    apply le_antisymm (hxglobal y)
    exact hymax xstar
  rw [hy_eq] at hmid
  have hmid' : finitePoissonObjective q m A xstar <
      finitePoissonObjective q m A mid := by simpa using hmid
  exact (not_lt_of_ge (hxglobal mid)) hmid'

-- @node: finitePoissonObjective_score
/-- Every directional score vanishes at a global maximizer. -/
lemma finitePoissonObjective_score {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (q m : I → ℝ) (A : E →ₗ[ℝ] (I → ℝ)) (x d : E)
    (hx : ∀ y, finitePoissonObjective q m A y ≤ finitePoissonObjective q m A x) :
    ∑ i, q i * A d i * (m i - Real.exp (A x i)) = 0 := by
  let path : ℝ → E := fun s => x + s • d
  have heta (i : I) : HasDerivAt (fun s => A (path s) i) (A d i) 0 := by
    have h := (hasDerivAt_const (𝕜 := ℝ) 0 (A x i)).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (A d i))
    convert h using 1
    · funext s
      simp [path, map_add, map_smul, smul_eq_mul]
    · ring
  have hderiv : HasDerivAt (fun s => finitePoissonObjective q m A (path s))
      (∑ i, q i * A d i * (m i - Real.exp (A x i))) 0 := by
    unfold finitePoissonObjective
    have hraw := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (((heta i).const_mul (m i)).sub (heta i).exp).const_mul (q i))
    convert hraw using 1
    simp only [path, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlocal : IsLocalMax (fun s => finitePoissonObjective q m A (path s)) 0 :=
    Filter.Eventually.of_forall fun s => by simpa [path] using hx (path s)
  exact hlocal.hasDerivAt_eq_zero hderiv

-- @node: finitePoissonObjective_isMax_of_score
/-- For a nonnegative weighted Poisson objective, vanishing of every
directional score is sufficient for global maximality. -/
lemma finitePoissonObjective_isMax_of_score {E I : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype I]
    (q m : I → ℝ) (A : E →ₗ[ℝ] (I → ℝ)) (x : E)
    (hq : ∀ i, 0 ≤ q i)
    (hscore : ∀ d : E, ∑ i, q i * A d i * (m i - Real.exp (A x i)) = 0) :
    ∀ y, finitePoissonObjective q m A y ≤ finitePoissonObjective q m A x := by
  intro y
  have hterm (i : I) :
      q i * (m i * A y i - Real.exp (A y i)) -
          q i * (m i * A x i - Real.exp (A x i)) ≤
        q i * A (y - x) i * (m i - Real.exp (A x i)) := by
    have he : 1 + (A y i - A x i) ≤ Real.exp (A y i - A x i) := by
      simpa [add_comm] using Real.add_one_le_exp (A y i - A x i)
    have hexp : Real.exp (A x i) * (1 + (A y i - A x i)) ≤ Real.exp (A y i) := by
      calc
        Real.exp (A x i) * (1 + (A y i - A x i)) ≤
            Real.exp (A x i) * Real.exp (A y i - A x i) :=
          mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
        _ = Real.exp (A y i) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hqexp := mul_le_mul_of_nonneg_left hexp (hq i)
    simp only [map_sub, Pi.sub_apply]
    nlinarith
  unfold finitePoissonObjective
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [hscore (y - x), Finset.sum_sub_distrib] at hsum
  linarith

/-- A criterion with a unique global maximum is maximized uniquely by its total
maximizer selector. -/
lemma uniqueGlobalMax_maximizerOrZero {E : Type*} [Zero E] (f : E → ℝ)
    (h : ∃! x : E, ∀ y, f y ≤ f x) :
    IsUniqueGlobalMax f (maximizerOrZero f) := by
  obtain ⟨x, hx, huniq⟩ := h
  have hex : ∃ z, ∀ y, f y ≤ f z := ⟨x, hx⟩
  have hsel : maximizerOrZero f = x := by
    rw [maximizerOrZero, dif_pos hex]
    exact huniq _ (Classical.choose_spec hex)
  rw [hsel]
  exact ⟨hx, fun y hy => huniq y (fun z => (hx z).trans_eq hy.symm)⟩

end Causalean.Stat
