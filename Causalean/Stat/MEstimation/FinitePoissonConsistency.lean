/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.MEstimation.ArgmaxStability
import Causalean.Stat.MEstimation.FinitePoisson
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Sequences

/-!
# Consistency and continuity of finite Poisson projections

This module proves uniform convergence of finite Poisson objectives, compact
containment and convergence of their maximizers, and continuity of the selected
maximizer under perturbations of the finite mean vector.
-/

open scoped BigOperators Topology
open Filter

namespace Causalean.Stat

-- @node: finitePoissonObjective_tendstoUniformlyOn
/-- Pointwise convergence of the finitely many weights and means gives uniform
convergence of the finite Poisson objective on every compact parameter set. -/
lemma finitePoissonObjective_tendstoUniformlyOn {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype I] (qN mN : ℕ → I → ℝ) (q m : I → ℝ)
    (A : E →ₗ[ℝ] (I → ℝ)) (K : Set E) (hK : IsCompact K)
    (hq : ∀ i, Tendsto (fun N => qN N i) atTop (nhds (q i)))
    (hm : ∀ i, Tendsto (fun N => mN N i) atTop (nhds (m i))) :
    TendstoUniformlyOn (fun N => finitePoissonObjective (qN N) (mN N) A)
      (finitePoissonObjective q m A) atTop K := by
  let cN : ℕ → (I → ℝ) × (I → ℝ) := fun N => (qN N, mN N)
  let c : (I → ℝ) × (I → ℝ) := (q, m)
  let F : ((I → ℝ) × (I → ℝ)) → E → ℝ := fun p x =>
    finitePoissonObjective p.1 p.2 A x
  have hc : Tendsto cN atTop (nhds c) := by
    exact (tendsto_pi_nhds.mpr hq).prodMk_nhds (tendsto_pi_nhds.mpr hm)
  let U := Metric.closedBall c 1
  letI : ProperSpace ((I → ℝ) × (I → ℝ)) :=
    FiniteDimensional.proper_real _
  have hU : IsCompact U := ProperSpace.isCompact_closedBall c 1
  have hcU : c ∈ U := by simp [U]
  have hevent : ∀ᶠ N in atTop, cN N ∈ U := by
    have := (Metric.tendsto_nhds.mp hc 1 zero_lt_one)
    filter_upwards [this] with N hN
    exact Metric.mem_closedBall.mpr hN.le
  have hcWithin : Tendsto cN atTop (nhdsWithin c U) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨hc, tendsto_principal.2 hevent⟩
  have hcont : Continuous (Function.uncurry F) := by
    unfold F finitePoissonObjective
    fun_prop
  have hUC : UniformContinuousOn (Function.uncurry F) (U ×ˢ K) :=
    (hU.prod hK).uniformContinuousOn_of_continuous hcont.continuousOn
  have hlocal : TendstoUniformlyOn F (F c) (nhdsWithin c U) K :=
    hUC.tendstoUniformlyOn hcU
  intro V hV
  exact hcWithin.eventually (hlocal V hV)

-- @node: finitePoissonObjective_eventually_common_compact
/-- Convergent positive coefficients and a fixed injective design put any
eventual sequence of global maximizers in one common compact ball. -/
lemma finitePoissonObjective_eventually_common_compact {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype I] [DecidableEq I]
    (qN mN : ℕ → I → ℝ) (q m : I → ℝ)
    (A : E →ₗ[ℝ] (I → ℝ)) (argmax : ℕ → E)
    (hqpos : ∀ i, 0 < q i) (hmpos : ∀ i, 0 < m i)
    (hA : Function.Injective A)
    (hq : ∀ i, Tendsto (fun N => qN N i) atTop (nhds (q i)))
    (hm : ∀ i, Tendsto (fun N => mN N i) atTop (nhds (m i)))
    (hmax : ∀ᶠ N in atTop, ∀ y,
      finitePoissonObjective (qN N) (mN N) A y ≤
        finitePoissonObjective (qN N) (mN N) A (argmax N)) :
    ∃ K : Set E, IsCompact K ∧ ∀ᶠ N in atTop, argmax N ∈ K := by
  classical
  let w : I → ℝ := fun i => q i / 2 * min (m i / 2) 1
  let B : E →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x i => w i * A x i
      map_add' := by intro x y; funext i; simp; ring
      map_smul' := by intro c x; funext i; simp; ring }
  have hwpos : ∀ i, 0 < w i := by
    intro i
    exact mul_pos (half_pos (hqpos i)) (lt_min (half_pos (hmpos i)) zero_lt_one)
  have hB : Function.Injective B := by
    intro x y hxy
    apply hA
    funext i
    have hi := congrFun hxy i
    dsimp [B] at hi
    exact (mul_left_cancel₀ (ne_of_gt (hwpos i)) hi)
  obtain ⟨L, hL, hanti⟩ := (LinearMap.injective_iff_antilipschitz B).mp hB
  let kappa : ℝ := L⁻¹
  have hkappa : 0 < kappa := inv_pos.mpr hL
  have hBnorm (x : E) : kappa * ‖x‖ ≤ ‖B x‖ := by
    have h := hanti x 0
    have hh := ENNReal.toReal_mono (by finiteness) h
    have h' : ‖x‖ ≤ (L : ℝ) * ‖B x‖ := by
      simpa [edist_dist, dist_eq_norm, ENNReal.toReal_mul] using hh
    change (L : ℝ)⁻¹ * ‖x‖ ≤ ‖B x‖
    calc
      (L : ℝ)⁻¹ * ‖x‖ ≤ (L : ℝ)⁻¹ * ((L : ℝ) * ‖B x‖) :=
        mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hL.le)
      _ = ((L : ℝ)⁻¹ * (L : ℝ)) * ‖B x‖ := by ring
      _ = ‖B x‖ := by
        rw [inv_mul_cancel₀ (show (L : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hL)]
        simp
  have hbounds : ∀ᶠ N in atTop, ∀ i,
      q i / 2 < qN N i ∧ qN N i < 2 * q i ∧
      m i / 2 < mN N i ∧ mN N i < 2 * m i := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [
      (tendsto_order.1 (hq i)).1 (q i / 2) (by linarith [hqpos i]),
      (tendsto_order.1 (hq i)).2 (2 * q i) (by linarith [hqpos i]),
      (tendsto_order.1 (hm i)).1 (m i / 2) (by linarith [hmpos i]),
      (tendsto_order.1 (hm i)).2 (2 * m i) (by linarith [hmpos i])]
      with N hqlo hqhi hmlo hmhi
    exact ⟨hqlo, hqhi, hmlo, hmhi⟩
  let M : ℝ := ∑ i, (2 * q i) * ((2 * m i + 1) ^ 2 / 2)
  let Q : ℝ := ∑ i, 2 * q i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (by norm_num) (hqpos i).le)
      (div_nonneg (sq_nonneg _) (by norm_num))
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ =>
    mul_nonneg (by norm_num) (hqpos i).le
  let R : ℝ := (M + Q) / kappa
  have hR : 0 ≤ R := div_nonneg (add_nonneg hM hQ) hkappa.le
  let K : Set E := Metric.closedBall 0 R
  letI : ProperSpace E := FiniteDimensional.proper_real E
  refine ⟨K, ProperSpace.isCompact_closedBall 0 R, ?_⟩
  filter_upwards [hbounds, hmax] with N hb hmaxN
  have htail (x : E) : finitePoissonObjective (qN N) (mN N) A x ≤ M - ‖B x‖ := by
    have hterm : ∀ i,
        qN N i * (mN N i * A x i - Real.exp (A x i)) ≤
          (2 * q i) * ((2 * m i + 1) ^ 2 / 2) - |B x i| := by
      intro i
      have hc := poissonCell_linear_coercive_bound (mN N i) (A x i)
        (lt_trans (half_pos (hmpos i)) (hb i).2.2.1)
      have hqn : 0 ≤ qN N i := (lt_trans (half_pos (hqpos i)) (hb i).1).le
      have hlower : w i ≤ qN N i * min (mN N i) 1 := by
        exact mul_le_mul (le_of_lt (hb i).1)
          (min_le_min (le_of_lt (hb i).2.2.1) le_rfl)
          (le_min (half_pos (hmpos i)).le zero_le_one) hqn
      have habs : |B x i| = w i * |A x i| := by
        dsimp [B]
        rw [abs_mul, abs_of_pos (hwpos i)]
      rw [habs]
      have hcoarse := mul_le_mul_of_nonneg_left hc hqn
      have hconst : qN N i * ((mN N i + 1) ^ 2 / 2) ≤
          (2 * q i) * ((2 * m i + 1) ^ 2 / 2) := by
        have hmn0 : 0 ≤ mN N i :=
          (lt_trans (half_pos (hmpos i)) (hb i).2.2.1).le
        have hmupper := (hb i).2.2.2
        have hsq : (mN N i + 1) ^ 2 ≤ (2 * m i + 1) ^ 2 := by nlinarith
        exact mul_le_mul (le_of_lt (hb i).2.1)
          (div_le_div_of_nonneg_right hsq (by norm_num))
          (div_nonneg (sq_nonneg _) (by norm_num))
          (mul_nonneg (by norm_num) (hqpos i).le)
      nlinarith [mul_le_mul_of_nonneg_right hlower (abs_nonneg (A x i))]
    calc
      finitePoissonObjective (qN N) (mN N) A x ≤
          ∑ i, ((2 * q i) * ((2 * m i + 1) ^ 2 / 2) - |B x i|) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = M - ∑ i, |B x i| := by rw [Finset.sum_sub_distrib]
      _ ≤ M - ‖B x‖ := by
        gcongr
        rw [Pi.norm_def]
        have hnn : (Finset.univ.sup fun i => ‖B x i‖₊) ≤ ∑ i, ‖B x i‖₊ :=
          Finset.sup_le fun i _ =>
            Finset.single_le_sum (fun j _ => zero_le ‖B x j‖₊) (Finset.mem_univ i)
        calc
          ((Finset.univ.sup fun i => ‖B x i‖₊ : NNReal) : ℝ) ≤
              ((∑ i, ‖B x i‖₊ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr hnn
          _ = ∑ i, |B x i| := by simp [Real.norm_eq_abs]
  have hzero : -Q ≤ finitePoissonObjective (qN N) (mN N) A 0 := by
    unfold finitePoissonObjective
    simp only [map_zero, Pi.zero_apply, mul_zero, Real.exp_zero, zero_sub, mul_neg,
      mul_one, Finset.sum_neg_distrib, neg_le_neg_iff]
    exact Finset.sum_le_sum fun i _ => (hb i).2.1.le
  have hchain := (hzero.trans (hmaxN 0)).trans (htail (argmax N))
  have hbn := hBnorm (argmax N)
  have hnorm : ‖argmax N‖ ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hkappa).2
    linarith
  simpa [K, Metric.mem_closedBall, dist_eq_norm] using hnorm

-- @node: finitePoissonObjective_argmax_tendsto
/-- Stability of finite-dimensional Poisson maximizers under convergence of
their finitely many positive weights and means. -/
lemma finitePoissonObjective_argmax_tendsto {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E] [Fintype I] [DecidableEq I]
    (qN mN : ℕ → I → ℝ) (q m : I → ℝ)
    (A : E →ₗ[ℝ] (I → ℝ)) (argmax : ℕ → E) (limitArgmax : E)
    (hqpos : ∀ i, 0 < q i) (hmpos : ∀ i, 0 < m i)
    (hA : Function.Injective A)
    (hq : ∀ i, Tendsto (fun N => qN N i) atTop (nhds (q i)))
    (hm : ∀ i, Tendsto (fun N => mN N i) atTop (nhds (m i)))
    (hArgmax : ∀ᶠ N in atTop, ∀ y,
      finitePoissonObjective (qN N) (mN N) A y ≤
        finitePoissonObjective (qN N) (mN N) A (argmax N))
    (hLimit : IsUniqueGlobalMax (finitePoissonObjective q m A) limitArgmax) :
    Tendsto argmax atTop (nhds limitArgmax) := by
  obtain ⟨K₀, hK₀, hmem⟩ := finitePoissonObjective_eventually_common_compact
    qN mN q m A argmax hqpos hmpos hA hq hm hArgmax
  let K : Set E := insert limitArgmax K₀
  have hK : IsCompact K := hK₀.insert limitArgmax
  have hlimitmem : limitArgmax ∈ K := Set.mem_insert _ _
  have hargmem : ∀ᶠ N in atTop, argmax N ∈ K :=
    hmem.mono fun N hN => Set.mem_insert_of_mem _ hN
  apply tendsto_argmax_of_eventually_mem_compact
    (fun N => finitePoissonObjective (qN N) (mN N) A)
    (finitePoissonObjective q m A) argmax limitArgmax K hK hlimitmem
  · exact (finitePoissonObjective_continuous q m A).continuousOn
  · intro y hy
    exact hLimit.1 y
  · exact finitePoissonObjective_tendstoUniformlyOn qN mN q m A K hK hq hm
  · exact hargmem
  · exact hArgmax.mono fun N hN y hy => hN y
  · intro y hy heq
    exact hLimit.2 y heq

-- @node: finitePoissonObjective_argmax_continuousAt_mean
/-- At a strictly positive mean vector, the unique selected maximizer of a
full-rank finite Poisson objective varies continuously with all cell means. -/
lemma finitePoissonObjective_argmax_continuousAt_mean
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I] [Nonempty I]
    (q : I → ℝ) (A : E →ₗ[ℝ] (I → ℝ)) (m₀ : I → ℝ)
    (hq : ∀ i, 0 < q i) (hm₀ : ∀ i, 0 < m₀ i)
    (hA : Function.Injective A) :
    ContinuousAt
      (fun m : I → ℝ =>
        maximizerOrZero (finitePoissonObjective q m A))
      m₀ := by
  rw [ContinuousAt, Filter.tendsto_iff_seq_tendsto]
  intro mN hmN
  have hm : ∀ i, Filter.Tendsto (fun N => mN N i) Filter.atTop (nhds (m₀ i)) :=
    tendsto_pi_nhds.mp hmN
  have hmpos : ∀ᶠ N in Filter.atTop, ∀ i, 0 < mN N i := by
    rw [Filter.eventually_all]
    intro i
    exact (tendsto_order.1 (hm i)).1 0 (hm₀ i)
  have hmax : ∀ᶠ N in Filter.atTop, ∀ y,
      finitePoissonObjective q (mN N) A y ≤
        finitePoissonObjective q (mN N) A
          (maximizerOrZero (finitePoissonObjective q (mN N) A)) := by
    filter_upwards [hmpos] with N hpos
    exact (uniqueGlobalMax_maximizerOrZero _
      (finitePoissonObjective_exists_unique_max q (mN N) A hq hpos hA)).1
  have hlimit : IsUniqueGlobalMax (finitePoissonObjective q m₀ A)
      (maximizerOrZero (finitePoissonObjective q m₀ A)) :=
    uniqueGlobalMax_maximizerOrZero _
      (finitePoissonObjective_exists_unique_max q m₀ A hq hm₀ hA)
  exact finitePoissonObjective_argmax_tendsto
    (fun _ => q) mN q m₀ A
    (fun N => maximizerOrZero (finitePoissonObjective q (mN N) A))
    (maximizerOrZero (finitePoissonObjective q m₀ A)) hq hm₀ hA
    (fun i => tendsto_const_nhds) hm hmax hlimit

end Causalean.Stat
