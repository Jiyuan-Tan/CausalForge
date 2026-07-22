/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.MEstimation.FinitePoisson

/-!
# Conditional sign characterization for finite Poisson projections

This module characterizes the sign of one selected coefficient from the score
at a conditional nuisance fit with that coefficient fixed at zero.
-/

open scoped BigOperators

namespace Causalean.Stat

-- @node: finitePoissonObjective_snd_sign_of_nuisance_score
/-- If the zero-scalar conditional nuisance fit clears every nuisance score,
then strict full-rank Poisson geometry makes the selected scalar coefficient
have exactly the sign of the remaining scalar score. -/
lemma finitePoissonObjective_snd_sign_of_nuisance_score
    {U I : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] [Fintype I] [DecidableEq I] [Nonempty I]
    (q m : I → ℝ) (A : (U × ℝ) →ₗ[ℝ] (I → ℝ)) (u₀ : U)
    (hq : ∀ i, 0 < q i) (hm : ∀ i, 0 < m i)
    (hA : Function.Injective A)
    (hNuisance : ∀ u : U,
      ∑ i, q i * A (u, 0) i * (m i - Real.exp (A (u₀, 0) i)) = 0) :
    let beta :=
      (maximizerOrZero (finitePoissonObjective q m A)).2
    let scalarScore :=
      ∑ i, q i * A (0, 1) i * (m i - Real.exp (A (u₀, 0) i))
    (beta < 0 ↔ scalarScore < 0) ∧
    (beta = 0 ↔ scalarScore = 0) ∧
    (0 < beta ↔ 0 < scalarScore) := by
  dsimp only
  let xstar : U × ℝ := maximizerOrZero (finitePoissonObjective q m A)
  let xzero : U × ℝ := (u₀, 0)
  let v : U × ℝ := xstar - xzero
  let scalarScore : ℝ :=
    ∑ i, q i * A (0, 1) i * (m i - Real.exp (A xzero i))
  have hunique := finitePoissonObjective_exists_unique_max q m A hq hm hA
  obtain ⟨x, hxmax, hxunique⟩ := hunique
  have hexists : ∃ x, ∀ y, finitePoissonObjective q m A y ≤
      finitePoissonObjective q m A x := ⟨x, hxmax⟩
  have hxstar_eq : xstar = x := by
    dsimp [xstar, maximizerOrZero]
    rw [dif_pos hexists]
    exact hxunique _ (Classical.choose_spec hexists)
  have hxstar : ∀ y, finitePoissonObjective q m A y ≤
      finitePoissonObjective q m A xstar := by
    rw [hxstar_eq]
    exact hxmax
  have hstarScore (d : U × ℝ) :
      ∑ i, q i * A d i * (m i - Real.exp (A xstar i)) = 0 :=
    finitePoissonObjective_score q m A xstar d hxstar
  have hxstar_add : xstar = xzero + v := by
    simp [v]
  have hzeroScore (d : U × ℝ) :
      (∑ i, q i * A d i * (m i - Real.exp (A xzero i))) =
        d.2 * scalarScore := by
    have hd : d = (d.1, 0) + d.2 • (0, (1 : ℝ)) := by
      ext <;> simp
    have hAd (i : I) : A d i = A (d.1, 0) i + d.2 * A (0, 1) i := by
      calc
        A d i = A ((d.1, 0) + d.2 • (0, (1 : ℝ))) i :=
          congrArg (fun z => A z i) hd
        _ = _ := by
          rw [map_add, map_smul]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ = ∑ i, (q i * A (d.1, 0) i *
            (m i - Real.exp (A xzero i)) +
          d.2 * (q i * A (0, 1) i *
            (m i - Real.exp (A xzero i)))) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hAd]
              ring
      _ = (∑ i, q i * A (d.1, 0) i *
            (m i - Real.exp (A xzero i))) +
          d.2 * ∑ i, q i * A (0, 1) i *
            (m i - Real.exp (A xzero i)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = d.2 * scalarScore := by
        rw [show (∑ i, q i * A (d.1, 0) i *
            (m i - Real.exp (A xzero i))) = 0 by simpa [xzero] using hNuisance d.1]
        simp [scalarScore]
  have hvsecond : v.2 = xstar.2 := by
    simp [v, xzero]
  have hstrict (hv : v ≠ 0) : 0 < xstar.2 * scalarScore := by
    have hAv : A v ≠ 0 := fun hav => hv (hA (by simpa using hav))
    obtain ⟨i, hi⟩ : ∃ i, A v i ≠ 0 := by
      simpa only [Function.ne_iff] using hAv
    have harg (j : I) : A xstar j = A xzero j + A v j := by
      rw [hxstar_add, map_add]
      rfl
    have hnonneg (j : I) :
        0 ≤ q j * A v j * (Real.exp (A xstar j) - Real.exp (A xzero j)) := by
      have hqj := (hq j).le
      by_cases hav : 0 ≤ A v j
      · have he : Real.exp (A xzero j) ≤ Real.exp (A xstar j) := by
          apply Real.exp_le_exp.mpr
          rw [harg]
          linarith
        exact mul_nonneg (mul_nonneg hqj hav) (sub_nonneg.mpr he)
      · have hav' : A v j ≤ 0 := le_of_not_ge hav
        have he : Real.exp (A xstar j) ≤ Real.exp (A xzero j) := by
          apply Real.exp_le_exp.mpr
          rw [harg]
          linarith
        have : Real.exp (A xstar j) - Real.exp (A xzero j) ≤ 0 := sub_nonpos.mpr he
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos hqj hav') this
    have hposi :
        0 < q i * A v i * (Real.exp (A xstar i) - Real.exp (A xzero i)) := by
      rcases lt_or_gt_of_ne hi with hav | hav
      · have he : Real.exp (A xstar i) < Real.exp (A xzero i) := by
          apply Real.exp_lt_exp.mpr
          rw [harg]
          linarith
        have hdiff : Real.exp (A xstar i) - Real.exp (A xzero i) < 0 :=
          sub_neg.mpr he
        exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (hq i) hav) hdiff
      · have he : Real.exp (A xzero i) < Real.exp (A xstar i) := by
          apply Real.exp_lt_exp.mpr
          rw [harg]
          linarith
        exact mul_pos (mul_pos (hq i) hav) (sub_pos.mpr he)
    have hsumpos : 0 < ∑ j,
        q j * A v j * (Real.exp (A xstar j) - Real.exp (A xzero j)) := by
      apply Finset.sum_pos'
      · intro j _
        exact hnonneg j
      · exact ⟨i, Finset.mem_univ i, hposi⟩
    have hdecomp :
        (∑ j, q j * A v j * (m j - Real.exp (A xzero j))) =
          (∑ j, q j * A v j * (m j - Real.exp (A xstar j))) +
            ∑ j, q j * A v j *
              (Real.exp (A xstar j) - Real.exp (A xzero j)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hzeroScore v, hvsecond, hstarScore v, zero_add] at hdecomp
    rw [hdecomp]
    exact hsumpos
  have hzero : xstar.2 = 0 ↔ scalarScore = 0 := by
    constructor
    · intro hb
      by_contra hs
      have hv : v = 0 := by
        by_contra hv
        have := hstrict hv
        rw [hb, zero_mul] at this
        exact (lt_irrefl 0) this
      have hscalar := hstarScore (0, 1)
      rw [show xstar = xzero by simpa [v] using congrArg (fun z => z + xzero) hv]
        at hscalar
      exact hs (by simpa [scalarScore] using hscalar)
    · intro hs
      have hzeroScore' (d : U × ℝ) :
          ∑ i, q i * A d i * (m i - Real.exp (A xzero i)) = 0 := by
        rw [hzeroScore d, hs, mul_zero]
      have hxzero : ∀ y, finitePoissonObjective q m A y ≤
          finitePoissonObjective q m A xzero :=
        finitePoissonObjective_isMax_of_score q m A xzero
          (fun i => (hq i).le) hzeroScore'
      have hxzero_eq : xzero = x := hxunique xzero hxzero
      rw [hxstar_eq, ← hxzero_eq]
  have hneg : xstar.2 < 0 ↔ scalarScore < 0 := by
    constructor
    · intro hb
      have hv : v ≠ 0 := by
        intro hv
        have := congrArg Prod.snd hv
        simp [v, xzero] at this
        linarith
      have hp := hstrict hv
      nlinarith
    · intro hs
      have hb : xstar.2 ≠ 0 := fun hb => hs.ne (hzero.mp hb)
      have hv : v ≠ 0 := by
        intro hv
        have := congrArg Prod.snd hv
        simp [v, xzero] at this
        exact hb this
      have hp := hstrict hv
      nlinarith
  have hpos : 0 < xstar.2 ↔ 0 < scalarScore := by
    constructor
    · intro hb
      have hv : v ≠ 0 := by
        intro hv
        have := congrArg Prod.snd hv
        simp [v, xzero] at this
        linarith
      have hp := hstrict hv
      nlinarith
    · intro hs
      have hb : xstar.2 ≠ 0 := fun hb => hs.ne' (hzero.mp hb)
      have hv : v ≠ 0 := by
        intro hv
        have := congrArg Prod.snd hv
        simp [v, xzero] at this
        exact hb this
      have hp := hstrict hv
      nlinarith
  simpa [xstar, xzero, scalarScore] using And.intro hneg (And.intro hzero hpos)

end Causalean.Stat
