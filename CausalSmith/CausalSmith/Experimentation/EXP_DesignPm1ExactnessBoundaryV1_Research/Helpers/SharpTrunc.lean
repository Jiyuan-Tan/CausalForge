/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SharpZero
import Mathlib.Data.Fin.VecNotation

/-! # Sharp-certificate truncation helpers -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: sharp_truncation_value_of_no_reduced_argmin_in_slice
/-- If no relaxed minimizer meets the parity slice, the implementable reduced value is
the weighted-simplex truncation value at the selector. -/
lemma sharp_truncation_value_of_no_reduced_argmin_in_slice (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa)
    (hNoMeet : ¬ ∃ x y z, InReducedTriangle m x y z ∧
      (∀ x' y' z', InReducedTriangle m x' y' z' →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
      parityThreshold m ≤ y + z) :
    implementableReducedValue m a b r kappa =
      wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1] kappa
        (truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
          (truncSelector (2 * (m : ℝ)) (parityThreshold m)
            ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1] kappa)) := by
  have hm : 2 ≤ m := hHom.1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by positivity
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hq0 : 0 ≤ qParam m := le_of_lt hq
  have hM : 0 < 2 * (m : ℝ) := by positivity
  let alpha : Fin 3 → ℝ := ![cX m a b r / qParam m, cY b r, cZ m]
  let beta : Fin 3 → ℝ := ![1 / qParam m, 1, 1]
  have hbetaPos : ∀ i, 0 < beta i := by
    intro i
    fin_cases i
    · have : 0 < 1 / qParam m := by positivity
      simpa [beta] using this
    · simp [beta]
    · simp [beta]
  have hbetaY : beta 1 = 1 := by simp [beta]
  have hbetaZ : beta 2 = 1 := by simp [beta]
  have hd0 : 0 ≤ parityThreshold m := by
    unfold parityThreshold
    by_cases hEven : Even m
    · simp [hEven]
    · simp [hEven]
      positivity
  have hdM : parityThreshold m ≤ 2 * (m : ℝ) := by
    unfold parityThreshold
    by_cases hEven : Even m
    · simp [hEven]
    · simp [hEven]
      have : 2 / (m : ℝ) ≤ 2 * (m : ℝ) := by
        rw [div_le_iff₀ hmpos]
        nlinarith [sq_nonneg ((m : ℝ) - 1)]
      exact this
  obtain ⟨X_rel, hRelMin⟩ := exists_relaxed_reduced_minimizer m a b r kappa hHom hk
  let t_rel : Fin 3 → ℝ := ![qParam m * X_rel.1, X_rel.2.1, X_rel.2.2]
  have hrelS : InSimplex (2 * (m : ℝ)) t_rel :=
    reducedTriangle_to_simplex m X_rel.1 X_rel.2.1 X_rel.2.2 hq0 hRelMin.1
  have hrelWsMin : ∀ s : Fin 3 → ℝ, InSimplex (2 * (m : ℝ)) s →
      wsObj alpha beta kappa t_rel ≤ wsObj alpha beta kappa s := by
    intro s hs
    have hsRed := simplex_to_reducedTriangle m s hq hs
    have hle := hRelMin.2 (s 0 / qParam m) (s 1) (s 2) hsRed
    have hleft :
        wsObj alpha beta kappa t_rel =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_rel.1 X_rel.2.1 X_rel.2.2 := by
      rw [show wsObj alpha beta kappa t_rel =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa t_rel by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa X_rel.1 X_rel.2.1 X_rel.2.2 (ne_of_gt hq)]
    have hright :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            (s 0 / qParam m) (s 1) (s 2) := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      exact wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa s (ne_of_gt hq)
    simpa [hleft, hright] using hle
  have hrelInfeas : ¬ parityThreshold m ≤ t_rel 1 + t_rel 2 := by
    intro hfeas
    exact hNoMeet ⟨X_rel.1, X_rel.2.1, X_rel.2.2, hRelMin.1, hRelMin.2,
      by simpa [t_rel] using hfeas⟩
  obtain ⟨htruncFeas, htruncMin⟩ :=
    (trunc_from_minimizer (2 * (m : ℝ)) (parityThreshold m) hd0 hdM
      alpha beta kappa hbetaPos hbetaY hbetaZ hk t_rel hrelS hrelWsMin).2 hrelInfeas
  let t_impl : Fin 3 → ℝ :=
    truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
      (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa)
  let X_impl : ℝ × ℝ × ℝ := (t_impl 0 / qParam m, t_impl 1, t_impl 2)
  have hImplMin : InReducedTriangle m X_impl.1 X_impl.2.1 X_impl.2.2 ∧
      parityThreshold m ≤ X_impl.2.1 + X_impl.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z → parityThreshold m ≤ y + z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
    refine ⟨by simpa [X_impl, t_impl] using simplex_to_reducedTriangle m t_impl hq htruncFeas.1,
      by simpa [X_impl, t_impl] using htruncFeas.2, ?_⟩
    intro x y z hT hpar
    let s : Fin 3 → ℝ := ![qParam m * x, y, z]
    have hsS : InSimplex (2 * (m : ℝ)) s := reducedTriangle_to_simplex m x y z hq0 hT
    have hsTrunc : InTruncSimplex (2 * (m : ℝ)) (parityThreshold m) s :=
      ⟨hsS, by simpa [s] using hpar⟩
    have hle := htruncMin s hsTrunc
    have hleft :
        wsObj alpha beta kappa t_impl =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2 := by
      rw [show wsObj alpha beta kappa t_impl =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa t_impl by rfl]
      rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa t_impl (ne_of_gt hq)]
    have hright :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa x y z (ne_of_gt hq)]
    simpa [t_impl, hleft, hright] using hle
  have hVal := implementableReducedValue_eq_of_min m a b r kappa X_impl hImplMin
  have hobj :
      reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
          X_impl.1 X_impl.2.1 X_impl.2.2 =
        wsObj alpha beta kappa t_impl := by
    rw [show wsObj alpha beta kappa t_impl =
        wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
          kappa t_impl by rfl]
    rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
      kappa t_impl (ne_of_gt hq)]
  rw [hVal, hobj]

-- @node: sharp_roundingLoss_zero_of_even
/-- For even community size, the parity threshold is zero, so every relaxed minimizer
already lies in the implementable reduced slice. -/
lemma sharp_roundingLoss_zero_of_even (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) (hEven : Even m) :
    roundingLossCertificate m a b r kappa = 0 := by
  rw [sharp_roundingLoss_zero_iff_argmin_meets_slice m a b r kappa hHom hk]
  obtain ⟨X_rel, hRelMin⟩ := exists_relaxed_reduced_minimizer m a b r kappa hHom hk
  refine ⟨X_rel.1, X_rel.2.1, X_rel.2.2, hRelMin.1, hRelMin.2, ?_⟩
  rcases hRelMin.1 with ⟨_hx, hy, hz, _hsum⟩
  simp [parityThreshold, hEven, add_nonneg hy hz]

end CausalSmith.Experimentation.DesignPm1
