/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.GapReduction
import Mathlib.Data.Fin.VecNotation

/-! # Sharp-certificate zero-loss and exposed-face helpers -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: sharp_roundingLoss_zero_iff_argmin_meets_slice
/-- The rounding-loss carrier has zero value exactly when a relaxed reduced minimizer
meets the parity slice. -/
lemma sharp_roundingLoss_zero_iff_argmin_meets_slice (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) :
    roundingLossCertificate m a b r kappa = 0 ↔
      ∃ x y z, InReducedTriangle m x y z ∧
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
        parityThreshold m ≤ y + z := by
  rw [roundingLossCertificate, ← rounding_gap_reduction m a b r kappa hHom hk]
  exact zero_gap_iff_argmin_meets_slice m a b r kappa hHom hk

-- @node: sharp_roundingLoss_zero_iff_unique_argmin_subset_slice
/-- In the unique-relaxed-minimizer case, zero rounding loss is equivalent to every
relaxed minimizer lying in the parity slice. -/
lemma sharp_roundingLoss_zero_iff_unique_argmin_subset_slice (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) (hkpos : 0 < kappa)
    (hRelUnique : ∃! t : ℝ × ℝ × ℝ,
      InReducedTriangle m t.1 t.2.1 t.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              t.1 t.2.1 t.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z) :
    roundingLossCertificate m a b r kappa = 0 ↔
      ∀ x y z, InReducedTriangle m x y z →
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') →
        parityThreshold m ≤ y + z := by
  rw [roundingLossCertificate, ← rounding_gap_reduction m a b r kappa hHom hk]
  exact zero_gap_iff_unique_argmin_subset_slice m a b r kappa hHom hk hkpos hRelUnique

-- @node: sharp_kappa_zero_reduced_min_iff
/-- At `κ = 0`, reduced minimizers are exactly the exposed face of the minimum
coordinates of `α = (c_x/q, c_y, c_z)`. -/
lemma sharp_kappa_zero_reduced_min_iff (m : ℕ) (a b r kappa x y z : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk0 : kappa = 0)
    (hT : InReducedTriangle m x y z) :
    ((∀ x' y' z', InReducedTriangle m x' y' z' →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z')
      ↔ (x ≠ 0 → cX m a b r / qParam m ≤ cY b r ∧ cX m a b r / qParam m ≤ cZ m) ∧
        (y ≠ 0 → cY b r ≤ cX m a b r / qParam m ∧ cY b r ≤ cZ m) ∧
        (z ≠ 0 → cZ m ≤ cX m a b r / qParam m ∧ cZ m ≤ cY b r)) := by
  subst kappa
  have hm : 2 ≤ m := hHom.1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hq0 : 0 ≤ qParam m := le_of_lt hq
  have hM : 0 < 2 * (m : ℝ) := by positivity
  let alpha : Fin 3 → ℝ := ![cX m a b r / qParam m, cY b r, cZ m]
  let beta : Fin 3 → ℝ := ![1 / qParam m, 1, 1]
  let t : Fin 3 → ℝ := ![qParam m * x, y, z]
  have htS : InSimplex (2 * (m : ℝ)) t := reducedTriangle_to_simplex m x y z hq0 hT
  constructor
  · intro hMin
    have hwsMin : ∀ s : Fin 3 → ℝ, InSimplex (2 * (m : ℝ)) s →
        wsObj alpha beta 0 t ≤ wsObj alpha beta 0 s := by
      intro s hs
      have hsRed := simplex_to_reducedTriangle m s hq hs
      have hle := hMin (s 0 / qParam m) (s 1) (s 2) hsRed
      have hleft :
          wsObj alpha beta 0 t =
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0 x y z := by
        rw [show wsObj alpha beta 0 t =
            wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
              0 t by rfl]
        rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
          0 x y z (ne_of_gt hq)]
      have hright :
          wsObj alpha beta 0 s =
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0
              (s 0 / qParam m) (s 1) (s 2) := by
        rw [show wsObj alpha beta 0 s =
            wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
              0 s by rfl]
        exact wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
          0 s (ne_of_gt hq)
      simpa [hleft, hright] using hle
    have hface : t ∈ exposedMinFace (2 * (m : ℝ)) alpha :=
      (kappa_zero_face (2 * (m : ℝ)) hM alpha beta t).1 ⟨htS, hwsMin⟩
    rcases hface with ⟨_htS, hsupport⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hx
      have ht0 : t 0 ≠ 0 := by
        intro ht0
        have hx0 : x = 0 := by
          have : qParam m * x = 0 := by simpa [t] using ht0
          exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hq)
        exact hx hx0
      exact ⟨by simpa [alpha] using hsupport 0 ht0 1,
        by simpa [alpha] using hsupport 0 ht0 2⟩
    · intro hy
      have ht1 : t 1 ≠ 0 := by simpa [t] using hy
      exact ⟨by simpa [alpha] using hsupport 1 ht1 0,
        by simpa [alpha] using hsupport 1 ht1 2⟩
    · intro hz
      have ht2 : t 2 ≠ 0 := by simpa [t] using hz
      exact ⟨by simpa [alpha] using hsupport 2 ht2 0,
        by simpa [alpha] using hsupport 2 ht2 1⟩
  · rintro ⟨hxMin, hyMin, hzMin⟩
    have hface : t ∈ exposedMinFace (2 * (m : ℝ)) alpha := by
      refine ⟨htS, ?_⟩
      intro i hti j
      fin_cases i <;> fin_cases j <;> simp [alpha]
      · exact (hxMin (by
          intro hx
          exact hti (by simp [t, hx]))).1
      · exact (hxMin (by
          intro hx
          exact hti (by simp [t, hx]))).2
      · exact (hyMin (by simpa [t] using hti)).1
      · exact (hyMin (by simpa [t] using hti)).2
      · exact (hzMin (by simpa [t] using hti)).1
      · exact (hzMin (by simpa [t] using hti)).2
    have hwsMin := (kappa_zero_face (2 * (m : ℝ)) hM alpha beta t).2 hface
    intro x' y' z' hT'
    let s : Fin 3 → ℝ := ![qParam m * x', y', z']
    have hsS : InSimplex (2 * (m : ℝ)) s := reducedTriangle_to_simplex m x' y' z' hq0 hT'
    have hle := hwsMin.2 s hsS
    have hleft :
        wsObj alpha beta 0 t =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0 x y z := by
      rw [show wsObj alpha beta 0 t =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            0 t by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        0 x y z (ne_of_gt hq)]
    have hright :
        wsObj alpha beta 0 s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0 x' y' z' := by
      rw [show wsObj alpha beta 0 s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            0 s by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        0 x' y' z' (ne_of_gt hq)]
    simpa [hleft, hright] using hle

end CausalSmith.Experimentation.DesignPm1
