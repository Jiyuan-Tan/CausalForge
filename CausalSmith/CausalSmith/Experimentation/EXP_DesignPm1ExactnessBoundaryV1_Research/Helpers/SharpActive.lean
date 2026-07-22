/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.GapReduction
import Mathlib.Data.Fin.VecNotation

/-! # Sharp-certificate active-set assembly helpers -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: sharp_reduced_active_set_and_unique
/-- For `κ > 0`, the active-set SOCP certificate gives the unique relaxed minimizer in
reduced coordinates and the relaxed value formula. -/
lemma sharp_reduced_active_set_and_unique (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) (hkpos : 0 < kappa) :
    (∃! t : ℝ × ℝ × ℝ, InReducedTriangle m t.1 t.2.1 t.2.2 ∧
      ∀ x' y' z', InReducedTriangle m x' y' z' →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa t.1 t.2.1 t.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
    (∃ S : Finset (Fin 3), ∃ lam : ℝ,
      IsAdmissibleSupport ![cX m a b r / qParam m, cY b r, cZ m]
        ![1 / qParam m, 1, 1] kappa S lam ∧
      InReducedTriangle m
        (activeSetPoint (2 * (m : ℝ)) ![cX m a b r / qParam m, cY b r, cZ m]
          ![1 / qParam m, 1, 1] S lam 0 / qParam m)
        (activeSetPoint (2 * (m : ℝ)) ![cX m a b r / qParam m, cY b r, cZ m]
          ![1 / qParam m, 1, 1] S lam 1)
        (activeSetPoint (2 * (m : ℝ)) ![cX m a b r / qParam m, cY b r, cZ m]
          ![1 / qParam m, 1, 1] S lam 2) ∧
      (∀ x' y' z', InReducedTriangle m x' y' z' →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            (activeSetPoint (2 * (m : ℝ)) ![cX m a b r / qParam m, cY b r, cZ m]
              ![1 / qParam m, 1, 1] S lam 0 / qParam m)
            (activeSetPoint (2 * (m : ℝ)) ![cX m a b r / qParam m, cY b r, cZ m]
              ![1 / qParam m, 1, 1] S lam 1)
            (activeSetPoint (2 * (m : ℝ)) ![cX m a b r / qParam m, cY b r, cZ m]
              ![1 / qParam m, 1, 1] S lam 2)
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
      relaxedReducedValue m a b r kappa = 2 * (m : ℝ) * lam) := by
  have hm : 2 ≤ m := hHom.1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
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
  obtain ⟨⟨S, lam⟩, hp, _huniqPair⟩ :=
    (weighted_simplex_active_set (2 * (m : ℝ)) hM alpha beta kappa hbetaPos hk).1
      hkpos
  let t0 : Fin 3 → ℝ := activeSetPoint (2 * (m : ℝ)) alpha beta S lam
  let X0 : ℝ × ℝ × ℝ := (t0 0 / qParam m, t0 1, t0 2)
  have ht0S : InSimplex (2 * (m : ℝ)) t0 := by
    simpa [t0] using hp.2.1
  have ht0Strict : ∀ s : Fin 3 → ℝ, InSimplex (2 * (m : ℝ)) s → s ≠ t0 →
      wsObj alpha beta kappa t0 < wsObj alpha beta kappa s := by
    simpa [t0] using hp.2.2.1
  have hMin : InReducedTriangle m X0.1 X0.2.1 X0.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X0.1 X0.2.1 X0.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
    refine ⟨by simpa [X0] using simplex_to_reducedTriangle m t0 hq ht0S, ?_⟩
    intro x y z hT
    let s : Fin 3 → ℝ := ![qParam m * x, y, z]
    have hsS : InSimplex (2 * (m : ℝ)) s := reducedTriangle_to_simplex m x y z hq0 hT
    have hleWs : wsObj alpha beta kappa t0 ≤ wsObj alpha beta kappa s := by
      by_cases hEq : s = t0
      · rw [hEq]
      · exact le_of_lt (ht0Strict s hsS hEq)
    have hleft :
        wsObj alpha beta kappa t0 =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X0.1 X0.2.1 X0.2.2 := by
      rw [show wsObj alpha beta kappa t0 =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa t0 by rfl]
      rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa t0 (ne_of_gt hq)]
    have hright :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa x y z (ne_of_gt hq)]
    simpa [hleft, hright] using hleWs
  have hUnique : ∃! t : ℝ × ℝ × ℝ, InReducedTriangle m t.1 t.2.1 t.2.2 ∧
      ∀ x' y' z', InReducedTriangle m x' y' z' →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa t.1 t.2.1 t.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z' := by
    refine ⟨X0, hMin, ?_⟩
    rintro ⟨x, y, z⟩ ht
    let s : Fin 3 → ℝ := ![qParam m * x, y, z]
    have hsS : InSimplex (2 * (m : ℝ)) s := reducedTriangle_to_simplex m x y z hq0 ht.1
    have hsEq : s = t0 := by
      by_contra hne
      have hlt := ht0Strict s hsS hne
      have hleRed := ht.2 X0.1 X0.2.1 X0.2.2 hMin.1
      have hleft :
          wsObj alpha beta kappa s =
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
        rw [show wsObj alpha beta kappa s =
            wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
              kappa s by rfl]
        rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
          kappa x y z (ne_of_gt hq)]
      have hright :
          wsObj alpha beta kappa t0 =
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              X0.1 X0.2.1 X0.2.2 := by
        rw [show wsObj alpha beta kappa t0 =
            wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
              kappa t0 by rfl]
        rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
          kappa t0 (ne_of_gt hq)]
      have hleWs : wsObj alpha beta kappa s ≤ wsObj alpha beta kappa t0 := by
        simpa [hleft, hright] using hleRed
      exact (not_lt_of_ge hleWs) hlt
    have hx : x = t0 0 / qParam m := by
      have h0 := congrFun hsEq 0
      dsimp [s] at h0
      rw [← h0]
      field_simp [ne_of_gt hq]
    have hy : y = t0 1 := by
      have h1 := congrFun hsEq 1
      simpa [s] using h1
    have hz : z = t0 2 := by
      have h2 := congrFun hsEq 2
      simpa [s] using h2
    ext <;> simp [X0, hx, hy, hz]
  have hRelVal :
      relaxedReducedValue m a b r kappa = 2 * (m : ℝ) * lam := by
    have hval := relaxedReducedValue_eq_of_min m a b r kappa X0 hMin
    have hwsVal :
        wsObj alpha beta kappa t0 = 2 * (m : ℝ) * lam := by
      simpa [t0] using hp.2.2.2
    have hobj :
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X0.1 X0.2.1 X0.2.2 = wsObj alpha beta kappa t0 := by
      rw [show wsObj alpha beta kappa t0 =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa t0 by rfl]
      rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa t0 (ne_of_gt hq)]
    rw [hval, hobj, hwsVal]
  refine ⟨hUnique, S, lam, ?_, ?_, ?_, hRelVal⟩
  · simpa [alpha, beta] using hp.1
  · simpa [X0, t0, alpha, beta] using hMin.1
  · simpa [X0, t0, alpha, beta] using hMin.2

end CausalSmith.Experimentation.DesignPm1
