/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexTruncationConvex
import Causalean.Mathlib.Optimization.SimplexTruncationSlice
import Causalean.Mathlib.Optimization.SimplexTruncationMinimizers

/-! # Weighted-simplex truncation

This file packages the constrained minimizer of the weighted-simplex SOCP over
the parity-truncated simplex `K_d = {t ∈ Δ_M : t_y + t_z ≥ d}`.  If the relaxed
optimum over `Δ_M` is feasible, it is also optimal over `K_d`; otherwise an
optimum lies on the boundary segment `H_d` with the explicit endpoint/interior
selector `sStar` from the 1-D convex slice.  The headline theorem is
`weighted_simplex_truncation`, with `trunc_from_minimizer` as the reusable
relaxed-minimizer dichotomy.

The definitions (`InTruncSimplex`, `truncSegPoint`, `truncSelector`) live in
`SimplexTruncationDefs`; the convexity/boundary-reduction step in
`SimplexTruncationConvex`; the 1-D slice minimization in `SimplexTruncationSlice`;
and the relaxed-optimum global-minimizer certificates in
`SimplexTruncationMinimizers`. This file glues them into a single dichotomy
(`trunc_from_minimizer`) and the headline lemma. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

/-- **Truncation dichotomy from a relaxed minimizer.** Given any `t_rel ∈ Δ_M` that
globally minimizes `wsObj` over `Δ_M`, the constrained problem over `K_d` splits:
if `t_rel ∈ K_d` it is already optimal there; otherwise (`t_rel` infeasible) the
face selector `truncSegPoint M d sStar` is feasible and optimal over `K_d`. This is the
κ-agnostic core shared by the `κ > 0` and `κ = 0` branches of the headline lemma. -/
lemma trunc_from_minimizer (M d : ℝ) (hd0 : 0 ≤ d) (hdM : d ≤ M)
    (α β : Fin 3 → ℝ) (kappa : ℝ)
    (hβ : ∀ i, 0 < β i) (hβy : β 1 = 1) (hβz : β 2 = 1) (hk : 0 ≤ kappa)
    (t_rel : Fin 3 → ℝ) (hrel : InSimplex M t_rel)
    (hmin : ∀ s, InSimplex M s → wsObj α β kappa t_rel ≤ wsObj α β kappa s) :
    (InTruncSimplex M d t_rel →
        ∀ s : Fin 3 → ℝ, InTruncSimplex M d s →
          wsObj α β kappa t_rel ≤ wsObj α β kappa s) ∧
    (¬ (d ≤ t_rel 1 + t_rel 2) →
        InTruncSimplex M d (truncSegPoint M d (truncSelector M d α β kappa)) ∧
        ∀ s : Fin 3 → ℝ, InTruncSimplex M d s →
          wsObj α β kappa (truncSegPoint M d (truncSelector M d α β kappa))
            ≤ wsObj α β kappa s) := by
  have hβnn : ∀ i, 0 ≤ β i := fun i => (hβ i).le
  refine ⟨fun _ s hs => hmin s hs.1, ?_⟩
  intro hinf'
  have hinf : t_rel 1 + t_rel 2 < d := not_le.mp hinf'
  have hdpos : 0 < d := by
    have h1 := hrel.1 1; have h2 := hrel.1 2; linarith
  obtain ⟨hs0, hsd⟩ := truncSelector_mem M d α β kappa hdpos (hβ 0).le hk
  set sStar := truncSelector M d α β kappa with hsStar
  have e0 : truncSegPoint M d sStar 0 = M - d := by simp [truncSegPoint]
  have e1 : truncSegPoint M d sStar 1 = sStar := by simp [truncSegPoint]
  have e2 : truncSegPoint M d sStar 2 = d - sStar := by simp [truncSegPoint]
  have n0 : 0 ≤ truncSegPoint M d sStar 0 := by rw [e0]; linarith
  have n1 : 0 ≤ truncSegPoint M d sStar 1 := by rw [e1]; linarith
  have n2 : 0 ≤ truncSegPoint M d sStar 2 := by rw [e2]; linarith
  have hfeas : InTruncSimplex M d (truncSegPoint M d sStar) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · exact n0
      · exact n1
      · exact n2
    · rw [Fin.sum_univ_three, e0, e1, e2]; ring
    · rw [e1, e2]; linarith
  refine ⟨hfeas, ?_⟩
  intro s hs
  obtain ⟨σ, hσ0, hσd, hred⟩ :=
    truncSeg_reduction M d kappa α β hd0 hdM hβnn hk t_rel hrel hmin hinf s hs
  calc wsObj α β kappa (truncSegPoint M d sStar)
      ≤ wsObj α β kappa (truncSegPoint M d σ) :=
        truncSeg_selector_le M d α β kappa hdpos (hβ 0).le hβy hβz hk σ hσ0 hσd
    _ ≤ wsObj α β kappa s := hred

-- @node: lem:weighted-simplex-truncation
/-- **Weighted-simplex truncation.** In the notation of `weighted_simplex_active_set`,
for any positive simplex mass `M`, positive coordinate weights `β` with
`β_y = β_z = 1`, and `0 ≤ κ`.

*`κ > 0`:* let `(S, λ)` be admissible relaxed data and `t_rel` the induced
active-set point. If `t_rel ∈ K_d` it already minimizes over `K_d`; otherwise the
constrained optimum is `truncSegPoint M d sStar` at the endpoint/interior selector
`sStar = truncSelector`, feasible and minimizing over `K_d`.

*`κ = 0`:* the relaxed argmin set is the exposed `α`-minimizing face. If the chosen
face point `t_rel` lies in `K_d` it minimizes over `K_d`; otherwise the constrained
optimum is `truncSegPoint M d sStar` with the `κ = 0` endpoint rule `sStar = 0` if
`δ ≥ 0`, `sStar = d` if `δ ≤ 0` (the `κ = 0` value of `truncSelector`).

This encodes the displayed boundary-segment value/selector formula for both
`κ > 0` and the `κ = 0` truncation case. -/
lemma weighted_simplex_truncation (M d : ℝ) (hM : 0 < M)
    (hd0 : 0 ≤ d) (hdM : d ≤ M)
    (α β : Fin 3 → ℝ) (kappa : ℝ)
    (hβ : ∀ i, 0 < β i)
    (hβy : β 1 = 1) (hβz : β 2 = 1) (hk : 0 ≤ kappa) :
    (0 < kappa → ∀ (S : Finset (Fin 3)) (lam : ℝ),
        IsAdmissibleSupport α β kappa S lam →
      (InTruncSimplex M d (activeSetPoint M α β S lam) →
        ∀ s : Fin 3 → ℝ, InTruncSimplex M d s →
          wsObj α β kappa (activeSetPoint M α β S lam) ≤ wsObj α β kappa s) ∧
      (¬ (d ≤ activeSetPoint M α β S lam 1 + activeSetPoint M α β S lam 2) →
        InTruncSimplex M d (truncSegPoint M d (truncSelector M d α β kappa)) ∧
        ∀ s : Fin 3 → ℝ, InTruncSimplex M d s →
          wsObj α β kappa (truncSegPoint M d (truncSelector M d α β kappa))
            ≤ wsObj α β kappa s)) ∧
    (kappa = 0 → ∀ t_rel : Fin 3 → ℝ, t_rel ∈ exposedMinFace M α →
      (InTruncSimplex M d t_rel →
        ∀ s : Fin 3 → ℝ, InTruncSimplex M d s →
          wsObj α β kappa t_rel ≤ wsObj α β kappa s) ∧
      (¬ (d ≤ t_rel 1 + t_rel 2) →
        InTruncSimplex M d (truncSegPoint M d (truncSelector M d α β kappa)) ∧
        ∀ s : Fin 3 → ℝ, InTruncSimplex M d s →
          wsObj α β kappa (truncSegPoint M d (truncSelector M d α β kappa))
            ≤ wsObj α β kappa s)) := by
  constructor
  · -- κ > 0
    intro hkpos S lam hadm
    obtain ⟨hsimp, hmin⟩ :=
      activeSetPoint_isMinimizer M hM α β kappa hβ hkpos S lam hadm
    exact trunc_from_minimizer M d hd0 hdM α β kappa hβ hβy hβz hk _ hsimp hmin
  · -- κ = 0
    intro hk0 t_rel hface
    subst hk0
    have hsimp : InSimplex M t_rel := hface.1
    have hmin : ∀ s, InSimplex M s → wsObj α β 0 t_rel ≤ wsObj α β 0 s :=
      exposedMinFace_isMinimizer M hM α β t_rel hface
    exact trunc_from_minimizer M d hd0 hdM α β 0 hβ hβy hβz le_rfl _ hsimp hmin

end Causalean.Mathlib.Optimization
