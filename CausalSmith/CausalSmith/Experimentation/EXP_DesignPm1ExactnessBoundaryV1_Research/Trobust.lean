/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Robust-corner exactness (`thm:robust-corner-exactness`)

Finite-`κ` iid exactness holds iff on the affine-balanced locus `a+3b=2m`,
`r=2b(a+b)`. On the locus, for every `κ > 0`, `I_n` is the unique relaxed minimizer
attained by `P_iid`; off the locus, `I_n` is never a finite-`κ` minimizer but
minimizers converge to `I_n` as `κ → ∞`. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Filter Topology

-- @node: thm:robust-corner-exactness
/-- **Robust-corner exactness.** Under two-block homophily: `I_n` is a minimizer of
`F_{r,κ}` over `E_m^blk` for some finite `κ` iff `a+3b=2m` and `r=2b(a+b)`; on this
locus, for every `κ > 0`, `I_n` is the unique relaxed minimizer and `P_iid ∈ P_m^sym`
attains it with `X(P_iid)=I_n`; off the locus `I_n` is never a finite-`κ` minimizer,
though relaxed minimizers converge (entrywise) to `I_n` as `κ → ∞`.

The iid-exactness frontier `kappa_iid(m,a,b,r)` — the smallest robustness weight from
which `I_n = X(P_iid)` is optimal — has no closed-form decl (bound only as a symbol,
like `r_star`). Its [0,∞) space with `kappa_iid ≥ kappa_cut` is now pinned by the
dedicated carrier predicate `IsIidExactnessFrontier` in `Basic.lean` (the `0 ≤ κ_iid`
and `κ_cut ≤ κ_iid` conjuncts fix the space and ordering, the optimality clause its
frontier role). This theorem supplies the frontier's EXACT finiteness criterion, not its
value: the two tagged clauses below give a finite such weight EXISTS iff the
affine-balanced locus `a+3b=2m ∧ r=2b(a+b)` holds (off-locus `kappa_iid = +∞`), and on
the locus every `κ > 0` is admissible. -/
theorem robust_corner_exactness (m : ℕ) (a b r : ℝ) (hHom : TwoBlockHomophily m a b)
    (hr0 : 0 ≤ r) : -- @realizes r(range 0 ≤ r pins r ∈ [0,∞))
    ((∃ kappa : ℝ, 0 ≤ kappa ∧
        (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) ∈ blockElliptope m a b ∧
        ∀ X ∈ blockElliptope m a b,
          designObjective m a b r kappa 1 ≤ designObjective m a b r kappa X)
      -- @realizes kappa_iid(m,a,b,r)(finiteness criterion: a finite iid-exactness
      -- weight EXISTS iff the affine-balanced locus a+3b=2m ∧ r=2b(a+b); off-locus =+∞)
      ↔ (a + 3 * b = 2 * (m : ℝ) ∧ r = 2 * b * (a + b))) ∧
    ((a + 3 * b = 2 * (m : ℝ) ∧ r = 2 * b * (a + b)) →
      -- @realizes kappa_iid(m,a,b,r)(on-locus value: every κ>0 makes I_n the unique
      -- relaxed minimizer, so the infimal admissible weight kappa_iid = 0 (≥ kappa_cut))
      ∀ kappa : ℝ, 0 < kappa →
        ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) ∈ blockElliptope m a b ∧
          ∀ X ∈ blockElliptope m a b, X ≠ 1 →
            designObjective m a b r kappa 1 < designObjective m a b r kappa X)) ∧
    (iidDesign m ∈ blockExchangeableDesignClass m ∧
      assignmentSecondMoment m (iidDesign m) = 1) ∧
    (¬ (a + 3 * b = 2 * (m : ℝ) ∧ r = 2 * b * (a + b)) →
      (∀ kappa : ℝ, 0 < kappa →
        ¬ (∀ X ∈ blockElliptope m a b,
            designObjective m a b r kappa 1 ≤ designObjective m a b r kappa X)) ∧
      (∀ (Xseq : ℝ → Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ),
        (∀ kappa : ℝ, 0 < kappa → Xseq kappa ∈ blockElliptope m a b ∧
          ∀ X ∈ blockElliptope m a b,
            designObjective m a b r kappa (Xseq kappa) ≤ designObjective m a b r kappa X) →
        ∀ i j, Tendsto (fun kappa => Xseq kappa i j) atTop
          (𝓝 ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) i j)))) := by
  have hiff :
      ((∃ kappa : ℝ, 0 ≤ kappa ∧
          (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) ∈ blockElliptope m a b ∧
          ∀ X ∈ blockElliptope m a b,
            designObjective m a b r kappa 1 ≤ designObjective m a b r kappa X)
        ↔ (a + 3 * b = 2 * (m : ℝ) ∧ r = 2 * b * (a + b))) := by
    constructor
    · rintro ⟨kappa, _hk, _hmem, hmin⟩
      exact robust_locus_of_center_coeffs m a b r hHom
        (center_coeffs_of_identity_relaxed_min m a b r kappa hHom hmin).1
        (center_coeffs_of_identity_relaxed_min m a b r kappa hHom hmin).2
    · intro hloc
      refine ⟨1, by norm_num, ?_, ?_⟩
      · exact (identity_strict_relaxed_min_of_locus m a b r 1 hHom (by norm_num) hloc).1
      · intro X hX
        by_cases hEq : X = (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
        · subst X
          rfl
        · exact le_of_lt
            ((identity_strict_relaxed_min_of_locus m a b r 1 hHom (by norm_num) hloc).2
              X hX hEq)
  refine ⟨hiff, ?_⟩
  refine ⟨?_, ?_⟩
  · intro hloc kappa hk
    exact identity_strict_relaxed_min_of_locus m a b r kappa hHom hk hloc
  refine ⟨?_, ?_⟩
  · exact ⟨iidDesign_mem_blockExchangeable m, iidDesign_secondMoment m⟩
  · intro hnot
    constructor
    · intro kappa hk hmin
      exact hnot (robust_locus_of_center_coeffs m a b r hHom
        (center_coeffs_of_identity_relaxed_min m a b r kappa hHom hmin).1
        (center_coeffs_of_identity_relaxed_min m a b r kappa hHom hmin).2)
    · intro Xseq hXseq i j
      exact robust_minimizers_tendsto_identity_entries m a b r hHom hr0 Xseq hXseq i j

end CausalSmith.Experimentation.DesignPm1
