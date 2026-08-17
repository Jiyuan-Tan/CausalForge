/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs
import Causalean.Mathlib.Optimization.WeightedSimplexKKT
import Causalean.Mathlib.Optimization.WeightedSimplexExists
import Causalean.Mathlib.Optimization.WeightedSimplexFace

/-! # Weighted-simplex active-set SOCP

This file packages the active-set/KKT solution of the linear-plus-weighted-norm
second-order cone program
`min_{t ∈ Δ_M} Σ αᵢ tᵢ + κ √(Σ βᵢ tᵢ²)` over the three-point simplex.  Strict
convexity for `κ > 0` gives a unique minimizer, realized by the admissible
support/multiplier pair; for `κ = 0`, the minimizer set is the exposed
`α`-minimizing face.  The headline theorem is `weighted_simplex_active_set`.

The shared definitions live in `SimplexActiveSetDefs`; the analytic content lives
in `WeightedSimplexKKT` (`κ > 0` optimality), `WeightedSimplexExists` (admissible
support existence), and `WeightedSimplexFace` (`κ = 0` face). -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

-- @node: lem:weighted-simplex-active-set
/-- **Weighted-simplex active-set solution.** Fix [a positive total simplex mass `M`](hyp:hM),
linear weights `α`, [coordinate weights `β` that are all strictly positive](hyp:hβ), and
[a nonnegative regularization parameter `κ`](hyp:hk0), and consider minimizing the
second-order-cone objective `Σ αᵢtᵢ + κ·√(Σβᵢtᵢ²)` over the three-point simplex `Δ_M` of total
mass `M`. Then [the following two facts hold: whenever `κ` is strictly positive, there is a
*unique* admissible support/multiplier pair `(S, λ)`, its induced active-set point lies in
`Δ_M` and is the *unique* global minimizer of the objective, with optimal value the closed
form `M · λ`; and whenever `κ` equals zero, a point of `Δ_M` minimizes the objective exactly
when it lies on the exposed `α`-minimizing face](goal). This encodes the displayed KKT
coordinate formula, the uniqueness of the admissible support, the value formula, and the
`κ = 0` face clause. -/
lemma weighted_simplex_active_set (M : ℝ) (hM : 0 < M)
    (α β : Fin 3 → ℝ) (kappa : ℝ)
    (hβ : ∀ i, 0 < β i) (hk0 : 0 ≤ kappa) :
    (0 < kappa →
      ∃! p : Finset (Fin 3) × ℝ,
        IsAdmissibleSupport α β kappa p.1 p.2 ∧
        InSimplex M (activeSetPoint M α β p.1 p.2) ∧
        (∀ s : Fin 3 → ℝ, InSimplex M s → s ≠ activeSetPoint M α β p.1 p.2 →
          wsObj α β kappa (activeSetPoint M α β p.1 p.2) < wsObj α β kappa s) ∧
        wsObj α β kappa (activeSetPoint M α β p.1 p.2) = M * p.2) ∧
    (kappa = 0 →
      ∀ t : Fin 3 → ℝ,
        (InSimplex M t ∧
            ∀ s : Fin 3 → ℝ, InSimplex M s → wsObj α β kappa t ≤ wsObj α β kappa s)
          ↔ t ∈ exposedMinFace M α) := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · -- κ > 0: unique admissible pair, active-set point is the strict minimizer, value M·λ.
    obtain ⟨S, lam, hadm⟩ := exists_admissible α β kappa hβ hk
    refine ⟨(S, lam), ⟨hadm,
      activeSetPoint_mem M α β S lam hM.le (fun i _ => hβ i) hadm.1 hadm.2.2.1,
      activeSetPoint_strict_min M α β kappa S lam hM hβ hk hadm,
      activeSetPoint_value M α β kappa S lam hM.le (fun i _ => hβ i) hk
        hadm.1 hadm.2.2.1 hadm.2.1⟩, ?_⟩
    rintro ⟨S', lam'⟩ ⟨hadm', hmem', hmin', hval'⟩
    -- The two active-set points coincide (each is the strict minimizer of the SOCP).
    set t := activeSetPoint M α β S lam with ht
    set t' := activeSetPoint M α β S' lam' with ht'
    have hmin : ∀ s : Fin 3 → ℝ, InSimplex M s → s ≠ t →
        wsObj α β kappa t < wsObj α β kappa s :=
      activeSetPoint_strict_min M α β kappa S lam hM hβ hk hadm
    have htt' : t = t' := by
      by_contra hne
      have h1 : wsObj α β kappa t < wsObj α β kappa t' :=
        hmin t' (activeSetPoint_mem M α β S' lam' hM.le (fun i _ => hβ i)
          hadm'.1 hadm'.2.2.1) (fun h => hne h.symm)
      have h2 : wsObj α β kappa t' < wsObj α β kappa t :=
        hmin' t (activeSetPoint_mem M α β S lam hM.le (fun i _ => hβ i)
          hadm.1 hadm.2.2.1) (fun h => hne h)
      exact lt_irrefl _ (h1.trans h2)
    -- Supports agree: `i ∈ S ↔ 0 < tᵢ = t'ᵢ ↔ i ∈ S'`.
    have hSS' : S = S' := by
      ext i
      rw [← activeSetPoint_pos_iff M α β S lam hM (fun i _ => hβ i)
            hadm.1 hadm.2.2.1 i,
          ← activeSetPoint_pos_iff M α β S' lam' hM (fun i _ => hβ i)
            hadm'.1 hadm'.2.2.1 i, ← ht, ← ht', htt']
    -- Multipliers agree via the value formula `M·λ = wsObj t = wsObj t' = M·λ'`.
    have hlam : lam = lam' := by
      have hv : M * lam = M * lam' := by
        rw [← activeSetPoint_value M α β kappa S lam hM.le (fun i _ => hβ i) hk
              hadm.1 hadm.2.2.1 hadm.2.1, ← ht, htt', ht',
            activeSetPoint_value M α β kappa S' lam' hM.le (fun i _ => hβ i) hk
              hadm'.1 hadm'.2.2.1 hadm'.2.1]
      exact mul_left_cancel₀ (ne_of_gt hM) hv
    exact Prod.ext hSS'.symm hlam.symm
  · -- κ = 0: minimizer set is the exposed α-minimizing face.
    subst hk
    intro t
    simpa [wsObj] using kappa_zero_face M α t

end Causalean.Mathlib.Optimization
