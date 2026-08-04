/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs
import Causalean.Mathlib.Optimization.WeightedSimplexFace
import Causalean.Mathlib.Analysis.WeightedCauchySchwarz
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Weighted-simplex truncation: relaxed global minimizers

Self-contained proofs that the two relaxed-optimum descriptions used by the
truncation lemma really are global minimizers of `wsObj` over the full simplex
`Δ_M`, so the truncation argument does not depend on `weighted_simplex_active_set`:

* `activeSetPoint_isMinimizer` (`κ > 0`): any KKT-admissible support/multiplier pair
  induces a simplex point that globally minimizes `wsObj`. The optimality is a
  Cauchy–Schwarz (weighted ℓ²) certificate: `κ β_i t*_i / ‖t*‖_β = λ − α_i` on the
  support and `α_j ≥ λ` off it, so the first-order (subgradient) inequality collapses
  to `λ·(Σ s − M) = 0`.
* `exposedMinFace_isMinimizer` (`κ = 0`): a point of the exposed `α`-minimizing face
  minimizes the (now purely linear) objective, since its mass sits on `argmin α`. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

/-- **KKT admissible ⟹ global minimizer (`κ > 0`).** For positive weights and a
KKT-admissible support/multiplier pair `(S, λ)`, the induced active-set point lies in
`Δ_M` and globally minimizes the SOCP objective `wsObj` there. -/
lemma activeSetPoint_isMinimizer (M : ℝ) (hM : 0 < M) (α β : Fin 3 → ℝ) (kappa : ℝ)
    (hβ : ∀ i, 0 < β i) (hkpos : 0 < kappa)
    (S : Finset (Fin 3)) (lam : ℝ) (hadm : IsAdmissibleSupport α β kappa S lam) :
    InSimplex M (activeSetPoint M α β S lam) ∧
    ∀ s : Fin 3 → ℝ, InSimplex M s →
      wsObj α β kappa (activeSetPoint M α β S lam) ≤ wsObj α β kappa s := by
  classical
  rcases hadm with ⟨hSne, hsum, hact, hoff⟩
  let t : Fin 3 → ℝ := activeSetPoint M α β S lam
  let D : ℝ := ∑ h ∈ S, (lam - α h) / β h
  have hDpos : 0 < D := by
    dsimp [D]
    exact Finset.sum_pos
      (fun i hi => div_pos (sub_pos.mpr (hact i hi)) (hβ i)) hSne
  have htS : ∀ i, i ∈ S → t i = M * ((lam - α i) / β i) / D := by
    intro i hi
    simp [t, activeSetPoint, hi, D]
  have htOff : ∀ i, i ∉ S → t i = 0 := by
    intro i hi
    simp [t, activeSetPoint, hi]
  have htpos : ∀ i, i ∈ S → 0 < t i := by
    intro i hi
    rw [htS i hi]
    exact div_pos (mul_pos hM (div_pos (sub_pos.mpr (hact i hi)) (hβ i))) hDpos
  have ht_nonneg : ∀ i, 0 ≤ t i := by
    intro i
    by_cases hi : i ∈ S
    · exact (htpos i hi).le
    · rw [htOff i hi]
  have hsum_t_support :
      (∑ i, t i) = ∑ i ∈ S, M * ((lam - α i) / β i) / D := by
    calc
      (∑ i, t i) = ∑ i, if i ∈ S then M * ((lam - α i) / β i) / D else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [hi, htS i hi]
        · simp [hi, htOff i hi]
      _ = ∑ i ∈ S, M * ((lam - α i) / β i) / D := by
        simp
  have hsum_t : ∑ i, t i = M := by
    rw [hsum_t_support]
    calc
      (∑ i ∈ S, M * ((lam - α i) / β i) / D)
          = ∑ i ∈ S, (M / D) * ((lam - α i) / β i) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [hDpos.ne']
      _ = (M / D) * ∑ i ∈ S, (lam - α i) / β i := by
        rw [Finset.mul_sum]
      _ = (M / D) * D := by
        rfl
      _ = M := by
        field_simp [hDpos.ne']
  have ht_simplex : InSimplex M t := ⟨ht_nonneg, hsum_t⟩
  refine ⟨ht_simplex, ?_⟩
  intro s hs
  let Nt : ℝ := Real.sqrt (∑ i, β i * t i ^ 2)
  let Ns : ℝ := Real.sqrt (∑ i, β i * s i ^ 2)
  have ht_sq_nonneg : 0 ≤ ∑ i, β i * t i ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hβ i).le (sq_nonneg (t i)))
  have hs_sq_nonneg : 0 ≤ ∑ i, β i * s i ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hβ i).le (sq_nonneg (s i)))
  have hNt_sq : Nt ^ 2 = ∑ i, β i * t i ^ 2 := by
    dsimp [Nt]
    rw [Real.sq_sqrt ht_sq_nonneg]
  have hNs_sq : Ns ^ 2 = ∑ i, β i * s i ^ 2 := by
    dsimp [Ns]
    rw [Real.sq_sqrt hs_sq_nonneg]
  have hquad_support :
      (∑ i, β i * t i ^ 2) =
        ∑ i ∈ S, β i * (M * ((lam - α i) / β i) / D) ^ 2 := by
    calc
      (∑ i, β i * t i ^ 2) =
          ∑ i, if i ∈ S then β i * (M * ((lam - α i) / β i) / D) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [hi, htS i hi]
        · simp [hi, htOff i hi]
      _ = ∑ i ∈ S, β i * (M * ((lam - α i) / β i) / D) ^ 2 := by
        simp
  have hquad :
      (∑ i, β i * t i ^ 2) = M ^ 2 * kappa ^ 2 / D ^ 2 := by
    rw [hquad_support]
    calc
      (∑ i ∈ S, β i * (M * ((lam - α i) / β i) / D) ^ 2)
          = ∑ i ∈ S, (M ^ 2 / D ^ 2) * ((lam - α i) ^ 2 / β i) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(hβ i).ne', hDpos.ne']
      _ = (M ^ 2 / D ^ 2) * ∑ i ∈ S, (lam - α i) ^ 2 / β i := by
        rw [Finset.mul_sum]
      _ = (M ^ 2 / D ^ 2) * kappa ^ 2 := by
        rw [hsum]
      _ = M ^ 2 * kappa ^ 2 / D ^ 2 := by
        field_simp [hDpos.ne']
  have hNt_nonneg : 0 ≤ Nt := by
    dsimp [Nt]
    exact Real.sqrt_nonneg _
  have hNt_formula : Nt = M * kappa / D := by
    have hright_nonneg : 0 ≤ M * kappa / D := by positivity
    apply (Real.sqrt_eq_iff_mul_self_eq ht_sq_nonneg hright_nonneg).2
    rw [hquad]
    field_simp [hDpos.ne']
  have hNtpos : 0 < Nt := by
    rw [hNt_formula]
    positivity
  have hcoord : ∀ i, i ∈ S → kappa * (β i * t i) = (lam - α i) * Nt := by
    intro i hi
    rw [htS i hi, hNt_formula]
    field_simp [(hβ i).ne', hDpos.ne']
  have hCS : (∑ i, β i * t i * s i) ≤ Nt * Ns := by
    exact (le_abs_self _).trans (by
      simpa [Nt, Ns, mul_assoc] using
        Causalean.Mathlib.Analysis.abs_weighted_inner_le
          (Finset.univ : Finset (Fin 3)) β t s (fun i _ => (hβ i).le))
  have hcross_eq : ∀ y : Fin 3 → ℝ,
      kappa * (∑ i, β i * t i * y i) =
        Nt * ∑ i ∈ S, (lam - α i) * y i := by
    intro y
    calc
      kappa * (∑ i, β i * t i * y i)
          = ∑ i, (kappa * (β i * t i)) * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, if i ∈ S then ((lam - α i) * Nt) * y i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [hi, hcoord i hi]
        · simp [hi, htOff i hi]
      _ = ∑ i ∈ S, ((lam - α i) * Nt) * y i := by
        simp
      _ = Nt * ∑ i ∈ S, (lam - α i) * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hsupport_s_bound : (∑ i ∈ S, (lam - α i) * s i) ≤ kappa * Ns := by
    have hmul := mul_le_mul_of_nonneg_left hCS hkpos.le
    rw [hcross_eq s] at hmul
    have hmul' : Nt * (∑ i ∈ S, (lam - α i) * s i) ≤ Nt * (kappa * Ns) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact le_of_mul_le_mul_left hmul' hNtpos
  have hcross_tt : (∑ i, β i * t i * t i) = Nt ^ 2 := by
    calc
      (∑ i, β i * t i * t i) = ∑ i, β i * t i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = Nt ^ 2 := hNt_sq.symm
  have hsupport_t_eq : (∑ i ∈ S, (lam - α i) * t i) = kappa * Nt := by
    have h := hcross_eq t
    rw [hcross_tt] at h
    have h' : Nt * (∑ i ∈ S, (lam - α i) * t i) = Nt * (kappa * Nt) := by
      calc
        Nt * (∑ i ∈ S, (lam - α i) * t i) = kappa * Nt ^ 2 := h.symm
        _ = Nt * (kappa * Nt) := by ring
    exact mul_left_cancel₀ hNtpos.ne' h'
  have hsum_t_compl : (∑ i ∈ Sᶜ, t i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact htOff i (by simpa using hi)
  have hsum_t_S : (∑ i ∈ S, t i) = M := by
    calc
      (∑ i ∈ S, t i) = (∑ i, t i) := by
        rw [← Finset.sum_add_sum_compl S t, hsum_t_compl, add_zero]
      _ = M := hsum_t
  have halpha_t_compl : (∑ i ∈ Sᶜ, α i * t i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [htOff i (by simpa using hi)]
  have halpha_t_support : (∑ i, α i * t i) = ∑ i ∈ S, α i * t i := by
    rw [← Finset.sum_add_sum_compl S (fun i => α i * t i), halpha_t_compl, add_zero]
  have hvalue_t : wsObj α β kappa t = lam * M := by
    calc
      wsObj α β kappa t = (∑ i, α i * t i) + kappa * Nt := by
        simp [wsObj, Nt]
      _ = (∑ i ∈ S, α i * t i) + ∑ i ∈ S, (lam - α i) * t i := by
        rw [halpha_t_support, hsupport_t_eq]
      _ = ∑ i ∈ S, lam * t i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = lam * ∑ i ∈ S, t i := by
        rw [Finset.mul_sum]
      _ = lam * M := by
        rw [hsum_t_S]
  have hoff_s_bound : (∑ i ∈ Sᶜ, lam * s i) ≤ ∑ i ∈ Sᶜ, α i * s i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hoff i (by simpa using hi)) (hs.1 i)
  have hlinear_s_bound :
      lam * M ≤ (∑ i, α i * s i) + ∑ i ∈ S, (lam - α i) * s i := by
    have hsplit_lam := Finset.sum_add_sum_compl S (fun i => lam * s i)
    have hsplit_alpha := Finset.sum_add_sum_compl S (fun i => α i * s i)
    have hactive :
        (∑ i ∈ S, α i * s i) + ∑ i ∈ S, (lam - α i) * s i =
          ∑ i ∈ S, lam * s i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hfull_lam : (∑ i, lam * s i) = lam * M := by
      calc
        (∑ i, lam * s i) = lam * ∑ i, s i := by
          rw [Finset.mul_sum]
        _ = lam * M := by
          rw [hs.2]
    calc
      lam * M = ∑ i, lam * s i := hfull_lam.symm
      _ = (∑ i ∈ S, lam * s i) + ∑ i ∈ Sᶜ, lam * s i := hsplit_lam.symm
      _ ≤ (∑ i ∈ S, lam * s i) + ∑ i ∈ Sᶜ, α i * s i := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hoff_s_bound (∑ i ∈ S, lam * s i)
      _ = (∑ i, α i * s i) + ∑ i ∈ S, (lam - α i) * s i := by
        rw [← hactive, ← hsplit_alpha]
        ring
  have hvalue_s : lam * M ≤ wsObj α β kappa s := by
    calc
      lam * M ≤ (∑ i, α i * s i) + ∑ i ∈ S, (lam - α i) * s i :=
        hlinear_s_bound
      _ ≤ (∑ i, α i * s i) + kappa * Ns := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hsupport_s_bound (∑ i, α i * s i)
      _ = wsObj α β kappa s := by
        simp [wsObj, Ns]
  calc
    wsObj α β kappa (activeSetPoint M α β S lam) = wsObj α β kappa t := by
      simp [t]
    _ = lam * M := hvalue_t
    _ ≤ wsObj α β kappa s := hvalue_s

/-- **Exposed face ⟹ global minimizer (`κ = 0`).** A point of the exposed
`α`-minimizing face globally minimizes the linear objective `wsObj α β 0` over `Δ_M`. -/
lemma exposedMinFace_isMinimizer (M : ℝ) (α β : Fin 3 → ℝ)
    (t_rel : Fin 3 → ℝ) (hface : t_rel ∈ exposedMinFace M α) :
    ∀ s : Fin 3 → ℝ, InSimplex M s →
      wsObj α β 0 t_rel ≤ wsObj α β 0 s := by
  simpa [wsObj] using ((kappa_zero_face M α t_rel).2 hface).2

end Causalean.Mathlib.Optimization
