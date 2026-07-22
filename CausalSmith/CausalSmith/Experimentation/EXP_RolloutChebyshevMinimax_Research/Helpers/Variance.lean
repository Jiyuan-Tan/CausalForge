/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variance helpers: TV-envelope sharpness and the envelope-to-exact-risk bridge

`lem:variance-envelope-sharpness` and `lem:exact-risk-envelope-upper`.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Amplification
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Pointwise
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: lem:variance-envelope-sharpness
/-- Total-variation variance envelope **and its sharpness**: if the round statistics
`X₀,...,X_k` satisfy the per-round envelope `Var_pi(X_j) ≤ σ₀²/n` (the threaded assumption
`RoundMeanVarianceEnvelope`), then `Var_pi(∑ⱼ wⱼ Xⱼ) ≤ (σ₀²/n)(∑ⱼ|wⱼ|)²` for every real `w`,
via the `L²(π)` triangle inequality.

Moreover the bound is **sharp** over the diagonal variance envelope: there is a positive
semidefinite (rank-one) covariance matrix `Γ` with every diagonal entry bounded by `σ₀²/n`
whose quadratic form `w'Γw = ∑ᵢ∑ⱼ wᵢ Γᵢⱼ wⱼ` equals `(σ₀²/n)(∑ⱼ|wⱼ|)²`, so no smaller
envelope constant is possible. (Witness `Γ = (σ₀²/n)·ssᵀ` with `sⱼ = sign wⱼ`; the sign
constraint `0 ≤ σ₀²` is the round-mean variance constant's range `σ₀² ∈ ℝ₊`.) -/
lemma variance_envelope_sharpness (n k : ℕ) {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (X : Fin (k + 1) → Ω → ℝ) (sigma0sq : ℝ) (w : Fin (k + 1) → ℝ)
    (hsig : 0 ≤ sigma0sq)
    (hvar : RoundMeanVarianceEnvelope n k D X sigma0sq) :
    D.Var (fun z => ∑ j, w j * X j z) ≤ sigma0sq / (n : ℝ) * (∑ j, |w j|) ^ 2 ∧
      ∃ Γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, Γ.PosSemidef ∧
        (∀ j, Γ j j ≤ sigma0sq / (n : ℝ)) ∧
        (∑ i, ∑ j, w i * Γ i j * w j) = sigma0sq / (n : ℝ) * (∑ j, |w j|) ^ 2 := by
  classical
  let s : ℝ := sigma0sq / (n : ℝ)
  have hs : 0 ≤ s := div_nonneg hsig (Nat.cast_nonneg n)
  have hvar_nonneg : ∀ Y : Ω → ℝ, 0 ≤ D.Var Y := by
    intro Y
    unfold FiniteDesign.Var
    exact D.E_nonneg (fun z => sq_nonneg _)
  have hcov_le_sqrt : ∀ Y Z : Ω → ℝ,
      D.Cov Y Z ≤ Real.sqrt (D.Var Y) * Real.sqrt (D.Var Z) := by
    intro Y Z
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Ω)
      (fun z => Real.sqrt (D.p z) * (Y z - D.E Y))
      (fun z => Real.sqrt (D.p z) * (Z z - D.E Z))
    unfold FiniteDesign.Cov FiniteDesign.Var
    convert hcs using 1
    · unfold FiniteDesign.E
      apply Finset.sum_congr rfl
      intro z _
      have hp : Real.sqrt (D.p z) * Real.sqrt (D.p z) = D.p z := by
        rw [← sq, Real.sq_sqrt (D.p_nonneg z)]
      rw [← hp]
      ring_nf
      rw [Real.sq_sqrt (sq_nonneg (Real.sqrt (D.p z)))]
      ring
    · have hY : Real.sqrt (D.E fun z => (Y z - D.E Y) ^ 2) =
          Real.sqrt (∑ i, (Real.sqrt (D.p i) * (Y i - D.E Y)) ^ 2) := by
        apply congrArg Real.sqrt
        unfold FiniteDesign.E
        apply Finset.sum_congr rfl
        intro z _
        have hp : Real.sqrt (D.p z) * Real.sqrt (D.p z) = D.p z := by
          rw [← sq, Real.sq_sqrt (D.p_nonneg z)]
        rw [← hp]
        ring_nf
        rw [Real.sq_sqrt (sq_nonneg (Real.sqrt (D.p z)))]
        ring
      have hZ : Real.sqrt (D.E fun z => (Z z - D.E Z) ^ 2) =
          Real.sqrt (∑ i, (Real.sqrt (D.p i) * (Z i - D.E Z)) ^ 2) := by
        apply congrArg Real.sqrt
        unfold FiniteDesign.E
        apply Finset.sum_congr rfl
        intro z _
        have hp : Real.sqrt (D.p z) * Real.sqrt (D.p z) = D.p z := by
          rw [← sq, Real.sq_sqrt (D.p_nonneg z)]
        rw [← hp]
        ring_nf
        rw [Real.sq_sqrt (sq_nonneg (Real.sqrt (D.p z)))]
        ring
      rw [hY, hZ]
  have hcov_abs_le_sqrt : ∀ Y Z : Ω → ℝ,
      |D.Cov Y Z| ≤ Real.sqrt (D.Var Y) * Real.sqrt (D.Var Z) := by
    intro Y Z
    refine abs_le.2 ⟨?_, hcov_le_sqrt Y Z⟩
    have h := hcov_le_sqrt (fun z => -Y z) Z
    have hcov : D.Cov (fun z => -Y z) Z = -D.Cov Y Z := by
      simpa using D.Cov_const_mul_left (-1) Y Z
    have hvar_neg : D.Var (fun z => -Y z) = D.Var Y := by
      simpa using D.Var_const_mul (-1) Y
    have hneg : -D.Cov Y Z ≤ Real.sqrt (D.Var Y) * Real.sqrt (D.Var Z) := by
      simpa [hcov, hvar_neg] using h
    linarith
  have hcov : ∀ i j : Fin (k + 1), |D.Cov (X i) (X j)| ≤ s := by
    intro i j
    have hi := Real.sqrt_le_sqrt (hvar i)
    have hj := Real.sqrt_le_sqrt (hvar j)
    have hprod :
        Real.sqrt (D.Var (X i)) * Real.sqrt (D.Var (X j)) ≤ Real.sqrt s * Real.sqrt s := by
      exact mul_le_mul hi hj (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hi)
    have hs_sqrt : Real.sqrt s * Real.sqrt s = s := by
      rw [← sq, Real.sq_sqrt hs]
    exact (hcov_abs_le_sqrt (X i) (X j)).trans (hprod.trans_eq hs_sqrt)
  have hupper :
      D.Var (fun z => ∑ j, w j * X j z) ≤ s * (∑ j, |w j|) ^ 2 := by
    calc
      D.Var (fun z => ∑ j, w j * X j z)
          = ∑ i, ∑ j, w i * w j * D.Cov (X i) (X j) := by
            simpa using D.Var_linear_comb (Finset.univ : Finset (Fin (k + 1))) w X
      _ ≤ ∑ i, ∑ j, |w i| * |w j| * s := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have hle_abs :
            w i * w j * D.Cov (X i) (X j) ≤ |w i * w j * D.Cov (X i) (X j)| :=
          le_abs_self _
        have habs_eq :
            |w i * w j * D.Cov (X i) (X j)| =
              |w i| * |w j| * |D.Cov (X i) (X j)| := by
          rw [abs_mul, abs_mul]
        calc
          w i * w j * D.Cov (X i) (X j)
              ≤ |w i * w j * D.Cov (X i) (X j)| := hle_abs
          _ = |w i| * |w j| * |D.Cov (X i) (X j)| := habs_eq
          _ ≤ |w i| * |w j| * s := by
            exact mul_le_mul_of_nonneg_left (hcov i j)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = s * (∑ j, |w j|) ^ 2 := by
        rw [pow_two]
        simp [Finset.mul_sum, mul_assoc, mul_comm]
  have hsharp :
      ∃ Γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, Γ.PosSemidef ∧
        (∀ j, Γ j j ≤ s) ∧
        (∑ i, ∑ j, w i * Γ i j * w j) = s * (∑ j, |w j|) ^ 2 := by
    let eps : Fin (k + 1) → ℝ := fun j => if 0 ≤ w j then 1 else -1
    refine ⟨s • Matrix.vecMulVec eps eps, ?_, ?_, ?_⟩
    · have hbase : (Matrix.vecMulVec eps eps).PosSemidef := by
        simpa using Matrix.posSemidef_vecMulVec_self_star (R := ℝ) eps
      exact hbase.smul hs
    · intro j
      have heps_sq : eps j * eps j = 1 := by
        by_cases h : 0 ≤ w j <;> simp [eps, h]
      simp [s, Matrix.vecMulVec, heps_sq]
    · have hw_eps : ∀ i, w i * eps i = |w i| := by
        intro i
        by_cases h : 0 ≤ w i
        · simp [eps, h, abs_of_nonneg h]
        · have hlt : w i < 0 := lt_of_not_ge h
          simp [eps, h, abs_of_neg hlt]
      calc
        (∑ i, ∑ j, w i * (s • Matrix.vecMulVec eps eps) i j * w j)
            = s * ((∑ i, w i * eps i) * (∑ j, w j * eps j)) := by
              simp [Matrix.vecMulVec, Finset.mul_sum, mul_left_comm, mul_comm]
        _ = s * (∑ j, |w j|) ^ 2 := by
          simp [hw_eps, pow_two]
  exact ⟨by simpa [s] using hupper, by simpa [s] using hsharp⟩

-- @node: sInf_le_mul_sInf_of_forall_exists_le
/-- Order bookkeeping for taking an infimum after a uniform multiplicative comparison. -/
lemma sInf_le_mul_sInf_of_forall_exists_le (F G : Set ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hFne : F.Nonempty) (hFbdd : BddBelow F) (hGne : G.Nonempty)
    (hlink : ∀ g ∈ G, ∃ f ∈ F, f ≤ c * g) :
    sInf F ≤ c * sInf G := by
  rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg hc G]
  refine (csInf_le_iff hFbdd hFne).2 ?_
  intro b hb
  refine le_csInf (Set.smul_set_nonempty.mpr hGne) ?_
  intro x hx
  rcases Set.mem_smul_set.mp hx with ⟨g, hg, rfl⟩
  rcases hlink g hg with ⟨f, hf, hle⟩
  exact (hb hf).trans (by simpa [smul_eq_mul] using hle)

-- @node: lem:exact-risk-envelope-upper
/-- Envelope-to-exact-risk bridge: for `β ≥ 1`, `k ≥ β`, `q ∈ (0,1]`, and every budgeted
schedule `p ∈ S_{k,q}`, the fixed-schedule exact risk is dominated by the amplification envelope,
`inf_{w∈W_β(p)} sup_{P∈P_β} w'Γ_P(p)w ≤ (σ₀²/n) A_β(p)` (the same `L²` triangle argument as
`variance_envelope_sharpness` applied to the exact covariance `Γ_P(p)`); consequently
`R_exact(β,k,q) ≤ (σ₀²/n) M_{β,k,q}`. -/
lemma exact_risk_envelope_upper (n k beta : ℕ) {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (q sigma0sq : ℝ) (hbeta : 1 ≤ beta) (hk : beta ≤ k) (_hq : 0 < q ∧ q ≤ 1)
    (hsig : 0 ≤ sigma0sq)
    (p : Fin (k + 1) → ℝ) (hp : BudgetedSchedule k q p) :
    (sInf { rw : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧
        rw = sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
            (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
            (m : ℝ → ℝ) (a : ℕ → ℝ),
          RolloutLawClass n k beta D Y Z barY m a sigma0sq p ∧
            rP = D.Var (fun z => ∑ j, w j * barY j z) } }
        ≤ sigma0sq / (n : ℝ) * amplification beta k p) ∧
      exactNestedRisk n k beta D q sigma0sq
        ≤ sigma0sq / (n : ℝ) * minimaxAmplification beta k q := by
  classical
  let fixedRisk : (Fin (k + 1) → ℝ) → ℝ := fun p' =>
    sInf { rw : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p' w ∧
        rw = sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
            (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
            (m : ℝ → ℝ) (a : ℕ → ℝ),
          RolloutLawClass n k beta D Y Z barY m a sigma0sq p' ∧
            rP = D.Var (fun z => ∑ j, w j * barY j z) } }
  let scale : ℝ := sigma0sq / (n : ℝ)
  have hscale : 0 ≤ scale := div_nonneg hsig (Nat.cast_nonneg n)
  have hvar_nonneg : ∀ Y : Ω → ℝ, 0 ≤ D.Var Y := by
    intro Y; unfold FiniteDesign.Var; exact D.E_nonneg (fun z => sq_nonneg _)
  have fixedRisk_nonneg : ∀ p' : Fin (k + 1) → ℝ, 0 ≤ fixedRisk p' := by
    intro p'
    dsimp [fixedRisk]
    apply Real.sInf_nonneg
    intro rw hrw
    rcases hrw with ⟨w, hw, rfl⟩
    apply Real.sSup_nonneg
    intro rP hrP
    rcases hrP with ⟨Y, Z, barY, m, a, hlaw, rfl⟩
    exact hvar_nonneg _
  have fixed_le_for : ∀ p' : Fin (k + 1) → ℝ, BudgetedSchedule k q p' →
      fixedRisk p' ≤ scale * amplification beta k p' := by
    intro p' hp'
    let F : Set ℝ :=
      { rw : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p' w ∧
        rw = sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
            (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
            (m : ℝ → ℝ) (a : ℕ → ℝ),
          RolloutLawClass n k beta D Y Z barY m a sigma0sq p' ∧
            rP = D.Var (fun z => ∑ j, w j * barY j z) } }
    let G : Set ℝ :=
      { v : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p' w ∧
        v = (∑ j, |w j|) ^ 2 }
    rcases unbiased_weight_set_nonempty beta k q p' hbeta hk hp' with ⟨w0, hw0⟩
    have hFne : F.Nonempty := by
      refine ⟨sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
            (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
            (m : ℝ → ℝ) (a : ℕ → ℝ),
          RolloutLawClass n k beta D Y Z barY m a sigma0sq p' ∧
            rP = D.Var (fun z => ∑ j, w0 j * barY j z) }, ?_⟩
      exact ⟨w0, hw0, rfl⟩
    have hGne : G.Nonempty := by exact ⟨(∑ j, |w0 j|) ^ 2, w0, hw0, rfl⟩
    have hFbdd : BddBelow F := by
      refine ⟨0, ?_⟩
      intro rw hrw
      rcases hrw with ⟨w, hw, rfl⟩
      apply Real.sSup_nonneg
      intro rP hrP
      rcases hrP with ⟨Y, Z, barY, m, a, hlaw, rfl⟩
      exact hvar_nonneg _
    have hlink : ∀ g ∈ G, ∃ f ∈ F, f ≤ scale * g := by
      intro g hg
      rcases hg with ⟨w, hw, rfl⟩
      let lawValues : Set ℝ :=
        { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
            (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
            (m : ℝ → ℝ) (a : ℕ → ℝ),
          RolloutLawClass n k beta D Y Z barY m a sigma0sq p' ∧
            rP = D.Var (fun z => ∑ j, w j * barY j z) }
      refine ⟨sSup lawValues, ?_, ?_⟩
      · exact ⟨w, hw, rfl⟩
      · apply Real.sSup_le
        · intro rP hrP
          rcases hrP with ⟨Y, Z, barY, m, a, hlaw, rfl⟩
          exact (variance_envelope_sharpness n k D barY sigma0sq w hsig
            hlaw.variance_envelope).1
        · exact mul_nonneg hscale (sq_nonneg _)
    change sInf F ≤ scale * sInf G
    exact sInf_le_mul_sInf_of_forall_exists_le F G scale hscale hFne hFbdd hGne hlink
  have hfixed_le : fixedRisk p ≤ sigma0sq / (n : ℝ) * amplification beta k p := by
    simpa [scale] using fixed_le_for p hp
  have hexact_le : exactNestedRisk n k beta D q sigma0sq
      ≤ sigma0sq / (n : ℝ) * minimaxAmplification beta k q := by
    let F : Set ℝ :=
      { rp : ℝ | ∃ p' : Fin (k + 1) → ℝ, BudgetedSchedule k q p' ∧ rp = fixedRisk p' }
    let G : Set ℝ :=
      { v : ℝ | ∃ p' : Fin (k + 1) → ℝ, BudgetedSchedule k q p' ∧
        v = amplification beta k p' }
    have hFne : F.Nonempty := ⟨fixedRisk p, p, hp, rfl⟩
    have hGne : G.Nonempty := ⟨amplification beta k p, p, hp, rfl⟩
    have hFbdd : BddBelow F := by
      refine ⟨0, ?_⟩
      intro rp hrp
      rcases hrp with ⟨p', hp', rfl⟩
      exact fixedRisk_nonneg p'
    have hlink : ∀ g ∈ G, ∃ f ∈ F, f ≤ scale * g := by
      intro g hg
      rcases hg with ⟨p', hp', rfl⟩
      exact ⟨fixedRisk p', ⟨p', hp', rfl⟩, fixed_le_for p' hp'⟩
    change sInf F ≤ scale * sInf G
    exact sInf_le_mul_sInf_of_forall_exists_le F G scale hscale hFne hFbdd hGne hlink
  exact ⟨hfixed_le, hexact_le⟩
end CausalSmith.Experimentation.RolloutChebyshev
