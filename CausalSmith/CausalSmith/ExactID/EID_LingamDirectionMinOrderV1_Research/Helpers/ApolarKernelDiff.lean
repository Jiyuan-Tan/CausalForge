/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Divided-power blocks as sums of loading powers, and the apolar differentiation identity

`f_r = Σ_j c_{jr} ℓ_j^r` (binomial identity) and
`q(∂) ℓ^{n+k} = ((n+k)!/k!) · q(ℓ) · ℓ^k` for `q` homogeneous of degree `n`.
These feed the common-contraction-kernel identity of the arrow-recovery flagship.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernel

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-! ### Linear forms attached to loading directions -/

/-- The binary linear form associated with a loading direction. -/
noncomputable def linForm (u : ℂ × ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C u.1 * MvPolynomial.X 0 + MvPolynomial.C u.2 * MvPolynomial.X 1

/-- Evaluation of a differential symbol at a loading direction. -/
noncomputable def evalAtDir (q : MvPolynomial (Fin 2) ℂ) (u : ℂ × ℂ) : ℂ :=
  MvPolynomial.eval (fun i => if i = 0 then u.1 else u.2) q

private lemma linForm_pow (u : ℂ × ℂ) (r : ℕ) :
    linForm u ^ r = ∑ a ∈ Finset.range (r + 1),
      MvPolynomial.C (r.choose a : ℂ) *
        (MvPolynomial.C u.1 * MvPolynomial.X 0) ^ (r - a) *
        (MvPolynomial.C u.2 * MvPolynomial.X 1) ^ a := by
  rw [show linForm u = MvPolynomial.C u.2 * MvPolynomial.X 1 +
      MvPolynomial.C u.1 * MvPolynomial.X 0 by simp [linForm, add_comm]]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← map_natCast MvPolynomial.C]
  ring

/-- A retained forward divided-power cumulant block is the corresponding sum of
loading-direction powers. -/
lemma dividedPowerBlock_forward_eq_sum_linForm_pow (m L r : ℕ) (θ : ParamSpace ℂ m)
    (hr : 2 ≤ r) (hrL : r ≤ L) :
    dividedPowerBlock (forwardCumulantMap m L θ) r =
      ∑ j : Fin (m + 2), MvPolynomial.C (θ.2.2 j r) *
        linForm (forwardLoading m θ.1 θ.2.1 j) ^ r := by
  rw [dividedPowerBlock]
  simp only [forwardCumulantMap, hr, hrL]
  calc
    _ = ∑ a ∈ Finset.range (r + 1), ∑ j : Fin (m + 2),
        MvPolynomial.C (θ.2.2 j r) *
          (MvPolynomial.C (r.choose a : ℂ) *
            (MvPolynomial.C (forwardLoading m θ.1 θ.2.1 j).1 * MvPolynomial.X 0) ^ (r - a) *
            (MvPolynomial.C (forwardLoading m θ.1 θ.2.1 j).2 * MvPolynomial.X 1) ^ a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [if_pos ⟨by simp, by simp, har⟩]
      rw [MvPolynomial.C_mul, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [MvPolynomial.C_mul]
      rw [map_pow, map_pow]
      ring
    _ = ∑ j : Fin (m + 2), MvPolynomial.C (θ.2.2 j r) *
        linForm (forwardLoading m θ.1 θ.2.1 j) ^ r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [linForm_pow]
      simp_rw [Finset.mul_sum]

/-- The corresponding retained reverse divided-power cumulant block. -/
lemma dividedPowerBlock_reverse_eq_sum_linForm_pow (m L r : ℕ) (η : ParamSpace ℂ m)
    (hr : 2 ≤ r) (hrL : r ≤ L) :
    dividedPowerBlock (reverseCumulantMap m L η) r =
      ∑ j : Fin (m + 2), MvPolynomial.C (η.2.2 j r) *
        linForm (reverseLoading m η.1 η.2.1 j) ^ r := by
  rw [dividedPowerBlock]
  simp only [reverseCumulantMap, hr, hrL]
  calc
    _ = ∑ a ∈ Finset.range (r + 1), ∑ j : Fin (m + 2),
        MvPolynomial.C (η.2.2 j r) *
          (MvPolynomial.C (r.choose a : ℂ) *
            (MvPolynomial.C (reverseLoading m η.1 η.2.1 j).1 * MvPolynomial.X 0) ^ (r - a) *
            (MvPolynomial.C (reverseLoading m η.1 η.2.1 j).2 * MvPolynomial.X 1) ^ a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [if_pos ⟨by simp, by simp, har⟩]
      rw [MvPolynomial.C_mul, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [MvPolynomial.C_mul]
      rw [map_pow, map_pow]
      ring
    _ = ∑ j : Fin (m + 2), MvPolynomial.C (η.2.2 j r) *
        linForm (reverseLoading m η.1 η.2.1 j) ^ r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [linForm_pow]
      simp_rw [Finset.mul_sum]

/-! ### Apolar differentiation of a loading-direction power -/

private lemma pderiv_zero_linForm (u : ℂ × ℂ) :
    MvPolynomial.pderiv (0 : Fin 2) (linForm u) = MvPolynomial.C u.1 := by
  simp [linForm]

private lemma pderiv_one_linForm (u : ℂ × ℂ) :
    MvPolynomial.pderiv (1 : Fin 2) (linForm u) = MvPolynomial.C u.2 := by
  simp [linForm]

private lemma pderiv_iter_linForm_pow (i : Fin 2) (a : ℂ) (u : ℂ × ℂ)
    (hi : MvPolynomial.pderiv i (linForm u) = MvPolynomial.C a)
    (p t : ℕ) (ht : t ≤ p) :
    (fun g => MvPolynomial.pderiv i g)^[t] (linForm u ^ p) =
      MvPolynomial.C (Nat.descFactorial p t : ℂ) *
        (MvPolynomial.C a)^t * linForm u ^ (p - t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    rw [ih (Nat.le_of_succ_le ht)]
    rw [show MvPolynomial.C (Nat.descFactorial p t : ℂ) * (MvPolynomial.C a)^t =
        MvPolynomial.C ((Nat.descFactorial p t : ℂ) * a ^ t) by
      rw [← map_pow, ← map_mul]]
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, hi]
    rw [show (↑(p - t) : MvPolynomial (Fin 2) ℂ) = MvPolynomial.C (↑(p - t) : ℂ) by
      rw [← map_natCast MvPolynomial.C]]
    rw [Nat.descFactorial_succ]
    push_cast
    have hsub : p - (t + 1) = p - t - 1 := by omega
    rw [hsub]
    simp only [← map_pow, ← map_mul]
    calc
      MvPolynomial.C (↑(Nat.descFactorial p t) * a ^ t) *
          (MvPolynomial.C (↑(p - t)) * linForm u ^ (p - t - 1) * MvPolynomial.C a) =
          (MvPolynomial.C (↑(Nat.descFactorial p t) * a ^ t) *
            MvPolynomial.C (↑(p - t)) * MvPolynomial.C a) * linForm u ^ (p - t - 1) := by
        ring
      _ = MvPolynomial.C ((↑(Nat.descFactorial p t) * a ^ t) * ↑(p - t) * a) *
          linForm u ^ (p - t - 1) := by
        rw [← map_mul MvPolynomial.C, ← map_mul MvPolynomial.C]
      _ = _ := by
        congr 1
        ring

private lemma pderiv_iter_C_mul (i : Fin 2) (a : ℂ) (f : MvPolynomial (Fin 2) ℂ) (t : ℕ) :
    (fun g => MvPolynomial.pderiv i g)^[t] (MvPolynomial.C a * f) =
      MvPolynomial.C a * (fun g => MvPolynomial.pderiv i g)^[t] f := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      (fun g => MvPolynomial.pderiv i g)^[t.succ] (MvPolynomial.C a * f) =
          MvPolynomial.pderiv i ((fun g => MvPolynomial.pderiv i g)^[t]
            (MvPolynomial.C a * f)) := Function.iterate_succ_apply' _ _ _
      _ = MvPolynomial.pderiv i (MvPolynomial.C a *
          (fun g => MvPolynomial.pderiv i g)^[t] f) := by rw [ih]
      _ = MvPolynomial.C a * MvPolynomial.pderiv i
          ((fun g => MvPolynomial.pderiv i g)^[t] f) := MvPolynomial.pderiv_C_mul
      _ = MvPolynomial.C a * (fun g => MvPolynomial.pderiv i g)^[t.succ] f := by
        rw [Function.iterate_succ_apply']

private lemma pderiv_mixed_linForm_pow (u : ℂ × ℂ) (p a b : ℕ) (hab : a + b ≤ p) :
    (fun g => MvPolynomial.pderiv (0 : Fin 2) g)^[a]
      ((fun g => MvPolynomial.pderiv (1 : Fin 2) g)^[b] (linForm u ^ p)) =
      MvPolynomial.C (Nat.descFactorial p (a + b) : ℂ) *
        (MvPolynomial.C u.1)^a * (MvPolynomial.C u.2)^b * linForm u ^ (p - (a + b)) := by
  have hb : b ≤ p := Nat.le_trans (Nat.le_add_left _ _) hab
  have ha : a ≤ p - b := by omega
  rw [pderiv_iter_linForm_pow (1 : Fin 2) u.2 u (pderiv_one_linForm u) p b hb]
  rw [show MvPolynomial.C (Nat.descFactorial p b : ℂ) * (MvPolynomial.C u.2)^b =
      MvPolynomial.C ((Nat.descFactorial p b : ℂ) * u.2^b) by
    rw [← map_pow, ← map_mul]]
  rw [pderiv_iter_C_mul]
  rw [pderiv_iter_linForm_pow (0 : Fin 2) u.1 u (pderiv_zero_linForm u) (p - b) a ha]
  have hdesc : Nat.descFactorial (p - b) a * Nat.descFactorial p b =
      Nat.descFactorial p (a + b) := by
    simpa using Nat.descFactorial_mul_descFactorial (n := p) (k := b) (m := a + b)
      (Nat.le_add_left _ _)
  have hsub : p - b - a = p - (a + b) := by omega
  rw [hsub]
  simp only [← map_pow, ← map_mul]
  calc
    MvPolynomial.C (↑(Nat.descFactorial p b) * u.2 ^ b) *
        (MvPolynomial.C (↑(Nat.descFactorial (p - b) a) * u.1 ^ a) *
          linForm u ^ (p - (a + b))) =
        (MvPolynomial.C (↑(Nat.descFactorial p b) * u.2 ^ b) *
          MvPolynomial.C (↑(Nat.descFactorial (p - b) a) * u.1 ^ a)) *
          linForm u ^ (p - (a + b)) := by ring
    _ = MvPolynomial.C ((↑(Nat.descFactorial p b) * u.2 ^ b) *
          (↑(Nat.descFactorial (p - b) a) * u.1 ^ a)) *
          linForm u ^ (p - (a + b)) := by rw [← map_mul MvPolynomial.C]
    _ = _ := by
      congr 1
      have hdesc' : (↑(Nat.descFactorial (p - b) a) : ℂ) *
          ↑(Nat.descFactorial p b) = ↑(Nat.descFactorial p (a + b)) := by
        exact_mod_cast hdesc
      congr 1
      calc
        (↑(Nat.descFactorial p b) : ℂ) * u.2 ^ b *
            (↑(Nat.descFactorial (p - b) a) * u.1 ^ a) =
            (↑(Nat.descFactorial (p - b) a) * ↑(Nat.descFactorial p b)) *
              u.1 ^ a * u.2 ^ b := by ring
        _ = _ := by rw [hdesc']

private lemma evalAtDir_eq_sum (q : MvPolynomial (Fin 2) ℂ) (u : ℂ × ℂ) :
    evalAtDir q u = ∑ d ∈ q.support, MvPolynomial.coeff d q * u.1 ^ d 0 * u.2 ^ d 1 := by
  rw [evalAtDir, MvPolynomial.eval_eq']
  simp_rw [Fin.prod_univ_two]
  apply Finset.sum_congr rfl
  intro d hd
  simp
  ring

/-- Applying a homogeneous differential symbol to a loading-direction power. -/
lemma diffApply_linForm_pow (q : MvPolynomial (Fin 2) ℂ) {n : ℕ}
    (hq : q.IsHomogeneous n) (u : ℂ × ℂ) (k : ℕ) :
    diffApply q (linForm u ^ (n + k)) =
      MvPolynomial.C (Nat.descFactorial (n + k) n : ℂ) *
        MvPolynomial.C (evalAtDir q u) * linForm u ^ k := by
  classical
  have hdegree : ∀ d ∈ q.support, d 0 + d 1 = n := by
    intro d hd
    have hd' : MvPolynomial.coeff d q ≠ 0 := by
      exact MvPolynomial.mem_support_iff.mp hd
    have h := hq hd'
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using h
  rw [diffApply]
  calc
    ∑ d ∈ q.support, MvPolynomial.coeff d q •
        ((fun g => MvPolynomial.pderiv (0 : Fin 2) g)^[d 0]
          ((fun g => MvPolynomial.pderiv (1 : Fin 2) g)^[d 1] (linForm u ^ (n + k)))) =
        Finset.sum q.support (fun d =>
          MvPolynomial.C (Nat.descFactorial (n + k) n : ℂ) *
            MvPolynomial.C (MvPolynomial.coeff d q * u.1 ^ (d 0) * u.2 ^ (d 1)) *
              linForm u ^ k) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hddeg := hdegree d hd
      have hdle : d 0 + d 1 ≤ n + k := by omega
      rw [pderiv_mixed_linForm_pow u (n + k) (d 0) (d 1) hdle]
      rw [show n + k - (d 0 + d 1) = k by omega, hddeg]
      rw [MvPolynomial.smul_eq_C_mul]
      simp only [← map_pow, ← map_mul]
      calc
        MvPolynomial.C (MvPolynomial.coeff d q) *
            (MvPolynomial.C (↑(Nat.descFactorial (n + k) n) * u.1 ^ d 0 * u.2 ^ d 1) *
              linForm u ^ k) =
            (MvPolynomial.C (MvPolynomial.coeff d q) *
              MvPolynomial.C (↑(Nat.descFactorial (n + k) n) * u.1 ^ d 0 * u.2 ^ d 1)) *
              linForm u ^ k := by ring
        _ = MvPolynomial.C (MvPolynomial.coeff d q *
            (↑(Nat.descFactorial (n + k) n) * u.1 ^ d 0 * u.2 ^ d 1)) * linForm u ^ k := by
          rw [← map_mul MvPolynomial.C]
        _ = _ := by
          congr 1
          ring
    _ = MvPolynomial.C (Nat.descFactorial (n + k) n : ℂ) *
        MvPolynomial.C (∑ d ∈ q.support,
          MvPolynomial.coeff d q * u.1 ^ d 0 * u.2 ^ d 1) * linForm u ^ k := by
      rw [map_sum, Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [← evalAtDir_eq_sum]

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
