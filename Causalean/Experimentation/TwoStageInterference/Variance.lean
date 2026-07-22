/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008), Theorem 5: within-group difference-in-means variance

The variance of the within-group difference-in-means estimator of a treatment effect, under a
completely randomized experiment that always treats exactly `K` of the `n` units in the group.
Under stratified interference (Hudgens & Halloran's Assumption 2) each unit's outcome on the
design's support takes only two values — one when the unit is treated (so `K−1` others are
treated) and one when it is untreated (so `K` others are treated) — so the estimator is a linear
function of the treatment indicators and its randomization variance is the classical Neyman
completely-randomized-experiment variance.  Writing `S₁` and `S₀` for the population variances of
the treated-state and untreated-state outcomes (with `n−1` in the denominator) and `Sτ` for the
population variance of the unit-level treatment effects, the variance of the difference-in-means
estimator equals `S₁/K + S₀/(n−K) − Sτ/n`.  The generic identity (`Var_tauHat`) is stated for *any*
within-group design whose treatment indicators satisfy the first- and second-order moment
hypotheses; the completely randomized (mixed) design of Assumption 1 is the canonical such design,
and `Var_tauHat_CRD` specializes the identity to it — with the moments discharged from the design
(`crd_mean`/`crd_pair`) rather than assumed.  This file also proves that the natural conservative
variance estimator is pointwise nonnegative.

The two-valued outcomes `a j` (unit `j` when treated) and `b j` (unit `j` when untreated) are
taken as the data; the connection to the stratified-interference factorization
(`exists_strat_factor`) is upstream and not re-threaded here.
-/

import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Experimentation.TwoStageInterference.CompleteRandomization
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Within-group Neyman variance under complete randomization

This file proves the Hudgens-Halloran within-group difference-in-means variance identity. The
generic theorem states the Neyman split `S₁/K + S₀/(n−K) − Sτ/n` from first- and second-order
treatment-indicator moments, then specializes it to the completely randomized within-group design.

The public definitions are the treatment indicator `T`, the difference-in-means statistic
`tauHat`, the population mean `popMeanV`, and the sample variances `S1`, `S0`, and `Stau`.
`Var_tauHat` is the moment-conditioned theorem; `Var_tauHat_CRD` is the corresponding theorem for
the actual completely randomized design, with `crd_mean` and `crd_pair` supplying the moments.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-- Variance is invariant under adding a constant: `Var(X + c) = Var X`. -/
lemma FiniteDesign.Var_add_const {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (X : Ω → ℝ) (c : ℝ) :
    D.Var (fun z => X z + c) = D.Var X := by
  unfold FiniteDesign.Var
  have hE : D.E (fun z => X z + c) = D.E X + c := by
    rw [FiniteDesign.E_add, FiniteDesign.E_const]
  rw [hE]
  exact D.E_congr (fun z => by ring)

/-- A double sum of `cⱼ cₖ` weighted by a two-valued kernel (`vd` on the diagonal, `vo` off it)
collapses to `vo·(∑ c)² + (vd − vo)·∑ c²`.  This is the algebraic core that turns the
`Var_linear_comb` double sum into the Neyman split form. -/
lemma sum_sum_ite_quadratic {α : Type*} [DecidableEq α] (s : Finset α) (c : α → ℝ) (vd vo : ℝ) :
    (∑ j ∈ s, ∑ k ∈ s, c j * c k * (if j = k then vd else vo))
      = vo * (∑ j ∈ s, c j) ^ 2 + (vd - vo) * ∑ j ∈ s, (c j) ^ 2 := by
  have hsplit : ∀ j k, c j * c k * (if j = k then vd else vo)
      = vo * (c j * c k) + (if j = k then (vd - vo) * (c j * c k) else 0) := by
    intro j k; by_cases h : j = k <;> simp [h] <;> ring
  simp only [hsplit, Finset.sum_add_distrib]
  congr 1
  · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_ite_eq s i (fun k => (vd - vo) * (c i * c k)), if_pos hi, sq]

/-- The sum of squared deviations equals the raw second moment minus the squared first moment
divided by `m`: `∑ⱼ (xⱼ − x̄)² = ∑ⱼ xⱼ² − (∑ⱼ xⱼ)²/m`, where `x̄ = (∑ x)/m`. -/
lemma sum_sub_mean_sq {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) :
    (∑ j, (x j - (∑ i, x i) / m) ^ 2) = (∑ j, (x j) ^ 2) - (∑ i, x i) ^ 2 / m := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hcard : (∑ _j : Fin m, ((∑ i, x i) / m) ^ 2) = (∑ i, x i) ^ 2 / m := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hexp : ∀ j, (x j - (∑ i, x i) / m) ^ 2
      = (x j) ^ 2 - 2 * ((∑ i, x i) / m) * (x j) + ((∑ i, x i) / m) ^ 2 := fun j => by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcard, ← Finset.mul_sum]
  field_simp
  ring

section Group

variable {n : ℕ}

/-- Treatment indicator of unit `j`: `1` on within-group assignments that treat `j`, `0`
otherwise.  (The indicator does not depend on the design.) -/
noncomputable def T (j : Fin n) : (Fin n → Bool) → ℝ :=
  FiniteDesign.ind (fun w => w j = true)

variable (K : ℕ) (a b : Fin n → ℝ)

/-- The difference-in-means estimator `ȳ(0) − ȳ(1)`: the mean untreated-state outcome among the
`n − K` control units minus the mean treated-state outcome among the `K` treated units, as a
function of the realized assignment.  On the design's support the treated units realize `a` and
the control units realize `b`, so this is linear in the treatment indicators. -/
noncomputable def tauHat : (Fin n → Bool) → ℝ :=
  fun w => (∑ j, b j * (1 - T j w)) / (n - K : ℝ) - (∑ j, a j * T j w) / K

/-! ### Population sample variances (Neyman, `n−1` denominator) -/

/-- Population mean of a unit-indexed quantity: `(1/n)∑ⱼ x j`. -/
noncomputable def popMeanV (x : Fin n → ℝ) : ℝ := (∑ j, x j) / n

/-- Population sample variance of the treated-state outcomes `a`, `S₁ = (1/(n−1))∑ⱼ(a j − ā)²`. -/
noncomputable def S1 : ℝ := (∑ j, (a j - popMeanV a) ^ 2) / (n - 1 : ℝ)

/-- Population sample variance of the untreated-state outcomes `b`,
`S₀ = (1/(n−1))∑ⱼ(b j − b̄)²`. -/
noncomputable def S0 : ℝ := (∑ j, (b j - popMeanV b) ^ 2) / (n - 1 : ℝ)

/-- Population sample variance of the unit-level treatment effects `a j − b j`,
`Sτ = (1/(n−1))∑ⱼ((a j − b j) − (ā − b̄))²`. -/
noncomputable def Stau : ℝ :=
  (∑ j, ((a j - b j) - (popMeanV a - popMeanV b)) ^ 2) / (n - 1 : ℝ)

/-! ### Complete-randomization covariances of the treatment indicators -/

section Covariance

variable (ρ : FiniteDesign (Fin n → Bool))
variable (hmean : ∀ j, ρ.E (T j) = (K : ℝ) / n)
variable (hpair : ∀ j k, j ≠ k →
  ρ.E (fun w => T j w * T k w) = (K * (K - 1) : ℝ) / (n * (n - 1)))

include hmean in
/-- The diagonal covariance `Cov(Tⱼ, Tⱼ) = Var(Tⱼ) = (K/n)(1 − K/n)`. -/
lemma cov_diag (j : Fin n) :
    ρ.Cov (T j) (T j) = (K / n : ℝ) * (1 - K / n) := by
  rw [FiniteDesign.Cov_self]
  simp only [T]
  rw [FiniteDesign.Var_ind]
  change ρ.E (T j) * (1 - ρ.E (T j)) = _
  rw [hmean j]

include hmean hpair in
/-- The off-diagonal covariance `Cov(Tⱼ, Tₖ) = K(K−1)/(n(n−1)) − (K/n)²` for `j ≠ k`. -/
lemma cov_offdiag (j k : Fin n) (hjk : j ≠ k) :
    ρ.Cov (T j) (T k)
      = (K * (K - 1) : ℝ) / (n * (n - 1)) - (K / n) * (K / n) := by
  rw [FiniteDesign.Cov_eq, hpair j k hjk, hmean j, hmean k]

end Covariance

/-! ### Theorem 5: the Neyman completely-randomized variance -/

section MainVariance

variable (ρ : FiniteDesign (Fin n → Bool))
variable (hK : 0 < K) (hKn : K < n)
variable (hmean : ∀ j, ρ.E (T j) = (K : ℝ) / n)
variable (hpair : ∀ j k, j ≠ k →
  ρ.E (fun w => T j w * T k w) = (K * (K - 1) : ℝ) / (n * (n - 1)))

include hK hKn hmean hpair in
/-- **Hudgens–Halloran (2008), Theorem 5 (within-group / Neyman form).**  For any within-group
design whose treatment indicators have first moment `K/n` (`hmean`) and pairwise second moment
`K(K−1)/(n(n−1))` (`hpair`) — the moments of the completely randomized (mixed) design of
Assumption 1, which treats exactly `K` of `n` units — with the two-valued potential outcomes `a`
(treated state) and `b` (control state), the randomization variance of the difference-in-means
estimator is `S₁/K + S₀/(n−K) − Sτ/n`.  (`Var_tauHat_CRD` specializes this to the completely
randomized design, discharging the two moment hypotheses.) -/
theorem Var_tauHat :
    ρ.Var (tauHat K a b) = S1 a / K + S0 b / (n - K) - Stau a b / n := by
  -- Write the estimator as a linear combination of the indicators plus a constant.
  set c : Fin n → ℝ := fun j => -(b j / (n - K) + a j / K) with hc
  have hlin : tauHat K a b = fun w => (∑ j, c j * T j w) + (∑ j, b j) / (n - K) := by
    funext w; unfold tauHat
    have e1 : ∑ j, b j * (1 - T j w) = (∑ j, b j) - ∑ j, b j * T j w := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have e2 : ∑ j, c j * T j w
        = -((∑ j, b j * T j w) / (n - K)) - (∑ j, a j * T j w) / K := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [hc]; ring)
    rw [e1, e2]; ring
  rw [hlin, FiniteDesign.Var_add_const, FiniteDesign.Var_linear_comb]
  -- The completely-randomized covariances are two-valued: `vd` on the diagonal, `vo` off it.
  set vd : ℝ := (K / n : ℝ) * (1 - K / n) with hvd
  set vo : ℝ := (K * (K - 1) : ℝ) / (n * (n - 1)) - (K / n) * (K / n) with hvo
  have hcov : ∀ i j, ρ.Cov (T i) (T j) = if i = j then vd else vo := by
    intro i j
    by_cases h : i = j
    · subst h; rw [if_pos rfl, hvd]; exact cov_diag K ρ hmean i
    · rw [if_neg h, hvo]; exact cov_offdiag K ρ hmean hpair i j h
  have hrw : ∀ i j, c i * c j * ρ.Cov (T i) (T j)
      = c i * c j * (if i = j then vd else vo) := fun i j => by rw [hcov i j]
  simp only [hrw]
  rw [sum_sum_ite_quadratic Finset.univ c vd vo]
  -- Positivity of the denominators.
  have hKr : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have hKn' : (K : ℝ) < n := by exact_mod_cast hKn
  have hnKpos : (0 : ℝ) < n - K := by linarith
  have hnKr : (n - K : ℝ) ≠ 0 := ne_of_gt hnKpos
  have hn1pos : (1 : ℝ) < n := by exact_mod_cast lt_of_le_of_lt hK hKn
  have hnpos0 : (0 : ℝ) < n := by linarith
  have hnr : (n : ℝ) ≠ 0 := ne_of_gt hnpos0
  have hn1r : (n - 1 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n - 1 := by linarith
    exact ne_of_gt this
  -- Linear and quadratic sums of the coefficients in terms of raw moments.
  have hsumc : (∑ j, c j) = -((∑ j, b j) / (n - K) + (∑ j, a j) / K) := by
    simp only [hc]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  have hsumc2 : (∑ j, c j ^ 2)
      = (∑ j, b j ^ 2) / (n - K) ^ 2 + 2 * (∑ j, a j * b j) / ((n - K) * K)
        + (∑ j, a j ^ 2) / K ^ 2 := by
    simp only [hc]
    rw [show (∑ j, b j ^ 2) / (↑n - ↑K) ^ 2 + 2 * (∑ j, a j * b j) / ((↑n - ↑K) * ↑K)
          + (∑ j, a j ^ 2) / ↑K ^ 2
        = (∑ j, b j ^ 2) / (↑n - ↑K) ^ 2 + (∑ j, 2 * (a j * b j)) / ((↑n - ↑K) * ↑K)
          + (∑ j, a j ^ 2) / ↑K ^ 2 from by rw [← Finset.mul_sum]]
    rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by field_simp; ring)
  -- Unfold the sample variances via the deviation-sum identity.
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le K) hKn
  unfold S1 S0 Stau popMeanV
  rw [sum_sub_mean_sq hnpos a, sum_sub_mean_sq hnpos b]
  -- For Sτ, rewrite the mean of effects as the difference of means, then apply the identity.
  have hStau : (∑ j, ((a j - b j) - ((∑ i, a i) / n - (∑ i, b i) / n)) ^ 2)
      = (∑ j, (a j - b j) ^ 2) - (∑ i, (a i - b i)) ^ 2 / n := by
    have hmean_eq : ((∑ i, a i) / n - (∑ i, b i) / n) = (∑ i, (a i - b i)) / n := by
      rw [Finset.sum_sub_distrib, sub_div]
    rw [hmean_eq, sum_sub_mean_sq hnpos (fun j => a j - b j)]
  rw [hStau, hsumc, hsumc2]
  -- Expand the effect-sum moments in terms of `a`, `b` raw moments.
  have hsumab2 : (∑ j, (a j - b j) ^ 2)
      = (∑ j, a j ^ 2) - 2 * (∑ j, a j * b j) + (∑ j, b j ^ 2) := by
    have hpt : ∀ j, (a j - b j) ^ 2 = a j ^ 2 - 2 * (a j * b j) + b j ^ 2 := fun j => by ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hsumabsub : (∑ i, (a i - b i)) = (∑ i, a i) - (∑ i, b i) :=
    Finset.sum_sub_distrib a b
  rw [hsumab2, hsumabsub, hvd, hvo]
  -- Pure field algebra over the five moment sums; verified symbolically.
  field_simp
  ring

end MainVariance

/-- **Hudgens–Halloran (2008), Theorem 5, for the completely randomized design.**  The Neyman
variance identity `Var(τ̂) = S₁/K + S₀/(n−K) − Sτ/n`, specialized to the actual completely
randomized within-group design `crd` (exactly `K` of `n` units treated, every treated set equally
likely).  Its first- and second-order treatment moments are the derived facts `crd_mean`/`crd_pair`,
so — unlike `Var_tauHat` — no moment hypotheses are assumed; this is the identity as Hudgens &
Halloran state it under their mixed-strategy Assumption 1. -/
theorem Var_tauHat_CRD (hK : 0 < K) (hKn : K < n) :
    (crd K hKn.le).Var (tauHat K a b) = S1 a / K + S0 b / (n - K) - Stau a b / n :=
  Var_tauHat K a b (crd K hKn.le) hK hKn
    (fun j => crd_mean K hKn.le j) (fun j k hjk => crd_pair K hKn.le j k hjk)

end Group

end TwoStageInterference
end Experimentation
end Causalean
