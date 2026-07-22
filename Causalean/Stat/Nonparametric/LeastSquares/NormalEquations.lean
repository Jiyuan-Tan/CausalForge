/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Normal equations for weighted linear least squares

Normal equations and projection-optimality identities for weighted linear least-squares fits with
nonnegative observation weights.

A weighted linear least-squares fit chooses coefficients `c` minimizing
`∑ᵢ wᵢ (Yᵢ − ∑ⱼ cⱼ Φᵢⱼ)²` against a design matrix `Φ` (basis functions evaluated at the
data) with nonnegative weights `wᵢ`. This file proves the first-order optimality
conditions — the **normal equations**

`∑ᵢ wᵢ (Yᵢ − ∑ⱼ cⱼ Φᵢⱼ) Φᵢₖ = 0`  for every basis index `k`,

directly from global minimality (no differentiability API: the objective is quadratic
along each coordinate direction, so a one-variable perturbation forces the linear
coefficient to vanish). The abstract design matrix `Φ` specialises to:
* **local polynomial regression** — `Φᵢⱼ = (aᵢ − t)ʲ` (`wls_normal_equations`), the
  source of the equivalent-kernel polynomial-reproduction property (Fan–Gijbels 1996);
* **series / sieve regression** — `Φᵢⱼ = φⱼ(Xᵢ)` for a basis `φ` (Newey 1997; Chen 2007).
These are the algebraic identities underlying both interior local-polynomial and
series-estimator analyses.
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators

/-- The weighted residual at coefficient vector `c` against design matrix `Φ`:
`rᵢ(c) = Yᵢ − ∑ⱼ cⱼ Φᵢⱼ`. -/
noncomputable def lstsqResidual {N : ℕ} {ι : Type*} [Fintype ι]
    (Φ : Fin N → ι → ℝ) (Y : Fin N → ℝ) (c : ι → ℝ) (i : Fin N) : ℝ :=
  Y i - ∑ j, c j * Φ i j

/-- The weighted sum of squares `∑ᵢ wᵢ rᵢ(c)²`. -/
noncomputable def lstsqObjective {N : ℕ} {ι : Type*} [Fintype ι]
    (Φ : Fin N → ι → ℝ) (w Y : Fin N → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, w i * lstsqResidual Φ Y c i ^ 2

private lemma sum_update_univ_eq_sub_add {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (a : α) (b : ℝ) :
    (∑ x, Function.update f a b x) = (∑ x, f x) - f a + b := by
  classical
  let rest : ℝ := ∑ x ∈ (Finset.univ \ {a}), f x
  have hupdate : (∑ x, Function.update f a b x) = b + rest := by
    simpa [rest] using
      (Finset.sum_update_of_mem (s := Finset.univ) (i := a) (f := f) (b := b)
        (Finset.mem_univ a))
  have hbase : (∑ x, f x) = f a + rest := by
    simp [rest]
  rw [hupdate, hbase]
  ring

private lemma linear_coeff_eq_zero_of_quadratic_nonneg {A B : ℝ} (hB : 0 ≤ B)
    (hquad : ∀ s : ℝ, 0 ≤ -2 * s * A + s ^ 2 * B) :
    A = 0 := by
  have hden : B + 1 ≠ 0 := by positivity
  have hpos : 0 < B + 2 := by linarith
  have h := hquad (A / (B + 1))
  have hle : A ^ 2 * (B + 2) ≤ 0 := by
    rw [div_pow] at h
    field_simp [hden] at h
    nlinarith
  have hnonneg : 0 ≤ A ^ 2 * (B + 2) := mul_nonneg (sq_nonneg A) (le_of_lt hpos)
  have hsquare : A ^ 2 = 0 := by nlinarith
  exact sq_eq_zero_iff.mp hsquare

/-- **Normal equations for weighted linear least squares.** If `c` globally minimizes the
weighted sum of squares `∑ᵢ wᵢ (Yᵢ − ∑ⱼ cⱼ Φᵢⱼ)²` over all coefficient vectors and the
weights are nonnegative, then the weighted residual is orthogonal to every design column:
`∑ᵢ wᵢ (Yᵢ − ∑ⱼ cⱼ Φᵢⱼ) Φᵢₖ = 0` for each basis index `k`. -/
theorem lstsq_normal_equations {N : ℕ} {ι : Type*} [Fintype ι]
    {Φ : Fin N → ι → ℝ} {w Y : Fin N → ℝ} {c : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hmin : ∀ c' : ι → ℝ, lstsqObjective Φ w Y c ≤ lstsqObjective Φ w Y c') :
    ∀ k : ι, ∑ i, w i * lstsqResidual Φ Y c i * Φ i k = 0 := by
  intro k
  classical
  let r : Fin N → ℝ := fun i => lstsqResidual Φ Y c i
  let A : ℝ := ∑ i, w i * r i * Φ i k
  let B : ℝ := ∑ i, w i * (Φ i k) ^ 2
  have hres_update (s : ℝ) (i : Fin N) :
      lstsqResidual Φ Y (Function.update c k (c k + s)) i =
        r i - s * Φ i k := by
    unfold lstsqResidual
    dsimp [r]
    have hfun :
        (fun j : ι => Function.update c k (c k + s) j * Φ i j) =
          Function.update (fun j : ι => c j * Φ i j) k ((c k + s) * Φ i k) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp
      · simp [Function.update, hj]
    have hsum :
        (∑ j : ι, Function.update c k (c k + s) j * Φ i j) =
          (∑ j : ι, c j * Φ i j) + s * Φ i k := by
      rw [hfun, sum_update_univ_eq_sub_add]
      ring
    rw [hsum]
    change Y i - ((∑ j : ι, c j * Φ i j) + s * Φ i k) =
      (Y i - ∑ j : ι, c j * Φ i j) - s * Φ i k
    ring
  have hobj (s : ℝ) :
      lstsqObjective Φ w Y (Function.update c k (c k + s)) =
        lstsqObjective Φ w Y c - 2 * s * A + s ^ 2 * B := by
    unfold lstsqObjective
    calc
      (∑ i, w i * lstsqResidual Φ Y (Function.update c k (c k + s)) i ^ 2) =
          ∑ i, (w i * r i ^ 2 - 2 * s * (w i * r i * Φ i k) +
            s ^ 2 * (w i * (Φ i k) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hres_update s i]
        ring
      _ = (∑ i, w i * lstsqResidual Φ Y c i ^ 2) - 2 * s * A + s ^ 2 * B := by
        simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, A, B, r]
  have hquad : ∀ s : ℝ, 0 ≤ -2 * s * A + s ^ 2 * B := by
    intro s
    have h := hmin (Function.update c k (c k + s))
    rw [hobj s] at h
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i) (sq_nonneg _)
  exact linear_coeff_eq_zero_of_quadratic_nonneg hB hquad

/-- **Normal equations for weighted polynomial least squares** (local-polynomial design
`Φᵢⱼ = (xᵢ)ʲ`). The weighted least-squares minimizer of `∑ᵢ wᵢ (Yᵢ − ∑ⱼ cⱼ xᵢʲ)²` has
residual orthogonal to every design monomial: `∑ᵢ wᵢ (Yᵢ − ∑ⱼ cⱼ xᵢʲ) xᵢᵏ = 0`. -/
theorem wls_normal_equations {N p : ℕ} {x w Y : Fin N → ℝ} {c : Fin (p + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hmin : ∀ c' : Fin (p + 1) → ℝ,
        (∑ i, w i * (Y i - ∑ j, c j * x i ^ (j : ℕ)) ^ 2)
          ≤ ∑ i, w i * (Y i - ∑ j, c' j * x i ^ (j : ℕ)) ^ 2) :
    ∀ k : Fin (p + 1),
      ∑ i, w i * (Y i - ∑ j, c j * x i ^ (j : ℕ)) * x i ^ (k : ℕ) = 0 := by
  have hmin' : ∀ c' : Fin (p + 1) → ℝ,
      lstsqObjective (fun (i : Fin N) (j : Fin (p + 1)) => x i ^ (j : ℕ)) w Y c
        ≤ lstsqObjective (fun (i : Fin N) (j : Fin (p + 1)) => x i ^ (j : ℕ)) w Y c' := by
    intro c'
    simpa [lstsqObjective, lstsqResidual] using hmin c'
  intro k
  have hk := lstsq_normal_equations
    (Φ := fun (i : Fin N) (j : Fin (p + 1)) => x i ^ (j : ℕ)) hw hmin' k
  simpa [lstsqResidual] using hk

/-- **Pythagorean decomposition for weighted least squares.** If the residual at `c` is
orthogonal to every design column (`∑ᵢ wᵢ rᵢ(c) Φᵢₖ = 0` for all `k` — e.g. `c` is the
least-squares minimizer, by `lstsq_normal_equations`), then for any coefficient vector `c'`
the weighted sum of squares splits exactly as
`SSE(c') = SSE(c) + ∑ᵢ wᵢ (∑ⱼ (cⱼ − c'ⱼ) Φᵢⱼ)²`: the orthogonality kills the cross term, so the
excess error is the weighted norm of the fitted-value difference. -/
theorem lstsq_pythagoras {N : ℕ} {ι : Type*} [Fintype ι]
    {Φ : Fin N → ι → ℝ} {w Y : Fin N → ℝ} {c : ι → ℝ}
    (hortho : ∀ k : ι, ∑ i, w i * lstsqResidual Φ Y c i * Φ i k = 0)
    (c' : ι → ℝ) :
    lstsqObjective Φ w Y c'
      = lstsqObjective Φ w Y c + ∑ i, w i * (∑ j, (c j - c' j) * Φ i j) ^ 2 := by
  classical
  let d : Fin N → ℝ := fun i => ∑ j, (c j - c' j) * Φ i j
  have hkey : ∀ i, lstsqResidual Φ Y c' i = lstsqResidual Φ Y c i + d i := by
    intro i
    unfold lstsqResidual
    dsimp [d]
    calc
      Y i - ∑ j, c' j * Φ i j =
          (Y i - ∑ j, c j * Φ i j) + ((∑ j, c j * Φ i j) - ∑ j, c' j * Φ i j) := by
        ring
      _ = (Y i - ∑ j, c j * Φ i j) + ∑ j, (c j - c' j) * Φ i j := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hcross : (∑ i, w i * lstsqResidual Φ Y c i * d i) = 0 := by
    dsimp [d]
    calc
      (∑ i, w i * lstsqResidual Φ Y c i * (∑ j, (c j - c' j) * Φ i j)) =
          ∑ i, ∑ j, (c j - c' j) * (w i * lstsqResidual Φ Y c i * Φ i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ j, ∑ i, (c j - c' j) * (w i * lstsqResidual Φ Y c i * Φ i j) := by
        rw [Finset.sum_comm]
      _ = ∑ j, (c j - c' j) * (∑ i, w i * lstsqResidual Φ Y c i * Φ i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = 0 := by
        simp [hortho]
  unfold lstsqObjective
  have hsum :
      (∑ i, w i * lstsqResidual Φ Y c' i ^ 2) =
        (∑ i, w i * lstsqResidual Φ Y c i ^ 2)
          + 2 * (∑ i, w i * lstsqResidual Φ Y c i * d i)
          + ∑ i, w i * d i ^ 2 := by
    calc
      (∑ i, w i * lstsqResidual Φ Y c' i ^ 2) =
          ∑ i, (w i * lstsqResidual Φ Y c i ^ 2
            + 2 * (w i * lstsqResidual Φ Y c i * d i)
            + w i * d i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hkey i]
        ring
      _ = (∑ i, w i * lstsqResidual Φ Y c i ^ 2)
          + 2 * (∑ i, w i * lstsqResidual Φ Y c i * d i)
          + ∑ i, w i * d i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum, hcross]
  dsimp [d]
  ring

/-- **Optimality of the orthogonal least-squares fit.** With nonnegative weights, a residual
orthogonal to every design column attains the minimal weighted sum of squares:
`SSE(c) ≤ SSE(c')` for every `c'`. (Immediate from `lstsq_pythagoras`, the excess term being a
nonnegative weighted sum of squares.) -/
theorem lstsq_objective_le_of_orthogonal {N : ℕ} {ι : Type*} [Fintype ι]
    {Φ : Fin N → ι → ℝ} {w Y : Fin N → ℝ} {c : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hortho : ∀ k : ι, ∑ i, w i * lstsqResidual Φ Y c i * Φ i k = 0)
    (c' : ι → ℝ) :
    lstsqObjective Φ w Y c ≤ lstsqObjective Φ w Y c' := by
  rw [lstsq_pythagoras hortho c']
  have hnn : 0 ≤ ∑ i, w i * (∑ j, (c j - c' j) * Φ i j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  linarith

end Causalean.Stat.Nonparametric
