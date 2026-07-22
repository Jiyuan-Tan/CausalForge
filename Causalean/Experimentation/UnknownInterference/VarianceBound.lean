/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sävje–Aronow–Hudgens (2021): the Horvitz–Thompson variance bound under a Bernoulli design

Under a Bernoulli design with regularity constant `k` (treatment probabilities in `[k⁻¹, 1−k⁻¹]`
and second moments `E[Y_i²] ≤ k²`), the Horvitz–Thompson estimator's variance is controlled by the
average interference dependence:

    Var(ĤT) ≤ k⁴ · d̄ / n.

This is the quantitative heart of the paper (the bound stated in the body just before §4): it makes
the variance vanish, hence the estimator consistent, exactly when `d̄ = o(n)`.  The argument:

1. `Var(ĤT) = n⁻² ∑ᵢ ∑ⱼ Cov(HTᵢ, HTⱼ)` (variance of a sum).
2. `Cov(HTᵢ, HTⱼ) = 0` whenever `i` and `j` are **not** interference dependent: their HT summands
   depend on the disjoint coordinate blocks `interferers i` and `interferers j`, so the
   disjoint-block independence `Cov_prod_disjoint_zero` applies.
3. Each surviving covariance is bounded by `k⁴` via `|Cov(X,Y)| ≤ (Var X + Var Y)/2` and the
   per-summand variance bound `Var(HTᵢ) ≤ E[HTᵢ²] ≤ k²·E[Y_i²] ≤ k⁴` (using `|HTᵢ| ≤ k·|Y_i|`).
4. The number of interference-dependent ordered pairs is `dbarCount = n·d̄`, giving the bound.
-/

import Causalean.Experimentation.UnknownInterference.Bernoulli
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance

/-! # Variance bounds under unknown interference

The Horvitz-Thompson variance is bounded by the average amount of interference dependence under
Bernoulli assignment.

This file proves the Sävje-Aronow-Hudgens finite-sample bound
`Var(htEst) <= k^4 * dbar / n` under overlap and second-moment control.  The block
`interferers y i` records the coordinate support of the `i`th HT summand;
`htSummand_depends_on_interferers` and `disjoint_interferers_of_not_interfDep` connect the
interference graph to product-design disjoint-block independence, and `cov_htSummand_zero`
eliminates covariance terms off that graph.  The per-summand bound `var_htSummand_le` controls
the remaining covariance terms by `k^4`, and the headline theorem `var_htEst_le` sums them over
the `dbarCount = n * dbar` dependent ordered pairs.
-/

open scoped BigOperators Classical
open Finset

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The block of units that interfere with `i` (its own treatment included): the coordinate support
of the `i`ᵗʰ HT summand. -/
noncomputable def interferers (y : U → (U → Bool) → ℝ) (i : U) : Finset U :=
  Finset.univ.filter (fun ℓ => Interferes y ℓ i)

/-- The `i`ᵗʰ HT summand depends only on the treatments of the units interfering with `i`. -/
theorem htSummand_depends_on_interferers (p : U → ℝ) (y : U → (U → Bool) → ℝ) (i : U)
    (z z' : U → Bool) (h : ∀ ℓ ∈ interferers y i, z ℓ = z' ℓ) :
    htSummand p y i z = htSummand p y i z' := by
  have hmem : ∀ ℓ : U, Interferes y ℓ i → ℓ ∈ interferers y i := by
    intro ℓ hℓ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, hℓ⟩
  -- `i` interferes with itself, so `z i = z' i`.
  have hzi : z i = z' i := h i (hmem i (Or.inl rfl))
  -- The outcome agrees because `z, z'` agree on all interferers of `i`.
  have hyi : y i z = y i z' :=
    y_eq_of_agree_on_interferers y i z z' (fun ℓ hℓ => h ℓ (hmem ℓ hℓ))
  unfold htSummand
  rw [hzi, hyi]

/-- If `i` and `j` are not interference dependent, their interferer blocks are disjoint. -/
theorem disjoint_interferers_of_not_interfDep (y : U → (U → Bool) → ℝ) {i j : U}
    (h : ¬ InterfDep y i j) :
    Disjoint (interferers y i) (interferers y j) := by
  rw [Finset.disjoint_left]
  intro ℓ hℓi hℓj
  have hi : Interferes y ℓ i := (Finset.mem_filter.mp hℓi).2
  have hj : Interferes y ℓ j := (Finset.mem_filter.mp hℓj).2
  exact h ⟨ℓ, hi, hj⟩

/-- **No covariance off the interference-dependence graph.** Under the Bernoulli design, two HT
summands are uncorrelated when their units are not interference dependent. -/
theorem cov_htSummand_zero (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) {i j : U} (h : ¬ InterfDep y i j) :
    (bernoulliDesign p hp0 hp1).Cov (htSummand p y i) (htSummand p y j) = 0 := by
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  unfold bernoulliDesign
  exact FiniteDesign.Cov_prod_disjoint_zero (fun i => coinDesign (p i) (hp0 i) (hp1 i))
    (interferers y i) (interferers y j) (disjoint_interferers_of_not_interfDep y h)
    (htSummand p y i) (htSummand p y j)
    (fun z z' hzz => htSummand_depends_on_interferers p y i z z' hzz)
    (fun z z' hzz => htSummand_depends_on_interferers p y j z z' hzz)

/-- Monotonicity of expectation: pointwise `≤` lifts to `E`. -/
private lemma E_mono {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) {X Y : Ω → ℝ}
    (h : ∀ z, X z ≤ Y z) : D.E X ≤ D.E Y :=
  Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z) (D.p_nonneg z))

/-- Variance is nonnegative (it is the expectation of a square). -/
private lemma Var_nonneg {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) (X : Ω → ℝ) :
    0 ≤ D.Var X :=
  D.E_nonneg (fun _ => sq_nonneg _)

/-- **Per-summand variance bound.** Under the regularity conditions, `Var(HTᵢ) ≤ k⁴`. -/
theorem var_htSummand_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k)
    (hplo : ∀ i, k⁻¹ ≤ p i) (hphi : ∀ i, p i ≤ 1 - k⁻¹)
    (hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2) (i : U) :
    (bernoulliDesign p hp0 hp1).Var (htSummand p y i) ≤ k ^ 4 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkinv0 : (0 : ℝ) < k⁻¹ := inv_pos.mpr hk0
  have hpi0 : (0 : ℝ) < p i := lt_of_lt_of_le hkinv0 (hplo i)
  have hpi1 : (0 : ℝ) < 1 - p i := lt_of_lt_of_le hkinv0 (by linarith [hphi i])
  -- `1/p i ≤ k` and `1/(1 - p i) ≤ k`.
  have hrecp : 1 / p i ≤ k := by
    rw [div_le_iff₀ hpi0]
    have := (hplo i)
    have hk' : k⁻¹ * k = 1 := inv_mul_cancel₀ (ne_of_gt hk0)
    nlinarith [mul_le_mul_of_nonneg_right (hplo i) (le_of_lt hk0)]
  have hrecq : 1 / (1 - p i) ≤ k := by
    rw [div_le_iff₀ hpi1]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith [hphi i] : k⁻¹ ≤ 1 - p i) (le_of_lt hk0),
      inv_mul_cancel₀ (ne_of_gt hk0)]
  -- Pointwise: `(htSummand)² ≤ k² (y i)²`.
  have hpt : ∀ z, (htSummand p y i z) ^ 2 ≤ k ^ 2 * (y i z) ^ 2 := by
    intro z
    have habs : |htSummand p y i z| ≤ k * |y i z| := by
      unfold htSummand
      by_cases hz : z i = true
      · rw [if_pos hz, if_pos hz]
        rw [show (1 : ℝ) * y i z / p i - (0 : ℝ) * y i z / (1 - p i) = y i z / p i by ring]
        rw [abs_div, abs_of_pos hpi0]
        calc |y i z| / p i = |y i z| * (1 / p i) := by ring
          _ ≤ |y i z| * k := by
                apply mul_le_mul_of_nonneg_left hrecp (abs_nonneg _)
          _ = k * |y i z| := by ring
      · rw [if_neg hz, if_neg hz]
        rw [show (0 : ℝ) * y i z / p i - (1 : ℝ) * y i z / (1 - p i)
              = - (y i z / (1 - p i)) by ring]
        rw [abs_neg, abs_div, abs_of_pos hpi1]
        calc |y i z| / (1 - p i) = |y i z| * (1 / (1 - p i)) := by ring
          _ ≤ |y i z| * k := by
                apply mul_le_mul_of_nonneg_left hrecq (abs_nonneg _)
          _ = k * |y i z| := by ring
    have h1 : (htSummand p y i z) ^ 2 = |htSummand p y i z| ^ 2 := (sq_abs _).symm
    have h2 : (k * |y i z|) ^ 2 = k ^ 2 * (y i z) ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [h1, ← h2]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  -- `Var ≤ E[(htSummand)²] ≤ E[k² (y i)²] = k² E[(y i)²] ≤ k² · k² = k⁴`.
  calc D.Var (htSummand p y i)
      ≤ D.E (fun z => (htSummand p y i z) ^ 2) := by
        rw [D.Var_eq]; linarith [sq_nonneg (D.E (htSummand p y i))]
    _ ≤ D.E (fun z => k ^ 2 * (y i z) ^ 2) := E_mono D hpt
    _ = k ^ 2 * D.E (fun z => (y i z) ^ 2) := D.E_const_mul _ _
    _ ≤ k ^ 2 * k ^ 2 := by
        apply mul_le_mul_of_nonneg_left (hmom i) (sq_nonneg k)
    _ = k ^ 4 := by ring

/-- **The Horvitz–Thompson variance bound (Sävje–Aronow–Hudgens 2021).** Under a Bernoulli design
with regularity constant `k`, `Var(ĤT) ≤ k⁴ · d̄ / n`. -/
theorem var_htEst_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U)
    (hplo : ∀ i, k⁻¹ ≤ p i) (hphi : ∀ i, p i ≤ 1 - k⁻¹)
    (hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2) :
    (bernoulliDesign p hp0 hp1).Var (htEst p y) ≤ k ^ 4 * dbar y / (Fintype.card U : ℝ) := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by
    rw [hn]; exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  -- Termwise covariance bound: `Cov(HTᵢ, HTⱼ) ≤ (if InterfDep then k⁴ else 0)`.
  have hcov : ∀ i j, D.Cov (htSummand p y i) (htSummand p y j)
      ≤ (if InterfDep y i j then (k ^ 4 : ℝ) else 0) := by
    intro i j
    by_cases hdep : InterfDep y i j
    · rw [if_pos hdep]
      -- `Var(X−Y) ≥ 0` gives `Cov ≤ (Var X + Var Y)/2 ≤ k⁴`.
      have hVsub : 0 ≤ D.Var (fun z => htSummand p y i z - htSummand p y j z) :=
        Var_nonneg D _
      rw [D.Var_sub] at hVsub
      have hVi : D.Var (htSummand p y i) ≤ k ^ 4 :=
        var_htSummand_le p hp0 hp1 y k hk hplo hphi hmom i
      have hVj : D.Var (htSummand p y j) ≤ k ^ 4 :=
        var_htSummand_le p hp0 hp1 y k hk hplo hphi hmom j
      linarith
    · rw [if_neg hdep]
      exact le_of_eq (cov_htSummand_zero p hp0 hp1 y hdep)
  -- `htEst = n⁻¹ * ∑ᵢ HTᵢ`, so `Var(htEst) = (n⁻¹)² Var(∑ᵢ HTᵢ)`.
  have hEstEq : htEst p y
      = fun z => n⁻¹ * ∑ i : U, (1 : ℝ) * htSummand p y i z := by
    funext z; unfold htEst; rw [hn, div_eq_inv_mul]; congr 1
    exact Finset.sum_congr rfl (fun i _ => (one_mul _).symm)
  have hVarEst : D.Var (htEst p y)
      = (n⁻¹) ^ 2 * ∑ i : U, ∑ j : U, D.Cov (htSummand p y i) (htSummand p y j) := by
    rw [hEstEq, D.Var_const_mul, D.Var_linear_comb Finset.univ (fun _ => (1:ℝ)) (htSummand p y)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [one_mul, one_mul]
  -- Bound the double sum by `k⁴ · dbarCount`.
  have hsumle : (∑ i : U, ∑ j : U, D.Cov (htSummand p y i) (htSummand p y j))
      ≤ k ^ 4 * dbarCount y := by
    have hstep : (∑ i : U, ∑ j : U, D.Cov (htSummand p y i) (htSummand p y j))
        ≤ ∑ i : U, ∑ j : U, (if InterfDep y i j then (k ^ 4 : ℝ) else 0) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    refine le_trans hstep ?_
    rw [dbarCount]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hdep : InterfDep y i j <;> simp [hdep]
  -- Assemble the final bound.
  rw [hVarEst]
  have hk4 : (0 : ℝ) ≤ k ^ 4 := by positivity
  have hninv2 : (0 : ℝ) ≤ (n⁻¹) ^ 2 := sq_nonneg _
  calc (n⁻¹) ^ 2 * ∑ i : U, ∑ j : U, D.Cov (htSummand p y i) (htSummand p y j)
      ≤ (n⁻¹) ^ 2 * (k ^ 4 * dbarCount y) :=
        mul_le_mul_of_nonneg_left hsumle hninv2
    _ = k ^ 4 * dbar y / n := by
        rw [dbar, hn]
        ring

end UnknownInterference
end Experimentation
end Causalean
