/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sävje–Aronow–Hudgens (2021): confidence statements under unknown interference

The paper's third contribution: the precision of the Horvitz–Thompson estimator, and why the
conventional variance estimator may mislead under interference.

* **The warning** — the conventional Horvitz–Thompson variance estimator `V̂_Ber = n⁻²∑ᵢ ĤTᵢ²` has
  `E[V̂_Ber] − Var(ĤT) = n⁻²(∑ᵢ(E ĤTᵢ)² − ∑_{i≠j} Cov(ĤTᵢ,ĤTⱼ))`. The off-diagonal covariances are
  nonzero only between interference-dependent units, can have either sign, and are exactly the bias
  that makes `V̂_Ber` anti-conservative (understate uncertainty) under interference.
* **The fix** — inflating the conventional estimator by an interference-degree measure restores
  conservativeness: `Var(ĤT) ≤ (1 + D)·E[V̂_Ber]` whenever every unit's interference degree is at
  most `D`. (Unconditional, in expectation — the cleaner cousin of the paper's `d_max`/spectral-radius
  inflated estimators.)
* **The interval** — since the paper proves a central limit theorem generally fails (Chebyshev is
  sharp), the valid confidence statement is **Chebyshev-based**: any conservative variance bound `V ≥
  Var(ĤT)` yields the interval `ĤT ± √(V/α)` with coverage of EATE at least `1 − α` (exact, using HT
  unbiasedness `E[ĤT] = EATE`). Instantiating with the proven `Var(ĤT) ≤ k⁴·d̄/n` gives a concrete
  finite-sample valid interval for EATE under unknown interference.

**Scope / faithfulness.** The conservativeness here is *in expectation*; the paper's data-dependent
estimators are asymptotically conservative *in probability*, which additionally needs the estimator
to concentrate (`Var(V̂) → 0`) — the same in-expectation-vs-in-probability boundary as the
Liu–Hudgens feasible interval, left as the next step. The full anti-conservativeness *limit*
(Proposition with the `B₁`/`B₂` spillover decomposition) is also deferred; the exact finite-sample
bias identity here is its honest core.
-/

import Causalean.Experimentation.UnknownInterference.VarianceBound
import Causalean.Experimentation.UnknownInterference.Unbiased
import Causalean.Experimentation.DesignBased.Chebyshev

/-! # Confidence under unknown interference

Chebyshev confidence statements remain valid under unknown interference when they use proven
conservative variance bounds.

This file formalizes three finite-sample confidence facts for the Sävje-Aronow-Hudgens
Bernoulli setup.  The conventional variance estimator `VhatBer` has an exact expectation-bias
identity `E_VhatBer_bias`, showing how off-diagonal covariances from interference can make it
anti-conservative.  The degree statistic `degDep` supports `var_htEst_le_inflated`, an
in-expectation conservative inflation of `VhatBer` when each unit has bounded interference
degree.  Finally, `chebyshev_ci_eate` proves coverage for any positive conservative variance
bound, and `eate_ci_kbound` instantiates it with the finite-sample variance bound
`k^4 * dbar / n`.
-/

open scoped BigOperators Classical
open Finset

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The conventional Horvitz–Thompson variance estimator** `V̂_Ber = n⁻² ∑ᵢ ĤTᵢ²`.  Pointwise this
equals the paper's `n⁻²[∑ᵢ ZᵢYᵢ²/pᵢ² + ∑ᵢ(1−Zᵢ)Yᵢ²/(1−pᵢ)²]` (the cross term vanishes since
`Zᵢ(1−Zᵢ)=0`). -/
noncomputable def VhatBer (p : U → ℝ) (y : U → (U → Bool) → ℝ) (z : U → Bool) : ℝ :=
  (∑ i, (htSummand p y i z) ^ 2) / (Fintype.card U : ℝ) ^ 2

/-- The interference **degree** of unit `i`: the number of units interference-dependent with `i`
(`d̄ᵢ = ∑ⱼ 1[InterfDep i j]`). -/
noncomputable def degDep (y : U → (U → Bool) → ℝ) (i : U) : ℝ :=
  ∑ j, if InterfDep y i j then (1 : ℝ) else 0

/-- `E[V̂_Ber] = n⁻² ∑ᵢ E[ĤTᵢ²]` — pushing expectation through the conventional estimator. -/
private lemma E_VhatBer_eq (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) :
    (bernoulliDesign p hp0 hp1).E (VhatBer p y)
      = (∑ i, (bernoulliDesign p hp0 hp1).E (fun z => (htSummand p y i z) ^ 2))
        / (Fintype.card U : ℝ) ^ 2 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hEq : D.E (VhatBer p y)
      = D.E (fun z => (n ^ 2)⁻¹ * ∑ i, (htSummand p y i z) ^ 2) := by
    refine D.E_congr (fun z => ?_)
    unfold VhatBer
    rw [hn, div_eq_inv_mul]
  rw [hEq, D.E_const_mul, D.E_sum]
  rw [div_eq_inv_mul]

/-- `Var(ĤT) = n⁻² ∑ᵢ ∑ⱼ Cov(ĤTᵢ, ĤTⱼ)` — variance of a scaled sum. -/
private lemma Var_htEst_eq (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) :
    (bernoulliDesign p hp0 hp1).Var (htEst p y)
      = (∑ i, ∑ j, (bernoulliDesign p hp0 hp1).Cov (htSummand p y i) (htSummand p y j))
        / (Fintype.card U : ℝ) ^ 2 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hEstEq : htEst p y = fun z => n⁻¹ * ∑ i : U, (1 : ℝ) * htSummand p y i z := by
    funext z; unfold htEst; rw [hn, div_eq_inv_mul]; congr 1
    exact Finset.sum_congr rfl (fun i _ => (one_mul _).symm)
  rw [hEstEq, D.Var_const_mul, D.Var_linear_comb Finset.univ (fun _ => (1:ℝ)) (htSummand p y)]
  rw [inv_pow, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [one_mul, one_mul]

/-- **The anti-conservativeness mechanism (Sävje–Aronow–Hudgens 2021).** For the Bernoulli design,
the conventional variance estimator's expectation equals the true variance plus the average of the
squared per-unit means minus the off-diagonal covariances. -/
theorem E_VhatBer_bias (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) :
    (bernoulliDesign p hp0 hp1).E (VhatBer p y)
      = (bernoulliDesign p hp0 hp1).Var (htEst p y)
        + (∑ i, ((bernoulliDesign p hp0 hp1).E (htSummand p y i)) ^ 2
            - ∑ i, ∑ j ∈ Finset.univ.erase i,
                (bernoulliDesign p hp0 hp1).Cov (htSummand p y i) (htSummand p y j))
          / (Fintype.card U : ℝ) ^ 2 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  rw [E_VhatBer_eq p hp0 hp1 y, Var_htEst_eq p hp0 hp1 y]
  -- `E[ĤTᵢ²] = Var(ĤTᵢ) + (E ĤTᵢ)²`.
  have hsq : ∀ i, D.E (fun z => (htSummand p y i z) ^ 2)
      = D.Var (htSummand p y i) + (D.E (htSummand p y i)) ^ 2 := by
    intro i; rw [D.Var_eq]; ring
  -- Split the inner full sum into the diagonal `Var` + the off-diagonal covariances.
  have hsplit : ∀ i, ∑ j, D.Cov (htSummand p y i) (htSummand p y j)
      = D.Var (htSummand p y i)
        + ∑ j ∈ Finset.univ.erase i, D.Cov (htSummand p y i) (htSummand p y j) := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ
          (fun j => D.Cov (htSummand p y i) (htSummand p y j)) (Finset.mem_univ i)]
    rw [D.Cov_self]
  -- Rewrite both numerators.
  rw [Finset.sum_congr rfl (fun i _ => hsq i)]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i)]
  -- Now both sides are sums divided by `n²`; collect over `n²`.
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rcases eq_or_ne (n ^ 2) 0 with h0 | h0
  · have : (Fintype.card U : ℝ) ^ 2 = 0 := by rw [← hn]; exact h0
    rw [this]; simp
  · field_simp
    ring

/-- **Conservative inflation (Sävje–Aronow–Hudgens 2021).** Inflating the conventional estimator by
`(1 + D)`, where `D` bounds every unit's interference degree, makes it conservative in expectation:
`Var(ĤT) ≤ (1 + D)·E[V̂_Ber]`.  The off-diagonal covariances are bounded by the per-unit variances
(`|Cov(ĤTᵢ,ĤTⱼ)| ≤ (Var ĤTᵢ + Var ĤTⱼ)/2 ≤ (E[ĤTᵢ²]+E[ĤTⱼ²])/2`), and each unit appears in at most
`D` interference-dependent pairs. -/
theorem var_htEst_le_inflated (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) (D : ℝ) (hD : ∀ i, degDep y i ≤ D) :
    (bernoulliDesign p hp0 hp1).Var (htEst p y)
      ≤ (1 + D) * (bernoulliDesign p hp0 hp1).E (VhatBer p y) := by
  set Des := bernoulliDesign p hp0 hp1 with hDes
  set n : ℝ := (Fintype.card U : ℝ) with hn
  -- Abbreviation for `E[ĤTᵢ²]`, and its key facts.
  set Ec : U → ℝ := fun i => Des.E (fun z => (htSummand p y i z) ^ 2) with hEc
  have hEc_nonneg : ∀ i, 0 ≤ Ec i := fun i => Des.E_nonneg (fun _ => sq_nonneg _)
  have hVar_le : ∀ i, Des.Var (htSummand p y i) ≤ Ec i := by
    intro i; rw [Des.Var_eq]; have := sq_nonneg (Des.E (htSummand p y i)); linarith
  -- Symmetry of interference dependence.
  have hsymm : ∀ i j, InterfDep y i j → InterfDep y j i := by
    rintro i j ⟨ℓ, h1, h2⟩; exact ⟨ℓ, h2, h1⟩
  -- Diagonal extraction: `∑ⱼ Cov(i,j) = Var(i) + ∑_{j≠i} Cov(i,j)`.
  have hsplit : ∀ i, ∑ j, Des.Cov (htSummand p y i) (htSummand p y j)
      = Des.Var (htSummand p y i)
        + ∑ j ∈ Finset.univ.erase i, Des.Cov (htSummand p y i) (htSummand p y j) := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ
          (fun j => Des.Cov (htSummand p y i) (htSummand p y j)) (Finset.mem_univ i), Des.Cov_self]
  -- Off-diagonal covariance bound: `Cov(i,j) ≤ (Eᵢ+Eⱼ)/2` when dependent, `= 0` otherwise.
  have hcov_le : ∀ i j, Des.Cov (htSummand p y i) (htSummand p y j)
      ≤ (if InterfDep y i j then (Ec i + Ec j) / 2 else 0) := by
    intro i j
    by_cases hdep : InterfDep y i j
    · rw [if_pos hdep]
      have hVsub : 0 ≤ Des.Var (fun z => htSummand p y i z - htSummand p y j z) :=
        Des.E_nonneg (fun _ => sq_nonneg _)
      rw [Des.Var_sub] at hVsub
      have hi := hVar_le i; have hj := hVar_le j; linarith
    · rw [if_neg hdep]
      exact le_of_eq (cov_htSummand_zero p hp0 hp1 y hdep)
  -- Off-diagonal double sum ≤ the `(Eᵢ+Eⱼ)/2` bound.
  have hoff_le : (∑ i, ∑ j ∈ Finset.univ.erase i, Des.Cov (htSummand p y i) (htSummand p y j))
      ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
          (if InterfDep y i j then (Ec i + Ec j) / 2 else 0) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov_le i j))
  -- Extend `erase i` to `univ` (nonneg terms).
  have hext : (∑ i, ∑ j ∈ Finset.univ.erase i,
        (if InterfDep y i j then (Ec i + Ec j) / 2 else 0))
      ≤ ∑ i, ∑ j, (if InterfDep y i j then (Ec i + Ec j) / 2 else 0) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ) ?_
    intro j _ _; by_cases hdep : InterfDep y i j
    · rw [if_pos hdep]; have := hEc_nonneg i; have := hEc_nonneg j; linarith
    · rw [if_neg hdep]
  -- Split the full double sum into `(S1 + S2)/2`.
  have hsplit2 : (∑ i, ∑ j, (if InterfDep y i j then (Ec i + Ec j) / 2 else 0))
      = ((∑ i, ∑ j, (if InterfDep y i j then Ec i else 0))
          + ∑ i, ∑ j, (if InterfDep y i j then Ec j else 0)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hdep : InterfDep y i j <;> simp [hdep]
  -- `S1 = ∑ᵢ Eᵢ·degDep i ≤ D·∑ᵢ Eᵢ`.
  have hS1 : (∑ i, ∑ j, (if InterfDep y i j then Ec i else 0)) ≤ D * ∑ i, Ec i := by
    have hrw : (∑ i, ∑ j, (if InterfDep y i j then Ec i else 0))
        = ∑ i, Ec i * degDep y i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [degDep, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hdep : InterfDep y i j <;> simp [hdep]
    rw [hrw, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [mul_comm (Ec i)]
    exact mul_le_mul_of_nonneg_right (hD i) (hEc_nonneg i)
  -- `S2`: swap order, use symmetry, same bound.
  have hS2 : (∑ i, ∑ j, (if InterfDep y i j then Ec j else 0)) ≤ D * ∑ i, Ec i := by
    rw [Finset.sum_comm]
    have hrw : (∑ j, ∑ i, (if InterfDep y i j then Ec j else 0))
        = ∑ j, Ec j * degDep y j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [degDep, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hdep : InterfDep y j i
      · rw [if_pos (hsymm j i hdep), if_pos hdep, mul_one]
      · rw [if_neg (fun hc => hdep (hsymm i j hc)), if_neg hdep, mul_zero]
    rw [hrw, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [mul_comm (Ec j)]
    exact mul_le_mul_of_nonneg_right (hD j) (hEc_nonneg j)
  -- Off-diagonal ≤ D·∑ᵢ Eᵢ.
  have hoff_D : (∑ i, ∑ j ∈ Finset.univ.erase i, Des.Cov (htSummand p y i) (htSummand p y j))
      ≤ D * ∑ i, Ec i := by
    calc (∑ i, ∑ j ∈ Finset.univ.erase i, Des.Cov (htSummand p y i) (htSummand p y j))
        ≤ ∑ i, ∑ j, (if InterfDep y i j then (Ec i + Ec j) / 2 else 0) := le_trans hoff_le hext
      _ = ((∑ i, ∑ j, (if InterfDep y i j then Ec i else 0))
            + ∑ i, ∑ j, (if InterfDep y i j then Ec j else 0)) / 2 := hsplit2
      _ ≤ D * ∑ i, Ec i := by linarith [hS1, hS2]
  -- Whole double sum ≤ (1+D)·∑ᵢ Eᵢ.
  have hdouble : (∑ i, ∑ j, Des.Cov (htSummand p y i) (htSummand p y j))
      ≤ (1 + D) * ∑ i, Ec i := by
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    have hdiag : (∑ i, Des.Var (htSummand p y i)) ≤ ∑ i, Ec i :=
      Finset.sum_le_sum (fun i _ => hVar_le i)
    have hexp : (1 + D) * ∑ i, Ec i = (∑ i, Ec i) + D * ∑ i, Ec i := by ring
    rw [hexp]; linarith [hdiag, hoff_D]
  -- Divide by `n²`.
  rw [Var_htEst_eq p hp0 hp1 y, E_VhatBer_eq p hp0 hp1 y, ← hEc, ← hn, ← mul_div_assoc]
  gcongr

/-- **Chebyshev confidence interval for EATE.** For a positive conservative variance bound
`V ≥ Var(ĤT)`, positive `α`, and nonzero treatment and control propensities, the interval
`ĤT ± √(V/α)` covers the EATE estimand with probability at least `1 − α`. -/
theorem chebyshev_ci_eate (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0) (y : U → (U → Bool) → ℝ)
    {V α : ℝ} (hV0 : 0 < V) (hV : (bernoulliDesign p hp0 hp1).Var (htEst p y) ≤ V) (hα : 0 < α) :
    1 - α ≤ (bernoulliDesign p hp0 hp1).Pr
      (fun z => |htEst p y z - EATE (bernoulliDesign p hp0 hp1) y| ≤ Real.sqrt (V / α)) := by
  classical
  set D := bernoulliDesign p hp0 hp1 with hD
  set t : ℝ := Real.sqrt (V / α) with ht
  have hVα : 0 < V / α := div_pos hV0 hα
  have ht0 : 0 < t := Real.sqrt_pos.mpr hVα
  have ht2 : t ^ 2 = V / α := by rw [ht, Real.sq_sqrt (le_of_lt hVα)]
  have hμ : D.E (htEst p y) = EATE D y := htEst_unbiased p hp0 hp1 hp0' hp1' y
  -- Chebyshev: Pr(t ≤ |htEst - EATE|) ≤ Var / t²
  have hcheb := D.chebyshev (htEst p y) ht0
  rw [hμ] at hcheb
  set A : (U → Bool) → Prop := fun z => |htEst p y z - EATE D y| ≤ t with hA
  set B : (U → Bool) → Prop := fun z => t ≤ |htEst p y z - EATE D y| with hB
  -- Pr B ≤ α.
  have hVt : D.Var (htEst p y) / t ^ 2 ≤ α := by
    rw [ht2]
    have hstep : D.Var (htEst p y) / (V / α) ≤ V / (V / α) :=
      div_le_div_of_nonneg_right hV (by positivity)
    have hVdiv : V / (V / α) = α := by field_simp
    rw [hVdiv] at hstep; exact hstep
  have hPrB : D.Pr B ≤ α := le_trans hcheb hVt
  -- A and B cover everything: ind A + ind B ≥ 1 pointwise.
  have hcover : ∀ z, (1 : ℝ) ≤ FiniteDesign.ind A z + FiniteDesign.ind B z := by
    intro z
    rcases le_total (|htEst p y z - EATE D y|) t with h | h
    · have hi : FiniteDesign.ind A z = 1 := by unfold FiniteDesign.ind A; simp [h]
      have hBn : 0 ≤ FiniteDesign.ind B z := FiniteDesign.ind_nonneg B z
      rw [hi]; linarith
    · have hi : FiniteDesign.ind B z = 1 := by unfold FiniteDesign.ind B; simp [h]
      have hAn : 0 ≤ FiniteDesign.ind A z := FiniteDesign.ind_nonneg A z
      rw [hi]; linarith
  -- 1 = E[1] ≤ E[ind A + ind B] = Pr A + Pr B.
  have h1le : (1 : ℝ) ≤ D.Pr A + D.Pr B := by
    have hEmono : D.E (fun _ => (1 : ℝ))
        ≤ D.E (fun z => FiniteDesign.ind A z + FiniteDesign.ind B z) := by
      unfold FiniteDesign.E
      exact Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (hcover z) (D.p_nonneg z))
    rw [D.E_const, D.E_add] at hEmono
    change (1 : ℝ) ≤ D.E (FiniteDesign.ind A) + D.E (FiniteDesign.ind B)
    exact hEmono
  linarith [hPrB, h1le]

/-- `d̄ ≥ 1`: the diagonal pairs `InterfDep i i` (each holds) already contribute `n`. -/
private lemma one_le_dbar (y : U → (U → Bool) → ℝ) (hcard : 1 ≤ Fintype.card U) :
    1 ≤ dbar y := by
  have hn0 : (0 : ℝ) < (Fintype.card U : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  -- dbarCount ≥ n: each diagonal term is 1, and the inner sum dominates the diagonal term.
  have hdiag : ∀ i : U, (1 : ℝ) ≤ ∑ j : U, if InterfDep y i j then (1 : ℝ) else 0 := by
    intro i
    have hii : InterfDep y i i := ⟨i, Or.inl rfl, Or.inl rfl⟩
    have hterm : (if InterfDep y i i then (1 : ℝ) else 0) = 1 := by simp [hii]
    calc (1 : ℝ) = (if InterfDep y i i then (1 : ℝ) else 0) := hterm.symm
      _ ≤ ∑ j : U, if InterfDep y i j then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun j => if InterfDep y i j then (1 : ℝ) else 0)
            (fun j _ => by positivity) (Finset.mem_univ i)
  have hcount : (Fintype.card U : ℝ) ≤ dbarCount y := by
    unfold dbarCount
    calc (Fintype.card U : ℝ) = ∑ _i : U, (1 : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ]; simp
      _ ≤ ∑ i : U, ∑ j : U, if InterfDep y i j then (1 : ℝ) else 0 :=
          Finset.sum_le_sum (fun i _ => hdiag i)
  rw [dbar, le_div_iff₀ hn0, one_mul]
  exact hcount

/-- **A concrete finite-sample confidence interval for EATE (Sävje–Aronow–Hudgens 2021).** Under the
regularity conditions, the Chebyshev interval `ĤT ± √(k⁴·d̄/(n·α))` covers EATE with probability at
least `1 − α` — a valid (conservative) interval under unknown interference, needing only the
regularity constant `k` and the interference measure `d̄`. -/
theorem eate_ci_kbound (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0) (y : U → (U → Bool) → ℝ)
    (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U)
    (hplo : ∀ i, k⁻¹ ≤ p i) (hphi : ∀ i, p i ≤ 1 - k⁻¹)
    (hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2)
    {α : ℝ} (hα : 0 < α) :
    1 - α ≤ (bernoulliDesign p hp0 hp1).Pr
      (fun z => |htEst p y z - EATE (bernoulliDesign p hp0 hp1) y|
        ≤ Real.sqrt (k ^ 4 * dbar y / ((Fintype.card U : ℝ) * α))) := by
  set V : ℝ := k ^ 4 * dbar y / (Fintype.card U : ℝ) with hVdef
  have hn0 : (0 : ℝ) < (Fintype.card U : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hdbar1 : 1 ≤ dbar y := one_le_dbar y hcard
  have hdbar0 : 0 < dbar y := lt_of_lt_of_le zero_lt_one hdbar1
  have hV0 : 0 < V := by rw [hVdef]; positivity
  have hV : (bernoulliDesign p hp0 hp1).Var (htEst p y) ≤ V :=
    var_htEst_le p hp0 hp1 y k hk hcard hplo hphi hmom
  have hci := chebyshev_ci_eate p hp0 hp1 hp0' hp1' y hV0 hV hα
  -- The interval radius matches: √(V/α) = √(k⁴·d̄/(n·α)).
  have harg : V / α = k ^ 4 * dbar y / ((Fintype.card U : ℝ) * α) := by
    rw [hVdef, div_div]
  rw [harg] at hci
  exact hci

end UnknownInterference
end Experimentation
end Causalean
