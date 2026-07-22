/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional / cross-fit `O_p` rate for centered empirical means

Paper-agnostic workhorse behind every cross-fit / DML
"remainder-is-negligible" step: the centered empirical mean of a (possibly
cross-fit / conditional) score is `O_p(n^{-1/2} · (second-moment)^{1/2})`.

The bounded-in-probability predicate is the project's existing
`Causalean.Stat.IsBigOp` (`def:est-stoch-order`); we do **not** introduce a second
`O_p` predicate.  The conditional second-moment estimate is the existing engine
`Causalean.Mathlib.iid_centered_sum_sq_lintegral_le` (which already kills the
cross terms via the conditional product law).  What this file adds is:

* a small `IsBigOp` rate-algebra API (`mono_rate`, `scale_rate`,
  `const_rate_collapse`, `const_mul`, `add'`);
* the **Markov primitive** `IsBigOp.of_sq_lintegral_le`: a deterministic
  `L²`-second-moment envelope `∫⁻ (Xₙ)² ≤ Vₙ` yields `Xₙ = O_p(√Vₙ)`.  This is
  the step previously inlined (privately) in
  `Estimation/OrthogonalMoments/DMLCrossFit.lean`;
* **Lemma B** `isBigOp_centered_crossFit_sum`: the conditional / cross-fit
  lift — eval fold independent of a sub-σ-field `m_A`, nuisance `m_A`-measurable
  ⇒ the centered fold sum is `O_p(√Vₙ)` for any deterministic envelope `Vₙ`
  dominating `∫_Ω ‖g_n ω‖²_{L²(P)} dμ`;
* **Lemma A** the unconditional i.i.d. corollary: `∫(ℙₙf − m)² ≤ E_P[f²]/n`,
  the Chebyshev tail, and `(ℙₙf − m) = O_p(√(E_P[f²]/n))`.

The file is estimand-agnostic; the weak-overlap clipped-AIPW upper rate is just
the first downstream consumer.
-/

import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Sample
import Causalean.Mathlib.IIDCenteredSum
import Mathlib.Probability.Independence.Basic

/-!
This file provides reusable stochastic-order algebra and centered empirical-mean
rate bounds.  It extends `IsBigOp` with monotonicity, scaling, sum, finite-sum,
and product rules; proves `IsBigOp.of_sq_lintegral_le`, a Markov/Chebyshev
primitive from deterministic second-moment envelopes; proves the cross-fit fold
rate `isBigOp_centered_crossFit_sum`; and gives the i.i.d. sample-mean
corollaries `IIDSample.sampleMean_sub_sq_lintegral_le`,
`IIDSample.sampleMean_sub_meas_ge_le`, and `IIDSample.sampleMean_sub_isBigOp`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## Rate algebra for `IsBigOp`

Small reusable API on the existing `O_p` predicate: weaken to a larger rate,
absorb a positive constant rate factor, collapse a constant rate to `1`, pull a
constant multiple through, and add two `O_p` bounds at the sum of their rates.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {Xn Yn : ℕ → Ω → ℝ} {rn sn : ℕ → ℝ}

/-- **Weaken to a larger rate.**  `O_p(rₙ)` with `0 ≤ rₙ ≤ sₙ` is `O_p(sₙ)`:
a larger envelope is a weaker statement. -/
theorem IsBigOp.mono_rate (hrn : ∀ n, 0 ≤ rn n) (hle : ∀ n, rn n ≤ sn n)
    (h : IsBigOp Xn rn μ) : IsBigOp Xn sn μ := by
  intro ε hε
  rcases h ε hε with ⟨M0, hM0⟩
  let M : ℝ := max M0 0
  refine ⟨M, ?_⟩
  refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
  intro n
  apply measure_mono
  intro ω hω
  have hsn : 0 ≤ sn n := le_trans (hrn n) (hle n)
  have hMmul : M0 * rn n ≤ M * sn n := by
    by_cases hM0_nonneg : 0 ≤ M0
    · have hM_eq : M = M0 := by simp [M, hM0_nonneg]
      rw [hM_eq]
      exact mul_le_mul_of_nonneg_left (hle n) hM0_nonneg
    · have hM_eq : M = 0 := by
        simp [M, le_of_lt (lt_of_not_ge hM0_nonneg)]
      rw [hM_eq, zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hM0_nonneg) (hrn n)
  exact lt_of_le_of_lt hMmul hω

/-- **Absorb a positive constant rate factor.**  `O_p(c · rₙ)` with `c > 0` is
`O_p(rₙ)`; the constant is absorbed into the witness `M`. -/
theorem IsBigOp.scale_rate {c : ℝ} (hc : 0 < c)
    (h : IsBigOp Xn (fun n => c * rn n) μ) : IsBigOp Xn rn μ := by
  have _hc := hc
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M * c, ?_⟩
  simpa [mul_assoc] using hM

/-- **Collapse a constant rate to `1`.**  For a *fixed* nonnegative `N`,
`O_p(fun _ => N)` is `O_p(fun _ => 1)`: a constant scale only changes the
witness `M`.  Used to normalize the fold-sum `O_p` bounds to the canonical
unit rate consumed by the cross-fitted DML proofs. -/
theorem IsBigOp.const_rate_collapse {N : ℝ} (hN : 0 ≤ N)
    (h : IsBigOp Xn (fun _ => N) μ) : IsBigOp Xn (fun _ => (1 : ℝ)) μ := by
  have _hN := hN
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M * N, ?_⟩
  simpa using hM

/-- **Constant multiple.**  If `Xₙ = O_p(rₙ)` then `c · Xₙ = O_p(rₙ)` for any
fixed scalar `c`. -/
theorem IsBigOp.const_mul (c : ℝ) (h : IsBigOp Xn rn μ) :
    IsBigOp (fun n ω => c * Xn n ω) rn μ := by
  intro ε hε
  by_cases hc : c = 0
  · refine ⟨0, ?_⟩
    simp [hc]
  · rcases h ε hε with ⟨M, hM⟩
    refine ⟨|c| * M, ?_⟩
    have hcpos : 0 < |c| := abs_pos.mpr hc
    convert hM using 2
    ext n
    congr 1
    ext ω
    change |c| * M * rn n < |c * Xn n ω| ↔ M * rn n < |Xn n ω|
    rw [abs_mul]
    constructor
    · intro hω
      have hω' : |c| * (M * rn n) < |c| * |Xn n ω| := by
        simpa [mul_assoc] using hω
      nlinarith [hcpos]
    · intro hω
      have hω' : |c| * (M * rn n) < |c| * |Xn n ω| := by
        nlinarith [hcpos]
      simpa [mul_assoc] using hω'

/-- **Additivity at the sum rate.**  `O_p(rₙ) + O_p(sₙ) = O_p(rₙ + sₙ)`, for
nonnegative rates.  (`IsBigOp.add` is the special case `rₙ = sₙ`.) -/
theorem IsBigOp.add' (hrn : ∀ n, 0 ≤ rn n) (hsn : ∀ n, 0 ≤ sn n)
    (hX : IsBigOp Xn rn μ) (hY : IsBigOp Yn sn μ) :
    IsBigOp (fun n ω => Xn n ω + Yn n ω) (fun n => rn n + sn n) μ := by
  intro ε hε
  rcases hX (ε / 4) (by linarith) with ⟨MX0, hMX0⟩
  rcases hY (ε / 4) (by linarith) with ⟨MY0, hMY0⟩
  let MX : ℝ := max MX0 0
  let MY : ℝ := max MY0 0
  have hMX_nonneg : 0 ≤ MX := by exact le_max_right MX0 0
  have hMY_nonneg : 0 ≤ MY := by exact le_max_right MY0 0
  have hMX0_le : MX0 ≤ MX := by exact le_max_left MX0 0
  have hMY0_le : MY0 ≤ MY := by exact le_max_left MY0 0
  let M : ℝ := max MX MY
  have hMX_le_M : MX ≤ M := le_max_left MX MY
  have hMY_le_M : MY ≤ M := le_max_right MX MY
  refine ⟨M, ?_⟩
  let A : ℕ → Set Ω := fun n => {ω | MX0 * rn n < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | MY0 * sn n < |Yn n ω|}
  let C : ℕ → Set Ω := fun n =>
    {ω | M * (rn n + sn n) < |Xn n ω + Yn n ω|}
  have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
    intro n
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ MX0 * rn n < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl hx)
      have hnotB : ¬ MY0 * sn n < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr hy)
      have hXle0 : |Xn n ω| ≤ MX0 * rn n := le_of_not_gt hnotA
      have hYle0 : |Yn n ω| ≤ MY0 * sn n := le_of_not_gt hnotB
      have hXle : |Xn n ω| ≤ M * rn n := by
        calc
          |Xn n ω| ≤ MX0 * rn n := hXle0
          _ ≤ MX * rn n := mul_le_mul_of_nonneg_right hMX0_le (hrn n)
          _ ≤ M * rn n := mul_le_mul_of_nonneg_right hMX_le_M (hrn n)
      have hYle : |Yn n ω| ≤ M * sn n := by
        calc
          |Yn n ω| ≤ MY0 * sn n := hYle0
          _ ≤ MY * sn n := mul_le_mul_of_nonneg_right hMY0_le (hsn n)
          _ ≤ M * sn n := mul_le_mul_of_nonneg_right hMY_le_M (hsn n)
      have hsum : |Xn n ω + Yn n ω| ≤ M * (rn n + sn n) := by
        calc
          |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| :=
            abs_add_le (Xn n ω) (Yn n ω)
          _ ≤ M * rn n + M * sn n := add_le_add hXle hYle
          _ = M * (rn n + sn n) := by ring
      exact not_lt_of_ge hsum hω
    calc
      μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
  rw [Filter.limsup_le_iff]
  intro y hy
  have hquarter_half : ENNReal.ofReal (ε / 4) < ENNReal.ofReal (ε / 2) := by
    rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
  have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hMX0 hquarter_half)
  have hBevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hMY0 hquarter_half)
  filter_upwards [hAevent, hBevent] with n hAn hBn
  calc
    μ {ω | M * (fun n => rn n + sn n) n < |Xn n ω + Yn n ω|} = μ (C n) := by
      simp [C]
    _ ≤ μ (A n) + μ (B n) := hpoint n
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hAn hBn
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add]
      · congr 1; ring
      · linarith
      · linarith
    _ < y := hy

/-- If `|Xₙ| ≤ |Yₙ|` pointwise and `Yₙ = O_p(rₙ)`, then `Xₙ = O_p(rₙ)`. -/
theorem IsBigOp.of_abs_le (h : ∀ n ω, |Xn n ω| ≤ |Yn n ω|)
    (hY : IsBigOp Yn rn μ) : IsBigOp Xn rn μ := by
  intro ε hε
  rcases hY ε hε with ⟨M, hM⟩
  refine ⟨M, le_trans (Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_)) hM⟩
  intro n
  exact measure_mono fun ω hω => lt_of_lt_of_le hω (h n ω)

/-- The constant-zero sequence is `O_p(rₙ)` for any rate. -/
theorem IsBigOp.zero : IsBigOp (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) rn μ := by
  intro ε hε
  refine ⟨0, ?_⟩
  have hset : (fun n => μ {ω | (0 : ℝ) * rn n < |(0 : ℝ)|}) = fun _ => (0 : ENNReal) := by
    ext n; simp
  rw [hset, Filter.limsup_const]
  exact zero_le _

/-- A finite sum of `O_p(rₙ)` sequences is `O_p(rₙ)` (same rate; constants absorb). -/
theorem IsBigOp.finset_sum {ι : Type*} (s : Finset ι) {X : ι → ℕ → Ω → ℝ}
    (h : ∀ i ∈ s, IsBigOp (X i) rn μ) :
    IsBigOp (fun n ω => ∑ i ∈ s, X i n ω) rn μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hcast : (fun (n : ℕ) (ω : Ω) => ∑ i ∈ (∅ : Finset ι), X i n ω)
          = fun _ _ => (0 : ℝ) := by ext n ω; simp
      rw [hcast]; exact IsBigOp.zero
  | insert i s hi ih =>
      have hisum : IsBigOp (fun n ω => X i n ω + ∑ j ∈ s, X j n ω) rn μ :=
        IsBigOp.add (h i (Finset.mem_insert_self i s))
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
      refine IsBigOp.of_abs_le
        (Yn := fun n ω => X i n ω + ∑ j ∈ s, X j n ω) ?_ hisum
      intro n ω
      rw [Finset.sum_insert hi]

/-- **Product rule for stochastic big-O.**  If `Xₙ = O_p(rₙ)` and
`Yₙ = O_p(sₙ)` for nonnegative rates, then `XₙYₙ = O_p(rₙsₙ)`. -/
theorem IsBigOp.mul (hrn : ∀ n, 0 ≤ rn n) (hsn : ∀ n, 0 ≤ sn n)
    (hX : IsBigOp Xn rn μ) (hY : IsBigOp Yn sn μ) :
    IsBigOp (fun n ω => Xn n ω * Yn n ω) (fun n => rn n * sn n) μ := by
  intro ε hε
  rcases hX (ε / 4) (by linarith) with ⟨Mx0, hMx0⟩
  rcases hY (ε / 4) (by linarith) with ⟨My0, hMy0⟩
  let Mx : ℝ := max Mx0 0
  let My : ℝ := max My0 0
  have hMx_nonneg : 0 ≤ Mx := le_max_right Mx0 0
  have hMy_nonneg : 0 ≤ My := le_max_right My0 0
  have hMx0_le : Mx0 ≤ Mx := le_max_left Mx0 0
  have hMy0_le : My0 ≤ My := le_max_left My0 0
  refine ⟨Mx * My, ?_⟩
  let A : ℕ → Set Ω := fun n => {ω | Mx0 * rn n < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | My0 * sn n < |Yn n ω|}
  let C : ℕ → Set Ω := fun n =>
    {ω | (Mx * My) * (rn n * sn n) < |Xn n ω * Yn n ω|}
  have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
    intro n
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ Mx0 * rn n < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl hx)
      have hnotB : ¬ My0 * sn n < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr hy)
      have hXle0 : |Xn n ω| ≤ Mx0 * rn n := le_of_not_gt hnotA
      have hYle0 : |Yn n ω| ≤ My0 * sn n := le_of_not_gt hnotB
      have hXle : |Xn n ω| ≤ Mx * rn n := by
        exact le_trans hXle0 (mul_le_mul_of_nonneg_right hMx0_le (hrn n))
      have hYle : |Yn n ω| ≤ My * sn n := by
        exact le_trans hYle0 (mul_le_mul_of_nonneg_right hMy0_le (hsn n))
      have hprod : |Xn n ω * Yn n ω| ≤ (Mx * My) * (rn n * sn n) := by
        calc
          |Xn n ω * Yn n ω| = |Xn n ω| * |Yn n ω| := abs_mul (Xn n ω) (Yn n ω)
          _ ≤ (Mx * rn n) * (My * sn n) :=
              mul_le_mul hXle hYle (abs_nonneg _)
                (mul_nonneg hMx_nonneg (hrn n))
          _ = (Mx * My) * (rn n * sn n) := by ring
      exact not_lt_of_ge hprod hω
    calc
      μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
  rw [Filter.limsup_le_iff]
  intro y hy
  have hquarter_half : ENNReal.ofReal (ε / 4) < ENNReal.ofReal (ε / 2) := by
    rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
  have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hMx0 hquarter_half)
  have hBevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hMy0 hquarter_half)
  filter_upwards [hAevent, hBevent] with n hAn hBn
  calc
    μ {ω | (Mx * My) * (rn n * sn n) < |Xn n ω * Yn n ω|} = μ (C n) := by
      simp [C]
    _ ≤ μ (A n) + μ (B n) := hpoint n
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hAn hBn
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add]
      · congr 1; ring
      · linarith
      · linarith
    _ < y := hy

/-! ## The Markov primitive: `L²`-envelope ⇒ `O_p`

A deterministic bound on the conditional/unconditional second moment yields the
matching `O_p` rate.  This is the elementary Chebyshev/Markov step, isolated
once so every cross-fit rate proof reuses it instead of re-deriving it inline.
-/

/-- **Markov second-moment ⇒ `O_p`.**  If each `Xₙ` is `μ`-a.e.-measurable and
its second moment is bounded by a deterministic envelope,
`∫⁻ (Xₙ ω)² dμ ≤ Vₙ` with `0 ≤ Vₙ`, then `Xₙ = O_p(√Vₙ)`.

Proof: Markov on `(Xₙ)²` gives `μ{M√Vₙ < |Xₙ|} ≤ μ{M²Vₙ ≤ (Xₙ)²} ≤
(∫⁻ (Xₙ)²)/(M²Vₙ) ≤ 1/M²`; take `M = 1/√ε`. -/
theorem IsBigOp.of_sq_lintegral_le {Vn : ℕ → ℝ}
    (hX : ∀ n, AEMeasurable (Xn n) μ)
    (hVn : ∀ n, 0 ≤ Vn n)
    (hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal ((Xn n ω) ^ 2) ∂μ
        ≤ ENNReal.ofReal (Vn n)) :
    IsBigOp Xn (fun n => Real.sqrt (Vn n)) μ := by
  intro ε hε
  set Mε : ℝ := Real.sqrt (1 / ε) with hMε_def
  have hMε_pos : 0 < Mε := by
    rw [hMε_def]
    exact Real.sqrt_pos.mpr (by positivity)
  have hMε_sq_pos : 0 < Mε ^ 2 := pow_pos hMε_pos 2
  have hMε_sq : Mε ^ 2 = 1 / ε := by
    rw [hMε_def, Real.sq_sqrt]
    positivity
  have hMε_inv_sq : 1 / (Mε ^ 2) = ε := by
    rw [hMε_sq]
    field_simp [hε.ne']
  refine ⟨Mε, ?_⟩
  have hper_n :
      ∀ n,
        μ {ω | Mε * Real.sqrt (Vn n) < |Xn n ω|} ≤ ENNReal.ofReal ε := by
    intro n
    set Y : Ω → ℝ := Xn n with hY_def
    have hY_aemeas : AEMeasurable Y μ := by
      simpa [Y] using hX n
    have hY_sq_aemeas : AEMeasurable (fun ω => ENNReal.ofReal ((Y ω) ^ 2)) μ :=
      (hY_aemeas.pow_const 2).ennreal_ofReal
    by_cases hVzero : Vn n = 0
    · have hInt_zero :
          ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ = 0 := by
        have hb := hbound n
        rw [hVzero, ENNReal.ofReal_zero] at hb
        exact le_antisymm (by simpa [Y] using hb) bot_le
      have hae_zero : (fun ω => ENNReal.ofReal ((Y ω) ^ 2)) =ᵐ[μ] 0 :=
        (MeasureTheory.lintegral_eq_zero_iff' hY_sq_aemeas).mp hInt_zero
      have hnull :
          μ {ω | Mε * Real.sqrt (Vn n) < |Y ω|} = 0 := by
        rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
        filter_upwards [hae_zero] with ω hω
        simp only [not_lt]
        rw [hVzero, Real.sqrt_zero, mul_zero]
        by_contra hpos_not
        have hpos : 0 < |Y ω| := lt_of_not_ge hpos_not
        have hsq_pos : 0 < (Y ω) ^ 2 := sq_pos_iff.mpr (by
          exact abs_pos.mp hpos)
        have hne : ENNReal.ofReal ((Y ω) ^ 2) ≠ 0 :=
          ENNReal.ofReal_ne_zero_iff.mpr hsq_pos
        exact hne hω
      rw [hY_def] at hnull
      rw [show {ω | Mε * Real.sqrt (Vn n) < |Xn n ω|} =
          {ω | Mε * Real.sqrt (Vn n) < |Y ω|} by simp [Y]]
      rw [hnull]
      exact bot_le
    · have hVpos : 0 < Vn n := lt_of_le_of_ne (hVn n) (Ne.symm hVzero)
      have hden_pos : 0 < Mε ^ 2 * Vn n := mul_pos hMε_sq_pos hVpos
      have hden_ne_zero : ENNReal.ofReal (Mε ^ 2 * Vn n) ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact hden_pos
      have hden_ne_top : ENNReal.ofReal (Mε ^ 2 * Vn n) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hsubset :
          {ω | Mε * Real.sqrt (Vn n) < |Y ω|} ⊆
            {ω | ENNReal.ofReal (Mε ^ 2 * Vn n) ≤
              ENNReal.ofReal ((Y ω) ^ 2)} := by
        intro ω hω
        have hsq : Mε ^ 2 * Vn n < (Y ω) ^ 2 := by
          have hω_lt : Mε * Real.sqrt (Vn n) < |Y ω| := hω
          have hsq' : (Mε * Real.sqrt (Vn n)) ^ 2 < |Y ω| ^ 2 :=
            sq_lt_sq'
              (by
                have hleft_nonneg : 0 ≤ Mε * Real.sqrt (Vn n) :=
                  mul_nonneg hMε_pos.le (Real.sqrt_nonneg _)
                linarith [abs_nonneg (Y ω), hω_lt])
              hω_lt
          simpa [mul_pow, Real.sq_sqrt (hVn n), sq_abs, mul_assoc, mul_comm,
            mul_left_comm] using hsq'
        exact ENNReal.ofReal_le_ofReal hsq.le
      have hmarkov := MeasureTheory.meas_ge_le_lintegral_div hY_sq_aemeas
        hden_ne_zero hden_ne_top
      have hdiv_le : ENNReal.ofReal (Vn n) / ENNReal.ofReal (Mε ^ 2 * Vn n)
          ≤ ENNReal.ofReal ε := by
        calc
          ENNReal.ofReal (Vn n) / ENNReal.ofReal (Mε ^ 2 * Vn n)
              = ENNReal.ofReal (Vn n / (Mε ^ 2 * Vn n)) := by
                rw [ENNReal.ofReal_div_of_pos hden_pos]
          _ = ENNReal.ofReal (1 / (Mε ^ 2)) := by
                congr 1
                field_simp [hVpos.ne', hMε_sq_pos.ne']
          _ = ENNReal.ofReal ε := by
                rw [hMε_inv_sq]
          _ ≤ ENNReal.ofReal ε := le_rfl
      rw [hY_def]
      calc
        μ {ω | Mε * Real.sqrt (Vn n) < |Xn n ω|}
            = μ {ω | Mε * Real.sqrt (Vn n) < |Y ω|} := by simp [Y]
        _ ≤ μ {ω | ENNReal.ofReal (Mε ^ 2 * Vn n) ≤ ENNReal.ofReal ((Y ω) ^ 2)} :=
              measure_mono hsubset
        _ ≤ (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ) /
              ENNReal.ofReal (Mε ^ 2 * Vn n) := hmarkov
        _ ≤ ENNReal.ofReal (Vn n) / ENNReal.ofReal (Mε ^ 2 * Vn n) := by
              gcongr
              simpa [Y] using hbound n
        _ ≤ ENNReal.ofReal ε := hdiv_le
  exact Filter.limsup_le_of_le ⟨0, by intro _ _; exact bot_le⟩
    (Eventually.of_forall hper_n)

/-! ## Lemma B — the conditional / cross-fit lift

The deliverable.  Given a per-`n` sub-σ-field `m_A n` (the training σ-field),
an evaluation index set `s n` whose observations are conditionally i.i.d. given
`m_A n` (independent of `m_A n` with i.i.d. product law), and a score
`g n : Ω → X → ℝ` that is `(m_A n ⊗ σ_X)`-measurable (the cross-fit case: a
fixed integrand evaluated at the `m_A n`-measurable nuisance) and lies in
`L²(P)` for each `ω`, the centered scaled fold sum

    Xₙ(ω) = (1/√|s n|) Σ_{i ∈ s n} (g n ω (W i ω) − ∫ g n ω dP)

is `O_p(√Vₙ)` for any deterministic `Vₙ` dominating `∫_Ω ‖g n ω‖²_{L²(P)} dμ`.

Here `∫ g n ω dP = 𝔼[g n (·, W) | m_A n](ω)` is the conditional mean (the eval
fold is independent of `m_A n`), so `Xₙ` is exactly `√|s n|·(ℙₙ g − 𝔼[g|m_A n])`.
The second-moment estimate is `Causalean.Mathlib.iid_centered_sum_sq_lintegral_le`;
the rate then follows from `IsBigOp.of_sq_lintegral_le`. -/
/-- **Cross-fit empirical-increment rate.** For a score that depends on the
sample only through a training σ-algebra (the cross-fitting situation: a fixed
function evaluated at nuisances estimated on the other folds), the centred and
scaled evaluation-fold average is stochastically bounded at the root of any
deterministic sequence dominating the score's mean squared norm — the
empirical-process step that gives cross-fit estimators their rate without
entropy conditions. -/
theorem isBigOp_centered_crossFit_sum
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W : ℕ → Ω → X) (hW_meas : ∀ i, Measurable (W i))
    (s : ℕ → Finset ℕ) (hs_pos : ∀ n, 0 < (s n).card)
    (m_A : ℕ → MeasurableSpace Ω) (hm_A_le : ∀ n, m_A n ≤ mΩ)
    (hindep : ∀ n,
      Indep (m_A n)
        (MeasurableSpace.comap
          (fun ω (i : s n) => W i.val ω) (inferInstance : MeasurableSpace _)) μ)
    (hiid : ∀ n,
      (μ.map (fun ω (i : s n) => W i.val ω)) = Measure.pi (fun _ : s n => P))
    (g : ℕ → Ω → X → ℝ)
    (hg_meas : ∀ n, Measurable[(m_A n).prod mX] (Function.uncurry (g n)))
    (hg_memLp : ∀ n ω, MemLp (g n ω) 2 P)
    {Vn : ℕ → ℝ} (hVn : ∀ n, 0 ≤ Vn n)
    (hVbound : ∀ n,
      ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g n ω) 2 P).toReal ^ 2) ∂μ
        ≤ ENNReal.ofReal (Vn n)) :
    IsBigOp
      (fun n ω => (Real.sqrt ((s n).card : ℝ))⁻¹ *
        ∑ i ∈ s n, (g n ω (W i ω) - ∫ x, g n ω x ∂P))
      (fun n => Real.sqrt (Vn n)) μ := by
  refine IsBigOp.of_sq_lintegral_le ?hX hVn ?hbound
  · intro n
    have hcenter_meas : Measurable
        (fun ω => ∑ i ∈ s n, (g n ω (W i ω) - ∫ x, g n ω x ∂P)) := by
      refine Finset.measurable_sum _ ?_
      intro i hi
      have hfirst : @Measurable Ω Ω mΩ (m_A n) id :=
        measurable_id.mono le_rfl (hm_A_le n)
      have hpair : @Measurable Ω (Ω × X) mΩ ((m_A n).prod mX)
          (fun ω => (ω, W i ω)) :=
        hfirst.prodMk (hW_meas i)
      have hgi : Measurable (fun ω => g n ω (W i ω)) := by
        simpa [Function.uncurry] using (hg_meas n).comp hpair
      have hint_A : Measurable[m_A n] (fun ω => ∫ x, g n ω x ∂P) := by
        letI : MeasurableSpace Ω := m_A n
        have hsm : StronglyMeasurable (Function.uncurry (g n)) :=
          (show Measurable (Function.uncurry (g n)) from hg_meas n).stronglyMeasurable
        exact hsm.integral_prod_right.measurable
      have hint : Measurable (fun ω => ∫ x, g n ω x ∂P) :=
        hint_A.mono (hm_A_le n) le_rfl
      exact hgi.sub hint
    exact (measurable_const.mul hcenter_meas).aemeasurable
  · intro n
    have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
      (s := s n) (hs_pos n) (W := W) (fun i _ => hW_meas i)
      (m_A n) (hm_A_le n) (hindep n) (hiid n)
      (g n) (hg_meas n) (hg_memLp n)
    exact hraw.trans (hVbound n)

/-! ## Lemma A — the unconditional i.i.d. corollary

Special case of the engine with the trivial training σ-field `⊥` and a fixed
integrand `f`.  This is the form the `(ℙₙ − P)φ^bd` term consumes. -/

namespace IIDSample

variable {X : Type*} [MeasurableSpace X] {P : Measure X}

/-- **Centered sample-mean second moment.**  For an i.i.d. sample and a
square-integrable statistic `f`, the centered sample mean over the first `n`
points has second moment bounded by `E_P[f²]/n`:

    ∫⁻ ω, ((ℙₙf)(ω) − ∫ f dP)² dμ ≤ E_P[f²] / n.

Proof: `(1/√n) Σ_{i<n} (f(Zᵢ) − m) = √n (ℙₙf − m)`, so the engine's bound
`∫⁻ (√n (ℙₙf − m))² ≤ E_P[f²]` divides to the claim. -/
theorem sampleMean_sub_sq_lintegral_le
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {f : X → ℝ} (hf_meas : Measurable f) (hf : MemLp f 2 P) {n : ℕ} (hn : 0 < n) :
    ∫⁻ ω, ENNReal.ofReal ((S.sampleMean f n ω - ∫ x, f x ∂P) ^ 2) ∂μ
      ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / n) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiid :
      μ.map (fun ω (i : Finset.range n) => S.Z i.val ω) =
        Measure.pi (fun _ : Finset.range n => P) := by
    have hindep_s : iIndepFun (fun i : Finset.range n => S.Z i) μ := by
      exact S.indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Finset.range n => (S.meas i).aemeasurable)).mp hindep_s
    calc
      μ.map (fun ω (i : Finset.range n) => S.Z i.val ω)
          = Measure.pi (fun i : Finset.range n => μ.map (S.Z i)) := hmap
      _ = Measure.pi (fun _ : Finset.range n => P) := by
          congr with i
          rw [← (S.identDist i).map_eq, S.law]
  have hindep :
      Indep (⊥ : MeasurableSpace Ω)
        (MeasurableSpace.comap
          (fun ω (i : Finset.range n) => S.Z i.val ω) inferInstance) μ := by
    exact ProbabilityTheory.indep_bot_left _
  have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
    (s := Finset.range n) (by simpa [Finset.card_range] using hn) (W := S.Z)
    (fun i _ => S.meas i)
    (⊥ : MeasurableSpace Ω) bot_le hindep hiid
    (fun _ x => f x)
    (by
      change Measurable[(⊥ : MeasurableSpace Ω).prod (inferInstance : MeasurableSpace X)]
        (fun p : Ω × X => f p.2)
      exact hf_meas.comp measurable_snd)
    (fun _ => hf)
  have heLp_sq :
      ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) =
        ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
    have h_eLp := hf.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    rw [h_eLp]
    simp only [ENNReal.toReal_ofNat]
    have hroot_nonneg : 0 ≤ (∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ := by
      exact Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
    rw [ENNReal.toReal_ofReal hroot_nonneg]
    have hsq : ((∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹) ^ 2 =
        ∫ x, f x ^ 2 ∂P := by
      have hint_eq : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) = ∫ x, f x ^ 2 ∂P := by
        congr with x
        norm_num [sq_abs]
      rw [hint_eq]
      rw [show ((∫ x, f x ^ 2 ∂P) ^ (2 : ℝ)⁻¹) ^ 2 =
          ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 by norm_num]
      rw [show ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 =
          ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by
        norm_num [Real.rpow_two]]
      rw [← Real.rpow_mul]
      · norm_num
        exact Real.rpow_one (∫ x, f x ^ 2 ∂P)
      · exact integral_nonneg fun x => sq_nonneg _
    rw [hsq]
  have hscaled_bound :
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ Finset.range n, (f (S.Z i ω) - ∫ x, f x ∂P)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
    have hraw' :
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n,
                ((fun _ x => f x) ω (S.Z i ω) - ∫ x, (fun _ x => f x) ω x ∂P)) ^ 2) ∂μ
          ≤ ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
      calc
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n,
                ((fun _ x => f x) ω (S.Z i ω) - ∫ x, (fun _ x => f x) ω x ∂P)) ^ 2) ∂μ
            ≤ ∫⁻ ω, ENNReal.ofReal ((eLpNorm ((fun _ x => f x) ω) 2 P).toReal ^ 2) ∂μ :=
              hraw
        _ = ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
              simp [heLp_sq]
    simpa [Finset.card_range] using hraw'
  let Z : Ω → ℝ := fun ω =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range n, (f (S.Z i ω) - ∫ x, f x ∂P)
  let D : Ω → ℝ := fun ω => S.sampleMean f n ω - ∫ x, f x ∂P
  have hZ_eq : ∀ ω, Z ω = Real.sqrt (n : ℝ) * D ω := by
    intro ω
    have hsum_sub :
        (∑ i ∈ Finset.range n, (f (S.Z i ω) - ∫ x, f x ∂P)) =
          (∑ i ∈ Finset.range n, f (S.Z i ω)) - (n : ℝ) * (∫ x, f x ∂P) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_range, nsmul_eq_mul]
    dsimp [Z, D, IIDSample.sampleMean]
    rw [hsum_sub]
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
    field_simp [hsqrt_ne, hnR.ne']
    rw [Real.sq_sqrt hnR.le]
  have hD_sq : ∀ ω, D ω ^ 2 = (n : ℝ)⁻¹ * Z ω ^ 2 := by
    intro ω
    rw [hZ_eq ω, mul_pow, Real.sq_sqrt hnR.le]
    field_simp [hnR.ne']
  have hn_inv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnR.le
  calc
    ∫⁻ ω, ENNReal.ofReal ((S.sampleMean f n ω - ∫ x, f x ∂P) ^ 2) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂μ := by rfl
    _ = ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ * Z ω ^ 2) ∂μ := by
          simp_rw [hD_sq]
    _ = ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹) * ENNReal.ofReal (Z ω ^ 2) ∂μ := by
          simp_rw [ENNReal.ofReal_mul hn_inv_nonneg]
    _ = ENNReal.ofReal ((n : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((n : ℝ)⁻¹) *
          ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
          exact mul_le_mul_right (by simpa [Z] using hscaled_bound) _
    _ = ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / n) := by
          rw [← ENNReal.ofReal_mul hn_inv_nonneg]
          congr 1
          field_simp [hnR.ne']

/-- **Chebyshev tail for the centered sample mean.**  For `t > 0`,

    μ{ω | t ≤ |(ℙₙf)(ω) − ∫ f dP|} ≤ E_P[f²] / (n · t²). -/
theorem sampleMean_sub_meas_ge_le
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {f : X → ℝ} (hf_meas : Measurable f) (hf : MemLp f 2 P) {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
      ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / (n * t ^ 2)) := by
  classical
  let D : Ω → ℝ := fun ω => S.sampleMean f n ω - ∫ x, f x ∂P
  have hD_meas : Measurable D := by
    dsimp [D, IIDSample.sampleMean]
    exact (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => hf_meas.comp (S.meas i))).sub measurable_const
  have hD_sq_aemeas : AEMeasurable (fun ω => ENNReal.ofReal ((D ω) ^ 2)) μ :=
    (hD_meas.aemeasurable.pow_const 2).ennreal_ofReal
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht 2
  have ht_sq_ne_zero : ENNReal.ofReal (t ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ht_sq_pos
  have ht_sq_ne_top : ENNReal.ofReal (t ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsubset :
      {ω | t ≤ |D ω|} ⊆
        {ω | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((D ω) ^ 2)} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    have hs : t ^ 2 ≤ (D ω) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_pos ht] using hω
    exact hs
  have hmarkov := MeasureTheory.meas_ge_le_lintegral_div hD_sq_aemeas
    ht_sq_ne_zero ht_sq_ne_top
  have hsecond := sampleMean_sub_sq_lintegral_le S hf_meas hf hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    μ {ω | t ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
        = μ {ω | t ≤ |D ω|} := by rfl
    _ ≤ μ {ω | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((D ω) ^ 2)} :=
          measure_mono hsubset
    _ ≤ (∫⁻ ω, ENNReal.ofReal ((D ω) ^ 2) ∂μ) / ENNReal.ofReal (t ^ 2) :=
          hmarkov
    _ ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / n) / ENNReal.ofReal (t ^ 2) := by
          gcongr
    _ = ENNReal.ofReal (((∫ x, (f x) ^ 2 ∂P) / n) / (t ^ 2)) := by
          rw [ENNReal.ofReal_div_of_pos ht_sq_pos]
    _ = ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / (n * t ^ 2)) := by
          congr 1
          field_simp [hnR.ne', ht.ne']

/-- **Unconditional `O_p` rate (Lemma A).**  The centered sample mean is
`O_p(n^{-1/2} · (E_P[f²])^{1/2})`:

    (ℙₙf − ∫ f dP) = O_p( √(E_P[f²] / n) ).

Feeding the centered statistic `f − ∫ f dP` (whose `E_P[(·)²] = Var_P f`) gives
the sharp `O_p(√(Var_P f / n))` form. -/
theorem sampleMean_sub_isBigOp
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {f : X → ℝ} (hf_meas : Measurable f) (hf : MemLp f 2 P) :
    IsBigOp (fun n ω => S.sampleMean f n ω - ∫ x, f x ∂P)
      (fun n => Real.sqrt ((∫ x, (f x) ^ 2 ∂P) / n)) μ := by
  classical
  let A : ℝ := ∫ x, (f x) ^ 2 ∂P
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x => sq_nonneg _
  intro ε hε
  set Mε : ℝ := Real.sqrt (1 / ε) with hMε_def
  have hMε_pos : 0 < Mε := by
    rw [hMε_def]
    exact Real.sqrt_pos.mpr (by positivity)
  have hMε_sq_pos : 0 < Mε ^ 2 := pow_pos hMε_pos 2
  have hMε_sq : Mε ^ 2 = 1 / ε := by
    rw [hMε_def, Real.sq_sqrt]
    positivity
  have hMε_inv_sq : 1 / (Mε ^ 2) = ε := by
    rw [hMε_sq]
    field_simp [hε.ne']
  refine ⟨Mε, ?_⟩
  have hD_meas : ∀ n, Measurable
      (fun ω => S.sampleMean f n ω - ∫ x, f x ∂P) := by
    intro n
    dsimp [IIDSample.sampleMean]
    exact (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => hf_meas.comp (S.meas i))).sub measurable_const
  have hper_n :
      ∀ᶠ n : ℕ in atTop,
        μ {ω | Mε * Real.sqrt (A / n) <
            |S.sampleMean f n ω - ∫ x, f x ∂P|} ≤ ENNReal.ofReal ε := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    let D : Ω → ℝ := fun ω => S.sampleMean f n ω - ∫ x, f x ∂P
    by_cases hAzero : A = 0
    · have hsecond := sampleMean_sub_sq_lintegral_le S hf_meas hf hn
      have hInt_zero : ∫⁻ ω, ENNReal.ofReal ((D ω) ^ 2) ∂μ = 0 := by
        have hb : ∫⁻ ω, ENNReal.ofReal ((D ω) ^ 2) ∂μ ≤ ENNReal.ofReal 0 := by
          simpa [D, A, hAzero] using hsecond
        rw [ENNReal.ofReal_zero] at hb
        exact le_antisymm hb bot_le
      have hD_sq_aemeas : AEMeasurable (fun ω => ENNReal.ofReal ((D ω) ^ 2)) μ :=
        ((hD_meas n).aemeasurable.pow_const 2).ennreal_ofReal
      have hae_zero : (fun ω => ENNReal.ofReal ((D ω) ^ 2)) =ᵐ[μ] 0 :=
        (MeasureTheory.lintegral_eq_zero_iff' hD_sq_aemeas).mp hInt_zero
      have hnull : μ {ω | Mε * Real.sqrt (A / n) < |D ω|} = 0 := by
        rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
        filter_upwards [hae_zero] with ω hω
        simp only [not_lt]
        rw [hAzero, zero_div, Real.sqrt_zero, mul_zero]
        by_contra hpos_not
        have hpos : 0 < |D ω| := lt_of_not_ge hpos_not
        have hsq_pos : 0 < (D ω) ^ 2 := sq_pos_iff.mpr (abs_pos.mp hpos)
        have hne : ENNReal.ofReal ((D ω) ^ 2) ≠ 0 :=
          ENNReal.ofReal_ne_zero_iff.mpr hsq_pos
        exact hne hω
      rw [show {ω | Mε * Real.sqrt (A / n) <
          |S.sampleMean f n ω - ∫ x, f x ∂P|} =
          {ω | Mε * Real.sqrt (A / n) < |D ω|} by rfl]
      rw [hnull]
      exact bot_le
    · have hApos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hAzero)
      have hrate_pos : 0 < Real.sqrt (A / n) := by
        exact Real.sqrt_pos.mpr (div_pos hApos hnR)
      have ht_pos : 0 < Mε * Real.sqrt (A / n) :=
        mul_pos hMε_pos hrate_pos
      have htail := sampleMean_sub_meas_ge_le S hf_meas hf hn ht_pos
      have hsubset :
          {ω | Mε * Real.sqrt (A / n) < |D ω|} ⊆
            {ω | Mε * Real.sqrt (A / n) ≤ |D ω|} := by
        intro ω hω
        have hlt : Mε * Real.sqrt (A / n) < |D ω| := hω
        exact le_of_lt hlt
      have htail' :
          μ {ω | Mε * Real.sqrt (A / n) < |D ω|}
            ≤ ENNReal.ofReal (A / (n * (Mε * Real.sqrt (A / n)) ^ 2)) := by
        calc
          μ {ω | Mε * Real.sqrt (A / n) < |D ω|}
              ≤ μ {ω | Mε * Real.sqrt (A / n) ≤ |D ω|} := measure_mono hsubset
          _ = μ {ω | Mε * Real.sqrt (A / n) ≤
                |S.sampleMean f n ω - ∫ x, f x ∂P|} := by rfl
          _ ≤ ENNReal.ofReal
                ((∫ x, (f x) ^ 2 ∂P) / (n * (Mε * Real.sqrt (A / n)) ^ 2)) :=
                htail
          _ = ENNReal.ofReal (A / (n * (Mε * Real.sqrt (A / n)) ^ 2)) := by
                rfl
      have hreal :
          A / (n * (Mε * Real.sqrt (A / n)) ^ 2) = 1 / (Mε ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg hA_nonneg hnR.le)]
        field_simp [hApos.ne', hnR.ne', hMε_sq_pos.ne']
      calc
        μ {ω | Mε * Real.sqrt (A / n) <
            |S.sampleMean f n ω - ∫ x, f x ∂P|}
            = μ {ω | Mε * Real.sqrt (A / n) < |D ω|} := by rfl
        _ ≤ ENNReal.ofReal (A / (n * (Mε * Real.sqrt (A / n)) ^ 2)) := htail'
        _ = ENNReal.ofReal (1 / (Mε ^ 2)) := by rw [hreal]
        _ = ENNReal.ofReal ε := by rw [hMε_inv_sq]
        _ ≤ ENNReal.ofReal ε := le_rfl
  exact Filter.limsup_le_of_le ⟨0, by intro _ _; exact bot_le⟩
    (hper_n.mono fun _ h => h)

end IIDSample

end Causalean.Stat
