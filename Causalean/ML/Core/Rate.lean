/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Limit.Convergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Learning-rate abstraction and rate algebra

The causal-free common currency between the method folders (which prove per-method
L²-estimation rates) and `ML/CausalApplication` (which assembles them to discharge DML's
nuisance-rate conditions).

* `AchievesL2Rate ĥ h⋆ P rₙ μ` — every L² seminorm of the estimation error is
  finite, and its real-number conversion is `O_p(rₙ)` under the experiment law.
* generic probabilistic stochastic-order facts: an `o_p(rₙ)` with `rₙ ≤ 1` is
  `o_p(1)`; a product of two `o_p(n^{-1/4})` is `o_p(n^{-1/2})`; and an
  `O_p(n^{-1/2})` rate is `o_p(n^{-1/4})` (turning a method's root-n `IsBigOp`
  into the `o_p(n^{-1/4})` the DML side consumes).
-/

namespace Causalean.ML

open MeasureTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Xn Yn : ℕ → Ω → ℝ}

/-- Rate weakening: an `o_p(rn)` sequence with `rn ≤ 1` is `o_p(1)`. -/
theorem isLittleOp_one_of_le_one {rn : ℕ → ℝ} (hr : ∀ n, rn n ≤ 1)
    (h : IsLittleOp Xn rn μ) : IsLittleOp Xn (fun _ => 1) μ := by
  intro ε hε
  have hlim : Tendsto (fun n => μ {ω | ε * rn n < |Xn n ω|}) atTop (𝓝 0) := h ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hmul : ε * rn n ≤ ε * 1 :=
    mul_le_mul_of_nonneg_left (hr n) (le_of_lt hε)
  exact lt_of_le_of_lt hmul (by simpa using hω)

/-- **The `n^{-1/4}` product rule.** The product of two `o_p(n^{-1/4})` sequences
is `o_p(n^{-1/2})` — the DML product-rate condition from per-nuisance `n^{-1/4}`
rates. -/
theorem isLittleOp_mul_quarter
    (hX : IsLittleOp Xn (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) μ)
    (hY : IsLittleOp Yn (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) μ) :
    IsLittleOp (fun n ω => Xn n ω * Yn n ω) (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
  intro ε hε
  let δ : ℝ := Real.sqrt ε
  have hδpos : 0 < δ := Real.sqrt_pos.2 hε
  have hδsq : δ * δ = ε := by
    simpa [δ, pow_two] using Real.sq_sqrt (le_of_lt hε)
  let A : ℕ → Set Ω := fun n => {ω | δ * (n : ℝ) ^ (-(1 / 4 : ℝ)) < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | δ * (n : ℝ) ^ (-(1 / 4 : ℝ)) < |Yn n ω|}
  let C : ℕ → Set Ω :=
    fun n => {ω | ε * (n : ℝ) ^ (-(1 / 2 : ℝ)) < |Xn n ω * Yn n ω|}
  have hAt : Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
    simpa [A, δ] using hX δ hδpos
  have hBt : Tendsto (fun n => μ (B n)) atTop (𝓝 0) := by
    simpa [B, δ] using hY δ hδpos
  have hsum : Tendsto (fun n => μ (A n) + μ (B n)) atTop (𝓝 0) := by
    simpa using hAt.add hBt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrate_nonneg : 0 ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hrate_prod :
      (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 4 : ℝ)) =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    norm_num
  have hpoint : μ (C n) ≤ μ (A n) + μ (B n) := by
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ δ * (n : ℝ) ^ (-(1 / 4 : ℝ)) < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl hx)
      have hnotB : ¬ δ * (n : ℝ) ^ (-(1 / 4 : ℝ)) < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr hy)
      have hXle : |Xn n ω| ≤ δ * (n : ℝ) ^ (-(1 / 4 : ℝ)) := le_of_not_gt hnotA
      have hYle : |Yn n ω| ≤ δ * (n : ℝ) ^ (-(1 / 4 : ℝ)) := le_of_not_gt hnotB
      have hbound_nonneg : 0 ≤ δ * (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_nonneg (le_of_lt hδpos) hrate_nonneg
      have hprod : |Xn n ω * Yn n ω| ≤ ε * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        calc
          |Xn n ω * Yn n ω| = |Xn n ω| * |Yn n ω| := abs_mul (Xn n ω) (Yn n ω)
          _ ≤ (δ * (n : ℝ) ^ (-(1 / 4 : ℝ))) *
              (δ * (n : ℝ) ^ (-(1 / 4 : ℝ))) :=
            mul_le_mul hXle hYle (abs_nonneg _) hbound_nonneg
          _ = ε * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [mul_mul_mul_comm, hδsq, hrate_prod]
      exact not_lt_of_ge hprod hω
    calc
      μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
  simpa [C] using hpoint

/-- An `O_p(n^{-1/2})` (root-n) rate is `o_p(n^{-1/4})`: a method's root-n
estimation rate clears the DML `o_p(n^{-1/4})` bar. -/
theorem isLittleOp_quarter_of_isBigOp_sqrt
    (h : IsBigOp Xn (fun n => (Real.sqrt (n : ℝ))⁻¹) μ) :
    IsLittleOp Xn (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · filter_upwards with n
    simp [hδtop]
  have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
  let α : ℝ := δ.toReal / 2
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  rcases h α hαpos with ⟨M0, hM0⟩
  let M : ℝ := max M0 1
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
  have hM0le : M0 ≤ M := by
    dsimp [M]
    exact le_max_left M0 1
  let A : ℕ → Set Ω := fun n => {ω | ε * (n : ℝ) ^ (-(1 / 4 : ℝ)) < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | M * (Real.sqrt (n : ℝ))⁻¹ < |Xn n ω|}
  have hlimB : Filter.limsup (fun n => μ (B n)) atTop ≤ ENNReal.ofReal α := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
    intro n
    apply measure_mono
    intro ω hω
    dsimp [B] at hω ⊢
    have hrate_nonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hM0le hrate_nonneg) hω
  have hα_lt_delta : ENNReal.ofReal α < δ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hδpos]
    · exact hδtop
  have hBevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimB hα_lt_delta)
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      M * (Real.sqrt (n : ℝ))⁻¹ ≤ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have ht : Tendsto (fun n : ℕ => (M / ε) * (n : ℝ) ^ (-(1 / 4 : ℝ)))
        atTop (𝓝 0) := by
      have hp : Tendsto (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
        exact tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 / 4 : ℝ))
      simpa using (Tendsto.const_mul (M / ε) (hp.comp tendsto_natCast_atTop_atTop))
    have hevent_abs : ∀ᶠ n : ℕ in atTop,
        |(M / ε) * (n : ℝ) ^ (-(1 / 4 : ℝ))| < 1 := by
      have hnear := (Metric.tendsto_nhds.mp ht) 1 (by norm_num : (0 : ℝ) < (1 : ℝ))
      simpa [Real.dist_eq, abs_mul, abs_div] using hnear
    filter_upwards [hevent_abs, eventually_ge_atTop 1] with n hnabs hn_ge
    have hnsmall : (M / ε) * (n : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := (abs_lt.mp hnabs).2
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn_ge
    let q : ℝ := (n : ℝ) ^ (-(1 / 4 : ℝ))
    have hqpos : 0 < q := by
      dsimp [q]
      exact Real.rpow_pos_of_pos hnpos _
    have hinv_eq : (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_neg (le_of_lt hnpos)]
    have hpow_add : q * q = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp [q]
      rw [← Real.rpow_add hnpos]
      congr 1
      norm_num
    have hmul : (M / ε * q) * (ε * q) ≤ 1 * (ε * q) := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hnsmall) (le_of_lt (mul_pos hε hqpos))
    have hleft : (M / ε * q) * (ε * q) = M * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← hpow_add]
      field_simp [hε.ne']
    calc
      M * (Real.sqrt (n : ℝ))⁻¹ = M * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hinv_eq]
      _ = (M / ε * q) * (ε * q) := by rw [hleft]
      _ ≤ 1 * (ε * q) := hmul
      _ = ε * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by simp [q]
  filter_upwards [hBevent, hthreshold] with n hBn hthr
  have hsubset : A n ⊆ B n := by
    intro ω hω
    dsimp [A, B] at hω ⊢
    exact lt_of_le_of_lt hthr hω
  have heq : {ω | ε * (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) n < |Xn n ω|} = A n := by
    ext ω
    simp [A]
  rw [heq]
  exact le_of_lt (lt_of_le_of_lt (measure_mono hsubset) hBn)

/-- The L² estimation error has a finite seminorm at every sample size and
experiment outcome, and that finite seminorm is stochastically bounded at the
supplied rate under the experiment law.  The L² seminorm is computed using the
covariate marginal of the joint law, so the real-valued stochastic-order claim
never comes from converting an infinite extended norm to zero. -/
def AchievesL2Rate {X : Type*} [MeasurableSpace X]
    (hhat : ℕ → Ω → (X → ℝ)) (hstar : X → ℝ) (P : Measure (X × ℝ))
    (rn : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  (∀ n ω, eLpNorm (fun x => hhat n ω x - hstar x) 2 (P.map Prod.fst) ≠ ⊤) ∧
    IsBigOp
      (fun n ω => (eLpNorm (fun x => hhat n ω x - hstar x) 2 (P.map Prod.fst)).toReal)
      rn μ

end Causalean.ML
