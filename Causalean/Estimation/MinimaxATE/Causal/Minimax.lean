/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.MinimaxATE.Causal.Bridge
import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.LowerBound
import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.LowerBound

/-!
# Causal re-centering of the cell-varying minimax converses

This file re-centers the VaryingCenterCase1 and VaryingCenterCase2 minimax lower
bounds onto the genuine causal estimand `causalATE = E[Y(1) - Y(0)]` of the
concrete backdoor potential outcome system.  The observed-data contrast `ate g`
remains the internal computational handle: the minimax model and Le Cam machinery
live below the causal layer, so `nMiss`/`minimaxMiss` themselves cannot be
re-centered without a circular import.  The bridge `causalATE_eq_ate` identifies
the two targets under validity and strict overlap.

The file defines the causal-centered risk functional `minimaxMissCausal`, a
causal two-point witness wrapper `TwoPointWitnessCausal`, and the reusable Le Cam
lemmas `twoPointWitnessCausal_lower_bound` and `twoPointWitnessCausal_quarter`.
It then proves the causal-centered cell-varying lower bounds
`minimax_lower_bound_var_causal` for Case 1 and
`minimax_lower_bound_var2_causal` for Case 2, adding the strict-overlap
side conditions needed to invoke `causalATE_eq_ate` on the null and perturbed
witnesses.
-/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open Causalean.Estimation.MinimaxATE.Causal
open scoped ENNReal BigOperators

variable {C : Type} [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C]

/-! ## Causal-centered miss probability -/

/-- **Causal-centered minimax miss probability.**  This mirrors `minimaxMiss`, but
centers each DGP's miss event at the potential-outcome estimand `causalATE m g`
of the concrete backdoor system. -/
noncomputable def minimaxMissCausal (mhat : C → ℝ) (ghat : Bool → C → ℝ)
    (εg εm : ℝ) (n : ℕ) (est : (Fin n → Obs C) → ℝ) (s : ℝ) : ℝ :=
  ⨆ p : InClassDGP mhat ghat εg εm,
    (productLaw p.2.valid n).real {x | s ≤ |est x - causalATE (C := C) p.1.1 p.1.2|}

/-- Each in-class causal-centered miss probability is bounded above by `1`. -/
theorem bddAbove_nMissCausal_range (mhat : C → ℝ) (ghat : Bool → C → ℝ)
    (εg εm : ℝ) (n : ℕ) (est : (Fin n → Obs C) → ℝ) (s : ℝ) :
    BddAbove (Set.range fun p : InClassDGP mhat ghat εg εm =>
      (productLaw p.2.valid n).real {x | s ≤ |est x - causalATE (C := C) p.1.1 p.1.2|}) := by
  refine ⟨1, ?_⟩
  rintro y ⟨p, rfl⟩
  calc
    (productLaw p.2.valid n).real
        {x | s ≤ |est x - causalATE (C := C) p.1.1 p.1.2|}
      ≤ (productLaw p.2.valid n).real Set.univ :=
        measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := by rw [probReal_univ]

/-- A specific in-class DGP's causal-centered miss probability is dominated by
the causal-centered minimax miss. -/
theorem nMissCausal_le_minimaxMissCausal {mhat : C → ℝ} {ghat : Bool → C → ℝ}
    {εg εm : ℝ} {n : ℕ} {est : (Fin n → Obs C) → ℝ} {s : ℝ}
    (p : InClassDGP mhat ghat εg εm) :
    (productLaw p.2.valid n).real
        {x | s ≤ |est x - causalATE (C := C) p.1.1 p.1.2|}
      ≤ minimaxMissCausal mhat ghat εg εm n est s :=
  le_ciSup (bddAbove_nMissCausal_range mhat ghat εg εm n est s) p

/-! ## Causal two-point reduction -/

/-- Two-point Le Cam witness whose realizability target is `minimaxMissCausal`. -/
structure TwoPointWitnessCausal (C : Type) [Fintype C] [Nonempty C] [MeasurableSpace C]
    [MeasurableSingletonClass C]
    (n : ℕ) (mhat : C → ℝ) (ghat : Bool → C → ℝ) (εg εm : ℝ) where
  s : ℝ
  c : ℝ
  Q : Bool → Measure (Fin n → Obs C)
  prob : ∀ j, IsProbabilityMeasure (Q j)
  θ : Bool → ℝ
  sep : 2 * s ≤ |θ true - θ false|
  tvBound : tvDist (Q false) (Q true) ≤ c
  dominated : ∀ (est : (Fin n → Obs C) → ℝ) (j : Bool),
    (Q j).real {x | s ≤ |est x - θ j|} ≤ minimaxMissCausal mhat ghat εg εm n est s

variable {n : ℕ} {mhat : C → ℝ} {ghat : Bool → C → ℝ} {εg εm : ℝ}

/-- Le Cam lower bound for a causal-centered two-point witness. -/
theorem twoPointWitnessCausal_lower_bound
    (W : TwoPointWitnessCausal C n mhat ghat εg εm)
    {est : (Fin n → Obs C) → ℝ} (hest : Measurable est) :
    (1 - W.c) / 2 ≤ minimaxMissCausal mhat ghat εg εm n est W.s := by
  haveI := W.prob false
  haveI := W.prob true
  have hsep : 2 * W.s ≤ |W.θ false - W.θ true| := by
    rw [abs_sub_comm]
    exact W.sep
  have h := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := W.Q false) (P₁ := W.Q true) hest hsep W.tvBound
  refine h.trans ?_
  rw [max_le_iff]
  exact ⟨W.dominated est false, W.dominated est true⟩

/-- A causal-centered witness with `c ≤ 1/2` yields a `1/4` minimax miss lower bound. -/
theorem twoPointWitnessCausal_quarter
    (W : TwoPointWitnessCausal C n mhat ghat εg εm) (hc : W.c ≤ 1 / 2)
    {est : (Fin n → Obs C) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMissCausal mhat ghat εg εm n est W.s := by
  refine le_trans ?_ (twoPointWitnessCausal_lower_bound W hest)
  linarith

namespace VarConstr

variable {K : ℕ}

/-! ## Strict overlap for the VaryingCenterCase1 witnesses -/

/-- The null VaryingCenterCase1 witness has strict propensity overlap. -/
theorem mhatV_strictOverlap (P : VarConstr K) [NeZero K] :
    ∀ x : Fin K × Bool, P.mhatV x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro x
  exact ⟨P.hm₀0 x.1, P.hm₀1 x.1⟩

/-- The perturbed VaryingCenterCase1 witness has strict propensity overlap.

The lower bound is immediate from `hm₀0` and `denomV_pos`.  The current
`VarConstr` fields give only `m₀ j * (1 + β / g₁ j) ≤ 1` in the worst branch, so
the strict upper bound needs a strict version of `hmU` (or an equivalent
non-boundary condition). -/
theorem mPertV_strictOverlap (P : VarConstr K) [NeZero K]
    (hmU_strict : ∀ j, P.m₀ j * (1 + P.β / P.g₁ j) < 1) (lam : Fin K → Bool) :
    ∀ x : Fin K × Bool, P.mPertV lam x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro x
  constructor
  · simp only [mPertV]
    exact mul_pos (P.hm₀0 x.1) (P.denomV_pos lam x)
  · simp only [mPertV]
    have hr := P.ratio_nonneg x.1
    have hr1 := P.ratio_lt_one x.1
    have hm0 := P.hm₀0 x.1
    have hm1 := P.hm₀1 x.1
    have hstrict := hmU_strict x.1
    rcases Δ_mem lam x with h | h
    · rw [h]
      nlinarith
    · rw [h]
      nlinarith

/-! ## Domination for the causal-centered minimax miss -/

/-- An in-class DGP's causal-centered miss probability is dominated by
`minimaxMissCausal`. -/
theorem realV_le_minimaxMissCausal (P : VarConstr K) {n : ℕ} [NeZero K]
    {εg εm : ℝ} {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
    (hin : InClass (P.mhatV (K := K)) P.ghatV εg εm m g)
    (est : (Fin n → Obs (Fin K × Bool)) → ℝ) (s : ℝ) :
    (productLaw hin.valid n).real {x | s ≤ |est x - causalATE (C := Fin K × Bool) m g|}
      ≤ minimaxMissCausal P.mhatV P.ghatV εg εm n est s := by
  simpa using
    nMissCausal_le_minimaxMissCausal
      (⟨(m, g), hin⟩ : InClassDGP (P.mhatV (K := K)) P.ghatV εg εm)
      (est := est) (s := s)

/-! ## Causal-centered VaryingCenterCase1 lower bound -/

/-- **Causal-centered structure-agnostic minimax lower bound (Case 1).**
For the outcome-dominant cell-varying construction, strict perturbed-propensity
overlap lets the observed-data Case-1 lower bound be re-centered onto the genuine
causal estimand, so every measurable estimator has causal-centered miss
probability at least `1/4` at half of the displayed Case-1 ATE separation.

The proof uses the same two-point witness as `minimax_lower_bound_var` and
transfers the null and perturbation miss events through `causalATE_eq_ate`. -/
theorem minimax_lower_bound_var_causal (P : VarConstr K) {n : ℕ} [NeZero K]
    {εg εm : ℝ}
    (hm : ∀ j, (P.m₀ j * (P.β / P.g₁ j)) ^ 2 ≤ εm)
    (hg : ∀ j, P.g₁ j ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ j - P.β) ^ 2 ≤ εg)
    (hmU_strict : ∀ j, P.m₀ j * (1 + P.β / P.g₁ j) < 1)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hΓsum : ∑ j, P.ΓV j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV j / (K : ℝ)) ^ 2 ≤ Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMissCausal P.mhatV P.ghatV εg εm n est
      ((Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β * (P.α + P.β))
        * (∑ j : Fin K, P.g₁ j / (P.g₁ j ^ 2 - P.β ^ 2)) / 2) := by
  set gap := (Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β * (P.α + P.β))
    * ∑ j : Fin K, P.g₁ j / (P.g₁ j ^ 2 - P.β ^ 2) with hgap
  have hgap0 : 0 ≤ gap := by
    have h := P.ate_gap_nonneg (fun _ => true)
    rwa [P.ate_gapV (fun _ => true)] at h
  set s := gap / 2 with hs
  set θ0 := ate (P.ghatV (K := K)) with hθ0
  let W : TwoPointWitnessCausal (Fin K × Bool) n P.mhatV P.ghatV εg εm :=
    { s := s
      c := 1 / 2
      Q := fun j => cond j (QtrueV P n) (QfalseV P n)
      prob := by
        intro j
        cases j
        · exact QfalseV_isProb P n
        · exact QtrueV_isProb P n
      θ := fun j => cond j (θ0 + gap) θ0
      sep := by
        change 2 * s ≤ |(θ0 + gap) - θ0|
        rw [add_sub_cancel_left, abs_of_nonneg hgap0, hs]
        linarith
      tvBound := by simpa using P.tvDist_QfalseV_QtrueV_le_half (n := n) hΓsum hreg
      dominated := by
        intro est' j
        cases j
        · change (QfalseV P n).real {x | s ≤ |est' x - θ0|}
              ≤ minimaxMissCausal P.mhatV P.ghatV εg εm n est' s
          have hb := P.realV_le_minimaxMissCausal (n := n)
            (inClass_nullV P hεg hεm) est' s
          have hbridge :
              causalATE (P.mhatV (K := K)) P.ghatV = ate P.ghatV :=
            causalATE_eq_ate (P.validDGP_hatV (K := K)) (P.mhatV_strictOverlap (K := K))
          rw [hbridge, ← hθ0] at hb
          exact hb
        · change (QtrueV P n).real {x | s ≤ |est' x - (θ0 + gap)|}
              ≤ minimaxMissCausal P.mhatV P.ghatV εg εm n est' s
          haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertV P n lam) :=
            fun lam => QpertV_isProb P n lam
          unfold QtrueV
          refine mixtureReal_le (signWeight K) (signWeight_sum K)
            (fun lam => QpertV P n lam) _ _ ?_
          intro lam
          have hb := P.realV_le_minimaxMissCausal (n := n) (P.inClassV hm hg hεg lam) est' s
          have hkey : ate (P.gPertV lam) = θ0 + gap := by
            have := P.ate_gapV lam
            rw [hθ0, hgap]
            linarith [this]
          have hbridge :
              causalATE (P.mPertV lam) (P.gPertV lam) = ate (P.gPertV lam) :=
            causalATE_eq_ate (P.validDGP_pertV lam)
              (P.mPertV_strictOverlap hmU_strict lam)
          rw [hbridge, hkey] at hb
          exact hb }
  exact twoPointWitnessCausal_quarter W (le_refl _) hest

end VarConstr

namespace VarConstr2

variable {K : ℕ}

/-! ## Strict overlap for the VaryingCenterCase2 witnesses -/

/-- The null VaryingCenterCase2 witness has strict propensity overlap. -/
theorem mhat2_strictOverlap (P : VarConstr2 K) [NeZero K] :
    ∀ x : Fin K × Bool, P.mhat2 x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro x
  exact ⟨P.hm₀0 x.1, P.hm₀1 x.1⟩

/-- The perturbed VaryingCenterCase2 witness has strict propensity overlap.

The Case-2 construction writes the perturbed propensity as `m₀ j * (1 + κ j * Δ)`.
Strict lower overlap in the negative-sign branch needs `κ j < 1`, while strict
upper overlap in the positive-sign branch needs a strict version of the Case-2
upper-bound field. -/
theorem mPert2_strictOverlap (P : VarConstr2 K) [NeZero K]
    (hκ_strict : ∀ j, P.κ j < 1)
    (hmU_strict : ∀ j, P.m₀ j * (1 + P.κ j) < 1) (lam : Fin K → Bool) :
    ∀ x : Fin K × Bool, P.mPert2 lam x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro x
  constructor
  · rw [P.mPert2_eq lam x]
    have hm0 := P.hm₀0 x.1
    have hκ0 := P.κ_nonneg x.1
    have hκ1 := hκ_strict x.1
    rcases Δ_mem lam x with h | h
    · rw [h]; nlinarith
    · rw [h]; nlinarith
  · rw [P.mPert2_eq lam x]
    have hm1 := P.hm₀1 x.1
    have hκ0 := P.κ_nonneg x.1
    have hκ1 := hκ_strict x.1
    have hstrict := hmU_strict x.1
    rcases Δ_mem lam x with h | h
    · rw [h]; simpa using hstrict
    · rw [h]; nlinarith

/-! ## Domination for the causal-centered Case-2 minimax miss -/

/-- An in-class Case-2 DGP's causal-centered miss probability is dominated by
`minimaxMissCausal`. -/
theorem real2_le_minimaxMissCausal (P : VarConstr2 K) {n : ℕ} [NeZero K]
    {εg εm : ℝ} {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
    (hin : InClass (P.mhat2 (K := K)) P.ghat2 εg εm m g)
    (est : (Fin n → Obs (Fin K × Bool)) → ℝ) (s : ℝ) :
    (productLaw hin.valid n).real {x | s ≤ |est x - causalATE (C := Fin K × Bool) m g|}
      ≤ minimaxMissCausal P.mhat2 P.ghat2 εg εm n est s := by
  simpa using
    nMissCausal_le_minimaxMissCausal
      (⟨(m, g), hin⟩ : InClassDGP (P.mhat2 (K := K)) P.ghat2 εg εm)
      (est := est) (s := s)

/-! ## Causal-centered VaryingCenterCase2 lower bound -/

/-- **Causal-centered structure-agnostic minimax lower bound (Case 2).**
For the propensity-dominant cell-varying construction, a strictly positive
treated-arm bump and strict perturbed-propensity overlap imply that every
measurable estimator has causal-centered miss probability at least `1/4` at half
of the displayed strictly positive ATE separation.

This is the causal recentering of `minimax_lower_bound_var2`; it covers the
Case-2 regime left open by the Case-1 theorem `minimax_lower_bound_var_causal`. -/
theorem minimax_lower_bound_var2_causal (P : VarConstr2 K) {n : ℕ} [NeZero K]
    {εg εm : ℝ}
    (hβpos : 0 < P.β)
    (hm : ∀ j, (P.m₀ j * P.κ j) ^ 2 ≤ εm)
    (hg : ∀ j, P.β ^ 2 * (P.α * P.g₁ j + 1) ^ 2
        / (1 - P.β / P.g₁ j - P.α * P.β) ^ 2 ≤ εg)
    (hκ_strict : ∀ j, P.κ j < 1)
    (hmU_strict : ∀ j, P.m₀ j * (1 + P.κ j) < 1)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hΓsum : ∑ j, P.ΓV2 j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV2 j / (K : ℝ)) ^ 2 ≤ Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMissCausal P.mhat2 P.ghat2 εg εm n est
      ((Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β)
        * (∑ j : Fin K, P.g₁ j * (P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β)
            / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2)) / 2) := by
  set gap := (Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β)
    * ∑ j : Fin K, P.g₁ j * (P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β)
        / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2) with hgap
  have hgap_pos : 0 < gap := by
    have hcard : 0 < (Fintype.card (Fin K × Bool) : ℝ)⁻¹ := by
      have hcard_nat : 0 < Fintype.card (Fin K × Bool) := Fintype.card_pos
      exact inv_pos.mpr (by exact_mod_cast hcard_nat)
    have h2β : 0 < 2 * P.β := by positivity
    have hsum_pos :
        0 < ∑ j : Fin K,
          P.g₁ j * (P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β)
            / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2) := by
      apply Finset.sum_pos
      · intro j _
        have hg1 := P.hg₁0 j
        have hE := P.denomE_pos j
        have hab := P.alphabeta_le_one j
        have hinner :
            0 < P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β := by
          have hnonneg : 0 ≤ P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) := by
            apply mul_nonneg (mul_nonneg P.hα (sq_nonneg _))
            linarith
          linarith
        exact div_pos (mul_pos hg1 hinner) hE
      · exact Finset.univ_nonempty
    rw [hgap]
    exact mul_pos (mul_pos hcard h2β) hsum_pos
  set s := gap / 2 with hs
  set θ0 := ate (P.ghat2 (K := K)) with hθ0
  let W : TwoPointWitnessCausal (Fin K × Bool) n P.mhat2 P.ghat2 εg εm :=
    { s := s
      c := 1 / 2
      Q := fun j => cond j (Qtrue2 P n) (Qfalse2 P n)
      prob := by
        intro j
        cases j
        · exact Qfalse2_isProb P n
        · exact Qtrue2_isProb P n
      θ := fun j => cond j (θ0 + gap) θ0
      sep := by
        change 2 * s ≤ |(θ0 + gap) - θ0|
        rw [add_sub_cancel_left, abs_of_pos hgap_pos, hs]
        linarith
      tvBound := by simpa using P.tvDist_Qfalse2_Qtrue2_le_half (n := n) hΓsum hreg
      dominated := by
        intro est' j
        cases j
        · change (Qfalse2 P n).real {x | s ≤ |est' x - θ0|}
              ≤ minimaxMissCausal P.mhat2 P.ghat2 εg εm n est' s
          have hb := P.real2_le_minimaxMissCausal (n := n)
            (inClass_null2 P hεg hεm) est' s
          have hbridge :
              causalATE (P.mhat2 (K := K)) P.ghat2 = ate P.ghat2 :=
            causalATE_eq_ate (P.validDGP_hat2 (K := K)) (P.mhat2_strictOverlap (K := K))
          rw [hbridge, ← hθ0] at hb
          exact hb
        · change (Qtrue2 P n).real {x | s ≤ |est' x - (θ0 + gap)|}
              ≤ minimaxMissCausal P.mhat2 P.ghat2 εg εm n est' s
          haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert2 P n lam) :=
            fun lam => Qpert2_isProb P n lam
          unfold Qtrue2
          refine mixtureReal_le (signWeight K) (signWeight_sum K)
            (fun lam => Qpert2 P n lam) _ _ ?_
          intro lam
          have hb := P.real2_le_minimaxMissCausal (n := n)
            (P.inClass2 hm hg hεg lam) est' s
          have hkey : ate (P.gPert2 lam) = θ0 + gap := by
            have := P.ate_gap2 lam
            rw [hθ0, hgap]
            linarith [this]
          have hbridge :
              causalATE (P.mPert2 lam) (P.gPert2 lam) = ate (P.gPert2 lam) :=
            causalATE_eq_ate (P.validDGP_pert2 lam)
              (P.mPert2_strictOverlap hκ_strict hmU_strict lam)
          rw [hbridge, hkey] at hb
          exact hb }
  exact twoPointWitnessCausal_quarter W (le_refl _) hest

end VarConstr2

end Causalean.Estimation.MinimaxATE
