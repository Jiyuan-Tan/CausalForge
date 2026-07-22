/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: assembly (second / propensity-dominant construction)

The Case-2 analogue of `VaryingCenterCase1/LowerBound.lean`.  It assembles the propensity-dominant
construction (`VaryingCenterCase2/Construction`/`Gap`/`Membership`/`ChiSqOverlap`) into a
`TwoPointWitness` and discharges the χ² indistinguishability via the **non-uniform**
`ingster_bound_general` (per-pair coefficient `d j = Γⱼ/K`), yielding a minimax
lower bound around the same cell-varying nuisance center, but valid in the regime
`εm > εg` (where `VaryingCenterCase1/LowerBound.lean`'s construction degrades).

The capstone `minimax_lower_bound_var2` shows that, with the
propensity-dominant per-pair budgets met and the regularity conditions
`Σⱼ Γⱼ/K ≤ 1` and `(n²/2) Σⱼ (Γⱼ/K)² ≤ log 2`, every measurable estimator misses the
true ATE by `s = ½(ate gλ − ate ĝ)` with probability `≥ 1/4` somewhere in the class.
Together with `minimax_lower_bound_var` (Case 1), this establishes the
full product rate `√(εg·εm)` in **both** regimes.
-/

import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Membership
import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.ChiSqOverlap
import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Ingster
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore
import Causalean.Estimation.MinimaxATE.Reduction.Witness
import Causalean.Stat.Minimax.Mixture

/-! # Propensity-Dominant Lower Bound

This file assembles the second cell-varying perturbation family into a two-point
testing witness for the structure-agnostic average treatment effect minimax lower
bound.  Under the stated per-cell budgets and chi-squared regularity conditions, it
shows that every estimator has nontrivial miss probability at the induced separation.
-/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

namespace VarConstr2

/-- The paired-cell covariate is nonempty whenever `K ≠ 0`. -/
instance instNonemptyFinBoolProd {K : ℕ} [NeZero K] : Nonempty (Fin K × Bool) :=
  ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩, true)⟩

variable {K : ℕ}

/-- The null estimate is itself in the class (zero nuisance error). -/
theorem inClass_null2 (P : VarConstr2 K) {εg εm : ℝ} (hεg : 0 ≤ εg) (hεm : 0 ≤ εm) :
    InClass (P.mhat2 (K := K)) P.ghat2 εg εm P.mhat2 P.ghat2 where
  valid := P.validDGP_hat2
  err_g d := by rw [l2sq_self]; exact hεg
  err_m := by rw [l2sq_self]; exact hεm

/-- The null `n`-sample law `P̂^⊗n`. -/
noncomputable def Qfalse2 (P : VarConstr2 K) (n : ℕ) [NeZero K] :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (P.validDGP_hat2 (K := K)) n

/-- The perturbed `n`-sample law `Qλ^⊗n`. -/
noncomputable def Qpert2 (P : VarConstr2 K) (n : ℕ) [NeZero K] (lam : Fin K → Bool) :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (P.validDGP_pert2 lam) n

/-- The alternative `n`-sample law: the uniform Rademacher mixture of the perturbed laws. -/
noncomputable def Qtrue2 (P : VarConstr2 K) (n : ℕ) [NeZero K] :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  mixture (signWeight K) (fun lam => Qpert2 P n lam)

/-- The null sample law is a probability measure. -/
theorem Qfalse2_isProb (P : VarConstr2 K) (n : ℕ) [NeZero K] :
    IsProbabilityMeasure (Qfalse2 P n) := by unfold Qfalse2; infer_instance

/-- Each perturbed sample law is a probability measure. -/
theorem Qpert2_isProb (P : VarConstr2 K) (n : ℕ) [NeZero K] (lam : Fin K → Bool) :
    IsProbabilityMeasure (Qpert2 P n lam) := by unfold Qpert2; infer_instance

/-- The Rademacher mixture of perturbed sample laws is a probability measure. -/
theorem Qtrue2_isProb (P : VarConstr2 K) (n : ℕ) [NeZero K] :
    IsProbabilityMeasure (Qtrue2 P n) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert2 P n lam) :=
    fun lam => Qpert2_isProb P n lam
  unfold Qtrue2
  exact mixture_isProbabilityMeasure _ (signWeight_sum K) _

/-- An in-class DGP's miss probability at its own ATE is dominated by the minimax miss. -/
theorem real2_le_minimaxMiss (P : VarConstr2 K) {n : ℕ} [NeZero K] {εg εm : ℝ}
    {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
    (hin : InClass (P.mhat2 (K := K)) P.ghat2 εg εm m g)
    (est : (Fin n → Obs (Fin K × Bool)) → ℝ) (s : ℝ) :
    (productLaw hin.valid n).real {x | s ≤ |est x - ate g|}
      ≤ minimaxMiss P.mhat2 P.ghat2 εg εm n est s := by
  simpa [nMiss] using
    nMiss_le_minimaxMiss (⟨(m, g), hin⟩ : InClassDGP (P.mhat2 (K := K)) P.ghat2 εg εm)
      (est := est) (s := s)

/-- The null `n`-sample law charges every point. -/
theorem Qfalse2_singleton_ne_zero (P : VarConstr2 K) {n : ℕ} [NeZero K]
    (ω : Fin n → Obs (Fin K × Bool)) : Qfalse2 P n {ω} ≠ 0 := by
  have hpos : 0 < (Qfalse2 P n).real {ω} := by
    rw [Qfalse2, productLaw_real_singleton]
    apply Finset.prod_pos
    intro i _
    have hC : (0 : ℝ) < (Fintype.card (Fin K × Bool) : ℝ) := by
      have := Fintype.card_pos (α := Fin K × Bool); exact_mod_cast this
    have hm0 := P.hm₀0 (ω i).1.1; have h1m0 : (0:ℝ) < 1 - P.m₀ (ω i).1.1 := by
      have := P.hm₀1 (ω i).1.1; linarith
    have hg00 := P.hg₀0 (ω i).1.1; have h1g0 : (0:ℝ) < 1 - P.g₀ (ω i).1.1 := by
      have := P.hg₀1 (ω i).1.1; linarith
    have hg10 := P.hg₁0 (ω i).1.1; have h1g1 : (0:ℝ) < 1 - P.g₁ (ω i).1.1 := by
      have := P.hg₁1 (ω i).1.1; linarith
    simp only [obsReal, mhat2, ghat2]
    rcases (ω i).2.1 with _ | _ <;> rcases (ω i).2.2 with _ | _ <;>
      · simp only [Bool.false_eq_true, if_false, if_true]
        refine mul_pos (mul_pos (inv_pos.mpr hC) ?_) ?_ <;> assumption
  intro h
  rw [Measure.real, h, ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

/-- The alternative law's `.real` point mass: a uniform mixture over sign vectors. -/
theorem Qtrue2_real_singleton (P : VarConstr2 K) {n : ℕ} [NeZero K]
    (ω : Fin n → Obs (Fin K × Bool)) :
    (Qtrue2 P n).real {ω}
      = ∑ lam : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹
          * ∏ i, obsReal (P.mPert2 lam) (P.gPert2 lam) (ω i) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert2 P n lam) :=
    fun lam => Qpert2_isProb P n lam
  rw [Qtrue2, Measure.real, mixture_apply]
  rw [ENNReal.toReal_sum (fun lam _ => ENNReal.mul_ne_top
    (by rw [signWeight]; exact ENNReal.inv_ne_top.2 (by simp)) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [ENNReal.toReal_mul, signWeight_toReal]
  congr 1
  rw [Qpert2]
  exact productLaw_real_singleton (P.validDGP_pert2 lam) ω

/-- **Mixture second-moment identity** (second construction). -/
theorem one_add_chiSqDiv_Qtrue2_Qfalse2 (P : VarConstr2 K) {n : ℕ} [NeZero K] :
    1 + chiSqDiv (Qtrue2 P n) (Qfalse2 P n)
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
          ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (P.chiSqOverlapV2 lam lam') ^ n := by
  haveI : IsProbabilityMeasure (Qtrue2 P n) := Qtrue2_isProb P n
  haveI : IsProbabilityMeasure (Qfalse2 P n) := Qfalse2_isProb P n
  have hac : Qtrue2 P n ≪ Qfalse2 P n :=
    absolutelyContinuous_of_singleton_pos _ _ (Qfalse2_singleton_ne_zero P)
  rw [finite_one_add_chiSqDiv (Qtrue2 P n) (Qfalse2 P n) hac]
  have hstep : ∀ ω : Fin n → Obs (Fin K × Bool),
      ((Qtrue2 P n).real {ω}) ^ 2 / (Qfalse2 P n).real {ω}
        = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
            ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
              * ∏ i, (obsReal (P.mPert2 lam) (P.gPert2 lam) (ω i)
                    * obsReal (P.mPert2 lam') (P.gPert2 lam') (ω i)
                    / obsReal P.mhat2 P.ghat2 (ω i)) := by
    intro ω
    rw [Qtrue2_real_singleton P ω, Qfalse2,
      productLaw_real_singleton (P.validDGP_hat2 (K := K)) ω, sq, Finset.sum_mul_sum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun lam' _ => ?_
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl fun ω _ => hstep ω]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam' _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold chiSqOverlapV2
  rw [Fintype.sum_pow]

/-- **The χ² indistinguishability bound** (second construction). -/
theorem chiSqDiv_Qtrue2_Qfalse2_le_one (P : VarConstr2 K) {n : ℕ} [NeZero K]
    (hΓsum : ∑ j, P.ΓV2 j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV2 j / (K : ℝ)) ^ 2 ≤ Real.log 2) :
    chiSqDiv (Qtrue2 P n) (Qfalse2 P n) ≤ 1 := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hid := P.one_add_chiSqDiv_Qtrue2_Qfalse2 (n := n)
  have hov : ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (P.chiSqOverlapV2 lam lam') ^ n
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
          * (1 + ∑ j, (P.ΓV2 j / (K : ℝ)) * (signOf (lam j) * signOf (lam' j))) ^ n := by
    refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun lam' _ => ?_
    rw [P.chiSqOverlap_eq2 lam lam']
  have hbound := ingster_bound_general K n
    (d := fun j => P.ΓV2 j / (K : ℝ))
    (fun j => div_nonneg (P.ΓV2_nonneg j) (Nat.cast_nonneg K)) hΓsum hreg
  rw [← hov] at hbound
  rw [← hid] at hbound
  linarith

/-- **Total-variation indistinguishability** (second construction). -/
theorem tvDist_Qfalse2_Qtrue2_le_half (P : VarConstr2 K) {n : ℕ} [NeZero K]
    (hΓsum : ∑ j, P.ΓV2 j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV2 j / (K : ℝ)) ^ 2 ≤ Real.log 2) :
    tvDist (Qfalse2 P n) (Qtrue2 P n) ≤ 1 / 2 := by
  haveI : IsProbabilityMeasure (Qtrue2 P n) := Qtrue2_isProb P n
  haveI : IsProbabilityMeasure (Qfalse2 P n) := Qfalse2_isProb P n
  have hac : Qtrue2 P n ≪ Qfalse2 P n :=
    absolutelyContinuous_of_singleton_pos _ _ (Qfalse2_singleton_ne_zero P)
  have hchi := P.chiSqDiv_Qtrue2_Qfalse2_le_one (n := n) hΓsum hreg
  rw [tvDist_symm]
  calc tvDist (Qtrue2 P n) (Qfalse2 P n)
      ≤ (1 / 2) * Real.sqrt (chiSqDiv (Qtrue2 P n) (Qfalse2 P n)) :=
        tvDist_le_half_sqrt_chiSqDiv _ _ hac Integrable.of_finite
    _ ≤ (1 / 2) * Real.sqrt 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); exact Real.sqrt_le_sqrt hchi
    _ = 1 / 2 := by rw [Real.sqrt_one]; ring

/-- **Structure-agnostic minimax lower bound (second / propensity-dominant construction).**
For a cell-varying nuisance center whose treated-arm bump is strictly positive, if
the Case-2 propensity-dominant budgets and χ² regularity conditions hold, every
measurable estimator has miss probability at least `1/4` at half of the displayed
strictly positive ATE separation somewhere in the structure-agnostic class.

This is the `εm > εg` construction: the propensity error carries the larger budget,
and the strict positivity guard rules out the degenerate zero-separation
instantiation. -/
theorem minimax_lower_bound_var2 (P : VarConstr2 K) {n : ℕ} [NeZero K] {εg εm : ℝ}
    (hβpos : 0 < P.β)
    (hm : ∀ j, (P.m₀ j * P.κ j) ^ 2 ≤ εm)
    (hg : ∀ j, P.β ^ 2 * (P.α * P.g₁ j + 1) ^ 2
        / (1 - P.β / P.g₁ j - P.α * P.β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hΓsum : ∑ j, P.ΓV2 j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV2 j / (K : ℝ)) ^ 2 ≤ Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMiss P.mhat2 P.ghat2 εg εm n est
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
  -- the two-point witness
  let W : TwoPointWitness (Fin K × Bool) n P.mhat2 P.ghat2 εg εm :=
    { s := s
      c := 1 / 2
      Q := fun j => cond j (Qtrue2 P n) (Qfalse2 P n)
      prob := by
        intro j; cases j
        · exact Qfalse2_isProb P n
        · exact Qtrue2_isProb P n
      θ := fun j => cond j (θ0 + gap) θ0
      sep := by
        change 2 * s ≤ |(θ0 + gap) - θ0|
        rw [add_sub_cancel_left, abs_of_pos hgap_pos, hs]; linarith
      tvBound := by simpa using P.tvDist_Qfalse2_Qtrue2_le_half (n := n) hΓsum hreg
      dominated := by
        intro est' j
        cases j
        · -- null branch
          change (Qfalse2 P n).real {x | s ≤ |est' x - θ0|}
              ≤ minimaxMiss P.mhat2 P.ghat2 εg εm n est' s
          have hb := P.real2_le_minimaxMiss (n := n) (inClass_null2 P hεg hεm) est' s
          rw [hθ0]
          exact hb
        · -- mixture branch
          change (Qtrue2 P n).real {x | s ≤ |est' x - (θ0 + gap)|}
              ≤ minimaxMiss P.mhat2 P.ghat2 εg εm n est' s
          haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert2 P n lam) :=
            fun lam => Qpert2_isProb P n lam
          unfold Qtrue2
          refine mixtureReal_le (signWeight K) (signWeight_sum K)
            (fun lam => Qpert2 P n lam) _ _ ?_
          intro lam
          have hb := P.real2_le_minimaxMiss (n := n) (P.inClass2 hm hg hεg lam) est' s
          have hkey : ate (P.gPert2 lam) = θ0 + gap := by
            have := P.ate_gap2 lam
            rw [hθ0, hgap]; linarith [this]
          rw [hkey] at hb
          exact hb }
  exact twoPointWitness_quarter W (le_refl _) hest

end VarConstr2

end Causalean.Estimation.MinimaxATE
