/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: assembly (cell-varying center)

The cell-varying-center analogue of `ConstCenterGeneral/LowerBound.lean`. It assembles the
construction (`VaryingCenterCase1/Construction.lean`, `VaryingCenterCase1/Gap.lean`, `VaryingCenterCase1/Membership.lean`,
and `VaryingCenterCase1/ChiSqOverlap.lean`) into a
`TwoPointWitness` and discharges the χ² indistinguishability via the **non-uniform**
`ingster_bound_general` (per-pair coefficient `d j = Γⱼ/K`), yielding a minimax
lower bound around a **cell-varying** nuisance center — the finite-model analogue of
the paper's functional center, for centers constant within each Rademacher pair.

The capstone `minimax_lower_bound_var` shows that, with the per-pair
budgets met and the regularity conditions `Σⱼ Γⱼ/K ≤ 1` and
`(n²/2) Σⱼ (Γⱼ/K)² ≤ log 2`, every measurable estimator misses the true ATE by
`s = ½(ate gλ − ate ĝ)` with probability `≥ 1/4` somewhere in the class.  At a
constant center this is `minimax_lower_bound_gen`.
-/

import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Membership
import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.ChiSqOverlap
import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Ingster
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore
import Causalean.Estimation.MinimaxATE.Reduction.Witness
import Causalean.Stat.Minimax.Mixture

/-! # Cell-Varying Lower Bound

This file assembles the cell-varying-center construction into the structure-agnostic ATE minimax
lower bound.  It combines per-pair class membership, ATE-gap, and chi-squared-overlap arguments
with a non-uniform Ingster bound to handle nuisance centers that vary across paired cells.

It defines the null and alternative sample laws `QfalseV`, `QpertV`, and `QtrueV`, proves their
probability-measure and point-mass facts, computes the mixture second moment in
`one_add_chiSqDiv_QtrueV_QfalseV`, and derives the chi-squared and total-variation
indistinguishability bounds `chiSqDiv_QtrueV_QfalseV_le_one` and
`tvDist_QfalseV_QtrueV_le_half`.  The headline theorem `minimax_lower_bound_var` packages these
ingredients into a `TwoPointWitness`, proving a `1 / 4` minimax miss lower bound at half the
cell-varying ATE gap. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

namespace VarConstr

/-- The paired-cell covariate is nonempty whenever `K ≠ 0`. -/
instance instNonemptyFinBoolProd {K : ℕ} [NeZero K] : Nonempty (Fin K × Bool) :=
  ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩, true)⟩

variable {K : ℕ}

/-- The null estimate is itself in the class (zero nuisance error). -/
theorem inClass_nullV (P : VarConstr K) {εg εm : ℝ} (hεg : 0 ≤ εg) (hεm : 0 ≤ εm) :
    InClass (P.mhatV (K := K)) P.ghatV εg εm P.mhatV P.ghatV where
  valid := P.validDGP_hatV
  err_g d := by rw [l2sq_self]; exact hεg
  err_m := by rw [l2sq_self]; exact hεm

/-- The null `n`-sample law `P̂^⊗n`. -/
noncomputable def QfalseV (P : VarConstr K) (n : ℕ) [NeZero K] :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (P.validDGP_hatV (K := K)) n

/-- The perturbed `n`-sample law `Qλ^⊗n`. -/
noncomputable def QpertV (P : VarConstr K) (n : ℕ) [NeZero K] (lam : Fin K → Bool) :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (P.validDGP_pertV lam) n

/-- The alternative `n`-sample law: the uniform Rademacher mixture of the perturbed laws. -/
noncomputable def QtrueV (P : VarConstr K) (n : ℕ) [NeZero K] :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  mixture (signWeight K) (fun lam => QpertV P n lam)

/-- The null sample law is a probability measure. -/
theorem QfalseV_isProb (P : VarConstr K) (n : ℕ) [NeZero K] :
    IsProbabilityMeasure (QfalseV P n) := by unfold QfalseV; infer_instance

/-- Each perturbed sample law is a probability measure. -/
theorem QpertV_isProb (P : VarConstr K) (n : ℕ) [NeZero K] (lam : Fin K → Bool) :
    IsProbabilityMeasure (QpertV P n lam) := by unfold QpertV; infer_instance

/-- The Rademacher mixture of perturbed sample laws is a probability measure. -/
theorem QtrueV_isProb (P : VarConstr K) (n : ℕ) [NeZero K] :
    IsProbabilityMeasure (QtrueV P n) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertV P n lam) :=
    fun lam => QpertV_isProb P n lam
  unfold QtrueV
  exact mixture_isProbabilityMeasure _ (signWeight_sum K) _

/-- An in-class DGP's miss probability at its own ATE is dominated by the minimax miss. -/
theorem realV_le_minimaxMiss (P : VarConstr K) {n : ℕ} [NeZero K] {εg εm : ℝ}
    {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
    (hin : InClass (P.mhatV (K := K)) P.ghatV εg εm m g)
    (est : (Fin n → Obs (Fin K × Bool)) → ℝ) (s : ℝ) :
    (productLaw hin.valid n).real {x | s ≤ |est x - ate g|}
      ≤ minimaxMiss P.mhatV P.ghatV εg εm n est s := by
  simpa [nMiss] using
    nMiss_le_minimaxMiss (⟨(m, g), hin⟩ : InClassDGP (P.mhatV (K := K)) P.ghatV εg εm)
      (est := est) (s := s)

/-- The null `n`-sample law charges every point. -/
theorem QfalseV_singleton_ne_zero (P : VarConstr K) {n : ℕ} [NeZero K]
    (ω : Fin n → Obs (Fin K × Bool)) : QfalseV P n {ω} ≠ 0 := by
  have hpos : 0 < (QfalseV P n).real {ω} := by
    rw [QfalseV, productLaw_real_singleton]
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
    simp only [obsReal, mhatV, ghatV]
    rcases (ω i).2.1 with _ | _ <;> rcases (ω i).2.2 with _ | _ <;>
      · simp only [Bool.false_eq_true, if_false, if_true]
        refine mul_pos (mul_pos (inv_pos.mpr hC) ?_) ?_ <;> assumption
  intro h
  rw [Measure.real, h, ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

/-- The alternative law's `.real` point mass: a uniform mixture over sign vectors. -/
theorem QtrueV_real_singleton (P : VarConstr K) {n : ℕ} [NeZero K]
    (ω : Fin n → Obs (Fin K × Bool)) :
    (QtrueV P n).real {ω}
      = ∑ lam : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹
          * ∏ i, obsReal (P.mPertV lam) (P.gPertV lam) (ω i) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertV P n lam) :=
    fun lam => QpertV_isProb P n lam
  rw [QtrueV, Measure.real, mixture_apply]
  rw [ENNReal.toReal_sum (fun lam _ => ENNReal.mul_ne_top
    (by rw [signWeight]; exact ENNReal.inv_ne_top.2 (by simp)) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [ENNReal.toReal_mul, signWeight_toReal]
  congr 1
  rw [QpertV]
  exact productLaw_real_singleton (P.validDGP_pertV lam) ω

/-- **Mixture second-moment identity** (cell-varying center). -/
theorem one_add_chiSqDiv_QtrueV_QfalseV (P : VarConstr K) {n : ℕ} [NeZero K] :
    1 + chiSqDiv (QtrueV P n) (QfalseV P n)
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
          ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (P.chiSqOverlapV lam lam') ^ n := by
  haveI : IsProbabilityMeasure (QtrueV P n) := QtrueV_isProb P n
  haveI : IsProbabilityMeasure (QfalseV P n) := QfalseV_isProb P n
  have hac : QtrueV P n ≪ QfalseV P n :=
    absolutelyContinuous_of_singleton_pos _ _ (QfalseV_singleton_ne_zero P)
  rw [finite_one_add_chiSqDiv (QtrueV P n) (QfalseV P n) hac]
  have hstep : ∀ ω : Fin n → Obs (Fin K × Bool),
      ((QtrueV P n).real {ω}) ^ 2 / (QfalseV P n).real {ω}
        = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
            ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
              * ∏ i, (obsReal (P.mPertV lam) (P.gPertV lam) (ω i)
                    * obsReal (P.mPertV lam') (P.gPertV lam') (ω i)
                    / obsReal P.mhatV P.ghatV (ω i)) := by
    intro ω
    rw [QtrueV_real_singleton P ω, QfalseV,
      productLaw_real_singleton (P.validDGP_hatV (K := K)) ω, sq, Finset.sum_mul_sum]
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
  unfold chiSqOverlapV
  rw [Fintype.sum_pow]

/-- **The χ² indistinguishability bound** (cell-varying center). -/
theorem chiSqDiv_QtrueV_QfalseV_le_one (P : VarConstr K) {n : ℕ} [NeZero K]
    (hΓsum : ∑ j, P.ΓV j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV j / (K : ℝ)) ^ 2 ≤ Real.log 2) :
    chiSqDiv (QtrueV P n) (QfalseV P n) ≤ 1 := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hid := P.one_add_chiSqDiv_QtrueV_QfalseV (n := n)
  have hov : ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (P.chiSqOverlapV lam lam') ^ n
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
          * (1 + ∑ j, (P.ΓV j / (K : ℝ)) * (signOf (lam j) * signOf (lam' j))) ^ n := by
    refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun lam' _ => ?_
    rw [P.chiSqOverlap_eqV lam lam']
  have hbound := ingster_bound_general K n
    (d := fun j => P.ΓV j / (K : ℝ))
    (fun j => div_nonneg (P.ΓV_nonneg j) (Nat.cast_nonneg K)) hΓsum hreg
  rw [← hov] at hbound
  rw [← hid] at hbound
  linarith

/-- **Total-variation indistinguishability** (cell-varying center). -/
theorem tvDist_QfalseV_QtrueV_le_half (P : VarConstr K) {n : ℕ} [NeZero K]
    (hΓsum : ∑ j, P.ΓV j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV j / (K : ℝ)) ^ 2 ≤ Real.log 2) :
    tvDist (QfalseV P n) (QtrueV P n) ≤ 1 / 2 := by
  haveI : IsProbabilityMeasure (QtrueV P n) := QtrueV_isProb P n
  haveI : IsProbabilityMeasure (QfalseV P n) := QfalseV_isProb P n
  have hac : QtrueV P n ≪ QfalseV P n :=
    absolutelyContinuous_of_singleton_pos _ _ (QfalseV_singleton_ne_zero P)
  have hchi := P.chiSqDiv_QtrueV_QfalseV_le_one (n := n) hΓsum hreg
  rw [tvDist_symm]
  calc tvDist (QtrueV P n) (QfalseV P n)
      ≤ (1 / 2) * Real.sqrt (chiSqDiv (QtrueV P n) (QfalseV P n)) :=
        tvDist_le_half_sqrt_chiSqDiv _ _ hac Integrable.of_finite
    _ ≤ (1 / 2) * Real.sqrt 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); exact Real.sqrt_le_sqrt hchi
    _ = 1 / 2 := by rw [Real.sqrt_one]; ring

/-- **Structure-agnostic minimax lower bound (cell-varying center).**  Around a
nuisance center that varies across pairs (constant within each pair), with the
per-pair budgets and the regularity conditions met, **every** measurable estimator
misses the true ATE by `s = ½(ate gλ − ate ĝ)` with probability at least `1/4`
somewhere in the class. -/
theorem minimax_lower_bound_var (P : VarConstr K) {n : ℕ} [NeZero K] {εg εm : ℝ}
    (hm : ∀ j, (P.m₀ j * (P.β / P.g₁ j)) ^ 2 ≤ εm)
    (hg : ∀ j, P.g₁ j ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ j - P.β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hΓsum : ∑ j, P.ΓV j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV j / (K : ℝ)) ^ 2 ≤ Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMiss P.mhatV P.ghatV εg εm n est
      ((Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β * (P.α + P.β))
        * (∑ j : Fin K, P.g₁ j / (P.g₁ j ^ 2 - P.β ^ 2)) / 2) := by
  set gap := (Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β * (P.α + P.β))
    * ∑ j : Fin K, P.g₁ j / (P.g₁ j ^ 2 - P.β ^ 2) with hgap
  have hgap0 : 0 ≤ gap := by
    have h := P.ate_gap_nonneg (fun _ => true)
    rwa [P.ate_gapV (fun _ => true)] at h
  set s := gap / 2 with hs
  set θ0 := ate (P.ghatV (K := K)) with hθ0
  -- the two-point witness
  let W : TwoPointWitness (Fin K × Bool) n P.mhatV P.ghatV εg εm :=
    { s := s
      c := 1 / 2
      Q := fun j => cond j (QtrueV P n) (QfalseV P n)
      prob := by
        intro j; cases j
        · exact QfalseV_isProb P n
        · exact QtrueV_isProb P n
      θ := fun j => cond j (θ0 + gap) θ0
      sep := by
        change 2 * s ≤ |(θ0 + gap) - θ0|
        rw [add_sub_cancel_left, abs_of_nonneg hgap0, hs]; linarith
      tvBound := by simpa using P.tvDist_QfalseV_QtrueV_le_half (n := n) hΓsum hreg
      dominated := by
        intro est' j
        cases j
        · -- null branch
          change (QfalseV P n).real {x | s ≤ |est' x - θ0|}
              ≤ minimaxMiss P.mhatV P.ghatV εg εm n est' s
          have hb := P.realV_le_minimaxMiss (n := n) (inClass_nullV P hεg hεm) est' s
          rw [hθ0]
          exact hb
        · -- mixture branch
          change (QtrueV P n).real {x | s ≤ |est' x - (θ0 + gap)|}
              ≤ minimaxMiss P.mhatV P.ghatV εg εm n est' s
          haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertV P n lam) :=
            fun lam => QpertV_isProb P n lam
          unfold QtrueV
          refine mixtureReal_le (signWeight K) (signWeight_sum K)
            (fun lam => QpertV P n lam) _ _ ?_
          intro lam
          have hb := P.realV_le_minimaxMiss (n := n) (P.inClassV hm hg hεg lam) est' s
          have hkey : ate (P.gPertV lam) = θ0 + gap := by
            have := P.ate_gapV lam
            rw [hθ0, hgap]; linarith [this]
          rw [hkey] at hb
          exact hb }
  exact twoPointWitness_quarter W (le_refl _) hest

end VarConstr

end Causalean.Estimation.MinimaxATE
