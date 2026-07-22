/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: assembly (general constant center)

The general-constant-center analogue of `ExplicitWitness.lean` + `ChiSquaredCore.lean`.
It assembles the construction (`ConstCenterGeneral/Construction.lean`, `ConstCenterGeneral/Gap.lean`,
`ConstCenterGeneral/Membership.lean`, and `ConstCenterGeneral/ChiSqOverlap.lean`)
into a `TwoPointWitness` and discharges the χ² indistinguishability, yielding an
**unconditional** minimax lower bound around an arbitrary constant nuisance center
`(m₀, g₀, g₁) ∈ (0,1)³`.

* `QfalseG = P̂^⊗n`, `QtrueG = (1/2^K) Σ_λ Qλ^⊗n` — null and Rademacher-mixture laws.
* The `dominated` obligation is discharged by `mixtureReal_le`: every `Qλ` is in-class
  (`inClassG`) and shares ATE `θ_true = (g₁−g₀) + g₁β(α+β)/(g₁²−β²)` (`ate_gPertG`).
* The χ² bound reuses the abstract `ingster_bound` with `γ = Γ/2` (`chiSqOverlap_eqG` gives
  the coefficient `Γ/K`), so `χ² ≤ 1` whenever `Γ ≤ 1` and `2n²(Γ/2)² ≤ K·log 2`.

The capstone `minimax_lower_bound_gen` shows every measurable estimator
misses the true ATE by `s = g₁β(α+β)/(2(g₁²−β²)) ≍ √(εg·εm)` with probability `≥ 1/4`
somewhere in the class — the doubly-robust product rate is unbeatable for any constant
bounded-away center.  At `m₀ = g₁ = 1/2` this recovers `minimax_lower_bound`.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Membership
import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.ChiSqOverlap
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore
import Causalean.Estimation.MinimaxATE.Reduction.Witness
import Causalean.Stat.Minimax.Mixture

/-! # General-Center Lower Bound

This file assembles the general constant-center construction for structure-agnostic ATE
estimation into a two-point minimax lower bound. It defines the null sample law `QfalseG`, the
sign-indexed perturbed sample laws `QpertG`, and the Rademacher-mixture alternative `QtrueG`,
then proves their probability-measure facts.

The main calculations are `one_add_chiSqDiv_QtrueG_QfalseG`, which expresses the mixture
second moment through the general-center overlap coefficient, `chiSqDiv_QtrueG_QfalseG_le_one`,
which applies the Ingster bound under the `Γ` sample-size regime, and
`tvDist_QfalseG_QtrueG_le_half`, which converts chi-squared control to total variation. The
capstone `minimax_lower_bound_gen` shows that every measurable estimator misses by the
general-center product-rate scale somewhere in the structure-agnostic nuisance class. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

namespace GenConstr

/-- The paired-cell covariate is nonempty whenever `K ≠ 0`. -/
instance instNonemptyFinBoolProd {K : ℕ} [NeZero K] : Nonempty (Fin K × Bool) :=
  ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩, true)⟩

/-- The per-cell overlap coefficient is nonnegative. -/
theorem Γ_nonneg (P : GenConstr) : 0 ≤ P.Γ := by
  have h1 := P.hm₀0; have h2 := P.hm₀1; have h3 := P.hg₁0; have h4 := P.hg₁1
  unfold Γ
  have t1 : 0 ≤ P.m₀ * P.α ^ 2 / P.g₁ := by positivity
  have t2 : 0 ≤ P.m₀ * (P.α + P.β / P.g₁) ^ 2 / (1 - P.g₁) := by
    apply div_nonneg (by positivity); linarith
  have t3 : 0 ≤ P.m₀ ^ 2 * P.β ^ 2 / (P.g₁ ^ 2 * (1 - P.m₀)) := by
    apply div_nonneg (by positivity)
    have : 0 < 1 - P.m₀ := by linarith
    positivity
  linarith

/-- The null estimate is itself in the class (zero nuisance error). -/
theorem inClass_nullG (P : GenConstr) {K : ℕ} {εg εm : ℝ} (hεg : 0 ≤ εg) (hεm : 0 ≤ εm) :
    InClass (P.mhatG (K := K)) P.ghatG εg εm P.mhatG P.ghatG where
  valid := P.validDGP_hatG
  err_g d := by rw [l2sq_self]; exact hεg
  err_m := by rw [l2sq_self]; exact hεm

/-- The null `n`-sample law `P̂^⊗n`. -/
noncomputable def QfalseG (P : GenConstr) (K n : ℕ) [NeZero K] :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (P.validDGP_hatG (K := K)) n

/-- The perturbed `n`-sample law `Qλ^⊗n`. -/
noncomputable def QpertG (P : GenConstr) (K n : ℕ) [NeZero K] (lam : Fin K → Bool) :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (P.validDGP_pertG lam) n

/-- The alternative `n`-sample law: the uniform Rademacher mixture of the perturbed laws. -/
noncomputable def QtrueG (P : GenConstr) (K n : ℕ) [NeZero K] :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  mixture (signWeight K) (fun lam => QpertG P K n lam)

/-- The null sample law is a probability measure. -/
theorem QfalseG_isProb (P : GenConstr) (K n : ℕ) [NeZero K] :
    IsProbabilityMeasure (QfalseG P K n) := by unfold QfalseG; infer_instance

/-- Each perturbed sample law is a probability measure. -/
theorem QpertG_isProb (P : GenConstr) (K n : ℕ) [NeZero K] (lam : Fin K → Bool) :
    IsProbabilityMeasure (QpertG P K n lam) := by unfold QpertG; infer_instance

/-- The Rademacher mixture of perturbed sample laws is a probability measure. -/
theorem QtrueG_isProb (P : GenConstr) (K n : ℕ) [NeZero K] :
    IsProbabilityMeasure (QtrueG P K n) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertG P K n lam) :=
    fun lam => QpertG_isProb P K n lam
  unfold QtrueG
  exact mixture_isProbabilityMeasure _ (signWeight_sum K) _

/-- An in-class DGP's `n`-sample miss probability at its own ATE is dominated by the
minimax miss probability. -/
theorem realG_le_minimaxMiss (P : GenConstr) {K n : ℕ} [NeZero K] {εg εm : ℝ}
    {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
    (hin : InClass (P.mhatG (K := K)) P.ghatG εg εm m g)
    (est : (Fin n → Obs (Fin K × Bool)) → ℝ) (s : ℝ) :
    (productLaw hin.valid n).real {x | s ≤ |est x - ate g|}
      ≤ minimaxMiss P.mhatG P.ghatG εg εm n est s := by
  simpa [nMiss] using
    nMiss_le_minimaxMiss (⟨(m, g), hin⟩ : InClassDGP (P.mhatG (K := K)) P.ghatG εg εm)
      (est := est) (s := s)

/-- The null `n`-sample law charges every point. -/
theorem QfalseG_singleton_ne_zero (P : GenConstr) {K n : ℕ} [NeZero K]
    (ω : Fin n → Obs (Fin K × Bool)) : QfalseG P K n {ω} ≠ 0 := by
  have hm0 := P.hm₀0; have h1m0 : (0:ℝ) < 1 - P.m₀ := by have := P.hm₀1; linarith
  have hg00 := P.hg₀0; have h1g0 : (0:ℝ) < 1 - P.g₀ := by have := P.hg₀1; linarith
  have hg10 := P.hg₁0; have h1g1 : (0:ℝ) < 1 - P.g₁ := by have := P.hg₁1; linarith
  have hpos : 0 < (QfalseG P K n).real {ω} := by
    rw [QfalseG, productLaw_real_singleton]
    apply Finset.prod_pos
    intro i _
    have hC : (0 : ℝ) < (Fintype.card (Fin K × Bool) : ℝ) := by
      have := Fintype.card_pos (α := Fin K × Bool); exact_mod_cast this
    simp only [obsReal, mhatG, ghatG]
    rcases (ω i).2.1 with _ | _ <;> rcases (ω i).2.2 with _ | _ <;>
      · simp only [Bool.false_eq_true, if_false, if_true]; positivity
  intro h
  rw [Measure.real, h, ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

/-- The alternative law's `.real` point mass: a uniform mixture over sign vectors. -/
theorem QtrueG_real_singleton (P : GenConstr) {K n : ℕ} [NeZero K]
    (ω : Fin n → Obs (Fin K × Bool)) :
    (QtrueG P K n).real {ω}
      = ∑ lam : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹
          * ∏ i, obsReal (P.mPertG lam) (P.gPertG lam) (ω i) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertG P K n lam) :=
    fun lam => QpertG_isProb P K n lam
  rw [QtrueG, Measure.real, mixture_apply]
  rw [ENNReal.toReal_sum (fun lam _ => ENNReal.mul_ne_top
    (by rw [signWeight]; exact ENNReal.inv_ne_top.2 (by simp)) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [ENNReal.toReal_mul, signWeight_toReal]
  congr 1
  rw [QpertG]
  exact productLaw_real_singleton (P.validDGP_pertG lam) ω

/-- **Mixture second-moment identity** (general center). -/
theorem one_add_chiSqDiv_QtrueG_QfalseG (P : GenConstr) {K n : ℕ} [NeZero K] :
    1 + chiSqDiv (QtrueG P K n) (QfalseG P K n)
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
          ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (P.chiSqOverlapG lam lam') ^ n := by
  haveI : IsProbabilityMeasure (QtrueG P K n) := QtrueG_isProb P K n
  haveI : IsProbabilityMeasure (QfalseG P K n) := QfalseG_isProb P K n
  have hac : QtrueG P K n ≪ QfalseG P K n :=
    absolutelyContinuous_of_singleton_pos _ _ (QfalseG_singleton_ne_zero P)
  rw [finite_one_add_chiSqDiv (QtrueG P K n) (QfalseG P K n) hac]
  have hstep : ∀ ω : Fin n → Obs (Fin K × Bool),
      ((QtrueG P K n).real {ω}) ^ 2 / (QfalseG P K n).real {ω}
        = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
            ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
              * ∏ i, (obsReal (P.mPertG lam) (P.gPertG lam) (ω i)
                    * obsReal (P.mPertG lam') (P.gPertG lam') (ω i)
                    / obsReal P.mhatG P.ghatG (ω i)) := by
    intro ω
    rw [QtrueG_real_singleton P ω, QfalseG,
      productLaw_real_singleton (P.validDGP_hatG (K := K)) ω, sq, Finset.sum_mul_sum]
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
  unfold chiSqOverlapG
  rw [Fintype.sum_pow]

/-- **The χ² indistinguishability bound** (general center): `Γ ≤ 1`, `2n²(Γ/2)² ≤ K·log 2`
imply `χ²(QtrueG‖QfalseG) ≤ 1`. -/
theorem chiSqDiv_QtrueG_QfalseG_le_one (P : GenConstr) {K n : ℕ} [NeZero K]
    (hΓ : P.Γ ≤ 1) (hreg : 2 * (n : ℝ) ^ 2 * (P.Γ / 2) ^ 2 ≤ (K : ℝ) * Real.log 2) :
    chiSqDiv (QtrueG P K n) (QfalseG P K n) ≤ 1 := by
  have hΓ0 := P.Γ_nonneg
  have hid := P.one_add_chiSqDiv_QtrueG_QfalseG (K := K) (n := n)
  have hov : ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (P.chiSqOverlapG lam lam') ^ n
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
          * (1 + (2 * (P.Γ / 2) / (K : ℝ)) * ∑ j, signOf (lam j) * signOf (lam' j)) ^ n := by
    refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun lam' _ => ?_
    rw [P.chiSqOverlap_eqG lam lam', show P.Γ / (K : ℝ) = 2 * (P.Γ / 2) / (K : ℝ) from by ring]
  have hbound := ingster_bound K n (by linarith : (0:ℝ) ≤ P.Γ / 2)
    (by linarith : 2 * (P.Γ / 2) ≤ 1) hreg
  rw [← hov] at hbound
  rw [← hid] at hbound
  linarith

/-- **Total-variation indistinguishability** (general center). -/
theorem tvDist_QfalseG_QtrueG_le_half (P : GenConstr) {K n : ℕ} [NeZero K]
    (hΓ : P.Γ ≤ 1) (hreg : 2 * (n : ℝ) ^ 2 * (P.Γ / 2) ^ 2 ≤ (K : ℝ) * Real.log 2) :
    tvDist (QfalseG P K n) (QtrueG P K n) ≤ 1 / 2 := by
  haveI : IsProbabilityMeasure (QtrueG P K n) := QtrueG_isProb P K n
  haveI : IsProbabilityMeasure (QfalseG P K n) := QfalseG_isProb P K n
  have hac : QtrueG P K n ≪ QfalseG P K n :=
    absolutelyContinuous_of_singleton_pos _ _ (QfalseG_singleton_ne_zero P)
  have hchi := P.chiSqDiv_QtrueG_QfalseG_le_one (K := K) (n := n) hΓ hreg
  rw [tvDist_symm]
  calc tvDist (QtrueG P K n) (QfalseG P K n)
      ≤ (1 / 2) * Real.sqrt (chiSqDiv (QtrueG P K n) (QfalseG P K n)) :=
        tvDist_le_half_sqrt_chiSqDiv _ _ hac Integrable.of_finite
    _ ≤ (1 / 2) * Real.sqrt 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); exact Real.sqrt_le_sqrt hchi
    _ = 1 / 2 := by rw [Real.sqrt_one]; ring

/-- **Structure-agnostic minimax lower bound (general constant center).**  Around any
constant nuisance center `(m₀, g₀, g₁) ∈ (0,1)³`, with the Rademacher-bump budgets met
(`(m₀β/g₁)² ≤ εm`, `g₁²(α+β)²/(g₁−β)² ≤ εg`), `Γ ≤ 1`, and the sample-size regime
`2n²(Γ/2)² ≤ K·log 2`, **every** measurable estimator misses the true ATE by
`s = g₁β(α+β)/(2(g₁²−β²))` with probability at least `1/4` somewhere in the class. -/
theorem minimax_lower_bound_gen (P : GenConstr) {K n : ℕ} [NeZero K] {εg εm : ℝ}
    (hm : (P.m₀ * (P.β / P.g₁)) ^ 2 ≤ εm)
    (hg : P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hΓ : P.Γ ≤ 1) (hreg : 2 * (n : ℝ) ^ 2 * (P.Γ / 2) ^ 2 ≤ (K : ℝ) * Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMiss P.mhatG P.ghatG εg εm n est
      (P.g₁ * P.β * (P.α + P.β) / (2 * (P.g₁ ^ 2 - P.β ^ 2))) := by
  have hden : (0:ℝ) < P.g₁ ^ 2 - P.β ^ 2 := P.g1sq_sub_betasq_pos
  have hdenne : P.g₁ ^ 2 - P.β ^ 2 ≠ 0 := hden.ne'
  set gap := P.g₁ * P.β * (P.α + P.β) / (P.g₁ ^ 2 - P.β ^ 2) with hgap
  have hgap0 : 0 ≤ gap := by
    rw [hgap]; have := P.hβ; have := P.hα; have := P.hg₁0
    apply div_nonneg (by positivity) hden.le
  set s := P.g₁ * P.β * (P.α + P.β) / (2 * (P.g₁ ^ 2 - P.β ^ 2)) with hs
  have hs_gap : s = gap / 2 := by rw [hs, hgap]; field_simp
  -- the two-point witness
  let W : TwoPointWitness (Fin K × Bool) n P.mhatG P.ghatG εg εm :=
    { s := s
      c := 1 / 2
      Q := fun j => cond j (QtrueG P K n) (QfalseG P K n)
      prob := by
        intro j; cases j
        · exact QfalseG_isProb P K n
        · exact QtrueG_isProb P K n
      θ := fun j => cond j ((P.g₁ - P.g₀) + gap) (P.g₁ - P.g₀)
      sep := by
        change 2 * s ≤ |((P.g₁ - P.g₀) + gap) - (P.g₁ - P.g₀)|
        rw [add_sub_cancel_left, abs_of_nonneg hgap0, hs_gap]; linarith
      tvBound := by simpa using P.tvDist_QfalseG_QtrueG_le_half (K := K) (n := n) hΓ hreg
      dominated := by
        intro est' j
        cases j
        · -- null branch: `cond false` reduces to `QfalseG` / `g₁ − g₀`
          change (QfalseG P K n).real {x | s ≤ |est' x - (P.g₁ - P.g₀)|}
              ≤ minimaxMiss P.mhatG P.ghatG εg εm n est' s
          have hb := P.realG_le_minimaxMiss (K := K) (n := n) (inClass_nullG P hεg hεm) est' s
          rw [P.ate_ghatG] at hb
          exact hb
        · -- mixture branch
          change (QtrueG P K n).real {x | s ≤ |est' x - ((P.g₁ - P.g₀) + gap)|}
              ≤ minimaxMiss P.mhatG P.ghatG εg εm n est' s
          haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertG P K n lam) :=
            fun lam => QpertG_isProb P K n lam
          unfold QtrueG
          refine mixtureReal_le (signWeight K) (signWeight_sum K)
            (fun lam => QpertG P K n lam) _ _ ?_
          intro lam
          have hb := P.realG_le_minimaxMiss (K := K) (n := n) (P.inClassG hm hg lam) est' s
          rw [P.ate_gPertG lam, ← hgap] at hb
          exact hb }
  exact twoPointWitness_quarter W (le_refl _) hest

end GenConstr

end Causalean.Estimation.MinimaxATE
