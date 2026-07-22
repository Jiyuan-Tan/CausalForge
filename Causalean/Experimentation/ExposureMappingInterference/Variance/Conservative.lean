/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.HT.Variance

/-!
# Conservative variance estimators (Aronow–Samii 2017, §5)

Design-based variance estimators for `Var[ŷᵀ(d)]` and `Var[τ̂(dk,dl)]`.  In the
positive-joint regime (`π_{ij}(d) > 0`, `π_{ij}(d,d') > 0` for `i ≠ j`) the variance
estimator `htVarEst` is exactly unbiased (Lemma 5.1, `varun`).  The covariance
`Cov[ŷᵀ(dk),ŷᵀ(dl)]` is unidentified, so its estimator `htCovEst` is only nonpositively
biased (Prop 5.4, `ncov`, via Young's inequality `2ab ≤ a²+b²` for the diagonal term).
Assembling these gives the conservative effect-variance estimator `htEffectVarEst` with
nonnegative bias (Prop 5.7, `consvar`) — the input the interval result consumes.

The zero-pairwise refinements handle the `π_{ij} = 0` corner cases.  Prop 5.2
(`E_htVarEst_eq_addBias`, `varbias`) characterizes the bias of `htVarEst` as the explicit
correction `A = ∑_{π_{ij}=0} y_i y_j`; the Young correction `htA2` (`Â₂`) restores
conservativeness (Prop 5.3, `E_htVarEst_add_htA2_ge`, `a2`).  Prop 5.5
(`E_htCovEst_eq_of_noEffect`, `no_bias_cov`) shows `htCovEst` is exactly unbiased under no
effect.  The general covariance estimator `htCovEstA` (`Ĉov_A`, `eq:ht_cov_general_estimator`)
is nonpositively biased with no positive-cross-joint assumption (Prop 5.6,
`E_htCovEstA_le`, `cova`); its Young correction ranges over *all* `j ∈ U` with
`π_{ij}(d_k,d_l)=0` (faithful to the paper — the diagonal `j=i`, always zero since
`d_k ≠ d_l`, subsumes the unidentified `−∑ᵢ y_i(d_k)y_i(d_l)` term).  Assembling these gives
the general conservative effect-variance estimator `htEffectVarEstA` with nonnegative bias
(general `consvar`, `E_htEffectVarEstA_ge`).
-/


open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Δ]

/-- Horvitz–Thompson estimator of `Var[ŷᵀ(d)]` (eq:ht_variance_estimator), positive-joint
regime. Uses observed outcomes `Yobs`. -/
noncomputable def htVarEst (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (z : Ω) : ℝ :=
  (∑ i, expoInd f θ i d z * (1 - prop D f θ i d) * (Yobs y f θ i z / prop D f θ i d) ^ 2)
  + ∑ i, ∑ j ∈ Finset.univ.erase i,
      expoInd f θ i d z * expoInd f θ j d z
        * ((propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d)
            / propPairSame D f θ i j d)
        * ((Yobs y f θ i z / prop D f θ i d) * (Yobs y f θ j z / prop D f θ j d))

/-- Horvitz–Thompson-type estimator of `Cov[ŷᵀ(dk),ŷᵀ(dl)]` (eq:ht_cov_estimator),
positive-joint regime. Conservative (nonpositively biased) via the Young-inequality
diagonal correction. -/
noncomputable def htCovEst (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (z : Ω) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i,
      expoInd f θ i dk z * expoInd f θ j dl z
        * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
            / propPairCross D f θ i j dk dl)
        * ((Yobs y f θ i z / prop D f θ i dk) * (Yobs y f θ j z / prop D f θ j dl)))
  - ∑ i, (expoInd f θ i dk z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dk)
          + expoInd f θ i dl z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dl))

/-- Conservative variance estimator for `Var[τ̂(dk,dl)]` (eq:ate_var_estimator),
positive-joint regime. -/
noncomputable def htEffectVarEst (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (z : Ω) : ℝ :=
  (htVarEst D y f θ dk z + htVarEst D y f θ dl z - 2 * htCovEst D y f θ dk dl z)
    / (Fintype.card ι : ℝ) ^ 2

/-- **Lemma 5.1 (`varun`).** In the positive-joint regime the HT variance estimator is
unbiased for the true variance. -/
theorem E_htVarEst (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (hpos : ∀ i, prop D f θ i d ≠ 0)
    (hjoint : ∀ i j, i ≠ j → propPairSame D f θ i j d ≠ 0) :
    D.E (htVarEst D y f θ d) = D.Var (htTotal D y f θ d) := by
  rw [Var_htTotal]
  unfold htVarEst
  rw [D.E_add, D.E_sum, D.E_sum]
  congr 1
  · -- diagonal sum
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have key : (fun z => expoInd f θ i d z * (1 - prop D f θ i d)
          * (Yobs y f θ i z / prop D f θ i d) ^ 2)
        = (fun z => ((1 - prop D f θ i d) * (prop D f θ i d)⁻¹ ^ 2)
            * (expoInd f θ i d z * (Yobs y f θ i z) ^ 2)) := by
      funext z; rw [div_pow]; ring
    rw [key, D.E_const_mul]
    rw [D.E_congr (Y := fun z => expoInd f θ i d z * (y i d) ^ 2)
        (fun z => expoInd_mul_Yobs_sq y f θ i d z)]
    rw [D.E_mul_const, E_expoInd]
    ring
  · -- off-diagonal sum
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [D.E_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hij : i ≠ j := fun h => hji h.symm
    have hjoint_ij := hjoint i j hij
    have hi := hpos i
    have hjp := hpos j
    -- factor constants out of the expectation
    have key : (fun z => expoInd f θ i d z * expoInd f θ j d z
          * ((propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d)
              / propPairSame D f θ i j d)
          * ((Yobs y f θ i z / prop D f θ i d) * (Yobs y f θ j z / prop D f θ j d)))
        = (fun z => (((propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d)
              / propPairSame D f θ i j d) * ((prop D f θ i d)⁻¹ * (prop D f θ j d)⁻¹))
            * (expoInd f θ i d z * expoInd f θ j d z
                * Yobs y f θ i z * Yobs y f θ j z)) := by
      funext z; ring
    rw [key, D.E_const_mul]
    -- now evaluate E of the product of indicators times both observed outcomes
    have hprod : D.E (fun z => expoInd f θ i d z * expoInd f θ j d z
          * Yobs y f θ i z * Yobs y f θ j z)
        = y i d * y j d * propPairSame D f θ i j d := by
      rw [D.E_congr (Y := fun z => (y i d * y j d)
          * (expoInd f θ i d z * expoInd f θ j d z)) (fun z => ?_)]
      · rw [D.E_const_mul]; rfl
      · -- force both outcomes via expoInd₂_mul_Yobs and its symmetric use
        have h1 : expoInd f θ i d z * expoInd f θ j d z * Yobs y f θ i z
            = expoInd f θ i d z * expoInd f θ j d z * y i d :=
          expoInd₂_mul_Yobs y f θ i j d d z
        have h2 : expoInd f θ j d z * expoInd f θ i d z * Yobs y f θ j z
            = expoInd f θ j d z * expoInd f θ i d z * y j d :=
          expoInd₂_mul_Yobs y f θ j i d d z
        calc expoInd f θ i d z * expoInd f θ j d z * Yobs y f θ i z * Yobs y f θ j z
            = (expoInd f θ i d z * expoInd f θ j d z * Yobs y f θ i z) * Yobs y f θ j z := by ring
          _ = (expoInd f θ i d z * expoInd f θ j d z * y i d) * Yobs y f θ j z := by rw [h1]
          _ = y i d * (expoInd f θ j d z * expoInd f θ i d z * Yobs y f θ j z) := by ring
          _ = y i d * (expoInd f θ j d z * expoInd f θ i d z * y j d) := by rw [h2]
          _ = (y i d * y j d) * (expoInd f θ i d z * expoInd f θ j d z) := by ring
    rw [hprod]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc,
      mul_div_assoc, mul_div_assoc, div_self hjoint_ij]
    ring

/-- **Proposition 5.4 (`ncov`).** In the positive marginal and positive cross-joint regime, the
HT covariance estimator is nonpositively biased for the true covariance. -/
theorem E_htCovEst_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hne : dk ≠ dl) (hk : ∀ i, prop D f θ i dk ≠ 0) (hl : ∀ i, prop D f θ i dl ≠ 0)
    (hjoint : ∀ i j, i ≠ j → propPairCross D f θ i j dk dl ≠ 0) :
    D.E (htCovEst D y f θ dk dl) ≤ D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl) := by
  rw [Cov_htTotal D y f θ dk dl hne hk hl]
  -- compute the expectation of the covariance estimator
  have hE : D.E (htCovEst D y f θ dk dl)
      = (∑ i, ∑ j ∈ Finset.univ.erase i,
            (propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
              * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl)))
        - ∑ i, ((y i dk) ^ 2 / 2 + (y i dl) ^ 2 / 2) := by
    unfold htCovEst
    rw [D.E_sub, D.E_sum, D.E_sum]
    congr 1
    · -- off-diagonal sum (same cancellation as the variance case)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [D.E_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hij : i ≠ j := fun h => hji h.symm
      have hjoint_ij := hjoint i j hij
      have hidk := hk i
      have hjdl := hl j
      have key : (fun z => expoInd f θ i dk z * expoInd f θ j dl z
            * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                / propPairCross D f θ i j dk dl)
            * ((Yobs y f θ i z / prop D f θ i dk) * (Yobs y f θ j z / prop D f θ j dl)))
          = (fun z => (((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                / propPairCross D f θ i j dk dl)
                * ((prop D f θ i dk)⁻¹ * (prop D f θ j dl)⁻¹))
              * (expoInd f θ i dk z * expoInd f θ j dl z
                  * Yobs y f θ i z * Yobs y f θ j z)) := by
        funext z; ring
      rw [key, D.E_const_mul]
      have hprod : D.E (fun z => expoInd f θ i dk z * expoInd f θ j dl z
            * Yobs y f θ i z * Yobs y f θ j z)
          = y i dk * y j dl * propPairCross D f θ i j dk dl := by
        rw [D.E_congr (Y := fun z => (y i dk * y j dl)
            * (expoInd f θ i dk z * expoInd f θ j dl z)) (fun z => ?_)]
        · rw [D.E_const_mul]; rfl
        · have h1 : expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z
              = expoInd f θ i dk z * expoInd f θ j dl z * y i dk :=
            expoInd₂_mul_Yobs y f θ i j dk dl z
          have h2 : expoInd f θ j dl z * expoInd f θ i dk z * Yobs y f θ j z
              = expoInd f θ j dl z * expoInd f θ i dk z * y j dl :=
            expoInd₂_mul_Yobs y f θ j i dl dk z
          calc expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z * Yobs y f θ j z
              = (expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z) * Yobs y f θ j z := by
                  ring
            _ = (expoInd f θ i dk z * expoInd f θ j dl z * y i dk) * Yobs y f θ j z := by rw [h1]
            _ = y i dk * (expoInd f θ j dl z * expoInd f θ i dk z * Yobs y f θ j z) := by ring
            _ = y i dk * (expoInd f θ j dl z * expoInd f θ i dk z * y j dl) := by rw [h2]
            _ = (y i dk * y j dl) * (expoInd f θ i dk z * expoInd f θ j dl z) := by ring
      rw [hprod]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc,
        mul_div_assoc, mul_div_assoc, div_self hjoint_ij]
      ring
    · -- diagonal correction sum
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [D.E_add]
      have hidk := hk i
      have hidl := hl i
      congr 1
      · have key : (fun z => expoInd f θ i dk z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dk))
            = (fun z => (2 * prop D f θ i dk)⁻¹ * (expoInd f θ i dk z * (Yobs y f θ i z) ^ 2)) := by
          funext z; rw [div_eq_mul_inv]; ring
        rw [key, D.E_const_mul,
          D.E_congr (Y := fun z => expoInd f θ i dk z * (y i dk) ^ 2)
            (fun z => expoInd_mul_Yobs_sq y f θ i dk z),
          D.E_mul_const, E_expoInd]
        rw [mul_inv,
          show (2:ℝ)⁻¹ * (prop D f θ i dk)⁻¹ * (prop D f θ i dk * y i dk ^ 2)
            = (2:ℝ)⁻¹ * y i dk ^ 2 * ((prop D f θ i dk)⁻¹ * prop D f θ i dk) by ring,
          inv_mul_cancel₀ hidk]
        ring
      · have key : (fun z => expoInd f θ i dl z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dl))
            = (fun z => (2 * prop D f θ i dl)⁻¹ * (expoInd f θ i dl z * (Yobs y f θ i z) ^ 2)) := by
          funext z; rw [div_eq_mul_inv]; ring
        rw [key, D.E_const_mul,
          D.E_congr (Y := fun z => expoInd f θ i dl z * (y i dl) ^ 2)
            (fun z => expoInd_mul_Yobs_sq y f θ i dl z),
          D.E_mul_const, E_expoInd]
        rw [mul_inv,
          show (2:ℝ)⁻¹ * (prop D f θ i dl)⁻¹ * (prop D f θ i dl * y i dl ^ 2)
            = (2:ℝ)⁻¹ * y i dl ^ 2 * ((prop D f θ i dl)⁻¹ * prop D f θ i dl) by ring,
          inv_mul_cancel₀ hidl]
        ring
  rw [hE]
  -- now: offdiag - ∑ ((y dk)²+(y dl)²)/2 ≤ offdiag - ∑ y dk y dl
  apply sub_le_sub_left
  -- ∑ y dk y dl ≤ ∑ ((y dk)²+(y dl)²)/2, termwise via Young's inequality
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  refine Finset.sum_induction _ (0 ≤ ·) (fun a b ha hb => add_nonneg ha hb) le_rfl
    (fun i _ => ?_)
  rw [show y i dk ^ 2 / 2 + y i dl ^ 2 / 2 - y i dk * y i dl = (y i dk - y i dl) ^ 2 / 2 by ring]
  exact div_nonneg (sq_nonneg _) (by norm_num)

/-- **Proposition 5.7 (`consvar`).** In the positive-joint regime, the assembled effect-variance
estimator has nonnegative bias: its expectation is at least the true variance of `τ̂`. -/
theorem E_htEffectVarEst_ge (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hne : dk ≠ dl)
    (hk : ∀ i, prop D f θ i dk ≠ 0) (hl : ∀ i, prop D f θ i dl ≠ 0)
    (hjk : ∀ i j, i ≠ j → propPairSame D f θ i j dk ≠ 0)
    (hjl : ∀ i j, i ≠ j → propPairSame D f θ i j dl ≠ 0)
    (hjc : ∀ i j, i ≠ j → propPairCross D f θ i j dk dl ≠ 0) :
    D.Var (htEffect D y f θ dk dl) ≤ D.E (htEffectVarEst D y f θ dk dl) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  -- Variance of the effect estimator in terms of the totals' moments.
  have hVar : D.Var (htEffect D y f θ dk dl)
      = N⁻¹ ^ 2 * (D.Var (htTotal D y f θ dk) + D.Var (htTotal D y f θ dl)
          - 2 * D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl)) := by
    rw [D.Var_congr (Y := fun z => N⁻¹ * (htTotal D y f θ dk z - htTotal D y f θ dl z))
        (fun z => by unfold htEffect htMean; rw [div_eq_mul_inv, div_eq_mul_inv]; ring)]
    rw [FiniteDesign.Var_const_mul, FiniteDesign.Var_sub]
  -- Expectation of the variance estimator in terms of the same moments.
  have hE : D.E (htEffectVarEst D y f θ dk dl)
      = N⁻¹ ^ 2 * (D.Var (htTotal D y f θ dk) + D.Var (htTotal D y f θ dl)
          - 2 * D.E (htCovEst D y f θ dk dl)) := by
    rw [D.E_congr (Y := fun z => N⁻¹ ^ 2 *
        (htVarEst D y f θ dk z + htVarEst D y f θ dl z - 2 * htCovEst D y f θ dk dl z))
        (fun z => by unfold htEffectVarEst; rw [div_eq_mul_inv, mul_comm, ← hN]; ring)]
    rw [D.E_const_mul]
    congr 1
    rw [D.E_sub, D.E_add, D.E_const_mul,
      E_htVarEst D y f θ dk hk hjk, E_htVarEst D y f θ dl hl hjl]
  rw [hVar, hE]
  -- N⁻² ≥ 0, and E[htCovEst] ≤ Cov gives the bracket inequality.
  have hCov := E_htCovEst_le D y f θ dk dl hne hk hl hjc
  have hsq : (0 : ℝ) ≤ N⁻¹ ^ 2 := sq_nonneg _
  apply mul_le_mul_of_nonneg_left _ hsq
  -- a + b - 2 Cov ≤ a + b - 2 E[htCovEst]  since E[htCovEst] ≤ Cov
  have h2 : (2 : ℝ) * D.E (htCovEst D y f θ dk dl)
      ≤ 2 * D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl) := by
    apply mul_le_mul_of_nonneg_left hCov
    norm_num
  exact sub_le_sub_left h2 (D.Var (htTotal D y f θ dk) + D.Var (htTotal D y f θ dl))

/-- **Proposition 5.2 (`varbias`).** Without the positive-joint assumption (only `π_i(d) ≠ 0`),
the HT variance estimator differs from the true variance by the signed zero-joint correction
`A = ∑_{π_{ij}(d)=0} y_i(d) y_j(d)`.  For a pair with `π_{ij}(d)=0`
the off-diagonal factor `(π_{ij}−π_iπ_j)/π_{ij}` in `htVarEst` is `0` in Lean (division by
zero), so the pair is dropped, whereas the true variance carries `−π_iπ_j·(y_i/π_i)(y_j/π_j)
= −y_i y_j`; the resulting bias is `A`. -/
theorem E_htVarEst_eq_addBias (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (hpos : ∀ i, prop D f θ i d ≠ 0) :
    D.E (htVarEst D y f θ d)
      = D.Var (htTotal D y f θ d)
        + ∑ i, ∑ j ∈ Finset.univ.erase i,
            (if propPairSame D f θ i j d = 0 then (1:ℝ) else 0) * (y i d * y j d) := by
  rw [Var_htTotal]
  unfold htVarEst
  rw [D.E_add, D.E_sum, D.E_sum]
  -- The diagonal sums coincide; the off-diagonal sums differ by the zero-joint correction.
  rw [add_assoc]
  congr 1
  · -- diagonal sum (identical to `E_htVarEst`)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have key : (fun z => expoInd f θ i d z * (1 - prop D f θ i d)
          * (Yobs y f θ i z / prop D f θ i d) ^ 2)
        = (fun z => ((1 - prop D f θ i d) * (prop D f θ i d)⁻¹ ^ 2)
            * (expoInd f θ i d z * (Yobs y f θ i z) ^ 2)) := by
      funext z; rw [div_pow]; ring
    rw [key, D.E_const_mul]
    rw [D.E_congr (Y := fun z => expoInd f θ i d z * (y i d) ^ 2)
        (fun z => expoInd_mul_Yobs_sq y f θ i d z)]
    rw [D.E_mul_const, E_expoInd]
    ring
  · -- off-diagonal: combine the estimator's off-diagonal expectation with the bias term,
    -- and show the result equals the true off-diagonal sum.
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [D.E_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hij : i ≠ j := fun h => hji h.symm
    have hi := hpos i
    have hjp := hpos j
    -- compute the expectation of the estimator's off-diagonal term
    have key : (fun z => expoInd f θ i d z * expoInd f θ j d z
          * ((propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d)
              / propPairSame D f θ i j d)
          * ((Yobs y f θ i z / prop D f θ i d) * (Yobs y f θ j z / prop D f θ j d)))
        = (fun z => (((propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d)
              / propPairSame D f θ i j d) * ((prop D f θ i d)⁻¹ * (prop D f θ j d)⁻¹))
            * (expoInd f θ i d z * expoInd f θ j d z
                * Yobs y f θ i z * Yobs y f θ j z)) := by
      funext z; ring
    rw [key, D.E_const_mul]
    have hprod : D.E (fun z => expoInd f θ i d z * expoInd f θ j d z
          * Yobs y f θ i z * Yobs y f θ j z)
        = y i d * y j d * propPairSame D f θ i j d := by
      rw [D.E_congr (Y := fun z => (y i d * y j d)
          * (expoInd f θ i d z * expoInd f θ j d z)) (fun z => ?_)]
      · rw [D.E_const_mul]; rfl
      · have h1 : expoInd f θ i d z * expoInd f θ j d z * Yobs y f θ i z
            = expoInd f θ i d z * expoInd f θ j d z * y i d :=
          expoInd₂_mul_Yobs y f θ i j d d z
        have h2 : expoInd f θ j d z * expoInd f θ i d z * Yobs y f θ j z
            = expoInd f θ j d z * expoInd f θ i d z * y j d :=
          expoInd₂_mul_Yobs y f θ j i d d z
        calc expoInd f θ i d z * expoInd f θ j d z * Yobs y f θ i z * Yobs y f θ j z
            = (expoInd f θ i d z * expoInd f θ j d z * Yobs y f θ i z) * Yobs y f θ j z := by ring
          _ = (expoInd f θ i d z * expoInd f θ j d z * y i d) * Yobs y f θ j z := by rw [h1]
          _ = y i d * (expoInd f θ j d z * expoInd f θ i d z * Yobs y f θ j z) := by ring
          _ = y i d * (expoInd f θ j d z * expoInd f θ i d z * y j d) := by rw [h2]
          _ = (y i d * y j d) * (expoInd f θ i d z * expoInd f θ j d z) := by ring
    rw [hprod]
    -- now case split on whether the joint probability vanishes
    by_cases hz : propPairSame D f θ i j d = 0
    · rw [if_pos hz, hz]
      -- estimator term vanishes (the `* (yᵢyⱼ * 0)` factor); true off-diagonal term is `−yᵢyⱼ`,
      -- the bias term `+ yᵢyⱼ` exactly cancels it, both sides equal `0`.
      rw [mul_zero, mul_zero, zero_sub, one_mul]
      field_simp
      ring
    · rw [if_neg hz, zero_mul, add_zero]
      -- estimator term equals true off-diagonal term (positive-joint cancellation)
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc,
        mul_div_assoc, mul_div_assoc, div_self hz]
      ring

/-- Young-inequality correction `Â₂` (eq for Prop 5.3): for each zero-joint pair
`(i,j)` with `π_{ij}(d)=0`, it adds the diagonal Young terms
`1(expo i=d)·(Yobs i)²/(2π_i) + 1(expo j=d)·(Yobs j)²/(2π_j)`, whose expectation is
`y_i(d)²/2 + y_j(d)²/2`.  Added to `htVarEst`, it makes the estimator conservative even
when some joint exposure probabilities vanish. -/
noncomputable def htA2 (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (z : Ω) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    (if propPairSame D f θ i j d = 0 then (1:ℝ) else 0)
      * (expoInd f θ i d z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i d)
          + expoInd f θ j d z * (Yobs y f θ j z) ^ 2 / (2 * prop D f θ j d))

/-- **Proposition 5.3 (`a2`).** With only `π_i(d) ≠ 0`, adding the Young correction `Â₂`
makes the variance estimator conservative: `Var[ŷᵀ(d)] ≤ E[V̂ + Â₂]`.  Indeed
`E[V̂+Â₂] = Var + A + E[Â₂] = Var + ∑_{π_{ij}=0} (y_i+y_j)²/2 ≥ Var`. -/
theorem E_htVarEst_add_htA2_ge (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (hpos : ∀ i, prop D f θ i d ≠ 0) :
    D.Var (htTotal D y f θ d)
      ≤ D.E (fun z => htVarEst D y f θ d z + htA2 D y f θ d z) := by
  rw [D.E_add, E_htVarEst_eq_addBias D y f θ d hpos]
  -- E[Â₂] = ∑_{π_{ij}=0} (y_i²/2 + y_j²/2)
  have hEA2 : D.E (htA2 D y f θ d)
      = ∑ i, ∑ j ∈ Finset.univ.erase i,
          (if propPairSame D f θ i j d = 0 then (1:ℝ) else 0)
            * ((y i d) ^ 2 / 2 + (y j d) ^ 2 / 2) := by
    unfold htA2
    rw [D.E_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [D.E_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hi := hpos i
    have hjp := hpos j
    have key : (fun z => (if propPairSame D f θ i j d = 0 then (1:ℝ) else 0)
          * (expoInd f θ i d z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i d)
              + expoInd f θ j d z * (Yobs y f θ j z) ^ 2 / (2 * prop D f θ j d)))
        = (fun z => (if propPairSame D f θ i j d = 0 then (1:ℝ) else 0)
            * ((2 * prop D f θ i d)⁻¹ * (expoInd f θ i d z * (Yobs y f θ i z) ^ 2)
                + (2 * prop D f θ j d)⁻¹ * (expoInd f θ j d z * (Yobs y f θ j z) ^ 2))) := by
      funext z; rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [key, D.E_const_mul, D.E_add, D.E_const_mul, D.E_const_mul,
      D.E_congr (Y := fun z => expoInd f θ i d z * (y i d) ^ 2)
        (fun z => expoInd_mul_Yobs_sq y f θ i d z),
      D.E_congr (X := fun z => expoInd f θ j d z * (Yobs y f θ j z) ^ 2)
        (Y := fun z => expoInd f θ j d z * (y j d) ^ 2)
        (fun z => expoInd_mul_Yobs_sq y f θ j d z),
      D.E_mul_const, D.E_mul_const, E_expoInd, E_expoInd]
    rw [mul_inv, mul_inv]
    congr 1
    rw [show (2:ℝ)⁻¹ * (prop D f θ i d)⁻¹ * (prop D f θ i d * y i d ^ 2)
          = (2:ℝ)⁻¹ * y i d ^ 2 * ((prop D f θ i d)⁻¹ * prop D f θ i d) by ring,
      inv_mul_cancel₀ hi,
      show (2:ℝ)⁻¹ * (prop D f θ j d)⁻¹ * (prop D f θ j d * y j d ^ 2)
          = (2:ℝ)⁻¹ * y j d ^ 2 * ((prop D f θ j d)⁻¹ * prop D f θ j d) by ring,
      inv_mul_cancel₀ hjp]
    ring
  rw [hEA2]
  -- Var + A + E[Â₂] = Var + ∑_{zero}(y_i+y_j)²/2 ≥ Var
  rw [add_assoc]
  apply le_add_of_nonneg_right
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_nonneg (fun j _ => ?_)
  by_cases hz : propPairSame D f θ i j d = 0
  · rw [if_pos hz, one_mul, one_mul,
      show y i d * y j d + (y i d ^ 2 / 2 + y j d ^ 2 / 2) = (y i d + y j d) ^ 2 / 2 by ring]
    exact div_nonneg (sq_nonneg _) (by norm_num)
  · rw [if_neg hz, zero_mul, zero_mul, add_zero]

/-- **Proposition 5.5 (`no_bias_cov`).** In the positive marginal and positive cross-joint regime,
when the two exposures share the same potential outcomes (`y_i(dk) = y_i(dl)` for all `i`), the
HT covariance estimator is exactly unbiased: the Young diagonal correction
`(y_i²/2 + y_i²/2) = y_i² = y_i(dk)y_i(dl)` is exact, so the nonpositive bias of Prop 5.4
vanishes. -/
theorem E_htCovEst_eq_of_noEffect (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ)
    (θ : ι → Θ) (dk dl : Δ) (hne : dk ≠ dl)
    (hk : ∀ i, prop D f θ i dk ≠ 0) (hl : ∀ i, prop D f θ i dl ≠ 0)
    (hjc : ∀ i j, i ≠ j → propPairCross D f θ i j dk dl ≠ 0)
    (heq : ∀ i, y i dk = y i dl) :
    D.E (htCovEst D y f θ dk dl) = D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl) := by
  rw [Cov_htTotal D y f θ dk dl hne hk hl]
  have hE : D.E (htCovEst D y f θ dk dl)
      = (∑ i, ∑ j ∈ Finset.univ.erase i,
            (propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
              * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl)))
        - ∑ i, ((y i dk) ^ 2 / 2 + (y i dl) ^ 2 / 2) := by
    unfold htCovEst
    rw [D.E_sub, D.E_sum, D.E_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [D.E_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hij : i ≠ j := fun h => hji h.symm
      have hjoint_ij := hjc i j hij
      have hidk := hk i
      have hjdl := hl j
      have key : (fun z => expoInd f θ i dk z * expoInd f θ j dl z
            * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                / propPairCross D f θ i j dk dl)
            * ((Yobs y f θ i z / prop D f θ i dk) * (Yobs y f θ j z / prop D f θ j dl)))
          = (fun z => (((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                / propPairCross D f θ i j dk dl)
                * ((prop D f θ i dk)⁻¹ * (prop D f θ j dl)⁻¹))
              * (expoInd f θ i dk z * expoInd f θ j dl z
                  * Yobs y f θ i z * Yobs y f θ j z)) := by
        funext z; ring
      rw [key, D.E_const_mul]
      have hprod : D.E (fun z => expoInd f θ i dk z * expoInd f θ j dl z
            * Yobs y f θ i z * Yobs y f θ j z)
          = y i dk * y j dl * propPairCross D f θ i j dk dl := by
        rw [D.E_congr (Y := fun z => (y i dk * y j dl)
            * (expoInd f θ i dk z * expoInd f θ j dl z)) (fun z => ?_)]
        · rw [D.E_const_mul]; rfl
        · have h1 : expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z
              = expoInd f θ i dk z * expoInd f θ j dl z * y i dk :=
            expoInd₂_mul_Yobs y f θ i j dk dl z
          have h2 : expoInd f θ j dl z * expoInd f θ i dk z * Yobs y f θ j z
              = expoInd f θ j dl z * expoInd f θ i dk z * y j dl :=
            expoInd₂_mul_Yobs y f θ j i dl dk z
          calc expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z * Yobs y f θ j z
              = (expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z) * Yobs y f θ j z := by
                  ring
            _ = (expoInd f θ i dk z * expoInd f θ j dl z * y i dk) * Yobs y f θ j z := by rw [h1]
            _ = y i dk * (expoInd f θ j dl z * expoInd f θ i dk z * Yobs y f θ j z) := by ring
            _ = y i dk * (expoInd f θ j dl z * expoInd f θ i dk z * y j dl) := by rw [h2]
            _ = (y i dk * y j dl) * (expoInd f θ i dk z * expoInd f θ j dl z) := by ring
      rw [hprod]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc,
        mul_div_assoc, mul_div_assoc, div_self hjoint_ij]
      ring
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [D.E_add]
      have hidk := hk i
      have hidl := hl i
      congr 1
      · have key : (fun z => expoInd f θ i dk z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dk))
            = (fun z => (2 * prop D f θ i dk)⁻¹ * (expoInd f θ i dk z * (Yobs y f θ i z) ^ 2)) := by
          funext z; rw [div_eq_mul_inv]; ring
        rw [key, D.E_const_mul,
          D.E_congr (Y := fun z => expoInd f θ i dk z * (y i dk) ^ 2)
            (fun z => expoInd_mul_Yobs_sq y f θ i dk z),
          D.E_mul_const, E_expoInd]
        rw [mul_inv,
          show (2:ℝ)⁻¹ * (prop D f θ i dk)⁻¹ * (prop D f θ i dk * y i dk ^ 2)
            = (2:ℝ)⁻¹ * y i dk ^ 2 * ((prop D f θ i dk)⁻¹ * prop D f θ i dk) by ring,
          inv_mul_cancel₀ hidk]
        ring
      · have key : (fun z => expoInd f θ i dl z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dl))
            = (fun z => (2 * prop D f θ i dl)⁻¹ * (expoInd f θ i dl z * (Yobs y f θ i z) ^ 2)) := by
          funext z; rw [div_eq_mul_inv]; ring
        rw [key, D.E_const_mul,
          D.E_congr (Y := fun z => expoInd f θ i dl z * (y i dl) ^ 2)
            (fun z => expoInd_mul_Yobs_sq y f θ i dl z),
          D.E_mul_const, E_expoInd]
        rw [mul_inv,
          show (2:ℝ)⁻¹ * (prop D f θ i dl)⁻¹ * (prop D f θ i dl * y i dl ^ 2)
            = (2:ℝ)⁻¹ * y i dl ^ 2 * ((prop D f θ i dl)⁻¹ * prop D f θ i dl) by ring,
          inv_mul_cancel₀ hidl]
        ring
  rw [hE]
  -- the diagonal correction equals ∑ y_i(dk) y_i(dl) exactly under `heq`
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [heq i]; ring

/-- General Horvitz–Thompson covariance estimator (`eq:ht_cov_general_estimator`),
handling zero cross-joint exposure probabilities.  The first double sum (over `j ≠ i`)
keeps `π_{ij}(d_k,d_l) > 0` pairs via `/π_{ij}` (zero-joint pairs drop, `x/0 = 0`); the
subtracted Young correction ranges over *all* `j ∈ U` with `π_{ij}(d_k,d_l) = 0`,
including the diagonal `j = i` (always zero since `d_k ≠ d_l`), which recovers the
positive-joint estimator's diagonal correction. -/
noncomputable def htCovEstA (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (z : Ω) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i,
      expoInd f θ i dk z * expoInd f θ j dl z
        * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
            / propPairCross D f θ i j dk dl)
        * ((Yobs y f θ i z / prop D f θ i dk) * (Yobs y f θ j z / prop D f θ j dl)))
  - ∑ i, ∑ j, (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
      * (expoInd f θ i dk z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dk)
          + expoInd f θ j dl z * (Yobs y f θ j z) ^ 2 / (2 * prop D f θ j dl))

/-- **Proposition 5.6 (`cova`).** The general covariance estimator `Ĉov_A` is nonpositively
biased for the true covariance, with NO positive-cross-joint assumption.  Zero-cross-joint
off-diagonal pairs drop from the first sum, while the Young correction (over all `j` with
`π_{ij}(d_k,d_l)=0`, including the diagonal) dominates the corresponding `−y_i(d_k)y_j(d_l)`
covariance contributions termwise via `y_i(d_k)y_j(d_l) ≤ y_i(d_k)²/2 + y_j(d_l)²/2`. -/
theorem E_htCovEstA_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hne : dk ≠ dl) (hk : ∀ i, prop D f θ i dk ≠ 0) (hl : ∀ i, prop D f θ i dl ≠ 0) :
    D.E (htCovEstA D y f θ dk dl) ≤ D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl) := by
  rw [Cov_htTotal D y f θ dk dl hne hk hl]
  -- expectation of the general covariance estimator
  have hE : D.E (htCovEstA D y f θ dk dl)
      = (∑ i, ∑ j ∈ Finset.univ.erase i,
            (if propPairCross D f θ i j dk dl = 0 then (0:ℝ) else 1)
              * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                  * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl))))
        - ∑ i, ∑ j, (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
            * ((y i dk) ^ 2 / 2 + (y j dl) ^ 2 / 2) := by
    unfold htCovEstA
    rw [D.E_sub, D.E_sum, D.E_sum]
    congr 1
    · -- first (off-diagonal) sum
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [D.E_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hij : i ≠ j := fun h => hji h.symm
      have hidk := hk i
      have hjdl := hl j
      have key : (fun z => expoInd f θ i dk z * expoInd f θ j dl z
            * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                / propPairCross D f θ i j dk dl)
            * ((Yobs y f θ i z / prop D f θ i dk) * (Yobs y f θ j z / prop D f θ j dl)))
          = (fun z => (((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                / propPairCross D f θ i j dk dl)
                * ((prop D f θ i dk)⁻¹ * (prop D f θ j dl)⁻¹))
              * (expoInd f θ i dk z * expoInd f θ j dl z
                  * Yobs y f θ i z * Yobs y f θ j z)) := by
        funext z; ring
      rw [key, D.E_const_mul]
      have hprod : D.E (fun z => expoInd f θ i dk z * expoInd f θ j dl z
            * Yobs y f θ i z * Yobs y f θ j z)
          = y i dk * y j dl * propPairCross D f θ i j dk dl := by
        rw [D.E_congr (Y := fun z => (y i dk * y j dl)
            * (expoInd f θ i dk z * expoInd f θ j dl z)) (fun z => ?_)]
        · rw [D.E_const_mul]; rfl
        · have h1 : expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z
              = expoInd f θ i dk z * expoInd f θ j dl z * y i dk :=
            expoInd₂_mul_Yobs y f θ i j dk dl z
          have h2 : expoInd f θ j dl z * expoInd f θ i dk z * Yobs y f θ j z
              = expoInd f θ j dl z * expoInd f θ i dk z * y j dl :=
            expoInd₂_mul_Yobs y f θ j i dl dk z
          calc expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z * Yobs y f θ j z
              = (expoInd f θ i dk z * expoInd f θ j dl z * Yobs y f θ i z) * Yobs y f θ j z := by
                  ring
            _ = (expoInd f θ i dk z * expoInd f θ j dl z * y i dk) * Yobs y f θ j z := by rw [h1]
            _ = y i dk * (expoInd f θ j dl z * expoInd f θ i dk z * Yobs y f θ j z) := by ring
            _ = y i dk * (expoInd f θ j dl z * expoInd f θ i dk z * y j dl) := by rw [h2]
            _ = (y i dk * y j dl) * (expoInd f θ i dk z * expoInd f θ j dl z) := by ring
      rw [hprod]
      by_cases hz : propPairCross D f θ i j dk dl = 0
      · rw [if_pos hz, zero_mul, hz, mul_zero, mul_zero]
      · rw [if_neg hz, one_mul]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc,
          mul_div_assoc, mul_div_assoc, div_self hz]
        ring
    · -- Young correction sum (over all j)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [D.E_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hidk := hk i
      have hjdl := hl j
      have key : (fun z => (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
            * (expoInd f θ i dk z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dk)
                + expoInd f θ j dl z * (Yobs y f θ j z) ^ 2 / (2 * prop D f θ j dl)))
          = (fun z => (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
              * ((2 * prop D f θ i dk)⁻¹ * (expoInd f θ i dk z * (Yobs y f θ i z) ^ 2)
                  + (2 * prop D f θ j dl)⁻¹ * (expoInd f θ j dl z * (Yobs y f θ j z) ^ 2))) := by
        funext z; rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [key, D.E_const_mul, D.E_add, D.E_const_mul, D.E_const_mul,
        D.E_congr (Y := fun z => expoInd f θ i dk z * (y i dk) ^ 2)
          (fun z => expoInd_mul_Yobs_sq y f θ i dk z),
        D.E_congr (X := fun z => expoInd f θ j dl z * (Yobs y f θ j z) ^ 2)
          (Y := fun z => expoInd f θ j dl z * (y j dl) ^ 2)
          (fun z => expoInd_mul_Yobs_sq y f θ j dl z),
        D.E_mul_const, D.E_mul_const, E_expoInd, E_expoInd]
      rw [mul_inv, mul_inv]
      congr 1
      rw [show (2:ℝ)⁻¹ * (prop D f θ i dk)⁻¹ * (prop D f θ i dk * y i dk ^ 2)
            = (2:ℝ)⁻¹ * y i dk ^ 2 * ((prop D f θ i dk)⁻¹ * prop D f θ i dk) by ring,
        inv_mul_cancel₀ hidk,
        show (2:ℝ)⁻¹ * (prop D f θ j dl)⁻¹ * (prop D f θ j dl * y j dl ^ 2)
            = (2:ℝ)⁻¹ * y j dl ^ 2 * ((prop D f θ j dl)⁻¹ * prop D f θ j dl) by ring,
        inv_mul_cancel₀ hjdl]
      ring
  rw [hE]
  -- Compare to eq:totals_covariance: it suffices to show
  --   Cov - E[htCovEstA] = ∑_diag Young-gap + ∑_offdiag Young-gap ≥ 0.
  rw [← sub_nonneg]
  -- Rewrite the goal's Cov first sum (full off-diagonal) by splitting on π_{ij}=0.
  have hsplit : (∑ i, ∑ j ∈ Finset.univ.erase i,
        (propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
          * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl)))
      = (∑ i, ∑ j ∈ Finset.univ.erase i,
          (if propPairCross D f θ i j dk dl = 0 then (0:ℝ) else 1)
            * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
                * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl))))
        + ∑ i, ∑ j ∈ Finset.univ.erase i,
            (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
              * (- (y i dk * y j dl)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hidk := hk i
    have hjdl := hl j
    by_cases hz : propPairCross D f θ i j dk dl = 0
    · rw [if_pos hz, if_pos hz, zero_mul, zero_add, one_mul, hz]
      field_simp
      ring
    · rw [if_neg hz, if_neg hz, one_mul, zero_mul, add_zero]
  rw [hsplit]
  -- Split the all-j Young sum into diagonal (j=i) and off-diagonal (j≠i).
  have hYoung : (∑ i, ∑ j, (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
          * ((y i dk) ^ 2 / 2 + (y j dl) ^ 2 / 2))
      = (∑ i, ((y i dk) ^ 2 / 2 + (y i dl) ^ 2 / 2))
        + ∑ i, ∑ j ∈ Finset.univ.erase i,
            (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
              * ((y i dk) ^ 2 / 2 + (y j dl) ^ 2 / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    -- diagonal j = i: indicator is 1 since π_{ii}(dk,dl)=0
    rw [propPairCross_self_of_ne D f θ i hne, if_pos rfl, one_mul]
  rw [hYoung]
  -- Name the off-diagonal positive-joint sum `P` (it cancels) and reduce to a gap of
  -- nonnegative diagonal + off-diagonal Young corrections.
  set P : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i,
      (if propPairCross D f θ i j dk dl = 0 then (0:ℝ) else 1)
        * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
            * ((y i dk / prop D f θ i dk) * (y j dl / prop D f θ j dl))) with hP
  -- Goal: 0 ≤ (P + Negyy) - (Diagyy + (P - (Diagyoung + Offyoung)))
  rw [show P + (∑ i, ∑ j ∈ Finset.univ.erase i,
            (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0) * (- (y i dk * y j dl)))
          - (∑ i, y i dk * y i dl)
          - (P - (∑ i, ((y i dk) ^ 2 / 2 + (y i dl) ^ 2 / 2)
                  + ∑ i, ∑ j ∈ Finset.univ.erase i,
                      (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
                        * ((y i dk) ^ 2 / 2 + (y j dl) ^ 2 / 2)))
        = (∑ i, ((y i dk) ^ 2 / 2 + (y i dl) ^ 2 / 2) - ∑ i, y i dk * y i dl)
          + (∑ i, ∑ j ∈ Finset.univ.erase i,
                (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0)
                  * ((y i dk) ^ 2 / 2 + (y j dl) ^ 2 / 2)
            + ∑ i, ∑ j ∈ Finset.univ.erase i,
                (if propPairCross D f θ i j dk dl = 0 then (1:ℝ) else 0) * (- (y i dk * y j dl)))
        by ring]
  apply add_nonneg
  · -- diagonal gaps: ∑ᵢ (yᵢdk²/2 + yᵢdl²/2) - ∑ᵢ yᵢdkyᵢdl ≥ 0
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [show (y i dk) ^ 2 / 2 + (y i dl) ^ 2 / 2 - y i dk * y i dl
          = (y i dk - y i dl) ^ 2 / 2 by ring]
    exact div_nonneg (sq_nonneg _) (by norm_num)
  · -- off-diagonal gaps
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg (fun j _ => ?_)
    by_cases hz : propPairCross D f θ i j dk dl = 0
    · rw [if_pos hz, one_mul, one_mul,
        show (y i dk) ^ 2 / 2 + (y j dl) ^ 2 / 2 + - (y i dk * y j dl)
          = (y i dk - y j dl) ^ 2 / 2 by ring]
      exact div_nonneg (sq_nonneg _) (by norm_num)
    · rw [if_neg hz, zero_mul, zero_mul, add_zero]

/-- General conservative variance estimator for `Var[τ̂(dk,dl)]` (`eq:ate_var_estimator`),
assembling the zero-joint-robust variance corrections `Â₂` and the general covariance
estimator `Ĉov_A`. -/
noncomputable def htEffectVarEstA (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ)
    (θ : ι → Θ) (dk dl : Δ) (z : Ω) : ℝ :=
  (htVarEst D y f θ dk z + htA2 D y f θ dk z + htVarEst D y f θ dl z + htA2 D y f θ dl z
      - 2 * htCovEstA D y f θ dk dl z)
    / (Fintype.card ι : ℝ) ^ 2

/-- **Proposition 5.7, general form (`consvar`).** Without any positive-joint assumption
(only `π_i(d) ≠ 0`), the assembled general effect-variance estimator has nonnegative bias:
its expectation is at least the true variance of `τ̂`.  Follows from Proposition 5.3 (twice)
and Proposition 5.6 by linearity of expectation. -/
theorem E_htEffectVarEstA_ge (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hne : dk ≠ dl)
    (hk : ∀ i, prop D f θ i dk ≠ 0) (hl : ∀ i, prop D f θ i dl ≠ 0) :
    D.Var (htEffect D y f θ dk dl) ≤ D.E (htEffectVarEstA D y f θ dk dl) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  -- Variance of the effect estimator in terms of the totals' moments.
  have hVar : D.Var (htEffect D y f θ dk dl)
      = N⁻¹ ^ 2 * (D.Var (htTotal D y f θ dk) + D.Var (htTotal D y f θ dl)
          - 2 * D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl)) := by
    rw [D.Var_congr (Y := fun z => N⁻¹ * (htTotal D y f θ dk z - htTotal D y f θ dl z))
        (fun z => by unfold htEffect htMean; rw [div_eq_mul_inv, div_eq_mul_inv]; ring)]
    rw [FiniteDesign.Var_const_mul, FiniteDesign.Var_sub]
  -- Expectation of the variance estimator in terms of the corrected moments.
  have hE : D.E (htEffectVarEstA D y f θ dk dl)
      = N⁻¹ ^ 2 * (D.E (fun z => htVarEst D y f θ dk z + htA2 D y f θ dk z)
          + D.E (fun z => htVarEst D y f θ dl z + htA2 D y f θ dl z)
          - 2 * D.E (htCovEstA D y f θ dk dl)) := by
    rw [D.E_congr (Y := fun z => N⁻¹ ^ 2 *
        ((htVarEst D y f θ dk z + htA2 D y f θ dk z)
          + (htVarEst D y f θ dl z + htA2 D y f θ dl z) - 2 * htCovEstA D y f θ dk dl z))
        (fun z => by unfold htEffectVarEstA; rw [div_eq_mul_inv, mul_comm, ← hN]; ring)]
    rw [D.E_const_mul]
    congr 1
    rw [D.E_sub, D.E_add, D.E_const_mul]
  rw [hVar, hE]
  -- N⁻² ≥ 0; Prop 5.3 twice and Prop 5.6 bound the bracket.
  have hsq : (0 : ℝ) ≤ N⁻¹ ^ 2 := sq_nonneg _
  apply mul_le_mul_of_nonneg_left _ hsq
  have hAk := E_htVarEst_add_htA2_ge D y f θ dk hk
  have hAl := E_htVarEst_add_htA2_ge D y f θ dl hl
  have hCov := E_htCovEstA_le D y f θ dk dl hne hk hl
  have h2 : (2 : ℝ) * D.E (htCovEstA D y f θ dk dl)
      ≤ 2 * D.Cov (htTotal D y f θ dk) (htTotal D y f θ dl) :=
    mul_le_mul_of_nonneg_left hCov (by norm_num)
  -- Var dk + Var dl - 2 Cov ≤ E[V̂dk+Â₂dk] + E[V̂dl+Â₂dl] - 2 E[Ĉov_A]
  exact sub_le_sub (add_le_add hAk hAl) h2

end ExposureMappingInterference
end Experimentation
end Causalean
