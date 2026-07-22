/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative
import Causalean.Experimentation.DesignBased.EdgeVarianceBound

/-!
# Quadruple-sum variance bound for the conservative variance estimator (Aronow–Samii Prop 6.6)

The feasible Wald-coverage theorem reduces, via `relVar_of_NsqVar_tendsto`, to `Var[N·V̂] → 0`.
This file establishes the *per-population* core of that limit, the appendix quadruple-sum bound

    Var[ V̂_raw ]  ≤  8·M²·m³·N,        V̂_raw = ŷVar(dk) + ŷVar(dl) − 2·Ĉov,

where `V̂ = N⁻²·V̂_raw` (so `Var[N·V̂] = N⁻²·Var[V̂_raw] ≤ 8M²m³/N`).  The estimator `V̂_raw` is
rewritten as a single **edge-sum** `∑_{i,j} vb i j` over ordered pairs (diagonal `i=j` folds in
the three single-index sums; off-diagonal folds the three pairwise sums), and the abstract
`var_edge_sum_le` is applied with:

* boundedness `|vb i j z| ≤ M` from **Condition 1** (bounded outcomes/inverse-propensities) plus
  the explicit joint-overlap bound **Condition 1'** (`1/π_{ij} ≤ c₃` on all ordered pairs — the
  quantitative input the paper's appendix uses implicitly);
* off-edge vanishing `vb i j = 0` for non-adjacent `i ≠ j`, since then the exposures are
  independent and the centered-cross factors `π_{ij} − π_iπ_j = Cov[1ᵢ,1ⱼ]` vanish;
* edge-covariance vanishing `Cov[vb i j, vb k l] = 0` for graph-unlinked edge pairs — the
  **Condition 3** (local dependence / dependency graph) input, in the form the appendix uses.
-/


open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Δ]

/-! ### Edge-function decomposition of `V̂_raw` -/

/-- Diagonal (variance) summand of `ŷVar(d)`: `1ᵢ(d)·(1−πᵢ)·(Yᵢ/πᵢ)²`. -/
noncomputable def diagVar (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (i : ι) (z : Ω) : ℝ :=
  expoInd f θ i d z * (1 - prop D f θ i d) * (Yobs y f θ i z / prop D f θ i d) ^ 2

/-- Off-diagonal (variance) summand of `ŷVar(d)`. -/
noncomputable def offVar (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (i j : ι) (z : Ω) : ℝ :=
  expoInd f θ i d z * expoInd f θ j d z
    * ((propPairSame D f θ i j d - prop D f θ i d * prop D f θ j d) / propPairSame D f θ i j d)
    * (Yobs y f θ i z / prop D f θ i d * (Yobs y f θ j z / prop D f θ j d))

/-- Off-diagonal summand of the covariance estimator `Ĉov`. -/
noncomputable def offCov (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (i j : ι) (z : Ω) : ℝ :=
  expoInd f θ i dk z * expoInd f θ j dl z
    * ((propPairCross D f θ i j dk dl - prop D f θ i dk * prop D f θ j dl)
        / propPairCross D f θ i j dk dl)
    * (Yobs y f θ i z / prop D f θ i dk * (Yobs y f θ j z / prop D f θ j dl))

/-- Diagonal (Young) correction summand of `Ĉov`. -/
noncomputable def diagCov (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (i : ι) (z : Ω) : ℝ :=
  expoInd f θ i dk z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dk)
    + expoInd f θ i dl z * (Yobs y f θ i z) ^ 2 / (2 * prop D f θ i dl)

/-- Diagonal edge term: `diagVar(dk) + diagVar(dl) + 2·diagCov`. -/
noncomputable def vbDiag (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (i : ι) (z : Ω) : ℝ :=
  diagVar D y f θ dk i z + diagVar D y f θ dl i z + 2 * diagCov D y f θ dk dl i z

/-- Off-diagonal edge term: `offVar(dk) + offVar(dl) − 2·offCov`. -/
noncomputable def vbOff (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (i j : ι) (z : Ω) : ℝ :=
  offVar D y f θ dk i j z + offVar D y f θ dl i j z - 2 * offCov D y f θ dk dl i j z

/-- The edge-function for `V̂_raw`: diagonal term on `i = j`, off-diagonal term otherwise. -/
noncomputable def vb (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (i j : ι) (z : Ω) : ℝ :=
  if i = j then vbDiag D y f θ dk dl i z else vbOff D y f θ dk dl i j z

/-- Uniform pointwise bound on the edge-function, from Conditions 1 and 1'.  Chosen large enough
to dominate both the squared inverse-propensity terms (`∝ c₂²`) and the Young-correction terms
(`∝ c₂`), uniformly in the joint-overlap constant `c₃`. -/
noncomputable def vbBound (c₁ c₂ c₃ : ℝ) : ℝ :=
  4 * (1 + c₃) * c₁ ^ 2 * (c₂ ^ 2 + c₂)

/-! ### The per-population quadruple-sum bound -/

/-- **Edge-sum identity.** `V̂_raw = ∑_{i,j} vb i j`: the three single-index sums of
`ŷVar(dk)`, `ŷVar(dl)`, `Ĉov` fold into the diagonal `i = j`, and the three pairwise sums into
the off-diagonal `i ≠ j`. -/
theorem htVarEst_add_sub_eq_edgeSum (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ)
    (θ : ι → Θ) (dk dl : Δ) :
    (fun z => htVarEst D y f θ dk z + htVarEst D y f θ dl z - 2 * htCovEst D y f θ dk dl z)
      = (fun z => ∑ i, ∑ j, vb D y f θ dk dl i j z) := by
  funext z
  -- Split each inner edge-sum into the diagonal term (`i = j`) plus the off-diagonal remainder.
  have hRHS : (∑ i, ∑ j, vb D y f θ dk dl i j z)
      = (∑ i, vbDiag D y f θ dk dl i z)
        + (∑ i, ∑ j ∈ Finset.univ.erase i, vbOff D y f θ dk dl i j z) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.add_sum_erase Finset.univ (fun j => vb D y f θ dk dl i j z) (mem_univ i)]
    congr 1
    · rw [vb, if_pos rfl]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [vb, if_neg ((Finset.mem_erase.mp hj).1).symm]
  rw [hRHS]
  unfold htVarEst htCovEst vbDiag vbOff diagVar offVar offCov diagCov
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- `0 ≤ expoInd f θ i d z ≤ 1`: the exposure indicator is a 0/1 quantity. -/
private lemma abs_expoInd_le_one (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) (z : Ω) :
    |expoInd f θ i d z| ≤ 1 :=
  abs_le.mpr ⟨le_trans (by norm_num) (FiniteDesign.ind_nonneg _ z), FiniteDesign.ind_le_one _ z⟩

/-- The exposure indicator is idempotent: `(1ᵢ(d))² = 1ᵢ(d)`. -/
private lemma expoInd_sq (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) (z : Ω) :
    (expoInd f θ i d z) ^ 2 = expoInd f θ i d z :=
  congrFun (FiniteDesign.ind_sq (fun z => expo f θ i z = d)) z

/-- The propensity `prop` lies in `[0,1]`: it is a probability. -/
private lemma prop_mem_unit (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) :
    0 ≤ prop D f θ i d ∧ prop D f θ i d ≤ 1 :=
  ⟨D.Pr_nonneg _, D.Pr_le_one _⟩

/-- `propPairSame` is nonnegative (expectation of a product of two indicators). -/
private lemma propPairSame_nonneg (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i j : ι)
    (d : Δ) : 0 ≤ propPairSame D f θ i j d :=
  D.E_nonneg (fun z => mul_nonneg (FiniteDesign.ind_nonneg _ z) (FiniteDesign.ind_nonneg _ z))

/-- `propPairCross` is nonnegative (expectation of a product of two indicators). -/
private lemma propPairCross_nonneg (D : FiniteDesign Ω) (f : Ω → Θ → Δ) (θ : ι → Θ) (i j : ι)
    (d d' : Δ) : 0 ≤ propPairCross D f θ i j d d' :=
  D.E_nonneg (fun z => mul_nonneg (FiniteDesign.ind_nonneg _ z) (FiniteDesign.ind_nonneg _ z))

/-- **Inverse-propensity-weighted summand bound.** The weighted observed outcome
`1ₐ(d)·(Yₐ/πₐ)` is bounded by `c₁·c₂` whenever outcomes are bounded by `c₁` and the inverse
propensity by `c₂`. -/
private lemma abs_expoInd_Yobs_div_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ)
    (θ : ι → Θ) (a : ι) (d : Δ) (z : Ω) {c₁ c₂ : ℝ}
    (hy : ∀ i d, |y i d| ≤ c₁) (hπ : 0 < prop D f θ a d) (hπinv : 1 / prop D f θ a d ≤ c₂) :
    |expoInd f θ a d z * (Yobs y f θ a z / prop D f θ a d)| ≤ c₁ * c₂ := by
  have hc₁ : 0 ≤ c₁ := le_trans (abs_nonneg _) (hy a d)
  rw [mul_div_assoc', expoInd_mul_Yobs, abs_div, abs_of_pos hπ, abs_mul]
  -- `|1ₐ| · |y a d| / π ≤ c₁ / π = c₁ · (1/π) ≤ c₁ · c₂`
  have hnum : |expoInd f θ a d z| * |y a d| ≤ c₁ := by
    calc |expoInd f θ a d z| * |y a d| ≤ 1 * c₁ :=
          mul_le_mul (abs_expoInd_le_one f θ a d z) (hy a d) (abs_nonneg _) (by norm_num)
      _ = c₁ := one_mul c₁
  rw [div_le_iff₀ hπ]
  calc |expoInd f θ a d z| * |y a d| ≤ c₁ := hnum
    _ = c₁ * (1 / prop D f θ a d) * prop D f θ a d := by field_simp
    _ ≤ c₁ * c₂ * prop D f θ a d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hπinv hc₁) (le_of_lt hπ)

/-- **Centered-cross coefficient bound.** For a joint propensity `P ≥ 0` with `1/P ≤ c₃` and
marginal propensities `πᵢ, πⱼ ∈ [0,1]`, the centered factor `(P − πᵢπⱼ)/P` is at most `1 + c₃`. -/
private lemma abs_centered_coeff_le {P πi πj c₃ : ℝ} (hP : 0 ≤ P) (hPinv : 1 / P ≤ c₃)
    (hπi0 : 0 ≤ πi) (hπi1 : πi ≤ 1) (hπj0 : 0 ≤ πj) (hπj1 : πj ≤ 1) (hc₃ : 0 ≤ c₃) :
    |(P - πi * πj) / P| ≤ 1 + c₃ := by
  rcases eq_or_lt_of_le hP with hP0 | hPpos
  · -- `P = 0`: the quotient is `0` by `div_zero`.
    rw [← hP0, div_zero, abs_zero]; linarith
  · have hPpos := hPpos
    have hprodnn : 0 ≤ πi * πj := mul_nonneg hπi0 hπj0
    have hprod1 : πi * πj ≤ 1 := mul_le_one₀ hπi1 hπj0 hπj1
    have hsplit : (P - πi * πj) / P = 1 - (πi * πj) / P := by field_simp
    rw [hsplit]
    have hq0 : 0 ≤ (πi * πj) / P := div_nonneg hprodnn (le_of_lt hPpos)
    have hqle : (πi * πj) / P ≤ c₃ := by
      rw [div_eq_mul_one_div]
      calc πi * πj * (1 / P) ≤ 1 * c₃ :=
            mul_le_mul hprod1 hPinv (by positivity) (by norm_num)
        _ = c₃ := one_mul c₃
    rw [abs_le]; constructor <;> linarith

/-- **Diagonal-variance summand bound.** `|diagVar d a z| ≤ c₁²·c₂²`. -/
private lemma abs_diagVar_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (a : ι) (z : Ω) {c₁ c₂ : ℝ} (hy : ∀ i d, |y i d| ≤ c₁)
    (hπ : 0 < prop D f θ a d) (hπ1 : prop D f θ a d ≤ 1) (hπinv : 1 / prop D f θ a d ≤ c₂) :
    |diagVar D y f θ d a z| ≤ c₁ ^ 2 * c₂ ^ 2 := by
  have hAsq : (expoInd f θ a d z * (Yobs y f θ a z / prop D f θ a d)) ^ 2 ≤ (c₁ * c₂) ^ 2 := by
    have hA := abs_expoInd_Yobs_div_le D y f θ a d z hy hπ hπinv
    exact sq_le_sq' (by linarith [(abs_le.mp hA).1]) (abs_le.mp hA).2
  -- `diagVar = (1-π)·(1ₐ·(Yₐ/π))²`, using indicator idempotence.
  have hrw : diagVar D y f θ d a z
      = (1 - prop D f θ a d) * (expoInd f θ a d z * (Yobs y f θ a z / prop D f θ a d)) ^ 2 := by
    unfold diagVar
    rw [mul_pow, expoInd_sq]; ring
  rw [hrw, abs_mul,
    abs_of_nonneg (sq_nonneg (expoInd f θ a d z * (Yobs y f θ a z / prop D f θ a d)))]
  have hcoeff : |1 - prop D f θ a d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc |1 - prop D f θ a d| * (expoInd f θ a d z * (Yobs y f θ a z / prop D f θ a d)) ^ 2
      ≤ 1 * (c₁ * c₂) ^ 2 :=
        mul_le_mul hcoeff hAsq (sq_nonneg _) (by norm_num)
    _ = c₁ ^ 2 * c₂ ^ 2 := by ring

/-- **Young-correction summand bound.** `|diagCov dk dl a z| ≤ 2·c₁²·c₂`. -/
private lemma abs_diagCov_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (a : ι) (z : Ω) {c₁ c₂ : ℝ} (hy : ∀ i d, |y i d| ≤ c₁)
    (hπk : 0 < prop D f θ a dk) (hπl : 0 < prop D f θ a dl)
    (hπinvk : 1 / prop D f θ a dk ≤ c₂) (hπinvl : 1 / prop D f θ a dl ≤ c₂) :
    |diagCov D y f θ dk dl a z| ≤ 2 * c₁ ^ 2 * c₂ := by
  -- Each Young term `1ₐ·Yₐ²/(2π) ≤ c₁²·(1/(2π)) ≤ c₁²·c₂`.
  have hterm : ∀ d, 0 < prop D f θ a d → 1 / prop D f θ a d ≤ c₂ →
      |expoInd f θ a d z * (Yobs y f θ a z) ^ 2 / (2 * prop D f θ a d)| ≤ c₁ ^ 2 * c₂ := by
    intro d hπ hπinv
    rw [expoInd_mul_Yobs_sq, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * prop D f θ a d),
      div_le_iff₀ (by positivity : (0:ℝ) < 2 * prop D f θ a d)]
    have hnum : |expoInd f θ a d z * y a d ^ 2| ≤ c₁ ^ 2 := by
      rw [abs_mul, abs_pow]
      calc |expoInd f θ a d z| * |y a d| ^ 2 ≤ 1 * c₁ ^ 2 :=
            mul_le_mul (abs_expoInd_le_one f θ a d z)
              (pow_le_pow_left₀ (abs_nonneg _) (hy a d) 2) (by positivity) (by norm_num)
        _ = c₁ ^ 2 := one_mul _
    calc |expoInd f θ a d z * y a d ^ 2| ≤ c₁ ^ 2 := hnum
      _ = c₁ ^ 2 * (1 / prop D f θ a d) * prop D f θ a d := by field_simp
      _ ≤ c₁ ^ 2 * c₂ * prop D f θ a d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hπinv (sq_nonneg _)) (le_of_lt hπ)
      _ = c₁ ^ 2 * c₂ * (2 * prop D f θ a d) - c₁ ^ 2 * c₂ * prop D f θ a d := by ring
      _ ≤ c₁ ^ 2 * c₂ * (2 * prop D f θ a d) := by
          have : 0 ≤ c₁ ^ 2 * c₂ * prop D f θ a d :=
            mul_nonneg (mul_nonneg (sq_nonneg _) (le_trans (by positivity) hπinv)) (le_of_lt hπ)
          linarith
  unfold diagCov
  calc |expoInd f θ a dk z * Yobs y f θ a z ^ 2 / (2 * prop D f θ a dk)
          + expoInd f θ a dl z * Yobs y f θ a z ^ 2 / (2 * prop D f θ a dl)|
      ≤ |expoInd f θ a dk z * Yobs y f θ a z ^ 2 / (2 * prop D f θ a dk)|
        + |expoInd f θ a dl z * Yobs y f θ a z ^ 2 / (2 * prop D f θ a dl)| := abs_add_le _ _
    _ ≤ c₁ ^ 2 * c₂ + c₁ ^ 2 * c₂ := add_le_add (hterm dk hπk hπinvk) (hterm dl hπl hπinvl)
    _ = 2 * c₁ ^ 2 * c₂ := by ring

/-- **Off-diagonal variance summand bound.** `|offVar d i j z| ≤ (1+c₃)·c₁²·c₂²`. -/
private lemma abs_offVar_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (d : Δ) (i j : ι) (z : Ω) {c₁ c₂ c₃ : ℝ} (hc₃ : 0 ≤ c₃) (hy : ∀ i d, |y i d| ≤ c₁)
    (hπi : 0 < prop D f θ i d) (hπj : 0 < prop D f θ j d)
    (hπi1 : prop D f θ i d ≤ 1) (hπj1 : prop D f θ j d ≤ 1)
    (hπinvi : 1 / prop D f θ i d ≤ c₂) (hπinvj : 1 / prop D f θ j d ≤ c₂)
    (hj : 1 / propPairSame D f θ i j d ≤ c₃) :
    |offVar D y f θ d i j z| ≤ (1 + c₃) * c₁ ^ 2 * c₂ ^ 2 := by
  set P := propPairSame D f θ i j d
  set ri := expoInd f θ i d z * (Yobs y f θ i z / prop D f θ i d) with hri
  set rj := expoInd f θ j d z * (Yobs y f θ j z / prop D f θ j d) with hrj
  have hcoeff := abs_centered_coeff_le (propPairSame_nonneg D f θ i j d) hj
    (le_of_lt hπi) hπi1 (le_of_lt hπj) hπj1 hc₃
  have hAi := abs_expoInd_Yobs_div_le D y f θ i d z hy hπi hπinvi
  have hAj := abs_expoInd_Yobs_div_le D y f θ j d z hy hπj hπinvj
  have hrearr : offVar D y f θ d i j z = ri * rj * ((P - prop D f θ i d * prop D f θ j d) / P) := by
    unfold offVar; rw [hri, hrj]; ring
  rw [hrearr, abs_mul, abs_mul]
  have hc₁c₂ : 0 ≤ c₁ * c₂ := le_trans (abs_nonneg _) hAi
  calc |ri| * |rj| * |(P - prop D f θ i d * prop D f θ j d) / P|
      ≤ (c₁ * c₂) * (c₁ * c₂) * (1 + c₃) :=
        mul_le_mul (mul_le_mul hAi hAj (abs_nonneg _) hc₁c₂) hcoeff (abs_nonneg _)
          (mul_nonneg hc₁c₂ hc₁c₂)
    _ = (1 + c₃) * c₁ ^ 2 * c₂ ^ 2 := by ring

/-- **Off-diagonal covariance summand bound.** `|offCov dk dl i j z| ≤ (1+c₃)·c₁²·c₂²`. -/
private lemma abs_offCov_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (i j : ι) (z : Ω) {c₁ c₂ c₃ : ℝ} (hc₃ : 0 ≤ c₃) (hy : ∀ i d, |y i d| ≤ c₁)
    (hπi : 0 < prop D f θ i dk) (hπj : 0 < prop D f θ j dl)
    (hπi1 : prop D f θ i dk ≤ 1) (hπj1 : prop D f θ j dl ≤ 1)
    (hπinvi : 1 / prop D f θ i dk ≤ c₂) (hπinvj : 1 / prop D f θ j dl ≤ c₂)
    (hj : 1 / propPairCross D f θ i j dk dl ≤ c₃) :
    |offCov D y f θ dk dl i j z| ≤ (1 + c₃) * c₁ ^ 2 * c₂ ^ 2 := by
  set P := propPairCross D f θ i j dk dl
  set ri := expoInd f θ i dk z * (Yobs y f θ i z / prop D f θ i dk) with hri
  set rj := expoInd f θ j dl z * (Yobs y f θ j z / prop D f θ j dl) with hrj
  have hcoeff := abs_centered_coeff_le (propPairCross_nonneg D f θ i j dk dl) hj
    (le_of_lt hπi) hπi1 (le_of_lt hπj) hπj1 hc₃
  have hAi := abs_expoInd_Yobs_div_le D y f θ i dk z hy hπi hπinvi
  have hAj := abs_expoInd_Yobs_div_le D y f θ j dl z hy hπj hπinvj
  have hrearr : offCov D y f θ dk dl i j z
      = ri * rj * ((P - prop D f θ i dk * prop D f θ j dl) / P) := by
    unfold offCov; rw [hri, hrj]; ring
  rw [hrearr, abs_mul, abs_mul]
  have hc₁c₂ : 0 ≤ c₁ * c₂ := le_trans (abs_nonneg _) hAi
  calc |ri| * |rj| * |(P - prop D f θ i dk * prop D f θ j dl) / P|
      ≤ (c₁ * c₂) * (c₁ * c₂) * (1 + c₃) :=
        mul_le_mul (mul_le_mul hAi hAj (abs_nonneg _) hc₁c₂) hcoeff (abs_nonneg _)
          (mul_nonneg hc₁c₂ hc₁c₂)
    _ = (1 + c₃) * c₁ ^ 2 * c₂ ^ 2 := by ring

/-- **Boundedness of the edge-function** (Conditions 1 + 1'): `|vb i j z| ≤ vbBound c₁ c₂ c₃`. -/
theorem abs_vb_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hne : dk ≠ dl)
    {c₁ c₂ c₃ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hy : ∀ i d, |y i d| ≤ c₁)
    (hπk : ∀ i, 0 < prop D f θ i dk) (hπl : ∀ i, 0 < prop D f θ i dl)
    (hπinvk : ∀ i, 1 / prop D f θ i dk ≤ c₂) (hπinvl : ∀ i, 1 / prop D f θ i dl ≤ c₂)
    (hjk : ∀ i j, 1 / propPairSame D f θ i j dk ≤ c₃)
    (hjl : ∀ i j, 1 / propPairSame D f θ i j dl ≤ c₃)
    (hjc : ∀ i j, 1 / propPairCross D f θ i j dk dl ≤ c₃)
    (i j : ι) (z : Ω) :
    |vb D y f θ dk dl i j z| ≤ vbBound c₁ c₂ c₃ := by
  -- Marginal propensities are at most `1` (used to bound `1 - π` and `πᵢ·πⱼ`).
  have hπk1 : ∀ a, prop D f θ a dk ≤ 1 := fun a => (prop_mem_unit D f θ a dk).2
  have hπl1 : ∀ a, prop D f θ a dl ≤ 1 := fun a => (prop_mem_unit D f θ a dl).2
  unfold vb
  split_ifs with hij
  · -- Diagonal case `i = j`.
    unfold vbDiag
    have hbk := abs_diagVar_le D y f θ dk i z hy (hπk i) (hπk1 i) (hπinvk i)
    have hbl := abs_diagVar_le D y f θ dl i z hy (hπl i) (hπl1 i) (hπinvl i)
    have hbc := abs_diagCov_le D y f θ dk dl i z hy (hπk i) (hπl i) (hπinvk i) (hπinvl i)
    have htri :
        |diagVar D y f θ dk i z + diagVar D y f θ dl i z + 2 * diagCov D y f θ dk dl i z|
          ≤ |diagVar D y f θ dk i z| + |diagVar D y f θ dl i z|
            + 2 * |diagCov D y f θ dk dl i z| := by
      refine le_trans (abs_add_le _ _) ?_
      gcongr
      · exact abs_add_le _ _
      · rw [abs_mul]; simp
    refine le_trans htri ?_
    -- `c₁²c₂² + c₁²c₂² + 2·(2c₁²c₂) = 2c₁²c₂² + 4c₁²c₂ ≤ vbBound`.
    have hsum : |diagVar D y f θ dk i z| + |diagVar D y f θ dl i z|
        + 2 * |diagCov D y f θ dk dl i z|
        ≤ c₁ ^ 2 * c₂ ^ 2 + c₁ ^ 2 * c₂ ^ 2 + 2 * (2 * c₁ ^ 2 * c₂) := by
      gcongr
    refine le_trans hsum ?_
    unfold vbBound
    nlinarith [sq_nonneg c₁, hc₂, hc₃, mul_nonneg (sq_nonneg c₁) hc₂,
      mul_nonneg (mul_nonneg (sq_nonneg c₁) hc₂) hc₃,
      mul_nonneg (mul_nonneg (sq_nonneg c₁) hc₂) hc₂,
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg c₁) hc₂) hc₂) hc₃]
  · -- Off-diagonal case `i ≠ j`.
    unfold vbOff
    have hvk := abs_offVar_le D y f θ dk i j z hc₃ hy (hπk i) (hπk j) (hπk1 i) (hπk1 j)
      (hπinvk i) (hπinvk j) (hjk i j)
    have hvl := abs_offVar_le D y f θ dl i j z hc₃ hy (hπl i) (hπl j) (hπl1 i) (hπl1 j)
      (hπinvl i) (hπinvl j) (hjl i j)
    have hcv := abs_offCov_le D y f θ dk dl i j z hc₃ hy (hπk i) (hπl j) (hπk1 i) (hπl1 j)
      (hπinvk i) (hπinvl j) (hjc i j)
    have htri :
        |offVar D y f θ dk i j z + offVar D y f θ dl i j z - 2 * offCov D y f θ dk dl i j z|
          ≤ |offVar D y f θ dk i j z| + |offVar D y f θ dl i j z|
            + 2 * |offCov D y f θ dk dl i j z| := by
      refine le_trans (abs_sub _ _) ?_
      gcongr
      · exact abs_add_le _ _
      · rw [abs_mul]; simp
    refine le_trans htri ?_
    have hsum : |offVar D y f θ dk i j z| + |offVar D y f θ dl i j z|
        + 2 * |offCov D y f θ dk dl i j z|
        ≤ (1 + c₃) * c₁ ^ 2 * c₂ ^ 2 + (1 + c₃) * c₁ ^ 2 * c₂ ^ 2
          + 2 * ((1 + c₃) * c₁ ^ 2 * c₂ ^ 2) := by gcongr
    refine le_trans hsum ?_
    unfold vbBound
    nlinarith [sq_nonneg c₁, hc₂, hc₃, mul_nonneg (sq_nonneg c₁) hc₂,
      mul_nonneg (mul_nonneg (sq_nonneg c₁) hc₂) hc₃,
      mul_nonneg (mul_nonneg (sq_nonneg c₁) (sq_nonneg c₂)) (by linarith : (0:ℝ) ≤ 1 + c₃)]

/-- **Off-edge vanishing.** If the same-exposure and cross-exposure pair propensities factor as
products for an off-diagonal pair `i ≠ j`, then the centered-cross factors vanish and
`vb i j = 0`; Condition 3 supplies these factorization hypotheses for non-adjacent pairs. -/
theorem vb_eq_zero_of_indep (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (i j : ι) (hij : i ≠ j)
    (hsame_k : propPairSame D f θ i j dk = prop D f θ i dk * prop D f θ j dk)
    (hsame_l : propPairSame D f θ i j dl = prop D f θ i dl * prop D f θ j dl)
    (hcross : propPairCross D f θ i j dk dl = prop D f θ i dk * prop D f θ j dl) :
    vb D y f θ dk dl i j = fun _ => 0 := by
  funext z
  rw [vb, if_neg hij, vbOff, offVar, offVar, offCov, hsame_k, hsame_l, hcross]
  ring

/-- **Per-population quadruple-sum bound (Aronow–Samii appendix, Prop 6.6).** Under Condition 1
(`hy`/`hπinv*`), Condition 1' (`hj*`: joint overlap on all ordered pairs), and Condition 3 (the
symmetric bounded-degree dependency graph `G` with off-edge exposure independence `hGindep` and
unlinked-edge covariance vanishing `hcov0`), the variance of the raw conservative variance
estimator is linear in the population size:
`Var[ŷVar(dk)+ŷVar(dl)−2Ĉov] ≤ 8·(vbBound c₁ c₂ c₃)²·m³·N`. -/
theorem var_htEdgeStat_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ)
    (dk dl : Δ) (hne : dk ≠ dl)
    {c₁ c₂ c₃ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hy : ∀ i d, |y i d| ≤ c₁)
    (hπk : ∀ i, 0 < prop D f θ i dk) (hπl : ∀ i, 0 < prop D f θ i dl)
    (hπinvk : ∀ i, 1 / prop D f θ i dk ≤ c₂) (hπinvl : ∀ i, 1 / prop D f θ i dl ≤ c₂)
    (hjk : ∀ i j, 1 / propPairSame D f θ i j dk ≤ c₃)
    (hjl : ∀ i j, 1 / propPairSame D f θ i j dl ≤ c₃)
    (hjc : ∀ i j, 1 / propPairCross D f θ i j dk dl ≤ c₃)
    (G : ι → ι → Prop) [DecidableRel G] (hrefl : ∀ i, G i i) (hsymm : ∀ i j, G i j → G j i)
    {m : ℕ} (hdeg : ∀ i, (Finset.univ.filter (fun j => G i j)).card ≤ m)
    (hGindep : ∀ i j, ¬ G i j →
        propPairSame D f θ i j dk = prop D f θ i dk * prop D f θ j dk ∧
        propPairSame D f θ i j dl = prop D f θ i dl * prop D f θ j dl ∧
        propPairCross D f θ i j dk dl = prop D f θ i dk * prop D f θ j dl)
    (hcov0 : ∀ i j k l, ¬ (G i k ∨ G i l ∨ G j k ∨ G j l) →
        D.Cov (vb D y f θ dk dl i j) (vb D y f θ dk dl k l) = 0) :
    D.Var (fun z => htVarEst D y f θ dk z + htVarEst D y f θ dl z
              - 2 * htCovEst D y f θ dk dl z)
      ≤ 8 * vbBound c₁ c₂ c₃ ^ 2 * ((m : ℝ) ^ 3 * (Fintype.card ι : ℝ)) := by
  rw [htVarEst_add_sub_eq_edgeSum]
  have hMnn : 0 ≤ vbBound c₁ c₂ c₃ := by
    unfold vbBound
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg c₁))
      (add_nonneg (sq_nonneg c₂) hc₂)
  refine D.var_edge_sum_le (vb D y f θ dk dl) hMnn ?_ G hsymm hdeg ?_ hcov0
  · exact fun i j z => abs_vb_le D y f θ dk dl hne hc₁ hc₂ hc₃ hy hπk hπl hπinvk hπinvl
      hjk hjl hjc i j z
  · intro i j hGij
    rcases eq_or_ne i j with rfl | hij
    · exact absurd (hrefl i) hGij
    · obtain ⟨hsk, hsl, hc⟩ := hGindep i j hGij
      exact vb_eq_zero_of_indep D y f θ dk dl i j hij hsk hsl hc

end ExposureMappingInterference
end Experimentation
end Causalean
