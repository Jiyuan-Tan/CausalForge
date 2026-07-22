/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Joint asymptotic normality of a finite vector of sample quantiles

For finitely many interior levels `τ : Fin k → ℝ` with population quantiles
`q : Fin k → ℝ` (`F(qⱼ) = τⱼ`) and densities `f : Fin k → ℝ` (`fⱼ > 0`), the
vector of sample quantiles is jointly asymptotically normal:

    √n ( q̂ₙ(τⱼ) − qⱼ )_{j}  ⇒  N(0, Σ),
    Σ_{jl}  =  (min(τⱼ, τₗ) − τⱼ τₗ) / (fⱼ fₗ).

This is the multivariate counterpart of `Stat/SampleQuantileBahadur.lean`'s
scalar CLT, assembled from:

* the per-coordinate **derived** Bahadur representation
  (`IIDSample.sampleQuantile_isAsymLinear`), packaged into the vector
  asymptotic-linearity predicate `IsAsymLinearVec`;
* the project's **multivariate CLT** (`IsAsymLinearVec.tendsto_normal_vec_clt`,
  Cramér–Wold) consuming the joint influence function
  `ψ(z)_j = (τⱼ − 1{z ≤ qⱼ}) / fⱼ`;
* the indicator cross-moment `∫ ψⱼ ψₗ dP = (min(τⱼ,τₗ) − τⱼτₗ)/(fⱼfₗ)`
  identifying the limiting covariance `Σ`.

As elsewhere in the multivariate-CLT stack (`Stat/MultivariateCLT.lean`,
`Stat/GaussianCharFunBridge.lean`), the target law `Q` is kept abstract via its
characteristic function `charFun Q t = exp(−½ ∫⟪t,ψ⟫² dP)`; the covariance
lemma `quantileIFVec_cross` identifies `∫⟪t,ψ⟫² dP = tᵀ Σ t` with the `Σ` above.

References: van der Vaart (1998) §21 (joint quantile CLT).
-/

import Causalean.Stat.Quantile.SampleQuantileBahadur
import Causalean.Stat.CLT.MultivariateCLT
import Causalean.Stat.CLT.GaussianCharFunBridge
import Causalean.Stat.Limit.Convergence

/-! # Joint Normality of a Quantile Vector

This file proves joint asymptotic normality for a finite vector of sample
quantiles. It packages the coordinatewise Bahadur representations into vector
asymptotic linearity and uses the multivariate CLT to obtain an abstract
Gaussian limit with covariance entries determined by quantile influence-function
cross-moments. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}
  {k : ℕ}

/-- Pack a coordinate function into Euclidean space (the `PiLp 2` synonym). -/
noncomputable abbrev eucl (v : Fin k → ℝ) : EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm v

/-! ## Joint influence function and estimator vector -/

/-- The **joint quantile influence function**
`ψ(z)_j = (τⱼ − 1{z ≤ qⱼ}) / fⱼ`, valued in `EuclideanSpace ℝ (Fin k)`. -/
noncomputable def quantileIFVec (τ q f : Fin k → ℝ) : ℝ → EuclideanSpace ℝ (Fin k) :=
  fun z => eucl (fun j => quantileIF (τ j) (q j) (f j) z)

/-- The **sample-quantile vector** `(q̂ₙ(τ₁), …, q̂ₙ(τ_k))`. -/
noncomputable def IIDSample.sampleQuantileVec (S : IIDSample Ω ℝ μ P) (τ : Fin k → ℝ) :
    ℕ → Ω → EuclideanSpace ℝ (Fin k) :=
  fun n ω => eucl (fun j => S.sampleQuantile (τ j) n ω)

/-- The joint quantile influence function is measurable. -/
lemma measurable_quantileIFVec (τ q f : Fin k → ℝ) : Measurable (quantileIFVec τ q f) := by
  unfold quantileIFVec eucl
  refine ((EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.measurable).comp ?_
  exact measurable_pi_lambda _ (fun j => measurable_quantileIF (τ j) (q j) (f j))

/-! ## Limiting covariance: indicator cross-moment -/

/-- **Covariance entry.**  The cross-moment of two quantile influence functions:

    ∫ ψ_{τⱼ} ψ_{τₗ} dP  =  (min(τⱼ, τₗ) − τⱼ τₗ) / (fⱼ fₗ).

Uses `∫ 1{z ≤ qⱼ} 1{z ≤ qₗ} dP = F(min(qⱼ,qₗ)) = min(τⱼ,τₗ)` (the last equality
by monotonicity of the cdf together with `F(qᵢ) = τᵢ`). -/
lemma quantileIF_cross [IsProbabilityMeasure P] {τj qj fj τl ql fl : ℝ}
    (hj : cdf P qj = τj) (hl : cdf P ql = τl) :
    ∫ z, quantileIF τj qj fj z * quantileIF τl ql fl z ∂P
      = (min τj τl - τj * τl) / (fj * fl) := by
  -- Product of two lower-ray indicators is the indicator of the smaller ray.
  have hprod : ∀ z, cdfStat qj z * cdfStat ql z = cdfStat (min qj ql) z := by
    intro z
    simp only [cdfStat, Set.indicator_apply, Set.mem_Iic, le_min_iff]
    by_cases hzj : z ≤ qj <;> by_cases hzl : z ≤ ql <;> simp [hzj, hzl]
  -- The cdf of the min equals the min of the cdfs (by monotonicity).
  have hmin : cdf P (min qj ql) = min τj τl := by
    rcases le_total qj ql with hq | hq
    · rw [min_eq_left hq, hj, min_eq_left]
      rw [← hj, ← hl]; exact monotone_cdf P hq
    · rw [min_eq_right hq, hl, min_eq_right]
      rw [← hj, ← hl]; exact monotone_cdf P hq
  -- Expand the product of influence functions.
  have hexpand : (fun z => quantileIF τj qj fj z * quantileIF τl ql fl z)
      = (fun z => (τj * τl - τj * cdfStat ql z - τl * cdfStat qj z
          + cdfStat (min qj ql) z) / (fj * fl)) := by
    funext z
    unfold quantileIF
    rw [div_mul_div_comm, ← hprod z]; ring
  rw [hexpand]
  have hil : Integrable (cdfStat ql) P := integrable_cdfStat ql
  have hij : Integrable (cdfStat qj) P := integrable_cdfStat qj
  have him : Integrable (cdfStat (min qj ql)) P := integrable_cdfStat (min qj ql)
  rw [integral_div]
  have e1 : ∫ z, (τj * τl - τj * cdfStat ql z - τl * cdfStat qj z
      + cdfStat (min qj ql) z) ∂P
      = τj * τl - τj * cdf P ql - τl * cdf P qj + cdf P (min qj ql) := by
    have hB : Integrable (fun z => τj * τl - τj * cdfStat ql z) P :=
      (integrable_const (τj * τl)).sub (hil.const_mul τj)
    have hC : Integrable (fun z => τl * cdfStat qj z) P := hij.const_mul τl
    have hA : Integrable (fun z => τj * τl - τj * cdfStat ql z - τl * cdfStat qj z) P :=
      hB.sub hC
    rw [integral_add hA him, integral_sub hB hC,
      integral_sub (integrable_const (τj * τl)) (hil.const_mul τj)]
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_cdfStat]
  rw [e1, hl, hj, hmin]
  ring

/-! ## Vector asymptotic linearity (derived, from the per-coordinate Bahadur) -/

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- Coordinate access for `eucl`: `(eucl v) j = v j`. -/
@[simp] lemma eucl_apply (v : Fin k → ℝ) (j : Fin k) : (eucl v) j = v j := rfl

/-- Euclidean norm of a packed vector, squared, is the coordinatewise sum of
squares. -/
lemma norm_sq_eucl (v : Fin k → ℝ) : ‖eucl v‖ ^ 2 = ∑ j, (v j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  rfl

/-- The Euclidean norm of a packed vector is bounded by the `ℓ¹` norm of its
coordinates: `‖eucl v‖ ≤ ∑ j, |v j|`. -/
lemma norm_eucl_le_sum_abs (v : Fin k → ℝ) : ‖eucl v‖ ≤ ∑ j, |v j| := by
  have hnonneg : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsq : ‖eucl v‖ ^ 2 ≤ (∑ j, |v j|) ^ 2 := by
    rw [norm_sq_eucl]
    have hle : ∑ j, (v j) ^ 2 ≤ (∑ j, |v j|) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      calc (v j) ^ 2 = |v j| * |v j| := by rw [sq, ← abs_mul_abs_self]
        _ ≤ ∑ i, |v j| * |v i| := by
            refine Finset.single_le_sum (f := fun i => |v j| * |v i|)
              (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    exact hle
  exact le_of_pow_le_pow_left₀ (by norm_num) hnonneg hsq

/-- The zero sequence is `o_p(1)`. -/
lemma isLittleOp_zero_one' :
    IsLittleOp (fun _ (_ : Ω) => (0 : ℝ)) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hempty : {ω : Ω | ε * (1 : ℝ) < |(0 : ℝ)|} = (∅ : Set Ω) := by
    ext ω; simp only [abs_zero, mul_one, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hε.not_gt
  have heq : (fun _ : ℕ => μ {ω : Ω | ε * (1 : ℝ) < |(0 : ℝ)|})
      = fun _ : ℕ => (0 : ENNReal) := by
    funext n; rw [hempty, measure_empty]
  rw [show (fun n : ℕ => μ {ω : Ω | ε * (fun _ => (1 : ℝ)) n < |(fun _ _ => (0 : ℝ)) n ω|})
        = (fun _ : ℕ => μ {ω : Ω | ε * (1 : ℝ) < |(0 : ℝ)|}) from rfl, heq]
  exact tendsto_const_nhds

/-- A finite sum of `o_p(1)` sequences is `o_p(1)`. -/
lemma isLittleOp_finset_sum_one {ι : Type*} (s : Finset ι) (g : ι → ℕ → Ω → ℝ)
    (h : ∀ i ∈ s, IsLittleOp (g i) (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => ∑ i ∈ s, g i n ω) (fun _ => (1 : ℝ)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLittleOp_zero_one' (μ := μ)
  | insert a s has ih =>
      have ha := h a (Finset.mem_insert_self a s)
      have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hadd := IsLittleOp.add_one ha hs
      simpa [Finset.sum_insert has] using hadd

/-- Domination: if `|Xn| ≤ C·|Yn|` with `Yn` `o_p(1)` and `C > 0`, then `Xn` is
`o_p(1)`. -/
lemma isLittleOp_of_abs_le_const_mul_one {X Y : ℕ → Ω → ℝ} {C : ℝ}
    (hC : 0 < C) (hY : IsLittleOp Y (fun _ => (1 : ℝ)) μ)
    (hbound : ∀ n ω, |X n ω| ≤ C * |Y n ω|) :
    IsLittleOp X (fun _ => (1 : ℝ)) μ :=
  IsLittleOp.of_abs_le_const_mul_one hC hY hbound

/-- The absolute value of an `o_p(1)` sequence is `o_p(1)` (the threshold events
coincide). -/
lemma isLittleOp_abs {R : ℕ → Ω → ℝ} (hR : IsLittleOp R (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => |R n ω|) (fun _ => (1 : ℝ)) μ := by
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hR ?_
  intro n ω
  simp

/-- The sample-quantile vector is asymptotically linear with the joint influence
function `ψ`.  `mean_zero` and `finite_var` are coordinatewise reductions of the
scalar facts; the vector `remainder` is `o_p(1)` because each coordinate is the
scalar Bahadur remainder (`o_p(1)` by `sampleQuantile_isAsymLinear`) and the
Euclidean norm of a finite vector of `o_p(1)` coordinates is `o_p(1)`. -/
theorem IIDSample.sampleQuantileVec_isAsymLinearVec (S : IIDSample Ω ℝ μ P)
    {τ q f : Fin k → ℝ} (hreg : ∀ j, SampleQuantileReg P (τ j) (q j) (f j)) :
    IsAsymLinearVec (S.sampleQuantileVec τ) (eucl q) (quantileIFVec τ q f) S
      (fun m => Finset.range m) := by
  -- Per-coordinate scalar asymptotic linearity.
  set AL : ∀ j, IsAsymLinear (S.sampleQuantile (τ j)) (q j)
      (quantileIF (τ j) (q j) (f j)) S (fun m => Finset.range m) :=
    fun j => S.sampleQuantile_isAsymLinear (hreg j) with hAL
  -- The coordinate influence functions, packaged as `g x = (fun j => quantileIF…)`.
  set g : ℝ → Fin k → ℝ := fun x j => quantileIF (τ j) (q j) (f j) x with hg
  -- Coordinatewise bound used throughout.
  have hcoordbound : ∀ x j, |g x j| ≤ (|τ j| + 1) / |f j| := by
    intro x j
    have hc0 : 0 ≤ cdfStat (q j) x := cdfStat_nonneg (q j) x
    have hc1 : cdfStat (q j) x ≤ 1 := cdfStat_le_one (q j) x
    have hnum : |τ j - cdfStat (q j) x| ≤ |τ j| + 1 := by
      rw [abs_le]
      exact ⟨by have := neg_abs_le (τ j); linarith,
             by have := le_abs_self (τ j); linarith⟩
    change |quantileIF (τ j) (q j) (f j) x| ≤ _
    unfold quantileIF
    rw [abs_div, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (abs_nonneg _))
  have hg_int : Integrable g P := by
    -- bounded by a constant (sup-norm ≤ sum of coordinate bounds) on a prob. measure
    refine (integrable_const (∑ j, (|τ j| + 1) / |f j|)).mono'
      (measurable_pi_lambda _ (fun j =>
        measurable_quantileIF (τ j) (q j) (f j))).aestronglyMeasurable ?_
    filter_upwards with x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ =>
      div_nonneg (by positivity) (abs_nonneg _))).2 (fun j => ?_)
    rw [Real.norm_eq_abs]
    exact (hcoordbound x j).trans (Finset.single_le_sum
      (f := fun j => (|τ j| + 1) / |f j|)
      (fun i _ => div_nonneg (by positivity) (abs_nonneg _)) (Finset.mem_univ j))
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero : ∫ quantileIFVec = 0
    change ∫ x, eucl (g x) ∂P = 0
    rw [ContinuousLinearEquiv.integral_comp_comm (EuclideanSpace.equiv (Fin k) ℝ).symm g]
    have hzero : (∫ x, g x ∂P) = 0 := by
      funext j
      have hproj := ContinuousLinearMap.integral_comp_comm
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j) hg_int
      simp only [ContinuousLinearMap.proj_apply] at hproj
      rw [← hproj]
      exact (AL j).mean_zero
    rw [hzero, map_zero]
  · -- finite_var : ‖quantileIFVec‖² ∈ L¹(P)
    have hsum : (fun x => ‖quantileIFVec τ q f x‖ ^ 2)
        = fun x => ∑ j, (quantileIF (τ j) (q j) (f j) x) ^ 2 := by
      funext x
      exact norm_sq_eucl (g x)
    rw [hsum]
    exact integrable_finset_sum _ (fun j _ => quantileIF_sq_integrable)
  · -- remainder : the vector Bahadur remainder is o_p(1)
    -- The per-coordinate scalar remainder `Rₙⱼ`.
    set R : Fin k → ℕ → Ω → ℝ := fun j n ω =>
      Real.sqrt ((Finset.range n).card : ℝ) * (S.sampleQuantile (τ j) n ω - q j)
        - (Real.sqrt ((Finset.range n).card : ℝ))⁻¹
            * ∑ i ∈ Finset.range n, quantileIF (τ j) (q j) (f j) (S.Z i ω) with hR
    have hRlit : ∀ j, IsLittleOp (R j) (fun _ => (1 : ℝ)) μ := fun j => (AL j).remainder
    -- The vector bracket equals `eucl (fun j => R j n ω)`.
    have hbracket : ∀ n ω,
        Real.sqrt (((Finset.range n).card : ℝ)) • (S.sampleQuantileVec τ n ω - eucl q)
          - (Real.sqrt (((Finset.range n).card : ℝ)))⁻¹ •
              ∑ i ∈ Finset.range n, quantileIFVec τ q f (S.Z i ω)
          = eucl (fun j => R j n ω) := by
      intro n ω
      change Real.sqrt _ • (eucl (fun j => S.sampleQuantile (τ j) n ω) - eucl q)
          - (Real.sqrt _)⁻¹ • ∑ i ∈ Finset.range n, eucl (g (S.Z i ω))
          = eucl (fun j => R j n ω)
      rw [← map_sub, ← map_smul, ← map_sum, ← map_smul, ← map_sub]
      congr 1
      funext j
      simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hR, hg]
    -- `∑ⱼ |Rₙⱼ|` is o_p(1), and the vector norm is bounded by it.
    have hsum_lit : IsLittleOp (fun n ω => ∑ j, |R j n ω|) (fun _ => (1 : ℝ)) μ :=
      isLittleOp_finset_sum_one Finset.univ (fun j n ω => |R j n ω|)
        (fun j _ => isLittleOp_abs (hRlit j))
    refine isLittleOp_of_abs_le_const_mul_one (C := 1) one_pos hsum_lit ?_
    intro n ω
    rw [hbracket n ω]
    rw [abs_of_nonneg (norm_nonneg _), one_mul,
      abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    exact norm_eucl_le_sum_abs (fun j => R j n ω)

/-! ## Headline: joint asymptotic normality -/

/-- **Joint asymptotic normality of the sample-quantile vector.**

    √n ( q̂ₙ(τⱼ) − qⱼ )_{j}  ⇒  Q,

where the target `Q` is the centered Gaussian with `charFun Q t = exp(−½ ∫⟪t,ψ⟫² dP)`
— i.e. `N(0, Σ)` with `Σ_{jl} = (min(τⱼ,τₗ) − τⱼτₗ)/(fⱼfₗ)` (see `quantileIF_cross`).

Bahadur remainders are **derived** per coordinate (no empirical-process
hypothesis); the only inputs are the per-coordinate `SampleQuantileReg`
(interior level, positive density, cdf identification, differentiability,
atomless population) and the abstract Gaussian-charFun target, matching the rest
of the multivariate-CLT stack. -/
theorem IIDSample.sampleQuantileVec_tendsto_normal (S : IIDSample Ω ℝ μ P)
    {τ q f : Fin k → ℝ} (hreg : ∀ j, SampleQuantileReg P (τ j) (q j) (f j))
    (Q : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure Q]
    (hQ : ∀ t : EuclideanSpace ℝ (Fin k), charFun Q t
        = Complex.exp (-(((∫ z, (⟪t, quantileIFVec τ q f z⟫) ^ 2 ∂P : ℝ)) : ℂ) / 2))
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator (S.sampleQuantileVec τ) (eucl q)
        (fun m => Finset.range m) n) μ)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S (quantileIFVec τ q f) (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
      (fun n => ⟨μ.map (IsAsymLinearVec.rescaledEstimator (S.sampleQuantileVec τ)
                  (eucl q) (fun m => Finset.range m) n),
                  Measure.isProbabilityMeasure_map (hθn_meas n)⟩)
      atTop (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩) := by
  refine (S.sampleQuantileVec_isAsymLinearVec hreg).tendsto_normal_vec_clt
    (measurable_quantileIFVec τ q f) ?_ Q hQ hθn_meas hSum_meas
  -- `Integrable (quantileIFVec τ q f) P`: bounded by a constant on a probability measure.
  refine (integrable_const (Real.sqrt (∑ j, ((|τ j| + 1) / |f j|) ^ 2))).mono'
    (measurable_quantileIFVec τ q f).aestronglyMeasurable ?_
  filter_upwards with z
  -- Each coordinate is bounded by `(|τ j| + 1) / |f j|`.
  have hcoord : ∀ j, |quantileIF (τ j) (q j) (f j) z| ≤ (|τ j| + 1) / |f j| := by
    intro j
    have hc0 : 0 ≤ cdfStat (q j) z := cdfStat_nonneg (q j) z
    have hc1 : cdfStat (q j) z ≤ 1 := cdfStat_le_one (q j) z
    have hnum : |τ j - cdfStat (q j) z| ≤ |τ j| + 1 := by
      rw [abs_le]
      exact ⟨by have := neg_abs_le (τ j); linarith, by have := le_abs_self (τ j); linarith⟩
    unfold quantileIF
    rw [abs_div, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (abs_nonneg _))
  rw [show ‖quantileIFVec τ q f z‖ = ‖eucl (fun j => quantileIF (τ j) (q j) (f j) z)‖ from rfl,
    eucl, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  simp only [EuclideanSpace.equiv]
  rw [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2

end Causalean.Stat
