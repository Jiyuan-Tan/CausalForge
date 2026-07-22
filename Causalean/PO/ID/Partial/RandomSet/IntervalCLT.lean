/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Scalar interval-data CLT (Beresteanu–Molinari 2008, Theorems 3.1/3.2)

The Tier-1 capstone of the random-set program.  For an i.i.d. sample of interval
data `Yᵢ = [y_{iL}, y_{iU}]` (`y_L ≤ y_U`) with finite second moments, the
population Aumann expectation is the Manski sharp bound `E[Y] = [E y_L, E y_U]`
and the sample-mean interval is `Ȳₙ = [ȳ_{nL}, ȳ_{nU}]`.  Beresteanu–Molinari
Theorem 3.2 states

    √n · H(Ȳₙ, E[Y])  ⇒  max(|z_L|, |z_U|),

the max-abs of the bivariate Gaussian limit `(z_L, z_U)` of the centered endpoint
means.  This is a **continuous-mapping image of the multivariate CLT**: the
endpoint process `√n((ȳ_{nL}, ȳ_{nU}) − (E y_L, E y_U))` is exactly the vector
normalised sum of the centered influence function `ψ`, which converges to
`gaussianLimit ψ` (`Stat/CLT/GaussianLimit.lean`), and the Hausdorff statistic is
`maxAbs` of that vector by the keystone `hausdorffDist_Icc` (`Hausdorff.lean`).

## Main results

* `maxAbs` / `continuous_maxAbs` — the functional `w ↦ max(|w₀|, |w₁|)` on `ℝ²`.
* `normalizedSum_maxAbs_clt` — the abstract continuous-mapping CLT: `maxAbs` of the
  vector normalised sum converges to `(gaussianLimit ψ).map maxAbs`.
* `maxAbs_normalizedSum_eq` — **the Hausdorff bridge**: `maxAbs (normalised sum)`
  equals `√n · H(Ȳₙ, E[Y])`, identifying the statistic above with the Hausdorff
  distance between the sample and population identified intervals.
-/

import Causalean.PO.ID.Partial.RandomSet.Hausdorff
import Causalean.PO.ID.Partial.RandomSet.Interval
import Causalean.Stat.CLT.GaussianLimit

/-! # Scalar Interval-Data Central Limit Theorem

This file derives the central limit theorem for the Hausdorff distance between a
sample-mean interval and the population Aumann expectation interval. It reduces
the interval statistic to the maximum absolute value of the bivariate endpoint
process, allowing the library's multivariate central limit theorem and continuous
mapping machinery to apply.

Main declarations:
* `maxAbs`, `continuous_maxAbs`, and `measurable_maxAbs` define the endpoint
  functional for symmetric Hausdorff distance.
* `normalizedSum_maxAbs_clt` is the abstract continuous-mapping CLT for
  `maxAbs` of a normalized vector sum.
* `sampleMean`, `intervalIFVec`, and `maxAbs_normalizedSum_eq` connect endpoint
  sums to `sqrt n * hausdorffDist`.
* `interval_data_clt` states the scalar interval-data CLT from explicit CLT
  hypotheses.
* `interval_data_clt_of_memLp` discharges those hypotheses from measurable
  endpoints with `MemLp 2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped RealInnerProductSpace

namespace Causalean.PartialID.RandomSet

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- A pair of real endpoint deviations is viewed as a two-dimensional Euclidean
vector. -/
noncomputable abbrev eucl₂ (v : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm v

/-- The **max-abs functional** `w ↦ max(|w₀|, |w₁|)` on `ℝ²`.  In the `d = 1`
random-set picture this is the Hausdorff distance between the intervals whose
endpoint gaps are `w₀` and `w₁` (cf. `hausdorffDist_Icc`). -/
noncomputable def maxAbs (w : EuclideanSpace ℝ (Fin 2)) : ℝ := max |w 0| |w 1|

/-- The max-absolute-value functional on endpoint deviations is continuous. -/
lemma continuous_maxAbs : Continuous maxAbs := by unfold maxAbs; fun_prop

/-- The max-absolute-value functional on endpoint deviations is measurable. -/
lemma measurable_maxAbs : Measurable maxAbs := continuous_maxAbs.measurable

section CLT

variable {ψ : X → EuclideanSpace ℝ (Fin 2)} (hψ : Measurable ψ)
  (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)

/-- The limit law of the Hausdorff statistic is a probability measure (pushforward
of the Gaussian limit by the continuous `maxAbs`). -/
instance : IsProbabilityMeasure ((gaussianLimit hψ hvar).map maxAbs) :=
  Measure.isProbabilityMeasure_map measurable_maxAbs.aemeasurable

/-- **Abstract continuous-mapping CLT.**  `maxAbs` of the vector normalised sum
converges in distribution to the pushforward `(gaussianLimit ψ).map maxAbs` — the
law of `max(|z_L|, |z_U|)` for the bivariate Gaussian limit.  Immediate from the
multivariate CLT (`clt_normalizedSum_vec`) and the continuous-mapping theorem
(`Tendsto_dist_vec.map_continuous`). -/
theorem normalizedSum_maxAbs_clt
    (S : IIDSample Ω X μ P)
    (hψ_int : Integrable ψ P) (hmean : ∫ x, ψ x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n) μ) :
    Tendsto_dist_vec
      (fun n ω => maxAbs (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n ω))
      ((gaussianLimit hψ hvar).map maxAbs) μ
      (fun n => measurable_maxAbs.comp_aemeasurable (hSum_meas n)) :=
  Tendsto_dist_vec.map_continuous continuous_maxAbs hSum_meas
    (fun n => measurable_maxAbs.comp_aemeasurable (hSum_meas n))
    (S.clt_normalizedSum_vec hψ hvar hψ_int hmean hSum_meas)

end CLT

/-! ## The Hausdorff bridge: the statistic is `√n · H(Ȳₙ, E[Y])` -/

section Bridge

/-- The centered-sum / `√n` identity `(√n)⁻¹·(s − n·c) = √n·(s/n − c)`, the
algebra turning a normalised centered sum into `√n × (sample mean − population
mean)`. -/
lemma sqrt_inv_centered (n : ℕ) (s c : ℝ) :
    (Real.sqrt n)⁻¹ * (s - n * c) = Real.sqrt n * (s / n - c) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set r := Real.sqrt n with hr
    have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
    have hsq : r * r = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hnpos)
    rw [← hsq]
    field_simp

/-- Sample mean of `y` over the first `n` draws of the i.i.d. sample. -/
noncomputable def sampleMean (S : IIDSample Ω X μ P) (y : X → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, y (S.Z i ω)) / n

/-- The **centered interval-endpoint influence function**
`ψ(z) = (y_L(z) − E y_L, y_U(z) − E y_U)`, valued in `ℝ²`.  Its vector normalised
sum is the centered-and-scaled endpoint pair `√n((ȳ_{nL}, ȳ_{nU}) − (E y_L, E y_U))`. -/
noncomputable def intervalIFVec (yL yU : X → ℝ) (P : Measure X) :
    X → EuclideanSpace ℝ (Fin 2) :=
  fun z => eucl₂ ![yL z - ∫ x, yL x ∂P, yU z - ∫ x, yU x ∂P]

/-- Both coordinates of the vector normalised sum of `intervalIFVec` are
`√n · (sample mean − population mean)`. -/
private lemma normalizedSum_coord (S : IIDSample Ω X μ P) (yL yU : X → ℝ) (n : ℕ) (ω : Ω) :
    (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω) 0
        = Real.sqrt n * (sampleMean S yL n ω - ∫ x, yL x ∂P)
      ∧ (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω) 1
        = Real.sqrt n * (sampleMean S yU n ω - ∫ x, yU x ∂P) := by
  constructor
  · change ((EuclideanSpace.equiv (Fin 2) ℝ)
      (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω)) 0 = _
    unfold IsAsymLinearVec.normalizedSum intervalIFVec eucl₂
    rw [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply, Matrix.cons_val_zero, smul_eq_mul,
      Finset.card_range]
    rw [show (∑ i ∈ Finset.range n, (yL (S.Z i ω) - ∫ x, yL x ∂P))
          = (∑ i ∈ Finset.range n, yL (S.Z i ω)) - n * (∫ x, yL x ∂P) by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul],
      sqrt_inv_centered]
    simp only [sampleMean]
  · change ((EuclideanSpace.equiv (Fin 2) ℝ)
      (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω)) 1 = _
    unfold IsAsymLinearVec.normalizedSum intervalIFVec eucl₂
    rw [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      smul_eq_mul, Finset.card_range]
    rw [show (∑ i ∈ Finset.range n, (yU (S.Z i ω) - ∫ x, yU x ∂P))
          = (∑ i ∈ Finset.range n, yU (S.Z i ω)) - n * (∫ x, yU x ∂P) by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul],
      sqrt_inv_centered]
    simp only [sampleMean]

/-- The sample-mean interval is well-ordered (lower ≤ upper) when `y_L ≤ y_U`. -/
lemma sampleMean_le (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLU : ∀ z, yL z ≤ yU z) (n : ℕ) (ω : Ω) :
    sampleMean S yL n ω ≤ sampleMean S yU n ω := by
  unfold sampleMean
  gcongr with i _
  exact hLU _

/-- **The Hausdorff bridge (Beresteanu–Molinari Theorem 3.2, statistic form).**
`maxAbs` of the centered endpoint normalised sum is exactly
`√n · H(Ȳₙ, E[Y])`, the scaled Hausdorff distance between the sample-mean interval
`Ȳₙ = [ȳ_{nL}, ȳ_{nU}]` and the population identified interval `E[Y] = [E y_L, E y_U]`. -/
theorem maxAbs_normalizedSum_eq (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLU : ∀ z, yL z ≤ yU z) (hLint : Integrable yL P) (hUint : Integrable yU P)
    (n : ℕ) (ω : Ω) :
    maxAbs (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω)
      = Real.sqrt n * hausdorffDist
          (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω))
          (Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P)) := by
  obtain ⟨h0, h1⟩ := normalizedSum_coord S yL yU n ω
  unfold maxAbs
  rw [h0, h1]
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
  rw [← mul_max_of_nonneg _ _ (Real.sqrt_nonneg (n : ℝ)),
    hausdorffDist_Icc (sampleMean_le S yL yU hLU n ω)
      (integral_mono hLint hUint hLU)]

/-! ## Discharging the multivariate-CLT hypotheses from clean `MemLp 2` data -/

/-- Coordinate access for `eucl₂`: `(eucl₂ v) j = v j`. -/
@[simp] lemma eucl₂_apply (v : Fin 2 → ℝ) (j : Fin 2) : (eucl₂ v) j = v j := rfl

/-- Pointwise squared norm of the endpoint influence function as the sum of the
two squared centered endpoints. -/
lemma norm_sq_intervalIFVec (yL yU : X → ℝ) (x : X) :
    ‖intervalIFVec yL yU P x‖ ^ 2
      = (yL x - ∫ z, yL z ∂P) ^ 2 + (yU x - ∫ z, yU z ∂P) ^ 2 := by
  unfold intervalIFVec
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  rw [Fin.sum_univ_two]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, eucl₂_apply, eucl₂_apply]
  rw [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- `intervalIFVec` is measurable from measurability of the two endpoint maps. -/
lemma measurable_intervalIFVec (yL yU : X → ℝ)
    (hLmeas : Measurable yL) (hUmeas : Measurable yU) :
    Measurable (intervalIFVec yL yU P) := by
  unfold intervalIFVec eucl₂
  refine ((EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.measurable).comp ?_
  refine measurable_pi_lambda _ (fun j => ?_)
  fin_cases j
  · exact (hLmeas.sub measurable_const)
  · exact (hUmeas.sub measurable_const)

/-- The variance term `‖ψ‖² ∈ L¹(P)`, from `MemLp 2` of the two endpoints. -/
lemma intervalIFVec_var_integrable (yL yU : X → ℝ)
    (hLsq : MemLp yL 2 P) (hUsq : MemLp yU 2 P) :
    Integrable (fun x => ‖intervalIFVec yL yU P x‖ ^ 2) P := by
  have hL2 : MemLp (fun x => yL x - ∫ z, yL z ∂P) 2 P :=
    hLsq.sub (memLp_const _)
  have hU2 : MemLp (fun x => yU x - ∫ z, yU z ∂P) 2 P :=
    hUsq.sub (memLp_const _)
  have hLi : Integrable (fun x => (yL x - ∫ z, yL z ∂P) ^ 2) P :=
    (memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2
  have hUi : Integrable (fun x => (yU x - ∫ z, yU z ∂P) ^ 2) P :=
    (memLp_two_iff_integrable_sq hU2.aestronglyMeasurable).1 hU2
  have heq : (fun x => ‖intervalIFVec yL yU P x‖ ^ 2)
      = fun x => (yL x - ∫ z, yL z ∂P) ^ 2 + (yU x - ∫ z, yU z ∂P) ^ 2 := by
    funext x; exact norm_sq_intervalIFVec yL yU x
  rw [heq]
  exact hLi.add hUi

/-- `intervalIFVec` is Bochner-integrable, from `MemLp 2 ⇒ Integrable` of the
endpoints on a probability measure. -/
lemma intervalIFVec_integrable (yL yU : X → ℝ)
    (hLsq : MemLp yL 2 P) (hUsq : MemLp yU 2 P) :
    Integrable (intervalIFVec yL yU P) P := by
  have hLi : Integrable yL P := hLsq.integrable (by norm_num)
  have hUi : Integrable yU P := hUsq.integrable (by norm_num)
  unfold intervalIFVec eucl₂
  apply (ContinuousLinearEquiv.integrable_comp_iff (EuclideanSpace.equiv (Fin 2) ℝ).symm).2
  refine (integrable_pi_iff).2 (fun j => ?_)
  fin_cases j
  · exact hLi.sub (integrable_const _)
  · exact hUi.sub (integrable_const _)

/-- The endpoint influence function is centered: `∫ ψ dP = 0`. -/
lemma intervalIFVec_mean_zero (yL yU : X → ℝ)
    (hLsq : MemLp yL 2 P) (hUsq : MemLp yU 2 P) :
    ∫ x, intervalIFVec yL yU P x ∂P = 0 := by
  have hLi : Integrable yL P := hLsq.integrable (by norm_num)
  have hUi : Integrable yU P := hUsq.integrable (by norm_num)
  change ∫ x, eucl₂ ![yL x - ∫ z, yL z ∂P, yU x - ∫ z, yU z ∂P] ∂P = 0
  unfold eucl₂
  set g : X → (Fin 2 → ℝ) := fun x => ![yL x - ∫ z, yL z ∂P, yU x - ∫ z, yU z ∂P] with hg
  rw [ContinuousLinearEquiv.integral_comp_comm (EuclideanSpace.equiv (Fin 2) ℝ).symm g]
  have hint : Integrable g P := by
    refine (integrable_pi_iff).2 (fun j => ?_)
    fin_cases j
    · exact hLi.sub (integrable_const _)
    · exact hUi.sub (integrable_const _)
  have hzero : (∫ x, g x ∂P) = 0 := by
    funext j
    have hproj := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j) hint
    simp only [ContinuousLinearMap.proj_apply] at hproj
    rw [Pi.zero_apply, ← hproj]
    fin_cases j
    · have heq : (fun x => g x ((fun i => i) (⟨0, by omega⟩ : Fin 2)))
          = fun x => yL x - ∫ z, yL z ∂P := by
        funext x; simp only [hg]; rfl
      rw [heq, integral_sub hLi (integrable_const _), integral_const, probReal_univ, one_smul,
        sub_self]
    · have heq : (fun x => g x ((fun i => i) (⟨1, by omega⟩ : Fin 2)))
          = fun x => yU x - ∫ z, yU z ∂P := by
        funext x; simp only [hg]; rfl
      rw [heq, integral_sub hUi (integrable_const _), integral_const, probReal_univ, one_smul,
        sub_self]
  rw [hzero, map_zero]

/-- The vector normalised sum of `intervalIFVec` is `AEMeasurable` for each `n`,
from measurability of the endpoints and of the sample coordinates `S.Z i`. -/
lemma intervalIFVec_sum_aemeasurable (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLmeas : Measurable yL) (hUmeas : Measurable yU) :
    ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n) μ := by
  intro n
  unfold IsAsymLinearVec.normalizedSum
  refine (Measurable.aemeasurable ?_)
  refine (measurable_const_smul _).comp ?_
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (measurable_intervalIFVec yL yU hLmeas hUmeas).comp (S.meas i)

/-- The scaled Hausdorff statistic is `AEMeasurable` for each `n`.  Equals
`maxAbs ∘ (normalised sum)` everywhere by `maxAbs_normalizedSum_eq`. -/
lemma intervalIFVec_hHmeas (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLU : ∀ z, yL z ≤ yU z) (hLmeas : Measurable yL) (hUmeas : Measurable yU)
    (hLint : Integrable yL P) (hUint : Integrable yU P) :
    ∀ n : ℕ, AEMeasurable
      (fun ω => Real.sqrt n * hausdorffDist
        (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω))
        (Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P))) μ := by
  intro n
  refine (measurable_maxAbs.comp_aemeasurable
    (intervalIFVec_sum_aemeasurable S yL yU hLmeas hUmeas n)).congr ?_
  exact Filter.Eventually.of_forall fun ω =>
    maxAbs_normalizedSum_eq S yL yU hLU hLint hUint n ω

/-- **Beresteanu–Molinari Theorem 3.2 (scalar interval data).**  For an i.i.d.
sample of interval data `Yᵢ = [y_{iL}, y_{iU}]` with `y_L ≤ y_U` and the centered
endpoint influence function satisfying the multivariate-CLT hypotheses, the scaled
Hausdorff distance between the sample-mean interval `Ȳₙ` and the population
identified interval `E[Y] = [E y_L, E y_U]` converges in distribution to the
max-abs of the bivariate Gaussian limit:

    √n · H(Ȳₙ, E[Y])  ⇒  max(|z_L|, |z_U|).

Obtained by transporting the abstract continuous-mapping CLT
(`normalizedSum_maxAbs_clt`) across the Hausdorff bridge
(`maxAbs_normalizedSum_eq`) via `Tendsto_dist_vec.congr_ae`. -/
theorem interval_data_clt (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLU : ∀ z, yL z ≤ yU z) (hLint : Integrable yL P) (hUint : Integrable yU P)
    (hψ : Measurable (intervalIFVec yL yU P))
    (hvar : Integrable (fun x => ‖intervalIFVec yL yU P x‖ ^ 2) P)
    (hψ_int : Integrable (intervalIFVec yL yU P) P)
    (hmean : ∫ x, intervalIFVec yL yU P x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n) μ)
    (hHmeas : ∀ n : ℕ, AEMeasurable
      (fun ω => Real.sqrt n * hausdorffDist
        (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω))
        (Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P))) μ) :
    Tendsto_dist_vec
      (fun n ω => Real.sqrt n * hausdorffDist
        (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω))
        (Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P)))
      ((gaussianLimit hψ hvar).map maxAbs) μ hHmeas :=
  Tendsto_dist_vec.congr_ae
    (fun n => measurable_maxAbs.comp_aemeasurable (hSum_meas n))
    hHmeas
    (normalizedSum_maxAbs_clt hψ hvar S hψ_int hmean hSum_meas)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω =>
      maxAbs_normalizedSum_eq S yL yU hLU hLint hUint n ω)

/-- **Beresteanu–Molinari Theorem 3.2, self-contained `MemLp 2` form.**  For an
i.i.d. sample of interval data `Yᵢ = [y_{iL}, y_{iU}]` with `y_L ≤ y_U`, measurable
endpoints, and finite second moments (`MemLp 2`), the scaled Hausdorff distance
between the sample-mean interval and the population identified interval
`E[Y] = [E y_L, E y_U]` converges in distribution to the max-abs of the bivariate
Gaussian limit.  All four multivariate-CLT hypotheses of `interval_data_clt` are
discharged from the clean moment conditions on `yL, yU`. -/
theorem interval_data_clt_of_memLp (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLU : ∀ z, yL z ≤ yU z) (hLmeas : Measurable yL) (hUmeas : Measurable yU)
    (hLsq : MemLp yL 2 P) (hUsq : MemLp yU 2 P) :
    Tendsto_dist_vec
      (fun n ω => Real.sqrt n * hausdorffDist
        (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω))
        (Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P)))
      ((gaussianLimit (measurable_intervalIFVec yL yU hLmeas hUmeas)
        (intervalIFVec_var_integrable yL yU hLsq hUsq)).map maxAbs) μ
      (intervalIFVec_hHmeas S yL yU hLU hLmeas hUmeas
        (hLsq.integrable (by norm_num)) (hUsq.integrable (by norm_num))) :=
  interval_data_clt S yL yU hLU
    (hLsq.integrable (by norm_num)) (hUsq.integrable (by norm_num))
    (measurable_intervalIFVec yL yU hLmeas hUmeas)
    (intervalIFVec_var_integrable yL yU hLsq hUsq)
    (intervalIFVec_integrable yL yU hLsq hUsq)
    (intervalIFVec_mean_zero yL yU hLsq hUsq)
    (intervalIFVec_sum_aemeasurable S yL yU hLmeas hUmeas)
    (intervalIFVec_hHmeas S yL yU hLU hLmeas hUmeas
      (hLsq.integrable (by norm_num)) (hUsq.integrable (by norm_num)))

end Bridge

end Causalean.PartialID.RandomSet
