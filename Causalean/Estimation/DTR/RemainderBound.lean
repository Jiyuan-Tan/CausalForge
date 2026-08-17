/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sequential DR (DTR, n = 2) second-order remainder bound

Quantitative bound on the population sequential DR moment at any
`η ∈ H_ε`, derived from `seqDR_remainder_identity` plus stagewise
Cauchy–Schwarz:

    |∫ z, m_seqDR(η, z, θ₀) ∂(P_Z)|
        ≤ C_ε · (‖Δμ₀‖_{L²(P_H₀)} + ‖Δμ₁‖_{L²(P_H₁)})
                · (‖Δe₀‖_{L²(P_H₀)} + ‖Δe₁‖_{L²(P_H₁)}),

with `C_ε = 2 / (ε² · (1 − ε))`, an `O(ε⁻²)` closed form analogous to
the ATE `aipw_rem_const ε := 2 / (ε · (1 − ε))`.  The extra `ε⁻¹`
factor reflects the stage-1 weight bound `|w₁| ≤ ε⁻²`.

The product on the RHS is a `(Σ‖Δμ_k‖) · (Σ‖Δe_k‖)` slack form on the
two-summand identity:

    Σ_k aₖ bₖ ≤ (Σ_k aₖ) · (Σ_k bₖ)   for nonneg aₖ, bₖ,

applied to `aₖ := ‖Δμ_k‖₂` and `bₖ := ‖Δe_k‖₂`.

Also includes the `IsLittleOp` corollary `seqDR_remainder_op` mirroring
`aipw_remainder_op`: under random nuisances `η̂_n` realising `H_ε` and the
two-stage L²-product rate hypothesis, the population moment at the random
nuisance is `o_p(n^{-1/2})`.  This is the form consumed at DML stage by
`DTRInstance.lean`.

The stochastic-order corollary uses the canonical `IsLittleOp` closure
helpers imported from `Causalean.Stat.Orthogonality.ConditionalOp`, rather
than restating the ATE proof-local helper lemmas.
-/

import Causalean.Estimation.DTR.RemainderIdentity
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
Bounds the sequential doubly robust second-order remainder for a two-stage
dynamic-treatment-regime problem. The constants track overlap and stagewise
nuisance errors in the DTR product-rate condition. The main declarations are
`seqDR_rem_const`, `seqDR_remainder_bound`, and the random-nuisance
stochastic-order corollary `seqDR_remainder_op`.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Sequential DR remainder constant

Choose `C_ε := 2 / (ε² · (1 − ε))`, the `O(ε⁻²)` closed form analogous to
the ATE `aipw_rem_const ε := 2 / (ε · (1 − ε))`.  The extra `ε⁻¹` factor
absorbs the stage-1 weight bound `|w₁| ≤ ε⁻²`. -/

/-- **Sequential DR (DTR, n = 2) remainder constant for strict overlap `ε`.**

`C_ε := 2 / (ε² · (1 − ε))`. -/
noncomputable def seqDR_rem_const (ε : ℝ) : ℝ := 2 / (ε ^ 2 * (1 - ε))

/-! ## Headline quantitative bound -/

/-- **Sequential DR (DTR, n = 2) remainder bound.** Consider a two-stage dynamic
treatment-regime estimation system satisfying [the sequential causal
assumptions](hyp:hA), for which [the stage-0 and stage-1 propensity scores are
bounded within a margin ε of 0 and 1 (strict overlap)](hyp:h_overlap), and where
[the factual outcome](hyp:h_y2) and [the potential outcome under every fixed
treatment regime](hyp:h_yd2) each have finite second moment. For any candidate
nuisance vector η whose propensities likewise [lie in this strict-overlap
band](hyp:hη), and whose [stage-0 outcome-regression error](hyp:hΔμ₀_memLp),
[stage-1 outcome-regression error](hyp:hΔμ₁_memLp), [stage-0 propensity
error](hyp:hΔe₀_memLp), and [stage-1 propensity error](hyp:hΔe₁_memLp) are each
square-integrable against the corresponding stage's history law, [the absolute value
of the population sequential doubly robust moment at η and the true target θ₀ is at
most an explicit `O(ε⁻²)` constant times the sum of the two stagewise
outcome-regression L² errors, times the sum of the two stagewise propensity L²
errors](goal).

Cauchy–Schwarz on each summand of `seqDR_remainder_identity`, plus
the slack inequality `Σ aₖ bₖ ≤ (Σ aₖ) · (Σ bₖ)` for nonneg sequences,
yields the L²-product bound.  The constant `seqDR_rem_const ε` absorbs
the stage-0 IPW weight bound `ε⁻¹` and the stage-1 IPW weight bound
`ε⁻²`. -/
theorem seqDR_remainder_bound
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ dbar : Fin 2 → δ, Integrable
      (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ)
    (η : DTRNuisanceVec₂ δ γ) (hη : η ∈ DTREstimationSystem.H_ε ε)
    (hΔμ₀_memLp : MemLp (fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀)
    (hΔμ₁_memLp : MemLp (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁)
    (hΔe₀_memLp : MemLp (fun s₀ => η.e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀)
    (hΔe₁_memLp : MemLp (fun h => η.e₁_fn h - S.e₁_val h) 2 S.P_H₁) :
    |∫ z, S.seqDRMomentFunctional η z S.θ₀ ∂(S.P_Z)|
      ≤ seqDR_rem_const ε *
          ((eLpNorm (fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal
            + (eLpNorm (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal) *
          ((eLpNorm (fun s₀ => η.e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal
            + (eLpNorm (fun h => η.e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal) := by
  let dμ0 : γ 0 → ℝ := fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀
  let de0 : γ 0 → ℝ := fun s₀ => η.e₀_fn s₀ - S.e₀_val s₀
  let dμ1 : γ 1 × δ × γ 0 → ℝ := fun h => η.μ₁_fn h - S.μ₁_val h
  let de1 : γ 1 × δ × γ 0 → ℝ := fun h => η.e₁_fn h - S.e₁_val h
  let rem0 : γ 0 → ℝ := fun s₀ => de0 s₀ * (1 / η.e₀_fn s₀) * dμ0 s₀
  let rem1 : γ 1 × δ × γ 0 → ℝ := fun h =>
    indEq h.2.1 (S.dbar 0) * de1 h * (1 / (η.e₀_fn h.2.2 * η.e₁_fn h)) * dμ1 h
  have hC_ge_inv0 : ε⁻¹ ≤ seqDR_rem_const ε := by
    unfold seqDR_rem_const
    have hpos : 0 < ε := h_overlap.1
    have hone : 0 < 1 - ε := by linarith [h_overlap.2.1]
    have hden : 0 < ε ^ 2 * (1 - ε) := mul_pos (sq_pos_of_pos hpos) hone
    rw [div_eq_mul_inv]
    field_simp [hpos.ne', hden.ne']
    nlinarith [h_overlap.2.1]
  have hC_ge_inv1 : (ε * ε)⁻¹ ≤ seqDR_rem_const ε := by
    unfold seqDR_rem_const
    have hpos : 0 < ε := h_overlap.1
    have hone : 0 < 1 - ε := by linarith [h_overlap.2.1]
    have hεε : 0 < ε * ε := mul_pos hpos hpos
    have hden : 0 < ε ^ 2 * (1 - ε) := mul_pos (sq_pos_of_pos hpos) hone
    rw [div_eq_mul_inv]
    field_simp [hpos.ne', hεε.ne', hden.ne']
    nlinarith [h_overlap.2.1]
  have hC_nonneg : 0 ≤ seqDR_rem_const ε :=
    (inv_nonneg.mpr (mul_nonneg h_overlap.1.le h_overlap.1.le)).trans hC_ge_inv1
  have hη0_lower : ∀ s₀, ε ≤ η.e₀_fn s₀ := fun s₀ => (hη.1 s₀).1
  have hη1_lower : ∀ h, ε ≤ η.e₁_fn h := fun h => (hη.2 h).1
  have hη0_pos : ∀ s₀, 0 < η.e₀_fn s₀ :=
    fun s₀ => lt_of_lt_of_le h_overlap.1 (hη0_lower s₀)
  have hη1_pos : ∀ h, 0 < η.e₁_fn h :=
    fun h => lt_of_lt_of_le h_overlap.1 (hη1_lower h)
  have hpoint0 : ∀ s₀, |rem0 s₀| ≤ seqDR_rem_const ε * |dμ0 s₀ * de0 s₀| := by
    intro s₀
    have hinv : |(η.e₀_fn s₀)⁻¹| ≤ seqDR_rem_const ε := by
      have hle : (η.e₀_fn s₀)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ (hη0_pos s₀) h_overlap.1).2 (hη0_lower s₀)
      rw [abs_of_pos (inv_pos.mpr (hη0_pos s₀))]
      exact hle.trans hC_ge_inv0
    calc
      |rem0 s₀| = |dμ0 s₀ * de0 s₀| * |(η.e₀_fn s₀)⁻¹| := by
        simp [rem0, div_eq_mul_inv, abs_mul, mul_left_comm, mul_comm]
      _ ≤ |dμ0 s₀ * de0 s₀| * seqDR_rem_const ε :=
        mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = seqDR_rem_const ε * |dμ0 s₀ * de0 s₀| := by ring
  have hpoint1 : ∀ h, |rem1 h| ≤ seqDR_rem_const ε * |dμ1 h * de1 h| := by
    intro h
    have hpos0 : 0 < η.e₀_fn h.2.2 := hη0_pos h.2.2
    have hpos1 : 0 < η.e₁_fn h := hη1_pos h
    have hprod_pos : 0 < η.e₀_fn h.2.2 * η.e₁_fn h := mul_pos hpos0 hpos1
    have hεprod : ε * ε ≤ η.e₀_fn h.2.2 * η.e₁_fn h :=
      mul_le_mul (hη0_lower h.2.2) (hη1_lower h) h_overlap.1.le
        (le_trans h_overlap.1.le (hη0_lower h.2.2))
    have hinv : |(η.e₀_fn h.2.2 * η.e₁_fn h)⁻¹| ≤ seqDR_rem_const ε := by
      have hle : (η.e₀_fn h.2.2 * η.e₁_fn h)⁻¹ ≤ (ε * ε)⁻¹ :=
        (inv_le_inv₀ hprod_pos (mul_pos h_overlap.1 h_overlap.1)).2 hεprod
      rw [abs_of_pos (inv_pos.mpr hprod_pos)]
      exact hle.trans hC_ge_inv1
    have hind : |indEq h.2.1 (S.dbar 0)| ≤ 1 := by
      unfold indEq
      split <;> simp
    calc
      |rem1 h| =
          |indEq h.2.1 (S.dbar 0)| *
            |dμ1 h * de1 h| * |(η.e₀_fn h.2.2 * η.e₁_fn h)⁻¹| := by
        simp [rem1, div_eq_mul_inv, abs_mul, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ 1 * |dμ1 h * de1 h| * seqDR_rem_const ε := by
        exact mul_le_mul
          (mul_le_mul hind le_rfl (abs_nonneg _) zero_le_one)
          hinv (abs_nonneg _) (mul_nonneg zero_le_one (abs_nonneg _))
      _ = seqDR_rem_const ε * |dμ1 h * de1 h| := by ring
  haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
    constructor
    simpa using ENNReal.inv_two_add_inv_two
  haveI : IsFiniteMeasure S.P_H₀ := by
    unfold DTREstimationSystem.P_H₀
    infer_instance
  haveI : IsFiniteMeasure S.P_H₁ := by
    unfold DTREstimationSystem.P_H₁
    infer_instance
  have hprod0_int : Integrable (fun s₀ => dμ0 s₀ * de0 s₀) S.P_H₀ := by
    have hmul : MemLp (fun s₀ => dμ0 s₀ * de0 s₀) 1 S.P_H₀ :=
      hΔe₀_memLp.mul hΔμ₀_memLp
    exact hmul.integrable (by norm_num)
  have hprod1_int : Integrable (fun h => dμ1 h * de1 h) S.P_H₁ := by
    have hmul : MemLp (fun h => dμ1 h * de1 h) 1 S.P_H₁ :=
      hΔe₁_memLp.mul hΔμ₁_memLp
    exact hmul.integrable (by norm_num)
  have hbound0_int :
      Integrable (fun s₀ => seqDR_rem_const ε * |dμ0 s₀ * de0 s₀|) S.P_H₀ :=
    hprod0_int.norm.const_mul (seqDR_rem_const ε)
  have hbound1_int :
      Integrable (fun h => seqDR_rem_const ε * |dμ1 h * de1 h|) S.P_H₁ :=
    hprod1_int.norm.const_mul (seqDR_rem_const ε)
  have hrem0_meas : Measurable rem0 := by
    dsimp [rem0, dμ0, de0]
    exact (((η.e₀_meas.sub S.e₀_meas).mul
      ((measurable_const.div η.e₀_meas))).mul
        ((η.μ₀_meas.sub S.μ₀_meas)))
  have hrem1_meas : Measurable rem1 := by
    have hind : Measurable (fun h : γ 1 × δ × γ 0 => indEq h.2.1 (S.dbar 0)) := by
      have hset : MeasurableSet {x : δ | x = S.dbar 0} := MeasurableSet.singleton _
      have hbase : Measurable (Set.indicator {x : δ | x = S.dbar 0} (fun _ => (1 : ℝ))) :=
        measurable_const.indicator hset
      have heq : (fun x : δ => indEq x (S.dbar 0)) =
          Set.indicator {x : δ | x = S.dbar 0} (fun _ => (1 : ℝ)) := by
        funext x
        unfold indEq
        by_cases hx : x = S.dbar 0 <;> simp [hx]
      exact (heq ▸ hbase).comp measurable_snd.fst
    dsimp [rem1, dμ1, de1]
    exact (((hind.mul (η.e₁_meas.sub S.e₁_meas)).mul
      ((measurable_const.div ((η.e₀_meas.comp measurable_snd.snd).mul η.e₁_meas)))).mul
        (η.μ₁_meas.sub S.μ₁_meas))
  have hrem0_abs_int : Integrable (fun s₀ => |rem0 s₀|) S.P_H₀ :=
    hbound0_int.mono'
      (continuous_abs.measurable.comp hrem0_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s₀ => by
        simpa [Real.norm_eq_abs] using hpoint0 s₀)
  have hrem1_abs_int : Integrable (fun h => |rem1 h|) S.P_H₁ :=
    hbound1_int.mono'
      (continuous_abs.measurable.comp hrem1_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => by
        simpa [Real.norm_eq_abs] using hpoint1 h)
  have hCS0 :
      ∫ s₀, |dμ0 s₀ * de0 s₀| ∂(S.P_H₀)
        ≤ (eLpNorm dμ0 2 S.P_H₀).toReal * (eLpNorm de0 2 S.P_H₀).toReal := by
    simpa [dμ0, de0] using
      integral_abs_mul_le_eLpNorm_mul_eLpNorm
        (ν := S.P_H₀) hΔμ₀_memLp hΔe₀_memLp
  have hCS1 :
      ∫ h, |dμ1 h * de1 h| ∂(S.P_H₁)
        ≤ (eLpNorm dμ1 2 S.P_H₁).toReal * (eLpNorm de1 2 S.P_H₁).toReal := by
    simpa [dμ1, de1] using
      integral_abs_mul_le_eLpNorm_mul_eLpNorm
        (ν := S.P_H₁) hΔμ₁_memLp hΔe₁_memLp
  have hident := seqDR_remainder_identity S h_overlap hA h_y2 h_yd2 η hη
    hΔμ₀_memLp hΔμ₁_memLp hΔe₀_memLp hΔe₁_memLp
  calc
    |∫ z, S.seqDRMomentFunctional η z S.θ₀ ∂(S.P_Z)|
        = |∫ s₀, rem0 s₀ ∂(S.P_H₀) + ∫ h, rem1 h ∂(S.P_H₁)| := by
          rw [hident]
    _ ≤ |∫ s₀, rem0 s₀ ∂(S.P_H₀)| + |∫ h, rem1 h ∂(S.P_H₁)| :=
          abs_add_le _ _
    _ ≤ ∫ s₀, |rem0 s₀| ∂(S.P_H₀) + ∫ h, |rem1 h| ∂(S.P_H₁) :=
          add_le_add MeasureTheory.abs_integral_le_integral_abs
            MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ s₀, seqDR_rem_const ε * |dμ0 s₀ * de0 s₀| ∂(S.P_H₀) +
          ∫ h, seqDR_rem_const ε * |dμ1 h * de1 h| ∂(S.P_H₁) := by
          exact add_le_add
            (integral_mono_ae hrem0_abs_int hbound0_int
              (Filter.Eventually.of_forall hpoint0))
            (integral_mono_ae hrem1_abs_int hbound1_int
              (Filter.Eventually.of_forall hpoint1))
    _ = seqDR_rem_const ε * (∫ s₀, |dμ0 s₀ * de0 s₀| ∂(S.P_H₀)) +
          seqDR_rem_const ε * (∫ h, |dμ1 h * de1 h| ∂(S.P_H₁)) := by
          rw [integral_const_mul, integral_const_mul]
    _ ≤ seqDR_rem_const ε *
          ((eLpNorm dμ0 2 S.P_H₀).toReal * (eLpNorm de0 2 S.P_H₀).toReal) +
        seqDR_rem_const ε *
          ((eLpNorm dμ1 2 S.P_H₁).toReal * (eLpNorm de1 2 S.P_H₁).toReal) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hCS0 hC_nonneg)
            (mul_le_mul_of_nonneg_left hCS1 hC_nonneg)
    _ ≤ seqDR_rem_const ε *
          ((eLpNorm dμ0 2 S.P_H₀).toReal + (eLpNorm dμ1 2 S.P_H₁).toReal) *
          ((eLpNorm de0 2 S.P_H₀).toReal + (eLpNorm de1 2 S.P_H₁).toReal) := by
          have hμ0 : 0 ≤ (eLpNorm dμ0 2 S.P_H₀).toReal := ENNReal.toReal_nonneg
          have hμ1 : 0 ≤ (eLpNorm dμ1 2 S.P_H₁).toReal := ENNReal.toReal_nonneg
          have he0 : 0 ≤ (eLpNorm de0 2 S.P_H₀).toReal := ENNReal.toReal_nonneg
          have he1 : 0 ≤ (eLpNorm de1 2 S.P_H₁).toReal := ENNReal.toReal_nonneg
          nlinarith [mul_nonneg hμ0 he1, mul_nonneg hμ1 he0]
    _ = seqDR_rem_const ε *
          ((eLpNorm (fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal
            + (eLpNorm (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal) *
          ((eLpNorm (fun s₀ => η.e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal
            + (eLpNorm (fun h => η.e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal) := by
          simp [dμ0, de0, dμ1, de1]

/-! ## Stochastic-order corollary used by DML

If `η̂_n` realises `H_ε` pointwise and satisfies the L²-product rate
hypothesis on each stage at rate `n^{-1/2}`, then the population
sequential DR moment at the random nuisance is `o_p(n^{-1/2})`.  This is
the form consumed by `DTRInstance.lean` (the `R₁` cross-term of the
three-remainder DML decomposition).

The product-rate hypothesis is supplied at the level of *pairs* of
stages, mirroring `aipw_remainder_op` which sums over `a ∈ {0, 1}`. -/

/-- **Sequential DR remainder is `o_p(n^{-1/2})` under the two-stage
product rate.** Consider a two-stage dynamic treatment-regime estimation system
satisfying [the sequential causal assumptions](hyp:hA), for which [the stage-0 and
stage-1 propensity scores are bounded within a margin ε of 0 and 1 (strict
overlap)](hyp:h_overlap), and where [the factual outcome](hyp:h_y2) and [the
potential outcome under every fixed treatment regime](hyp:h_yd2) each have finite
second moment. Let `η̂ₙ` be a sequence of sample-size-indexed, possibly random,
candidate nuisance vectors that [always land in the strict-overlap band, for every
sample size and every outcome of the underlying randomness](hyp:h_in_H), with
[stage-0 outcome-regression error](hyp:hΔμ₀_memLp), [stage-1 outcome-regression
error](hyp:hΔμ₁_memLp), [stage-0 propensity error](hyp:hΔe₀_memLp), and [stage-1
propensity error](hyp:hΔe₁_memLp) each square-integrable against the corresponding
stage's history law at every sample size and outcome. If the four stagewise L²
products of outcome-regression and propensity error — [own-stage at
stage 0](hyp:h_product_rate_00), [own-stage at stage 1](hyp:h_product_rate_11),
[stage-0 outcome-regression with stage-1 propensity](hyp:h_product_rate_01), and
[stage-1 outcome-regression with stage-0 propensity](hyp:h_product_rate_10) — are
each `o_p(n^{-1/2})`, then [the population sequential doubly robust moment evaluated
at the random nuisance `η̂ₙ` is itself `o_p(n^{-1/2})`](goal).

If `η̂_n ω ∈ H_ε` for all `n, ω` and for each stage `k ∈ {0, 1}` the
L²-product `‖Δμ_k‖₂ · ‖Δe_k‖₂ = o_p(n^{-1/2})`, plus the stage-cross
products `‖Δμ_0‖₂ · ‖Δe_1‖₂` and `‖Δμ_1‖₂ · ‖Δe_0‖₂` are also
`o_p(n^{-1/2})`, then the population sequential DR moment at the random
nuisance is `o_p(n^{-1/2})` under `μ`.

The cross-stage product hypotheses are needed because `seqDR_remainder_bound`
yields `(‖Δμ_0‖ + ‖Δμ_1‖) · (‖Δe_0‖ + ‖Δe_1‖)`, which expands into all
four pairs.  Direct consequence of `seqDR_remainder_bound` plus closure
of `IsLittleOp` under finite sums and constant scaling. -/
theorem seqDR_remainder_op
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ dbar : Fin 2 → δ, Integrable
      (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ DTREstimationSystem.H_ε ε)
    (hΔμ₀_memLp :
      ∀ n ω, MemLp
        (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀)
    (hΔμ₁_memLp :
      ∀ n ω, MemLp
        (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁)
    (hΔe₀_memLp :
      ∀ n ω, MemLp
        (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀)
    (hΔe₁_memLp :
      ∀ n ω, MemLp
        (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁)
    (h_product_rate_00 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun s₀ =>
              (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
            (eLpNorm (fun s₀ =>
              (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (h_product_rate_11 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun h =>
              (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal *
            (eLpNorm (fun h =>
              (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (h_product_rate_01 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun s₀ =>
              (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
            (eLpNorm (fun h =>
              (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (h_product_rate_10 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun h =>
              (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal *
            (eLpNorm (fun s₀ =>
              (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsLittleOp
      (fun n ω => ∫ z, S.seqDRMomentFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
  let rn : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let prod00 : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun s₀ =>
        (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
      (eLpNorm (fun s₀ =>
        (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal
  let prod11 : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun h =>
        (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal *
      (eLpNorm (fun h =>
        (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal
  let prod01 : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun s₀ =>
        (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
      (eLpNorm (fun h =>
        (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal
  let prod10 : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun h =>
        (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal *
      (eLpNorm (fun s₀ =>
        (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal
  let sumProd : ℕ → P.Ω → ℝ := fun n ω =>
    prod00 n ω + prod11 n ω + prod01 n ω + prod10 n ω
  have hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rn n := by
    filter_upwards with n
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsum_rate :
      IsLittleOp sumProd rn P.μ := by
    have h0011 :
        IsLittleOp (fun n ω => prod00 n ω + prod11 n ω) rn P.μ := by
      simpa [prod00, prod11, rn] using
        IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg
          h_product_rate_00 h_product_rate_11
    have h0110 :
        IsLittleOp (fun n ω => prod01 n ω + prod10 n ω) rn P.μ := by
      simpa [prod01, prod10, rn] using
        IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg
          h_product_rate_01 h_product_rate_10
    simpa [sumProd, add_assoc] using
      IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg h0011 h0110
  have hCpos : 0 < seqDR_rem_const ε := by
    unfold seqDR_rem_const
    have h1 : 0 < 1 - ε := by linarith [h_overlap.2.1]
    have hden_pos : 0 < ε ^ 2 * (1 - ε) := mul_pos (sq_pos_of_pos h_overlap.1) h1
    positivity
  refine IsLittleOp.of_abs_le_const_mul (μ := P.μ) hCpos hsum_rate ?_
  intro n ω
  have hsum_nonneg : 0 ≤ sumProd n ω := by
    have h00 : 0 ≤ prod00 n ω := by
      dsimp [prod00]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have h11 : 0 ≤ prod11 n ω := by
      dsimp [prod11]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have h01 : 0 ≤ prod01 n ω := by
      dsimp [prod01]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have h10 : 0 ≤ prod10 n ω := by
      dsimp [prod10]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    dsimp [sumProd]
    positivity
  have hbound := seqDR_remainder_bound S h_overlap hA h_y2 h_yd2
    (η_hat n ω) (h_in_H n ω) (hΔμ₀_memLp n ω) (hΔμ₁_memLp n ω)
    (hΔe₀_memLp n ω) (hΔe₁_memLp n ω)
  have habs_sum : |sumProd n ω| = sumProd n ω := abs_of_nonneg hsum_nonneg
  calc
    |∫ z, S.seqDRMomentFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z)|
        ≤ seqDR_rem_const ε * sumProd n ω := by
          have hrhs :
              seqDR_rem_const ε *
                  ((eLpNorm (fun s₀ =>
                        (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal
                    + (eLpNorm (fun h =>
                        (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal) *
                  ((eLpNorm (fun s₀ =>
                        (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal
                    + (eLpNorm (fun h =>
                        (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal)
                = seqDR_rem_const ε * sumProd n ω := by
            dsimp [sumProd, prod00, prod11, prod01, prod10]
            ring
          exact hbound.trans_eq hrhs
    _ = seqDR_rem_const ε * |sumProd n ω| :=
          congrArg (fun x => seqDR_rem_const ε * x) habs_sum.symm

end DTREstimationSystem

end DTR
end Estimation
end Causalean
