/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Concentration.ProjectionMatrixTail
import Causalean.Stat.Concentration.ConditionalKernel
import Mathlib.Probability.Independence.Conditional

/-!
# Conditional concentration of projected bounded noise

This module lifts the rank-sensitive projection tail bound to regular
conditional distributions.  A projector measurable with respect to the
conditioning sigma-algebra is frozen on almost every conditional fiber before
the unconditional result is applied.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Fix [a sub-σ-algebra `m` of the ambient σ-algebra](hyp:hm) and a finite family `eps` of real
random variables on `Ω` that is [measurable](hyp:hmeas) and [almost surely bounded by 1 in
absolute value under `μ`](hyp:hbound); suppose further that, on almost every `m`-conditioning
fiber, [each `eps i` has conditional mean zero under the regular conditional kernel given
`m`](hyp:hcenter), and that [the family `eps` is conditionally independent given
`m`](hyp:hindep). Let `Pi` be a matrix-valued map that is [`m`-measurable entrywise](hyp:hPi)
and, on almost every `m`-conditioning fiber, [symmetric](hyp:hsymm), [idempotent
(`Pi·Pi = Pi`)](hyp:hidem), and [of rank at most `r`](hyp:hrank), and fix [a positive tolerance
`zeta`](hyp:hzeta). Then, on almost every `m`-conditioning fiber, [the conditional probability
— under the regular conditional kernel given `m` — that the projected noise's squared energy
$\sum_i(\sum_j \mathrm{Pi}_{ij}\,\mathrm{eps}_j)^2$ exceeds the threshold
$8(r\log 5+\log(2/\zeta))$ is at most `zeta`](goal). -/
theorem ae_condExpKernel_projection_energy_gt_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {n r : ℕ}
    (eps : Fin n → Ω → ℝ) (Pi : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ i, @Measurable Ω ℝ mΩ _ (eps i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |eps i ω| ≤ 1)
    (hcenter : ∀ i, ∀ᵐ ω ∂μ.trim hm,
      ∫ ω', eps i ω' ∂(@ProbabilityTheory.condExpKernel Ω mΩ _ μ _ m) ω = 0)
    (hindep : @ProbabilityTheory.iCondIndepFun Ω (Fin n) m mΩ _ hm
      (fun _ ↦ ℝ) (fun _ ↦ inferInstance) eps μ _)
    (hPi : ∀ i j, Measurable[m] (fun ω ↦ Pi ω i j))
    (hsymm : ∀ᵐ ω ∂μ.trim hm, (Pi ω).transpose = Pi ω)
    (hidem : ∀ᵐ ω ∂μ.trim hm, Pi ω * Pi ω = Pi ω)
    (hrank : ∀ᵐ ω ∂μ.trim hm, Matrix.rank (Pi ω) ≤ r)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∀ᵐ ω ∂μ.trim hm,
      ((@ProbabilityTheory.condExpKernel Ω mΩ _ μ _ m) ω).real
        {ω' | 8 * ((r : ℝ) * Real.log 5 + Real.log (2 / zeta)) <
          ∑ i, (∑ j, Pi ω' i j * eps j ω') ^ 2} ≤ zeta := by
  classical
  let κ : @ProbabilityTheory.Kernel Ω Ω m mΩ :=
    @ProbabilityTheory.condExpKernel Ω mΩ _ μ _ m
  have hbound_fiber : ∀ᵐ ω ∂μ.trim hm, ∀ i, ∀ᵐ ω' ∂κ ω,
      |eps i ω'| ≤ 1 := by
    rw [ae_all_iff]
    intro i
    exact @ae_ae_condExpKernel_of_ae Ω mΩ _ μ _ m hm
      (fun ω ↦ |eps i ω| ≤ 1) (hbound i)
  have hindep_fiber : ∀ᵐ ω ∂μ.trim hm,
      @ProbabilityTheory.iIndepFun Ω (Fin n) mΩ (fun _ ↦ ℝ)
        (fun _ ↦ inferInstance) eps (κ ω) :=
    @ProbabilityTheory.Kernel.iIndepFun.ae_iIndepFun_real
      Ω Ω (Fin n) m mΩ κ (μ.trim hm) _ eps hmeas
      (show ProbabilityTheory.Kernel.iIndepFun eps κ (μ.trim hm) from hindep)
  have hcenter_fiber : ∀ᵐ ω ∂μ.trim hm, ∀ i,
      ∫ ω', eps i ω' ∂κ ω = 0 := by
    rw [ae_all_iff]
    exact hcenter
  have hPi_fiber : ∀ᵐ ω ∂μ.trim hm, ∀ i j,
      ∀ᵐ ω' ∂κ ω, Pi ω' i j = Pi ω i j := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact @ae_eq_const_condExpKernel_of_measurable Ω mΩ _ μ _ m hm
      ℝ _ _ (fun ω ↦ Pi ω i j) (hPi i j)
  filter_upwards [hbound_fiber, hindep_fiber, hindep.ae_isProbabilityMeasure,
    hcenter_fiber, hPi_fiber, hsymm, hidem, hrank]
    with ω hb hi hprob hc hfreeze hs hy hr
  letI : IsProbabilityMeasure (κ ω) := hprob
  by_cases hzeta_one : 1 ≤ zeta
  · exact (measureReal_le_one.trans hzeta_one)
  · have hzeta_lt_one : zeta < 1 := lt_of_not_ge hzeta_one
    let L : ℝ := (r : ℝ) * Real.log 5 + Real.log (2 / zeta)
    let t : ℝ := Real.sqrt (2 * L)
    have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    have hratio : 1 < 2 / zeta := by
      rw [lt_div_iff₀ hzeta]
      linarith
    have hL : 0 < L := by
      dsimp [L]
      have hlogratio : 0 < Real.log (2 / zeta) := Real.log_pos hratio
      positivity
    have ht : 0 ≤ t := Real.sqrt_nonneg _
    have ht_sq : t ^ 2 = 2 * L := by
      dsimp [t]
      rw [Real.sq_sqrt]
      linarith
    have hstatic := @measure_projection_energy_gt_le Ω mΩ n r (κ ω) _
      eps (Pi ω) (fun i => (hmeas i).aemeasurable) hb hc hi hs hy hr t ht
    have hevent :
        (κ ω).real
          {ω' | 8 * L < ∑ i, (∑ j, Pi ω' i j * eps j ω') ^ 2} =
        (κ ω).real
          {ω' | 4 * t ^ 2 < ∑ i, (∑ j, Pi ω i j * eps j ω') ^ 2} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      have hfreeze_all : ∀ᵐ ω' ∂κ ω, ∀ i j,
          Pi ω' i j = Pi ω i j := by
        rw [ae_all_iff]
        intro i
        rw [ae_all_iff]
        intro j
        exact hfreeze i j
      filter_upwards [hfreeze_all] with ω' hω'
      have hPi_eq : Pi ω' = Pi ω := by
        ext i j
        exact hω' i j
      change (8 * L < ∑ i, (∑ j, Pi ω' i j * eps j ω') ^ 2) =
        (4 * t ^ 2 < ∑ i, (∑ j, Pi ω i j * eps j ω') ^ 2)
      rw [hPi_eq, ht_sq]
      ring_nf
    rw [show (r : ℝ) * Real.log 5 + Real.log (2 / zeta) = L by rfl]
    rw [hevent]
    refine hstatic.trans ?_
    have hpow : (5 ^ r : ℝ) = Real.exp ((r : ℝ) * Real.log 5) := by
      symm
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    rw [ht_sq, hpow]
    have hratio_pos : 0 < 2 / zeta := div_pos (by norm_num) hzeta
    rw [show -(2 * L) / 2 = -L by ring]
    rw [← Real.exp_add]
    change Real.exp ((r : ℝ) * Real.log 5 -
      ((r : ℝ) * Real.log 5 + Real.log (2 / zeta))) ≤ zeta
    rw [show (r : ℝ) * Real.log 5 -
      ((r : ℝ) * Real.log 5 + Real.log (2 / zeta)) =
        -Real.log (2 / zeta) by ring]
    rw [Real.exp_neg, Real.exp_log hratio_pos]
    rw [inv_div]
    linarith

end

end Causalean.Stat.Concentration
