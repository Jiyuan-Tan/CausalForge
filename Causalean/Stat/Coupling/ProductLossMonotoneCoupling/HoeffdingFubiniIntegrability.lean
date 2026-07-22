/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.HoeffdingFubini

/-!
# Integrability and Fubini swaps for Hoeffding's identity

This file proves the integrability bounds and Fubini swaps that turn the signed
tail representation of the product into Lebesgue integrals of fibre
expectations and marginal tail means.

The output supplies the integrable fibre and mean-tail formulas consumed by the
final Hoeffding covariance identity.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-- The single-coordinate tail kernel is integrable on `volume ⊗ π`. Domination:
`∫ s, |signedTail p.1 s| ds = |p.1|`, which is `π`-integrable since `X ∈ L²(π)`
and `π` is finite. -/
lemma integrable_tail_fst_prod (h : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) 2 μ) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => signedTail z.2.1 z.1) (volume.prod π) := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  have hmeas : Measurable (fun z : ℝ × (ℝ × ℝ) => signedTail z.2.1 z.1) := by
    exact measurable_signedTail_uncurry.comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ?_
  constructor
  · exact Filter.Eventually.of_forall fun p => integrable_signedTail p.1
  · have h12 : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
    have hInt : Integrable (fun p : ℝ × ℝ => p.1) π :=
      (coupling_fst_memLp h hμ).integrable h12
    simpa [Real.norm_eq_abs, integral_abs_signedTail] using hInt.norm

/-- The single-coordinate tail kernel is integrable on `volume ⊗ π` (second
coordinate). -/
lemma integrable_tail_snd_prod (h : IsCoupling π μ ν) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => signedTail z.2.2 z.1) (volume.prod π) := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  have hmeas : Measurable (fun z : ℝ × (ℝ × ℝ) => signedTail z.2.2 z.1) := by
    exact measurable_signedTail_uncurry.comp
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ?_
  constructor
  · exact Filter.Eventually.of_forall fun p => integrable_signedTail p.2
  · have h12 : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
    have hInt : Integrable (fun p : ℝ × ℝ => p.2) π :=
      (coupling_snd_memLp h hν).integrable h12
    simpa [Real.norm_eq_abs, integral_abs_signedTail] using hInt.norm

/-- **The key integrability.** The product tail kernel
`Φ q p = signedTail p.1 q.1 * signedTail p.2 q.2` is integrable on
`(volume ⊗ volume) ⊗ π`. Domination: for fixed `p`,
`∫ q, ‖Φ q p‖ dq = |p.1| * |p.2|` (`integral_norm_signedTail_prod`), and
`p ↦ |p.1| * |p.2|` is `π`-integrable by Cauchy–Schwarz on the `L²` marginals.
Formally: apply `MeasureTheory.integrable_prod_iff'` with the joint measurability
supplied by `measurable_signedTail_uncurry`. -/
lemma integrable_bigPhi (h : IsCoupling π μ ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        signedTail z.2.1 z.1.1 * signedTail z.2.2 z.1.2)
      ((volume.prod volume).prod π) := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  have hmeas₁ :
      Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => signedTail z.2.1 z.1.1) := by
    exact measurable_signedTail_uncurry.comp
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  have hmeas₂ :
      Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => signedTail z.2.2 z.1.2) := by
    exact measurable_signedTail_uncurry.comp
      ((measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  refine (integrable_prod_iff' (hmeas₁.mul hmeas₂).aestronglyMeasurable).2 ?_
  constructor
  · exact Filter.Eventually.of_forall fun p => integrable_signedTail_prod p.1 p.2
  · have hbase : Integrable (fun y : ℝ × ℝ => |y.1| * |y.2|) π := by
      simpa [Real.norm_eq_abs, abs_mul] using (coupling_integrable_mul h hμ hν).norm
    exact hbase.congr (Filter.Eventually.of_forall fun y => by
      symm
      simpa [Real.norm_eq_abs, abs_mul] using integral_norm_signedTail_prod y.1 y.2)

/-- **First swap.** `E_π[XY]` is the Lebesgue double integral of the fibre
integrals: `∫ p, p.1 * p.2 ∂π = ∫ q, (∫ p, Φ q p ∂π) dq`. Immediate from
`integral_signedTail_prod` (pointwise in `p`) followed by
`MeasureTheory.integral_integral_swap` applied to `integrable_bigPhi`. -/
lemma integral_prod_eq_integral_fiber (h : IsCoupling π μ ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p : ℝ × ℝ, p.1 * p.2 ∂π)
      = ∫ q : ℝ × ℝ, (∫ p : ℝ × ℝ, signedTail p.1 q.1 * signedTail p.2 q.2 ∂π)
          ∂(volume.prod volume) := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  calc
    (∫ p : ℝ × ℝ, p.1 * p.2 ∂π)
        = ∫ p : ℝ × ℝ,
            (∫ q : ℝ × ℝ, signedTail p.1 q.1 * signedTail p.2 q.2
              ∂(volume.prod volume)) ∂π := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => (integral_signedTail_prod p.1 p.2).symm
    _ = ∫ q : ℝ × ℝ,
          (∫ p : ℝ × ℝ, signedTail p.1 q.1 * signedTail p.2 q.2 ∂π)
            ∂(volume.prod volume) := by
          exact (integral_integral_swap (μ := volume.prod volume) (ν := π)
            (f := fun q : ℝ × ℝ => fun p : ℝ × ℝ =>
              signedTail p.1 q.1 * signedTail p.2 q.2) (integrable_bigPhi h hμ hν)).symm

/-- **Tail formula for the mean.** `E[X] = ∫ s, (SX s - 𝟙{s<0}) ds`, by the same
swap on `volume ⊗ π` using `integral_signedTail` pointwise. -/
lemma mean_fst_tail (h : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) 2 μ) :
    (∫ x : ℝ, x ∂μ) = ∫ s : ℝ, (survFst π s - tailInd 0 s) ∂volume := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  calc
    (∫ x : ℝ, x ∂μ) = ∫ p : ℝ × ℝ, p.1 ∂π :=
      (coupling_integral_fst h hμ).symm
    _ = ∫ p : ℝ × ℝ, (∫ s : ℝ, signedTail p.1 s ∂volume) ∂π := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => (integral_signedTail p.1).symm
    _ = ∫ s : ℝ, (∫ p : ℝ × ℝ, signedTail p.1 s ∂π) ∂volume := by
          exact (integral_integral_swap (μ := volume) (ν := π)
            (f := fun s : ℝ => fun p : ℝ × ℝ => signedTail p.1 s)
            (integrable_tail_fst_prod h hμ)).symm
    _ = ∫ s : ℝ, (survFst π s - tailInd 0 s) ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun s => integral_signedTail_fst h s

/-- **Tail formula for the mean** (second coordinate). -/
lemma mean_snd_tail (h : IsCoupling π μ ν) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ y : ℝ, y ∂ν) = ∫ t : ℝ, (survSnd π t - tailInd 0 t) ∂volume := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  calc
    (∫ y : ℝ, y ∂ν) = ∫ p : ℝ × ℝ, p.2 ∂π :=
      (coupling_integral_snd h hν).symm
    _ = ∫ p : ℝ × ℝ, (∫ t : ℝ, signedTail p.2 t ∂volume) ∂π := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => (integral_signedTail p.2).symm
    _ = ∫ t : ℝ, (∫ p : ℝ × ℝ, signedTail p.2 t ∂π) ∂volume := by
          exact (integral_integral_swap (μ := volume) (ν := π)
            (f := fun t : ℝ => fun p : ℝ × ℝ => signedTail p.2 t)
            (integrable_tail_snd_prod h hν)).symm
    _ = ∫ t : ℝ, (survSnd π t - tailInd 0 t) ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => integral_signedTail_snd h t

/-- The centred marginal survival function `s ↦ SX s - 𝟙{s<0}` is Lebesgue
integrable (it is `E[signedTail X ·]`, integrable by
`Integrable.integral_prod_left` on `integrable_tail_fst_prod`). -/
lemma integrable_survFst_sub (h : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) 2 μ) :
    Integrable (fun s : ℝ => survFst π s - tailInd 0 s) volume := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  exact (integrable_tail_fst_prod h hμ).integral_prod_left.congr
    (Filter.Eventually.of_forall fun s => integral_signedTail_fst h s)

/-- The centred marginal survival function `t ↦ SY t - 𝟙{t<0}` is Lebesgue
integrable. -/
lemma integrable_survSnd_sub (h : IsCoupling π μ ν) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    Integrable (fun t : ℝ => survSnd π t - tailInd 0 t) volume := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  exact (integrable_tail_snd_prod h hν).integral_prod_left.congr
    (Filter.Eventually.of_forall fun t => integral_signedTail_snd h t)

/-- The fibre `q ↦ ∫ p, Φ q p ∂π` is integrable on `ℝ × ℝ`, by
`Integrable.integral_prod_left` applied to `integrable_bigPhi`. -/
lemma integrable_fiber (h : IsCoupling π μ ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    Integrable (fun q : ℝ × ℝ =>
        ∫ p : ℝ × ℝ, signedTail p.1 q.1 * signedTail p.2 q.2 ∂π)
      (volume.prod volume) := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  exact (integrable_bigPhi h hμ hν).integral_prod_left

end Causalean.Stat
