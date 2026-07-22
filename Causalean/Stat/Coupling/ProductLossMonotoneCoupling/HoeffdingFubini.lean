/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Survival
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.TailIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Fubini step in Hoeffding's covariance identity

Fix a coupling `π ∈ Π(μ, ν)` with `L²` marginals. Writing
`Φ q p = signedTail p.1 q.1 * signedTail p.2 q.2` for the product tail
representation of `p.1 * p.2` (see `TailIntegral.lean`), this file performs the
two Fubini swaps that turn the moments of `π` into Lebesgue integrals of
survival functions:

* `integral_prod_eq_integral_fiber` : `E_π[XY] = ∫∫ (∫ Φ q p ∂π) dq`;
* `mean_fst_tail` / `mean_snd_tail` : `E[X] = ∫ (SX s - 𝟙{s<0}) ds`, likewise `E[Y]`;
* `fiber_integral_pi` : the inner `π`-integral evaluates, by linearity of the
  expectation of a product of tail indicators, to
  `S s t - 𝟙{t<0}·SX s - 𝟙{s<0}·SY t + 𝟙{s<0}·𝟙{t<0}`.

The domination that legitimises both swaps is `∫∫ |Φ q p| dq = |p.1| * |p.2|`
(`integral_norm_signedTail_prod`), whose `π`-integral is finite by Cauchy–Schwarz
on the `L²` marginals. Subtracting `E[X]·E[Y]` (rewritten as a double integral
via `integral_prod_mul`) cancels the three inhomogeneous terms and leaves the
survival gap `S - SX·SY`, which is the Fréchet gap by `surv_gap_eq`.

Orientation convention: all product measures are taken as
`(volume.prod volume).prod π`, i.e. *tail variables first*, so that
`MeasureTheory.Integrable.integral_prod_left` directly yields integrability of
the fibre `q ↦ ∫ Φ q p ∂π` against Lebesgue×Lebesgue.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-! ### Moving the `L²` hypotheses through the marginals -/

/-- The first coordinate is in `L²(π)` when `μ = π.map Prod.fst` has a second
moment. -/
lemma coupling_fst_memLp (h : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) 2 μ) :
    MemLp (fun p : ℝ × ℝ => p.1) 2 π := by
  rw [← h.map_fst] at hμ
  simpa [Function.comp_def] using
    (hμ.comp_of_map (μ := π) (f := Prod.fst) measurable_fst.aemeasurable)

/-- The second coordinate is in `L²(π)` when `ν = π.map Prod.snd` has a second
moment. -/
lemma coupling_snd_memLp (h : IsCoupling π μ ν) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    MemLp (fun p : ℝ × ℝ => p.2) 2 π := by
  rw [← h.map_snd] at hν
  simpa [Function.comp_def] using
    (hν.comp_of_map (μ := π) (f := Prod.snd) measurable_snd.aemeasurable)

/-- `E_π[X] = E_μ[id]`: the first moment of a coupling is that of its first
marginal. -/
lemma coupling_integral_fst (h : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) 2 μ) :
    (∫ p : ℝ × ℝ, p.1 ∂π) = ∫ x : ℝ, x ∂μ := by
  have hμ' : AEStronglyMeasurable (fun x : ℝ => x) (π.map Prod.fst) := by
    simpa [h.map_fst] using hμ.aestronglyMeasurable
  rw [← h.map_fst]
  exact (integral_map measurable_fst.aemeasurable hμ').symm

/-- `E_π[Y] = E_ν[id]`: the first moment of a coupling is that of its second
marginal. -/
lemma coupling_integral_snd (h : IsCoupling π μ ν) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p : ℝ × ℝ, p.2 ∂π) = ∫ y : ℝ, y ∂ν := by
  have hν' : AEStronglyMeasurable (fun y : ℝ => y) (π.map Prod.snd) := by
    simpa [h.map_snd] using hν.aestronglyMeasurable
  rw [← h.map_snd]
  exact (integral_map measurable_snd.aemeasurable hν').symm

/-- `XY ∈ L¹(π)` by Cauchy–Schwarz from the two `L²` marginals. -/
lemma coupling_integrable_mul (h : IsCoupling π μ ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2) π := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  simpa [Pi.mul_apply] using
    (coupling_fst_memLp h hμ).integrable_mul (coupling_snd_memLp h hν)

/-! ### The fibre integrals -/

/-- The `π`-integral of the signed tail indicator of the first coordinate is the
marginal survival function minus the constant `𝟙{s<0}`:
`∫ p, (𝟙{s < p.1} - 𝟙{s < 0}) ∂π = SX s - 𝟙{s < 0}`. Uses
`∫ p, 𝟙{s < p.1} ∂π = π.real (Prod.fst ⁻¹' Ioi s)` and `π univ = 1`. -/
lemma integral_signedTail_fst (h : IsCoupling π μ ν) (s : ℝ) :
    (∫ p : ℝ × ℝ, signedTail p.1 s ∂π) = survFst π s - tailInd 0 s := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  let A : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioi s
  have hA : MeasurableSet A := measurableSet_Ioi.preimage measurable_fst
  have hfun :
      (fun p : ℝ × ℝ => signedTail p.1 s)
        = fun p : ℝ × ℝ => A.indicator (fun _ => (1 : ℝ)) p - tailInd 0 s := by
    funext p
    by_cases hsp : s < p.1 <;> simp [A, signedTail, tailInd_apply, hsp]
  have hInd : Integrable (fun p : ℝ × ℝ => A.indicator (fun _ => (1 : ℝ)) p) π :=
    (integrable_const (1 : ℝ)).indicator hA
  have hConst : Integrable (fun _ : ℝ × ℝ => tailInd 0 s) π :=
    integrable_const _
  have hIntA :
      (∫ p : ℝ × ℝ, A.indicator (fun _ => (1 : ℝ)) p ∂π) = π.real A := by
    simpa only using (integral_indicator_one (μ := π) (s := A) hA)
  rw [hfun, integral_sub hInd hConst, hIntA, integral_const]
  simp [survFst, A, Measure.real, smul_eq_mul]

/-- The `π`-integral of the signed tail indicator of the second coordinate. -/
lemma integral_signedTail_snd (h : IsCoupling π μ ν) (t : ℝ) :
    (∫ p : ℝ × ℝ, signedTail p.2 t ∂π) = survSnd π t - tailInd 0 t := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  let B : Set (ℝ × ℝ) := Prod.snd ⁻¹' Ioi t
  have hB : MeasurableSet B := measurableSet_Ioi.preimage measurable_snd
  have hfun :
      (fun p : ℝ × ℝ => signedTail p.2 t)
        = fun p : ℝ × ℝ => B.indicator (fun _ => (1 : ℝ)) p - tailInd 0 t := by
    funext p
    by_cases htp : t < p.2 <;> simp [B, signedTail, tailInd_apply, htp]
  have hInd : Integrable (fun p : ℝ × ℝ => B.indicator (fun _ => (1 : ℝ)) p) π :=
    (integrable_const (1 : ℝ)).indicator hB
  have hConst : Integrable (fun _ : ℝ × ℝ => tailInd 0 t) π :=
    integrable_const _
  have hIntB :
      (∫ p : ℝ × ℝ, B.indicator (fun _ => (1 : ℝ)) p ∂π) = π.real B := by
    simpa only using (integral_indicator_one (μ := π) (s := B) hB)
  rw [hfun, integral_sub hInd hConst, hIntB, integral_const]
  simp [survSnd, B, Measure.real, smul_eq_mul]

/-- **Fibre integral.** Expanding the product of two signed tail indicators into
four indicator products and integrating each against `π`:

    `∫ p, signedTail p.1 s * signedTail p.2 t ∂π
       = S s t - 𝟙{t<0}·SX s - 𝟙{s<0}·SY t + 𝟙{s<0}·𝟙{t<0}`,

where `S` is the joint survival function of `π` and `SX, SY` its marginal
survival functions. Each of the four terms is the `π`-mass of a measurable set
(the quadrant `Ioi s ×ˢ Ioi t`, the two half-planes, and `univ`). -/
lemma fiber_integral_pi (h : IsCoupling π μ ν) (s t : ℝ) :
    (∫ p : ℝ × ℝ, signedTail p.1 s * signedTail p.2 t ∂π)
      = jointSurv π s t - tailInd 0 t * survFst π s - tailInd 0 s * survSnd π t
        + tailInd 0 s * tailInd 0 t := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  let A : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioi s
  let B : Set (ℝ × ℝ) := Prod.snd ⁻¹' Ioi t
  let C : Set (ℝ × ℝ) := Ioi s ×ˢ Ioi t
  let a : ℝ := tailInd 0 s
  let b : ℝ := tailInd 0 t
  have hA : MeasurableSet A := measurableSet_Ioi.preimage measurable_fst
  have hB : MeasurableSet B := measurableSet_Ioi.preimage measurable_snd
  have hC : MeasurableSet C := measurableSet_Ioi.prod measurableSet_Ioi
  have hfun :
      (fun p : ℝ × ℝ => signedTail p.1 s * signedTail p.2 t)
        = fun p : ℝ × ℝ =>
            C.indicator (fun _ => (1 : ℝ)) p
              - b * A.indicator (fun _ => (1 : ℝ)) p
              - a * B.indicator (fun _ => (1 : ℝ)) p
              + a * b := by
    funext p
    by_cases hsp : s < p.1
    · by_cases htp : t < p.2
      · by_cases hs0 : s < 0 <;> by_cases ht0 : t < 0 <;>
          simp [A, B, C, a, b, signedTail, tailInd_apply, hsp, htp,
            hs0, ht0]
      · by_cases hs0 : s < 0 <;> by_cases ht0 : t < 0 <;>
          simp [A, B, C, a, b, signedTail, tailInd_apply, hsp, htp,
            hs0, ht0]
    · by_cases htp : t < p.2
      · by_cases hs0 : s < 0 <;> by_cases ht0 : t < 0 <;>
          simp [A, B, C, a, b, signedTail, tailInd_apply, hsp, htp,
            hs0, ht0]
      · by_cases hs0 : s < 0 <;> by_cases ht0 : t < 0 <;>
          simp [A, B, C, a, b, signedTail, tailInd_apply, hsp, htp,
            hs0, ht0]
  have hIA : Integrable (fun p : ℝ × ℝ => A.indicator (fun _ => (1 : ℝ)) p) π :=
    (integrable_const (1 : ℝ)).indicator hA
  have hIB : Integrable (fun p : ℝ × ℝ => B.indicator (fun _ => (1 : ℝ)) p) π :=
    (integrable_const (1 : ℝ)).indicator hB
  have hIC : Integrable (fun p : ℝ × ℝ => C.indicator (fun _ => (1 : ℝ)) p) π :=
    (integrable_const (1 : ℝ)).indicator hC
  have hBA : Integrable (fun p : ℝ × ℝ => b * A.indicator (fun _ => (1 : ℝ)) p) π :=
    hIA.const_mul b
  have hAB : Integrable (fun p : ℝ × ℝ => a * B.indicator (fun _ => (1 : ℝ)) p) π :=
    hIB.const_mul a
  have hK : Integrable (fun _ : ℝ × ℝ => a * b) π := integrable_const _
  have hIntA :
      (∫ p : ℝ × ℝ, A.indicator (fun _ => (1 : ℝ)) p ∂π) = π.real A := by
    simpa only using (integral_indicator_one (μ := π) (s := A) hA)
  have hIntB :
      (∫ p : ℝ × ℝ, B.indicator (fun _ => (1 : ℝ)) p ∂π) = π.real B := by
    simpa only using (integral_indicator_one (μ := π) (s := B) hB)
  have hIntC :
      (∫ p : ℝ × ℝ, C.indicator (fun _ => (1 : ℝ)) p ∂π) = π.real C := by
    simpa only using (integral_indicator_one (μ := π) (s := C) hC)
  rw [hfun]
  change
    (∫ p : ℝ × ℝ,
        (((fun p : ℝ × ℝ => C.indicator (fun _ => (1 : ℝ)) p)
            - (fun p : ℝ × ℝ => b * A.indicator (fun _ => (1 : ℝ)) p)
            - (fun p : ℝ × ℝ => a * B.indicator (fun _ => (1 : ℝ)) p))
            + (fun _ : ℝ × ℝ => a * b)) p ∂π)
      = jointSurv π s t - tailInd 0 t * survFst π s - tailInd 0 s * survSnd π t
        + tailInd 0 s * tailInd 0 t
  rw [integral_add' ((hIC.sub hBA).sub hAB) hK]
  rw [integral_sub' (hIC.sub hBA) hAB]
  rw [integral_sub' hIC hBA]
  rw [integral_const_mul, integral_const_mul]
  rw [hIntA, hIntB, hIntC, integral_const]
  simp [jointSurv, survFst, survSnd, A, B, C, a, b, Measure.real, smul_eq_mul]

/-! ### Integrability on the triple product, and the two swaps -/

end Causalean.Stat
