/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The signed tail representation of a real number

The elementary identity behind Hoeffding's covariance formula is that every real
number is the Lebesgue integral of a *signed tail indicator*:

    `a = ∫ s, (𝟙{s < a} - 𝟙{s < 0}) ds`.

Indeed the integrand vanishes outside the interval between `0` and `a`, where it
equals `+1` (if `a ≥ 0`) or `-1` (if `a < 0`), so the integral is the signed
length `a`.

This file packages that identity, its integrability, and the corresponding
statements for the *product* `signedTail x s * signedTail y t` on `ℝ × ℝ`, which
represents the product `x * y` as a two-dimensional Lebesgue integral:

    `x * y = ∫∫ (𝟙{s < x} - 𝟙{s < 0})(𝟙{t < y} - 𝟙{t < 0}) ds dt`.

Together with the `L¹` bound `∫∫ |·| = |x| * |y|` (which is what makes the
downstream Fubini swap legitimate for `L²` marginals, via Cauchy–Schwarz), this
is the entire analytic input to `hoeffding_cov_identity`.
-/

namespace Causalean.Stat

open MeasureTheory Set

/-- `tailInd a s` is the indicator `𝟙{s < a}`, i.e. `1` when `s < a` and `0`
otherwise, written as the indicator function of the ray `Iio a`. -/
noncomputable def tailInd (a s : ℝ) : ℝ := (Iio a).indicator (fun _ => (1 : ℝ)) s

/-- `signedTail a s = 𝟙{s < a} - 𝟙{s < 0}`, the *signed tail indicator* of `a`.
As a function of `s` it is `+1` on `[0, a)` when `a ≥ 0`, `-1` on `[a, 0)` when
`a < 0`, and `0` elsewhere; its Lebesgue integral is exactly `a`. -/
noncomputable def signedTail (a s : ℝ) : ℝ := tailInd a s - tailInd 0 s

/-- The tail indicator equals one below the threshold and zero at or above it. -/
@[simp] lemma tailInd_apply (a s : ℝ) : tailInd a s = if s < a then 1 else 0 := by
  simp [tailInd, Set.indicator_apply, Set.mem_Iio]

/-- `signedTail a` is, as a function of `s`, the difference of the indicators of
the two intervals `Ico 0 a` and `Ico a 0` (at most one of which is nonempty).
This is the normal form used to compute its integral and to see it is
integrable. -/
lemma signedTail_eq_indicator_sub (a : ℝ) :
    signedTail a =
      (Ico 0 a).indicator (fun _ => (1 : ℝ)) - (Ico a 0).indicator (fun _ => (1 : ℝ)) := by
  funext s
  by_cases hsa : s < a <;> by_cases hs0 : s < 0 <;>
    simp [signedTail, tailInd_apply, Set.indicator_apply, Set.mem_Ico, hsa, hs0]

/-- `signedTail a` is measurable in the tail variable `s`. -/
lemma measurable_signedTail (a : ℝ) : Measurable (signedTail a) := by
  rw [signedTail_eq_indicator_sub]
  exact (measurable_const.indicator measurableSet_Ico).sub
    (measurable_const.indicator measurableSet_Ico)

/-- `signedTail` is jointly measurable in `(a, s)`, since `{z | z.2 < z.1}` is
an open (hence measurable) subset of `ℝ × ℝ`. -/
lemma measurable_signedTail_uncurry :
    Measurable (fun z : ℝ × ℝ => signedTail z.1 z.2) := by
  have hxa : MeasurableSet {z : ℝ × ℝ | z.2 < z.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have hx0 : MeasurableSet {z : ℝ × ℝ | z.2 < (0 : ℝ)} :=
    measurableSet_lt measurable_snd measurable_const
  have h1 : Measurable (fun z : ℝ × ℝ =>
      ({z : ℝ × ℝ | z.2 < z.1}.indicator (fun _ => (1 : ℝ)) z)) :=
    measurable_const.indicator hxa
  have h0 : Measurable (fun z : ℝ × ℝ =>
      ({z : ℝ × ℝ | z.2 < (0 : ℝ)}.indicator (fun _ => (1 : ℝ)) z)) :=
    measurable_const.indicator hx0
  simpa [signedTail, tailInd, Set.indicator_apply, Set.mem_Iio] using h1.sub h0

/-- The signed tail indicator is bounded by `1` in absolute value. -/
lemma abs_signedTail_le_one (a s : ℝ) : |signedTail a s| ≤ 1 := by
  simp [signedTail, tailInd_apply]
  split_ifs <;> norm_num

/-- `signedTail a` is Lebesgue integrable: it is a bounded function supported on
a bounded interval. -/
lemma integrable_signedTail (a : ℝ) : Integrable (signedTail a) volume := by
  rw [signedTail_eq_indicator_sub]
  refine Integrable.sub ?_ ?_
  · refine (integrableOn_const (μ := volume) (s := Ico (0 : ℝ) a)
      (hs := ?_)).integrable_indicator measurableSet_Ico
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  · refine (integrableOn_const (μ := volume) (s := Ico a (0 : ℝ))
      (hs := ?_)).integrable_indicator measurableSet_Ico
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top

/-- **Signed tail representation.** `∫ s, (𝟙{s < a} - 𝟙{s < 0}) ds = a`. -/
lemma integral_signedTail (a : ℝ) : (∫ s : ℝ, signedTail a s ∂volume) = a := by
  have hrw : (fun s : ℝ => signedTail a s)
      = fun s : ℝ => (({s : ℝ | s < a}.indicator (fun _ : ℝ => (1 : ℝ)) s) -
          ({s : ℝ | s < 0}.indicator (fun _ : ℝ => (1 : ℝ)) s)) := rfl
  rw [hrw]
  by_cases ha : 0 ≤ a
  · have hdiff :
        (fun s : ℝ => ({s : ℝ | s < a}.indicator (fun _ : ℝ => (1 : ℝ)) s) -
          ({s : ℝ | s < 0}.indicator (fun _ : ℝ => (1 : ℝ)) s))
          = (Ico (0 : ℝ) a).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext s
      by_cases hsa : s < a
      · by_cases hs0 : s < 0
        · have hsI : s ∉ Ico (0 : ℝ) a := by simp [Set.mem_Ico, not_le_of_gt hs0]
          simp [hsa, hs0, hsI]
        · have hsI : s ∈ Ico (0 : ℝ) a := ⟨le_of_not_gt hs0, hsa⟩
          simp [hsa, hs0, hsI]
      · have hs0 : ¬ s < 0 := fun hs0 => hsa (lt_of_lt_of_le hs0 ha)
        have hsI : s ∉ Ico (0 : ℝ) a := fun hsI => hsa hsI.2
        simp [hsa, hs0, hsI]
    rw [hdiff]
    have hint :
        (∫ s : ℝ, (Ico (0 : ℝ) a).indicator (fun _ : ℝ => (1 : ℝ)) s ∂volume)
          = volume.real (Ico (0 : ℝ) a) := by
      simpa only using
        (integral_indicator_one (μ := volume) (s := Ico (0 : ℝ) a) measurableSet_Ico)
    rw [hint, measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal]
    · ring
    · exact sub_nonneg.mpr ha
  · have hle : a ≤ 0 := le_of_not_ge ha
    have hdiff :
        (fun s : ℝ => ({s : ℝ | s < a}.indicator (fun _ : ℝ => (1 : ℝ)) s) -
          ({s : ℝ | s < 0}.indicator (fun _ : ℝ => (1 : ℝ)) s))
          = (Ico a (0 : ℝ)).indicator (fun _ : ℝ => (-1 : ℝ)) := by
      funext s
      by_cases hsa : s < a
      · have hs0 : s < 0 := lt_of_lt_of_le hsa hle
        have hsI : s ∉ Ico a (0 : ℝ) := fun hsI => (not_lt_of_ge hsI.1) hsa
        simp [hsa, hs0, hsI]
      · by_cases hs0 : s < 0
        · have hsI : s ∈ Ico a (0 : ℝ) := ⟨le_of_not_gt hsa, hs0⟩
          simp [hsa, hs0, hsI]
        · have hsI : s ∉ Ico a (0 : ℝ) := fun hsI => hs0 hsI.2
          simp [hsa, hs0, hsI]
    rw [hdiff]
    calc
      (∫ s : ℝ, (Ico a (0 : ℝ)).indicator (fun _ : ℝ => (-1 : ℝ)) s ∂volume)
          = volume.real (Ico a (0 : ℝ)) * (-1 : ℝ) := by
            rw [integral_indicator_const (-1 : ℝ) measurableSet_Ico]
            simp [smul_eq_mul]
      _ = a := by
            rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal]
            · ring
            · exact sub_nonneg.mpr hle

/-- The `L¹` norm of the signed tail indicator is `|a|`: the integrand is `±1`
on an interval of length `|a|`. -/
lemma integral_abs_signedTail (a : ℝ) : (∫ s : ℝ, |signedTail a s| ∂volume) = |a| := by
  by_cases ha : 0 ≤ a
  · have hnonneg : ∀ s : ℝ, 0 ≤ signedTail a s := by
      intro s
      simp [signedTail, tailInd_apply]
      split_ifs <;> linarith
    have habs : (fun s : ℝ => |signedTail a s|) = signedTail a := by
      funext s
      exact abs_of_nonneg (hnonneg s)
    rw [habs, integral_signedTail, abs_of_nonneg ha]
  · have hlt : a < 0 := lt_of_not_ge ha
    have hnonpos : ∀ s : ℝ, signedTail a s ≤ 0 := by
      intro s
      simp [signedTail, tailInd_apply]
      split_ifs <;> linarith
    have habs : (fun s : ℝ => |signedTail a s|) = fun s : ℝ => -signedTail a s := by
      funext s
      exact abs_of_nonpos (hnonpos s)
    rw [habs, integral_neg, integral_signedTail, abs_of_neg hlt]

/-- The tensor product `(s, t) ↦ signedTail x s * signedTail y t` is integrable
on `ℝ × ℝ` for Lebesgue×Lebesgue. -/
lemma integrable_signedTail_prod (x y : ℝ) :
    Integrable (fun q : ℝ × ℝ => signedTail x q.1 * signedTail y q.2)
      (volume.prod volume) :=
  (integrable_signedTail x).mul_prod (integrable_signedTail y)

/-- **Product tail representation.** `x * y` is the two-dimensional integral of
the product of the two signed tail indicators:
`∫∫ (𝟙{s<x} - 𝟙{s<0})(𝟙{t<y} - 𝟙{t<0}) ds dt = x * y`. -/
lemma integral_signedTail_prod (x y : ℝ) :
    (∫ q : ℝ × ℝ, signedTail x q.1 * signedTail y q.2 ∂(volume.prod volume)) = x * y := by
  rw [integral_prod_mul (fun s => signedTail x s) (fun t => signedTail y t),
    integral_signedTail, integral_signedTail]

/-- The `L¹` norm of the product tail representation is `|x| * |y|`. This is the
domination bound that makes the Fubini swap against an `L²` coupling valid:
its `π`-integral is `E|XY| < ∞` by Cauchy–Schwarz. -/
lemma integral_norm_signedTail_prod (x y : ℝ) :
    (∫ q : ℝ × ℝ, ‖signedTail x q.1 * signedTail y q.2‖ ∂(volume.prod volume))
      = |x| * |y| := by
  simp only [norm_mul, Real.norm_eq_abs]
  rw [integral_prod_mul (fun s : ℝ => |signedTail x s|)
    (fun t : ℝ => |signedTail y t|), integral_abs_signedTail, integral_abs_signedTail]

end Causalean.Stat
