/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Directional functional delta method for lattice functionals

The ordinary delta method (`Stat/Inference/DeltaMethod.lean`) pushes a CLT
through a *Fréchet*-differentiable map.  Many partial-identification bound
functionals are **not** Fréchet differentiable: an interval-identified
parameter's sharp endpoints are `sup'`/`inf'` of separately estimable
quantities (intersections of interval bounds `⋂ⱼ [Lⱼ, Uⱼ] = [sup' L, inf' U]`;
Manski MIV envelopes; combined MTR + MTS bounds).  Such `max`/`min` functionals
are only
*Hadamard directionally* differentiable (`Stat/Inference/HadamardDeriv.lean`),
and the derivative is **nonlinear at a tie** — which is exactly the
*binding*/kink regime where inference is delicate (Hirano–Porter 2012;
Fang–Santos 2019).

This file gives the directional delta theorem for `max`/`min : ℝ × ℝ → ℝ` at a
tie `a = b`, the case that the Fréchet delta method cannot reach.  At a tie the
rescaled image equals the functional applied to the joint rescaled deviation
*exactly*,

    √n · (max (âₙ) (b̂ₙ) − a)  =  max (√n (âₙ − a)) (√n (b̂ₙ − a)),

so the limit is obtained from the joint CLT by the continuous mapping theorem
(`Tendsto_dist_vec.map_continuous`), with **no** linearization remainder.  The
limit law `Q.map (z ↦ max z.1 z.2)` is the pushforward of the joint Gaussian —
generally *not* Gaussian (it is the law of `max(Z₁, Z₂)`).

Off the diagonal (`a ≠ b`) the functional is locally linear and the limit
reduces to an ordinary marginal CLT via a vanishing-probability Slutsky
argument; `isLittleOp_one_of_measure_ne_tendsto_zero` below is the reusable
ingredient for that case.

Reference: van der Vaart (1998) §20.2; Fang & Santos (2019), Rev. Econ. Stud.
-/

import Causalean.Stat.Inference.HadamardDeriv
import Causalean.Stat.Limit.ConvergenceVec
import Causalean.Stat.CLT.AsymptoticLinearity

/-!
This file develops the directional functional delta method for max/min lattice
functionals.  It provides the reusable Slutsky lemma
`isLittleOp_one_of_measure_ne_tendsto_zero`, probability-measure instances for
`Q.map max` and `Q.map min`, exact tie identities `sqrt_mul_max_sub` and
`sqrt_mul_min_sub`, and derived measurability lemmas for the image statistics.

The headline theorems `deltaMethod_max_tie` and `deltaMethod_min_tie` cover the
binding case `a = b`: a joint CLT for `√n • ((an,bn) - (a,a))` is pushed through
the continuous lattice functional, yielding the generally non-Gaussian laws
`Q.map (fun z => max z.1 z.2)` and `Q.map (fun z => min z.1 z.2)`.
-/

namespace Causalean.Stat

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Reusable Slutsky ingredient: a vanishing-probability difference is `o_p(1)` -/

omit [IsProbabilityMeasure μ] in
/-- If `Yₙ` and `Xₙ` agree except on an event of vanishing probability, then
`Yₙ − Xₙ = o_p(1)`.  This is the device that handles the *off-diagonal* case of
the directional delta method (where the lattice functional locally selects one
coordinate, so the rescaled image equals that coordinate's marginal except when
the estimated ordering is wrong — an event whose probability tends to `0`). -/
theorem isLittleOp_one_of_measure_ne_tendsto_zero {Xn Yn : ℕ → Ω → ℝ}
    (h : Tendsto (fun n => μ {ω | Yn n ω ≠ Xn n ω}) atTop (𝓝 0)) :
    IsLittleOp (fun n ω => Yn n ω - Xn n ω) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hsub : ∀ n, {ω | ε * (1 : ℝ) < |Yn n ω - Xn n ω|} ⊆ {ω | Yn n ω ≠ Xn n ω} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro heq
    rw [heq, sub_self, abs_zero, mul_one] at hω
    exact absurd hω (not_lt.2 (le_of_lt hε))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => zero_le _) (fun n => measure_mono (hsub n))

/-! ## Probability-measure instances for the lattice pushforwards

The limit law of the rescaled image is the pushforward of the joint limit by the
continuous lattice functional; it is automatically a probability measure, so the
`Tendsto_dist` conclusion below carries that instance *without it being assumed*. -/

/-- The maximum of a two-dimensional probability limit is itself a probability
law. -/
instance instIsProbabilityMeasure_map_max (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (Q.map (fun z : ℝ × ℝ => max z.1 z.2)) :=
  Measure.isProbabilityMeasure_map
    (continuous_fst.max continuous_snd).measurable.aemeasurable

/-- The minimum of a two-dimensional probability limit is itself a probability
law. -/
instance instIsProbabilityMeasure_map_min (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (Q.map (fun z : ℝ × ℝ => min z.1 z.2)) :=
  Measure.isProbabilityMeasure_map
    (continuous_fst.min continuous_snd).measurable.aemeasurable

/-! ## The exact tie identity and the derived measurability of the image statistic

At a tie `a = b` the rescaled image equals the lattice functional applied to the
joint rescaled deviation *exactly*; from this identity the image statistic's
`AEMeasurability` is *derived* from the joint deviation's, so it need not be
assumed either. -/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **The tie identity for `max`.**
`√n (max âₙ b̂ₙ − a) = max (√n(âₙ−a)) (√n(b̂ₙ−a))` (no remainder). -/
lemma sqrt_mul_max_sub (an bn : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) * (max (an n ω) (bn n ω) - a)
      = (fun z : ℝ × ℝ => max z.1 z.2)
          (Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) := by
  have hsnn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← mul_max_of_nonneg _ _ hsnn]
  congr 1
  rcases le_total (an n ω) (bn n ω) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **The tie identity for `min`.**  Companion to `sqrt_mul_max_sub`. -/
lemma sqrt_mul_min_sub (an bn : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) * (min (an n ω) (bn n ω) - a)
      = (fun z : ℝ × ℝ => min z.1 z.2)
          (Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) := by
  have hsnn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← mul_min_of_nonneg _ _ hsnn]
  congr 1
  rcases le_total (an n ω) (bn n ω) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]

omit [IsProbabilityMeasure μ] in
/-- The image statistic `√n (max âₙ b̂ₙ − a)` is `AEMeasurable` for every `n`,
*derived* from the joint rescaled deviation's measurability via `sqrt_mul_max_sub`
— so `deltaMethod_max_tie` need not assume it. -/
lemma maxStat_aemeasurable (an bn : ℕ → Ω → ℝ) (a : ℝ)
    (hSn_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω => Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) μ) :
    ∀ (n : ℕ), AEMeasurable
      (fun ω => Real.sqrt (n : ℝ) * (max (an n ω) (bn n ω) - a)) μ := fun n =>
  ((continuous_fst.max continuous_snd).measurable.comp_aemeasurable (hSn_meas n)).congr
    (Filter.Eventually.of_forall fun ω => (sqrt_mul_max_sub an bn a n ω).symm)

omit [IsProbabilityMeasure μ] in
/-- The image statistic `√n (min âₙ b̂ₙ − a)` is `AEMeasurable` for every `n`,
derived likewise via `sqrt_mul_min_sub`. -/
lemma minStat_aemeasurable (an bn : ℕ → Ω → ℝ) (a : ℝ)
    (hSn_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω => Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) μ) :
    ∀ (n : ℕ), AEMeasurable
      (fun ω => Real.sqrt (n : ℝ) * (min (an n ω) (bn n ω) - a)) μ := fun n =>
  ((continuous_fst.min continuous_snd).measurable.comp_aemeasurable (hSn_meas n)).congr
    (Filter.Eventually.of_forall fun ω => (sqrt_mul_min_sub an bn a n ω).symm)

/-! ## Directional delta method at a tie -/

/-- **Directional delta method for `max` at a tie.**  Suppose the joint rescaled
deviation `√n • ((âₙ, b̂ₙ) − (a, a))` converges in distribution to `Q` on
`ℝ × ℝ`.  Then

    √n · (max (âₙ) (b̂ₙ) − a)  ⇒  Q.map (z ↦ max z.1 z.2).

This is the directional delta method at the binding point `a = b`, where `max`
is Hadamard directionally (but not Fréchet) differentiable
(`hasHadamardDirDerivAt_max`); the proof is the continuous mapping theorem
applied to the exact identity
`√n (max âₙ b̂ₙ − a) = max (√n(âₙ−a)) (√n(b̂ₙ−a))`. -/
theorem deltaMethod_max_tie
    (an bn : ℕ → Ω → ℝ) (a : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (hSn_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω => Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) μ)
    (hCLT : Tendsto_dist_vec
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) Q μ hSn_meas) :
    Tendsto_dist (fun (n : ℕ) ω => Real.sqrt (n : ℝ) * (max (an n ω) (bn n ω) - a))
      (Q.map (fun z : ℝ × ℝ => max z.1 z.2)) μ (maxStat_aemeasurable an bn a hSn_meas) := by
  -- continuous mapping theorem on the joint CLT: the rescaled image is `max ∘ Sₙ`
  -- exactly (`sqrt_mul_max_sub`), with no linearization remainder.
  have hgmeas : ∀ (n : ℕ), AEMeasurable
      (fun ω => (fun z : ℝ × ℝ => max z.1 z.2)
        (Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a)))) μ := fun (n : ℕ) =>
    (continuous_fst.max continuous_snd).measurable.comp_aemeasurable (hSn_meas n)
  have hmap := Tendsto_dist_vec.map_continuous (continuous_fst.max continuous_snd)
    hSn_meas hgmeas hCLT
  -- transport `max ∘ Sₙ ⇒ Q.map max` to the (pointwise-equal) rescaled image
  exact hmap.congr_ae hgmeas (maxStat_aemeasurable an bn a hSn_meas)
    (Eventually.of_forall fun n => Eventually.of_forall fun ω =>
      (sqrt_mul_max_sub an bn a n ω).symm)

/-- **Directional delta method for `min` at a tie.**  Companion to
`deltaMethod_max_tie`: at `a = b`,

    √n · (min (âₙ) (b̂ₙ) − a)  ⇒  Q.map (z ↦ min z.1 z.2). -/
theorem deltaMethod_min_tie
    (an bn : ℕ → Ω → ℝ) (a : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (hSn_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω => Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) μ)
    (hCLT : Tendsto_dist_vec
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a))) Q μ hSn_meas) :
    Tendsto_dist (fun (n : ℕ) ω => Real.sqrt (n : ℝ) * (min (an n ω) (bn n ω) - a))
      (Q.map (fun z : ℝ × ℝ => min z.1 z.2)) μ (minStat_aemeasurable an bn a hSn_meas) := by
  have hgmeas : ∀ (n : ℕ), AEMeasurable
      (fun ω => (fun z : ℝ × ℝ => min z.1 z.2)
        (Real.sqrt (n : ℝ) • ((an n ω, bn n ω) - (a, a)))) μ := fun (n : ℕ) =>
    (continuous_fst.min continuous_snd).measurable.comp_aemeasurable (hSn_meas n)
  have hmap := Tendsto_dist_vec.map_continuous (continuous_fst.min continuous_snd)
    hSn_meas hgmeas hCLT
  -- transport `min ∘ Sₙ ⇒ Q.map min` to the (pointwise-equal) rescaled image
  exact hmap.congr_ae hgmeas (minStat_aemeasurable an bn a hSn_meas)
    (Eventually.of_forall fun n => Eventually.of_forall fun ω =>
      (sqrt_mul_min_sub an bn a n ω).symm)

end Causalean.Stat
