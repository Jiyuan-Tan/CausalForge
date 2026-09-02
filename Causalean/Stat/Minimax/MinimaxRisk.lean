/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic minimax risk packaging

Causal-agnostic specialization of the Le Cam two-point bound
(`Causalean/Stat/Minimax/LeCam.lean`) to a **real-valued functional** `τ` estimated
from `n` i.i.d. samples.  This is the shape consumed by minimax lower bounds for
concrete estimands (e.g. the structure-agnostic ATE optimality theorem, which
lives in the causal `Estimation/` tree, not here).

Main results:

* `real_two_point_lower_bound` — Le Cam specialized to `Θ = ℝ`: under `2s`-separation
  `2s ≤ |θ₀ − θ₁|`, every estimator's worst-case miss probability is `≥ ½(1 − tvDist)`.
* `two_point_lower_bound_of_tvDist_le` — same with an explicit upper bound `c` on `tvDist`.
* `iid_two_point_lower_bound` — the `n`-sample version: the data law is the product
  `Measure.pi (fun _ : Fin n ↦ P)` and the separation is on the functional values
  `τ P₀, τ P₁`.
* `two_point_lower_bound_of_chiSqDiv_le` — the χ²-divergence form obtained from
  `tvDist ≤ ½√χ²`, useful when explicit finite or product χ² computations are
  available.
* `mse_integrable_of_estimator_bound` — bounded-estimator bookkeeping for squared
  losses, used before MSE lower bounds can be applied to truncated estimators.
* `integral_le_sSup_range_of_isProbabilityMeasure` — the Bayes-risk step: the average of a
  risk function against any prior probability measure is at most its worst-case value, so a
  minimax lower bound follows from a lower bound on a single prior's Bayes risk.

These statements remain project-agnostic: concrete causal or nonparametric lower
bounds import this layer after constructing the two laws, the functional
separation, and the required divergence estimate.
-/

import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.ChiSquared
import Causalean.Stat.Sample.PiTransport

import Mathlib.MeasureTheory.Constructions.Pi

/-! # Minimax Risk Lower Bounds

This file specializes Le Cam's two-point method to real-valued statistical
functionals and to estimators based on independent repeated samples. It records
the total-variation, chi-squared-divergence, and bounded-estimator integrability
forms used to certify concrete minimax rates. -/

namespace Causalean.Stat

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P₀ P₁ : Measure Ω}
  [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]

/-- **Le Cam two-point bound for a real-valued parameter.**  If [two candidate values
`θ₀, θ₁ : ℝ` are `2s`-separated](hyp:hsep), then for [any measurable estimator
`est : Ω → ℝ`](hyp:hest), [the worst-case probability of missing the truth by `≥ s` is at least
`½(1 − tvDist P₀ P₁)`](goal). Specialization of `half_one_sub_tvDist_le_max_error` to `Θ = ℝ`
with `dist a b = |a − b|`. -/
theorem real_two_point_lower_bound {est : Ω → ℝ} (hest : Measurable est)
    {θ₀ θ₁ s : ℝ} (hsep : 2 * s ≤ |θ₀ - θ₁|) :
    (1 - tvDist P₀ P₁) / 2
      ≤ max (P₀.real {ω | s ≤ |est ω - θ₀|}) (P₁.real {ω | s ≤ |est ω - θ₁|}) := by
  have hsep' : 2 * s ≤ dist θ₀ θ₁ := by rwa [Real.dist_eq]
  have h := half_one_sub_tvDist_le_max_error (P₀ := P₀) (P₁ := P₁) (Θ := ℝ) hest hsep'
  simpa only [Real.dist_eq] using h

/-- **Le Cam two-point bound with an explicit total-variation bound.**  If [two candidate
values `θ₀, θ₁ : ℝ` are `2s`-separated](hyp:hsep), [`est : Ω → ℝ` is a measurable
estimator](hyp:hest), and [the total variation distance `tvDist P₀ P₁` is at most `c`](hyp:hc),
then [the worst-case probability of missing the truth by `≥ s` is at least `(1 − c)/2`](goal).
Variant of `real_two_point_lower_bound` with an explicit total-variation upper bound. -/
theorem two_point_lower_bound_of_tvDist_le {est : Ω → ℝ} (hest : Measurable est)
    {θ₀ θ₁ s c : ℝ} (hsep : 2 * s ≤ |θ₀ - θ₁|) (hc : tvDist P₀ P₁ ≤ c) :
    (1 - c) / 2
      ≤ max (P₀.real {ω | s ≤ |est ω - θ₀|}) (P₁.real {ω | s ≤ |est ω - θ₁|}) := by
  have h := real_two_point_lower_bound (P₀ := P₀) (P₁ := P₁) hest hsep
  have : (1 - c) / 2 ≤ (1 - tvDist P₀ P₁) / 2 := by linarith
  exact this.trans h

/-- **`n`-sample structure-agnostic two-point bound.**  Given two single-observation laws `P₀`,
`P₁` and a real functional `τ` such that [the functional values `τ P₀, τ P₁` are
`2s`-separated](hyp:hsep), then for [any measurable estimator `est` built from `n` i.i.d.
samples (data law `Measure.pi (fun _ ↦ Pⱼ)`)](hyp:hest), [the worst-case miss probability,
using `τ P₀` and `τ P₁` as the two parameters, is at least `½(1 − tvDist)` between the two
`n`-fold product laws](goal). -/
theorem iid_two_point_lower_bound {S : Type*} [MeasurableSpace S]
    (P₀ P₁ : Measure S) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (τ : Measure S → ℝ) (n : ℕ) {s : ℝ} (hsep : 2 * s ≤ |τ P₀ - τ P₁|)
    {est : (Fin n → S) → ℝ} (hest : Measurable est) :
    (1 - tvDist (Measure.pi fun _ : Fin n => P₀) (Measure.pi fun _ : Fin n => P₁)) / 2
      ≤ max ((Measure.pi fun _ : Fin n => P₀).real {x | s ≤ |est x - τ P₀|})
            ((Measure.pi fun _ : Fin n => P₁).real {x | s ≤ |est x - τ P₁|}) :=
  real_two_point_lower_bound (P₀ := Measure.pi fun _ : Fin n => P₀)
    (P₁ := Measure.pi fun _ : Fin n => P₁) hest hsep

/-- **χ²-form two-point lower bound.**  For [a measurable estimator `est`](hyp:hest), if [two
candidate values `θ₀, θ₁` are `2s`-separated](hyp:hsep), [`P₀` is absolutely continuous with
respect to `P₁`](hyp:hac), [the squared density deviation `(dP₀/dP₁ − 1)²` is
`P₁`-integrable](hyp:hint), and [the χ²-divergence `chiSqDiv P₀ P₁` is at most `c`](hyp:hc),
then [the worst-case miss probability is at least `(1 − ½√c)/2`](goal), via `tvDist ≤ ½√χ²`.
Since `chiSqDiv` tensorizes over i.i.d. samples (`chiSqDiv_prod`) and is computable for explicit
families, this is the form used to certify minimax rates. -/
theorem two_point_lower_bound_of_chiSqDiv_le {est : Ω → ℝ} (hest : Measurable est)
    {θ₀ θ₁ s : ℝ} (hsep : 2 * s ≤ |θ₀ - θ₁|) (hac : P₀ ≪ P₁)
    (hint : Integrable (fun x => ((P₀.rnDeriv P₁ x).toReal - 1) ^ 2) P₁)
    {c : ℝ} (hc : chiSqDiv P₀ P₁ ≤ c) :
    (1 - (1 / 2) * Real.sqrt c) / 2
      ≤ max (P₀.real {ω | s ≤ |est ω - θ₀|}) (P₁.real {ω | s ≤ |est ω - θ₁|}) := by
  have htv : tvDist P₀ P₁ ≤ (1 / 2) * Real.sqrt c := by
    refine (tvDist_le_half_sqrt_chiSqDiv P₀ P₁ hac hint).trans ?_
    gcongr
  exact two_point_lower_bound_of_tvDist_le hest hsep htv

/-- **Squared-loss integrability for a truncated estimator.**  If a measurable estimator `T`
takes values in the bounded interval `[-M, M]` (with `M ≥ 0`), then under any finite measure `Q`
its squared loss `(T − θ)²` against an arbitrary target `θ` is integrable, because it is bounded
by the constant `(M + |θ|)²`.  This is the routine integrability bookkeeping needed before the
worst-case squared risk of a truncated estimator can be compared in a two-point lower bound. -/
lemma mse_integrable_of_estimator_bound {S : Type*} [MeasurableSpace S]
    (Q : Measure S) [IsFiniteMeasure Q] (T : S → ℝ) (hT : Measurable T)
    {M theta : ℝ} (hM : 0 ≤ M) (hbound : ∀ s, T s ∈ Set.Icc (-M) M) :
    Integrable (fun s => (T s - theta) ^ 2) Q := by
  refine Integrable.of_bound
    ((hT.sub measurable_const).pow_const (2 : ℕ)).aestronglyMeasurable
    ((M + |theta|) ^ 2) ?_
  filter_upwards with s
  have hTabs : |T s| ≤ M := abs_le.mpr (hbound s)
  have hsub : |T s - theta| ≤ M + |theta| :=
    (abs_sub (T s) theta).trans (add_le_add hTabs le_rfl)
  have hC : 0 ≤ M + |theta| := add_nonneg hM (abs_nonneg theta)
  have hsq : (T s - theta) ^ 2 ≤ (M + |theta|) ^ 2 := by
    nlinarith [hsub, abs_nonneg (T s - theta), hC, sq_abs (T s - theta)]
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (T s - theta))] using hsq

/-- **Bayes risk never exceeds worst-case risk.**  Averaging an integrable risk function over
the parameter space against any prior *probability* distribution gives at most the supremum of
that risk over the parameter space (assuming the risk is bounded above).  This is the step that
lets a minimax lower bound be certified by exhibiting a single prior and bounding its average
risk from below. -/
lemma integral_le_sSup_range_of_isProbabilityMeasure
    {Θ : Type*} [MeasurableSpace Θ]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (risk : Θ → ℝ) (hrisk : Integrable risk π)
    (hbounded : BddAbove (Set.range risk)) :
    ∫ θ, risk θ ∂π ≤ sSup (Set.range risk) := by
  have hpoint : ∀ θ, risk θ ≤ sSup (Set.range risk) :=
    fun θ => le_csSup hbounded (Set.mem_range_self θ)
  have hconst :
      Integrable (fun _ : Θ => sSup (Set.range risk)) π :=
    integrable_const _
  have hmono :
      (∫ θ, risk θ ∂π) ≤
        ∫ _ : Θ, sSup (Set.range risk) ∂π :=
    integral_mono hrisk hconst hpoint
  simpa using hmono

end Causalean.Stat


namespace Causalean.Stat

open MeasureTheory

universe uX uY uI

/-! ## Squared-risk transport through deterministic experiments

These results pull estimators back through deterministic observation rules and transfer
squared-risk lower bounds when the statistical target changes by a nondegenerate affine map.
The final theorem applies the same reduction directly to finite i.i.d. product experiments.
-/

variable {X : Type uX} {Y : Type uY} {Iota : Type uI}
  [MeasurableSpace X] [MeasurableSpace Y]

/-- The squared risk of a real-valued estimator is its expected squared error around a
specified real target. -/
noncomputable def sqRisk (law : Measure X) (est : X → ℝ) (theta : ℝ) : ℝ :=
  ∫ z, (est z - theta) ^ 2 ∂law

/-- The affine pullback estimator first applies the deterministic observation rule, then
subtracts the affine offset from the target estimator and divides by the affine slope. -/
noncomputable def affinePullbackEstimator (phi : X → Y) (a b : ℝ)
    (targetEst : Y → ℝ) : X → ℝ :=
  fun z => (targetEst (phi z) - b) / a

/-- If [the observation rule is measurable](hyp:hphi) and [the target estimator is
measurable](hyp:htarget), then [undoing an affine change after pulling the estimator back
through the observation rule is measurable](goal). -/
@[fun_prop]
theorem measurable_affinePullbackEstimator {phi : X → Y} {a b : ℝ}
    {targetEst : Y → ℝ} (hphi : Measurable phi)
    (htarget : Measurable targetEst) :
    Measurable (affinePullbackEstimator phi a b targetEst) := by
  exact ((htarget.comp hphi).sub measurable_const).div measurable_const

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- If [the affine slope is nonzero](hyp:ha), then [the squared error of a target estimator
after deterministic observation equals the squared error of its affine pullback multiplied
by the squared slope](goal), point by point. -/
theorem affine_sqLoss_pullback_identity {phi : X → Y} {a b theta : ℝ}
    {targetEst : Y → ℝ} (ha : a ≠ 0) (z : X) :
    a ^ 2 *
        (affinePullbackEstimator phi a b targetEst z - theta) ^ 2 =
      (targetEst (phi z) - (a * theta + b)) ^ 2 := by
  unfold affinePullbackEstimator
  field_simp
  ring

/-- If [the affine slope is nonzero](hyp:ha), [the deterministic observation rule is
measurable](hyp:hphi), and [the target estimator is measurable](hyp:htarget), then [its
squared risk under the pushed-forward law equals the pullback estimator's squared risk
multiplied by the squared slope](goal).

This identity uses the library's usual zero value for a nonintegrable integral, so it needs no
integrability assumption. -/
theorem sqRisk_map_affinePullback {law : Measure X} {phi : X → Y}
    {a b theta : ℝ} {targetEst : Y → ℝ} (ha : a ≠ 0)
    (hphi : Measurable phi) (htarget : Measurable targetEst) :
    a ^ 2 * sqRisk law (affinePullbackEstimator phi a b targetEst) theta =
      sqRisk (law.map phi) targetEst (a * theta + b) := by
  have hloss : Measurable (fun y => (targetEst y - (a * theta + b)) ^ 2) :=
    (htarget.sub measurable_const).pow_const 2
  unfold sqRisk
  calc
    a ^ 2 * (∫ z, (affinePullbackEstimator phi a b targetEst z - theta) ^ 2 ∂law) =
        ∫ z, a ^ 2 *
          (affinePullbackEstimator phi a b targetEst z - theta) ^ 2 ∂law :=
      (integral_const_mul (a ^ 2) _).symm
    _ = ∫ z, (targetEst (phi z) - (a * theta + b)) ^ 2 ∂law := by
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun z => affine_sqLoss_pullback_identity ha z)
    _ = ∫ y, (targetEst y - (a * theta + b)) ^ 2 ∂law.map phi :=
      (integral_map hphi.aemeasurable hloss.aestronglyMeasurable).symm

/-- Suppose [the affine slope is nonzero](hyp:ha), [the observation rule is
measurable](hyp:hphi), and [each target-experiment law is the pushforward of its corresponding
source law](hyp:hQ). If [every measurable source estimator has squared risk at least a fixed
level for some parameter](hyp:hsource), then [every measurable target estimator has squared
risk at least that level multiplied by the squared affine slope for some parameter](goal),
where the target parameter is transformed by the same affine map. -/
theorem forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport
    (P : Iota → Measure X) (Q : Iota → Measure Y)
    (theta : Iota → ℝ) (phi : X → Y) (a b L : ℝ)
    (ha : a ≠ 0) (hphi : Measurable phi)
    (hQ : ∀ j, Q j = (P j).map phi)
    (hsource : ∀ sourceEst : X → ℝ, Measurable sourceEst →
      ∃ j, L ≤ sqRisk (P j) sourceEst (theta j)) :
    ∀ targetEst : Y → ℝ, Measurable targetEst →
      ∃ j, a ^ 2 * L ≤ sqRisk (Q j) targetEst (a * theta j + b) := by
  intro targetEst htarget
  obtain ⟨j, hj⟩ := hsource (affinePullbackEstimator phi a b targetEst)
    (measurable_affinePullbackEstimator hphi htarget)
  refine ⟨j, ?_⟩
  calc
    a ^ 2 * L ≤
        a ^ 2 * sqRisk (P j) (affinePullbackEstimator phi a b targetEst) (theta j) :=
      mul_le_mul_of_nonneg_left hj (sq_nonneg a)
    _ = sqRisk ((P j).map phi) targetEst (a * theta j + b) :=
      sqRisk_map_affinePullback ha hphi htarget
    _ = sqRisk (Q j) targetEst (a * theta j + b) := by rw [hQ j]

/-- Suppose every source law is a probability law, [the affine slope is
nonzero](hyp:ha), [the observation rule is measurable](hyp:hphi), and [each target marginal
law is the pushforward of its corresponding source marginal](hyp:hQ). If [every measurable
estimator based on the finite source product experiment has squared risk at least a fixed level
for some parameter](hyp:hsource), then [every measurable estimator based on the corresponding
target product experiment has squared risk at least that level multiplied by the squared affine
slope for some parameter](goal), including when the sample has no coordinates. -/
theorem forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport_pi
    (n : ℕ) (P : Iota → Measure X) (Q : Iota → Measure Y)
    [∀ j, IsProbabilityMeasure (P j)]
    (theta : Iota → ℝ) (phi : X → Y) (a b L : ℝ)
    (ha : a ≠ 0) (hphi : Measurable phi)
    (hQ : ∀ j, Q j = (P j).map phi)
    (hsource : ∀ sourceEst : (Fin n → X) → ℝ, Measurable sourceEst →
      ∃ j, L ≤ sqRisk (Measure.pi (fun _ : Fin n => P j))
        sourceEst (theta j)) :
    ∀ targetEst : (Fin n → Y) → ℝ, Measurable targetEst →
      ∃ j, a ^ 2 * L ≤
        sqRisk (Measure.pi (fun _ : Fin n => Q j))
          targetEst (a * theta j + b) := by
  apply forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport
    (P := fun j => Measure.pi (fun _ : Fin n => P j))
    (Q := fun j => Measure.pi (fun _ : Fin n => Q j))
    (theta := theta) (phi := fun z i => phi (z i))
    (a := a) (b := b) (L := L) ha (measurable_finCoordinatewise n hphi) ?_ hsource
  intro j
  calc
    Measure.pi (fun _ : Fin n => Q j) =
        Measure.pi (fun _ : Fin n => (P j).map phi) := by
      congr 1
      funext i
      exact hQ j
    _ = (Measure.pi (fun _ : Fin n => P j)).map
        (fun z : Fin n → X => fun i => phi (z i)) :=
      (map_pi_finCoordinatewise n (P j) hphi).symm

end Causalean.Stat
