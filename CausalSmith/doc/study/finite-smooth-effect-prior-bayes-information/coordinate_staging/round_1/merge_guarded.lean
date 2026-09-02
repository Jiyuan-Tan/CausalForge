/-!
## Finite dominated-experiment information calculus

This section converts counting-measure likelihood integrals and guarded Fisher
information into finite real sums, proves score centering, and integrates a
pointwise information bound against an arbitrary normalized nonnegative prior.
-/

open MeasureTheory Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- If [the masses of a finite likelihood sum to one](hyp:hnorm), then [its integral
against counting measure is one](goal). -/
theorem finite_likelihood_normalization {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {p : ℝ → X → ℝ} {θ : ℝ}
    (hnorm : ∑ x, p θ x = 1) :
    ∫ x, p θ x ∂Measure.count = 1 := by
  rw [integral_count, hnorm]

/-- If [each cell probability has the supplied parameter derivative](hyp:hderiv), then
[the derivative of their finite sum is the sum of those derivatives](goal). -/
theorem hasDerivAt_finite_likelihood_sum {X : Type*} [Fintype X]
    {p dp : ℝ → X → ℝ} {θ : ℝ}
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (dp θ x) θ) :
    HasDerivAt (fun t => ∑ x, p t x) (∑ x, dp θ x) θ := by
  have hsum : HasDerivAt (∑ x : X, fun t => p t x) (∑ x, dp θ x) θ :=
    HasDerivAt.sum (u := Finset.univ) (fun x _ => hderiv x)
  have heq : (fun t => ∑ x, p t x) = (∑ x : X, fun t => p t x) := by
    funext t
    rw [Finset.sum_apply]
  rw [heq]
  exact hsum

/-- If [each cell probability has the supplied derivative](hyp:hderiv) and [the finite
likelihood is locally normalized](hyp:hnorm), then [the derivative masses sum to
zero](goal). -/
theorem finite_derivative_centering {X : Type*} [Fintype X]
    {p dp : ℝ → X → ℝ} {θ : ℝ}
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (dp θ x) θ)
    (hnorm : ∀ᶠ t in nhds θ, ∑ x, p t x = 1) :
    ∑ x, dp θ x = 0 := by
  have hsum := hasDerivAt_finite_likelihood_sum hderiv
  apply hsum.unique
  exact (hasDerivAt_const θ 1).congr_of_eventuallyEq hnorm

/-- If [finite likelihood masses are nonnegative](hyp:hp) and [their derivatives vanish
on zero-mass cells](hyp:hzero), then [likelihood mass times guarded score equals the
cell derivative](goal). -/
theorem finite_likelihoodScore_mul {X : Type*} {p dp : ℝ → X → ℝ} {θ : ℝ}
    (hp : ∀ x, 0 ≤ p θ x) (hzero : ∀ x, p θ x = 0 → dp θ x = 0) (x : X) :
    likelihoodScore p dp θ x * p θ x = dp θ x := by
  exact guarded_score_mul_density (hp x) (hzero x)

/-- If [finite likelihood masses are nonnegative](hyp:hp), [derivatives vanish on
zero-mass cells](hyp:hzero), and [the derivative masses are centered](hyp:hcenter),
then [the likelihood-weighted guarded scores sum to zero](goal). -/
theorem finite_likelihoodScore_centered {X : Type*} [Fintype X]
    {p dp : ℝ → X → ℝ} {θ : ℝ}
    (hp : ∀ x, 0 ≤ p θ x) (hzero : ∀ x, p θ x = 0 → dp θ x = 0)
    (hcenter : ∑ x, dp θ x = 0) :
    ∑ x, likelihoodScore p dp θ x * p θ x = 0 := by
  simpa only [finite_likelihoodScore_mul hp hzero] using hcenter

/-- [Conditional Fisher information under counting measure equals the finite sum of
likelihood mass times squared guarded score](goal). -/
theorem fisherInformation_count_eq_sum {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (p dp : ℝ → X → ℝ) (θ : ℝ) :
    fisherInformation Measure.count p dp θ =
      ∑ x, p θ x * (likelihoodScore p dp θ x) ^ 2 := by
  exact integral_count _

/-- If [the prior is nonnegative](hyp:hw_nonneg), [normalized](hyp:hw_norm), and
[integrable](hyp:hw_int), [prior-weighted Fisher information is integrable]
(hyp:hweighted_int), and [conditional Fisher information is pointwise bounded wherever
the prior is positive](hyp:hpointwise), then [average Fisher information is bounded by
the same constant](goal). -/
theorem average_fisherInformation_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ell u I : ℝ} {w : ℝ → ℝ} {p dp : ℝ → X → ℝ}
    (hw_nonneg : ∀ θ, 0 ≤ w θ)
    (hw_norm : ∫ θ, w θ ∂parameterMeasure ell u = 1)
    (hw_int : Integrable w (parameterMeasure ell u))
    (hweighted_int : Integrable
      (fun θ => w θ * fisherInformation μ p dp θ) (parameterMeasure ell u))
    (hpointwise : ∀ θ, 0 < w θ → fisherInformation μ p dp θ ≤ I) :
    ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure ell u ≤ I := by
  calc
    ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure ell u ≤
        ∫ θ, w θ * I ∂parameterMeasure ell u := by
      apply integral_mono hweighted_int (hw_int.mul_const I)
      intro θ
      by_cases hwpos : 0 < w θ
      · exact mul_le_mul_of_nonneg_left (hpointwise θ hwpos) (hw_nonneg θ)
      · have hwzero : w θ = 0 := le_antisymm (le_of_not_gt hwpos) (hw_nonneg θ)
        simp [hwzero]
    _ = (∫ θ, w θ ∂parameterMeasure ell u) * I := integral_mul_const I w
    _ = I := by rw [hw_norm, one_mul]

end Causalean.Stat.Limit.ObservationDependentVanTrees
