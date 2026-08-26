
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
