
namespace Causalean.Stat

open MeasureTheory

universe uX uY

/-! ## Coordinatewise recoding of finite product samples

These results package the measurable coordinatewise lift of an observation rule,
its action on a finite product law, and the corresponding expectation identity.
-/

variable {X : Type uX} {Y : Type uY}
  [MeasurableSpace X] [MeasurableSpace Y]

/-- Applying [a measurable observation rule](hyp:hphi) separately to every position of a
finite sample [produces a measurable recoded sample](goal). -/
theorem measurable_finCoordinatewise (n : ℕ) {phi : X → Y}
    (hphi : Measurable phi) :
    Measurable (fun z : Fin n → X => fun i => phi (z i)) := by
  exact measurable_pi_lambda _ fun i => hphi.comp (measurable_pi_apply i)

/-- Under a common probability law, applying [a measurable observation rule](hyp:hphi)
coordinate by coordinate [turns the finite product law into the finite product of the
recoded marginal law](goal). -/
theorem map_pi_finCoordinatewise (n : ℕ) (mu : Measure X)
    [IsProbabilityMeasure mu] {phi : X → Y} (hphi : Measurable phi) :
    (Measure.pi (fun _ : Fin n => mu)).map
        (fun z : Fin n → X => fun i => phi (z i)) =
      Measure.pi (fun _ : Fin n => mu.map phi) := by
  let _ : IsProbabilityMeasure (mu.map phi) :=
    Measure.isProbabilityMeasure_map hphi.aemeasurable
  exact Measure.pi_map_pi (fun _ : Fin n => hphi.aemeasurable)

/-- Under a common probability law, if [the observation rule is measurable](hyp:hphi) and
[the real-valued statistic of the recoded sample is measurable](hyp:hg), then [its expectation
after coordinatewise recoding equals its expectation under the product of the recoded
marginal law](goal). -/
theorem integral_comp_finCoordinatewise (n : ℕ) (mu : Measure X)
    [IsProbabilityMeasure mu] {phi : X → Y} (hphi : Measurable phi)
    (g : (Fin n → Y) → ℝ) (hg : Measurable g) :
    (∫ z : Fin n → X, g (fun i => phi (z i))
        ∂Measure.pi (fun _ : Fin n => mu)) =
      ∫ y, g y ∂Measure.pi (fun _ : Fin n => mu.map phi) := by
  let coord : (Fin n → X) → (Fin n → Y) := fun z i => phi (z i)
  have hcoord : Measurable coord := measurable_finCoordinatewise n hphi
  calc
    (∫ z : Fin n → X, g (fun i => phi (z i))
        ∂Measure.pi (fun _ : Fin n => mu)) =
        ∫ y, g y ∂(Measure.pi (fun _ : Fin n => mu)).map coord :=
      (integral_map hcoord.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂Measure.pi (fun _ : Fin n => mu.map phi) := by
      rw [map_pi_finCoordinatewise n mu hphi]

end Causalean.Stat
