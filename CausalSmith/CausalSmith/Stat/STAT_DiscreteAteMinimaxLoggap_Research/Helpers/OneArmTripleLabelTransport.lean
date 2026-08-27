import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmObservationCounts
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmFuzzyReduction

/-!
# Lossless triple-label transport on the control-zero model

The three observation labels admit a canonical representative.  On a
control-zero law this representative channel loses no information, because
the omitted control-success atom has probability zero.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory

/-- Canonical observation represented by a category and one of the three
control-zero labels. -/
def oneArmTripleRepresentative {d : ℕ} (u : Fin d × Fin 3) : Obs d :=
  (u.1, if u.2 = 0 then true else if u.2 = 1 then true else false,
    if u.2 = 0 then true else false)

/-- Labelling an observation and then taking the canonical representative
returns the original observation, for every observation other than a
control-arm success.  Since that one atom carries no mass under a control-zero
law, the three-label channel is lossless there. -/
lemma oneArmTripleRepresentative_label_of_not_controlSuccess
    {d : ℕ} (z : Obs d) (hz : ¬ (z.2.1 = false ∧ z.2.2 = true)) :
    oneArmTripleRepresentative (oneArmObservationTripleLabel z) = z := by
  rcases z with ⟨k, a, y⟩
  fin_cases a <;> fin_cases y <;>
    simp [oneArmTripleRepresentative, oneArmObservationTripleLabel] at hz ⊢

private lemma controlSuccess_jointMass_eq_zero
    {n d : ℕ} {epsilon : ℝ} (P : ControlZeroLaw n d epsilon) (k : Fin d) :
    jointMass P.1 k false true = 0 := by
  have hj0 : 0 ≤ jointMass P.1 k false true :=
    (jointMass_mem_unitInterval P.1 k false true).1
  have hjle : jointMass P.1 k false true ≤ armMass P.1 k false := by
    simp [armMass]
    exact (jointMass_mem_unitInterval P.1 k false false).1
  by_cases ha : armMass P.1 k false = 0
  · linarith
  · have hmean := P.2.control_zero k
    unfold outcomeMean at hmean
    exact (div_eq_zero_iff.mp hmean).resolve_right ha

private lemma obsLaw_controlSuccess_set_eq_zero
    {n d : ℕ} {epsilon : ℝ} (P : ControlZeroLaw n d epsilon) :
    obsLaw P.1 {z | z.2.1 = false ∧ z.2.2 = true} = 0 := by
  rw [obsLaw, PMF.toMeasure_apply _ MeasurableSet.of_discrete]
  rw [tsum_fintype]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z.2.1 = false ∧ z.2.2 = true
  · rcases z with ⟨k, a, y⟩
    simp only at hz
    rcases hz with ⟨rfl, rfl⟩
    have hreal : (P.1.pmf (k, false, true)).toReal = 0 := by
      simpa [jointMass] using controlSuccess_jointMass_eq_zero P k
    have hpmf : P.1.pmf (k, false, true) = 0 := by
      apply (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right
      exact PMF.apply_ne_top _ _
    simp [Set.indicator, hpmf]
  · simp [Set.indicator, hz]

/-- Labeling and then choosing the canonical representative reconstructs a
control-zero one-observation law exactly. -/
lemma map_oneArmTripleRepresentative_map_label_obsLaw
    {n d : ℕ} {epsilon : ℝ} (P : ControlZeroLaw n d epsilon) :
    Measure.map oneArmTripleRepresentative
        (Measure.map oneArmObservationTripleLabel (obsLaw P.1)) =
      obsLaw P.1 := by
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  have hae :
      (oneArmTripleRepresentative ∘ oneArmObservationTripleLabel) =ᵐ[obsLaw P.1]
        id := by
    filter_upwards [compl_mem_ae_iff.2 (obsLaw_controlSuccess_set_eq_zero P)] with z hz
    exact oneArmTripleRepresentative_label_of_not_controlSuccess z hz
  rw [Measure.map_congr hae, Measure.map_id]

/-- Applying the representative coordinatewise to the triple-label product
law preserves the squared risk of every fixed-sample estimator. -/
lemma productRisk_oneArmTripleRepresentative_eq
    {n d : ℕ} {epsilon : ℝ} (P : ControlZeroLaw n d epsilon)
    (est : (Fin n → Obs d) → ℝ) (theta : ℝ) :
    (∫ z, (est (fun i => oneArmTripleRepresentative (z i)) - theta) ^ 2
      ∂Measure.pi (fun _ : Fin n =>
        Measure.map oneArmObservationTripleLabel (obsLaw P.1))) =
      mse (productLaw P.1 n) est theta := by
  let rep : (Fin n → Fin d × Fin 3) → (Fin n → Obs d) :=
    fun z i => oneArmTripleRepresentative (z i)
  have hrep : Measurable rep := measurable_of_finite _
  have hpi : Measure.map rep
      (Measure.pi (fun _ : Fin n =>
        Measure.map oneArmObservationTripleLabel (obsLaw P.1))) =
      productLaw P.1 n := by
    unfold productLaw
    rw [Measure.pi_map_pi (fun _ => (measurable_of_finite _).aemeasurable)]
    exact congrArg (fun μ : Fin n → Measure (Obs d) => Measure.pi μ)
      (funext fun _ => map_oneArmTripleRepresentative_map_label_obsLaw P)
  unfold mse
  rw [← hpi, integral_map hrep.aemeasurable
    (measurable_of_finite _).aestronglyMeasurable]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
