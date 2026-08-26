import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductConditioning
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmConditioning
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmFuzzyReduction
import Causalean.Stat.Minimax.Mixture

/-!
# Good-event conditioning for finite one-arm product priors

This module conditions a finite prior on a positive-mass good event, records
the resulting predictive-mixture decomposition, and maps mass/target-good iid
configurations to anchored control-zero laws.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open scoped ENNReal NNReal BigOperators

section FiniteConditioning

variable {α Ω : Type*} [Fintype α]

/-- Prior mass of a finite event. -/
noncomputable def oneArmFiniteEventMass (ω : PMF α) (G : α → Prop)
    [DecidablePred G] : ℝ≥0∞ :=
  ∑ x with G x, ω x

lemma oneArmFiniteEventMass_add_compl (ω : PMF α) (G : α → Prop)
    [DecidablePred G] :
    oneArmFiniteEventMass ω G + oneArmFiniteEventMass ω (fun x => ¬ G x) = 1 := by
  rw [oneArmFiniteEventMass, oneArmFiniteEventMass]
  rw [Finset.sum_filter_add_sum_filter_not]
  simpa only [tsum_fintype] using ω.tsum_coe

lemma oneArmFiniteEventMass_le_one (ω : PMF α) (G : α → Prop)
    [DecidablePred G] : oneArmFiniteEventMass ω G ≤ 1 := by
  have h := oneArmFiniteEventMass_add_compl ω G
  exact le_add_right (le_refl _) |>.trans_eq h

lemma oneArmFiniteEventMass_eq_toMeasure
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ω : PMF α) (G : α → Prop) [DecidablePred G] :
    oneArmFiniteEventMass ω G = ω.toMeasure {x | G x} := by
  letI : DecidablePred G := Classical.decPred G
  rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete, tsum_fintype]
  rw [oneArmFiniteEventMass]
  rw [Finset.filter_congr_decidable]
  calc
    _ = ∑ x, if G x then ω x else 0 :=
      Finset.sum_filter G (ω : α → ℝ≥0∞) (s := Finset.univ)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : G x <;> simp [Set.indicator, hx]

/-- Normalized weights on a positive-mass finite event. -/
noncomputable def oneArmFiniteConditionedWeight
    (ω : PMF α) (G : α → Prop) [DecidablePred G]
    (z : {x // G x}) : ℝ≥0∞ :=
  ω z.1 * (oneArmFiniteEventMass ω G)⁻¹

lemma oneArmFiniteConditionedWeight_sum
    (ω : PMF α) (G : α → Prop) [DecidablePred G]
    (hG0 : oneArmFiniteEventMass ω G ≠ 0) :
    ∑ z : {x // G x}, oneArmFiniteConditionedWeight ω G z = 1 := by
  simp only [oneArmFiniteConditionedWeight]
  rw [← Finset.sum_mul]
  have hmass : ∑ z : {x // G x}, ω z.1 = oneArmFiniteEventMass ω G := by
    simpa only [oneArmFiniteEventMass] using
      (Finset.sum_subtype (Finset.univ.filter G) (by simp) ω).symm
  rw [hmass, ENNReal.mul_inv_cancel hG0]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (oneArmFiniteEventMass_le_one ω G)

/-- The predictive mixture induced by conditioning a finite prior on an event. -/
noncomputable def oneArmFiniteConditionedMixture
    [MeasurableSpace Ω] (ω : PMF α) (G : α → Prop) [DecidablePred G]
    (_hG0 : oneArmFiniteEventMass ω G ≠ 0) (K : α → Measure Ω) : Measure Ω :=
  mixture (oneArmFiniteConditionedWeight ω G) (fun z => K z.1)

noncomputable instance oneArmFiniteConditionedMixture_isProbabilityMeasure
    [MeasurableSpace Ω] (ω : PMF α) (G : α → Prop) [DecidablePred G]
    (_hG0 : oneArmFiniteEventMass ω G ≠ 0) (K : α → Measure Ω)
    [∀ x, IsProbabilityMeasure (K x)] :
    IsProbabilityMeasure (oneArmFiniteConditionedMixture ω G _hG0 K) := by
  unfold oneArmFiniteConditionedMixture
  exact mixture_isProbabilityMeasure _
    (oneArmFiniteConditionedWeight_sum ω G _hG0) _

/-- A finite prior predictive is the good conditional predictive plus the bad
conditional predictive, weighted by their prior masses. -/
theorem oneArmFiniteMixture_conditioning_decomposition
    [MeasurableSpace Ω] (ω : PMF α) (G : α → Prop) [DecidablePred G]
    (hG0 : oneArmFiniteEventMass ω G ≠ 0)
    (hB0 : oneArmFiniteEventMass ω (fun x => ¬ G x) ≠ 0)
    (K : α → Measure Ω) :
    mixture (fun x => ω x) K =
      oneArmFiniteEventMass ω G •
          oneArmFiniteConditionedMixture ω G hG0 K +
        oneArmFiniteEventMass ω (fun x => ¬ G x) •
          oneArmFiniteConditionedMixture ω (fun x => ¬ G x) hB0 K := by
  ext A hA
  rw [mixture_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [oneArmFiniteConditionedMixture, mixture_apply, smul_eq_mul]
  have hGtop : oneArmFiniteEventMass ω G ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (oneArmFiniteEventMass_le_one ω G)
  have hBtop : oneArmFiniteEventMass ω (fun x => ¬ G x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (oneArmFiniteEventMass_le_one ω (fun x => ¬ G x))
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [oneArmFiniteConditionedWeight]
  simp_rw [show ∀ x : {x // G x},
      oneArmFiniteEventMass ω G *
          (ω x.1 * (oneArmFiniteEventMass ω G)⁻¹ * K x.1 A) =
        ω x.1 * K x.1 A by
    intro x
    calc
      _ = (oneArmFiniteEventMass ω G * (oneArmFiniteEventMass ω G)⁻¹) *
          (ω x.1 * K x.1 A) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hG0 hGtop, one_mul]]
  simp_rw [show ∀ x : {x // ¬ G x},
      oneArmFiniteEventMass ω (fun x => ¬ G x) *
          (ω x.1 * (oneArmFiniteEventMass ω (fun x => ¬ G x))⁻¹ * K x.1 A) =
        ω x.1 * K x.1 A by
    intro x
    calc
      _ = (oneArmFiniteEventMass ω (fun x => ¬ G x) *
            (oneArmFiniteEventMass ω (fun x => ¬ G x))⁻¹) *
          (ω x.1 * K x.1 A) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hB0 hBtop, one_mul]]
  exact (Fintype.sum_subtype_add_sum_subtype G
    (fun x => ω x * K x A)).symm

/-- If the discarded event has zero prior mass, conditioning on the good
event leaves the predictive mixture unchanged. -/
theorem oneArmFiniteMixture_eq_conditioned_of_compl_mass_eq_zero
    [MeasurableSpace Ω] (ω : PMF α) (G : α → Prop) [DecidablePred G]
    (hG0 : oneArmFiniteEventMass ω G ≠ 0)
    (hB : oneArmFiniteEventMass ω (fun x => ¬ G x) = 0)
    (K : α → Measure Ω) [∀ x, IsProbabilityMeasure (K x)] :
    mixture (fun x => ω x) K =
      oneArmFiniteConditionedMixture ω G hG0 K := by
  have hG1 : oneArmFiniteEventMass ω G = 1 := by
    have hsum := oneArmFiniteEventMass_add_compl ω G
    simpa [hB] using hsum
  ext A hA
  rw [mixture_apply, oneArmFiniteConditionedMixture, mixture_apply]
  simp only [oneArmFiniteConditionedWeight, hG1, inv_one, mul_one]
  have hbadWeight :
      ∑ z : {x // ¬ G x}, ω z.1 = 0 := by
    calc
      ∑ z : {x // ¬ G x}, ω z.1 = ∑ x with ¬ G x, ω x := by
        simpa using (Finset.sum_subtype (Finset.univ.filter fun x => ¬ G x)
          (by simp) ω).symm
      _ = 0 := by simpa only [oneArmFiniteEventMass] using hB
  have hbad : ∑ z : {x // ¬ G x}, ω z.1 * K z.1 A = 0 := by
    apply le_antisymm
    · calc
        ∑ z : {x // ¬ G x}, ω z.1 * K z.1 A ≤
            ∑ z : {x // ¬ G x}, ω z.1 := by
          apply Finset.sum_le_sum
          intro z _
          simpa [mul_comm] using _root_.mul_le_mul_left
            ((measure_mono (Set.subset_univ A)).trans_eq
              (measure_univ : K z.1 Set.univ = 1)) (ω z.1)
        _ = 0 := hbadWeight
    · exact bot_le
  rw [← Fintype.sum_subtype_add_sum_subtype G
    (fun x => ω x * K x A), hbad, add_zero]

end FiniteConditioning

section AnchoredGoodEvent

/-- A product-prior realization is good when its active mass fits below one
and its unnormalized treated functional is close to the chosen center. -/
def oneArmAnchoredGood {α : Type*} {m : ℕ}
    (q mu : α → ℝ) (theta radius : ℝ) (z : Fin m → α) : Prop :=
  (∑ i, q (z i)) ≤ 1 ∧
    |(∑ i, q (z i) * mu (z i)) - theta| ≤ radius

/-- A good realization of iid atoms completed by a residual anchor. -/
noncomputable def oneArmAnchoredLawOfGoodAtoms
    {α : Type*} {n m : ℕ} {epsilon theta radius : ℝ}
    (q pi mu : α → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (hq : ∀ x, 0 ≤ q x)
    (hpi : ∀ x, pi x ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (z : {z : Fin m → α // oneArmAnchoredGood q mu theta radius z}) :
    ControlZeroLaw n (m + 1) epsilon :=
  oneArmAnchoredControlZero (fun i => q (z.1 i))
    (fun i => pi (z.1 i)) (fun i => mu (z.1 i)) he0 hehalf
    (fun i => hq (z.1 i)) z.2.1 (fun i => hpi (z.1 i))
    (fun i => hmu (z.1 i))

/-- Every anchored law selected by the good event has target within the
prescribed radius of the side's center. -/
lemma oneArmAnchoredLawOfGoodAtoms_target
    {α : Type*} {n m : ℕ} {epsilon theta radius : ℝ}
    (q pi mu : α → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (hq : ∀ x, 0 ≤ q x)
    (hpi : ∀ x, pi x ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hpi_pos : ∀ x, 0 < pi x)
    (z : {z : Fin m → α // oneArmAnchoredGood q mu theta radius z}) :
    |treatedFunctional
        (oneArmAnchoredLawOfGoodAtoms (n := n) q pi mu he0 hehalf hq hpi hmu z).1 -
          theta| ≤ radius := by
  rw [oneArmAnchoredLawOfGoodAtoms,
    oneArmAnchoredControlZero_functional _ _ _ he0 hehalf
      (fun i => hq (z.1 i)) z.2.1 (fun i => hpi (z.1 i))
      (fun i => hmu (z.1 i)) (fun i => hpi_pos (z.1 i))]
  exact z.2.2

/-- The mass/functional Chebyshev good event implies the anchored good event
when the mass center plus its tolerance is at most one. -/
lemma oneArmProductConcentrationGood_anchored
    {α : Type*} {m : ℕ} (q mu : α → ℝ)
    (massCenter theta δmass δfun : ℝ)
    (hcap : massCenter + δmass ≤ 1) (z : Fin m → α)
    (hmass : |(∑ i, q (z i)) - massCenter| < δmass)
    (hfun : |(∑ i, q (z i) * mu (z i)) - theta| < δfun) :
    oneArmAnchoredGood q mu theta δfun z := by
  constructor
  · have hupper := (abs_lt.mp hmass).2
    linarith
  · exact hfun.le

end AnchoredGoodEvent

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
