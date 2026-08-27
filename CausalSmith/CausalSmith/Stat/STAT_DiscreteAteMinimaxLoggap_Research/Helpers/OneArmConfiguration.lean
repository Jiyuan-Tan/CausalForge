import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound

/-!
# Deterministic one-arm configurations

This file turns a triple of cell probabilities, propensities and treated outcome
means into an explicit discrete observation law whose control outcome is
identically zero, and reads off its cell masses, propensities, outcome means and
treated functional.  These laws are the members of the control-zero class that the
hard priors are supported on.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped ENNReal BigOperators

/-- Real atom mass of a control-zero one-arm configuration. -/
noncomputable def oneArmConfigurationAtom {d : ℕ}
    (p pi mu : Fin d → ℝ) (z : Obs d) : ℝ :=
  if z.2.1 then
    if z.2.2 then p z.1 * pi z.1 * mu z.1
    else p z.1 * pi z.1 * (1 - mu z.1)
  else if z.2.2 then 0 else p z.1 * (1 - pi z.1)

/-- When the cell probabilities, propensities and outcome means all lie in the unit
interval, every configuration atom is nonnegative.  This is one of the two
conditions making the atoms a genuine probability mass function. -/
lemma oneArmConfigurationAtom_nonneg {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1) (z : Obs d) :
    0 ≤ oneArmConfigurationAtom p pi mu z := by
  unfold oneArmConfigurationAtom
  split_ifs <;> try positivity
  · exact mul_nonneg (mul_nonneg (hp _).1 (hpi _).1) (hmu _).1
  · exact mul_nonneg (mul_nonneg (hp _).1 (hpi _).1) (sub_nonneg.mpr (hmu _).2)
  · exact mul_nonneg (hp _).1 (sub_nonneg.mpr (hpi _).2)

/-- Once the cell probabilities sum to one, the configuration atoms sum to one over
all observations, since within each cell the treated and control branches recombine
to the cell probability.  Together with nonnegativity this makes the atoms a
probability mass function. -/
lemma oneArmConfigurationAtom_sum {d : ℕ}
    (p pi mu : Fin d → ℝ) (hp_sum : ∑ r, p r = 1) :
    ∑ z : Obs d, oneArmConfigurationAtom p pi mu z = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, oneArmConfigurationAtom,
    Bool.false_eq_true, if_false, if_true]
  calc
    ∑ r, (p r * pi r * mu r + p r * pi r * (1 - mu r) +
        (0 + p r * (1 - pi r))) = ∑ r, p r := by
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = 1 := hp_sum

/-- The normalized observation law associated with a deterministic one-arm
configuration. -/
noncomputable def oneArmConfigurationLaw {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) : DiscreteLaw d where
  pmf := PMF.ofFintype
    (fun z => ENNReal.ofReal (oneArmConfigurationAtom p pi mu z)) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => oneArmConfigurationAtom_nonneg p pi mu hp hpi hmu z),
        oneArmConfigurationAtom_sum p pi mu hp_sum]
      simp

/-- The joint probability that the configuration law assigns to a cell, treatment
and outcome is exactly the corresponding configuration atom.  This is the unfolding
rule from which all the summary quantities below are computed. -/
lemma oneArmConfigurationLaw_jointMass {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d) (a y : Bool) :
    jointMass (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum) r a y =
      oneArmConfigurationAtom p pi mu (r, a, y) := by
  unfold jointMass oneArmConfigurationLaw
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact oneArmConfigurationAtom_nonneg p pi mu hp hpi hmu (r, a, y)

/-- The marginal probability of a cell under the configuration law is the cell
probability it was built from.  The configuration parameters are therefore read
back unchanged from the law. -/
lemma oneArmConfigurationLaw_cellMass {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d) :
    cellMass (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum) r = p r := by
  unfold cellMass
  simp only [Fintype.sum_bool,
    oneArmConfigurationLaw_jointMass p pi mu hp hpi hmu hp_sum,
    oneArmConfigurationAtom, Bool.false_eq_true, if_false, if_true]
  ring

/-- In any cell of positive probability, the conditional probability of treatment
under the configuration law is the propensity it was built from.  This is what lets
overlap restrictions be imposed directly on the configuration parameters. -/
lemma oneArmConfigurationLaw_propensity {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d) (hpr : 0 < p r) :
    propensity (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum) r = pi r := by
  unfold propensity armMass
  rw [oneArmConfigurationLaw_cellMass p pi mu hp hpi hmu hp_sum]
  simp only [Fintype.sum_bool,
    oneArmConfigurationLaw_jointMass p pi mu hp hpi hmu hp_sum,
    oneArmConfigurationAtom, if_true, Bool.false_eq_true, if_false]
  field_simp [ne_of_gt hpr]
  ring

/-- In a cell that has positive probability and positive propensity, the mean
outcome among the treated equals the outcome mean the configuration was built
from.  This identifies the treated regression function of the law. -/
lemma oneArmConfigurationLaw_outcomeMean_true {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d)
    (hpr : 0 < p r) (hpir : 0 < pi r) :
    outcomeMean (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum) true r = mu r := by
  unfold outcomeMean armMass
  simp only [Fintype.sum_bool,
    oneArmConfigurationLaw_jointMass p pi mu hp hpi hmu hp_sum,
    oneArmConfigurationAtom, if_true, Bool.false_eq_true, if_false]
  field_simp [ne_of_gt hpr, ne_of_gt hpir]
  ring

/-- The mean outcome among the controls is identically zero in every cell: the
configuration puts no mass on a control unit with outcome one.  This is exactly the
control-zero restriction that defines the class. -/
lemma oneArmConfigurationLaw_outcomeMean_false {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d) :
    outcomeMean (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum) false r = 0 := by
  unfold outcomeMean armMass
  simp only [Fintype.sum_bool,
    oneArmConfigurationLaw_jointMass p pi mu hp hpi hmu hp_sum,
    oneArmConfigurationAtom, Bool.false_eq_true, if_false]
  simp

/-- When every propensity is strictly positive, the treated functional of the
configuration law is the weighted average `∑ᵣ pᵣ μᵣ` of the treated outcome means.
This is the estimand the hard priors must separate. -/
lemma oneArmConfigurationLaw_treatedFunctional {d : ℕ}
    (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (hpi_pos : ∀ r, 0 < pi r) :
    treatedFunctional (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum) =
      ∑ r, p r * mu r := by
  unfold treatedFunctional
  apply Finset.sum_congr rfl
  intro r _
  rw [oneArmConfigurationLaw_cellMass p pi mu hp hpi hmu hp_sum]
  by_cases hpr : 0 < p r
  · rw [oneArmConfigurationLaw_outcomeMean_true p pi mu hp hpi hmu hp_sum r hpr (hpi_pos r)]
  · have hpr0 : p r = 0 := by linarith [(hp r).1]
    rw [hpr0]
    simp

/-- Normalizing an approximate mass vector changes its one-arm functional by
at most the mass defect.  This is the deterministic target comparison in D.2. -/
lemma normalized_oneArmFunctional_sub_le_massDefect
    {d : ℕ} (p mu : Fin d → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hS : 0 < ∑ r, p r) :
    |(∑ r, (p r / (∑ t, p t)) * mu r) - ∑ r, p r * mu r| ≤
      |(∑ r, p r) - 1| := by
  let S := ∑ r, p r
  let T := ∑ r, p r * mu r
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hp r) (hmu r).1
  have hTle : T ≤ S := by
    dsimp [T, S]
    exact Finset.sum_le_sum fun r _ =>
      mul_le_of_le_one_right (hp r) (hmu r).2
  have hnorm : ∑ r, (p r / S) * mu r = T / S := by
    dsimp [T]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hratio : T / S ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hT0 hS.le, (div_le_one hS).2 hTle⟩
  change |(∑ r, (p r / S) * mu r) - T| ≤ |S - 1|
  rw [hnorm]
  have hS0 : S ≠ 0 := ne_of_gt (by simpa [S] using hS)
  have hident : T / S - T = (1 - S) * (T / S) := by
    field_simp [hS0]
  rw [hident, abs_mul]
  calc
    |1 - S| * |T / S| ≤ |1 - S| :=
      mul_le_of_le_one_right (abs_nonneg (1 - S)) (by
        rw [abs_of_nonneg hratio.1]
        exact hratio.2)
    _ = |S - 1| := abs_sub_comm 1 S

/-- Every deterministic configuration satisfying overlap gives a member of the
control-zero class, with treated functional `∑ pᵣ μᵣ`. -/
noncomputable def oneArmConfigurationControlZero
    {n d : ℕ} {epsilon : ℝ} (p pi mu : Fin d → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (epsilon : ℝ) (1 - epsilon))
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) :
    ControlZeroLaw n d epsilon := by
  let hpi01 : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1 := fun r => by
    have hr := hpi r
    exact ⟨he0.le.trans hr.1, by linarith [hr.2, he0]⟩
  let P := oneArmConfigurationLaw p pi mu hp hpi01 hmu hp_sum
  refine ⟨P, ?_⟩
  constructor
  · refine ⟨he0, hehalf, rfl, ?_⟩
    intro r hr
    have hpr : 0 < p r := by
      rw [← oneArmConfigurationLaw_cellMass p pi mu hp hpi01 hmu hp_sum]
      exact hr
    rw [oneArmConfigurationLaw_propensity p pi mu hp hpi01 hmu hp_sum r hpr]
    exact hpi r
  · intro r
    exact oneArmConfigurationLaw_outcomeMean_false p pi mu hp hpi01 hmu hp_sum r

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
