import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductConditioning
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmShiftedGridPriorLift

/-!
# Concrete concentration envelope for the shifted one-arm prior

The lifted mass and treated-functional atoms both lie in `[0, scale]`.  This
supplies the variance bounds used in the final product-prior conditioning.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory

lemma oneArmShifted_massAtom_mem_Icc
    {D : ℕ} {κ scale : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D)
    (hscale : 0 ≤ scale) (z : Option (Fin (2 * D + 4))) :
    oneArmProductMassAtom scale (oneArmShiftedSelectionGrid κ D) z ∈
      Set.Icc 0 scale := by
  cases z with
  | none => simp [oneArmProductMassAtom, liftedCellMass, hscale]
  | some i =>
      simp only [oneArmProductMassAtom, liftedCellMass]
      exact ⟨mul_nonneg hscale
          (oneArmShiftedSelectionGrid_pos hκ hκ1 hD i).le,
        mul_le_of_le_one_right hscale
          (oneArmShiftedSelectionGrid_mem_Icc hκ hκ1 hD i).2⟩

lemma oneArmShifted_functionalAtom_mem_Icc
    {D : ℕ} {κ scale : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D)
    (hscale : 0 ≤ scale) (z : Option (Fin (2 * D + 4))) :
    oneArmProductFunctionalAtom scale (oneArmShiftedPoleScale κ D)
        (oneArmShiftedSelectionGrid κ D) z ∈ Set.Icc 0 scale := by
  cases z with
  | none => simp [oneArmProductFunctionalAtom, liftedCellMass, hscale]
  | some i =>
      have hx := oneArmShiftedSelectionGrid_pos hκ hκ1 hD i
      have ha := oneArmShiftedPoleScale_pos hκ hD
      have hratio : oneArmShiftedSelectionGrid κ D i /
          (oneArmShiftedSelectionGrid κ D i + oneArmShiftedPoleScale κ D) ∈
          Set.Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · exact (div_le_one (add_pos hx ha)).2 (by linarith)
      simp only [oneArmProductFunctionalAtom, liftedCellMass, liftedOutcomeMean]
      exact ⟨mul_nonneg (mul_nonneg hscale hx.le) hratio.1,
        calc
          scale * oneArmShiftedSelectionGrid κ D i *
              (oneArmShiftedSelectionGrid κ D i /
                (oneArmShiftedSelectionGrid κ D i + oneArmShiftedPoleScale κ D)) ≤
              scale * oneArmShiftedSelectionGrid κ D i := by
                exact mul_le_of_le_one_right (mul_nonneg hscale hx.le) hratio.2
          _ ≤ scale := mul_le_of_le_one_right hscale
            (oneArmShiftedSelectionGrid_mem_Icc hκ hκ1 hD i).2⟩

lemma oneArmShifted_massAtom_variance_le_sq
    {D : ℕ} {κ scale : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D)
    (hscale : 0 ≤ scale) [MeasurableSpace (Option (Fin (2 * D + 4)))]
    [MeasurableSingletonClass (Option (Fin (2 * D + 4)))]
    (ω : PMF (Option (Fin (2 * D + 4)))) :
    Var[oneArmProductMassAtom scale (oneArmShiftedSelectionGrid κ D);
      ω.toMeasure] ≤ scale ^ 2 := by
  have hbound : ∀ᵐ z ∂ω.toMeasure,
      oneArmProductMassAtom scale (oneArmShiftedSelectionGrid κ D) z ∈
        Set.Icc 0 scale :=
    Filter.Eventually.of_forall
      (oneArmShifted_massAtom_mem_Icc hκ hκ1 hD hscale)
  have hvar := variance_le_sq_of_bounded hbound
    (Measurable.aemeasurable (measurable_of_finite _))
  nlinarith [sq_nonneg scale]

lemma oneArmShifted_functionalAtom_variance_le_sq
    {D : ℕ} {κ scale : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D)
    (hscale : 0 ≤ scale) [MeasurableSpace (Option (Fin (2 * D + 4)))]
    [MeasurableSingletonClass (Option (Fin (2 * D + 4)))]
    (ω : PMF (Option (Fin (2 * D + 4)))) :
    Var[oneArmProductFunctionalAtom scale (oneArmShiftedPoleScale κ D)
        (oneArmShiftedSelectionGrid κ D); ω.toMeasure] ≤ scale ^ 2 := by
  have hbound : ∀ᵐ z ∂ω.toMeasure,
      oneArmProductFunctionalAtom scale (oneArmShiftedPoleScale κ D)
          (oneArmShiftedSelectionGrid κ D) z ∈ Set.Icc 0 scale :=
    Filter.Eventually.of_forall
      (oneArmShifted_functionalAtom_mem_Icc hκ hκ1 hD hscale)
  have hvar := variance_le_sq_of_bounded hbound
    (Measurable.aemeasurable (measurable_of_finite _))
  nlinarith [sq_nonneg scale]

/-- The concrete two-statistic Chebyshev envelope used for either shifted
inverse-tilted product prior. -/
lemma oneArmShifted_mass_functional_bad_le_sq_envelope
    {D m : ℕ} {κ scale δ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D) (hscale : 0 ≤ scale)
    [MeasurableSpace (Option (Fin (2 * D + 4)))]
    [DiscreteMeasurableSpace (Option (Fin (2 * D + 4)))]
    (ω : PMF (Option (Fin (2 * D + 4)))) (hδ : 0 < δ) :
    oneArmFiniteIidMeasure ω m
        ({z | δ ≤
            |(∑ i, oneArmProductMassAtom scale
                (oneArmShiftedSelectionGrid κ D) (z i)) -
              m * ∫ u, oneArmProductMassAtom scale
                (oneArmShiftedSelectionGrid κ D) u ∂ω.toMeasure|} ∪
         {z | δ ≤
            |(∑ i, oneArmProductFunctionalAtom scale
                (oneArmShiftedPoleScale κ D)
                (oneArmShiftedSelectionGrid κ D) (z i)) -
              m * ∫ u, oneArmProductFunctionalAtom scale
                (oneArmShiftedPoleScale κ D)
                (oneArmShiftedSelectionGrid κ D) u ∂ω.toMeasure|}) ≤
      ENNReal.ofReal (m * scale ^ 2 / δ ^ 2) +
        ENNReal.ofReal (m * scale ^ 2 / δ ^ 2) := by
  refine (oneArmProduct_mass_functional_bad_le ω m scale
    (oneArmShiftedPoleScale κ D) (oneArmShiftedSelectionGrid κ D)
    MemLp.of_discrete MemLp.of_discrete hδ hδ).trans ?_
  apply add_le_add <;> apply ENNReal.ofReal_le_ofReal <;>
    gcongr
  · exact oneArmShifted_massAtom_variance_le_sq hκ hκ1 hD hscale ω
  · exact oneArmShifted_functionalAtom_variance_le_sq hκ hκ1 hD hscale ω

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
