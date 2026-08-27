import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmLogCalibration
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmShiftedGridPriorLift
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductPredictive

/-!
# Shifted-prior predictive total variation
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open scoped BigOperators NNReal ENNReal

/-- The discrete σ-algebra on the option type `Option (Fin N)`, in which every
subset is measurable.  It is the ambient measurable structure used here for the
lifted grid label augmented with a "no cell" value. -/
local instance shiftedOptionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Option (Fin N)) := ⊤

/-- The shifted inverse-tilted priors have unconditioned common-anchor
predictive total variation at most `2 d / n^4`. -/
theorem tvDist_oneArmShiftedPriorPredictive_le
    {n d : ℕ} {epsilon κ : ℝ} (hn : 2 ≤ n)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (he0 : 0 < epsilon)
    (hoverlap : epsilon * (1 + κ) ≤ 1 - epsilon)
    (omega₀ omega₁ : PMF (Fin (2 * oneArmLogDegree n + 4)))
    (hmom : ∀ c,
      ∑ r, (omega₀ r).toReal *
          finiteGridBasisEval
            (oneArmShiftedSelectionBasis κ (oneArmLogDegree n)) c r =
        ∑ r, (omega₁ r).toReal *
          finiteGridBasisEval
            (oneArmShiftedSelectionBasis κ (oneArmLogDegree n)) c r)
    (anchorLaw : PMF (Fin 3 → ℕ)) :
    let D := oneArmLogDegree n
    let scale := (D : ℝ) / (128 * (n : ℝ))
    let x := oneArmShiftedSelectionGrid κ D
    let pole := oneArmShiftedPoleScale κ D
    let hD : 1 ≤ D := oneArmLogDegree_pos hn
    let hweight₀ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
      D hκ hκ1 hD omega₀
    let hweight₁ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
      D hκ hκ1 hD omega₁
    let ω₀ := inverseTiltPMF omega₀ x pole hweight₀
    let ω₁ := inverseTiltPMF omega₁ x pole hweight₁
    let p := liftedCellMass scale x
    let pi := liftedPropensity epsilon pole x
    let mu := liftedOutcomeMean pole x
    let sampleScale := 4 * (n : ℝ)
    let lam11 := fun z => (sampleScale * p z * pi z * mu z).toNNReal
    let lam10 := fun z => (sampleScale * p z * pi z * (1 - mu z)).toNNReal
    let lam0 := fun z => (sampleScale * p z * (1 - pi z)).toNNReal
    tvDist
        (mixture (oneArmFiniteIidPMF ω₀ d)
          (fun z => Measure.pi fun r : Fin (d + 1) =>
            Fin.cases (motive := fun _ => Measure (Fin 3 → ℕ))
              anchorLaw.toMeasure
              (fun i => (triplePoissonPMF
                (lam11 (z i)) (lam10 (z i)) (lam0 (z i))).toMeasure) r))
        (mixture (oneArmFiniteIidPMF ω₁ d)
          (fun z => Measure.pi fun r : Fin (d + 1) =>
            Fin.cases (motive := fun _ => Measure (Fin 3 → ℕ))
              anchorLaw.toMeasure
              (fun i => (triplePoissonPMF
                (lam11 (z i)) (lam10 (z i)) (lam0 (z i))).toMeasure) r)) ≤
      2 * (d : ℝ) / (n : ℝ) ^ 4 := by
  dsimp only
  let D := oneArmLogDegree n
  have hD : 1 ≤ D := oneArmLogDegree_pos hn
  let scale : ℝ := (D : ℝ) / (128 * (n : ℝ))
  let x := oneArmShiftedSelectionGrid κ D
  let pole := oneArmShiftedPoleScale κ D
  let hweight₀ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
    D hκ hκ1 hD omega₀
  let hweight₁ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
    D hκ hκ1 hD omega₁
  let ω₀ := inverseTiltPMF omega₀ x pole hweight₀
  let ω₁ := inverseTiltPMF omega₁ x pole hweight₁
  let p := liftedCellMass scale x
  let pi := liftedPropensity epsilon pole x
  let mu := liftedOutcomeMean pole x
  let sampleScale : ℝ := 4 * (n : ℝ)
  let lam11 : Option (Fin (2 * D + 4)) → ℝ≥0 :=
    fun z => (sampleScale * p z * pi z * mu z).toNNReal
  let lam10 : Option (Fin (2 * D + 4)) → ℝ≥0 :=
    fun z => (sampleScale * p z * pi z * (1 - mu z)).toNNReal
  let lam0 : Option (Fin (2 * D + 4)) → ℝ≥0 :=
    fun z => (sampleScale * p z * (1 - pi z)).toNNReal
  have hnR : (0 : ℝ) < n := by positivity
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hs : 0 ≤ sampleScale := by dsimp [sampleScale]; positivity
  have hp (z : Option (Fin (2 * D + 4))) : 0 ≤ p z := by
    cases z with
    | none => simp [p, liftedCellMass]
    | some i =>
        exact mul_nonneg hscale
          (oneArmShiftedSelectionGrid_pos hκ hκ1 hD i).le
  have hpiIcc (z : Option (Fin (2 * D + 4))) : pi z ∈ Set.Icc (0 : ℝ) 1 := by
    have hpi := liftedPropensity_mem_Icc_of_shift_le he0.le
      (oneArmShiftedPoleScale_pos hκ hD).le hκ.le
      (fun i => oneArmShiftedSelectionGrid_pos hκ hκ1 hD i)
      (fun i => by
        unfold oneArmShiftedPoleScale
        exact mul_le_mul_of_nonneg_left
          (oneArmShiftedSelectionGrid_mem_Icc hκ hκ1 hD i).1 hκ.le)
      hoverlap z
    exact ⟨he0.le.trans hpi.1, hpi.2.trans (by linarith)⟩
  have hmuIcc (z : Option (Fin (2 * D + 4))) : mu z ∈ Set.Icc (0 : ℝ) 1 := by
    exact liftedOutcomeMean_mem_Icc
      (oneArmShiftedPoleScale_pos hκ hD).le
      (oneArmShiftedPole_le_grid hκ hκ1 hD) z
  have h11 (z : Option (Fin (2 * D + 4))) :
      (lam11 z : ℝ) = sampleScale * p z * pi z * mu z := by
    rw [show lam11 z = (sampleScale * p z * pi z * mu z).toNNReal by rfl,
      Real.coe_toNNReal]
    exact mul_nonneg (mul_nonneg (mul_nonneg hs (hp z)) (hpiIcc z).1)
      (hmuIcc z).1
  have h10 (z : Option (Fin (2 * D + 4))) :
      (lam10 z : ℝ) = sampleScale * p z * pi z * (1 - mu z) := by
    rw [show lam10 z =
      (sampleScale * p z * pi z * (1 - mu z)).toNNReal by rfl,
      Real.coe_toNNReal]
    exact mul_nonneg (mul_nonneg (mul_nonneg hs (hp z)) (hpiIcc z).1)
      (sub_nonneg.mpr (hmuIcc z).2)
  have h0 (z : Option (Fin (2 * D + 4))) :
      (lam0 z : ℝ) = sampleScale * p z * (1 - pi z) := by
    rw [show lam0 z = (sampleScale * p z * (1 - pi z)).toNNReal by rfl,
      Real.coe_toNNReal]
    exact mul_nonneg (mul_nonneg hs (hp z))
      (sub_nonneg.mpr (hpiIcc z).2)
  have hmoment : ∀ i j k : ℕ, i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal *
          (p r ^ i * (p r * pi r) ^ j * (p r * pi r * mu r) ^ k) =
        ∑ r, (ω₁ r).toReal *
          (p r ^ i * (p r * pi r) ^ j * (p r * pi r * mu r) ^ k) := by
    intro i j k hdeg
    exact oneArmShiftedSelection_inverseTilt_liftedRawMoment_eq
      hD hκ hκ1 omega₀ omega₁ hmom scale epsilon i j k hdeg
  have hbudget (z : Option (Fin (2 * D + 4))) :
      4 * (sampleScale * p z) + 2 * Real.log ((n : ℝ) ^ 2) ≤
        (((D + 1 : ℕ) : ℝ) * Real.log 2) := by
    cases z with
    | none =>
        simpa [sampleScale, p, liftedCellMass, D] using
          oneArmLogDegree_taylor_budget_four_n hn
            (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    | some i =>
        have hx : oneArmShiftedSelectionGrid κ D i ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨(oneArmShiftedNodeScale_pos hκ hD).le.trans
              (oneArmShiftedSelectionGrid_mem_Icc hκ hκ1 hD i).1,
            (oneArmShiftedSelectionGrid_mem_Icc hκ hκ1 hD i).2⟩
        simpa [sampleScale, p, scale, x, liftedCellMass, D] using
          oneArmLogDegree_taylor_budget_four_n hn hx
  have hone :=
    tvDist_mixedTriplePoissonPMF_le_two_inv_sq_of_moments_log_budget
      ω₀ ω₁ lam11 lam10 lam0 lam11 lam10 lam0
      p pi mu p pi mu h11 h10 h0 h11 h10 h0 hs
      (by positivity : 0 < ((n : ℝ) ^ 2)) hp hp hpiIcc hpiIcc
      hmuIcc hmuIcc D hmoment hbudget hbudget
  have hproduct := tvDist_mixture_iid_productKernel_with_common_anchor_le
    ω₀ ω₁ anchorLaw
    (fun z => triplePoissonPMF (lam11 z) (lam10 z) (lam0 z))
    (fun z => triplePoissonPMF (lam11 z) (lam10 z) (lam0 z)) d
  refine hproduct.trans ?_
  calc
    (d : ℝ) * tvDist
        (ω₀.bind fun z => triplePoissonPMF (lam11 z) (lam10 z) (lam0 z)).toMeasure
        (ω₁.bind fun z => triplePoissonPMF (lam11 z) (lam10 z) (lam0 z)).toMeasure ≤
      (d : ℝ) * (2 * ((n : ℝ) ^ 2)⁻¹ ^ 2) := by
        gcongr
        simpa [mixedTriplePoissonPMF] using hone
    _ = 2 * (d : ℝ) / (n : ℝ) ^ 4 := by
      field_simp

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
