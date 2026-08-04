import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Entropy

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Zhao-event transport for bounded linear localization
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationZhao

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationAdapters
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationEntropy

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

noncomputable def zhaoEvent
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (u delta : ℝ) : Set (Fin n → 𝒳 × 𝒜) :=
  {sample | ∀ g₁ ∈ predictionPolytope E, ∀ g₂ ∈ predictionPolytope E,
    (∫ w, (g₁ w.1 w.2 - g₂ w.1 w.2) ^ 2
      ∂finiteContextActionLaw (contextMass P) E.reference) ≤
      2 / n * ∑ i, (g₁ (sample i).1 (sample i).2 -
        g₂ (sample i).1 (sample i).2) ^ 2 +
      32 / (3 * n) *
        Real.log (2 * supCoveringNumber (predictionPolytope E) u / delta) +
      10 * u}

def loggedZhaoEvent
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (u delta : ℝ) : Set (LoggedSample n 𝒳 𝒜) :=
  loggedDesign ⁻¹' zhaoEvent (n := n) E P u delta

lemma zhaoEvent_measurable
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (u delta : ℝ) :
    MeasurableSet (zhaoEvent (n := n) E P u delta) :=
  Set.toFinite _ |>.measurableSet

lemma loggedZhaoEvent_measurable
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (u delta : ℝ) :
    MeasurableSet (loggedZhaoEvent (n := n) E P u delta) :=
  loggedDesign_measurable
    (zhaoEvent_measurable (n := n) E P u delta)

lemma finiteContextActionLaw_integral
    (rho : 𝒳 → ℝ) (pi : Policy 𝒳 𝒜)
    (hrho : ∀ x, 0 ≤ rho x) (hpi : IsPolicy pi)
    (f : 𝒳 × 𝒜 → ℝ) :
    (∫ w, f w ∂finiteContextActionLaw rho pi) =
      ∑ x, rho x * ∑ a, pi x a * f (x, a) := by
  unfold finiteContextActionLaw
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_finset_sum_measure]
    · simp only [integral_smul_measure, integral_dirac]
      simp_rw [ENNReal.toReal_ofReal
        (mul_nonneg (hrho x) (hpi.1 x _))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp [smul_eq_mul, mul_assoc]
    · intro a _
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · intro x _
    rw [integrable_finset_sum_measure]
    intro a _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma zhaoEvent_probability
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D u delta : ℝ)
    (hshell : ExactShell E P C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) (hu : 0 < u) (hu1 : u < 1)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (productLaw E P n).real
      (loggedZhaoEvent (n := n) E P u delta) ≥ 1 - delta := by
  let hμ := finiteContextActionLaw_isProbability E P C D hshell
  have hz := hZhao (contextMass P) E.reference
    (contextMass_nonneg_local E P) (contextMass_sum_one E P)
    E.reference_isPolicy hμ (predictionPolytope E) n u delta hn
    (fun _ h => h.1) hu hu1 hdelta hdelta1
  have hmap := loggedDesign_map_productLaw
    (n := n) E P C D hshell
  have happly := Measure.map_apply loggedDesign_measurable
    (zhaoEvent_measurable (n := n) E P u delta)
    (μ := productLaw E P n)
  rw [hmap] at happly
  calc
    (productLaw E P n).real
        (loggedZhaoEvent (n := n) E P u delta) =
      (iidProduct
        (finiteContextActionLaw (contextMass P) E.reference)
        hμ n).real (zhaoEvent (n := n) E P u delta) := by
      unfold Measure.real loggedZhaoEvent
      exact congrArg ENNReal.toReal happly.symm
    _ ≥ 1 - delta := hz

end CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationZhao
