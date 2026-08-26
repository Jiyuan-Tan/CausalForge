import Causalean.Stat.Minimax.TotalVariation
import Mathlib.MeasureTheory.Measure.Real

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open scoped NNReal ENNReal

lemma tvDist_triangle' {Ω : Type*} [MeasurableSpace Ω]
    (P Q R : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    tvDist P R ≤ tvDist P Q + tvDist Q R := by
  unfold tvDist
  apply ciSup_le
  intro A
  have hPQ := abs_measureReal_sub_le_tvDist
    (μ := P) (ν := Q) A.2
  have hQR := abs_measureReal_sub_le_tvDist
    (μ := Q) (ν := R) A.2
  calc
    |P.real A.1 - R.real A.1| ≤
        |P.real A.1 - Q.real A.1| + |Q.real A.1 - R.real A.1| := by
      exact abs_sub_le _ _ _
    _ ≤ tvDist P Q + tvDist Q R := add_le_add hPQ hQR

/-- Conditioning a prior perturbs its predictive law by at most the discarded
prior mass.  The hypothesis is the good/bad mixture decomposition induced by
conditioning; the conclusion is independent of the observation kernel. -/
lemma tvDist_conditionedPredictive_le_badMass
    {Ω : Type*} [MeasurableSpace Ω]
    (Q QE QB : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure QE] [IsProbabilityMeasure QB]
    (q : ℝ≥0) (hq : q ≤ 1)
    (hdecomp : Q = q • QE + (1 - q) • QB) :
    tvDist QE Q ≤ ((1 - q : ℝ≥0) : ℝ) := by
  unfold tvDist
  apply ciSup_le
  intro A
  rw [hdecomp]
  rw [measureReal_add_apply, measureReal_nnreal_smul_apply,
    measureReal_nnreal_smul_apply]
  have hqreal : (q : ℝ) + ((1 - q : ℝ≥0) : ℝ) = 1 := by
    rw [NNReal.coe_sub hq]
    norm_num
  have hqexpr : (q : ℝ) = 1 - ((1 - q : ℝ≥0) : ℝ) := by linarith
  have hrewrite :
      QE.real A.1 -
          ((q : ℝ) * QE.real A.1 + ((1 - q : ℝ≥0) : ℝ) * QB.real A.1) =
        ((1 - q : ℝ≥0) : ℝ) * (QE.real A.1 - QB.real A.1) := by
    rw [hqexpr]
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (NNReal.coe_nonneg (1 - q))]
  have htvone : |QE.real A.1 - QB.real A.1| ≤ 1 :=
    abs_measureReal_sub_le_one (μ := QE) (ν := QB) A.1
  exact mul_le_of_le_one_right (NNReal.coe_nonneg (1 - q)) htvone

/-- Two conditioned prior predictives are bounded by their unconditioned TV
plus the two discarded prior masses. -/
lemma tvDist_two_conditionedPredictives_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Q₀ Q₁ QE₀ QE₁ QB₀ QB₁ : Measure Ω)
    [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure QE₀] [IsProbabilityMeasure QE₁]
    [IsProbabilityMeasure QB₀] [IsProbabilityMeasure QB₁]
    (q₀ q₁ : ℝ≥0) (hq₀ : q₀ ≤ 1) (hq₁ : q₁ ≤ 1)
    (hdecomp₀ : Q₀ = q₀ • QE₀ + (1 - q₀) • QB₀)
    (hdecomp₁ : Q₁ = q₁ • QE₁ + (1 - q₁) • QB₁) :
    tvDist QE₀ QE₁ ≤
      ((1 - q₀ : ℝ≥0) : ℝ) + tvDist Q₀ Q₁ + ((1 - q₁ : ℝ≥0) : ℝ) := by
  have h0 := tvDist_conditionedPredictive_le_badMass
    Q₀ QE₀ QB₀ q₀ hq₀ hdecomp₀
  have h1 := tvDist_conditionedPredictive_le_badMass
    Q₁ QE₁ QB₁ q₁ hq₁ hdecomp₁
  rw [tvDist_symm QE₁ Q₁] at h1
  calc
    tvDist QE₀ QE₁ ≤ tvDist QE₀ Q₀ + tvDist Q₀ QE₁ :=
      tvDist_triangle' QE₀ Q₀ QE₁
    _ ≤ ((1 - q₀ : ℝ≥0) : ℝ) + (tvDist Q₀ Q₁ + tvDist Q₁ QE₁) :=
      add_le_add h0 (tvDist_triangle' Q₀ Q₁ QE₁)
    _ ≤ ((1 - q₀ : ℝ≥0) : ℝ) +
        (tvDist Q₀ Q₁ + ((1 - q₁ : ℝ≥0) : ℝ)) := by
      gcongr
    _ = ((1 - q₀ : ℝ≥0) : ℝ) + tvDist Q₀ Q₁ +
        ((1 - q₁ : ℝ≥0) : ℝ) := by ring

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
