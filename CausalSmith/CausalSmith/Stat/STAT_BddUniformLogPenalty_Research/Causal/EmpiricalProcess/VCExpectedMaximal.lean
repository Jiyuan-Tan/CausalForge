import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.EntropyChaining
import Causalean.Stat.Concentration.Rademacher.Symmetrization
import Causalean.Stat.Concentration.UniformDeviation.LocalizedEnvelopeExpectation

/-!
# Variance-adaptive expected maximal inequality

This is an in-run lemma assembled from the proved Causalean symmetrization,
Dudley/VC entropy, and localized critical-radius layers.  It replaces the
retired external assumption: consumers call this theorem and carry no
additional empirical-process binder.
-/

open MeasureTheory Set
open scoped ENNReal
open Causalean.Stat.Concentration

namespace CausalSmith.Stat.BddUniformLogPenalty

-- @node: outerLIntegral_le_lintegral_of_ae_eq_measurable
/-- An a.e. equality with a measurable representative bounds the pointwise-majorant
outer integral by the representative's lower integral. -/
lemma outerLIntegral_le_lintegral_of_ae_eq_measurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ≥0∞} (hg : Measurable g) (hfg : f =ᵐ[μ] g) :
    MeasureTheory.outerLIntegral μ f ≤ ∫⁻ x, g x ∂μ := by
  classical
  let s : Set Ω := {x | f x ≠ g x}
  have hs0 : μ s = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    simpa [s, Filter.EventuallyEq] using hfg
  obtain ⟨t, hst, htmeas, ht0⟩ := exists_measurable_superset_of_null hs0
  let G : Ω → ℝ≥0∞ := fun x => if x ∈ t then ∞ else g x
  have hGmeas : Measurable G := by
    exact Measurable.ite htmeas measurable_const hg
  have hfG : f ≤ G := by
    intro x
    by_cases hxt : x ∈ t
    · simp [G, hxt]
    · have hxs : x ∉ s := fun hxs => hxt (hst hxs)
      have hxfg : f x = g x := by simpa [s] using hxs
      simp [G, hxt, hxfg]
  rw [MeasureTheory.outerLIntegral]
  refine (iInf_le_of_le G (iInf_le_of_le hGmeas (iInf_le_of_le hfG ?_)))
  apply le_of_eq
  apply lintegral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp ht0] with x hxt
  simp [G, hxt]

/-- Pointwise supremum of the centered empirical process. -/
noncomputable def empiricalProcessSup {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : ι → Ω → ℝ) {n : ℕ} (w : Fin n → Ω) : ℝ≥0∞ :=
  ⨆ i : ι, ENNReal.ofReal |centeredEmpiricalAverage μ w (g i)|

/-- The continuum outer integral obeys the explicit variance-adaptive VC
rate before the logarithm is normalized to a problem-specific ratio. -/
-- @node: vcExpectedMaximalInequality_explicit
lemma vcExpectedMaximalInequality_explicit
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (g : ι → Ω → ℝ) (U σ A v : ℝ)
    (hsep : HasCountableEmpiricalSupReduction μ g)
    (hent : HasVCUniformEntropy μ g U σ A v) :
    ∀ n : ℕ, 1 ≤ n →
      MeasureTheory.outerLIntegral (Measure.pi (fun _ : Fin n => μ))
          (empiricalProcessSup μ g) ≤
        ENNReal.ofReal (varianceAdaptiveVCConstant *
          vcExpectedMaximalRate U σ A v n) := by
  rcases hsep with ⟨hmeas, g0, hreduce⟩
  rcases hent with ⟨hσ, hσU, hA, hv, _hmeas', henv, hL2, hcover⟩
  intro n hn
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  let F : ℕ → Ω → ℝ := fun k => g (g0 k)
  let μn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  have hFmeas : ∀ k, Measurable (F k) := fun k => hmeas (g0 k)
  have hFenv : ∀ k x, |F k x| ≤ U := fun k x => henv (g0 k) x
  have hmain := varianceAdaptiveExpectedMaximal_le μ F hσ hσU hA hv
    hFmeas hFenv (fun k => hL2 (g0 k)) (hcover g0) n hn0
  have hdevMeas : Measurable (fun w : Fin n → Ω => countableEmpiricalSup μ F w) := by
    exact uniformDeviation_measurable id hFmeas
  have hU : 0 < U := hσ.trans hσU
  have hdevBound : ∀ w : Fin n → Ω, countableEmpiricalSup μ F w ≤ 2 * U := by
    intro w
    unfold countableEmpiricalSup uniformDeviation
    apply ciSup_le
    intro k
    have hint : Integrable (F k) μ :=
      Integrable.of_bound (hFmeas k).aestronglyMeasurable U
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hFenv k x)
    have hmean : |∫ x, F k x ∂μ| ≤ U := by
      calc
        |∫ x, F k x ∂μ| ≤ ∫ x, |F k x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _x, U ∂μ := integral_mono hint.abs (integrable_const U) (hFenv k)
        _ = U := by simp
    have havg : |(n : ℝ)⁻¹ * ∑ i, F k (w i)| ≤ U := by
      calc
        _ = (n : ℝ)⁻¹ * |∑ i, F k (w i)| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn0))]
        _ ≤ (n : ℝ)⁻¹ * ∑ i, |F k (w i)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, U := by
          gcongr with i
          exact hFenv k (w i)
        _ = U := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
    change |(n : ℝ)⁻¹ * ∑ i, F k (w i) - ∫ x, F k x ∂μ| ≤ 2 * U
    exact (abs_sub _ _).trans (by linarith)
  have hdevNonneg : ∀ w : Fin n → Ω, 0 ≤ countableEmpiricalSup μ F w := by
    intro w
    exact Real.iSup_nonneg fun k => abs_nonneg _
  have hdevInt : Integrable (fun w : Fin n → Ω => countableEmpiricalSup μ F w) μn :=
    Integrable.of_bound hdevMeas.aestronglyMeasurable (2 * U)
      (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hdevNonneg w)]
        exact hdevBound w)
  have hcountEq (w : Fin n → Ω) :
      ENNReal.ofReal (countableEmpiricalSup μ F w) =
        ⨆ k : ℕ, ENNReal.ofReal |centeredEmpiricalAverage μ w (g (g0 k))| := by
    unfold countableEmpiricalSup uniformDeviation
    change ENNReal.ofReal
        (⨆ k : ℕ, |centeredEmpiricalAverage μ w (F k)|) =
      ⨆ k : ℕ, ENNReal.ofReal |centeredEmpiricalAverage μ w (F k)|
    refine (Monotone.map_ciSup_of_continuousAt
      (g := fun k : ℕ => |centeredEmpiricalAverage μ w (F k)|)
      ENNReal.continuous_ofReal.continuousAt ENNReal.ofReal_mono (bdd := ?_))
    refine ⟨2 * U, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hint : Integrable (F k) μ :=
      Integrable.of_bound (hFmeas k).aestronglyMeasurable U
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hFenv k x)
    have hmean : |∫ x, F k x ∂μ| ≤ U := by
      calc
        |∫ x, F k x ∂μ| ≤ ∫ x, |F k x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _x, U ∂μ := integral_mono hint.abs (integrable_const U) (hFenv k)
        _ = U := by simp
    have havg : |(n : ℝ)⁻¹ * ∑ i, F k (w i)| ≤ U := by
      calc
        _ = (n : ℝ)⁻¹ * |∑ i, F k (w i)| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn0))]
        _ ≤ (n : ℝ)⁻¹ * ∑ i, |F k (w i)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, U := by
          gcongr with i
          exact hFenv k (w i)
        _ = U := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
    change |(n : ℝ)⁻¹ * ∑ i, F k (w i) - ∫ x, F k x ∂μ| ≤ 2 * U
    exact (abs_sub _ _).trans (by linarith)
  have hsupMeas : Measurable
      (fun w : Fin n → Ω => ENNReal.ofReal (countableEmpiricalSup μ F w)) :=
    ENNReal.measurable_ofReal.comp hdevMeas
  calc
    MeasureTheory.outerLIntegral μn (empiricalProcessSup μ g) ≤
        ∫⁻ w, ENNReal.ofReal (countableEmpiricalSup μ F w) ∂μn :=
      outerLIntegral_le_lintegral_of_ae_eq_measurable μn hsupMeas (by
        filter_upwards [hreduce n] with w hw
        rw [empiricalProcessSup, hw]
        exact (hcountEq w).symm)
    _ = ENNReal.ofReal (∫ w, countableEmpiricalSup μ F w ∂μn) := by
      rw [ofReal_integral_eq_lintegral_ofReal hdevInt (ae_of_all _ hdevNonneg)]
    _ ≤ ENNReal.ofReal (varianceAdaptiveVCConstant *
          vcExpectedMaximalRate U σ A v n) := ENNReal.ofReal_le_ofReal hmain

/-- A countably reducible VC-type class obeys the variance-adaptive two-term
expected maximal inequality. -/
lemma vcExpectedMaximalInequality
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (g : ι → Ω → ℝ) (U σ A v : ℝ)
    (hsep : HasCountableEmpiricalSupReduction μ g)
    (hent : HasVCUniformEntropy μ g U σ A v) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      MeasureTheory.outerLIntegral (Measure.pi (fun _ : Fin n => μ))
          (empiricalProcessSup μ g) ≤
        ENNReal.ofReal (C *
          (σ * Real.sqrt (Real.log (U / σ) / n) +
            U * Real.log (U / σ) / n)) := by
  rcases hsep with ⟨hmeas, g0, hreduce⟩
  rcases vcEntropy_chaining_bound μ g g0 U σ A v hent with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hg_meas : ∀ k, Measurable (g (g0 k)) := fun k => hmeas (g0 k)
  have havg_meas : ∀ k,
      Measurable (fun w : Fin n → Ω =>
        centeredEmpiricalAverage μ w (g (g0 k))) := by
    intro k
    unfold centeredEmpiricalAverage
    fun_prop
  have hsup_meas : Measurable
      (countableEmpiricalProcessSup μ g g0 : (Fin n → Ω) → ℝ≥0∞) := by
    unfold countableEmpiricalProcessSup
    fun_prop
  exact (outerLIntegral_le_lintegral_of_ae_eq_measurable
    (Measure.pi (fun _ : Fin n => μ)) hsup_meas (hreduce n)).trans (hbound n hn)

end CausalSmith.Stat.BddUniformLogPenalty
