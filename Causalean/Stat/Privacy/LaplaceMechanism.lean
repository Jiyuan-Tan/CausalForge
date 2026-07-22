/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Laplace mechanism and pure differential privacy

This file supplies the classical centred Laplace distribution, its density-ratio
bound, scalar and finite-dimensional Laplace mechanisms, and post-processing
lemmas.  Dataset types and adjacency relations remain completely abstract.
-/

namespace Causalean.Stat.Privacy

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The centered Laplace density at a real value decays exponentially with its absolute distance
from zero and is normalized by twice its positive scale. -/
def laplacePDF (b x : ℝ) : ℝ := (2 * b)⁻¹ * Real.exp (-|x| / b)

/-- The centered Laplace distribution is obtained by weighting Lebesgue measure with the centered
Laplace density at the chosen scale. -/
def laplaceMeasure (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (laplacePDF b x))

private lemma laplacePDF_nonneg {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 ≤ laplacePDF b x := by
  unfold laplacePDF
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hb.le)) (Real.exp_pos _).le

private lemma measurable_laplacePDF (b : ℝ) : Measurable (laplacePDF b) := by
  unfold laplacePDF
  fun_prop

private lemma integrable_laplacePDF {b : ℝ} (hb : 0 < b) :
    Integrable (laplacePDF b) := by
  have hpos : 0 < (1 / b : ℝ) := one_div_pos.mpr hb
  have hneg : (-1 / b : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hb
  have hleft : IntegrableOn (laplacePDF b) (Iic 0) := by
    have h := (integrableOn_exp_mul_Iic hpos 0).const_mul ((2 * b)⁻¹)
    exact (integrableOn_congr_fun (fun x hx => by
      have hx' : x ≤ 0 := hx
      simp only [laplacePDF, abs_of_nonpos hx']
      congr 2
      field_simp) measurableSet_Iic).mpr h
  have hright : IntegrableOn (laplacePDF b) (Ioi 0) := by
    have h := (integrableOn_exp_mul_Ioi hneg 0).const_mul ((2 * b)⁻¹)
    exact (integrableOn_congr_fun (fun x hx => by
      have hx' : 0 < x := hx
      simp only [laplacePDF, abs_of_pos hx']
      congr 2
      field_simp) measurableSet_Ioi).mpr h
  rw [← integrableOn_univ]
  simpa only [Iic_union_Ioi] using hleft.union hright

private lemma integral_laplacePDF {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, laplacePDF b x = 1 := by
  have hpos : 0 < (1 / b : ℝ) := one_div_pos.mpr hb
  have hneg : (-1 / b : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hb
  have hleft : IntegrableOn (laplacePDF b) (Iic 0) :=
    (integrable_laplacePDF hb).integrableOn
  have hright : IntegrableOn (laplacePDF b) (Ioi 0) :=
    (integrable_laplacePDF hb).integrableOn
  rw [← integral_add_compl measurableSet_Iic (integrable_laplacePDF hb)]
  rw [compl_Iic]
  rw [show (∫ x in Iic 0, laplacePDF b x) = (2 * b)⁻¹ * b by
      calc
        _ = ∫ x in Iic 0, (2 * b)⁻¹ * Real.exp ((1 / b) * x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
          have hx' : x ≤ 0 := hx
          simp only [laplacePDF, abs_of_nonpos hx']
          congr 2
          field_simp
        _ = _ := by
          rw [integral_const_mul, integral_exp_mul_Iic hpos 0]
          simp,
      show (∫ x in Ioi 0, laplacePDF b x) = (2 * b)⁻¹ * b by
      calc
        _ = ∫ x in Ioi 0, (2 * b)⁻¹ * Real.exp ((-1 / b) * x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hx' : 0 < x := hx
          simp only [laplacePDF, abs_of_pos hx']
          congr 2
          field_simp
        _ = _ := by
          rw [integral_const_mul, integral_exp_mul_Ioi hneg 0]
          simp]
  field_simp
  norm_num

/-- At every positive scale, the centered Laplace measure has total mass one and therefore defines
a probability distribution. -/
theorem laplaceMeasure_isProbabilityMeasure (b : ℝ) (hb : 0 < b) :
    IsProbabilityMeasure (laplaceMeasure b) := by
  refine ⟨?_⟩
  rw [laplaceMeasure, withDensity_apply _ MeasurableSet.univ]
  rw [Measure.restrict_univ]
  have hdens : (fun x => ENNReal.ofReal (laplacePDF b x)) =
      fun x => (Real.toNNReal (laplacePDF b x) : ENNReal) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (laplacePDF_nonneg hb x)]
    congr 1
    ext
    simp [Real.toNNReal_of_nonneg (laplacePDF_nonneg hb x)]
  rw [hdens, lintegral_coe_eq_integral]
  · convert congrArg ENNReal.ofReal (integral_laplacePDF hb) using 1 <;>
      simp [max_eq_left (laplacePDF_nonneg hb _)]
  · simpa [Real.toNNReal_of_nonneg, laplacePDF_nonneg hb] using integrable_laplacePDF hb

/-- Moving the center of a positive-scale Laplace density changes its value at any observation by
at most an exponential factor determined by the distance between the old and new centers divided
by the scale. -/
theorem laplacePDF_shift_le (b u v z : ℝ) (hb : 0 < b) :
    laplacePDF b (z - u) ≤
      Real.exp (|u - v| / b) * laplacePDF b (z - v) := by
  have htri : |z - v| - |z - u| ≤ |u - v| := by
    calc
      |z - v| - |z - u| ≤ |(z - v) - (z - u)| :=
        abs_sub_abs_le_abs_sub (z - v) (z - u)
      _ = |u - v| := by congr 1; simp
  have hexp : Real.exp (-|z - u| / b) ≤
      Real.exp (|u - v| / b) * Real.exp (-|z - v| / b) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    rw [show |u - v| / b + -|z - v| / b =
        (|u - v| - |z - v|) / b by ring]
    exact (div_le_div_iff_of_pos_right hb).2 (by linarith)
  unfold laplacePDF
  calc
    (2 * b)⁻¹ * Real.exp (-|z - u| / b) ≤
        (2 * b)⁻¹ * (Real.exp (|u - v| / b) * Real.exp (-|z - v| / b)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (|u - v| / b) *
        ((2 * b)⁻¹ * Real.exp (-|z - v| / b)) := by ring

/-- The scalar Laplace mechanism releases a real-valued query after adding independent centered
Laplace noise at the chosen scale. -/
def laplaceMech {D : Type*} (b : ℝ) (q : D → ℝ) : D → Measure ℝ :=
  fun d => (laplaceMeasure b).map (fun z => z + q d)

private lemma laplaceMech_eq_withDensity {D : Type*} (b : ℝ) (q : D → ℝ) (d : D) :
    laplaceMech b q d =
      volume.withDensity (fun x => ENNReal.ofReal (laplacePDF b (x - q d))) := by
  apply Measure.ext
  intro s hs
  rw [laplaceMech, Measure.map_apply (by fun_prop) hs, laplaceMeasure,
    withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage (by fun_prop)), ← lintegral_indicator hs]
  have hfun : Measurable
      (fun x => s.indicator (fun y => ENNReal.ofReal (laplacePDF b (y - q d))) x) :=
    (((measurable_laplacePDF b).comp (by fun_prop)).ennreal_ofReal).indicator hs
  calc
    _ = ∫⁻ a, (fun x => s.indicator
          (fun y => ENNReal.ofReal (laplacePDF b (y - q d))) x) (a + q d) := by
      apply lintegral_congr
      intro x
      by_cases hx : x + q d ∈ s
      · simp [hx]
      · simp [hx]
    _ = ∫⁻ a, s.indicator
          (fun y => ENNReal.ofReal (laplacePDF b (y - q d))) a ∂Measure.map (· + q d) volume := by
      rw [lintegral_map hfun (by fun_prop)]
    _ = ∫⁻ a, s.indicator
          (fun y => ENNReal.ofReal (laplacePDF b (y - q d))) a := by
      rw [map_add_right_eq_self]

/-- Adding positive-scale Laplace noise to a scalar query produces a probability distribution for
the release under every dataset. -/
theorem laplaceMech_isProbabilityMeasure {D : Type*} (b : ℝ) (hb : 0 < b)
    (q : D → ℝ) (d : D) : IsProbabilityMeasure (laplaceMech b q d) := by
  letI : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  unfold laplaceMech
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- A scalar query with a positive sensitivity bound becomes purely differentially private when
independent Laplace noise is calibrated by dividing that bound by the positive privacy level. -/
theorem laplaceMech_pure_dp {D : Type*} (Adj : D → D → Prop) (q : D → ℝ)
    {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsens : ∀ d d', Adj d d' → |q d - q d'| ≤ Δ) :
    ∀ d d', Adj d d' → ∀ s, MeasurableSet s →
      (laplaceMech (Δ / ε) q d).real s ≤
        Real.exp ε * (laplaceMech (Δ / ε) q d').real s := by
  intro d d' hadd s hs
  have hb : 0 < Δ / ε := div_pos hΔ hε
  have hscale : |q d - q d'| / (Δ / ε) ≤ ε := by
    apply (div_le_iff₀ hb).2
    calc
      |q d - q d'| ≤ Δ := hsens d d' hadd
      _ = ε * (Δ / ε) := by field_simp
  have hpdf (x : ℝ) : laplacePDF (Δ / ε) (x - q d) ≤
      Real.exp ε * laplacePDF (Δ / ε) (x - q d') := by
    calc
      laplacePDF (Δ / ε) (x - q d) ≤
          Real.exp (|q d - q d'| / (Δ / ε)) *
            laplacePDF (Δ / ε) (x - q d') :=
        laplacePDF_shift_le (Δ / ε) (q d) (q d') x hb
      _ ≤ Real.exp ε * laplacePDF (Δ / ε) (x - q d') := by
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hscale)
          (laplacePDF_nonneg hb _)
  have hmeasure : laplaceMech (Δ / ε) q d ≤
      (ENNReal.ofReal (Real.exp ε)) • laplaceMech (Δ / ε) q d' := by
    rw [laplaceMech_eq_withDensity, laplaceMech_eq_withDensity]
    let f : ℝ → ENNReal :=
      fun x => ENNReal.ofReal (laplacePDF (Δ / ε) (x - q d'))
    have hf : Measurable f :=
      ((measurable_laplacePDF (Δ / ε)).comp (by fun_prop)).ennreal_ofReal
    change volume.withDensity _ ≤ ENNReal.ofReal (Real.exp ε) • volume.withDensity f
    rw [← withDensity_smul (μ := volume) (ENNReal.ofReal (Real.exp ε)) hf]
    apply withDensity_mono
    filter_upwards with x
    change ENNReal.ofReal (laplacePDF (Δ / ε) (x - q d)) ≤
      ENNReal.ofReal (Real.exp ε) *
        ENNReal.ofReal (laplacePDF (Δ / ε) (x - q d'))
    rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le]
    exact ENNReal.ofReal_le_ofReal (hpdf x)
  have hle := hmeasure s
  rw [Measure.smul_apply] at hle
  letI : IsProbabilityMeasure (laplaceMech (Δ / ε) q d) :=
    laplaceMech_isProbabilityMeasure (Δ / ε) hb q d
  letI : IsProbabilityMeasure (laplaceMech (Δ / ε) q d') :=
    laplaceMech_isProbabilityMeasure (Δ / ε) hb q d'
  change ((laplaceMech (Δ / ε) q d) s).toReal ≤
    Real.exp ε * ((laplaceMech (Δ / ε) q d') s).toReal
  rw [← ENNReal.toReal_ofReal (Real.exp_pos ε).le, ← ENNReal.toReal_mul]
  · exact ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top (laplaceMech (Δ / ε) q d') s)) hle

/-- The finite-dimensional Laplace mechanism releases a vector-valued query after adding mutually
independent centered Laplace noise to its coordinates. -/
def laplaceMechPi {D ι : Type*} [Fintype ι] (b : ℝ) (q : D → (ι → ℝ)) :
    D → Measure (ι → ℝ) :=
  fun d => (Measure.pi (fun _ : ι => laplaceMeasure b)).map (fun z => z + q d)

/-- Adding independent positive-scale Laplace noise in finitely many coordinates produces a
probability distribution for the vector release under every dataset. -/
theorem laplaceMechPi_isProbabilityMeasure {D ι : Type*} [Fintype ι]
    (b : ℝ) (hb : 0 < b) (q : D → (ι → ℝ)) (d : D) :
    IsProbabilityMeasure (laplaceMechPi b q d) := by
  letI : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : ι => laplaceMeasure b)) :=
    inferInstance
  unfold laplaceMechPi
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma prod_le_smul_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β) [SFinite μ₂] [SFinite ν₂]
    (c₁ c₂ : ENNReal) (h₁ : μ₁ ≤ c₁ • ν₁) (h₂ : μ₂ ≤ c₂ • ν₂) :
    μ₁.prod μ₂ ≤ (c₁ * c₂) • ν₁.prod ν₂ := by
  have hprod : μ₁.prod μ₂ ≤ (c₁ • ν₁).prod (c₂ • ν₂) := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.prod_apply hs, Measure.prod_apply hs]
    exact lintegral_mono' h₁ (fun x => h₂ (Prod.mk x ⁻¹' s))
  simpa [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    mul_comm, mul_left_comm, mul_assoc] using hprod

private lemma pi_le_smul_pi_fin : ∀ (n : ℕ) (μ ν : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (c : Fin n → ENNReal),
    (∀ i, μ i ≤ c i • ν i) →
      Measure.pi μ ≤ (∏ i, c i) • Measure.pi ν := by
  intro n
  induction n with
  | zero =>
      intro μ ν _ _ c h
      have hμν : μ = ν := by
        funext i
        exact Fin.elim0 i
      simp [hμν]
  | succ n ih =>
      intro μ ν hμ hν c h
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have htail : Measure.pi (fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j)) ≤
          (∏ j : Fin n, c ((0 : Fin (n + 1)).succAbove j)) •
            Measure.pi (fun j : Fin n => ν ((0 : Fin (n + 1)).succAbove j)) :=
        ih (fun j => μ ((0 : Fin (n + 1)).succAbove j))
          (fun j => ν ((0 : Fin (n + 1)).succAbove j))
          (fun j => c ((0 : Fin (n + 1)).succAbove j))
          (fun j => h ((0 : Fin (n + 1)).succAbove j))
      have hp := prod_le_smul_prod (μ 0) (ν 0)
        (Measure.pi (fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j)))
        (Measure.pi (fun j : Fin n => ν ((0 : Fin (n + 1)).succAbove j)))
        (c 0) (∏ j : Fin n, c ((0 : Fin (n + 1)).succAbove j)) (h 0) htail
      have heμ := (measurePreserving_piFinSuccAbove μ 0).map_eq
      have heν := (measurePreserving_piFinSuccAbove ν 0).map_eq
      rw [← heμ, ← heν] at hp
      have hback := Measure.map_mono hp e.symm.measurable
      rw [Measure.map_smul,
        Measure.map_map e.symm.measurable e.measurable,
        Measure.map_map e.symm.measurable e.measurable] at hback
      have hid : (e.symm : (ℝ × (Fin n → ℝ)) → (Fin (n + 1) → ℝ)) ∘ e = id := by
        funext x
        exact e.symm_apply_apply x
      rw [hid, Measure.map_id] at hback
      rw [Fin.prod_univ_succAbove c 0]
      simpa [smul_smul] using hback

private lemma pi_le_smul_pi {ι : Type*} [Fintype ι]
    (μ ν : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (c : ι → ENNReal) (h : ∀ i, μ i ≤ c i • ν i) :
    Measure.pi μ ≤ (∏ i, c i) • Measure.pi ν := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hfin := pi_le_smul_pi_fin (Fintype.card ι) (fun j => μ (e j))
    (fun j => ν (e j)) (fun j => c (e j)) (fun j => h (e j))
  have heμ := (measurePreserving_piCongrLeft μ e).map_eq
  have heν := (measurePreserving_piCongrLeft ν e).map_eq
  have hmapped := Measure.map_mono hfin
    (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e).measurable
  rw [heμ, Measure.map_smul, heν] at hmapped
  rw [e.prod_comp c] at hmapped
  exact hmapped

private lemma laplace_shift_measure_le (b u v : ℝ) (hb : 0 < b) :
    (laplaceMeasure b).map (fun z => z + u) ≤
      ENNReal.ofReal (Real.exp (|u - v| / b)) •
        (laplaceMeasure b).map (fun z => z + v) := by
  let qu : Unit → ℝ := fun _ => u
  let qv : Unit → ℝ := fun _ => v
  rw [show (laplaceMeasure b).map (fun z => z + u) = laplaceMech b qu () by rfl,
    show (laplaceMeasure b).map (fun z => z + v) = laplaceMech b qv () by rfl,
    laplaceMech_eq_withDensity, laplaceMech_eq_withDensity]
  let f : ℝ → ENNReal := fun x => ENNReal.ofReal (laplacePDF b (x - v))
  have hf : Measurable f :=
    ((measurable_laplacePDF b).comp (by fun_prop)).ennreal_ofReal
  change volume.withDensity _ ≤
    ENNReal.ofReal (Real.exp (|u - v| / b)) • volume.withDensity f
  rw [← withDensity_smul (μ := volume)
    (ENNReal.ofReal (Real.exp (|u - v| / b))) hf]
  apply withDensity_mono
  filter_upwards with x
  change ENNReal.ofReal (laplacePDF b (x - u)) ≤
    ENNReal.ofReal (Real.exp (|u - v| / b)) *
      ENNReal.ofReal (laplacePDF b (x - v))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (laplacePDF_shift_le b u v x hb)

private lemma laplaceMechPi_eq_pi_shift {D ι : Type*} [Fintype ι]
    (b : ℝ) (hb : 0 < b) (q : D → (ι → ℝ)) (d : D) :
    laplaceMechPi b q d =
      Measure.pi (fun i : ι => (laplaceMeasure b).map (fun z => z + q d i)) := by
  letI : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  letI (i : ι) : IsProbabilityMeasure
      ((laplaceMeasure b).map (fun z => z + q d i)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hmp := measurePreserving_pi (fun _ : ι => laplaceMeasure b)
    (fun i : ι => (laplaceMeasure b).map (fun z => z + q d i))
    (fun i : ι => by
      exact ⟨by fun_prop, rfl⟩)
  rw [laplaceMechPi]
  convert hmp.map_eq using 1

/-- A finite vector query with a positive ℓ¹-sensitivity bound becomes purely differentially
private when each coordinate receives independent Laplace noise calibrated by dividing that bound
by the positive privacy level. -/
theorem laplaceMechPi_pure_dp {D ι : Type*} [Fintype ι]
    (Adj : D → D → Prop) (q : D → (ι → ℝ)) {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsens : ∀ d d', Adj d d' → ∑ i, |q d i - q d' i| ≤ Δ) :
    ∀ d d', Adj d d' → ∀ s, MeasurableSet s →
      (laplaceMechPi (Δ / ε) q d).real s ≤
        Real.exp ε * (laplaceMechPi (Δ / ε) q d').real s := by
  intro d d' hadd s hs
  have hb : 0 < Δ / ε := div_pos hΔ hε
  let μ : ι → Measure ℝ :=
    fun i => (laplaceMeasure (Δ / ε)).map (fun z => z + q d i)
  let ν : ι → Measure ℝ :=
    fun i => (laplaceMeasure (Δ / ε)).map (fun z => z + q d' i)
  let c : ι → ENNReal :=
    fun i => ENNReal.ofReal (Real.exp (|q d i - q d' i| / (Δ / ε)))
  letI (i : ι) : IsProbabilityMeasure (μ i) := by
    dsimp [μ]
    letI := laplaceMeasure_isProbabilityMeasure (Δ / ε) hb
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI (i : ι) : IsProbabilityMeasure (ν i) := by
    dsimp [ν]
    letI := laplaceMeasure_isProbabilityMeasure (Δ / ε) hb
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hpi : Measure.pi μ ≤ (∏ i, c i) • Measure.pi ν :=
    pi_le_smul_pi μ ν c (fun i => laplace_shift_measure_le _ _ _ hb)
  have hsum : (∑ i, |q d i - q d' i| / (Δ / ε)) ≤ ε := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hb).2
    calc
      (∑ i, |q d i - q d' i|) ≤ Δ := hsens d d' hadd
      _ = ε * (Δ / ε) := by field_simp
  have hc : (∏ i, c i) ≤ ENNReal.ofReal (Real.exp ε) := by
    change (∏ i, ENNReal.ofReal (Real.exp (|q d i - q d' i| / (Δ / ε)))) ≤ _
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← Real.exp_sum]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hsum)
  have hmeasure : laplaceMechPi (Δ / ε) q d ≤
      ENNReal.ofReal (Real.exp ε) • laplaceMechPi (Δ / ε) q d' := by
    rw [laplaceMechPi_eq_pi_shift (hb := hb), laplaceMechPi_eq_pi_shift (hb := hb)]
    apply hpi.trans
    rw [Measure.le_iff']
    intro t
    simp only [Measure.smul_apply, smul_eq_mul]
    change (∏ i, c i) * (Measure.pi ν) t ≤
      ENNReal.ofReal (Real.exp ε) * (Measure.pi ν) t
    gcongr
  have hle := hmeasure s
  rw [Measure.smul_apply] at hle
  letI := laplaceMechPi_isProbabilityMeasure (Δ / ε) hb q d
  letI := laplaceMechPi_isProbabilityMeasure (Δ / ε) hb q d'
  change ((laplaceMechPi (Δ / ε) q d) s).toReal ≤
    Real.exp ε * ((laplaceMechPi (Δ / ε) q d') s).toReal
  rw [← ENNReal.toReal_ofReal (Real.exp_pos ε).le, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top (laplaceMechPi (Δ / ε) q d') s)) hle

/-- Any pure differential-privacy guarantee also satisfies approximate differential privacy after
adding any nonnegative failure allowance. -/
theorem pure_dp_implies_approx_dp {α : Type*} [MeasurableSpace α]
    (M : D → Measure α) (d d' : D) (ε δ : ℝ)
    (hpure : ∀ s, MeasurableSet s →
      (M d).real s ≤ Real.exp ε * (M d').real s) (hδ : 0 ≤ δ) :
    ∀ s, MeasurableSet s →
      (M d).real s ≤ Real.exp ε * (M d').real s + δ := by
  intro s hs
  exact (hpure s hs).trans (le_add_of_nonneg_right hδ)

/-- Applying a measurable scalar summary to a private vector release preserves the same pure
differential-privacy guarantee. -/
theorem pure_dp_postprocess {D ι : Type*}
    (M : D → Measure (ι → ℝ)) (d d' : D) (ε : ℝ)
    (hM : ∀ s, MeasurableSet s →
      (M d).real s ≤ Real.exp ε * (M d').real s)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f) :
    ∀ s, MeasurableSet s →
      ((M d).map f).real s ≤ Real.exp ε * ((M d').map f).real s := by
  intro s hs
  change ((M d).map f s).toReal ≤ Real.exp ε * ((M d').map f s).toReal
  rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
  exact hM (f ⁻¹' s) (hs.preimage hf)

/-- Applying a measurable scalar summary to a vector release preserves the same approximate
differential-privacy guarantee. -/
theorem approx_dp_postprocess {D ι : Type*}
    (M : D → Measure (ι → ℝ)) (d d' : D) (ε δ : ℝ)
    (hM : ∀ s, MeasurableSet s →
      (M d).real s ≤ Real.exp ε * (M d').real s + δ)
    (_hδ : 0 ≤ δ) (f : (ι → ℝ) → ℝ) (hf : Measurable f) :
    ∀ s, MeasurableSet s →
      ((M d).map f).real s ≤
        Real.exp ε * ((M d').map f).real s + δ := by
  intro s hs
  change ((M d).map f s).toReal ≤ Real.exp ε * ((M d').map f s).toReal + δ
  rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
  exact hM (f ⁻¹' s) (hs.preimage hf)

private lemma integrable_abs_mul_laplacePDF (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| * laplacePDF b x) := by
  let f : ℝ → ℝ := fun x => (2 * b)⁻¹ * (x * Real.exp (-x / b))
  have hright : IntegrableOn f (Ioi 0) := by
    have hbase := Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num)
    have hscaled : IntegrableOn
        (fun x : ℝ => Real.exp (-(1 / b * x)) *
          (1 / b * x) ^ ((2 : ℝ) - 1)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) 0
        (one_div_pos.mpr hb)).mpr (by simpa using hbase)
    have hs : IntegrableOn
        (fun x : ℝ => (2 * b)⁻¹ *
          (b * (Real.exp (-(1 / b * x)) *
            (1 / b * x) ^ ((2 : ℝ) - 1)))) (Ioi 0) :=
      (hscaled.const_mul b).const_mul (2 * b)⁻¹
    refine hs.congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp only [f]
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    field_simp [hb.ne']
  have hright_abs : IntegrableOn (fun x => f |x|) (Ioi 0) := by
    refine hright.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change f x = f |x|
    rw [abs_of_pos (by simpa only [mem_Ioi] using hx)]
  have hall : Integrable (fun x => f |x|) := by
    have hleft : IntegrableOn (fun x => f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x :=
        (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright_abs
    rw [← integrableOn_univ]
    simpa only [Iic_union_Ioi] using hleft.union hright_abs
  refine hall.congr (ae_of_all _ fun x => ?_)
  simp only [f, laplacePDF]
  ring

/-- The absolute value of a centered Laplace draw has a finite expectation at every positive
scale. -/
theorem laplaceMeasure_integrable_abs (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => |x|) (laplaceMeasure b) := by
  rw [laplaceMeasure,
    integrable_withDensity_iff_integrable_smul' (measurable_laplacePDF b).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (laplacePDF_nonneg hb _), smul_eq_mul, mul_comm] using
    integrable_abs_mul_laplacePDF b hb

/-- The expected absolute value of a centered Laplace draw equals its positive scale. -/
theorem laplaceMeasure_integral_abs (b : ℝ) (hb : 0 < b) :
    ∫ x, |x| ∂(laplaceMeasure b) = b := by
  rw [laplaceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_laplacePDF b).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (laplacePDF_nonneg hb _), smul_eq_mul]
  let f : ℝ → ℝ := fun x => (2 * b)⁻¹ * (x * Real.exp (-x / b))
  rw [show (fun x : ℝ => laplacePDF b x * |x|) = fun x => f |x| by
    funext x
    simp only [f, laplacePDF]
    ring, integral_comp_abs]
  have hplain : (∫ x in Ioi (0 : ℝ), x * Real.exp (-x / b)) = b ^ 2 := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) *
          Real.exp (-((1 / b) * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
        rw [show -x / b = -(1 / b * x) by ring]
      _ = (1 / (1 / b)) ^ (2 : ℝ) * Real.Gamma (2 : ℝ) :=
        Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (one_div_pos.mpr hb)
      _ = b ^ 2 := by
        rw [show Real.Gamma (2 : ℝ) = 1 by norm_num]
        field_simp [hb.ne']
        exact Real.rpow_natCast b 2
  have hright : (∫ x in Ioi (0 : ℝ), f x) = (2 * b)⁻¹ * b ^ 2 := by
    rw [show f = fun x => (2 * b)⁻¹ * (x * Real.exp (-x / b)) by rfl,
      integral_const_mul, hplain]
  rw [hright]
  field_simp [hb.ne']

private lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    Real.sqrt (∑ i : ι, (w i) ^ 2) ≤ ∑ i : ι, |w i| := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · simpa [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i => |w i|) fun _ _ => abs_nonneg _)

/-- The expected Euclidean norm of a finite vector of independent centered Laplace draws is at most
the number of coordinates times their common positive scale. -/
theorem laplacePi_integral_euclidean_norm_le {ι : Type*} [Fintype ι]
    (b : ℝ) (hb : 0 < b) :
    ∫ w, Real.sqrt (∑ i : ι, (w i) ^ 2)
        ∂(Measure.pi fun _ : ι => laplaceMeasure b) ≤
      (Fintype.card ι : ℝ) * b := by
  letI : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  let P : Measure (ι → ℝ) := Measure.pi fun _ : ι => laplaceMeasure b
  have hcoord (i : ι) : Integrable (fun w : ι → ℝ => |w i|) P :=
    integrable_comp_eval (laplaceMeasure_integrable_abs b hb)
  have hsum : Integrable (fun w : ι → ℝ => ∑ i : ι, |w i|) P :=
    integrable_finset_sum _ fun i _ => hcoord i
  have hnorm : Integrable (fun w : ι → ℝ => Real.sqrt (∑ i : ι, (w i) ^ 2)) P := by
    have hcontinuous : Continuous (fun w : ι → ℝ =>
        Real.sqrt (∑ i : ι, (w i) ^ 2)) :=
      Real.continuous_sqrt.comp
        (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)
    refine hsum.mono' hcontinuous.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_sum_sq_le_sum_abs w
  calc
    ∫ w, Real.sqrt (∑ i : ι, (w i) ^ 2) ∂P ≤
        ∫ w, ∑ i : ι, |w i| ∂P :=
      integral_mono hnorm hsum (sqrt_sum_sq_le_sum_abs)
    _ = ∑ i : ι, ∫ w, |w i| ∂P :=
      integral_finset_sum _ fun i _ => hcoord i
    _ = ∑ _i : ι, b := by
      congr 1 with i
      change (∫ w : ι → ℝ, |w i| ∂Measure.pi (fun _ : ι => laplaceMeasure b)) = b
      exact (integral_comp_eval
        (μ := fun _ : ι => laplaceMeasure b) (i := i) (f := fun x : ℝ => |x|)
        (Continuous.aestronglyMeasurable continuous_abs)).trans
          (laplaceMeasure_integral_abs b hb)
    _ = (Fintype.card ι : ℝ) * b := by simp

/-- The Euclidean norm of finitely many independent centered Laplace draws has a finite expectation
whenever their common scale is positive. -/
theorem laplacePi_integrable_euclidean_norm {ι : Type*} [Fintype ι]
    (b : ℝ) (hb : 0 < b) :
    Integrable (fun w : ι → ℝ => Real.sqrt (∑ i : ι, (w i) ^ 2))
      (Measure.pi fun _ : ι => laplaceMeasure b) := by
  letI : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  have hcoord (i : ι) : Integrable (fun w : ι → ℝ => |w i|)
      (Measure.pi fun _ : ι => laplaceMeasure b) :=
    integrable_comp_eval (laplaceMeasure_integrable_abs b hb)
  have hsum : Integrable (fun w : ι → ℝ => ∑ i : ι, |w i|)
      (Measure.pi fun _ : ι => laplaceMeasure b) :=
    integrable_finset_sum _ fun i _ => hcoord i
  have hcontinuous : Continuous (fun w : ι → ℝ =>
      Real.sqrt (∑ i : ι, (w i) ^ 2)) :=
    Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)
  refine hsum.mono' hcontinuous.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_sum_sq_le_sum_abs w

end

end Causalean.Stat.Privacy
