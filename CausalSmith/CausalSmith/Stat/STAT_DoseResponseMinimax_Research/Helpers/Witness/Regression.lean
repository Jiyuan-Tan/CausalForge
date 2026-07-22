/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: the two semantic ties (regression + ignorability)

The anti-laundering ties of the genuine construction:
`MuIsRegression` (the conditional mean of `Y` given `(A,X)` IS `μ_ζ(A,X)`) and
`NoUnmeasuredConfounding` (the potential outcome `Y(a)` is `A ⟂ · | X`). Both are
proved on the genuine joint law `doseDataMeasure` viewed through its single-bind
restructuring `doseDataMeasure = doseAXMeasure.bind doseChannelAX`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Measure
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Channel

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ}

/-- The `A`-marginal of the shared `(A,X)`-law is `doseAMeasure q0`. -/
lemma doseAXMeasure_map_fst {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    (hpX : IsProbabilityMeasure (doseXMeasure p0)) :
    (doseAXMeasure (d := d) p0 q0).map (fun p => p.1) = doseAMeasure q0 := by
  classical
  let mX : Measure (Fin d → ℝ) := doseXMeasure p0
  let mA : Measure ℝ := doseAMeasure q0
  haveI : SFinite mA := by
    dsimp [mA]
    unfold doseAMeasure
    infer_instance
  ext s hs
  have hpre : MeasurableSet ((fun p : ℝ × (Fin d → ℝ) => p.1) ⁻¹' s) :=
    hs.preimage measurable_fst
  have hmap : Measurable fun x : Fin d → ℝ => mA.map fun a : ℝ => (a, x) := by
    exact Measurable.map_prodMk_right (μ := mA)
  rw [Measure.map_apply measurable_fst hs]
  unfold doseAXMeasure
  change (mX.bind (fun x => mA.map fun a : ℝ => (a, x)))
      ((fun p : ℝ × (Fin d → ℝ) => p.1) ⁻¹' s) = mA s
  rw [Measure.bind_apply hpre hmap.aemeasurable]
  have hinner :
      (fun x : Fin d → ℝ =>
        (mA.map fun a : ℝ => (a, x))
          ((fun p : ℝ × (Fin d → ℝ) => p.1) ⁻¹' s)) = fun _ => mA s := by
    funext x
    rw [Measure.map_apply measurable_prodMk_right hpre]
    rfl
  rw [hinner, lintegral_const]
  simp [mX, hpX.measure_univ]

private lemma doseDataMeasure_map_A {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta).map
        (fun O : DoseObs d => O.A) = doseAMeasure q0 := by
  classical
  let mAX : Measure (ℝ × (Fin d → ℝ)) := doseAXMeasure (d := d) p0 q0
  let κ : Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta
  ext s hs
  have hsA : MeasurableSet ((fun O : DoseObs d => O.A) ⁻¹' s) :=
    hs.preimage measurable_doseObs_A
  have hsfst : MeasurableSet ((fun p : ℝ × (Fin d → ℝ) => p.1) ⁻¹' s) :=
    hs.preimage measurable_fst
  rw [Measure.map_apply measurable_doseObs_A hs]
  rw [doseDataMeasure_eq_AXbind]
  change (mAX.bind κ) ((fun O : DoseObs d => O.A) ⁻¹' s) = doseAMeasure q0 s
  rw [Measure.bind_apply hsA κ.measurable.aemeasurable]
  have hinner :
      (fun p : ℝ × (Fin d → ℝ) => κ p ((fun O : DoseObs d => O.A) ⁻¹' s)) =
        Set.indicator ((fun p : ℝ × (Fin d → ℝ) => p.1) ⁻¹' s)
          (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    rw [show κ p =
        (twoPointMean B
          (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)).map
          (fun y => DoseObs.mk y p.1 p.2) by rfl]
    rw [Measure.map_apply (measurable_doseObs_mk p.1 p.2) hsA]
    by_cases hp : p.1 ∈ s
    · have hpre :
          (fun y : ℝ => DoseObs.mk y p.1 p.2) ⁻¹'
              ((fun O : DoseObs d => O.A) ⁻¹' s) = Set.univ := by
        ext y
        simp [hp]
      rw [hpre]
      haveI : IsProbabilityMeasure
          (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)) :=
        twoPointMean_isProbabilityMeasure hB (hmu p.1 p.2)
      simp [Set.indicator, hp]
    · have hpre :
          (fun y : ℝ => DoseObs.mk y p.1 p.2) ⁻¹'
              ((fun O : DoseObs d => O.A) ⁻¹' s) = ∅ := by
        ext y
        simp [hp]
      rw [hpre]
      simp [Set.indicator, hp]
  rw [hinner, lintegral_indicator hsfst, lintegral_const]
  simp only [one_mul]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  have hmapfst := doseAXMeasure_map_fst (d := d) (p0 := p0) (q0 := q0) hpX
  rw [← hmapfst, Measure.map_apply measurable_fst hs]

private lemma doseAMeasure_singleton_null (q0 : ℝ → ℝ) (a : ℝ) :
    (doseAMeasure q0) {a} = 0 := by
  unfold doseAMeasure
  rw [withDensity_apply _ (measurableSet_singleton a)]
  have hzero : (volume.restrict (Set.Icc (0 : ℝ) 1)) {a} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton a)]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  exact setLIntegral_measure_zero {a} (fun x => ENNReal.ofReal (q0 x)) hzero

private lemma doseDataMeasure_integral_AX {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ} (F : DoseObs d → ℝ)
    (hF : Integrable F (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta))
    (hF' : Integrable
      (fun p : ℝ × (Fin d → ℝ) =>
        ∫ y, F (DoseObs.mk y p.1 p.2)
          ∂twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2))
      (doseAXMeasure (d := d) p0 q0)) :
    ∫ O, F O ∂doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta =
      ∫ p, ∫ y, F (DoseObs.mk y p.1 p.2)
          ∂twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)
        ∂doseAXMeasure (d := d) p0 q0 := by
  classical
  let mAX : Measure (ℝ × (Fin d → ℝ)) := doseAXMeasure (d := d) p0 q0
  let mu : ℝ → (Fin d → ℝ) → ℝ :=
    doseWitnessMu (d := d) alpha t0 lambda h zeta
  let κ : ℝ × (Fin d → ℝ) → Measure ℝ := fun p => twoPointMean B (mu p.1 p.2)
  let g : ℝ × (Fin d → ℝ) → ℝ → DoseObs d := fun p y => DoseObs.mk y p.1 p.2
  have hκ : Measurable κ := by
    dsimp [κ, mu, doseWitnessMu]
    fun_prop
  have hg : ∀ p, Measurable (g p) := by
    intro p
    exact measurable_doseObs_mk p.1 p.2
  have hgm : Measurable fun p => (κ p).map (g p) := by
    simpa [κ, g, mu] using
      (doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta).measurable
  have hFbind : Integrable F (mAX.bind fun p => (κ p).map (g p)) := by
    simpa [mAX, κ, g, mu, doseDataMeasure_eq_AXbind] using hF
  rw [doseDataMeasure_eq_AXbind]
  change ∫ O, F O ∂mAX.bind (fun p => (κ p).map (g p)) =
    ∫ p, ∫ y, F (g p y) ∂κ p ∂mAX
  exact Causalean.Mathlib.MeasureTheory.integral_bind_map hκ hg hgm hFbind

private lemma doseRegression_setIntegral_preimage_eq
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B M alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B) (hBM : |B| ≤ M)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B)
    (T : Set (ℝ × (Fin d → ℝ))) (hT : MeasurableSet T) :
    ∫ O in (fun O : DoseObs d => (O.A, O.X)) ⁻¹' T,
        doseWitnessMu (d := d) alpha t0 lambda h zeta O.A O.X
        ∂doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta =
      ∫ O in (fun O : DoseObs d => (O.A, O.X)) ⁻¹' T, O.Y
        ∂doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta := by
  classical
  let μ : Measure (DoseObs d) := doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta
  let mAX : Measure (ℝ × (Fin d → ℝ)) := doseAXMeasure (d := d) p0 q0
  let muF : ℝ → (Fin d → ℝ) → ℝ :=
    doseWitnessMu (d := d) alpha t0 lambda h zeta
  let pair : DoseObs d → ℝ × (Fin d → ℝ) := fun O => (O.A, O.X)
  let ind : ℝ × (Fin d → ℝ) → ℝ := T.indicator (fun _ => (1 : ℝ))
  let rhs : ℝ × (Fin d → ℝ) → ℝ := fun p => ind p * muF p.1 p.2
  haveI : IsProbabilityMeasure μ :=
    doseDataMeasure_isProbabilityMeasure (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta) hB hpX hpA hmu
  haveI : IsProbabilityMeasure mAX := doseAXMeasure_isProbabilityMeasure (d := d) hpX hpA
  have hMnonneg : 0 ≤ M := (abs_nonneg B).trans hBM
  have hpair_meas : Measurable pair := measurable_doseObs_A.prod measurable_doseObs_X
  have hind_meas : Measurable ind := measurable_const.indicator hT
  have hmu_pair_meas : Measurable fun p : ℝ × (Fin d → ℝ) => muF p.1 p.2 := by
    simpa [muF] using measurable_doseWitnessMu (d := d) alpha t0 lambda h zeta
  have hmu_obs_meas : Measurable fun O : DoseObs d => muF O.A O.X :=
    hmu_pair_meas.comp hpair_meas
  have hrhs_meas : Measurable rhs := by
    exact hind_meas.mul hmu_pair_meas
  have hrhs_int : Integrable rhs mAX := by
    refine integrable_of_measurable_ae_bounded hrhs_meas B ?_
    exact Filter.Eventually.of_forall fun p => by
      by_cases hp : p ∈ T
      · simpa [rhs, ind, Set.indicator, hp] using hmu p.1 p.2
      · have hBnonneg : 0 ≤ B := hB.le
        simpa [rhs, ind, Set.indicator, hp] using hBnonneg
  have hmuInt : Integrable (fun O : DoseObs d => ind (pair O) * muF O.A O.X) μ := by
    refine integrable_of_measurable_ae_bounded ((hind_meas.comp hpair_meas).mul hmu_obs_meas) B ?_
    exact Filter.Eventually.of_forall fun O => by
      by_cases hp : pair O ∈ T
      · simpa [ind, Set.indicator, hp] using hmu O.A O.X
      · have hBnonneg : 0 ≤ B := hB.le
        simpa [ind, Set.indicator, hp] using hBnonneg
  have hYbd : ∀ᵐ O ∂μ, |O.Y| ≤ M := by
    simpa [μ] using
      (doseDataMeasure_ae_Y_mem_Icc (d := d) (p0 := p0) (q0 := q0)
        (B := B) (M := M) (alpha := alpha) (t0 := t0)
        (lambda := lambda) (h := h) (zeta := zeta) hBM).mono
        (fun O hO => abs_le.mpr hO)
  have hYInt : Integrable (fun O : DoseObs d => ind (pair O) * O.Y) μ := by
    refine integrable_of_measurable_ae_bounded
      ((hind_meas.comp hpair_meas).mul measurable_doseObs_Y) M ?_
    filter_upwards [hYbd] with O hO
    by_cases hp : pair O ∈ T
    · simpa [ind, Set.indicator, hp] using hO
    · simpa [ind, Set.indicator, hp] using hMnonneg
  have hmuFibInt : Integrable
      (fun p : ℝ × (Fin d → ℝ) =>
        ∫ y, ind (pair (DoseObs.mk y p.1 p.2)) *
            muF (DoseObs.mk y p.1 p.2).A (DoseObs.mk y p.1 p.2).X
          ∂twoPointMean B (muF p.1 p.2)) mAX := by
    refine hrhs_int.congr ?_
    exact Filter.Eventually.of_forall fun p => by
      haveI : IsProbabilityMeasure (twoPointMean B (muF p.1 p.2)) :=
        twoPointMean_isProbabilityMeasure hB (hmu p.1 p.2)
      simp [rhs, ind, pair, muF, integral_const, measureReal_def]
  have hYFibInt : Integrable
      (fun p : ℝ × (Fin d → ℝ) =>
        ∫ y, ind (pair (DoseObs.mk y p.1 p.2)) * (DoseObs.mk y p.1 p.2).Y
          ∂twoPointMean B (muF p.1 p.2)) mAX := by
    refine hrhs_int.congr ?_
    exact Filter.Eventually.of_forall fun p => by
      symm
      change (∫ y, ind p * y ∂twoPointMean B (muF p.1 p.2)) = rhs p
      rw [integral_const_mul]
      rw [twoPointMean_mean hB (hmu p.1 p.2)]
  have hmuCollapse :
      ∫ O, ind (pair O) * muF O.A O.X ∂μ = ∫ p, rhs p ∂mAX := by
    rw [show (∫ O, ind (pair O) * muF O.A O.X ∂μ) =
        ∫ O, (fun O : DoseObs d => ind (pair O) * muF O.A O.X) O ∂μ by rfl]
    rw [doseDataMeasure_integral_AX (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta)
      (F := fun O : DoseObs d => ind (pair O) * muF O.A O.X) hmuInt hmuFibInt]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      haveI : IsProbabilityMeasure (twoPointMean B (muF p.1 p.2)) :=
        twoPointMean_isProbabilityMeasure hB (hmu p.1 p.2)
      simp [rhs, ind, pair, muF, integral_const, measureReal_def]
  have hYCollapse :
      ∫ O, ind (pair O) * O.Y ∂μ = ∫ p, rhs p ∂mAX := by
    rw [show (∫ O, ind (pair O) * O.Y ∂μ) =
        ∫ O, (fun O : DoseObs d => ind (pair O) * O.Y) O ∂μ by rfl]
    rw [doseDataMeasure_integral_AX (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta)
      (F := fun O : DoseObs d => ind (pair O) * O.Y) hYInt hYFibInt]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      change (∫ y, ind p * y ∂twoPointMean B (muF p.1 p.2)) = rhs p
      rw [integral_const_mul]
      rw [twoPointMean_mean hB (hmu p.1 p.2)]
  have hpre_meas : MeasurableSet (pair ⁻¹' T) := hT.preimage hpair_meas
  calc
    ∫ O in pair ⁻¹' T, muF O.A O.X ∂μ
        = ∫ O, ind (pair O) * muF O.A O.X ∂μ := by
          rw [← integral_indicator hpre_meas]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun O => by
            by_cases hp : pair O ∈ T <;> simp [ind, Set.indicator, hp]
    _ = ∫ p, rhs p ∂mAX := hmuCollapse
    _ = ∫ O, ind (pair O) * O.Y ∂μ := hYCollapse.symm
    _ = ∫ O in pair ⁻¹' T, O.Y ∂μ := by
          rw [← integral_indicator hpre_meas]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun O => by
            by_cases hp : pair O ∈ T <;> simp [ind, Set.indicator, hp]

/-- The realized-treatment level is a.s. not equal to any fixed level `a`: the
treatment has a Lebesgue density `q0`, so `{O | O.A = a}` is `doseDataMeasure`-null. -/
lemma doseDataMeasure_A_singleton_null {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ} (a : ℝ)
    (hB : 0 < B)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta) {O | O.A = a} = 0 := by
  classical
  have _hpA_univ : (doseAMeasure q0) Set.univ = 1 := hpA.measure_univ
  let μ : Measure (DoseObs d) := doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta
  have hmapA := doseDataMeasure_map_A (d := d) (p0 := p0) (q0 := q0)
    (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
    (h := h) (zeta := zeta) hB hpX hmu
  have hpre :
      (fun O : DoseObs d => O.A) ⁻¹' ({a} : Set ℝ) = {O | O.A = a} := by
    ext O
    simp
  rw [← hpre]
  rw [← Measure.map_apply measurable_doseObs_A (measurableSet_singleton a)]
  rw [hmapA]
  exact doseAMeasure_singleton_null q0 a

-- @node: dose-witness-mu-regression
/-- **Semantic tie 1 (genuine regression).** Under the genuine joint law, the
conditional mean of `Y` given `(A,X)` equals `μ_ζ(A,X)`, because the outcome channel
`twoPointMean B (μ_ζ(a,x))` has mean exactly `μ_ζ(a,x)`. This forbids the Dirac/
decoupled laundering: `μ` is the real regression of the data law. -/
lemma doseWitness_muReg {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B M alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B) (hBM : |B| ≤ M)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    MuIsRegression (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta) := by
  classical
  let μ : Measure (DoseObs d) := doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta
  let g : DoseObs d → ℝ :=
    fun O => doseWitnessMu (d := d) alpha t0 lambda h zeta O.A O.X
  let mAXobs : MeasurableSpace (DoseObs d) :=
    MeasurableSpace.comap (fun O : DoseObs d => (O.A, O.X)) inferInstance
  haveI : IsProbabilityMeasure μ :=
    doseDataMeasure_isProbabilityMeasure (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta) hB hpX hpA hmu
  have hmAX : mAXobs ≤ instMeasurableSpaceDoseObs := by
    dsimp [mAXobs]
    exact (measurable_doseObs_A.prodMk measurable_doseObs_X).comap_le
  have hYbd : ∀ᵐ O ∂μ, |O.Y| ≤ M := by
    simpa [μ] using
      (doseDataMeasure_ae_Y_mem_Icc (d := d) (p0 := p0) (q0 := q0)
        (B := B) (M := M) (alpha := alpha) (t0 := t0)
        (lambda := lambda) (h := h) (zeta := zeta) hBM).mono
        (fun O hO => abs_le.mpr hO)
  have hYint : Integrable (fun O : DoseObs d => O.Y) μ := by
    exact @integrable_of_measurable_ae_bounded (DoseObs d) instMeasurableSpaceDoseObs μ
      inferInstance (fun O : DoseObs d => O.Y) measurable_doseObs_Y M hYbd
  have hg_meas_default :
      @Measurable (DoseObs d) ℝ instMeasurableSpaceDoseObs inferInstance g := by
    dsimp [g]
    exact (measurable_doseWitnessMu (d := d) alpha t0 lambda h zeta).comp
      (measurable_doseObs_A.prodMk measurable_doseObs_X)
  have hgInt : Integrable g μ := by
    refine @integrable_of_measurable_ae_bounded (DoseObs d) instMeasurableSpaceDoseObs μ
      inferInstance g hg_meas_default B ?_
    exact Filter.Eventually.of_forall fun O => hmu O.A O.X
  have hg_int_finite :
      ∀ s : Set (DoseObs d), MeasurableSet[mAXobs] s → μ s < ∞ → IntegrableOn g s μ := by
    intro s _hs _hfin
    exact hgInt.integrableOn
  have hg_rel_meas : Measurable[mAXobs] g := by
    have hpair : Measurable[mAXobs] (fun O : DoseObs d => (O.A, O.X)) :=
      Measurable.of_comap_le le_rfl
    have hr : Measurable fun p : ℝ × (Fin d → ℝ) =>
        doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2 :=
      measurable_doseWitnessMu (d := d) alpha t0 lambda h zeta
    exact hr.comp hpair
  have hgm : AEStronglyMeasurable[mAXobs] g μ := hg_rel_meas.aestronglyMeasurable
  have hg_eq :
      ∀ s : Set (DoseObs d), MeasurableSet[mAXobs] s → μ s < ∞ →
        ∫ x in s, g x ∂μ = ∫ x in s, x.Y ∂μ := by
    intro s hs _hfin
    rcases (MeasurableSpace.measurableSet_comap.mp hs) with ⟨T, hT, hTs⟩
    have hpre := doseRegression_setIntegral_preimage_eq (d := d) (p0 := p0) (q0 := q0)
      (B := B) (M := M) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta) hB hBM hpX hpA hmu T hT
    rw [← hTs]
    simpa [μ, g] using hpre
  unfold MuIsRegression doseWitness
  change μ[(fun O : DoseObs d => O.Y) | mAXobs] =ᵐ[μ] g
  exact (ae_eq_condExp_of_forall_setIntegral_eq hmAX hYint hg_int_finite hg_eq hgm).symm

-- @node: dose-witness-ignorability
/-- **Semantic tie 2 (ignorability).** The potential outcome `Y(a)` equals the
regression mean `μ_ζ(a,X)` almost surely (the realized `A` hits the fixed level `a`
only on a `q0`-null set), so `Y(a)` is `X`-measurable and `Y(a) ⟂ A | X`. -/
lemma doseWitness_ignorability {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    NoUnmeasuredConfounding (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta) := by
  classical
  intro a _ha
  have hpot_meas :
      Measurable (dosePotential (d := d) alpha t0 lambda h zeta a) := by
    unfold dosePotential
    refine Measurable.ite
      (measurableSet_eq_fun (measurable_doseObs_A (d := d)) measurable_const)
      measurable_doseObs_Y ?_
    unfold doseWitnessMu
    fun_prop
  refine ⟨hpot_meas, ?_⟩
  intro f hf hfb
  rcases hfb with ⟨Mf, hMf⟩
  let μ : Measure (DoseObs d) := doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta
  let u : DoseObs d → ℝ :=
    fun O => f (doseWitnessMu (d := d) alpha t0 lambda h zeta a O.X)
  haveI : IsProbabilityMeasure μ := by
    let mAX : Measure (ℝ × (Fin d → ℝ)) := doseAXMeasure (d := d) p0 q0
    let κ : Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) :=
      doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta
    haveI : IsProbabilityMeasure mAX := doseAXMeasure_isProbabilityMeasure (d := d) hpX hpA
    haveI : IsMarkovKernel κ := instIsMarkovDoseChannelAX (d := d) hB hmu
    dsimp [μ]
    rw [doseDataMeasure_eq_AXbind]
    change IsProbabilityMeasure (mAX.bind κ)
    exact isProbabilityMeasure_bind κ.measurable.aemeasurable
      (Filter.Eventually.of_forall fun p => by infer_instance)
  let mAXobs : MeasurableSpace (DoseObs d) :=
    MeasurableSpace.comap (fun O : DoseObs d => (O.A, O.X)) inferInstance
  let mXobs : MeasurableSpace (DoseObs d) :=
    MeasurableSpace.comap (fun O : DoseObs d => O.X) inferInstance
  have hmAX : mAXobs ≤ instMeasurableSpaceDoseObs := by
    dsimp [mAXobs]
    exact (measurable_doseObs_A.prod measurable_doseObs_X).comap_le
  have hmX : mXobs ≤ instMeasurableSpaceDoseObs := by
    dsimp [mXobs]
    exact measurable_doseObs_X.comap_le
  have hu_meas_X : Measurable[mXobs] u := by
    have hX : Measurable[mXobs] (fun O : DoseObs d => O.X) := Measurable.of_comap_le le_rfl
    have hr : Measurable fun x : Fin d → ℝ =>
        f (doseWitnessMu (d := d) alpha t0 lambda h zeta a x) := by
      unfold doseWitnessMu
      fun_prop
    exact hr.comp hX
  have hu_meas_AX : Measurable[mAXobs] u := by
    have hpair : Measurable[mAXobs] (fun O : DoseObs d => (O.A, O.X)) :=
      Measurable.of_comap_le le_rfl
    have hr : Measurable fun p : ℝ × (Fin d → ℝ) =>
        f (doseWitnessMu (d := d) alpha t0 lambda h zeta a p.2) := by
      unfold doseWitnessMu
      fun_prop
    exact hr.comp hpair
  have hu_meas_default :
      @Measurable (DoseObs d) ℝ instMeasurableSpaceDoseObs inferInstance u := by
    have hmu_a :
        @Measurable (DoseObs d) ℝ instMeasurableSpaceDoseObs inferInstance
          (fun O : DoseObs d =>
            doseWitnessMu (d := d) alpha t0 lambda h zeta a O.X) := by
      unfold doseWitnessMu
      fun_prop
    exact hf.comp hmu_a
  have hu_int : Integrable u μ := by
    exact @integrable_of_measurable_ae_bounded (DoseObs d) instMeasurableSpaceDoseObs μ
      inferInstance u hu_meas_default (max Mf 0)
      (Filter.Eventually.of_forall fun O => (hMf _).trans (le_max_left Mf 0))
  have huAX : AEStronglyMeasurable[mAXobs] u μ := hu_meas_AX.aestronglyMeasurable
  have huX : AEStronglyMeasurable[mXobs] u μ := hu_meas_X.aestronglyMeasurable
  have hnull := doseDataMeasure_A_singleton_null (d := d) (p0 := p0) (q0 := q0)
    (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
    (h := h) (zeta := zeta) a hB hpX hpA hmu
  have hAne : ∀ᵐ O ∂μ, O.A ≠ a := by
    rw [ae_iff]
    simpa [μ] using hnull
  have hpot_eq :
      (fun O : DoseObs d =>
          f ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).pot a O))
        =ᵐ[μ] u := by
    filter_upwards [hAne] with O hO
    simp [doseWitness, dosePotential, u, hO]
  have hpot_int : Integrable
      (fun O : DoseObs d =>
        f ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).pot a O)) μ := by
    exact hu_int.congr hpot_eq.symm
  refine ⟨hpot_int, ?_⟩
  change
    μ[(fun O : DoseObs d =>
        f ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).pot a O)) | mAXobs]
      =ᵐ[μ]
    μ[(fun O : DoseObs d =>
        f ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).pot a O)) | mXobs]
  calc
    μ[(fun O : DoseObs d =>
        f ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).pot a O)) | mAXobs]
        =ᵐ[μ] μ[u | mAXobs] := condExp_congr_ae hpot_eq
    _ =ᵐ[μ] u := condExp_of_aestronglyMeasurable' hmAX huAX hu_int
    _ =ᵐ[μ] μ[u | mXobs] := (condExp_of_aestronglyMeasurable' hmX huX hu_int).symm
    _ =ᵐ[μ] μ[(fun O : DoseObs d =>
        f ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).pot a O)) | mXobs] :=
      (condExp_congr_ae hpot_eq).symm

end CausalSmith.Stat.DoseResponseMinimax
