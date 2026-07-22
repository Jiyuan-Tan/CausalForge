/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: the crux all-β two-point lower construction

The explicit least-favourable two-point construction proving the all-β oracle lower
floor (`lem:oracle-dose-regression-lower-all-beta`). GENUINE construction: the two
witnesses share the slack baseline `(p_0, q_0)`-marginals and perturb ONLY the
treatment regression by a local Hölder-`α` bump `μ_ζ(a,x) = ζ λ h^α ψ((a−t_0)/h)`, so
the conditional mean of `Y` given `(A,X)` IS `μ_ζ` (`MuIsRegression`) and the n-fold KL
is genuinely bump-driven (`Θ(n h^{2α+1})`), NOT zero. The bound follows from the Le Cam
two-point MSE reduction at the `Θ(1)` KL budget `K = 16 λ² (M−η_0)/B²` with
`h_n = n^{-1/(2α+1)}`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Membership
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.KL
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.BumpHolder
import Causalean.Stat.Minimax.MinimaxRisk
import Causalean.Stat.Minimax.LeCamTwoPoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Pi

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable {d : ℕ}

/-- Uniform bound on the identifying functional over the model class:
`|θ_P(t_0)| ≤ M · M · vol([0,1]^d)`. Used for `BddAbove` of the worst-case risk. -/
lemma thetaFunctional_abs_le {P : DoseLaw d}
    {alpha beta s M c0 eps0 t0 : ℝ} (hM : 0 ≤ M) (heps : 0 ≤ eps0)
    (hP : HolderDoseClass d alpha beta s M c0 eps0 t0 P) :
    |thetaFunctional P t0| ≤ M * M * (volume.real (cube d)) := by
  rw [thetaFunctional]
  have hbound : ∀ x ∈ cube d, ‖P.mu t0 x * P.px x‖ ≤ M * M := by
    intro x hx
    have ht0win : t0 ∈ doseWindow t0 eps0 := center_mem_doseWindow heps
    have hmu : |P.mu t0 x| ≤ M := by
      have h := (hP.muT x hx).2.1 0 (Nat.zero_le _) t0 ht0win
      simpa using h
    have hpx : |P.px x| ≤ M := by
      have h := hP.pxH.1.2.1 0 (Nat.zero_le _) x hx
      simpa [Real.norm_eq_abs] using h
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hmu hpx (abs_nonneg _) hM
  simpa [Real.norm_eq_abs, mul_assoc] using
    (norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cube d)
      (f := fun x => P.mu t0 x * P.px x) (C := M * M)
      (volume_cube_lt_top d) hbound)

-- @node: minimaxRisk-two-point-lower
/-- The two-point Le Cam reduction in minimax form: two class members with bounded KL
between their `n`-fold product laws force the pointwise minimax risk to be at least
`c_K` times their squared target separation. -/
lemma minimaxRisk_two_point_lower {alpha beta s M c0 eps0 t0 : ℝ}
    (hM : 0 < M) (heps : 0 ≤ eps0) (n : ℕ)
    (P0 P1 : DoseLaw d)
    (h0 : HolderDoseClass d alpha beta s M c0 eps0 t0 P0)
    (h1 : HolderDoseClass d alpha beta s M c0 eps0 t0 P1)
    (K cK : ℝ) (hcK : 0 < cK)
    (hbody : ∀ {S : Type*} [MeasurableSpace S]
        (Q0 Q1 : Measure S) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
        (theta0 theta1 : ℝ),
        InformationTheory.klDiv Q0 Q1 ≤ ENNReal.ofReal K →
        ∀ T : S → ℝ, Measurable T →
          Integrable (fun s => (T s - theta0) ^ 2) Q0 →
          Integrable (fun s => (T s - theta1) ^ 2) Q1 →
          cK * (theta1 - theta0) ^ 2
            ≤ max (∫ s, (T s - theta0) ^ 2 ∂Q0) (∫ s, (T s - theta1) ^ 2 ∂Q1))
    (hKL : InformationTheory.klDiv
        (Measure.pi fun _ : Fin n => P0.dataMeasure)
        (Measure.pi fun _ : Fin n => P1.dataMeasure)
        ≤ ENNReal.ofReal K) :
    cK * (thetaFunctional P1 t0 - thetaFunctional P0 t0) ^ 2
      ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0 := by
  have _ : 0 < cK := hcK
  let C : DoseLaw d → Prop := HolderDoseClass d alpha beta s M c0 eps0 t0
  let Est := {est : (Fin n → DoseObs d) → ℝ //
      Measurable est ∧ ∀ s, est s ∈ Set.Icc (-M) M}
  have hMnonneg : 0 ≤ M := hM.le
  letI : Nonempty Est := ⟨⟨fun _ => 0, measurable_const, fun _ => by
    exact ⟨by linarith, by linarith⟩⟩⟩
  rw [minimaxRisk]
  change cK * (thetaFunctional P1 t0 - thetaFunctional P0 t0) ^ 2 ≤
    ⨅ est : Est,
      ⨆ P : {P : DoseLaw d // C P},
        ∫ s, (est.1 s - thetaFunctional P.1 t0) ^ 2 ∂
          (Measure.pi fun _ : Fin n => P.1.dataMeasure)
  refine le_ciInf ?_
  intro est
  let T : (Fin n → DoseObs d) → ℝ := est.1
  have hT : Measurable T := est.2.1
  have hTbd : ∀ s, T s ∈ Set.Icc (-M) M := est.2.2
  let θ0 : ℝ := thetaFunctional P0 t0
  let θ1 : ℝ := thetaFunctional P1 t0
  let Q0 : Measure (Fin n → DoseObs d) := Measure.pi fun _ : Fin n => P0.dataMeasure
  let Q1 : Measure (Fin n → DoseObs d) := Measure.pi fun _ : Fin n => P1.dataMeasure
  have hprob0 : IsProbabilityMeasure P0.dataMeasure := h0.iid.1
  have hprob1 : IsProbabilityMeasure P1.dataMeasure := h1.iid.1
  letI : IsProbabilityMeasure P0.dataMeasure := hprob0
  letI : IsProbabilityMeasure P1.dataMeasure := hprob1
  letI : IsProbabilityMeasure Q0 := by dsimp [Q0]; infer_instance
  letI : IsProbabilityMeasure Q1 := by dsimp [Q1]; infer_instance
  have hInt0 : Integrable (fun s => (T s - θ0) ^ 2) Q0 := by
    exact Causalean.Stat.mse_integrable_of_estimator_bound Q0 T hT hMnonneg hTbd
  have hInt1 : Integrable (fun s => (T s - θ1) ^ 2) Q1 := by
    exact Causalean.Stat.mse_integrable_of_estimator_bound Q1 T hT hMnonneg hTbd
  have hLC :
      cK * (θ1 - θ0) ^ 2
        ≤ max (∫ s, (T s - θ0) ^ 2 ∂Q0) (∫ s, (T s - θ1) ^ 2 ∂Q1) := by
    have hKLQ : InformationTheory.klDiv Q0 Q1 ≤ ENNReal.ofReal K := by
      simpa [Q0, Q1] using hKL
    let e : (Fin n → DoseObs d) ≃ᵐ ULift (Fin n → DoseObs d) :=
      (MeasurableEquiv.ulift).symm
    let Q0u : Measure (ULift (Fin n → DoseObs d)) := Measure.map e Q0
    let Q1u : Measure (ULift (Fin n → DoseObs d)) := Measure.map e Q1
    let Tu : ULift (Fin n → DoseObs d) → ℝ := fun s => T s.down
    letI : IsProbabilityMeasure Q0u := by
      dsimp [Q0u]
      exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable
    letI : IsProbabilityMeasure Q1u := by
      dsimp [Q1u]
      exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable
    have hKLu : InformationTheory.klDiv Q0u Q1u ≤ ENNReal.ofReal K := by
      calc
        InformationTheory.klDiv Q0u Q1u = InformationTheory.klDiv Q0 Q1 := by
          simpa [Q0u, Q1u, e] using klDiv_map_measurableEquiv e Q0 Q1
        _ ≤ ENNReal.ofReal K := hKLQ
    have hTu : Measurable Tu := by
      exact hT.comp measurable_down
    have hTubd : ∀ s, Tu s ∈ Set.Icc (-M) M := fun s => hTbd s.down
    have hInt0u : Integrable (fun s => (Tu s - θ0) ^ 2) Q0u := by
      exact Causalean.Stat.mse_integrable_of_estimator_bound Q0u Tu hTu hMnonneg hTubd
    have hInt1u : Integrable (fun s => (Tu s - θ1) ^ 2) Q1u := by
      exact Causalean.Stat.mse_integrable_of_estimator_bound Q1u Tu hTu hMnonneg hTubd
    have hLCu :
        cK * (θ1 - θ0) ^ 2
          ≤ max (∫ s, (Tu s - θ0) ^ 2 ∂Q0u) (∫ s, (Tu s - θ1) ^ 2 ∂Q1u) := by
      exact hbody Q0u Q1u θ0 θ1 hKLu Tu hTu hInt0u hInt1u
    have hIntEq0 :
        (∫ s, (Tu s - θ0) ^ 2 ∂Q0u) =
          ∫ s, (T s - θ0) ^ 2 ∂Q0 := by
      simpa [Q0u, Tu, e] using
        MeasureTheory.integral_map_equiv e (fun s => (Tu s - θ0) ^ 2) (μ := Q0)
    have hIntEq1 :
        (∫ s, (Tu s - θ1) ^ 2 ∂Q1u) =
          ∫ s, (T s - θ1) ^ 2 ∂Q1 := by
      simpa [Q1u, Tu, e] using
        MeasureTheory.integral_map_equiv e (fun s => (Tu s - θ1) ^ 2) (μ := Q1)
    simpa [hIntEq0, hIntEq1] using hLCu
  let A : ℝ := M + M * M * volume.real (cube d)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hbdd : BddAbove (Set.range (fun P : {P : DoseLaw d // C P} =>
      ∫ s, (T s - thetaFunctional P.1 t0) ^ 2 ∂
        (Measure.pi fun _ : Fin n => P.1.dataMeasure))) := by
    refine ⟨A ^ 2, ?_⟩
    rintro y ⟨P, rfl⟩
    let Q : Measure (Fin n → DoseObs d) := Measure.pi fun _ : Fin n => P.1.dataMeasure
    let θ : ℝ := thetaFunctional P.1 t0
    have hprobP : IsProbabilityMeasure P.1.dataMeasure := P.2.iid.1
    letI : IsProbabilityMeasure P.1.dataMeasure := hprobP
    letI : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
    have hInt : Integrable (fun s => (T s - θ) ^ 2) Q := by
      exact Causalean.Stat.mse_integrable_of_estimator_bound Q T hT hMnonneg hTbd
    have hConst : Integrable (fun _ : Fin n → DoseObs d => A ^ 2) Q := integrable_const _
    have hpoint : (fun s => (T s - θ) ^ 2) ≤ fun _ : Fin n → DoseObs d => A ^ 2 := by
      intro sample
      have hTabs : |T sample| ≤ M := abs_le.mpr (hTbd sample)
      have htheta : |θ| ≤ M * M * volume.real (cube d) := by
        exact thetaFunctional_abs_le hMnonneg heps P.2
      have hdiff : |T sample - θ| ≤ A := by
        dsimp [A]
        exact (abs_sub (T sample) θ).trans (add_le_add hTabs htheta)
      nlinarith [hdiff, abs_nonneg (T sample - θ), hA_nonneg, sq_abs (T sample - θ)]
    have hle := MeasureTheory.integral_mono hInt hConst hpoint
    have hconsteq : (∫ _ : Fin n → DoseObs d, A ^ 2 ∂Q) = A ^ 2 := by
      simp
    exact hle.trans_eq hconsteq
  have hsup0 :
      (∫ s, (T s - thetaFunctional P0 t0) ^ 2 ∂
        (Measure.pi fun _ : Fin n => P0.dataMeasure)) ≤
      ⨆ P : {P : DoseLaw d // C P},
        ∫ s, (T s - thetaFunctional P.1 t0) ^ 2 ∂
          (Measure.pi fun _ : Fin n => P.1.dataMeasure) := by
    simpa [C] using
      le_ciSup hbdd (⟨P0, h0⟩ : {P : DoseLaw d // C P})
  have hsup1 :
      (∫ s, (T s - thetaFunctional P1 t0) ^ 2 ∂
        (Measure.pi fun _ : Fin n => P1.dataMeasure)) ≤
      ⨆ P : {P : DoseLaw d // C P},
        ∫ s, (T s - thetaFunctional P.1 t0) ^ 2 ∂
          (Measure.pi fun _ : Fin n => P.1.dataMeasure) := by
    simpa [C] using
      le_ciSup hbdd (⟨P1, h1⟩ : {P : DoseLaw d // C P})
  have hmax :
      max (∫ s, (T s - θ0) ^ 2 ∂Q0) (∫ s, (T s - θ1) ^ 2 ∂Q1) ≤
      ⨆ P : {P : DoseLaw d // C P},
        ∫ s, (T s - thetaFunctional P.1 t0) ^ 2 ∂
          (Measure.pi fun _ : Fin n => P.1.dataMeasure) := by
    refine max_le ?_ ?_
    · simpa [Q0, θ0, T] using hsup0
    · simpa [Q1, θ1, T] using hsup1
  exact (by simpa [θ0, θ1] using hLC.trans hmax)

-- @node: lem:oracle-dose-regression-lower-all-beta
/-- The all-β oracle lower floor. Assume the strict-slack baseline. For every
`β > 0` there is `c_or > 0`, depending only on the fixed model radii and the slack
baseline (not on `n`), such that for all sufficiently large `n`,
`R_n(P_{α,β,s}(M,c_0,ε_0,t_0), t_0) ≥ c_or n^{-2α/(2α+1)}`. The construction
perturbs only the treatment regression and leaves the treatment density fixed, so
the bound is independent of whether `β ≥ α`. -/
lemma oracle_dose_regression_lower_all_beta {d : ℕ}
    (alpha beta s M c0 eps0 t0 : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hs : 0 < s)
    (hreg : RegimeConstants alpha beta s M c0 eps0 t0)
    (hslack : BaselineSubmodelSlack d beta s M c0 eps0 t0) :
    ∃ cor : ℝ, 0 < cor ∧ ∀ᶠ n : ℕ in Filter.atTop,
      cor * (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
        ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0 := by
  classical
  have _ : 0 < beta := hbeta
  have _ : 0 < s := hs
  rcases hslack with
    ⟨p0, q0, eta0, B0, heta0, hB0, hB0M, hp0nn, hq0nn, hp0int, hq0int,
      hp0H, hp0bd, hq0H, hq0pos⟩
  have hregC := hreg
  rcases hreg with ⟨hα, hβ, hsp, hMpos, hc0, ht0, heps, hinterior⟩
  let B : ℝ := M / 2
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hBM : B ≤ M := by dsimp [B]; linarith
  obtain ⟨lambda, hlam_pos, hlam_le4, hMuHolder⟩ :=
    doseBump_holder_gate alpha M t0 eps0 hα hMpos
  have hlam_leB2 : lambda ≤ B / 2 := by
    have hB2 : B / 2 = M / 4 := by
      dsimp [B]
      ring
    simpa [hB2] using hlam_le4
  have hpX : IsProbabilityMeasure (doseXMeasure (d := d) p0) :=
    doseXMeasure_isProbabilityMeasure (d := d) (p0 := p0) hp0nn hp0int
  have hpA : IsProbabilityMeasure (doseAMeasure q0) :=
    doseAMeasure_isProbabilityMeasure (q0 := q0) hq0nn hq0int
  let K : ℝ := 16 * lambda ^ 2 * (M - eta0) / B ^ 2
  obtain ⟨cK, hcK, hbody_raw⟩ := Causalean.Stat.Minimax.le_cam_two_point_mse K
  let hbody : ∀ {S : Type} [MeasurableSpace S]
      (Q0 Q1 : Measure S) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
      (theta0 theta1 : ℝ),
      InformationTheory.klDiv Q0 Q1 ≤ ENNReal.ofReal K →
      ∀ T : S → ℝ, Measurable T →
        Integrable (fun s => (T s - theta0) ^ 2) Q0 →
        Integrable (fun s => (T s - theta1) ^ 2) Q1 →
        cK * (theta1 - theta0) ^ 2
          ≤ max (∫ s, (T s - theta0) ^ 2 ∂Q0) (∫ s, (T s - theta1) ^ 2 ∂Q1) :=
    hbody_raw
  refine ⟨4 * cK * lambda ^ 2, ?_, ?_⟩
  · positivity
  have hdenpos : 0 < 2 * alpha + 1 := by nlinarith
  have hdenne : 2 * alpha + 1 ≠ 0 := ne_of_gt hdenpos
  have hexp_pos : 0 < 1 / (2 * alpha + 1) := by positivity
  have hh_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / (2 * alpha + 1))))
      atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop hexp_pos).comp tendsto_natCast_atTop_atTop
  filter_upwards [hh_tendsto.eventually_le_const zero_lt_one,
      hh_tendsto.eventually_le_const heps.1,
      Filter.eventually_ge_atTop 1] with n hh1 hheps hn1
  let h : ℝ := (n : ℝ) ^ (-(1 / (2 * alpha + 1)))
  have hhpos : 0 < h := by
    dsimp [h]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    exact Real.rpow_pos_of_pos hnpos _
  have hhle : h ≤ 1 := by simpa [h] using hh1
  have hhe : h ≤ eps0 := by simpa [h] using hheps
  let P0 : DoseLaw d := doseWitness (d := d) p0 q0 B alpha t0 lambda h (-1)
  let P1 : DoseLaw d := doseWitness (d := d) p0 q0 B alpha t0 lambda h 1
  have hmu_abs_le_B2 : ∀ {zeta : ℝ}, (zeta = -1 ∨ zeta = 1) →
      ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B / 2 := by
    intro zeta hzeta a x
    have hzeta_abs : |zeta| ≤ 1 := by
      rcases hzeta with rfl | rfl <;> norm_num
    have hhp_nonneg : 0 ≤ h ^ alpha := Real.rpow_nonneg hhpos.le alpha
    have hhp_le : h ^ alpha ≤ 1 := Real.rpow_le_one hhpos.le hhle halpha.le
    have hbump_abs := doseBump_abs_le_one ((a - t0) / h)
    calc
      |doseWitnessMu (d := d) alpha t0 lambda h zeta a x|
          = |zeta| * lambda * h ^ alpha * |doseBump ((a - t0) / h)| := by
            rw [doseWitnessMu, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlam_pos.le,
              abs_of_nonneg hhp_nonneg]
      _ ≤ 1 * lambda * 1 * 1 := by
            gcongr
      _ = lambda := by ring
      _ ≤ B / 2 := hlam_leB2
  have hmu_abs_le_B : ∀ {zeta : ℝ}, (zeta = -1 ∨ zeta = 1) →
      ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B := by
    intro zeta hzeta a x
    exact (hmu_abs_le_B2 hzeta a x).trans (by linarith [hBpos])
  have hmem0 : HolderDoseClass d alpha beta s M c0 eps0 t0 P0 := by
    dsimp [P0]
    exact doseWitness_mem_class (d := d) (p0 := p0) (q0 := q0)
      (alpha := alpha) (beta := beta) (s := s) (M := M) (c0 := c0)
      (eps0 := eps0) (t0 := t0) (eta0 := eta0) (B := B)
      (lambda := lambda) (h := h) (zeta := -1)
      hregC heta0 hBpos hBM hp0nn hp0int hp0H hp0bd hq0nn hq0int hq0H hq0pos
      (hmu_abs_le_B (Or.inl rfl)) (hMuHolder (Or.inl rfl) hhpos hhle) (Or.inl rfl)
      hhpos hhle
  have hmem1 : HolderDoseClass d alpha beta s M c0 eps0 t0 P1 := by
    dsimp [P1]
    exact doseWitness_mem_class (d := d) (p0 := p0) (q0 := q0)
      (alpha := alpha) (beta := beta) (s := s) (M := M) (c0 := c0)
      (eps0 := eps0) (t0 := t0) (eta0 := eta0) (B := B)
      (lambda := lambda) (h := h) (zeta := 1)
      hregC heta0 hBpos hBM hp0nn hp0int hp0H hp0bd hq0nn hq0int hq0H hq0pos
      (hmu_abs_le_B (Or.inr rfl)) (hMuHolder (Or.inr rfl) hhpos hhle) (Or.inr rfl)
      hhpos hhle
  have hq0bd : ∀ a ∈ doseWindow t0 eps0, q0 a ≤ M - eta0 := by
    intro a ha
    have h := hq0H.2.1 0 (Nat.zero_le _) a ha
    exact (le_abs_self (q0 a)).trans (by simpa using h)
  have hKL0 := doseWitness_kl_nfold_le (d := d) (p0 := p0) (q0 := q0)
    (B := B) (M := M) (alpha := alpha) (lambda := lambda) (eta0 := eta0)
    (t0 := t0) (eps0 := eps0) (h := h) n hBpos halpha hhpos hhle hhe hinterior
    hpX hpA hp0int hlam_pos.le hlam_leB2
    (hmu_abs_le_B2 (Or.inr rfl)) (hmu_abs_le_B2 (Or.inl rfl)) hq0nn hq0bd
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hpow_budget : h ^ (2 * alpha + 1) = (n : ℝ)⁻¹ := by
    dsimp [h]
    rw [← Real.rpow_mul hnpos.le]
    have hmul : (-(1 / (2 * alpha + 1))) * (2 * alpha + 1) = -1 := by
      field_simp [hdenne]
    rw [hmul, Real.rpow_neg_one]
  have hn_mul_hpow : (n : ℝ) * h ^ (2 * alpha + 1) = 1 := by
    rw [hpow_budget]
    exact mul_inv_cancel₀ (ne_of_gt hnpos)
  have hbudget_eq :
      (n : ℝ) * (16 * lambda ^ 2 * (M - eta0) / B ^ 2 * h ^ (2 * alpha + 1)) = K := by
    dsimp [K]
    calc
      (n : ℝ) * (16 * lambda ^ 2 * (M - eta0) / B ^ 2 * h ^ (2 * alpha + 1))
          = (16 * lambda ^ 2 * (M - eta0) / B ^ 2) *
              ((n : ℝ) * h ^ (2 * alpha + 1)) := by ring
      _ = (16 * lambda ^ 2 * (M - eta0) / B ^ 2) * 1 := by rw [hn_mul_hpow]
      _ = 16 * lambda ^ 2 * (M - eta0) / B ^ 2 := by ring
  have hKL : InformationTheory.klDiv
      (Measure.pi fun _ : Fin n => P0.dataMeasure)
      (Measure.pi fun _ : Fin n => P1.dataMeasure)
      ≤ ENNReal.ofReal K := by
    dsimp [P0, P1]
    simpa [hbudget_eq] using hKL0
  have hlow := minimaxRisk_two_point_lower (d := d) (alpha := alpha) (beta := beta)
    (s := s) (M := M) (c0 := c0) (eps0 := eps0) (t0 := t0)
    hMpos heps.1.le n P0 P1 hmem0 hmem1 K cK hcK hbody hKL
  have hsep : thetaFunctional P1 t0 - thetaFunctional P0 t0 = 2 * lambda * h ^ alpha := by
    dsimp [P0, P1]
    exact doseWitness_theta_sep (d := d) p0 q0 B alpha t0 lambda h hp0int
  have hrate : h ^ (2 * alpha) = (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))) := by
    dsimp [h]
    rw [← Real.rpow_mul hnpos.le]
    congr 1
    field_simp [hdenne]
  have hsq_sep : cK * (2 * lambda * h ^ alpha) ^ 2 =
      (4 * cK * lambda ^ 2) * h ^ (2 * alpha) := by
    have hpowsq : (h ^ alpha) ^ 2 = h ^ (2 * alpha) := by
      rw [sq, ← Real.rpow_add hhpos]
      congr 1
      ring
    calc
      cK * (2 * lambda * h ^ alpha) ^ 2
          = cK * ((2 * lambda) ^ 2 * (h ^ alpha) ^ 2) := by ring
      _ = (4 * cK * lambda ^ 2) * h ^ (2 * alpha) := by
        rw [hpowsq]
        ring
  calc
    (4 * cK * lambda ^ 2) * (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
        = cK * (thetaFunctional P1 t0 - thetaFunctional P0 t0) ^ 2 := by
          rw [hsep, hsq_sep, hrate]
    _ ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0 := hlow

end CausalSmith.Stat.DoseResponseMinimax
