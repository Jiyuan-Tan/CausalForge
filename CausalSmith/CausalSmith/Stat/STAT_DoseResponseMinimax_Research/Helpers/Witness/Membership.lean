/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: witness model-class membership

Bundles the genuine witness's membership in the anisotropic Hölder dose-response
class `HolderDoseClass`, assembling all fourteen member atoms (the three semantic ties,
consistency, ignorability, boundedness, the Hölder atoms, positivity, interior, iid)
from the leaf lemmas + the strict-slack baseline + the bump-Hölder gate.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Regression
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.PiCond
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Theta
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.HolderAux
import Mathlib.Probability.HasLawExists

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ}

/-- Generic existence of an i.i.d. sample with a prescribed probability law, via the
Mathlib infinite-product construction `ProbabilityTheory.exists_iid`. Discharges the
i.i.d.-sampling existential of `IidSampling`. -/
lemma iidSample_nonempty {X : Type} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
      Nonempty (@Causalean.Stat.IIDSample Ω X mΩ _ μ P) := by
  obtain ⟨Ω, mΩ, μ, Z, hmeas, hlaw, hindep, hprob⟩ :=
    ProbabilityTheory.exists_iid ℕ P
  refine ⟨Ω, mΩ, μ, ⟨{ Z := Z, meas := hmeas, indep := hindep, identDist := ?_, law := ?_ }⟩⟩
  · intro i
    exact { aemeasurable_fst := (hlaw 0).aemeasurable
            aemeasurable_snd := (hlaw i).aemeasurable
            map_eq := (hlaw 0).map_eq.trans (hlaw i).map_eq.symm }
  · exact (hlaw 0).map_eq

/-- The genuine witness's data law puts the covariate `X` in the cube `[0,1]^d` a.s. -/
lemma doseDataMeasure_ae_X_mem_cube {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hp0_nonneg : ∀ x ∈ cube d, 0 ≤ p0 x)
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    ∀ᵐ O ∂(doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta), O.X ∈ cube d := by
  classical
  have _hp0_nonneg := hp0_nonneg
  let μ : Measure (DoseObs d) := doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta
  let Sbad : Set (DoseObs d) := {O | O.X ∉ cube d}
  have hSbad : MeasurableSet Sbad := by
    dsimp [Sbad]
    exact (measurableSet_cube d).compl.preimage measurable_doseObs_X
  rw [ae_iff]
  change μ Sbad = 0
  have hpre : Sbad = (fun O : DoseObs d => O.X) ⁻¹' (cube d)ᶜ := by
    rfl
  rw [hpre]
  rw [← Measure.map_apply measurable_doseObs_X (measurableSet_cube d).compl]
  rw [doseDataMeasure_map_X (d := d) (p0 := p0) (q0 := q0)
    (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
    (h := h) (zeta := zeta) hB hpA hmu]
  unfold doseXMeasure
  rw [withDensity_apply _ (measurableSet_cube d).compl]
  have hzero : (volume.restrict (cube d)) ((cube d)ᶜ) = 0 := by
    rw [Measure.restrict_apply (measurableSet_cube d).compl]
    simp
  exact setLIntegral_measure_zero ((cube d)ᶜ) (fun x => ENNReal.ofReal (p0 x)) hzero

/-- The genuine witness's data law puts the treatment `A` in `[0,1]` a.s. -/
lemma doseDataMeasure_ae_A_mem_Icc {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    ∀ᵐ O ∂(doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta),
      O.A ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have _hq0_nonneg := hq0_nonneg
  let μ : Measure (DoseObs d) := doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta
  let Sbad : Set (DoseObs d) := {O | O.A ∉ Set.Icc (0 : ℝ) 1}
  have hSbad : MeasurableSet Sbad := by
    dsimp [Sbad]
    exact measurableSet_Icc.compl.preimage measurable_doseObs_A
  rw [ae_iff]
  change μ Sbad = 0
  have hpre : Sbad = (fun O : DoseObs d => O.A) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ := by
    rfl
  rw [hpre]
  rw [← Measure.map_apply measurable_doseObs_A measurableSet_Icc.compl]
  have hmapA :
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta).map
          (fun O : DoseObs d => O.A) = doseAMeasure q0 := by
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
  rw [hmapA]
  unfold doseAMeasure
  rw [withDensity_apply _ measurableSet_Icc.compl]
  have hzero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    simp
  exact setLIntegral_measure_zero ((Set.Icc (0 : ℝ) 1)ᶜ)
    (fun a => ENNReal.ofReal (q0 a)) hzero

-- @node: dose-witness-membership
/-- The genuine two-point witness lies in the anisotropic Hölder dose-response class.
Only the treatment regression is perturbed (by the bump), the slack baseline
`(p_0, q_0)` is frozen, and the two semantic ties hold for the genuine joint law. -/
lemma doseWitness_mem_class {alpha beta s M c0 eps0 t0 eta0 B lambda h zeta : ℝ}
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    (hreg : RegimeConstants alpha beta s M c0 eps0 t0)
    (heta : 0 < eta0) (hB : 0 < B) (hBM : B ≤ M)
    (hp0_nonneg : ∀ x ∈ cube d, 0 ≤ p0 x) (hp0_int : (∫ x in cube d, p0 x) = 1)
    (hpxH : HolderBallND p0 s (M - eta0) (cube d))
    (hpxbd : ∀ x ∈ cube d, p0 x ≤ M - eta0)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a) (hq0_int : (∫ a in Set.Icc (0 : ℝ) 1, q0 a) = 1)
    (hqH : HolderBall1D q0 beta (M - eta0) (doseWindow t0 eps0))
    (hqpos : ∀ a ∈ doseWindow t0 eps0, c0 + eta0 ≤ q0 a)
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B)
    (hMuHolder : HolderBall1D
      (fun a => zeta * lambda * h ^ alpha * doseBump ((a - t0) / h)) alpha M
      (doseWindow t0 eps0))
    (hζ : zeta = -1 ∨ zeta = 1) (hhpos : 0 < h) (hhle : h ≤ 1) :
    HolderDoseClass d alpha beta s M c0 eps0 t0
      (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta) := by
  classical
  rcases hreg with ⟨hα, hβ, hs, hM, hc0, ht0, heps, hinterior⟩
  have _hζ := hζ
  have _hhpos := hhpos
  have _hhle := hhle
  have hpX : IsProbabilityMeasure (doseXMeasure p0) :=
    doseXMeasure_isProbabilityMeasure (d := d) (p0 := p0) hp0_nonneg hp0_int
  have hpA : IsProbabilityMeasure (doseAMeasure q0) :=
    doseAMeasure_isProbabilityMeasure (q0 := q0) hq0_nonneg hq0_int
  have hBMabs : |B| ≤ M := by
    rw [abs_of_pos hB]
    exact hBM
  refine
    { iid := ?_
      consistency := doseWitness_consistency (d := d) p0 q0 B alpha t0 lambda h zeta
      ignorability := doseWitness_ignorability (d := d) (p0 := p0) (q0 := q0)
        (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
        (h := h) (zeta := zeta) hB hpX hpA hmu
      bdd := doseWitness_bdd (d := d) (p0 := p0) (q0 := q0)
        (B := B) (M := M) (alpha := alpha) (t0 := t0)
        (lambda := lambda) (h := h) (zeta := zeta) hBMabs
      interior := hinterior
      positivity := ?_
      muT := ?_
      piT := ?_
      muX := ?_
      piX := ?_
      pxH := ?_
      muReg := doseWitness_muReg (d := d) (p0 := p0) (q0 := q0)
        (B := B) (M := M) (alpha := alpha) (t0 := t0)
        (lambda := lambda) (h := h) (zeta := zeta) hB hBMabs hpX hpA hmu
      pxDens := doseWitness_pxDens (d := d) (p0 := p0) (q0 := q0)
        (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
        (h := h) (zeta := zeta) hB hpA hmu
      -- Genuinely-new obligation from the `PiIsCondTreatmentDensity` tie of
      -- `HolderDoseClass`: (i) the range conjunct `0 ≤ π_P` on `[0,1]×cube` (immediate
      -- from `hq0_nonneg`, since the witness `pi a x = q0 a ≥ 0`), and (ii) the joint
      -- `(A,X)` law factorizes as `q0(a)·p0(x)` (A drawn independently of X with density
      -- q0, so the conditional density of A given X is q0 = the witness `pi` field, and
      -- `px = p0`). Left to the proof loop as the single new gap.
      piCond := doseWitness_piCond (d := d) (p0 := p0) (q0 := q0)
        (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
        (h := h) (zeta := zeta) hB hq0_nonneg hp0_int hq0_int hmu }
  · have hprob : IsProbabilityMeasure
        ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).dataMeasure) := by
      simpa [doseWitness] using
        doseDataMeasure_isProbabilityMeasure (d := d) (p0 := p0) (q0 := q0)
          (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
          (h := h) (zeta := zeta) hB hpX hpA hmu
    have hA :
        ∀ᵐ O ∂((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).dataMeasure),
          O.A ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [doseWitness] using
        doseDataMeasure_ae_A_mem_Icc (d := d) (p0 := p0) (q0 := q0)
          (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
          (h := h) (zeta := zeta) hB hq0_nonneg hpX hmu
    have hX :
        ∀ᵐ O ∂((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).dataMeasure),
          O.X ∈ cube d := by
      simpa [doseWitness] using
        doseDataMeasure_ae_X_mem_cube (d := d) (p0 := p0) (q0 := q0)
          (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
          (h := h) (zeta := zeta) hB hp0_nonneg hpA hmu
    letI : IsProbabilityMeasure
        ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).dataMeasure) := hprob
    exact ⟨hprob, hA, hX,
      iidSample_nonempty ((doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).dataMeasure)⟩
  · intro a ha x hx
    have hle : c0 ≤ q0 a := by
      linarith [hqpos a ha, heta]
    simpa [doseWitness] using hle
  · intro x hx
    simpa [doseWitness, doseWitnessMu] using hMuHolder
  · intro x hx
    simpa [doseWitness] using HolderBall1D_mono_radius (fun a => q0 a) hqH (by linarith)
  · have hconst :
        (fun x : Fin d → ℝ =>
          (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).mu t0 x)
          = fun _ => zeta * lambda * h ^ alpha := by
      funext x
      simp [doseWitness, doseWitnessMu, doseBump_zero]
    change HolderBallND
      (fun x : Fin d → ℝ =>
        (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta).mu t0 x)
      s M (cube d)
    rw [hconst]
    refine HolderBallND_const (d := d) (zeta * lambda * h ^ alpha) s M (cube d) ?_ hM.le
    have hmu0 := hmu t0 (fun _ : Fin d => (0 : ℝ))
    have hz : |zeta * lambda * h ^ alpha| ≤ B := by
      simpa [doseWitnessMu, doseBump_zero] using hmu0
    exact hz.trans hBM
  · have ht0win : t0 ∈ doseWindow t0 eps0 := center_mem_doseWindow heps.1.le
    have hq0_eta : |q0 t0| ≤ M - eta0 := by
      have hder := hqH.2.1 0 (by simp) t0 ht0win
      simpa using hder
    have hq0M : |q0 t0| ≤ M := hq0_eta.trans (by linarith)
    simpa [doseWitness] using
      HolderBallND_const (d := d) (q0 t0) s M (cube d) hq0M hM.le
  · refine ⟨?_, ?_, ?_⟩
    · exact HolderBallND_mono_radius p0 hpxH (by linarith)
    · intro x hx
      exact hp0_nonneg x hx
    · intro x hx
      exact (hpxbd x hx).trans (by linarith)

end CausalSmith.Stat.DoseResponseMinimax
