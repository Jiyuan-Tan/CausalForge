/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic

/-! Provides centered empirical-process and cross-fit process helpers. -/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ## Localized finite-VC empirical-process envelopes (assumed atomic gates)

`ass:vc-localized-envelope` and `ass:vc-localized-offset-envelope` are ATOMIC
empirical-process ASSUMPTIONS in the note's DAG (node kind `empirical-process`,
`ass:` prefix), on the same footing as `ass:iid` / `ass:margin`: the standard
finite-VC localized (fixed-radius and offset/Rademacher) empirical-process bounds
of Bartlett-Bousquet-Mendelson (2005). The note proves `lem:localized-vc-self-bound`,
`lem:crossfit-localized-offset-control`, and `thm:margin-localization` FROM these
inputs and never derives the inputs themselves; the achievability theorem
`oeq:feasible-upper` is conditional on them (they are conjuncts of the `upperRisk`
supremum domain in `Basic.lean`). They are therefore carried as visible assumed
`Prop` hypotheses (`VCLocalizedEnvelope` / `VCLocalizedOffsetEnvelope`) threaded to
the consumers below, NOT discharged. Discharging them is a substantial upstream
contribution (the population-to-empirical localization step) tracked in
`doc/research/SUBSTRATE_DEBT.md`. -/

/-! ## Centered empirical-process objects

The localized empirical-process lemmas below quantify over genuine centered
policy-indexed processes `(P_m - P) g_π` built from an i.i.d. sample and bound
their EXPECTED localized suprema, not abstract scalar placeholders. -/

/-- Centered policy-indexed empirical process `(P_m - P) g_π = m⁻¹ ∑_i g_π(O_i)
- E_P g_π` for an increment function `g` on a size-`m` sample. -/
noncomputable def centeredEmpProcess {m : ℕ} (P : ObservedLaw 𝒳)
    (g : Policy 𝒳 → Observation 𝒳 → ℝ) (sample : Fin m → Observation 𝒳)
    (π : Policy 𝒳) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, g π (sample i) - ∫ O, g π O ∂P.dataMeasure

/-- Expected localized supremum `E_P sup_{π ∈ Π : R_P(π) ≤ r} |(P_m - P) g_π|`,
the i.i.d. sample of size `m` drawn from `P`. -/
noncomputable def expectedLocalizedSup {m : ℕ} (P : ObservedLaw 𝒳)
    (g : Policy 𝒳 → Observation 𝒳 → ℝ) (policySet : Set (Policy 𝒳)) (r : ℝ) : ℝ :=
  ∫ sample, sSup ((fun π => |centeredEmpProcess P g sample π|) ''
      {π | π ∈ policySet ∧ lawRegret P π ≤ r})
    ∂(Measure.pi (fun _ : Fin m => P.dataMeasure))

/-- Pooled cross-fit centered process: average of the foldwise centered
increments `g (assign i)`, with each evaluation fold i.i.d. conditional on its
training fold. -/
noncomputable def pooledCrossfitProcess {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (sample : Fin n → Observation 𝒳) (π : Policy 𝒳) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i,
    (g (assign i) π (sample i) - ∫ O, g (assign i) π O ∂P.dataMeasure)

/-- Expected pooled cross-fit localized supremum. -/
noncomputable def expectedPooledLocalizedSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r : ℝ) : ℝ :=
  ∫ sample, sSup ((fun π => |pooledCrossfitProcess P g assign sample π|) ''
      {π | π ∈ policySet ∧ lawRegret P π ≤ r})
    ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))

/-- Expected pooled cross-fit offset positive-part supremum
`E_P sup_π {2|G_cf(π)| - R_P(π)/4}_+`. -/
noncomputable def expectedPooledOffsetSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) : ℝ :=
  ∫ sample, sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P g assign sample π| - lawRegret P π / 4))
      '' policySet)
    ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))

abbrev foldIndex {n K : ℕ} (assign : Fin n → Fin K) (k : Fin K) :=
  {i : Fin n // assign i = k}

def foldProjection {n K : ℕ} (assign : Fin n → Fin K) (k : Fin K)
    (sample : Fin n → Observation 𝒳) : foldIndex assign k → Observation 𝒳 :=
  fun i => sample i.1

lemma measurePreserving_foldProjection {n K : ℕ} (P : ObservedLaw 𝒳)
    (assign : Fin n → Fin K) (k : Fin K) [IsProbabilityMeasure P.dataMeasure] :
    MeasurePreserving (foldProjection (𝒳 := 𝒳) assign k)
      (Measure.pi (fun _ : Fin n => P.dataMeasure))
      (Measure.pi (fun _ : foldIndex assign k => P.dataMeasure)) := by
  classical
  let p : Fin n → Prop := fun i => assign i = k
  let hsplit := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Fin n => P.dataMeasure) (p := p)
  let hfst : MeasurePreserving Prod.fst
      ((Measure.pi (fun _ : Subtype p => P.dataMeasure)).prod
        (Measure.pi (fun _ : Subtype (fun i => ¬ p i) => P.dataMeasure)))
      (Measure.pi (fun _ : Subtype p => P.dataMeasure)) := by
    exact measurePreserving_fst
  simpa [foldProjection, p, MeasurableEquiv.piEquivPiSubtypeProd] using hfst.comp hsplit

private lemma measurable_sSup_of_countable_skeleton {n : ℕ}
    (policySet Pi0 : Set (Policy 𝒳))
    (F : (Fin n → Observation 𝒳) → Policy 𝒳 → ℝ)
    (hPi0_count : Pi0.Countable)
    (hF : ∀ π ∈ Pi0, Measurable (fun sample => F sample π))
    (heq : ∀ sample,
      sSup ((fun π => F sample π) '' policySet) =
        sSup ((fun π => F sample π) '' Pi0)) :
    Measurable (fun sample => sSup ((fun π => F sample π) '' policySet)) := by
  classical
  letI : Countable Pi0 := hPi0_count.to_subtype
  have hsup :
      Measurable (fun sample : Fin n → Observation 𝒳 =>
        ⨆ π : Pi0, F sample π.1) := by
    exact Measurable.iSup (fun π => hF π.1 π.2)
  convert hsup using 1
  ext sample
  rw [heq sample]
  have himage :
      ((fun π : Policy 𝒳 => F sample π) '' Pi0) =
        ((fun π : Pi0 => F sample π.1) '' Set.univ) := by
    ext y
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨⟨π, hπ⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨π, _hπ, rfl⟩
      exact ⟨π.1, π.2, rfl⟩
  rw [himage]
  have huniv :
      ((fun π : Pi0 => F sample π.1) '' Set.univ) =
        Set.range (fun π : Pi0 => F sample π.1) := by
    ext y
    constructor
    · rintro ⟨π, _hπ, rfl⟩
      exact ⟨π, rfl⟩
    · rintro ⟨π, rfl⟩
      exact ⟨π, Set.mem_univ _, rfl⟩
  rw [huniv]
  rw [sSup_range]

noncomputable def foldCenteredProcess {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (k : Fin K) (sample : Fin n → Observation 𝒳) (π : Policy 𝒳) : ℝ :=
  ((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
    ∑ i : foldIndex assign k,
      (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure)

noncomputable def foldLocalizedSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r : ℝ) (k : Fin K)
    (sample : Fin n → Observation 𝒳) : ℝ :=
  sSup ((fun π => |foldCenteredProcess P g assign k sample π|) ''
      {π | π ∈ policySet ∧ lawRegret P π ≤ r})

noncomputable def foldOffsetSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (k : Fin K)
    (sample : Fin n → Observation 𝒳) : ℝ :=
  sSup ((fun π =>
      max 0 (2 * |foldCenteredProcess P g assign k sample π| - lawRegret P π / 4))
    '' policySet)

noncomputable def foldLocalizedSubSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r : ℝ) (k : Fin K)
    (sample : foldIndex assign k → Observation 𝒳) : ℝ :=
  sSup ((fun π =>
      |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)|) ''
      {π | π ∈ policySet ∧ lawRegret P π ≤ r})

noncomputable def foldOffsetSubSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (k : Fin K)
    (sample : foldIndex assign k → Observation 𝒳) : ℝ :=
  sSup ((fun π =>
      max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)|
        - lawRegret P π / 4)) '' policySet)

private lemma foldSubCentered_eq_centeredEmpProcess_piCongr {n K : ℕ}
    (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (k : Fin K) (π : Policy 𝒳)
    (e : foldIndex assign k ≃ Fin (Fintype.card (foldIndex assign k)))
    (hm : 0 < Fintype.card (foldIndex assign k))
    (sample : foldIndex assign k → Observation 𝒳) :
    ((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)
      =
    centeredEmpProcess P (g k)
      ((MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample) π := by
  classical
  let m := Fintype.card (foldIndex assign k)
  let I : ℝ := ∫ O, g k π O ∂P.dataMeasure
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hsum_center :
      (∑ i : foldIndex assign k, (g k π (sample i) - I)) =
        (∑ i : foldIndex assign k, g k π (sample i)) - (m : ℝ) * I := by
    simp [m, I, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hsum_reindex :
      (∑ j : Fin (Fintype.card (foldIndex assign k)),
        g k π
          (((MeasurableEquiv.piCongrLeft
            (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample) j))
        =
      ∑ i : foldIndex assign k, g k π (sample i) := by
    symm
    refine Fintype.sum_equiv e
      (fun i : foldIndex assign k => g k π (sample i))
      (fun j : Fin (Fintype.card (foldIndex assign k)) =>
        g k π
          (((MeasurableEquiv.piCongrLeft
            (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample) j))
      ?_
    intro i
    have happly :
        ((MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample)
            (e i) = sample i :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (e := e) (β := fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳)
        sample i
    simp [happly]
  calc
    ((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)
        = (m : ℝ)⁻¹ * ((∑ i : foldIndex assign k, g k π (sample i)) - (m : ℝ) * I) := by
            simp [m, I, hsum_center]
    _ = (m : ℝ)⁻¹ * (∑ i : foldIndex assign k, g k π (sample i)) - I := by
            field_simp [hmR]
    _ = (m : ℝ)⁻¹ *
          (∑ j : Fin (Fintype.card (foldIndex assign k)),
            g k π
              (((MeasurableEquiv.piCongrLeft
                (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample) j)) -
          I := by rw [hsum_reindex]
    _ = centeredEmpProcess P (g k)
        ((MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample) π := by
          rfl

private lemma foldLocalizedSubSup_eq_fin {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r : ℝ) (k : Fin K)
    (e : foldIndex assign k ≃ Fin (Fintype.card (foldIndex assign k)))
    (hm : 0 < Fintype.card (foldIndex assign k))
    (sample : foldIndex assign k → Observation 𝒳) :
    foldLocalizedSubSup P g assign policySet r k sample =
      sSup ((fun π =>
          |centeredEmpProcess P (g k)
            ((MeasurableEquiv.piCongrLeft
              (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample) π|)
        '' {π | π ∈ policySet ∧ lawRegret P π ≤ r}) := by
  classical
  unfold foldLocalizedSubSup
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨π, hπ, by
      have hcenter := foldSubCentered_eq_centeredEmpProcess_piCongr P g assign k π e hm sample
      simpa using congrArg (fun x : ℝ => |x|) hcenter.symm⟩
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨π, hπ, by
      have hcenter := foldSubCentered_eq_centeredEmpProcess_piCongr P g assign k π e hm sample
      simpa using congrArg (fun x : ℝ => |x|) hcenter⟩

private lemma foldOffsetSubSup_eq_fin {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (k : Fin K)
    (e : foldIndex assign k ≃ Fin (Fintype.card (foldIndex assign k)))
    (hm : 0 < Fintype.card (foldIndex assign k))
    (sample : foldIndex assign k → Observation 𝒳) :
    foldOffsetSubSup P g assign policySet k sample =
      sSup ((fun π =>
          max 0 (2 * |centeredEmpProcess P (g k)
            ((MeasurableEquiv.piCongrLeft
              (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample) π|
            - lawRegret P π / 4)) '' policySet) := by
  classical
  unfold foldOffsetSubSup
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨π, hπ, by
      have hcenter := foldSubCentered_eq_centeredEmpProcess_piCongr P g assign k π e hm sample
      simpa using congrArg
        (fun x : ℝ => max 0 (2 * |x| - lawRegret P π / 4)) hcenter.symm⟩
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨π, hπ, by
      have hcenter := foldSubCentered_eq_centeredEmpProcess_piCongr P g assign k π e hm sample
      simpa using congrArg
        (fun x : ℝ => max 0 (2 * |x| - lawRegret P π / 4)) hcenter⟩

private lemma integral_foldLocalizedSubSup_eq_expected {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r : ℝ) (k : Fin K)
    [SigmaFinite P.dataMeasure]
    (hm : 0 < Fintype.card (foldIndex assign k)) :
    ∫ sample : foldIndex assign k → Observation 𝒳,
        foldLocalizedSubSup P g assign policySet r k sample
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))
      =
    expectedLocalizedSup (m := Fintype.card (foldIndex assign k)) P (g k) policySet r := by
  classical
  let e : foldIndex assign k ≃ Fin (Fintype.card (foldIndex assign k)) :=
    Fintype.equivFin (foldIndex assign k)
  let F : (Fin (Fintype.card (foldIndex assign k)) → Observation 𝒳) → ℝ :=
    fun sample =>
      sSup ((fun π => |centeredEmpProcess P (g k) sample π|) ''
        {π | π ∈ policySet ∧ lawRegret P π ≤ r})
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e)
      (Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))
      (Measure.pi (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) := by
    simpa using
      (MeasureTheory.measurePreserving_piCongrLeft
        (μ := fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure) e)
  have hcomp := hmp.integral_comp' F
  calc
    ∫ sample : foldIndex assign k → Observation 𝒳,
        foldLocalizedSubSup P g assign policySet r k sample
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))
        =
      ∫ sample : foldIndex assign k → Observation 𝒳,
        F ((MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample)
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun sample =>
            foldLocalizedSubSup_eq_fin P g assign policySet r k e hm sample)
    _ =
      ∫ sample : Fin (Fintype.card (foldIndex assign k)) → Observation 𝒳,
        F sample
        ∂(Measure.pi (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) := hcomp
    _ = expectedLocalizedSup (m := Fintype.card (foldIndex assign k)) P (g k) policySet r := by
          rfl

private lemma integral_foldOffsetSubSup_eq_expected {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (k : Fin K)
    [SigmaFinite P.dataMeasure]
    (hm : 0 < Fintype.card (foldIndex assign k)) :
    ∫ sample : foldIndex assign k → Observation 𝒳,
        foldOffsetSubSup P g assign policySet k sample
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))
      =
    ∫ sample,
        sSup ((fun π => max 0
          (2 * |centeredEmpProcess P (g k) sample π| - lawRegret P π / 4)) '' policySet)
        ∂(Measure.pi
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) := by
  classical
  let e : foldIndex assign k ≃ Fin (Fintype.card (foldIndex assign k)) :=
    Fintype.equivFin (foldIndex assign k)
  let F : (Fin (Fintype.card (foldIndex assign k)) → Observation 𝒳) → ℝ :=
    fun sample =>
      sSup ((fun π => max 0
        (2 * |centeredEmpProcess P (g k) sample π| - lawRegret P π / 4)) '' policySet)
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e)
      (Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))
      (Measure.pi (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) := by
    simpa using
      (MeasureTheory.measurePreserving_piCongrLeft
        (μ := fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure) e)
  have hcomp := hmp.integral_comp' F
  calc
    ∫ sample : foldIndex assign k → Observation 𝒳,
        foldOffsetSubSup P g assign policySet k sample
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))
        =
      ∫ sample : foldIndex assign k → Observation 𝒳,
        F ((MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => Observation 𝒳) e) sample)
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun sample =>
            foldOffsetSubSup_eq_fin P g assign policySet k e hm sample)
    _ =
      ∫ sample : Fin (Fintype.card (foldIndex assign k)) → Observation 𝒳,
        F sample
        ∂(Measure.pi (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) := hcomp
    _ =
      ∫ sample,
        sSup ((fun π => max 0
          (2 * |centeredEmpProcess P (g k) sample π| - lawRegret P π / 4)) '' policySet)
        ∂(Measure.pi
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) := by
          rfl

lemma integral_foldLocalizedSup_eq_expected {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r : ℝ) (k : Fin K)
    [IsProbabilityMeasure P.dataMeasure]
    (hm : 0 < Fintype.card (foldIndex assign k))
    (hInt_sub : Integrable
      (fun sample : foldIndex assign k → Observation 𝒳 =>
        foldLocalizedSubSup P g assign policySet r k sample)
      (Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))) :
    ∫ sample : Fin n → Observation 𝒳,
        foldLocalizedSup P g assign policySet r k sample
        ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
      =
    expectedLocalizedSup (m := Fintype.card (foldIndex assign k)) P (g k) policySet r := by
  classical
  let F : (foldIndex assign k → Observation 𝒳) → ℝ :=
    fun sample => foldLocalizedSubSup P g assign policySet r k sample
  have hproj := measurePreserving_foldProjection P assign k
  have hmap : Measure.map (foldProjection (𝒳 := 𝒳) assign k)
      (Measure.pi (fun _ : Fin n => P.dataMeasure))
      = Measure.pi (fun _ : foldIndex assign k => P.dataMeasure) := hproj.map_eq
  have hsm : AEStronglyMeasurable F
      (Measure.map (foldProjection (𝒳 := 𝒳) assign k)
        (Measure.pi (fun _ : Fin n => P.dataMeasure))) := by
    rw [hmap]
    exact hInt_sub.aestronglyMeasurable
  calc
    ∫ sample : Fin n → Observation 𝒳,
        foldLocalizedSup P g assign policySet r k sample
        ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
        =
      ∫ sample : Fin n → Observation 𝒳,
        F (foldProjection (𝒳 := 𝒳) assign k sample)
        ∂(Measure.pi (fun _ : Fin n => P.dataMeasure)) := by
          rfl
    _ = ∫ sample : foldIndex assign k → Observation 𝒳, F sample
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure)) := by
          rw [← hmap]
          exact (integral_map hproj.aemeasurable hsm).symm
    _ = expectedLocalizedSup (m := Fintype.card (foldIndex assign k)) P (g k) policySet r :=
          integral_foldLocalizedSubSup_eq_expected P g assign policySet r k hm

lemma integral_foldOffsetSup_eq_expected {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (k : Fin K)
    [IsProbabilityMeasure P.dataMeasure]
    (hm : 0 < Fintype.card (foldIndex assign k))
    (hInt_sub : Integrable
      (fun sample : foldIndex assign k → Observation 𝒳 =>
        foldOffsetSubSup P g assign policySet k sample)
      (Measure.pi (fun _ : foldIndex assign k => P.dataMeasure))) :
    ∫ sample : Fin n → Observation 𝒳,
        foldOffsetSup P g assign policySet k sample
        ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
      =
    ∫ sample,
        sSup ((fun π => max 0
          (2 * |centeredEmpProcess P (g k) sample π| - lawRegret P π / 4)) '' policySet)
        ∂(Measure.pi
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) := by
  classical
  let F : (foldIndex assign k → Observation 𝒳) → ℝ :=
    fun sample => foldOffsetSubSup P g assign policySet k sample
  have hproj := measurePreserving_foldProjection P assign k
  have hmap : Measure.map (foldProjection (𝒳 := 𝒳) assign k)
      (Measure.pi (fun _ : Fin n => P.dataMeasure))
      = Measure.pi (fun _ : foldIndex assign k => P.dataMeasure) := hproj.map_eq
  have hsm : AEStronglyMeasurable F
      (Measure.map (foldProjection (𝒳 := 𝒳) assign k)
        (Measure.pi (fun _ : Fin n => P.dataMeasure))) := by
    rw [hmap]
    exact hInt_sub.aestronglyMeasurable
  calc
    ∫ sample : Fin n → Observation 𝒳,
        foldOffsetSup P g assign policySet k sample
        ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
        =
      ∫ sample : Fin n → Observation 𝒳,
        F (foldProjection (𝒳 := 𝒳) assign k sample)
        ∂(Measure.pi (fun _ : Fin n => P.dataMeasure)) := by
          rfl
    _ = ∫ sample : foldIndex assign k → Observation 𝒳, F sample
        ∂(Measure.pi (fun _ : foldIndex assign k => P.dataMeasure)) := by
          rw [← hmap]
          exact (integral_map hproj.aemeasurable hsm).symm
    _ =
      ∫ sample,
        sSup ((fun π => max 0
          (2 * |centeredEmpProcess P (g k) sample π| - lawRegret P π / 4)) '' policySet)
        ∂(Measure.pi
          (fun _ : Fin (Fintype.card (foldIndex assign k)) => P.dataMeasure)) :=
          integral_foldOffsetSubSup_eq_expected P g assign policySet k hm

private lemma pooledCrossfitProcess_eq_sum_fold {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (sample : Fin n → Observation 𝒳) (π : Policy 𝒳) (hn : 0 < n) :
    pooledCrossfitProcess P g assign sample π =
      ∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
        foldCenteredProcess P g assign k sample π := by
  classical
  let e : Fin n ≃ Sigma (foldIndex assign) := {
    toFun := fun i => ⟨assign i, ⟨i, rfl⟩⟩
    invFun := fun p => p.2.1
    left_inv := fun i => rfl
    right_inv := fun p => by
      cases p with
      | mk k i =>
        cases i with
        | mk i hi =>
          subst k
          rfl }
  have hregroup :
      (∑ i : Fin n, (g (assign i) π (sample i)
          - ∫ O, g (assign i) π O ∂P.dataMeasure)) =
        ∑ k : Fin K, ∑ i : foldIndex assign k,
          (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure) := by
    calc
      (∑ i : Fin n, (g (assign i) π (sample i)
          - ∫ O, g (assign i) π O ∂P.dataMeasure))
          = ∑ p : Sigma (foldIndex assign),
              (g p.1 π (sample p.2.1)
                - ∫ O, g p.1 π O ∂P.dataMeasure) := by
            simpa [e] using
              (Fintype.sum_equiv e
                (fun i : Fin n => g (assign i) π (sample i)
                  - ∫ O, g (assign i) π O ∂P.dataMeasure)
                (fun p : Sigma (foldIndex assign) =>
                  g p.1 π (sample p.2.1)
                    - ∫ O, g p.1 π O ∂P.dataMeasure)
                (by intro i; rfl))
      _ = ∑ k : Fin K, ∑ i : foldIndex assign k,
          (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure) := by
            rw [Fintype.sum_sigma]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hterm : ∀ k : Fin K,
      ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
          (((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
            ∑ i : foldIndex assign k,
              (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure)) =
        (n : ℝ)⁻¹ * ∑ i : foldIndex assign k,
          (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure) := by
    intro k
    let m := Fintype.card (foldIndex assign k)
    let S : ℝ := ∑ i : foldIndex assign k,
      (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure)
    by_cases hm : m = 0
    · have hempty : IsEmpty (foldIndex assign k) := Fintype.card_eq_zero_iff.mp hm
      simp [m, S, hm]
    · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      field_simp [m, S, hmR, hnR]
  calc
    pooledCrossfitProcess P g assign sample π
        = (n : ℝ)⁻¹ * ∑ i : Fin n,
            (g (assign i) π (sample i)
              - ∫ O, g (assign i) π O ∂P.dataMeasure) := rfl
    _ = (n : ℝ)⁻¹ * ∑ k : Fin K, ∑ i : foldIndex assign k,
            (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure) := by
          rw [hregroup]
    _ = ∑ k : Fin K, (n : ℝ)⁻¹ * ∑ i : foldIndex assign k,
            (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure) := by
          rw [Finset.mul_sum]
    _ = ∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
        foldCenteredProcess P g assign k sample π := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [foldCenteredProcess]
          exact (hterm k).symm

private lemma sum_foldIndex_card {n K : ℕ} (assign : Fin n → Fin K) :
    (∑ k : Fin K, Fintype.card (foldIndex assign k)) = n := by
  classical
  let e : Fin n ≃ Sigma (foldIndex assign) := {
    toFun := fun i => ⟨assign i, ⟨i, rfl⟩⟩
    invFun := fun p => p.2.1
    left_inv := fun i => rfl
    right_inv := fun p => by
      cases p with
      | mk k i =>
        cases i with
        | mk i hi =>
          subst k
          rfl }
  have hcard : Fintype.card (Sigma (foldIndex assign)) = n := by
    simpa using Fintype.card_congr e.symm
  calc
    (∑ k : Fin K, Fintype.card (foldIndex assign k))
        = Fintype.card (Sigma (foldIndex assign)) :=
          (Fintype.card_sigma (α := foldIndex assign)).symm
    _ = n := hcard

lemma sum_foldWeights_eq_one {n K : ℕ} (assign : Fin n → Fin K) (hn : 0 < n) :
    (∑ k : Fin K, (Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) = 1 := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hcard := sum_foldIndex_card assign
  calc
    (∑ k : Fin K, (Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ))
        = ((∑ k : Fin K, (Fintype.card (foldIndex assign k) : ℝ)) / (n : ℝ)) := by
          rw [Finset.sum_div]
    _ = 1 := by
          rw [← Nat.cast_sum, hcard]
          field_simp [hnR]

lemma inv_card_sum_assign_eq_sum_foldWeights {n K : ℕ}
    (assign : Fin n → Fin K) (H : Fin K → ℝ) (hn : 0 < n) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, H (assign i) =
      ∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) * H k := by
  classical
  let e : Fin n ≃ Sigma (foldIndex assign) := {
    toFun := fun i => ⟨assign i, ⟨i, rfl⟩⟩
    invFun := fun p => p.2.1
    left_inv := fun i => rfl
    right_inv := fun p => by
      cases p with
      | mk k i =>
        cases i with
        | mk i hi =>
          subst k
          rfl }
  have hregroup :
      (∑ i : Fin n, H (assign i)) =
        ∑ k : Fin K, ∑ _i : foldIndex assign k, H k := by
    calc
      (∑ i : Fin n, H (assign i))
          = ∑ p : Sigma (foldIndex assign), H p.1 := by
            simpa [e] using
              (Fintype.sum_equiv e
                (fun i : Fin n => H (assign i))
                (fun p : Sigma (foldIndex assign) => H p.1)
                (by intro i; rfl))
      _ = ∑ k : Fin K, ∑ _i : foldIndex assign k, H k := by
            rw [Fintype.sum_sigma]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℝ)⁻¹ * ∑ i : Fin n, H (assign i)
        = (n : ℝ)⁻¹ * ∑ k : Fin K, ∑ _i : foldIndex assign k, H k := by
          rw [hregroup]
    _ = ∑ k : Fin K, (n : ℝ)⁻¹ * ∑ _i : foldIndex assign k, H k := by
          rw [Finset.mul_sum]
    _ = ∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) * H k := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp [div_eq_inv_mul, mul_comm, mul_left_comm]

lemma foldIndex_card_le {n K : ℕ} (assign : Fin n → Fin K) (k : Fin K) :
    Fintype.card (foldIndex assign k) ≤ n := by
  classical
  simpa using
    Fintype.card_le_of_injective (fun i : foldIndex assign k => (i.1 : Fin n))
      (by intro a b h; exact Subtype.ext h)

lemma fold_weight_mul_inv_sqrt_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ((m : ℝ) / (n : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_neg hmR.le, Real.rpow_neg hnR.le]
  rw [← Real.sqrt_eq_rpow (m : ℝ), ← Real.sqrt_eq_rpow (n : ℝ)]
  have hsqrt_le : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmn)
  have hsqrt_n_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_m_nonneg : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hmul : Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    calc
      Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)
          ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
            exact mul_le_mul_of_nonneg_right hsqrt_le hsqrt_n_nonneg
      _ = (n : ℝ) := by rw [Real.mul_self_sqrt hnR.le]
  have hm_eq : (m : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := by
    rw [Real.mul_self_sqrt hmR.le]
  have hcross : (m : ℝ) * Real.sqrt (n : ℝ) ≤ (n : ℝ) * Real.sqrt (m : ℝ) := by
    calc
      (m : ℝ) * Real.sqrt (n : ℝ)
          = Real.sqrt (m : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
            conv_lhs => rw [hm_eq]
            ring
      _ ≤ Real.sqrt (m : ℝ) * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hmul hsqrt_m_nonneg
      _ = (n : ℝ) * Real.sqrt (m : ℝ) := by ring
  field_simp [hmR.ne', hnR.ne', Real.sqrt_pos.2 hmR, Real.sqrt_pos.2 hnR]
  exact hcross

lemma fold_weight_mul_offset_rpow_le {m n : ℕ} {B A : ℝ}
    (hm : 0 < m) (hmn : m ≤ n) (hA1 : A ≤ 1) :
    ((m : ℝ) / (n : ℝ)) * (B ^ 2 / (m : ℝ)) ^ A ≤
      (B ^ 2 / (n : ℝ)) ^ A := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let x : ℝ := (m : ℝ) / (n : ℝ)
  have hxpos : 0 < x := div_pos hmR hnR
  have hxnonneg : 0 ≤ x := hxpos.le
  have hxle : x ≤ 1 := by
    dsimp [x]
    exact div_le_one_of_le₀ (by exact_mod_cast hmn) hnR.le
  have hbnonneg : 0 ≤ B ^ 2 / (n : ℝ) := div_nonneg (sq_nonneg B) hnR.le
  have hxpow_le : x ^ (1 - A) ≤ 1 := by
    exact Real.rpow_le_one hxnonneg hxle (sub_nonneg.mpr hA1)
  have heq_base : B ^ 2 / (m : ℝ) = (B ^ 2 / (n : ℝ)) / x := by
    dsimp [x]
    field_simp [hmR.ne', hnR.ne']
  calc
    ((m : ℝ) / (n : ℝ)) * (B ^ 2 / (m : ℝ)) ^ A
        = x * (((B ^ 2 / (n : ℝ)) / x) ^ A) := by rw [heq_base]
    _ = x * ((B ^ 2 / (n : ℝ)) ^ A / x ^ A) := by
          rw [Real.div_rpow hbnonneg hxnonneg]
    _ = (B ^ 2 / (n : ℝ)) ^ A * x ^ (1 - A) := by
          have hxA_ne : x ^ A ≠ 0 := (Real.rpow_pos_of_pos hxpos A).ne'
          have hsub := Real.rpow_sub hxpos 1 A
          rw [Real.rpow_one] at hsub
          rw [hsub]
          field_simp [hxA_ne]
    _ ≤ (B ^ 2 / (n : ℝ)) ^ A * 1 := by
          exact mul_le_mul_of_nonneg_left hxpow_le (Real.rpow_nonneg hbnonneg A)
    _ = (B ^ 2 / (n : ℝ)) ^ A := by ring

lemma log_nat_rpow_le {m n : ℕ} {p : ℝ}
    (hm : 0 < m) (hmn : m ≤ n) (hp : 0 ≤ p) :
    (Real.log (m : ℝ)) ^ p ≤ (Real.log (n : ℝ)) ^ p := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hlog_nonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hm)
  have hlog_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hmR hmnR
  exact Real.rpow_le_rpow hlog_nonneg hlog_le hp

private lemma abs_integral_le_of_bound (P : ObservedLaw 𝒳)
    (f : Observation 𝒳 → ℝ) (B : ℝ) [IsProbabilityMeasure P.dataMeasure]
    (hB : 0 ≤ B) (hbound : ∀ O, |f O| ≤ B) :
    |∫ O, f O ∂P.dataMeasure| ≤ B := by
  have hnorm : ‖∫ O, f O ∂P.dataMeasure‖ ≤ B * P.dataMeasure.real Set.univ := by
    exact norm_integral_le_of_norm_le_const (μ := P.dataMeasure)
      (f := f) (C := B)
      (Filter.Eventually.of_forall (by simpa [Real.norm_eq_abs] using hbound))
  simpa [Real.norm_eq_abs] using hnorm

private lemma abs_foldCenteredProcess_le {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (k : Fin K) (sample : Fin n → Observation 𝒳) (π : Policy 𝒳) (B : ℝ)
    [IsProbabilityMeasure P.dataMeasure]
    (hB : 0 ≤ B) (hbound : ∀ O, |g k π O| ≤ B) :
    |foldCenteredProcess P g assign k sample π| ≤ 2 * B := by
  classical
  let m := Fintype.card (foldIndex assign k)
  let S : ℝ := ∑ i : foldIndex assign k,
      (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure)
  have hint : |∫ O, g k π O ∂P.dataMeasure| ≤ B :=
    abs_integral_le_of_bound P (g k π) B hB hbound
  have hcenter : ∀ i : foldIndex assign k,
      |g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure| ≤ 2 * B := by
    intro i
    calc
      |g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure|
          ≤ |g k π (sample i.1)| + |∫ O, g k π O ∂P.dataMeasure| := abs_sub _ _
      _ ≤ B + B := add_le_add (hbound _) hint
      _ = 2 * B := by ring
  by_cases hm : m = 0
  · have hempty : IsEmpty (foldIndex assign k) := Fintype.card_eq_zero_iff.mp hm
    simp [foldCenteredProcess, m, hm, hB]
  · have hmposNat : 0 < m := Nat.pos_of_ne_zero hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
    have hsum : |S| ≤ (m : ℝ) * (2 * B) := by
      calc
        |S| = |∑ i : foldIndex assign k,
          (g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure)| := rfl
        _ ≤ ∑ i : foldIndex assign k,
            |g k π (sample i.1) - ∫ O, g k π O ∂P.dataMeasure| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : foldIndex assign k, 2 * B := by
              exact Finset.sum_le_sum (fun i _ => hcenter i)
        _ = (m : ℝ) * (2 * B) := by simp [m]
    have hnon : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr hmpos.le
    have habs : |(m : ℝ)⁻¹ * S| ≤ (m : ℝ)⁻¹ * ((m : ℝ) * (2 * B)) := by
      calc
        |(m : ℝ)⁻¹ * S| = (m : ℝ)⁻¹ * |S| := by
          rw [abs_mul, abs_of_nonneg hnon]
        _ ≤ (m : ℝ)⁻¹ * ((m : ℝ) * (2 * B)) :=
          mul_le_mul_of_nonneg_left hsum hnon
    have hcalc : (m : ℝ)⁻¹ * ((m : ℝ) * (2 * B)) = 2 * B := by
      field_simp [ne_of_gt hmpos]
    simpa [foldCenteredProcess, m, S, hcalc] using habs

private lemma contrast_abs_le_two (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) :
    ∀ x, |P.contrast x| ≤ (2 : ℝ) := by
  rcases hwf with ⟨_hPprob, _hPXprob, _hmap, _hτmeas, _hpropmeas, _hmu0meas,
    _hmu1meas, hτeq, _hprop, _hceA, _hceY1, _hceY0⟩
  intro x
  have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
    abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
  have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
    abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
  calc
    |P.contrast x| = |P.mu1 x - P.mu0 x| := by rw [hτeq]
    _ ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hmu1 hmu0
    _ = (2 : ℝ) := by norm_num

lemma lawOptimalPolicy_measurable (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) : Measurable (lawOptimalPolicy P) := by
  rcases hwf with ⟨_hPprob, _hPXprob, _hmap, hτmeas, _⟩
  refine measurable_to_bool (f := lawOptimalPolicy P) ?_
  change MeasurableSet {x | lawOptimalPolicy P x = true}
  simpa [lawOptimalPolicy, optimalPolicy] using
    measurableSet_le measurable_const hτmeas

private lemma abs_lawWelfare_le_two (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    |lawWelfare P π| ≤ (2 : ℝ) := by
  rcases hwf with ⟨_hPprob, hPXprob, _hmap, hτmeas, _hpropmeas, _hmu0meas,
    _hmu1meas, hτeq, _hprop, _hceA, _hceY1, _hceY0⟩
  letI : IsProbabilityMeasure P.PX := hPXprob
  have hτbound : ∀ x, |P.contrast x| ≤ (2 : ℝ) := by
    intro x
    have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
    have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
    calc
      |P.contrast x| = |P.mu1 x - P.mu0 x| := by rw [hτeq]
      _ ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hmu1 hmu0
      _ = (2 : ℝ) := by norm_num
  have hnorm :
      ‖∫ x, boolIndicator (π x) * P.contrast x ∂P.PX‖
        ≤ (2 : ℝ) * P.PX.real Set.univ := by
    apply norm_integral_le_of_norm_le_const (μ := P.PX)
      (f := fun x => boolIndicator (π x) * P.contrast x) (C := (2 : ℝ))
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    have hb : |boolIndicator (π x)| ≤ (1 : ℝ) := by
      cases π x <;> simp [boolIndicator]
    nlinarith [mul_le_mul hb (hτbound x) (abs_nonneg (P.contrast x))
      (by norm_num : (0 : ℝ) ≤ 1)]
  simpa [lawWelfare, Real.norm_eq_abs] using hnorm

private lemma lawRegret_lower_bound (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    (-4 : ℝ) ≤ lawRegret P π := by
  have hoptm : Measurable (lawOptimalPolicy P) := lawOptimalPolicy_measurable P hwf
  have hopt := abs_lawWelfare_le_two P (lawOptimalPolicy P) hwf hbdd hoptm
  have hpi := abs_lawWelfare_le_two P π hwf hbdd hπ
  have hopt_low : (-2 : ℝ) ≤ lawWelfare P (lawOptimalPolicy P) := (abs_le.mp hopt).1
  have hpi_high : lawWelfare P π ≤ (2 : ℝ) := (abs_le.mp hpi).2
  have hmain : (-4 : ℝ) ≤ lawWelfare P (lawOptimalPolicy P) - lawWelfare P π := by
    linarith
  simpa [lawRegret, regret, lawWelfare, lawOptimalPolicy] using hmain

lemma lawRegret_nonneg (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    0 ≤ lawRegret P π := by
  rw [regret_eq_disagreement_integral P π hwf hbdd hπ]
  exact integral_nonneg (fun x =>
    mul_nonneg (abs_nonneg _) (by
      unfold disagreementIndicator
      split <;> norm_num))

private lemma max_weighted_abs_sub_le_sum {K : ℕ} (w H : Fin K → ℝ) (R : ℝ)
    (hw_nonneg : ∀ k, 0 ≤ w k) (hw_sum : (∑ k, w k) = 1) :
    max 0 (2 * |∑ k, w k * H k| - R / 4)
      ≤ ∑ k, w k * max 0 (2 * |H k| - R / 4) := by
  classical
  have habs : |∑ k, w k * H k| ≤ ∑ k, w k * |H k| := by
    calc
      |∑ k, w k * H k| ≤ ∑ k, |w k * H k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, w k * |H k| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (hw_nonneg k)]
  have hsum_eq :
      (∑ k, w k * (2 * |H k| - R / 4)) =
        2 * (∑ k, w k * |H k|) - R / 4 := by
    calc
      (∑ k, w k * (2 * |H k| - R / 4))
          = ∑ k, (2 * (w k * |H k|) - (R / 4) * w k) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = 2 * (∑ k, w k * |H k|) - (R / 4) * (∑ k, w k) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * (∑ k, w k * |H k|) - R / 4 := by
            rw [hw_sum]
            ring
  have hlinear : 2 * |∑ k, w k * H k| - R / 4
      ≤ ∑ k, w k * (2 * |H k| - R / 4) := by
    rw [hsum_eq]
    linarith
  have hzero : 0 ≤ ∑ k, w k * max 0 (2 * |H k| - R / 4) := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (hw_nonneg k) (le_max_left _ _)
  have hlinle : 2 * |∑ k, w k * H k| - R / 4
      ≤ ∑ k, w k * max 0 (2 * |H k| - R / 4) := by
    calc
      2 * |∑ k, w k * H k| - R / 4
          ≤ ∑ k, w k * (2 * |H k| - R / 4) := hlinear
      _ ≤ ∑ k, w k * max 0 (2 * |H k| - R / 4) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hw_nonneg k)
  exact max_le hzero hlinle

lemma pooledLocalizedSup_pointwise_le_sum_fold {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r B : ℝ) (sample : Fin n → Observation 𝒳)
    [IsProbabilityMeasure P.dataMeasure]
    (hn : 0 < n) (hB : 0 ≤ B)
    (hbound : ∀ (k : Fin K), ∀ π ∈ policySet, ∀ O, |g k π O| ≤ B) :
    sSup ((fun π => |pooledCrossfitProcess P g assign sample π|) ''
      {π | π ∈ policySet ∧ lawRegret P π ≤ r})
      ≤ ∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
          foldLocalizedSup P g assign policySet r k sample := by
  classical
  let loc : Set (Policy 𝒳) := {π | π ∈ policySet ∧ lawRegret P π ≤ r}
  let w : Fin K → ℝ := fun k => (Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact div_nonneg (by positivity) (by exact_mod_cast hn.le)
  have hfold_nonneg : ∀ k, 0 ≤ foldLocalizedSup P g assign policySet r k sample := by
    intro k
    apply Real.sSup_nonneg
    rintro y ⟨π, hπ, rfl⟩
    exact abs_nonneg _
  have hR_nonneg : 0 ≤ ∑ k : Fin K, w k * foldLocalizedSup P g assign policySet r k sample := by
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nonneg k) (hfold_nonneg k))
  apply Real.sSup_le ?_ hR_nonneg
  rintro y ⟨π, hπloc, rfl⟩
  have hpool := pooledCrossfitProcess_eq_sum_fold P g assign sample π hn
  have hbdd_fold : ∀ k : Fin K,
      BddAbove ((fun π => |foldCenteredProcess P g assign k sample π|) '' loc) := by
    intro k
    refine ⟨2 * B, ?_⟩
    rintro y ⟨π, hπ, rfl⟩
    exact abs_foldCenteredProcess_le P g assign k sample π B hB (hbound k π hπ.1)
  calc
    |pooledCrossfitProcess P g assign sample π|
        = |∑ k : Fin K, w k * foldCenteredProcess P g assign k sample π| := by
            rw [hpool]
    _ ≤ ∑ k : Fin K, |w k * foldCenteredProcess P g assign k sample π| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin K, w k * |foldCenteredProcess P g assign k sample π| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul, abs_of_nonneg (hw_nonneg k)]
    _ ≤ ∑ k : Fin K, w k * foldLocalizedSup P g assign policySet r k sample := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left
              (le_csSup (hbdd_fold k) ⟨π, hπloc, rfl⟩) (hw_nonneg k)

lemma pooledOffsetSup_pointwise_le_sum_fold {n K dPi : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (B : ℝ) (sample : Fin n → Observation 𝒳)
    (hpc : PolicyClassVC policySet dPi) (hwf : WellFormedLaw P)
    (hbdd : BoundedOutcome P) [IsProbabilityMeasure P.dataMeasure]
    (hn : 0 < n) (hB : 0 ≤ B)
    (hbound : ∀ (k : Fin K), ∀ π ∈ policySet, ∀ O, |g k π O| ≤ B) :
    sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P g assign sample π| - lawRegret P π / 4))
      '' policySet)
      ≤ ∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
          foldOffsetSup P g assign policySet k sample := by
  classical
  let w : Fin K → ℝ := fun k => (Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact div_nonneg (by positivity) (by exact_mod_cast hn.le)
  have hw_sum : (∑ k : Fin K, w k) = 1 := sum_foldWeights_eq_one assign hn
  have hfold_nonneg : ∀ k, 0 ≤ foldOffsetSup P g assign policySet k sample := by
    intro k
    apply Real.sSup_nonneg
    rintro y ⟨π, hπ, rfl⟩
    exact le_max_left _ _
  have hR_nonneg : 0 ≤ ∑ k : Fin K, w k * foldOffsetSup P g assign policySet k sample := by
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nonneg k) (hfold_nonneg k))
  apply Real.sSup_le ?_ hR_nonneg
  rintro y ⟨π, hπmem, rfl⟩
  have hpool := pooledCrossfitProcess_eq_sum_fold P g assign sample π hn
  have hbdd_fold : ∀ k : Fin K,
      BddAbove ((fun π =>
        max 0 (2 * |foldCenteredProcess P g assign k sample π| - lawRegret P π / 4))
        '' policySet) := by
    intro k
    refine ⟨4 * B + 1, ?_⟩
    rintro y ⟨π, hπ, rfl⟩
    have hfold :
        |foldCenteredProcess P g assign k sample π| ≤ 2 * B :=
      abs_foldCenteredProcess_le P g assign k sample π B hB (hbound k π hπ)
    have hreg : (-4 : ℝ) ≤ lawRegret P π :=
      lawRegret_lower_bound P π hwf hbdd (hpc.1 π hπ)
    have hmain :
        2 * |foldCenteredProcess P g assign k sample π| - lawRegret P π / 4
          ≤ 4 * B + 1 := by
      nlinarith
    have hnon : 0 ≤ 4 * B + 1 := by nlinarith
    exact max_le hnon hmain
  calc
    max 0 (2 * |pooledCrossfitProcess P g assign sample π| - lawRegret P π / 4)
        = max 0 (2 * |∑ k : Fin K, w k * foldCenteredProcess P g assign k sample π|
            - lawRegret P π / 4) := by
          rw [hpool]
    _ ≤ ∑ k : Fin K, w k *
          max 0 (2 * |foldCenteredProcess P g assign k sample π| - lawRegret P π / 4) :=
        max_weighted_abs_sub_le_sum w
          (fun k => foldCenteredProcess P g assign k sample π)
          (lawRegret P π) hw_nonneg hw_sum
    _ ≤ ∑ k : Fin K, w k * foldOffsetSup P g assign policySet k sample := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (le_csSup (hbdd_fold k) ⟨π, hπmem, rfl⟩) (hw_nonneg k)


end CausalSmith.Stat.PolicyRegretMarginOverlap
