/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.DriftBound

/-! Provides localized VC process and cross-fit offset-control helpers. -/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: lem:localized-vc-process-bound
/-- `lem:localized-vc-process-bound`. Fixed-radius localized process bound: for an
i.i.d. sample of size `m`, the EXPECTED localized supremum `E_P Z_m(r)` of the
centered policy-indexed empirical process `(P_m - P) g_π` — with increment envelope
`B` and conditional second moment `≤ C B² P_X(D_π)` — is bounded by
`C B m^{-1/2} r^{α/(2+2α)}(log m)^p`, combining `margin_localization` with the
discharged finite-VC envelope. -/
lemma localized_vc_process_bound (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi : ℕ)
    (hpc : PolicyClassVC policySet dPi)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P)
    -- `ass:vc-localized-envelope` (atomic empirical-process assumption), supplied
    -- from the `upperRisk` domain conjunct at the consumer; threaded, not discharged.
    (henv : VCLocalizedEnvelope P policySet α) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ (m : ℕ) (B r : ℝ) (g : Policy 𝒳 → Observation 𝒳 → ℝ),
        PolicyCompatible g →
        0 < m → 0 ≤ B → 0 ≤ r →
        (∀ π ∈ policySet, ∀ O, |g π O| ≤ B) →
        (∀ π ∈ policySet,
          ∫ O, (g π O) ^ 2 ∂P.dataMeasure
            ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
        expectedLocalizedSup (m := m) P g policySet r
          ≤ C * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
              * (Real.log m) ^ p := by
  simpa [VCLocalizedEnvelope, expectedLocalizedSup, centeredEmpProcess]
    using henv

-- @node: lem:crossfit-localized-process-reduction
/-- `lem:crossfit-localized-process-reduction`. Foldwise application plus balanced
fixed-`K` collapse: conditioning on the training folds, each balanced evaluation
fold is i.i.d., so `localized_vc_process_bound` applies foldwise. The conclusion
records BOTH halves of the NL statement: (1) the CONDITIONAL-on-training-folds
foldwise bound — each evaluation-fold centered increment process `g k` has expected
localized supremum bounded at the same rate (this is the i.i.d.-per-fold deliverable
that conditioning on the training fold supplies); and (2) HENCE the unconditional
pooled bound — the pooled cross-fit centered process `pooledCrossfitProcess` (built
from the foldwise increments `g k` via `assign n`) has expected localized supremum
bounded by `C B n^{-1/2} r^{α/(2+2α)}(log n)^p`.

SCOPE (Lean encoding fidelity): this pooled-process reduction is itself
enumeration-independent (it quantifies over a generic increment family `g`, not
the ERM `enum`), but it feeds the upper-bound track
(`crude_localized_master_bound`, `feasible_upper`) which is stated for an
ARBITRARY enumeration-based ERM — Lean OMITS the note's dense `Π₀` enumeration
condition on `enum`. -/
lemma crossfit_localized_process_reduction (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi K : ℕ)
    (assign : (n : ℕ) → Fin n → Fin K)
    (hpc : PolicyClassVC policySet dPi)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P)
    (hK : FixedFoldCount K assign) (hiid : IsIIDSample P)
    -- `ass:vc-localized-envelope`, threaded from the `upperRisk` domain conjunct.
    (henv : VCLocalizedEnvelope P policySet α) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ (n : ℕ) (B r : ℝ) (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ),
        0 < n → 0 ≤ B → 0 ≤ r →
        -- The cross-fit increments factor through `π O.X` (note: `(π-π_⋆)·Γ`), so
        -- they are policy-compatible — the form the localized envelope applies to.
        (∀ k : Fin K, PolicyCompatible (g k)) →
        -- Increment measurability (note's increments are measurable): with the
        -- `PolicyClassVC` countable dense skeleton this makes the localized/offset
        -- `sSup` over `policySet` measurable+integrable (regularity-bookkeeping).
        (∀ (k : Fin K), ∀ π ∈ policySet, Measurable (g k π)) →
        -- regularity gate: empirical-process sSup measurability/integrability
        -- (vdV-Wellner; presupposed by the envelope; deferred Causalean infra,
        -- SUBSTRATE_DEBT).  Pure Bochner regularity, no rate or bound content.
        (hInt_pooledLocalized : Integrable (fun sample : Fin n → Observation 𝒳 =>
          sSup ((fun π => |pooledCrossfitProcess P g (assign n) sample π|) ''
            {π | π ∈ policySet ∧ lawRegret P π ≤ r}))
          (Measure.pi (fun _ : Fin n => P.dataMeasure))) →
        (hInt_foldLocalized : ∀ k : Fin K,
          Integrable (fun sample : foldIndex (assign n) k → Observation 𝒳 =>
            foldLocalizedSubSup P g (assign n) policySet r k sample)
          (Measure.pi (fun _ : foldIndex (assign n) k => P.dataMeasure))) →
        (∀ (k : Fin K), ∀ π ∈ policySet, ∀ O, |g k π O| ≤ B) →
        (∀ (k : Fin K), ∀ π ∈ policySet,
          ∫ O, (g k π O) ^ 2 ∂P.dataMeasure
            ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
        (∀ k : Fin K,
          expectedLocalizedSup (m := n) P (g k) policySet r
            ≤ C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
                * (Real.log n) ^ p) ∧
        expectedPooledLocalizedSup P g (assign n) policySet r
          ≤ C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
              * (Real.log n) ^ p
    := by
  rcases henv with ⟨C0, p0, hC0, hp0, Henv⟩
  let C : ℝ := C0 * (K : ℝ)
  have hKpos : 0 < K := hK.1
  have hKposR : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hC : 0 < C := mul_pos hC0 hKposR
  refine ⟨C, p0, hC, hp0, ?_⟩
  intro n B r g hn hB hr hcompat hmeas hInt_pooledLocalized hInt_foldLocalized
    hbound hsecond
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  have hC0_le_C : C0 ≤ C := by
    dsimp [C]
    have hKge1R : (1 : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hKpos
    nlinarith [hC0, hKge1R]
  have hrate_nonneg :
      0 ≤ B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
          * (Real.log n) ^ p0 := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hn)
    positivity
  constructor
  · intro k
    have hk :=
      Henv n B r (g k) (hcompat k) hn hB hr (hbound k) (hsecond k)
    calc
      expectedLocalizedSup (m := n) P (g k) policySet r
          ≤ C0 * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
              * (Real.log n) ^ p0 := by
            simpa [expectedLocalizedSup, centeredEmpProcess] using hk
      _ ≤ C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
              * (Real.log n) ^ p0 := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_right hC0_le_C hrate_nonneg
  · classical
    let μn : Measure (Fin n → Observation 𝒳) :=
      Measure.pi (fun _ : Fin n => P.dataMeasure)
    let w : Fin K → ℝ :=
      fun k => (Fintype.card (foldIndex (assign n) k) : ℝ) / (n : ℝ)
    let pooled : (Fin n → Observation 𝒳) → ℝ :=
      fun sample =>
        sSup ((fun π => |pooledCrossfitProcess P g (assign n) sample π|) ''
          {π | π ∈ policySet ∧ lawRegret P π ≤ r})
    let folded : Fin K → (Fin n → Observation 𝒳) → ℝ :=
      fun k sample => foldLocalizedSup P g (assign n) policySet r k sample
    have hw_nonneg : ∀ k, 0 ≤ w k := by
      intro k
      exact div_nonneg (by positivity) (by exact_mod_cast hn.le)
    have hInt_fold_full : ∀ k : Fin K, Integrable (folded k) μn := by
      intro k
      have hproj := measurePreserving_foldProjection P (assign n) k
      have hcomp := hproj.integrable_comp_of_integrable
        (g := fun sample : foldIndex (assign n) k → Observation 𝒳 =>
          foldLocalizedSubSup P g (assign n) policySet r k sample)
        (hInt_foldLocalized k)
      simpa [folded, foldLocalizedSup, foldLocalizedSubSup, foldCenteredProcess,
        foldProjection, Function.comp_def] using hcomp
    have hInt_rhs : Integrable
        (fun sample : Fin n → Observation 𝒳 => ∑ k : Fin K, w k * folded k sample) μn := by
      simpa using
        (integrable_finset_sum (s := Finset.univ)
          (f := fun k sample => w k * folded k sample)
          (fun k _ => (hInt_fold_full k).const_mul (w k)))
    have hpoint :
        ∀ sample : Fin n → Observation 𝒳,
          pooled sample ≤ ∑ k : Fin K, w k * folded k sample := by
      intro sample
      simpa [pooled, folded, w] using
        pooledLocalizedSup_pointwise_le_sum_fold P g (assign n) policySet r B sample
          hn hB hbound
    have hmono :
        ∫ sample, pooled sample ∂μn
          ≤ ∫ sample, (∑ k : Fin K, w k * folded k sample) ∂μn :=
      integral_mono hInt_pooledLocalized hInt_rhs hpoint
    let radiusRate : ℝ := r ^ (α / (2 + 2 * α))
    let base : ℝ :=
      C0 * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * radiusRate * (Real.log (n : ℝ)) ^ p0
    have hbase_nonneg : 0 ≤ base := by
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hn)
      positivity
    have hfold_term_le :
        ∀ k : Fin K, w k * (∫ sample, folded k sample ∂μn) ≤ base := by
      intro k
      let m := Fintype.card (foldIndex (assign n) k)
      by_cases hm0 : m = 0
      · have hwzero : w k = 0 := by simp [w, m, hm0]
        simp [hwzero, hbase_nonneg]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hmn : m ≤ n := by
          simpa [m] using foldIndex_card_le (assign n) k
        have heq :
            ∫ sample, folded k sample ∂μn =
              expectedLocalizedSup (m := m) P (g k) policySet r := by
          simpa [folded, μn, m] using
            integral_foldLocalizedSup_eq_expected P g (assign n) policySet r k hmpos
              (hInt_foldLocalized k)
        have henvk :=
          Henv m B r (g k) (hcompat k) hmpos hB hr (hbound k) (hsecond k)
        have hfold_le :
            ∫ sample, folded k sample ∂μn
              ≤ C0 * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * radiusRate *
                  (Real.log (m : ℝ)) ^ p0 := by
          rw [heq]
          simpa [expectedLocalizedSup, centeredEmpProcess, radiusRate, m] using henvk
        have hmul_le :
            w k * (∫ sample, folded k sample ∂μn)
              ≤ w k *
                (C0 * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * radiusRate *
                  (Real.log (m : ℝ)) ^ p0) :=
          mul_le_mul_of_nonneg_left hfold_le (hw_nonneg k)
        have hweight := fold_weight_mul_inv_sqrt_le hmpos hmn
        have hlog := log_nat_rpow_le hmpos hmn hp0
        have hweight_nonneg :
            0 ≤ ((m : ℝ) / (n : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
          positivity
        have hlogm_nonneg : 0 ≤ (Real.log (m : ℝ)) ^ p0 :=
          Real.rpow_nonneg
            (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hmpos)) p0
        have hn_half_nonneg : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          positivity
        have hsize_core :
            (((m : ℝ) / (n : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ))) *
                (Real.log (m : ℝ)) ^ p0
              ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ p0 :=
          mul_le_mul hweight hlog hlogm_nonneg hn_half_nonneg
        have hconst_nonneg : 0 ≤ C0 * B * radiusRate := by
          positivity
        have hsize :
            w k *
                (C0 * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * radiusRate *
                  (Real.log (m : ℝ)) ^ p0)
              ≤ base := by
          calc
            w k *
                (C0 * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * radiusRate *
                  (Real.log (m : ℝ)) ^ p0)
                =
              (C0 * B * radiusRate) *
                ((((m : ℝ) / (n : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ))) *
                  (Real.log (m : ℝ)) ^ p0) := by
                  simp [w, m]
                  ring
            _ ≤ (C0 * B * radiusRate) *
                ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ p0) :=
                  mul_le_mul_of_nonneg_left hsize_core hconst_nonneg
            _ = base := by
                  simp [base, radiusRate]
                  ring
        exact hmul_le.trans hsize
    calc
      expectedPooledLocalizedSup P g (assign n) policySet r
          = ∫ sample, pooled sample ∂μn := by rfl
      _ ≤ ∫ sample, (∑ k : Fin K, w k * folded k sample) ∂μn := hmono
      _ = ∑ k : Fin K, ∫ sample, w k * folded k sample ∂μn := by
            simpa using
              (integral_finset_sum (s := Finset.univ)
                (f := fun k sample => w k * folded k sample)
                (fun k _ => (hInt_fold_full k).const_mul (w k)))
      _ = ∑ k : Fin K, w k * ∫ sample, folded k sample ∂μn := by
            simp [integral_const_mul]
      _ ≤ ∑ _k : Fin K, base := by
            exact Finset.sum_le_sum (fun k _ => hfold_term_le k)
      _ = C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * radiusRate *
            (Real.log (n : ℝ)) ^ p0 := by
            simp [base, C]
            ring
      _ = C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
            r ^ (α / (2 + 2 * α)) * (Real.log n) ^ p0 := by
            simp [radiusRate]

-- @node: lem:crossfit-localized-offset-control
/-- `lem:crossfit-localized-offset-control`. Pooled offset positive-part control:
conditioning on training folds and applying the discharged offset envelope
foldwise, the EXPECTED pooled cross-fit offset supremum
`E_P sup_π {2|G_cf(π)| - R_P(π)/4}_+` is bounded by `C (B²/n)^{A_α}(log n)^p`,
`A_α=(1+α)/(2+α)`. Stochastic input to `localized_vc_self_bound`; must not depend
on it. -/
lemma crossfit_localized_offset_control
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi K : ℕ)
    (assign : (n : ℕ) → Fin n → Fin K)
    (hpc : PolicyClassVC policySet dPi) (hK : FixedFoldCount K assign)
    -- `ass:vc-localized-offset-envelope`, in its uniform class-level form.
    (hoffU : VCLocalizedOffsetEnvelopeUnif policySet α) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ (P : ObservedLaw 𝒳),
        MarginTail P Cm α u0 → ZeroEffectRegular P policySet →
        IsIIDSample P → WellFormedLaw P → BoundedOutcome P →
          ∀ (n : ℕ) (B : ℝ) (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ),
            0 < n → 0 ≤ B →
            -- The cross-fit increments factor through `π O.X` (note: `(π-π_⋆)·Γ`), so
            -- they are policy-compatible — the form the localized offset envelope applies to.
            (∀ k : Fin K, PolicyCompatible (g k)) →
            -- Increment measurability (note's increments are measurable): with the
            -- `PolicyClassVC` countable dense skeleton this makes the localized/offset
            -- `sSup` over `policySet` measurable+integrable (regularity-bookkeeping).
            (∀ (k : Fin K), ∀ π ∈ policySet, Measurable (g k π)) →
            -- regularity gate: empirical-process sSup measurability/integrability
            -- (vdV-Wellner; presupposed by the envelope; deferred Causalean infra,
            -- SUBSTRATE_DEBT).  Pure Bochner regularity, no rate or bound content.
            (hInt_pooledOffset : Integrable (fun sample : Fin n → Observation 𝒳 =>
              sSup ((fun π =>
                max 0 (2 * |pooledCrossfitProcess P g (assign n) sample π| -
                  lawRegret P π / 4)) '' policySet))
              (Measure.pi (fun _ : Fin n => P.dataMeasure))) →
            (hInt_foldOffset : ∀ k : Fin K,
              Integrable (fun sample : foldIndex (assign n) k → Observation 𝒳 =>
                foldOffsetSubSup P g (assign n) policySet k sample)
              (Measure.pi (fun _ : foldIndex (assign n) k => P.dataMeasure))) →
            (∀ (k : Fin K), ∀ π ∈ policySet, ∀ O, |g k π O| ≤ B) →
            (∀ (k : Fin K), ∀ π ∈ policySet,
              ∫ O, (g k π O) ^ 2 ∂P.dataMeasure
                ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
            expectedPooledOffsetSup P g (assign n) policySet
              ≤ C * (B ^ 2 / (n : ℝ)) ^ ((1 + α) / (2 + α)) * (Real.log n) ^ p
    := by
  rcases hoffU with ⟨C0, p0, hC0, hp0, Hoff⟩
  let C : ℝ := C0 * (K : ℝ)
  have hKpos : 0 < K := hK.1
  have hKposR : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hC : 0 < C := mul_pos hC0 hKposR
  refine ⟨C, p0, hC, hp0, ?_⟩
  intro P hmargin _hze hiid hwf hbdd n B g hn hB hcompat hmeas
    hInt_pooledOffset hInt_foldOffset hbound hsecond
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let μn : Measure (Fin n → Observation 𝒳) :=
    Measure.pi (fun _ : Fin n => P.dataMeasure)
  let A : ℝ := (1 + α) / (2 + α)
  let w : Fin K → ℝ :=
    fun k => (Fintype.card (foldIndex (assign n) k) : ℝ) / (n : ℝ)
  let pooled : (Fin n → Observation 𝒳) → ℝ :=
    fun sample =>
      sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P g (assign n) sample π| -
          lawRegret P π / 4)) '' policySet)
  let folded : Fin K → (Fin n → Observation 𝒳) → ℝ :=
    fun k sample => foldOffsetSup P g (assign n) policySet k sample
  have hα_nonneg : 0 ≤ α := hmargin.1
  have hdenpos : 0 < 2 + α := by linarith
  have hA1 : A ≤ 1 := by
    dsimp [A]
    exact div_le_one_of_le₀ (by linarith) hdenpos.le
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact div_nonneg (by positivity) (by exact_mod_cast hn.le)
  have hInt_fold_full : ∀ k : Fin K, Integrable (folded k) μn := by
    intro k
    have hproj := measurePreserving_foldProjection P (assign n) k
    have hcomp := hproj.integrable_comp_of_integrable
      (g := fun sample : foldIndex (assign n) k → Observation 𝒳 =>
        foldOffsetSubSup P g (assign n) policySet k sample)
      (hInt_foldOffset k)
    simpa [folded, foldOffsetSup, foldOffsetSubSup, foldCenteredProcess,
      foldProjection, Function.comp_def] using hcomp
  have hInt_rhs : Integrable
      (fun sample : Fin n → Observation 𝒳 => ∑ k : Fin K, w k * folded k sample) μn := by
    simpa using
      (integrable_finset_sum (s := Finset.univ)
        (f := fun k sample => w k * folded k sample)
        (fun k _ => (hInt_fold_full k).const_mul (w k)))
  have hpoint :
      ∀ sample : Fin n → Observation 𝒳,
        pooled sample ≤ ∑ k : Fin K, w k * folded k sample := by
    intro sample
    simpa [pooled, folded, w] using
      pooledOffsetSup_pointwise_le_sum_fold P g (assign n) policySet B sample
        hpc hwf hbdd hn hB hbound
  have hmono :
      ∫ sample, pooled sample ∂μn
        ≤ ∫ sample, (∑ k : Fin K, w k * folded k sample) ∂μn :=
    integral_mono hInt_pooledOffset hInt_rhs hpoint
  let base : ℝ := C0 * (B ^ 2 / (n : ℝ)) ^ A * (Real.log (n : ℝ)) ^ p0
  have hbase_nonneg : 0 ≤ base := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hn)
    positivity
  have hfold_term_le :
      ∀ k : Fin K, w k * (∫ sample, folded k sample ∂μn) ≤ base := by
    intro k
    let m := Fintype.card (foldIndex (assign n) k)
    by_cases hm0 : m = 0
    · have hwzero : w k = 0 := by simp [w, m, hm0]
      simp [hwzero, hbase_nonneg]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmn : m ≤ n := by
        simpa [m] using foldIndex_card_le (assign n) k
      have heq :
          ∫ sample, folded k sample ∂μn =
            ∫ sample,
              sSup ((fun π => max 0
                (2 * |centeredEmpProcess P (g k) sample π| - lawRegret P π / 4))
                  '' policySet)
              ∂(Measure.pi (fun _ : Fin m => P.dataMeasure)) := by
        simpa [folded, μn, m] using
          integral_foldOffsetSup_eq_expected P g (assign n) policySet k hmpos
            (hInt_foldOffset k)
      have hoffk :=
        Hoff P m B (g k) (hcompat k) hmpos hB (hbound k) (hsecond k)
      have hfold_le :
          ∫ sample, folded k sample ∂μn
            ≤ C0 * (B ^ 2 / (m : ℝ)) ^ A * (Real.log (m : ℝ)) ^ p0 := by
        rw [heq]
        simpa [centeredEmpProcess, A, m] using hoffk
      have hmul_le :
          w k * (∫ sample, folded k sample ∂μn)
            ≤ w k * (C0 * (B ^ 2 / (m : ℝ)) ^ A *
                (Real.log (m : ℝ)) ^ p0) :=
        mul_le_mul_of_nonneg_left hfold_le (hw_nonneg k)
      have hweight := fold_weight_mul_offset_rpow_le (B := B) (A := A) hmpos hmn hA1
      have hlog := log_nat_rpow_le hmpos hmn hp0
      have hweight_nonneg :
          0 ≤ ((m : ℝ) / (n : ℝ)) * (B ^ 2 / (m : ℝ)) ^ A := by
        positivity
      have hlogm_nonneg : 0 ≤ (Real.log (m : ℝ)) ^ p0 :=
        Real.rpow_nonneg
          (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hmpos)) p0
      have hbase_factor_nonneg : 0 ≤ (B ^ 2 / (n : ℝ)) ^ A := by
        positivity
      have hsize_core :
          (((m : ℝ) / (n : ℝ)) * (B ^ 2 / (m : ℝ)) ^ A) *
              (Real.log (m : ℝ)) ^ p0
            ≤ (B ^ 2 / (n : ℝ)) ^ A * (Real.log (n : ℝ)) ^ p0 :=
        mul_le_mul hweight hlog hlogm_nonneg hbase_factor_nonneg
      have hsize :
          w k * (C0 * (B ^ 2 / (m : ℝ)) ^ A *
              (Real.log (m : ℝ)) ^ p0)
            ≤ base := by
        calc
          w k * (C0 * (B ^ 2 / (m : ℝ)) ^ A *
              (Real.log (m : ℝ)) ^ p0)
              =
            C0 * ((((m : ℝ) / (n : ℝ)) * (B ^ 2 / (m : ℝ)) ^ A) *
              (Real.log (m : ℝ)) ^ p0) := by
                simp [w, m]
                ring
          _ ≤ C0 * ((B ^ 2 / (n : ℝ)) ^ A * (Real.log (n : ℝ)) ^ p0) :=
                mul_le_mul_of_nonneg_left hsize_core hC0.le
          _ = base := by
                simp [base]
                ring
      exact hmul_le.trans hsize
  calc
    expectedPooledOffsetSup P g (assign n) policySet
        = ∫ sample, pooled sample ∂μn := by rfl
    _ ≤ ∫ sample, (∑ k : Fin K, w k * folded k sample) ∂μn := hmono
    _ = ∑ k : Fin K, ∫ sample, w k * folded k sample ∂μn := by
          simpa using
            (integral_finset_sum (s := Finset.univ)
              (f := fun k sample => w k * folded k sample)
              (fun k _ => (hInt_fold_full k).const_mul (w k)))
    _ = ∑ k : Fin K, w k * ∫ sample, folded k sample ∂μn := by
          simp [integral_const_mul]
    _ ≤ ∑ _k : Fin K, base := by
          exact Finset.sum_le_sum (fun k _ => hfold_term_le k)
    _ = C * (B ^ 2 / (n : ℝ)) ^ A * (Real.log (n : ℝ)) ^ p0 := by
          simp [base, C]
          ring
    _ = C * (B ^ 2 / (n : ℝ)) ^ ((1 + α) / (2 + α)) * (Real.log n) ^ p0 := by
          simp [A]


end CausalSmith.Stat.PolicyRegretMarginOverlap
