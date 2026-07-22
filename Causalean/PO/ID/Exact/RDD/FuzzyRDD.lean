/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fuzzy regression-discontinuity identification

Implements the regression-representative formal counterpart of
def:po-fuzzy-rdd-system, def:po-fuzzy-rdd-assumptions, and prop:po-fuzzy-rdd
from Basic Concepts.tex.

The textbook fuzzy RDD estimand is the cutoff-local LATE.  In this file, as in
`SharpRDD.lean`, the formal target is stated using chosen regression-function
representatives:

    τ_FRD(c) = (μ_Y(1,c) - μ_Y(0,c)) / (μ_D(1,c) - μ_D(0,c)).

Here `μ_Y(z, ·)` represents `E[Y(D(z)) | X = ·]` and `μ_D(z, ·)` represents
`E[D(z) | X = ·]`.  Local exclusion is encoded by the available outcome
potential outcomes `Y(d)`.  The LATE bridge in this file assumes global a.s.
monotonicity, `D(0) ≤ D(1)`, which is stronger than the cutoff-neighborhood
monotonicity used in some textbook fuzzy RDD statements; the
regression-representative Wald identity itself does not use monotonicity
directly.

Two shared helper modules supply the heavy lifting:

* `Causalean.PO.Analysis.Regression` provides the `IsRegressionFunction` predicate and its
  pushforward-integrability lemma.
* `Causalean.PO.ID.Exact.RDD.RDDLimits` provides the one-sided limit
  identification engine (`oneSidedLimit_eq_right`/`_left`) used to convert
  a.e. agreement of observable and latent regressions on a half-line into
  pointwise equality of one-sided limits at the cutoff.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Analysis.Regression
import Causalean.PO.ID.Exact.RDD.RDDLimits
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Order.Basic

/-! # Fuzzy Regression Discontinuity

This file formalizes fuzzy regression-discontinuity identification using
regression-function representatives at the cutoff. `POFuzzyRDDSystem` defines
the running variable, cutoff indicator, binary treatment, outcome, potential
treatment `DofZ`, potential outcome `YofD`, induced outcome `YofDofZ`, and the
complier-weighted outcome difference `YdiffComplier`.

The `Assumptions` bundle records consistency, deterministic cutoff eligibility,
local treatment monotonicity near the cutoff, latent and observable regression
representatives, one-sided support, observable one-sided limits, a complier
outcome-difference representative, and a nonzero first-stage jump. The main
definitions are `tau_FRD` and `tau_LATE`. Theorems `nuD_right_limit_eq`,
`nuD_left_limit_eq`, `nuY_right_limit_eq`, and `nuY_left_limit_eq` identify the
observable one-sided limits with latent regression values, and
`frd_identification` identifies the observable cutoff Wald ratio. The theorem
`tau_late_identification` gives the separate global-monotonicity bridge from
the fuzzy RDD ratio to the cutoff representative complier-effect ratio. -/

namespace Causalean
namespace PO

open Filter MeasureTheory
open scoped Topology

/-- A fuzzy regression-discontinuity model in the potential-outcome framework.
A unit has a continuous running variable `X`, an above-cutoff indicator `Z`
(whether `X` exceeds the cutoff `c`), a binary treatment `D` whose take-up
probability jumps — but does not jump all the way from 0 to 1 — at the cutoff,
and a real outcome `Y`. The cutoff effect on the outcome divided by the cutoff
jump in treatment identifies the cutoff-local LATE (`def:po-fuzzy-rdd-system`). -/
structure POFuzzyRDDSystem (P : POSystem) where
  /-- Running (forcing) variable `X`. -/
  Xvar : POVar P ℝ
  /-- Above-cutoff indicator `Z = 1{X ≥ c}`. -/
  Zvar : POVar P Bool
  /-- Binary treatment `D`. -/
  Dvar : POVar P Bool
  /-- Real outcome `Y`. -/
  Yvar : POVar P ℝ
  /-- Cutoff value of the running variable. -/
  c : ℝ
  hYD : Yvar.v ≠ Dvar.v
  hZD : Zvar.v ≠ Dvar.v
  hDY : Dvar.v ≠ Yvar.v

namespace POFuzzyRDDSystem

variable {P : POSystem} (S : POFuzzyRDDSystem P)

/-- Factual running variable `X`. -/
noncomputable def factualX : P.Ω → ℝ := S.Xvar.factual

/-- Factual cutoff-eligibility instrument `Z`. -/
noncomputable def factualZ : P.Ω → Bool := S.Zvar.factual

/-- Factual treatment `D`. -/
noncomputable def factualD : P.Ω → Bool := S.Dvar.factual

/-- Factual outcome `Y`. -/
noncomputable def factualY : P.Ω → ℝ := S.Yvar.factual

/-- Instrument-specific potential treatment `D(z)`. -/
noncomputable def DofZ (z : Bool) : P.Ω → Bool :=
  S.Dvar.cfUnder S.Zvar z

/-- Treatment-specific potential outcome `Y(d)`. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ :=
  S.Yvar.cfUnder S.Dvar d

/-- Outcome under the treatment induced by instrument value `z`, `Y(D(z))`. -/
noncomputable def YofDofZ (z : Bool) : P.Ω → ℝ :=
  fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω

/-- Y-difference weighted by the complier indicator `1_{D(1)=1, D(0)=0}`.
Equals `Y(D(1)) − Y(D(0))` a.e. under monotonicity; used in the LATE bridge. -/
noncomputable def YdiffComplier : P.Ω → ℝ :=
  fun ω => (S.YofD true ω - S.YofD false ω) *
    if S.DofZ true ω = true ∧ S.DofZ false ω = false then 1 else 0

/-- The factual running variable is measurable. -/
lemma measurable_factualX : Measurable S.factualX := S.Xvar.measurable_factual
/-- The factual cutoff-eligibility instrument is measurable. -/
lemma measurable_factualZ : Measurable S.factualZ := S.Zvar.measurable_factual
/-- The factual treatment is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.Dvar.measurable_factual
/-- The factual outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.Yvar.measurable_factual

/-- The instrument-specific potential treatment is measurable. -/
lemma measurable_DofZ (z : Bool) : Measurable (S.DofZ z) :=
  S.Dvar.measurable_cfUnder S.Zvar z

/-- The treatment-specific potential outcome is measurable. -/
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.Yvar.measurable_cfUnder S.Dvar d

/-- The outcome under the instrument-induced treatment is measurable. -/
lemma measurable_YofDofZ (z : Bool) : Measurable (S.YofDofZ z) := by
  unfold YofDofZ
  exact Measurable.ite (S.measurable_DofZ z (MeasurableSet.singleton true))
    (S.measurable_YofD true) (S.measurable_YofD false)

/-- The complier-weighted outcome difference is measurable. -/
lemma measurable_YdiffComplier : Measurable S.YdiffComplier := by
  unfold YdiffComplier
  apply Measurable.mul
  · exact (S.measurable_YofD true).sub (S.measurable_YofD false)
  · exact Measurable.ite
      ((S.measurable_DofZ true (MeasurableSet.singleton true)).inter
        (S.measurable_DofZ false (MeasurableSet.singleton false)))
      measurable_const measurable_const

/-- Factual eligibility event `{Z = z}`. -/
def zEvent (z : Bool) : Set P.Ω := S.Zvar.event z

/-- The factual eligibility event is measurable. -/
lemma measurableSet_zEvent (z : Bool) : MeasurableSet (S.zEvent z) :=
  S.Zvar.measurableSet_event z

/-- The fuzzy RDD assumption bundle records consistency, deterministic
cutoff eligibility, cutoff-neighborhood monotonicity of treatment take-up, regression
representatives for latent and observable treatment and outcome variables,
one-sided support near the cutoff, and a nonzero first-stage jump.

The classical local-exclusion clause is represented by using only `Y(d)`
potential outcomes, rather than separate direct responses `Y(z,d)`.  The
monotonicity field is local to a neighborhood of the cutoff, matching the
standard fuzzy-RDD condition.  The final field phrases the first stage as a
nonzero jump of the latent treatment regression representatives at `c`; by the
limit-identification lemmas below, this is equivalent to the nonzero denominator
in the observable Wald ratio. -/
structure Assumptions (S : POFuzzyRDDSystem P) where
  consistency : P.Consistency
  cutoffEligibility : ∀ᵐ ω ∂P.μ, S.factualZ ω ↔ S.c ≤ S.factualX ω
  /-- In a neighborhood of the cutoff, units who would take treatment below the
  cutoff would also take treatment above the cutoff, up to a null set. -/
  monotonicity :
    ∃ ε > (0 : ℝ), ∀ᵐ ω ∂P.μ,
      |S.factualX ω - S.c| < ε → S.DofZ false ω = true → S.DofZ true ω = true
  muD : Bool → ℝ → ℝ
  muY : Bool → ℝ → ℝ
  nuD : ℝ → ℝ
  nuY : ℝ → ℝ
  muD_isReg : ∀ z, IsRegressionFunction P.μ S.factualX
    (fun ω => ((S.DofZ z ω).toNat : ℝ)) (muD z)
  muY_isReg : ∀ z, IsRegressionFunction P.μ S.factualX (S.YofDofZ z) (muY z)
  nuD_isReg : IsRegressionFunction P.μ S.factualX
    (fun ω => ((S.factualD ω).toNat : ℝ)) nuD
  nuY_isReg : IsRegressionFunction P.μ S.factualX S.factualY nuY
  muD_continuousAt : ∀ z, ContinuousAt (muD z) S.c
  muY_continuousAt : ∀ z, ContinuousAt (muY z) S.c
  support_right : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo S.c (S.c + ε)) ≠ 0
  support_left : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo (S.c - ε) S.c) ≠ 0
  nuD_right_limit_exists : ∃ L : ℝ, Tendsto nuD (𝓝[>] S.c) (𝓝 L)
  nuD_left_limit_exists : ∃ L : ℝ, Tendsto nuD (𝓝[<] S.c) (𝓝 L)
  nuY_right_limit_exists : ∃ L : ℝ, Tendsto nuY (𝓝[>] S.c) (𝓝 L)
  nuY_left_limit_exists : ∃ L : ℝ, Tendsto nuY (𝓝[<] S.c) (𝓝 L)
  mu_Ydiff_complier : ℝ → ℝ
  mu_Ydiff_complier_isReg : IsRegressionFunction P.μ S.factualX
    S.YdiffComplier mu_Ydiff_complier
  mu_Ydiff_complier_continuousAt : ContinuousAt mu_Ydiff_complier S.c
  firstStageJump : muD true S.c - muD false S.c ≠ 0

/-- Cutoff-local fuzzy RDD Wald estimand in regression-representative form. -/
noncomputable def tau_FRD (hA : S.Assumptions) : ℝ :=
  (hA.muY true S.c - hA.muY false S.c) /
    (hA.muD true S.c - hA.muD false S.c)

/-- Cutoff-local complier-effect ratio in regression-representative form.
It divides the complier outcome-difference representative at the cutoff by the
first-stage jump; `tau_late_identification` connects this ratio to `tau_FRD`
under the fuzzy-RDD assumptions. -/
noncomputable def tau_LATE (hA : S.Assumptions) : ℝ :=
  hA.mu_Ydiff_complier S.c / (hA.muD true S.c - hA.muD false S.c)

/-- The right-hand treatment limit is the selected limit at the cutoff of the
observable treatment regression as the running variable approaches from above. -/
noncomputable def nuD_right_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuD_right_limit_exists

/-- The left-hand treatment limit is the selected limit at the cutoff of the
observable treatment regression as the running variable approaches from below. -/
noncomputable def nuD_left_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuD_left_limit_exists

/-- The right-hand outcome limit is the selected limit at the cutoff of the
observable outcome regression as the running variable approaches from above. -/
noncomputable def nuY_right_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuY_right_limit_exists

/-- The left-hand outcome limit is the selected limit at the cutoff of the
observable outcome regression as the running variable approaches from below. -/
noncomputable def nuY_left_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuY_left_limit_exists

/-- The chosen right-hand treatment-regression limit is a genuine right-hand
limit at the cutoff. -/
lemma tendsto_nuD_right_limit (hA : S.Assumptions) :
    Tendsto hA.nuD (𝓝[>] S.c) (𝓝 (S.nuD_right_limit hA)) :=
  Classical.choose_spec hA.nuD_right_limit_exists

/-- The chosen left-hand treatment-regression limit is a genuine left-hand limit
at the cutoff. -/
lemma tendsto_nuD_left_limit (hA : S.Assumptions) :
    Tendsto hA.nuD (𝓝[<] S.c) (𝓝 (S.nuD_left_limit hA)) :=
  Classical.choose_spec hA.nuD_left_limit_exists

/-- The chosen right-hand outcome-regression limit is a genuine right-hand limit
at the cutoff. -/
lemma tendsto_nuY_right_limit (hA : S.Assumptions) :
    Tendsto hA.nuY (𝓝[>] S.c) (𝓝 (S.nuY_right_limit hA)) :=
  Classical.choose_spec hA.nuY_right_limit_exists

/-- The chosen left-hand outcome-regression limit is a genuine left-hand limit
at the cutoff. -/
lemma tendsto_nuY_left_limit (hA : S.Assumptions) :
    Tendsto hA.nuY (𝓝[<] S.c) (𝓝 (S.nuY_left_limit hA)) :=
  Classical.choose_spec hA.nuY_left_limit_exists

private lemma aemeasurable_factualX (S : POFuzzyRDDSystem P) :
    AEMeasurable S.factualX P.μ := S.measurable_factualX.aemeasurable

/-! ### D-side bridges -/

private lemma factualD_eq_DofZ_on_zEvent
    (hC : P.Consistency) (z : Bool) :
    ∀ ω ∈ S.zEvent z, S.factualD ω = S.DofZ z ω := by
  intro ω hω
  exact (POVar.cf_eq_factual_on_event hC S.Dvar S.Zvar z S.hZD.symm hω).symm

private lemma factualD_eq_DofZ_true_ae_restrict_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (fun ω => ((S.factualD ω).toNat : ℝ))
      =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)]
        fun ω => ((S.DofZ true ω).toNat : ℝ) := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.c ≤ S.factualX ω := hAsub hωA
  have hZprop : S.factualZ ω := hcut.mpr hx
  have hZ : S.factualZ ω = true := by
    cases hZω : S.factualZ ω <;> simp_all
  rw [S.factualD_eq_DofZ_on_zEvent hA.consistency true ω hZ]

private lemma factualD_eq_DofZ_false_ae_restrict_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (fun ω => ((S.factualD ω).toNat : ℝ))
      =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)]
        fun ω => ((S.DofZ false ω).toNat : ℝ) := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.factualX ω < S.c := hAsub hωA
  have hnotZ : ¬ S.factualZ ω := by
    intro hZ
    exact (not_le_of_gt hx) (hcut.mp hZ)
  have hZ : S.factualZ ω = false := by
    cases hZω : S.factualZ ω <;> simp_all
  rw [S.factualD_eq_DofZ_on_zEvent hA.consistency false ω hZ]

private lemma integral_factualD_eq_DofZ_true_on_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ true ω).toNat : ℝ) ∂P.μ :=
  integral_congr_ae (S.factualD_eq_DofZ_true_ae_restrict_Ici hA hAsub hAmeas)

private lemma integral_factualD_eq_DofZ_false_on_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ false ω).toNat : ℝ) ∂P.μ :=
  integral_congr_ae (S.factualD_eq_DofZ_false_ae_restrict_Iio hA hAsub hAmeas)

private lemma regression_integral_bridge_D_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muD true (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ :=
          (hA.nuD_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ true ω).toNat : ℝ) ∂P.μ :=
          S.integral_factualD_eq_DofZ_true_on_Ici hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muD true (S.factualX ω) ∂P.μ :=
          (hA.muD_isReg true).integral_preimage_eq A hAmeas

private lemma regression_integral_bridge_D_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muD false (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ :=
          (hA.nuD_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ false ω).toNat : ℝ) ∂P.μ :=
          S.integral_factualD_eq_DofZ_false_on_Iio hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muD false (S.factualX ω) ∂P.μ :=
          (hA.muD_isReg false).integral_preimage_eq A hAmeas

/-! ### Y-side bridges -/

private lemma factualY_eq_YofDofZ_on_zEvent
    (hC : P.Consistency) (z : Bool) :
    ∀ ω ∈ S.zEvent z, S.factualY ω = S.YofDofZ z ω := by
  intro ω hω
  calc
    S.factualY ω = S.YofD (S.factualD ω) ω :=
      POVar.factual_eq_cfUnder_self_selected hC S.Yvar S.Dvar S.hDY.symm ω
    _ = S.YofD (S.DofZ z ω) ω := by
      rw [S.factualD_eq_DofZ_on_zEvent hC z ω hω]
    _ = S.YofDofZ z ω := by
      unfold YofDofZ
      cases S.DofZ z ω <;> rfl

private lemma factualY_eq_YofDofZ_true_ae_restrict_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofDofZ true := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.c ≤ S.factualX ω := hAsub hωA
  have hZprop : S.factualZ ω := hcut.mpr hx
  have hZ : S.factualZ ω = true := by
    cases hZω : S.factualZ ω <;> simp_all
  exact S.factualY_eq_YofDofZ_on_zEvent hA.consistency true ω hZ

private lemma factualY_eq_YofDofZ_false_ae_restrict_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofDofZ false := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.factualX ω < S.c := hAsub hωA
  have hnotZ : ¬ S.factualZ ω := by
    intro hZ
    exact (not_le_of_gt hx) (hcut.mp hZ)
  have hZ : S.factualZ ω = false := by
    cases hZω : S.factualZ ω <;> simp_all
  exact S.factualY_eq_YofDofZ_on_zEvent hA.consistency false ω hZ

private lemma integral_factualY_eq_YofDofZ_true_on_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ true ω ∂P.μ :=
  integral_congr_ae (S.factualY_eq_YofDofZ_true_ae_restrict_Ici hA hAsub hAmeas)

private lemma integral_factualY_eq_YofDofZ_false_on_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ false ω ∂P.μ :=
  integral_congr_ae (S.factualY_eq_YofDofZ_false_ae_restrict_Iio hA hAsub hAmeas)

private lemma regression_integral_bridge_Y_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muY true (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nuY_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ true ω ∂P.μ :=
          S.integral_factualY_eq_YofDofZ_true_on_Ici hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muY true (S.factualX ω) ∂P.μ :=
          (hA.muY_isReg true).integral_preimage_eq A hAmeas

private lemma regression_integral_bridge_Y_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muY false (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nuY_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ false ω ∂P.μ :=
          S.integral_factualY_eq_YofDofZ_false_on_Iio hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muY false (S.factualX ω) ∂P.μ :=
          (hA.muY_isReg false).integral_preimage_eq A hAmeas

/-! ### A.e. agreement of observable and latent regressions on half-lines

A single generic helper `aeEq_pushforward_of_bridge` does the work: given two
regression representatives `ν`, `μ` over the same factual `X` and a slice-wise
integral bridge on a measurable half-line `H`, it deduces `ν =ᵐ[π.restrict H] μ`
where `π = P.μ.map S.factualX`. -/

private lemma aeEq_pushforward_of_bridge
    {ν μ : ℝ → ℝ} {gν gμ : P.Ω → ℝ} {H : Set ℝ}
    (hν : IsRegressionFunction P.μ S.factualX gν ν)
    (hμ : IsRegressionFunction P.μ S.factualX gμ μ)
    (hH : MeasurableSet H)
    (h_bridge : ∀ {A : Set ℝ}, A ⊆ H → MeasurableSet A →
      (∫ ω in S.factualX ⁻¹' A, gν ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, gμ ω ∂P.μ) :
    ν =ᵐ[(P.μ.map S.factualX).restrict H] μ := by
  set π := P.μ.map S.factualX with hπ
  set ρ := π.restrict H with hρ
  have hInt_ν : Integrable ν ρ :=
    (hν.integrable_pushforward S.aemeasurable_factualX).restrict
  have hInt_μ : Integrable μ ρ :=
    (hμ.integrable_pushforward S.aemeasurable_factualX).restrict
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    ν μ hInt_ν hInt_μ ?_
  intro s hs _
  have hslice : MeasurableSet (s ∩ H) := hs.inter hH
  have hsub : s ∩ H ⊆ H := Set.inter_subset_right
  -- Pushforward setIntegral identities on the slice s ∩ H.
  have hν_pull :
      (∫ x in s ∩ H, ν x ∂π) = ∫ ω in S.factualX ⁻¹' (s ∩ H), ν (S.factualX ω) ∂P.μ :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := ν) hslice
      hν.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hμ_pull :
      (∫ x in s ∩ H, μ x ∂π) = ∫ ω in S.factualX ⁻¹' (s ∩ H), μ (S.factualX ω) ∂P.μ :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := μ) hslice
      hμ.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hν_reg :
      (∫ ω in S.factualX ⁻¹' (s ∩ H), gν ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' (s ∩ H), ν (S.factualX ω) ∂P.μ :=
    hν.integral_preimage_eq (s ∩ H) hslice
  have hμ_reg :
      (∫ ω in S.factualX ⁻¹' (s ∩ H), gμ ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' (s ∩ H), μ (S.factualX ω) ∂P.μ :=
    hμ.integral_preimage_eq (s ∩ H) hslice
  have h_bridge' :
      (∫ ω in S.factualX ⁻¹' (s ∩ H), gν ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' (s ∩ H), gμ ω ∂P.μ :=
    h_bridge hsub hslice
  have h_restrict_ν : (∫ x in s, ν x ∂ρ) = ∫ x in s ∩ H, ν x ∂π := by
    rw [hρ, Measure.restrict_restrict hs]
  have h_restrict_μ : (∫ x in s, μ x ∂ρ) = ∫ x in s ∩ H, μ x ∂π := by
    rw [hρ, Measure.restrict_restrict hs]
  rw [h_restrict_ν, h_restrict_μ, hν_pull, hμ_pull, ← hν_reg, ← hμ_reg, h_bridge']

private lemma nuD_eq_muD_true_ae_restrict_Ici (hA : S.Assumptions) :
    hA.nuD =ᵐ[(P.μ.map S.factualX).restrict (Set.Ici S.c)] hA.muD true :=
  S.aeEq_pushforward_of_bridge hA.nuD_isReg (hA.muD_isReg true)
    measurableSet_Ici
    (fun {_A} hAsub hAmeas =>
      S.integral_factualD_eq_DofZ_true_on_Ici hA hAsub hAmeas)

private lemma nuD_eq_muD_false_ae_restrict_Iio (hA : S.Assumptions) :
    hA.nuD =ᵐ[(P.μ.map S.factualX).restrict (Set.Iio S.c)] hA.muD false :=
  S.aeEq_pushforward_of_bridge hA.nuD_isReg (hA.muD_isReg false)
    measurableSet_Iio
    (fun {_A} hAsub hAmeas =>
      S.integral_factualD_eq_DofZ_false_on_Iio hA hAsub hAmeas)

private lemma nuY_eq_muY_true_ae_restrict_Ici (hA : S.Assumptions) :
    hA.nuY =ᵐ[(P.μ.map S.factualX).restrict (Set.Ici S.c)] hA.muY true :=
  S.aeEq_pushforward_of_bridge hA.nuY_isReg (hA.muY_isReg true)
    measurableSet_Ici
    (fun {_A} hAsub hAmeas =>
      S.integral_factualY_eq_YofDofZ_true_on_Ici hA hAsub hAmeas)

private lemma nuY_eq_muY_false_ae_restrict_Iio (hA : S.Assumptions) :
    hA.nuY =ᵐ[(P.μ.map S.factualX).restrict (Set.Iio S.c)] hA.muY false :=
  S.aeEq_pushforward_of_bridge hA.nuY_isReg (hA.muY_isReg false)
    measurableSet_Iio
    (fun {_A} hAsub hAmeas =>
      S.integral_factualY_eq_YofDofZ_false_on_Iio hA hAsub hAmeas)

/-! ### Limits of observable regressions at the cutoff

Thin wrappers around the generic engine in
`Causalean.PO.RDDLimits` (`oneSidedLimit_eq_right`/`_left`).  Each lemma combines
the half-line a.e. agreement (proved above) with the corresponding continuity
and support hypotheses from the `Assumptions` bundle. -/

/-- Any right-hand observable treatment-regression limit at the cutoff equals
the treated latent treatment regression there. -/
theorem nuD_right_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuD (𝓝[>] S.c) (𝓝 L)) :
    L = hA.muD true S.c :=
  RDDLimits.oneSidedLimit_eq_right
    (S.nuD_eq_muD_true_ae_restrict_Ici hA)
    (hA.muD_continuousAt true)
    hA.support_right
    h

/-- Any left-hand observable treatment-regression limit at the cutoff equals the
untreated latent treatment regression there. -/
theorem nuD_left_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuD (𝓝[<] S.c) (𝓝 L)) :
    L = hA.muD false S.c :=
  RDDLimits.oneSidedLimit_eq_left
    (S.nuD_eq_muD_false_ae_restrict_Iio hA)
    (hA.muD_continuousAt false)
    hA.support_left
    h

/-- Any right-hand observable outcome-regression limit at the cutoff equals the
treated latent outcome regression there. -/
theorem nuY_right_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuY (𝓝[>] S.c) (𝓝 L)) :
    L = hA.muY true S.c :=
  RDDLimits.oneSidedLimit_eq_right
    (S.nuY_eq_muY_true_ae_restrict_Ici hA)
    (hA.muY_continuousAt true)
    hA.support_right
    h

/-- Any left-hand observable outcome-regression limit at the cutoff equals the
untreated latent outcome regression there. -/
theorem nuY_left_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuY (𝓝[<] S.c) (𝓝 L)) :
    L = hA.muY false S.c :=
  RDDLimits.oneSidedLimit_eq_left
    (S.nuY_eq_muY_false_ae_restrict_Iio hA)
    (hA.muY_continuousAt false)
    hA.support_left
    h

/-! ### Fuzzy RDD identification — prop:po-fuzzy-rdd -/

/-- **Fuzzy RDD identification at the cutoff** in regression-representative
form.  The Wald ratio of latent right/left representative jumps equals the
Wald ratio of one-sided observable regression limits:

    τ_FRD(c) =
      (lim_{x↓c} ν_Y(x) - lim_{x↑c} ν_Y(x)) /
      (lim_{x↓c} ν_D(x) - lim_{x↑c} ν_D(x)).
-/
theorem frd_identification (hA : S.Assumptions) :
    S.tau_FRD hA =
      (S.nuY_right_limit hA - S.nuY_left_limit hA) /
        (S.nuD_right_limit hA - S.nuD_left_limit hA) := by
  rw [show S.nuY_right_limit hA = hA.muY true S.c from
        S.nuY_right_limit_eq hA (S.tendsto_nuY_right_limit hA),
      show S.nuY_left_limit hA = hA.muY false S.c from
        S.nuY_left_limit_eq hA (S.tendsto_nuY_left_limit hA),
      show S.nuD_right_limit hA = hA.muD true S.c from
        S.nuD_right_limit_eq hA (S.tendsto_nuD_right_limit hA),
      show S.nuD_left_limit hA = hA.muD false S.c from
        S.nuD_left_limit_eq hA (S.tendsto_nuD_left_limit hA)]
  rfl

/-! ### LATE bridge — strengthened global-monotonicity variant of prop:po-fuzzy-rdd

Under monotonicity, defiers have measure zero, so `Y(D(1)) − Y(D(0))` agrees
a.e. with `YdiffComplier`.  Both have continuous regression representatives at
`c`, giving a pointwise equality that makes `τ_FRD = τ_LATE`. -/

/-- Under monotonicity, `Y(D(1)) − Y(D(0)) =ᵐ[P.μ] YdiffComplier`. -/
private lemma YofDofZ_diff_eq_YdiffComplier_ae
    (hmono : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true) :
    (fun ω => S.YofDofZ true ω - S.YofDofZ false ω) =ᵐ[P.μ] S.YdiffComplier := by
  filter_upwards [hmono] with ω hmonoω
  simp only [YofDofZ, YdiffComplier]
  cases h1 : S.DofZ true ω <;> cases h0 : S.DofZ false ω <;>
    simp_all [mul_zero, mul_one]

/-- The Y-jump of latent regressions equals `μ_Ydiff_complier` at the cutoff. -/
private lemma muY_diff_eq_mu_Ydiff_complier_at_cutoff (hA : S.Assumptions)
    (hmono : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true) :
    hA.muY true S.c - hA.muY false S.c = hA.mu_Ydiff_complier S.c := by
  have h_ae : (fun x => hA.muY true x - hA.muY false x) =ᵐ[P.μ.map S.factualX]
      hA.mu_Ydiff_complier :=
    IsRegressionFunction.aeEq_of_aeEq_response
      S.aemeasurable_factualX
      (S.YofDofZ_diff_eq_YdiffComplier_ae hmono)
      ((hA.muY_isReg true).sub (hA.muY_isReg false))
      hA.mu_Ydiff_complier_isReg
  exact RDDLimits.value_eq_of_aeEq_right
    (ae_restrict_of_ae h_ae)
    ((hA.muY_continuousAt true).sub (hA.muY_continuousAt false))
    hA.mu_Ydiff_complier_continuousAt
    hA.support_right

/-- **Fuzzy RDD identifies a cutoff representative complier ratio under an
extra global monotonicity bridge**.
When consistency, deterministic cutoff eligibility, local exclusion through
potential outcomes, the local fuzzy-RDD assumptions, and global a.s. monotonicity
all hold,
the observable Wald ratio at the cutoff equals the complier-weighted
outcome-difference representative divided by the first-stage jump.

-- TODO(faithfulness): fuzzy RDD source statement — to reach the local
-- cutoff-complier claim from the standard local monotonicity assumption, the
-- library needs a local-regression bridge from neighborhood a.e. monotonicity to
-- equality of the cutoff regression representatives. -/
theorem tau_late_identification (hA : S.Assumptions)
    (hmono : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true) :
    S.tau_LATE hA = S.tau_FRD hA := by
  simp only [tau_LATE, tau_FRD]
  congr 1
  exact (S.muY_diff_eq_mu_Ydiff_complier_at_cutoff hA hmono).symm

end POFuzzyRDDSystem

end PO
end Causalean
