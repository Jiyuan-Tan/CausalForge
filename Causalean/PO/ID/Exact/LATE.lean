/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# IV System and LATE in the Potential Outcome Framework

Implements def:po-iv-system, def:po-iv-assumptions, def:po-late,
prop:po-late, and rem:po-late from Basic Concepts.tex.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

/-! # Instrumental Variables LATE

This file formalizes the binary-instrument local average treatment effect in
the potential-outcome framework. It defines the IV subsystem `POIVSystem`,
potential treatments `DofZ`, potential outcomes `YofD`, the complier event,
event-conditional observable means, the IV assumption bundle, and the target
`LATE`.

The proof surface decomposes the Wald argument into public identities:
`first_stage_identity`, `reduced_form_identity`, `pointwise_monotonicity`, and
`event_conditioning_identity`. The theorem `late_wald` assembles these pieces
to identify the observable Wald ratio with the complier average treatment
effect. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A binary instrumental-variables subsystem records an instrument, treatment,
and outcome inside a potential-outcome system.

IV subsystem over a PO system -- def:po-iv-system. -/
structure POIVSystem (P : POSystem) where
  Z : P.V
  D : P.V
  Y : P.V
  hZbool : P.X Z ≃ᵐ Bool
  hDbool : P.X D ≃ᵐ Bool
  hYreal : P.X Y ≃ᵐ ℝ
  hZD : Z ≠ D
  hDY : D ≠ Y
  hZY : Z ≠ Y

namespace POIVSystem

variable {P : POSystem} (S : POIVSystem P)

/-- Instrument packaged as a `POVar` valued in `Bool`. -/
def zVar : POVar P Bool := ⟨S.Z, S.hZbool⟩

/-- Treatment packaged as a `POVar` valued in `Bool`. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- Outcome packaged as a `POVar` valued in `ℝ`. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- Regime fixing instrument to `z`. -/
noncomputable def instrumentRegime (z : Bool) : Regime P.V P.X :=
  Regime.single S.Z (S.hZbool.symm z)

/-- Regime fixing treatment to `d`. -/
noncomputable def treatmentRegime (d : Bool) : Regime P.V P.X :=
  Regime.single S.D (S.hDbool.symm d)

/-- The potential treatment under an instrument value is the treatment that
would be observed if the instrument were fixed to that value.

`D(z) : P.Ω → Bool`. -/
noncomputable def DofZ (z : Bool) : P.Ω → Bool :=
  S.dVar.cfUnder S.zVar z

/-- The potential outcome under a treatment value is the outcome that would be
observed if treatment were fixed to that value.

`Y(d) : P.Ω → ℝ`. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ :=
  S.yVar.cfUnder S.dVar d

/-- Factual instrument Z. -/
noncomputable def factualZ : P.Ω → Bool := S.zVar.factual

/-- Factual treatment D. -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- Factual outcome Y. -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- Complier event `{ω | D(1)(ω) = 1 ∧ D(0)(ω) = 0}` -- def:po-late. -/
def complierEvent : Set P.Ω :=
  { ω | S.DofZ true ω = true ∧ S.DofZ false ω = false }

/-- Set `{ω | Z(ω) = z}`. -/
def zEvent (z : Bool) : Set P.Ω := S.zVar.event z

/-- The potential treatment under a fixed instrument value is measurable. -/
lemma measurable_DofZ (z : Bool) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- The factual instrument is measurable. -/
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual

/-- The factual treatment is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- The factual outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- The potential outcome under a fixed treatment value is measurable. -/
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- The complier event is measurable. -/
lemma measurableSet_complierEvent : MeasurableSet S.complierEvent :=
  (S.measurable_DofZ true (MeasurableSpace.measurableSet_top (s := {true}))).inter
    (S.measurable_DofZ false (MeasurableSpace.measurableSet_top (s := {false})))

/-- The factual instrument event is measurable. -/
lemma measurableSet_zEvent (z : Bool) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _

/-- `Y` composed with `D(z)`: `1_{D(z)=1} Y(1) + 1_{D(z)=0} Y(0)`. -/
noncomputable def YofDofZ (z : Bool) : P.Ω → ℝ :=
  fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω

/-- `E[D | Z = z]`, the event-level conditional expectation of the (0/1-coded)
factual treatment on `{Z = z}`. Uses the shared PO conditioning tool
`eventCondExp` (definitionally `(∫_A g)/μ(A)`). -/
noncomputable def condExpDZ (z : Bool) : ℝ :=
  eventCondExp P.μ (S.zEvent z) (fun ω => ((S.factualD ω).toNat : ℝ))

/-- `E[Y | Z = z]`, the event-level conditional expectation of the factual outcome
on `{Z = z}`, via the shared PO conditioning tool `eventCondExp`. -/
noncomputable def condExpYZ (z : Bool) : ℝ :=
  eventCondExp P.μ (S.zEvent z) S.factualY

/-- Regimed variable for `D(z)` (treatment under instrument set to `z`). -/
def dUnderZ (z : Bool) : RegimedVar P Bool :=
  ⟨S.dVar, Regime.single S.Z (S.hZbool.symm z)⟩

/-- Regimed variable for `Y(d)` (outcome under treatment set to `d`). -/
def yUnderD (d : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩

/-- Counterfactual bundle `(D(1), D(0), Y(1), Y(0))`. -/
noncomputable def cfBundle : POCFBundle P :=
  POCFBundle.cons (S.dUnderZ true) <|
  POCFBundle.cons (S.dUnderZ false) <|
  POCFBundle.cons (S.yUnderD true) <|
  POCFBundle.cons (S.yUnderD false) <|
  POCFBundle.nil P

/-- Classical IV assumptions -- def:po-iv-assumptions.

Exclusion is encoded by the `Y(d)` potential-outcome interface: outcomes
have no `z` argument, so the instrument cannot affect `Y` except through `D`.
The classical `Y(z, d)` formulation with explicit exclusion `Y(z, d) = Y(d)`
is equivalent under this ontology, and is implicit in our definition of
`POIVSystem`. -/
structure Assumptions (S : POIVSystem P) : Prop where
  /-- Consistency (SUTVA): the observed `D`/`Y` equal the realized potential
      treatment/outcome (`D = D(Z)`, `Y = Y(D)`). Links observed data to the
      counterfactuals. (Exclusion — `Z` affects `Y` only through `D` — is built
      into the `Y(d)` interface: outcomes carry no `z` argument, see the type
      docstring above.) -/
  consistency : P.Consistency
  /-- Instrument independence (random/ignorable instrument): the instrument is
      independent of the full counterfactual bundle, `Z ⟂ (D(1), D(0), Y(1), Y(0))`.
      Phrased as independence of the factual instrument from the counterfactual
      bundle. This is the IV exogeneity condition. -/
  instrumentIndep : P.IndepCF (RegimedVar.ofFactual S.zVar) S.cfBundle P.μ
  /-- Monotonicity (no defiers): turning the instrument on never moves a unit out
      of treatment — `D(1) ≥ D(0)` a.s. On `Bool` this is `D(0)=1 → D(1)=1`. Rules
      out defiers so the IV ratio identifies the complier effect. -/
  monotonicity : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true
  /-- Relevance (non-trivial first stage): the complier event `C = {D(1)=1, D(0)=0}`
      has positive probability, so the instrument actually shifts treatment for a
      positive mass of units (the LATE denominator is non-zero). -/
  relevance : 0 < (P.μ S.complierEvent).toReal

/-- Local Average Treatment Effect -- def:po-late.

    `E[Y(1) - Y(0) | C]`, the average treatment effect over the complier event
    `C`, via the shared PO conditioning tool `eventCondExp` (definitionally
    `(∫_C (Y(1)-Y(0)))/P(C)`). Equals the informal `E[Y(1)-Y(0) | C]` when
    `P(C) > 0`. -/
noncomputable def LATE : ℝ :=
  eventCondExp P.μ S.complierEvent (fun ω => S.YofD true ω - S.YofD false ω)

/-- On `zEvent z`, the counterfactual treatment `D(z)` equals the factual `D`.
    Pointwise specialization of `Consistency.factual` with `r = instrumentRegime z`,
    `Y = {D}`. -/
lemma DofZ_eq_factualD_on_zEvent (hA : S.Assumptions) (z : Bool)
    {ω : P.Ω} (hω : ω ∈ S.zEvent z) :
    S.DofZ z ω = S.factualD ω :=
  POVar.cf_eq_factual_on_event hA.consistency S.dVar S.zVar z S.hZD.symm hω

/-- Factual `Y` equals the counterfactual `Y(factualD ω)`.  Pointwise
    specialization of `Consistency.factual` with `r = treatmentRegime (factualD ω)`,
    `Y = {Y}`. -/
lemma factualY_eq_YofD_factualD (hA : S.Assumptions) (ω : P.Ω) :
    S.factualY ω = S.YofD (S.factualD ω) ω :=
  POVar.factual_eq_cfUnder_self_selected hA.consistency S.yVar S.dVar S.hDY.symm ω

/-- Step 1 of rem:po-late: first-stage identity.
    `E[D | Z=1] - E[D | Z=0] = P(C)`. -/
theorem first_stage_identity (hA : S.Assumptions)
    (hZ1 : 0 < (P.μ (S.zEvent true)).toReal)
    (hZ0 : 0 < (P.μ (S.zEvent false)).toReal) :
    S.condExpDZ true - S.condExpDZ false = (P.μ S.complierEvent).toReal := by
  -- Step 1: `condExpDZ z = ∫ (DofZ z ω).toNat ∂μ`.
  have hμne_zero : ∀ z, 0 < (P.μ (S.zEvent z)).toReal →
      P.μ (S.zVar.event z) ≠ 0 := fun z hZ h =>
    absurd hZ (by simp [show S.zEvent z = S.zVar.event z from rfl, h])
  have hμne_top : ∀ z, P.μ (S.zVar.event z) ≠ ⊤ := fun _ => measure_ne_top _ _
  have hCE : ∀ z (_hZ : 0 < (P.μ (S.zEvent z)).toReal),
      S.condExpDZ z = ∫ ω, ((S.DofZ z ω).toNat : ℝ) ∂P.μ := by
    intro z hZ
    -- `h_proj` on the bundle `jointValue`: indices 0,1 are `D(1),D(0)`.
    let h_proj : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
      fun f => ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)).toNat : ℝ)
    have hh_meas : Measurable h_proj := by
      change Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
        ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)).toNat : ℝ)
      cases z
      · exact (by fun_prop : Measurable fun n : ℕ => (n : ℝ)).comp
          ((by fun_prop : Measurable Bool.toNat).comp
            (measurable_pi_apply (1 : Fin 4)))
      · exact (by fun_prop : Measurable fun n : ℕ => (n : ℝ)).comp
          ((by fun_prop : Measurable Bool.toNat).comp
            (measurable_pi_apply (0 : Fin 4)))
    have h_cons : ∀ ω ∈ S.zVar.event z,
        ((S.factualD ω).toNat : ℝ) = h_proj (S.cfBundle.jointValue ω) := by
      intro ω hω
      rw [← S.DofZ_eq_factualD_on_zEvent hA z hω]
      change ((S.DofZ z ω).toNat : ℝ)
        = ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
              ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)).toNat : ℝ)
      cases z <;> rfl
    have hbridge : S.condExpDZ z =
        eventCondExp P.μ (S.zVar.event z) (fun ω => ((S.factualD ω).toNat : ℝ)) := rfl
    rw [hbridge,
      POSystem.eventCondExp_of_consistency_IndepCF hA.instrumentIndep
        (a := S.zVar) hh_meas h_cons (hμne_zero z hZ) (hμne_top z)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    change ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
            ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)).toNat : ℝ)
        = ((S.DofZ z ω).toNat : ℝ)
    cases z <;> rfl
  rw [hCE true hZ1, hCE false hZ0]
  -- Step 2: fold the two integrals into `∫ ((DofZ true).toNat - (DofZ false).toNat) ∂μ`.
  have hDbdd : ∀ z, ∀ ω, |((S.DofZ z ω).toNat : ℝ)| ≤ 1 := fun z ω => by
    cases S.DofZ z ω <;> simp
  have hDint : ∀ z, Integrable (fun ω => ((S.DofZ z ω).toNat : ℝ)) P.μ := fun z =>
    (MeasureTheory.integrable_const (1:ℝ)).mono'
      ((by fun_prop : Measurable (fun n : ℕ => (n : ℝ))).comp
        ((by fun_prop : Measurable Bool.toNat).comp (S.measurable_DofZ z)) |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall (hDbdd z))
  rw [← MeasureTheory.integral_sub (hDint true) (hDint false)]
  -- Step 3: under monotonicity, `(DofZ true).toNat - (DofZ false).toNat = 1_C a.s.`.
  have hInd : ∀ᵐ ω ∂P.μ,
      ((S.DofZ true ω).toNat : ℝ) - ((S.DofZ false ω).toNat : ℝ)
        = S.complierEvent.indicator (fun _ => (1:ℝ)) ω := by
    refine hA.monotonicity.mono (fun ω hω => ?_)
    by_cases h1 : S.DofZ true ω = true
    · by_cases h0 : S.DofZ false ω = true
      · have hnC : ω ∉ S.complierEvent := by
          intro ⟨_, h0'⟩; rw [h0] at h0'; exact Bool.noConfusion h0'
        simp [h1, h0, Set.indicator_of_notMem hnC]
      · have h0' : S.DofZ false ω = false := Bool.not_eq_true _ |>.mp h0
        have hC : ω ∈ S.complierEvent := ⟨h1, h0'⟩
        simp [h1, h0', Set.indicator_of_mem hC]
    · have h1' : S.DofZ true ω = false := Bool.not_eq_true _ |>.mp h1
      by_cases h0 : S.DofZ false ω = true
      · exfalso; rw [hω h0] at h1'; exact Bool.noConfusion h1'.symm
      · have h0' : S.DofZ false ω = false := Bool.not_eq_true _ |>.mp h0
        have hnC : ω ∉ S.complierEvent := by
          intro ⟨h1'', _⟩; rw [h1'] at h1''; exact Bool.false_ne_true h1''
        simp [h1', h0', Set.indicator_of_notMem hnC]
  rw [MeasureTheory.integral_congr_ae hInd]
  rw [MeasureTheory.integral_indicator_const (1:ℝ) S.measurableSet_complierEvent]
  simp [MeasureTheory.measureReal_def]

/-- Step 2 of rem:po-late: reduced-form identity.
    `E[Y | Z=1] - E[Y | Z=0] = E[Y(D(1)) - Y(D(0))]`. -/
theorem reduced_form_identity (hA : S.Assumptions)
    (hZ1 : 0 < (P.μ (S.zEvent true)).toReal)
    (hZ0 : 0 < (P.μ (S.zEvent false)).toReal)
    (hY1 : Integrable (S.YofD true) P.μ)
    (hY0 : Integrable (S.YofD false) P.μ) :
    S.condExpYZ true - S.condExpYZ false =
      ∫ ω, (S.YofDofZ true ω - S.YofDofZ false ω) ∂P.μ := by
  -- Measurability and integrability of `YofDofZ z`.
  have hYDZ_meas : ∀ z, Measurable (S.YofDofZ z) := fun z => by
    unfold YofDofZ
    exact Measurable.ite (S.measurable_DofZ z (MeasurableSet.singleton true))
      (S.measurable_YofD true) (S.measurable_YofD false)
  have hYDZ_bdd : ∀ z, ∀ ω,
      |S.YofDofZ z ω| ≤ |S.YofD true ω| + |S.YofD false ω| := fun z ω => by
    have h1 := abs_nonneg (S.YofD true ω)
    have h0 := abs_nonneg (S.YofD false ω)
    unfold YofDofZ; cases S.DofZ z ω <;> simp [h1, h0]
  have hYDZ_int : ∀ z, Integrable (S.YofDofZ z) P.μ := fun z =>
    (hY1.norm.add hY0.norm).mono' (hYDZ_meas z).aestronglyMeasurable
      (Filter.Eventually.of_forall (hYDZ_bdd z))
  -- Step 1: `condExpYZ z = ∫ YofDofZ z ω ∂μ`.
  have hμne_zero : ∀ z, 0 < (P.μ (S.zEvent z)).toReal →
      P.μ (S.zVar.event z) ≠ 0 := fun z hZ h =>
    absurd hZ (by simp [show S.zEvent z = S.zVar.event z from rfl, h])
  have hμne_top : ∀ z, P.μ (S.zVar.event z) ≠ ⊤ := fun _ => measure_ne_top _ _
  have hCE : ∀ z (_hZ : 0 < (P.μ (S.zEvent z)).toReal),
      S.condExpYZ z = ∫ ω, S.YofDofZ z ω ∂P.μ := by
    intro z hZ
    -- `h_proj` on the bundle: indices 0,1 are `D(1),D(0)`; 2,3 are `Y(1),Y(0)`.
    let h_proj : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
      fun f => if ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)) : Bool)
               then ((f (2 : Fin 4)) : ℝ) else ((f (3 : Fin 4)) : ℝ)
    have hh_meas : Measurable h_proj := by
      change Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
        if ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)) : Bool)
        then ((f (2 : Fin 4)) : ℝ) else ((f (3 : Fin 4)) : ℝ)
      cases z
      · refine Measurable.ite ?_ ?_ ?_
        · exact (by fun_prop :
            Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
              ((f (1 : Fin 4)) : Bool)) (MeasurableSet.singleton true)
        · exact measurable_pi_apply (2 : Fin 4)
        · exact measurable_pi_apply (3 : Fin 4)
      · refine Measurable.ite ?_ ?_ ?_
        · exact (by fun_prop :
            Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
              ((f (0 : Fin 4)) : Bool)) (MeasurableSet.singleton true)
        · exact measurable_pi_apply (2 : Fin 4)
        · exact measurable_pi_apply (3 : Fin 4)
    have h_cons : ∀ ω ∈ S.zVar.event z,
        S.factualY ω = h_proj (S.cfBundle.jointValue ω) := by
      intro ω hω
      rw [S.factualY_eq_YofD_factualD hA ω, ← S.DofZ_eq_factualD_on_zEvent hA z hω]
      have hJV0 : (S.cfBundle.jointValue ω (0 : Fin 4) : Bool) = S.DofZ true ω := rfl
      have hJV1 : (S.cfBundle.jointValue ω (1 : Fin 4) : Bool) = S.DofZ false ω := rfl
      have hJV2 : (S.cfBundle.jointValue ω (2 : Fin 4) : ℝ) = S.YofD true ω := rfl
      have hJV3 : (S.cfBundle.jointValue ω (3 : Fin 4) : ℝ) = S.YofD false ω := rfl
      change S.YofD (S.DofZ z ω) ω
        = if ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
                      ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)) : Bool)
          then ((S.cfBundle.jointValue ω (2 : Fin 4)) : ℝ)
          else ((S.cfBundle.jointValue ω (3 : Fin 4)) : ℝ)
      rw [hJV0, hJV1, hJV2, hJV3]
      cases z <;> cases S.DofZ _ ω <;> simp
    have hbridge : S.condExpYZ z =
        eventCondExp P.μ (S.zVar.event z) S.factualY := rfl
    rw [hbridge,
      POSystem.eventCondExp_of_consistency_IndepCF hA.instrumentIndep
        (a := S.zVar) hh_meas h_cons (hμne_zero z hZ) (hμne_top z)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    change (if ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
                        ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)) : Bool)
            then ((S.cfBundle.jointValue ω (2 : Fin 4)) : ℝ)
            else ((S.cfBundle.jointValue ω (3 : Fin 4)) : ℝ)) = S.YofDofZ z ω
    unfold YofDofZ
    cases z <;> rfl
  rw [hCE true hZ1, hCE false hZ0]
  rw [← MeasureTheory.integral_sub (hYDZ_int true) (hYDZ_int false)]

/-- Step 3 of rem:po-late: pointwise monotonicity identity.
    `Y(D(1)) - Y(D(0)) = (Y(1) - Y(0)) · 1_C` almost surely. -/
theorem pointwise_monotonicity (hA : S.Assumptions) :
    ∀ᵐ ω ∂P.μ,
      S.YofDofZ true ω - S.YofDofZ false ω
        = (S.YofD true ω - S.YofD false ω) *
            S.complierEvent.indicator (fun _ => (1:ℝ)) ω := by
  refine hA.monotonicity.mono (fun ω hω => ?_)
  unfold YofDofZ complierEvent
  rcases hD1 : S.DofZ true ω <;> rcases hD0 : S.DofZ false ω <;>
    simp_all [Set.indicator]

/-- Step 4 of rem:po-late: event-conditioning identity.
    `E[(Y(1) - Y(0)) · 1_C] = P(C) · LATE`. -/
theorem event_conditioning_identity :
    ∫ ω, (S.YofD true ω - S.YofD false ω) *
           S.complierEvent.indicator (fun _ => (1:ℝ)) ω ∂P.μ
      = (P.μ S.complierEvent).toReal * S.LATE := by
  unfold LATE eventCondExp
  have hC : MeasurableSet S.complierEvent := S.measurableSet_complierEvent
  have h_rw :
      (fun ω => (S.YofD true ω - S.YofD false ω) *
                S.complierEvent.indicator (fun _ => (1:ℝ)) ω)
      = S.complierEvent.indicator (fun ω => S.YofD true ω - S.YofD false ω) := by
    funext ω
    by_cases hω : ω ∈ S.complierEvent
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [h_rw, MeasureTheory.integral_indicator hC]
  by_cases hμ : (P.μ S.complierEvent).toReal = 0
  · rw [hμ, zero_mul]
    have hμ0 : P.μ S.complierEvent = 0 := by
      have hne : P.μ S.complierEvent ≠ ⊤ := measure_ne_top _ _
      exact (ENNReal.toReal_eq_zero_iff _).mp hμ |>.resolve_right hne
    have hrest : P.μ.restrict S.complierEvent = 0 := by
      rw [MeasureTheory.Measure.restrict_eq_zero]; exact hμ0
    simp [hrest]
  · field_simp

/-- Wald identification of LATE -- prop:po-late.
    `(E[Y|Z=1] - E[Y|Z=0]) / (E[D|Z=1] - E[D|Z=0]) = LATE`. -/
theorem late_wald (hA : S.Assumptions)
    (hZ1 : 0 < (P.μ (S.zEvent true)).toReal)
    (hZ0 : 0 < (P.μ (S.zEvent false)).toReal)
    (hY1 : Integrable (S.YofD true) P.μ)
    (hY0 : Integrable (S.YofD false) P.μ) :
    (S.condExpYZ true - S.condExpYZ false) /
      (S.condExpDZ true - S.condExpDZ false)
      = S.LATE := by
  rw [S.first_stage_identity hA hZ1 hZ0]
  rw [S.reduced_form_identity hA hZ1 hZ0 hY1 hY0]
  have heq : ∀ᵐ ω ∂P.μ, S.YofDofZ true ω - S.YofDofZ false ω
      = (S.YofD true ω - S.YofD false ω) *
          S.complierEvent.indicator (fun _ => (1:ℝ)) ω := S.pointwise_monotonicity hA
  rw [MeasureTheory.integral_congr_ae heq]
  rw [S.event_conditioning_identity]
  have hC : (P.μ S.complierEvent).toReal ≠ 0 := ne_of_gt hA.relevance
  field_simp

end POIVSystem

end PO
end Causalean
