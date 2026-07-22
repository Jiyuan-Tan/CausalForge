/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variable-intensity instrumental variables

Angrist-Imbens style identification for finite ordered treatment intensities:
a directed instrument contrast identifies an average causal response over the
treatment-intensity margins crossed by the instrument-induced treatment change.
-/

import Causalean.PO.ID.Exact.VariableIntensityIV.OrderedTreatment
import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Conditioning.EventCondExp

/-! # Variable-Intensity Instrumental Variables

This file formalizes a finite ordered-treatment instrumental-variable system for
an Angrist-Imbens style directed instrument contrast, **inside the
potential-outcome framework** (`POSystem`). The instrument, treatment intensity,
and outcome are system variables; potential intensities `D(z)` and
treatment-indexed potential outcomes `Y(d)` are genuine counterfactuals
(`POVar.cfUnder`), and consistency / instrument-independence are the project's
canonical PO assumptions (`POSystem.Consistency`, `POSystem.IndepCF`) rather than
ad-hoc structure fields.

It defines margin-specific causal responses, crossing events, and the population
objects needed to express average causal responses over crossed treatment
margins; the directed Wald estimand; the headline average-causal-response
characterization; binary-treatment and constant-response specializations; and an
interface-only population 2SLS score/decomposition layer. -/

namespace Causalean
namespace PO.ID.Exact
namespace VariableIntensityIV

open Finset MeasureTheory ProbabilityTheory

noncomputable section

/-- A variable-intensity IV system records an instrument, an ordered treatment
intensity, and an outcome inside a potential-outcome system, with the treatment
taking at least one margin.

The instrument value space is identified with a finite set `𝒵`, the treatment
value space with the ordered intensity levels `Fin (J+1)`, and the outcome value
space with `ℝ`.  Exclusion is encoded structurally: outcomes enter only through
the treatment-indexed counterfactual `Y(d)`, which fixes the treatment and never
the instrument, so the instrument has no direct path to the outcome. -/
structure VariableIntensityIVSystem (P : POSystem) (𝒵 : Type*) [MeasurableSpace 𝒵]
    [Fintype 𝒵] [MeasurableSingletonClass 𝒵] (J : ℕ) where
  /-- The ordered treatment has at least one margin. -/
  hJ_pos : 0 < J
  /-- Instrument system variable. -/
  Z : P.V
  /-- Treatment-intensity system variable. -/
  D : P.V
  /-- Outcome system variable. -/
  Y : P.V
  /-- The instrument value space is identified with the finite set `𝒵`. -/
  hZ𝒵 : P.X Z ≃ᵐ 𝒵
  /-- The treatment value space is identified with the ordered levels `Fin (J+1)`. -/
  hDintensity : P.X D ≃ᵐ Fin (J + 1)
  /-- The outcome value space is identified with `ℝ`. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- Instrument and treatment are distinct variables. -/
  hZD : Z ≠ D
  /-- Treatment and outcome are distinct variables. -/
  hDY : D ≠ Y
  /-- Instrument and outcome are distinct variables. -/
  hZY : Z ≠ Y

namespace VariableIntensityIVSystem

variable {P : POSystem} {𝒵 : Type*} [MeasurableSpace 𝒵]
variable [Fintype 𝒵] [MeasurableSingletonClass 𝒵]
variable {J : ℕ} (S : VariableIntensityIVSystem P 𝒵 J)

/-- Instrument packaged as a `POVar` valued in `𝒵`. -/
def zVar : POVar P 𝒵 := ⟨S.Z, S.hZ𝒵⟩

/-- Treatment intensity packaged as a `POVar` valued in `Fin (J+1)`. -/
def dVar : POVar P (Fin (J + 1)) := ⟨S.D, S.hDintensity⟩

/-- Outcome packaged as a `POVar` valued in `ℝ`. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- Potential treatment intensity `D(z)`: the intensity that would be observed if
the instrument were fixed to `z`.  A genuine single-intervention counterfactual. -/
def DofZ (z : 𝒵) : P.Ω → Fin (J + 1) := S.dVar.cfUnder S.zVar z

/-- Treatment-indexed potential outcome `Y(d)`: the outcome that would be observed
if the treatment intensity were fixed to `d`.  No instrument argument enters, so
exclusion is structural. -/
def YofD (d : Fin (J + 1)) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- Factual instrument `Z`. -/
def factualZ : P.Ω → 𝒵 := S.zVar.factual

/-- Factual treatment intensity `D`. -/
def factualD : P.Ω → Fin (J + 1) := S.dVar.factual

/-- Factual outcome `Y`. -/
def factualY : P.Ω → ℝ := S.yVar.factual

/-- Factual instrument cell `{Z = z}`. -/
def zEvent (z : 𝒵) : Set P.Ω := S.zVar.event z

/-- The potential treatment under a fixed instrument value is measurable. -/
lemma measurable_DofZ (z : 𝒵) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- The potential outcome under a fixed treatment value is measurable. -/
lemma measurable_YofD (d : Fin (J + 1)) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- The factual instrument is measurable. -/
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual

/-- The factual treatment is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- The factual outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- The factual instrument cell is measurable. -/
lemma measurableSet_zEvent (z : 𝒵) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event z

/-! ### Counterfactual bundle for a directed contrast

The IV-validity independence hypothesis is `Z ⟂ (Y(0),…,Y(J), D(z0), D(z1))`.
We package the right-hand side as a `POCFBundle`: two `Fin (J+1)`-valued
components `D(z0), D(z1)` at indices `0, 1`, followed by `J+1` real-valued
outcome components `Y(0),…,Y(J)` at indices `2,…,J+2`. -/

/-- Regimed variable for `D(z)` (treatment intensity under instrument set to `z`). -/
def dUnderZ (z : 𝒵) : RegimedVar P (Fin (J + 1)) :=
  ⟨S.dVar, Regime.single S.Z (S.hZ𝒵.symm z)⟩

/-- Regimed variable for `Y(d)` (outcome under treatment intensity set to `d`). -/
def yUnderD (d : Fin (J + 1)) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDintensity.symm d)⟩

/-- Homogeneous bundle of the `J+1` treatment-indexed potential outcomes
`Y(0),…,Y(J)`. -/
def outcomeBundle : POCFBundle P where
  n := J + 1
  type := fun _ => ℝ
  inst := fun _ => inferInstance
  vars := fun d => S.yUnderD d

/-- Counterfactual bundle `(D(z0), D(z1), Y(0),…,Y(J))` for the contrast
`(z0, z1)`.  Index `0` is `D(z0)`, index `1` is `D(z1)`, index `d+2` is `Y(d)`. -/
def cfContrastBundle (z0 z1 : 𝒵) : POCFBundle P :=
  POCFBundle.cons (S.dUnderZ z0) (POCFBundle.cons (S.dUnderZ z1) S.outcomeBundle)

/-- Unit causal response on margin `j → j+1`: `Δ_jY = Y(j+1) - Y(j)`. -/
def marginResponse (j : Fin J) : P.Ω → ℝ :=
  fun ω => S.YofD (OrderedTreatment.upperLevel j) ω -
    S.YofD (OrderedTreatment.lowerLevel j) ω

/-- Crossing event `C_j(z0,z1) = {D(z1) ≥ j+1 > D(z0)}`. -/
def crossingEvent (z0 z1 : 𝒵) (j : Fin J) : Set P.Ω :=
  {ω | OrderedTreatment.Crossing (S.DofZ z0 ω) (S.DofZ z1 ω) j}

/-- Crossing probability for a directed instrument contrast and margin. -/
def crossingProb (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  (P.μ (S.crossingEvent z0 z1 j)).toReal

private lemma measurable_intensityValue :
    Measurable (fun d : Fin (J + 1) => OrderedTreatment.intensityValue d) := by
  exact (by fun_prop : Measurable fun n : ℕ => (n : ℝ)).comp
    (by fun_prop : Measurable fun d : Fin (J + 1) => d.val)

private lemma measurable_intensityValue_DofZ (z : 𝒵) :
    Measurable (fun ω => OrderedTreatment.intensityValue (S.DofZ z ω)) :=
  (measurable_intensityValue (J := J)).comp (S.measurable_DofZ z)

private lemma integrable_intensityValue_DofZ (z : 𝒵) :
    Integrable (fun ω => OrderedTreatment.intensityValue (S.DofZ z ω)) P.μ := by
  have hbdd : ∀ ω,
      ‖OrderedTreatment.intensityValue (S.DofZ z ω)‖ ≤ (J : ℝ) := by
    intro ω
    change |((S.DofZ z ω).val : ℝ)| ≤ (J : ℝ)
    rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le (S.DofZ z ω).val)]
    exact_mod_cast Nat.le_of_lt_succ (S.DofZ z ω).isLt
  exact (MeasureTheory.integrable_const (J : ℝ)).mono'
    (S.measurable_intensityValue_DofZ z).aestronglyMeasurable
    (Filter.Eventually.of_forall hbdd)

private lemma measurableSet_crossingEvent (z0 z1 : 𝒵) (j : Fin J) :
    MeasurableSet (S.crossingEvent z0 z1 j) := by
  unfold crossingEvent OrderedTreatment.Crossing
  have hA : MeasurableSet {d : Fin (J + 1) | OrderedTreatment.upperLevel j ≤ d} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have hB : MeasurableSet {d : Fin (J + 1) | d < OrderedTreatment.upperLevel j} :=
    Set.Finite.measurableSet (Set.toFinite _)
  exact (hA.preimage (S.measurable_DofZ z1)).inter (hB.preimage (S.measurable_DofZ z0))

private lemma crossingIndicator_fun_eq_indicator (z0 z1 : 𝒵) (j : Fin J) :
    (fun ω => OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j)
      = (S.crossingEvent z0 z1 j).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hC : OrderedTreatment.Crossing (S.DofZ z0 ω) (S.DofZ z1 ω) j
  · have hω : ω ∈ S.crossingEvent z0 z1 j := hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_mem hω]
  · have hω : ω ∉ S.crossingEvent z0 z1 j := by
      simpa [crossingEvent] using hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_notMem hω]

private lemma marginResponse_mul_crossingIndicator_eq_indicator (z0 z1 : 𝒵)
    (j : Fin J) :
    (fun ω => S.marginResponse j ω *
        OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j)
      = (S.crossingEvent z0 z1 j).indicator (S.marginResponse j) := by
  funext ω
  by_cases hC : OrderedTreatment.Crossing (S.DofZ z0 ω) (S.DofZ z1 ω) j
  · have hω : ω ∈ S.crossingEvent z0 z1 j := hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_mem hω]
  · have hω : ω ∉ S.crossingEvent z0 z1 j := by
      simpa [crossingEvent] using hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_notMem hω]

/-- Total crossing probability, equivalently the first-stage denominator under
directed monotonicity. -/
def totalCrossingProb (z0 z1 : 𝒵) : ℝ :=
  ∑ j : Fin J, S.crossingProb z0 z1 j

/-- Normalized Angrist-Imbens margin-crossing weight. -/
def crossingWeight (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  OrderedTreatment.normalizedWeight (S.crossingProb z0 z1) j

/-- Indicator-weighted margin effect `E[Δ_jY · 1_{C_j}]`, represented as a set
integral over the crossing event. -/
def indicatorWeightedEffect (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  ∫ ω in S.crossingEvent z0 z1 j, S.marginResponse j ω ∂P.μ

/-- Unnormalized sum of indicator-weighted crossing effects. -/
def unnormalizedACRContrast (z0 z1 : 𝒵) : ℝ :=
  ∑ j : Fin J, S.indicatorWeightedEffect z0 z1 j

/-- Indicator-weighted ACR ratio, avoiding partial conditional means in the
core algebra. -/
def indicatorWeightedACR (z0 z1 : 𝒵) : ℝ :=
  S.unnormalizedACRContrast z0 z1 / S.totalCrossingProb z0 z1

/-- The conditional margin response is the average unit-level causal response
among units whose potential treatment crosses a selected treatment margin when
the instrument changes along a selected ordered contrast.

No positivity or integrability side condition is required for this definition. -/
def conditionalMarginResponse (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  PO.eventCondExp P.μ (S.crossingEvent z0 z1 j) (S.marginResponse j)

/-- Angrist-Imbens average causal response:
`Σ_j ω_j E[Δ_jY | C_j]`. -/
def averageCausalResponse (z0 z1 : 𝒵) : ℝ :=
  ∑ j : Fin J, S.crossingWeight z0 z1 j * S.conditionalMarginResponse z0 z1 j

/-- Potential outcome `Y(D(z))`: the outcome if the instrument were set to `z`.
Equals `Y(d)` at `d = D(z)(ω)`.  No direct instrument effect enters because
`YofD` fixes only the treatment intensity `d`, not `z` (structural exclusion). -/
def YofDofZ (z : 𝒵) : P.Ω → ℝ :=
  fun ω => S.YofD (S.DofZ z ω) ω

private lemma measurable_YofDofZ (z : 𝒵) :
    Measurable (S.YofDofZ z) := by
  classical
  unfold YofDofZ
  have hsum : (fun ω => S.YofD (S.DofZ z ω) ω)
      = fun ω => ∑ d : Fin (J + 1),
          ({d} : Set (Fin (J + 1))).indicator (fun _ => S.YofD d ω) (S.DofZ z ω) := by
    funext ω
    rw [Finset.sum_eq_single (S.DofZ z ω)]
    · simp
    · intro d _ hd
      simp [hd]
    · intro h
      simp at h
  rw [hsum]
  refine Finset.measurable_sum _ ?_
  intro d _
  exact (S.measurable_YofD d).indicator
    ((MeasurableSet.singleton d).preimage (S.measurable_DofZ z))

/-- Potential first-stage contrast `E[D(z1) − D(z0)]` using potential
treatment intensities. -/
def firstStageContrast (z0 z1 : 𝒵) : ℝ :=
  ∫ ω, (OrderedTreatment.intensityValue (S.DofZ z1 ω) -
    OrderedTreatment.intensityValue (S.DofZ z0 ω)) ∂P.μ

/-- Potential reduced-form contrast `E[Y(D(z1)) − Y(D(z0))]`. -/
def reducedFormContrast (z0 z1 : 𝒵) : ℝ :=
  ∫ ω, (S.YofDofZ z1 ω - S.YofDofZ z0 ω) ∂P.μ

/-- `E[D | Z = z]` — observed first-stage conditional mean at instrument value
`z`, defined via `eventCondExp` over the cell `{Z = z}`. -/
def condExpDZ (z : 𝒵) : ℝ :=
  PO.eventCondExp P.μ (S.zEvent z)
    (fun ω => OrderedTreatment.intensityValue (S.factualD ω))

/-- `E[Y | Z = z]` — observed reduced-form conditional mean at instrument value
`z`, defined via `eventCondExp` over the cell `{Z = z}`. -/
def condExpYZ (z : 𝒵) : ℝ :=
  PO.eventCondExp P.μ (S.zEvent z) S.factualY

/-- Directed Wald estimand for two instrument cells. -/
def wald (z0 z1 : 𝒵) : ℝ :=
  (S.condExpYZ z1 - S.condExpYZ z0) /
    (S.condExpDZ z1 - S.condExpDZ z0)

/-- IV-validity assumptions for a fixed directed contrast `(z0,z1)`.

Consistency (`D = D(Z)`, `Y = Y(D)`) is the project's canonical PO consistency
assumption `P.Consistency`, and instrument independence is `P.IndepCF`: the
factual instrument is independent of the counterfactual bundle
`(D(z0), D(z1), Y(0),…,Y(J))`.

Exclusion is **structurally encoded**: `YofD d = yVar.cfUnder dVar d` fixes only
the treatment intensity `d`, never the instrument, so the instrument has no
direct path to the outcome beyond its effect through `D`. -/
structure ValidContrastAssumptions (z0 z1 : 𝒵) : Prop where
  /-- Consistency (SUTVA): observed `D`/`Y` equal the realized potential
  intensity/outcome, `D = D(Z)`, `Y = Y(D)`. -/
  consistency : P.Consistency
  /-- H1: instrument independence from the contrast-relevant counterfactuals,
  `Z ⟂ (D(z0), D(z1), Y(0),…,Y(J))`. -/
  hIndependence : P.IndepCF (RegimedVar.ofFactual S.zVar) (S.cfContrastBundle z0 z1) P.μ
  /-- H5: directed monotonicity, `D(z1) ≥ D(z0)`, a.s. -/
  hMonotone : ∀ᵐ ω ∂P.μ, S.DofZ z0 ω ≤ S.DofZ z1 ω
  /-- H6: positive first stage. -/
  hRelevance : 0 < S.firstStageContrast z0 z1
  /-- H7: treatment-indexed potential outcomes are integrable. -/
  hIntegrableY : ∀ d, Integrable (S.YofD d) P.μ

/-- Integrability of a margin response, derived from H7. -/
lemma integrable_marginResponse {z0 z1 : 𝒵} (hValid : S.ValidContrastAssumptions z0 z1)
    (j : Fin J) :
    Integrable (S.marginResponse j) P.μ := by
  exact
    (hValid.hIntegrableY (OrderedTreatment.upperLevel j)).sub
      (hValid.hIntegrableY (OrderedTreatment.lowerLevel j))

private lemma integrable_YofDofZ {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) (z : 𝒵) :
    Integrable (S.YofDofZ z) P.μ := by
  have hbound : ∀ᵐ ω ∂P.μ,
      ‖S.YofDofZ z ω‖ ≤ (fun ω => ∑ d : Fin (J + 1), ‖S.YofD d ω‖) ω :=
    Filter.Eventually.of_forall fun ω => by
      unfold YofDofZ
      exact Finset.single_le_sum
        (fun d _ => norm_nonneg (S.YofD d ω)) (Finset.mem_univ _)
  have hsum_int : Integrable (fun ω => ∑ d : Fin (J + 1), ‖S.YofD d ω‖) P.μ := by
    classical
    induction (Finset.univ : Finset (Fin (J + 1))) using Finset.induction_on with
    | empty =>
        simp
    | insert a s has ih =>
        simpa [Finset.sum_insert, has] using (hValid.hIntegrableY a).norm.add ih
  exact hsum_int.mono' (S.measurable_YofDofZ z).aestronglyMeasurable hbound

/-! ### Consistency bridges

On the cell `{Z = z}` the potential intensity `D(z)` agrees with the factual `D`,
and the factual outcome `Y` agrees with the treatment-selected counterfactual
`Y(D)`.  Both are pointwise specializations of `P.Consistency` via the shared
consistency lemmas. -/

/-- On `zEvent z`, the counterfactual intensity `D(z)` equals the factual `D`. -/
lemma DofZ_eq_factualD_on_zEvent (hC : P.Consistency) (z : 𝒵)
    {ω : P.Ω} (hω : ω ∈ S.zEvent z) :
    S.DofZ z ω = S.factualD ω :=
  POVar.cf_eq_factual_on_event hC S.dVar S.zVar z S.hZD.symm hω

/-- Factual `Y` equals the counterfactual `Y(factualD ω)`. -/
lemma factualY_eq_YofD_factualD (hC : P.Consistency) (ω : P.Ω) :
    S.factualY ω = S.YofD (S.factualD ω) ω :=
  POVar.factual_eq_cfUnder_self_selected hC S.yVar S.dVar S.hDY.symm ω

/-- First-stage bridge (left cell `z0`): the observed first-stage conditional
mean equals the unconditional expectation of the potential intensity `D(z0)`. -/
lemma condExpDZ_left_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal) :
    S.condExpDZ z0 = ∫ ω, OrderedTreatment.intensityValue (S.DofZ z0 ω) ∂P.μ := by
  have hμne_zero : P.μ (S.zVar.event z0) ≠ 0 := fun h =>
    absurd hCell0 (by simp [show S.zEvent z0 = S.zVar.event z0 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z0) ≠ ⊤ := measure_ne_top _ _
  let idx0 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨0, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => OrderedTreatment.intensityValue (f idx0)
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        OrderedTreatment.intensityValue (f idx0)
    exact (measurable_intensityValue (J := J)).comp (measurable_pi_apply idx0)
  have h_cons : ∀ ω ∈ S.zVar.event z0,
      OrderedTreatment.intensityValue (S.factualD ω) =
        hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [← S.DofZ_eq_factualD_on_zEvent hValid.consistency z0 hω]
    change OrderedTreatment.intensityValue (S.DofZ z0 ω) =
      OrderedTreatment.intensityValue ((S.cfContrastBundle z0 z1).jointValue ω idx0)
    rfl
  have hbridge : S.condExpDZ z0 =
      eventCondExp P.μ (S.zVar.event z0)
        (fun ω => OrderedTreatment.intensityValue (S.factualD ω)) := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_consistency_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas h_cons hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  change OrderedTreatment.intensityValue ((S.cfContrastBundle z0 z1).jointValue ω idx0) =
    OrderedTreatment.intensityValue (S.DofZ z0 ω)
  rfl

/-- First-stage bridge (right cell `z1`). -/
lemma condExpDZ_right_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal) :
    S.condExpDZ z1 = ∫ ω, OrderedTreatment.intensityValue (S.DofZ z1 ω) ∂P.μ := by
  have hμne_zero : P.μ (S.zVar.event z1) ≠ 0 := fun h =>
    absurd hCell1 (by simp [show S.zEvent z1 = S.zVar.event z1 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z1) ≠ ⊤ := measure_ne_top _ _
  let idx1 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨1, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => OrderedTreatment.intensityValue (f idx1)
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        OrderedTreatment.intensityValue (f idx1)
    exact (measurable_intensityValue (J := J)).comp (measurable_pi_apply idx1)
  have h_cons : ∀ ω ∈ S.zVar.event z1,
      OrderedTreatment.intensityValue (S.factualD ω) =
        hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [← S.DofZ_eq_factualD_on_zEvent hValid.consistency z1 hω]
    change OrderedTreatment.intensityValue (S.DofZ z1 ω) =
      OrderedTreatment.intensityValue
        ((S.cfContrastBundle z0 z1).jointValue ω idx1)
    rfl
  have hbridge : S.condExpDZ z1 =
      eventCondExp P.μ (S.zVar.event z1)
        (fun ω => OrderedTreatment.intensityValue (S.factualD ω)) := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_consistency_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas h_cons hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  change OrderedTreatment.intensityValue
      ((S.cfContrastBundle z0 z1).jointValue ω idx1) =
    OrderedTreatment.intensityValue (S.DofZ z1 ω)
  rfl

/-- Reduced-form bridge (left cell `z0`): the observed reduced-form conditional
mean equals the unconditional expectation of `Y(D(z0))`. -/
lemma condExpYZ_left_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal) :
    S.condExpYZ z0 = ∫ ω, S.YofDofZ z0 ω ∂P.μ := by
  classical
  have hμne_zero : P.μ (S.zVar.event z0) ≠ 0 := fun h =>
    absurd hCell0 (by simp [show S.zEvent z0 = S.zVar.event z0 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z0) ≠ ⊤ := measure_ne_top _ _
  let idx0 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨0, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let idxY (i : Fin (J + 1)) : Fin (S.cfContrastBundle z0 z1).n :=
    Fin.succ (Fin.succ i)
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => ∑ i : Fin (J + 1), if f idx0 = i then f (idxY i) else 0
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        ∑ i : Fin (J + 1), if f idx0 = i then f (idxY i) else 0
    refine Finset.measurable_sum _ ?_
    intro i _hi
    refine Measurable.ite ?_ (measurable_pi_apply (idxY i)) measurable_const
    exact (MeasurableSet.singleton i).preimage (measurable_pi_apply idx0)
  have h_cons : ∀ ω ∈ S.zVar.event z0,
      S.factualY ω = hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [S.factualY_eq_YofD_factualD hValid.consistency ω,
      ← S.DofZ_eq_factualD_on_zEvent hValid.consistency z0 hω]
    have hJV0 : (S.cfContrastBundle z0 z1).jointValue ω idx0 = S.DofZ z0 ω := rfl
    have hJVY : ∀ i : Fin (J + 1),
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
      intro i
      rfl
    change S.YofD (S.DofZ z0 ω) ω =
      ∑ i : Fin (J + 1),
        if (S.cfContrastBundle z0 z1).jointValue ω idx0 = i then
          (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0
    rw [hJV0]
    rw [Finset.sum_eq_single (S.DofZ z0 ω)]
    · simp [hJVY]
    · intro i _hi hi
      by_cases hEq : S.DofZ z0 ω = i
      · exact False.elim (hi hEq.symm)
      · exact if_neg hEq
    · intro h
      simp at h
  have hbridge : S.condExpYZ z0 =
      eventCondExp P.μ (S.zVar.event z0) S.factualY := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_consistency_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas h_cons hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  have hJV0 : (S.cfContrastBundle z0 z1).jointValue ω idx0 = S.DofZ z0 ω := rfl
  have hJVY : ∀ i : Fin (J + 1),
      (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
    intro i
    rfl
  change (∑ i : Fin (J + 1),
      if (S.cfContrastBundle z0 z1).jointValue ω idx0 = i then
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0) =
    S.YofDofZ z0 ω
  unfold YofDofZ
  rw [hJV0]
  rw [Finset.sum_eq_single (S.DofZ z0 ω)]
  · simp [hJVY]
  · intro i _hi hi
    by_cases hEq : S.DofZ z0 ω = i
    · exact False.elim (hi hEq.symm)
    · exact if_neg hEq
  · intro h
    simp at h

/-- Reduced-form bridge (right cell `z1`). -/
lemma condExpYZ_right_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal) :
    S.condExpYZ z1 = ∫ ω, S.YofDofZ z1 ω ∂P.μ := by
  classical
  have hμne_zero : P.μ (S.zVar.event z1) ≠ 0 := fun h =>
    absurd hCell1 (by simp [show S.zEvent z1 = S.zVar.event z1 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z1) ≠ ⊤ := measure_ne_top _ _
  let idx1 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨1, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let idxY (i : Fin (J + 1)) : Fin (S.cfContrastBundle z0 z1).n :=
    Fin.succ (Fin.succ i)
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => ∑ i : Fin (J + 1), if f idx1 = i then f (idxY i) else 0
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        ∑ i : Fin (J + 1), if f idx1 = i then f (idxY i) else 0
    refine Finset.measurable_sum _ ?_
    intro i _hi
    refine Measurable.ite ?_ (measurable_pi_apply (idxY i)) measurable_const
    exact (MeasurableSet.singleton i).preimage (measurable_pi_apply idx1)
  have h_cons : ∀ ω ∈ S.zVar.event z1,
      S.factualY ω = hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [S.factualY_eq_YofD_factualD hValid.consistency ω,
      ← S.DofZ_eq_factualD_on_zEvent hValid.consistency z1 hω]
    have hJV1 : (S.cfContrastBundle z0 z1).jointValue ω idx1 = S.DofZ z1 ω := rfl
    have hJVY : ∀ i : Fin (J + 1),
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
      intro i
      rfl
    change S.YofD (S.DofZ z1 ω) ω =
      ∑ i : Fin (J + 1),
        if (S.cfContrastBundle z0 z1).jointValue ω idx1 = i then
          (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0
    rw [hJV1]
    rw [Finset.sum_eq_single (S.DofZ z1 ω)]
    · simp [hJVY]
    · intro i _hi hi
      by_cases hEq : S.DofZ z1 ω = i
      · exact False.elim (hi hEq.symm)
      · exact if_neg hEq
    · intro h
      simp at h
  have hbridge : S.condExpYZ z1 =
      eventCondExp P.μ (S.zVar.event z1) S.factualY := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_consistency_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas h_cons hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  have hJV1 : (S.cfContrastBundle z0 z1).jointValue ω idx1 = S.DofZ z1 ω := rfl
  have hJVY : ∀ i : Fin (J + 1),
      (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
    intro i
    rfl
  change (∑ i : Fin (J + 1),
      if (S.cfContrastBundle z0 z1).jointValue ω idx1 = i then
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0) =
    S.YofDofZ z1 ω
  unfold YofDofZ
  rw [hJV1]
  rw [Finset.sum_eq_single (S.DofZ z1 ω)]
  · simp [hJVY]
  · intro i _hi hi
    by_cases hEq : S.DofZ z1 ω = i
    · exact False.elim (hi hEq.symm)
    · exact if_neg hEq
  · intro h
    simp at h

/-- First-stage denominator equals the sum of crossing probabilities. -/
theorem firstStage_eq_sum_crossingProb {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) :
    S.firstStageContrast z0 z1 = ∑ j : Fin J, S.crossingProb z0 z1 j := by
  unfold firstStageContrast crossingProb
  have hpoint :
      (fun ω => OrderedTreatment.intensityValue (S.DofZ z1 ω) -
          OrderedTreatment.intensityValue (S.DofZ z0 ω))
        =ᵐ[P.μ]
      fun ω => ∑ j : Fin J,
        OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j :=
    hValid.hMonotone.mono fun _ hmono =>
      OrderedTreatment.ordered_telescope_identity hmono
  calc
    ∫ ω, (OrderedTreatment.intensityValue (S.DofZ z1 ω) -
        OrderedTreatment.intensityValue (S.DofZ z0 ω)) ∂P.μ
        = ∫ ω, ∑ j : Fin J,
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          exact MeasureTheory.integral_congr_ae hpoint
    _ = ∑ j : Fin J, ∫ ω,
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          rw [S.crossingIndicator_fun_eq_indicator z0 z1 i]
          exact (MeasureTheory.integrable_const (μ := P.μ) (1 : ℝ)).indicator
            (S.measurableSet_crossingEvent z0 z1 i)
    _ = ∑ j : Fin J, (P.μ (S.crossingEvent z0 z1 j)).toReal := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [S.crossingIndicator_fun_eq_indicator z0 z1 j]
          exact MeasureTheory.integral_indicator_one (S.measurableSet_crossingEvent z0 z1 j)

/-- Crossing weights are nonnegative for a valid directed contrast. -/
lemma crossingWeight_nonneg {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) (j : Fin J) :
    0 ≤ S.crossingWeight z0 z1 j := by
  have hProb : ∀ i : Fin J, 0 ≤ S.crossingProb z0 z1 i := by
    intro i
    exact ENNReal.toReal_nonneg
  have hSum : 0 < ∑ i : Fin J, S.crossingProb z0 z1 i := by
    rw [← S.firstStage_eq_sum_crossingProb hValid]
    exact hValid.hRelevance
  exact OrderedTreatment.normalizedWeight_nonneg (S.crossingProb z0 z1) hProb hSum j

/-- Crossing weights sum to one for a valid directed contrast. -/
lemma sum_crossingWeight_eq_one {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) :
    ∑ j : Fin J, S.crossingWeight z0 z1 j = 1 := by
  have hSum : 0 < ∑ i : Fin J, S.crossingProb z0 z1 i := by
    rw [← S.firstStage_eq_sum_crossingProb hValid]
    exact hValid.hRelevance
  exact OrderedTreatment.sum_normalizedWeight_eq_one (S.crossingProb z0 z1) hSum

/-- Reduced form equals the sum of indicator-weighted causal responses across
crossed margins. -/
theorem reducedForm_eq_sum_crossingEffects {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) :
    S.reducedFormContrast z0 z1 =
      ∑ j : Fin J, S.indicatorWeightedEffect z0 z1 j := by
  unfold reducedFormContrast YofDofZ indicatorWeightedEffect
  have hpoint :
      (fun ω => S.YofD (S.DofZ z1 ω) ω - S.YofD (S.DofZ z0 ω) ω)
        =ᵐ[P.μ]
      fun ω => ∑ j : Fin J, S.marginResponse j ω *
        OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j :=
    hValid.hMonotone.mono fun ω hmono => by
      simpa [OrderedTreatment.marginIncrement, marginResponse] using
        OrderedTreatment.ordered_telescope_indicator
          (J := J) (fun d : Fin (J + 1) => S.YofD d ω) hmono
  calc
    ∫ ω, (S.YofD (S.DofZ z1 ω) ω - S.YofD (S.DofZ z0 ω) ω) ∂P.μ
        = ∫ ω, ∑ j : Fin J, S.marginResponse j ω *
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          exact MeasureTheory.integral_congr_ae hpoint
    _ = ∑ j : Fin J, ∫ ω, S.marginResponse j ω *
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          rw [S.marginResponse_mul_crossingIndicator_eq_indicator z0 z1 i]
          exact (S.integrable_marginResponse hValid i).indicator
            (S.measurableSet_crossingEvent z0 z1 i)
    _ = ∑ j : Fin J, ∫ ω in S.crossingEvent z0 z1 j, S.marginResponse j ω ∂P.μ := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [S.marginResponse_mul_crossingIndicator_eq_indicator z0 z1 j]
          rw [MeasureTheory.integral_indicator (S.measurableSet_crossingEvent z0 z1 j)]

/-- Indicator-weighted and conditional-mean ACR forms agree: the ratio
`(Σ_j E[Δ_jY · 1_{C_j}]) / (Σ_j ℙ(C_j))` equals `Σ_j ω_j E[Δ_jY | C_j]`.
This is a pure algebraic identity that holds for any values of
`indicatorWeightedEffect`, `crossingProb`, and `conditionalMarginResponse`
and does not require the contrast-validity assumptions. -/
theorem indicatorWeightedACR_eq_averageCausalResponse {z0 z1 : 𝒵} :
    S.indicatorWeightedACR z0 z1 = S.averageCausalResponse z0 z1 := by
  simp only [indicatorWeightedACR, averageCausalResponse, crossingWeight,
    OrderedTreatment.normalizedWeight,
    Causalean.Panel.Weighted.NormalizedWeights.normalizedWeight, totalCrossingProb,
    conditionalMarginResponse, unnormalizedACRContrast, indicatorWeightedEffect, crossingProb]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← PO.eventCondExp_mul_measure_toReal P.μ (S.crossingEvent z0 z1 j)
    (S.marginResponse j)]
  ring_nf

/-- Angrist-Imbens ACR characterization: the directed Wald estimand equals the
average causal response over crossed treatment-intensity margins. -/
theorem wald_eq_averageCausalResponse {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal) :
    S.wald z0 z1 = S.averageCausalResponse z0 z1 := by
  have hDZ0 := S.condExpDZ_left_eq_integral hValid hCell0
  have hDZ1 := S.condExpDZ_right_eq_integral hValid hCell1
  have hYZ0 := S.condExpYZ_left_eq_integral hValid hCell0
  have hYZ1 := S.condExpYZ_right_eq_integral hValid hCell1
  have hDint0 := S.integrable_intensityValue_DofZ z0
  have hDint1 := S.integrable_intensityValue_DofZ z1
  have hYint0 := S.integrable_YofDofZ hValid z0
  have hYint1 := S.integrable_YofDofZ hValid z1
  unfold wald
  rw [hYZ1, hYZ0, hDZ1, hDZ0]
  rw [← MeasureTheory.integral_sub hYint1 hYint0,
    ← MeasureTheory.integral_sub hDint1 hDint0]
  change S.reducedFormContrast z0 z1 / S.firstStageContrast z0 z1 =
    S.averageCausalResponse z0 z1
  rw [← S.indicatorWeightedACR_eq_averageCausalResponse]
  simp [indicatorWeightedACR, unnormalizedACRContrast, totalCrossingProb,
    S.reducedForm_eq_sum_crossingEffects hValid, S.firstStage_eq_sum_crossingProb hValid]

namespace SpecialCases

/-- Canonical single treatment margin transported from `Fin 1` under `J = 1`. -/
def binaryMargin (hBinaryIntensity : J = 1) : Fin J :=
  hBinaryIntensity.symm ▸ (0 : Fin 1)

/-- Binary-intensity specialization: with a single margin, Wald is the
conditional mean response on the unique crossing event. -/
theorem wald_eq_late_of_binaryIntensity {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal)
    (hBinaryIntensity : J = 1) :
    S.wald z0 z1 =
      PO.eventCondExp P.μ (S.crossingEvent z0 z1 (binaryMargin hBinaryIntensity))
        (S.marginResponse (binaryMargin hBinaryIntensity)) := by
  subst hBinaryIntensity
  rw [S.wald_eq_averageCausalResponse hValid hCell0 hCell1]
  have hweight : S.crossingWeight z0 z1 0 = 1 := by
    simpa using S.sum_crossingWeight_eq_one hValid
  simp [averageCausalResponse, binaryMargin, conditionalMarginResponse, hweight]

/-- Under `J = 1`, the unique crossing event coincides with the complier event
`{D(z1) = Fin.last J ∧ D(z0) = 0}`, i.e. the unit jump from level 0 to the
maximum level.  When `J = 1`, `Fin.last 1 = 1 : Fin 2`, so this recovers exactly
the binary-treatment LATE complier event `{D(z1) = 1 ∧ D(z0) = 0}` of
Imbens-Angrist (1994):
`β_Wald(z0,z1) = E[Y(1) − Y(0) | D(z1) = Fin.last J ∧ D(z0) = 0]`. -/
lemma crossingEvent_eq_complianceEvent (z0 z1 : 𝒵) (hJ : J = 1) :
    S.crossingEvent z0 z1 (binaryMargin hJ) =
      {ω | S.DofZ z1 ω = Fin.last J ∧ S.DofZ z0 ω = (0 : Fin (J + 1))} := by
  subst hJ
  ext ω
  simp only [binaryMargin, crossingEvent, OrderedTreatment.Crossing,
    OrderedTreatment.upperLevel, Set.mem_setOf_eq, Fin.last]
  have hone : (Fin.succ (0 : Fin 1)) = (⟨1, by omega⟩ : Fin 2) := by decide
  rw [hone]
  have hone_val : (⟨1, by omega⟩ : Fin 2).val = 1 := rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨le_antisymm (Fin.le_last _) h1, Fin.ext ?_⟩
    have hv2 : (S.DofZ z0 ω).val < (⟨1, by omega⟩ : Fin 2).val :=
      Fin.val_fin_lt.mpr h2
    rw [hone_val] at hv2
    have hge : 0 ≤ (S.DofZ z0 ω).val := Nat.zero_le _
    simp only [Fin.val_zero]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1 ▸ le_refl _, Fin.val_fin_lt.mp ?_⟩
    rw [hone_val]
    have hv2 : (S.DofZ z0 ω).val = (0 : Fin 2).val := congr_arg Fin.val h2
    simp only [Fin.val_zero] at hv2
    omega

/-- Constant marginal response specialization. -/
theorem wald_eq_constantResponse {z0 z1 : 𝒵} {τ : ℝ}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal)
    (hConstantResponse : ∀ j : Fin J, S.marginResponse j =ᵐ[P.μ] fun _ => τ) :
    S.wald z0 z1 = τ := by
  rw [S.wald_eq_averageCausalResponse hValid hCell0 hCell1]
  rw [← S.indicatorWeightedACR_eq_averageCausalResponse]
  unfold indicatorWeightedACR unnormalizedACRContrast totalCrossingProb indicatorWeightedEffect
    crossingProb
  have hterm : ∀ j : Fin J,
      (∫ ω in S.crossingEvent z0 z1 j, S.marginResponse j ω ∂P.μ) =
        τ * (P.μ (S.crossingEvent z0 z1 j)).toReal := by
    intro j
    rw [MeasureTheory.setIntegral_congr_ae (S.measurableSet_crossingEvent z0 z1 j)
      ((hConstantResponse j).mono fun _ hx _ => hx)]
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def]
    exact smul_eq_mul _ _ |>.trans (mul_comm _ _)
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
  have hpos : 0 < ∑ j : Fin J, (P.μ (S.crossingEvent z0 z1 j)).toReal := by
    simpa [crossingProb] using (by
      rw [← S.firstStage_eq_sum_crossingProb hValid]
      exact hValid.hRelevance : 0 < ∑ j : Fin J, S.crossingProb z0 z1 j)
  field_simp [ne_of_gt hpos]

/-- Margin-specific response average specialization. -/
theorem wald_eq_marginResponseAverage {z0 z1 : 𝒵} (m : Fin J → ℝ)
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal)
    (hMarginResponse : ∀ j : Fin J, m j = S.conditionalMarginResponse z0 z1 j) :
    S.wald z0 z1 = ∑ j : Fin J, S.crossingWeight z0 z1 j * m j := by
  rw [S.wald_eq_averageCausalResponse hValid hCell0 hCell1]
  simp [averageCausalResponse, hMarginResponse]

end SpecialCases

/-- Centered finite instrument score used to define an interface-only
population 2SLS estimand for multivalued instruments. -/
structure PopulationTwoSLSScore (k : ℕ) where
  /-- Instrument score `S(z) ∈ ℝ^k`. -/
  score : 𝒵 → Fin k → ℝ
  /-- Population first-stage projection coefficient. -/
  gammaD : Fin k → ℝ
  /-- Centering of each score coordinate. -/
  centered : ∀ r : Fin k, ∫ ω, score (S.factualZ ω) r ∂P.μ = 0
  /-- Nonzero one-endogenous-regressor denominator. -/
  denom_nonzero :
    ∫ ω, (∑ r : Fin k, gammaD r * score (S.factualZ ω) r) *
      OrderedTreatment.intensityValue (S.factualD ω) ∂P.μ ≠ 0

namespace PopulationTwoSLSScore

variable {S} (T : S.PopulationTwoSLSScore k)

/-- First-stage fitted treatment `D_S(ω) = γ_D^T S(Z(ω))`; the linear projection
of `D` onto the instrument score. -/
def fittedTreatment : P.Ω → ℝ :=
  fun ω => ∑ r : Fin k, T.gammaD r * T.score (S.factualZ ω) r

/-- Population 2SLS estimand `β_2SLS(S) = E[D_S Y] / E[D_S D]`.
This declaration is only the population ratio interface: the file does not
derive the binary-instrument bridge `beta2SLS T = wald z0 z1`. Such a bridge
would require centering algebra and the scalar FWL identity for a score of the
form `S(Z) = Z - E[Z]`. -/
def beta2SLS : ℝ :=
  (∫ ω, T.fittedTreatment ω * S.factualY ω ∂P.μ) /
    (∫ ω, T.fittedTreatment ω * OrderedTreatment.intensityValue (S.factualD ω) ∂P.μ)

end PopulationTwoSLSScore

/-- Deferred interface for expanding a multivalued-instrument 2SLS estimand into
finite directed contrasts.  A later theorem can add sign-alignment assumptions
to turn this signed decomposition into a convex ACR average.

The fields `reducedForm_decomp` and `firstStage_decomp` are assumed hypotheses,
not derived theorems. Deriving them requires a finite signed decomposition of
`E[D_S Y]` and `E[D_S D]` into cell contrasts via the law of total expectation,
plus measure-backed covariance algebra and sign-alignment conditions beyond this
interface. -/
structure TwoSLSContrastDecomposition {k : ℕ} (T : S.PopulationTwoSLSScore k) where
  /-- Signed weight on an ordered instrument-cell contrast. -/
  contrastWeight : 𝒵 × 𝒵 → ℝ
  /-- First-stage contribution attached to each ordered contrast. -/
  pairFirstStage : 𝒵 × 𝒵 → ℝ
  /-- Reduced-form contribution attached to each ordered contrast. -/
  pairReducedForm : 𝒵 × 𝒵 → ℝ
  /-- Reduced-form expansion into finite ordered contrasts, carried as a
  field of the decomposition interface. -/
  reducedForm_decomp :
    ∫ ω, T.fittedTreatment ω * S.factualY ω ∂P.μ =
      ∑ p : 𝒵 × 𝒵, contrastWeight p * pairReducedForm p
  /-- First-stage expansion into finite ordered contrasts, carried as a field
  of the decomposition interface. -/
  firstStage_decomp :
    ∫ ω, T.fittedTreatment ω * OrderedTreatment.intensityValue (S.factualD ω) ∂P.μ =
      ∑ p : 𝒵 × 𝒵, contrastWeight p * pairFirstStage p

end VariableIntensityIVSystem
end
end VariableIntensityIV
end PO.ID.Exact
end Causalean
