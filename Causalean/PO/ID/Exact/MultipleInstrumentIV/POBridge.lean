/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Potential-outcome layer for the Mogstad-Torgovitsky-Walters multiple-IV algebra

This file puts the finite MTW response-type algebra (`FiniteIndex`,
`ResponseTypeStats`, `PopulationBridge`, `ObservedBridge`) on top of an explicit
potential-outcome system. It discharges the two transferred-assumption fields of
`ObservedBridge` (`outcome_cell`, `treatment_cell`) by deriving
the instrument-cell conditional means from consistency and instrument
independence, exactly as `PO/ID/Exact/LATE.lean` does for the binary-instrument
Wald ratio.

The construction:

* `POMultipleIVSystem` records a `Fin K`-valued instrument `Z`, a binary
  treatment `D`, and a real outcome `Y` inside a `POSystem`.
* The response type of a unit is `G = (D(z⁰), …, D(z^{K-1}))`, a genuine
  counterfactual object; its masses and within-type conditional effects
  `Δ_g = E[Y(1)-Y(0) | G=g]` populate the finite `ResponseTypeStats`.
* `Assumptions` requires consistency and, for each support point, instrument
  independence `Z ⟂ (D(zᵏ), Y(1), Y(0))` (the IV exogeneity condition).
* The end result restates the observed 2SLS ratio `E[h(Z)Y]/E[h(Z)D]` as the
  response-type weighted sum `Σ_g ω_g Δ_g` in real PO language.

Source labels: `def:po-estimand-mtw-system`, `ass:po-estimand-mtw-iv-validity`,
`thm:po-estimand-mtw-signed-decomposition`, `prop:po-estimand-mtw-response-type-form`.
NL artifact: `doc/basic_concepts/po/estimand_characterization/mogstad_torgovitsky_walters_multiple_iv.md`.
-/

import Causalean.PO.ID.Exact.MultipleInstrumentIV.Main
import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Conditioning.EventCondExp
/-! # Multiple-Instrument IV Potential-Outcome Bridge

This file grounds the MTW multiple-instrument finite algebra in a
potential-outcome system. The structure `POMultipleIVSystem` records a finite
instrument, binary treatment, and real outcome; `responseType`, `mass`,
`effect`, `toStats`, and `toPopulationBridge` turn its counterfactual response
types into the finite response-type algebra.

The bridge lemmas `treatmentDrop` and `outcomeDrop` derive instrument-cell
conditional means from consistency and instrument independence. The definitions
`toObservedBridge` and theorem
`observedBeta2SLS_eq_responseTypeWeightedSum` assemble those derived cell
identities into the observed MTW 2SLS characterization. -/

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset MeasureTheory ProbabilityTheory Causalean.PO

noncomputable section

/-- A multiple-instrument IV subsystem records a finite `Fin K`-valued
instrument, a binary treatment, and a real outcome inside a potential-outcome
system. This is the `Fin K` generalization of `PO.POIVSystem`. -/
structure POMultipleIVSystem (P : Causalean.PO.POSystem) (K : ℕ) where
  /-- Instrument node. -/
  Z : P.V
  /-- Treatment node. -/
  D : P.V
  /-- Outcome node. -/
  Y : P.V
  /-- The instrument value space is a `Fin K` support. -/
  hZfin : P.X Z ≃ᵐ Fin K
  /-- The treatment is binary. -/
  hDbool : P.X D ≃ᵐ Bool
  /-- The outcome is real. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- The instrument and treatment are distinct nodes. -/
  hZD : Z ≠ D
  /-- The treatment and outcome are distinct nodes. -/
  hDY : D ≠ Y
  /-- The instrument and outcome are distinct nodes. -/
  hZY : Z ≠ Y

namespace POMultipleIVSystem

variable {P : Causalean.PO.POSystem} {K : ℕ} (S : POMultipleIVSystem P K)

/-- Instrument packaged as a `POVar` valued in `Fin K`. -/
def zVar : POVar P (Fin K) := ⟨S.Z, S.hZfin⟩

/-- Treatment packaged as a `POVar` valued in `Bool`. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- Outcome packaged as a `POVar` valued in `ℝ`. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- Potential treatment `D(zᵏ)` under fixing the instrument to support point
`k`. -/
def DofZ (k : Fin K) : P.Ω → Bool := S.dVar.cfUnder S.zVar k

/-- Potential outcome `Y(d)` under fixing the treatment to `d`. -/
def YofD (d : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- Factual instrument `Z`. -/
def factualZ : P.Ω → Fin K := S.zVar.factual

/-- Factual treatment `D`. -/
def factualD : P.Ω → Bool := S.dVar.factual

/-- Factual outcome `Y`. -/
def factualY : P.Ω → ℝ := S.yVar.factual

/-- Response type `G(ω) = (D(z⁰)(ω), …, D(z^{K-1})(ω))`, the vector of potential
treatments across the instrument support. -/
def responseType : P.Ω → ResponseType K := fun ω k => S.DofZ k ω

/-- The event `{G = g}` that a unit has response type `g`. -/
def gEvent (g : ResponseType K) : Set P.Ω := S.responseType ⁻¹' {g}

/-- The instrument cell `{Z = zᵏ}`. -/
def zEvent (k : Fin K) : Set P.Ω := S.zVar.event k

/-- Potential outcome under the treatment that instrument value `zᵏ` induces,
`Y(D(zᵏ)) = 1_{D(zᵏ)=1} Y(1) + 1_{D(zᵏ)=0} Y(0)`. -/
def YofDofZ (k : Fin K) : P.Ω → ℝ :=
  fun ω => if S.DofZ k ω then S.YofD true ω else S.YofD false ω

/-- Regimed variable `D(zᵏ)` (treatment under instrument set to `zᵏ`). -/
def dUnderZ (k : Fin K) : RegimedVar P Bool :=
  ⟨S.dVar, Regime.single S.Z (S.hZfin.symm k)⟩

/-- Regimed variable `Y(d)` (outcome under treatment set to `d`). -/
def yUnderD (d : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩

/-- The three-element counterfactual cell `(D(zᵏ), Y(1), Y(0))` relevant to
identifying the conditional means on `{Z = zᵏ}`. Coordinates: `0 ↦ D(zᵏ)`,
`1 ↦ Y(1)`, `2 ↦ Y(0)`. -/
def cfCell (k : Fin K) : POCFBundle P :=
  POCFBundle.cons (S.dUnderZ k) <|
  POCFBundle.cons (S.yUnderD true) <|
  POCFBundle.cons (S.yUnderD false) <|
  POCFBundle.nil P

/-! ### Measurability -/

/-- The potential treatment under any instrument support point is measurable. -/
lemma measurable_DofZ (k : Fin K) : Measurable (S.DofZ k) :=
  S.dVar.measurable_cfUnder S.zVar k

/-- The potential outcome under either treatment arm is measurable. -/
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- The factual instrument value is measurable. -/
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual

/-- The factual treatment value is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- The factual outcome value is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- The response-type map collecting all treatment responses is measurable. -/
lemma measurable_responseType : Measurable S.responseType :=
  measurable_pi_lambda _ (fun k => S.measurable_DofZ k)

/-- Each response-type cell is measurable. -/
lemma measurableSet_gEvent (g : ResponseType K) : MeasurableSet (S.gEvent g) :=
  S.measurable_responseType (measurableSet_singleton g)

/-- Each instrument support cell is measurable. -/
lemma measurableSet_zEvent (k : Fin K) : MeasurableSet (S.zEvent k) :=
  S.zVar.measurableSet_event k

/-- The outcome under the treatment induced by an instrument support point is measurable. -/
lemma measurable_YofDofZ (k : Fin K) : Measurable (S.YofDofZ k) := by
  unfold YofDofZ
  exact Measurable.ite (S.measurable_DofZ k (MeasurableSet.singleton true))
    (S.measurable_YofD true) (S.measurable_YofD false)

/-! ### Assumptions -/

/-- Classical multiple-instrument IV assumptions -- `ass:po-estimand-mtw-iv-validity`.

Exclusion is encoded by the `Y(d)` interface (outcomes carry no `z` argument, so
the instrument cannot affect `Y` except through `D`), exactly as in
`PO.POIVSystem`. -/
structure Assumptions (S : POMultipleIVSystem P K) : Prop where
  /-- Consistency (SUTVA): observed `D`/`Y` equal the realized potential
  treatment/outcome. -/
  consistency : P.Consistency
  /-- Instrument independence (IV exogeneity): for each support point, the
  instrument is independent of the counterfactual cell `(D(zᵏ), Y(1), Y(0))`.
  This is implied by (and weaker than) full joint independence of `Z` from all
  potential outcomes; it is exactly what the cell-conditional-mean derivations
  below consume. -/
  instrumentIndep :
    ∀ k : Fin K, P.IndepCF (RegimedVar.ofFactual S.zVar) (S.cfCell k) P.μ

/-! ### Consistency-on-cell rewrites -/

/-- On `{Z = zᵏ}`, the counterfactual treatment `D(zᵏ)` equals the factual `D`. -/
lemma DofZ_eq_factualD_on_zEvent (hA : S.Assumptions) (k : Fin K)
    {ω : P.Ω} (hω : ω ∈ S.zEvent k) :
    S.DofZ k ω = S.factualD ω :=
  POVar.cf_eq_factual_on_event hA.consistency S.dVar S.zVar k S.hZD.symm hω

/-- Factual `Y` equals `Y(factualD)` pointwise. -/
lemma factualY_eq_YofD_factualD (hA : S.Assumptions) (ω : P.Ω) :
    S.factualY ω = S.YofD (S.factualD ω) ω :=
  POVar.factual_eq_cfUnder_self_selected hA.consistency S.yVar S.dVar S.hDY.symm ω

/-- On `{G = g}`, the potential treatment `D(zᵏ)` is the constant `g k`. -/
lemma DofZ_eq_on_gEvent (g : ResponseType K) (k : Fin K)
    {ω : P.Ω} (hω : ω ∈ S.gEvent g) :
    S.DofZ k ω = g k := by
  have : S.responseType ω = g := hω
  calc S.DofZ k ω = S.responseType ω k := rfl
    _ = g k := by rw [this]

/-! ### Drop-of-conditioning at the instrument cell (uses `instrumentIndep`)

These two lemmas are the `Fin K` analogues of the LATE first-stage / reduced-form
"Step 1" computations. On `{Z = zᵏ}`, consistency rewrites the factual integrand
into a measurable projection of the counterfactual cell `(D(zᵏ), Y(1), Y(0))`,
and instrument independence drops the conditioning. -/

/-- `E[D | Z = zᵏ] = E[D(zᵏ)]` (0/1-coded). -/
theorem treatmentDrop [IsFiniteMeasure P.μ] (hA : S.Assumptions) (k : Fin K)
    (hZk : P.μ (S.zEvent k) ≠ 0) :
    eventCondExp P.μ (S.zEvent k) (fun ω => boolToReal (S.factualD ω))
      = ∫ ω, boolToReal (S.DofZ k ω) ∂P.μ := by
  let h_proj : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => boolToReal ((f (0 : Fin 3)) : Bool)
  have hh_meas : Measurable h_proj := by
    change Measurable fun f : ∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i =>
      boolToReal ((f (0 : Fin 3)) : Bool)
    exact (by fun_prop : Measurable fun b : Bool => boolToReal b).comp
      (measurable_pi_apply (0 : Fin 3))
  have hF_eq : ∀ ω ∈ S.zVar.event k,
      boolToReal (S.factualD ω) = h_proj ((S.cfCell k).jointValue ω) := by
    intro ω hω
    rw [← S.DofZ_eq_factualD_on_zEvent hA k hω]
    dsimp [h_proj]
    have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
    rw [hJV0]
  change eventCondExp P.μ (S.zVar.event k) (fun ω => boolToReal (S.factualD ω))
      = ∫ ω, boolToReal (S.DofZ k ω) ∂P.μ
  rw [POSystem.eventCondExp_of_consistency_IndepCF (hA.instrumentIndep k)
    (a := S.zVar) hh_meas hF_eq hZk (measure_ne_top _ _)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  dsimp [h_proj]
  have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
  rw [hJV0]

/-- `E[Y | Z = zᵏ] = E[Y(D(zᵏ))]`. -/
theorem outcomeDrop [IsFiniteMeasure P.μ] (hA : S.Assumptions) (k : Fin K)
    (hZk : P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ) :
    eventCondExp P.μ (S.zEvent k) S.factualY = ∫ ω, S.YofDofZ k ω ∂P.μ := by
  have _hY1 : Integrable (S.YofD true) P.μ := hY1
  have _hY0 : Integrable (S.YofD false) P.μ := hY0
  let getD : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → Bool :=
    fun f => ((f (0 : Fin 3)) : Bool)
  let getY1 : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => ((f (1 : Fin 3)) : ℝ)
  let getY0 : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => ((f (2 : Fin 3)) : ℝ)
  let h_proj : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => cond (getD f) (getY1 f) (getY0 f)
  have hh_meas : Measurable h_proj := by
    have hD_meas : Measurable getD := by
      dsimp [getD]
      exact measurable_pi_apply (0 : Fin 3)
    have hY1_meas : Measurable getY1 := by
      dsimp [getY1]
      exact measurable_pi_apply (1 : Fin 3)
    have hY0_meas : Measurable getY0 := by
      dsimp [getY0]
      exact measurable_pi_apply (2 : Fin 3)
    have hif : Measurable fun f =>
        if getD f = true then getY1 f else getY0 f := by
      refine Measurable.ite ?_ ?_ ?_
      · exact hD_meas (MeasurableSet.singleton true)
      · exact hY1_meas
      · exact hY0_meas
    simpa [h_proj, Bool.cond_eq_ite] using hif
  have hF_eq : ∀ ω ∈ S.zVar.event k,
      S.factualY ω = h_proj ((S.cfCell k).jointValue ω) := by
    intro ω hω
    rw [S.factualY_eq_YofD_factualD hA ω,
      ← S.DofZ_eq_factualD_on_zEvent hA k hω]
    dsimp [h_proj, getD, getY1, getY0]
    have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
    have hJV1 : ((S.cfCell k).jointValue ω (1 : Fin 3) : ℝ) = S.YofD true ω := rfl
    have hJV2 : ((S.cfCell k).jointValue ω (2 : Fin 3) : ℝ) = S.YofD false ω := rfl
    rw [hJV0, hJV1, hJV2]
    cases S.DofZ k ω <;> simp
  change eventCondExp P.μ (S.zVar.event k) S.factualY = ∫ ω, S.YofDofZ k ω ∂P.μ
  rw [POSystem.eventCondExp_of_consistency_IndepCF (hA.instrumentIndep k)
    (a := S.zVar) hh_meas hF_eq hZk (measure_ne_top _ _)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  dsimp [h_proj, getD, getY1, getY0]
  have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
  have hJV1 : ((S.cfCell k).jointValue ω (1 : Fin 3) : ℝ) = S.YofD true ω := rfl
  have hJV2 : ((S.cfCell k).jointValue ω (2 : Fin 3) : ℝ) = S.YofD false ω := rfl
  rw [hJV0, hJV1, hJV2]
  unfold YofDofZ
  cases S.DofZ k ω <;> simp

/-! ### Response-type total-law partition (pure measure theory, no independence)

The response type `G` partitions the sample space; the law of total expectation
rewrites the unconditional integrals from the drop step as finite sums over
response types. -/

/-- The response-type events are pairwise disjoint. -/
lemma gEvent_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint S.gEvent) := by
  intro g h hgh
  refine Set.disjoint_left.mpr ?_
  intro ω hg hh
  exact hgh ((Set.mem_singleton_iff.mp hg).symm.trans (Set.mem_singleton_iff.mp hh))

/-- The response-type events cover the sample space. -/
lemma gEvent_iUnion : (⋃ g : ResponseType K, S.gEvent g) = Set.univ := by
  ext ω; simp [gEvent]

/-- Total law over response types for an integrable integrand. -/
lemma integral_partition [IsFiniteMeasure P.μ] {f : P.Ω → ℝ} (hf : Integrable f P.μ) :
    ∫ ω, f ω ∂P.μ
      = ∑ g : ResponseType K, (P.μ (S.gEvent g)).toReal * eventCondExp P.μ (S.gEvent g) f :=
  integral_eq_sum_measure_mul_eventCondExp P.μ S.gEvent S.measurableSet_gEvent
    S.gEvent_pairwise_disjoint S.gEvent_iUnion f hf

/-! ### Finite masses, effects, and baseline terms populating the algebra -/

/-- Response-type mass `π_g = P(G = g)`. -/
def mass (g : ResponseType K) : ℝ := (P.μ (S.gEvent g)).toReal

/-- Within-type conditional causal effect `Δ_g = E[Y(1) - Y(0) | G = g]`. -/
def effect (g : ResponseType K) : ℝ :=
  eventCondExp P.μ (S.gEvent g) (fun ω => S.YofD true ω - S.YofD false ω)

/-- Reference support point `z⁰` (requires `0 < K`). -/
def z0 (_S : POMultipleIVSystem P K) (hK : 0 < K) : Fin K := ⟨0, hK⟩

/-- Baseline response-type outcome `E[Y(D(z⁰)) | G = g]`, the term the centered
first-stage index cancels. -/
def baseOutcome (hK : 0 < K) (g : ResponseType K) : ℝ :=
  eventCondExp P.μ (S.gEvent g) (S.YofDofZ (S.z0 hK))

/-- Baseline treatment mean `E[D(z⁰)]`. -/
def baseTreatment (hK : 0 < K) : ℝ :=
  ∫ ω, boolToReal (S.DofZ (S.z0 hK) ω) ∂P.μ

/-- Response-type masses are nonnegative because they are real-valued probabilities. -/
lemma mass_nonneg (g : ResponseType K) : 0 ≤ S.mass g := ENNReal.toReal_nonneg

/-- Response-type masses sum to one. -/
lemma mass_sum_one : ∑ g : ResponseType K, S.mass g = 1 := by
  have hsum :
      (Finset.univ).sum
          (fun g : ResponseType K =>
            (P.μ (S.responseType ⁻¹' ({g} : Set (ResponseType K)))).toReal) =
        (P.μ (S.responseType ⁻¹' (Set.univ : Set (ResponseType K)))).toReal := by
    simpa [Measure.real] using
      (MeasureTheory.sum_measureReal_preimage_singleton
        (μ := P.μ) (s := (Finset.univ : Finset (ResponseType K)))
        (f := S.responseType)
        (hf := by
          intro g _hg
          exact S.measurable_responseType (measurableSet_singleton g))
        (h := by
          intro g _hg
          exact measure_ne_top _ _))
  simpa [mass, gEvent, Set.preimage_univ, IsProbabilityMeasure.measure_univ] using hsum

/-- Finite response-type statistics assembled from the PO system. -/
def toStats : ResponseTypeStats K where
  mass := S.mass
  effect := S.effect
  mass_nonneg := S.mass_nonneg
  mass_sum_one := S.mass_sum_one

/-- Saturated finite-support population bridge assembled from the PO system. -/
def toPopulationBridge (hK : 0 < K) : ResponseTypeStats.PopulationBridge K where
  stats := S.toStats
  baseOutcome := S.baseOutcome hK

/-- Ordered finite index built from the instrument masses and a supplied
saturated first-stage score. -/
def toFiniteIndex (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l) :
    FiniteIndex K :=
  FiniteIndex.fromMeasureScore P.μ S.factualZ S.measurable_factualZ dhat hmono

/-! ### Telescoping identity -/

/-- The telescoped adjacent step at support point `k` collapses to the difference
of endpoint treatments: `Σ_{j≤k}(d_j - d_{j-1}) = g k - g 0`. -/
lemma telescoped_eq (hK : 0 < K) (g : ResponseType K) (k : Fin K) :
    ResponseTypeStats.PopulationBridge.telescopedTypeStep g k
      = boolToReal (g k) - boolToReal (g (S.z0 hK)) := by
  classical
  let a : ℕ → ℝ := fun n => if h : n < K then boolToReal (g ⟨n, h⟩) else 0
  have htel : ∀ n : ℕ, (∑ r ∈ Finset.range n, (a (r + 1) - a r)) = a n - a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hsum :
      (∑ j ∈ (Finset.univ.filter fun j : Adj K => j.1.val ≤ k.val), typeStep g j)
        = ∑ r ∈ Finset.range k.val, (a (r + 1) - a r) := by
    refine Finset.sum_nbij (fun j : Adj K => j.1.val - 1) ?_ ?_ ?_ ?_
    · intro j hj
      have hjle : j.1.val ≤ k.val := by simpa using hj
      rw [Finset.mem_range]
      change j.1.val - 1 < k.val
      have hpos : 0 < j.1.val := j.2
      omega
    · intro j1 hj1 j2 hj2 h
      apply Subtype.ext
      apply Fin.ext
      have hj1le : j1.1.val ≤ k.val := by simpa using hj1
      have hj2le : j2.1.val ≤ k.val := by simpa using hj2
      have hpos1 : 0 < j1.1.val := j1.2
      have hpos2 : 0 < j2.1.val := j2.2
      change j1.1.val - 1 = j2.1.val - 1 at h
      omega
    · intro r hr
      have hrlt : r < k.val := by simpa using hr
      refine ⟨⟨⟨r + 1, ?_⟩, ?_⟩, ?_, ?_⟩
      · exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hrlt) k.isLt
      · exact Nat.succ_pos r
      · simpa using (show r + 1 ≤ k.val by omega)
      · change r + 1 - 1 = r
        omega
    · intro j hj
      have hjle : j.1.val ≤ k.val := by simpa using hj
      have hsucc : j.1.val - 1 + 1 = j.1.val :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt j.2)
      have hpred_lt : j.1.val - 1 < K :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.1.isLt
      simp [typeStep, Adj.upper, Adj.lower, a, hpred_lt, hsucc]
  unfold ResponseTypeStats.PopulationBridge.telescopedTypeStep
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [hsum, htel]
  have hak : a k.val = boolToReal (g k) := by
    simp [a, k.isLt]
  have ha0 : a 0 = boolToReal (g (S.z0 hK)) := by
    simp [a, hK, z0]
  rw [hak, ha0]

/-! ### Cell identities discharging the ObservedBridge transferred assumptions -/

/-- Treatment cell identity: `E[D | Z = zᵏ] = baseTreatment + treatmentAtSupport k`. -/
theorem treatment_cell_eq [IsFiniteMeasure P.μ] (hK : 0 < K) (hA : S.Assumptions)
    (k : Fin K) (hZk : P.μ (S.zEvent k) ≠ 0) :
    eventCondExp P.μ (S.zEvent k) (fun ω => boolToReal (S.factualD ω))
      = S.baseTreatment hK
        + (S.toPopulationBridge hK).treatmentAtSupport k := by
  have hDint : ∀ q : Fin K, Integrable (fun ω => boolToReal (S.DofZ q ω)) P.μ := by
    intro q
    have hbdd : ∀ ω, |boolToReal (S.DofZ q ω)| ≤ (1 : ℝ) := by
      intro ω
      cases S.DofZ q ω <;> simp [boolToReal]
    exact (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (((by fun_prop : Measurable fun b : Bool => boolToReal b).comp
        (S.measurable_DofZ q)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbdd)
  have hCell : ∀ (q : Fin K) (g : ResponseType K),
      S.mass g * eventCondExp P.μ (S.gEvent g) (fun ω => boolToReal (S.DofZ q ω)) =
        S.mass g * boolToReal (g q) := by
    intro q g
    calc
      S.mass g * eventCondExp P.μ (S.gEvent g) (fun ω => boolToReal (S.DofZ q ω)) =
          eventCondExp P.μ (S.gEvent g) (fun ω => boolToReal (S.DofZ q ω)) * S.mass g := by
        ring
      _ = ∫ ω in S.gEvent g, boolToReal (S.DofZ q ω) ∂P.μ := by
        rw [mass, eventCondExp_mul_measure_toReal]
      _ = ∫ ω in S.gEvent g, boolToReal (g q) ∂P.μ := by
        refine MeasureTheory.setIntegral_congr_fun (S.measurableSet_gEvent g) ?_
        intro ω hω
        dsimp
        rw [S.DofZ_eq_on_gEvent g q hω]
      _ = boolToReal (g q) * S.mass g := by
        simp [mass, Measure.real, mul_comm]
      _ = S.mass g * boolToReal (g q) := by
        ring
  have hInt : ∫ ω, boolToReal (S.DofZ k ω) ∂P.μ =
      ∑ g : ResponseType K, S.mass g * boolToReal (g k) := by
    rw [S.integral_partition (hDint k)]
    refine Finset.sum_congr rfl ?_
    intro g _
    simpa [mass] using hCell k g
  have hBase : S.baseTreatment hK =
      ∑ g : ResponseType K, S.mass g * boolToReal (g (S.z0 hK)) := by
    unfold baseTreatment
    rw [S.integral_partition (hDint (S.z0 hK))]
    refine Finset.sum_congr rfl ?_
    intro g _
    simpa [mass] using hCell (S.z0 hK) g
  have hTreat : (S.toPopulationBridge hK).treatmentAtSupport k =
      ∑ g : ResponseType K,
        S.mass g * (boolToReal (g k) - boolToReal (g (S.z0 hK))) := by
    unfold ResponseTypeStats.PopulationBridge.treatmentAtSupport toPopulationBridge toStats
    refine Finset.sum_congr rfl ?_
    intro g _
    rw [S.telescoped_eq hK g k]
  rw [S.treatmentDrop hA k hZk, hInt, hBase, hTreat]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro g _
  ring

/-- Outcome cell identity: `E[Y | Z = zᵏ] = outcomeAtSupport k`. -/
theorem outcome_cell_eq [IsFiniteMeasure P.μ] (hK : 0 < K) (hA : S.Assumptions)
    (k : Fin K) (hZk : P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ) :
    eventCondExp P.μ (S.zEvent k) S.factualY
      = (S.toPopulationBridge hK).outcomeAtSupport k := by
  have hYDZ_bdd : ∀ q : Fin K, ∀ ω,
      |S.YofDofZ q ω| ≤ |S.YofD true ω| + |S.YofD false ω| := by
    intro q ω
    have h1 := abs_nonneg (S.YofD true ω)
    have h0 := abs_nonneg (S.YofD false ω)
    unfold YofDofZ
    cases S.DofZ q ω <;> simp [h1, h0]
  have hYDZ_int : ∀ q : Fin K, Integrable (S.YofDofZ q) P.μ := by
    intro q
    exact (hY1.norm.add hY0.norm).mono' (S.measurable_YofDofZ q).aestronglyMeasurable
      (Filter.Eventually.of_forall (hYDZ_bdd q))
  have hCE : ∀ (q : Fin K) (g : ResponseType K),
      eventCondExp P.μ (S.gEvent g) (S.YofDofZ q) =
        eventCondExp P.μ (S.gEvent g) (S.YofD false) +
          boolToReal (g q) * S.effect g := by
    intro q g
    let c : ℝ := boolToReal (g q)
    have hcongr : eventCondExp P.μ (S.gEvent g) (S.YofDofZ q) =
        eventCondExp P.μ (S.gEvent g)
          (fun ω => S.YofD false ω + c * (S.YofD true ω - S.YofD false ω)) := by
      apply eventCondExp_congr_on P.μ (S.measurableSet_gEvent g)
      intro ω hω
      unfold YofDofZ
      rw [S.DofZ_eq_on_gEvent g q hω]
      dsimp [c]
      cases g q <;> simp [boolToReal]
    calc
      eventCondExp P.μ (S.gEvent g) (S.YofDofZ q) =
          eventCondExp P.μ (S.gEvent g)
            (fun ω => S.YofD false ω + c * (S.YofD true ω - S.YofD false ω)) := hcongr
      _ = eventCondExp P.μ (S.gEvent g) (S.YofD false) +
            eventCondExp P.μ (S.gEvent g) (fun ω => c * (S.YofD true ω - S.YofD false ω)) := by
        change eventCondExp P.μ (S.gEvent g)
            ((S.YofD false) + fun ω => c * (S.YofD true ω - S.YofD false ω)) =
          eventCondExp P.μ (S.gEvent g) (S.YofD false) +
            eventCondExp P.μ (S.gEvent g) (fun ω => c * (S.YofD true ω - S.YofD false ω))
        rw [eventCondExp_add]
        · exact hY0.integrableOn
        · exact (hY1.integrableOn.sub hY0.integrableOn).const_mul c
      _ = eventCondExp P.μ (S.gEvent g) (S.YofD false) +
            c * eventCondExp P.μ (S.gEvent g) (fun ω => S.YofD true ω - S.YofD false ω) := by
        rw [eventCondExp_smul]
      _ = eventCondExp P.μ (S.gEvent g) (S.YofD false) + boolToReal (g q) * S.effect g := by
        rfl
  have hTerm : ∀ g : ResponseType K,
      eventCondExp P.μ (S.gEvent g) (S.YofDofZ k) =
        S.baseOutcome hK g +
          ResponseTypeStats.PopulationBridge.telescopedTypeStep g k * S.effect g := by
    intro g
    unfold baseOutcome
    rw [hCE k g, hCE (S.z0 hK) g, S.telescoped_eq hK g k]
    ring
  have hInt : ∫ ω, S.YofDofZ k ω ∂P.μ =
      ∑ g : ResponseType K,
        S.mass g * eventCondExp P.μ (S.gEvent g) (S.YofDofZ k) := by
    rw [S.integral_partition (hYDZ_int k)]
    refine Finset.sum_congr rfl ?_
    intro g _
    rfl
  rw [S.outcomeDrop hA k hZk hY1 hY0, hInt]
  unfold ResponseTypeStats.PopulationBridge.outcomeAtSupport toPopulationBridge toStats
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [hTerm g]

/-! ### Assembled observed bridge and the potential-outcome 2SLS characterization -/

/-- The instrument masses `ρ_k` from `toFiniteIndex` are the probabilities of the
observed instrument cells. -/
lemma rho_eq_zMass (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l) (k : Fin K) :
    (S.toFiniteIndex dhat hmono).rho k
      = (P.μ (ResponseTypeStats.PopulationBridge.zEvent S.factualZ k)).toReal := by
  rfl

/-- The observed bridge assembled from the PO system, with the two conditional-mean
fields *derived* (not assumed) from consistency and instrument independence. -/
def toObservedBridge (hK : 0 < K) (hA : S.Assumptions)
    (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l)
    (hZpos : ∀ k : Fin K, P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ) :
    ResponseTypeStats.PopulationBridge.ObservedBridge P.μ S.factualZ S.factualD
      S.factualY (S.toFiniteIndex dhat hmono) (S.toPopulationBridge hK) where
  isProbability := P.isProb
  rho_eq_zMass := S.rho_eq_zMass dhat hmono
  outcome_cell := fun k =>
    S.outcome_cell_eq hK hA k (hZpos k) hY1 hY0
  baseTreatment := S.baseTreatment hK
  treatment_cell := fun k =>
    S.treatment_cell_eq hK hA k (hZpos k)

/-- **Potential-outcome multiple-IV 2SLS characterization**
(`prop:po-estimand-mtw-response-type-form`, PO level).

The observed 2SLS ratio `E[h(Z)Y] / E[h(Z)D]` equals the response-type weighted
sum `Σ_g ω_g Δ_g`, where the weights `ω_g` are the normalized MTW response-type
weights and `Δ_g = E[Y(1) - Y(0) | G = g]` is the within-type conditional causal
effect. The conditional-mean bridges are derived from consistency and instrument
independence, so this consumes only genuine potential-outcome assumptions. -/
theorem observedBeta2SLS_eq_responseTypeWeightedSum
    [IsFiniteMeasure P.μ] (hK : 0 < K) (hA : S.Assumptions)
    (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l)
    (hZpos : ∀ k : Fin K, P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ)
    (hYInt : Integrable
      (fun ω => (S.toFiniteIndex dhat hmono).centeredIndex (S.factualZ ω) * S.factualY ω) P.μ)
    (hDInt : Integrable
      (fun ω => (S.toFiniteIndex dhat hmono).centeredIndex (S.factualZ ω)
        * boolToReal (S.factualD ω)) P.μ)
    (hden : ResponseTypeStats.PopulationBridge.observedFirstStageMoment
      P.μ S.factualZ S.factualD (S.toFiniteIndex dhat hmono) ≠ 0) :
    ResponseTypeStats.PopulationBridge.observedBeta2SLS
        P.μ S.factualZ S.factualD S.factualY (S.toFiniteIndex dhat hmono)
      = (S.toPopulationBridge hK).stats.responseTypeEstimand (S.toFiniteIndex dhat hmono) :=
  (S.toObservedBridge hK hA dhat hmono hZpos hY1 hY0).observedBeta2SLS_eq_responseTypeWeightedSum
    S.measurable_factualZ hYInt hDInt hden

end POMultipleIVSystem

end

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
