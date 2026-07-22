/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-Period Dynamic LATE: data layer

The `PODynLATESystem` structure (def:po-dynamic-late-system) plus all basic
accessors, regimes, counterfactual maps, history bundles, observable
nested-regression functionals, the assumption bundle (def:po-dynamic-late-assumptions),
and the target functionals (def:po-dynamic-late) for the two-period dynamic
IV/LATE setting of Sojitra (2025).  No proof of the bridge identities or
ratio identifications lives here -- see `Bridges.lean` and `WhenToTreat.lean`.

Generalises `PO/ID/Exact/LATE.lean` to two periods with sequential
encouragements `Z₁, Z₂` and noncompliant treatments `D₁, D₂`, plus baseline /
intermediate state covariates `S₀ : POVar P γ₀`, `S₁ : POVar P γ₁`.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Conditioning.EventCondExp
import Causalean.PO.Conditioning.CondExpTooling
import Causalean.PO.Conditioning.Bundle
import Causalean.Mathlib.CondIndep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional

/-! # Two-Period Dynamic LATE Setup

This file defines the data, regimes, counterfactual variables, history
information, observable nested regressions, assumptions, and target parameters
for a two-period dynamic instrumental-variables LATE design. It supplies the
common interface used by the bridge and ratio-identification files.

The design has sequential binary encouragements and treatments, a baseline
state, an intermediate state, and a real outcome. It supports observable nested
regressions, dynamic LATE targets, when-to-treat targets, mixture targets, and
the dynamic IV/LATE assumption bundle. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A two-period dynamic instrumental-variable (LATE) model in the
potential-outcome framework. A unit is observed over two periods: baseline
covariates `S₀`, then in period 1 a binary encouragement / instrument `Z₁` and
the treatment `D₁` it shifts; an intermediate state `S₁`; then in period 2 a
second encouragement `Z₂` and treatment `D₂`; and finally a real outcome `Y`.
Sequential instrument variation identifies dynamic complier treatment effects
(`def:po-dynamic-late-system`).

`γ₀, γ₁` are the value spaces of the baseline and intermediate state covariates
`S₀, S₁`.  Encouragements `Z₁, Z₂` and treatments `D₁, D₂` are binary; the
outcome `Y` is real-valued.  All seven nodes are pairwise distinct, packaged via
`Function.Injective` on a `Fin 7 → P.V` accessor. -/
structure PODynLATESystem (P : POSystem) (γ₀ γ₁ : Type)
    [MeasurableSpace γ₀] [MeasurableSpace γ₁] where
  S0 : POVar P γ₀
  S1 : POVar P γ₁
  Z1 : P.V
  D1 : P.V
  Z2 : P.V
  D2 : P.V
  Y  : P.V
  hZ1bool : P.X Z1 ≃ᵐ Bool
  hD1bool : P.X D1 ≃ᵐ Bool
  hZ2bool : P.X Z2 ≃ᵐ Bool
  hD2bool : P.X D2 ≃ᵐ Bool
  hYreal  : P.X Y  ≃ᵐ ℝ
  /-- Pairwise distinctness of all seven atomic nodes. -/
  vars_inj : Function.Injective
    (![S0.v, S1.v, Z1, D1, Z2, D2, Y] : Fin 7 → P.V)

namespace PODynLATESystem

variable {P : POSystem} {γ₀ γ₁ : Type}
variable [MeasurableSpace γ₀] [MeasurableSpace γ₁]
variable (S : PODynLATESystem P γ₀ γ₁)

/-! ### POVar wrappers and factual maps -/

/-- The first encouragement is packaged as a binary potential-outcome variable. -/
def z1Var : POVar P Bool := ⟨S.Z1, S.hZ1bool⟩
/-- The second encouragement is packaged as a binary potential-outcome variable. -/
def z2Var : POVar P Bool := ⟨S.Z2, S.hZ2bool⟩
/-- The first treatment is packaged as a binary potential-outcome variable. -/
def d1Var : POVar P Bool := ⟨S.D1, S.hD1bool⟩
/-- The second treatment is packaged as a binary potential-outcome variable. -/
def d2Var : POVar P Bool := ⟨S.D2, S.hD2bool⟩
/-- The outcome is packaged as a real-valued potential-outcome variable. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- The factual baseline state is the observed baseline covariate value. -/
noncomputable def factualS0 : P.Ω → γ₀ := S.S0.factual
/-- The factual intermediate state is the observed intermediate covariate value. -/
noncomputable def factualS1 : P.Ω → γ₁ := S.S1.factual
/-- The factual first encouragement is the observed first-stage instrument value. -/
noncomputable def factualZ1 : P.Ω → Bool := S.z1Var.factual
/-- The factual second encouragement is the observed second-stage instrument value. -/
noncomputable def factualZ2 : P.Ω → Bool := S.z2Var.factual
/-- The factual first treatment is the observed first-stage treatment value. -/
noncomputable def factualD1 : P.Ω → Bool := S.d1Var.factual
/-- The factual second treatment is the observed second-stage treatment value. -/
noncomputable def factualD2 : P.Ω → Bool := S.d2Var.factual
/-- The factual outcome is the observed outcome value. -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-! ### Pairwise distinctness lemmas (extracted from `vars_inj`) -/

private abbrev varVec : Fin 7 → P.V :=
  ![S.S0.v, S.S1.v, S.Z1, S.D1, S.Z2, S.D2, S.Y]

private lemma varVec_apply_zero : S.varVec 0 = S.S0.v := rfl
private lemma varVec_apply_one : S.varVec 1 = S.S1.v := rfl
private lemma varVec_apply_two : S.varVec 2 = S.Z1 := rfl
private lemma varVec_apply_three : S.varVec 3 = S.D1 := rfl
private lemma varVec_apply_four : S.varVec 4 = S.Z2 := rfl
private lemma varVec_apply_five : S.varVec 5 = S.D2 := rfl
private lemma varVec_apply_six : S.varVec 6 = S.Y := rfl

/-- The most-used corollary: the two encouragement nodes are distinct. -/
lemma Z1_ne_Z2 : S.Z1 ≠ S.Z2 := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 4 by decide)
  simpa [varVec_apply_two, varVec_apply_four] using this

/-- The two treatment nodes are distinct. -/
lemma D1_ne_D2 : S.D1 ≠ S.D2 := by
  have := S.vars_inj.ne (show (3 : Fin 7) ≠ 5 by decide)
  simpa [varVec_apply_three, varVec_apply_five] using this

/-- `Y` is distinct from each treatment. -/
lemma D1_ne_Y : S.D1 ≠ S.Y := by
  have := S.vars_inj.ne (show (3 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_three, varVec_apply_six] using this

/-- The second treatment node is distinct from the outcome node. -/
lemma D2_ne_Y : S.D2 ≠ S.Y := by
  have := S.vars_inj.ne (show (5 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_five, varVec_apply_six] using this

/-- `Y` is distinct from each encouragement. -/
lemma Z1_ne_Y : S.Z1 ≠ S.Y := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_two, varVec_apply_six] using this

/-- The second encouragement node is distinct from the outcome node. -/
lemma Z2_ne_Y : S.Z2 ≠ S.Y := by
  have := S.vars_inj.ne (show (4 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_four, varVec_apply_six] using this

/-- Encouragements are distinct from treatments. -/
lemma Z1_ne_D1 : S.Z1 ≠ S.D1 := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 3 by decide)
  simpa [varVec_apply_two, varVec_apply_three] using this

/-- The first encouragement node is distinct from the second treatment node. -/
lemma Z1_ne_D2 : S.Z1 ≠ S.D2 := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 5 by decide)
  simpa [varVec_apply_two, varVec_apply_five] using this

/-- The second encouragement node is distinct from the first treatment node. -/
lemma Z2_ne_D1 : S.Z2 ≠ S.D1 := by
  have := S.vars_inj.ne (show (4 : Fin 7) ≠ 3 by decide)
  simpa [varVec_apply_four, varVec_apply_three] using this

/-- The second encouragement node is distinct from the second treatment node. -/
lemma Z2_ne_D2 : S.Z2 ≠ S.D2 := by
  have := S.vars_inj.ne (show (4 : Fin 7) ≠ 5 by decide)
  simpa [varVec_apply_four, varVec_apply_five] using this

/-! ### Two-target encouragement and treatment regimes (`Regime.ofList`) -/

/-- Regime fixing both encouragements: `Z₁ ↦ z 0, Z₂ ↦ z 1`. -/
noncomputable def encouragementRegime (z : Fin 2 → Bool) : Regime P.V P.X :=
  Regime.ofList
    [⟨S.Z1, S.hZ1bool.symm (z 0)⟩, ⟨S.Z2, S.hZ2bool.symm (z 1)⟩]
    (by
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
      exact S.Z1_ne_Z2)

/-- Regime fixing both treatments: `D₁ ↦ d 0, D₂ ↦ d 1`. -/
noncomputable def treatmentRegime (d : Fin 2 → Bool) : Regime P.V P.X :=
  Regime.ofList
    [⟨S.D1, S.hD1bool.symm (d 0)⟩, ⟨S.D2, S.hD2bool.symm (d 1)⟩]
    (by
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
      exact S.D1_ne_D2)

/-- Regime fixing only the stage-2 encouragement: `Z₂ ↦ z₂`.  Used in the
stage-2 ignorability condition where `Z₁` remains factual. -/
noncomputable def encZ2Regime (z₂ : Bool) : Regime P.V P.X :=
  Regime.single S.Z2 (S.hZ2bool.symm z₂)

/-- The encouragement and treatment regimes are disjoint (their targets
`{Z₁, Z₂}` and `{D₁, D₂}` share no node). -/
lemma encouragementRegime_disjoint_treatmentRegime (z d : Fin 2 → Bool) :
    (S.encouragementRegime z).Disjoint (S.treatmentRegime d) := by
  unfold encouragementRegime treatmentRegime Regime.Disjoint
  rw [Regime.ofList_target, Regime.ofList_target]
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_insert] at hv hv'
  rcases hv with hv | hv | hv
  · subst hv
    rcases hv' with hv' | hv' | hv'
    · exact S.Z1_ne_D1 hv'
    · exact S.Z1_ne_D2 hv'
    · exact (Finset.notMem_empty _ hv').elim
  · subst hv
    rcases hv' with hv' | hv' | hv'
    · exact S.Z2_ne_D1 hv'
    · exact S.Z2_ne_D2 hv'
    · exact (Finset.notMem_empty _ hv').elim
  · exact (Finset.notMem_empty _ hv).elim

/-- Joint encouragement-and-treatment regime `r_z ⊔ r_d` fixing
`Z₁,Z₂,D₁,D₂` simultaneously. -/
noncomputable def encTreatRegime (z d : Fin 2 → Bool) : Regime P.V P.X :=
  (S.encouragementRegime z).sqcup (S.treatmentRegime d)
    (S.encouragementRegime_disjoint_treatmentRegime z d)

/-! ### Counterfactual variables under encouragement / treatment regimes -/

/-- `D₁(z) := D₁` evaluated under the encouragement regime fixing both `Z`'s.
By exclusion (`D₁` has no `Z₂` parent in the primitive process), this equals
`D₁(z 0)`; we keep the two-coordinate form to avoid splitting cases. -/
noncomputable def D1ofZ (z : Fin 2 → Bool) : P.Ω → Bool :=
  S.d1Var.cf (S.encouragementRegime z)

/-- `D₂(z)` under the encouragement regime fixing both `Z`'s. -/
noncomputable def D2ofZ (z : Fin 2 → Bool) : P.Ω → Bool :=
  S.d2Var.cf (S.encouragementRegime z)

/-- Joint counterfactual treatment vector `D(z) = (D₁(z), D₂(z))`. -/
noncomputable def DofZ (z : Fin 2 → Bool) : P.Ω → (Fin 2 → Bool) :=
  fun ω i => Fin.cases (S.D1ofZ z ω) (fun _ => S.D2ofZ z ω) i

/-- `D₂(Z₁, z₂)`: stage-2 treatment when only `Z₂` is fixed (and `Z₁`
remains factual).  Used in the stage-2 ignorability bundle. -/
noncomputable def D2ofZ2 (z₂ : Bool) : P.Ω → Bool :=
  S.d2Var.cf (S.encZ2Regime z₂)

/-- `Y(d)` under the treatment regime fixing both `D`'s. -/
noncomputable def YofD (d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.yVar.cf (S.treatmentRegime d)

/-- `Y(D(z))` defined directly via the encouragement regime: under the
two-target encouragement intervention, `D₁` and `D₂` are computed from `z`
via the structural recursion, and `Y` is then computed from the resulting
treatment vector.  This is the natural "outcome under encouragement `z`"
map; `composition` consistency identifies it with the explicit composition. -/
noncomputable def YofDofZ (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.yVar.cf (S.encouragementRegime z)

/-- `Y(D₁, D₂(Z₁, z₂))` realised as `Y` under the regime fixing only
`Z₂ = z₂`. -/
noncomputable def YofZ2 (z₂ : Bool) : P.Ω → ℝ := S.yVar.cf (S.encZ2Regime z₂)

/-- The first treatment under a two-target encouragement regime is measurable. -/
lemma measurable_D1ofZ (z : Fin 2 → Bool) : Measurable (S.D1ofZ z) :=
  S.d1Var.measurable_cf _
/-- The second treatment under a two-target encouragement regime is measurable. -/
lemma measurable_D2ofZ (z : Fin 2 → Bool) : Measurable (S.D2ofZ z) :=
  S.d2Var.measurable_cf _
/-- The joint counterfactual treatment vector under encouragement is measurable. -/
lemma measurable_DofZ (z : Fin 2 → Bool) : Measurable (S.DofZ z) := by
  refine measurable_pi_lambda _ ?_
  intro i
  refine i.cases ?_ ?_
  · simpa [DofZ] using S.measurable_D1ofZ z
  · intro _; simpa [DofZ] using S.measurable_D2ofZ z
/-- The second treatment under a stage-2-only encouragement regime is measurable. -/
lemma measurable_D2ofZ2 (z₂ : Bool) : Measurable (S.D2ofZ2 z₂) :=
  S.d2Var.measurable_cf _
/-- The outcome under a fixed treatment vector is measurable. -/
lemma measurable_YofD (d : Fin 2 → Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cf _
/-- The outcome under a fixed encouragement vector is measurable. -/
lemma measurable_YofDofZ (z : Fin 2 → Bool) : Measurable (S.YofDofZ z) :=
  S.yVar.measurable_cf _
/-- The outcome under a stage-2-only encouragement regime is measurable. -/
lemma measurable_YofZ2 (z₂ : Bool) : Measurable (S.YofZ2 z₂) :=
  S.yVar.measurable_cf _
/-- The observed baseline state is measurable. -/
lemma measurable_factualS0 : Measurable S.factualS0 := S.S0.measurable_factual
/-- The observed intermediate state is measurable. -/
lemma measurable_factualS1 : Measurable S.factualS1 := S.S1.measurable_factual
/-- The observed first encouragement is measurable. -/
lemma measurable_factualZ1 : Measurable S.factualZ1 := S.z1Var.measurable_factual
/-- The observed second encouragement is measurable. -/
lemma measurable_factualZ2 : Measurable S.factualZ2 := S.z2Var.measurable_factual
/-- The observed first treatment is measurable. -/
lemma measurable_factualD1 : Measurable S.factualD1 := S.d1Var.measurable_factual
/-- The observed second treatment is measurable. -/
lemma measurable_factualD2 : Measurable S.factualD2 := S.d2Var.measurable_factual
/-- The observed outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- Factual `Y` is integrable once the two stage-2 counterfactual outcomes are
integrable.  The proof partitions on the factual Boolean `Z₂` cell and uses
PO consistency to identify `Y(Z₂ = z₂)` with factual `Y` on that cell. -/
lemma integrable_factualY_of_consistency_integrable_YofZ2 [IsFiniteMeasure P.μ]
    (hC : P.Consistency) (hY : ∀ z₂ : Bool, Integrable (S.YofZ2 z₂) P.μ) :
    Integrable S.factualY P.μ := by
  have htrue_int : Integrable (fun ω => S.YofZ2 true ω * S.z2Var.indicator true ω) P.μ :=
    S.z2Var.integrable_mul_indicator true (hY true) (S.measurable_YofZ2 true)
  have hfalse_int : Integrable (fun ω => S.YofZ2 false ω * S.z2Var.indicator false ω) P.μ :=
    S.z2Var.integrable_mul_indicator false (hY false) (S.measurable_YofZ2 false)
  have hsum_int : Integrable
      ((fun ω => S.YofZ2 true ω * S.z2Var.indicator true ω) +
        fun ω => S.YofZ2 false ω * S.z2Var.indicator false ω) P.μ :=
    htrue_int.add hfalse_int
  refine hsum_int.congr (Filter.Eventually.of_forall ?_)
  intro ω
  by_cases hω : S.factualZ2 ω = true
  · have hcf : S.YofZ2 true ω = S.factualY ω := by
      simpa [YofZ2, encZ2Regime, factualY, factualZ2, z2Var, yVar, POVar.cfUnder]
        using POVar.cf_eq_factual_on_event hC S.yVar S.z2Var true
          S.Z2_ne_Y.symm hω
    have hind_true : S.z2Var.indicator true ω = 1 := by
      exact S.z2Var.indicator_apply_eq_one hω
    have hfalse : S.factualZ2 ω ≠ false := by
      rw [hω]
      decide
    have hind_false : S.z2Var.indicator false ω = 0 := by
      exact S.z2Var.indicator_apply_eq_zero hfalse
    simp [Pi.add_apply, hcf, hind_true, hind_false]
  · have hω_false : S.factualZ2 ω = false := by
      cases hz : S.factualZ2 ω <;> simp_all
    have hcf : S.YofZ2 false ω = S.factualY ω := by
      simpa [YofZ2, encZ2Regime, factualY, factualZ2, z2Var, yVar, POVar.cfUnder]
        using POVar.cf_eq_factual_on_event hC S.yVar S.z2Var false
          S.Z2_ne_Y.symm hω_false
    have hind_true : S.z2Var.indicator true ω = 0 := by
      exact S.z2Var.indicator_apply_eq_zero hω
    have hind_false : S.z2Var.indicator false ω = 1 := by
      exact S.z2Var.indicator_apply_eq_one hω_false
    simp [Pi.add_apply, hcf, hind_true, hind_false]

/-! ### Regimed variables for ignorability bundles -/

/-- `Y` under the two-target encouragement regime, as a `RegimedVar`. -/
noncomputable def yUnderZ (z : Fin 2 → Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, S.encouragementRegime z⟩

/-- `D₁` under the two-target encouragement regime, as a `RegimedVar`. -/
noncomputable def d1UnderZ (z : Fin 2 → Bool) : RegimedVar P Bool :=
  ⟨S.d1Var, S.encouragementRegime z⟩

/-- `D₂` under the two-target encouragement regime, as a `RegimedVar`. -/
noncomputable def d2UnderZ (z : Fin 2 → Bool) : RegimedVar P Bool :=
  ⟨S.d2Var, S.encouragementRegime z⟩

/-- `Y` under the stage-2-only encouragement regime. -/
noncomputable def yUnderZ2 (z₂ : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, S.encZ2Regime z₂⟩

/-- `D₂` under the stage-2-only encouragement regime. -/
noncomputable def d2UnderZ2 (z₂ : Bool) : RegimedVar P Bool :=
  ⟨S.d2Var, S.encZ2Regime z₂⟩

/-! ### History bundles (sequential conditioning σ-algebras) -/

/-- Stage-1 history bundle: the singleton `(S₀,)`.  Conditioning on this
σ-algebra realises `· | S₀` in the outer regression. -/
noncomputable def historyBundle1 : POCFBundle P :=
  POCFBundle.cons (RegimedVar.ofFactual S.S0) (POCFBundle.nil P)

/-- Stage-2 history bundle: `(S₀, S₁, Z₁, D₁)`.  Conditioning on this
σ-algebra realises `· | S, D₁, Z₁` in the inner regression (the stage-2
encouragement `Z₂` is *not* in the conditioning set; it is restricted via
an indicator). -/
noncomputable def historyBundle2 : POCFBundle P :=
  POCFBundle.cons (RegimedVar.ofFactual S.S0) <|
  POCFBundle.cons (RegimedVar.ofFactual S.S1) <|
  POCFBundle.cons (RegimedVar.ofFactual S.z1Var) <|
  POCFBundle.cons (RegimedVar.ofFactual S.d1Var) <|
  POCFBundle.nil P

/-! ### Counterfactual bundles for sequential ignorability -/

/-- Stage-1 ignorability bundle `(Y(D(z)), D₁(z), D₂(z))`, the counterfactual
target of `Z₁ ⟂ · | S₀`. -/
noncomputable def cfBundle1 (z : Fin 2 → Bool) : POCFBundle P :=
  POCFBundle.cons (S.yUnderZ z) <|
  POCFBundle.cons (S.d1UnderZ z) <|
  POCFBundle.cons (S.d2UnderZ z) <|
  POCFBundle.nil P

/-- Stage-2 ignorability bundle `(Y(D₁, D₂(Z₁, z₂)), D₂(Z₁, z₂))`, the
counterfactual target of `Z₂ ⟂ · | S, D₁, Z₁`. -/
noncomputable def cfBundle2 (z₂ : Bool) : POCFBundle P :=
  POCFBundle.cons (S.yUnderZ2 z₂) <|
  POCFBundle.cons (S.d2UnderZ2 z₂) <|
  POCFBundle.nil P

/-! ### Joint-treatment indicator and joint-encouragement indicator -/

/-- Real-valued indicator of `{D = d}`, i.e. `1_{D₁=d 0} · 1_{D₂=d 1}`. -/
noncomputable def indD (d : Fin 2 → Bool) : P.Ω → ℝ :=
  fun ω => S.d1Var.indicator (d 0) ω * S.d2Var.indicator (d 1) ω

/-- Real-valued indicator of `{Z = z}`. -/
noncomputable def indZ (z : Fin 2 → Bool) : P.Ω → ℝ :=
  fun ω => S.z1Var.indicator (z 0) ω * S.z2Var.indicator (z 1) ω

/-- The joint treatment indicator is measurable. -/
lemma measurable_indD (d : Fin 2 → Bool) : Measurable (S.indD d) :=
  (S.d1Var.measurable_indicator _).mul (S.d2Var.measurable_indicator _)

/-- The joint encouragement indicator is measurable. -/
lemma measurable_indZ (z : Fin 2 → Bool) : Measurable (S.indZ z) :=
  (S.z1Var.measurable_indicator _).mul (S.z2Var.measurable_indicator _)

/-! ### Observable nested-regression functionals
    (def:po-dynamic-late-observable-functionals) -/

/-- Inner regression `E[Y | S, D₁, Z = z]` realised as the bundle ratio
`E[Y · 1_{Z=z} | history2] / E[1_{Z=z} | history2]`. -/
noncomputable def innerCondY (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle2.condExpRatio
    (fun ω => S.factualY ω * S.indZ z ω) (S.indZ z) P.μ

/-- Inner regression `P(D = d | S, D₁, Z = z)` realised as the bundle ratio
`E[1_{D=d} · 1_{Z=z} | history2] / E[1_{Z=z} | history2]`. -/
noncomputable def innerCondD (z d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle2.condExpRatio
    (fun ω => S.indD d ω * S.indZ z ω) (S.indZ z) P.μ

/-- Outer regression of `innerCondY z` over `(S₀, Z₁ = z₁)`, as a function of
`S₀`.  This is `cObsMean(z; S₀)`. -/
noncomputable def cObsMean (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => S.innerCondY z ω * S.z1Var.indicator (z 0) ω)
    (S.z1Var.indicator (z 0)) P.μ

/-- Outer regression of `innerCondD z d` over `(S₀, Z₁ = z₁)`. -/
noncomputable def cObsProb (z d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => S.innerCondD z d ω * S.z1Var.indicator (z 0) ω)
    (S.z1Var.indicator (z 0)) P.μ

/-- Unconditional version `obsMean(z) := E[cObsMean(z; S₀)]`. -/
noncomputable def obsMean (z : Fin 2 → Bool) : ℝ := ∫ ω, S.cObsMean z ω ∂P.μ

/-- Unconditional version `obsProb(z, d) := E[cObsProb(z, d; S₀)]`. -/
noncomputable def obsProb (z d : Fin 2 → Bool) : ℝ := ∫ ω, S.cObsProb z d ω ∂P.μ

/-! ### Target functionals (def:po-dynamic-late) -/

/-- Indicator of the dynamic complier event `{ω | D(z)(ω) = d}`. -/
def DofZEq (z d : Fin 2 → Bool) : Set P.Ω := { ω | S.DofZ z ω = d }

/-- The dynamic complier event is measurable. -/
lemma measurableSet_DofZEq (z d : Fin 2 → Bool) : MeasurableSet (S.DofZEq z d) := by
  have hsing : MeasurableSet ({d} : Set (Fin 2 → Bool)) := MeasurableSet.singleton _
  exact S.measurable_DofZ z hsing

/-- Dynamic LATE `θ(z, d) := E[Y(d) - Y(0) | D(z) = d]`, totalised as
`(∫_{D(z)=d} (Y(d) - Y(0)) dμ) / μ({D(z) = d}).toReal`. -/
noncomputable def LATE (z d : Fin 2 → Bool) : ℝ :=
  (∫ ω in S.DofZEq z d, (S.YofD d ω - S.YofD ![false, false] ω) ∂P.μ) /
    (P.μ (S.DofZEq z d)).toReal

/-- Heterogeneous dynamic LATE `θ(z, d, S₀)`: the bundle conditional version
of `LATE z d`, realised as `historyBundle1.condExpRatio` of the
indicator-weighted contrast. -/
noncomputable def cLATE (z d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => (S.YofD d ω - S.YofD ![false, false] ω) *
              (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω)
    ((S.DofZEq z d).indicator (fun _ => (1 : ℝ))) P.μ

/-- When-to-treat LATE `τ_d := θ(d, d)`. -/
noncomputable def whenToTreatLATE (d : Fin 2 → Bool) : ℝ := S.LATE d d

/-- Heterogeneous when-to-treat LATE `τ_d(S₀)`. -/
noncomputable def cWhenToTreatLATE (d : Fin 2 → Bool) : P.Ω → ℝ := S.cLATE d d

/-- Mixture LATE `β_z := E[Y(D(z)) - Y(0) | D(z) ≠ 0]`. -/
noncomputable def mixtureLATE (z : Fin 2 → Bool) : ℝ :=
  (∫ ω in {ω | S.DofZ z ω ≠ ![false, false]},
      (S.YofDofZ z ω - S.YofD ![false, false] ω) ∂P.μ) /
    (P.μ {ω | S.DofZ z ω ≠ ![false, false]}).toReal

/-- Heterogeneous mixture LATE `β_z(S₀)`. -/
noncomputable def cMixtureLATE (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => (S.YofDofZ z ω - S.YofD ![false, false] ω) *
              ({ω | S.DofZ z ω ≠ ![false, false]}).indicator (fun _ => (1 : ℝ)) ω)
    (({ω | S.DofZ z ω ≠ ![false, false]}).indicator (fun _ => (1 : ℝ))) P.μ

/-! ### Coordinate-wise order on `Fin 2 → Bool` -/

/-- Coordinate-wise order `d ≼ z`: `d 0 ≤ z 0 ∧ d 1 ≤ z 1`. -/
def Preceq (d z : Fin 2 → Bool) : Prop := d 0 ≤ z 0 ∧ d 1 ≤ z 1

/-! ### Assumption bundle (def:po-dynamic-late-assumptions) -/

/-- The dynamic IV / LATE assumptions of def:po-dynamic-late-assumptions.

* **consistency**: PO consistency for the underlying system.
* **ignorability1**: `{Y(D(z)), D₁(z), D₂(z)} ⟂ Z₁ | S₀` for every `z`.
* **ignorability2**: `{Y(D₁, D₂(Z₁, z₂)), D₂(Z₁, z₂)} ⟂ Z₂ | (S₀, S₁, Z₁, D₁)`
  for every `z₂`.
* **overlap1**: positive stage-1 propensity given `S₀`, a.s.
* **overlap2**: positive stage-2 propensity given `(S, D₁, Z₁)`, a.s.
* **relevance1**: positive stage-1 first stage `E[D₁(1) - D₁(0) | S₀] > 0`, a.s.
* **relevance2**: positive stage-2 first stage given the stage-2 history, a.s.
* **oneSidedNoncompliance**: `D₁(z) ≤ z 0` and `D₂(z) ≤ z 1` a.s., for every `z`.
* **exclusion**: `Y` depends on `(D, S)` only, not on `Z`.  In regime terms,
  the value of `Y` under the joint encouragement-and-treatment regime
  agrees pointwise with the value of `Y` under the treatment-only regime.
  This corresponds to the note's primitive-process clause `Y(D, S)`
  (encouragements affect the terminal outcome only through treatment
  and state histories).
* **integrability**: `Y(d)` is integrable for every fixed treatment vector. -/
structure Assumptions (S : PODynLATESystem P γ₀ γ₁)
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] : Prop where
  consistency : P.Consistency
  ignorability1 : ∀ z : Fin 2 → Bool,
    P.CondIndepCFBundle (RegimedVar.ofFactual S.z1Var) (S.cfBundle1 z)
      S.historyBundle1 P.μ
  ignorability2 : ∀ z₂ : Bool,
    P.CondIndepCFBundle (RegimedVar.ofFactual S.z2Var) (S.cfBundle2 z₂)
      S.historyBundle2 P.μ
  overlap1 : ∀ z₁ : Bool, ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle1.condExpGiven (S.z1Var.indicator z₁) P.μ ω
  overlap2 : ∀ z₂ : Bool, ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle2.condExpGiven (S.z2Var.indicator z₂) P.μ ω
  relevance1 : ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle1.condExpGiven
        (fun ω' => ((S.D1ofZ ![true, false] ω').toNat : ℝ) -
                   ((S.D1ofZ ![false, false] ω').toNat : ℝ)) P.μ ω
  relevance2 : ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle2.condExpGiven
        (fun ω' => ((S.D2ofZ ![S.factualZ1 ω', true] ω').toNat : ℝ) -
                   ((S.D2ofZ ![S.factualZ1 ω', false] ω').toNat : ℝ)) P.μ ω
  oneSidedNoncompliance : ∀ z : Fin 2 → Bool, ∀ᵐ ω ∂P.μ,
    S.D1ofZ z ω ≤ z 0 ∧ S.D2ofZ z ω ≤ z 1
  /-- Exclusion: `Y` under the joint encouragement-and-treatment regime
  equals `Y` under the treatment-only regime (pointwise).  Captures the
  primitive-process clause `Y(D, S)`. -/
  exclusion : ∀ (z d : Fin 2 → Bool) (ω : P.Ω),
    S.yVar.cf (S.encTreatRegime z d) ω = S.YofD d ω
  /-- **Primitive-process clause for `D₁`** (def:po-dynamic-late-assumptions
  primitive process `D₁(Z₁, S₀)`).  `D₁` does not depend on `Z₂`: the value
  of `D₁` under the joint encouragement regime fixing both `Z`'s agrees
  pointwise with its value under the regime fixing only `Z₁`.  This is the
  Lean-level encoding of the doc's "encouragements affect the terminal
  outcome only through treatment and state histories" applied at `D₁`. -/
  exclusion_D1 : ∀ (z : Fin 2 → Bool) (ω : P.Ω),
    S.d1Var.cf (S.encouragementRegime z) ω
      = S.d1Var.cf (Regime.single S.Z1 (S.hZ1bool.symm (z 0))) ω
  /-- **Primitive-process clause for `Z₁`** (def:po-dynamic-late-assumptions
  primitive process `Z₁(S₀)`).  `Z₁` does not depend on `Z₂`: the structural
  eval of `Z₁` under any regime fixing only `Z₂` agrees with its factual
  eval (under the empty regime).  Used by the stage-1 composition consistency
  rewrite `YofDofZ_eq_YofZ2_on_z1Event` to apply `Consistency.composition`
  with `r₁ := encZ2Regime z₂`, `r₂ := Regime.single Z₁ (...)` on the event
  `{Z₁ = z 0}` (the `IntermediateAgrees` premise asks that `P.eval (encZ2Regime z₂) ω S.Z1`
  equals the assigned value, which by this clause + factual `Z₁ = z 0` is
  exactly `S.hZ1bool.symm (z 0)`). -/
  exclusion_Z1 : ∀ (z₂ : Bool) (ω : P.Ω),
    P.eval (S.encZ2Regime z₂) ω S.Z1 = P.eval Regime.empty ω S.Z1
  integrable_YofD : ∀ d : Fin 2 → Bool, Integrable (S.YofD d) P.μ
  integrable_YofDofZ : ∀ z : Fin 2 → Bool, Integrable (S.YofDofZ z) P.μ
  integrable_YofZ2 : ∀ z₂ : Bool, Integrable (S.YofZ2 z₂) P.μ

namespace Assumptions

/-- Compatibility projection for older call sites: factual outcome integrability
is derived from consistency plus integrability of the two `YofZ2` cells. -/
lemma integrable_factualY [StandardBorelSpace P.Ω] (As : S.Assumptions) :
    Integrable S.factualY P.μ :=
  S.integrable_factualY_of_consistency_integrable_YofZ2 As.consistency As.integrable_YofZ2

end Assumptions

end PODynLATESystem

end PO
end Causalean
