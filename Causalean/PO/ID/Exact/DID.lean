/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-period Difference-in-Differences ATT identification

Implements def:po-did-system, def:po-did-assumptions, and prop:po-did-att from
Basic Concepts.tex.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Two-Period Difference-in-Differences

This file formalizes two-period difference-in-differences identification of the
average treatment effect on the treated. It packages the treatment and outcome
variables, the parallel-trends assumptions, and the resulting observable
contrast.

The proof works at the event-conditional-mean level: it needs consistency, no
anticipation, parallel trends, positivity of treated and control groups, and
integrability of the counterfactual outcomes that enter the DID contrast. The
main theorem `att_did` identifies the treated-group mean counterfactual contrast
with the observed treated-minus-control difference in outcome changes. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- A two-period DID system consists of a binary treatment and real pre- and post-period outcomes.

The treatment node is required to be distinct from both outcome nodes. -/
structure PODIDSystem (P : POSystem) where
  D : P.V
  Y₀ : P.V
  Y₁ : P.V
  hDbool : P.X D ≃ᵐ Bool
  hY0real : P.X Y₀ ≃ᵐ ℝ
  hY1real : P.X Y₁ ≃ᵐ ℝ
  hDY0 : D ≠ Y₀
  hDY1 : D ≠ Y₁

namespace PODIDSystem

variable {P : POSystem} (S : PODIDSystem P)

/-- The treatment node is packaged as a binary potential-outcome variable. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- The pre-period outcome node is packaged as a real-valued potential-outcome variable. -/
def y0Var : POVar P ℝ := ⟨S.Y₀, S.hY0real⟩

/-- The post-period outcome node is packaged as a real-valued potential-outcome variable. -/
def y1Var : POVar P ℝ := ⟨S.Y₁, S.hY1real⟩

/-- The pre-period potential outcome is evaluated under the intervention that fixes treatment. -/
noncomputable def Y0ofD (d : Bool) : P.Ω → ℝ := S.y0Var.cfUnder S.dVar d

/-- The post-period potential outcome is evaluated under the intervention that fixes treatment. -/
noncomputable def Y1ofD (d : Bool) : P.Ω → ℝ := S.y1Var.cfUnder S.dVar d

/-- The factual treatment is the observed binary treatment value. -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- The factual pre-period outcome is the observed pre-period outcome value. -/
noncomputable def factualY₀ : P.Ω → ℝ := S.y0Var.factual

/-- The factual post-period outcome is the observed post-period outcome value. -/
noncomputable def factualY₁ : P.Ω → ℝ := S.y1Var.factual

/-- The treatment event contains the units whose observed treatment equals the chosen arm. -/
def dEvent (d : Bool) : Set P.Ω := S.dVar.event d

/-- The pre-period potential outcome under a fixed treatment arm is measurable. -/
lemma measurable_Y0ofD (d : Bool) : Measurable (S.Y0ofD d) :=
  S.y0Var.measurable_cfUnder S.dVar d

/-- The post-period potential outcome under a fixed treatment arm is measurable. -/
lemma measurable_Y1ofD (d : Bool) : Measurable (S.Y1ofD d) :=
  S.y1Var.measurable_cfUnder S.dVar d

/-- The observed treatment is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- The observed pre-period outcome is measurable. -/
lemma measurable_factualY₀ : Measurable S.factualY₀ := S.y0Var.measurable_factual

/-- The observed post-period outcome is measurable. -/
lemma measurable_factualY₁ : Measurable S.factualY₁ := S.y1Var.measurable_factual

/-- Each observed treatment-arm event is measurable. -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  S.dVar.measurableSet_event _

/-- The ATT is the treated-group mean difference between treated and untreated
post-period potential outcomes. -/
noncomputable def ATT : ℝ :=
  eventCondExp P.μ (S.dEvent true) (fun ω => S.Y1ofD true ω - S.Y1ofD false ω)

/-- Assumptions for two-period difference-in-differences identification of the
ATT (`def:po-did-assumptions`). In words: the observed outcomes coincide with the
realized-arm potential outcomes (consistency); in the pre-period the treated and
control groups have the same potential outcome regardless of treatment
(no-anticipation); and absent treatment the two groups would have changed in
parallel between the two periods (parallel trends). Each group occurs with
positive probability and the outcomes are integrable, so the group-conditional
means are well-defined and finite. -/
structure Assumptions (S : PODIDSystem P) : Prop where
  /-- Consistency (SUTVA): the observed outcome equals the potential outcome of
  the realized treatment arm. -/
  consistency : P.Consistency
  /-- No anticipation: in the pre-period the potential outcome does not depend on
  the (future) treatment, so `Y₀(1) = Y₀(0)` a.s. -/
  noAnticipation : ∀ᵐ ω ∂P.μ, S.Y0ofD true ω = S.Y0ofD false ω
  /-- Parallel trends: the average untreated change from the pre- to the
  post-period is the same in the treated group as in the control group. -/
  parallelTrends :
    eventCondExp P.μ (S.dEvent true)
        (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
      = eventCondExp P.μ (S.dEvent false)
          (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
  /-- The treated group has positive probability, so its group-mean is defined.
  (Finiteness `μ ≠ ⊤` is automatic: `P.μ` is a probability measure.) -/
  posTrue_ne_zero : P.μ (S.dEvent true) ≠ 0
  /-- The control group has positive probability, so its group-mean is defined. -/
  posFalse_ne_zero : P.μ (S.dEvent false) ≠ 0
  /-- Integrability of the control pre-period potential outcome `Y₀(0)`. -/
  intY0ofD_false : Integrable (S.Y0ofD false) P.μ
  /-- Integrability of the control post-period potential outcome `Y₁(0)`. -/
  intY1ofD_false : Integrable (S.Y1ofD false) P.μ
  /-- Integrability of the treated post-period potential outcome `Y₁(1)`. -/
  intY1ofD_true : Integrable (S.Y1ofD true) P.μ

/-- Pointwise equality on the event `{D = d}`: `factualY₁ - factualY₀` equals
`Y₁(d) - Y₀(d)`. -/
private lemma factualDiff_eq_cfDiff_on_dEvent (hC : P.Consistency) (d : Bool) :
    ∀ ω ∈ S.dEvent d,
      S.factualY₁ ω - S.factualY₀ ω = S.Y1ofD d ω - S.Y0ofD d ω := by
  intro ω hω
  have h1 : S.Y1ofD d ω = S.factualY₁ ω :=
    POVar.cf_eq_factual_on_event hC S.y1Var S.dVar d S.hDY1.symm hω
  have h0 : S.Y0ofD d ω = S.factualY₀ ω :=
    POVar.cf_eq_factual_on_event hC S.y0Var S.dVar d S.hDY0.symm hω
  rw [h1, h0]

/-- Under the DID assumptions, the ATT equals the observed treated-control
difference in outcome changes. -/
theorem att_did (hA : S.Assumptions) :
    S.ATT
      = eventCondExp P.μ (S.dEvent true)
          (fun ω => S.factualY₁ ω - S.factualY₀ ω)
        - eventCondExp P.μ (S.dEvent false)
            (fun ω => S.factualY₁ ω - S.factualY₀ ω) := by
  -- Step 1: by no anticipation, `Y₁(1) - Y₁(0)` rewrites a.e. as
  -- `(Y₁(1) - Y₀(1)) - (Y₁(0) - Y₀(0))`.
  have hAE : (fun ω => S.Y1ofD true ω - S.Y1ofD false ω)
      =ᵐ[P.μ] fun ω =>
        (S.Y1ofD true ω - S.Y0ofD true ω) -
          (S.Y1ofD false ω - S.Y0ofD false ω) := by
    refine hA.noAnticipation.mono (fun ω hω => ?_)
    change S.Y1ofD true ω - S.Y1ofD false ω
      = (S.Y1ofD true ω - S.Y0ofD true ω) - (S.Y1ofD false ω - S.Y0ofD false ω)
    rw [hω]; ring
  -- Step 2: split via additivity.  Use the `eventCondExp` definition and
  -- `integral_congr_ae` + `integral_sub`.
  have hATT_split :
      S.ATT
        = eventCondExp P.μ (S.dEvent true)
            (fun ω => S.Y1ofD true ω - S.Y0ofD true ω)
          - eventCondExp P.μ (S.dEvent true)
              (fun ω => S.Y1ofD false ω - S.Y0ofD false ω) := by
    unfold ATT
    rw [eventCondExp_congr_ae P.μ (S.dEvent true) hAE]
    -- `Y0ofD true` is integrable via a.e. equality with `Y0ofD false`.
    have hY0true_int : Integrable (S.Y0ofD true) P.μ :=
      hA.intY0ofD_false.congr (hA.noAnticipation.mono (fun _ h => h.symm))
    exact eventCondExp_sub P.μ (S.dEvent true)
      (hA.intY1ofD_true.sub hY0true_int).integrableOn
      (hA.intY1ofD_false.sub hA.intY0ofD_false).integrableOn
  -- Step 3: on `dEvent true`, consistency gives
  -- `Y₁(1) - Y₀(1) = factualY₁ - factualY₀`.
  have h_first :
      eventCondExp P.μ (S.dEvent true)
          (fun ω => S.Y1ofD true ω - S.Y0ofD true ω)
        = eventCondExp P.μ (S.dEvent true)
            (fun ω => S.factualY₁ ω - S.factualY₀ ω) :=
    (eventCondExp_congr_on P.μ (S.measurableSet_dEvent true)
      (fun ω hω => (S.factualDiff_eq_cfDiff_on_dEvent hA.consistency true ω hω).symm))
  -- Step 4: parallel trends rewrites the second term to condition on `D=0`.
  have h_pt : eventCondExp P.μ (S.dEvent true)
        (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
      = eventCondExp P.μ (S.dEvent false)
          (fun ω => S.Y1ofD false ω - S.Y0ofD false ω) := hA.parallelTrends
  -- Step 5: on `dEvent false`, consistency gives
  -- `Y₁(0) - Y₀(0) = factualY₁ - factualY₀`.
  have h_second :
      eventCondExp P.μ (S.dEvent false)
          (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
        = eventCondExp P.μ (S.dEvent false)
            (fun ω => S.factualY₁ ω - S.factualY₀ ω) :=
    eventCondExp_congr_on P.μ (S.measurableSet_dEvent false)
      (fun ω hω => (S.factualDiff_eq_cfDiff_on_dEvent hA.consistency false ω hω).symm)
  rw [hATT_split, h_first, h_pt, h_second]

end PODIDSystem

end PO
end Causalean
