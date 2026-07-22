/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.MinimaxATE.Causal.Construction
import Causalean.Estimation.ATE.Setup
import Causalean.PO.Bridge.FromSCMCondIndep
import Causalean.SCM.Factored.ObsChainKernel
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Causal Grounding of the Minimax ATE Model

This file is the **clean interface** between the causal layer (the
`POBackdoorSystem` built in `Construction.lean`, whose ATE `E[Y(1) − Y(0)]` is
the genuine causal target) and the observed-data contrast `ate g` on which the
minimax proof machinery computes.

The headline theorem is `causalATE_eq_ate`:

    causalATE m g  =  ate g           (under strict overlap `0 < m x < 1`)

where `causalATE m g := (dgpBackdoor m g).ATE = ∫ (Y(1) − Y(0)) dμ` is the
potential-outcome ATE of the constructed backdoor system.  With this in hand the
causal-centered lower bounds in `Causal/Minimax.lean` are bounds on the *causal*
estimand, identified by backdoor adjustment, not merely on a regression contrast.

The proof routes through the reusable `BackdoorEstimationSystem.θ₀_eq_ATE`
(`Estimation/ATE/Setup.lean`): instantiate the estimation system with value-space
regression `μ_val := g` and propensity `e_val := m`, so that
`θ₀ = ∫ (g 1 − g 0) dP_X` and `θ₀ = S.ATE`; then `P_X = Uniform(C)` collapses
`θ₀` to the average `(1/card C) Σ_x (g 1 x − g 0 x) = ate g`.

## Obligation status

* `dgp_consistency` — proved (FREE from `POSystem.ofSCM_consistency`).
* `dgp_unconfoundedness` and `dgp_adjustedCE_eq_g` prove the genuine
  causal-layer obligations: the d-separation lift and the outcome-regression
  conditional-mean computation of the constructed SCM law.
* `dgp_propScore_eq_m`, `dgp_overlap`, `dgp_assumptions`, `dgp_P_X_eq_covLaw`,
  and `dgpBES` assemble the backdoor-estimation-system interface needed for the
  final bridge theorem.
-/

namespace Causalean.Estimation.MinimaxATE.Causal

open Causalean Causalean.PO Causalean.Estimation.ATE
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {C : Type} [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [StandardBorelSpace C]
variable {m : C → ℝ} {g : Bool → C → ℝ}

/-! ## Carrier regularity instances -/

/-- The constructed potential-outcome system has a probability measure as its population law. -/
instance dgpPO_isProb : IsProbabilityMeasure (dgpPO m g).μ := by
  change IsProbabilityMeasure (SCM.latentProduct (dgpSCM m g))
  infer_instance

/-- The constructed potential-outcome system has a standard Borel sample space. -/
theorem dgpPO_borel : StandardBorelSpace (dgpPO m g).Ω := by
  change StandardBorelSpace (SCM.LatentValues (dgpSCM m g))
  haveI : ∀ n : SWIGNode WNode, StandardBorelSpace (swigΩ (WΩ C) n) := by
    intro n; cases n <;> infer_instance
  exact StandardBorelSpace.pi_countable

/-- The standard Borel structure for the constructed potential-outcome system is
available as an instance. -/
noncomputable instance dgpPO_standardBorel : StandardBorelSpace (dgpPO m g).Ω :=
  dgpPO_borel

/-! ## The causal estimand -/

/-- The causal average treatment effect of the constructed finite backdoor system,
namely `(dgpBackdoor m g).ATE`.  The theorem `causalATE_eq_ate` later identifies
this potential-outcome estimand with the finite observed-data contrast `ate g`
under validity and strict overlap. -/
noncomputable def causalATE (m : C → ℝ) (g : Bool → C → ℝ) : ℝ :=
  (dgpBackdoor m g).ATE

/-! ## Causal-layer obligations (mirrors the CausalSmith stat witness) -/

/-- The constructed potential-outcome system satisfies consistency. -/
theorem dgp_consistency : (dgpPO m g).Consistency :=
  POSystem.ofSCM_consistency (dgpSCM m g) (dgpFixed m g)

private abbrev iUn (m : C → ℝ) (g : Bool → C → ℝ) :
    {u // u ∈ (dgpSCM m g).unobserved} :=
  ⟨SWIGNode.random WNode.Un, by simp [dgpSCM, wSWIGGraph]⟩

private abbrev iEa (m : C → ℝ) (g : Bool → C → ℝ) :
    {u // u ∈ (dgpSCM m g).unobserved} :=
  ⟨SWIGNode.random WNode.Ea, by simp [dgpSCM, wSWIGGraph]⟩

private abbrev iEy (m : C → ℝ) (g : Bool → C → ℝ) :
    {u // u ∈ (dgpSCM m g).unobserved} :=
  ⟨SWIGNode.random WNode.Ey, by simp [dgpSCM, wSWIGGraph]⟩

private lemma dgp_AIdx_name :
    Classical.choose ((dgpSCM m g).observed_is_random (AIdx m g).val (AIdx m g).property) =
      WNode.A := by
  have hspec :=
    Classical.choose_spec ((dgpSCM m g).observed_is_random (AIdx m g).val
      (AIdx m g).property)
  change SWIGNode.random WNode.A =
      SWIGNode.random
        (Classical.choose ((dgpSCM m g).observed_is_random (AIdx m g).val
          (AIdx m g).property)) at hspec
  injection hspec with h
  exact h.symm

private lemma dgp_regimeTargetN_single_A (d : Bool) :
    regimeTargetN (dgpSCM m g)
      (Regime.single (AIdx m g) (show obsValue (dgpSCM m g) (AIdx m g) from d)) =
        {WNode.A} := by
  classical
  ext D
  constructor
  · intro hD
    simp only [regimeTargetN, Finset.mem_image] at hD
    rcases hD with ⟨v, hv, hname⟩
    have hvA : v = AIdx m g := by
      have hv_target : v ∈
          (Regime.single (AIdx m g) (show obsValue (dgpSCM m g) (AIdx m g) from d)).target :=
        (Finset.mem_filter.mp hv).1
      have hv_single : v ∈ ({AIdx m g} : Finset (ObsIdx (dgpSCM m g))) := by
        simpa [Regime.single] using hv_target
      exact Finset.mem_singleton.mp hv_single
    subst v
    rw [dgp_AIdx_name (m := m) (g := g)] at hname
    simpa [hname]
  · intro hD
    have hDA : D = WNode.A := by simpa using hD
    subst D
    simp only [regimeTargetN, Finset.mem_image]
    refine ⟨AIdx m g, ?_, dgp_AIdx_name (m := m) (g := g)⟩
    exact Finset.mem_filter.mpr ⟨by simp [Regime.single],
      by simpa [dgp_AIdx_name (m := m) (g := g), dgpSCM, wSWIGGraph]⟩

private lemma dgp_factualX_eq_latentUn :
    (dgpBackdoor m g).factualX =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) := by
  funext ℓ
  simp only [POBackdoorSystem.factualX, POVar.factual, POVar.cf]
  change (dgpBackdoor m g).xVar.equiv
      (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (XIdx m g)) =
    ℓ (iUn (C := C) m g)
  rw [inducedEval_empty_eq_evalMap]
  change (XEquiv m g)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by
          simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩) =
    ℓ (iUn (C := C) m g)
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
  unfold XEquiv dgpSCM parentVal iUn
  rfl

private noncomputable def dgpXSingletonEquiv :
    C ≃ᵐ ValuesOn ({SWIGNode.random WNode.Xc} : Finset (SWIGNode WNode)) (swigΩ (WΩ C)) where
  toFun := SCM.singletonValues (Ω := WΩ C) (v := SWIGNode.random WNode.Xc)
  invFun := SCM.singletonValue (Ω := WΩ C) (v := SWIGNode.random WNode.Xc)
  left_inv := fun x =>
    SCM.singletonValue_singletonValues (Ω := WΩ C) (v := SWIGNode.random WNode.Xc) x
  right_inv := fun x =>
    SCM.singletonValues_singletonValue (Ω := WΩ C) (v := SWIGNode.random WNode.Xc) x
  measurable_toFun := SCM.measurable_singletonValues (Ω := WΩ C)
  measurable_invFun := SCM.measurable_singletonValue (Ω := WΩ C)

private lemma dgp_factualD_eq_treatFun :
    (dgpBackdoor m g).factualD =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) := by
  funext ℓ
  simp only [POBackdoorSystem.factualD, POVar.factual, POVar.cf]
  change (dgpBackdoor m g).dVar.equiv
      (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (AIdx m g)) =
    treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
  rw [inducedEval_empty_eq_evalMap]
  change (AEquiv m g)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.A, by
          simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩) =
    treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.A, by simp [dgpSCM, wSWIGGraph]⟩]
  change treatFun
      (m ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by
          simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩))
      (ℓ (iEa (C := C) m g)) =
    treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
  unfold dgpSCM parentVal iUn
  rfl

private lemma dgp_factualY_eq_outFun :
    (dgpBackdoor m g).factualY =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        outFun (C := C) g
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
          (ℓ (iUn (C := C) m g))
          (ℓ (iEy (C := C) m g))) := by
  funext ℓ
  simp only [POBackdoorSystem.factualY, POVar.factual, POVar.cf]
  change (dgpBackdoor m g).yVar.equiv
      (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (YIdx m g)) =
    outFun (C := C) g
      (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
      (ℓ (iUn (C := C) m g))
      (ℓ (iEy (C := C) m g))
  rw [inducedEval_empty_eq_evalMap]
  change (YEquiv m g)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Y, by
          simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩) =
    outFun (C := C) g
      (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
      (ℓ (iUn (C := C) m g))
      (ℓ (iEy (C := C) m g))
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.Y, by simp [dgpSCM, wSWIGGraph]⟩]
  change outFun (C := C) g
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.A, by
          simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by
          simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩)
      (ℓ (iEy (C := C) m g)) =
    outFun (C := C) g
      (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
      (ℓ (iUn (C := C) m g))
      (ℓ (iEy (C := C) m g))
  have hAeval :
      (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.A, by
            simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩ =
        treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)) := by
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.A, by simp [dgpSCM, wSWIGGraph]⟩]
    change treatFun
        (m ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩))
        (ℓ (iEa (C := C) m g)) =
      treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    unfold dgpSCM parentVal iUn
    rfl
  have hXeval :
      (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩ =
        ℓ (iUn (C := C) m g) := by
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    unfold dgpSCM parentVal iUn
    rfl
  rw [hAeval, hXeval]

private lemma dgp_YofD_eq_outFun (d : Bool) :
    (dgpBackdoor m g).YofD d =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))) := by
  funext ℓ
  let r : Regime (ObsIdx (dgpSCM m g)) (obsValue (dgpSCM m g)) :=
    Regime.single (AIdx m g) d
  let M' := (dgpSCM m g).fixSet (regimeTargetN (dgpSCM m g) r)
    (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
  unfold POBackdoorSystem.YofD POVar.cfUnder POVar.cf
  change (YEquiv m g)
      (M'.evalMap (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
        ⟨SWIGNode.random WNode.Y, by
          simp [M', SCM.randomVars, dgpSCM, wSWIGGraph]⟩) =
    outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))
  let ξ : ∀ w : {w // w ∈ M'.dag.parents (SWIGNode.random WNode.Y)}, swigΩ (WΩ C) w.val :=
    fun w =>
      if huo : w.val ∈ M'.unobserved then ℓ ⟨w.val, huo⟩
      else if hfix : w.val ∈ M'.fixed then
        combinedFixed (dgpSCM m g) (dgpFixed m g) r ⟨w.val, hfix⟩
      else
        have hedge : M'.dag.edge w.val (SWIGNode.random WNode.Y) := M'.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M'.observed := by
          rcases Finset.mem_union.mp (M'.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        M'.evalMap (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
          ⟨w.val, Finset.mem_union_left _ hobs⟩
  rw [SCM.evalMap_fixSet_observed_apply (dgpSCM m g) (regimeTargetN (dgpSCM m g) r)
    (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
    (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
    ⟨SWIGNode.random WNode.Y, by simp [dgpSCM, wSWIGGraph]⟩]
  change (YEquiv m g) ((dgpSCM m g).structFun ⟨SWIGNode.random WNode.Y, by
      simp [dgpSCM, wSWIGGraph]⟩
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)) =
    outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))
  simp only [YEquiv, dgpSCM]
  change outFun (C := C) g
      (parentVal (C := C)
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)
        (show wEdge WNode.A WNode.Y from trivial))
      (parentVal (C := C)
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)
        (show wEdge WNode.Xc WNode.Y from trivial))
      (parentVal (C := C)
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)
        (show wEdge WNode.Ey WNode.Y from trivial)) =
    outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))
  have hTargetA : regimeTargetN (dgpSCM m g) r = {WNode.A} := by
    dsimp [r]
    exact dgp_regimeTargetN_single_A (m := m) (g := g) d
  have hDmem : WNode.A ∈ regimeTargetN (dgpSCM m g) r := by
    simpa [hTargetA]
  have hAtgt : (AIdx m g) ∈ r.target := by
    change (AIdx m g) ∈ ({AIdx m g} : Finset (ObsIdx (dgpSCM m g)))
    exact Finset.mem_singleton_self (AIdx m g)
  have hAval : (AIdx m g).val = SWIGNode.random WNode.A := by
    rfl
  have hA : parentVal (C := C)
      (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ)
      (show wEdge WNode.A WNode.Y from trivial) = d := by
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ
        ⟨SWIGNode.random WNode.A, wParent_mem (show wEdge WNode.A WNode.Y from trivial)⟩ = d
    rw [SCM.fixMonoParentMap_apply_random (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Y) WNode.A hDmem]
    dsimp [ξ]
    rw [dif_neg]
    · rw [dif_pos]
      · change (combinedFixed (dgpSCM m g) (dgpFixed m g) r
          ⟨SWIGNode.fixed WNode.A,
            Finset.mem_union_right _ (Finset.mem_image.mpr ⟨WNode.A, hDmem, rfl⟩)⟩ : Bool) = d
        rw [combinedFixed_new (dgpSCM m g) (dgpFixed m g) r
          (AIdx m g) hAtgt WNode.A hDmem hAval]
        simpa [r, Regime.single, AIdx]
    · simp [M', SCM.fixSet, SCM.fixMono, dgpSCM, wSWIGGraph]
  rw [hA]
  have hXeval : M'.evalMap (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
      ⟨SWIGNode.random WNode.Xc, Finset.mem_union_left _ (by simp [M', dgpSCM, wSWIGGraph])⟩ =
    ℓ (iUn (C := C) m g) := by
    rw [SCM.evalMap_fixSet_observed_apply (dgpSCM m g) (regimeTargetN (dgpSCM m g) r)
      (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
      (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    simp only [dgpSCM]
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Xc) _
        ⟨SWIGNode.random WNode.Un, wParent_mem (show wEdge WNode.Un WNode.Xc from trivial)⟩ =
      ℓ (iUn (C := C) m g)
    rw [SCM.fixMonoParentMap_apply_random_notMem (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Xc)
      _ WNode.Un]
    · rw [dif_pos]
      · rfl
      · change SWIGNode.random WNode.Un ∈ M'.unobserved
        simp [M', dgpSCM, wSWIGGraph]
    · simpa [hTargetA]
  have hXnot : WNode.Xc ∉ regimeTargetN (dgpSCM m g) r := by
    simpa [hTargetA]
  have hX : parentVal (C := C)
      (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ)
      (show wEdge WNode.Xc WNode.Y from trivial) = ℓ (iUn (C := C) m g) := by
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ
        ⟨SWIGNode.random WNode.Xc, wParent_mem (show wEdge WNode.Xc WNode.Y from trivial)⟩ =
      ℓ (iUn (C := C) m g)
    rw [SCM.fixMonoParentMap_apply_random_notMem (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Y)
      ξ WNode.Xc hXnot]
    dsimp [ξ]
    rw [dif_neg]
    · rw [dif_neg]
      · simpa using hXeval
      · simp [M', SCM.fixSet, SCM.fixMono, dgpSCM, wSWIGGraph]
    · simp [M', SCM.fixSet, SCM.fixMono, dgpSCM, wSWIGGraph]
  rw [hX]
  have hEynot : WNode.Ey ∉ regimeTargetN (dgpSCM m g) r := by
    simpa [hTargetA]
  have hEy : parentVal (C := C)
      (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ)
      (show wEdge WNode.Ey WNode.Y from trivial) = ℓ (iEy (C := C) m g) := by
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ
        ⟨SWIGNode.random WNode.Ey, wParent_mem (show wEdge WNode.Ey WNode.Y from trivial)⟩ =
      ℓ (iEy (C := C) m g)
    rw [SCM.fixMonoParentMap_apply_random_notMem (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Y)
      ξ WNode.Ey hEynot]
    dsimp [ξ]
    rw [dif_pos]
  rw [hEy]

private lemma dgp_dIndicator_true_eq_threshold :
    (dgpBackdoor m g).dVar.indicator true =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if (show ℝ from ℓ (iEa (C := C) m g)) ≤
            m (show C from ℓ (iUn (C := C) m g)) then (1 : ℝ) else 0) := by
  funext ℓ
  unfold POVar.indicator POVar.event
  change (((dgpBackdoor m g).factualD ⁻¹' {true}).indicator (fun _ => (1 : ℝ))) ℓ =
    (if (show ℝ from ℓ (iEa (C := C) m g)) ≤
        m (show C from ℓ (iUn (C := C) m g)) then (1 : ℝ) else 0)
  rw [dgp_factualD_eq_treatFun (m := m) (g := g)]
  unfold treatFun
  by_cases h : (show ℝ from ℓ (iEa (C := C) m g)) ≤
      m (show C from ℓ (iUn (C := C) m g))
  · simp [h]
  · simp [h]

private lemma unifLaw_integral_Iic_indicator (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ e, (if e ≤ t then (1 : ℝ) else 0) ∂unifLaw = t := by
  have hs : MeasurableSet (Set.Iic t : Set ℝ) := measurableSet_Iic
  have hfun : (fun e : ℝ => if e ≤ t then (1 : ℝ) else 0) =
      (Set.Iic t).indicator (fun _ => (1 : ℝ)) := by
    funext e
    by_cases h : e ≤ t
    · simp [Set.indicator_of_mem, h]
    · simp [Set.indicator_of_notMem, h]
  rw [hfun]
  have hint : ∫ e, (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) e ∂unifLaw =
      unifLaw.real (Set.Iic t) := by
    simpa only using (MeasureTheory.integral_indicator_one (μ := unifLaw) hs)
  rw [hint]
  rw [MeasureTheory.measureReal_def]
  unfold unifLaw
  rw [Measure.restrict_apply hs]
  have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) t := by
    ext e
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, ⟨h.1, le_trans h.2 ht.2⟩⟩
  rw [hset, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal]
  · simp
  · simpa using ht.1

private lemma integrable_of_measurable_zero_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (h01 : ∀ ω, f ω = 0 ∨ f ω = 1) :
    Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
  intro ω
  rcases h01 ω with h | h <;> simp [h]

private lemma dgp_indep_ea_un :
    Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEa (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance)
      (dgpPO m g).μ := by
  change Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEa (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance)
      ((dgpSCM m g).latentProduct)
  rw [← IndepFun_iff_Indep]
  change IndepFun
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEa (C := C) m g))
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g))
      (Measure.pi (dgpSCM m g).latentDist)
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  have hdisj : Disjoint ({iEa (C := C) m g} : Finset {u // u ∈ (dgpSCM m g).unobserved})
      ({iUn (C := C) m g} : Finset {u // u ∈ (dgpSCM m g).unobserved}) := by
    simp
  have hbase := indepFun_pi_of_disjoint
    (Ω := fun u : {u // u ∈ (dgpSCM m g).unobserved} => swigΩ (WΩ C) u.val)
    (S := {iEa (C := C) m g}) (T := {iUn (C := C) m g})
    (fun u => (dgpSCM m g).latentDist u) hdisj
  have hcomp := hbase.comp
    (measurable_pi_apply
      (⟨iEa (C := C) m g, by simp⟩ :
        {u // u ∈ ({iEa (C := C) m g} :
          Finset {u // u ∈ (dgpSCM m g).unobserved})}))
    (measurable_pi_apply
      (⟨iUn (C := C) m g, by simp⟩ :
        {u // u ∈ ({iUn (C := C) m g} :
          Finset {u // u ∈ (dgpSCM m g).unobserved})}))
  simpa using hcomp

private lemma dgp_integral_ea_threshold (x : C) (ht : m x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0) ∂(dgpPO m g).μ =
      m x := by
  change ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (fun e : ℝ => if e ≤ m x then (1 : ℝ) else 0) (ℓ (iEa (C := C) m g)) ∂Measure.pi
        (dgpSCM m g).latentDist =
      m x
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  have hf_meas : Measurable (fun e : ℝ => if e ≤ m x then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  rw [← integral_map (μ := Measure.pi (dgpSCM m g).latentDist)
    (f := fun e : ℝ => if e ≤ m x then (1 : ℝ) else 0)
    (measurable_pi_apply (iEa (C := C) m g)).aemeasurable]
  swap
  · exact hf_meas.aestronglyMeasurable
  rw [Measure.pi_map_eval]
  have hscale : (∏ j ∈ Finset.univ.erase (iEa (C := C) m g),
      ((dgpSCM m g).latentDist j) Set.univ) = 1 := by
    simp
  rw [hscale, one_smul]
  unfold iEa dgpSCM
  change ∫ e, (if e ≤ m x then (1 : ℝ) else 0) ∂unifLaw = m x
  exact unifLaw_integral_Iic_indicator (m x) ht

private lemma dgp_condExp_ea_threshold_const (x : C) (ht : m x ∈ Set.Icc (0 : ℝ) 1) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0 |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance]
      =ᵐ[(dgpPO m g).μ] fun _ => m x := by
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEa (C := C) m g)
  let uFun : SCM.LatentValues (dgpSCM m g) → C := fun ℓ => ℓ (iUn (C := C) m g)
  let eInd : SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun ℓ => if eFun ℓ ≤ m x then (1 : ℝ) else 0
  have he_sm : StronglyMeasurable[MeasurableSpace.comap eFun inferInstance] eInd := by
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap eFun inferInstance
    have he_meas : Measurable eFun := comap_measurable eFun
    have hset : MeasurableSet {ℓ : SCM.LatentValues (dgpSCM m g) | eFun ℓ ≤ m x} :=
      measurableSet_le he_meas measurable_const
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  have hle_e : MeasurableSpace.comap eFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [eFun]
    exact (measurable_pi_apply (iEa (C := C) m g)).comap_le
  have hle_u : MeasurableSpace.comap uFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [uFun]
    exact (measurable_pi_apply (iUn (C := C) m g)).comap_le
  haveI : IsProbabilityMeasure (dgpPO m g).μ := dgpPO_isProb
  haveI : IsFiniteMeasure (dgpPO m g).μ := inferInstance
  haveI : IsFiniteMeasure ((dgpPO m g).μ.trim hle_u) :=
    isFiniteMeasure_trim (μ := (dgpPO m g).μ) hle_u
  have hsig : SigmaFinite ((dgpPO m g).μ.trim hle_u) :=
    MeasureTheory.IsFiniteMeasure.toSigmaFinite ((dgpPO m g).μ.trim hle_u)
  have hmain := by
    exact @MeasureTheory.condExp_indep_eq
      (SCM.LatentValues (dgpSCM m g)) ℝ _ _ _
      (MeasurableSpace.comap eFun inferInstance)
      (MeasurableSpace.comap uFun inferInstance)
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g)))
      ((dgpPO m g).μ) eInd hle_e hle_u hsig he_sm dgp_indep_ea_un
  have hmain' :
      (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0 |
        MeasurableSpace.comap
          (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance]
        =ᵐ[(dgpPO m g).μ]
          fun _ => ∫ ℓ : SCM.LatentValues (dgpSCM m g),
            (if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0) ∂(dgpPO m g).μ := by
    simpa [eInd, uFun, eFun] using hmain
  refine hmain'.trans ?_
  exact Filter.Eventually.of_forall fun ℓ => by
    dsimp [eInd, eFun, uFun]
    change (∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0) ∂(dgpPO m g).μ) =
      m x
    exact dgp_integral_ea_threshold (m := m) (g := g) x ht

private lemma dgp_condExp_ea_threshold_var (hv : ValidDGP m g) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      if (show ℝ from ℓ (iEa (C := C) m g)) ≤
          m (show C from ℓ (iUn (C := C) m g)) then (1 : ℝ) else 0 |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance]
      =ᵐ[(dgpPO m g).μ]
        fun ℓ => m (show C from ℓ (iUn (C := C) m g)) := by
  classical
  let uFun : SCM.LatentValues (dgpSCM m g) → C := fun ℓ => ℓ (iUn (C := C) m g)
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEa (C := C) m g)
  let cell : C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun x ℓ => if uFun ℓ = x then (1 : ℝ) else 0
  let eth : C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun x ℓ => if eFun ℓ ≤ m x then (1 : ℝ) else 0
  let piece : C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun x ℓ => cell x ℓ * eth x ℓ
  have hle_σUn :
      MeasurableSpace.comap uFun inferInstance ≤
        (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [uFun]
    exact (measurable_pi_apply (iUn (C := C) m g)).comap_le
  have hcell_sm : ∀ x, StronglyMeasurable[MeasurableSpace.comap uFun inferInstance] (cell x) := by
    intro x
    have hu_meas :
        @Measurable (SCM.LatentValues (dgpSCM m g)) C
          (MeasurableSpace.comap uFun inferInstance) inferInstance uFun :=
      comap_measurable uFun
    have hs :
        @MeasurableSet (SCM.LatentValues (dgpSCM m g))
          (MeasurableSpace.comap uFun inferInstance)
          {ℓ : SCM.LatentValues (dgpSCM m g) | uFun ℓ = x} :=
      (MeasurableSet.singleton x).preimage hu_meas
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap uFun inferInstance
    exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
  have heth_meas : ∀ x, Measurable (eth x) := by
    intro x
    change @Measurable (SCM.LatentValues (dgpSCM m g)) ℝ
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) inferInstance
      (eth x)
    dsimp [eth, eFun]
    exact Measurable.ite
      (measurableSet_le
        (show Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          ℓ (iEa (C := C) m g)) from measurable_pi_apply (iEa (C := C) m g))
        measurable_const)
      measurable_const measurable_const
  have heth_int : ∀ x, Integrable (eth x) (dgpPO m g).μ := by
    intro x
    exact integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) (heth_meas x) fun ℓ => by
      dsimp [eth]
      split_ifs <;> simp
  have hpiece_int : ∀ x, Integrable (piece x) (dgpPO m g).μ := by
    intro x
    refine integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) ?_ ?_
    · change Measurable (piece x)
      exact ((hcell_sm x).mono hle_σUn).measurable.mul (heth_meas x)
    · intro ℓ
      dsimp [piece, cell, eth]
      split_ifs <;> simp
  have hpiece_pull : ∀ x,
      (dgpPO m g).μ[piece x | MeasurableSpace.comap uFun inferInstance]
        =ᵐ[(dgpPO m g).μ] cell x * (fun _ => m x) := by
    intro x
    have hpull :
        (dgpPO m g).μ[piece x | MeasurableSpace.comap uFun inferInstance]
          =ᵐ[(dgpPO m g).μ]
            cell x * (dgpPO m g).μ[eth x | MeasurableSpace.comap uFun inferInstance] := by
      have hmul : piece x = cell x * eth x := rfl
      rw [hmul]
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (μ := (dgpPO m g).μ) (m := MeasurableSpace.comap uFun inferInstance)
        (hcell_sm x) (hpiece_int x) (heth_int x)
    refine hpull.trans ?_
    have hconst :
        (dgpPO m g).μ[eth x | MeasurableSpace.comap uFun inferInstance]
          =ᵐ[(dgpPO m g).μ] fun _ => m x := by
      simpa [eth, eFun, uFun] using
        dgp_condExp_ea_threshold_const (m := m) (g := g) x (hv.m_mem x)
    filter_upwards [hconst] with ℓ hℓ
    change cell x ℓ *
        (dgpPO m g).μ[eth x | MeasurableSpace.comap uFun inferInstance] ℓ =
      cell x ℓ * m x
    exact congrArg (fun y => cell x ℓ * y) hℓ
  have hsource :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if eFun ℓ ≤ m (uFun ℓ) then (1 : ℝ) else 0)
        =
      (∑ x : C, piece x) := by
    funext ℓ
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single (uFun ℓ)]
    · dsimp [piece, cell, eth]
      simp
    · intro x _ hx
      have hx' : uFun ℓ ≠ x := fun h => hx h.symm
      dsimp [piece, cell]
      simp [hx']
    · intro hnot
      exact (hnot (Finset.mem_univ (uFun ℓ))).elim
  have htarget :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => m (uFun ℓ)) =
      (∑ x : C, cell x * fun _ : SCM.LatentValues (dgpSCM m g) => m x) := by
    funext ℓ
    simp only [Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_eq_single (uFun ℓ)]
    · dsimp [cell]
      simp
    · intro x _ hx
      have hx' : uFun ℓ ≠ x := fun h => hx h.symm
      dsimp [cell]
      simp [hx']
    · intro hnot
      exact (hnot (Finset.mem_univ (uFun ℓ))).elim
  have hsum :
      (dgpPO m g).μ[(∑ x : C, piece x) | MeasurableSpace.comap uFun inferInstance]
        =ᵐ[(dgpPO m g).μ]
          (∑ x : C, (dgpPO m g).μ[piece x | MeasurableSpace.comap uFun inferInstance]) := by
    simpa using
      (MeasureTheory.condExp_finset_sum
        (μ := (dgpPO m g).μ) (s := (Finset.univ : Finset C))
        (f := piece) (by intro x _; exact hpiece_int x)
        (MeasurableSpace.comap uFun inferInstance))
  refine (MeasureTheory.condExp_congr_ae (μ := (dgpPO m g).μ)
    (m := MeasurableSpace.comap uFun inferInstance)
    (Filter.EventuallyEq.of_eq hsource)).trans ?_
  refine hsum.trans ?_
  refine (eventuallyEq_sum fun x _ => hpiece_pull x).trans ?_
  exact Filter.EventuallyEq.of_eq htarget.symm

private lemma dgp_indep_ey_dx :
    Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEy (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance)
      (dgpPO m g).μ := by
  change Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEy (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance)
      ((dgpSCM m g).latentProduct)
  rw [← IndepFun_iff_Indep]
  change IndepFun
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEy (C := C) m g))
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
          ℓ (iUn (C := C) m g)))
      (Measure.pi (dgpSCM m g).latentDist)
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  let S : Finset {u // u ∈ (dgpSCM m g).unobserved} := {iEy (C := C) m g}
  let T : Finset {u // u ∈ (dgpSCM m g).unobserved} :=
    {iUn (C := C) m g, iEa (C := C) m g}
  have hdisj : Disjoint S T := by
    simp [S, T, iEy, iUn, iEa]
  have hbase := indepFun_pi_of_disjoint
    (Ω := fun u : {u // u ∈ (dgpSCM m g).unobserved} => swigΩ (WΩ C) u.val)
    (S := S) (T := T)
    (fun u => (dgpSCM m g).latentDist u) hdisj
  let pEy : {u // u ∈ S} := ⟨iEy (C := C) m g, by simp [S]⟩
  let pUn : {u // u ∈ T} := ⟨iUn (C := C) m g, by simp [T]⟩
  let pEa : {u // u ∈ T} := ⟨iEa (C := C) m g, by simp [T]⟩
  let right :
      (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) → Bool × C :=
    fun vals =>
      (treatFun (m (show C from vals pUn)) (show ℝ from vals pEa),
        (show C from vals pUn))
  have hright : Measurable right := by
    have hUn : Measurable (fun vals : (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) =>
        (show C from vals pUn)) := by
      exact measurable_pi_apply pUn
    have hEa : Measurable (fun vals : (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) =>
        (show ℝ from vals pEa)) := by
      exact measurable_pi_apply pEa
    have htreat : Measurable
        (fun vals : (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) =>
          treatFun (m (show C from vals pUn)) (show ℝ from vals pEa)) := by
      unfold treatFun
      apply measurable_to_bool
      simpa [Set.preimage, decide_eq_true_eq] using
        measurableSet_le hEa ((measurable_of_finite m).comp hUn)
    exact htreat.prodMk hUn
  have hcomp := hbase.comp (measurable_pi_apply pEy) hright
  simpa [S, T, pEy, pUn, pEa, right] using hcomp

private lemma dgp_integral_ey_threshold (d : Bool) (x : C)
    (ht : g d x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0) ∂(dgpPO m g).μ =
      g d x := by
  change ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (fun e : ℝ => if e ≤ g d x then (1 : ℝ) else 0) (ℓ (iEy (C := C) m g)) ∂Measure.pi
        (dgpSCM m g).latentDist =
      g d x
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  have hf_meas : Measurable (fun e : ℝ => if e ≤ g d x then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  rw [← integral_map (μ := Measure.pi (dgpSCM m g).latentDist)
    (f := fun e : ℝ => if e ≤ g d x then (1 : ℝ) else 0)
    (measurable_pi_apply (iEy (C := C) m g)).aemeasurable]
  swap
  · exact hf_meas.aestronglyMeasurable
  rw [Measure.pi_map_eval]
  have hscale : (∏ j ∈ Finset.univ.erase (iEy (C := C) m g),
      ((dgpSCM m g).latentDist j) Set.univ) = 1 := by
    simp
  rw [hscale, one_smul]
  unfold iEy dgpSCM
  change ∫ e, (if e ≤ g d x then (1 : ℝ) else 0) ∂unifLaw = g d x
  exact unifLaw_integral_Iic_indicator (g d x) ht

private lemma dgp_condExp_ey_threshold_const (d : Bool) (x : C)
    (ht : g d x ∈ Set.Icc (0 : ℝ) 1) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0 |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance]
      =ᵐ[(dgpPO m g).μ] fun _ => g d x := by
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEy (C := C) m g)
  let dxFun : SCM.LatentValues (dgpSCM m g) → Bool × C :=
    fun ℓ => (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
      ℓ (iUn (C := C) m g))
  let eInd : SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun ℓ => if eFun ℓ ≤ g d x then (1 : ℝ) else 0
  have he_sm : StronglyMeasurable[MeasurableSpace.comap eFun inferInstance] eInd := by
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap eFun inferInstance
    have he_meas : Measurable eFun := comap_measurable eFun
    have hset : MeasurableSet {ℓ : SCM.LatentValues (dgpSCM m g) | eFun ℓ ≤ g d x} :=
      measurableSet_le he_meas measurable_const
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  have hle_e : MeasurableSpace.comap eFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [eFun]
    exact (measurable_pi_apply (iEy (C := C) m g)).comap_le
  have hdx_meas : Measurable dxFun := by
    dsimp [dxFun]
    have hUn : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show C from ℓ (iUn (C := C) m g))) :=
      measurable_pi_apply (iUn (C := C) m g)
    have hEa : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show ℝ from ℓ (iEa (C := C) m g))) :=
      measurable_pi_apply (iEa (C := C) m g)
    have htreat : Measurable
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) := by
      unfold treatFun
      apply measurable_to_bool
      simpa [Set.preimage, decide_eq_true_eq] using
        measurableSet_le hEa ((measurable_of_finite m).comp hUn)
    exact htreat.prodMk hUn
  have hle_dx : MeasurableSpace.comap dxFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) :=
    hdx_meas.comap_le
  haveI : IsProbabilityMeasure (dgpPO m g).μ := dgpPO_isProb
  haveI : IsFiniteMeasure (dgpPO m g).μ := inferInstance
  haveI : IsFiniteMeasure ((dgpPO m g).μ.trim hle_dx) :=
    isFiniteMeasure_trim (μ := (dgpPO m g).μ) hle_dx
  have hsig : SigmaFinite ((dgpPO m g).μ.trim hle_dx) :=
    MeasureTheory.IsFiniteMeasure.toSigmaFinite ((dgpPO m g).μ.trim hle_dx)
  have hmain := by
    exact @MeasureTheory.condExp_indep_eq
      (SCM.LatentValues (dgpSCM m g)) ℝ _ _ _
      (MeasurableSpace.comap eFun inferInstance)
      (MeasurableSpace.comap dxFun inferInstance)
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g)))
      ((dgpPO m g).μ) eInd hle_e hle_dx hsig he_sm dgp_indep_ey_dx
  have hmain' :
      (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0 |
        MeasurableSpace.comap
          (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
            (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
              ℓ (iUn (C := C) m g))) inferInstance]
        =ᵐ[(dgpPO m g).μ]
          fun _ => ∫ ℓ : SCM.LatentValues (dgpSCM m g),
            (if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0) ∂(dgpPO m g).μ := by
    simpa [eInd, dxFun, eFun] using hmain
  refine hmain'.trans ?_
  exact Filter.Eventually.of_forall fun ℓ => by
    change (∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0) ∂(dgpPO m g).μ) =
      g d x
    exact dgp_integral_ey_threshold (m := m) (g := g) d x ht

private lemma dgp_condExp_outcome_threshold_var (hv : ValidDGP m g) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      outFun (C := C) g
        (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
        (ℓ (iUn (C := C) m g))
        (ℓ (iEy (C := C) m g)) |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance]
      =ᵐ[(dgpPO m g).μ]
        fun ℓ => g
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
          (ℓ (iUn (C := C) m g)) := by
  classical
  let dxFun : SCM.LatentValues (dgpSCM m g) → Bool × C :=
    fun ℓ => (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
      ℓ (iUn (C := C) m g))
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEy (C := C) m g)
  let cell : Bool × C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun p ℓ => if dxFun ℓ = p then (1 : ℝ) else 0
  let eth : Bool × C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun p ℓ => if eFun ℓ ≤ g p.1 p.2 then (1 : ℝ) else 0
  let piece : Bool × C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun p ℓ => cell p ℓ * eth p ℓ
  have hdx_meas : Measurable dxFun := by
    dsimp [dxFun]
    have hUn : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show C from ℓ (iUn (C := C) m g))) :=
      measurable_pi_apply (iUn (C := C) m g)
    have hEa : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show ℝ from ℓ (iEa (C := C) m g))) :=
      measurable_pi_apply (iEa (C := C) m g)
    have htreat : Measurable
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) := by
      unfold treatFun
      apply measurable_to_bool
      simpa [Set.preimage, decide_eq_true_eq] using
        measurableSet_le hEa ((measurable_of_finite m).comp hUn)
    exact htreat.prodMk hUn
  have hle_σDX :
      MeasurableSpace.comap dxFun inferInstance ≤
        (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) :=
    hdx_meas.comap_le
  have hcell_sm : ∀ p, StronglyMeasurable[MeasurableSpace.comap dxFun inferInstance] (cell p) := by
    intro p
    have hdx_meas' :
        @Measurable (SCM.LatentValues (dgpSCM m g)) (Bool × C)
          (MeasurableSpace.comap dxFun inferInstance) inferInstance dxFun :=
      comap_measurable dxFun
    have hs :
        @MeasurableSet (SCM.LatentValues (dgpSCM m g))
          (MeasurableSpace.comap dxFun inferInstance)
          {ℓ : SCM.LatentValues (dgpSCM m g) | dxFun ℓ = p} :=
      (MeasurableSet.singleton p).preimage hdx_meas'
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap dxFun inferInstance
    exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
  have heth_meas : ∀ p, Measurable (eth p) := by
    intro p
    change @Measurable (SCM.LatentValues (dgpSCM m g)) ℝ
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) inferInstance
      (eth p)
    dsimp [eth, eFun]
    exact Measurable.ite
      (measurableSet_le
        (show Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          ℓ (iEy (C := C) m g)) from measurable_pi_apply (iEy (C := C) m g))
        measurable_const)
      measurable_const measurable_const
  have heth_int : ∀ p, Integrable (eth p) (dgpPO m g).μ := by
    intro p
    exact integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) (heth_meas p) fun ℓ => by
      dsimp [eth]
      split_ifs <;> simp
  have hpiece_int : ∀ p, Integrable (piece p) (dgpPO m g).μ := by
    intro p
    refine integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) ?_ ?_
    · change Measurable (piece p)
      exact ((hcell_sm p).mono hle_σDX).measurable.mul (heth_meas p)
    · intro ℓ
      dsimp [piece, cell, eth]
      split_ifs <;> simp
  have hpiece_pull : ∀ p,
      (dgpPO m g).μ[piece p | MeasurableSpace.comap dxFun inferInstance]
        =ᵐ[(dgpPO m g).μ] cell p * (fun _ => g p.1 p.2) := by
    intro p
    have hpull :
        (dgpPO m g).μ[piece p | MeasurableSpace.comap dxFun inferInstance]
          =ᵐ[(dgpPO m g).μ]
            cell p * (dgpPO m g).μ[eth p | MeasurableSpace.comap dxFun inferInstance] := by
      have hmul : piece p = cell p * eth p := rfl
      rw [hmul]
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (μ := (dgpPO m g).μ) (m := MeasurableSpace.comap dxFun inferInstance)
        (hcell_sm p) (hpiece_int p) (heth_int p)
    refine hpull.trans ?_
    have hconst :
        (dgpPO m g).μ[eth p | MeasurableSpace.comap dxFun inferInstance]
          =ᵐ[(dgpPO m g).μ] fun _ => g p.1 p.2 := by
      simpa [eth, eFun, dxFun] using
        dgp_condExp_ey_threshold_const (m := m) (g := g) p.1 p.2 (hv.g_mem p.1 p.2)
    filter_upwards [hconst] with ℓ hℓ
    change cell p ℓ *
        (dgpPO m g).μ[eth p | MeasurableSpace.comap dxFun inferInstance] ℓ =
      cell p ℓ * g p.1 p.2
    exact congrArg (fun y => cell p ℓ * y) hℓ
  have hsource :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        outFun (C := C) g (dxFun ℓ).1 (dxFun ℓ).2 (eFun ℓ))
        =
      (∑ p : Bool × C, piece p) := by
    funext ℓ
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single (dxFun ℓ)]
    · dsimp [piece, cell, eth, outFun]
      simp
    · intro p _ hp
      have hp' : dxFun ℓ ≠ p := fun h => hp h.symm
      dsimp [piece, cell]
      simp [hp']
    · intro hnot
      exact (hnot (Finset.mem_univ (dxFun ℓ))).elim
  have htarget :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => g (dxFun ℓ).1 (dxFun ℓ).2) =
      (∑ p : Bool × C, cell p * fun _ : SCM.LatentValues (dgpSCM m g) => g p.1 p.2) := by
    funext ℓ
    simp only [Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_eq_single (dxFun ℓ)]
    · dsimp [cell]
      simp
    · intro p _ hp
      have hp' : dxFun ℓ ≠ p := fun h => hp h.symm
      dsimp [cell]
      simp [hp']
    · intro hnot
      exact (hnot (Finset.mem_univ (dxFun ℓ))).elim
  have hsum :
      (dgpPO m g).μ[(∑ p : Bool × C, piece p) | MeasurableSpace.comap dxFun inferInstance]
        =ᵐ[(dgpPO m g).μ]
          (∑ p : Bool × C, (dgpPO m g).μ[piece p | MeasurableSpace.comap dxFun inferInstance]) := by
    simpa using
      (MeasureTheory.condExp_finset_sum
        (μ := (dgpPO m g).μ) (s := (Finset.univ : Finset (Bool × C)))
        (f := piece) (by intro p _; exact hpiece_int p)
        (MeasurableSpace.comap dxFun inferInstance))
  refine (MeasureTheory.condExp_congr_ae (μ := (dgpPO m g).μ)
    (m := MeasurableSpace.comap dxFun inferInstance)
    (Filter.EventuallyEq.of_eq hsource)).trans ?_
  refine hsum.trans ?_
  refine (eventuallyEq_sum fun p _ => hpiece_pull p).trans ?_
  exact Filter.EventuallyEq.of_eq htarget.symm

/-- **Unconfoundedness** `A ⟂ (Y(1), Y(0)) | X`.  The treatment noise `Ea` and
outcome noise `Ey` are independent latent roots given the covariate, so the
realized treatment is conditionally independent of the potential-outcome bundle
given `X`.  Discharged via `POSystem.ofSCM_condIndepCF_of_dSep` (d-separation in
the split graph + value correspondences). -/
theorem dgp_unconfoundedness :
    (dgpPO m g).CondIndepCF
      (RegimedVar.ofFactual (dgpBackdoor m g).dVar)
      (dgpBackdoor m g).cfBundle
      (RegimedVar.ofFactual (dgpBackdoor m g).xVar)
      (dgpPO m g).μ := by
  classical
  let X : Finset (SWIGNode WNode) := {SWIGNode.random WNode.A}
  let Y : Finset (SWIGNode WNode) :=
    {SWIGNode.random WNode.Ey, SWIGNode.random WNode.Un}
  let Z : Finset (SWIGNode WNode) := {SWIGNode.random WNode.Xc}
  let cVar : POVar (dgpPO m g) (ValuesOn Z (swigΩ (WΩ C))) :=
    ⟨XIdx m g, by
      simpa [Z] using (dgpXSingletonEquiv (C := C))⟩
  let c : RegimedVar (dgpPO m g) (ValuesOn Z (swigΩ (WΩ C))) :=
    RegimedVar.ofFactual cVar
  let aMap : ValuesOn X (swigΩ (WΩ C)) → Bool :=
    fun vals => vals ⟨SWIGNode.random WNode.A, by simp [X]⟩
  let BMap : ValuesOn Y (swigΩ (WΩ C)) →
      (∀ i : Fin (dgpBackdoor m g).cfBundle.n, (dgpBackdoor m g).cfBundle.type i) :=
    fun vals i => by
      dsimp [POBackdoorSystem.cfBundle, POCFBundle.cons, POCFBundle.nil] at i ⊢
      exact Fin.cases
        (outFun (C := C) g true
          (vals ⟨SWIGNode.random WNode.Un, by simp [Y]⟩)
          (vals ⟨SWIGNode.random WNode.Ey, by simp [Y]⟩))
        (fun j => Fin.cases
          (outFun (C := C) g false
            (vals ⟨SWIGNode.random WNode.Un, by simp [Y]⟩)
            (vals ⟨SWIGNode.random WNode.Ey, by simp [Y]⟩))
          (fun k => k.elim0) j) i
  haveI : StandardBorelSpace (POSystem.ofSCM (dgpSCM m g) (dgpFixed m g)).Ω := by
    change StandardBorelSpace (dgpPO m g).Ω
    exact dgpPO_borel
  haveI : StandardBorelSpace
      (∀ i : Fin (dgpBackdoor m g).cfBundle.n, (dgpBackdoor m g).cfBundle.type i) := by
    haveI : ∀ i : Fin (dgpBackdoor m g).cfBundle.n,
        StandardBorelSpace ((dgpBackdoor m g).cfBundle.type i) := by
      intro i
      dsimp [POBackdoorSystem.cfBundle, POCFBundle.cons, POCFBundle.nil] at i ⊢
      exact Fin.cases (inferInstance : StandardBorelSpace ℝ)
        (fun j => Fin.cases (inferInstance : StandardBorelSpace ℝ)
          (fun k => k.elim0) j) i
    exact StandardBorelSpace.pi_countable
  haveI : Nonempty
      (∀ i : Fin (dgpBackdoor m g).cfBundle.n, (dgpBackdoor m g).cfBundle.type i) := by
    haveI : ∀ i : Fin (dgpBackdoor m g).cfBundle.n,
        Nonempty ((dgpBackdoor m g).cfBundle.type i) := by
      intro i
      dsimp [POBackdoorSystem.cfBundle, POCFBundle.cons, POCFBundle.nil] at i ⊢
      exact Fin.cases (inferInstance : Nonempty ℝ)
        (fun j => Fin.cases (inferInstance : Nonempty ℝ)
          (fun k => k.elim0) j) i
    infer_instance
  have hci :
      (dgpPO m g).CondIndepCF
        (RegimedVar.ofFactual (dgpBackdoor m g).dVar)
        (dgpBackdoor m g).cfBundle c (dgpPO m g).μ := by
    refine POSystem.ofSCM_condIndepCF_of_dSep (M := dgpSCM m g) (s := dgpFixed m g)
      (X := X) (Y := Y) (Z := Z)
      ?hX ?hY ?hZ ?hDisj_XY ?hDisj_XZ ?hDisj_YZ ?hdSep
      (RegimedVar.ofFactual (dgpBackdoor m g).dVar)
      (dgpBackdoor m g).cfBundle c aMap BMap ?haMap ?hBMap ?ha_value ?hB_value ?hc_value
    · intro v hv
      simp [X] at hv
      subst v
      simp [SCM.randomVars, dgpSCM, wSWIGGraph]
    · intro v hv
      simp [Y] at hv
      rcases hv with rfl | rfl <;> simp [SCM.randomVars, dgpSCM, wSWIGGraph]
    · intro v hv
      simp [Z] at hv
      subst v
      simp [SCM.randomVars, dgpSCM, wSWIGGraph]
    · native_decide
    · native_decide
    · native_decide
    · change (initialSWIG wDAG).dSep
        ({SWIGNode.random WNode.A} : Finset (SWIGNode WNode))
        ({SWIGNode.random WNode.Ey, SWIGNode.random WNode.Un} : Finset (SWIGNode WNode))
        ({SWIGNode.random WNode.Xc} : Finset (SWIGNode WNode))
      native_decide
    · dsimp [aMap]
      exact measurable_pi_apply
        (⟨SWIGNode.random WNode.A, by simp [X]⟩ : {w // w ∈ X})
    · refine measurable_pi_lambda _ ?_
      intro i
      fin_cases i
      · dsimp [BMap]
        unfold outFun
        exact Measurable.ite
            (measurableSet_le
            (measurable_pi_apply
              (⟨SWIGNode.random WNode.Ey, by simp [Y]⟩ : {w // w ∈ Y}))
            ((measurable_of_finite (g true)).comp
              (measurable_pi_apply
                (⟨SWIGNode.random WNode.Un, by simp [Y]⟩ : {w // w ∈ Y}))))
          measurable_const measurable_const
      · dsimp [BMap]
        unfold outFun
        exact Measurable.ite
            (measurableSet_le
            (measurable_pi_apply
              (⟨SWIGNode.random WNode.Ey, by simp [Y]⟩ : {w // w ∈ Y}))
            ((measurable_of_finite (g false)).comp
              (measurable_pi_apply
                (⟨SWIGNode.random WNode.Un, by simp [Y]⟩ : {w // w ∈ Y}))))
          measurable_const measurable_const
    · funext ℓ
      change (dgpBackdoor m g).factualD ℓ =
        (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.A, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩
      rw [dgp_factualD_eq_treatFun (m := m) (g := g)]
      symm
      rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.A, by simp [dgpSCM, wSWIGGraph]⟩]
      change treatFun (m ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩))
          (ℓ (iEa (C := C) m g)) =
        treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
      rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
      unfold dgpSCM parentVal iUn
      rfl
    · funext ℓ i
      dsimp [POCFBundle.jointValue, POBackdoorSystem.cfBundle, POCFBundle.cons,
        POCFBundle.nil, BMap]
      fin_cases i
      · change (dgpBackdoor m g).YofD true ℓ =
          outFun (C := C) g true
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Un, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩)
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Ey, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩)
        rw [dgp_YofD_eq_outFun (m := m) (g := g) true]
        rfl
      · change (dgpBackdoor m g).YofD false ℓ =
          outFun (C := C) g false
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Un, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩)
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Ey, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩)
        rw [dgp_YofD_eq_outFun (m := m) (g := g) false]
        rfl
    · funext ℓ z
      rcases z with ⟨v, hv⟩
      simp [Z] at hv
      subst v
      change (dgpBackdoor m g).factualX ℓ =
        (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩
      rw [dgp_factualX_eq_latentUn (m := m) (g := g)]
      change ℓ (iUn (C := C) m g) =
        (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩
      rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
      unfold dgpSCM parentVal iUn
      rfl
  have hc_eq : c.value =
      SCM.singletonValues (Ω := WΩ C) (v := SWIGNode.random WNode.Xc) ∘
        (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value := by
    funext ℓ z
    rcases z with ⟨v, hv⟩
    simp [Z] at hv
    subst v
    rfl
  refine POSystem.condIndepCF_congr_cond ?_ hci
  rw [hc_eq]
  apply le_antisymm
  · have hx_meas :
        @Measurable (dgpPO m g).Ω C
          (MeasurableSpace.comap
            (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value inferInstance)
          inferInstance
          (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value :=
      comap_measurable _
    exact ((SCM.measurable_singletonValues (Ω := WΩ C)
      (v := SWIGNode.random WNode.Xc)).comp hx_meas).comap_le
  · have hsingleton_meas :
        @Measurable (dgpPO m g).Ω
          (ValuesOn ({SWIGNode.random WNode.Xc} : Finset (SWIGNode WNode)) (swigΩ (WΩ C)))
          (MeasurableSpace.comap
            (SCM.singletonValues (Ω := WΩ C) (v := SWIGNode.random WNode.Xc) ∘
              (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value) inferInstance)
          inferInstance
          (SCM.singletonValues (Ω := WΩ C) (v := SWIGNode.random WNode.Xc) ∘
            (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value) :=
      comap_measurable _
    have hx_meas :
        @Measurable (dgpPO m g).Ω C
          (MeasurableSpace.comap
            (SCM.singletonValues (Ω := WΩ C) (v := SWIGNode.random WNode.Xc) ∘
              (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value) inferInstance)
          inferInstance
          (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value := by
      simpa [Function.comp_assoc] using
        ((SCM.measurable_singletonValue (Ω := WΩ C)
          (v := SWIGNode.random WNode.Xc)).comp hsingleton_meas)
    exact hx_meas.comap_le

/-- The constructed treatment propensity equals the supplied propensity function
given the covariate.

This follows from the structural treatment assignment using independent unit-interval noise. -/
theorem dgp_propScore_eq_m (hv : ValidDGP m g) :
    (dgpBackdoor m g).propScore true
      =ᵐ[(dgpPO m g).μ] (fun ω => m ((dgpBackdoor m g).factualX ω)) := by
  unfold POBackdoorSystem.propScore
  rw [POBackdoorSystem.sigmaX, dgp_factualX_eq_latentUn (m := m) (g := g),
    dgp_dIndicator_true_eq_threshold (m := m) (g := g)]
  exact dgp_condExp_ea_threshold_var (m := m) (g := g) hv

/-- The constructed adjusted conditional mean equals the supplied outcome regression
in each treatment arm.

Only overlap is needed for the observable ratio defining the adjusted conditional mean. -/
theorem dgp_adjustedCE_eq_g (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1)
    (d : Bool) :
    (dgpBackdoor m g).adjustedCE d
      =ᵐ[(dgpPO m g).μ] (fun ω => g d ((dgpBackdoor m g).factualX ω)) := by
  let S : POBackdoorSystem (dgpPO m g) C := dgpBackdoor m g
  have hY : Integrable S.factualY (dgpPO m g).μ := by
    refine MeasureTheory.Integrable.of_bound S.measurable_factualY.aestronglyMeasurable 1
      (Filter.Eventually.of_forall ?_)
    intro ℓ
    rw [show S.factualY =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          outFun (C := C) g
            (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
            (ℓ (iUn (C := C) m g))
            (ℓ (iEy (C := C) m g))) from
          dgp_factualY_eq_outFun (m := m) (g := g)]
    by_cases h :
        (show ℝ from ℓ (iEy (C := C) m g)) ≤
          g (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
            (ℓ (iUn (C := C) m g))
    · simp [outFun, h]
    · simp [outFun, h]
  have hov :
      ∀ᵐ ω ∂(dgpPO m g).μ,
        0 < S.propScore true ω ∧ S.propScore true ω < 1 := by
    filter_upwards [dgp_propScore_eq_m (m := m) (g := g) hv] with ω hω
    rw [hω]
    exact ⟨(hso _).1, (hso _).2⟩
  have h_ne : ∀ᵐ ω ∂(dgpPO m g).μ, S.propScore d ω ≠ 0 :=
    S.propScore_ne_of_overlap hov d
  have houtcome :
      S.outcomeReg =ᵐ[(dgpPO m g).μ]
        fun ω => g (S.factualD ω) (S.factualX ω) := by
    unfold POBackdoorSystem.outcomeReg POBackdoorSystem.sigmaDX POBackdoorSystem.factualDX
    rw [show S.factualY =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          outFun (C := C) g
            (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
            (ℓ (iUn (C := C) m g))
            (ℓ (iEy (C := C) m g))) from
          dgp_factualY_eq_outFun (m := m) (g := g)]
    rw [show S.factualD =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) from
          dgp_factualD_eq_treatFun (m := m) (g := g)]
    rw [show S.factualX =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) from
          dgp_factualX_eq_latentUn (m := m) (g := g)]
    exact dgp_condExp_outcome_threshold_var (m := m) (g := g) hv
  have hratio_def :
      S.adjustedCE d
        = S.xVar.condExpRatio
          (fun ω => S.factualY ω * S.dVar.indicator d ω)
          (S.dVar.indicator d) (dgpPO m g).μ := by
    funext ω
    unfold POBackdoorSystem.adjustedCE POBackdoorSystem.propScore
      POBackdoorSystem.sigmaX POBackdoorSystem.factualX POVar.condExpRatio
      POVar.condExpGiven
    rfl
  rw [hratio_def]
  refine S.xVar.condExpRatio_eq_of_mul
    (g := fun ω => S.factualY ω * S.dVar.indicator d ω)
    (h := S.dVar.indicator d)
    (target := fun ω => g d (S.factualX ω)) ?_ ?_
  · let s : Set (dgpPO m g).Ω := S.dVar.event d
    let target : (dgpPO m g).Ω → ℝ := fun ω => g d (S.factualX ω)
    have hsDX : MeasurableSet[S.sigmaDX] s := by
      change MeasurableSet[MeasurableSpace.comap S.factualDX inferInstance]
        (S.factualD ⁻¹' {d})
      exact ⟨Prod.fst ⁻¹' {d}, measurableSet_singleton d |>.preimage measurable_fst, rfl⟩
    have hs : MeasurableSet s := S.dVar.measurableSet_event d
    have hmul_indicator :
        (fun ω => S.factualY ω * S.dVar.indicator d ω) = s.indicator S.factualY := by
      funext ω
      by_cases hω : ω ∈ s
      · have hind : S.dVar.indicator d ω = 1 := S.dVar.indicator_apply_eq_one hω
        rw [hind, mul_one, Set.indicator_of_mem hω]
      · have hD : S.factualD ω ≠ d := hω
        have hind : S.dVar.indicator d ω = 0 := S.dVar.indicator_apply_eq_zero hD
        rw [hind, mul_zero, Set.indicator_of_notMem hω]
    have htarget_meas : Measurable[S.sigmaX] target := by
      have hg_d : Measurable (fun x : C => g d x) := measurable_of_finite _
      change Measurable[MeasurableSpace.comap S.factualX inferInstance]
        ((fun x : C => g d x) ∘ S.factualX)
      exact hg_d.comp (comap_measurable S.factualX)
    have htarget_sm : StronglyMeasurable[S.sigmaX] target :=
      htarget_meas.stronglyMeasurable
    have houtcome_target :
        s.indicator S.outcomeReg =ᵐ[(dgpPO m g).μ] s.indicator target := by
      filter_upwards [houtcome] with ω hω
      by_cases hmem : ω ∈ s
      · have hD : S.factualD ω = d := hmem
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω, hD]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    have htower :
        (dgpPO m g).μ[s.indicator S.factualY | S.sigmaX]
          =ᵐ[(dgpPO m g).μ] (dgpPO m g).μ[s.indicator S.outcomeReg | S.sigmaX] := by
      simpa [s, POBackdoorSystem.outcomeReg] using
        MeasureTheory.condExp_setIndicator_condExp_of_le
          (μ := (dgpPO m g).μ) (m := S.sigmaX) (m' := S.sigmaDX)
          S.sigmaX_le_sigmaDX S.sigmaDX_le hsDX hY
    have hleft :
        (dgpPO m g).μ[fun ω => S.factualY ω * S.dVar.indicator d ω | S.sigmaX]
          =ᵐ[(dgpPO m g).μ] (dgpPO m g).μ[s.indicator target | S.sigmaX] :=
      (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := (dgpPO m g).μ)
        (Filter.EventuallyEq.of_eq hmul_indicator)).trans
        (htower.trans
          (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := (dgpPO m g).μ)
            houtcome_target))
    have hind_int : Integrable (S.dVar.indicator d) (dgpPO m g).μ :=
      S.dVar.integrable_indicator d
    have htarget_mul_indicator :
        target * S.dVar.indicator d = s.indicator target := by
      funext ω
      by_cases hω : ω ∈ s
      · have hind : S.dVar.indicator d ω = 1 := S.dVar.indicator_apply_eq_one hω
        rw [Pi.mul_apply, hind, mul_one, Set.indicator_of_mem hω]
      · have hD : S.factualD ω ≠ d := hω
        have hind : S.dVar.indicator d ω = 0 := S.dVar.indicator_apply_eq_zero hD
        rw [Pi.mul_apply, hind, mul_zero, Set.indicator_of_notMem hω]
    have htarget_mul_int : Integrable (target * S.dVar.indicator d) (dgpPO m g).μ := by
      rw [htarget_mul_indicator]
      exact (MeasureTheory.Integrable.indicator
        (MeasureTheory.integrable_condExp (μ := (dgpPO m g).μ) (m := S.sigmaDX) (f := S.factualY)) hs)
          |>.congr houtcome_target
    have hpull :
        (dgpPO m g).μ[target * S.dVar.indicator d | S.sigmaX]
          =ᵐ[(dgpPO m g).μ] target * (dgpPO m g).μ[S.dVar.indicator d | S.sigmaX] :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := (dgpPO m g).μ) htarget_sm htarget_mul_int hind_int
    change (dgpPO m g).μ[fun ω => S.factualY ω * S.dVar.indicator d ω | S.sigmaX]
        =ᵐ[(dgpPO m g).μ] (dgpPO m g).μ[S.dVar.indicator d | S.sigmaX] * target
    refine hleft.trans ?_
    refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := (dgpPO m g).μ)
      (Filter.EventuallyEq.of_eq htarget_mul_indicator.symm)).trans ?_
    exact hpull.trans (Filter.EventuallyEq.of_eq (by
      funext ω
      exact mul_comm _ _))
  · have hEq : S.xVar.condExpGiven (S.dVar.indicator d) (dgpPO m g).μ = S.propScore d := by
      unfold POVar.condExpGiven POBackdoorSystem.propScore
        POBackdoorSystem.sigmaX POBackdoorSystem.factualX
      rfl
    rw [hEq]
    exact h_ne

/-- The constructed propensity satisfies overlap whenever the supplied propensity
is strictly between zero and one. -/
theorem dgp_overlap (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂(dgpPO m g).μ,
      0 < (dgpBackdoor m g).propScore true ω ∧
      (dgpBackdoor m g).propScore true ω < 1 := by
  filter_upwards [dgp_propScore_eq_m (m := m) (g := g) hv] with ω hω
  rw [hω]; exact ⟨(hso _).1, (hso _).2⟩

private lemma outFun_norm_le_one (d : Bool) (x : C) (ey : ℝ) :
    ‖outFun (C := C) g d x ey‖ ≤ (1 : ℝ) := by
  unfold outFun
  split_ifs <;> norm_num

private lemma dgp_integrable_YofD (d : Bool) :
    Integrable ((dgpBackdoor m g).YofD d) (dgpPO m g).μ := by
  refine MeasureTheory.Integrable.of_bound
    ((dgpBackdoor m g).measurable_YofD d).aestronglyMeasurable 1
    (Filter.Eventually.of_forall ?_)
  intro ℓ
  rw [dgp_YofD_eq_outFun (m := m) (g := g) d]
  exact outFun_norm_le_one (g := g) d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))

/-- The treated potential outcome is integrable because it is bounded Bernoulli-valued. -/
theorem dgp_integrable_Y1 :
    Integrable ((dgpBackdoor m g).YofD true) (dgpPO m g).μ := by
  exact dgp_integrable_YofD (m := m) (g := g) true

/-- The control potential outcome is integrable because it is bounded Bernoulli-valued. -/
theorem dgp_integrable_Y0 :
    Integrable ((dgpBackdoor m g).YofD false) (dgpPO m g).μ := by
  exact dgp_integrable_YofD (m := m) (g := g) false

/-- The constructed finite backdoor system satisfies the standard backdoor assumptions. -/
theorem dgp_assumptions (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    (dgpBackdoor m g).Assumptions where
  consistency := dgp_consistency
  unconfoundedness := dgp_unconfoundedness
  overlap := dgp_overlap hv hso
  integrable_Y1 := dgp_integrable_Y1
  integrable_Y0 := dgp_integrable_Y0

/-! ## The covariate marginal is uniform -/

/-- The factual covariate marginal of the constructed system is uniform on the
finite covariate space. -/
theorem dgp_P_X_eq_covLaw :
    (dgpPO m g).μ.map (dgpBackdoor m g).factualX = covLaw C := by
  let iUn : {u // u ∈ (dgpSCM m g).unobserved} :=
    ⟨SWIGNode.random WNode.Un, by simp [dgpSCM, wSWIGGraph]⟩
  have hx : (dgpBackdoor m g).factualX =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ iUn) := by
    funext ℓ
    simp only [POBackdoorSystem.factualX, POVar.factual, POVar.cf]
    change (dgpBackdoor m g).xVar.equiv
        (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (XIdx m g)) =
      ℓ iUn
    rw [inducedEval_empty_eq_evalMap]
    change (XEquiv m g)
        ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, dgpSCM, wSWIGGraph]⟩) = ℓ iUn
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    unfold XEquiv dgpSCM parentVal
    rfl
  rw [hx]
  change Measure.map (Function.eval iUn) (SCM.latentProduct (dgpSCM m g)) = covLaw C
  letI : ∀ u : {u // u ∈ (dgpSCM m g).unobserved},
      IsProbabilityMeasure ((dgpSCM m g).latentDist u) :=
    (dgpSCM m g).isProbability_latent
  haveI : ∀ u : {u // u ∈ (dgpSCM m g).unobserved},
      SigmaFinite ((dgpSCM m g).latentDist u) := fun _ => inferInstance
  rw [SCM.latentProduct, MeasureTheory.Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  change covLaw C = covLaw C
  rfl

/-! ## The estimation system with value-space regressions `(g, m)` -/

/-- This is the backdoor estimation system whose value-space regression and
propensity are the supplied functions.

Strict overlap supplies the pointwise positivity and upper-bound fields for the propensity. -/
noncomputable def dgpBES (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    BackdoorEstimationSystem (dgpPO m g) C where
  toPOBackdoorSystem := dgpBackdoor m g
  μ_val := g
  μ_meas := fun _ => measurable_of_finite _
  e_val := m
  e_meas := measurable_of_finite _
  e_pos := fun x => (hso x).1
  e_lt_one := fun x => (hso x).2
  μ_reg_compat := fun d => (dgp_adjustedCE_eq_g hv hso d).symm
  e_compat := dgp_propScore_eq_m hv

/-! ## The bridge -/

/-- The causal ATE of the constructed backdoor system equals the observed-data
contrast used by the minimax proof.

The bridge uses backdoor identification and the uniform covariate marginal, so lower bounds for
the observed-data contrast transfer to the causal estimand. -/
theorem causalATE_eq_ate (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    causalATE m g = ate g := by
  have hθ : (dgpBES (m := m) (g := g) hv hso).θ₀ =
      (dgpBES (m := m) (g := g) hv hso).toPOBackdoorSystem.ATE :=
    (dgpBES (m := m) (g := g) hv hso).θ₀_eq_ATE
      (dgp_assumptions (m := m) (g := g) hv hso)
  -- `causalATE = S.ATE = θ₀ = ∫ (g 1 − g 0) dP_X`, and `P_X = Uniform(C)` turns
  -- the integral into the average `(1/card C) Σ_x (g 1 x − g 0 x) = ate g`.
  rw [causalATE]
  change (dgpBES (m := m) (g := g) hv hso).toPOBackdoorSystem.ATE = ate g
  rw [← hθ]
  unfold BackdoorEstimationSystem.θ₀ BackdoorEstimationSystem.P_X dgpBES
  rw [dgp_P_X_eq_covLaw (m := m) (g := g)]
  unfold covLaw ate
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply]
  calc
    ∑ x, (Fintype.card C : ℝ)⁻¹ * (g true x - g false x)
        = ∑ x, ((Fintype.card C : ℝ)⁻¹ * g true x -
            (Fintype.card C : ℝ)⁻¹ * g false x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = ∑ x, (Fintype.card C : ℝ)⁻¹ * g true x -
          ∑ x, (Fintype.card C : ℝ)⁻¹ * g false x := by
          rw [Finset.sum_sub_distrib]
    _ = (Fintype.card C : ℝ)⁻¹ * ∑ x, g true x -
          (Fintype.card C : ℝ)⁻¹ * ∑ x, g false x := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = (Fintype.card C : ℝ)⁻¹ * (∑ x, g true x - ∑ x, g false x) := by
          ring

end Causalean.Estimation.MinimaxATE.Causal
