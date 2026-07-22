/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Frontdoor ATE identification in the Potential Outcome Framework

Implements `prop:po-frontdoor-ate` from Basic Concepts.tex (§subsec:po-frontdoor-ate):
classical frontdoor identification of the ATE under binary treatment `A`,
discrete mediator `M` (finite value space), and real outcome `Y`.  The
conclusion is the discrete-sum identity

    E[Y(a)] = ∑ₘ ( E[Y | A=1, M=m] · P(A=1) + E[Y | A=0, M=m] · P(A=0) )
                  · P(M = m | A = a)

with ATE obtained by subtracting `a = 1` and `a = 0`.

The proof uses the **composition clause** of `POSystem.Consistency` to collapse
the two-variable counterfactual `Y(a, M(a))` to `Y(a)` on the level set
`{M(a) = m}`, full mediation to drop the treatment index from `Y(a,m)`, and the
two PO exchangeability assumptions to identify the resulting conditional
expectations.  Event-level style (`eventCondExp`), matching `Manski.lean` /
`DID.lean` — no σ-algebra conditional expectations are used.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.CondExpTooling
import Causalean.PO.Conditioning.EventCondExp
import Causalean.PO.Assumptions.IndepCF
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Frontdoor Average Treatment Effect

This file formalizes classical frontdoor identification for a binary treatment,
finite mediator, and real outcome in the potential-outcome framework. It defines
the frontdoor subsystem, assumptions, observable adjustment functional, and the
proof equating that functional with the average treatment effect.

The proof uses event-conditional means, full mediation, two exchangeability
assumptions, and composition consistency to relate the two-variable
counterfactual outcome through the mediator to the single-treatment potential
outcome. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A frontdoor system consists of a binary treatment, a finite discrete
mediator, and a real outcome.

The treatment, mediator, and outcome nodes are pairwise distinct. -/
structure POFrontdoorSystem (P : POSystem) (β : Type*)
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
    [DecidableEq β] where
  A : P.V
  M : P.V
  Y : P.V
  hAbool : P.X A ≃ᵐ Bool
  hMequiv : P.X M ≃ᵐ β
  hYreal : P.X Y ≃ᵐ ℝ
  hAM : A ≠ M
  hAY : A ≠ Y
  hMY : M ≠ Y

namespace POFrontdoorSystem

variable {P : POSystem} {β : Type*}
  [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β] [DecidableEq β]
  (S : POFrontdoorSystem P β)

/-! ### `POVar` wrappers -/

/-- The treatment node is packaged as a binary potential-outcome variable. -/
def aVar : POVar P Bool := ⟨S.A, S.hAbool⟩
/-- The mediator node is packaged as a potential-outcome variable with finite mediator values. -/
def mVar : POVar P β    := ⟨S.M, S.hMequiv⟩
/-- The outcome node is packaged as a real-valued potential-outcome variable. -/
def yVar : POVar P ℝ    := ⟨S.Y, S.hYreal⟩

/-! ### Counterfactuals -/

/-- The treatment-arm potential outcome fixes treatment to the chosen arm. -/
noncomputable def YofA (a : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.aVar a

/-- The treatment-arm potential mediator fixes treatment to the chosen arm. -/
noncomputable def MofA (a : Bool) : P.Ω → β := S.mVar.cfUnder S.aVar a

/-- The joint treatment-mediator regime fixes treatment and mediator simultaneously.

Built as a disjoint union of the singleton regimes `{A ← a}` and `{M ← m}`; the
disjointness hypothesis uses `S.hAM : A ≠ M`. -/
noncomputable def regimeAM (a : Bool) (m : β) : Regime P.V P.X :=
  (Regime.single S.A (S.hAbool.symm a)).sqcup
    (Regime.single S.M (S.hMequiv.symm m))
    (Regime.single_disjoint_single S.hAM _ _)

/-- The two-variable potential outcome fixes both treatment and mediator. -/
noncomputable def YofAM (a : Bool) (m : β) : P.Ω → ℝ :=
  S.yVar.cf (S.regimeAM a m)

/-! ### Factuals -/

/-- The factual treatment is the observed treatment assignment for each unit. -/
noncomputable def factualA : P.Ω → Bool := S.aVar.factual
/-- The factual mediator is the observed mediator value for each unit. -/
noncomputable def factualM : P.Ω → β    := S.mVar.factual
/-- The factual outcome is the observed outcome for each unit. -/
noncomputable def factualY : P.Ω → ℝ    := S.yVar.factual

/-! ### Measurability -/

/-- Treatment-arm potential outcomes are measurable. -/
lemma measurable_YofA (a : Bool) : Measurable (S.YofA a) :=
  S.yVar.measurable_cfUnder S.aVar a
/-- Treatment-arm potential mediators are measurable. -/
lemma measurable_MofA (a : Bool) : Measurable (S.MofA a) :=
  S.mVar.measurable_cfUnder S.aVar a
/-- Joint treatment-mediator potential outcomes are measurable. -/
lemma measurable_YofAM (a : Bool) (m : β) : Measurable (S.YofAM a m) :=
  S.yVar.measurable_cf _
/-- The observed treatment is measurable. -/
lemma measurable_factualA : Measurable S.factualA := S.aVar.measurable_factual
/-- The observed mediator is measurable. -/
lemma measurable_factualM : Measurable S.factualM := S.mVar.measurable_factual
/-- The observed outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-! ### Events and indicators -/

/-- The event `{A = a}`. -/
def aEvent (a : Bool) : Set P.Ω := S.aVar.event a
/-- The event `{M = m}`. -/
def mEvent (m : β) : Set P.Ω := S.mVar.event m

/-- The factual treatment event for a treatment arm is measurable. -/
lemma measurableSet_aEvent (a : Bool) : MeasurableSet (S.aEvent a) :=
  S.aVar.measurableSet_event _
/-- The factual mediator event for a mediator value is measurable. -/
lemma measurableSet_mEvent (m : β) : MeasurableSet (S.mEvent m) :=
  S.mVar.measurableSet_event _

/-! ### Counterfactual bundle (for the `M(a) ⊥ A` assumption)

The bundle `[M(true), M(false)]` is independent of factual `A`.  Sufficient for
the marginal exchangeability statement `M(a) ⊥ A` for each `a`. -/

/-- `M(a)` as a `RegimedVar`. -/
def mUnderA (a : Bool) : RegimedVar P β :=
  ⟨S.mVar, Regime.single S.A (S.hAbool.symm a)⟩

/-- Bundle `[M(true), M(false)]`, used to state `A ⊥ (M(1), M(0))`. -/
noncomputable def mBundle : POCFBundle P :=
  POCFBundle.cons (S.mUnderA true) <|
  POCFBundle.cons (S.mUnderA false) <|
  POCFBundle.nil P

/-! ### Observable functionals -/

/-- `P(A = a)`. -/
noncomputable def pA (a : Bool) : ℝ := (P.μ (S.aEvent a)).toReal

/-- `P(M = m | A = a)`, event-conditional probability. -/
noncomputable def pMgivenA (m : β) (a : Bool) : ℝ :=
  eventCondExp P.μ (S.aEvent a) (S.mVar.indicator m)

/-- `E[Y | A = a, M = m]`. -/
noncomputable def EYgivenAM (a : Bool) (m : β) : ℝ :=
  eventCondExp P.μ (S.aEvent a ∩ S.mEvent m) S.factualY

/-- The frontdoor-adjusted functional `φ(a)` at treatment `a`:

    ∑ₘ (E[Y|A=1,M=m]·P(A=1) + E[Y|A=0,M=m]·P(A=0)) · P(M=m|A=a). -/
noncomputable def frontdoorTerm (a : Bool) : ℝ :=
  ∑ m : β,
    (S.EYgivenAM true m * S.pA true + S.EYgivenAM false m * S.pA false)
      * S.pMgivenA m a

/-- Target parameter `E[Y(1) - Y(0)]`. -/
noncomputable def ATE : ℝ := ∫ ω, S.YofA true ω - S.YofA false ω ∂P.μ

/-- Observable (frontdoor-adjusted) ATE. -/
noncomputable def frontdoorATE : ℝ := S.frontdoorTerm true - S.frontdoorTerm false

/-! ### Assumptions (def:po-frontdoor-ate-assumptions) -/

/-- Frontdoor assumptions at the PO level. -/
structure Assumptions (S : POFrontdoorSystem P β) : Prop where
  /-- Consistency axiom for the ambient PO system. -/
  consistency : P.Consistency
  /-- **Full mediation / exclusion restriction:** `Y(a,m) = Y(a',m)` a.s. for all
  `a, a' ∈ {0,1}` and `m ∈ β`. -/
  fullMediation :
    ∀ (a a' : Bool) (m : β), S.YofAM a m =ᵐ[P.μ] S.YofAM a' m
  /-- **Treatment–mediator exchangeability:** `A ⊥ (M(1), M(0))`.  Equivalent
  (for binary `A`) to `M(a) ⊥ A` for each `a`. -/
  exch_AM : P.IndepCF (RegimedVar.ofFactual S.aVar) S.mBundle P.μ
  /-- **Mediator–outcome exchangeability within treatment arms:** for mediator
  values in the support of `M(a)`, and each treatment arm `a'`, the conditional
  law of `Y(m)` (= any `Y(a,m)` by full mediation) on `{A = a'} ∩ {M = m}`
  equals its conditional law on `{A = a'}`.  Stated at the `eventCondExp` level
  (discrete form, matching Manski/LATE style), and gated by positive `M(a)` mass
  so zero-probability mediator cells need no exchangeability assumption. -/
  exch_MY :
    ∀ (a : Bool) (m : β),
      0 < P.μ ({ω | S.MofA a ω = m}) →
      ∀ a' : Bool,
      eventCondExp P.μ (S.aEvent a' ∩ S.mEvent m) (S.YofAM true m)
        = eventCondExp P.μ (S.aEvent a') (S.YofAM true m)
  /-- **Positivity (treatment):** `P(A = a) > 0`. -/
  posA : ∀ a : Bool, 0 < P.μ (S.aEvent a)
  /-- **Positivity (mediator within support of `M(a)`):** if `P(M(a) = m) > 0`,
  then for every treatment arm `a'` we have `P(A=a', M=m) > 0`.  Stated on the
  `ENNReal`-valued measure for convenience. -/
  posAM : ∀ (a : Bool) (m : β),
    0 < P.μ ({ω | S.MofA a ω = m}) →
      ∀ a' : Bool, 0 < P.μ (S.aEvent a' ∩ S.mEvent m)
  /-- **Joint mediator–outcome independence across worlds:** `M(a) ⊥ Y(1, m)`
  as `IndepFun`.  This is required for the drop-of-conditioning step

      E[Y(m) · 1_{M(a)=m}] = E[Y(m)] · P(M(a) = m)

  used in the frontdoor proof sketch. It is not
  derivable from the other four assumptions in the bare PO framework: under a
  graphical frontdoor DAG it would follow from d-separation (no directed path
  from the counterfactual mediator `M(a)` to the full-mediation outcome
  `Y(1, m)`), but in the bare PO setting it must be stated explicitly.

  Cross-world independence `M(a) ⟂ Y(1, m)`. In Pearl's graphical frontdoor
  this follows from d-separation; here we state it directly as a primitive
  PO assumption. A future graphical-derivation file under `SCM/ID/` could
  derive this from the three Pearl frontdoor graph conditions via the
  SWIG/d-separation infrastructure in `Causalean/Graph/`. -/
  indep_Y_M : ∀ (a : Bool) (m : β), IndepFun (S.MofA a) (S.YofAM true m) P.μ
  /-- Integrability of each `Y(a)`. -/
  integrable_YofA : ∀ a : Bool, Integrable (S.YofA a) P.μ
  /-- Integrability of each `Y(a,m)`. -/
  integrable_YofAM : ∀ (a : Bool) (m : β), Integrable (S.YofAM a m) P.μ

/-! ### Helper lemmas

Each lemma below corresponds to a step in the proof sketch of
`prop:po-frontdoor-ate`. -/

variable {S}

/-- On the event `{A = a}`, `M(a)(ω) = factualM ω`.  Single-target consistency. -/
lemma MofA_eq_factualM_on_aEvent (hC : P.Consistency) (a : Bool)
    {ω : P.Ω} (hω : ω ∈ S.aEvent a) :
    S.MofA a ω = S.factualM ω :=
  POVar.cf_eq_factual_on_event hC S.mVar S.aVar a (Ne.symm S.hAM) hω

/-- On the event `{A = a} ∩ {M = m}`, `Y(a,m)(ω) = factualY ω`.  Multi-target
consistency via `cf_eq_factual_of_factualAgrees`. -/
lemma YofAM_eq_factualY_on_aMEvent (hC : P.Consistency) (a : Bool) (m : β)
    {ω : P.Ω} (hω : ω ∈ S.aEvent a ∩ S.mEvent m) :
    S.YofAM a m ω = S.factualY ω := by
  -- The target set of `regimeAM a m` is `{A, M}`; `Y ∉ {A, M}` since `hAY, hMY`.
  have h_notmem : S.yVar.v ∉ (S.regimeAM a m).target := by
    simp only [regimeAM, Regime.sqcup_target, Regime.single_target, Finset.singleton_union,
      yVar, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨S.hAY.symm, S.hMY.symm⟩
  -- On `{A=a} ∩ {M=m}`, `ω` factually agrees with `regimeAM a m`, by combining
  -- the per-variable factual equalities `aVar.factual ω = a`, `mVar.factual ω = m`.
  have hAgrees : P.FactualAgrees (S.regimeAM a m) ω :=
    POSystem.factualAgrees_sqcup _
      (S.aVar.factualAgrees_single a hω.1)
      (S.mVar.factualAgrees_single m hω.2)
  exact POVar.cf_eq_factual_of_factualAgrees hC S.yVar (S.regimeAM a m)
    h_notmem ω hAgrees

/-- The observed outcome is integrable when all joint treatment-mediator
potential outcomes are integrable and consistency holds. -/
lemma integrable_factualY_of_consistency_integrable_YofAM
    (hC : P.Consistency)
    (hY : ∀ (a : Bool) (m : β), Integrable (S.YofAM a m) P.μ) :
    Integrable S.factualY P.μ := by
  let cell : Bool → β → P.Ω → ℝ :=
    fun a m ω => S.YofAM a m ω * S.aVar.indicator a ω * S.mVar.indicator m ω
  have hcell_int : ∀ a m, Integrable (cell a m) P.μ := by
    intro a m
    have hA_int :
        Integrable (fun ω => S.YofAM a m ω * S.aVar.indicator a ω) P.μ :=
      S.aVar.integrable_mul_indicator a (hY a m) (S.measurable_YofAM a m)
    simpa [cell, mul_assoc] using
      S.mVar.integrable_mul_indicator m hA_int
        ((S.measurable_YofAM a m).mul (S.aVar.measurable_indicator a))
  have hsum_int :
      Integrable (fun ω => ∑ a : Bool, ∑ m : β, cell a m ω) P.μ := by
    have hsum_beta : ∀ a, Integrable (fun ω => ∑ m : β, cell a m ω) P.μ := by
      intro a
      have hsum_finset : ∀ s : Finset β,
          Integrable (fun ω => s.sum fun m => cell a m ω) P.μ := by
        intro s
        refine Finset.induction_on s ?base ?step
        · simp
        · intro m s hms hs
          simpa [Finset.sum_insert hms] using (hcell_int a m).add hs
      simpa using hsum_finset Finset.univ
    have htrue : Integrable (fun ω => ∑ m : β, cell true m ω) P.μ := hsum_beta true
    have hfalse : Integrable (fun ω => ∑ m : β, cell false m ω) P.μ := hsum_beta false
    simpa [Fintype.sum_bool] using htrue.add hfalse
  refine hsum_int.congr (Filter.Eventually.of_forall ?_)
  intro ω
  have hA_indicator : ∀ a, S.aVar.indicator a ω = if S.factualA ω = a then 1 else 0 := by
    intro a
    by_cases hωa : S.factualA ω = a
    · simp [S.aVar.indicator_apply_eq_one hωa, hωa]
    · simp [S.aVar.indicator_apply_eq_zero hωa, hωa]
  have hM_indicator : ∀ m, S.mVar.indicator m ω = if S.factualM ω = m then 1 else 0 := by
    intro m
    by_cases hωm : S.factualM ω = m
    · simp [S.mVar.indicator_apply_eq_one hωm, hωm]
    · simp [S.mVar.indicator_apply_eq_zero hωm, hωm]
  change (∑ a : Bool, ∑ m : β, cell a m ω) = S.factualY ω
  rw [Fintype.sum_bool]
  cases hAω : S.factualA ω
  · simp only [hA_indicator, hAω, Bool.false_eq_true, ↓reduceIte, mul_zero,
      hM_indicator, mul_ite, mul_one, ite_self, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, zero_add, cell]
    exact YofAM_eq_factualY_on_aMEvent hC false (S.factualM ω)
      (show ω ∈ S.aEvent false ∩ S.mEvent (S.factualM ω) from ⟨hAω, rfl⟩)
  · simp only [hA_indicator, hAω, ↓reduceIte, mul_one, hM_indicator, mul_ite,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, Bool.true_eq_false, ite_self,
      Finset.sum_const_zero, add_zero, cell]
    exact YofAM_eq_factualY_on_aMEvent hC true (S.factualM ω)
      (show ω ∈ S.aEvent true ∩ S.mEvent (S.factualM ω) from ⟨hAω, rfl⟩)

namespace Assumptions

/-- Compatibility projection for older call sites: factual outcome integrability
is derived from consistency plus integrability of the finite `Y(a,m)` cells. -/
lemma integrable_factualY (hA : S.Assumptions) :
    Integrable S.factualY P.μ :=
  S.integrable_factualY_of_consistency_integrable_YofAM
    hA.consistency hA.integrable_YofAM

end Assumptions

/-- **Composition lemma** (`def:po-consistency`, composition clause): on the
event `{M(a) = m}`, `Y(a, m)(ω) = Y(a)(ω)`.

This is the potential-outcome version of `Y(a) = Y(a, M(a))` a.s.  We apply
`POSystem.Consistency.composition` with `r₁ = {A ← a}`, `r₂ = {M ← m}`, and the
hypothesis that `M` already takes value `m` under `r₁` (i.e. on `{M(a) = m}`). -/
lemma YofAM_eq_YofA_on_MofA_event (hC : P.Consistency) (a : Bool) (m : β)
    {ω : P.Ω} (hω : S.MofA a ω = m) :
    S.YofAM a m ω = S.YofA a ω := by
  -- Disjointness of the two single-target regimes.
  have hdisj : (Regime.single S.A (S.hAbool.symm a)).Disjoint
                (Regime.single S.M (S.hMequiv.symm m)) :=
    Regime.single_disjoint_single S.hAM _ _
  -- `Y ∉ {A} ∪ {M}`.
  have hY_notmem :
      _root_.Disjoint ({S.Y} : Finset P.V)
        ((Regime.single S.A (S.hAbool.symm a)).target ∪
          (Regime.single S.M (S.hMequiv.symm m)).target) := by
    simp only [Regime.single_target, Finset.singleton_union, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => S.hAY h.symm, fun h => S.hMY h.symm⟩
  -- `IntermediateAgrees`: under `{A ← a}`, `M` evaluates to `hMequiv.symm m`.
  have hInter :
      P.IntermediateAgrees (Regime.single S.A (S.hAbool.symm a))
                            (Regime.single S.M (S.hMequiv.symm m)) ω := by
    intro v hv
    have hvM : v = S.M := Finset.mem_singleton.mp hv
    subst hvM
    -- `MofA a ω = m` ⇒ `hMequiv (P.eval r₁ ω M) = m` ⇒ `P.eval r₁ ω M = hMequiv.symm m`.
    have : S.mVar.equiv (P.eval (Regime.single S.A (S.hAbool.symm a)) ω S.M) = m := by
      simpa [MofA, POVar.cfUnder, POVar.cf, mVar, aVar] using hω
    have := congrArg S.mVar.equiv.symm this
    change P.eval (Regime.single S.A (S.hAbool.symm a)) ω S.M =
      S.hMequiv.symm m
    simpa using this
  -- Apply `hC.composition`.
  have hComp :=
    hC.composition (Regime.single S.A (S.hAbool.symm a))
      (Regime.single S.M (S.hMequiv.symm m)) hdisj {S.Y} hY_notmem ω hInter
  -- Extract the `Y`-coordinate.
  have hYcoord :
      P.eval (Regime.single S.A (S.hAbool.symm a)
                |>.sqcup (Regime.single S.M (S.hMequiv.symm m)) hdisj) ω S.Y
        = P.eval (Regime.single S.A (S.hAbool.symm a)) ω S.Y := by
    simpa [POSystem.poVariable] using
      congrFun hComp ⟨S.Y, Finset.mem_singleton_self S.Y⟩
  -- Push through `yVar.equiv`.
  change S.yVar.equiv (P.eval _ ω S.Y) = S.yVar.equiv (P.eval _ ω S.Y)
  exact congrArg S.yVar.equiv hYcoord

/-! ### Finite-partition helpers

Two pure measure-theory identities used by the main proof.  Both are stated at
the level of `∫ f ∂P.μ` — no potential outcomes / causal content. -/

/-- **Partition of `∫ f` along fibers of `MofA a` (finite codomain `β`).** -/
lemma integral_eq_sum_integral_MofA (f : P.Ω → ℝ) (hf : Integrable f P.μ)
    (a : Bool) :
    ∫ ω, f ω ∂P.μ
      = ∑ m : β, ∫ ω in {ω' | S.MofA a ω' = m}, f ω ∂P.μ := by
  -- Sets `{ω | MofA a ω = m}` for `m : β` are the fibers of `MofA a`.
  set s : β → Set P.Ω := fun m => {ω | S.MofA a ω = m} with hs
  have hmeas : ∀ m, MeasurableSet (s m) := fun m =>
    S.measurable_MofA a (MeasurableSet.singleton m)
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro m₁ m₂ hne
    refine Set.disjoint_left.mpr ?_
    intro ω hω₁ hω₂
    apply hne
    simp only [Set.mem_setOf_eq, s] at hω₁ hω₂
    exact hω₁ ▸ hω₂
  have hcov : ⋃ m, s m = Set.univ := by
    refine Set.eq_univ_of_forall (fun ω => ?_)
    exact Set.mem_iUnion.mpr ⟨S.MofA a ω, rfl⟩
  have hintOn : ∀ m, IntegrableOn f (s m) P.μ := fun m => hf.integrableOn
  have hsplit :
      ∫ ω in ⋃ m, s m, f ω ∂P.μ = ∑ m : β, ∫ ω in s m, f ω ∂P.μ :=
    MeasureTheory.integral_iUnion_fintype hmeas hdisj hintOn
  rw [← setIntegral_univ, ← hcov, hsplit]

/-- **Bool-partition tower identity for `eventCondExp`.** -/
lemma integral_eq_sum_eventCondExp_aEvent (g : P.Ω → ℝ) (hg : Integrable g P.μ) :
    ∫ ω, g ω ∂P.μ
      = ∑ a' : Bool,
          eventCondExp P.μ (S.aEvent a') g * (P.μ (S.aEvent a')).toReal := by
  -- Rewrite each RHS term as a set integral.
  have hterm : ∀ a' : Bool,
      eventCondExp P.μ (S.aEvent a') g * (P.μ (S.aEvent a')).toReal
        = ∫ ω in S.aEvent a', g ω ∂P.μ := by
    intro a'
    unfold eventCondExp
    by_cases h0 : (P.μ (S.aEvent a')).toReal = 0
    · -- Both sides are 0.
      rw [h0, mul_zero]
      have hμ0 : P.μ (S.aEvent a') = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
        · exact h
        · exact absurd h (measure_ne_top _ _)
      exact (MeasureTheory.setIntegral_measure_zero g hμ0).symm
    · field_simp
  -- Swap the sum to set-integrals.
  have hsum :
      ∑ a' : Bool,
          eventCondExp P.μ (S.aEvent a') g * (P.μ (S.aEvent a')).toReal
        = ∑ a' : Bool, ∫ ω in S.aEvent a', g ω ∂P.μ := by
    exact Finset.sum_congr rfl (fun a' _ => hterm a')
  rw [hsum]
  -- Now prove `∫ g = ∑ a', ∫ in aEvent a', g`.
  have hmeas : ∀ a' : Bool, MeasurableSet (S.aEvent a') :=
    S.measurableSet_aEvent
  have hdisj : Pairwise (Function.onFun Disjoint (fun a' : Bool => S.aEvent a')) := by
    intro a₁ a₂ hne
    refine Set.disjoint_left.mpr ?_
    intro ω hω₁ hω₂
    apply hne
    show a₁ = a₂
    have h1 : S.factualA ω = a₁ := hω₁
    have h2 : S.factualA ω = a₂ := hω₂
    exact h1.symm.trans h2
  have hcov : ⋃ a' : Bool, S.aEvent a' = Set.univ := by
    refine Set.eq_univ_of_forall (fun ω => ?_)
    exact Set.mem_iUnion.mpr ⟨S.factualA ω, rfl⟩
  have hintOn : ∀ a' : Bool, IntegrableOn g (S.aEvent a') P.μ :=
    fun _ => hg.integrableOn
  have hsplit :
      ∫ ω in ⋃ a' : Bool, S.aEvent a', g ω ∂P.μ
        = ∑ a' : Bool, ∫ ω in S.aEvent a', g ω ∂P.μ :=
    MeasureTheory.integral_iUnion_fintype hmeas hdisj hintOn
  rw [← setIntegral_univ, ← hcov, hsplit]

/-! ### Main theorem -/

variable (S)

/-- **Frontdoor identification (individual regime).**  For each `a ∈ {0,1}`,
`E[Y(a)] = frontdoorTerm(a)`.

The proof follows the frontdoor identification sketch:

1. Partition by `MofA a` (finite, so `E[Y(a)] = ∑_m E[Y(a) · 1_{M(a)=m}]`).
2. On `{M(a) = m}`, composition gives `Y(a) = Y(a,m)` and full mediation gives
   `Y(a,m) = Y(1,m)`; `Exch_AM` drops `{M(a)=m}` → `μ({M(a)=m}) = pMgivenA m a`.
3. Inside each mediator level, tower over `A ∈ {0,1}` and apply `Exch_MY` + the
   on-event consistency lemma `YofAM_eq_factualY_on_aMEvent` to identify
   `E[Y(1,m) | A=a'] = E[Y | A=a', M=m]`.
4. Combine into `frontdoorTerm a`.

The drop-of-conditioning step

    `∫ in {MofA a = m}, YofAM true m = μ({MofA a = m}).toReal · ∫ YofAM true m`

uses the joint mediator–outcome independence assumption `indep_Y_M`, which is
not derivable from `exch_AM` (`A ⊥ M(·)`) or `exch_MY` (within-arm M–Y
conditional-expectation identity) alone; under a graphical frontdoor DAG it
would be a consequence of d-separation, but in the bare PO framework it has to
be stated explicitly. -/
theorem EofY_eq_frontdoorTerm (hA : S.Assumptions) (a : Bool) :
    ∫ ω, S.YofA a ω ∂P.μ = S.frontdoorTerm a := by
  -- Shorthands.
  set mSet : β → Set P.Ω := fun m => {ω | S.MofA a ω = m} with hmSet_def
  have hmSet_meas : ∀ m, MeasurableSet (mSet m) := fun m =>
    S.measurable_MofA a (MeasurableSet.singleton m)
  have hpA_ne_top : P.μ (S.aEvent a) ≠ ⊤ := measure_ne_top _ _
  have hpA_ne_zero : P.μ (S.aEvent a) ≠ 0 := (hA.posA a).ne'
  have hpA_toReal_pos : 0 < (P.μ (S.aEvent a)).toReal := by
    rw [ENNReal.toReal_pos_iff]; exact ⟨hA.posA a, lt_top_iff_ne_top.mpr hpA_ne_top⟩
  have hpA_toReal_ne_zero : (P.μ (S.aEvent a)).toReal ≠ 0 := hpA_toReal_pos.ne'
  -- ───────────────────────────────────────────────────────────────────────────
  -- (A) Mediator-marginal identity: μ(mSet m).toReal = pMgivenA m a.
  -- ───────────────────────────────────────────────────────────────────────────
  -- (A.1) Independence: factualA ⊥ MofA a (from exch_AM component projection).
  have hInd_AMa : ProbabilityTheory.IndepFun S.factualA (S.MofA a) P.μ := by
    cases a with
    | true => exact hA.exch_AM.component (0 : Fin 2)
    | false => exact hA.exch_AM.component (1 : Fin 2)
  -- (A.2) Independence on preimage sets: μ(aEvent a ∩ mSet m) = μ(aEvent a) * μ(mSet m).
  have hIndepMeas : ∀ m,
      P.μ (S.aEvent a ∩ mSet m) = P.μ (S.aEvent a) * P.μ (mSet m) := by
    intro m
    have h := hInd_AMa.measure_inter_preimage_eq_mul
      (s := {a}) (t := {m}) (measurableSet_singleton _) (measurableSet_singleton _)
    -- `aEvent a = factualA ⁻¹' {a}` and `mSet m = MofA a ⁻¹' {m}` both by rfl.
    exact h
  -- (A.3) Consistency set identity: aEvent a ∩ mSet m = aEvent a ∩ mEvent m.
  have hConsist_set :
      ∀ m, S.aEvent a ∩ mSet m = S.aEvent a ∩ S.mEvent m := by
    intro m
    ext ω
    refine ⟨?_, ?_⟩
    · rintro ⟨hA_ω, hMofA_ω⟩
      refine ⟨hA_ω, ?_⟩
      have h_eq := MofA_eq_factualM_on_aEvent hA.consistency a hA_ω
      change S.factualM ω = m
      rw [← h_eq]; exact hMofA_ω
    · rintro ⟨hA_ω, hM_ω⟩
      refine ⟨hA_ω, ?_⟩
      have h_eq := MofA_eq_factualM_on_aEvent hA.consistency a hA_ω
      change S.MofA a ω = m
      rw [h_eq]; exact hM_ω
  -- (A.4) indM m equals set indicator of mEvent m.
  have hIndM : ∀ m, S.mVar.indicator m = (S.mEvent m).indicator (fun _ => (1:ℝ)) :=
    fun m => S.mVar.indicator_eq_event_indicator m
  -- (A.5) Evaluate pMgivenA m a in closed form.
  have hpM_val : ∀ m,
      S.pMgivenA m a =
        (P.μ (S.aEvent a ∩ S.mEvent m)).toReal / (P.μ (S.aEvent a)).toReal := by
    intro m
    unfold pMgivenA eventCondExp
    rw [hIndM]
    rw [MeasureTheory.setIntegral_indicator (S.measurableSet_mEvent m)]
    rw [MeasureTheory.setIntegral_one_eq_measureReal]
    rfl
  -- (A.6) Mediator-marginal identity.
  have hMarginal : ∀ m, (P.μ (mSet m)).toReal = S.pMgivenA m a := by
    intro m
    rw [hpM_val m]
    have h₁ : (P.μ (S.aEvent a ∩ mSet m)).toReal
        = (P.μ (S.aEvent a)).toReal * (P.μ (mSet m)).toReal := by
      rw [hIndepMeas m]
      exact ENNReal.toReal_mul
    have h₂ : (P.μ (S.aEvent a ∩ S.mEvent m)).toReal
        = (P.μ (S.aEvent a)).toReal * (P.μ (mSet m)).toReal := by
      rw [← hConsist_set m]; exact h₁
    rw [h₂]
    field_simp
  -- ───────────────────────────────────────────────────────────────────────────
  -- (D) Inner integral: ∫ YofAM true m = ∑ a', EYgivenAM a' m · pA a'.
  -- ───────────────────────────────────────────────────────────────────────────
  have hInner : ∀ m : β, 0 < P.μ (mSet m) →
      ∫ ω, S.YofAM true m ω ∂P.μ
        = ∑ a' : Bool, S.EYgivenAM a' m * S.pA a' := by
    intro m hm_pos
    -- Tower over Bool partition by A.
    rw [integral_eq_sum_eventCondExp_aEvent (S := S) _ (hA.integrable_YofAM true m)]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    -- Use exch_MY to pass to aEvent a' ∩ mEvent m.
    rw [← hA.exch_MY a m hm_pos a']
    -- Inside the event aEvent a' ∩ mEvent m, YofAM true m = factualY a.e.
    -- First, full mediation: YofAM true m =ᵐ[μ] YofAM a' m.
    -- Then, consistency on aEvent a' ∩ mEvent m: YofAM a' m = factualY.
    have hYeq : ∀ ω ∈ S.aEvent a' ∩ S.mEvent m,
        S.YofAM a' m ω = S.factualY ω :=
      fun ω hω => YofAM_eq_factualY_on_aMEvent hA.consistency a' m hω
    -- eventCondExp (aEvent a' ∩ mEvent m) (YofAM true m)
    --   = eventCondExp (aEvent a' ∩ mEvent m) (YofAM a' m)  [full mediation a.e.]
    --   = eventCondExp (aEvent a' ∩ mEvent m) factualY      [consistency on event]
    have hcongr_ae :
        eventCondExp P.μ (S.aEvent a' ∩ S.mEvent m) (S.YofAM true m)
          = eventCondExp P.μ (S.aEvent a' ∩ S.mEvent m) (S.YofAM a' m) := by
      unfold eventCondExp
      congr 1
      refine MeasureTheory.integral_congr_ae ?_
      exact (Filter.EventuallyEq.filter_mono (hA.fullMediation true a' m)
              MeasureTheory.ae_restrict_le)
    have hcongr_event :
        eventCondExp P.μ (S.aEvent a' ∩ S.mEvent m) (S.YofAM a' m)
          = eventCondExp P.μ (S.aEvent a' ∩ S.mEvent m) S.factualY := by
      unfold eventCondExp
      congr 1
      refine MeasureTheory.setIntegral_congr_fun
        ((S.measurableSet_aEvent a').inter (S.measurableSet_mEvent m)) ?_
      exact hYeq
    rw [hcongr_ae, hcongr_event]
    -- Now the goal is EYgivenAM a' m * pA a' = eventCondExp ... factualY * μ(aEvent a').toReal.
    unfold EYgivenAM pA
    ring
  -- ───────────────────────────────────────────────────────────────────────────
  -- (B,C) ∫ YofA a = ∑ m, (∫ YofAM true m) · μ(mSet m).toReal.
  -- Uses composition + full mediation on the slice {MofA a = m}, and drop of
  -- conditioning from exch_AM.
  -- ───────────────────────────────────────────────────────────────────────────
  have hOuter : ∀ m : β,
      ∫ ω in mSet m, S.YofA a ω ∂P.μ
        = (P.μ (mSet m)).toReal * ∫ ω, S.YofAM true m ω ∂P.μ := by
    intro m
    -- Step (B): on mSet m, YofA a = YofAM a m (composition), and
    -- YofAM a m =ᵐ YofAM true m (full mediation), so on mSet m,
    -- YofA a = YofAM true m a.e. (viewing full mediation as an a.e. equality
    -- of the full functions, which restricts to mSet m).
    have hB : ∫ ω in mSet m, S.YofA a ω ∂P.μ
            = ∫ ω in mSet m, S.YofAM true m ω ∂P.μ := by
      -- Use a.e. equality on mSet m: YofA a =ᵐ[μ.restrict (mSet m)] YofAM true m.
      refine MeasureTheory.integral_congr_ae ?_
      -- On mSet m (a pointwise event): YofA a = YofAM a m.
      -- Off mSet m we need nothing, but we produce a restrict-a.e. statement via
      -- indicator/filter reasoning. Simplest: combine pointwise composition
      -- identity (on mSet m) with a.e. full mediation, restricted.
      have h_comp_on : ∀ ω ∈ mSet m, S.YofA a ω = S.YofAM a m ω := by
        intro ω hω
        exact (YofAM_eq_YofA_on_MofA_event hA.consistency a m hω).symm
      -- YofAM a m =ᵐ[μ] YofAM true m.
      have h_fm := (hA.fullMediation a true m).symm  -- YofAM true m =ᵐ YofAM a m
      -- Combine: for almost every ω in mSet m, YofA a ω = YofAM true m ω.
      have h_fm_restrict : S.YofAM a m =ᵐ[P.μ.restrict (mSet m)] S.YofAM true m := by
        exact (hA.fullMediation a true m).filter_mono MeasureTheory.ae_restrict_le
      -- YofA a =ᵐ[restrict] YofAM a m (pointwise on mSet m ⇒ a.e. on restrict).
      have h_comp_ae :
          S.YofA a =ᵐ[P.μ.restrict (mSet m)] S.YofAM a m := by
        rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (hmSet_meas m)]
        filter_upwards with ω hω using h_comp_on ω hω
      exact h_comp_ae.trans h_fm_restrict
    rw [hB]
    -- Step (C): drop-of-conditioning for YofAM true m using indep_Y_M.
    -- mSet m = (MofA a) ⁻¹' {m}, so IndepFun gives the preimage integral identity.
    have hdrop :
        ∫ ω in (S.MofA a) ⁻¹' {m}, id (S.YofAM true m ω) ∂P.μ
          = (P.μ ((S.MofA a) ⁻¹' {m})).toReal
              * ∫ ω, id (S.YofAM true m ω) ∂P.μ :=
      (hA.indep_Y_M a m).integral_restrict_preimage_eq_mul
        (S.measurable_MofA a) (S.measurable_YofAM true m)
        (measurableSet_singleton m) measurable_id
    simpa [mSet, id] using hdrop
  -- ───────────────────────────────────────────────────────────────────────────
  -- Main chain: combine (i) partition, (B,C) drop + marginal, (D) inner.
  -- ───────────────────────────────────────────────────────────────────────────
  rw [integral_eq_sum_integral_MofA (S := S) _ (hA.integrable_YofA a) a]
  -- Now the goal is ∑ m, ∫ in {MofA a = m}, YofA a = frontdoorTerm a.
  -- Rewrite the LHS sum using hOuter, hMarginal, hInner.
  have hStep : ∀ m : β,
      ∫ ω in mSet m, S.YofA a ω ∂P.μ
        = S.pMgivenA m a * ∑ a' : Bool, S.EYgivenAM a' m * S.pA a' := by
    intro m
    by_cases hm_pos : 0 < P.μ (mSet m)
    · rw [hOuter m, hInner m hm_pos, hMarginal m]
    · have hm_zero : P.μ (mSet m) = 0 := le_antisymm (not_lt.mp hm_pos) bot_le
      rw [hOuter m, ← hMarginal m, hm_zero]
      simp
  have hLHS :
      ∑ m : β, ∫ ω in mSet m, S.YofA a ω ∂P.μ
        = ∑ m : β, S.pMgivenA m a * ∑ a' : Bool, S.EYgivenAM a' m * S.pA a' :=
    Finset.sum_congr rfl (fun m _ => hStep m)
  rw [hLHS]
  -- Remaining: ∑ m, pMgivenA m a * (∑ a', EYgivenAM a' m * pA a') = frontdoorTerm a.
  unfold frontdoorTerm
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- pMgivenA m a * (EYgivenAM true m * pA true + EYgivenAM false m * pA false)
  -- = (EYgivenAM true m * pA true + EYgivenAM false m * pA false) * pMgivenA m a.
  rw [Fintype.sum_bool]
  ring

/-- **Frontdoor identification of the ATE.**  Immediate corollary of
`EofY_eq_frontdoorTerm` at `a = true, false` by linearity. -/
theorem ate_frontdoor (hA : S.Assumptions) : S.ATE = S.frontdoorATE := by
  unfold ATE frontdoorATE
  rw [integral_sub (hA.integrable_YofA true) (hA.integrable_YofA false)]
  rw [EofY_eq_frontdoorTerm S hA true, EofY_eq_frontdoorTerm S hA false]

end POFrontdoorSystem

end PO
end Causalean
