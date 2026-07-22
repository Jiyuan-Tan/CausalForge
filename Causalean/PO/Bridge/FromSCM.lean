/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Potential Outcome System Induced by a gSCM

Implements `def:po-from-scm` from Basic Concepts.tex (lines 1186–1263):
given a gSCM `M : SCM N Ω` and a background assignment `s : SCM.FixedValues M`,
constructs the potential outcome system `PO(M; s) : POSystem` on all observed
random nodes of `M`.

Concretely, for a regime `r = (X, x)`, the induced world-eval map at a latent
draw `ℓ : SCM.LatentValues M` is

    ω ↦ π_V (Eval^{M}_r (s, ℓ))
        = π_V ∘ (M.fixSet X …).evalMap (s ⊔ x) ℓ.

The bridge uses `M.fixSet` on the regime targets whose fixed counterparts are
not already fixed in `M`, combines the background `s` with the corresponding
regime assignments, then applies `evalMap` and projects onto all observed
random nodes.

## References

* Basic Concepts.tex, def:po-from-scm, rem:po-induced, prop:po-consistency,
  rem:po-vs-do (lines 1186–1263).
-/

import Causalean.PO.Assumptions.Consistency
import Causalean.SCM.Model.Evaluation
import Causalean.SCM.Model.InterventionSet
import Causalean.SCM.Model.CounterfactualLemmas
import Causalean.SCM.Model.EquivKernel

/-! # Potential Outcome Systems from Structural Models

This file constructs the potential-outcome system induced by a generalized
structural causal model and a background assignment of fixed variables. The
construction keeps one potential-outcome variable for every observed random
node, translates structurally eligible regime targets into interventions,
evaluates the intervened model at latent draws, and projects back to the
observed variables.

The construction is organized around `ObsIdx`, `regimeTargetN`,
`combinedFixed`, `inducedEval`, and `POSystem.ofSCM`.  The theorem
`POSystem.ofSCM_consistency` proves that the induced potential-outcome system
satisfies factual and composition consistency by reducing those clauses to the
SCM counterfactual consistency lemmas. -/

namespace Causalean
namespace PO

open MeasureTheory

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- § 1. Observed-node index type for the induced PO system
-- ============================================================

/-- The observed-node index set of the induced potential-outcome system consists
of all random observed nodes of the structural model.

The PO system induced by a gSCM has one variable per observed random node,
including nodes whose fixed counterpart is already part of the structural
model's background fixed set. Implements def:po-from-scm. -/
abbrev ObsIdx (M : Causalean.SCM N Ω) :=
  {v : SWIGNode N // v ∈ M.observed}

/-- Every observed random node is an index of the potential-outcome system induced by an SCM. -/
def obsIdx_mk_random (M : Causalean.SCM N Ω) (n : N)
    (h : SWIGNode.random n ∈ M.observed) : ObsIdx M :=
  ⟨SWIGNode.random n, h⟩

/-- The value space of an observed-node index in the induced potential-outcome
system is the structural-model value space attached to that observed node.

Each observed node carries its SWIG value space `swigΩ Ω v.val`. Implements
def:po-from-scm. -/
abbrev obsValue (M : Causalean.SCM N Ω) (v : ObsIdx M) : Type uΩ := swigΩ Ω v.val

/-- The observed-node indices of an induced potential-outcome system form a finite type. -/
instance instFintypeObsIdx (M : Causalean.SCM N Ω) : Fintype (ObsIdx M) :=
  inferInstance

/-- Observed-node indices of an induced potential-outcome system have decidable equality. -/
instance instDecidableEqObsIdx (M : Causalean.SCM N Ω) : DecidableEq (ObsIdx M) :=
  inferInstance

/-- The value space attached to each observed-node index has the measurable
structure inherited from the structural model. -/
instance instMeasurableObsValue (M : Causalean.SCM N Ω) (v : ObsIdx M) :
    MeasurableSpace (obsValue M v) :=
  inferInstanceAs (MeasurableSpace (swigΩ Ω v.val))

-- ============================================================
-- § 2. Regime → do-set translation (graph-level)
-- ============================================================

/-- The structural variable names targeted by a potential-outcome regime are the
underlying names of the regime targets whose fixed counterparts are not already
fixed in the structural model.

Observed nodes of `M` are all of the form `.random n`, so we read the `N`-name
via `M.observed_is_random`. Helper for def:po-from-scm. -/
noncomputable def regimeTargetN
    (M : Causalean.SCM N Ω) (r : Regime (ObsIdx M) (obsValue M)) : Finset N :=
  (r.target.filter (fun v => SWIGNode.fixed
    (Classical.choose (M.observed_is_random v.val v.property)) ∉ M.fixed)).image (fun v =>
    -- v : ObsIdx M, i.e. v.val : SWIGNode N with v.property : v.val ∈ M.observed.
    -- Extract the `N`-name via classical choice on `observed_is_random`.
    Classical.choose (M.observed_is_random v.val v.property))

/-- `fixSet`-obligation for `regimeTargetN`: every target `D` has `.random D ∈ M.observed`. -/
lemma regimeTargetN_obs
    (M : Causalean.SCM N Ω) (r : Regime (ObsIdx M) (obsValue M)) :
    ∀ D ∈ regimeTargetN M r, SWIGNode.random D ∈ M.observed := by
  intro D hD
  simp only [regimeTargetN, Finset.mem_image] at hD
  rcases hD with ⟨v, _, rfl⟩
  have hspec := Classical.choose_spec (M.observed_is_random v.val v.property)
  rw [← hspec]
  exact v.property

/-- `fixSet`-obligation: `.fixed D ∉ M.fixed` for every structurally eligible
    regime target `D`. The target-name translation filters out observed
    variables whose fixed counterpart is already in `M.fixed`. -/
lemma regimeTargetN_notFixed
    (M : Causalean.SCM N Ω) (r : Regime (ObsIdx M) (obsValue M)) :
    ∀ D ∈ regimeTargetN M r, SWIGNode.fixed D ∉ M.fixed := by
  intro D hD
  simp only [regimeTargetN, Finset.mem_image] at hD
  rcases hD with ⟨v, hv, rfl⟩
  exact (Finset.mem_filter.mp hv).2

-- ============================================================
-- § 3. Combined background + regime assignment on the intervened fixed set
-- ============================================================

/-- The N-name extracted from an `ObsIdx M` element via `observed_is_random`. -/
private noncomputable def obsName (M : Causalean.SCM N Ω) (v : ObsIdx M) : N :=
  Classical.choose (M.observed_is_random v.val v.property)

private lemma obsName_spec (M : Causalean.SCM N Ω) (v : ObsIdx M) :
    v.val = SWIGNode.random (obsName M v) :=
  Classical.choose_spec (M.observed_is_random v.val v.property)

/-- Existence helper for `combinedFixed`: when `v.val ∉ M.fixed`, there is
    a `v' ∈ r.target` with `.fixed (obsName M v') = v.val`. -/
private lemma combinedFixed_exists
    (M : Causalean.SCM N Ω) (r : Regime (ObsIdx M) (obsValue M))
    (v : {x // x ∈ M.fixed ∪ (regimeTargetN M r).image SWIGNode.fixed})
    (hMfix : v.val ∉ M.fixed) :
    ∃ v' : ObsIdx M, v' ∈ r.target ∧ SWIGNode.fixed (obsName M v') = v.val := by
  have hImg : v.val ∈ (regimeTargetN M r).image SWIGNode.fixed :=
    (Finset.mem_union.mp v.property).resolve_left hMfix
  rcases Finset.mem_image.mp hImg with ⟨D, hD, hfixEq⟩
  rcases Finset.mem_image.mp hD with ⟨v', hv'tgt, hobsEq⟩
  exact ⟨v', (Finset.mem_filter.mp hv'tgt).1, by simp [obsName, hobsEq, hfixEq]⟩

/-- The combined fixed-variable assignment feeds the original background values
and the regime's intervention values into the intervened structural model.

Combined fixed assignment `s ⊔ x` for the post-intervention SCM
`M.fixSet (regimeTargetN r) _ _`. Reads `M.fixed` coordinates from `s`, new
intervention coordinates from `r.assign` via a single `Classical.choose`
pinned by uniqueness (see `combinedFixed_new`). -/
noncomputable def combinedFixed
    (M : Causalean.SCM N Ω) (s : SCM.FixedValues M)
    (r : Regime (ObsIdx M) (obsValue M)) :
    SCM.FixedValues
      (M.fixSet (regimeTargetN M r) (regimeTargetN_obs M r) (regimeTargetN_notFixed M r)) :=
  fun v =>
    if hMfix : v.val ∈ M.fixed then
      s ⟨v.val, hMfix⟩
    else
      let v' := Classical.choose (combinedFixed_exists M r v hMfix)
      let hv'spec := Classical.choose_spec (combinedFixed_exists M r v hMfix)
      -- Cast `r.assign v' hv'spec.1 : obsValue M v' = swigΩ Ω v'.val` into `swigΩ Ω v.val`.
      -- Both reduce to `Ω (obsName' M v')` via `obsName'_spec` and `hv'spec.2`.
      cast (show obsValue M v' = swigΩ Ω v.val by
              change swigΩ Ω v'.val = swigΩ Ω v.val
              rw [obsName_spec M v', ← hv'spec.2])
        (r.assign v' hv'spec.1)

-- ============================================================
-- § 4. The induced world-eval map (def:po-from-scm)
-- ============================================================

/-- The induced joint evaluation map assigns values to all observed-node indices
by evaluating the intervened structural model at a background assignment, a
potential-outcome regime, and a latent draw.

Induced world-eval map: `ω ↦ π_V (Eval^M_r (s, ω))`. Builds the intervened SCM
`M.fixSet (regimeTargetN r)`, forms the combined fixed assignment `s ⊔ x`,
evaluates at the latent draw `ℓ`, and projects onto each observed random node
using its membership in the intervened model's random variables.
Implements def:po-from-scm. -/
noncomputable def inducedEval
    (M : Causalean.SCM N Ω) (s : SCM.FixedValues M)
    (r : Regime (ObsIdx M) (obsValue M))
    (ℓ : SCM.LatentValues M) : ∀ v : ObsIdx M, obsValue M v :=
  let M' := M.fixSet (regimeTargetN M r) (regimeTargetN_obs M r) (regimeTargetN_notFixed M r)
  fun v =>
    -- v.val ∈ M.observed = M'.observed, so v.val ∈ M'.randomVars
    let hmem : v.val ∈ M'.randomVars := by
      simp [SCM.randomVars, v.property]
    M'.evalMap (combinedFixed M s r) ℓ ⟨v.val, hmem⟩

/-- The induced joint evaluation map of a structural model is measurable in the latent draw. -/
lemma inducedEval_measurable (M : Causalean.SCM N Ω)
    (s : SCM.FixedValues M) (r : Regime (ObsIdx M) (obsValue M)) :
    Measurable (inducedEval M s r) := by
  let M' := M.fixSet (regimeTargetN M r) (regimeTargetN_obs M r) (regimeTargetN_notFixed M r)
  refine measurable_pi_lambda _ (fun v => ?_)
  have h : Measurable (fun ℓ : SCM.LatentValues M =>
      M'.evalMap (combinedFixed M s r) ℓ) := by
    have hmeas := M'.evalMap_measurable
    have : Measurable (fun ℓ : SCM.LatentValues M =>
        Function.uncurry M'.evalMap (combinedFixed M s r, ℓ)) :=
      hmeas.comp (Measurable.prod measurable_const measurable_id')
    simpa [Function.uncurry] using this
  exact (measurable_pi_apply ⟨v.val, by simp [SCM.randomVars, v.property]⟩).comp h

-- ============================================================
-- § 5. The induced PO system `PO(M; s)` — def:po-from-scm
-- ============================================================

/-- A structural model and a background assignment induce a potential-outcome
system whose variables are all observed random nodes of the model.

Potential outcome system induced by a gSCM `M` and background assignment `s`.
The system has one variable for every observed random node of `M`; when a regime
targets a node whose fixed counterpart is already fixed in `M`, that target is
not passed again to the structural `fixSet`. `PO(M; s)` of def:po-from-scm. -/
noncomputable def POSystem.ofSCM
    (M : Causalean.SCM N Ω) (s : SCM.FixedValues M) :
    Causalean.PO.POSystem where
  V := ObsIdx M
  X := obsValue M
  Ω := SCM.LatentValues M
  μ := M.latentProduct
  eval := fun r ℓ => inducedEval M s r ℓ
  measurable_eval := fun r => inducedEval_measurable M s r

-- ============================================================
-- § 6. Bridge helpers: combinedFixed properties
-- ============================================================

/-- On original fixed coordinates, `combinedFixed` agrees with `s`. -/
lemma combinedFixed_old (M : Causalean.SCM N Ω) (s : SCM.FixedValues M)
    (r : Regime (ObsIdx M) (obsValue M))
    (v : SWIGNode N) (hv : v ∈ M.fixed) :
    combinedFixed M s r ⟨v, Finset.mem_union_left _ hv⟩ = s ⟨v, hv⟩ := by
  simp only [combinedFixed, dif_pos hv]

/-- `regimeTargetN M r` is the image of the structurally eligible regime targets under `obsName M`. -/
lemma regimeTargetN_eq_image_obsName (M : Causalean.SCM N Ω)
    (r : Regime (ObsIdx M) (obsValue M)) :
    regimeTargetN M r =
      (r.target.filter (fun v => SWIGNode.fixed (obsName M v) ∉ M.fixed)).image (obsName M) := rfl

/-- Every structural variable name targeted by a translated regime comes from
an observed-node index whose observed node is the corresponding random node. -/
lemma regimeTargetN_mem_val (M : Causalean.SCM N Ω)
    (r : Regime (ObsIdx M) (obsValue M)) (D : N) (hD : D ∈ regimeTargetN M r) :
    ∃ v' : ObsIdx M, v' ∈ r.target ∧ v'.val = SWIGNode.random D := by
  simp only [regimeTargetN, Finset.mem_image] at hD
  rcases hD with ⟨v', hv'tgt, hDeq⟩
  exact ⟨v', (Finset.mem_filter.mp hv'tgt).1, hDeq ▸ obsName_spec M v'⟩

/-- Two elements of `ObsIdx M` with the same `.val` are equal (injectivity of the coercion). -/
lemma obsIdx_val_injective {M : Causalean.SCM N Ω} {v w : ObsIdx M} (h : v.val = w.val) : v = w :=
  Subtype.ext h

/-- `obsName M` is injective: `obsName v = obsName w → v = w`. -/
lemma obsName_injective (M : Causalean.SCM N Ω) : Function.Injective (obsName M) :=
  fun v w hvw => obsIdx_val_injective (by rw [obsName_spec M v, obsName_spec M w, hvw])

/-- `Regime.sqcup` agrees with `r₁` on `r₁.target`. -/
lemma sqcup_assign_left {V : Type*} [DecidableEq V] [Fintype V]
    {X : V → Type*} [∀ v, MeasurableSpace (X v)]
    (r₁ r₂ : Regime V X) (h : r₁.Disjoint r₂)
    (v : V) (hv : v ∈ r₁.target) :
    (r₁.sqcup r₂ h).assign v (Finset.mem_union_left _ hv) = r₁.assign v hv := by
  simp [Regime.sqcup, hv]

/-- `Regime.sqcup` agrees with `r₂` on `r₂.target`. -/
lemma sqcup_assign_right {V : Type*} [DecidableEq V] [Fintype V]
    {X : V → Type*} [∀ v, MeasurableSpace (X v)]
    (r₁ r₂ : Regime V X) (h : r₁.Disjoint r₂)
    (v : V) (hv : v ∈ r₂.target) :
    (r₁.sqcup r₂ h).assign v (Finset.mem_union_right _ hv) = r₂.assign v hv := by
  have h1 : v ∉ r₁.target := fun hv₁ => Finset.disjoint_left.mp h hv₁ hv
  simp [Regime.sqcup, h1]

/-- On new intervention coordinates, `combinedFixed` at `⟨.fixed D, _⟩`
    equals `r.assign v' hv'tgt`, both at type `Ω D`.  The internal
    `Classical.choose` witness is identified with `v'` by uniqueness
    (both have `.val = .random D`); the cast chain collapses via
    `cast_heq` + `proof_irrel_heq`. -/
lemma combinedFixed_new (M : Causalean.SCM N Ω) (s : SCM.FixedValues M)
    (r : Regime (ObsIdx M) (obsValue M))
    (v' : ObsIdx M) (hv'tgt : v' ∈ r.target)
    (D : N) (hD : D ∈ regimeTargetN M r) (hDval : v'.val = SWIGNode.random D) :
    (combinedFixed M s r ⟨SWIGNode.fixed D,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩ : Ω D) =
    cast (congrArg (swigΩ Ω) hDval) (r.assign v' hv'tgt) := by
  have hFD_notFix : SWIGNode.fixed D ∉ M.fixed := regimeTargetN_notFixed M r D hD
  unfold combinedFixed
  rw [dif_neg hFD_notFix]
  set hExist := combinedFixed_exists M r ⟨SWIGNode.fixed D, _⟩ hFD_notFix with hE_def
  have hChosen : Classical.choose hExist = v' := by
    have hspec := Classical.choose_spec hExist
    apply obsIdx_val_injective
    have h_obsname : obsName M (Classical.choose hExist) = D := by
      have := hspec.2; injection this
    rw [obsName_spec M (Classical.choose hExist), h_obsname, hDval]
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  refine HEq.trans ?_ (cast_heq _ _).symm
  congr 1
  exact proof_irrel_heq _ _

/-- `regimeTargetN M Regime.empty = ∅`. -/
@[simp] lemma regimeTargetN_empty (M : Causalean.SCM N Ω) :
    regimeTargetN M (Regime.empty (V := ObsIdx M) (X := obsValue M)) = ∅ := by
  simp [regimeTargetN, Regime.empty]

/-- `inducedEval` at `Regime.empty` equals `M.evalMap s` at the same latent. -/
lemma inducedEval_empty_eq_evalMap (M : Causalean.SCM N Ω) (s : SCM.FixedValues M)
    (ℓ : SCM.LatentValues M) (v : ObsIdx M) :
    inducedEval M s Regime.empty ℓ v =
    M.evalMap s ℓ ⟨v.val, Finset.mem_union_left _ v.property⟩ := by
  -- `inducedEval M s Regime.empty ℓ v = (M.fixSet ∅ ...).evalMap (combinedFixed M s Regime.empty) ℓ ⟨v.val, _⟩`
  -- Use `evalMap_eq_of_equiv (fixSet_empty_equiv M ...)`.
  unfold inducedEval
  simp only [regimeTargetN_empty]
  -- RHS of inducedEval: `(M.fixSet ∅ ...).evalMap (combinedFixed M s Regime.empty) ℓ ⟨v.val, _⟩`
  apply SCM.evalMap_eq_of_equiv (SCM.fixSet_empty_equiv M _ _)
  · -- Fixed coords agree: combinedFixed at M.fixed = s
    intro d hd₁ hd₂
    -- `(M.fixSet ∅).fixed = M.fixed ∪ ∅ = M.fixed` (by rfl since ∅.image = ∅)
    simp only [SCM.fixSet_fixed, Finset.image_empty, Finset.union_empty] at hd₁
    exact combinedFixed_old M s Regime.empty d hd₁
  · -- Latent coords: `(M.fixSet ∅).unobserved = M.unobserved` (by rfl)
    intro u hu₁ hu₂
    rfl

-- ============================================================
-- § 7. Consistency of the induced system (prop:po-consistency)
-- ============================================================

/-- Transport `evalMap` of `M.fixSet` across set equality `X₁ = X₂`. -/
private lemma evalMap_fixSet_transport
    (M : Causalean.SCM N Ω)
    {X₁ X₂ : Finset N} (hX : X₁ = X₂)
    (hO₁ : ∀ D ∈ X₁, SWIGNode.random D ∈ M.observed)
    (hF₁ : ∀ D ∈ X₁, SWIGNode.fixed D ∉ M.fixed)
    (hO₂ : ∀ D ∈ X₂, SWIGNode.random D ∈ M.observed)
    (hF₂ : ∀ D ∈ X₂, SWIGNode.fixed D ∉ M.fixed)
    (s₁ : (M.fixSet X₁ hO₁ hF₁).FixedValues)
    (s₂ : (M.fixSet X₂ hO₂ hF₂).FixedValues)
    (hs : ∀ (v : SWIGNode N) (hv₁ : v ∈ (M.fixSet X₁ hO₁ hF₁).fixed)
            (hv₂ : v ∈ (M.fixSet X₂ hO₂ hF₂).fixed),
          s₁ ⟨v, hv₁⟩ = s₂ ⟨v, hv₂⟩)
    (ℓ : SCM.LatentValues M)
    (v : SWIGNode N)
    (hv₁ : v ∈ (M.fixSet X₁ hO₁ hF₁).randomVars)
    (hv₂ : v ∈ (M.fixSet X₂ hO₂ hF₂).randomVars) :
    (M.fixSet X₁ hO₁ hF₁).evalMap s₁ ℓ ⟨v, hv₁⟩ =
    (M.fixSet X₂ hO₂ hF₂).evalMap s₂ ℓ ⟨v, hv₂⟩ := by
  subst hX
  exact SCM.evalMap_eq_of_equiv (SCM.Equiv.refl _) s₁ ℓ s₂ ℓ
    (fun {d} hd₁ hd₂ => hs d hd₁ hd₂) (fun {_} _ _ => rfl) hv₁ hv₂

/-- The potential-outcome system induced by an SCM satisfies consistency.

The proof reduces factual consistency to the SCM factual-counterfactual
consistency lemma and composition consistency to the SCM commuting-intervention
lemma. -/
theorem POSystem.ofSCM_consistency
    (M : Causalean.SCM N Ω) (s : SCM.FixedValues M) :
    (POSystem.ofSCM M s).Consistency where
  -- ---------------------------------------------------------------
  -- Factual consistency
  -- ---------------------------------------------------------------
  factual := by
    intro r Y hY_disj ℓ hFactual
    funext v
    simp only [POSystem.poVariable, POSystem.ofSCM]
    change inducedEval M s r ℓ v.val = inducedEval M s Regime.empty ℓ v.val
    rw [inducedEval_empty_eq_evalMap M s ℓ v.val]
    -- Clear the let-binding from inducedEval's `hmem`
    simp only [inducedEval]
    -- Goal: (M.fixSet (regimeTargetN M r) ...).evalMap (combinedFixed M s r) ℓ ⟨v.val.val, _⟩
    --     = M.evalMap s ℓ ⟨v.val.val, _⟩
    exact SCM.evalMap_fixSet_factual_eq M (regimeTargetN M r)
        (regimeTargetN_obs M r) (regimeTargetN_notFixed M r)
        s ℓ (combinedFixed M s r)
      -- hOld: combinedFixed agrees with s on M.fixed
      (fun w hw => combinedFixed_old M s r w hw)
      -- hNew: for D ∈ regimeTargetN M r,
      --   M.evalMap s ℓ ⟨.random D, _⟩ = combinedFixed M s r ⟨.fixed D, _⟩
      (fun D hD => by
        obtain ⟨v', hv'tgt, hDval⟩ := regimeTargetN_mem_val M r D hD
        have hfa := hFactual v' hv'tgt
        simp only [POSystem.ofSCM] at hfa
        change inducedEval M s Regime.empty ℓ v' = r.assign v' hv'tgt at hfa
        rw [inducedEval_empty_eq_evalMap M s ℓ v'] at hfa
        -- hfa : M.evalMap s ℓ ⟨v'.val, _⟩ = r.assign v' hv'tgt : swigΩ Ω v'.val
        rw [combinedFixed_new M s r v' hv'tgt D hD hDval]
        obtain ⟨v'val, v'prop⟩ := v'
        cases hDval
        exact hfa)
      -- hv_disj: v.val.val ≠ .random D for all D ∈ regimeTargetN M r
      ⟨v.val.val, v.val.property⟩
      (fun D hD heq => by
        obtain ⟨v', hv'tgt, hv'val⟩ := regimeTargetN_mem_val M r D hD
        have hvv' : v.val = v' := obsIdx_val_injective (heq.trans hv'val.symm)
        exact Finset.disjoint_left.mp hY_disj v.property (hvv' ▸ hv'tgt))
  -- ---------------------------------------------------------------
  -- Composition consistency
  -- ---------------------------------------------------------------
  composition := by
    intro r₁ r₂ h Y hY_disj ℓ hIntermediate
    funext v
    simp only [POSystem.poVariable, POSystem.ofSCM]
    unfold inducedEval
    -- Sets and proof obligations for the union fixSet
    set X₁ := regimeTargetN M r₁ with hX₁_def
    set X₂ := regimeTargetN M r₂ with hX₂_def
    have hUnion : regimeTargetN M (r₁.sqcup r₂ h) = X₁ ∪ X₂ := by
      simp only [hX₁_def, hX₂_def, regimeTargetN, Regime.sqcup_target]
      simpa [Finset.image_union] using
        congrArg (Finset.image (fun v : ObsIdx M =>
          Classical.choose (M.observed_is_random v.val v.property)))
          (Finset.filter_union (s₁ := r₁.target) (s₂ := r₂.target)
            (p := fun v : ObsIdx M =>
              SWIGNode.fixed (Classical.choose (M.observed_is_random v.val v.property)) ∉
                M.fixed))
    have hObsU : ∀ D ∈ X₁ ∪ X₂, SWIGNode.random D ∈ M.observed :=
      fun D hD => regimeTargetN_obs M (r₁.sqcup r₂ h) D (hUnion ▸ hD)
    have hFixU : ∀ D ∈ X₁ ∪ X₂, SWIGNode.fixed D ∉ M.fixed :=
      fun D hD => regimeTargetN_notFixed M (r₁.sqcup r₂ h) D (hUnion ▸ hD)
    -- sxU: combinedFixed M s (r₁.sqcup r₂ h) re-typed to live on M.fixSet (X₁ ∪ X₂)
    set sxU : SCM.FixedValues (M.fixSet (X₁ ∪ X₂) hObsU hFixU) :=
      fun w => combinedFixed M s (r₁.sqcup r₂ h) ⟨w.val, by
        have := w.property
        simp only [SCM.fixSet_fixed] at this ⊢
        rw [hUnion]; exact this⟩
    -- Transport LHS to use M.fixSet (X₁ ∪ X₂)
    change (M.fixSet (regimeTargetN M (r₁.sqcup r₂ h)) _ _).evalMap
        (combinedFixed M s (r₁.sqcup r₂ h)) ℓ ⟨v.val.val, _⟩ =
      (M.fixSet X₁ _ _).evalMap (combinedFixed M s r₁) ℓ ⟨v.val.val, _⟩
    rw [evalMap_fixSet_transport M hUnion _ _ hObsU hFixU
        (combinedFixed M s (r₁.sqcup r₂ h)) sxU
        (fun _ _ _ => rfl)]
    rotate_left
    · simp only [SCM.randomVars, SCM.fixSet_observed, SCM.fixSet_unobserved]
      exact Finset.mem_union_left _ v.val.property
    -- Disjointness of X₁ and X₂ in N
    have hDisjN : Disjoint X₁ X₂ := by
      simp only [hX₁_def, hX₂_def, regimeTargetN]
      exact Finset.disjoint_image (obsName_injective M) |>.mpr (by
        rw [Finset.disjoint_left]
        intro v hv₁ hv₂
        exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hv₁).1 (Finset.mem_filter.mp hv₂).1)
    -- Apply evalMap_fixSet_union_eq
    refine SCM.evalMap_fixSet_union_eq M X₁ X₂ hDisjN
      (regimeTargetN_obs M r₁) (regimeTargetN_notFixed M r₁)
      (regimeTargetN_obs M r₂) (regimeTargetN_notFixed M r₂)
      hObsU hFixU s ℓ (combinedFixed M s r₁) sxU
      ?_ ?_ ?_ ⟨v.val.val, v.val.property⟩ ?_
    · -- hCompat_old: sxU and combinedFixed M s r₁ both equal s on M.fixed
      intro w hw
      change combinedFixed M s (r₁.sqcup r₂ h) ⟨w, Finset.mem_union_left _ hw⟩ =
        combinedFixed M s r₁ ⟨w, Finset.mem_union_left _ hw⟩
      rw [combinedFixed_old M s (r₁.sqcup r₂ h) w hw, combinedFixed_old M s r₁ w hw]
    · -- hCompat_x₁: sxU ⟨.fixed D, _⟩ = (combinedFixed M s r₁) ⟨.fixed D, _⟩ for D ∈ X₁
      intro D hD
      -- Pick v' ∈ r₁.target with v'.val = .random D
      obtain ⟨v', hv'tgt₁, hDval⟩ := regimeTargetN_mem_val M r₁ D hD
      have hv'tgtU : v' ∈ (r₁.sqcup r₂ h).target := Finset.mem_union_left _ hv'tgt₁
      have hD_U : D ∈ regimeTargetN M (r₁.sqcup r₂ h) := hUnion ▸ Finset.mem_union_left _ hD
      change combinedFixed M s (r₁.sqcup r₂ h) ⟨SWIGNode.fixed D, _⟩ =
        combinedFixed M s r₁ ⟨SWIGNode.fixed D, _⟩
      rw [combinedFixed_new M s (r₁.sqcup r₂ h) v' hv'tgtU D hD_U hDval,
          combinedFixed_new M s r₁ v' hv'tgt₁ D hD hDval,
          sqcup_assign_left r₁ r₂ h v' hv'tgt₁]
    · -- hIntermediate: (M.fixSet X₁).evalMap (combinedFixed M s r₁) ℓ ⟨.random D, _⟩
      --              = sxU ⟨.fixed D, _⟩ for D ∈ X₂
      intro D hD
      obtain ⟨v', hv'tgt₂, hDval⟩ := regimeTargetN_mem_val M r₂ D hD
      -- v' ∉ r₁.target by disjointness
      have hv'_not₁ : v' ∉ r₁.target := fun hv₁ => Finset.disjoint_left.mp h hv₁ hv'tgt₂
      have hv'tgtU : v' ∈ (r₁.sqcup r₂ h).target := Finset.mem_union_right _ hv'tgt₂
      have hD_U : D ∈ regimeTargetN M (r₁.sqcup r₂ h) := hUnion ▸ Finset.mem_union_right _ hD
      -- Use hIntermediate from PO consistency: inducedEval M s r₁ ℓ v' = r₂.assign v' hv'tgt₂
      have hIA := hIntermediate v' hv'tgt₂
      simp only [POSystem.ofSCM] at hIA
      unfold inducedEval at hIA
      -- hIA : (M.fixSet (regimeTargetN M r₁)).evalMap (combinedFixed M s r₁) ℓ ⟨v'.val, _⟩
      --     = r₂.assign v' hv'tgt₂  (at type swigΩ Ω v'.val = Ω D)
      change (M.fixSet X₁ _ _).evalMap (combinedFixed M s r₁) ℓ ⟨SWIGNode.random D, _⟩ =
        combinedFixed M s (r₁.sqcup r₂ h) ⟨SWIGNode.fixed D, _⟩
      rw [combinedFixed_new M s (r₁.sqcup r₂ h) v' hv'tgtU D hD_U hDval]
      -- (r₁.sqcup r₂).assign v' hv'tgtU = r₂.assign v' hv'tgt₂
      rw [show (r₁.sqcup r₂ h).assign v' hv'tgtU = r₂.assign v' hv'tgt₂ from
            sqcup_assign_right r₁ r₂ h v' hv'tgt₂]
      -- Now LHS at type Ω D, RHS = cast (...) (r₂.assign v' hv'tgt₂)
      -- Use hIA and adjust via cast
      have hThis : (M.fixSet X₁ _ _).evalMap (combinedFixed M s r₁) ℓ
              ⟨v'.val, Finset.mem_union_left _ v'.property⟩ = r₂.assign v' hv'tgt₂ := hIA
      -- transport via hDval : v'.val = .random D
      obtain ⟨v'val, v'prop⟩ := v'
      cases hDval
      simpa using hThis
    · -- hv_disj: v.val.val ≠ .random D for all D ∈ X₁ ∪ X₂
      intro D hD heq
      have hD' : D ∈ regimeTargetN M (r₁.sqcup r₂ h) := hUnion ▸ hD
      obtain ⟨v', hv'tgt, hv'val⟩ := regimeTargetN_mem_val M (r₁.sqcup r₂ h) D hD'
      have hvv' : v.val = v' := obsIdx_val_injective (heq.trans hv'val.symm)
      simp only [Regime.sqcup_target] at hv'tgt
      exact Finset.disjoint_left.mp hY_disj v.property (hvv' ▸ hv'tgt)

end PO
end Causalean
