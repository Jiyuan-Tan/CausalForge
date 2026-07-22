/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.Backdoor
import Causalean.SCM.ID.Adjustment
import Causalean.SCM.ID.Toolkit.FrontdoorGraph
import Causalean.SCM.ID.GraphicalThms.QFactorIdentity
import Causalean.SCM.Model.EquivKernel
import Causalean.SCM.Do.ValuesReindex

/-!
# Frontdoor identification, a.e. in the treatment value

This file states the **frontdoor completeness / identification** result tying the
graph-level functional `SCM.frontdoorAdjustment` (defined in `SCM/ID/Adjustment.lean`)
to the true post-intervention `Y`-marginal `(M.fixSet X).obsKernel.map π_Y`, under the
three frontdoor graph clauses recorded by `SWIGGraph.frontdoorCriterion`.

It is the frontdoor analogue of `SCM/ID/Backdoor.lean`, and is stated in the same
regime-uniform a.e. style: the identity holds for `νX`-almost-every treatment value
`t` (where `νX` is the observational treatment marginal), via the version-safe joint
identity `νX ⊗ₘ Kdo = νX ⊗ₘ Kfd` (`ProbabilityTheory.Kernel.ae_eq_of_compProd_eq`).

## Mediator representation

The mediator set is a **base** node set `W : Finset N` (so that it is *intervenable*
— the frontdoor derivation routes through `do(W)`).  Wherever `frontdoorAdjustment`
expects a `Finset (SWIGNode N)` mediator it is instantiated at `W.image SWIGNode.random`.

## Proof skeleton (for the main theorem; do-calculus Rules 2 and 3)

Pearl's derivation, in three legs, mirrored at the kernel level:

* **Leg A — mediator (Rule 2, FD2).**  `P(Z | do(X)) = P(Z | X)`: the `Z`-marginal of
  the post-intervention kernel equals the observational conditional `P(Z | X = x_do)`,
  because there is no unblocked back-door path `X → Z` (the `fd_no_backdoor_XZ` clause).
  State this leg `νX`-a.e. (or in `compProd` form), never pointwise in the treatment
  slice — the pointwise conditional reads `obsCondKernel` on a `νX`-null `{X = t}`
  slice and is too strong for continuous treatment (see `SCM/ID/Backdoor.lean`).
* **Leg B — outcome (FD1 + FD3).**  Because `Z` intercepts every directed `X → Y`
  path (criterion `fd_intercept`), `P(Y | do(X), Z) = P(Y | do(Z))`; and since `X`
  is a valid back-door adjustment set for `Z → Y` (criterion `fd_backdoor_ZY`),
  `P(Y | do(Z)) = ∫_{x'} P(Y | X = x', Z) dP(x')`.  This leg is exactly
  `backdoor_completeness_ae_compProd` instantiated with treatment `:= W`,
  adjustment set `:= X.image SWIGNode.random`, outcome `:= Y`.
* **Composition.**  Chaining Leg A and Leg B reproduces the `frontdoorAdjustment`
  body `∫_z (∫_{x'} P(Y | X=x', Z=z) dP(x')) dP(Z | X=x_do)`.

The FD1 bridge is exposed as an explicit compProd substrate hypothesis, keeping
the theorem focused on assembling the frontdoor functional from Rule 2, Rule 3,
and the backdoor marginal-invariance leg rather than re-deriving disintegration
inside the final theorem.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- `frontdoorCriterion` says that the base mediator set `W` satisfies Pearl's
    frontdoor criterion for treatment variables `X` and outcome nodes `Y`: the
    mediator random nodes intercept every directed treatment-outcome path, have
    no open back-door path from treatment, admit treatment adjustment for the
    mediator-outcome effect, and are excluded from the treatment and outcome
    sets.

    Writing `Z := W.image SWIGNode.random` for the mediator's random copies, `W`
    satisfies these graph clauses relative to treatment `X` and outcome `Y` if:

    * **(FD1) Interception.**  `Z` intercepts all directed paths from `X` to `Y`:
      in the `splitMono` graph (the do(X) split, where the outgoing edges of each
      `random D`, `D ∈ X`, are carried by the root intervention copy `fixed D`, so
      `random D` is a sink), the mediator set `Z = W.image .random` d-separates `Y`
      from the intervention copies `X.image .fixed`.  Because each `fixed D` is a root
      carrying exactly `D`'s causal outgoing edges, this d-separation says exactly
      that every directed `X → Y` path (the causal effect of intervening on `X`) runs
      through the mediator `Z` — i.e. full mediation / the exclusion restriction.
      (Using `X.image .random` here would be wrong: `random X` is a sink in the split
      graph, so a d-separation against it encodes a back-door condition, not
      interception.)
    * **(FD2) No back-door `X → Z`.**  There is no unblocked back-door path from `X`
      to the mediator, i.e. `∅` is a back-door adjustment set for `(X, Z)`.  Encoded
      as the backdoor criterion of the empty adjustment set:
      `G.backdoorCriterion X hX_obs hX_fix Z ∅`.
    * **(FD3) Back-door `Z → Y` blocked by `X`.**  `X.image .random` is a valid
      back-door adjustment set for the mediator's effect on `Y`:
      `G.backdoorCriterion W hW_obs hW_fix Y (X.image SWIGNode.random)`.
    * **(FD4) Mediator exclusion.**  The mediator random nodes are disjoint from
      both the treatment random nodes and the outcome set. -/
def frontdoorCriterion
    (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hX_fix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (W : Finset N)
    (hW_obs : ∀ D ∈ W, SWIGNode.random D ∈ G.observed)
    (hW_fix : ∀ D ∈ W, SWIGNode.fixed D ∉ G.fixed)
    (Y : Finset (SWIGNode N)) : Prop :=
  -- (FD1) interception: Z = W.random intercepts all directed X → Y paths, i.e. the
  -- intervention copies `X.fixed` (carrying X's causal outgoing edges; `random X` is a
  -- sink) reach `Y` only through `Z`.
  (G.splitMono X hX_obs hX_fix).dag.dSep Y (X.image SWIGNode.fixed)
      (W.image SWIGNode.random) ∧
  -- (FD2) no back-door X → Z (∅ is a backdoor adjustment set for (X, Z)).
  G.backdoorCriterion X hX_obs hX_fix (W.image SWIGNode.random) ∅ ∧
  -- (FD3) X.random is a backdoor adjustment set for the mediator effect (W → Y).
  G.backdoorCriterion W hW_obs hW_fix Y (X.image SWIGNode.random) ∧
  -- (FD4) mediator exclusions from treatment and outcome nodes.
  Disjoint (W.image SWIGNode.random) (X.image SWIGNode.random) ∧
  Disjoint (W.image SWIGNode.random) Y

end SWIGGraph

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
-- Genuine per-node primitives; all ValuesOn-level `StandardBorelSpace`/`Nonempty` (incl.
-- `M.RandomValues`), every kernel finiteness (`obsKernel`/`jointKernel`/`doKernelY`/
-- `adjustmentKernelY`/`frontdoorKernelY`), and `CountableOrCountablyGenerated` derive from these.
variable [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]

open scoped MeasureTheory ProbabilityTheory

private lemma disjoint_base_of_disjoint_random_image
    {X W : Finset N}
    (hDisj : Disjoint (W.image SWIGNode.random) (X.image SWIGNode.random)) :
    Disjoint W X := by
  rw [Finset.disjoint_left] at hDisj ⊢
  intro d hdW hdX
  exact hDisj (Finset.mem_image.mpr ⟨d, hdW, rfl⟩)
    (Finset.mem_image.mpr ⟨d, hdX, rfl⟩)

private lemma fixSet_fixed_not_mem_of_disjoint
    (M : Causalean.SCM N Ω) (X W : Finset N)
    (hW_obs : ∀ D ∈ W, SWIGNode.random D ∈ M.observed)
    (hW_fixed : ∀ D ∈ W, SWIGNode.fixed D ∉ M.fixed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hDisj : Disjoint W X) :
    ∀ D ∈ X, SWIGNode.fixed D ∉ (M.fixSet W hW_obs hW_fixed).fixed := by
  intro D hD hmem
  rw [SCM.fixSet_fixed] at hmem
  rcases Finset.mem_union.mp hmem with hM | hWF
  · exact hX_fixed D hD hM
  · rcases Finset.mem_image.mp hWF with ⟨D0, hD0W, hEq⟩
    cases hEq
    exact (Finset.disjoint_left.mp hDisj) hD0W hD

private lemma fixSet_fixed_not_mem
    (M : Causalean.SCM N Ω) (X W : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hW_fixed : ∀ D ∈ W, SWIGNode.fixed D ∉ M.fixed)
    (hDisj : Disjoint X W) :
    ∀ D ∈ W, SWIGNode.fixed D ∉ (M.fixSet X hX_obs hX_fixed).fixed := by
  intro D hD hmem
  rw [SCM.fixSet_fixed] at hmem
  rcases Finset.mem_union.mp hmem with hM | hXF
  · exact hW_fixed D hD hM
  · rcases Finset.mem_image.mp hXF with ⟨D0, hD0X, hEq⟩
    cases hEq
    exact (Finset.disjoint_left.mp hDisj) hD0X hD

-- ============================================================
-- § 1. The frontdoor-adjustment kernel in the treatment value
-- ============================================================

/-- Frontdoor-adjustment `Y`-marginal as a kernel in the treatment value `t`, at base
    `s₀` — the frontdoor analogue of `adjustmentKernelY`.  Reindexes the graph-level
    `frontdoorAdjustment` (with mediator `Z := W.image SWIGNode.random`) along
    `fixSetExtend s₀`, so its input is the treatment value `t` rather than the full
    post-intervention slice. -/
noncomputable def frontdoorKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y W : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hW : W ⊆ M.observed)
    (s0 : M.FixedValues) :
    ProbabilityTheory.Kernel (ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
      (ValuesOn Y (swigΩ Ω)) :=
  (M.frontdoorAdjustment X hObs hFix Y W hY hW).comap
    (M.fixSetExtend X hObs hFix s0) (M.measurable_fixSetExtend X hObs hFix s0)

/-- The treatment-indexed frontdoor-adjustment `Y`-marginal kernel is finite. -/
instance instIsFiniteKernelFrontdoorKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y W : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hW : W ⊆ M.observed)
    (s0 : M.FixedValues) :
    ProbabilityTheory.IsFiniteKernel (M.frontdoorKernelY X hObs hFix Y W hY hW s0) := by
  rw [SCM.frontdoorKernelY]; infer_instance

-- ============================================================
-- § 2. Completeness, a.e. in treatment (compProd primary form)
-- ============================================================

/-- **Frontdoor Leg A (mediator).**

    The mediator law under `do(X)` agrees, in the version-safe compProd form, with
    the empty-adjustment backdoor functional.  This is `backdoor_completeness_ae_compProd`
    instantiated with outcome `Wbase.image .random` and adjustment set `∅`, using
    the FD2 clause of the frontdoor criterion. -/
private theorem frontdoor_legA_mediator
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hWr : Wbase.image SWIGNode.random ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (_hFD : M.toSWIGGraph.frontdoorCriterion X hObs hFix Wbase hWobs hWfix Y)
    (hDisj_WrXr : Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random))
    (s0 : M.FixedValues)
    (hOverlapA : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M X hObs hFix
        (∅ : Finset (SWIGNode N)) (by simpa using hXr) s)
    (hPositivityA : M.BackdoorPositivityAE X (∅ : Finset (SWIGNode N))
        (Finset.empty_subset M.observed) hXr (by simpa using hXr) s0) :
    (M.treatmentMarginal X hXr s0) ⊗ₘ
        (M.doKernelY X hObs hFix (Wbase.image SWIGNode.random) hWr s0)
      =
    (M.treatmentMarginal X hXr s0) ⊗ₘ
        (M.adjustmentKernelY X hObs hFix (Wbase.image SWIGNode.random)
          (∅ : Finset (SWIGNode N)) hWr (Finset.empty_subset M.observed) s0) := by
  exact M.backdoor_completeness_ae_compProd X hObs hFix
    (Wbase.image SWIGNode.random) (∅ : Finset (SWIGNode N))
    hWr (Finset.empty_subset M.observed) hXr (by simpa using hXr) _hFD.2.1
    hDisj_WrXr (Finset.disjoint_empty_right _) s0 hOverlapA hPositivityA

/-- **Frontdoor Leg B (outcome).**

    The outcome law under `do(Wbase)` is identified by adjusting for the
    observational treatment variables `X.image .random`.  This is
    `backdoor_completeness_ae_compProd` instantiated with treatment `Wbase`,
    outcome `Y`, and adjustment set `X.image .random`, using FD3. -/
private theorem frontdoor_legB_outcome
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hWr : Wbase.image SWIGNode.random ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (_hFD : M.toSWIGGraph.frontdoorCriterion X hObs hFix Wbase hWobs hWfix Y)
    (hDisj_YWr : Disjoint Y (Wbase.image SWIGNode.random))
    (hDisj_WrXr : Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random))
    (s0 : M.FixedValues)
    (hOverlapB : ∀ s : (M.fixSet Wbase hWobs hWfix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M Wbase hWobs hWfix
        (X.image SWIGNode.random) (Finset.union_subset hWr hXr) s)
    (hPositivityB : M.BackdoorPositivityAE Wbase (X.image SWIGNode.random)
        hXr hWr (Finset.union_subset hWr hXr) s0) :
    (M.treatmentMarginal Wbase hWr s0) ⊗ₘ (M.doKernelY Wbase hWobs hWfix Y hY s0)
      =
    (M.treatmentMarginal Wbase hWr s0) ⊗ₘ
        (M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
          hY hXr s0) := by
  exact M.backdoor_completeness_ae_compProd Wbase hWobs hWfix Y (X.image SWIGNode.random)
    hY hXr hWr (Finset.union_subset hWr hXr) _hFD.2.2.1 hDisj_YWr hDisj_WrXr
    s0 hOverlapB hPositivityB

/-- **Intervention-order swap for the `Y`-marginal.**  Two structurally
    equivalent gSCMs with `HEq`-corresponding base slices have the same
    observational `Y`-marginal.  Used to commute the two do-intervention orders
    `(do X)(do W)` and `(do W)(do X)` in the FD1 derivation. -/
private lemma obsKernel_map_proj_eq_of_equiv
    {M₁ M₂ : Causalean.SCM N Ω} (h : SCM.Equiv M₁ M₂)
    (Y : Finset (SWIGNode N))
    (hY₁ : Y ⊆ M₁.observed) (hY₂ : Y ⊆ M₂.observed)
    (s₁ : M₁.FixedValues) (s₂ : M₂.FixedValues) (hs : HEq s₁ s₂) :
    (M₁.obsKernel s₁).map (valuesProjection hY₁)
      = (M₂.obsKernel s₂).map (valuesProjection hY₂) := by
  -- Extract the `obsKernel` HEq while `h` still has its `Equiv` type.
  have hok0 : HEq M₁.obsKernel M₂.obsKernel := SCM.Equiv.heq_obsKernel h
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  rcases h.1 with ⟨_hEdge, rfl, rfl, rfl⟩
  -- After unifying `observed`/`fixed`/`unobserved`, the `FixedValues` and
  -- `ObservedValues` types coincide, so the `HEq`s collapse to `Eq`.
  have hs_eq : s₁ = s₂ := eq_of_heq hs
  subst hs_eq
  have hok := eq_of_heq hok0
  rw [hok]

private lemma obsCondKernel_congr_cc
    (M : Causalean.SCM N Ω) (Y CC₁ CC₂ : Finset (SWIGNode N))
    (hCCeq : CC₁ = CC₂)
    (hY : Y ⊆ M.observed) (hCC₁ : CC₁ ⊆ M.observed) (hCC₂ : CC₂ ⊆ M.observed)
    (s : M.FixedValues) (c₁ : ValuesOn CC₁ (swigΩ Ω)) (c₂ : ValuesOn CC₂ (swigΩ Ω))
    (hc : HEq c₁ c₂) :
    M.obsCondKernel Y CC₁ hY hCC₁ (s, c₁) = M.obsCondKernel Y CC₂ hY hCC₂ (s, c₂) := by
  subst hCCeq
  have hc' : c₁ = c₂ := eq_of_heq hc
  subst hc'
  have hp : hCC₁ = hCC₂ := Subsingleton.elim _ _
  subst hp
  rfl

private lemma valuesUnionMk_union_comm_heq
    {A B : Finset (SWIGNode N)}
    (hDisj : Disjoint A B)
    (a : ValuesOn A (swigΩ Ω)) (b : ValuesOn B (swigΩ Ω)) :
    HEq (valuesUnionMk a b : ValuesOn (A ∪ B) (swigΩ Ω))
      (valuesUnionMk b a : ValuesOn (B ∪ A) (swigΩ Ω)) :=
  -- Now a one-line corollary of the `ValuesReindex` algebra layer.
  valuesUnionMk_comm_heq hDisj a b

private lemma adjustmentKernelY_empty_eq
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wr : Finset (SWIGNode N)) (hWr : Wr ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (s0 : M.FixedValues)
    (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    M.adjustmentKernelY X hObs hFix Wr (∅ : Finset (SWIGNode N)) hWr
        (Finset.empty_subset _) s0 t
      = M.obsCondKernel Wr (X.image SWIGNode.random) hWr hXr (s0, t) := by
  let sTt := M.fixSetExtend X hObs hFix s0 t
  let zMarginalPost :
      ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
        (ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) :=
    (M.obsKernel.map (valuesProjection (Finset.empty_subset M.observed))).comap
      (M.fixSetProj X hObs hFix)
      (M.measurable_fixSetProj X hObs hFix)
  haveI : ProbabilityTheory.IsMarkovKernel (M.obsCondKernel Wr
      (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hWr
      (Finset.union_subset hXr (Finset.empty_subset M.observed))) := by
    unfold SCM.obsCondKernel
    infer_instance
  let condPost :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))
        (ValuesOn Wr (swigΩ Ω)) :=
    (M.obsCondKernel Wr
        (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hWr
        (Finset.union_subset hXr (Finset.empty_subset M.observed))).comap
      (fun p =>
        (M.fixSetProj X hObs hFix p.1,
         M.fillZrW X hObs hFix (∅ : Finset (SWIGNode N)) p.1 p.2))
      (Measurable.prodMk
        ((M.measurable_fixSetProj X hObs hFix).comp measurable_fst)
        (M.measurable_fillZrW_prod X hObs hFix (∅ : Finset (SWIGNode N))))
  haveI : ProbabilityTheory.IsSFiniteKernel zMarginalPost := by
    dsimp [zMarginalPost]
    infer_instance
  haveI : ProbabilityTheory.IsSFiniteKernel condPost := by
    dsimp [condPost]
    infer_instance
  have hcollapse : ((zMarginalPost ⊗ₖ condPost).map Prod.snd) sTt
      = condPost (sTt, (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
    rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply]
    have hz : zMarginalPost sTt =
        MeasureTheory.Measure.dirac
          (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) := by
      ext S hS
      by_cases hempty : S = ∅
      · simp [hempty]
      · have h_univ : S = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          by_contra hx
          apply hempty
          ext y
          constructor
          · intro hy
            have : y = x := Subsingleton.elim y x
            exact False.elim (hx (this ▸ hy))
          · intro hy
            simp at hy
        rw [h_univ]
        dsimp [zMarginalPost]
        rw [ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _)]
        rw [MeasureTheory.Measure.map_apply (measurable_valuesProjection _) MeasurableSet.univ]
        simp [M.obsKernel_apply_univ (M.fixSetProj X hObs hFix sTt)]
    rw [hz]
    simpa [ProbabilityTheory.Kernel.sectR] using
      (MeasureTheory.Measure.dirac_bind
        (a := (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
        (f := condPost.sectR sTt) (hf := by fun_prop))
  have hadj : M.adjustmentKernelY X hObs hFix Wr (∅ : Finset (SWIGNode N)) hWr
        (Finset.empty_subset _) s0 t
      = ((zMarginalPost ⊗ₖ condPost).map Prod.snd) sTt := by
    rw [SCM.adjustmentKernelY, ProbabilityTheory.Kernel.comap_apply]
    change M.backdoorAdjustment X hObs hFix Wr (∅ : Finset (SWIGNode N)) hWr
        (Finset.empty_subset _) sTt = ((zMarginalPost ⊗ₖ condPost).map Prod.snd) sTt
    rw [SCM.backdoorAdjustment]
  rw [hadj, hcollapse]
  have hcond : condPost
      (sTt, (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
      = M.obsCondKernel Wr
          (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hWr
          (Finset.union_subset hXr (Finset.empty_subset M.observed))
          (s0, valuesUnionMk t
            (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
    simp [condPost, sTt, SCM.fixSetProj_fixSetExtend,
      SCM.fillZrW_fixSetExtend]
  rw [hcond]
  apply obsCondKernel_congr_cc M Wr
    (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
    (X.image SWIGNode.random)
    (Finset.union_empty _)
    hWr (Finset.union_subset hXr (Finset.empty_subset M.observed)) hXr
  exact valuesOn_heq_of_coord (Finset.union_empty _) _ _
    (fun v hvU hvX => valuesUnionMk_apply_left t
      (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) hvU hvX)

private lemma frontdoor_doubledo_dropX_marginal
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed)
    (hDisjBaseXW : Disjoint X Wbase)
    (hWobsX : ∀ D ∈ Wbase, SWIGNode.random D ∈ (M.fixSet X hObs hFix).observed)
    (hWfixX : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ (M.fixSet X hObs hFix).fixed)
    (hXobsW : ∀ D ∈ X, SWIGNode.random D ∈ (M.fixSet Wbase hWobs hWfix).observed)
    (hXfixW : ∀ D ∈ X, SWIGNode.fixed D ∉ (M.fixSet Wbase hWobs hWfix).fixed)
    (hG2 : ∀ z ∈ X, ∀ v ∈ Y,
      ¬ ((M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW).dag.isAncestor
        (SWIGNode.fixed z) v)
    (s0 : M.FixedValues)
    (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
    (w : ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) :
    (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
        ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
          (M.fixSetExtend X hObs hFix s0 t) w)).map
      (valuesProjection (by simpa [SCM.fixSet_observed] using hY))
      = M.doKernelY Wbase hWobs hWfix Y hY s0 w := by
  let M₁ := (M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX
  let M₂ := (M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW
  let s₁ : M₁.FixedValues :=
    (M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
      (M.fixSetExtend X hObs hFix s0 t) w
  let s₃ : M₂.FixedValues :=
    (M.fixSet Wbase hWobs hWfix).fixSetExtend X hXobsW hXfixW
      (M.fixSetExtend Wbase hWobs hWfix s0 w) t
  have hU1o : ∀ D ∈ X ∪ Wbase, SWIGNode.random D ∈ M.observed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hObs D hD
    · exact hWobs D hD
  have hU1f : ∀ D ∈ X ∪ Wbase, SWIGNode.fixed D ∉ M.fixed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hFix D hD
    · exact hWfix D hD
  have hU2o : ∀ D ∈ Wbase ∪ X, SWIGNode.random D ∈ M.observed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hWobs D hD
    · exact hObs D hD
  have hU2f : ∀ D ∈ Wbase ∪ X, SWIGNode.fixed D ∉ M.fixed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hWfix D hD
    · exact hFix D hD
  have e1 : SCM.Equiv M₁ (M.fixSet (X ∪ Wbase) hU1o hU1f) := by
    exact SCM.ID.intervention_target_simp M X Wbase ∅ hObs hFix hWobsX hWfixX
      hU1o hU1f hDisjBaseXW
  have e2 : SCM.Equiv M₂ (M.fixSet (Wbase ∪ X) hU2o hU2f) := by
    exact SCM.ID.intervention_target_simp M Wbase X ∅ hWobs hWfix hXobsW hXfixW
      hU2o hU2f hDisjBaseXW.symm
  have eb : SCM.Equiv
      (M.fixSet (X ∪ Wbase) hU1o hU1f) (M.fixSet (Wbase ∪ X) hU2o hU2f) := by
    simpa [Finset.union_comm] using
      (SCM.Equiv.refl (M.fixSet (X ∪ Wbase) hU1o hU1f))
  have eswap : SCM.Equiv M₁ M₂ := SCM.Equiv.trans e1 (SCM.Equiv.trans eb e2.symm)
  have hY₁ : Y ⊆ M₁.observed := by
    simpa [M₁, SCM.fixSet_observed] using hY
  have hY₂ : Y ⊆ M₂.observed := by
    simpa [M₂, SCM.fixSet_observed] using hY
  have hs : HEq s₁ s₃ := by
    have hFixed : M₁.fixed = M₂.fixed := by
      dsimp [M₁, M₂]
      simp [Finset.union_comm, Finset.union_left_comm]
    have hDisjXWf : Disjoint (X.image SWIGNode.fixed) (Wbase.image SWIGNode.fixed) := by
      rw [Finset.disjoint_left]
      intro v hvX hvW
      rcases Finset.mem_image.mp hvX with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hvW with ⟨w0, hw0, hEq⟩
      cases hEq
      exact (Finset.disjoint_left.mp hDisjBaseXW) hx hw0
    apply Function.hfunext
    · exact congrArg (fun S : Finset (SWIGNode N) => {i // i ∈ S}) hFixed
    · rintro ⟨v, hv₁⟩ ⟨v', hv₃⟩ hidx
      have hv_eq : v = v' := by
        exact (Subtype.heq_iff_coe_eq (by intro x; rw [hFixed])).mp hidx
      subst hv_eq
      apply heq_of_eq
      have hv₁_full :
          v ∈ (M.fixed ∪ X.image SWIGNode.fixed) ∪ Wbase.image SWIGNode.fixed := by
        simpa [M₁, SCM.fixSet_fixed] using hv₁
      by_cases hM : v ∈ M.fixed
      · simp [s₁, s₃, M₁, M₂, SCM.fixSetExtend, SCM.fixSet_fixed, hM]
      · by_cases hXf : v ∈ X.image SWIGNode.fixed
        · have hnotWf : v ∉ Wbase.image SWIGNode.fixed := fun hWf =>
            (Finset.disjoint_left.mp hDisjXWf) hXf hWf
          have hnotMW : v ∉ M.fixed ∪ Wbase.image SWIGNode.fixed := by
            simp [hM, hnotWf]
          have hMX : v ∈ M.fixed ∪ X.image SWIGNode.fixed :=
            Finset.mem_union_right _ hXf
          simp [s₁, s₃, M₁, M₂, SCM.fixSetExtend, SCM.fixSet_fixed,
            hM, hnotMW, hMX]
        · have hWf : v ∈ Wbase.image SWIGNode.fixed := by
            rcases Finset.mem_union.mp hv₁_full with hMX | hWf
            · rcases Finset.mem_union.mp hMX with hM' | hXf'
              · exact False.elim (hM hM')
              · exact False.elim (hXf hXf')
            · exact hWf
          have hnotMX : v ∉ M.fixed ∪ X.image SWIGNode.fixed := by
            simp [hM, hXf]
          have hMW : v ∈ M.fixed ∪ Wbase.image SWIGNode.fixed :=
            Finset.mem_union_right _ hWf
          simp [s₁, s₃, M₁, M₂, SCM.fixSetExtend, SCM.fixSet_fixed,
            hM, hnotMX, hMW]
  have hswap := obsKernel_map_proj_eq_of_equiv eswap Y hY₁ hY₂ s₁ s₃ hs
  have hdrop := SCM.condDistrib_intervention_ancestral_eq (M.fixSet Wbase hWobs hWfix)
    X hXobsW hXfixW Y (by simpa [SCM.fixSet_observed] using hY) hG2 s₃
  have hproj :
      (M.fixSet Wbase hWobs hWfix).fixSetProj X hXobsW hXfixW s₃
        = M.fixSetExtend Wbase hWobs hWfix s0 w := by
    dsimp [s₃]
    rw [SCM.fixSetProj_fixSetExtend]
  rw [show ((((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
        ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
          (M.fixSetExtend X hObs hFix s0 t) w)).map
      (valuesProjection (by simpa [SCM.fixSet_observed] using hY))) =
        (M₁.obsKernel s₁).map (valuesProjection hY₁) from rfl]
  rw [hswap]
  rw [show (M₂.obsKernel s₃).map (valuesProjection hY₂) =
      (((M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW).obsKernel s₃).map
        (valuesProjection
          ((SCM.fixSet_observed (M.fixSet Wbase hWobs hWfix) X hXobsW hXfixW).symm ▸
            (by simpa [SCM.fixSet_observed] using hY))) from rfl]
  rw [hdrop]
  rw [hproj]
  rw [SCM.doKernelY, ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
    ProbabilityTheory.Kernel.comap_apply]

private theorem frontdoor_fd1_interception_compProd
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hWr : Wbase.image SWIGNode.random ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (hXrW : X.image SWIGNode.random ∪ Wbase.image SWIGNode.random ⊆ M.observed)
    (_hFD : M.toSWIGGraph.frontdoorCriterion X hObs hFix Wbase hWobs hWfix Y)
    (hDisj_YWr : Disjoint Y (Wbase.image SWIGNode.random))
    (hDisj_WrXr : Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random))
    (s0 : M.FixedValues)
    (hOverlapA : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M X hObs hFix
        (∅ : Finset (SWIGNode N)) (by simpa using hXr) s)
    (hPositivityA : M.BackdoorPositivityAE X (∅ : Finset (SWIGNode N))
        (Finset.empty_subset M.observed) hXr (by simpa using hXr) s0)
    (hOverlapB : ∀ s : (M.fixSet Wbase hWobs hWfix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M Wbase hWobs hWfix
        (X.image SWIGNode.random) (Finset.union_subset hWr hXr) s)
    (hPositivityB : M.BackdoorPositivityAE Wbase (X.image SWIGNode.random)
        hXr hWr (Finset.union_subset hWr hXr) s0)
    (hOverlapFD1 : ∀ s : ((M.fixSet X hObs hFix).fixSet Wbase
        (by intro D hD; simpa [SCM.fixSet_observed] using hWobs D hD)
        (fixSet_fixed_not_mem M X Wbase hObs hFix hWfix
          ((disjoint_base_of_disjoint_random_image hDisj_WrXr).symm))).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap (M.fixSet X hObs hFix) Wbase
        (by intro D hD; simpa [SCM.fixSet_observed] using hWobs D hD)
        (fixSet_fixed_not_mem M X Wbase hObs hFix hWfix
          ((disjoint_base_of_disjoint_random_image hDisj_WrXr).symm))
        (∅ : Finset (SWIGNode N))
        (by
          simpa [Finset.union_empty, SCM.fixSet_observed] using hWr)
        s)
    (hPositivityFD1 : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      ((((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [SCM.fixSet_observed] using hWr)) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            (((M.fixSet X hObs hFix).obsKernel s).map
              (valuesProjection (Finset.empty_subset _)))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ (((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [Finset.union_empty, SCM.fixSet_observed] using hWr))))
    :
    (M.treatmentMarginal X hXr s0) ⊗ₘ (M.doKernelY X hObs hFix Y hY s0)
      = (M.treatmentMarginal X hXr s0) ⊗ₘ
          (M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0) := by
  have hLegA := frontdoor_legA_mediator M X hObs hFix Wbase hWobs hWfix Y hWr hXr
    _hFD hDisj_WrXr s0 hOverlapA hPositivityA
  have hLegB := frontdoor_legB_outcome M X hObs hFix Wbase hWobs hWfix Y hY hWr hXr
    _hFD hDisj_YWr hDisj_WrXr s0 hOverlapB hPositivityB
  have hG1 :=
    frontdoor_fd3_rule2_dSep M X Wbase hObs hFix hWobs hWfix Y hY _hFD.2.2.1
      hDisj_WrXr
  have hG2 :=
    frontdoor_fd1_rule3_nonDesc M X Wbase hObs hFix hWobs hWfix Y _hFD.1 hDisj_WrXr
  haveI : MeasureTheory.IsFiniteMeasure (M.treatmentMarginal X hXr s0) := by
    unfold treatmentMarginal
    exact (M.obsKernel s0).isFiniteMeasure_map _
  haveI : MeasureTheory.IsFiniteMeasure (M.treatmentMarginal Wbase hWr s0) := by
    unfold treatmentMarginal
    exact (M.obsKernel s0).isFiniteMeasure_map _
  haveI : ProbabilityTheory.IsFiniteKernel
      (M.doKernelY X hObs hFix (Wbase.image SWIGNode.random) hWr s0) := by
    rw [SCM.doKernelY]; infer_instance
  haveI : ProbabilityTheory.IsFiniteKernel
      (M.doKernelY Wbase hWobs hWfix Y hY s0) := by
    rw [SCM.doKernelY]; infer_instance
  have hLegA_ae :
      (M.doKernelY X hObs hFix (Wbase.image SWIGNode.random) hWr s0)
        =ᵐ[M.treatmentMarginal X hXr s0]
      (M.adjustmentKernelY X hObs hFix (Wbase.image SWIGNode.random)
        (∅ : Finset (SWIGNode N)) hWr (Finset.empty_subset M.observed) s0) :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hLegA
  have hLegB_ae :
      (M.doKernelY Wbase hWobs hWfix Y hY s0)
        =ᵐ[M.treatmentMarginal Wbase hWr s0]
      (M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random) hY hXr s0) :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hLegB
  -- Package the FD1 transport lemma.  The finite-kernel obstruction is handled
  -- by `hLegA_ae`/`hLegB_ae` above; the remaining step is to turn `hG1` into
  -- the per-treatment Rule-2 conditional equality for
  -- `(M.fixSet X).fixSet Wbase` with empty conditioning, then transport that
  -- double intervention to the `do(Wbase)` orientation consumed by `hG2`/Rule 3.
  -- This needs a genuine FD1 overlap/positivity hypothesis for
  -- `Rule2JointOverlap (M.fixSet X hObs hFix) Wbase ... ∅ ...` and a reusable
  -- structural kernel-transport lemma across the two intervention orders.
  have hWobsX : ∀ D ∈ Wbase, SWIGNode.random D ∈ (M.fixSet X hObs hFix).observed := by
    intro D hD
    simpa [SCM.fixSet_observed] using hWobs D hD
  have hDisjBaseXW : Disjoint X Wbase :=
    (disjoint_base_of_disjoint_random_image hDisj_WrXr).symm
  have hWfixX : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ (M.fixSet X hObs hFix).fixed :=
    fixSet_fixed_not_mem M X Wbase hObs hFix hWfix hDisjBaseXW
  have hWrX : Wbase.image SWIGNode.random ⊆ (M.fixSet X hObs hFix).observed := by
    simpa [SCM.fixSet_observed] using hWr
  have hWrEmptyX :
      Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)) ⊆
        (M.fixSet X hObs hFix).observed := by
    simpa [Finset.union_empty] using hWrX
  have hYpost : Y ⊆ (M.fixSet X hObs hFix).observed := by
    simpa [SCM.fixSet_observed] using hY
  have hR2FD1 (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
      ∀ᵐ p ∂(((M.fixSet X hObs hFix).obsKernel
          (M.fixSetExtend X hObs hFix s0 t)).map
            (valuesProjection hWrX) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            (((M.fixSet X hObs hFix).obsKernel
              (M.fixSetExtend X hObs hFix s0 t)).map
              (valuesProjection (Finset.empty_subset _)))),
        ((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
            (∅ : Finset (SWIGNode N))
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
              (Finset.empty_subset (M.fixSet X hObs hFix).observed))
            ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
              (M.fixSetExtend X hObs hFix s0 t) p.1, p.2)
          =
        (M.fixSet X hObs hFix).obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
            hYpost hWrEmptyX
            (M.fixSetExtend X hObs hFix s0 t, valuesUnionMk p.1 p.2) := by
    exact SCM.do_rule2_kernel (M.fixSet X hObs hFix) Wbase hWobsX hWfixX
      Y (∅ : Finset (SWIGNode N)) hYpost (Finset.empty_subset _)
      hWrX hWrEmptyX hDisj_YWr (Finset.disjoint_empty_right _)
      (by simpa [hWobsX, hWfixX] using hG1)
      (by intro z hz v hv; simpa using hv)
      (by intro z hz v hv; simpa using hv)
      (M.fixSetExtend X hObs hFix s0 t)
      (by
        intro s
        simpa [hWobsX, hWfixX, hWrEmptyX] using hOverlapFD1 s)
      (by
        simpa [hWrX, hWrEmptyX] using
          hPositivityFD1 (M.fixSetExtend X hObs hFix s0 t))
  -- Reduce the joint (compProd) equality to a per-treatment a.e. kernel equality.
  haveI : ProbabilityTheory.IsFiniteKernel
      (M.doKernelY X hObs hFix Y hY s0) := by
    rw [SCM.doKernelY]; infer_instance
  haveI : ProbabilityTheory.IsSFiniteKernel
      (M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0) := by
    rw [SCM.frontdoorKernelY, SCM.frontdoorAdjustment]; infer_instance
  set sT := fun t => M.fixSetExtend X hObs hFix s0 t with hsT
  set κ := M.doKernelY X hObs hFix (Wbase.image SWIGNode.random) hWr s0 with hκ_def
  set condDoX :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    (M.fixSet X hObs hFix).obsCondKernel Y (Wbase.image SWIGNode.random) hYpost hWrX
      with hcondDoX_def
  have hP1 : ∀ t,
      M.doKernelY X hObs hFix Y hY s0 t
        = condDoX.sectR (sT t) ∘ₘ κ t := by
    -- Now a direct application of the treatment-indexed chain rule.
    intro t
    rw [hsT, hcondDoX_def, hκ_def]
    exact SCM.doKernelY_disintegrate M X hObs hFix Y (Wbase.image SWIGNode.random)
      hY hWr s0 t
  let xDo : (M.fixSet X hObs hFix).FixedValues →
      ValuesOn (X.image SWIGNode.random) (swigΩ Ω) :=
    fun s => zFixedAsRandom
      (valuesProjection (fixSet_image_fixed_subset M X hObs hFix) s)
  have hxDo : Measurable xDo :=
    measurable_zFixedAsRandom.comp
      (measurable_valuesProjection (fixSet_image_fixed_subset M X hObs hFix))
  haveI : ProbabilityTheory.IsMarkovKernel
      (M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random) hWr hXr) := by
    unfold SCM.obsCondKernel
    infer_instance
  let zCondXdo :
      ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
        (ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) :=
    (M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random) hWr hXr).comap
      (fun s => (M.fixSetProj X hObs hFix s, xDo s))
      (Measurable.prodMk (M.measurable_fixSetProj X hObs hFix) hxDo)
  haveI : ProbabilityTheory.IsSFiniteKernel zCondXdo := by
    dsimp [zCondXdo]
    infer_instance
  let xMarginal :
      ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
        (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :=
    (M.obsKernel.map (valuesProjection hXr)).comap
      (M.fixSetProj X hObs hFix)
      (M.measurable_fixSetProj X hObs hFix)
  let yCondXZ :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (X.image SWIGNode.random) (swigΩ Ω) ×
            ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    (M.obsCondKernel Y (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random)
        hY hXrW).comap
      (fun p =>
        (M.fixSetProj X hObs hFix p.1,
         valuesUnionMk p.2.1 p.2.2))
      (Measurable.prodMk
        ((M.measurable_fixSetProj X hObs hFix).comp measurable_fst)
        (measurable_valuesUnionMk.comp
          (Measurable.prodMk
            (measurable_fst.comp measurable_snd)
            (measurable_snd.comp measurable_snd))))
  let innerY :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    ((xMarginal.comap Prod.fst measurable_fst) ⊗ₖ
      (yCondXZ.comap
        (fun q : ((M.fixSet X hObs hFix).FixedValues ×
            ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) ×
            ValuesOn (X.image SWIGNode.random) (swigΩ Ω) =>
          (q.1.1, q.2, q.1.2))
        (Measurable.prodMk
          (measurable_fst.comp measurable_fst)
          (Measurable.prodMk measurable_snd
            (measurable_snd.comp measurable_fst))))).map Prod.snd
  have hP2 : ∀ t,
      M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0 t
        = innerY.sectR (sT t) ∘ₘ zCondXdo (sT t) := by
    intro t
    have hfd :
        M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0 t
          = M.frontdoorAdjustment X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr
              (sT t) := by
      rw [SCM.frontdoorKernelY, ProbabilityTheory.Kernel.comap_apply, hsT]
    rw [hfd]
    change (((zCondXdo ⊗ₖ innerY).map Prod.snd) (sT t))
      = innerY.sectR (sT t) ∘ₘ zCondXdo (sT t)
    rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply]
  refine MeasureTheory.Measure.compProd_congr ?_
  have hZc : ∀ a,
      zCondXdo (sT a)
        = M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random)
            hWr hXr (s0, a) := by
    intro a
    rw [hsT]
    change (M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random)
        hWr hXr).comap
        (fun s => (M.fixSetProj X hObs hFix s, xDo s))
        (Measurable.prodMk (M.measurable_fixSetProj X hObs hFix) hxDo)
        (M.fixSetExtend X hObs hFix s0 a)
      = M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random)
          hWr hXr (s0, a)
    rw [ProbabilityTheory.Kernel.comap_apply]
    rw [SCM.fixSetProj_fixSetExtend]
    have hx : xDo (M.fixSetExtend X hObs hFix s0 a) = a := by
      dsimp [xDo]
      exact SCM.zFixedAsRandom_proj_fixSetExtend M X hObs hFix s0 a
    rw [hx]
  have hAdjZ : ∀ a,
      M.adjustmentKernelY X hObs hFix (Wbase.image SWIGNode.random)
          (∅ : Finset (SWIGNode N)) hWr (Finset.empty_subset M.observed) s0 a
        = zCondXdo (sT a) := by
    intro a
    rw [hZc a]
    exact adjustmentKernelY_empty_eq M X hObs hFix (Wbase.image SWIGNode.random)
      hWr hXr s0 a
  have hQ1 :
      ⇑κ =ᵐ[M.treatmentMarginal X hXr s0] fun a => zCondXdo (sT a) := by
    filter_upwards [hLegA_ae] with a ha
    rw [ha]
    exact hAdjZ a
  have hQ2 :
      ∀ᵐ a ∂M.treatmentMarginal X hXr s0,
        ∀ᵐ z ∂κ a, condDoX (sT a, z) = innerY (sT a, z) := by
    have hFD1Collapse : ∀ a,
        ∀ᵐ z ∂κ a,
          condDoX (sT a, z) = M.doKernelY Wbase hWobs hWfix Y hY s0 z := by
      intro a
      have hκ_a :
          ((M.fixSet X hObs hFix).obsKernel (sT a)).map (valuesProjection hWrX)
            = κ a := by
        rw [hκ_def, SCM.doKernelY,
          ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
          ProbabilityTheory.Kernel.comap_apply, hsT]
      have hprod := MeasureTheory.Measure.ae_ae_of_ae_compProd (hR2FD1 a)
      rw [hκ_a] at hprod
      filter_upwards [hprod] with z hz
      have hzDefault :
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
              (∅ : Finset (SWIGNode N))
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z,
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
            =
            ((M.fixSet X hObs hFix).obsCondKernel Y
              (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
              hYpost hWrEmptyX)
              (M.fixSetExtend X hObs hFix s0 a,
                valuesUnionMk z
                  (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
        have hdir :
            (((M.fixSet X hObs hFix).obsKernel (M.fixSetExtend X hObs hFix s0 a)).map
              (valuesProjection (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
              = MeasureTheory.Measure.dirac
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) := by
          exact obsKernel_empty_projection_eq_dirac (M.fixSet X hObs hFix)
            (Finset.empty_subset (M.fixSet X hObs hFix).observed)
            (M.fixSetExtend X hObs hFix s0 a)
            (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))
        have hz' : ∀ᵐ e ∂(MeasureTheory.Measure.dirac
              (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))),
            (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
                (∅ : Finset (SWIGNode N))
                ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
                ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                  (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
                ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                  (M.fixSetExtend X hObs hFix s0 a) z, e)
              =
              ((M.fixSet X hObs hFix).obsCondKernel Y
                (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
                hYpost hWrEmptyX)
                (M.fixSetExtend X hObs hFix s0 a, valuesUnionMk z e) := by
          rw [ProbabilityTheory.Kernel.const_apply] at hz
          rw [hdir] at hz
          exact hz
        simpa [MeasureTheory.ae_dirac_eq, Filter.eventually_pure] using hz'
      -- The remaining rewrites are exactly the empty-conditioning marginal
      -- collapse and intervention-order marginal transport.
      have hXobsW : ∀ D ∈ X, SWIGNode.random D ∈
          (M.fixSet Wbase hWobs hWfix).observed := by
        intro D hD
        simpa [SCM.fixSet_observed] using hObs D hD
      have hXfixW : ∀ D ∈ X, SWIGNode.fixed D ∉
          (M.fixSet Wbase hWobs hWfix).fixed :=
        fixSet_fixed_not_mem M Wbase X hWobs hWfix hFix hDisjBaseXW.symm
      have hG2' : ∀ d ∈ X, ∀ v ∈ Y,
          ¬ ((M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW).dag.isAncestor
            (SWIGNode.fixed d) v := by
        intro d hd v hv
        exact hG2 v (by simpa using hv) d hd
      have hLhsMarg :
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
              (∅ : Finset (SWIGNode N))
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                hYpost)
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z,
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
            =
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z)).map
            (valuesProjection
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                hYpost)) := by
        exact obsCondKernel_empty_eq_marginal
          ((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX) Y
          ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
          ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
            (M.fixSetExtend X hObs hFix s0 a) z)
          (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))
      have hDrop := frontdoor_doubledo_dropX_marginal M X hObs hFix Wbase hWobs hWfix
        Y hY hDisjBaseXW hWobsX hWfixX hXobsW hXfixW hG2' s0 a z
      calc
        condDoX (sT a, z)
            =
          ((M.fixSet X hObs hFix).obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hYpost
            hWrEmptyX)
            (M.fixSetExtend X hObs hFix s0 a,
              valuesUnionMk z
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
          rw [hcondDoX_def, hsT]
          apply obsCondKernel_congr_cc (M.fixSet X hObs hFix) Y
            (Wbase.image SWIGNode.random)
            (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
            (by simp) hYpost hWrX hWrEmptyX
          exact valuesOn_heq_of_coord (by simp) _ _
            (fun v hvW hvU => (valuesUnionMk_apply_left z
              (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) hvU hvW).symm)
        _ =
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
            (∅ : Finset (SWIGNode N))
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
              hYpost)
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
              (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
            ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
              (M.fixSetExtend X hObs hFix s0 a) z,
              (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := hzDefault.symm
        _ =
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z)).map
            (valuesProjection (by simpa [SCM.fixSet_observed] using hY)) := by
          rw [hLhsMarg]
        _ = M.doKernelY Wbase hWobs hWfix Y hY s0 z := hDrop
    have hκComp : κ ∘ₘ M.treatmentMarginal X hXr s0 = M.treatmentMarginal Wbase hWr s0 := by
      have hChain := SCM.obsKernel_map_eq_obsCondKernel_comp M
        (Wbase.image SWIGNode.random) (X.image SWIGNode.random) hWr hXr s0
      rw [SCM.treatmentMarginal, SCM.treatmentMarginal]
      rw [hChain]
      refine MeasureTheory.Measure.bind_congr_right ?_
      filter_upwards [hQ1] with a ha
      rw [ha]
      rw [hZc a]
      rfl
    have hLegB_pull :
        ∀ᵐ a ∂M.treatmentMarginal X hXr s0,
          ∀ᵐ z ∂κ a,
            M.doKernelY Wbase hWobs hWfix Y hY s0 z
              = M.adjustmentKernelY Wbase hWobs hWfix Y
                  (X.image SWIGNode.random) hY hXr s0 z := by
      have hb :
          ∀ᵐ z ∂κ ∘ₘ M.treatmentMarginal X hXr s0,
            M.doKernelY Wbase hWobs hWfix Y hY s0 z
              = M.adjustmentKernelY Wbase hWobs hWfix Y
                  (X.image SWIGNode.random) hY hXr s0 z := by
        simpa [hκComp] using hLegB_ae
      exact MeasureTheory.Measure.ae_ae_of_ae_bind (ProbabilityTheory.Kernel.aemeasurable κ) hb
    have hInner : ∀ a z,
        M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
            hY hXr s0 z = innerY (sT a, z) := by
      intro a z
      let μX : MeasureTheory.Measure (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :=
        (M.obsKernel s0).map (valuesProjection hXr)
      let sW := M.fixSetExtend Wbase hWobs hWfix s0 z
      have hWrXr :
          Wbase.image SWIGNode.random ∪ X.image SWIGNode.random ⊆ M.observed :=
        Finset.union_subset hWr hXr
      let condPostW :
          ProbabilityTheory.Kernel
            ((M.fixSet Wbase hWobs hWfix).FixedValues ×
              ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
            (ValuesOn Y (swigΩ Ω)) :=
        (M.obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random) hY hWrXr).comap
          (fun p =>
            (M.fixSetProj Wbase hWobs hWfix p.1,
             M.fillZrW Wbase hWobs hWfix (X.image SWIGNode.random) p.1 p.2))
          (Measurable.prodMk
            ((M.measurable_fixSetProj Wbase hWobs hWfix).comp measurable_fst)
            (M.measurable_fillZrW_prod Wbase hWobs hWfix (X.image SWIGNode.random)))
      let yInner :
          ProbabilityTheory.Kernel
            (((M.fixSet X hObs hFix).FixedValues ×
              ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) ×
              ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
            (ValuesOn Y (swigΩ Ω)) :=
        yCondXZ.comap
          (fun q : ((M.fixSet X hObs hFix).FixedValues ×
              ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) ×
              ValuesOn (X.image SWIGNode.random) (swigΩ Ω) =>
            (q.1.1, q.2, q.1.2))
          (Measurable.prodMk
            (measurable_fst.comp measurable_fst)
            (Measurable.prodMk measurable_snd
              (measurable_snd.comp measurable_fst)))
      haveI : ProbabilityTheory.IsMarkovKernel
          (M.obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random) hY hWrXr) := by
        unfold SCM.obsCondKernel
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel
          (M.obsCondKernel Y
            (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random) hY hXrW) := by
        unfold SCM.obsCondKernel
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel yCondXZ := by
        dsimp [yCondXZ]
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel condPostW := by
        dsimp [condPostW]
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel yInner := by
        dsimp [yInner, yCondXZ]
        infer_instance
      haveI : ProbabilityTheory.IsSFiniteKernel condPostW := by
        infer_instance
      haveI : ProbabilityTheory.IsSFiniteKernel yInner := by
        infer_instance
      have hLhs :
          M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
              hY hXr s0 z = condPostW.sectR sW ∘ₘ μX := by
        have hadj :
            M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
                hY hXr s0 z =
              M.backdoorAdjustment Wbase hWobs hWfix Y (X.image SWIGNode.random)
                hY hXr sW := by
          rw [SCM.adjustmentKernelY, ProbabilityTheory.Kernel.comap_apply]
        rw [hadj]
        change ((((M.obsKernel.map (valuesProjection hXr)).comap
                (M.fixSetProj Wbase hWobs hWfix)
                (M.measurable_fixSetProj Wbase hWobs hWfix))
              ⊗ₖ condPostW).map Prod.snd) sW
          = condPostW.sectR sW ∘ₘ μX
        rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply,
          ProbabilityTheory.Kernel.comap_apply,
          ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _)]
        simp [sW, μX, SCM.fixSetProj_fixSetExtend]
      have hRhs :
          innerY (sT a, z) = yInner.sectR (sT a, z) ∘ₘ μX := by
        change (((xMarginal.comap Prod.fst measurable_fst) ⊗ₖ yInner).map Prod.snd)
            (sT a, z) = yInner.sectR (sT a, z) ∘ₘ μX
        rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply,
          ProbabilityTheory.Kernel.comap_apply]
        have hx : xMarginal (sT a) = μX := by
          rw [hsT]
          change ((M.obsKernel.map (valuesProjection hXr)).comap
              (M.fixSetProj X hObs hFix)
              (M.measurable_fixSetProj X hObs hFix))
              (M.fixSetExtend X hObs hFix s0 a) = μX
          rw [ProbabilityTheory.Kernel.comap_apply,
            SCM.fixSetProj_fixSetExtend,
            ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _)]
        rw [hx]
      rw [hLhs, hRhs]
      refine MeasureTheory.Measure.comp_congr ?_
      filter_upwards [] with x'
      calc
        condPostW.sectR sW x'
            =
          M.obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random) hY hWrXr
            (s0, valuesUnionMk z x') := by
          rw [ProbabilityTheory.Kernel.sectR_apply]
          simp [condPostW, sW, ProbabilityTheory.Kernel.comap_apply,
            SCM.fixSetProj_fixSetExtend, SCM.fillZrW_fixSetExtend]
        _ =
          M.obsCondKernel Y
            (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random) hY hXrW
            (s0, valuesUnionMk x' z) := by
          exact obsCondKernel_congr_cc M Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random)
            (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random)
            (Finset.union_comm _ _) hY hWrXr hXrW s0
            (valuesUnionMk z x') (valuesUnionMk x' z)
            (valuesUnionMk_union_comm_heq hDisj_WrXr z x')
        _ = yInner.sectR (sT a, z) x' := by
          rw [ProbabilityTheory.Kernel.sectR_apply, hsT]
          simp [yInner, yCondXZ, ProbabilityTheory.Kernel.comap_apply,
            SCM.fixSetProj_fixSetExtend]
    filter_upwards [hLegB_pull] with a haB
    filter_upwards [hFD1Collapse a, haB] with z hzFD hzB
    calc
      condDoX (sT a, z)
          = M.doKernelY Wbase hWobs hWfix Y hY s0 z := hzFD
      _ = M.adjustmentKernelY Wbase hWobs hWfix Y
            (X.image SWIGNode.random) hY hXr s0 z := hzB
      _ = innerY (sT a, z) := hInner a z
  filter_upwards [hQ1, hQ2] with a ha1 ha2
  calc
    M.doKernelY X hObs hFix Y hY s0 a
        = condDoX.sectR (sT a) ∘ₘ κ a := hP1 a
    _ = innerY.sectR (sT a) ∘ₘ κ a := by
      refine MeasureTheory.Measure.bind_congr_right ?_
      filter_upwards [ha2] with z hz
      rw [ProbabilityTheory.Kernel.sectR_apply, ProbabilityTheory.Kernel.sectR_apply]
      exact hz
    _ = innerY.sectR (sT a) ∘ₘ zCondXdo (sT a) := by
      rw [ha1]
    _ = M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0 a :=
      (hP2 a).symm

/-- **Frontdoor completeness — joint (compProd), version-safe primary form.**

    `νX ⊗ₘ doKernelY = νX ⊗ₘ frontdoorKernelY` at base `s₀`, under the frontdoor
    criterion and the back-door positivity / overlap conditions inherited from the
    `do(W)` outcome leg.  This is the frontdoor analogue of
    `backdoor_completeness_ae_compProd`.

    Proof plan: combine Leg A (`frontdoor_mediator_rule2`) and Leg B
    (`backdoor_completeness_ae_compProd` with treatment `:= W`, adjustment
    `:= X.image .random`, outcome `:= Y`), then reassemble into the
    `frontdoorAdjustment` body.  See the module docstring. -/
theorem frontdoor_completeness_ae_compProd
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hWr : Wbase.image SWIGNode.random ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (hXrW : X.image SWIGNode.random ∪ Wbase.image SWIGNode.random ⊆ M.observed)
    (_hFD : M.toSWIGGraph.frontdoorCriterion X hObs hFix Wbase hWobs hWfix Y)
    (hDisj_YWr : Disjoint Y (Wbase.image SWIGNode.random))
    (hDisj_WrXr : Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random))
    (s0 : M.FixedValues)
    (hOverlapA : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M X hObs hFix
        (∅ : Finset (SWIGNode N)) (by simpa using hXr) s)
    (hPositivityA : M.BackdoorPositivityAE X (∅ : Finset (SWIGNode N))
        (Finset.empty_subset M.observed) hXr (by simpa using hXr) s0)
    (hOverlapB : ∀ s : (M.fixSet Wbase hWobs hWfix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M Wbase hWobs hWfix
        (X.image SWIGNode.random) (Finset.union_subset hWr hXr) s)
    (hPositivityB : M.BackdoorPositivityAE Wbase (X.image SWIGNode.random)
        hXr hWr (Finset.union_subset hWr hXr) s0)
    (hOverlapFD1 : ∀ s : ((M.fixSet X hObs hFix).fixSet Wbase
        (by intro D hD; simpa [SCM.fixSet_observed] using hWobs D hD)
        (fixSet_fixed_not_mem M X Wbase hObs hFix hWfix
          ((disjoint_base_of_disjoint_random_image hDisj_WrXr).symm))).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap (M.fixSet X hObs hFix) Wbase
        (by intro D hD; simpa [SCM.fixSet_observed] using hWobs D hD)
        (fixSet_fixed_not_mem M X Wbase hObs hFix hWfix
          ((disjoint_base_of_disjoint_random_image hDisj_WrXr).symm))
        (∅ : Finset (SWIGNode N))
        (by
          simpa [Finset.union_empty, SCM.fixSet_observed] using hWr)
        s)
    (hPositivityFD1 : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      ((((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [SCM.fixSet_observed] using hWr)) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            (((M.fixSet X hObs hFix).obsKernel s).map
              (valuesProjection (Finset.empty_subset _)))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ (((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [Finset.union_empty, SCM.fixSet_observed] using hWr)))) :
    (M.treatmentMarginal X hXr s0) ⊗ₘ (M.doKernelY X hObs hFix Y hY s0)
      = (M.treatmentMarginal X hXr s0) ⊗ₘ
          (M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0) := by
  exact frontdoor_fd1_interception_compProd M X hObs hFix Wbase hWobs hWfix Y hY hWr hXr
    hXrW _hFD hDisj_YWr hDisj_WrXr s0 hOverlapA hPositivityA hOverlapB hPositivityB
    hOverlapFD1 hPositivityFD1

/-- **Frontdoor identification, a.e. in the treatment value.**

    For `νX`-almost-every treatment value `t`, the post-intervention `Y`-marginal
    `doKernelY t` equals the frontdoor-adjustment functional `frontdoorKernelY t`.
    The frontdoor analogue of `backdoor_identifiable_ae`; follows from
    `frontdoor_completeness_ae_compProd` by `ae_eq_of_compProd_eq`. -/
theorem frontdoor_identifiable_ae
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hWr : Wbase.image SWIGNode.random ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (_hFD : M.toSWIGGraph.frontdoorCriterion X hObs hFix Wbase hWobs hWfix Y)
    (hDisj_YWr : Disjoint Y (Wbase.image SWIGNode.random))
    (hDisj_WrXr : Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random))
    (s0 : M.FixedValues)
    (hOverlapA : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M X hObs hFix
        (∅ : Finset (SWIGNode N)) (by simpa using hXr) s)
    (hPositivityA : M.BackdoorPositivityAE X (∅ : Finset (SWIGNode N))
        (Finset.empty_subset M.observed) hXr (by simpa using hXr) s0)
    (hOverlapB : ∀ s : (M.fixSet Wbase hWobs hWfix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M Wbase hWobs hWfix
        (X.image SWIGNode.random) (Finset.union_subset hWr hXr) s)
    (hPositivityB : M.BackdoorPositivityAE Wbase (X.image SWIGNode.random)
        hXr hWr (Finset.union_subset hWr hXr) s0)
    (hOverlapFD1 : ∀ s : ((M.fixSet X hObs hFix).fixSet Wbase
        (by intro D hD; simpa [SCM.fixSet_observed] using hWobs D hD)
        (fixSet_fixed_not_mem M X Wbase hObs hFix hWfix
          ((disjoint_base_of_disjoint_random_image hDisj_WrXr).symm))).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap (M.fixSet X hObs hFix) Wbase
        (by intro D hD; simpa [SCM.fixSet_observed] using hWobs D hD)
        (fixSet_fixed_not_mem M X Wbase hObs hFix hWfix
          ((disjoint_base_of_disjoint_random_image hDisj_WrXr).symm))
        (∅ : Finset (SWIGNode N))
        (by
          simpa [Finset.union_empty, SCM.fixSet_observed] using hWr)
        s)
    (hPositivityFD1 : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      ((((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [SCM.fixSet_observed] using hWr)) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            (((M.fixSet X hObs hFix).obsKernel s).map
              (valuesProjection (Finset.empty_subset _)))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ (((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [Finset.union_empty, SCM.fixSet_observed] using hWr)))) :
    ∀ᵐ t ∂(M.treatmentMarginal X hXr s0),
      M.doKernelY X hObs hFix Y hY s0 t
        = M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0 t := by
  have hXrW : X.image SWIGNode.random ∪ Wbase.image SWIGNode.random ⊆ M.observed :=
    Finset.union_subset hXr hWr
  haveI : MeasureTheory.IsFiniteMeasure (M.treatmentMarginal X hXr s0) := by
    unfold treatmentMarginal
    exact (M.obsKernel s0).isFiniteMeasure_map _
  exact ProbabilityTheory.Kernel.ae_eq_of_compProd_eq
    (M.frontdoor_completeness_ae_compProd X hObs hFix Wbase hWobs hWfix Y hY hWr hXr
      hXrW _hFD hDisj_YWr hDisj_WrXr s0 hOverlapA hPositivityA hOverlapB hPositivityB
      hOverlapFD1 hPositivityFD1)

end SCM

end Causalean
