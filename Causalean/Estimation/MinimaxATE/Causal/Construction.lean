/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.MinimaxATE.Model
import Causalean.PO.ID.Exact.ATE
import Causalean.PO.Bridge.FromSCM
import Causalean.Graph.DAG
import Causalean.Graph.SWIG
import Causalean.SCM.Model.EdgeType
import Causalean.SCM.Model.SCM
import Mathlib.Probability.Distributions.Uniform

/-!
# Causal Grounding of the Minimax ATE Model

This file builds, from a finite data-generating process `(m, g)` on a finite
covariate space `C`, a concrete generalized SCM realizing the textbook backdoor
triangle and lifts it through `Causalean.PO.Bridge.FromSCM.POSystem.ofSCM` to a
`POBackdoorSystem`.  Its potential-outcome ATE `S.ATE = E[Y(1) − Y(0)]` is what
the minimax lower bound is *really* about; the bridge `MinimaxATE/Causal/Bridge.lean`
identifies `S.ATE` with the observed-data contrast `ate g` used by the proof
machinery.

The DAG is the backdoor triangle on the OBSERVED covariate `Xc`:
`Un → Xc → A → Y` with `Xc → Y`, plus independent latent noise roots
`Ea → A`, `Ey → Y`:

* `Un ~ Uniform(C)`, the latent covariate draw; the observed covariate node
  `Xc := Un` copies it (Causalean SCM observed nodes must be endogenous);
* treatment `A := 1{Ea ≤ m Xc}`, so `A | X=x ~ Bernoulli(m x)` (`Ea ~ U[0,1]`);
* outcome `Y(a) := 1{Ey ≤ g a Xc}` and `Y := A·Y(1) + (1−A)·Y(0)`
  (`Ey ~ U[0,1]`), the consistency assignment; `Ea ⟂ Ey | X` so unconfoundedness
  `A ⟂ (Y(1), Y(0)) | X` holds.

Mirrors the proven-shape witness construction in
`CausalSmith/.../STAT_AteOverlapDecay_Clean/Witness/Construction.lean` (Causalean
cannot import CausalSmith, so the construction is reproduced here, specialized to
a finite covariate `C` and the propensity/outcome pair `(m, g)`).  The main
public objects are the witness graph data `WNode`, `wDAG`, and `wSWIGGraph`; the
structural functions `treatFun` and `outFun`; the laws `unifLaw` and `covLaw`;
the concrete SCM `dgpSCM`; and the induced potential-outcome/backdoor systems
`dgpPO` and `dgpBackdoor`.
-/

namespace Causalean.Estimation.MinimaxATE.Causal

open Causalean Causalean.PO
open MeasureTheory

/-! ## The witness node type and graph (covariate-independent) -/

/-- These are the nodes of the finite backdoor witness graph. -/
inductive WNode
  | Xc | A | Y | Un | Ea | Ey
  deriving DecidableEq

namespace WNode

/-- This gives a printable representation for the witness graph nodes. -/
protected def repr : WNode → Nat → Std.Format
  | Xc, _ => "WNode.Xc"
  | A, _ => "WNode.A"
  | Y, _ => "WNode.Y"
  | Un, _ => "WNode.Un"
  | Ea, _ => "WNode.Ea"
  | Ey, _ => "WNode.Ey"

/-- The witness graph nodes can be rendered for debugging and generated instances. -/
instance : Repr WNode := ⟨WNode.repr⟩

/-- The witness graph nodes form a finite type. -/
instance : Fintype WNode where
  elems := {Xc, A, Y, Un, Ea, Ey}
  complete := by intro x; cases x <;> simp

end WNode

open WNode

/-- This is the edge relation for the finite backdoor witness graph. -/
def wEdge : WNode → WNode → Prop
  | Un, Xc => True
  | Xc, A  => True
  | Xc, Y  => True
  | A,  Y  => True
  | Ea, A  => True
  | Ey, Y  => True
  | _,  _  => False

/-- The witness graph edge relation is decidable. -/
instance : DecidableRel wEdge := by
  intro a b; cases a <;> cases b <;> simp [wEdge] <;> infer_instance

/-- This topological order places latent roots before the observed covariate,
treatment, and outcome. -/
def wTopo : WNode → ℕ
  | Un => 0
  | Ea => 1
  | Ey => 2
  | Xc => 3
  | A  => 4
  | Y  => 5

/-- Every witness-graph edge points forward in the chosen topological order. -/
theorem wTopo_lt : ∀ u v, wEdge u v → wTopo u < wTopo v := by
  intro u v h; cases u <;> cases v <;> simp_all [wEdge, wTopo]

/-- This is the directed acyclic graph for the finite backdoor witness. -/
def wDAG : DAG WNode where
  edge := wEdge
  decEdge := inferInstance
  acyclic := DAG.acyclic_of_topoOrder wTopo_lt

/-- This is the SWIG graph with observed covariate, treatment, and outcome nodes
and latent noise roots. -/
def wSWIGGraph : SWIGGraph WNode where
  dag := initialSWIG wDAG
  fixed := ∅
  observed := {SWIGNode.random Xc, SWIGNode.random A, SWIGNode.random Y}
  unobserved := {SWIGNode.random Un, SWIGNode.random Ea, SWIGNode.random Ey}
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by
    intro u hu; simp at hu
    rcases hu with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obs_unobs_disjoint := by native_decide
  dag_edges_classified := by native_decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by
    intro u hu; simp at hu
    rcases hu with rfl | rfl | rfl <;>
      simpa [initialSWIG] using
        (swig_random_root_of_root wDAG ∅ _ (by native_decide))
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by native_decide, by native_decide⟩
  all_children_in_observed := by native_decide

section DGP

variable (C : Type) [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [StandardBorelSpace C]

/-- This assigns value spaces to the witness graph nodes. -/
def WΩ : WNode → Type
  | Xc => C
  | A  => Bool
  | Y  => ℝ
  | Un => C
  | Ea => ℝ
  | Ey => ℝ

/-- Each witness node value space has its measurable-space structure. -/
noncomputable instance WΩ_meas : ∀ n, MeasurableSpace (WΩ C n)
  | Xc => inferInstanceAs (MeasurableSpace C)
  | A  => inferInstanceAs (MeasurableSpace Bool)
  | Y  => inferInstanceAs (MeasurableSpace ℝ)
  | Un => inferInstanceAs (MeasurableSpace C)
  | Ea => inferInstanceAs (MeasurableSpace ℝ)
  | Ey => inferInstanceAs (MeasurableSpace ℝ)

/-- Each witness node value space is standard Borel. -/
noncomputable instance WΩ_borel : ∀ n, StandardBorelSpace (WΩ C n)
  | Xc => inferInstanceAs (StandardBorelSpace C)
  | A  => inferInstanceAs (StandardBorelSpace Bool)
  | Y  => inferInstanceAs (StandardBorelSpace ℝ)
  | Un => inferInstanceAs (StandardBorelSpace C)
  | Ea => inferInstanceAs (StandardBorelSpace ℝ)
  | Ey => inferInstanceAs (StandardBorelSpace ℝ)

/-- Each witness node value space is nonempty. -/
instance WΩ_nonempty : ∀ n, Nonempty (WΩ C n)
  | Xc => inferInstanceAs (Nonempty C)
  | A  => inferInstanceAs (Nonempty Bool)
  | Y  => inferInstanceAs (Nonempty ℝ)
  | Un => inferInstanceAs (Nonempty C)
  | Ea => inferInstanceAs (Nonempty ℝ)
  | Ey => inferInstanceAs (Nonempty ℝ)

/-! ## Structural functions and parent-value plumbing -/

/-- This structural function turns a uniform treatment noise draw into a Boolean treatment. -/
noncomputable def treatFun (p ea : ℝ) : Bool := decide (ea ≤ p)

/-- This structural function turns treatment, covariate, and outcome noise into a
Bernoulli outcome. -/
noncomputable def outFun (g : Bool → C → ℝ) (a : Bool) (x : C) (ey : ℝ) : ℝ :=
  if ey ≤ g a x then 1 else 0

/-- Every graph edge gives membership of the parent node in the corresponding SWIG parent set. -/
theorem wParent_mem {p c : WNode} (h : wEdge p c) :
    (SWIGNode.random p) ∈ (initialSWIG wDAG).parents (SWIGNode.random c) := by
  rw [DAG.mem_parents, initialSWIG_random_edge]; exact h

/-- This extracts a parent node's value from the tuple of parent values supplied
to a structural function. -/
def parentVal {c : WNode}
    (vals : ∀ w : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random c)}, swigΩ (WΩ C) w.val)
    {p : WNode} (h : wEdge p c) : WΩ C p :=
  vals ⟨SWIGNode.random p, wParent_mem h⟩

/-- This is the uniform law on the unit interval used for the latent noise roots. -/
noncomputable def unifLaw : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The unit-interval uniform law is a probability measure. -/
instance instIsProbabilityMeasureUnifLaw : IsProbabilityMeasure unifLaw := by
  unfold unifLaw
  constructor
  simp [Real.volume_Icc]

/-- This is the uniform law on the finite covariate space. -/
noncomputable def covLaw : Measure C := (PMF.uniformOfFintype C).toMeasure

/-- The finite covariate uniform law is a probability measure. -/
instance instIsProbabilityMeasureCovLaw : IsProbabilityMeasure (covLaw C) := by
  unfold covLaw; infer_instance

variable {C}

/-- This is the concrete stochastic structural causal model for a finite
propensity and outcome regression.

It realizes the backdoor triangle with a uniform covariate root, independent unit-interval noise
for treatment and outcome, treatment generated from the propensity, and outcome generated from
the arm-specific outcome regression. -/
noncomputable def dgpSCM (m : C → ℝ) (g : Bool → C → ℝ) :
    Causalean.SCM WNode (WΩ C) where
  toSWIGGraph := wSWIGGraph
  edgeTypes := EdgeTypeAssignment.allNonparametric (initialSWIG wDAG)
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := fun v vals =>
    match v with
    | ⟨SWIGNode.random Xc, _⟩ =>
        (parentVal (C := C) vals (show wEdge Un Xc from trivial) : C)
    | ⟨SWIGNode.random A, _⟩ =>
        treatFun (m (parentVal (C := C) vals (show wEdge Xc A from trivial)))
                 (parentVal (C := C) vals (show wEdge Ea A from trivial))
    | ⟨SWIGNode.random Y, _⟩ =>
        outFun (C := C) g (parentVal (C := C) vals (show wEdge A Y from trivial))
                 (parentVal (C := C) vals (show wEdge Xc Y from trivial))
                 (parentVal (C := C) vals (show wEdge Ey Y from trivial))
    | ⟨SWIGNode.random Un, h⟩ => absurd h (by decide)
    | ⟨SWIGNode.random Ea, h⟩ => absurd h (by decide)
    | ⟨SWIGNode.random Ey, h⟩ => absurd h (by decide)
    | ⟨SWIGNode.fixed n, h⟩ =>
        (by simp only [wSWIGGraph, Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h | h <;> exact absurd h (by simp) : False).elim
  structFun_measurable := by
    intro v
    rcases v with ⟨n, hn⟩
    cases n with
    | random a =>
        cases a <;> simp [parentVal, treatFun, outFun]
        · exact measurable_pi_apply _
        · let iEa : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random A)} :=
            ⟨SWIGNode.random Ea, wParent_mem (show wEdge Ea A from trivial)⟩
          let iX : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random A)} :=
            ⟨SWIGNode.random Xc, wParent_mem (show wEdge Xc A from trivial)⟩
          have hEa : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random A)},
                  swigΩ (WΩ C) w.val) => (show ℝ from vals iEa)) := by
            simpa [iEa] using (measurable_pi_apply iEa)
          have hX : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random A)},
                  swigΩ (WΩ C) w.val) => (show C from vals iX)) := by
            simpa [iX] using (measurable_pi_apply iX)
          apply measurable_to_bool
          simpa [Set.preimage, iEa, iX, decide_eq_true_eq] using
            measurableSet_le hEa ((measurable_of_finite m).comp hX)
        · let iEy : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random Y)} :=
            ⟨SWIGNode.random Ey, wParent_mem (show wEdge Ey Y from trivial)⟩
          let iA : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random Y)} :=
            ⟨SWIGNode.random A, wParent_mem (show wEdge A Y from trivial)⟩
          let iX : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random Y)} :=
            ⟨SWIGNode.random Xc, wParent_mem (show wEdge Xc Y from trivial)⟩
          have hEy : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) => (show ℝ from vals iEy)) := by
            simpa [iEy] using (measurable_pi_apply iEy)
          have hA : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) => (show Bool from vals iA)) := by
            simpa [iA] using (measurable_pi_apply iA)
          have hX : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) => (show C from vals iX)) := by
            simpa [iX] using (measurable_pi_apply iX)
          have hg : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) =>
                g (show Bool from vals iA) (show C from vals iX)) :=
            (measurable_of_finite (fun p : Bool × C => g p.1 p.2)).comp
              (hA.prodMk hX)
          refine Measurable.ite ?_ measurable_const measurable_const
          exact measurableSet_le hEy hg
    | fixed a =>
        simp [wSWIGGraph] at hn
  latentDist := fun u => by
    rcases u with ⟨n, hn⟩
    exact
      match n, hn with
      | SWIGNode.random Un, _ => covLaw C
      | SWIGNode.random Ea, _ => unifLaw
      | SWIGNode.random Ey, _ => unifLaw
      | _, _ => (0 : Measure _)
  isProbability_latent := by
    intro u
    rcases u with ⟨n, hn⟩
    cases n with
    | random n =>
        cases n <;> simp [wSWIGGraph] at hn ⊢
        · exact instIsProbabilityMeasureCovLaw C
        · exact instIsProbabilityMeasureUnifLaw
        · exact instIsProbabilityMeasureUnifLaw
    | fixed n =>
        simp [wSWIGGraph] at hn

/-- This is the empty background assignment for the witness SCM. -/
noncomputable def dgpFixed (m : C → ℝ) (g : Bool → C → ℝ) :
    SCM.FixedValues (dgpSCM m g) :=
  fun s => (Finset.notMem_empty s.val s.property).elim

/-- This is the potential-outcome system induced by the witness structural causal model. -/
noncomputable def dgpPO (m : C → ℝ) (g : Bool → C → ℝ) : POSystem :=
  POSystem.ofSCM (dgpSCM m g) (dgpFixed m g)

/-- This is the observed-node index of the treatment in the induced potential-outcome system. -/
noncomputable def AIdx (m : C → ℝ) (g : Bool → C → ℝ) : (dgpPO m g).V :=
  (⟨SWIGNode.random A, by simp [dgpSCM, wSWIGGraph]⟩ : ObsIdx (dgpSCM m g))

/-- This is the observed-node index of the outcome in the induced potential-outcome system. -/
noncomputable def YIdx (m : C → ℝ) (g : Bool → C → ℝ) : (dgpPO m g).V :=
  (⟨SWIGNode.random Y, by simp [dgpSCM, wSWIGGraph]⟩ : ObsIdx (dgpSCM m g))

/-- This is the observed-node index of the covariate in the induced potential-outcome system. -/
noncomputable def XIdx (m : C → ℝ) (g : Bool → C → ℝ) : (dgpPO m g).V :=
  (⟨SWIGNode.random Xc, by simp [dgpSCM, wSWIGGraph]⟩ : ObsIdx (dgpSCM m g))

/-- This identifies the treatment node's value space with Booleans. -/
noncomputable def AEquiv (m : C → ℝ) (g : Bool → C → ℝ) :
    (dgpPO m g).X (AIdx m g) ≃ᵐ Bool :=
  MeasurableEquiv.refl Bool

/-- This identifies the outcome node's value space with real numbers. -/
noncomputable def YEquiv (m : C → ℝ) (g : Bool → C → ℝ) :
    (dgpPO m g).X (YIdx m g) ≃ᵐ ℝ :=
  MeasurableEquiv.refl ℝ

/-- This identifies the covariate node's value space with the finite covariate type. -/
noncomputable def XEquiv (m : C → ℝ) (g : Bool → C → ℝ) :
    (dgpPO m g).X (XIdx m g) ≃ᵐ C :=
  MeasurableEquiv.refl C

/-- This is the backdoor potential-outcome system extracted from the finite witness construction.

It uses the constructed treatment, outcome, and covariate nodes as the variables of the backdoor
estimation problem. -/
noncomputable def dgpBackdoor (m : C → ℝ) (g : Bool → C → ℝ) :
    POBackdoorSystem (dgpPO m g) C where
  D := AIdx m g
  Y := YIdx m g
  Xvar := ⟨XIdx m g, XEquiv m g⟩
  hDbool := AEquiv m g
  hYreal := YEquiv m g
  hDY := by
    intro h; have := congrArg Subtype.val h
    simp only [AIdx, YIdx] at this; exact absurd this (by decide)
  hDX := by
    intro h; have := congrArg Subtype.val h
    simp only [AIdx, XIdx] at this; exact absurd this (by decide)
  hYX := by
    intro h; have := congrArg Subtype.val h
    simp only [YIdx, XIdx] at this; exact absurd this (by decide)

end DGP

end Causalean.Estimation.MinimaxATE.Causal
