/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.BackdoorCriterion
import Causalean.SCM.Do.Rule2AE

/-!
# Do-calculus derivation helpers (identification toolkit, Layer 2)

Graphical-side helpers that turn a `backdoorCriterion` into the d-separation /
non-descendance facts that the kernel-level do-calculus rules consume, plus the
Rule-2 *applicator* that hides the whole plumbing.  These are the lemmas that the
backdoor and frontdoor identification proofs previously rebuilt inline (≈40 lines
of `have` blocks each).  Factoring them out lets an identification proof name the
criterion and read off the graphical premises — or the entire Rule-2 conclusion —
in one call.

* `disjoint_fixed_observed` — a standing structural fact: an SCM's fixed and
  observed node sets are disjoint.
* `backdoorCriterion_dSep_fixSet` — criterion (ii) extended to the
  post-intervention fixed nodes (the conditioning set `Rule 2` wants).
* `backdoorCriterion_W_nonDesc` / `backdoorCriterion_W_nonDescM1` — criterion (i)
  in the two non-ancestry forms the Rule-2 witness transfer consumes.
* `backdoor_rule2_ae` — the **Rule-2 applicator**: from a `backdoorCriterion`
  (plus overlap + positivity) it produces the a.e. `obsCondKernel` do/obs identity
  directly, deriving the three graphical premises internally.  This is the
  one-call replacement for the criterion→premises→`do_rule2_kernel` sequence.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
-- Genuine per-node primitives; the Rule-2 witness's typeclass zoo derives from these.
variable [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]

open scoped MeasureTheory ProbabilityTheory

/-- **Fixed and observed node sets of an SCM are disjoint.**

    A node cannot be both a parameter (fixed) and a random/observed coordinate. -/
theorem disjoint_fixed_observed (M : Causalean.SCM N Ω) :
    Disjoint M.fixed M.observed := by
  rw [Finset.disjoint_left]
  intro x hxF hxO
  obtain ⟨n, rfl⟩ := M.fixed_is_fixed x hxF
  obtain ⟨m, hm⟩ := M.observed_is_random _ hxO
  cases hm

/-- **Backdoor criterion (ii), extended to the post-intervention fixed nodes.**

    From the splitMono d-separation in the criterion, the post-intervention graph
    `M.fixSet X` d-separates `Y` from `X.image .random` given
    `Z ∪ (M.fixSet X).fixed`.  This is the exact conditioning set that the
    kernel-level Rule 2 (`do_rule2_kernel`) consumes. -/
theorem backdoorCriterion_dSep_fixSet
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (h_bd : M.toSWIGGraph.backdoorCriterion X hObs hFix Y Z) :
    (M.fixSet X hObs hFix).dag.dSep
      Y (X.image SWIGNode.random) (Z ∪ (M.fixSet X hObs hFix).fixed) := by
  have h_step1 :
      (M.fixSet X hObs hFix).dag.dSep
        Y (X.image SWIGNode.random) (Z ∪ X.image SWIGNode.fixed) := h_bd.2.2.2.2
  have h_disj_obs_fixed : Disjoint M.fixed M.observed := disjoint_fixed_observed M
  have h_disj_mfixed_Y : Disjoint M.fixed Y := h_disj_obs_fixed.mono_right hY
  have h_disj_mfixed_Xr : Disjoint M.fixed (X.image SWIGNode.random) :=
    h_disj_obs_fixed.mono_right hXr
  have hRoots :
      ∀ r ∈ M.fixed, ∀ u, ¬ (M.fixSet X hObs hFix).dag.edge u r := by
    intro r hr u he
    have hs_ds : r ∈ (M.fixSet X hObs hFix).fixed :=
      SCM.fixSet_fixed_subset M X hObs hFix hr
    have hroot := (M.fixSet X hObs hFix).fixed_are_roots r hs_ds
    have hmem : u ∈ (M.fixSet X hObs hFix).dag.parents r :=
      (M.fixSet X hObs hFix).dag.mem_parents.mpr he
    rw [hroot] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  have h_step2 :
      (M.fixSet X hObs hFix).dag.dSep
        Y (X.image SWIGNode.random)
        ((Z ∪ X.image SWIGNode.fixed) ∪ M.fixed) :=
    DAG.dSep_union_roots_right _ h_step1 hRoots h_disj_mfixed_Y h_disj_mfixed_Xr
  have h_cond_rewrite :
      (Z ∪ X.image SWIGNode.fixed) ∪ M.fixed
        = Z ∪ (M.fixSet X hObs hFix).fixed := by
    rw [SCM.fixSet_fixed]; ext x; simp only [Finset.mem_union]; tauto
  rw [← h_cond_rewrite]; exact h_step2

/-- **Backdoor criterion (i), post-intervention non-descendance form.**

    No adjustment node `v ∈ Z` is a descendant of any intervened fixed node
    `SWIGNode.fixed x` (`x ∈ X`) in the post-intervention graph `M.fixSet X`. -/
theorem backdoorCriterion_W_nonDesc
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (h_bd : M.toSWIGGraph.backdoorCriterion X hObs hFix Y Z) :
    ∀ x ∈ X, ∀ v ∈ Z,
      ¬ (M.fixSet X hObs hFix).dag.isAncestor (SWIGNode.fixed x) v := by
  intro x hx v hv hanc
  have hanc_base : M.toSWIGGraph.dag.isAncestor (SWIGNode.random x) v :=
    SCM.fixSet_isAncestor_fixed_forward M X hObs hFix hx hanc
  exact h_bd.2.2.2.1 v hv x hx hanc_base

/-- **Backdoor criterion (i), base-graph non-descendance form.**

    No adjustment node `w ∈ Z` is a base-graph descendant of any treatment random
    node `SWIGNode.random D` (`D ∈ X`).  This is criterion (i) reshaped to the
    argument order the cross-model Rule-2 witness transfer consumes. -/
theorem backdoorCriterion_W_nonDescM1
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (h_bd : M.toSWIGGraph.backdoorCriterion X hObs hFix Y Z) :
    ∀ D ∈ X, ∀ w ∈ Z, ¬ M.dag.isAncestor (SWIGNode.random D) w :=
  fun D hD w hw => h_bd.2.2.2.1 w hw D hD

/-- **Rule-2 applicator (backdoor form).**

    From a `backdoorCriterion X … Y Z` (plus joint overlap and product-level
    positivity), the post-`do(X)` `Y | Z`-conditional kernel agrees, for
    `(νX ⊗ₘ μZ)`-almost-every treatment/adjustment pair `(t, z)`, with the
    observational `Y | (X.random ∪ Z)`-conditional at the filled point.  This is
    exactly the conclusion of `obsCondKernel_fixSet_eq_ae_witness`, but it consumes
    the criterion directly: the three graphical premises (`dSep`, and the two
    non-descendance forms) are derived internally via `backdoorCriterion_dSep_fixSet`
    / `backdoorCriterion_W_nonDesc` / `backdoorCriterion_W_nonDescM1`.  An
    identification proof therefore invokes Rule 2 in one line from the criterion,
    instead of rebuilding the graphical ledger and threading it into the raw rule. -/
theorem backdoor_rule2_ae
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (hXrZ : X.image SWIGNode.random ∪ Z ⊆ M.observed)
    (hDisj_YXr : Disjoint Y (X.image SWIGNode.random))
    (hDisj_XrZ : Disjoint (X.image SWIGNode.random) Z)
    (h_bd : M.toSWIGGraph.backdoorCriterion X hObs hFix Y Z)
    (s0 : M.FixedValues)
    (hOverlap : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M X hObs hFix Z hXrZ s)
    (hPositivity_ae :
      (((M.obsKernel s0).map (valuesProjection hXr) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            ((M.obsKernel s0).map (valuesProjection hZ))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ ((M.obsKernel s0).map (valuesProjection hXrZ))) :
    ∀ᵐ p ∂((M.obsKernel s0).map (valuesProjection hXr) ⊗ₘ
            ProbabilityTheory.Kernel.const _
              ((M.obsKernel s0).map (valuesProjection hZ))),
      (M.fixSet X hObs hFix).obsCondKernel Y Z
          ((SCM.fixSet_observed M X hObs hFix).symm ▸ hY)
          ((SCM.fixSet_observed M X hObs hFix).symm ▸ hZ)
          (M.fixSetExtend X hObs hFix s0 p.1, p.2)
      = M.obsCondKernel Y (X.image SWIGNode.random ∪ Z) hY hXrZ
          (s0, valuesUnionMk p.1 p.2) :=
  SCM.obsCondKernel_fixSet_eq_ae_witness M X hObs hFix Y Z hY hZ hXr hXrZ
    hDisj_YXr hDisj_XrZ
    (backdoorCriterion_dSep_fixSet M X hObs hFix Y Z hY hXr h_bd)
    (backdoorCriterion_W_nonDesc M X hObs hFix Y Z h_bd)
    (backdoorCriterion_W_nonDescM1 M X hObs hFix Y Z h_bd)
    s0 hOverlap hPositivity_ae

end SCM

end Causalean
