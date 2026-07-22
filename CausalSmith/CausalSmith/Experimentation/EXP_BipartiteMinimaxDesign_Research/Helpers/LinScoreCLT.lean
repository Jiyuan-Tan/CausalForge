/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Linear-score dependency graph for the bipartite minimax design
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Linearization
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DependencyCLT
import Causalean.Experimentation.DesignBased.ProductMeasure
import Causalean.Experimentation.DesignBased.GaussianCDF
import Mathlib.Algebra.Order.Floor.Semiring

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped BigOperators Topology
open Finset Filter MeasureTheory ProbabilityTheory
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference
open Causalean.SteinMethod

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

-- @node: linScore-outcome-block
/-- The intervention-coordinate block supporting a finite tuple of outcome-side
linear scores. -/
noncomputable def linScoreOutcomeBlock (E : BipartiteExperiment I O) (A : Finset O) :
    Finset I :=
  A.biUnion E.N

-- @node: linScore-expT-depends-on-neighborhood
lemma expT_depends_on_neighborhood (E : BipartiteExperiment I O) (i : O)
    {z z' : I → Bool} (h : ∀ k ∈ E.N i, z k = z' k) :
    E.expT z i = E.expT z' i := by
  classical
  unfold BipartiteExperiment.expT
  exact Finset.prod_congr rfl (fun k hk => by rw [h k hk])

-- @node: linScore-expC-depends-on-neighborhood
lemma expC_depends_on_neighborhood (E : BipartiteExperiment I O) (i : O)
    {z z' : I → Bool} (h : ∀ k ∈ E.N i, z k = z' k) :
    E.expC z i = E.expC z' i := by
  classical
  unfold BipartiteExperiment.expC
  exact Finset.prod_congr rfl (fun k hk => by rw [h k hk])

-- @node: linScore-depends-on-neighborhood
/-- An outcome's linearization score depends only on the assignments in that outcome's intervention neighborhood. -/
lemma linScore_depends_on_neighborhood (E : BipartiteExperiment I O) (p : I → ℝ) (i : O)
    {z z' : I → Bool} (h : ∀ k ∈ E.N i, z k = z' k) :
    E.linScore p z i = E.linScore p z' i := by
  unfold BipartiteExperiment.linScore
  rw [expT_depends_on_neighborhood E i h, expC_depends_on_neighborhood E i h]

-- @node: linScore-block-disjoint
/-- If no outcome in one block is identical to or overlaps an outcome in another block, the two blocks' supporting intervention neighborhoods are disjoint. -/
lemma disjoint_linScoreOutcomeBlock_of_no_overlap (E : BipartiteExperiment I O)
    {A B : Finset O}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ (a = b ∨ 0 < (E.shared a b).card)) :
    Disjoint (linScoreOutcomeBlock E A) (linScoreOutcomeBlock E B) := by
  classical
  rw [Finset.disjoint_left]
  intro k hkA hkB
  rw [linScoreOutcomeBlock, Finset.mem_biUnion] at hkA hkB
  rcases hkA with ⟨a, haA, hkNa⟩
  rcases hkB with ⟨b, hbB, hkNb⟩
  exact hAB a haA b hbB (Or.inr (Finset.card_pos.mpr ⟨k, by
    simpa [BipartiteExperiment.shared] using And.intro hkNa hkNb⟩))

-- `indepFun_prodDesign_of_depends_on_disjoint_blocks` promoted to
-- `Causalean.Experimentation.DesignBased.ProductMeasure` (imported above); resolved via the open
-- `Causalean.Experimentation.DesignBased` namespace.

-- @node: linScore-depgraph
/-- The overlap relation is a dependency graph for linear scores under the
heterogeneous Bernoulli product design. -/
noncomputable def linScoreDepGraph
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (E : BipartiteExperiment I O) (D : FiniteDesign (I → Bool)) (p : I → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1) :
    DepGraph (fun i z => E.linScore p z i) D.toMeasure where
  G i j := i = j ∨ 0 < (E.shared i j).card
  decG := inferInstance
  refl i := Or.inl rfl
  symm i j h := by
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by simpa [BipartiteExperiment.shared, Finset.inter_comm] using h)
  meas i := measurable_of_finite _
  indep A B hAB := by
    rw [hBern]
    unfold bernoulliDesign
    have hST : Disjoint (linScoreOutcomeBlock E A) (linScoreOutcomeBlock E B) :=
      disjoint_linScoreOutcomeBlock_of_no_overlap E hAB
    refine indepFun_prodDesign_of_depends_on_disjoint_blocks
      (fun k => coinDesign (p k) (hp0 k) (hp1 k)) hST
      (fun z => fun k : A => E.linScore p z k)
      (fun z => fun k : B => E.linScore p z k) ?_ ?_
    · intro z z' hzz
      funext k
      exact linScore_depends_on_neighborhood E p k (fun l hl => hzz l (by
        rw [linScoreOutcomeBlock, Finset.mem_biUnion]
        exact ⟨k, k.property, hl⟩))
    · intro z z' hzz
      funext k
      exact linScore_depends_on_neighborhood E p k (fun l hl => hzz l (by
        rw [linScoreOutcomeBlock, Finset.mem_biUnion]
        exact ⟨k, k.property, hl⟩))

-- @node: linScore-depgraph-degree
/-- The dependency-graph neighborhood of any outcome has size at most the ceiling of the overlap-dependency bound plus one. -/
lemma linScoreDepGraph_degree_le
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (E : BipartiteExperiment I O) (D : FiniteDesign (I → Bool)) (p : I → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1)
    {Dbar : ℝ} (hdep : BoundedOverlapDependency E Dbar) (i : O) :
    ((linScoreDepGraph E D p hp0 hp1 hBern).nbhd i).card ≤ Nat.ceil Dbar + 1 := by
  classical
  have hsub : (linScoreDepGraph E D p hp0 hp1 hBern).nbhd i ⊆ insert i (E.overlapNbrs i) := by
    intro j hj
    rw [DepGraph.mem_nbhd_iff] at hj
    rcases hj with hji | hover
    · simp [hji]
    · simp [BipartiteExperiment.overlapNbrs, Finset.card_pos.mp hover]
  have hcard : ((linScoreDepGraph E D p hp0 hp1 hBern).nbhd i).card
      ≤ (insert i (E.overlapNbrs i)).card := Finset.card_le_card hsub
  have hoverNat : (E.overlapNbrs i).card ≤ Nat.ceil Dbar := by
    exact Nat.cast_le.mp ((hdep.2 i).trans (Nat.le_ceil Dbar))
  calc
    ((linScoreDepGraph E D p hp0 hp1 hBern).nbhd i).card
        ≤ (insert i (E.overlapNbrs i)).card := hcard
    _ ≤ (E.overlapNbrs i).card + 1 := Finset.card_insert_le _ _
    _ ≤ Nat.ceil Dbar + 1 := Nat.add_le_add_right hoverNat 1

end CausalSmith.Experimentation.BipartiteMinimaxDesign
