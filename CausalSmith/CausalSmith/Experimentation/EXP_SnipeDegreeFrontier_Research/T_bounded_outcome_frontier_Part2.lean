import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.HellingerAffinity
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.HeadlineSupport
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.MinimaxRisk
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.T_bounded_outcome_frontier_Part1

/-!
# Exact risks on the complete-block design

Evaluates every risk functional appearing in the frontier theorem exactly on the
complete-block interaction graph.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
open Causalean.Stat
set_option maxHeartbeats 3000000 in
-- The proof compares four conditionally-complete suprema extensionally.
/-- Complete blocks attain the sharp SNIPE upper bound in both model classes,
for the fixed graph and for the unrestricted worst risk. -/
lemma completeBlock_all_risks_exact
    (n d β : ℕ) (B p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hβ : 1 ≤ β) (hB : 0 ≤ B) :
    1 ≤ d → d ∣ n →
      let m := n / d
      worstRiskFixedGraph (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          (blockGraph n d) d β B (snipeEstimator β p) =
          B ^ 2 * blockEnergy β p d / m ∧
      worstRiskBddFixedGraph (V := Fin n) p
          (le_of_lt hp0) (le_of_lt hp1)
          (blockGraph n d) d β B (snipeEstimator β p) =
          B ^ 2 * blockEnergy β p d / m ∧
      worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) =
          B ^ 2 * blockEnergy β p d / m ∧
      worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) =
          B ^ 2 * blockEnergy β p d / m ∧
      B ^ 2 * blockEnergy β p d / m =
          B ^ 2 * (d : ℝ) * blockEnergy β p d / n := by
  classical
  intro hd hdiv
  dsimp only
  let m := blockCount n d
  let A := blockEnergy β p d
  let target := B ^ 2 * A / m
  have hdn : d ≤ n :=
    Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv
  have hm : 0 < m := blockCount_pos n d hn hd hdn
  have hscale :
      target = B ^ 2 * (d : ℝ) * A / n := by
    have hncast : (n : ℝ) = (m : ℝ) * d := by
      norm_cast
      simpa [m, blockCount, Nat.mul_comm] using
        (Nat.div_mul_cancel hdiv).symm
    dsimp [target]
    rw [hncast]
    field_simp
  have hfixed : worstRiskFixedGraph (V := Fin n) p
      (le_of_lt hp0) (le_of_lt hp1) (blockGraph n d) d β B
      (snipeEstimator β p) = target := by
    by_cases hBpos : 0 < B
    · let w := canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv
      have heq (b : Fin m) :
          blockExtremal (blockGraph n d) d β p
              (le_of_lt hp0) (le_of_lt hp1) w
              (completeBlockUnits n d b) =
            (d : ℝ) ^ 2 * A := by
        apply le_antisymm
        · simpa [w, m, A] using
            canonical_completeBlock_blockExtremal_upper
              n d β p hp0 hp1 hn hd hdiv b
        · simpa [w, m, A] using
            completeBlock_blockExtremal_lower
              n d β p hp0 hp1 hn hd hdiv w b
      have hw :
          locLinWorstRisk (blockGraph n d) d β B p
              (le_of_lt hp0) (le_of_lt hp1) w = target := by
        rw [locLinWorstRisk_exact_blockExtremal
          n d β B p hBpos (le_of_lt hp0) (le_of_lt hp1)
          hn hd hdiv w]
        rw [show
            (∑ b : Fin m,
              blockExtremal (blockGraph n d) d β p
                (le_of_lt hp0) (le_of_lt hp1) w
                (completeBlockUnits n d b)) =
              ∑ _b : Fin m, (d : ℝ) ^ 2 * A by
          apply Finset.sum_congr rfl
          intro b hb
          exact heq b]
        simpa [target, m, A] using
          completeBlock_benchmark_algebra n d B A hn hd hdiv
      have hest (z : Fin n → Bool) (y : Fin n → ℝ) :
          snipeEstimator β p
              (fun j i => decide (blockGraph n d j i)) z y =
            locLinEstimator (blockGraph n d) d β p
              (le_of_lt hp0) (le_of_lt hp1) w z y := by
        unfold snipeEstimator locLinEstimator
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp [w, canonicalLocLinWeights]
        ring
      have hfixedUpper :
          worstRiskFixedGraph (V := Fin n) p
              (le_of_lt hp0) (le_of_lt hp1) (blockGraph n d) d β B
              (snipeEstimator β p) ≤ target := by
        unfold worstRiskFixedGraph
        apply csSup_le
        · let M0 : ModelClass (Fin n) d β B :=
            { edge := blockGraph n d
              decEdge := Classical.decRel _
              coef := fun _ _ => 0
              supported := by simp
              degree_le := blockGraph_degree_le n d hd
              low_order := by simp [LowOrder]
              mass_le := by
                intro i
                simpa [BoundedCoeffMass] using hB }
          exact ⟨riskAt p (le_of_lt hp0) (le_of_lt hp1) M0
            (snipeEstimator β p), M0, rfl, rfl⟩
        · rintro r ⟨M, hG, rfl⟩
          exact (riskAt_snipe_le p hp0 hp1 M).trans (by
            simpa [A] using hscale.symm.le)
      have hlocal_le_fixed :
          locLinWorstRisk (blockGraph n d) d β B p
              (le_of_lt hp0) (le_of_lt hp1) w ≤
            worstRiskFixedGraph (V := Fin n) p
              (le_of_lt hp0) (le_of_lt hp1) (blockGraph n d) d β B
              (snipeEstimator β p) := by
        unfold locLinWorstRisk worstRiskFixedGraph
        apply csSup_le
        · let L0 : LocLinSchedClass (blockGraph n d) d β B :=
            { coef := fun _ _ => 0
              supported := by simp
              low_order := by simp [LowOrder]
              mass_le := by
                intro i
                simpa [BoundedCoeffMass] using hB }
          exact ⟨locLinRiskAt (blockGraph n d) d β B p
            (le_of_lt hp0) (le_of_lt hp1) w L0, L0, rfl⟩
        · rintro r ⟨L, rfl⟩
          let M : ModelClass (Fin n) d β B :=
            { edge := blockGraph n d
              decEdge := Classical.decRel _
              coef := L.coef
              supported := L.supported
              degree_le := blockGraph_degree_le n d hd
              low_order := by
                intro i S hcard
                exact L.low_order i S
                  (lt_of_le_of_lt (min_le_left _ _) hcard)
              mass_le := L.mass_le }
          apply le_csSup
          · refine ⟨target, ?_⟩
            rintro _ ⟨N, hNG, rfl⟩
            exact (riskAt_snipe_le p hp0 hp1 N).trans (by
              simpa [A] using hscale.symm.le)
          · refine ⟨M, rfl, ?_⟩
            unfold riskAt locLinRiskAt
            have hedge : edgeFn M =
                fun j i => decide (blockGraph n d j i) := by rfl
            have hf :
                (fun z => locLinEstimator (blockGraph n d) d β p
                    (le_of_lt hp0) (le_of_lt hp1) w z
                    (obsOutcome (blockGraph n d) L.coef z)) =
                  fun z => snipeEstimator β p (edgeFn M) z
                    (obsOutcome M.edge M.coef z) := by
              funext z
              rw [hedge]
              exact (hest z
                (obsOutcome (blockGraph n d) L.coef z)).symm
            dsimp only
            rw [hf]
      exact le_antisymm hfixedUpper (hw ▸ hlocal_le_fixed)
    · have hB0 : B = 0 := by linarith
      subst B
      dsimp [target]
      rw [zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div]
      change worstRiskFixedGraph (V := Fin n) p
        (le_of_lt hp0) (le_of_lt hp1) (blockGraph n d) d β 0
        (snipeEstimator β p) = 0
      let M0 : ModelClass (Fin n) d β 0 :=
        { edge := blockGraph n d
          decEdge := Classical.decRel _
          coef := fun _ _ => 0
          supported := by simp
          degree_le := blockGraph_degree_le n d hd
          low_order := by simp [LowOrder]
          mass_le := by simp [BoundedCoeffMass] }
      have hbdd : BddAbove {r : ℝ | ∃ M : ModelClass (Fin n) d β 0,
          M.edge = blockGraph n d ∧
            r = riskAt p (le_of_lt hp0) (le_of_lt hp1) M
              (snipeEstimator β p)} := by
        refine ⟨0, ?_⟩
        rintro r ⟨M, hG, rfl⟩
        simpa using riskAt_snipe_le p hp0 hp1 M
      apply le_antisymm
      · unfold worstRiskFixedGraph
        apply csSup_le
        · exact ⟨riskAt p (le_of_lt hp0) (le_of_lt hp1) M0
            (snipeEstimator β p), M0, rfl, rfl⟩
        · rintro r ⟨M, hG, rfl⟩
          simpa using riskAt_snipe_le p hp0 hp1 M
      · have hrisk : 0 ≤ riskAt p (le_of_lt hp0) (le_of_lt hp1) M0
            (snipeEstimator β p) := by
          unfold riskAt
          exact
            (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
              (fun _ => le_of_lt hp1)).mse_nonneg _ _
        unfold worstRiskFixedGraph
        exact hrisk.trans (le_csSup hbdd ⟨M0, rfl, rfl⟩)
  have hglobalUpper :
      worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) ≤ target := by
    rw [hscale]
    simpa [A] using worstRisk_snipe_le (V := Fin n)
      p hp0 hp1 d β B
  have hfixed_le_global :
      worstRiskFixedGraph (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          (blockGraph n d) d β B (snipeEstimator β p) ≤
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) := by
    unfold worstRiskFixedGraph worstRisk
    apply csSup_le
    · let M0 : ModelClass (Fin n) d β B :=
        { edge := blockGraph n d
          decEdge := Classical.decRel _
          coef := fun _ _ => 0
          supported := by simp
          degree_le := blockGraph_degree_le n d hd
          low_order := by simp [LowOrder]
          mass_le := by
            intro i
            simpa [BoundedCoeffMass] using hB }
      exact ⟨riskAt p (le_of_lt hp0) (le_of_lt hp1) M0
        (snipeEstimator β p), M0, rfl, rfl⟩
    · rintro r ⟨M, hG, rfl⟩
      apply le_csSup
      · refine ⟨target, ?_⟩
        rintro _ ⟨N, rfl⟩
        exact (riskAt_snipe_le p hp0 hp1 N).trans (by
          simpa [A] using hscale.symm.le)
      · exact Set.mem_range_self M
  have hglobal :
      worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) = target :=
    le_antisymm hglobalUpper (hfixed ▸ hfixed_le_global)
  have hbddGlobalUpper :
      worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) ≤ target := by
    rw [hscale]
    simpa [A] using worstRiskBdd_snipe_le (V := Fin n)
      p hp0 hp1 d β B
  have hfixed_le_bddFixed :
      worstRiskFixedGraph (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          (blockGraph n d) d β B (snipeEstimator β p) ≤
        worstRiskBddFixedGraph (V := Fin n) p
          (le_of_lt hp0) (le_of_lt hp1) (blockGraph n d) d β B
          (snipeEstimator β p) := by
    unfold worstRiskFixedGraph worstRiskBddFixedGraph
    apply csSup_le
    · let M0 : ModelClass (Fin n) d β B :=
        { edge := blockGraph n d
          decEdge := Classical.decRel _
          coef := fun _ _ => 0
          supported := by simp
          degree_le := blockGraph_degree_le n d hd
          low_order := by simp [LowOrder]
          mass_le := by
            intro i
            simpa [BoundedCoeffMass] using hB }
      exact ⟨riskAt p (le_of_lt hp0) (le_of_lt hp1) M0
        (snipeEstimator β p), M0, rfl, rfl⟩
    · rintro r ⟨M, hG, rfl⟩
      obtain ⟨N, hEdge, hCoef⟩ :=
        modelClassIncluded_of_coeffMass (V := Fin n) d β B M
      apply le_csSup
      · refine ⟨target, ?_⟩
        rintro _ ⟨N', hN'G, rfl⟩
        exact (riskAtBdd_snipe_le p hp0 hp1 N').trans (by
          simpa [A] using hscale.symm.le)
      · refine ⟨N, ?_, ?_⟩
        · exact hEdge.trans hG
        · have hedge : edgeFn M = edgeFnBdd N := by
            funext j i
            simp [edgeFn, edgeFnBdd, hEdge]
          unfold riskAt riskAtBdd
          rw [hedge, hEdge, hCoef]
  have hbddFixed_le_global :
      worstRiskBddFixedGraph (V := Fin n) p
          (le_of_lt hp0) (le_of_lt hp1) (blockGraph n d) d β B
          (snipeEstimator β p) ≤
        worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) := by
    unfold worstRiskBddFixedGraph worstRiskBdd
    apply csSup_le
    · obtain ⟨M0, hM0G, hM0risk⟩ :
          ∃ M0 : BddOutcomeModelClass (Fin n) d β B,
            M0.edge = blockGraph n d ∧
            riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M0
              (snipeEstimator β p) =
              riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M0
                (snipeEstimator β p) := by
          let L0 : ModelClass (Fin n) d β B :=
            { edge := blockGraph n d
              decEdge := Classical.decRel _
              coef := fun _ _ => 0
              supported := by simp
              degree_le := blockGraph_degree_le n d hd
              low_order := by simp [LowOrder]
              mass_le := by
                intro i
                simpa [BoundedCoeffMass] using hB }
          obtain ⟨M0, hEdge, hCoef⟩ :=
            modelClassIncluded_of_coeffMass (V := Fin n) d β B L0
          exact ⟨M0, hEdge, rfl⟩
      exact ⟨riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M0
        (snipeEstimator β p), M0, hM0G, rfl⟩
    · rintro r ⟨M, hG, rfl⟩
      apply le_csSup
      · refine ⟨target, ?_⟩
        rintro _ ⟨N, rfl⟩
        exact (riskAtBdd_snipe_le p hp0 hp1 N).trans (by
          simpa [A] using hscale.symm.le)
      · exact Set.mem_range_self M
  have hbddFixed :
      worstRiskBddFixedGraph (V := Fin n) p
          (le_of_lt hp0) (le_of_lt hp1) (blockGraph n d) d β B
          (snipeEstimator β p) = target := by
    apply le_antisymm
    · exact hbddFixed_le_global.trans hbddGlobalUpper
    · rw [← hfixed]
      exact hfixed_le_bddFixed
  have hbddGlobal :
      worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B (snipeEstimator β p) = target := by
    apply le_antisymm
    · exact hbddGlobalUpper
    · rw [← hbddFixed]
      exact hbddFixed_le_global
  simpa [target, A, m, blockCount] using
    And.intro hfixed
      (And.intro hbddFixed
        (And.intro hglobal (And.intro hbddGlobal hscale)))

/-- An estimator's worst-case mean-squared error over the bounded-outcome model class is
unchanged when the assignment probability, its bounds, model-class parameters, and estimator
are replaced by equal values. -/
add_decl_doc worstRiskBdd.congr_simp

/-- The coefficient-mass worst-case risk restricted to a fixed graph is unchanged when the
assignment probability, its bounds, graph, model-class parameters, and estimator are replaced
by equal values. -/
add_decl_doc worstRiskFixedGraph.congr_simp

/-- The bounded-outcome worst-case risk restricted to a fixed graph is unchanged when the
assignment probability, its bounds, graph, model-class parameters, and estimator are replaced
by equal values. -/
add_decl_doc worstRiskBddFixedGraph.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
