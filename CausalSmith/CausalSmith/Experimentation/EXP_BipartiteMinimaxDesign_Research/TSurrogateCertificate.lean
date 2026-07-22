/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: the additive surrogate certificate (positive)

`thm:surrogate-certificate`. In the bounded-degree regime, the additive
degree-dispersion surrogate objective sandwiches the graph-only envelope up to the
constant `C(ε,d̄) = max{1, ε^{-(d̄-1)}}`, yielding an observable constant-factor
certificate `α_cert ≤ C(ε,d̄)`.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Surrogate
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.TConvexDesign
import Mathlib.Topology.Order.Compact

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: surrogateObjective_continuousOn_feasible
/-- The additive surrogate objective is continuous on the feasible design class under
strict overlap. -/
lemma surrogateObjective_continuousOn_feasible
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε0 : 0 < ε) :
    ContinuousOn E.surrogateObjective (feasibleSet (I := I) ε B) := by
  classical
  let s : Set (I → ℝ) := feasibleSet (I := I) ε B
  unfold BipartiteExperiment.surrogateObjective
  refine continuousOn_finset_sum Finset.univ ?_
  intro k _
  have hpk : ContinuousOn (fun p : I → ℝ => p k) s := (continuous_apply k).continuousOn
  have hp_ne : ∀ p ∈ s, p k ≠ 0 := by
    intro p hp
    exact ne_of_gt (lt_of_lt_of_le hε0 ((show FeasibleDesign ε B p from hp).floor k).1)
  have h1mp : ContinuousOn (fun p : I → ℝ => 1 - p k) s := by fun_prop
  have h1mp_ne : ∀ p ∈ s, 1 - p k ≠ 0 := by
    intro p hp
    have hlt : p k < 1 := by
      linarith [((show FeasibleDesign ε B p from hp).floor k).2, hε0]
    linarith
  have hterm1 : ContinuousOn (fun p : I → ℝ => (p k)⁻¹) s := hpk.inv₀ hp_ne
  have hterm2 : ContinuousOn (fun p : I → ℝ => (1 - p k)⁻¹) s := h1mp.inv₀ h1mp_ne
  exact continuousOn_const.mul (hterm1.add hterm2)

-- @node: optimalDesign_feasible_minimizes
/-- The envelope-optimal selector is feasible and minimizes `varEnvelope` on the
feasible set whenever the budget domain is admissible. -/
lemma optimalDesign_feasible_minimizes
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hB : BudgetAdmissible (I := I) ε B) :
    FeasibleDesign ε B (optimalDesign E ε B) ∧
      ∀ q, FeasibleDesign ε B q →
        E.varEnvelope (optimalDesign E ε B) ≤ E.varEnvelope q := by
  classical
  have hcv := convex_design E ε B hε0 hε2 hB.1 hB.2
  obtain ⟨pstar, hpstar, hmin⟩ := hcv.2.2.2.2.1
  let hex : ∃ p, p ∈ feasibleSet (I := I) ε B ∧
      ∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope p ≤ E.varEnvelope q :=
    ⟨pstar, hpstar, hmin⟩
  have hsel : optimalDesign E ε B = hex.choose := by
    unfold optimalDesign
    rw [dif_pos hex]
  have hspec := hex.choose_spec
  constructor
  · rw [hsel]
    simpa [feasibleSet] using hspec.1
  · intro q hq
    rw [hsel]
    exact hspec.2 q (by simpa [feasibleSet] using hq)

-- @node: surrogateDesign_feasible_minimizes
/-- The surrogate selector is feasible and minimizes `surrogateObjective` on the
feasible set whenever the budget domain is admissible. -/
lemma surrogateDesign_feasible_minimizes
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hB : BudgetAdmissible (I := I) ε B) :
    FeasibleDesign ε B (surrogateDesign E ε B) ∧
      ∀ q, FeasibleDesign ε B q →
        E.surrogateObjective (surrogateDesign E ε B) ≤ E.surrogateObjective q := by
  classical
  have hcv := convex_design E ε B hε0 hε2 hB.1 hB.2
  have hmin_exists :=
    hcv.2.1.exists_isMinOn hcv.1 (surrogateObjective_continuousOn_feasible E ε B hε0)
  obtain ⟨pstar, hpstar, hmin⟩ := hmin_exists
  let hex : ∃ p, p ∈ feasibleSet (I := I) ε B ∧
      ∀ q ∈ feasibleSet (I := I) ε B, E.surrogateObjective p ≤ E.surrogateObjective q :=
    ⟨pstar, hpstar, hmin⟩
  have hsel : surrogateDesign E ε B = hex.choose := by
    unfold surrogateDesign
    rw [dif_pos hex]
  have hspec := hex.choose_spec
  constructor
  · rw [hsel]
    simpa [feasibleSet] using hspec.1
  · intro q hq
    rw [hsel]
    exact hspec.2 q (by simpa [feasibleSet] using hq)

-- @node: thm:surrogate-certificate
/-- **Surrogate certificate.** With `C(ε,d̄) = max{1, ε^{-(d̄-1)}}`, the additive
surrogate objective `A` and the normalized envelope `V_env/4` satisfy the uniform
sandwich `A(p) ≤ V_env(p)/4 ≤ C(ε,d̄)·A(p)` over feasible `p`, and consequently the
observable approximation ratio is bounded by `C(ε,d̄)`. The selector feasibility
and optimality facts are derived from compact attainment under the regularity
condition `BudgetAdmissible ε B`, rather than assumed as hypotheses. -/
theorem surrogate_certificate
    (E : BipartiteExperiment I O) (ε B dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hdeg : BoundedOutcomeDegree E dbar)
    (hB : BudgetAdmissible (I := I) ε B) :
    (∀ q, FeasibleDesign ε B q →
        E.surrogateObjective q ≤ E.varEnvelope q / 4 ∧
        E.varEnvelope q / 4 ≤ max 1 (ε ^ (-(dbar - 1))) * E.surrogateObjective q) ∧
    approxRatio E ε B ≤ max 1 (ε ^ (-(dbar - 1))) := by
  classical
  let C : ℝ := max 1 (ε ^ (-(dbar - 1)))
  have hopt := optimalDesign_feasible_minimizes E ε B hε0 hε2 hB
  have hsurr := surrogateDesign_feasible_minimizes E ε B hε0 hε2 hB
  have hCnonneg : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
  have hsand : ∀ q, FeasibleDesign ε B q →
      E.surrogateObjective q ≤ E.varEnvelope q / 4 ∧
      E.varEnvelope q / 4 ≤ C * E.surrogateObjective q := by
    intro q hq
    constructor
    · rw [surrogateObjective_eq_pairAverage E q, varEnvelope_div_four_eq_pairSum E q]
      refine Finset.sum_le_sum ?_
      intro i _
      refine Finset.sum_le_sum ?_
      intro j _
      have hpair := pairAverage_le_envelopeKernel E ε B hε0 q hq i j
      have hn : 0 ≤ (Fintype.card O : ℝ)⁻¹ := by positivity
      calc
        ∑ k ∈ E.shared i j,
          (Fintype.card O : ℝ)⁻¹ *
            (((E.shared i j).card : ℝ)⁻¹ * ((q k)⁻¹ + (1 - q k)⁻¹))
            = (Fintype.card O : ℝ)⁻¹ *
                (((E.shared i j).card : ℝ)⁻¹ *
                  (∑ k ∈ E.shared i j, ((q k)⁻¹ + (1 - q k)⁻¹))) := by
              rw [← Finset.mul_sum]
              rw [← Finset.mul_sum]
        _ ≤ (Fintype.card O : ℝ)⁻¹ * (E.r1 q i j + E.r0 q i j + 2 * E.r10 i j) :=
              mul_le_mul_of_nonneg_left hpair hn
    · rw [varEnvelope_div_four_eq_pairSum E q, surrogateObjective_eq_pairAverage E q]
      calc
        ∑ i : O, ∑ j : O,
            (Fintype.card O : ℝ)⁻¹ * (E.r1 q i j + E.r0 q i j + 2 * E.r10 i j)
            ≤ ∑ i : O, ∑ j : O, C * (∑ k ∈ E.shared i j,
                (Fintype.card O : ℝ)⁻¹ *
                  (((E.shared i j).card : ℝ)⁻¹ * ((q k)⁻¹ + (1 - q k)⁻¹))) := by
              refine Finset.sum_le_sum ?_
              intro i _
              refine Finset.sum_le_sum ?_
              intro j _
              have hpair :=
                envelopeKernel_le_certificate_pairAverage E ε B dbar hε0 hε2 hdeg q hq i j
              have hn : 0 ≤ (Fintype.card O : ℝ)⁻¹ := by positivity
              calc
                (Fintype.card O : ℝ)⁻¹ * (E.r1 q i j + E.r0 q i j + 2 * E.r10 i j)
                    ≤ (Fintype.card O : ℝ)⁻¹ *
                        (C * (((E.shared i j).card : ℝ)⁻¹ *
                          (∑ k ∈ E.shared i j, ((q k)⁻¹ + (1 - q k)⁻¹)))) :=
                      mul_le_mul_of_nonneg_left hpair hn
                _ = C * (∑ k ∈ E.shared i j,
                  (Fintype.card O : ℝ)⁻¹ *
                    (((E.shared i j).card : ℝ)⁻¹ * ((q k)⁻¹ + (1 - q k)⁻¹))) := by
                      rw [← Finset.mul_sum]
                      rw [← Finset.mul_sum]
                      ring
        _ = C * (∑ i : O, ∑ j : O, ∑ k ∈ E.shared i j,
            (Fintype.card O : ℝ)⁻¹ *
              (((E.shared i j).card : ℝ)⁻¹ * ((q k)⁻¹ + (1 - q k)⁻¹))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
  refine ⟨by simpa [C] using hsand, ?_⟩
  by_cases henv : 0 < envMin E ε B
  · unfold approxRatio
    rw [if_pos henv]
    change E.varEnvelope (surrogateDesign E ε B) / envMin E ε B ≤ C
    have hsurr_sand := hsand (surrogateDesign E ε B) hsurr.1
    have hopt_sand := hsand (optimalDesign E ε B) hopt.1
    have hA_le : E.surrogateObjective (surrogateDesign E ε B) ≤
        E.surrogateObjective (optimalDesign E ε B) := hsurr.2 _ hopt.1
    have hCA_le : C * E.surrogateObjective (surrogateDesign E ε B) ≤
        C * E.surrogateObjective (optimalDesign E ε B) :=
      mul_le_mul_of_nonneg_left hA_le hCnonneg
    have hCF_le : C * E.surrogateObjective (optimalDesign E ε B) ≤
        C * (E.varEnvelope (optimalDesign E ε B) / 4) :=
      mul_le_mul_of_nonneg_left hopt_sand.1 hCnonneg
    have hF_le : E.varEnvelope (surrogateDesign E ε B) / 4 ≤
        C * (E.varEnvelope (optimalDesign E ε B) / 4) :=
      hsurr_sand.2.trans (hCA_le.trans hCF_le)
    have hV_le : E.varEnvelope (surrogateDesign E ε B) ≤
        C * E.varEnvelope (optimalDesign E ε B) := by
      nlinarith
    have hden : 0 < E.varEnvelope (optimalDesign E ε B) := by
      simpa [envMin] using henv
    exact (div_le_iff₀ hden).mpr (by simpa [envMin] using hV_le)
  · unfold approxRatio
    rw [if_neg henv]
    exact le_max_left _ _

end CausalSmith.Experimentation.BipartiteMinimaxDesign
