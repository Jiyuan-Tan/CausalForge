/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: witnesses attaining the eight lower expressions

Each witness is the primal optimum on the region where its expression is
extremal among the eight. They were located by complementary slackness against
the dual vertices; that derivation is offline scaffolding only, and no duality
theory enters below. Every table is explicit and is checked directly against
nonnegativity, normalization, and the eight marginal equations.

Four of the eight carry a free direction along which the objective is constant.
The free variable is pinned at the largest of its lower bounds, which is feasible
whenever anything is, and is what produces the `max 0 _` in the `bpAux`/`bpUAux`
definitions. Setting those free variables to zero instead yields negative entries
and does not work.

Feasibility is not derivable from the observed cells being nonnegative and summing
to one per instrument value: one obligation is Pearl's instrumental inequality.
The witness theorems therefore take a feasible table as a hypothesis, discharged
at the call site by `latentProb_feasible`.

The eight feasibility proofs share one uniform tactic block, so a given `simp` set
is not exercised by every branch; the unused-argument linter is disabled here
rather than hand-tuning eight copies apart.
-/

import Causalean.PO.ID.Partial.BalkePearl.Attainment.Basic

/-! # Witnesses attaining the Balke-Pearl lower expressions -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

set_option linter.unusedSimpArgs false

/-- Free-variable choice `t` in the witness attaining `bpLowerTerm 0`. -/
noncomputable def bpAux0t (S : POBalkePearlSystem P) : ℝ :=
  max 0 (S.cellProb false false true + S.cellProb false true true - S.cellProb false false false
    - S.cellProb true false false )

/-- Latent table attaining `bpLowerTerm 0`. -/
noncomputable def bpLowerWitness0 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false true
  | false, false, true, false => S.cellProb false false false - S.cellProb false false true -
      S.cellProb false true true + S.cellProb true false false + S.bpAux0t
  | false, true, false, false => S.cellProb false false false - S.cellProb false false true
  | false, true, true, false => -S.cellProb false false false + S.cellProb false false true +
      S.cellProb false true true - S.bpAux0t
  | true, false, true, false => S.cellProb false true false - S.bpAux0t
  | true, false, true, true => -S.cellProb false false false + S.cellProb false false true -
      S.cellProb false true false + S.cellProb false true true - S.cellProb true false false +
      S.cellProb true false true
  | true, true, true, false => S.bpAux0t
  | true, true, true, true => 1 - S.cellProb false false true - S.cellProb false true true -
      S.cellProb true false true
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 0` is feasible on its optimality region. -/
theorem bpLowerWitness0_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 0) :
    BPFeasible S hA S.bpLowerWitness0 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (S.cellProb false false true + S.cellProb false true true -
      S.cellProb false false false - S.cellProb true false false ) with ⟨hmx0, hmc0⟩ | ⟨hmx0,
      hmc0⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness0, bpAux0t, hmx0] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
          linarith
    · simp only [bpLowerWitness0, bpAux0t, hmx0, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness0, bpAux0t, hmx0, dArm, yArm, Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpLowerTerm 0` attains it. -/
theorem bpLowerWitness0_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness0 = S.bpLowerTerm 0 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness0, bpAux0t, bpLowerTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Free-variable choice `v` in the witness attaining `bpLowerTerm 1`. -/
noncomputable def bpAux1v (S : POBalkePearlSystem P) : ℝ :=
  max 0 (S.cellProb false false false - S.cellProb false false true +
    S.cellProb false true false - S.cellProb true false true )

/-- Latent table attaining `bpLowerTerm 1`. -/
noncomputable def bpLowerWitness1 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false false
  | false, false, true, false => -S.cellProb false false false + S.cellProb false false true -
      S.cellProb false true false + S.cellProb true false true + S.bpAux1v
  | false, true, true, false => S.cellProb false true true - S.bpAux1v
  | false, true, true, true => S.cellProb false false false - S.cellProb false false true +
      S.cellProb false true false - S.cellProb false true true + S.cellProb true false false -
      S.cellProb true false true
  | true, false, false, false => -S.cellProb false false false + S.cellProb false false true
  | true, false, true, false => S.cellProb false false false - S.cellProb false false true +
      S.cellProb false true false - S.bpAux1v
  | true, true, true, false => S.bpAux1v
  | true, true, true, true => 1 - S.cellProb false false false - S.cellProb false true false -
      S.cellProb true false false
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 1` is feasible on its optimality region. -/
theorem bpLowerWitness1_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 1) :
    BPFeasible S hA S.bpLowerWitness1 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (S.cellProb false false false - S.cellProb false false true +
      S.cellProb false true false - S.cellProb true false true ) with ⟨hmx0, hmc0⟩ | ⟨hmx0,
      hmc0⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness1, bpAux1v, hmx0] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
          linarith
    · simp only [bpLowerWitness1, bpAux1v, hmx0, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness1, bpAux1v, hmx0, dArm, yArm, Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpLowerTerm 1` attains it. -/
theorem bpLowerWitness1_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness1 = S.bpLowerTerm 1 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness1, bpAux1v, bpLowerTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Free-variable choice `u` in the witness attaining `bpLowerTerm 2`. -/
noncomputable def bpAux2u (S : POBalkePearlSystem P) : ℝ :=
  max 0 (S.cellProb false true true - S.cellProb false true false - S.cellProb true false false
    + S.cellProb true false true )

/-- Free-variable choice `v` in the witness attaining `bpLowerTerm 2`. -/
noncomputable def bpAux2v (S : POBalkePearlSystem P) : ℝ :=
  max 0 (S.cellProb false true true - S.cellProb true false false )

/-- Latent table attaining `bpLowerTerm 2`. -/
noncomputable def bpLowerWitness2 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false false
  | false, false, true, false => -S.cellProb false true true + S.cellProb true false false +
      S.bpAux2v
  | false, true, true, false => S.cellProb false true true - S.bpAux2v
  | true, false, false, false => S.cellProb false true false - S.cellProb false true true +
      S.cellProb true false false - S.cellProb true false true + S.bpAux2u
  | true, false, false, true => -S.cellProb false false false + S.cellProb false false true -
      S.cellProb false true false + S.cellProb false true true - S.cellProb true false false +
      S.cellProb true false true - S.bpAux2u
  | true, false, true, false => S.cellProb false true true - S.cellProb true false false +
      S.cellProb true false true - S.bpAux2u - S.bpAux2v
  | true, false, true, true => S.bpAux2u
  | true, true, true, false => S.bpAux2v
  | true, true, true, true => 1 - S.cellProb false false true - S.cellProb false true true -
      S.cellProb true false true
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 2` is feasible on its optimality region. -/
theorem bpLowerWitness2_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 2) :
    BPFeasible S hA S.bpLowerWitness2 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (S.cellProb false true true - S.cellProb false true false -
      S.cellProb true false false + S.cellProb true false true ) with ⟨hmx0, hmc0⟩ | ⟨hmx0,
      hmc0⟩
  all_goals rcases max_cases (0:ℝ) (S.cellProb false true true - S.cellProb true false false )
      with ⟨hmx1, hmc1⟩ | ⟨hmx1, hmc1⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness2, bpAux2u, bpAux2v, hmx0, hmx1] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
          linarith
    · simp only [bpLowerWitness2, bpAux2u, bpAux2v, hmx0, hmx1, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness2, bpAux2u, bpAux2v, hmx0, hmx1, dArm, yArm, Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpLowerTerm 2` attains it. -/
theorem bpLowerWitness2_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness2 = S.bpLowerTerm 2 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness2, bpAux2u, bpAux2v, bpLowerTerm, Fintype.sum_bool,
    boolToReal]
  linarith

/-- Free-variable choice `u` in the witness attaining `bpLowerTerm 3`. -/
noncomputable def bpAux3u (S : POBalkePearlSystem P) : ℝ :=
  max 0 (S.cellProb false true false - S.cellProb false true true + S.cellProb true false false
    - S.cellProb true false true )

/-- Free-variable choice `v` in the witness attaining `bpLowerTerm 3`. -/
noncomputable def bpAux3v (S : POBalkePearlSystem P) : ℝ :=
  max 0 (S.cellProb false true false - S.cellProb true false true )

/-- Latent table attaining `bpLowerTerm 3`. -/
noncomputable def bpLowerWitness3 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false true
  | false, false, true, false => -S.cellProb false true false + S.cellProb true false true +
      S.bpAux3v
  | false, true, false, false => -S.cellProb false true false + S.cellProb false true true -
      S.cellProb true false false + S.cellProb true false true + S.bpAux3u
  | false, true, false, true => S.cellProb false false false - S.cellProb false false true +
      S.cellProb false true false - S.cellProb false true true + S.cellProb true false false -
      S.cellProb true false true - S.bpAux3u
  | false, true, true, false => S.cellProb false true false + S.cellProb true false false -
      S.cellProb true false true - S.bpAux3u - S.bpAux3v
  | false, true, true, true => S.bpAux3u
  | true, false, true, false => S.cellProb false true false - S.bpAux3v
  | true, true, true, false => S.bpAux3v
  | true, true, true, true => 1 - S.cellProb false false false - S.cellProb false true false -
      S.cellProb true false false
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 3` is feasible on its optimality region. -/
theorem bpLowerWitness3_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 3) :
    BPFeasible S hA S.bpLowerWitness3 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (S.cellProb false true false - S.cellProb false true true +
      S.cellProb true false false - S.cellProb true false true ) with ⟨hmx0, hmc0⟩ | ⟨hmx0,
      hmc0⟩
  all_goals rcases max_cases (0:ℝ) (S.cellProb false true false - S.cellProb true false true )
      with ⟨hmx1, hmc1⟩ | ⟨hmx1, hmc1⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness3, bpAux3u, bpAux3v, hmx0, hmx1] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
          linarith
    · simp only [bpLowerWitness3, bpAux3u, bpAux3v, hmx0, hmx1, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpLowerWitness3, bpAux3u, bpAux3v, hmx0, hmx1, dArm, yArm, Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpLowerTerm 3` attains it. -/
theorem bpLowerWitness3_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness3 = S.bpLowerTerm 3 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness3, bpAux3u, bpAux3v, bpLowerTerm, Fintype.sum_bool,
    boolToReal]
  linarith

/-- Latent table attaining `bpLowerTerm 4`. -/
noncomputable def bpLowerWitness4 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false false + S.cellProb false true false -
      S.cellProb false true true + S.cellProb true false false
  | false, true, false, false => -S.cellProb false true false + S.cellProb false true true -
      S.cellProb true false false
  | false, true, true, false => S.cellProb true false false
  | true, false, false, true => -S.cellProb false false false + S.cellProb false false true -
      S.cellProb false true false + S.cellProb false true true - S.cellProb true false false
  | true, false, true, true => S.cellProb true false true
  | true, true, true, false => S.cellProb false true false
  | true, true, true, true => 1 - S.cellProb false false true - S.cellProb false true true -
      S.cellProb true false true
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 4` is feasible on its optimality region. -/
theorem bpLowerWitness4_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 4) :
    BPFeasible S hA S.bpLowerWitness4 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness4] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
        linarith
  · simp only [bpLowerWitness4, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness4, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpLowerTerm 4` attains it. -/
theorem bpLowerWitness4_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness4 = S.bpLowerTerm 4 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness4, bpLowerTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Latent table attaining `bpLowerTerm 5`. -/
noncomputable def bpLowerWitness5 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false true
  | false, false, true, false => S.cellProb true false false
  | false, true, false, false => S.cellProb false true true
  | false, true, false, true => S.cellProb false false false - S.cellProb false false true -
      S.cellProb false true true
  | true, false, true, false => S.cellProb false true false
  | true, false, true, true => -S.cellProb false true false - S.cellProb true false false +
      S.cellProb true false true
  | true, true, true, true => 1 - S.cellProb false false false - S.cellProb true false true
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 5` is feasible on its optimality region. -/
theorem bpLowerWitness5_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 5) :
    BPFeasible S hA S.bpLowerWitness5 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness5] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
        linarith
  · simp only [bpLowerWitness5, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness5, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpLowerTerm 5` attains it. -/
theorem bpLowerWitness5_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness5 = S.bpLowerTerm 5 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness5, bpLowerTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Latent table attaining `bpLowerTerm 6`. -/
noncomputable def bpLowerWitness6 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false false
  | false, false, true, false => S.cellProb true false true
  | false, true, true, false => S.cellProb false true true
  | false, true, true, true => -S.cellProb false true true + S.cellProb true false false -
      S.cellProb true false true
  | true, false, false, false => S.cellProb false true false
  | true, false, false, true => -S.cellProb false false false + S.cellProb false false true -
      S.cellProb false true false
  | true, true, true, true => 1 - S.cellProb false false true - S.cellProb true false false
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 6` is feasible on its optimality region. -/
theorem bpLowerWitness6_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 6) :
    BPFeasible S hA S.bpLowerWitness6 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness6] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
        linarith
  · simp only [bpLowerWitness6, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness6, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpLowerTerm 6` attains it. -/
theorem bpLowerWitness6_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness6 = S.bpLowerTerm 6 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness6, bpLowerTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Latent table attaining `bpLowerTerm 7`. -/
noncomputable def bpLowerWitness7 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => S.cellProb false false true - S.cellProb false true false +
      S.cellProb false true true + S.cellProb true false true
  | false, true, false, true => S.cellProb false false false - S.cellProb false false true +
      S.cellProb false true false - S.cellProb false true true - S.cellProb true false true
  | false, true, true, true => S.cellProb true false false
  | true, false, false, false => S.cellProb false true false - S.cellProb false true true -
      S.cellProb true false true
  | true, false, true, false => S.cellProb true false true
  | true, true, true, false => S.cellProb false true true
  | true, true, true, true => 1 - S.cellProb false false false - S.cellProb false true false -
      S.cellProb true false false
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpLowerTerm 7` is feasible on its optimality region. -/
theorem bpLowerWitness7_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm 7) :
    BPFeasible S hA S.bpLowerWitness7 := by
  have hs := h₀.sum_one
  have hn := h₀.nonneg
  have n0 := hn false false false false
  have n1 := hn false false false true
  have n2 := hn false false true false
  have n3 := hn false false true true
  have n4 := hn false true false false
  have n5 := hn false true false true
  have n6 := hn false true true false
  have n7 := hn false true true true
  have n8 := hn true false false false
  have n9 := hn true false false true
  have n10 := hn true false true false
  have n11 := hn true false true true
  have n12 := hn true true false false
  have n13 := hn true true false true
  have n14 := hn true true true false
  have n15 := hn true true true true
  have hm := h₀.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  have r0 := hreg 0; have r1 := hreg 1; have r2 := hreg 2; have r3 := hreg 3
  have r4 := hreg 4; have r5 := hreg 5; have r6 := hreg 6; have r7 := hreg 7
  simp only [bpLowerTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness7] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
        linarith
  · simp only [bpLowerWitness7, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpLowerWitness7, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpLowerTerm 7` attains it. -/
theorem bpLowerWitness7_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpLowerWitness7 = S.bpLowerTerm 7 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpLowerWitness7, bpLowerTerm, Fintype.sum_bool, boolToReal]
  linarith

/-! ### The lower endpoint is attained -/

/-- Some feasible latent table attains the closed-form lower endpoint. -/
theorem bpLower_mem_BPIdentifiedInterval (hA : S.BaseAssumptions) :
    S.bpLower ∈ S.BPIdentifiedInterval hA := by
  have h₀ := S.latentProb_feasible hA
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty) S.bpLowerTerm
  have hreg : ∀ j, S.bpLowerTerm j ≤ S.bpLowerTerm i := by
    intro j
    have h := Finset.le_sup' S.bpLowerTerm (Finset.mem_univ j)
    rwa [hi] at h
  have hb : S.bpLower = S.bpLowerTerm i := hi
  rw [hb]
  fin_cases i
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness0_feasible hA h₀ hreg)
    rw [S.bpLowerWitness0_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness1_feasible hA h₀ hreg)
    rw [S.bpLowerWitness1_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness2_feasible hA h₀ hreg)
    rw [S.bpLowerWitness2_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness3_feasible hA h₀ hreg)
    rw [S.bpLowerWitness3_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness4_feasible hA h₀ hreg)
    rw [S.bpLowerWitness4_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness5_feasible hA h₀ hreg)
    rw [S.bpLowerWitness5_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness6_feasible hA h₀ hreg)
    rw [S.bpLowerWitness6_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpLowerWitness7_feasible hA h₀ hreg)
    rw [S.bpLowerWitness7_objective hA] at h
    exact h

end POBalkePearlSystem

end PO
end Causalean
