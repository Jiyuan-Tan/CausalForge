/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: witnesses attaining the eight upper expressions

Mirror of `Attainment/Lower.lean`, for the region where each expression is the
smallest of the eight.

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

/-! # Witnesses attaining the Balke-Pearl upper expressions -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

set_option linter.unusedSimpArgs false

/-- Free-variable choice in the witness attaining `bpUpperTerm 0`. -/
noncomputable def bpUAux0u (S : POBalkePearlSystem P) : ℝ :=
  max 0 (-S.cellProb false false false - S.cellProb false false true -
    S.cellProb false true true - S.cellProb true false false + 1)

/-- Latent table attaining `bpUpperTerm 0`. -/
noncomputable def bpUpperWitness0 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, true => S.cellProb false false false +
      S.cellProb false false true + S.cellProb false true true +
      S.cellProb true false false + S.bpUAux0u - 1
  | false, false, true, true => S.cellProb true false true
  | false, true, false, true => -S.cellProb false false true -
      S.cellProb false true true - S.cellProb true false false - S.bpUAux0u + 1
  | false, true, true, true => S.cellProb true false false - S.cellProb true false true
  | true, false, false, false => S.cellProb false true false -
      S.cellProb false true true
  | true, false, false, true => -S.cellProb false false false -
      S.cellProb false true false - S.cellProb true false false - S.bpUAux0u + 1
  | true, true, false, false => S.cellProb false true true
  | true, true, false, true => S.bpUAux0u
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 0` is feasible on its optimality region. -/
theorem bpUpperWitness0_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 0 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness0 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (-S.cellProb false false false - S.cellProb false false true -
      S.cellProb false true true - S.cellProb true false false + 1) with ⟨hmx0, hmc0⟩ |
      ⟨hmx0, hmc0⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness0, bpUAux0u, hmx0] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith
    · simp only [bpUpperWitness0, bpUAux0u, hmx0, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness0, bpUAux0u, hmx0, dArm, yArm, Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpUpperTerm 0` attains it. -/
theorem bpUpperWitness0_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness0 = S.bpUpperTerm 0 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness0, bpUAux0u, bpUpperTerm, Fintype.sum_bool,
    boolToReal]
  linarith

/-- Free-variable choice in the witness attaining `bpUpperTerm 1`. -/
noncomputable def bpUAux1u (S : POBalkePearlSystem P) : ℝ :=
  max 0 (-S.cellProb false false false - S.cellProb false false true -
    S.cellProb false true false - S.cellProb true false true + 1)

/-- Latent table attaining `bpUpperTerm 1`. -/
noncomputable def bpUpperWitness1 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, true => S.cellProb false false false +
      S.cellProb false false true + S.cellProb false true false +
      S.cellProb true false true + S.bpUAux1u - 1
  | false, false, true, true => S.cellProb true false false
  | false, true, false, false => -S.cellProb false true false +
      S.cellProb false true true
  | false, true, false, true => -S.cellProb false false true -
      S.cellProb false true true - S.cellProb true false true - S.bpUAux1u + 1
  | true, false, false, true => -S.cellProb false false false -
      S.cellProb false true false - S.cellProb true false true - S.bpUAux1u + 1
  | true, false, true, true => -S.cellProb true false false + S.cellProb true false true
  | true, true, false, false => S.cellProb false true false
  | true, true, false, true => S.bpUAux1u
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 1` is feasible on its optimality region. -/
theorem bpUpperWitness1_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 1 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness1 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (-S.cellProb false false false - S.cellProb false false true -
      S.cellProb false true false - S.cellProb true false true + 1) with ⟨hmx0, hmc0⟩ |
      ⟨hmx0, hmc0⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness1, bpUAux1u, hmx0] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith
    · simp only [bpUpperWitness1, bpUAux1u, hmx0, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness1, bpUAux1u, hmx0, dArm, yArm, Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpUpperTerm 1` attains it. -/
theorem bpUpperWitness1_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness1 = S.bpUpperTerm 1 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness1, bpUAux1u, bpUpperTerm, Fintype.sum_bool,
    boolToReal]
  linarith

/-- Free-variable choice in the witness attaining `bpUpperTerm 2`. -/
noncomputable def bpUAux2u (S : POBalkePearlSystem P) : ℝ :=
  max 0 (S.cellProb false true false - S.cellProb false true true +
    S.cellProb true false false - S.cellProb true false true )

/-- Free-variable choice in the witness attaining `bpUpperTerm 2`. -/
noncomputable def bpUAux2v (S : POBalkePearlSystem P) : ℝ :=
  max 0 (-S.cellProb false false false - S.cellProb false false true -
    S.cellProb false true false - S.cellProb true false false + 1)

/-- Latent table attaining `bpUpperTerm 2`. -/
noncomputable def bpUpperWitness2 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, true => S.cellProb false false false +
      S.cellProb false false true + S.cellProb false true false +
      S.cellProb true false false + S.bpUAux2v - 1
  | false, false, true, true => S.cellProb true false true
  | false, true, false, false => -S.cellProb false true false +
      S.cellProb false true true - S.cellProb true false false +
      S.cellProb true false true + S.bpUAux2u
  | false, true, false, true => -S.cellProb false false true -
      S.cellProb false true true - S.cellProb true false true - S.bpUAux2u - S.bpUAux2v
      + 1
  | false, true, true, false => S.cellProb true false false - S.cellProb true false true
      - S.bpUAux2u
  | false, true, true, true => S.bpUAux2u
  | true, false, false, true => -S.cellProb false false false -
      S.cellProb false true false - S.cellProb true false false - S.bpUAux2v + 1
  | true, true, false, false => S.cellProb false true false
  | true, true, false, true => S.bpUAux2v
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 2` is feasible on its optimality region. -/
theorem bpUpperWitness2_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 2 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness2 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (S.cellProb false true false - S.cellProb false true true +
      S.cellProb true false false - S.cellProb true false true ) with ⟨hmx0, hmc0⟩ |
      ⟨hmx0, hmc0⟩
  all_goals rcases max_cases (0:ℝ) (-S.cellProb false false false -
      S.cellProb false false true - S.cellProb false true false -
      S.cellProb true false false + 1) with ⟨hmx1, hmc1⟩ | ⟨hmx1, hmc1⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness2, bpUAux2u, bpUAux2v, hmx0, hmx1] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith
    · simp only [bpUpperWitness2, bpUAux2u, bpUAux2v, hmx0, hmx1, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness2, bpUAux2u, bpUAux2v, hmx0, hmx1, dArm, yArm,
      Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpUpperTerm 2` attains it. -/
theorem bpUpperWitness2_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness2 = S.bpUpperTerm 2 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness2, bpUAux2u, bpUAux2v, bpUpperTerm,
    Fintype.sum_bool, boolToReal]
  linarith

/-- Free-variable choice in the witness attaining `bpUpperTerm 3`. -/
noncomputable def bpUAux3u (S : POBalkePearlSystem P) : ℝ :=
  max 0 (-S.cellProb false true false + S.cellProb false true true -
    S.cellProb true false false + S.cellProb true false true )

/-- Free-variable choice in the witness attaining `bpUpperTerm 3`. -/
noncomputable def bpUAux3v (S : POBalkePearlSystem P) : ℝ :=
  max 0 (-S.cellProb false false false - S.cellProb false false true -
    S.cellProb false true true - S.cellProb true false true + 1)

/-- Latent table attaining `bpUpperTerm 3`. -/
noncomputable def bpUpperWitness3 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, true => S.cellProb false false false +
      S.cellProb false false true + S.cellProb false true true +
      S.cellProb true false true + S.bpUAux3v - 1
  | false, false, true, true => S.cellProb true false false
  | false, true, false, true => -S.cellProb false false true -
      S.cellProb false true true - S.cellProb true false true - S.bpUAux3v + 1
  | true, false, false, false => S.cellProb false true false -
      S.cellProb false true true + S.cellProb true false false -
      S.cellProb true false true + S.bpUAux3u
  | true, false, false, true => -S.cellProb false false false -
      S.cellProb false true false - S.cellProb true false false - S.bpUAux3u -
      S.bpUAux3v + 1
  | true, false, true, false => -S.cellProb true false false +
      S.cellProb true false true - S.bpUAux3u
  | true, false, true, true => S.bpUAux3u
  | true, true, false, false => S.cellProb false true true
  | true, true, false, true => S.bpUAux3v
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 3` is feasible on its optimality region. -/
theorem bpUpperWitness3_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 3 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness3 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  rcases max_cases (0:ℝ) (-S.cellProb false true false + S.cellProb false true true -
      S.cellProb true false false + S.cellProb true false true ) with ⟨hmx0, hmc0⟩ |
      ⟨hmx0, hmc0⟩
  all_goals rcases max_cases (0:ℝ) (-S.cellProb false false false -
      S.cellProb false false true - S.cellProb false true true -
      S.cellProb true false true + 1) with ⟨hmx1, hmc1⟩ | ⟨hmx1, hmc1⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · rintro (_|_) (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness3, bpUAux3u, bpUAux3v, hmx0, hmx1] <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith
    · simp only [bpUpperWitness3, bpUAux3u, bpUAux3v, hmx0, hmx1, Fintype.sum_bool]
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      linarith
    · rintro (_|_) (_|_) (_|_) <;>
        simp only [bpUpperWitness3, bpUAux3u, bpUAux3v, hmx0, hmx1, dArm, yArm,
      Fintype.sum_bool] <;>
        norm_num <;>
        try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
      all_goals
        linarith

/-- The witness for `bpUpperTerm 3` attains it. -/
theorem bpUpperWitness3_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness3 = S.bpUpperTerm 3 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness3, bpUAux3u, bpUAux3v, bpUpperTerm,
    Fintype.sum_bool, boolToReal]
  linarith

/-- Latent table attaining `bpUpperTerm 4`. -/
noncomputable def bpUpperWitness4 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, true, true => S.cellProb false false true -
      S.cellProb false true false + S.cellProb false true true +
      S.cellProb true false true
  | false, true, false, true => S.cellProb false false false
  | false, true, true, true => -S.cellProb false false true +
      S.cellProb false true false - S.cellProb false true true +
      S.cellProb true false false - S.cellProb true false true
  | true, false, false, false => S.cellProb false false true
  | true, false, true, false => -S.cellProb false false true +
      S.cellProb false true false - S.cellProb false true true
  | true, true, false, false => S.cellProb false true true
  | true, true, false, true => -S.cellProb false false false -
      S.cellProb false true false - S.cellProb true false false + 1
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 4` is feasible on its optimality region. -/
theorem bpUpperWitness4_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 4 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness4 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness4] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith
  · simp only [bpUpperWitness4, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness4, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpUpperTerm 4` attains it. -/
theorem bpUpperWitness4_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness4 = S.bpUpperTerm 4 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness4, bpUpperTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Latent table attaining `bpUpperTerm 5`. -/
noncomputable def bpUpperWitness5 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, true => S.cellProb false false true
  | false, false, true, true => S.cellProb true false false
  | false, true, false, false => S.cellProb false false false +
      S.cellProb false true true + S.cellProb true false true - 1
  | false, true, false, true => -S.cellProb false false true -
      S.cellProb false true true - S.cellProb true false true + 1
  | true, false, true, false => S.cellProb false false false +
      S.cellProb false true false + S.cellProb true false true - 1
  | true, false, true, true => -S.cellProb false false false -
      S.cellProb false true false - S.cellProb true false false + 1
  | true, true, false, false => -S.cellProb false false false -
      S.cellProb true false true + 1
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 5` is feasible on its optimality region. -/
theorem bpUpperWitness5_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 5 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness5 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness5] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith
  · simp only [bpUpperWitness5, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness5, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpUpperTerm 5` attains it. -/
theorem bpUpperWitness5_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness5 = S.bpUpperTerm 5 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness5, bpUpperTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Latent table attaining `bpUpperTerm 6`. -/
noncomputable def bpUpperWitness6 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, false, true => S.cellProb false false false
  | false, false, true, true => S.cellProb true false true
  | false, true, true, false => S.cellProb false false true + S.cellProb false true true
      + S.cellProb true false false - 1
  | false, true, true, true => -S.cellProb false false true - S.cellProb false true true
      - S.cellProb true false true + 1
  | true, false, false, false => S.cellProb false false true +
      S.cellProb false true false + S.cellProb true false false - 1
  | true, false, false, true => -S.cellProb false false false -
      S.cellProb false true false - S.cellProb true false false + 1
  | true, true, false, false => -S.cellProb false false true -
      S.cellProb true false false + 1
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 6` is feasible on its optimality region. -/
theorem bpUpperWitness6_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 6 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness6 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness6] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith
  · simp only [bpUpperWitness6, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness6, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpUpperTerm 6` attains it. -/
theorem bpUpperWitness6_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness6 = S.bpUpperTerm 6 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness6, bpUpperTerm, Fintype.sum_bool, boolToReal]
  linarith

/-- Latent table attaining `bpUpperTerm 7`. -/
noncomputable def bpUpperWitness7 (S : POBalkePearlSystem P) :
    Bool → Bool → Bool → Bool → ℝ
  | false, false, true, true => S.cellProb false false false +
      S.cellProb false true false - S.cellProb false true true +
      S.cellProb true false false
  | false, true, false, false => S.cellProb false false false
  | false, true, true, false => -S.cellProb false false false -
      S.cellProb false true false + S.cellProb false true true
  | true, false, false, true => S.cellProb false false true
  | true, false, true, true => -S.cellProb false false false -
      S.cellProb false true false + S.cellProb false true true -
      S.cellProb true false false + S.cellProb true false true
  | true, true, false, false => S.cellProb false true false
  | true, true, false, true => -S.cellProb false false true - S.cellProb false true true
      - S.cellProb true false true + 1
  | _, _, _, _ => 0

set_option maxHeartbeats 1000000 in
/-- The witness for `bpUpperTerm 7` is feasible on its optimality region. -/
theorem bpUpperWitness7_feasible (hA : S.BaseAssumptions)
    {π₀ : Bool → Bool → Bool → Bool → ℝ} (h₀ : BPFeasible S hA π₀)
    (hreg : ∀ j, S.bpUpperTerm 7 ≤ S.bpUpperTerm j) :
    BPFeasible S hA S.bpUpperWitness7 := by
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
  simp only [bpUpperTerm] at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [e000, e100, e010, e110, e001, e101, e011, e111] at r0 r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, ?_⟩
  · rintro (_|_) (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness7] <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith
  · simp only [bpUpperWitness7, Fintype.sum_bool]
    try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    linarith
  · rintro (_|_) (_|_) (_|_) <;>
      simp only [bpUpperWitness7, dArm, yArm, Fintype.sum_bool] <;>
      norm_num <;>
      try simp only [e000, e100, e010, e110, e001, e101, e011, e111]
    all_goals
      linarith

/-- The witness for `bpUpperTerm 7` attains it. -/
theorem bpUpperWitness7_objective (hA : S.BaseAssumptions) :
    BPObjective S.bpUpperWitness7 = S.bpUpperTerm 7 := by
  have h0 := S.sum_cellProb_eq_one hA false
  have h1 := S.sum_cellProb_eq_one hA true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [BPObjective, bpUpperWitness7, bpUpperTerm, Fintype.sum_bool, boolToReal]
  linarith

/-! ### The upper endpoint is attained -/

/-- Some feasible latent table attains the closed-form upper endpoint. -/
theorem bpUpper_mem_BPIdentifiedInterval (hA : S.BaseAssumptions) :
    S.bpUpper ∈ S.BPIdentifiedInterval hA := by
  have h₀ := S.latentProb_feasible hA
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty) S.bpUpperTerm
  have hreg : ∀ j, S.bpUpperTerm i ≤ S.bpUpperTerm j := by
    intro j
    have h := Finset.inf'_le S.bpUpperTerm (Finset.mem_univ j)
    rwa [hi] at h
  have hb : S.bpUpper = S.bpUpperTerm i := hi
  rw [hb]
  fin_cases i
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness0_feasible hA h₀ hreg)
    rw [S.bpUpperWitness0_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness1_feasible hA h₀ hreg)
    rw [S.bpUpperWitness1_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness2_feasible hA h₀ hreg)
    rw [S.bpUpperWitness2_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness3_feasible hA h₀ hreg)
    rw [S.bpUpperWitness3_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness4_feasible hA h₀ hreg)
    rw [S.bpUpperWitness4_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness5_feasible hA h₀ hreg)
    rw [S.bpUpperWitness5_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness6_feasible hA h₀ hreg)
    rw [S.bpUpperWitness6_objective hA] at h
    exact h
  · have h := PartialID.mem_identifiedInterval (obj := BPObjective)
      (S.bpUpperWitness7_feasible hA h₀ hreg)
    rw [S.bpUpperWitness7_objective hA] at h
    exact h

end POBalkePearlSystem

end PO
end Causalean
