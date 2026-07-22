/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dynamic Treatment Regime: setup (general `n`)

General-`n` data layer for the sequential backdoor identification result
(`prop:po-dynamic-backdoor` from Basic Concepts.tex, subsection
`subsec:po-dynamic-regime`).

Design choices:
* Per-sequence exchangeability: hypotheses are quantified `∀ dbar : Fin n → δ`.
* Homogeneous treatment space `δ`; heterogeneous state types `γ : Fin n → Type`.
* Distinctness is kept as five separate hypotheses (not `Function.Injective`
  on a sum type) to make use sites clean.

Naming note: in the tex the intervention sequence is written `d̄`.  Lean's
lexer does not accept the grapheme cluster `d̄` as an identifier, so we use
`dbar` throughout.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Conditioning.CondExpTooling
import Causalean.PO.Conditioning.Bundle
import Causalean.Mathlib.CondIndep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Conditional

/-! # Dynamic Treatment Regime Setup

This file provides the general finite-horizon potential-outcome setup for dynamic
treatment regimes. It defines stagewise states, treatments, regimes, sequential
assumptions, and observable adjusted functionals used by dynamic backdoor
identification theorems.

The setup allows heterogeneous state types across stages and a common treatment
value space across stages. Sequential exchangeability and overlap are stated
for each treatment sequence and stage.

The main public objects are `PODTRSystem`, treatment-sequence regimes
`regimeUpTo` and `regime`, counterfactuals `Y_of` and `S_of`, history bundles,
the assumption bundle `Assumptions`, the backward-recursive regression
`innerReg`, and the estimands `dtrEffect` and `adjustedDtr`. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A finite-horizon dynamic treatment-regime system packages the variables for
sequential potential-outcome identification: a state history observed before each
treatment, the treatment chosen at that stage, and the terminal real-valued
outcome whose regime effect is later identified by dynamic backdoor adjustment.

Field guide:
* `S k` is the stage-`k` state or history-dependent covariate variable.
* `D k` is the stage-`k` treatment node in the ambient potential-outcome system.
* `Y` is the terminal outcome node.
* `hDmeas k` identifies the value space of treatment node `D k` with the common
  treatment alphabet `δ`.
* `hYreal` identifies the outcome value space with the real line.
* `distinctSS`, `distinctDD`, `distinctSD`, `distinctSY`, and `distinctDY` record
  that state, treatment, and outcome nodes are genuinely separate variables. -/
structure PODTRSystem (P : POSystem) (n : ℕ) (δ : Type)
    (γ : Fin n → Type)
    [MeasurableSpace δ] [MeasurableSingletonClass δ]
    [∀ k, MeasurableSpace (γ k)] where
  /-- Stage-`k` state variable `Sₖ` (history-dependent covariates observed
  before the stage-`k` treatment is assigned), valued in the stage's type `γ k`. -/
  S : ∀ k : Fin n, POVar P (γ k)
  /-- Stage-`k` treatment node `Dₖ`, given as an index into the ambient system's
  variable set `P.V`. -/
  D : Fin n → P.V
  /-- The terminal outcome node `Y` (a variable of the ambient system). -/
  Y : P.V
  /-- Each treatment node `Dₖ` has value space measurably equivalent to the
  common treatment type `δ` (treatment alphabet is the same across stages). -/
  hDmeas : ∀ k : Fin n, P.X (D k) ≃ᵐ δ
  /-- The outcome node `Y` has value space measurably equivalent to `ℝ`. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- The state nodes are distinct across stages (the map `k ↦ (S k).v` is
  injective). -/
  distinctSS : ∀ k l : Fin n, (S k).v = (S l).v → k = l
  /-- The treatment nodes are distinct across stages. -/
  distinctDD : Function.Injective D
  /-- No state node coincides with any treatment node. -/
  distinctSD : ∀ k l : Fin n, (S k).v ≠ D l
  /-- No state node coincides with the outcome node. -/
  distinctSY : ∀ k : Fin n, (S k).v ≠ Y
  /-- No treatment node coincides with the outcome node. -/
  distinctDY : ∀ k : Fin n, D k ≠ Y

namespace PODTRSystem

variable {P : POSystem} {n : ℕ} {δ : Type} {γ : Fin n → Type}
variable [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable [∀ k, MeasurableSpace (γ k)]

/-! ### POVar accessors -/

/-- The treatment at a stage is packaged as a potential-outcome variable with the
common treatment value space. -/
def dVar (S : PODTRSystem P n δ γ) (k : Fin n) : POVar P δ :=
  ⟨S.D k, S.hDmeas k⟩

/-- The terminal outcome is packaged as a real-valued potential-outcome variable. -/
def yVar (S : PODTRSystem P n δ γ) : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-! ### Regimes -/

/-- The regime target set contains the treatment nodes before the stage cutoff.

It is defined independently of regimes so later regime construction can prove
the required disjointness facts. -/
def regimeTarget (S : PODTRSystem P n δ γ) : ℕ → Finset P.V
  | 0 => ∅
  | k + 1 =>
      if h : k < n then insert (S.D ⟨k, h⟩) (S.regimeTarget k)
      else S.regimeTarget k

/-- Membership in the regime target is exactly being a treatment node before the cutoff. -/
lemma regimeTarget_mem_iff (S : PODTRSystem P n δ γ) :
    ∀ (k : ℕ) (_ : k ≤ n) (v : P.V),
      v ∈ S.regimeTarget k ↔ ∃ i : Fin n, i.val < k ∧ v = S.D i
  | 0, _, v => by
      simp [regimeTarget]
  | k + 1, h, v => by
      have hk : k < n := h
      simp only [regimeTarget, hk, ↓reduceDIte, Finset.mem_insert]
      constructor
      · rintro (rfl | hmem)
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self _, rfl⟩
        · rcases (S.regimeTarget_mem_iff k (Nat.le_of_lt hk) v).mp hmem with
            ⟨i, hi, rfl⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · exact Or.inr ((S.regimeTarget_mem_iff k (Nat.le_of_lt hk) _).mpr
            ⟨i, hi', rfl⟩)
        · left
          have : (⟨k, hk⟩ : Fin n) = i := by
            apply Fin.ext; simp [hi']
          rw [this]

/-- Mutual-recursive definition of the regime together with a proof that
its target equals `regimeTarget`.

The pair `(regime, target-proof)` is built by structural recursion on `k`;
the target-proof at level `k` is needed to discharge the disjointness
hypothesis for `Regime.sqcup` at level `k+1`. -/
noncomputable def regimeUpToAux (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    (k : ℕ) → k ≤ n →
      { r : Regime P.V P.X // r.target = S.regimeTarget k }
  | 0, _ => ⟨Regime.empty, by simp [regimeTarget, Regime.empty]⟩
  | k + 1, h =>
      have hk : k < n := h
      let rec_pair := S.regimeUpToAux dbar k (Nat.le_of_lt hk)
      let r_rec : Regime P.V P.X := rec_pair.1
      have hrec : r_rec.target = S.regimeTarget k := rec_pair.2
      let v := S.D ⟨k, hk⟩
      have hv_not : v ∉ r_rec.target := by
        rw [hrec]
        intro hmem
        rcases (S.regimeTarget_mem_iff k (Nat.le_of_lt hk) _).mp hmem with
          ⟨i, hi, heq⟩
        have hFin : (⟨k, hk⟩ : Fin n) = i := S.distinctDD heq
        have hval : (k : ℕ) = i.val := by
          have := congrArg Fin.val hFin
          simpa using this
        omega
      let r_new := Regime.sqcup
        (Regime.single v ((S.hDmeas ⟨k, hk⟩).symm (dbar ⟨k, hk⟩))) r_rec
        (Regime.single_disjoint_of_not_mem _ _ hv_not)
      ⟨r_new, by
        show r_new.target = S.regimeTarget (k + 1)
        simp only [r_new, Regime.sqcup_target, Regime.single_target,
                   regimeTarget, hk, ↓reduceDIte]
        rw [hrec]
        ext w
        simp [Finset.mem_insert, v]⟩

/-- The partial regime fixes treatments before the stage cutoff to a chosen treatment sequence. -/
noncomputable def regimeUpTo (S : PODTRSystem P n δ γ) (dbar : Fin n → δ)
    (k : ℕ) (h : k ≤ n) : Regime P.V P.X :=
  (S.regimeUpToAux dbar k h).1

/-- The target of the partial treatment regime is the standalone target set for the cutoff. -/
lemma regimeUpTo_target_eq (S : PODTRSystem P n δ γ) (dbar : Fin n → δ)
    (k : ℕ) (h : k ≤ n) :
    (S.regimeUpTo dbar k h).target = S.regimeTarget k :=
  (S.regimeUpToAux dbar k h).2

/-- The full treatment regime fixes every stage's treatment to the chosen treatment sequence. -/
noncomputable def regime (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    Regime P.V P.X :=
  S.regimeUpTo dbar n (le_refl n)

/-! ### Counterfactuals and factuals -/

/-- The terminal counterfactual outcome evaluates the outcome under the full treatment regime. -/
noncomputable def Y_of (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    P.Ω → ℝ := S.yVar.cf (S.regime dbar)

/-- The stage counterfactual state evaluates the state under the earlier treatment interventions. -/
noncomputable def S_of (S : PODTRSystem P n δ γ) (dbar : Fin n → δ)
    (k : Fin n) : P.Ω → γ k :=
  (S.S k).cf (S.regimeUpTo dbar k.val (Nat.le_of_lt k.isLt))

/-- The factual treatment at a stage is the observed treatment value at that stage. -/
noncomputable def factualD (S : PODTRSystem P n δ γ) (k : Fin n) : P.Ω → δ :=
  (S.dVar k).factual

/-- The factual outcome is the observed terminal outcome. -/
noncomputable def factualY (S : PODTRSystem P n δ γ) : P.Ω → ℝ :=
  S.yVar.factual

/-- The factual state at a stage is the observed state value at that stage. -/
noncomputable def factualS (S : PODTRSystem P n δ γ) (k : Fin n) : P.Ω → γ k :=
  (S.S k).factual

/-- The terminal counterfactual outcome under a treatment sequence is measurable. -/
lemma measurable_Y_of (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    Measurable (S.Y_of dbar) :=
  S.yVar.measurable_cf _
/-- Each stage counterfactual state under the earlier treatment interventions is
measurable. -/
lemma measurable_S_of (S : PODTRSystem P n δ γ) (dbar : Fin n → δ)
    (k : Fin n) : Measurable (S.S_of dbar k) :=
  (S.S k).measurable_cf _
/-- Each observed treatment process is measurable. -/
lemma measurable_factualD (S : PODTRSystem P n δ γ) (k : Fin n) :
    Measurable (S.factualD k) := (S.dVar k).measurable_factual
/-- The observed terminal outcome is measurable. -/
lemma measurable_factualY (S : PODTRSystem P n δ γ) :
    Measurable S.factualY := S.yVar.measurable_factual
/-- Each observed state process is measurable. -/
lemma measurable_factualS (S : PODTRSystem P n δ γ) (k : Fin n) :
    Measurable (S.factualS k) := (S.S k).measurable_factual

/-! ### Indicators -/

/-- Joint indicator `1_{D 0 = dbar 0 ∧ … ∧ D (k-1) = dbar (k-1)}`.

Defined by recursion on the stage cutoff `k`.  For `k > n` the extra factors
are dropped — callers should only use this with `k ≤ n`. -/
noncomputable def indD (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ℕ → P.Ω → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun ω =>
      if h : k < n then
        S.indD dbar k ω * (S.dVar ⟨k, h⟩).indicator (dbar ⟨k, h⟩) ω
      else
        S.indD dbar k ω

/-- The joint treatment-agreement indicator up to any cutoff is measurable. -/
lemma measurable_indD (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ∀ k : ℕ, Measurable (S.indD dbar k)
  | 0 => measurable_const
  | k + 1 => by
      unfold indD
      by_cases hk : k < n
      · simp only [hk, ↓reduceDIte]
        exact (S.measurable_indD dbar k).mul
          ((S.dVar ⟨k, hk⟩).measurable_indicator (dbar ⟨k, hk⟩))
      · simp only [hk, ↓reduceDIte]
        exact S.measurable_indD dbar k

/-! ### History bundles -/
/-- A history bundle collects the observed state and treatment history available
just before a selected stage, ending with the current state.

The history bundle at stage cutoff `k` is the factual tuple
`(S 0, D 0, S 1, D 1, ..., S (k-1), D (k-1), S k)`. At `k = 0` it is the
singleton `(S 0,)`.

Matches the old two-stage convention (`historyBundle₁ = (S₁,)`,
`historyBundle₂ = (S₁, D₁, S₂)`). Requires `k < n` since we reference `S k`. -/
noncomputable def historyBundle (S : PODTRSystem P n δ γ) :
    (k : ℕ) → k < n → POCFBundle P
  | 0, h =>
      POCFBundle.cons (RegimedVar.ofFactual (S.S ⟨0, h⟩)) (POCFBundle.nil P)
  | k + 1, h =>
      POCFBundle.cons (RegimedVar.ofFactual (S.S ⟨k + 1, h⟩)) <|
      POCFBundle.cons
        (RegimedVar.ofFactual (S.dVar ⟨k, Nat.lt_of_succ_lt h⟩)) <|
      S.historyBundle k (Nat.lt_of_succ_lt h)

/-! ### Counterfactual bundle wrapper (for exchangeability) -/

/-- Singleton CF bundle containing just `Y(dbar)` — used for the per-sequence
exchangeability statement. -/
noncomputable def cfYBundle (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    POCFBundle P :=
  POCFBundle.cons (⟨S.yVar, S.regime dbar⟩ : RegimedVar P ℝ) (POCFBundle.nil P)

/-! ### Sequential backdoor assumptions -/

/-- Sequential backdoor assumptions (PO level), general `n`.

Per-sequence exchangeability: for each `dbar : Fin n → δ` and each stage
`k : Fin n`, `D k ⟂ Y(dbar) | σ(historyBundle k)`.  Conditions on the full
σ-algebra of the history bundle (standard simplification of the
`{D̄_{k-1}=d̄_{k-1}}` qualifier).

Overlap is pointwise positivity:
`μ[1_{D k = dbar k} | σ(historyBundle k)] > 0` a.s. -/
structure Assumptions (S : PODTRSystem P n δ γ)
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] : Prop where
  consistency : P.Consistency
  /-- Per-sequence sequential exchangeability. -/
  exch : ∀ (dbar : Fin n → δ) (k : Fin n),
    P.CondIndepCFBundle
      (RegimedVar.ofFactual (S.dVar k))
      (S.cfYBundle dbar)
      (S.historyBundle k.val k.isLt) P.μ
  /-- Pointwise (a.s.) positivity of stagewise propensities. -/
  overlap : ∀ (dbar : Fin n → δ) (k : Fin n),
    ∀ᵐ ω ∂P.μ,
      0 < (S.historyBundle k.val k.isLt).condExpGiven
        ((S.dVar k).indicator (dbar k)) P.μ ω
  integrable_Y : ∀ dbar : Fin n → δ, Integrable (S.Y_of dbar) P.μ
  integrable_factualY : Integrable S.factualY P.μ

/-! ### Observable (adjusted) functionals -/
/-- The adjusted dynamic-treatment-regime regression is computed by backward
recursion through the observed treatment and state history, with the
zero-horizon case defined to be zero.

Backward-recursive definition of the adjusted DTR functional.

We index by `j : ℕ` = "number of stages still to pull out", going from the
innermost stage (`j = 0`, uses `historyBundle (n-1)`) out to the outermost
(`j = n - 1`, uses `historyBundle 0`).

* `j = 0` (stage `n`):
      μ[Y · 1_{D_{<n}=dbar} | σ(historyBundle (n-1))]
      / μ[1_{D_{<n}=dbar} | σ(historyBundle (n-1))].
* `j = k + 1` (stage `n - k - 1`):
      μ[innerReg_k · 1_{D (n-k-1) = dbar (n-k-1)} | σ(historyBundle (n-k-2))]
      / μ[1_{D (n-k-1) = dbar (n-k-1)} | σ(historyBundle (n-k-2))].

For `n ≥ 2` the full recursion ends at `j = n - 1`, which conditions on
`historyBundle 0`; the final `adjustedDtr` integrates that over `P.μ`.

For `n = 0`, `innerReg` is the constant `0`. -/
noncomputable def innerReg (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ℕ → P.Ω → ℝ
  | 0 => fun ω =>
      if h : 0 < n then
        (S.historyBundle (n - 1) (Nat.sub_lt h Nat.one_pos)).condExpGiven
          (fun ω' => S.factualY ω' * S.indD dbar n ω') P.μ ω
        /
        (S.historyBundle (n - 1) (Nat.sub_lt h Nat.one_pos)).condExpGiven
          (S.indD dbar n) P.μ ω
      else 0
  | j + 1 => fun ω =>
      if h : j + 1 < n then
        let histIdx : ℕ := n - j - 2
        have hhist : histIdx < n := by
          change n - j - 2 < n; omega
        let stage : Fin n := ⟨histIdx, hhist⟩
        (S.historyBundle histIdx hhist).condExpGiven
          (fun ω' => S.innerReg dbar j ω' * (S.dVar stage).indicator (dbar stage) ω')
          P.μ ω
        /
        (S.historyBundle histIdx hhist).condExpGiven
          ((S.dVar stage).indicator (dbar stage)) P.μ ω
      else S.innerReg dbar j ω

/-- Mean potential outcome `E[Y(dbar)]`.  Single counterfactual mean. -/
noncomputable def dtrEffect (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ℝ := ∫ ω, S.Y_of dbar ω ∂P.μ

/-- Adjusted DTR functional (observable side).  Integrates the outermost
ratio `innerReg dbar (n - 1)` — which conditions on `historyBundle 0 = (S 0,)` —
against `P.μ`.  For `n = 0` this is `0`. -/
noncomputable def adjustedDtr (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ℝ :=
  if 0 < n then ∫ ω, S.innerReg dbar (n - 1) ω ∂P.μ else 0

end PODTRSystem

end PO
end Causalean
