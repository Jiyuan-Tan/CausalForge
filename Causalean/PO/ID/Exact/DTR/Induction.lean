/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dynamic Treatment Regime: induction machinery (general `n`)

Provides the **base case** (`cdtr_base`) and the **inductive step**
(`cdtr_step`) for the backward induction underlying the general-`n` DTR
backdoor identification theorem.  `DTR/Main.lean` assembles these two
lemmas into the closed-form identification statement
`(historyBundle 0).condExpGiven (Y_of dbar) =ᵐ innerReg dbar (n-1)`.

The identity proved by induction is (★):

    innerReg dbar j · indD dbar (n-1-j)
      =ᵐ[P.μ]
    indD dbar (n-1-j) · (historyBundle (n-1-j)).condExpGiven (Y_of dbar)

with `j = 0` covered by `cdtr_base` and `j → j+1` by `cdtr_step`.
-/

import Causalean.PO.ID.Exact.DTR.Setup
import Causalean.PO.ID.Exact.DTR.Helpers
import Causalean.Mathlib.CondIndep

/-! # Dynamic Treatment Regime Induction

This file proves the base case and inductive step for the backward-induction
identity behind general finite-horizon dynamic backdoor identification. The
identity connects the observable iterated conditional-expectation ratios to the
conditional mean of the regime counterfactual outcome.

The public theorems `cdtr_base` and `cdtr_step` are the cancellation identities
consumed by `cdtr_iter`, `cdtr_backdoor`, and `dtr_backdoor` in `DTR/Main.lean`. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace PODTRSystem

variable {P : POSystem} {n : ℕ} {δ : Type} {γ : Fin n → Type}
variable [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable [∀ k, MeasurableSpace (γ k)]

/-! ### Base case: `j = 0` ------------------------------------------------

`innerReg dbar 0 · indD dbar (n-1)
   =ᵐ indD dbar (n-1) · historyBundle (n-1) .condExpGiven (Y_of dbar)`.

Proof structure (mirrors `DTR.lean` step_1):

1. Consistency rewrite: `factualY · indD dbar n =ᵐ Y_of dbar · indD dbar n`.
2. Factor `indD dbar n = indD dbar (n-1) · (dVar ⟨n-1⟩).indicator dbar_{n-1}`.
3. Pull `indD dbar (n-1)` out of the numerator condExp (strongly-measurable
   w.r.t. `σ(historyBundle (n-1))` by `stronglyMeasurable_indD_sigma_history`).
4. Apply stage-`(n-1)` exchangeability via `condExp_mul_of_condIndep` to split
   `μ[Y_of · indicator_{n-1} | σ_{n-1}]` into the product.
5. On `{indD (n-1) = 1}`, use overlap_{n-1} to establish the cancellation.
   On `{indD (n-1) = 0}`, both sides collapse to `0`. -/

/-- The innermost cancellation identity starts the backward induction for a
dynamic treatment regime. -/
theorem cdtr_base [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : PODTRSystem P n δ γ) (hA : S.Assumptions) (dbar : Fin n → δ)
    (hn : 0 < n) :
    (fun ω => S.innerReg dbar 0 ω * S.indD dbar (n-1) ω)
      =ᵐ[P.μ]
    (fun ω => S.indD dbar (n-1) ω *
      (S.historyBundle (n-1) (Nat.sub_lt hn Nat.one_pos)).condExpGiven
        (S.Y_of dbar) P.μ ω) := by
  -- Abbreviations.
  set m : ℕ := n - 1 with hm_def
  have hm_lt : m < n := Nat.sub_lt hn Nat.one_pos
  have hm_succ : m + 1 = n := by omega
  -- Index for the last-stage treatment.
  set kLast : Fin n := ⟨m, hm_lt⟩ with hkLast_def
  have hB := S.historyBundle m hm_lt
  have hσ_le : (S.historyBundle m hm_lt).sigma ≤
      (inferInstance : MeasurableSpace P.Ω) :=
    (S.historyBundle m hm_lt).sigma_le
  -- Integrability prerequisites.
  have hYof_int : Integrable (S.Y_of dbar) P.μ := hA.integrable_Y dbar
  have hindD_n_int : Integrable (S.indD dbar n) P.μ :=
    S.indD_integrable dbar n
  have hindD_m_int : Integrable (S.indD dbar m) P.μ :=
    S.indD_integrable dbar m
  have hindLast_int :
      Integrable ((S.dVar kLast).indicator (dbar kLast)) P.μ :=
    (S.dVar kLast).integrable_indicator (dbar kLast)
  have hYindD_int : Integrable
      (fun ω => S.factualY ω * S.indD dbar n ω) P.μ := by
    refine hA.integrable_factualY.mono
      (S.measurable_factualY.mul (S.measurable_indD dbar n)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases S.indD_eq_zero_or_one dbar n ω with h | h <;>
      simp [h]
  have hYof_indD_int : Integrable
      (fun ω => S.Y_of dbar ω * S.indD dbar n ω) P.μ :=
    (S.indD_mul_Y_integrable dbar n hYof_int).congr
      (Filter.Eventually.of_forall (fun ω => by ring))
  have hYof_indLast_int :
      Integrable (fun ω => S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω)
        P.μ := by
    exact (S.dVar kLast).integrable_mul_indicator
      (dbar kLast) hYof_int (S.measurable_Y_of dbar)
  -- (a) Consistency: factualY · indD n =ᵐ Y_of · indD n.
  have hConsistency :
      (fun ω => S.factualY ω * S.indD dbar n ω) =
        (fun ω => S.Y_of dbar ω * S.indD dbar n ω) := by
    -- Multi-target consistency over the event {factualD i = dbar i for all i}.
    have h := POVar.factual_mul_indicator_eq_cf_mul_indicator
      hA.consistency S.yVar (S.regime dbar)
      (S.yVar_notMem_regime dbar)
      {ω | ∀ i : Fin n, S.factualD i ω = dbar i}
      (S.factualAgrees_regime dbar)
    -- Replace the set-indicator by `indD dbar n` using indD_eq_indicator_event.
    have hrewrite : S.indD dbar n =
        ({ω | ∀ i : Fin n, S.factualD i ω = dbar i}).indicator (fun _ => (1:ℝ)) := by
      have := S.indD_eq_indicator_event dbar n (le_refl n)
      -- Translate `i.val < n` to `True` (all `i : Fin n` satisfy `i.val < n`).
      have h_set_eq :
          ({ω | ∀ i : Fin n, i.val < n → S.factualD i ω = dbar i})
            = {ω | ∀ i : Fin n, S.factualD i ω = dbar i} := by
        ext ω
        refine ⟨fun h i => h i i.isLt, fun h i _ => h i⟩
      rw [this, h_set_eq]
    rw [hrewrite]
    exact h
  -- (b) Factorisation `indD n = indD m · (dVar kLast).indicator`.
  have hFactor : S.indD dbar n = fun ω =>
      S.indD dbar m ω * (S.dVar kLast).indicator (dbar kLast) ω := by
    funext ω
    -- Compute `S.indD dbar n ω` directly.  Since `n = m + 1`, unfold.
    have h_eq : S.indD dbar n ω = S.indD dbar (m + 1) ω := by
      rw [hm_succ]
    rw [h_eq]
    -- `indD (m+1) ω = indD m ω * indicator ...`.
    have hsplit := congr_fun (S.indD_factor_split dbar m hm_lt) ω
    exact hsplit
  -- (c) Rewrite the numerator's integrand:
  -- `factualY · indD n = indD m · (Y_of · (dVar kLast).indicator)`.
  have hN_arg_eq :
      (fun ω => S.factualY ω * S.indD dbar n ω) =
        (fun ω => S.indD dbar m ω *
          (S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω)) := by
    rw [hConsistency, hFactor]
    funext ω; ring
  -- (d) Pull `indD m` out of the numerator condExp.
  have hN_pullout :
      (S.historyBundle m hm_lt).condExpGiven
          (fun ω => S.indD dbar m ω *
            (S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω)) P.μ
        =ᵐ[P.μ]
          (fun ω => S.indD dbar m ω *
            (S.historyBundle m hm_lt).condExpGiven
              (fun ω' => S.Y_of dbar ω' *
                (S.dVar kLast).indicator (dbar kLast) ω') P.μ ω) := by
    have hindD_m_sm :
        StronglyMeasurable[(S.historyBundle m hm_lt).sigma] (S.indD dbar m) :=
      S.stronglyMeasurable_indD_sigma_history m hm_lt dbar m (le_refl m)
    -- product integrability
    have hprod_int : Integrable
        (S.indD dbar m *
          fun ω => S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω) P.μ := by
      have heq :
          (S.indD dbar m *
            fun ω => S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω) =
            fun ω => S.indD dbar m ω *
              (S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω) := rfl
      rw [heq]
      have h_indD_Y_int :
          Integrable (fun ω => S.indD dbar m ω * S.Y_of dbar ω) P.μ :=
        S.indD_mul_Y_integrable dbar m hYof_int
      have hmul := (S.dVar kLast).integrable_mul_indicator (dbar kLast) h_indD_Y_int
        ((S.measurable_indD dbar m).mul (S.measurable_Y_of dbar))
      exact hmul.congr (Filter.Eventually.of_forall (fun ω => by ring))
    have hpull :=
      (S.historyBundle m hm_lt).condExpGiven_mul_of_stronglyMeasurable_left
        (f := S.indD dbar m)
        (g := fun ω => S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω)
        hindD_m_sm hprod_int hYof_indLast_int
    -- `hpull` has shape `condExp (indD m * _) =ᵐ indD m * condExp _`.
    filter_upwards [hpull] with ω hω
    simpa [Pi.mul_apply] using hω
  -- (e) Stage-`(n-1)` exchangeability + condExp_mul_of_condIndep.
  -- Project `hA.exch dbar kLast` onto `Y_of dbar` coordinate of `cfYBundle`.
  -- Index 0 in cfYBundle = singleton of `Y(dbar)`.
  have hcfY_n : (S.cfYBundle dbar).n = 1 := rfl
  let i0 : Fin (S.cfYBundle dbar).n := ⟨0, by rw [hcfY_n]; exact Nat.one_pos⟩
  -- The type at index 0 reduces to ℝ; supply the projection via a coercion.
  let ψ : (∀ i : Fin (S.cfYBundle dbar).n, (S.cfYBundle dbar).type i) → ℝ :=
    fun f => (f i0 : ℝ)
  have hψ_meas : Measurable ψ := by
    -- `ψ = (· : (cfYBundle dbar).type i0 → ℝ) ∘ (eval i0)`. Both measurable.
    -- Type at i0 reduces to ℝ definitionally.
    change Measurable (fun f : (∀ i, (S.cfYBundle dbar).type i) =>
      (f i0 : ℝ))
    exact measurable_pi_apply i0
  have hYof_eq_proj : S.Y_of dbar = ψ ∘ (S.cfYBundle dbar).jointValue := by
    funext ω; rfl
  have hCI :
      ProbabilityTheory.CondIndepFun (S.historyBundle m hm_lt).sigma
        hσ_le (S.factualD kLast) (S.Y_of dbar) P.μ := by
    have hproj := (hA.exch dbar kLast).project (ψ := ψ) hψ_meas
    rw [hYof_eq_proj]
    -- `hproj : CondIndepFun σ_le factualD (ψ ∘ jointValue) μ`.
    -- Here factualD = (dVar kLast).value (via ofFactual).
    exact hproj
  -- Use `condExp_mul_of_condIndep` with u := indicator of {dbar kLast}, v := id.
  let u : δ → ℝ := ({dbar kLast} : Set δ).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u :=
    measurable_const.indicator (MeasurableSet.singleton _)
  have hu_eq : (fun ω => u (S.factualD kLast ω)) =
      (S.dVar kLast).indicator (dbar kLast) := by
    funext ω
    unfold POVar.indicator
    by_cases h : S.factualD kLast ω = dbar kLast
    · have h1 : S.factualD kLast ω ∈ ({dbar kLast} : Set δ) := h
      have h2 : ω ∈ (S.dVar kLast).event (dbar kLast) := h
      rw [show u (S.factualD kLast ω) = (1 : ℝ) from Set.indicator_of_mem h1 _,
          Set.indicator_of_mem h2]
    · have h1 : S.factualD kLast ω ∉ ({dbar kLast} : Set δ) := h
      have h2 : ω ∉ (S.dVar kLast).event (dbar kLast) := h
      rw [show u (S.factualD kLast ω) = (0 : ℝ) from Set.indicator_of_notMem h1 _,
          Set.indicator_of_notMem h2]
  have huv_int : Integrable
      (fun ω => u (S.factualD kLast ω) * S.Y_of dbar ω) P.μ := by
    have hEq : (fun ω => u (S.factualD kLast ω) * S.Y_of dbar ω) =
        (fun ω => (S.dVar kLast).indicator (dbar kLast) ω * S.Y_of dbar ω) := by
      funext ω; rw [congr_fun hu_eq ω]
    rw [hEq]
    refine hYof_int.mono
      (((S.dVar kLast).measurable_indicator (dbar kLast)).mul
        (S.measurable_Y_of dbar)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases (S.dVar kLast).indicator_eq_one_or_zero (dbar kLast) ω with h | h <;>
      simp [h]
  have hfact :
      P.μ[fun ω => u (S.factualD kLast ω) * S.Y_of dbar ω
          | (S.historyBundle m hm_lt).sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (S.factualD kLast ω) | (S.historyBundle m hm_lt).sigma]
            * P.μ[fun ω => S.Y_of dbar ω | (S.historyBundle m hm_lt).sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
        (m := (S.historyBundle m hm_lt).sigma) hσ_le
        (f := S.factualD kLast) (g := S.Y_of dbar)
        (S.measurable_factualD kLast) (S.measurable_Y_of dbar) hCI
        (u := u) (v := id) hu_meas measurable_id
        (by rw [hu_eq]; exact hindLast_int) hYof_int huv_int
  -- Reshape `hfact` into condExpGiven form.
  have hfact' :
      (S.historyBundle m hm_lt).condExpGiven
          (fun ω => S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω) P.μ
        =ᵐ[P.μ]
          (fun ω => (S.historyBundle m hm_lt).condExpGiven
            ((S.dVar kLast).indicator (dbar kLast)) P.μ ω *
            (S.historyBundle m hm_lt).condExpGiven (S.Y_of dbar) P.μ ω) := by
    unfold POCFBundle.condExpGiven
    have hprod_rw :
        (fun ω => u (S.factualD kLast ω) * S.Y_of dbar ω) =
          (fun ω => S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω) := by
      funext ω; rw [congr_fun hu_eq ω]; ring
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply] using hω
  -- (f) Combine into the full numerator expression.
  have hNum_eq :
      (S.historyBundle m hm_lt).condExpGiven
          (fun ω => S.factualY ω * S.indD dbar n ω) P.μ
        =ᵐ[P.μ]
          (fun ω => S.indD dbar m ω *
            ((S.historyBundle m hm_lt).condExpGiven
                ((S.dVar kLast).indicator (dbar kLast)) P.μ ω *
              (S.historyBundle m hm_lt).condExpGiven (S.Y_of dbar) P.μ ω)) := by
    -- First rewrite the integrand.
    have hstep1 :
        (S.historyBundle m hm_lt).condExpGiven
            (fun ω => S.factualY ω * S.indD dbar n ω) P.μ
          = (S.historyBundle m hm_lt).condExpGiven
            (fun ω => S.indD dbar m ω *
              (S.Y_of dbar ω * (S.dVar kLast).indicator (dbar kLast) ω)) P.μ := by
      rw [hN_arg_eq]
    rw [hstep1]
    refine hN_pullout.trans ?_
    filter_upwards [hfact'] with ω hω
    rw [hω]
  -- (g) Denominator side: condExp of indD n = indD m · (dVar kLast).indicator.
  have hD_pullout :
      (S.historyBundle m hm_lt).condExpGiven (S.indD dbar n) P.μ
        =ᵐ[P.μ]
          (fun ω => S.indD dbar m ω *
            (S.historyBundle m hm_lt).condExpGiven
              ((S.dVar kLast).indicator (dbar kLast)) P.μ ω) := by
    have hindD_m_sm :
        StronglyMeasurable[(S.historyBundle m hm_lt).sigma] (S.indD dbar m) :=
      S.stronglyMeasurable_indD_sigma_history m hm_lt dbar m (le_refl m)
    have hprod_int : Integrable
        (S.indD dbar m * (S.dVar kLast).indicator (dbar kLast)) P.μ := by
      have heq : (S.indD dbar m * (S.dVar kLast).indicator (dbar kLast)) =
          fun ω => S.indD dbar m ω * (S.dVar kLast).indicator (dbar kLast) ω := rfl
      rw [heq, ← hFactor]
      exact hindD_n_int
    have hpull :=
      (S.historyBundle m hm_lt).condExpGiven_mul_of_stronglyMeasurable_left
        (f := S.indD dbar m) (g := (S.dVar kLast).indicator (dbar kLast))
        hindD_m_sm hprod_int hindLast_int
    -- Rewrite LHS using hFactor.
    have : (S.historyBundle m hm_lt).condExpGiven (S.indD dbar n) P.μ
        = (S.historyBundle m hm_lt).condExpGiven
            (fun ω => S.indD dbar m ω *
              (S.dVar kLast).indicator (dbar kLast) ω) P.μ := by
      rw [hFactor]
    rw [this]
    filter_upwards [hpull] with ω hω
    simpa [Pi.mul_apply] using hω
  -- (h) Pointwise cancellation using overlap.
  have hover_last := hA.overlap dbar kLast
  filter_upwards [hNum_eq, hD_pullout, hover_last] with ω hN hD hov
  -- Unfold `innerReg dbar 0 ω` using `hn`.
  have h_inner :
      S.innerReg dbar 0 ω =
        (S.historyBundle m hm_lt).condExpGiven
            (fun ω' => S.factualY ω' * S.indD dbar n ω') P.μ ω
        /
        (S.historyBundle m hm_lt).condExpGiven (S.indD dbar n) P.μ ω := by
    unfold PODTRSystem.innerReg
    simp only [hn, ↓reduceDIte]
    -- The result uses `historyBundle (n-1) _`; rewrite `n-1` to `m`.
    rfl
  -- Align `historyBundle (n-1) _` in the goal with `historyBundle m hm_lt`.
  have hHB_eq :
      (S.historyBundle (n-1) (Nat.sub_lt hn Nat.one_pos)).condExpGiven
        (S.Y_of dbar) P.μ
        = (S.historyBundle m hm_lt).condExpGiven (S.Y_of dbar) P.μ := rfl
  -- Likewise for the indicator factor on the LHS.
  change S.innerReg dbar 0 ω * S.indD dbar (n-1) ω
    = S.indD dbar (n-1) ω *
        (S.historyBundle (n-1) (Nat.sub_lt hn Nat.one_pos)).condExpGiven
          (S.Y_of dbar) P.μ ω
  rw [hHB_eq, h_inner, hN, hD]
  change _ / _ * S.indD dbar m ω = _
  -- Case split on indD m ω ∈ {0, 1}.
  rcases S.indD_eq_zero_or_one dbar m ω with h0 | h1
  · -- indD m ω = 0: both sides are 0.
    have h0' : S.indD dbar (n - 1) ω = 0 := h0
    simp [h0, h0']
  · -- indD m ω = 1: use overlap to get nonzero denominator, then cancel.
    have hneZero :
        (S.historyBundle m hm_lt).condExpGiven
          ((S.dVar kLast).indicator (dbar kLast)) P.μ ω ≠ 0 := by
      intro habs
      rw [habs] at hov
      linarith
    rw [h1]
    field_simp

/-! ### Inductive step: `j → j + 1` ---------------------------------------

From
  innerReg dbar j · indD dbar (k+1)
    =ᵐ indD dbar (k+1) · (historyBundle (k+1)).condExpGiven (Y_of dbar)
(where `k = n - 2 - j`, so `k + 1 = n - 1 - j`), deduce
  innerReg dbar (j+1) · indD dbar k
    =ᵐ indD dbar k · (historyBundle k).condExpGiven (Y_of dbar).

Proof sketch (mirrors the n=2 proof's `step_2` / `step_3` / `step_4`,
wrapped by `condExpRatio_eq_of_mul`):

(1) Rewrite the `innerReg (j+1)` side as a `condExpRatio` on `historyBundle k`
    with numerator integrand `innerReg j · indicator_{stage = dbar stage}` and
    denominator `indicator_{stage = dbar stage}`.  Here `stage : Fin n` is the
    stage index chosen by `innerReg`'s recursion at step `j+1`.
(2) Apply `condExpRatio_eq_of_mul` with `target :=
    (historyBundle k).condExpGiven (Y_of dbar) P.μ`, reducing to:
      (A) `condExpGiven (innerReg j · indicator_stage) =ᵐ
           condExpGiven indicator_stage · condExpGiven (Y_of dbar)`;
      (B) `condExpGiven indicator_stage ω ≠ 0` a.s.
(3) (A) chains:
      - `step_2`-analogue: rewrite the integrand using IH and `indD_factor_split`
        on `indD (k+1) = indD k · indicator_k`;
      - `step_3`-analogue: reverse pull-out of `indicator_k` on
        `historyBundle (k+1)` + tower down to `historyBundle k`;
      - `step_4`-analogue: apply `condExp_mul_of_condIndep` at stage `k` using
        `hA.exch dbar ⟨k, hk'⟩`.
(4) (B) from `overlap_k`.
(5) Restore the `· indD k` factor on both sides of the resulting equality.

Note on indexing: `DTR/Setup.lean`'s `innerReg (j+1)` recursion uses
`stage = histIdx = n - j - 2` and conditions on `historyBundle (n - j - 2) =
historyBundle k`, adding numerator factor
`(dVar ⟨k, hk⟩).indicator (dbar ⟨k, hk⟩)`.  The induction hypothesis in
`cdtr_step` is stated at depth `j` (with `indD (n - j - 1)` on the indD
side) and concludes at depth `j + 1` (with `indD (n - j - 2)`).  -/

/-- The induction step moves the dynamic-regime cancellation identity one stage outward.

It assumes the identity and integrability at the current depth and proves the
next identity in the backward induction. -/
theorem cdtr_step [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : PODTRSystem P n δ γ) (hA : S.Assumptions) (dbar : Fin n → δ)
    (j : ℕ) (hj : j + 1 < n)
    (hk : n - j - 2 < n)
    (hIH_int : Integrable (S.innerReg dbar j) P.μ)
    (IH : (fun ω => S.innerReg dbar j ω * S.indD dbar (n - j - 1) ω)
            =ᵐ[P.μ]
          (fun ω => S.indD dbar (n - j - 1) ω *
            (S.historyBundle (n - j - 1) (by omega)).condExpGiven
              (S.Y_of dbar) P.μ ω)) :
    (fun ω => S.innerReg dbar (j + 1) ω * S.indD dbar (n - j - 2) ω)
      =ᵐ[P.μ]
    (fun ω => S.indD dbar (n - j - 2) ω *
      (S.historyBundle (n - j - 2) hk).condExpGiven (S.Y_of dbar) P.μ ω) := by
  -- Abbreviations.
  set k : ℕ := n - j - 2 with hk_def
  have hk1 : k + 1 < n := by omega
  set kFin : Fin n := ⟨k, hk⟩ with hkFin_def
  set ind_k : P.Ω → ℝ := (S.dVar kFin).indicator (dbar kFin) with hind_k_def
  -- σ-algebra inclusion σ_k ≤ σ_{k+1}.
  have hσk_le : (S.historyBundle k hk).sigma ≤ (inferInstance : MeasurableSpace P.Ω) :=
    (S.historyBundle k hk).sigma_le
  have hσ_step : (S.historyBundle k hk).sigma ≤ (S.historyBundle (k+1) hk1).sigma :=
    S.historyBundle_sigma_mono_step k hk1
  -- Strong-measurability of `indD k` (σ_k) and `ind_k` (σ_{k+1}).
  have hindDk_sm :
      StronglyMeasurable[(S.historyBundle k hk).sigma] (S.indD dbar k) :=
    S.stronglyMeasurable_indD_sigma_history k hk dbar k (le_refl k)
  have hindk_sm_k1 :
      StronglyMeasurable[(S.historyBundle (k+1) hk1).sigma] ind_k :=
    S.stronglyMeasurable_indicator_dVar_sigma_history (k+1) hk1 kFin
      (Nat.lt_succ_self _) (dbar kFin)
  -- Integrability prerequisites.
  have hYof_int : Integrable (S.Y_of dbar) P.μ := hA.integrable_Y dbar
  have hindk_int : Integrable ind_k P.μ :=
    (S.dVar kFin).integrable_indicator (dbar kFin)
  have hindDk1_int : Integrable (S.indD dbar (k+1)) P.μ := S.indD_integrable dbar (k+1)
  have hYof_indk_int :
      Integrable (fun ω => S.Y_of dbar ω * ind_k ω) P.μ := by
    dsimp [ind_k]
    exact (S.dVar kFin).integrable_mul_indicator
      (dbar kFin) hYof_int (S.measurable_Y_of dbar)
  have hindk_Yof_int :
      Integrable (fun ω => ind_k ω * S.Y_of dbar ω) P.μ :=
    hYof_indk_int.congr (Filter.Eventually.of_forall (fun ω => by ring))
  -- `n - j - 1 = k + 1`.
  have hk1_idx : n - j - 1 = k + 1 := by omega
  -- Pointwise factor split: indD (k+1) = indD k · ind_k.
  have hFactor : S.indD dbar (k+1) = fun ω => S.indD dbar k ω * ind_k ω :=
    S.indD_factor_split dbar k hk
  -- Integrability of `innerReg j · indD (k+1)`: derived from IH RHS being integrable.
  have hCondExpY_k1_int :
      Integrable
        ((S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ) P.μ :=
    (S.historyBundle (k+1) hk1).integrable_condExpGiven _
  have hRHS_IH_int :
      Integrable (fun ω => S.indD dbar (k+1) ω *
        (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) P.μ := by
    refine hCondExpY_k1_int.mono
      ((S.measurable_indD dbar (k+1)).mul
        ((S.historyBundle (k+1) hk1).stronglyMeasurable_condExpGiven _).measurable
          ).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases S.indD_eq_zero_or_one dbar (k+1) ω with h | h <;> simp [h]
  -- Cast IH from `n - j - 1` to `k + 1`.
  have IH' : (fun ω => S.innerReg dbar j ω * S.indD dbar (k+1) ω)
            =ᵐ[P.μ]
          (fun ω => S.indD dbar (k+1) ω *
            (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) := by
    -- The indices `n - j - 1` and `k + 1` are equal (`hk1_idx`); rewrite via
    -- a heterogeneous-eq cast on the historyBundle.
    have hHB_eq :
        HEq ((S.historyBundle (n - j - 1)
              (by omega : n - j - 1 < n)).condExpGiven (S.Y_of dbar) P.μ)
            ((S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ) := by
      congr 1
      simp [hk1_idx]
    have hHB_eq' :
        (S.historyBundle (n - j - 1) (by omega : n - j - 1 < n)).condExpGiven
            (S.Y_of dbar) P.μ
          = (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ :=
      eq_of_heq hHB_eq
    have hindDeq : S.indD dbar (n - j - 1) = S.indD dbar (k + 1) := by
      rw [hk1_idx]
    have := IH
    rw [hindDeq] at this
    refine this.trans ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [hHB_eq']
  have hinnerReg_indD_int :
      Integrable (fun ω => S.innerReg dbar j ω * S.indD dbar (k+1) ω) P.μ :=
    hRHS_IH_int.congr IH'.symm
  -- ====== Master identity =====================================================
  -- Prove: μ[innerReg j · indD (k+1) | σ_k]  =ᵐ
  --        indD k · μ[ind_k | σ_k] · μ[Y_of | σ_k].
  -- Path:
  --  (a) condExpGiven_congr_ae of IH'.
  --  (b) Rewrite RHS integrand: indD (k+1) · μ[Y|σ_{k+1}] = indD k · (ind_k · μ[Y|σ_{k+1}]).
  --  (c) Pull indD k (σ_k-meas, bounded) out.
  --  (d) Reverse pullout of ind_k on σ_{k+1}.
  --  (e) Tower σ_k ≤ σ_{k+1}.
  --  (f) Stage-k exch.
  -- ============================================================================
  -- (a) Apply σ_k-CE to both sides of IH'.
  have hStepA :
      (S.historyBundle k hk).condExpGiven
          (fun ω => S.innerReg dbar j ω * S.indD dbar (k+1) ω) P.μ
        =ᵐ[P.μ]
      (S.historyBundle k hk).condExpGiven
          (fun ω => S.indD dbar (k+1) ω *
            (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) P.μ :=
    (S.historyBundle k hk).condExpGiven_congr_ae IH'
  -- (b) Rewrite: indD (k+1) · X = indD k · (ind_k · X).
  have hRewriteRHS :
      (fun ω => S.indD dbar (k+1) ω *
        (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)
        = (fun ω => S.indD dbar k ω *
            (ind_k ω *
              (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)) := by
    funext ω
    rw [show S.indD dbar (k+1) ω = S.indD dbar k ω * ind_k ω from
      congr_fun hFactor ω]
    ring
  -- (c) Pull indD k (σ_k-meas) out of σ_k-CE.
  have hindk_CE_int :
      Integrable (fun ω => ind_k ω *
        (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) P.μ := by
    dsimp [ind_k]
    have hmul := (S.dVar kFin).integrable_mul_indicator (dbar kFin)
      hCondExpY_k1_int
      ((S.historyBundle (k+1) hk1).stronglyMeasurable_condExpGiven _).measurable
    exact hmul.congr (Filter.Eventually.of_forall (fun ω => by ring))
  have hindDk_indk_CE_int :
      Integrable (S.indD dbar k * fun ω => ind_k ω *
        (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) P.μ := by
    have hrw :
        (S.indD dbar k * fun ω => ind_k ω *
          (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) =
          fun ω => S.indD dbar (k+1) ω *
            (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω := by
      funext ω
      change S.indD dbar k ω *
          (ind_k ω * (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) = _
      rw [show S.indD dbar (k+1) ω = S.indD dbar k ω * ind_k ω from
        congr_fun hFactor ω]
      ring
    rw [hrw]; exact hRHS_IH_int
  have hPullIndDk :
      (S.historyBundle k hk).condExpGiven
          (fun ω => S.indD dbar k ω *
            (ind_k ω *
              (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)) P.μ
        =ᵐ[P.μ]
          (fun ω => S.indD dbar k ω *
            (S.historyBundle k hk).condExpGiven
              (fun ω' => ind_k ω' *
                (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω')
              P.μ ω) := by
    have hpull :=
      (S.historyBundle k hk).condExpGiven_mul_of_stronglyMeasurable_left
        (f := S.indD dbar k)
        (g := fun ω => ind_k ω *
          (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)
        hindDk_sm hindDk_indk_CE_int hindk_CE_int
    filter_upwards [hpull] with ω hω
    simpa [Pi.mul_apply] using hω
  -- (d) Reverse pullout of ind_k on σ_{k+1}.
  have hRevPull :
      (fun ω => ind_k ω *
        (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)
        =ᵐ[P.μ]
      (S.historyBundle (k+1) hk1).condExpGiven
        (fun ω => ind_k ω * S.Y_of dbar ω) P.μ := by
    have hfwd :=
      (S.historyBundle (k+1) hk1).condExpGiven_mul_of_stronglyMeasurable_left
        (f := ind_k) (g := S.Y_of dbar)
        hindk_sm_k1 hindk_Yof_int hYof_int
    filter_upwards [hfwd] with ω hω
    simpa [Pi.mul_apply] using hω.symm
  -- (e) Tower σ_k ≤ σ_{k+1}.
  haveI : IsFiniteMeasure (P.μ.trim (S.historyBundle (k+1) hk1).sigma_le) :=
    isFiniteMeasure_trim _
  have hTower :
      (S.historyBundle k hk).condExpGiven
        ((S.historyBundle (k+1) hk1).condExpGiven
          (fun ω => ind_k ω * S.Y_of dbar ω) P.μ) P.μ
        =ᵐ[P.μ]
      (S.historyBundle k hk).condExpGiven
        (fun ω => ind_k ω * S.Y_of dbar ω) P.μ := by
    have h := (S.historyBundle (k+1) hk1).condExpGiven_tower_of_le
      (g := fun ω => ind_k ω * S.Y_of dbar ω) (μ := P.μ)
      (m := (S.historyBundle k hk).sigma) hσ_step
    simpa [POCFBundle.condExpGiven] using h
  -- (f) Stage-k exchangeability.
  have hcfY_n : (S.cfYBundle dbar).n = 1 := rfl
  let i0 : Fin (S.cfYBundle dbar).n := ⟨0, by rw [hcfY_n]; exact Nat.one_pos⟩
  let ψ : (∀ i : Fin (S.cfYBundle dbar).n, (S.cfYBundle dbar).type i) → ℝ :=
    fun f => (f i0 : ℝ)
  have hψ_meas : Measurable ψ := by
    change Measurable (fun f : (∀ i, (S.cfYBundle dbar).type i) =>
      (f i0 : ℝ))
    exact measurable_pi_apply i0
  have hYof_eq_proj : S.Y_of dbar = ψ ∘ (S.cfYBundle dbar).jointValue := by
    funext ω; rfl
  have hCI :
      ProbabilityTheory.CondIndepFun (S.historyBundle k hk).sigma
        hσk_le (S.factualD kFin) (S.Y_of dbar) P.μ := by
    have hproj := (hA.exch dbar kFin).project (ψ := ψ) hψ_meas
    rw [hYof_eq_proj]; exact hproj
  let u : δ → ℝ := ({dbar kFin} : Set δ).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u :=
    measurable_const.indicator (MeasurableSet.singleton _)
  have hu_eq : (fun ω => u (S.factualD kFin ω)) = ind_k := by
    funext ω
    show u (S.factualD kFin ω) = ind_k ω
    by_cases h : S.factualD kFin ω = dbar kFin
    · have h1 : S.factualD kFin ω ∈ ({dbar kFin} : Set δ) := h
      have h2 : ω ∈ (S.dVar kFin).event (dbar kFin) := h
      rw [show u (S.factualD kFin ω) = (1 : ℝ) from Set.indicator_of_mem h1 _,
          show ind_k ω = (1 : ℝ) from
            (S.dVar kFin).indicator_apply_eq_one h2]
    · have h1 : S.factualD kFin ω ∉ ({dbar kFin} : Set δ) := h
      have h2 : ω ∉ (S.dVar kFin).event (dbar kFin) := h
      rw [show u (S.factualD kFin ω) = (0 : ℝ) from Set.indicator_of_notMem h1 _,
          show ind_k ω = (0 : ℝ) from
            (S.dVar kFin).indicator_apply_eq_zero h2]
  have huv_int :
      Integrable (fun ω => u (S.factualD kFin ω) * S.Y_of dbar ω) P.μ := by
    have hEq : (fun ω => u (S.factualD kFin ω) * S.Y_of dbar ω) =
        (fun ω => ind_k ω * S.Y_of dbar ω) := by
      funext ω; rw [congr_fun hu_eq ω]
    rw [hEq]; exact hindk_Yof_int
  have hfact :
      P.μ[fun ω => u (S.factualD kFin ω) * S.Y_of dbar ω
          | (S.historyBundle k hk).sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (S.factualD kFin ω) | (S.historyBundle k hk).sigma]
            * P.μ[fun ω => S.Y_of dbar ω | (S.historyBundle k hk).sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
        (m := (S.historyBundle k hk).sigma) hσk_le
        (f := S.factualD kFin) (g := S.Y_of dbar)
        (S.measurable_factualD kFin) (S.measurable_Y_of dbar) hCI
        (u := u) (v := id) hu_meas measurable_id
        (by rw [hu_eq]; exact hindk_int) hYof_int huv_int
  have hExch :
      (S.historyBundle k hk).condExpGiven
          (fun ω => ind_k ω * S.Y_of dbar ω) P.μ
        =ᵐ[P.μ]
          (fun ω => (S.historyBundle k hk).condExpGiven ind_k P.μ ω *
            (S.historyBundle k hk).condExpGiven (S.Y_of dbar) P.μ ω) := by
    unfold POCFBundle.condExpGiven
    have hprod_rw : (fun ω => u (S.factualD kFin ω) * S.Y_of dbar ω) =
        (fun ω => ind_k ω * S.Y_of dbar ω) := by
      funext ω; rw [congr_fun hu_eq ω]
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply] using hω
  -- Combine (a)-(f) into Master:
  --   μ[innerReg j · indD (k+1) | σ_k] =ᵐ
  --   indD k · (μ[ind_k | σ_k] · μ[Y_of | σ_k]).
  have hMaster :
      (S.historyBundle k hk).condExpGiven
          (fun ω => S.innerReg dbar j ω * S.indD dbar (k+1) ω) P.μ
        =ᵐ[P.μ]
      (fun ω => S.indD dbar k ω *
        ((S.historyBundle k hk).condExpGiven ind_k P.μ ω *
          (S.historyBundle k hk).condExpGiven (S.Y_of dbar) P.μ ω)) := by
    refine hStepA.trans ?_
    rw [hRewriteRHS]
    refine hPullIndDk.trans ?_
    -- Now: indD k · μ[ind_k · μ[Y_of|σ_{k+1}] | σ_k] →
    --   indD k · μ[μ[ind_k · Y_of | σ_{k+1}] | σ_k] (via hRevPull + congr_ae) →
    --   indD k · μ[ind_k · Y_of | σ_k] (tower) →
    --   indD k · (μ[ind_k|σ_k] · μ[Y_of|σ_k]) (exch).
    have hCongr :=
      (S.historyBundle k hk).condExpGiven_congr_ae hRevPull
    filter_upwards [hCongr, hTower, hExch] with ω hC hT hE
    rw [hC, hT, hE]
  -- ====== Integrability of `innerReg j · ind_k` ===============================
  -- Required to pull `indD k` IN to relate `indD k · μ[innerReg j · ind_k | σ_k]`
  -- with `μ[innerReg j · indD (k+1) | σ_k]`.  Follows from `innerReg_integrable`
  -- (HelpersN.lean) plus boundedness of `ind_k`.
  have hinnerReg_indk_int :
      Integrable (fun ω => S.innerReg dbar j ω * ind_k ω) P.μ := by
    dsimp [ind_k]
    exact (S.dVar kFin).integrable_mul_indicator
      (dbar kFin) hIH_int (S.measurable_innerReg dbar j)
  -- Pull indD k IN: μ[indD k · (innerReg j · ind_k) | σ_k] =ᵐ indD k · μ[innerReg j · ind_k | σ_k].
  have hindDk_inner_int :
      Integrable (S.indD dbar k * fun ω => S.innerReg dbar j ω * ind_k ω) P.μ := by
    have hrw : (S.indD dbar k * fun ω => S.innerReg dbar j ω * ind_k ω) =
        fun ω => S.innerReg dbar j ω * S.indD dbar (k+1) ω := by
      funext ω
      change S.indD dbar k ω * (S.innerReg dbar j ω * ind_k ω) = _
      rw [show S.indD dbar (k+1) ω = S.indD dbar k ω * ind_k ω from
        congr_fun hFactor ω]
      ring
    rw [hrw]; exact hinnerReg_indD_int
  have hPullInLHS :
      (S.historyBundle k hk).condExpGiven
          (fun ω => S.innerReg dbar j ω * S.indD dbar (k+1) ω) P.μ
        =ᵐ[P.μ]
      (fun ω => S.indD dbar k ω *
        (S.historyBundle k hk).condExpGiven
          (fun ω' => S.innerReg dbar j ω' * ind_k ω') P.μ ω) := by
    have heq : (fun ω => S.innerReg dbar j ω * S.indD dbar (k+1) ω) =
        (fun ω => S.indD dbar k ω * (S.innerReg dbar j ω * ind_k ω)) := by
      funext ω
      rw [show S.indD dbar (k+1) ω = S.indD dbar k ω * ind_k ω from
        congr_fun hFactor ω]
      ring
    rw [heq]
    have hpull :=
      (S.historyBundle k hk).condExpGiven_mul_of_stronglyMeasurable_left
        (f := S.indD dbar k)
        (g := fun ω => S.innerReg dbar j ω * ind_k ω)
        hindDk_sm hindDk_inner_int hinnerReg_indk_int
    filter_upwards [hpull] with ω hω
    simpa [Pi.mul_apply] using hω
  -- Combine: indD k · μ[innerReg j · ind_k | σ_k] =ᵐ indD k · (μ[ind_k|σ_k] · μ[Y_of|σ_k]).
  have hKey :
      (fun ω => S.indD dbar k ω *
        (S.historyBundle k hk).condExpGiven
          (fun ω' => S.innerReg dbar j ω' * ind_k ω') P.μ ω)
        =ᵐ[P.μ]
      (fun ω => S.indD dbar k ω *
        ((S.historyBundle k hk).condExpGiven ind_k P.μ ω *
          (S.historyBundle k hk).condExpGiven (S.Y_of dbar) P.μ ω)) :=
    hPullInLHS.symm.trans hMaster
  -- Overlap: μ[ind_k | σ_k] ω ≠ 0 a.s.
  have hover_k := hA.overlap dbar kFin
  -- Pointwise conclusion.
  filter_upwards [hKey, hover_k] with ω hKω hovω
  -- Unfold innerReg (j+1) at ω.
  have h_inner :
      S.innerReg dbar (j+1) ω =
        (S.historyBundle k hk).condExpGiven
            (fun ω' => S.innerReg dbar j ω' * ind_k ω') P.μ ω
        /
        (S.historyBundle k hk).condExpGiven ind_k P.μ ω := by
    change (if h : j + 1 < n then _ else _) = _
    rw [dif_pos hj]
  change S.innerReg dbar (j+1) ω * S.indD dbar k ω =
      S.indD dbar k ω * (S.historyBundle k hk).condExpGiven (S.Y_of dbar) P.μ ω
  rw [h_inner]
  rcases S.indD_eq_zero_or_one dbar k ω with h0 | h1
  · simp [h0]
  · have hne : (S.historyBundle k hk).condExpGiven ind_k P.μ ω ≠ 0 := by
      intro habs
      rw [habs] at hovω; linarith
    have hKω' : (S.historyBundle k hk).condExpGiven
        (fun ω' => S.innerReg dbar j ω' * ind_k ω') P.μ ω
          = (S.historyBundle k hk).condExpGiven ind_k P.μ ω *
            (S.historyBundle k hk).condExpGiven (S.Y_of dbar) P.μ ω := by
      have := hKω
      rw [h1] at this
      linarith
    rw [hKω', h1]
    field_simp

end PODTRSystem

end PO
end Causalean
