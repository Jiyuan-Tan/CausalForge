/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dynamic Treatment Regime: strengthened cancellation identity

Under the **pointwise** overlap assumption (no uniform constant `c > 0`),
the proof of integrability of `innerReg dbar j` is interlocked with the
cancellation identity proved by induction in `Induction.lean`.  This file
proves a **single** unified inductive predicate

    P j ↔ innerReg dbar j =ᵐ[μ] (fun ω => indD dbar (n-1-j) ω
                                  · μ[Y_of dbar | σ(historyBundle (n-1-j))] ω)
          ∧ Integrable (innerReg dbar j) μ

(`cdtr_strong`).  From the a.e. identity, integrability of `innerReg j`
follows because the RHS is the pointwise product of an indicator (bounded
by `1`) and an integrable conditional expectation.

The previous direct-bound proof of integrability used a uniform `c > 0`
overlap, which no longer applies.

Downstream:

* `innerReg_integrable` is re-derived here
  from `cdtr_strong`.
* `cdtr_strong` directly implies the weaker product-form identity used by
  `cdtr_iter` in `Main.lean`.
-/

import Causalean.PO.ID.Exact.DTR.Induction

/-! # Dynamic Treatment Regime Strong Cancellation

This file proves the strengthened cancellation identity needed for
finite-horizon dynamic-treatment-regime identification under pointwise overlap.
The main theorem `PODTRSystem.cdtr_strong` carries two facts through the same
backward induction: `innerReg dbar j` is almost surely the product of the
partial treatment-regime indicator `indD dbar (n - 1 - j)` and the conditional
expectation of `Y_of dbar` given the corresponding history bundle, and
`innerReg dbar j` is integrable.

The derived lemma `PODTRSystem.innerReg_integrable` recovers the public
integrability statement from this stronger a.e. identity. This avoids any
uniform-overlap bound: after cancellation, integrability follows from a bounded
indicator multiplying an integrable conditional expectation. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace PODTRSystem

variable {P : POSystem} {n : ℕ} {δ : Type} {γ : Fin n → Type}
variable [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable [∀ k, MeasurableSpace (γ k)]

/-- Helper: integrability of `indD k · μ[Y_of | σ_k]` for `k < n`.

The conditional expectation is integrable for free; multiplying by the
bounded indicator `indD k` (∈ {0,1}) preserves integrability. -/
private lemma indD_mul_condExpY_integrable
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : PODTRSystem P n δ γ) (dbar : Fin n → δ)
    (k : ℕ) (hk : k < n) :
    Integrable (fun ω => S.indD dbar k ω *
      (S.historyBundle k hk).condExpGiven (S.Y_of dbar) P.μ ω) P.μ := by
  have hCE_int :
      Integrable ((S.historyBundle k hk).condExpGiven (S.Y_of dbar) P.μ) P.μ :=
    (S.historyBundle k hk).integrable_condExpGiven _
  refine hCE_int.mono
    ((S.measurable_indD dbar k).mul
      ((S.historyBundle k hk).stronglyMeasurable_condExpGiven _).measurable
        ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rcases S.indD_eq_zero_or_one dbar k ω with h | h <;> simp [h]

/-! ### Strengthened cancellation identity (a.e.)

The strong identity says `innerReg j` literally equals (a.e.) the product
of the partial indicator and the conditional expectation, _without_ the
extra `· indD` factor on the LHS that was used in `cdtr_step`.  This form
already encodes vanishing of `innerReg j` on `{indD = 0}`.

Both the identity and the integrability of `innerReg j` are proved
together by induction on `j`. -/

/-- Joint inductive invariant for the strengthened cancellation:

* (strong identity) `innerReg dbar j =ᵐ indD (n-1-j) · μ[Y_of dbar | σ_{n-1-j}]`;
* (integrability)  `Integrable (innerReg dbar j) P.μ`. -/
theorem cdtr_strong [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : PODTRSystem P n δ γ) (hA : S.Assumptions) (dbar : Fin n → δ)
    (hn : 0 < n) :
    ∀ j : ℕ, j < n →
      ((S.innerReg dbar j) =ᵐ[P.μ]
        (fun ω => S.indD dbar (n - 1 - j) ω *
          (S.historyBundle (n - 1 - j) (by omega)).condExpGiven
            (S.Y_of dbar) P.μ ω))
      ∧ Integrable (S.innerReg dbar j) P.μ := by
  intro j hj
  induction j with
  | zero =>
    -- ============================================================
    -- Base case (j = 0).  Strengthen `cdtr_base` via vanishing.
    -- ============================================================
    set m : ℕ := n - 1 with hm_def
    have hm_lt : m < n := Nat.sub_lt hn Nat.one_pos
    have hm_succ : m + 1 = n := by omega
    have hzero_idx : n - 1 - 0 = m := by omega
    set kLast : Fin n := ⟨m, hm_lt⟩ with hkLast_def
    -- Helper integrabilities.
    have hYof_int : Integrable (S.Y_of dbar) P.μ := hA.integrable_Y dbar
    have hindLast_int :
        Integrable ((S.dVar kLast).indicator (dbar kLast)) P.μ :=
      (S.dVar kLast).integrable_indicator (dbar kLast)
    have hindD_n_int : Integrable (S.indD dbar n) P.μ := S.indD_integrable dbar n
    have hYindLast_int :
        Integrable (fun ω => S.factualY ω *
          (S.dVar kLast).indicator (dbar kLast) ω) P.μ := by
      exact (S.dVar kLast).integrable_mul_indicator
        (dbar kLast) hA.integrable_factualY S.measurable_factualY
    have hindD_m_sm :
        StronglyMeasurable[(S.historyBundle m hm_lt).sigma] (S.indD dbar m) :=
      S.stronglyMeasurable_indD_sigma_history m hm_lt dbar m (le_refl m)
    -- Pointwise factorisation indD n = indD m * indicator.
    have hFactor : S.indD dbar n = fun ω =>
        S.indD dbar m ω * (S.dVar kLast).indicator (dbar kLast) ω := by
      funext ω
      have h_eq : S.indD dbar n ω = S.indD dbar (m + 1) ω := by rw [hm_succ]
      rw [h_eq]
      exact congr_fun (S.indD_factor_split dbar m hm_lt) ω
    -- Numerator pull-out: μ[factualY · indD n | σ_m]
    --                  =ᵐ indD m · μ[factualY · ind_last | σ_m].
    have hYind_int :
        Integrable (fun ω => S.factualY ω * S.indD dbar n ω) P.μ := by
      refine hA.integrable_factualY.mono
        (S.measurable_factualY.mul (S.measurable_indD dbar n)).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun ω => ?_)
      rcases S.indD_eq_zero_or_one dbar n ω with h | h <;> simp [h]
    have hN_pull :
        (S.historyBundle m hm_lt).condExpGiven
            (fun ω => S.factualY ω * S.indD dbar n ω) P.μ
          =ᵐ[P.μ]
        (fun ω => S.indD dbar m ω *
          (S.historyBundle m hm_lt).condExpGiven
            (fun ω' => S.factualY ω' *
              (S.dVar kLast).indicator (dbar kLast) ω') P.μ ω) := by
      have hprod_int :
          Integrable (S.indD dbar m *
            fun ω => S.factualY ω *
              (S.dVar kLast).indicator (dbar kLast) ω) P.μ := by
        have heq :
            (S.indD dbar m *
              fun ω => S.factualY ω *
                (S.dVar kLast).indicator (dbar kLast) ω) =
              fun ω => S.factualY ω * S.indD dbar n ω := by
          funext ω
          change S.indD dbar m ω *
              (S.factualY ω * (S.dVar kLast).indicator (dbar kLast) ω) = _
          rw [show S.indD dbar n ω = S.indD dbar m ω *
            (S.dVar kLast).indicator (dbar kLast) ω from congr_fun hFactor ω]
          ring
        rw [heq]; exact hYind_int
      have hpull :=
        (S.historyBundle m hm_lt).condExpGiven_mul_of_stronglyMeasurable_left
          (f := S.indD dbar m)
          (g := fun ω => S.factualY ω *
            (S.dVar kLast).indicator (dbar kLast) ω)
          hindD_m_sm hprod_int hYindLast_int
      have heqfun :
          (S.historyBundle m hm_lt).condExpGiven
              (fun ω => S.factualY ω * S.indD dbar n ω) P.μ
            = (S.historyBundle m hm_lt).condExpGiven
              (fun ω => S.indD dbar m ω *
                (S.factualY ω *
                  (S.dVar kLast).indicator (dbar kLast) ω)) P.μ := by
        congr 1
        funext ω
        rw [show S.indD dbar n ω = S.indD dbar m ω *
          (S.dVar kLast).indicator (dbar kLast) ω from congr_fun hFactor ω]
        ring
      rw [heqfun]
      have hpull' :=
        (S.historyBundle m hm_lt).condExpGiven_mul_of_stronglyMeasurable_left
          (f := S.indD dbar m)
          (g := fun ω => S.factualY ω *
            (S.dVar kLast).indicator (dbar kLast) ω)
          hindD_m_sm
          (by
            have heq :
                (S.indD dbar m *
                  fun ω => S.factualY ω *
                    (S.dVar kLast).indicator (dbar kLast) ω)
                  = fun ω => S.indD dbar m ω *
                    (S.factualY ω *
                      (S.dVar kLast).indicator (dbar kLast) ω) := rfl
            rw [heq] at hprod_int ⊢
            exact hprod_int)
          hYindLast_int
      filter_upwards [hpull'] with ω hω
      simpa [Pi.mul_apply] using hω
    -- Denominator pull-out: μ[indD n | σ_m] =ᵐ indD m · μ[ind_last | σ_m].
    have hD_pull :
        (S.historyBundle m hm_lt).condExpGiven (S.indD dbar n) P.μ
          =ᵐ[P.μ]
        (fun ω => S.indD dbar m ω *
          (S.historyBundle m hm_lt).condExpGiven
            ((S.dVar kLast).indicator (dbar kLast)) P.μ ω) := by
      have hprod_indD_int :
          Integrable (S.indD dbar m * (S.dVar kLast).indicator (dbar kLast)) P.μ := by
        have heq :
            S.indD dbar m * (S.dVar kLast).indicator (dbar kLast)
              = fun ω => S.indD dbar m ω *
                (S.dVar kLast).indicator (dbar kLast) ω := rfl
        rw [heq, ← hFactor]; exact hindD_n_int
      have hpull :=
        (S.historyBundle m hm_lt).condExpGiven_mul_of_stronglyMeasurable_left
          (f := S.indD dbar m) (g := (S.dVar kLast).indicator (dbar kLast))
          hindD_m_sm hprod_indD_int hindLast_int
      have heqfun :
          (S.historyBundle m hm_lt).condExpGiven (S.indD dbar n) P.μ
            = (S.historyBundle m hm_lt).condExpGiven
              (fun ω => S.indD dbar m ω *
                (S.dVar kLast).indicator (dbar kLast) ω) P.μ := by
        rw [hFactor]
      rw [heqfun]
      filter_upwards [hpull] with ω hω
      simpa [Pi.mul_apply] using hω
    -- The strong identity at j = 0 (independent of cdtr_base).
    have hStrong0 :
        (S.innerReg dbar 0) =ᵐ[P.μ]
          (fun ω => S.indD dbar m ω *
            (S.historyBundle m hm_lt).condExpGiven (S.Y_of dbar) P.μ ω) := by
      have hCE_base := S.cdtr_base hA dbar hn
      filter_upwards [hCE_base, hN_pull, hD_pull, hA.overlap dbar kLast]
        with ω hCE hNω hDω hov
      -- innerReg 0 ω = N(ω)/D(ω) (definitionally).
      have h_inner :
          S.innerReg dbar 0 ω =
            (S.historyBundle m hm_lt).condExpGiven
              (fun ω' => S.factualY ω' * S.indD dbar n ω') P.μ ω
            /
            (S.historyBundle m hm_lt).condExpGiven (S.indD dbar n) P.μ ω := by
        change (if h : 0 < n then _ else _) = _
        rw [dif_pos hn]
      rcases S.indD_eq_zero_or_one dbar m ω with h0 | h1
      · -- indD m ω = 0: both N and D vanish.
        rw [h_inner, hNω, hDω, h0]
        simp
      · -- indD m ω = 1: cdtr_base provides the equality directly.
        -- hCE : innerReg 0 ω · indD m ω = indD m ω · μ[Y_of|σ_m] ω
        -- with indD m ω = 1, both sides simplify.
        rw [show S.indD dbar m ω = (1 : ℝ) from h1] at hCE
        simp only [mul_one, one_mul] at hCE
        rw [hCE, h1, one_mul]
    -- Now assemble the final pair.
    refine ⟨?_, ?_⟩
    · -- Strong identity at index n - 1 - 0.  Bridge `m = n - 1 - 0`.
      have hbridge :
          (S.historyBundle (n - 1 - 0) (by omega : n - 1 - 0 < n)).condExpGiven
              (S.Y_of dbar) P.μ
            = (S.historyBundle m hm_lt).condExpGiven (S.Y_of dbar) P.μ := by
        have h_heq :
            HEq
              ((S.historyBundle (n - 1 - 0) (by omega : n - 1 - 0 < n)).condExpGiven
                (S.Y_of dbar) P.μ)
              ((S.historyBundle m hm_lt).condExpGiven (S.Y_of dbar) P.μ) := by
          congr 1
        exact eq_of_heq h_heq
      have hindD_eq : S.indD dbar (n - 1 - 0) = S.indD dbar m := by
        rw [hzero_idx]
      filter_upwards [hStrong0] with ω hω
      rw [hω, ← hindD_eq, ← hbridge]
    · -- Integrability from strong identity + RHS integrability.
      have hRHS := S.indD_mul_condExpY_integrable dbar m hm_lt
      exact hRHS.congr hStrong0.symm
  | succ j ih =>
    -- ============================================================
    -- Step (j → j + 1).  We use `cdtr_step` for the weak form, then
    -- strengthen via vanishing of `innerReg (j+1)` on `{indD k = 0}`.
    -- ============================================================
    have hj' : j < n := Nat.lt_of_succ_lt hj
    obtain ⟨ihStrong, ihInt⟩ := ih hj'
    set k : ℕ := n - j - 2 with hk_def
    have hk_lt : k < n := by omega
    have hk1 : k + 1 < n := by omega
    set kFin : Fin n := ⟨k, hk_lt⟩ with hkFin_def
    set ind_k : P.Ω → ℝ := (S.dVar kFin).indicator (dbar kFin) with hind_k_def
    have hk1_idx : n - j - 1 = k + 1 := by omega
    have hkstep_idx : n - 1 - (j + 1) = k := by omega
    have hk_idx_old : n - 1 - j = k + 1 := by omega
    have hk1_eq_kp1 : n - j - 1 = k + 1 := by omega
    -- Bridge the historyBundle proof argument via Nat equality.
    have hbridge_kp1 :
        (S.historyBundle (n - 1 - j) (by omega : n - 1 - j < n)).condExpGiven
            (S.Y_of dbar) P.μ
          = (S.historyBundle (k + 1) hk1).condExpGiven (S.Y_of dbar) P.μ := by
      have h_heq :
          HEq
            ((S.historyBundle (n - 1 - j) (by omega : n - 1 - j < n)).condExpGiven
              (S.Y_of dbar) P.μ)
            ((S.historyBundle (k + 1) hk1).condExpGiven (S.Y_of dbar) P.μ) := by
        congr 1; simp [hk_idx_old]
      exact eq_of_heq h_heq
    have hbridge_kp1' :
        (S.historyBundle (n - j - 1) (by omega : n - j - 1 < n)).condExpGiven
            (S.Y_of dbar) P.μ
          = (S.historyBundle (k + 1) hk1).condExpGiven (S.Y_of dbar) P.μ := by
      have h_heq :
          HEq
            ((S.historyBundle (n - j - 1) (by omega : n - j - 1 < n)).condExpGiven
              (S.Y_of dbar) P.μ)
            ((S.historyBundle (k + 1) hk1).condExpGiven (S.Y_of dbar) P.μ) := by
        congr 1; simp [hk1_eq_kp1]
      exact eq_of_heq h_heq
    have hindD_eq_old : S.indD dbar (n - 1 - j) = S.indD dbar (k + 1) := by
      rw [hk_idx_old]
    have hindD_eq_new : S.indD dbar (n - j - 1) = S.indD dbar (k + 1) := by
      rw [hk1_eq_kp1]
    -- Recover the strong IH at index k+1.
    have ihStrong' :
        (S.innerReg dbar j) =ᵐ[P.μ]
          (fun ω => S.indD dbar (k+1) ω *
            (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) := by
      filter_upwards [ihStrong] with ω hω
      rw [hω, ← hbridge_kp1, hindD_eq_old]
    -- Recover the weak IH (for `cdtr_step`).
    have ihWeak :
        (fun ω => S.innerReg dbar j ω * S.indD dbar (n - j - 1) ω)
          =ᵐ[P.μ]
        (fun ω => S.indD dbar (n - j - 1) ω *
          (S.historyBundle (n - j - 1) (by omega)).condExpGiven
            (S.Y_of dbar) P.μ ω) := by
      filter_upwards [ihStrong'] with ω hω
      rw [hω, hindD_eq_new, hbridge_kp1']
      -- Goal: (indD (k+1) ω · μ[Y|σ_{k+1}] ω) · indD (k+1) ω
      --     = indD (k+1) ω · μ[Y|σ_{k+1}] ω.
      rcases S.indD_eq_zero_or_one dbar (k + 1) ω with h | h
      · rw [h]; ring
      · rw [h]; ring
    -- Apply cdtr_step to get the weak form at j+1.
    have hk2 : n - j - 2 < n := hk_lt
    have hWeak := S.cdtr_step hA dbar j hj hk2 ihInt ihWeak
    -- Strong-meas of indD k on σ_k.
    have hindDk_sm :
        StronglyMeasurable[(S.historyBundle k hk_lt).sigma] (S.indD dbar k) :=
      S.stronglyMeasurable_indD_sigma_history k hk_lt dbar k (le_refl k)
    -- Pointwise factorisation indD (k+1) = indD k · ind_k.
    have hFactor : S.indD dbar (k+1) = fun ω => S.indD dbar k ω * ind_k ω :=
      S.indD_factor_split dbar k hk_lt
    -- Integrability of innerReg j · ind_k.
    have hinnerReg_indk_int :
        Integrable (fun ω => S.innerReg dbar j ω * ind_k ω) P.μ := by
      dsimp [ind_k]
      exact (S.dVar kFin).integrable_mul_indicator
        (dbar kFin) ihInt (S.measurable_innerReg dbar j)
    have hCE_int_k1 :
        Integrable
          ((S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ) P.μ :=
      (S.historyBundle (k+1) hk1).integrable_condExpGiven _
    have h_indk_CE_int :
        Integrable (fun ω => ind_k ω *
          (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) P.μ := by
      dsimp [ind_k]
      have hmul := (S.dVar kFin).integrable_mul_indicator (dbar kFin)
        hCE_int_k1
        ((S.historyBundle (k+1) hk1).stronglyMeasurable_condExpGiven _).measurable
      exact hmul.congr (Filter.Eventually.of_forall (fun ω => by ring))
    -- innerReg j · ind_k =ᵐ indD k · (ind_k · μ[Y|σ_{k+1}]).
    have hAEinnerReg_indk :
        (fun ω => S.innerReg dbar j ω * ind_k ω) =ᵐ[P.μ]
          (fun ω => S.indD dbar k ω *
            (ind_k ω *
              (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)) := by
      filter_upwards [ihStrong'] with ω hω
      rw [hω]
      -- LHS: indD(k+1) ω · μ[Y|σ_{k+1}] ω · ind_k ω.
      -- After hFactor: indD k ω · ind_k ω · μ[Y|σ_{k+1}] ω · ind_k ω.
      -- Use ind_k ∈ {0,1}: ind_k^2 = ind_k.
      rw [show S.indD dbar (k+1) ω = S.indD dbar k ω * ind_k ω from
        congr_fun hFactor ω]
      rcases (S.dVar kFin).indicator_eq_one_or_zero (dbar kFin) ω with h | h
      · -- ind_k ω = 1.
        show S.indD dbar k ω * ind_k ω *
            (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω * ind_k ω
          = S.indD dbar k ω *
            (ind_k ω *
              (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)
        rw [show ind_k ω = (1 : ℝ) from h]; ring
      · rw [show ind_k ω = (0 : ℝ) from h]; ring
    -- Now: μ[innerReg j · ind_k | σ_k] =ᵐ
    --      indD k · μ[ind_k · μ[Y|σ_{k+1}] | σ_k].
    have hN'_pullout :
        (S.historyBundle k hk_lt).condExpGiven
            (fun ω => S.innerReg dbar j ω * ind_k ω) P.μ
          =ᵐ[P.μ]
        (fun ω => S.indD dbar k ω *
          (S.historyBundle k hk_lt).condExpGiven
            (fun ω' => ind_k ω' *
              (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω')
            P.μ ω) := by
      have hCongr :=
        (S.historyBundle k hk_lt).condExpGiven_congr_ae hAEinnerReg_indk
      have hindD_indkY_int :
          Integrable (S.indD dbar k * fun ω => ind_k ω *
            (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω) P.μ := by
        have hae_eq :
            (S.indD dbar k * fun ω => ind_k ω *
              (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)
              =ᵐ[P.μ] (fun ω => S.innerReg dbar j ω * ind_k ω) :=
          hAEinnerReg_indk.symm
        exact hinnerReg_indk_int.congr hae_eq.symm
      have hpull :=
        (S.historyBundle k hk_lt).condExpGiven_mul_of_stronglyMeasurable_left
          (f := S.indD dbar k)
          (g := fun ω => ind_k ω *
            (S.historyBundle (k+1) hk1).condExpGiven (S.Y_of dbar) P.μ ω)
          hindDk_sm hindD_indkY_int h_indk_CE_int
      filter_upwards [hCongr, hpull] with ω hCω hPω
      rw [hCω]
      simpa [Pi.mul_apply] using hPω
    -- Strong identity at j+1.
    have hover_k := hA.overlap dbar kFin
    -- Bridge the (n - j - 2) index in hWeak to k.
    have hWeak' :
        (fun ω => S.innerReg dbar (j+1) ω * S.indD dbar k ω)
          =ᵐ[P.μ]
        (fun ω => S.indD dbar k ω *
          (S.historyBundle k hk_lt).condExpGiven (S.Y_of dbar) P.μ ω) := by
      have hidx : n - j - 2 = k := rfl
      simp only [hidx] at hWeak
      exact hWeak
    have hStrong_jp1 :
        (S.innerReg dbar (j+1)) =ᵐ[P.μ]
          (fun ω => S.indD dbar k ω *
            (S.historyBundle k hk_lt).condExpGiven (S.Y_of dbar) P.μ ω) := by
      filter_upwards [hWeak', hN'_pullout, hover_k] with ω hWω hNω hov
      have h_inner :
          S.innerReg dbar (j+1) ω =
            (S.historyBundle k hk_lt).condExpGiven
                (fun ω' => S.innerReg dbar j ω' * ind_k ω') P.μ ω
            /
            (S.historyBundle k hk_lt).condExpGiven ind_k P.μ ω := by
        change (if h : j + 1 < n then _ else _) = _
        rw [dif_pos hj]
      rcases S.indD_eq_zero_or_one dbar k ω with h0 | h1
      · -- indD k ω = 0: numerator vanishes (hN'_pullout has factor indD k);
        -- denominator > 0 (overlap); innerReg(j+1) = 0.
        have hN0 :
            (S.historyBundle k hk_lt).condExpGiven
              (fun ω' => S.innerReg dbar j ω' * ind_k ω') P.μ ω = 0 := by
          rw [hNω, h0]; simp
        rw [h_inner, hN0, h0]
        simp
      · -- indD k ω = 1: weak form gives the equality (after multiplying out 1).
        rw [show S.indD dbar k ω = (1 : ℝ) from h1] at hWω
        simp only [mul_one, one_mul] at hWω
        rw [hWω, h1, one_mul]
    refine ⟨?_, ?_⟩
    · -- Strong identity at index n - 1 - (j + 1) = k.
      -- Bridge `S.historyBundle (n - 1 - (j + 1)) ...` to `S.historyBundle k hk_lt`.
      have hbridge_step :
          (S.historyBundle (n - 1 - (j + 1)) (by omega : n - 1 - (j + 1) < n)).condExpGiven
              (S.Y_of dbar) P.μ
            = (S.historyBundle k hk_lt).condExpGiven (S.Y_of dbar) P.μ := by
        have h_heq :
            HEq
              ((S.historyBundle (n - 1 - (j + 1)) (by omega : n - 1 - (j + 1) < n)).condExpGiven
                (S.Y_of dbar) P.μ)
              ((S.historyBundle k hk_lt).condExpGiven (S.Y_of dbar) P.μ) := by
          congr 1; simp [hkstep_idx]
        exact eq_of_heq h_heq
      have hindD_eq_step : S.indD dbar (n - 1 - (j + 1)) = S.indD dbar k := by
        rw [hkstep_idx]
      filter_upwards [hStrong_jp1] with ω hω
      rw [hω, hindD_eq_step, hbridge_step]
    · -- Integrability.
      have hRHS := S.indD_mul_condExpY_integrable dbar k hk_lt
      exact hRHS.congr hStrong_jp1.symm

/-! ### Derived: integrability of `innerReg`

Replaces the earlier helper statement from `Helpers.lean`,
now derived from `cdtr_strong`. -/

/-- `innerReg dbar j` is integrable for every `j < n`.

Proof: `innerReg j` is a.e. equal to the bounded indicator times the
integrable conditional expectation `μ[Y_of dbar | σ_{n-1-j}]`.  See
`cdtr_strong`. -/
lemma innerReg_integrable [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : PODTRSystem P n δ γ) (hA : S.Assumptions) (dbar : Fin n → δ)
    (j : ℕ) (hj : j < n) : Integrable (S.innerReg dbar j) P.μ := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hj
  exact (S.cdtr_strong hA dbar hn j hj).2

end PODTRSystem

end PO
end Causalean
