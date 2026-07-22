/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dynamic Treatment Regime: helper lemmas for the general finite horizon

Auxiliary measurability, integrability, consistency, and
σ-algebra-comparison lemmas for the general finite-horizon DTR backdoor proof.
These results are used by `DTR/Induction.lean` and `DTR/Main.lean`.
-/

import Causalean.PO.ID.Exact.DTR.Setup

/-! # Dynamic Treatment Regime Helpers

This file provides auxiliary measurability, integrability, and sigma-algebra
comparison lemmas for the general finite-horizon dynamic treatment regime
proofs. These helpers support the backward-induction and final identification
arguments but are split out because they are shared across DTR files.

Important public lemmas include `historyBundle_sigma_mono`,
`indD_eq_indicator_event`, `stronglyMeasurable_indD_sigma_history`,
`factualAgrees_regime`, `indD_mul_Y_integrable`, `measurable_innerReg`, and
`yVar_notMem_regime`. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace PODTRSystem

variable {P : POSystem} {n : ℕ} {δ : Type} {γ : Fin n → Type}
variable [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable [∀ k, MeasurableSpace (γ k)]

/-! ### Step projection between consecutive history bundles

`historyBundle (k+1)` is `cons (S (k+1)) (cons (D k) (historyBundle k))`.
The joint value at stage `k+1` therefore contains the joint value at stage
`k` starting from coordinate `2`.  `hb_step_proj` extracts that suffix. -/

/-- Projection from the stage-`(k+1)` joint value down to the stage-`k` joint
value.  Drops the fresh `(S (k+1), D k)` pair and keeps the history prefix. -/
noncomputable def hb_step_proj (S : PODTRSystem P n δ γ) (k : ℕ) (h : k + 1 < n) :
    (∀ i, (S.historyBundle (k+1) h).type i) →
      (∀ j, (S.historyBundle k (Nat.lt_of_succ_lt h)).type j) :=
  fun f j => f j.succ.succ

/-- The projection from a stage's extended history to the previous history is measurable. -/
lemma measurable_hb_step_proj (S : PODTRSystem P n δ γ) (k : ℕ) (h : k + 1 < n) :
    Measurable (S.hb_step_proj k h) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply j.succ.succ

/-- Key algebraic identity: the stage-`k` joint value factors through the
stage-`(k+1)` joint value via `hb_step_proj`. -/
lemma hb_jointValue_step_eq (S : PODTRSystem P n δ γ) (k : ℕ) (h : k + 1 < n) :
    (S.historyBundle k (Nat.lt_of_succ_lt h)).jointValue
      = S.hb_step_proj k h ∘ (S.historyBundle (k+1) h).jointValue := by
  funext ω j
  rfl

/-- One-step σ-algebra inclusion: `σ(history k) ≤ σ(history (k+1))`. -/
lemma historyBundle_sigma_mono_step (S : PODTRSystem P n δ γ)
    (k : ℕ) (h : k + 1 < n) :
    (S.historyBundle k (Nat.lt_of_succ_lt h)).sigma
      ≤ (S.historyBundle (k+1) h).sigma := by
  change MeasurableSpace.comap
      (S.historyBundle k (Nat.lt_of_succ_lt h)).jointValue inferInstance ≤
    MeasurableSpace.comap (S.historyBundle (k+1) h).jointValue inferInstance
  rw [S.hb_jointValue_step_eq k h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (S.measurable_hb_step_proj k h).comap_le

/-- Iterated σ-algebra monotonicity: `σ(history j) ≤ σ(history k)` for `j ≤ k`. -/
lemma historyBundle_sigma_mono (S : PODTRSystem P n δ γ)
    (j k : ℕ) (hjk : j ≤ k) (hk : k < n) :
    (S.historyBundle j (lt_of_le_of_lt hjk hk)).sigma
      ≤ (S.historyBundle k hk).sigma := by
  induction k with
  | zero =>
      interval_cases j
      exact le_refl _
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · have hjk' : j ≤ k := Nat.lt_succ_iff.mp hlt
        have hkn : k < n := Nat.lt_of_succ_lt hk
        exact (ih hjk' hkn).trans (S.historyBundle_sigma_mono_step k hk)
      · have hjeq : j = k + 1 := le_antisymm hjk hge
        subst hjeq
        exact le_refl _

/-! ### `indD` integrability and pointwise identities -/

/-- `indD dbar k ω ∈ {0, 1}` for every `ω` and every `k`. -/
lemma indD_eq_zero_or_one (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ∀ (k : ℕ) (ω : P.Ω), S.indD dbar k ω = 0 ∨ S.indD dbar k ω = 1
  | 0, _ => Or.inr rfl
  | k + 1, ω => by
      unfold indD
      by_cases hk : k < n
      · simp only [hk, ↓reduceDIte]
        rcases indD_eq_zero_or_one S dbar k ω with h | h
        · left; simp [h]
        · rcases (S.dVar ⟨k, hk⟩).indicator_eq_one_or_zero (dbar ⟨k, hk⟩) ω with h' | h'
          · right; simp [h, h']
          · left; simp [h, h']
      · simp only [hk, ↓reduceDIte]
        exact indD_eq_zero_or_one S dbar k ω

/-- `indD dbar k` is bounded by 1, hence integrable for finite `μ`. -/
lemma indD_integrable (S : PODTRSystem P n δ γ)
    (dbar : Fin n → δ) (k : ℕ) [IsFiniteMeasure P.μ] :
    Integrable (S.indD dbar k) P.μ := by
  refine Integrable.of_bound (S.measurable_indD dbar k).aestronglyMeasurable 1
    (Filter.Eventually.of_forall ?_)
  intro ω
  rcases S.indD_eq_zero_or_one dbar k ω with h | h <;> simp [h]

/-- Event expression for `indD`: as a set-indicator of the agreement event. -/
lemma indD_eq_indicator_event (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ∀ (k : ℕ) (_ : k ≤ n),
      S.indD dbar k =
        ({ω | ∀ i : Fin n, i.val < k → S.factualD i ω = dbar i}).indicator
          (fun _ => (1 : ℝ))
  | 0, _ => by
      funext ω
      simp [indD]
  | k + 1, h => by
      have hk : k < n := h
      funext ω
      have hrec := indD_eq_indicator_event S dbar k (Nat.le_of_lt hk)
      -- Rewrite indD dbar (k+1) ω in terms of indD dbar k ω * indicator.
      have hstep :
          S.indD dbar (k+1) ω =
            S.indD dbar k ω * (S.dVar ⟨k, hk⟩).indicator (dbar ⟨k, hk⟩) ω := by
        change (if h' : k < n then
                S.indD dbar k ω * (S.dVar ⟨k, h'⟩).indicator (dbar ⟨k, h'⟩) ω
              else S.indD dbar k ω) = _
        simp [hk]
      rw [hstep]
      rw [show S.indD dbar k = _ from hrec]
      by_cases hall : ∀ i : Fin n, i.val < k + 1 → S.factualD i ω = dbar i
      · have hprefix : ∀ i : Fin n, i.val < k → S.factualD i ω = dbar i :=
          fun i hi => hall i (Nat.lt_succ_of_lt hi)
        have hnew : S.factualD ⟨k, hk⟩ ω = dbar ⟨k, hk⟩ :=
          hall ⟨k, hk⟩ (Nat.lt_succ_self _)
        have hmem : ω ∈ {ω | ∀ i : Fin n, i.val < k → S.factualD i ω = dbar i} :=
          hprefix
        have hmem' : ω ∈ {ω | ∀ i : Fin n, i.val < k + 1 → S.factualD i ω = dbar i} :=
          hall
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
        rw [(S.dVar ⟨k, hk⟩).indicator_apply_eq_one hnew]
        ring
      · have hnmem' : ω ∉ {ω | ∀ i : Fin n, i.val < k + 1 → S.factualD i ω = dbar i} :=
          hall
        rw [Set.indicator_of_notMem hnmem']
        by_cases hprefix : ∀ i : Fin n, i.val < k → S.factualD i ω = dbar i
        · have hnew : S.factualD ⟨k, hk⟩ ω ≠ dbar ⟨k, hk⟩ := by
            intro hn
            apply hall
            intro i hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
            · exact hprefix i hi'
            · have : i = ⟨k, hk⟩ := Fin.ext (by simpa using hi')
              rw [this]; exact hn
          have hmem : ω ∈ {ω | ∀ i : Fin n, i.val < k → S.factualD i ω = dbar i} :=
            hprefix
          rw [Set.indicator_of_mem hmem]
          rw [(S.dVar ⟨k, hk⟩).indicator_apply_eq_zero hnew]
          ring
        · have hnmem : ω ∉ {ω | ∀ i : Fin n, i.val < k → S.factualD i ω = dbar i} :=
            hprefix
          rw [Set.indicator_of_notMem hnmem]
          ring

/-- Pointwise factorisation `indD dbar (k+1) = indD dbar k · 1_{D k = dbar k}`. -/
lemma indD_factor_split (S : PODTRSystem P n δ γ)
    (dbar : Fin n → δ) (k : ℕ) (hk : k < n) :
    S.indD dbar (k+1) =
      fun ω => S.indD dbar k ω * (S.dVar ⟨k, hk⟩).indicator (dbar ⟨k, hk⟩) ω := by
  funext ω
  change (if h' : k < n then
          S.indD dbar k ω * (S.dVar ⟨k, h'⟩).indicator (dbar ⟨k, h'⟩) ω
        else S.indD dbar k ω) = _
  simp [hk]

/-! ### Factual-coordinate measurability w.r.t. `historyBundle.sigma`

Because `δ` and `γ k` are arbitrary measurable spaces (no topology assumed),
we state these as `Measurable[B.sigma]` rather than `StronglyMeasurable[B.sigma]`.
The strong-measurability version for the real-valued `indD` is derived
separately below.

The history bundle at stage `m` is
`(S m, D (m-1), …, S 1, D 0, S 0)` (length `2m+1`), so `factualS k'`
is measurable in `historyBundle m` for `k'.val ≤ m`, and `factualD k'`
is measurable in `historyBundle m` for `k'.val < m`. -/

/-- `factualS k'` is `(historyBundle m).sigma`-measurable for `k'.val ≤ m`. -/
lemma measurable_factualS_sigma_history (S : PODTRSystem P n δ γ)
    (m : ℕ) (hm : m < n) (k' : Fin n) (hk' : k'.val ≤ m) :
    Measurable[(S.historyBundle m hm).sigma] (S.factualS k') := by
  induction m with
  | zero =>
      have hkv : k'.val = 0 := Nat.le_zero.mp hk'
      have hkeq : k' = ⟨0, hm⟩ := Fin.ext (by simp [hkv])
      subst hkeq
      intro s hs
      refine ⟨(fun f : ∀ i, (S.historyBundle 0 hm).type i =>
                f ⟨0, Nat.zero_lt_succ 0⟩) ⁻¹' s, ?_, ?_⟩
      · exact measurable_pi_apply _ hs
      · rfl
  | succ m ih =>
      rcases Nat.lt_or_ge k'.val (m + 1) with hlt | hge
      · have hkm : k'.val ≤ m := Nat.lt_succ_iff.mp hlt
        have hmn : m < n := Nat.lt_of_succ_lt hm
        have hrec := ih hmn hkm
        -- Upgrade via σ-algebra monotonicity.
        intro s hs
        exact S.historyBundle_sigma_mono_step m hm _ (hrec hs)
      · have hkeq : k'.val = m + 1 := le_antisymm hk' hge
        have hkfin : k' = ⟨m + 1, hm⟩ := Fin.ext hkeq
        subst hkfin
        intro s hs
        refine ⟨(fun f : ∀ i, (S.historyBundle (m+1) hm).type i =>
                  f ⟨0, Nat.zero_lt_succ _⟩) ⁻¹' s, ?_, ?_⟩
        · exact measurable_pi_apply _ hs
        · rfl

/-- `factualD k'` is `(historyBundle m).sigma`-measurable for `k'.val < m`. -/
lemma measurable_factualD_sigma_history (S : PODTRSystem P n δ γ)
    (m : ℕ) (hm : m < n) (k' : Fin n) (hk' : k'.val < m) :
    Measurable[(S.historyBundle m hm).sigma] (S.factualD k') := by
  induction m with
  | zero =>
      exact absurd hk' (Nat.not_lt_zero _)
  | succ m ih =>
      rcases Nat.lt_or_ge k'.val m with hlt | hge
      · have hmn : m < n := Nat.lt_of_succ_lt hm
        intro s hs
        exact S.historyBundle_sigma_mono_step m hm _ ((ih hmn hlt) hs)
      · have hkeq : k'.val = m := by omega
        have hmlt : m < n := Nat.lt_of_succ_lt hm
        have hkfin : k' = ⟨m, hmlt⟩ := Fin.ext hkeq
        intro s hs
        -- index 1 in historyBundle (m+1) — use a Fin literal.
        let i1 : Fin ((S.historyBundle (m+1) hm).n) := ⟨1, by
          -- The length of historyBundle (m+1) is (historyBundle m).n + 1 + 1 ≥ 2.
          change 1 < (S.historyBundle m hmlt).n + 1 + 1
          omega⟩
        refine ⟨(fun f : ∀ i, (S.historyBundle (m+1) hm).type i => f i1) ⁻¹' s, ?_, ?_⟩
        · exact measurable_pi_apply _ hs
        · rw [hkfin]; rfl

/-- The real-valued indicator `dVar ⟨k', hk⟩.indicator (dbar ⟨k', hk⟩)` is
`(historyBundle m).sigma`-strongly-measurable for `k' < m`. -/
lemma stronglyMeasurable_indicator_dVar_sigma_history (S : PODTRSystem P n δ γ)
    (m : ℕ) (hm : m < n) (k' : Fin n) (hk' : k'.val < m) (x : δ) :
    StronglyMeasurable[(S.historyBundle m hm).sigma]
      ((S.dVar k').indicator x) := by
  have hfmeas := S.measurable_factualD_sigma_history m hm k' hk'
  have hev : MeasurableSet[(S.historyBundle m hm).sigma]
      ((S.dVar k').event x) :=
    hfmeas (MeasurableSet.singleton x)
  have hmeas : Measurable[(S.historyBundle m hm).sigma]
      ((S.dVar k').indicator x) := by
    unfold POVar.indicator
    exact measurable_const.indicator hev
  exact hmeas.stronglyMeasurable

/-- The joint-agreement indicator `indD dbar m'` is
`(historyBundle m).sigma`-strongly-measurable for `m' ≤ m`. -/
lemma stronglyMeasurable_indD_sigma_history (S : PODTRSystem P n δ γ)
    (m : ℕ) (hm : m < n) (dbar : Fin n → δ) :
    ∀ (m' : ℕ) (_ : m' ≤ m),
      StronglyMeasurable[(S.historyBundle m hm).sigma] (S.indD dbar m')
  | 0, _ => by
      unfold indD
      exact stronglyMeasurable_const
  | m' + 1, h => by
      have hm' : m' < n := lt_of_lt_of_le h (Nat.le_of_lt hm)
      have hrec := stronglyMeasurable_indD_sigma_history S m hm dbar m'
        (Nat.le_of_succ_le h)
      have hmlt : m' < m := h
      have hind := S.stronglyMeasurable_indicator_dVar_sigma_history
        m hm ⟨m', hm'⟩ hmlt (dbar ⟨m', hm'⟩)
      -- `indD (m'+1) = indD m' * indicator`.
      have heq : S.indD dbar (m' + 1) = fun ω =>
          S.indD dbar m' ω * (S.dVar ⟨m', hm'⟩).indicator (dbar ⟨m', hm'⟩) ω :=
        S.indD_factor_split dbar m' hm'
      rw [heq]
      -- `StronglyMeasurable` closed under mul.
      exact hrec.mul hind

/-! ### Multi-target consistency for the DTR regime -/

/-- Helper: for each `k ≤ n`, `FactualAgrees` for `regimeUpTo dbar k` holds on
the event "`factualD i = dbar i` for all `i.val < k`". -/
lemma factualAgrees_regimeUpTo (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ∀ (k : ℕ) (h : k ≤ n) (ω : P.Ω),
      (∀ i : Fin n, i.val < k → S.factualD i ω = dbar i) →
        P.FactualAgrees (S.regimeUpTo dbar k h) ω
  | 0, _, ω, _ => by
      change P.FactualAgrees (S.regimeUpToAux dbar 0 (by exact Nat.zero_le n)).1 ω
      unfold regimeUpToAux
      exact POSystem.factualAgrees_empty ω
  | k + 1, h, ω, hall => by
      have hk : k < n := h
      have hprefix : ∀ i : Fin n, i.val < k → S.factualD i ω = dbar i :=
        fun i hi => hall i (Nat.lt_succ_of_lt hi)
      have hnew : S.factualD ⟨k, hk⟩ ω = dbar ⟨k, hk⟩ :=
        hall ⟨k, hk⟩ (Nat.lt_succ_self _)
      have hrec := factualAgrees_regimeUpTo S dbar k (Nat.le_of_lt hk) ω hprefix
      -- Unfold regimeUpTo at k+1 to a sqcup.
      change P.FactualAgrees (S.regimeUpToAux dbar (k+1) h).1 ω
      unfold regimeUpToAux
      simp only
      apply POSystem.factualAgrees_sqcup
      · exact (S.dVar ⟨k, hk⟩).factualAgrees_single (dbar ⟨k, hk⟩) hnew
      · -- hrec is about S.regimeUpTo dbar k _ = (S.regimeUpToAux dbar k _).1.
        exact hrec

/-- General multi-target consistency: every `ω` in the full agreement event
factually agrees with `S.regime dbar`. -/
lemma factualAgrees_regime (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ∀ ω ∈ {ω | ∀ i : Fin n, S.factualD i ω = dbar i},
      P.FactualAgrees (S.regime dbar) ω := by
  intro ω hω
  exact S.factualAgrees_regimeUpTo dbar n (le_refl n) ω (fun i _ => hω i)

/-! ### Integrability of products `indD · Y` -/

/-- `indD dbar k · Y(dbar)` is integrable, bounded by `|Y(dbar)|`. -/
lemma indD_mul_Y_integrable (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) (k : ℕ)
    (hY : Integrable (S.Y_of dbar) P.μ) :
    Integrable (fun ω => S.indD dbar k ω * S.Y_of dbar ω) P.μ := by
  refine hY.mono
    ((S.measurable_indD dbar k).mul (S.measurable_Y_of dbar)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rcases S.indD_eq_zero_or_one dbar k ω with h | h <;> simp [h]

/-! ### Measurability of `innerReg` -/

/-- `innerReg dbar j` is measurable for every `j`. -/
lemma measurable_innerReg (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    ∀ j : ℕ, Measurable (S.innerReg dbar j)
  | 0 => by
      unfold innerReg
      by_cases hn : 0 < n
      · simp only [hn, ↓reduceDIte]
        set B := S.historyBundle (n-1) (Nat.sub_lt hn Nat.one_pos)
        have hN :=
          (B.stronglyMeasurable_condExpGiven
            (μ := P.μ) (fun ω' => S.factualY ω' * S.indD dbar n ω')).measurable
        have hD :=
          (B.stronglyMeasurable_condExpGiven
            (μ := P.μ) (S.indD dbar n)).measurable
        exact hN.div hD
      · simp only [hn, ↓reduceDIte]
        exact measurable_const
  | j + 1 => by
      unfold innerReg
      by_cases hj : j + 1 < n
      · simp only [hj, ↓reduceDIte]
        have hkk : n - j - 2 < n := by omega
        set kFin : Fin n := ⟨n - j - 2, hkk⟩
        set ind_k : P.Ω → ℝ := (S.dVar kFin).indicator (dbar kFin)
        set B := S.historyBundle (n - j - 2) hkk
        have hN :=
          (B.stronglyMeasurable_condExpGiven
            (μ := P.μ) (fun ω' => S.innerReg dbar j ω' * ind_k ω')).measurable
        have hD :=
          (B.stronglyMeasurable_condExpGiven (μ := P.μ) ind_k).measurable
        exact hN.div hD
      · simp only [hj, ↓reduceDIte]
        exact S.measurable_innerReg dbar j

/-! ### Integrability of `innerReg` is proved in `StrongCancellation.lean`,
where it follows directly from the strengthened a.e. identity
`innerReg j =ᵐ indD (n-j-1) · μ[Y_of dbar | σ_{n-j-1}]`.  The previous
uniform-`c` bound (`|innerReg j+1| ≤ |N|/c`) no longer applies under the
relaxed *pointwise* overlap hypothesis. -/

/-! ### Outcome variable is outside every regime target -/

/-- The outcome node `Y` is not a target of `S.regime dbar`. -/
lemma yVar_notMem_regime (S : PODTRSystem P n δ γ) (dbar : Fin n → δ) :
    S.yVar.v ∉ (S.regime dbar).target := by
  intro hmem
  have hmem' : S.yVar.v ∈ S.regimeTarget n := by
    rw [← S.regimeUpTo_target_eq dbar n (le_refl n)]
    exact hmem
  rcases (S.regimeTarget_mem_iff n (le_refl n) S.yVar.v).mp hmem' with ⟨i, _, heq⟩
  exact (S.distinctDY i) heq.symm

end PODTRSystem

end PO
end Causalean
