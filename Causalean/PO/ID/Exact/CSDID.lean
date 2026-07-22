/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Callaway--Sant'Anna staggered-adoption DID identification of ATT(g, t)

Implements `def:po-cs-did-system`, `def:po-cs-did-assumptions`, and
`prop:po-cs-did-att` from Basic Concepts.tex (no-covariate version).

Conventions
-----------
* Periods are indexed by `Fin T` with `2 ≤ T`.  Inside Lean we use 0-based
  indexing, so the .tex statement "for `2 ≤ g ≤ t ≤ T`" becomes
  `1 ≤ g.val ≤ t.val < T`.
* Cohort `g` is the set of units first treated at period `g`; the never-
  treated cohort is `C`.
* The treatment-path regime `regOf g` sets `D s = 0` for `s.val < g.val`
  and `D s = 1` for `s.val ≥ g.val`.  `regNT` sets `D s = 0` for every `s`.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Staggered-Adoption Difference-in-Differences

This file develops the potential-outcome setup for Callaway-Sant'Anna group-time treatment
effects. It encodes treatment cohorts, never-treated comparisons, and the assumptions needed to
identify the average treatment effect for a cohort at a time period.

It extends two-period DID to a finite horizon with first-treated cohorts and a
never-treated comparison group. Periods are zero-indexed, so admissible
group-time effects use a cohort after the first period and an outcome period no
earlier than that cohort.

The central definitions are `regOf`, `regNT`, `cohortEvent`,
`neverTreatedEvent`, and the group-time estimand `ATT`; the main theorem
`att_csdid` proves the observable group-time DID contrast under the
Callaway-Sant'Anna assumptions. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- A staggered-adoption DID system has binary treatment and real outcome variables at each period.

The treatment and outcome node families are injective and disjoint. -/
structure POCSDIDSystem (P : POSystem) where
  T : ℕ
  hT : 2 ≤ T
  D : Fin T → P.V
  Y : Fin T → P.V
  hDbool : ∀ s : Fin T, P.X (D s) ≃ᵐ Bool
  hYreal : ∀ s : Fin T, P.X (Y s) ≃ᵐ ℝ
  hDinj : Function.Injective D
  hYinj : Function.Injective Y
  hDY : ∀ s t : Fin T, D s ≠ Y t

namespace POCSDIDSystem

variable {P : POSystem} (S : POCSDIDSystem P)

/-! ### `POVar` wrappers, factuals, and events -/

/-- The treatment at a period is packaged as a binary potential-outcome variable. -/
def dVar (s : Fin S.T) : POVar P Bool := ⟨S.D s, S.hDbool s⟩

/-- The outcome at a period is packaged as a real-valued potential-outcome variable. -/
def yVar (s : Fin S.T) : POVar P ℝ := ⟨S.Y s, S.hYreal s⟩

/-- The factual treatment at a period is the observed treatment value for that period. -/
noncomputable def factualD (s : Fin S.T) : P.Ω → Bool := (S.dVar s).factual

/-- The factual outcome at a period is the observed outcome value for that period. -/
noncomputable def factualY (s : Fin S.T) : P.Ω → ℝ := (S.yVar s).factual

/-- The period-specific treatment event contains units with the chosen observed treatment value. -/
def dEvent (s : Fin S.T) (b : Bool) : Set P.Ω := (S.dVar s).event b

/-- The observed treatment at each period is measurable. -/
lemma measurable_factualD (s : Fin S.T) : Measurable (S.factualD s) :=
  (S.dVar s).measurable_factual

/-- The observed outcome at each period is measurable. -/
lemma measurable_factualY (s : Fin S.T) : Measurable (S.factualY s) :=
  (S.yVar s).measurable_factual

/-- Each period-specific treatment event is measurable. -/
lemma measurableSet_dEvent (s : Fin S.T) (b : Bool) :
    MeasurableSet (S.dEvent s b) :=
  (S.dVar s).measurableSet_event _

/-! ### Treatment-path regimes `regOf g` and `regNT`

Built recursively over `k ≤ S.T`, mirroring the construction in
`PO/ID/Exact/DTR/Setup.lean`.  The standalone target function
`dTargetUpTo` lets us prove disjointness for the next `Regime.sqcup`.
-/

/-- The standalone target set contains the treatment nodes from periods before the cutoff. -/
def dTargetUpTo (S : POCSDIDSystem P) : ℕ → Finset P.V
  | 0     => ∅
  | k + 1 =>
      if h : k < S.T then insert (S.D ⟨k, h⟩) (S.dTargetUpTo k)
      else S.dTargetUpTo k

/-- Membership in the target set is exactly being a treatment node before the cutoff. -/
lemma dTargetUpTo_mem_iff (S : POCSDIDSystem P) :
    ∀ (k : ℕ) (_ : k ≤ S.T) (v : P.V),
      v ∈ S.dTargetUpTo k ↔ ∃ i : Fin S.T, i.val < k ∧ v = S.D i
  | 0, _, v => by simp [dTargetUpTo]
  | k + 1, h, v => by
      have hk : k < S.T := h
      simp only [dTargetUpTo, hk, ↓reduceDIte, Finset.mem_insert]
      constructor
      · rintro (rfl | hmem)
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self _, rfl⟩
        · rcases (S.dTargetUpTo_mem_iff k (Nat.le_of_lt hk) v).mp hmem with
            ⟨i, hi, rfl⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · exact Or.inr ((S.dTargetUpTo_mem_iff k (Nat.le_of_lt hk) _).mpr
            ⟨i, hi', rfl⟩)
        · left
          have : (⟨k, hk⟩ : Fin S.T) = i := by apply Fin.ext; simp [hi']
          rw [this]

/-- The recursive auxiliary builds a treatment-path regime over the first
periods and records its target set. -/
noncomputable def regUpToAux (S : POCSDIDSystem P) (b : Fin S.T → Bool) :
    (k : ℕ) → k ≤ S.T →
      { r : Regime P.V P.X // r.target = S.dTargetUpTo k }
  | 0, _ => ⟨Regime.empty, by simp [dTargetUpTo, Regime.empty]⟩
  | k + 1, h =>
      have hk : k < S.T := h
      let pair := S.regUpToAux b k (Nat.le_of_lt hk)
      let r_rec : Regime P.V P.X := pair.1
      have hrec : r_rec.target = S.dTargetUpTo k := pair.2
      let v := S.D ⟨k, hk⟩
      have hv_not : v ∉ r_rec.target := by
        rw [hrec]
        intro hmem
        rcases (S.dTargetUpTo_mem_iff k (Nat.le_of_lt hk) _).mp hmem with
          ⟨i, hi, heq⟩
        have hFin : (⟨k, hk⟩ : Fin S.T) = i := S.hDinj heq
        have hval : (k : ℕ) = i.val := by
          have := congrArg Fin.val hFin; simpa using this
        omega
      let r_new := Regime.sqcup
        (Regime.single v ((S.hDbool ⟨k, hk⟩).symm (b ⟨k, hk⟩))) r_rec
        (Regime.single_disjoint_of_not_mem _ _ hv_not)
      ⟨r_new, by
        show r_new.target = S.dTargetUpTo (k + 1)
        simp only [r_new, Regime.sqcup_target, Regime.single_target,
                   dTargetUpTo, hk, ↓reduceDIte]
        rw [hrec]
        ext w; simp [Finset.mem_insert, v]⟩

/-- A full-horizon regime fixes every period's treatment according to a chosen treatment path. -/
noncomputable def regimeBy (S : POCSDIDSystem P) (b : Fin S.T → Bool) :
    Regime P.V P.X :=
  (S.regUpToAux b S.T (le_refl _)).1

/-- The target of a full-horizon treatment-path regime is the full set of treatment nodes. -/
lemma regimeBy_target_eq (S : POCSDIDSystem P) (b : Fin S.T → Bool) :
    (S.regimeBy b).target = S.dTargetUpTo S.T :=
  (S.regUpToAux b S.T (le_refl _)).2

/-- The cohort regime leaves periods before the cohort untreated and treats all later periods. -/
noncomputable def regOf (g : Fin S.T) : Regime P.V P.X :=
  S.regimeBy (fun s => decide (g.val ≤ s.val))

/-- The never-treated regime fixes every period's treatment to untreated. -/
noncomputable def regNT : Regime P.V P.X :=
  S.regimeBy (fun _ => false)

/-! ### Y-target lemmas: `S.Y t` is never in a `regimeBy` target -/

/-- An outcome node is not among the treatment targets before any cutoff. -/
lemma Y_notin_dTargetUpTo (t : Fin S.T) :
    ∀ k, k ≤ S.T → S.Y t ∉ S.dTargetUpTo k := by
  intro k hk hmem
  rcases (S.dTargetUpTo_mem_iff k hk _).mp hmem with ⟨i, _, heq⟩
  exact (S.hDY i t) heq.symm

/-- An outcome node is not targeted by any full-horizon treatment-path regime. -/
lemma Y_notin_regimeBy (t : Fin S.T) (b : Fin S.T → Bool) :
    S.Y t ∉ (S.regimeBy b).target := by
  rw [S.regimeBy_target_eq]
  exact S.Y_notin_dTargetUpTo t S.T (le_refl _)

/-- The outcome variable at a period is not targeted by the cohort regime. -/
lemma yVar_v_notin_regOf_target (t g : Fin S.T) :
    (S.yVar t).v ∉ (S.regOf g).target :=
  S.Y_notin_regimeBy t _

/-- The outcome variable at a period is not targeted by the never-treated regime. -/
lemma yVar_v_notin_regNT_target (t : Fin S.T) :
    (S.yVar t).v ∉ S.regNT.target :=
  S.Y_notin_regimeBy t _

/-! ### Counterfactual outcomes and ATT -/

/-- The cohort potential outcome is the period outcome under the treatment path for that cohort. -/
noncomputable def YofCohort (t g : Fin S.T) : P.Ω → ℝ :=
  (S.yVar t).cf (S.regOf g)

/-- The never-treated potential outcome is the period outcome under the never-treated path. -/
noncomputable def YofNT (t : Fin S.T) : P.Ω → ℝ :=
  (S.yVar t).cf S.regNT

/-- Cohort potential outcomes are measurable. -/
lemma measurable_YofCohort (t g : Fin S.T) : Measurable (S.YofCohort t g) :=
  (S.yVar t).measurable_cf _

/-- Never-treated potential outcomes are measurable. -/
lemma measurable_YofNT (t : Fin S.T) : Measurable (S.YofNT t) :=
  (S.yVar t).measurable_cf _

/-- The predecessor of an admissible cohort is the immediately preceding period. -/
def predFin (g : Fin S.T) (_hg : 1 ≤ g.val) : Fin S.T :=
  ⟨g.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) g.isLt⟩

/-- The cohort event contains units untreated just before the cohort period and
treated at the cohort period. -/
def cohortEvent (g : Fin S.T) (hg : 1 ≤ g.val) : Set P.Ω :=
  S.dEvent (S.predFin g hg) false ∩ S.dEvent g true

/-- Each cohort event is measurable. -/
lemma measurableSet_cohortEvent (g : Fin S.T) (hg : 1 ≤ g.val) :
    MeasurableSet (S.cohortEvent g hg) :=
  (S.measurableSet_dEvent _ _).inter (S.measurableSet_dEvent _ _)

/-- The never-treated event contains units untreated in every period. -/
def neverTreatedEvent : Set P.Ω := ⋂ s : Fin S.T, S.dEvent s false

/-- The never-treated event is measurable. -/
lemma measurableSet_neverTreatedEvent : MeasurableSet S.neverTreatedEvent :=
  MeasurableSet.iInter (fun s => S.measurableSet_dEvent s _)

/-- The group-time ATT is the cohort mean contrast between cohort and
never-treated potential outcomes. -/
noncomputable def ATT (g t : Fin S.T) (hg : 1 ≤ g.val) : ℝ :=
  eventCondExp P.μ (S.cohortEvent g hg)
    (fun ω => S.YofCohort t g ω - S.YofNT t ω)

/-! ### Assumptions -- def:po-cs-did-assumptions -/

/-- The Callaway-Sant'Anna assumptions combine consistency, irreversible
adoption, no anticipation, never-treated parallel trends, positivity, and
integrability. -/
structure Assumptions (S : POCSDIDSystem P) : Prop where
  /-- Consistency of the underlying PO system. -/
  consistency : P.Consistency
  /-- Irreversibility, base case: `D_0 = 0` almost surely. -/
  irreversibilityBase :
    ∀ᵐ ω ∂P.μ, S.factualD ⟨0, lt_of_lt_of_le Nat.zero_lt_two S.hT⟩ ω = false
  /-- Irreversibility, absorbing: `D_s = 1 ⟹ D_{s+1} = 1` almost surely. -/
  irreversibilityStep :
    ∀ (s : Fin S.T) (h : s.val + 1 < S.T), ∀ᵐ ω ∂P.μ,
      S.factualD s ω = true → S.factualD ⟨s.val + 1, h⟩ ω = true
  /-- No anticipation: pre-treatment outcomes are unaffected by future treatment. -/
  noAnticipation :
    ∀ (g s : Fin S.T), s.val < g.val →
      ∀ᵐ ω ∂P.μ, S.YofCohort s g ω = S.YofNT s ω
  /-- Never-treated parallel trends (long-difference form). -/
  parallelTrends :
    ∀ (g t : Fin S.T) (hg : 1 ≤ g.val) (_hgt : g.val ≤ t.val),
      eventCondExp P.μ (S.cohortEvent g hg)
          (fun ω => S.YofNT t ω - S.YofNT (S.predFin g hg) ω)
        = eventCondExp P.μ S.neverTreatedEvent
            (fun ω => S.YofNT t ω - S.YofNT (S.predFin g hg) ω)
  /-- Positivity of cohorts. -/
  posCohort : ∀ (g : Fin S.T) (hg : 1 ≤ g.val),
      P.μ (S.cohortEvent g hg) ≠ 0 ∧ P.μ (S.cohortEvent g hg) ≠ ⊤
  /-- Positivity of the never-treated event. -/
  posNT : P.μ S.neverTreatedEvent ≠ 0 ∧ P.μ S.neverTreatedEvent ≠ ⊤
  /-- Integrability of `Y_t(g)` for every cohort-period pair. -/
  intYofCohort : ∀ g t : Fin S.T, Integrable (S.YofCohort t g) P.μ
  /-- Integrability of `Y_t(∞)`. -/
  intYofNT : ∀ t : Fin S.T, Integrable (S.YofNT t) P.μ

/-! ### Cohort and never-treated consistency bridge lemmas -/

/-- On `cohortEvent g`, irreversibility forces the factual D-path to agree with
`regOf g`, hence by consistency `Y_t(g) = factual Y_t` almost surely on `G_g`. -/
private lemma factualY_eq_YofCohort_on_cohortEvent
    (hA : S.Assumptions) (g t : Fin S.T) (hg : 1 ≤ g.val) :
    ∀ᵐ ω ∂P.μ, ω ∈ S.cohortEvent g hg →
      S.YofCohort t g ω = S.factualY t ω := by
  -- On the cohort event, the observed switch time determines the whole
  -- absorbing treatment path, so consistency links the cohort potential outcome
  -- to the factual outcome.
  have hStep_ae : ∀ᵐ ω ∂P.μ,
      ∀ (s : Fin S.T) (h : s.val + 1 < S.T),
        S.factualD s ω = true → S.factualD ⟨s.val + 1, h⟩ ω = true := by
    rw [MeasureTheory.ae_all_iff]
    intro s
    rw [MeasureTheory.ae_all_iff]
    intro h
    exact hA.irreversibilityStep s h
  refine hStep_ae.mono (fun ω hStep hω => ?_)
  rcases hω with ⟨hPredFalse, hGTrue⟩
  have hPredFalse' : S.factualD (S.predFin g hg) ω = false := by
    simpa [cohortEvent, dEvent, factualD] using hPredFalse
  have hGTrue' : S.factualD g ω = true := by
    simpa [cohortEvent, dEvent, factualD] using hGTrue
  have hForwardTrue :
      ∀ (a b : ℕ) (haT : a < S.T) (hbT : b < S.T), a ≤ b →
        S.factualD ⟨a, haT⟩ ω = true →
          S.factualD ⟨b, hbT⟩ ω = true := by
    intro a b haT hbT hab haTrue
    refine Nat.le_induction ?base ?step b hab hbT haTrue
    · intro haT' haTrue'
      have hfin : (⟨a, haT'⟩ : Fin S.T) = ⟨a, haT⟩ := by
        ext
        rfl
      simpa [hfin] using haTrue'
    · intro n _ ih hn1T hnTrue
      have hnT : n < S.T := Nat.lt_of_succ_lt hn1T
      have hprev : S.factualD ⟨n, hnT⟩ ω = true := ih hnT hnTrue
      exact hStep ⟨n, hnT⟩ hn1T hprev
  have hD_path : ∀ s : Fin S.T,
      S.factualD s ω = decide (g.val ≤ s.val) := by
    intro s
    by_cases hgs : g.val ≤ s.val
    · have htrue : S.factualD s ω = true := by
        have htrue' : S.factualD ⟨s.val, s.isLt⟩ ω = true :=
          hForwardTrue g.val s.val g.isLt s.isLt hgs (by simpa using hGTrue')
        simpa using htrue'
      simpa [hgs] using htrue
    · have hsg : s.val < g.val := Nat.lt_of_not_ge hgs
      have hfalse : S.factualD s ω = false := by
        by_contra hnot
        have htrue_s : S.factualD s ω = true := by
          cases hsD : S.factualD s ω <;> simp_all
        have hpred_le : s.val ≤ g.val - 1 := by omega
        have hpredT : g.val - 1 < S.T := (S.predFin g hg).isLt
        have hpredTrue' :
            S.factualD ⟨g.val - 1, hpredT⟩ ω = true :=
          hForwardTrue s.val (g.val - 1) s.isLt hpredT hpred_le (by simpa using htrue_s)
        have hpredFin : (⟨g.val - 1, hpredT⟩ : Fin S.T) = S.predFin g hg := by
          ext
          rfl
        have hpredTrue : S.factualD (S.predFin g hg) ω = true := by
          simpa [hpredFin] using hpredTrue'
        simp [hPredFalse'] at hpredTrue
      simpa [hgs] using hfalse
  have hAgrees : P.FactualAgrees (S.regOf g) ω := by
    let b : Fin S.T → Bool := fun s => decide (g.val ≤ s.val)
    have hprefix : ∀ (k : ℕ) (h : k ≤ S.T),
        P.FactualAgrees (S.regUpToAux b k h).1 ω := by
      intro k
      induction k with
      | zero =>
          intro h
          change P.FactualAgrees (S.regUpToAux b 0 (by exact Nat.zero_le S.T)).1 ω
          unfold regUpToAux
          exact POSystem.factualAgrees_empty ω
      | succ k ih =>
          intro h
          have hk : k < S.T := h
          have hf : S.factualD ⟨k, hk⟩ ω = b ⟨k, hk⟩ := hD_path ⟨k, hk⟩
          have hrec := ih (Nat.le_of_lt hk)
          change P.FactualAgrees (S.regUpToAux b (k + 1) h).1 ω
          unfold regUpToAux
          simp only
          apply POSystem.factualAgrees_sqcup
          · exact (S.dVar ⟨k, hk⟩).factualAgrees_single (b ⟨k, hk⟩) hf
          · exact hrec
    change P.FactualAgrees
      (S.regUpToAux (fun s : Fin S.T => decide (g.val ≤ s.val)) S.T (le_refl S.T)).1 ω
    exact hprefix S.T (le_refl S.T)
  have h := POVar.cf_eq_factual_of_factualAgrees hA.consistency
    (S.yVar t) (S.regOf g) (S.yVar_v_notin_regOf_target t g) ω hAgrees
  simpa [YofCohort, factualY] using h

/-- On `neverTreatedEvent`, the D-path matches `regNT` directly, hence by
consistency `Y_t(∞) = factual Y_t` pointwise on `C`. -/
private lemma factualY_eq_YofNT_on_NT
    (hA : S.Assumptions) (t : Fin S.T) :
    ∀ᵐ ω ∂P.μ, ω ∈ S.neverTreatedEvent →
      S.YofNT t ω = S.factualY t ω := by
  -- The never-treated event directly supplies agreement with the all-false
  -- treatment path; the almost-everywhere wrapper matches the cohort bridge.
  refine Filter.Eventually.of_forall (fun ω hω => ?_)
  have hAgrees : P.FactualAgrees S.regNT ω := by
    let b : Fin S.T → Bool := fun _ => false
    have hprefix : ∀ (k : ℕ) (h : k ≤ S.T),
        P.FactualAgrees (S.regUpToAux b k h).1 ω := by
      intro k
      induction k with
      | zero =>
          intro h
          change P.FactualAgrees (S.regUpToAux b 0 (by exact Nat.zero_le S.T)).1 ω
          unfold regUpToAux
          exact POSystem.factualAgrees_empty ω
      | succ k ih =>
          intro h
          have hk : k < S.T := h
          have hf : S.factualD ⟨k, hk⟩ ω = false := by
            have hmem : ω ∈ S.dEvent ⟨k, hk⟩ false :=
              Set.mem_iInter.mp hω ⟨k, hk⟩
            simpa [dEvent, factualD] using hmem
          have hrec := ih (Nat.le_of_lt hk)
          change P.FactualAgrees (S.regUpToAux b (k + 1) h).1 ω
          unfold regUpToAux
          simp only
          apply POSystem.factualAgrees_sqcup
          · exact (S.dVar ⟨k, hk⟩).factualAgrees_single false hf
          · exact hrec
    change P.FactualAgrees (S.regUpToAux (fun _ : Fin S.T => false) S.T (le_refl S.T)).1 ω
    exact hprefix S.T (le_refl S.T)
  have h := POVar.cf_eq_factual_of_factualAgrees hA.consistency
    (S.yVar t) S.regNT (S.yVar_v_notin_regNT_target t) ω hAgrees
  simpa [YofNT, factualY] using h

/-! ### Main identification theorem -- prop:po-cs-did-att -/

/-- Callaway--Sant'Anna group-time DID identification of `ATT(g, t)`.

    ATT(g, t) = E[Y_t − Y_{g−1} | G_g] − E[Y_t − Y_{g−1} | C].

Mirrors `PODIDSystem.att_did` line by line. -/
theorem att_csdid (hA : S.Assumptions) (g t : Fin S.T)
    (hg : 1 ≤ g.val) (hgt : g.val ≤ t.val) :
    S.ATT g t hg
      = eventCondExp P.μ (S.cohortEvent g hg)
            (fun ω => S.factualY t ω - S.factualY (S.predFin g hg) ω)
        - eventCondExp P.μ S.neverTreatedEvent
            (fun ω => S.factualY t ω - S.factualY (S.predFin g hg) ω) := by
  have hPredLtG : (S.predFin g hg).val < g.val := by
    have : g.val - 1 < g.val :=
      Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hg) Nat.zero_lt_one
    simpa [predFin] using this
  have hAE : (fun ω => S.YofCohort t g ω - S.YofNT t ω)
      =ᵐ[P.μ] fun ω =>
        (S.YofCohort t g ω - S.YofCohort (S.predFin g hg) g ω) -
          (S.YofNT t ω - S.YofNT (S.predFin g hg) ω) := by
    refine (hA.noAnticipation g (S.predFin g hg) hPredLtG).mono (fun ω hω => ?_)
    change S.YofCohort t g ω - S.YofNT t ω
      = (S.YofCohort t g ω - S.YofCohort (S.predFin g hg) g ω) -
          (S.YofNT t ω - S.YofNT (S.predFin g hg) ω)
    rw [hω]
    ring
  have hATT_split :
      S.ATT g t hg
        = eventCondExp P.μ (S.cohortEvent g hg)
            (fun ω => S.YofCohort t g ω - S.YofCohort (S.predFin g hg) g ω)
          - eventCondExp P.μ (S.cohortEvent g hg)
              (fun ω => S.YofNT t ω - S.YofNT (S.predFin g hg) ω) := by
    unfold ATT
    rw [eventCondExp_congr_ae P.μ (S.cohortEvent g hg) hAE]
    exact eventCondExp_sub P.μ (S.cohortEvent g hg)
      ((hA.intYofCohort g t).sub (hA.intYofCohort g (S.predFin g hg))).integrableOn
      ((hA.intYofNT t).sub (hA.intYofNT (S.predFin g hg))).integrableOn
  have h_first :
      eventCondExp P.μ (S.cohortEvent g hg)
          (fun ω => S.YofCohort t g ω - S.YofCohort (S.predFin g hg) g ω)
        = eventCondExp P.μ (S.cohortEvent g hg)
            (fun ω => S.factualY t ω - S.factualY (S.predFin g hg) ω) := by
    unfold eventCondExp
    rw [MeasureTheory.integral_congr_ae]
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (S.measurableSet_cohortEvent g hg)]
    filter_upwards [S.factualY_eq_YofCohort_on_cohortEvent hA g t hg,
      S.factualY_eq_YofCohort_on_cohortEvent hA g (S.predFin g hg) hg] with ω ht hpred hω
    rw [ht hω, hpred hω]
  have h_pt : eventCondExp P.μ (S.cohortEvent g hg)
        (fun ω => S.YofNT t ω - S.YofNT (S.predFin g hg) ω)
      = eventCondExp P.μ S.neverTreatedEvent
          (fun ω => S.YofNT t ω - S.YofNT (S.predFin g hg) ω) :=
    hA.parallelTrends g t hg hgt
  have h_second :
      eventCondExp P.μ S.neverTreatedEvent
          (fun ω => S.YofNT t ω - S.YofNT (S.predFin g hg) ω)
        = eventCondExp P.μ S.neverTreatedEvent
            (fun ω => S.factualY t ω - S.factualY (S.predFin g hg) ω) := by
    unfold eventCondExp
    rw [MeasureTheory.integral_congr_ae]
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' S.measurableSet_neverTreatedEvent]
    filter_upwards [S.factualY_eq_YofNT_on_NT hA t,
      S.factualY_eq_YofNT_on_NT hA (S.predFin g hg)] with ω ht hpred hω
    rw [ht hω, hpred hω]
  rw [hATT_split, h_first, h_pt, h_second]

end POCSDIDSystem

end PO
end Causalean
