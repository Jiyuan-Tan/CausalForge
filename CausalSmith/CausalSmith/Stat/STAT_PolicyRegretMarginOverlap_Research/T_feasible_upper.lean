/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy-regret rate: conditional feasible achievability

Stage-2 scaffold. The CONDITIONAL achievability theorem `oeq:feasible-upper`,
stated over `def:upper-risk` with the estimator/fold/process side-conditions
bound as explicit `Prop` hypotheses. The theorem body assembles the master
bound and deterministic exponent balance.
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: oeq:feasible-upper
/-- `oeq:feasible-upper` (CONDITIONAL achievability). The regime-indexed conditional
upper risk `U_n = upperRisk …` — whose estimator IS the cross-fit clipped-AIPW
`1/n`-ERM `feasibleERM` run with the SELECTED schedule clip `q_n = qSched α γ a c
q0 n`, supremized over the bundled `def:law-class`/optimal/finite-VC/foldwise
nuisance-rate side-condition domain at the fixed regime `(a,c,C_μ,C_prod)` —
achieves the UNIFORM EVENTUAL rate bound `U_n ≤ C n^{-r_feas}(log n)^p`
(`r_feas = (feasibleRate …).r`, the solved exponent of the certified
`def:feasible-rate` object built from `hinputs`), using only the crude `q^{-2}`
score envelope, the uniform class-level localized finite-VC envelopes, and the
deterministic clip-bias controls. CRUCIALLY the constants
`C, p` are chosen BEFORE `n` (quantified outside the `∀ᶠ n in atTop`), so this
encodes the paper's uniform eventual conditional rate bound over `n` — a single
pair `(C,p)` controlling `U_n` for ALL large `n` — not a per-`n` bound with
constants chosen after `n` (which would be vacuous). The `def:feasible-rate`
INPUT-domain restrictions — `ū ∈ (0,u₀]`, `q₀ ∈ (0, min{1/2, c_o ū^γ}]` for `γ>0`
and the strict-overlap endpoint clip `q₀ ∈ (0, underline_p/2]` for `γ=0` — are carried
as `hinputs` (`FeasibleRateInputs`); the schedule admissibility `q_n ≤ c_o u_n^γ`
is now BUNDLED INTO the certified `feasibleRate … hinputs` object (its `admissible`
field, derived from `hinputs`) rather than carried as a separate hypothesis.

SCOPE (Lean encoding fidelity): the enumeration `enum : ℕ → Policy 𝒳` carries the
note's dense-`Π₀` enumeration condition as `hskel : DenseSkeleton enum policySet`
(every `enum j ∈ Π`, and every `π ∈ Π` is a pointwise limit of an `enum`-indexed
subsequence). So this conditional achievability bound is stated specifically for
the pointwise-dense-skeleton `1/n`-ERM `feasibleERM … enum …` of
`def:feasible-erm`, not an ARBITRARY enumeration-based ERM.

Not an unconditional minimax upper claim. -/
theorem feasible_upper {K : ℕ}
    (α γ Cm u0 Co co underlineP a c CMu CProd q0 uBar : ℝ) (dPi : ℕ)
    (assign : (m : ℕ) → Fin m → Fin K) (policySet : Set (Policy 𝒳))
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ)
    (rMu rE : ℕ → ℝ)
    (hγ : 0 ≤ γ)
    (hpoly : PolynomialNuisanceExponents rMu rE a c CMu CProd)
    (hCMu : 0 ≤ CMu) (hCProd : 0 ≤ CProd)
    (hrMu_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ rMu n)
    (hrE_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ rE n)
    (hμ0meas : ∀ n k, Measurable (muHat0 n k))
    (hμ1meas : ∀ n k, Measurable (muHat1 n k))
    (hemeas : ∀ n k, Measurable (eHat n k))
    (hμ0L2 : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P →
          ∀ k : Fin K, MemLp (fun x => muHat0 n k x - P.mu0 x) 2 P.PX)
    (hμ1L2 : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P →
          ∀ k : Fin K, MemLp (fun x => muHat1 n k x - P.mu1 x) 2 P.PX)
    (heL2 : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P →
          ∀ k : Fin K, MemLp (fun x => eHat n k x - P.propensity x) 2 P.PX)
    (hvc : PolicyClassVC policySet dPi)
    (henvU : VCLocalizedEnvelopeUnif policySet α)
    (hoffU : VCLocalizedOffsetEnvelopeUnif policySet α)
    (hK : FixedFoldCount K assign)
    (hbn : ∀ k : Fin K,
      BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k))
    (hskel : DenseSkeleton enum policySet)
    (hinputs : FeasibleRateInputs γ co underlineP u0 q0 uBar) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        upperRisk (n := n) α γ Cm u0 Co co underlineP a c CMu CProd q0 dPi
            policySet enum muHat0 muHat1 eHat assign rMu rE
          ≤ C * (n : ℝ)
              ^ (-(feasibleRate α γ a c co underlineP u0 q0 uBar hinputs).r)
              * (Real.log n) ^ p
    := by
  classical
  have hq0 : 0 < q0 := by
    by_cases hγ0 : γ = 0
    · exact (hinputs.2 hγ0).1
    · have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
      exact (hinputs.1 hγpos).2.2.1
  have huBar : 0 < γ → 0 < uBar := fun hγpos => (hinputs.1 hγpos).1
  have hadm : 0 < γ → feasibleAdmissible α γ a c co q0 uBar :=
    fun hγpos => (feasibleRate α γ a c co underlineP u0 q0 uBar hinputs).admissible hγpos
  have hq_sched_pos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < qSched α γ a c q0 n := by
    by_cases hγ0 : γ = 0
    · rw [Filter.eventually_atTop]
      exact ⟨0, fun _n _hn => by simpa [qSched, hγ0] using hq0⟩
    · filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
      simp [qSched, hγ0, hq0, Real.rpow_pos_of_pos hnpos]
  by_cases hempty_zero :
      γ = 0 ∧
        ¬ ∃ P : ObservedLaw 𝒳,
          LawClass α γ Cm u0 Co co underlineP policySet P
  · refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    filter_upwards [Filter.eventually_atTop.mpr ⟨2, fun n hn => hn⟩] with n hn2
    have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn2
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    have hbound_nonneg :
        0 ≤ (1 : ℝ) * (n : ℝ)
            ^ (-(feasibleRate α γ a c co underlineP u0 q0 uBar hinputs).r)
            * (Real.log n) ^ (0 : ℝ) := by
      positivity
    apply Real.sSup_le ?_ hbound_nonneg
    rintro y ⟨P, hP, rfl⟩
    exact False.elim (hempty_zero.2 ⟨P, hP.1⟩)
  have hq_half :
      ∀ᶠ n : ℕ in Filter.atTop, qSched α γ a c q0 n ≤ 1 / 2 := by
    by_cases hγ0 : γ = 0
    · have hnonempty :
          ∃ P : ObservedLaw 𝒳,
            LawClass α γ Cm u0 Co co underlineP policySet P := by
        by_contra hnone
        exact hempty_zero ⟨hγ0, hnone⟩
      rcases hnonempty with ⟨P0, hLaw0⟩
      have hunder_half : underlineP ≤ 1 / 2 := (hLaw0.strict hγ0).2.1
      have hq0_le_under : q0 ≤ underlineP / 2 := (hinputs.2 hγ0).2
      have hq0_le_half : q0 ≤ 1 / 2 := by nlinarith
      rw [Filter.eventually_atTop]
      exact ⟨0, fun _n _hn => by simpa [qSched, hγ0] using hq0_le_half⟩
    · have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
      rcases feasibleMaximizer_mem α γ a c hγpos with ⟨hs0, _hs1, _ht0, _ht1⟩
      have hq0_le_half : q0 ≤ 1 / 2 :=
        le_trans (hinputs.1 hγpos).2.2.2 (min_le_left _ _)
      filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hp_le_one :
          (n : ℝ) ^ (-(sFeas α γ a c)) ≤ 1 := by
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
      calc
        qSched α γ a c q0 n
            = q0 * (n : ℝ) ^ (-(sFeas α γ a c)) := by
              simp [qSched, hγ0]
        _ ≤ q0 * 1 := by
              exact mul_le_mul_of_nonneg_left hp_le_one hq0.le
        _ = q0 := by ring
        _ ≤ 1 / 2 := hq0_le_half
  have hq_zero_fixed :
      γ = 0 →
        ∃ q0fix : ℝ, 0 < q0fix ∧
          ∀ᶠ n : ℕ in Filter.atTop, qSched α γ a c q0 n = q0fix := by
    intro hγ0
    exact ⟨q0, hq0, Filter.Eventually.of_forall (fun n => by simp [qSched, hγ0])⟩
  rcases crude_localized_master_bound (𝒳 := 𝒳) policySet
      α γ Cm u0 Co co underlineP a c CMu CProd dPi assign
      (qSched α γ a c q0) (uSched α γ a c uBar) rMu rE
      enum muHat0 muHat1 eHat hvc henvU hoffU hskel hK hpoly hq_sched_pos
      hq_half hq_zero_fixed hrMu_nonneg hrE_nonneg hμ0meas hμ1meas hemeas
      hμ0L2 hμ1L2 heL2 hbn with
    ⟨Cmaster, pmaster, hCmaster, hpmaster, hmaster_event⟩
  rcases clip_balance_exponent α γ a c CMu CProd q0 uBar co rMu rE
      hpoly hCMu hCProd hrMu_nonneg hq0 huBar hadm with
    ⟨Cbal, pbal, hCbal, hpbal, hbal_pos, hbal_zero⟩
  refine ⟨Cmaster * Cbal, pmaster + pbal, mul_pos hCmaster hCbal,
    add_nonneg hpmaster hpbal, ?_⟩
  by_cases hγ0 : γ = 0
  · have hbal_event := hbal_zero hγ0
    filter_upwards
      [hmaster_event, hbal_event, Filter.eventually_atTop.mpr ⟨2, fun n hn => hn⟩]
      with n hmaster_n hbal_n hn2
    have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn2
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ)) hn2)
    have hbound_nonneg :
        0 ≤ Cmaster * Cbal * (n : ℝ) ^ (-(rFeas α γ a c))
            * (Real.log n) ^ (pmaster + pbal) := by positivity
    apply Real.sSup_le ?_ hbound_nonneg
    rintro y ⟨P, hP, rfl⟩
    rcases hP with
      ⟨hlaw, hopt, hiid, hnr, hbn, _hpoly_dom, _hvc_dom,
        _henv_dom, _hoff_dom, _hK_dom, _hskel_dom⟩
    have hq_le : qSched α γ a c q0 n ≤ underlineP / 2 := by
      simpa [qSched, hγ0] using (hinputs.2 hγ0).2
    have hmasterP := (hmaster_n P hlaw hopt hiid hnr hbn).2 hγ0 hq_le
    calc
      ∫ sample,
          lawRegret P
            (feasibleERM (qSched α γ a c q0 n) enum (muHat0 n) (muHat1 n)
              (eHat n) (assign n) sample)
          ∂Measure.pi (fun _ : Fin n => P.dataMeasure)
          ≤ Cmaster * ((n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n)
              * (Real.log n) ^ pmaster := hmasterP
      _ ≤ Cmaster * (Cbal * (n : ℝ) ^ (-(rFeas α γ a c))
              * (Real.log n) ^ pbal) * (Real.log n) ^ pmaster := by
            nlinarith [mul_le_mul_of_nonneg_left hbal_n hCmaster.le,
              Real.rpow_nonneg hlog_pos.le pmaster]
      _ = Cmaster * Cbal * (n : ℝ) ^ (-(rFeas α γ a c))
              * (Real.log n) ^ (pmaster + pbal) := by
            rw [Real.rpow_add hlog_pos]
            ring
      _ = Cmaster * Cbal * (n : ℝ)
              ^ (-(feasibleRate α γ a c co underlineP u0 q0 uBar hinputs).r)
              * (Real.log n) ^ (pmaster + pbal) := by
            simp [feasibleRate, rFeas]
  · have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
    have hbal_event := hbal_pos hγpos
    have hadm_event := hadm hγpos
    filter_upwards
      [hmaster_event, hbal_event, hadm_event,
        Filter.eventually_atTop.mpr ⟨2, fun n hn => hn⟩]
      with n hmaster_n hbal_n hadm_n hn2
    have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn2
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ (2 : ℕ)) hn2)
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ)) hn2)
    have hu_pos : 0 < uSched α γ a c uBar n := by
      simp [uSched, huBar hγpos, Real.rpow_pos_of_pos hnpos]
    have hu_le : uSched α γ a c uBar n ≤ u0 := by
      rcases feasibleMaximizer_mem α γ a c hγpos with ⟨_hs0, _hs1, ht0, _ht1⟩
      have hp_le_one :
          (n : ℝ) ^ (-(tFeas α γ a c)) ≤ 1 := by
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
      have huBar_le : uBar ≤ u0 := (hinputs.1 hγpos).2.1
      calc
        uSched α γ a c uBar n = uBar * (n : ℝ) ^ (-(tFeas α γ a c)) := rfl
        _ ≤ uBar * 1 := by
              exact mul_le_mul_of_nonneg_left hp_le_one (le_of_lt (huBar hγpos))
        _ = uBar := by ring
        _ ≤ u0 := huBar_le
    have hbound_nonneg :
        0 ≤ Cmaster * Cbal * (n : ℝ) ^ (-(rFeas α γ a c))
            * (Real.log n) ^ (pmaster + pbal) := by positivity
    apply Real.sSup_le ?_ hbound_nonneg
    rintro y ⟨P, hP, rfl⟩
    rcases hP with
      ⟨hlaw, hopt, hiid, hnr, hbn, _hpoly_dom, _hvc_dom,
        _henv_dom, _hoff_dom, _hK_dom, _hskel_dom⟩
    have hmasterP :=
      (hmaster_n P hlaw hopt hiid hnr hbn).1 hγpos hu_pos hu_le hadm_n
    calc
      ∫ sample,
          lawRegret P
            (feasibleERM (qSched α γ a c q0 n) enum (muHat0 n) (muHat1 n)
              (eHat n) (assign n) sample)
          ∂Measure.pi (fun _ : Fin n => P.dataMeasure)
          ≤ Cmaster *
              ((n : ℝ) ^ (-(rStar α γ))
                + ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α))
                + rMu n * rE n / qSched α γ a c q0 n
                + rMu n * (uSched α γ a c uBar n) ^ (α / 2)
                    * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
                + (rMu n) ^ 2 / uSched α γ a c uBar n)
              * (Real.log n) ^ pmaster := hmasterP
      _ ≤ Cmaster * (Cbal * (n : ℝ) ^ (-(rFeas α γ a c))
              * (Real.log n) ^ pbal) * (Real.log n) ^ pmaster := by
            nlinarith [mul_le_mul_of_nonneg_left hbal_n hCmaster.le,
              Real.rpow_nonneg hlog_pos.le pmaster]
      _ = Cmaster * Cbal * (n : ℝ) ^ (-(rFeas α γ a c))
              * (Real.log n) ^ (pmaster + pbal) := by
            rw [Real.rpow_add hlog_pos]
            ring
      _ = Cmaster * Cbal * (n : ℝ)
              ^ (-(feasibleRate α γ a c co underlineP u0 q0 uBar hinputs).r)
              * (Real.log n) ^ (pmaster + pbal) := by
            simp [feasibleRate]

end CausalSmith.Stat.PolicyRegretMarginOverlap
