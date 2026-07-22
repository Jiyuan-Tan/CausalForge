/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy-regret rate: achievability helper lemmas

Stage-2 scaffold. The build-inline helper lemmas behind the conditional
achievability theorem `oeq:feasible-upper`. Every proof body is `sorry`.
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
import Causalean.Stat.Concentration.LocalizedEnvelopeExpectation
import Causalean.Stat.Concentration.VCLocalizedRegime

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ## Discharged localized finite-VC empirical-process envelopes

The two localized finite-VC envelopes are SUBSTRATE FACTS (general
empirical-process theorems), not modeling assumptions, so they are not assumed
hypotheses anywhere: they are DERIVED here by reusing the axiom-clean Causalean
substrate
`Causalean.Stat.Concentration.localized_uniform_deviation_expectation`
(fixed-radius in-expectation envelope) and
`Causalean.Stat.Concentration.localized_offset_expectation`
(self-localizing offset positive-part envelope), bridged by the in-scope
`margin_localization` (regret radius → `L²(P)` norm radius) and the finite-VC
critical-radius rate `Causalean.Stat.Concentration.vcLocalizedEnvelope`. -/

-- @node: ass:vc-localized-envelope
/-- `ass:vc-localized-envelope` (DISCHARGED, reuse). The localized finite-VC
fixed-radius empirical-process envelope holds for the pointwise measurable
finite-VC policy class, derived from
`Causalean.Stat.Concentration.localized_uniform_deviation_expectation` with
`norm := L²(P)` fluctuation, the regret radius bridged via `margin_localization`
and `criticalRadius` bounded by the finite-VC rate. -/
lemma vc_localized_envelope (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi : ℕ)
    (hpc : PolicyClassVC policySet dPi)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P) :
    VCLocalizedEnvelope P.PX P.contrast policySet α := by
  sorry

-- @node: ass:vc-localized-offset-envelope
/-- `ass:vc-localized-offset-envelope` (DISCHARGED, reuse). The localized
finite-VC offset/Rademacher positive-part envelope holds for the same class,
derived from `Causalean.Stat.Concentration.localized_offset_expectation` with
`Δ := R_P` (regret), `κ = α/(2+2α)`, and `A, ρ` supplied by `margin_localization`
together with the finite-VC critical-radius rate. -/
lemma vc_localized_offset_envelope (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi : ℕ)
    (hpc : PolicyClassVC policySet dPi)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P) :
    VCLocalizedOffsetEnvelope P.PX P.contrast policySet α := by
  sorry

/-! ## Centered empirical-process objects

The localized empirical-process lemmas below quantify over genuine centered
policy-indexed processes `(P_m - P) g_π` built from an i.i.d. sample and bound
their EXPECTED localized suprema, not abstract scalar placeholders. -/

/-- Centered policy-indexed empirical process `(P_m - P) g_π = m⁻¹ ∑_i g_π(O_i)
- E_P g_π` for an increment function `g` on a size-`m` sample. -/
noncomputable def centeredEmpProcess {m : ℕ} (P : ObservedLaw 𝒳)
    (g : Policy 𝒳 → Observation 𝒳 → ℝ) (sample : Fin m → Observation 𝒳)
    (π : Policy 𝒳) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, g π (sample i) - ∫ O, g π O ∂P.dataMeasure

/-- Expected localized supremum `E_P sup_{π ∈ Π : R_P(π) ≤ r} |(P_m - P) g_π|`,
the i.i.d. sample of size `m` drawn from `P`. -/
noncomputable def expectedLocalizedSup {m : ℕ} (P : ObservedLaw 𝒳)
    (g : Policy 𝒳 → Observation 𝒳 → ℝ) (policySet : Set (Policy 𝒳)) (r : ℝ) : ℝ :=
  ∫ sample, sSup ((fun π => |centeredEmpProcess P g sample π|) ''
      {π | π ∈ policySet ∧ lawRegret P π ≤ r})
    ∂(Measure.pi (fun _ : Fin m => P.dataMeasure))

/-- Pooled cross-fit centered process: average of the foldwise centered
increments `g (assign i)`, with each evaluation fold i.i.d. conditional on its
training fold. -/
noncomputable def pooledCrossfitProcess {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (sample : Fin n → Observation 𝒳) (π : Policy 𝒳) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i,
    (g (assign i) π (sample i) - ∫ O, g (assign i) π O ∂P.dataMeasure)

/-- Expected pooled cross-fit localized supremum. -/
noncomputable def expectedPooledLocalizedSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (r : ℝ) : ℝ :=
  ∫ sample, sSup ((fun π => |pooledCrossfitProcess P g assign sample π|) ''
      {π | π ∈ policySet ∧ lawRegret P π ≤ r})
    ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))

/-- Expected pooled cross-fit offset positive-part supremum
`E_P sup_π {2|G_cf(π)| - R_P(π)/4}_+`. -/
noncomputable def expectedPooledOffsetSup {n K : ℕ} (P : ObservedLaw 𝒳)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) : ℝ :=
  ∫ sample, sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P g assign sample π| - lawRegret P π / 4))
      '' policySet)
    ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))

/-- Pointwise clip-bias drift `b_q(x)` of the clipped-AIPW conditional mean. -/
noncomputable def clipBias (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (x : 𝒳) : ℝ :=
  (clippedPropensity q eHat x - P.propensity x) *
    ((muHat1 x - P.mu1 x) / clippedPropensity q eHat x
      + (muHat0 x - P.mu0 x) / (1 - clippedPropensity q eHat x))

/-- Policy-weighted population drift `P[(π-π_⋆) b_q]`. -/
noncomputable def driftIntegral (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (π : Policy 𝒳) : ℝ :=
  ∫ x, (boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x))
        * clipBias P q muHat0 muHat1 eHat x ∂P.PX

-- @node: lem:clip-bias
/-- `lem:clip-bias`. Exact clipped-score conditional-mean drift identity:
`E[Γ_q|X=x]-τ(x)=(ē_q-e_P)(Δ₁/ē_q+Δ₀/(1-ē_q))`. -/
lemma clip_bias (P : ObservedLaw 𝒳) (q : ℝ) (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hpos : Positivity P) (hq : 0 < q) (hq1 : q < 1) (x : 𝒳) :
    (muHat1 x - muHat0 x
        + (P.propensity x / clippedPropensity q eHat x) * (P.mu1 x - muHat1 x)
        - ((1 - P.propensity x) / (1 - clippedPropensity q eHat x))
            * (P.mu0 x - muHat0 x))
      - (P.mu1 x - P.mu0 x)
      = clipBias P q muHat0 muHat1 eHat x := by
  sorry

-- @node: lem:feasible-erm-basic-inequality
/-- `lem:feasible-erm-basic-inequality`. The feasible ERM (`enum`-skeleton,
foldwise cross-fit) is a MEASURABLE `Π`-valued estimator: it is `Π`-valued for
every realized sample, the induced regret map `sample ↦ R_P(π̂_n(sample))` is
measurable (so the `U_n`/`M_n` integrals are well-defined), and against EVERY
comparator `π^b ∈ Π` the `1/n` basic inequality holds; under `OptimalInClass`
it applies in particular to `π^b = π_⋆`. -/
lemma feasible_erm_basic_inequality {n K : ℕ} (P : ObservedLaw 𝒳) (q : ℝ)
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (assign : Fin n → Fin K) (policySet : Set (Policy 𝒳)) (dPi : ℕ)
    (hvc : PolicyClassVC policySet dPi) (hopt : OptimalInClass P policySet)
    (henum : ∀ j, enum j ∈ policySet) (hn : 0 < n) :
    Measurable (fun s : Fin n → Observation 𝒳 =>
        lawRegret P (feasibleERM q enum muHat0 muHat1 eHat assign s)) ∧
      ∀ sample : Fin n → Observation 𝒳,
        feasibleERM q enum muHat0 muHat1 eHat assign sample ∈ policySet ∧
          ∀ πb ∈ policySet,
            empiricalWelfareScore q muHat0 muHat1 eHat assign sample πb
              ≤ empiricalWelfareScore q muHat0 muHat1 eHat assign sample
                  (feasibleERM q enum muHat0 muHat1 eHat assign sample) + (n : ℝ)⁻¹ := by
  sorry

-- @node: lem:crude-clipped-score-envelope
/-- `lem:crude-clipped-score-envelope`. Crude `q^{-1}` envelope of the clipped
AIPW score from clipped denominators and bounded outcomes/nuisances. -/
lemma crude_clipped_score_envelope (P : ObservedLaw 𝒳)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (q : ℝ)
    (hbdd : BoundedOutcome P)
    (hbn : ∀ x, muHat0 x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᵐ O ∂P.dataMeasure,
        |clippedAIPWScore q muHat0 muHat1 eHat O| ≤ C / q) ∧
      (∀ᵐ O ∂P.dataMeasure,
        (clippedAIPWScore q muHat0 muHat1 eHat O) ^ 2 ≤ C / q ^ 2) := by
  sorry

-- @node: lem:clipped-region-localization
/-- `lem:clipped-region-localization`. For `γ>0`, the disagreement mass inside
the clipped region is controlled: `P_X(D_π ∩ {p_P≤q}) ≤ C u^α q^{1/γ}+r/u`. -/
lemma clipped_region_localization (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Co co α γ u0 : ℝ)
    (hod : OverlapDecay P Co co α γ) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ π ∈ policySet, ∀ u q : ℝ,
      0 < u → u ≤ u0 → 0 < q → q ≤ co * u ^ γ →
        P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})
          ≤ C * u ^ α * q ^ (1 / γ) + lawRegret P π / u := by
  sorry

-- @node: lem:localized-clipped-drift-bound
/-- `lem:localized-clipped-drift-bound`. Deterministic drift bound for the actual
policy-weighted drift `|P[(π-π_⋆) b_q]| = |driftIntegral …|`, in BOTH overlap
regimes, from `clip_bias`, clipping, and clipped-region localization (which needs
overlap-decay and zero-effect). For `γ>0` and `q ≤ c_o u^γ` it is the three-term
bound; for `γ=0` with fixed `q ≤ underline_p/2` (the strict-overlap endpoint
`underline_p`, NOT hard-coded), strict overlap collapses it to `C r_μ r_e`. -/
lemma localized_clipped_drift_bound (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (q rMu rE α γ Co co u0 underlineP : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hsq0 : ∫ x, (muHat0 x - P.mu0 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hsq1 : ∫ x, (muHat1 x - P.mu1 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hse : ∫ x, (eHat x - P.propensity x) ^ 2 ∂P.PX ≤ rE ^ 2)
    (hod : OverlapDecay P Co co α γ) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P)
    (hstrict : StrictOverlapEndpoint P γ underlineP) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧
      (0 < γ → ∀ π ∈ policySet, ∀ u : ℝ,
        0 < u → u ≤ u0 → q ≤ co * u ^ γ →
          |driftIntegral P q muHat0 muHat1 eHat π|
            ≤ C * (rMu * rE / q + rMu * u ^ (α / 2) * q ^ (1 / (2 * γ))
                + rMu * (lawRegret P π / u) ^ (1 / 2 : ℝ))) ∧
      (γ = 0 → q ≤ underlineP / 2 → ∀ π ∈ policySet,
        |driftIntegral P q muHat0 muHat1 eHat π| ≤ C * (rMu * rE)) := by
  sorry

-- @node: lem:localized-vc-process-bound
/-- `lem:localized-vc-process-bound`. Fixed-radius localized process bound: for an
i.i.d. sample of size `m`, the EXPECTED localized supremum `E_P Z_m(r)` of the
centered policy-indexed empirical process `(P_m - P) g_π` — with increment envelope
`B` and conditional second moment `≤ C B² P_X(D_π)` — is bounded by
`C B m^{-1/2} r^{α/(2+2α)}(log m)^p`, combining `margin_localization` with the
discharged finite-VC envelope. -/
lemma localized_vc_process_bound (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi : ℕ)
    (hpc : PolicyClassVC policySet dPi)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ (m : ℕ) (B r : ℝ) (g : Policy 𝒳 → Observation 𝒳 → ℝ),
        0 < m → 0 ≤ B → 0 ≤ r →
        (∀ π ∈ policySet, ∀ O, |g π O| ≤ B) →
        (∀ π ∈ policySet,
          ∫ O, (g π O) ^ 2 ∂P.dataMeasure
            ≤ C * B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
        expectedLocalizedSup (m := m) P g policySet r
          ≤ C * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
              * (Real.log m) ^ p := by
  sorry

-- @node: lem:crossfit-localized-process-reduction
/-- `lem:crossfit-localized-process-reduction`. Foldwise application plus balanced
fixed-`K` collapse: conditioning on the training folds, each balanced evaluation
fold is i.i.d., so `localized_vc_process_bound` applies foldwise, and the pooled
cross-fit centered process `pooledCrossfitProcess` (built from the foldwise
increments `g k` via `assign n`) has expected localized supremum bounded by
`C B n^{-1/2} r^{α/(2+2α)}(log n)^p`. -/
lemma crossfit_localized_process_reduction (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi K : ℕ)
    (assign : (n : ℕ) → Fin n → Fin K)
    (hpc : PolicyClassVC policySet dPi)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P)
    (hK : FixedFoldCount K assign) (hiid : IsIIDSample P) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ (n : ℕ) (B r : ℝ) (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ),
        0 < n → 0 ≤ B → 0 ≤ r →
        (∀ (k : Fin K), ∀ π ∈ policySet, ∀ O, |g k π O| ≤ B) →
        (∀ (k : Fin K), ∀ π ∈ policySet,
          ∫ O, (g k π O) ^ 2 ∂P.dataMeasure
            ≤ C * B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
        expectedPooledLocalizedSup P g (assign n) policySet r
          ≤ C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
              * (Real.log n) ^ p := by
  sorry

-- @node: lem:crossfit-localized-offset-control
/-- `lem:crossfit-localized-offset-control`. Pooled offset positive-part control:
conditioning on training folds and applying the discharged offset envelope
foldwise, the EXPECTED pooled cross-fit offset supremum
`E_P sup_π {2|G_cf(π)| - R_P(π)/4}_+` is bounded by `C (B²/n)^{A_α}(log n)^p`,
`A_α=(1+α)/(2+α)`. Stochastic input to `localized_vc_self_bound`; must not depend
on it. -/
lemma crossfit_localized_offset_control (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ) (dPi K : ℕ)
    (assign : (n : ℕ) → Fin n → Fin K)
    (hpc : PolicyClassVC policySet dPi)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hiid : IsIIDSample P) (hK : FixedFoldCount K assign)
    (hbdd : BoundedOutcome P) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ (n : ℕ) (B : ℝ) (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ),
        0 < n → 0 ≤ B →
        (∀ (k : Fin K), ∀ π ∈ policySet, ∀ O, |g k π O| ≤ B) →
        (∀ (k : Fin K), ∀ π ∈ policySet,
          ∫ O, (g k π O) ^ 2 ∂P.dataMeasure
            ≤ C * B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
        expectedPooledOffsetSup P g (assign n) policySet
          ≤ C * (B ^ 2 / (n : ℝ)) ^ ((1 + α) / (2 + α)) * (Real.log n) ^ p := by
  sorry

-- @node: lem:localized-vc-self-bound
/-- `lem:localized-vc-self-bound`. EXPECTED-risk self-localized selection bound
from the offset-control node. With `ρ_n = (B²/n)^{A_α}(log n)^p`, `B ≥ 1`, the
EXPECTED pooled offset positive-part supremum controlled by `ρ_n` (the bound
supplied by `crossfit_localized_offset_control`, `hoff`), and any data-dependent
`Π`-valued selector `π̃` satisfying the SAMPLE-WISE selection inequality
`R_P(π̃(sample)) ≤ 2|G_cf(sample, π̃(sample))| + δ`, the EXPECTED regret obeys
`E_P R_P(π̃) ≤ C{ρ_n + δ}`, and if `δ ≤ 1/n` the `δ` term is absorbed into
`C ρ_n`. -/
lemma localized_vc_self_bound {n K : ℕ} (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (α B δ p : ℝ)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (πt : (Fin n → Observation 𝒳) → Policy 𝒳)
    (hB : 1 ≤ B) (hn : 0 < n) (hp : 0 ≤ p)
    (hmem : ∀ sample, πt sample ∈ policySet)
    (hoff : expectedPooledOffsetSup P g assign policySet
              ≤ (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p)
    (hsel : ∀ sample, lawRegret P (πt sample)
              ≤ 2 * |pooledCrossfitProcess P g assign sample (πt sample)| + δ) :
    ∃ C : ℝ, 0 < C ∧
      ∫ sample, lawRegret P (πt sample)
            ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          ≤ C * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p + δ) ∧
      (δ ≤ (n : ℝ)⁻¹ →
        ∫ sample, lawRegret P (πt sample)
              ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
            ≤ C * (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p) := by
  sorry

-- @node: lem:crude-localized-master-bound
/-- `lem:crude-localized-master-bound`. Pooled crude `q^{-2}`-envelope master
bound for the cross-fit clipped-AIPW `1/n`-ERM (`enum` skeleton, foldwise
nuisances, `assign` partition). BOTH overlap regimes: for `γ>0` with `q ≤ c_o u^γ`
it is the five-term bound; for `γ=0` with fixed `q ≤ underline_p/2` it collapses
to `C{n^{-A_α}+r_μ r_e}(log n)^p`. -/
lemma crude_localized_master_bound {n K : ℕ} (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳))
    (α γ Cm u0 Co co underlineP a c CMu CProd : ℝ) (dPi : ℕ)
    (assign : (m : ℕ) → Fin m → Fin K) (q rMu rE u : ℝ)
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (hlaw : LawClass α γ Cm u0 Co co underlineP policySet P)
    (hopt : OptimalInClass P policySet)
    (hvc : PolicyClassVC policySet dPi)
    (henum : ∀ j, enum j ∈ policySet)
    (hK : FixedFoldCount K assign) (hiid : IsIIDSample P)
    (hbn : ∀ k x, muHat0 k x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 k x ∈ Set.Icc (-1 : ℝ) 1)
    (hsq0 : ∀ k, ∫ x, (muHat0 k x - P.mu0 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hsq1 : ∀ k, ∫ x, (muHat1 k x - P.mu1 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hse : ∀ k, ∫ x, (eHat k x - P.propensity x) ^ 2 ∂P.PX ≤ rE ^ 2)
    (hn : 0 < n) (hq : 0 < q) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      (0 < γ → 0 < u → u ≤ u0 → q ≤ co * u ^ γ →
        ∫ sample,
            lawRegret P (feasibleERM q enum muHat0 muHat1 eHat (assign n) sample)
          ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          ≤ C * ((n : ℝ) ^ (-(rStar α γ)) + ((n : ℝ) * q ^ 2) ^ (-(Aalpha α))
              + rMu * rE / q + rMu * u ^ (α / 2) * q ^ (1 / (2 * γ))
              + rMu ^ 2 / u) * (Real.log n) ^ p) ∧
      (γ = 0 → q ≤ underlineP / 2 →
        ∫ sample,
            lawRegret P (feasibleERM q enum muHat0 muHat1 eHat (assign n) sample)
          ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          ≤ C * ((n : ℝ) ^ (-(Aalpha α)) + rMu * rE) * (Real.log n) ^ p) := by
  sorry

-- @node: lem:clip-balance-exponent
/-- `lem:clip-balance-exponent`. Optimization of the master-bound terms over the
DETERMINISTIC `def:feasible-rate` schedule `q_n = qSched`, `u_n = uSched` (tied to
`s_feas`, `t_feas`, not arbitrary) under the admissibility `q_n ≤ c_o u_n^γ`, to
the exponent `r_feas = (feasibleRate α γ a c q0 uBar).r`. BOTH regimes: for `γ>0` the
five master-bound terms; for `γ=0` the fixed-clip `n^{-A_α}+r_μ r_e` terms. -/
lemma clip_balance_exponent (α γ a c CMu CProd q0 uBar co : ℝ) (rMu rE : ℕ → ℝ)
    (hpoly : PolynomialNuisanceExponents rMu rE a c CMu CProd)
    (hq0 : 0 < q0) (huBar : 0 < uBar)
    (hadm : feasibleAdmissible α γ a c co q0 uBar) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      (0 < γ → ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) ^ (-(rStar α γ))
          + ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α))
          + rMu n * rE n / qSched α γ a c q0 n
          + rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
          + (rMu n) ^ 2 / uSched α γ a c uBar n
        ≤ C * (n : ℝ) ^ (-(feasibleRate α γ a c q0 uBar).r) * (Real.log n) ^ p) ∧
      (γ = 0 → ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n
        ≤ C * (n : ℝ) ^ (-(feasibleRate α γ a c q0 uBar).r) * (Real.log n) ^ p) := by
  sorry

end CausalSmith.Stat.PolicyRegretMarginOverlap
