/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy-regret rate under coupled margin / one-sided overlap decay: shared core

Stage-2 scaffold for `stat_policy_regret_margin_overlap` (v1).

This file carries the shared environment S-blocks, the assumption-atom
`def`s, the construction `def`s, the `LawClass` structure, and the two shared
foundational theorems (`thm:welfare-identity`, `thm:margin-localization`) plus
`prop:overlap-envelope`. Each emitted declaration carries its own node tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.PO.*`, `Causalean.Estimation.*` (ATE/AIPW, POSystem) | bypass-justified | Causal-structural / uncapped-influence abstraction; honest_scope makes consistency/unconfoundedness non-load-bearing, so the observed-law world is `Measure`-over-Mathlib. |
| `Causalean.Stat.Minimax.{TotalVariation,ChiSquared}` | reuse (in `T_minimax_lower`) | `chiSqDiv`, `tvDist_le_half_sqrt_chiSqDiv`, `chiSqDiv_prod` feed the Le Cam two-point testing floor. |
| `Causalean.Stat.Concentration.{VCLocalizedRegime,UniformDeviationLocalized}` | reuse target (assumed envelopes) | analytic content behind `ass:vc-localized-(offset-)envelope`, here bound as explicit `Prop` hypotheses over real localized/offset processes. |

No new typeclasses are introduced.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Causalean.Stat.Sample

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

/-! ## Environment S1 — observed-law policy-learning world -/

-- @env: S1
variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Deterministic binary policy `X → {0,1}`.
@realizes pi(𝒳→Bool realizes 𝒳→{0,1}) -/
abbrev Policy (𝒳 : Type*) := 𝒳 → Bool

/-- Real indicator of a Boolean. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- Observation `O=(X,A,Y) ∈ 𝒳 × {0,1} × [-1,1]`. The treatment space `{0,1}`
is encoded at the TYPE level by `A : Bool` (`true ↦ 1`, `false ↦ 0`, via
`boolIndicator`); the outcome space `[-1,1]` is a RANGE/support constraint carried
at the law level (`BoundedOutcome`, `WellFormedLaw`) rather than by a subtype,
since the witness measure constructions are stated over `ℝ`.
@realizes O(carrier 𝒳×Bool×ℝ realizes 𝒳×{0,1}×[-1,1]) -/
structure Observation (𝒳 : Type*) where
  X : 𝒳
  A : Bool -- @realizes A(A:Bool ↔ {0,1} at type level)
  Y : ℝ -- @realizes Y(carrier ℝ; range [-1,1] via BoundedOutcome)

instance instMeasurableSpaceObservation : MeasurableSpace (Observation 𝒳) :=
  MeasurableSpace.comap (fun O : Observation 𝒳 => (O.X, O.A, O.Y)) inferInstance

/-- Optimal policy `π_⋆(x)=1{τ(x) ≥ 0}`.
@realizes pi_star(Policy-valued, i.e. 𝒳→{0,1}) -/
noncomputable def optimalPolicy (τ : 𝒳 → ℝ) : Policy 𝒳 :=
  fun x => if 0 ≤ τ x then true else false

-- @node: def:disagreement
/-- Disagreement set `D_π = {x : π(x) ≠ π_⋆(x)}`. -/
def disagreementSet (π πstar : Policy 𝒳) : Set 𝒳 :=
  {x | π x ≠ πstar x}

/-- Real indicator of disagreement. -/
def disagreementIndicator (π πstar : Policy 𝒳) (x : 𝒳) : ℝ :=
  if π x ≠ πstar x then 1 else 0

/-- Welfare `V_P(π)=E_P[π(X) τ(X)]`.
@realizes V_P((𝒳→{0,1})→ℝ welfare functional) -/
noncomputable def welfare (PX : Measure 𝒳) (τ : 𝒳 → ℝ) (π : Policy 𝒳) : ℝ :=
  ∫ x, boolIndicator (π x) * τ x ∂PX

-- @node: def:welfare-regret
/-- Welfare regret `R_P(π)=V_P(π_⋆)-V_P(π)`, with `π_⋆=optimalPolicy τ`.
@realizes R_P((𝒳→{0,1})→ℝ regret functional) -/
noncomputable def regret (PX : Measure 𝒳) (τ : 𝒳 → ℝ) (π : Policy 𝒳) : ℝ :=
  welfare PX τ (optimalPolicy τ) - welfare PX τ π

/-- Build-inline observed-law object: the covariate marginal, the per-draw
observation law, and the law-side nuisance functionals the statements range
over. -/
structure ObservedLaw (𝒳 : Type*) [MeasurableSpace 𝒳] where
  dataMeasure : Measure (Observation 𝒳) -- @realizes O(law of O; its conditional structure given X is pinned to e_P, mu_0, mu_1 by the WellFormedLaw semantic clauses)
  PX : Measure 𝒳
  contrast : 𝒳 → ℝ -- @realizes tau_P(carrier 𝒳→ℝ; =μ₁-μ₀ & range [-2,2] via WellFormedLaw+BoundedOutcome)
  propensity : 𝒳 → ℝ -- @realizes e_P(carrier 𝒳→ℝ; range via WellFormedLaw+Positivity)
  mu0 : 𝒳 → ℝ -- @realizes mu_0(carrier 𝒳→ℝ; [-1,1] via BoundedOutcome)
  mu1 : 𝒳 → ℝ -- @realizes mu_1(carrier 𝒳→ℝ; [-1,1] via BoundedOutcome)

/-- Overlap `p_P(x)=min(e_P(x),1-e_P(x))`.
@realizes p_P(min(e,1-e); ∈[0,1/2] since e∈[0,1] via WellFormedLaw) -/
noncomputable def overlap (P : ObservedLaw 𝒳) (x : 𝒳) : ℝ :=
  min (P.propensity x) (1 - P.propensity x)

/-- Law-attached optimal policy. -/
noncomputable def lawOptimalPolicy (P : ObservedLaw 𝒳) : Policy 𝒳 :=
  optimalPolicy P.contrast

/-- Law-attached welfare. -/
noncomputable def lawWelfare (P : ObservedLaw 𝒳) (π : Policy 𝒳) : ℝ :=
  welfare P.PX P.contrast π

/-- Law-attached regret `R_P(π)`. -/
noncomputable def lawRegret (P : ObservedLaw 𝒳) (π : Policy 𝒳) : ℝ :=
  regret P.PX P.contrast π

/-- Well-formedness of an observed law on `𝒳 × {0,1} × [-1,1]`: the data law and
its covariate marginal are PROBABILITY measures, `P_X` IS the covariate marginal
of `dataMeasure`, the contrast is the regression difference `τ = μ₁ - μ₀`, and the
propensity takes values in `[0,1]`. These are the ambient SPACE/probability/marginal
facts (not statistical modelling assumptions); carrying them makes the welfare and
minimax integrals genuine Bochner integrals (probability measures), not junk
values.

The final three conjuncts are the OBSERVED-LAW SEMANTIC CONDITIONS tying
`dataMeasure` to the nuisance functionals `e_P`, `μ₀`, `μ₁`: they pin
`e_P(x)=P(A=1∣X=x)`, `μ₁(x)=E[Y∣A=1,X=x]`, and `μ₀(x)=E[Y∣A=0,X=x]` in the
standard tested (weak / conditional-expectation defining) form — for every bounded
measurable covariate test function `φ`, the `dataMeasure`-integral of the
arm-weighted (and outcome-weighted) score equals the `P_X`-integral of the
corresponding closed form. Without these the nuisance fields are detached from the
data law and `lem:clip-bias` is not the genuine conditional-expectation drift
identity. Bundled into `LawClass`. -/
def WellFormedLaw (P : ObservedLaw 𝒳) : Prop :=
  IsProbabilityMeasure P.dataMeasure ∧
    IsProbabilityMeasure P.PX ∧
    P.dataMeasure.map (fun O => O.X) = P.PX ∧
    -- Measurability of the law functionals: a well-formed law's contrast/propensity/regressions
    -- are measurable (implicit in the `.tex`'s Bochner integrals ∫|τ|·1{D_π}, ∫ e·φ, …). Regularity
    -- bookkeeping needed to make the welfare/regret integral manipulations genuine.
    Measurable P.contrast ∧ Measurable P.propensity ∧ Measurable P.mu0 ∧ Measurable P.mu1 ∧
    (∀ x, P.contrast x = P.mu1 x - P.mu0 x) ∧ -- @realizes tau_P(contrast x = mu1 x - mu0 x)
    (∀ x, P.propensity x ∈ Set.Icc (0 : ℝ) 1) ∧ -- @realizes e_P(propensity x ∈ Icc 0 1)
    (∀ φ : 𝒳 → ℝ, Measurable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
      ∫ O, boolIndicator O.A * φ O.X ∂P.dataMeasure
        = ∫ x, P.propensity x * φ x ∂P.PX) ∧ -- @realizes e_P(e_P = P(A=1∣X): ∫ 1{A}·φ dP = ∫ e_P·φ dP_X)
    (∀ φ : 𝒳 → ℝ, Measurable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
      ∫ O, boolIndicator O.A * O.Y * φ O.X ∂P.dataMeasure
        = ∫ x, P.propensity x * P.mu1 x * φ x ∂P.PX) ∧ -- @realizes mu_1(mu1 = E[Y∣A=1,X]: ∫ 1{A}·Y·φ dP = ∫ e_P·mu1·φ dP_X)
    (∀ φ : 𝒳 → ℝ, Measurable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
      ∫ O, (1 - boolIndicator O.A) * O.Y * φ O.X ∂P.dataMeasure
        = ∫ x, (1 - P.propensity x) * P.mu0 x * φ x ∂P.PX) -- @realizes mu_0(mu0 = E[Y∣A=0,X]: ∫ 1{A=0}·Y·φ dP = ∫ (1-e_P)·mu0·φ dP_X)

/-! ## Assumption `def`s -/

-- @node: ass:iid
/-- A1 i.i.d. sampling (`ass:iid`): the `n` observations are an i.i.d. sample
drawn from the observed law `P`. This carries the FULL i.i.d. sampling content by
reusing the cluster primitive `Causalean.Stat.IIDSample` — a sequence of
measurable maps `Z i` on a common ambient probability space `(Ω, μ)` with mutual
independence (`iIndepFun`), identical distribution (`IdentDistrib`), and law-match
`μ.map (Z 0) = P.dataMeasure` — rather than only asserting that the one-draw law
is a probability measure (which omits the i.i.d. content). The conjoined
`IsProbabilityMeasure P.dataMeasure` certifies that the per-draw law, hence the
`n`-fold experiment `Measure.pi (fun _ : Fin n => P.dataMeasure)` formed
downstream, is a probability measure. -/
def IsIIDSample (P : ObservedLaw 𝒳) : Prop :=
  IsProbabilityMeasure P.dataMeasure ∧
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : @MeasureTheory.Measure Ω _mΩ),
      Nonempty (@Causalean.Stat.IIDSample Ω (Observation 𝒳) _mΩ
        instMeasurableSpaceObservation μ P.dataMeasure)

-- @node: ass:bounded-outcome
/-- A2 bounded outcomes: the (potential) outcome `Y(a)` lies in `[-1,1]` for both
treatment arms `a ∈ {0,1}`. Treatment is binary at the TYPE level (`Observation.A :
Bool`, `true ↦ 1`), so the observed-law projection of `Y(a) ∈ [-1,1]` is the
conjunction of: the OBSERVED outcome lies in the EXACT range `[-1,1]` a.s. under the
data law (the realized `Y = Y(A)`, hence the realized arm's potential outcome), and
both outcome REGRESSIONS `μ₀, μ₁` — the arm-conditional means `E[Y(a)|X]` for
`a ∈ {0,1}` — also lie in `[-1,1]`. The ranges are stated as `Set.Icc (-1) 1`
membership so the encoding realizes the `[-1,1]` symbol space exactly (not merely an
absolute-value surrogate). -/
def BoundedOutcome (P : ObservedLaw 𝒳) : Prop :=
  (∀ᵐ O ∂P.dataMeasure, O.Y ∈ Set.Icc (-1 : ℝ) 1) ∧ -- @realizes Y(O.Y ∈ Icc (-1) 1 a.s.)
    (∀ x, P.mu0 x ∈ Set.Icc (-1 : ℝ) 1 ∧ P.mu1 x ∈ Set.Icc (-1 : ℝ) 1) -- @realizes mu_0(mu0 x ∈ Icc (-1) 1), mu_1(mu1 x ∈ Icc (-1) 1)

-- @node: ass:positivity
/-- A3 positivity: `0 < e_P(X) < 1` holds `P_X`-a.s.
@realizes e_P(a.s. 0 < propensity x ∧ propensity x < 1) -/
def Positivity (P : ObservedLaw 𝒳) : Prop :=
  ∀ᵐ x ∂P.PX, 0 < P.propensity x ∧ P.propensity x < 1

-- @node: ass:margin
/-- A4 Tsybakov margin: `P(0<|τ|≤u) ≤ C_m u^α` for `0 < u ≤ u_0`, with the named
condition's intrinsic parameter domain — nonnegative margin exponent `α`, positive
constant `C_m`, positive window `u_0` ([Tsybakov 2004]). The domain is load-bearing:
without `0 ≤ α` the localization bound is false (`α = -2` gives exponent `2`, and a
constant-contrast law forces `1 ≤ C·R²`, impossible uniformly as `R → 0`). -/
def MarginTail (P : ObservedLaw 𝒳) (Cm α u0 : ℝ) : Prop :=
  0 ≤ α ∧ 0 < Cm ∧ 0 < u0 ∧
  ∀ u : ℝ, 0 < u → u ≤ u0 →
    P.PX.real {x | 0 < |P.contrast x| ∧ |P.contrast x| ≤ u} ≤ Cm * u ^ α

-- @node: ass:zero-effect
/-- A5 canonical zero-effect region: either the zero-contrast set is null, or
every policy in the class agrees with `π_⋆` there. -/
def ZeroEffectRegular (P : ObservedLaw 𝒳) (policySet : Set (Policy 𝒳)) : Prop :=
  P.PX.real {x | P.contrast x = 0} = 0 ∨
    ∀ π ∈ policySet,
      P.PX.real {x | P.contrast x = 0 ∧ π x ≠ lawOptimalPolicy P x} = 0

-- @node: ass:overlap-decay
/-- A6 (novel) one-sided overlap-decay envelope:
`P{p_P ≤ v, 0<|τ|≤u} ≤ C_o u^α v^{1/γ}` for `0<v ≤ c_o u^γ`
(with `v^{1/γ}=1` when `γ=0`) in the margin window `0 < u ≤ u_0`. -/
def OverlapDecay (P : ObservedLaw 𝒳) (u0 Co co α γ : ℝ) : Prop :=
  ∀ u v : ℝ, 0 < u → u ≤ u0 → 0 < v → v ≤ co * u ^ γ →
    P.PX.real {x | overlap P x ≤ v ∧ 0 < |P.contrast x| ∧ |P.contrast x| ≤ u}
      ≤ Co * u ^ α * (if γ = 0 then 1 else v ^ (1 / γ))

-- @node: ass:policy-class
/-- A7 pointwise measurable finite-VC policy class with a countable
pointwise-dense skeleton `Π₀` and polynomial (Sauer–Shelah) trace growth at
VC-dimension `d_Π`.
@realizes Pi(policySet : Set (Policy 𝒳); measurable, countable dense skeleton, finite-VC) -/
def PolicyClassVC (policySet : Set (Policy 𝒳)) (dPi : ℕ) : Prop :=
  (∀ π ∈ policySet, Measurable π) ∧
  (∃ Pi0 : Set (Policy 𝒳), Pi0.Countable ∧ Pi0 ⊆ policySet ∧
    ∀ π ∈ policySet, ∃ seq : ℕ → Policy 𝒳,
      (∀ j, seq j ∈ Pi0) ∧ ∀ x, ∀ᶠ j in Filter.atTop, seq j x = π x) ∧
  (∀ m : ℕ, ∀ s : Fin m → 𝒳,
    Nat.card ((fun π : Policy 𝒳 => fun i => π (s i)) '' policySet) ≤ (m + 1) ^ dPi)

-- @node: ass:optimal-in-class
/-- A8 optimum-in-class: `π_⋆ ∈ Π`. -/
def OptimalInClass (P : ObservedLaw 𝒳) (policySet : Set (Policy 𝒳)) : Prop :=
  lawOptimalPolicy P ∈ policySet

-- @node: ass:margin-window
/-- A9 margin-window normalization: `0 < u_0 < 2`. -/
def MarginWindow (u0 : ℝ) : Prop := 0 < u0 ∧ u0 < 2

-- @node: ass:nuisance-rate
/-- A10 cross-fit L²(P) nuisance rates with product rate `O(n^{-1/2})`. The per-`n`
L²(P) rate bounds `‖μ̂_a-μ_a‖ ≤ r_μ,n`, `‖ê-e‖ ≤ r_e,n` are definitional (they
DEFINE the rate schedules `r_μ,n, r_e,n`), so they are stated for every `n`; the
product rate is the genuinely ASYMPTOTIC `O(n^{-1/2})` of the NL — stated as an
EVENTUAL bound (`∀ᶠ n in atTop`), not a per-`n` claim that would be false at `n=0`
(where `(0:ℝ)^{-1/2}=0`). -/
def NuisanceRate (P : ObservedLaw 𝒳)
    (muHat0 muHat1 eHat : ℕ → 𝒳 → ℝ) (rMu rE : ℕ → ℝ) : Prop :=
  (∀ n, ∫ x, (muHat0 n x - P.mu0 x) ^ 2 ∂P.PX ≤ (rMu n) ^ 2) ∧
  (∀ n, ∫ x, (muHat1 n x - P.mu1 x) ^ 2 ∂P.PX ≤ (rMu n) ^ 2) ∧
  (∀ n, ∫ x, (eHat n x - P.propensity x) ^ 2 ∂P.PX ≤ (rE n) ^ 2) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    rMu n * rE n ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)))

-- @node: ass:strict-overlap-endpoint
/-- A11 strict-overlap endpoint: when `γ=0`, `p_P ≥ underline_p` a.s. -/
def StrictOverlapEndpoint (P : ObservedLaw 𝒳) (γ underlineP : ℝ) : Prop :=
  γ = 0 →
    0 < underlineP ∧ underlineP ≤ 1 / 2 ∧ (∀ᵐ x ∂P.PX, underlineP ≤ overlap P x)

-- @node: ass:bounded-crossfit-nuisances
/-- A12 bounded cross-fit outcome regressions: `μ̂_a ∈ [-1,1]`. -/
def BoundedCrossfitNuisances (muHat0 muHat1 : ℕ → 𝒳 → ℝ) : Prop :=
  ∀ n x, muHat0 n x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 n x ∈ Set.Icc (-1 : ℝ) 1

-- @node: ass:polynomial-nuisance-exponents
/-- A13 polynomial nuisance exponents: `r_μ ≤ C_μ n^{-a}` and
`r_μ r_e ≤ C_prod n^{-c}` for large `n`, with `a ≥ 0`, `c ≥ 1/2`. -/
def PolynomialNuisanceExponents (rMu rE : ℕ → ℝ) (a c CMu CProd : ℝ) : Prop :=
  0 ≤ a ∧ 1 / 2 ≤ c ∧
    ∀ᶠ n in Filter.atTop,
      rMu n ≤ CMu * (n : ℝ) ^ (-a) ∧ rMu n * rE n ≤ CProd * (n : ℝ) ^ (-c)

-- @node: ass:fixed-crossfit-fold-count
/-- A14 fixed-`K` balanced cross-fitting: `K` is a fixed positive integer
independent of `n` (a single `ℕ`, not an `n`-indexed quantity), and the
deterministic fold-assignment `assign n : Fin n → Fin K` realizes a balanced
partition `I_1,…,I_K` of `{1,…,n}` whose every cell has size `⌊n/K⌋` or
`⌊n/K⌋+1`. -/
def FixedFoldCount (K : ℕ) (assign : (n : ℕ) → Fin n → Fin K) : Prop :=
  0 < K ∧
    ∀ n : ℕ, ∀ k : Fin K,
      Nat.card {i : Fin n // assign n i = k} = n / K ∨
        Nat.card {i : Fin n // assign n i = k} = n / K + 1

/-- Policy-compatible increments factor through the binary policy decision
`π O.X`. This is the well-posedness condition making the real-valued increment
class a fixed kernel composition with the finite-VC binary policy traces, which
is the structure needed for the localized empirical-process rate. -/
def PolicyCompatible (g : Policy 𝒳 → Observation 𝒳 → ℝ) : Prop :=
  ∃ G : Observation 𝒳 → Bool → ℝ, ∀ π O, g π O = G O (π O.X)

-- @node: ass:vc-localized-envelope
-- Atomic empirical-process ASSUMPTION (note kind `empirical-process`): carried as
-- this threaded Prop hypothesis on the consumers, NOT discharged. See Helpers.lean.
/-- A15 localized finite-VC fixed-radius empirical-process envelope. This is a
GENUINE in-EXPECTATION bound on a real centered policy-indexed empirical process
`(P_m - P) g_π` built from an i.i.d. sample of size `m` drawn from `P.dataMeasure`
(not an abstract scalar placeholder): for every policy-compatible increment `g`
with envelope `B` and localized conditional second moment `≤ B² P_X(D_π)`, the
EXPECTED localized supremum over `{π : R_P(π) ≤ r}` is bounded by
`C B m^{-1/2} r^{α/(2+2α)}(log m)^p`.
The second-moment coupling constant is fixed (`B²`, decoupled from the rate
constant `C`). -/
def VCLocalizedEnvelope (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (α : ℝ) : Prop :=
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ (m : ℕ) (B r : ℝ) (g : Policy 𝒳 → Observation 𝒳 → ℝ),
      PolicyCompatible g →
      0 < m → 0 ≤ B → 0 ≤ r →
      (∀ π ∈ policySet, ∀ O, |g π O| ≤ B) →
      (∀ π ∈ policySet,
        ∫ O, (g π O) ^ 2 ∂P.dataMeasure
          ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
      ∫ sample,
          sSup ((fun π => |(m : ℝ)⁻¹ * ∑ i, g π (sample i)
                  - ∫ O, g π O ∂P.dataMeasure|) ''
            {π | π ∈ policySet ∧ lawRegret P π ≤ r})
        ∂(Measure.pi (fun _ : Fin m => P.dataMeasure))
        ≤ C * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
            * (Real.log m) ^ p

/-- Uniform class-level version of `VCLocalizedEnvelope`. The constants `C,p`
depend on the policy class and `α`, not on the individual law `P`; this is the
shape needed before taking a supremum over laws in `upperRisk`. -/
def VCLocalizedEnvelopeUnif
    (policySet : Set (Policy 𝒳)) (α : ℝ) : Prop :=
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ P : ObservedLaw 𝒳,
      ∀ (m : ℕ) (B r : ℝ) (g : Policy 𝒳 → Observation 𝒳 → ℝ),
        PolicyCompatible g →
        0 < m → 0 ≤ B → 0 ≤ r →
        (∀ π ∈ policySet, ∀ O, |g π O| ≤ B) →
        (∀ π ∈ policySet,
          ∫ O, (g π O) ^ 2 ∂P.dataMeasure
            ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
        ∫ sample,
            sSup ((fun π => |(m : ℝ)⁻¹ * ∑ i, g π (sample i)
                    - ∫ O, g π O ∂P.dataMeasure|) ''
              {π | π ∈ policySet ∧ lawRegret P π ≤ r})
          ∂(Measure.pi (fun _ : Fin m => P.dataMeasure))
          ≤ C * B * (m : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
              * (Real.log m) ^ p

/-- A uniform class-level localized envelope supplies the old per-law envelope
for every law. -/
theorem VCLocalizedEnvelopeUnif.forall_vcLocalizedEnvelope
    (policySet : Set (Policy 𝒳)) (α : ℝ)
    (h : VCLocalizedEnvelopeUnif policySet α) :
    ∀ P : ObservedLaw 𝒳, VCLocalizedEnvelope P policySet α := by
  intro P
  rcases h with ⟨C, p, hC, hp, H⟩
  exact ⟨C, p, hC, hp, H P⟩

-- @node: ass:vc-localized-offset-envelope
-- Atomic empirical-process ASSUMPTION (note kind `empirical-process`): carried as
-- this threaded Prop hypothesis on the consumers, NOT discharged. See Helpers.lean.
/-- A16 localized finite-VC offset/Rademacher bound. The GENUINE in-EXPECTATION
offset positive-part bound on a real centered empirical process `(P_m - P) g_π`
from an i.i.d. sample of size `m`: `E sup_π {2|z_π| - R_P(π)/4}_+ ≤
C (B²/m)^{A_α}(log m)^p`, `A_α=(1+α)/(2+α)`, with the same fixed `B²` second-moment
coupling, for policy-compatible increments. -/
def VCLocalizedOffsetEnvelope (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (α : ℝ) : Prop :=
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ (m : ℕ) (B : ℝ) (g : Policy 𝒳 → Observation 𝒳 → ℝ),
      PolicyCompatible g →
      0 < m → 0 ≤ B →
      (∀ π ∈ policySet, ∀ O, |g π O| ≤ B) →
      (∀ π ∈ policySet,
        ∫ O, (g π O) ^ 2 ∂P.dataMeasure
          ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
      ∫ sample,
          sSup ((fun π => max 0 (2 * |(m : ℝ)⁻¹ * ∑ i, g π (sample i)
                  - ∫ O, g π O ∂P.dataMeasure| - lawRegret P π / 4)) '' policySet)
        ∂(Measure.pi (fun _ : Fin m => P.dataMeasure))
        ≤ C * (B ^ 2 / (m : ℝ)) ^ ((1 + α) / (2 + α)) * (Real.log m) ^ p

/-- Uniform class-level version of `VCLocalizedOffsetEnvelope`. The constants
`C,p` are hoisted above `∀ P`, matching the note's class-level finite-VC offset
assumption. -/
def VCLocalizedOffsetEnvelopeUnif
    (policySet : Set (Policy 𝒳)) (α : ℝ) : Prop :=
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ P : ObservedLaw 𝒳,
      ∀ (m : ℕ) (B : ℝ) (g : Policy 𝒳 → Observation 𝒳 → ℝ),
        PolicyCompatible g →
        0 < m → 0 ≤ B →
        (∀ π ∈ policySet, ∀ O, |g π O| ≤ B) →
        (∀ π ∈ policySet,
          ∫ O, (g π O) ^ 2 ∂P.dataMeasure
            ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P))) →
        ∫ sample,
            sSup ((fun π => max 0 (2 * |(m : ℝ)⁻¹ * ∑ i, g π (sample i)
                    - ∫ O, g π O ∂P.dataMeasure| - lawRegret P π / 4)) '' policySet)
          ∂(Measure.pi (fun _ : Fin m => P.dataMeasure))
          ≤ C * (B ^ 2 / (m : ℝ)) ^ ((1 + α) / (2 + α)) * (Real.log m) ^ p

/-- A uniform class-level localized offset envelope supplies the old per-law
offset envelope for every law. -/
theorem VCLocalizedOffsetEnvelopeUnif.forall_vcLocalizedOffsetEnvelope
    (policySet : Set (Policy 𝒳)) (α : ℝ)
    (h : VCLocalizedOffsetEnvelopeUnif policySet α) :
    ∀ P : ObservedLaw 𝒳, VCLocalizedOffsetEnvelope P policySet α := by
  intro P
  rcases h with ⟨C, p, hC, hp, H⟩
  exact ⟨C, p, hC, hp, H P⟩

/-! ## Exponent / schedule constructions (S2) -/

/-- `A_α = (1+α)/(2+α)`. -/
noncomputable def Aalpha (α : ℝ) : ℝ := (1 + α) / (2 + α)

/-- Admissible weak-arm exponent `β_{α,γ}`. -/
noncomputable def betaAG (α γ : ℝ) : ℝ :=
  if γ = 0 then 0 else α * γ / (α + 1)

/-- Converse denominator `D_{α,γ} = 2 + α + β_{α,γ}`. -/
noncomputable def Dag (α γ : ℝ) : ℝ := 2 + α + betaAG α γ

/-- Information exponent `r_⋆(α,γ) = (1+α)/D_{α,γ}`. -/
noncomputable def rStar (α γ : ℝ) : ℝ := (1 + α) / Dag α γ

-- @node: def:exponents
/-- Derived information exponents `(β_{α,γ}, D_{α,γ}, r_⋆)`. -/
noncomputable def infoExponents (α γ : ℝ) : ℝ × ℝ × ℝ :=
  (betaAG α γ, Dag α γ, rStar α γ)

/-- The `def:feasible-rate` balance objective `φ(s,t)` for a fixed regime. -/
noncomputable def feasiblePhi (α γ a c s t : ℝ) : ℝ :=
  min (min (Aalpha α * (1 - 2 * s)) (c - s))
      (min (a + s / (2 * γ) + α * t / 2) (2 * a - t))

/-- The joint feasible exponent `g_joint`, the maximal value of `φ` on the
compact feasible box. -/
noncomputable def gJoint (α γ a c : ℝ) : ℝ :=
  sSup ((fun st : ℝ × ℝ => feasiblePhi α γ a c st.1 st.2) ''
    {st : ℝ × ℝ | 0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / γ})

/-- A joint maximizer `(s_feas, t_feas)` of `φ` on the compact feasible box. -/
noncomputable def feasibleMaximizer (α γ a c : ℝ) : ℝ × ℝ :=
  Classical.epsilon fun st : ℝ × ℝ =>
    0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / γ ∧
      feasiblePhi α γ a c st.1 st.2 = gJoint α γ a c

/-- The analysis clip exponent `s_feas` (`q_n = q_0 n^{-s_feas}`). -/
noncomputable def sFeas (α γ a c : ℝ) : ℝ := (feasibleMaximizer α γ a c).1

/-- The margin-window exponent `t_feas` (`u_n = ū n^{-t_feas}`). -/
noncomputable def tFeas (α γ a c : ℝ) : ℝ := (feasibleMaximizer α γ a c).2

/-- Feasible clip schedule. For `γ>0` this is `q_n = q_0 n^{-s_feas}`; for `γ=0`
the construction uses the FIXED clip `q_n = q_0` (`≤ underline_p/2`), per
`def:feasible-rate`. -/
noncomputable def qSched (α γ a c q0 : ℝ) (n : ℕ) : ℝ :=
  if γ = 0 then q0 else q0 * (n : ℝ) ^ (-(sFeas α γ a c))

/-- Feasible margin-window schedule `u_n = ū n^{-t_feas}`. -/
noncomputable def uSched (α γ a c uBar : ℝ) (n : ℕ) : ℝ :=
  uBar * (n : ℝ) ^ (-(tFeas α γ a c))

/-- Large-`n` admissibility of the schedule: `q_n ≤ c_o u_n^γ` eventually. -/
def feasibleAdmissible (α γ a c co q0 uBar : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop,
    qSched α γ a c q0 n ≤ co * (uSched α γ a c uBar n) ^ γ

/-- Admissible-input domain of `def:feasible-rate`: the NL constraints on the chosen
window/clip constants `ū, q₀` that the feasible-rate construction is stated over.
For `γ>0`: `ū ∈ (0,u₀]` and `q₀ ∈ (0, min{1/2, c_o ū^γ}]`. For `γ=0`: the fixed clip
obeys `q₀ ∈ (0, underline_p/2]`. These input restrictions are part of
`def:feasible-rate` itself (not estimator-side assumptions); without them the selected
schedule `q_n = qSched`, `u_n = uSched` need not lie in the admissible clipping range,
so the conditional achievability exponent is stated over this domain. -/
def FeasibleRateInputs (γ co underlineP u0 q0 uBar : ℝ) : Prop :=
  (0 < γ → 0 < uBar ∧ uBar ≤ u0 ∧ 0 < q0 ∧ q0 ≤ min (1 / 2) (co * uBar ^ γ)) ∧
    (γ = 0 → 0 < q0 ∧ q0 ≤ underlineP / 2)

/-- The solved feasible upper exponent `r_feas = min{r_⋆, g_joint}` for `γ>0`,
`min{A_α, c}` for `γ=0`. Standalone accessor of the `FeasibleRate.r` field, so a
downstream consumer that needs only the exponent VALUE (not the full certified
construction, which requires the input-domain certificate) can name it directly. -/
noncomputable def rFeas (α γ a c : ℝ) : ℝ :=
  if γ = 0 then min (Aalpha α) c else min (rStar α γ) (gJoint α γ a c)

-- @node: lem:feasible-set-compact
/-- Compactness of the positive-`γ` feasible exponent set. -/
private lemma feasibleSet_compact (γ : ℝ) (hγ : 0 < γ) :
    IsCompact
      ({st : ℝ × ℝ |
        0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / γ}) := by
  let K : Set (ℝ × ℝ) :=
    {st : ℝ × ℝ | 0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / γ}
  have hrect : IsCompact (Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 / 2 : ℝ), 1 / (2 * γ))) :=
    isCompact_Icc
  have hclosed : IsClosed K := by
    have h1 : IsClosed ({st : ℝ × ℝ | (0 : ℝ) ≤ st.1}) := by
      simpa using (isClosed_le continuous_const continuous_fst)
    have h2 : IsClosed ({st : ℝ × ℝ | st.1 ≤ (1 / 2 : ℝ)}) := by
      simpa using (isClosed_le continuous_fst continuous_const)
    have h3 : IsClosed ({st : ℝ × ℝ | (0 : ℝ) ≤ st.2}) := by
      simpa using (isClosed_le continuous_const continuous_snd)
    have h4 : IsClosed ({st : ℝ × ℝ | st.2 ≤ st.1 / γ}) := by
      simpa using (isClosed_le continuous_snd (continuous_fst.div_const γ))
    simpa [K, Set.setOf_and, Set.inter_assoc] using (((h1.inter h2).inter h3).inter h4)
  have hsub : K ⊆ Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 / 2 : ℝ), 1 / (2 * γ)) := by
    intro st hst
    rcases hst with ⟨hs0, hs1, ht0, hts⟩
    constructor
    · exact ⟨hs0, ht0⟩
    · constructor
      · exact hs1
      · have hle : st.1 / γ ≤ (1 / 2 : ℝ) / γ := by gcongr
        have hcalc : (1 / 2 : ℝ) / γ = 1 / (2 * γ) := by ring
        linarith
  simpa [K] using hrect.of_isClosed_subset hclosed hsub

-- @node: lem:feasible-maximizer-exists
/-- The positive-`γ` feasible objective attains its `gJoint` supremum. -/
private lemma feasibleMaximizer_exists (α γ a c : ℝ) (hγ : 0 < γ) :
    ∃ st : ℝ × ℝ,
      0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / γ ∧
        feasiblePhi α γ a c st.1 st.2 = gJoint α γ a c := by
  let K : Set (ℝ × ℝ) :=
    {st : ℝ × ℝ | 0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / γ}
  have hK : IsCompact K := by simpa [K] using feasibleSet_compact γ hγ
  have hne : K.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [K]
  let f : ℝ × ℝ → ℝ := fun st => feasiblePhi α γ a c st.1 st.2
  have hf : ContinuousOn f K := by
    dsimp [f, feasiblePhi, Aalpha]
    fun_prop
  rcases hK.exists_sSup_image_eq hne hf with ⟨st, hst, hstmax⟩
  refine ⟨st, ?_⟩
  rcases hst with ⟨hs0, hs1, ht0, htle⟩
  refine ⟨hs0, hs1, ht0, htle, ?_⟩
  simpa [gJoint, K, f] using hstmax.symm

-- @node: lem:feasible-maximizer-spec
/-- Specification of the epsilon-selected feasible maximizer. -/
private lemma feasibleMaximizer_spec (α γ a c : ℝ) (hγ : 0 < γ) :
    0 ≤ (feasibleMaximizer α γ a c).1 ∧
      (feasibleMaximizer α γ a c).1 ≤ 1 / 2 ∧
      0 ≤ (feasibleMaximizer α γ a c).2 ∧
      (feasibleMaximizer α γ a c).2 ≤ (feasibleMaximizer α γ a c).1 / γ ∧
      feasiblePhi α γ a c
          (feasibleMaximizer α γ a c).1 (feasibleMaximizer α γ a c).2 =
        gJoint α γ a c := by
  have hex := feasibleMaximizer_exists α γ a c hγ
  simpa [feasibleMaximizer] using Classical.epsilon_spec hex

/-- The `feasibleMaximizer` epsilon-choice lands in the compact feasible box
(`γ>0`). Existence of a maximizer — continuity of `feasiblePhi` on the nonempty
compact box `{0≤s≤1/2, 0≤t≤s/γ}` (Mathlib `IsCompact.exists_isMaxOn`) — makes the
`Classical.epsilon` specification inhabited, so its first/second components are
feasible. (Certifies `def:feasible-rate`'s "let `(s_feas,t_feas)` be any
maximizer".) -/
lemma feasibleMaximizer_mem (α γ a c : ℝ) (hγ : 0 < γ) :
    0 ≤ sFeas α γ a c ∧ sFeas α γ a c ≤ 1 / 2 ∧
      0 ≤ tFeas α γ a c ∧ tFeas α γ a c ≤ sFeas α γ a c / γ := by
  rcases feasibleMaximizer_spec α γ a c hγ with ⟨hs0, hs1, ht0, ht1, _hmax⟩
  exact ⟨hs0, hs1, ht0, ht1⟩

/-- The `feasibleMaximizer` epsilon-choice MAXIMIZES `feasiblePhi` over the compact
feasible box (`γ>0`); hence `g_joint = feasiblePhi (s_feas) (t_feas)`. -/
lemma feasibleMaximizer_isMaxOn (α γ a c : ℝ) (hγ : 0 < γ) :
    ∀ s' t' : ℝ, 0 ≤ s' → s' ≤ 1 / 2 → 0 ≤ t' → t' ≤ s' / γ →
      feasiblePhi α γ a c s' t'
        ≤ feasiblePhi α γ a c (sFeas α γ a c) (tFeas α γ a c) := by
  intro s' t' hs0 hs1 ht0 ht1
  rcases feasibleMaximizer_spec α γ a c hγ with ⟨_hs0, _hs1, _ht0, _ht1, hmaxeq⟩
  have hst_mem :
      (s', t') ∈
        ({st : ℝ × ℝ |
          0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / γ}) := by
    exact ⟨hs0, hs1, ht0, ht1⟩
  have hle : feasiblePhi α γ a c s' t' ≤ gJoint α γ a c := by
    unfold gJoint
    refine le_csSup ?_ ?_
    · have hK := feasibleSet_compact γ hγ
      exact hK.bddAbove_image (by
        dsimp [feasiblePhi, Aalpha]
        fun_prop)
    · exact ⟨(s', t'), hst_mem, rfl⟩
  calc
    feasiblePhi α γ a c s' t' ≤ gJoint α γ a c := hle
    _ = feasiblePhi α γ a c (sFeas α γ a c) (tFeas α γ a c) := by
      simpa [sFeas, tFeas] using hmaxeq.symm

/-- The selected feasible maximizer attains the joint exponent value. -/
lemma feasibleMaximizer_value (α γ a c : ℝ) (hγ : 0 < γ) :
    feasiblePhi α γ a c (sFeas α γ a c) (tFeas α γ a c) =
      gJoint α γ a c := by
  rcases feasibleMaximizer_spec α γ a c hγ with ⟨_hs0, _hs1, _ht0, _ht1, hmaxeq⟩
  simpa [sFeas, tFeas] using hmaxeq

/-- Eventual schedule admissibility `q_n ≤ c_o u_n^γ` (`γ>0`): the selected clip
`q_n = q_0 n^{-s_feas}` stays under `c_o u_n^γ = c_o ū^γ n^{-γ t_feas}` for all
large `n`, because `q_0 ≤ c_o ū^γ` (input domain `FeasibleRateInputs`) and
`t_feas ≤ s_feas/γ` (maximizer feasibility) give the exponent comparison. This is
the construction's "Then `q_n ≤ c_o u_n^γ` for all large `n`" conclusion, derived
from the inputs rather than separately assumed. -/
lemma feasibleRate_admissible_of_inputs
    (α γ a c co underlineP u0 q0 uBar : ℝ)
    (hin : FeasibleRateInputs γ co underlineP u0 q0 uBar) :
    0 < γ → feasibleAdmissible α γ a c co q0 uBar := by
  intro hγ
  unfold feasibleAdmissible
  rcases (hin.1 hγ) with ⟨huBar0, _huBar_le, hq0, hq0le⟩
  have hq0le_co : q0 ≤ co * uBar ^ γ := by
    exact le_trans hq0le (min_le_right _ _)
  have hγne : γ ≠ 0 := ne_of_gt hγ
  rcases feasibleMaximizer_mem α γ a c hγ with ⟨_hs0, _hs1, _ht0, htle⟩
  filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hbase_nonneg : (0 : ℝ) ≤ n := le_of_lt hnpos
  have hγt_le_s : γ * tFeas α γ a c ≤ sFeas α γ a c := by
    simpa [mul_comm] using (le_div_iff₀ hγ).mp htle
  have hpow_exp :
      (n : ℝ) ^ (-(sFeas α γ a c))
        ≤ (n : ℝ) ^ (-(γ * tFeas α γ a c)) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    linarith
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (-(sFeas α γ a c)) :=
    Real.rpow_nonneg hbase_nonneg _
  have hmain :
      q0 * (n : ℝ) ^ (-(sFeas α γ a c))
        ≤ (co * uBar ^ γ) * (n : ℝ) ^ (-(γ * tFeas α γ a c)) := by
    calc
      q0 * (n : ℝ) ^ (-(sFeas α γ a c))
          ≤ (co * uBar ^ γ) * (n : ℝ) ^ (-(sFeas α γ a c)) := by
            exact mul_le_mul_of_nonneg_right hq0le_co hpow_nonneg
      _ ≤ (co * uBar ^ γ) * (n : ℝ) ^ (-(γ * tFeas α γ a c)) := by
        have hcoef_nonneg : 0 ≤ co * uBar ^ γ := le_trans (le_of_lt hq0) hq0le_co
        exact mul_le_mul_of_nonneg_left hpow_exp hcoef_nonneg
  have hpow_mul :
      (uBar * (n : ℝ) ^ (-(tFeas α γ a c))) ^ γ
        = uBar ^ γ * (n : ℝ) ^ (-(γ * tFeas α γ a c)) := by
    rw [Real.mul_rpow (le_of_lt huBar0) (Real.rpow_nonneg hbase_nonneg _)]
    rw [← Real.rpow_mul hbase_nonneg]
    ring_nf
  rw [qSched, uSched, if_neg hγne]
  calc
    q0 * (n : ℝ) ^ (-(sFeas α γ a c))
        ≤ (co * uBar ^ γ) * (n : ℝ) ^ (-(γ * tFeas α γ a c)) := hmain
    _ = co * (uBar ^ γ * (n : ℝ) ^ (-(γ * tFeas α γ a c))) := by ring
    _ = co * (uBar * (n : ℝ) ^ (-(tFeas α γ a c))) ^ γ := by rw [hpow_mul]

-- @node: def:feasible-rate
/-- Certified feasible-rate object (`def:feasible-rate`). Bundles the construction
DATA — the maximizer exponents `(s_feas, t_feas)`, the SELECTED clip/window
schedules `q_n = qSched`, `u_n = uSched` (with the `γ=0` fixed-clip branch baked
into `qSched`), and the solved exponent `r_feas` — TOGETHER WITH the certifying
PROPERTIES the NL construction asserts, bundled INTO the object rather than split
into separate consumer hypotheses: the input-domain restriction on the chosen
window/clip constants `ū, q₀` (`inputs`); feasibility and maximality of
`(s_feas, t_feas)` on the compact box for `γ>0` (`feasible`, `maximal`, so
`g_joint = φ(s_feas, t_feas)`); the definitional schedule/exponent ties
(`qDef, uDef, rDef`); and the eventual schedule admissibility `q_n ≤ c_o u_n^γ`
(`admissible`). -/
structure FeasibleRate (α γ a c co underlineP u0 q0 uBar : ℝ) where
  /-- Analysis clip exponent `s_feas` (`q_n = q_0 n^{-s_feas}` for `γ>0`). -/
  s : ℝ
  /-- Margin-window exponent `t_feas` (`u_n = ū n^{-t_feas}`). -/
  t : ℝ
  /-- Solved feasible upper exponent `r_feas`. -/
  r : ℝ
  /-- Selected clip schedule `q_n` (γ-branched). -/
  q : ℕ → ℝ
  /-- Selected window schedule `u_n`. -/
  u : ℕ → ℝ
  /-- NL input-domain restriction on the chosen window/clip constants `ū, q₀`
  (`ū ∈ (0,u₀]`, `q₀ ∈ (0, min{1/2, c_o ū^γ}]` for `γ>0`;
  `q₀ ∈ (0, underline_p/2]` for `γ=0`). -/
  inputs : FeasibleRateInputs γ co underlineP u0 q0 uBar
  /-- `(s_feas, t_feas)` lies in the compact feasible box (`γ>0`). -/
  feasible : 0 < γ → 0 ≤ s ∧ s ≤ 1 / 2 ∧ 0 ≤ t ∧ t ≤ s / γ
  /-- `(s_feas, t_feas)` MAXIMIZES `feasiblePhi` over the compact box (`γ>0`), so
  `g_joint = feasiblePhi (s_feas) (t_feas)`. -/
  maximal : 0 < γ → ∀ s' t' : ℝ, 0 ≤ s' → s' ≤ 1 / 2 → 0 ≤ t' → t' ≤ s' / γ →
    feasiblePhi α γ a c s' t' ≤ feasiblePhi α γ a c s t
  /-- Selected clip schedule definition `q_n = qSched`. -/
  qDef : q = qSched α γ a c q0
  /-- Selected window schedule definition `u_n = uSched`. -/
  uDef : u = uSched α γ a c uBar
  /-- Solved-exponent definition `r_feas = min{r_⋆, g_joint}` (`γ>0`) /
  `min{A_α, c}` (`γ=0`). -/
  rDef : r = rFeas α γ a c
  /-- Eventual schedule admissibility `q_n ≤ c_o u_n^γ` (`γ>0`). -/
  admissible : 0 < γ → feasibleAdmissible α γ a c co q0 uBar

/-- Feasible-rate construction (`def:feasible-rate`). Given the NL input-domain
certificate `hin`, packages the maximizer exponents `(s_feas, t_feas)`, the
selected schedules, the solved exponent `r_feas`, and the certifying properties
(feasibility from `feasibleMaximizer_mem`, maximality from
`feasibleMaximizer_isMaxOn`, admissibility from `feasibleRate_admissible_of_inputs`)
into the certified `FeasibleRate` object. The exponent value is `rFeas α γ a c`. -/
noncomputable def feasibleRate (α γ a c co underlineP u0 q0 uBar : ℝ)
    (hin : FeasibleRateInputs γ co underlineP u0 q0 uBar) :
    FeasibleRate α γ a c co underlineP u0 q0 uBar where
  s := sFeas α γ a c
  t := tFeas α γ a c
  r := rFeas α γ a c
  q := qSched α γ a c q0
  u := uSched α γ a c uBar
  inputs := hin
  feasible := feasibleMaximizer_mem α γ a c
  maximal := feasibleMaximizer_isMaxOn α γ a c
  qDef := rfl
  uDef := rfl
  rDef := rfl
  admissible := feasibleRate_admissible_of_inputs α γ a c co underlineP u0 q0 uBar hin

/-- Lower-bound contrast height `h_n = n^{-1/D_{α,γ}}`. -/
noncomputable def hLower (α γ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / Dag α γ))

/-- Lower-bound weak-arm scale `q_n = 1/4` if `β_{α,γ}=0` else `h_n^{β_{α,γ}}`. -/
noncomputable def qLower (α γ : ℝ) (n : ℕ) : ℝ :=
  if betaAG α γ = 0 then 1 / 4 else (hLower α γ n) ^ betaAG α γ

/-! ## Clipped score constructions (S3) -/

-- @node: def:clipped-propensity
/-- Clipped propensity `e_q(x)=min(1-q, max(q, e(x)))`. -/
noncomputable def clippedPropensity (q : ℝ) (e : 𝒳 → ℝ) (x : 𝒳) : ℝ :=
  min (1 - q) (max q (e x))

-- @node: def:clipped-aipw-score
/-- Clipped AIPW score
`Γ_q(O;η)=μ₁-μ₀+(A/e_q)(Y-μ₁)-((1-A)/(1-e_q))(Y-μ₀)`. -/
noncomputable def clippedAIPWScore (q : ℝ) (mu0 mu1 e : 𝒳 → ℝ)
    (O : Observation 𝒳) : ℝ :=
  mu1 O.X - mu0 O.X
    + (boolIndicator O.A / clippedPropensity q e O.X) * (O.Y - mu1 O.X)
    - ((1 - boolIndicator O.A) / (1 - clippedPropensity q e O.X)) * (O.Y - mu0 O.X)

/-- Cross-fitted empirical clipped-AIPW welfare criterion
`V̂_{n,q}(π)=n⁻¹ ∑_i π(X_i) Γ_q(O_i; η̂^{(-k(i))})`, where `assign i = k(i)` is the
evaluation fold of observation `i` and `η̂^{(-k)}` are the foldwise cross-fitted
nuisances indexed by fold `k`. -/
noncomputable def empiricalWelfareScore {n K : ℕ} (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (sample : Fin n → Observation 𝒳) (π : Policy 𝒳) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, boolIndicator (π (sample i).X) *
    clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i)) (eHat (assign i))
      (sample i)

-- @node: def:feasible-erm
/-- Feasible clipped-AIPW `1/n`-ERM over the countable pointwise-dense skeleton
`Π₀` enumerated by `enum : ℕ → Policy 𝒳`. With foldwise cross-fitted nuisances
`η̂^{(-k)}` and fold assignment `assign`, `π̂_n = enum j_n` where `j_n` is the
SMALLEST index `j` such that `enum j` is a `1/n`-near-maximizer of the cross-fitted
criterion over the whole enumeration (`sInf` of the near-maximizer index set). -/
noncomputable def feasibleERM {n K : ℕ} (q : ℝ) (enum : ℕ → Policy 𝒳)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (sample : Fin n → Observation 𝒳) : Policy 𝒳 :=
  enum (sInf {j : ℕ |
    ∀ j' : ℕ,
      empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j')
        ≤ empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j)
            + (n : ℝ)⁻¹})

/-- `enum` enumerates the countable pointwise-dense skeleton `Π₀` of the policy
class (the `ass:policy-class` / `def:feasible-erm` requirement): every `enum j`
lies in `Π`, and every `π ∈ Π` is the pointwise limit of an `enum`-indexed
subsequence. This is the note's dense-`Π₀` enumeration condition on `enum`; it is
what reduces `sup_Π V̂` to `sup_j V̂(enum j)`, so the `feasibleERM` near-maximizer
is a genuine `Π`-wide `1/n`-ERM rather than an ERM over an ARBITRARY enumeration. -/
def DenseSkeleton (enum : ℕ → Policy 𝒳) (policySet : Set (Policy 𝒳)) : Prop :=
  (∀ j, enum j ∈ policySet) ∧
    ∀ π ∈ policySet, ∃ seq : ℕ → ℕ,
      ∀ x, ∀ᶠ j in Filter.atTop, enum (seq j) x = π x

-- @node: def:minimax-regret
/-- Minimax regret `M_n = inf_{π̂} sup_{P ∈ 𝓟} E_P R_P(π̂)`. The infimum ranges
ONLY over MEASURABLE `Π`-valued estimators: `est sample ∈ policySet` for every
realized sample (`Π`-valued), and the induced per-law regret map
`sample ↦ R_P(est sample)` is measurable for every law (so each `E_P R_P(π̂)`
is genuinely the Bochner integral, not a junk value). The regret loss is bounded
in `[0,2]`, so the `iInf`/`iSup` are well-posed. -/
noncomputable def minimaxRegret (𝓟 : Set (ObservedLaw 𝒳))
    (policySet : Set (Policy 𝒳)) (n : ℕ) : ℝ :=
  ⨅ est : {est : (Fin n → Observation 𝒳) → Policy 𝒳 //
      (∀ sample, est sample ∈ policySet) ∧
        ∀ P : ObservedLaw 𝒳,
          Measurable (fun sample : Fin n → Observation 𝒳 => lawRegret P (est sample))},
    ⨆ P : 𝓟,
      ∫ sample, lawRegret P.1 (est.1 sample)
        ∂(Measure.pi (fun _ : Fin n => P.1.dataMeasure))

-- @node: def:law-class
/-- Baseline observed-law class `𝒫_{α,γ}`: the bundle of the six member
properties at fixed uniform constants. -/
structure LawClass (α γ Cm u0 Co co underlineP : ℝ)
    (policySet : Set (Policy 𝒳)) (P : ObservedLaw 𝒳) : Prop where
  /-- Ambient space/probability/marginal/range well-formedness of the observed law
  on `𝒳 × {0,1} × [-1,1]` (probability measures, `P_X` the marginal, `τ = μ₁-μ₀`,
  propensity in `[0,1]`); this is the law-space definition, not a 7th modelling
  assumption. -/
  wf : WellFormedLaw P
  bdd : BoundedOutcome P
  pos : Positivity P
  margin : MarginTail P Cm α u0
  zero : ZeroEffectRegular P policySet
  overlapDecay : OverlapDecay P u0 Co co α γ
  strict : StrictOverlapEndpoint P γ underlineP

-- @node: def:upper-risk
/-- Regime-indexed conditional feasible upper risk
`U_n(α,γ,a,c; η̂) = sup_P E_P R_P(π̂_n)`. The estimator is the feasible cross-fit
clipped-AIPW ERM `feasibleERM` run with the SELECTED schedule clip
`q_n = qSched α γ a c q0 n` and the supplied foldwise cross-fitted nuisances
`η̂` (`n`-indexed, fold-indexed).

SCOPE (Lean encoding fidelity): the note's dense-`Π₀` enumeration condition on
`enum` (the `def:feasible-erm` requirement that `enum` enumerate a countable
pointwise-dense skeleton of `Π`) is ENFORCED here as the `DenseSkeleton enum
policySet` conjunct of the supremum domain. Since `upperRisk` is an UPPER risk
used only in the bound `U_n ≤ C n^{-r_feas}(log n)^p`, gating the domain on this
condition makes `upperRisk` the risk of the genuine pointwise-dense-skeleton ERM
of the note (with the sound `sSup ∅ = 0` sentinel when the enumeration is not a
skeleton), not the risk of an ARBITRARY enumeration-based ERM.

Per `def:upper-risk`, the supremum domain BUNDLES
the FULL list of side conditions the construction is stated over (not just the
law-dependent ones): `P ∈ LawClass` with `OptimalInClass` and the i.i.d. sampling
model `IsIIDSample`; each foldwise nuisance estimate obeying `NuisanceRate`,
`BoundedCrossfitNuisances`, and
`PolynomialNuisanceExponents` at the fixed regime `(a,c,C_μ,C_prod)`; the policy
class `Π` satisfying `PolicyClassVC` together with the per-law localized VC and
offset envelopes; and the cross-fitting scheme satisfying `FixedFoldCount`.
The `P`-independent conjuncts (`BoundedCrossfitNuisances`,
`PolynomialNuisanceExponents`, `PolicyClassVC`, `FixedFoldCount`) gate whether the
domain is nonempty; because `U_n` is an UPPER risk used only in the bound
`U_n ≤ C n^{-r_feas}(log n)^p`, the empty-domain value `sSup ∅ = 0` is a sound
sentinel (not a junk inflation, as it would be for a converse `⨆`), so bundling them
faithfully matches the note without creating a vacuity defect. -/
noncomputable def upperRisk {n K : ℕ}
    (α γ Cm u0 Co co underlineP a c CMu CProd q0 : ℝ) (dPi : ℕ)
    (policySet : Set (Policy 𝒳)) (enum : ℕ → Policy 𝒳)
    (muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ) (assign : (m : ℕ) → Fin m → Fin K)
    (rMu rE : ℕ → ℝ) : ℝ :=
  sSup ((fun P : ObservedLaw 𝒳 =>
      ∫ sample, lawRegret P
          (feasibleERM (qSched α γ a c q0 n) enum
            (muHat0 n) (muHat1 n) (eHat n) (assign n) sample)
        ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))) ''
    {P | LawClass α γ Cm u0 Co co underlineP policySet P ∧
         OptimalInClass P policySet ∧
         IsIIDSample P ∧
         (∀ k : Fin K,
           NuisanceRate P (fun m => muHat0 m k) (fun m => muHat1 m k)
             (fun m => eHat m k) rMu rE) ∧
         (∀ k : Fin K,
           BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k)) ∧
         PolynomialNuisanceExponents rMu rE a c CMu CProd ∧
         PolicyClassVC policySet dPi ∧
         VCLocalizedEnvelope P policySet α ∧
         VCLocalizedOffsetEnvelope P policySet α ∧
         FixedFoldCount K assign ∧
         DenseSkeleton enum policySet})

/-! ## Shared foundational results -/

-- @node: thm:welfare-identity
/-- `thm:welfare-identity`. Under the well-formed law (`τ = μ₁-μ₀`) and bounded
outcomes, regret equals the `|τ|`-weighted disagreement mass. `hwf` is load-bearing:
the integral identity needs `τ` integrable, and `BoundedOutcome` bounds only `μ₀,μ₁`
— the contrast field is bounded (`τ ∈ [-2,2]`) only once `WellFormedLaw` ties
`τ = μ₁-μ₀`. Both are global standing setup conditions of the observed law. -/
theorem regret_eq_disagreement_integral
    (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    lawRegret P π =
      ∫ x, |P.contrast x| * disagreementIndicator π (lawOptimalPolicy P) x ∂P.PX
    := by
  rcases hwf with
    ⟨_hprobData, _hprobPX, _hmap, hτmeas, _hemeas, _hmu0meas, _hmu1meas,
      hτeq, _herange, _heSem, _hmu1Sem, _hmu0Sem⟩
  have hτ_bound : ∀ x, |P.contrast x| ≤ (2 : ℝ) := by
    intro x
    rw [hτeq x]
    have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
    have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
    calc
      |P.mu1 x - P.mu0 x| ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hmu1 hmu0
      _ = (2 : ℝ) := by norm_num
  have hoptSet : MeasurableSet {x : 𝒳 | 0 ≤ P.contrast x} := by
    exact measurableSet_le measurable_const hτmeas
  have hπSet : MeasurableSet {x : 𝒳 | π x = true} := by
    exact hπ (measurableSet_singleton true)
  have hf_meas :
      Measurable (fun x => if 0 ≤ P.contrast x then P.contrast x else 0) :=
    Measurable.ite hoptSet hτmeas measurable_const
  have hg_meas :
      Measurable (fun x => if π x = true then P.contrast x else 0) :=
    Measurable.ite hπSet hτmeas measurable_const
  have hf_int :
      Integrable (fun x => if 0 ≤ P.contrast x then P.contrast x else 0) P.PX := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 2 ?_
    filter_upwards with x
    by_cases hx : 0 ≤ P.contrast x <;> simp [hx, hτ_bound x]
  have hg_int :
      Integrable (fun x => if π x = true then P.contrast x else 0) P.PX := by
    refine Integrable.of_bound hg_meas.aestronglyMeasurable 2 ?_
    filter_upwards with x
    by_cases hx : π x = true <;> simp [hx, hτ_bound x]
  simp [lawRegret, regret, welfare, lawOptimalPolicy, optimalPolicy, boolIndicator]
  rw [← integral_sub hf_int hg_int]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hτnon : 0 ≤ P.contrast x
  · by_cases hπtrue : π x = true
    · simp [hτnon, hπtrue, abs_of_nonneg hτnon, disagreementIndicator, optimalPolicy]
    · simp [hτnon, hπtrue, abs_of_nonneg hτnon, disagreementIndicator, optimalPolicy]
  · have hτneg : P.contrast x < 0 := lt_of_not_ge hτnon
    by_cases hπtrue : π x = true
    · simp [hτnon, hπtrue, abs_of_neg hτneg, disagreementIndicator, optimalPolicy]
    · simp [hτnon, hπtrue, abs_of_neg hτneg, disagreementIndicator, optimalPolicy]

-- @node: measurableSet_disagreementSet
/-- The disagreement set is measurable when the policy and contrast are measurable. -/
lemma measurableSet_disagreementSet (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hτmeas : Measurable P.contrast) (hπ : Measurable π) :
    MeasurableSet (disagreementSet π (lawOptimalPolicy P)) := by
  have hπtrue : MeasurableSet {x : 𝒳 | π x = true} :=
    hπ (measurableSet_singleton true)
  have hπfalse : MeasurableSet {x : 𝒳 | π x = false} :=
    hπ (measurableSet_singleton false)
  have hopttrue : MeasurableSet {x : 𝒳 | lawOptimalPolicy P x = true} := by
    have hτnonneg : MeasurableSet {x : 𝒳 | 0 ≤ P.contrast x} :=
      measurableSet_le measurable_const hτmeas
    simpa [lawOptimalPolicy, optimalPolicy] using hτnonneg
  have hoptfalse : MeasurableSet {x : 𝒳 | lawOptimalPolicy P x = false} := by
    simpa [Set.compl_setOf] using hopttrue.compl
  have hrepr : disagreementSet π (lawOptimalPolicy P) =
      ({x : 𝒳 | π x = true} ∩ {x | lawOptimalPolicy P x = false}) ∪
        ({x : 𝒳 | π x = false} ∩ {x | lawOptimalPolicy P x = true}) := by
    ext x
    cases hpi : π x <;> cases hopt : lawOptimalPolicy P x <;>
      simp [disagreementSet, hpi, hopt]
  rw [hrepr]
  exact (hπtrue.inter hoptfalse).union (hπfalse.inter hopttrue)

-- @node: regret_disagreement_large_contrast_le
/-- The welfare identity controls disagreement on the region with contrast above `u`. -/
lemma regret_disagreement_large_contrast_le
    (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π)
    {u : ℝ} (hu : 0 < u) :
    P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | u < |P.contrast x|})
      ≤ lawRegret P π / u := by
  have hreg := regret_eq_disagreement_integral P π hwf hbdd hπ
  rcases hwf with
    ⟨_hprobData, hprobPX, _hmap, hτmeas, _hemeas, _hmu0meas, _hmu1meas,
      hτeq, _herange, _heSem, _hmu1Sem, _hmu0Sem⟩
  letI : IsProbabilityMeasure P.PX := hprobPX
  let D : Set 𝒳 := disagreementSet π (lawOptimalPolicy P)
  let E : Set 𝒳 := D ∩ {x | u < |P.contrast x|}
  let f : 𝒳 → ℝ :=
    fun x => |P.contrast x| * disagreementIndicator π (lawOptimalPolicy P) x
  have hτ_bound : ∀ x, |P.contrast x| ≤ (2 : ℝ) := by
    intro x
    rw [hτeq x]
    have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
    have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
    calc
      |P.mu1 x - P.mu0 x| ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hmu1 hmu0
      _ = (2 : ℝ) := by norm_num
  have hDmeas : MeasurableSet D := measurableSet_disagreementSet P π hτmeas hπ
  have hEmeas : MeasurableSet E := by
    exact hDmeas.inter (by
      simpa [Real.norm_eq_abs] using
        (measurableSet_lt measurable_const hτmeas.norm))
  have hf_meas : Measurable f := by
    have hτabs : Measurable (fun x => |P.contrast x|) := by
      simpa [Real.norm_eq_abs] using hτmeas.norm
    dsimp [f]
    apply hτabs.mul
    unfold disagreementIndicator
    exact Measurable.ite hDmeas measurable_const measurable_const
  have hf_int : Integrable f P.PX := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 2 ?_
    filter_upwards with x
    have hind : |disagreementIndicator π (lawOptimalPolicy P) x| ≤ (1 : ℝ) := by
      unfold disagreementIndicator
      split <;> simp
    calc
      |f x| =
          |P.contrast x| * |disagreementIndicator π (lawOptimalPolicy P) x| := by
        simp [f, abs_mul]
      _ ≤ 2 * 1 := by
        gcongr
        exact hτ_bound x
      _ = (2 : ℝ) := by norm_num
  have hf_nonneg : 0 ≤ᵐ[P.PX] f := by
    filter_upwards with x
    have hind : 0 ≤ disagreementIndicator π (lawOptimalPolicy P) x := by
      unfold disagreementIndicator
      split <;> norm_num
    exact mul_nonneg (abs_nonneg _) hind
  have hf_ge_u : ∀ x ∈ E, u ≤ f x := by
    intro x hx
    rcases hx with ⟨hxD, hxlarge⟩
    have hxD' : π x ≠ lawOptimalPolicy P x := by
      simpa [D, disagreementSet] using hxD
    have hind : disagreementIndicator π (lawOptimalPolicy P) x = 1 := by
      simp [disagreementIndicator, hxD']
    calc
      u ≤ |P.contrast x| := le_of_lt hxlarge
      _ = f x := by simp [f, hind]
  have hfiniteE : P.PX E ≠ ⊤ := measure_ne_top P.PX E
  have hset_ge : u * P.PX.real E ≤ ∫ x in E, f x ∂P.PX :=
    setIntegral_ge_of_const_le_real hEmeas hfiniteE hf_ge_u hf_int.integrableOn
  have hset_le : ∫ x in E, f x ∂P.PX ≤ ∫ x, f x ∂P.PX :=
    setIntegral_le_integral hf_int hf_nonneg
  have hmul_le : u * P.PX.real E ≤ lawRegret P π := by
    rw [hreg]
    exact hset_ge.trans hset_le
  rw [show disagreementSet π (lawOptimalPolicy P) ∩ {x | u < |P.contrast x|} = E by rfl]
  rw [le_div_iff₀ hu]
  simpa [mul_comm] using hmul_le

-- @node: disagreement_measure_le_margin_plus_regret_over_u
/-- The margin/large-contrast decomposition used in `thm:margin-localization`:
up to the zero-effect null part,
`D_π ⊆ {0<|τ|≤u} ∪ (D_π ∩ {|τ|>u})`, hence
`P_X(D_π) ≤ C_m u^α + R_P(π)/u`. -/
lemma disagreement_measure_le_margin_plus_regret_over_u
    (P : ObservedLaw 𝒳) (policySet : Set (Policy 𝒳)) (Cm α u0 : ℝ)
    (hmargin : MarginTail P Cm α u0) (hze : ZeroEffectRegular P policySet)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P)
    (hπmeas : ∀ π ∈ policySet, Measurable π)
    (π : Policy 𝒳) (hπmem : π ∈ policySet)
    {u : ℝ} (hu : 0 < u) (hu_le : u ≤ u0) :
    P.PX.real (disagreementSet π (lawOptimalPolicy P))
      ≤ Cm * u ^ α + lawRegret P π / u := by
  letI : IsProbabilityMeasure P.PX := hwf.2.1
  let D : Set 𝒳 := disagreementSet π (lawOptimalPolicy P)
  let ZD : Set 𝒳 := {x | P.contrast x = 0 ∧ π x ≠ lawOptimalPolicy P x}
  let S : Set 𝒳 := {x | 0 < |P.contrast x| ∧ |P.contrast x| ≤ u}
  let B : Set 𝒳 := D ∩ {x | u < |P.contrast x|}
  have hZD_zero : P.PX.real ZD = 0 := by
    rcases hze with hzero | hzeroD
    · have hle : P.PX.real ZD ≤ P.PX.real {x | P.contrast x = 0} := by
        exact measureReal_mono (μ := P.PX) (by
          intro x hx
          exact hx.1) (measure_ne_top P.PX {x | P.contrast x = 0})
      have hle0 : P.PX.real ZD ≤ 0 := by
        simpa [hzero] using hle
      exact le_antisymm hle0 measureReal_nonneg
    · simpa [ZD] using hzeroD π hπmem
  have hsmall : P.PX.real S ≤ Cm * u ^ α := by
    exact hmargin.2.2.2 u hu hu_le
  have hbig : P.PX.real B ≤ lawRegret P π / u := by
    simpa [B, D] using
      regret_disagreement_large_contrast_le P π hwf hbdd (hπmeas π hπmem) hu
  have hsubset : D ⊆ ZD ∪ S ∪ B := by
    intro x hxD
    by_cases hτzero : P.contrast x = 0
    · left
      left
      exact ⟨hτzero, by simpa [D, disagreementSet] using hxD⟩
    · by_cases hsmallContrast : |P.contrast x| ≤ u
      · left
        right
        exact ⟨abs_pos.mpr hτzero, hsmallContrast⟩
      · right
        exact ⟨hxD, lt_of_not_ge hsmallContrast⟩
  calc
    P.PX.real (disagreementSet π (lawOptimalPolicy P)) = P.PX.real D := rfl
    _ ≤ P.PX.real (ZD ∪ S ∪ B) :=
        measureReal_mono (μ := P.PX) hsubset (measure_ne_top P.PX (ZD ∪ S ∪ B))
    _ ≤ P.PX.real (ZD ∪ S) + P.PX.real B := measureReal_union_le _ _
    _ ≤ (P.PX.real ZD + P.PX.real S) + P.PX.real B := by
        have h := measureReal_union_le (μ := P.PX) ZD S
        linarith
    _ = P.PX.real S + P.PX.real B := by
        rw [hZD_zero]
        ring
    _ ≤ Cm * u ^ α + lawRegret P π / u := add_le_add hsmall hbig

-- @node: thm:margin-localization
/-- `thm:margin-localization`. Under the margin and zero-effect conditions,
disagreement mass is controlled by regret at the fast exponent `α/(1+α)`:
`P_X(D_π) ≤ C R_P(π)^{α/(1+α)}` for every `π ∈ policySet`.

The displayed paper statement names only `ass:margin` and `ass:zero-effect`;
`hwf : WellFormedLaw P` and `hbdd : BoundedOutcome P` are the paper's GLOBAL STANDING
setup conditions of the observed law (`ass:bounded-outcome` plus the well-formedness
`τ = μ₁-μ₀`), carried here as per-theorem hypotheses. They are pure bookkeeping —
together they bound the contrast `τ ∈ [-2,2]` (`WellFormedLaw` ties `τ = μ₁-μ₀`,
`BoundedOutcome` bounds `μ₀,μ₁ ∈ [-1,1]`) so the welfare/regret Bochner integrals
invoked through `thm:welfare-identity` are genuine (a non-integrable contrast would
collapse `R_P(π)` to the junk value `0` while `P_X(D_π) > 0`, falsifying the bound),
and carry no rate/separation content. Per the route "do not rely on an ambient
hidden prerequisite", they are stated explicitly rather than assumed silently. -/
theorem margin_localization
    (Cm α u0 : ℝ) :
    -- UNIFORM constant `C = C(C_m,u_0,α)`: the `∃ C` is hoisted ABOVE `∀ P` so the
    -- constant depends only on the margin parameters, not on the specific law (the
    -- `.tex` states "there is C=C(C_m,u_0,α) such that for every π …"); a per-law
    -- `∃ C(P)` inside `∀ P` would be a strictly weaker claim.
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : ObservedLaw 𝒳) (policySet : Set (Policy 𝒳)),
        MarginTail P Cm α u0 → ZeroEffectRegular P policySet →
        WellFormedLaw P → BoundedOutcome P → (∀ π ∈ policySet, Measurable π) →
          ∀ π ∈ policySet,
            P.PX.real (disagreementSet π (lawOptimalPolicy P))
              ≤ C * (lawRegret P π) ^ (α / (1 + α))
    := by
  classical
  let C : ℝ := |Cm| + 2 + if 0 < u0 then u0 ^ (-α) else 0
  refine ⟨C, ?_, ?_⟩
  · have htail_nonneg : 0 ≤ (if 0 < u0 then u0 ^ (-α) else 0) := by
      split_ifs with hu0
      · exact Real.rpow_nonneg hu0.le _
      · norm_num
    have hCmabs : 0 ≤ |Cm| := abs_nonneg Cm
    dsimp [C]
    nlinarith
  · intro P policySet hmargin hze hwf hbdd hπmeas π hπmem
    rcases hmargin with ⟨hαnonneg, hCmpos, hu0pos, _hmarginTail⟩
    letI : IsProbabilityMeasure P.PX := hwf.2.1
    let r : ℝ := lawRegret P π
    have hC_eq : C = |Cm| + 2 + u0 ^ (-α) := by
      simp [C, hu0pos]
    have hCge_small : Cm + 1 ≤ C := by
      rw [hC_eq, abs_of_pos hCmpos]
      have hpow_nonneg : 0 ≤ u0 ^ (-α) := Real.rpow_nonneg hu0pos.le _
      nlinarith
    have hCge_large : u0 ^ (-α) ≤ C := by
      rw [hC_eq]
      have hCmabs : 0 ≤ |Cm| := abs_nonneg Cm
      nlinarith
    have hreg_eq := regret_eq_disagreement_integral P π hwf hbdd (hπmeas π hπmem)
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      rw [hreg_eq]
      exact integral_nonneg (fun x =>
        mul_nonneg (abs_nonneg _) (by
          unfold disagreementIndicator
          split <;> norm_num))
    have hprobD :
        P.PX.real (disagreementSet π (lawOptimalPolicy P)) ≤ 1 := measureReal_le_one
    by_cases hαzero : α = 0
    · have hCge_one : 1 ≤ C := by
        rw [hC_eq, hαzero, abs_of_pos hCmpos]
        have hpow : u0 ^ (-(0 : ℝ)) = 1 := by simp
        rw [hpow]
        nlinarith
      calc
        P.PX.real (disagreementSet π (lawOptimalPolicy P)) ≤ 1 := hprobD
        _ ≤ C * (lawRegret P π) ^ (α / (1 + α)) := by
          simpa [hαzero] using hCge_one
    · have hαpos : 0 < α := lt_of_le_of_ne hαnonneg (Ne.symm hαzero)
      by_cases hrpos : 0 < r
      · let u : ℝ := r ^ (1 / (1 + α))
        have hu_pos : 0 < u := Real.rpow_pos_of_pos hrpos _
        by_cases hu_le : u ≤ u0
        · have hdecomp :
              P.PX.real (disagreementSet π (lawOptimalPolicy P))
                ≤ Cm * u ^ α + lawRegret P π / u :=
            disagreement_measure_le_margin_plus_regret_over_u P policySet Cm α u0
              ⟨hαnonneg, hCmpos, hu0pos, _hmarginTail⟩ hze hwf hbdd hπmeas
              π hπmem hu_pos hu_le
          have hupow :
              u ^ α = r ^ (α / (1 + α)) := by
            dsimp [u]
            rw [← Real.rpow_mul (le_of_lt hrpos)]
            congr 1
            ring
          have hdiv :
              lawRegret P π / u = r ^ (α / (1 + α)) := by
            dsimp [r, u]
            calc
              lawRegret P π / (lawRegret P π) ^ (1 / (1 + α))
                  = r / r ^ (1 / (1 + α)) := rfl
              _ = r ^ (α / (1 + α)) := by
                have hden : 1 + α ≠ 0 := by positivity
                calc
                  r / r ^ (1 / (1 + α))
                      = r ^ (1 : ℝ) / r ^ (1 / (1 + α)) := by rw [Real.rpow_one]
                  _ = r ^ ((1 : ℝ) - 1 / (1 + α)) := by rw [Real.rpow_sub hrpos]
                  _ = r ^ (α / (1 + α)) := by
                    congr 1
                    field_simp [hden]
                    ring
          have hmain :
              P.PX.real (disagreementSet π (lawOptimalPolicy P))
                ≤ (Cm + 1) * r ^ (α / (1 + α)) := by
            calc
              P.PX.real (disagreementSet π (lawOptimalPolicy P))
                  ≤ Cm * u ^ α + lawRegret P π / u := hdecomp
              _ = Cm * r ^ (α / (1 + α)) + r ^ (α / (1 + α)) := by
                rw [hupow, hdiv]
              _ = (Cm + 1) * r ^ (α / (1 + α)) := by ring
          have hpow_nonneg : 0 ≤ r ^ (α / (1 + α)) :=
            Real.rpow_nonneg hrpos.le _
          exact hmain.trans (mul_le_mul_of_nonneg_right hCge_small hpow_nonneg)
        · have hu0_lt : u0 < u := lt_of_not_ge hu_le
          have hpows : u0 ^ α ≤ r ^ (α / (1 + α)) := by
            calc
              u0 ^ α ≤ u ^ α := by
                exact Real.rpow_le_rpow hu0pos.le (le_of_lt hu0_lt) hαpos.le
              _ = r ^ (α / (1 + α)) := by
                dsimp [u]
                rw [← Real.rpow_mul (le_of_lt hrpos)]
                congr 1
                ring
          have hone_le :
              1 ≤ C * r ^ (α / (1 + α)) := by
            have hcoef_pos : 0 < u0 ^ (-α) := Real.rpow_pos_of_pos hu0pos _
            have hbase_nonneg : 0 ≤ r ^ (α / (1 + α)) :=
              Real.rpow_nonneg hrpos.le _
            have hone : (u0 ^ (-α)) * (u0 ^ α) = 1 := by
              rw [← Real.rpow_add hu0pos]
              ring_nf
              simp
            calc
              1 = (u0 ^ (-α)) * (u0 ^ α) := hone.symm
              _ ≤ (u0 ^ (-α)) * r ^ (α / (1 + α)) :=
                mul_le_mul_of_nonneg_left hpows hcoef_pos.le
              _ ≤ C * r ^ (α / (1 + α)) :=
                mul_le_mul_of_nonneg_right hCge_large hbase_nonneg
          exact hprobD.trans hone_le
      · have hr_eq : r = 0 := le_antisymm (le_of_not_gt hrpos) hr_nonneg
        have hD_le_zero :
            P.PX.real (disagreementSet π (lawOptimalPolicy P)) ≤ 0 := by
          refine le_of_forall_pos_le_add ?_
          intro ε hε
          let a : ℝ := ε / (Cm + 1)
          have hdenpos : 0 < Cm + 1 := by linarith
          have ha_pos : 0 < a := div_pos hε hdenpos
          let u : ℝ := min u0 (a ^ (1 / α))
          have hu_pos : 0 < u := by
            dsimp [u]
            exact lt_min hu0pos (Real.rpow_pos_of_pos ha_pos _)
          have hu_le : u ≤ u0 := by
            dsimp [u]
            exact min_le_left _ _
          have hu_le_a : u ≤ a ^ (1 / α) := by
            dsimp [u]
            exact min_le_right _ _
          have hdecomp :
              P.PX.real (disagreementSet π (lawOptimalPolicy P))
                ≤ Cm * u ^ α + lawRegret P π / u :=
            disagreement_measure_le_margin_plus_regret_over_u P policySet Cm α u0
              ⟨hαnonneg, hCmpos, hu0pos, _hmarginTail⟩ hze hwf hbdd hπmeas
              π hπmem hu_pos hu_le
          have hupow_le : u ^ α ≤ a := by
            have hpow_le : u ^ α ≤ (a ^ (1 / α)) ^ α :=
              Real.rpow_le_rpow hu_pos.le hu_le_a hαpos.le
            have ha_pow : (a ^ (1 / α)) ^ α = a := by
              rw [← Real.rpow_mul ha_pos.le (1 / α) α]
              have hmul : (1 / α) * α = (1 : ℝ) := by field_simp [hαpos.ne']
              rw [hmul, Real.rpow_one]
            exact hpow_le.trans_eq ha_pow
          have hCm_u_le : Cm * u ^ α ≤ Cm * a :=
            mul_le_mul_of_nonneg_left hupow_le hCmpos.le
          have hCm_a_le : Cm * a ≤ ε := by
            dsimp [a]
            field_simp [hdenpos.ne']
            nlinarith
          have hdiv_zero : lawRegret P π / u = 0 := by
            dsimp [r] at hr_eq
            rw [hr_eq]
            simp
          have hle_eps :
              Cm * u ^ α + lawRegret P π / u ≤ ε := by
            rw [hdiv_zero]
            linarith
          linarith
        have hD_zero :
            P.PX.real (disagreementSet π (lawOptimalPolicy P)) = 0 :=
          le_antisymm hD_le_zero measureReal_nonneg
        have hpow_zero :
            (lawRegret P π) ^ (α / (1 + α)) = 0 := by
          have h_exp_ne : α / (1 + α) ≠ 0 := by
            have hden : 1 + α ≠ 0 := by positivity
            exact div_ne_zero hαpos.ne' hden
          dsimp [r] at hr_eq
          rw [hr_eq]
          exact Real.zero_rpow h_exp_ne
        rw [hD_zero, hpow_zero]
        simp

-- @node: prop:overlap-envelope
/-- `prop:overlap-envelope`. At the tight window `v=h^β`, `u=h^{β/γ}`, the
envelope value equals `h^{(α+1)β/γ}`, admissibility `≥ h^α` is equivalent to
`β ≤ αγ/(α+1)=β_{α,γ}`, with equality at `β=β_{α,γ}`. Hence (final conjunct) a block
of mass `~h^α` with weak-arm exponent `β'` meets the `ass:overlap-decay` envelope iff
`β' ≤ β_{α,γ}`, so `β_{α,γ} ≥ 0` is the LEAST INFORMATIVE (largest) admissible
weak-arm exponent. -/
lemma overlap_envelope (α γ h β : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hh0 : 0 < h) (hh1 : h < 1) (_hβ : 0 ≤ β) :
    (h ^ (β / γ)) ^ α * (h ^ β) ^ (1 / γ) = h ^ ((α + 1) * β / γ) ∧
      ((h ^ (β / γ)) ^ α * (h ^ β) ^ (1 / γ) ≥ h ^ α ↔ β ≤ betaAG α γ) ∧
      (β = betaAG α γ →
        (h ^ (β / γ)) ^ α * (h ^ β) ^ (1 / γ) = h ^ α) ∧
      (0 ≤ betaAG α γ ∧
        ∀ β' : ℝ, 0 ≤ β' →
          ((h ^ (β' / γ)) ^ α * (h ^ β') ^ (1 / γ) ≥ h ^ α ↔ β' ≤ betaAG α γ)) := by
  have hpow : ∀ b : ℝ,
      (h ^ (b / γ)) ^ α * (h ^ b) ^ (1 / γ) = h ^ ((α + 1) * b / γ) := by
    intro b
    rw [← Real.rpow_mul (le_of_lt hh0), ← Real.rpow_mul (le_of_lt hh0)]
    rw [← Real.rpow_add hh0]
    congr 1
    field_simp [ne_of_gt hγ]
  have halg : ∀ b : ℝ,
      (h ^ ((α + 1) * b / γ) ≥ h ^ α ↔ b ≤ betaAG α γ) := by
    intro b
    rw [ge_iff_le]
    rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hh0 hh1]
    simp [betaAG, ne_of_gt hγ]
    have hα1 : 0 < α + 1 := by linarith
    constructor
    · intro hle
      calc b = ((α + 1) * b / γ) * γ / (α + 1) := by
            field_simp [ne_of_gt hγ, ne_of_gt hα1]
        _ ≤ α * γ / (α + 1) := by gcongr
    · intro hle
      calc ((α + 1) * b / γ) ≤ ((α + 1) * (α * γ / (α + 1)) / γ) := by
            gcongr
        _ = α := by field_simp [ne_of_gt hγ, ne_of_gt hα1]
  refine ⟨hpow β, ?_, ?_, ?_⟩
  · rw [hpow β]
    exact halg β
  · intro hb
    rw [hpow β, hb]
    have hα1 : 0 < α + 1 := by linarith
    have hcalc : ((α + 1) * (α * γ / (α + 1)) / γ) = α := by
      field_simp [ne_of_gt hγ, ne_of_gt hα1]
    simp [betaAG, ne_of_gt hγ, hcalc]
  · constructor
    · simp [betaAG, ne_of_gt hγ]
      positivity
    · intro β' hβ'
      rw [hpow β']
      exact halg β'

end CausalSmith.Stat.PolicyRegretMarginOverlap
