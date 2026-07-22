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

/-- Deterministic binary policy `X → {0,1}`. -/
abbrev Policy (𝒳 : Type*) := 𝒳 → Bool

/-- Real indicator of a Boolean. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- Observation `O=(X,A,Y) ∈ 𝒳 × {0,1} × [-1,1]`. -/
structure Observation (𝒳 : Type*) where
  X : 𝒳
  A : ℝ
  Y : ℝ

instance instMeasurableSpaceObservation : MeasurableSpace (Observation 𝒳) :=
  MeasurableSpace.comap (fun O : Observation 𝒳 => (O.X, O.A, O.Y)) inferInstance

/-- Optimal policy `π_⋆(x)=1{τ(x) ≥ 0}`. -/
noncomputable def optimalPolicy (τ : 𝒳 → ℝ) : Policy 𝒳 :=
  fun x => if 0 ≤ τ x then true else false

-- @node: def:disagreement
/-- Disagreement set `D_π = {x : π(x) ≠ π_⋆(x)}`. -/
def disagreementSet (π πstar : Policy 𝒳) : Set 𝒳 :=
  {x | π x ≠ πstar x}

/-- Real indicator of disagreement. -/
def disagreementIndicator (π πstar : Policy 𝒳) (x : 𝒳) : ℝ :=
  if π x ≠ πstar x then 1 else 0

/-- Welfare `V_P(π)=E_P[π(X) τ(X)]`. -/
noncomputable def welfare (PX : Measure 𝒳) (τ : 𝒳 → ℝ) (π : Policy 𝒳) : ℝ :=
  ∫ x, boolIndicator (π x) * τ x ∂PX

-- @node: def:welfare-regret
/-- Welfare regret `R_P(π)=V_P(π_⋆)-V_P(π)`, with `π_⋆=optimalPolicy τ`. -/
noncomputable def regret (PX : Measure 𝒳) (τ : 𝒳 → ℝ) (π : Policy 𝒳) : ℝ :=
  welfare PX τ (optimalPolicy τ) - welfare PX τ π

/-- Build-inline observed-law object: the covariate marginal, the per-draw
observation law, and the law-side nuisance functionals the statements range
over. -/
structure ObservedLaw (𝒳 : Type*) [MeasurableSpace 𝒳] where
  dataMeasure : Measure (Observation 𝒳)
  PX : Measure 𝒳
  contrast : 𝒳 → ℝ
  propensity : 𝒳 → ℝ
  mu0 : 𝒳 → ℝ
  mu1 : 𝒳 → ℝ

/-- Overlap `p_P(x)=min(e_P(x),1-e_P(x))`. -/
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
treatment arms `a ∈ {0,1}`. In the observed-law substrate the arm-`a` outcome is
seen on the event `{A = a}`, so this is the conjunction of the two arm-conditional
support bounds (`a = 1` and `a = 0`) under the data law. -/
def BoundedOutcome (P : ObservedLaw 𝒳) : Prop :=
  (∀ᵐ O ∂P.dataMeasure, O.A = 1 → |O.Y| ≤ 1) ∧
    (∀ᵐ O ∂P.dataMeasure, O.A = 0 → |O.Y| ≤ 1)

-- @node: ass:positivity
/-- A3 positivity: `0 < e_P(X) < 1` holds `P_X`-a.s. -/
def Positivity (P : ObservedLaw 𝒳) : Prop :=
  ∀ᵐ x ∂P.PX, 0 < P.propensity x ∧ P.propensity x < 1

-- @node: ass:margin
/-- A4 Tsybakov margin: `P(0<|τ|≤u) ≤ C_m u^α` for `0 < u ≤ u_0`. -/
def MarginTail (P : ObservedLaw 𝒳) (Cm α u0 : ℝ) : Prop :=
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
(with `v^{1/γ}=1` when `γ=0`). -/
def OverlapDecay (P : ObservedLaw 𝒳) (Co co α γ : ℝ) : Prop :=
  ∀ u v : ℝ, 0 < u → 0 < v → v ≤ co * u ^ γ →
    P.PX.real {x | overlap P x ≤ v ∧ 0 < |P.contrast x| ∧ |P.contrast x| ≤ u}
      ≤ Co * u ^ α * (if γ = 0 then 1 else v ^ (1 / γ))

-- @node: ass:policy-class
/-- A7 pointwise measurable finite-VC policy class with a countable
pointwise-dense skeleton `Π₀` and polynomial (Sauer–Shelah) trace growth at
VC-dimension `d_Π`. -/
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
/-- A10 cross-fit L²(P) nuisance rates with product rate `O(n^{-1/2})`. -/
def NuisanceRate (P : ObservedLaw 𝒳)
    (muHat0 muHat1 eHat : ℕ → 𝒳 → ℝ) (rMu rE : ℕ → ℝ) : Prop :=
  (∀ n, ∫ x, (muHat0 n x - P.mu0 x) ^ 2 ∂P.PX ≤ (rMu n) ^ 2) ∧
  (∀ n, ∫ x, (muHat1 n x - P.mu1 x) ^ 2 ∂P.PX ≤ (rMu n) ^ 2) ∧
  (∀ n, ∫ x, (eHat n x - P.propensity x) ^ 2 ∂P.PX ≤ (rE n) ^ 2) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, rMu n * rE n ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)))

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

-- (statement Prop discharged by the reuse-lemma `vc_localized_envelope`,
--  tagged `-- @node: ass:vc-localized-envelope`, in `Helpers.lean`.)
/-- A15 localized finite-VC fixed-radius empirical-process envelope: every
centered policy-indexed process with envelope `B` and localized conditional
second moment has fixed-radius supremum bounded by
`C B n^{-1/2} r^{α/(2+2α)} (log n)^p`. -/
def VCLocalizedEnvelope (PX : Measure 𝒳) (τ : 𝒳 → ℝ)
    (policySet : Set (Policy 𝒳)) (α : ℝ) : Prop :=
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ (n : ℕ) (B r : ℝ) (proc sndMom : Policy 𝒳 → ℝ),
      0 < n → 0 ≤ B → 0 ≤ r →
      (∀ π ∈ policySet, |proc π| ≤ B) →
      (∀ π ∈ policySet,
        sndMom π ≤ C * B ^ 2 * PX.real (disagreementSet π (optimalPolicy τ))) →
      sSup ((fun π => |proc π|) '' {π | π ∈ policySet ∧ regret PX τ π ≤ r})
        ≤ C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) * r ^ (α / (2 + 2 * α))
            * (Real.log n) ^ p

-- (statement Prop discharged by the reuse-lemma `vc_localized_offset_envelope`,
--  tagged `-- @node: ass:vc-localized-offset-envelope`, in `Helpers.lean`.)
/-- A16 localized finite-VC offset/Rademacher bound: the offset positive part
`E sup_π {2|z_π| - R_P(π)/4}_+` is bounded by `C (B²/n)^{A_α}(log n)^p`,
`A_α=(1+α)/(2+α)`. -/
def VCLocalizedOffsetEnvelope (PX : Measure 𝒳) (τ : 𝒳 → ℝ)
    (policySet : Set (Policy 𝒳)) (α : ℝ) : Prop :=
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ (n : ℕ) (B : ℝ) (proc sndMom : Policy 𝒳 → ℝ),
      0 < n → 0 ≤ B →
      (∀ π ∈ policySet, |proc π| ≤ B) →
      (∀ π ∈ policySet,
        sndMom π ≤ C * B ^ 2 * PX.real (disagreementSet π (optimalPolicy τ))) →
      sSup ((fun π => max 0 (2 * |proc π| - regret PX τ π / 4)) '' policySet)
        ≤ C * (B ^ 2 / (n : ℝ)) ^ ((1 + α) / (2 + α)) * (Real.log n) ^ p

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

/-- Packaged feasible-rate data: the maximizer exponents `(s_feas, t_feas)`, the
SELECTED clip/window schedules `q_n, u_n` (with the `γ=0` fixed-clip branch baked
into `qSched`), and the solved upper exponent `r_feas`. -/
structure FeasibleRate where
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

-- @node: def:feasible-rate
/-- Feasible-rate construction. The clip/window exponents `(s_feas, t_feas)`
maximize `φ` on the compact box; the packaged schedules `q_n = qSched`,
`u_n = uSched` bake in the `γ=0` fixed-clip branch (`q_n = q_0`); they satisfy the
eventual admissibility `q_n ≤ c_o u_n^γ` (`feasibleAdmissible`); and
`r = r_feas = min{r_⋆, g_joint}` for `γ>0`, `min{A_α, c}` for `γ=0`. -/
noncomputable def feasibleRate (α γ a c q0 uBar : ℝ) : FeasibleRate where
  s := sFeas α γ a c
  t := tFeas α γ a c
  r := if γ = 0 then min (Aalpha α) c else min (rStar α γ) (gJoint α γ a c)
  q := qSched α γ a c q0
  u := uSched α γ a c uBar

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
    + (O.A / clippedPropensity q e O.X) * (O.Y - mu1 O.X)
    - ((1 - O.A) / (1 - clippedPropensity q e O.X)) * (O.Y - mu0 O.X)

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
  bdd : BoundedOutcome P
  pos : Positivity P
  margin : MarginTail P Cm α u0
  zero : ZeroEffectRegular P policySet
  overlapDecay : OverlapDecay P Co co α γ
  strict : StrictOverlapEndpoint P γ underlineP

-- @node: def:upper-risk
/-- Regime-indexed conditional feasible upper risk
`U_n(α,γ,a,c; η̂) = sup_P E_P R_P(π̂_n)`. The estimator is the feasible cross-fit
clipped-AIPW ERM `feasibleERM` run with the SELECTED schedule clip
`q_n = qSched α γ a c q0 n` and the supplied foldwise cross-fitted nuisances
`η̂` (`n`-indexed, fold-indexed); the supremum ranges over the bundled
side-condition domain: `P ∈ LawClass` with `OptimalInClass`, the finite-VC
`PolicyClassVC`, the fixed regime `PolynomialNuisanceExponents` at the exponents
`(a,c)`, each foldwise nuisance estimate obeying `NuisanceRate` and
`BoundedCrossfitNuisances`, and the deterministic fold family obeying
`FixedFoldCount`. -/
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
         PolicyClassVC policySet dPi ∧
         PolynomialNuisanceExponents rMu rE a c CMu CProd ∧
         FixedFoldCount K assign ∧
         (∀ k : Fin K,
           NuisanceRate P (fun m => muHat0 m k) (fun m => muHat1 m k)
             (fun m => eHat m k) rMu rE) ∧
         (∀ k : Fin K,
           BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k))})

/-! ## Shared foundational results -/

-- @node: thm:welfare-identity
/-- `thm:welfare-identity`. Under bounded outcomes, regret equals the
`|τ|`-weighted disagreement mass. -/
theorem regret_eq_disagreement_integral
    (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hbdd : BoundedOutcome P) :
    lawRegret P π =
      ∫ x, |P.contrast x| * disagreementIndicator π (lawOptimalPolicy P) x ∂P.PX := by
  sorry

-- @node: thm:margin-localization
/-- `thm:margin-localization`. Under the margin and zero-effect conditions,
disagreement mass is controlled by regret at the fast exponent `α/(1+α)`. -/
theorem margin_localization
    (P : ObservedLaw 𝒳) (policySet : Set (Policy 𝒳))
    (Cm α u0 : ℝ)
    (hmargin : MarginTail P Cm α u0) (hzero : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P) :
    ∃ C : ℝ, 0 < C ∧ ∀ π ∈ policySet,
      P.PX.real (disagreementSet π (lawOptimalPolicy P))
        ≤ C * (lawRegret P π) ^ (α / (1 + α)) := by
  sorry

-- @node: prop:overlap-envelope
/-- `prop:overlap-envelope`. At the tight window `v=h^β`, `u=h^{β/γ}`, the
envelope value equals `h^{(α+1)β/γ}`, and admissibility `≥ h^α` is equivalent
to `β ≤ αγ/(α+1)=β_{α,γ}`. -/
lemma overlap_envelope (α γ h β : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hh0 : 0 < h) (hh1 : h < 1) (hβ : 0 ≤ β) :
    (h ^ (β / γ)) ^ α * (h ^ β) ^ (1 / γ) = h ^ ((α + 1) * β / γ) ∧
      ((h ^ (β / γ)) ^ α * (h ^ β) ^ (1 / γ) ≥ h ^ α ↔ β ≤ α * γ / (α + 1)) ∧
      (β = α * γ / (α + 1) →
        (h ^ (β / γ)) ^ α * (h ^ β) ^ (1 / γ) = h ^ α) ∧
      (β = betaAG α γ →
        (h ^ (β / γ)) ^ α * (h ^ β) ^ (1 / γ) = h ^ α) := by
  sorry

end CausalSmith.Stat.PolicyRegretMarginOverlap
