/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP pointwise CATE minimax: a two-point / TV-contraction proof-method barrier — shared core

Stage-2 scaffold for `stat_dp_cate_minimax_v1` (specialization
`holder_central_dp`).

**Headline scope (faithfulness).** This development proves a subfield-tier
PROOF-METHOD hardness result, NOT a sharp/matching minimax frontier. The headline
`thm:causal_dp_two_point_barrier` is a two-point / TV-contraction proof-method
OBSTRUCTION (never an impossibility claim, never a minimax converse). The
two-sided bracket `certified_private_cate_bracket` is NON-matching in general and
sharp only at `beta = gamma`; that `beta = gamma` sharp rate is INHERITED from
private pointwise regression, not a new causal exponent. The full-frontier
question is left as the non-theorem `CausalDpFrontierQuestion` Prop `def` on which
NO theorem depends.

This file carries the shared environment S-blocks (the i.i.d. observational CATE
sampling world `CateObs`/`CateLaw` with its potential-outcome overlay, the central
approximate-DP release overlay, and the regime constants + Hölder classes), the
assumption-atom `def`s, the model-class structure `HolderCateClass`, the
construction `def`s (`dpMinimaxRisk`, `nonprivateCateRate`,
`privateRegressionCalibration`, `causalPrivateFrontierHandle`), and the open-ended
`CausalDpFrontierQuestion`. Each emitted declaration carries its own node tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Stat.Sample.IIDSample` | reuse (in `IidSampling`) | the i.i.d. sampling content of `ass:iid`. |
| `Causalean.PO.*` (`POSystem`, `Consistency`, `CondIndepCF`) | bypass-justified | graph/regime-indexed PO skeleton heavier than the scalar CATE overlay; consistency + exchangeability kept as threaded `Prop`s on the constructed law (same call as sibling `DoseResponseMinimax`). |
| `CausalSmith.Stat.DoseResponseMinimax.HolderBallND` | bypass-justified (NOT reused) | its `⌊order⌋` convention gives a `0`-exponent condition at integer smoothness, disagreeing with this core's standard `⌈s⌉-1` convention; `HolderBallStd` is define-local. |
| `Causalean.Stat.Minimax.TotalVariation` / `ChiSquared` | reuse target (Helpers) | `tvDist`, `one_sub_tvDist_le_test`, `chiSqDiv`, `tvDist_le_half_sqrt_chiSqDiv`. No DP substrate exists anywhere; the DP overlay/contraction/Laplace release are build-inline. |

No new typeclasses are introduced.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Causalean.Stat.Sample
import Causalean.Stat.Minimax.TotalVariation

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat
open scoped BigOperators ENNReal

/-! ## Environment S1 — i.i.d. observational CATE sampling world -/

-- @env: S1
/-- Observed unit `O = (Y, A, X)` with outcome `Y ∈ [-1,1]`, binary treatment
`A ∈ {0,1}`, and covariate vector `X ∈ [0,1]^d`. The carrier fields are typed over
`ℝ` / `Fin d → ℝ`; the declared ranges `Y ∈ [-1,1]`, `A ∈ {0,1}`, `X ∈ [0,1]^d`
are pinned as standing a.s.-support clauses on the law by the three `IidSampling`
support conjuncts, which every law in `HolderCateClass` carries.
@realizes O(carrier ℝ×ℝ×(Fin d→ℝ); declared joint space {(Y,A,X): Y∈[-1,1], A∈{0,1}, X∈[0,1]^d} — its coordinate ranges are pinned a.s. by the per-coordinate `@realizes Y/A/X` `IidSampling` support conjuncts) -/
structure CateObs (d : ℕ) where
  Y : ℝ                -- @realizes Y(carrier ℝ; range [-1,1] pinned a.s. by the IidSampling Y-support conjunct)
  A : ℝ                -- @realizes A(carrier ℝ; range {0,1} pinned a.s. by the IidSampling A-support conjunct)
  X : Fin d → ℝ        -- @realizes X(carrier Fin d→ℝ; range [0,1]^d pinned a.s. by the IidSampling X-support conjunct)

/-- The observed-data type is measurable via its outcome/treatment/covariate tuple. -/
instance instMeasurableSpaceCateObs {d : ℕ} : MeasurableSpace (CateObs d) :=
  MeasurableSpace.comap (fun O : CateObs d => (O.Y, O.A, O.X)) inferInstance

@[fun_prop, measurability]
lemma measurable_CateObs_Y {d : ℕ} : Measurable (fun O : CateObs d => O.Y) := by
  simpa [Function.comp_def] using
    (measurable_fst.comp
      (comap_measurable (fun O : CateObs d => (O.Y, O.A, O.X))))

@[fun_prop, measurability]
lemma measurable_CateObs_A {d : ℕ} : Measurable (fun O : CateObs d => O.A) := by
  simpa [Function.comp_def] using
    (measurable_fst.comp (measurable_snd.comp
      (comap_measurable (fun O : CateObs d => (O.Y, O.A, O.X)))))

@[fun_prop, measurability]
lemma measurable_CateObs_X {d : ℕ} : Measurable (fun O : CateObs d => O.X) := by
  simpa [Function.comp_def] using
    (measurable_snd.comp (measurable_snd.comp
      (comap_measurable (fun O : CateObs d => (O.Y, O.A, O.X)))))

/-- **Latent full record** `U = (Y(0), Y(1), A, X)`: BOTH potential outcomes, the
treatment, and the covariates, on the law's OWN probability space. The potential
outcomes are LATENT random variables — never functions of the observed record —
so exactly one of them is ever revealed (the fundamental problem of causal
inference). The observed record is DERIVED from `U` by the consistency map
`CateFull.toObs` below.
@realizes Y(0), Y(1)(the latent potential-outcome pair, random variables on the law's own space) @realizes A(the realized treatment) @realizes X(the covariates) -/
structure CateFull (d : ℕ) where
  Y0 : ℝ               -- @realizes Y(0)(carrier ℝ; range [-1,1] pinned a.s. by PotentialOutcomeRange)
  Y1 : ℝ               -- @realizes Y(1)(carrier ℝ; range [-1,1] pinned a.s. by PotentialOutcomeRange)
  A : ℝ                -- @realizes A(carrier ℝ; range {0,1} pinned a.s. on the observed law)
  X : Fin d → ℝ        -- @realizes X(carrier Fin d→ℝ)

/-- The latent full-record type is measurable via its `(Y(0), Y(1), A, X)` tuple. -/
instance instMeasurableSpaceCateFull {d : ℕ} : MeasurableSpace (CateFull d) :=
  MeasurableSpace.comap (fun U : CateFull d => (U.Y0, U.Y1, U.A, U.X)) inferInstance

@[fun_prop, measurability]
lemma measurable_CateFull_Y0 {d : ℕ} : Measurable (fun U : CateFull d => U.Y0) := by
  simpa [Function.comp_def] using
    (measurable_fst.comp
      (comap_measurable (fun U : CateFull d => (U.Y0, U.Y1, U.A, U.X))))

@[fun_prop, measurability]
lemma measurable_CateFull_Y1 {d : ℕ} : Measurable (fun U : CateFull d => U.Y1) := by
  simpa [Function.comp_def] using
    (measurable_fst.comp (measurable_snd.comp
      (comap_measurable (fun U : CateFull d => (U.Y0, U.Y1, U.A, U.X)))))

@[fun_prop, measurability]
lemma measurable_CateFull_A {d : ℕ} : Measurable (fun U : CateFull d => U.A) := by
  simpa [Function.comp_def] using
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (comap_measurable (fun U : CateFull d => (U.Y0, U.Y1, U.A, U.X))))))

@[fun_prop, measurability]
lemma measurable_CateFull_X {d : ℕ} : Measurable (fun U : CateFull d => U.X) := by
  simpa [Function.comp_def] using
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (comap_measurable (fun U : CateFull d => (U.Y0, U.Y1, U.A, U.X))))))

/-- **The consistency map** `U = (Y(0), Y(1), A, X) ↦ (Y(A), A, X)`: the observed
outcome is the potential outcome AT THE REALIZED ARM. This is the Lean encoding of
`Y = Y(A)`; the observed data law is the image of the latent joint law under this
map (see `Consistency`).
@realizes Y(the observed outcome Y = Y(A), the potential outcome at the realized arm) -/
noncomputable def CateFull.toObs {d : ℕ} (U : CateFull d) : CateObs d :=
  open Classical in
  ⟨if U.A = 1 then U.Y1 else U.Y0, U.A, U.X⟩

@[fun_prop, measurability]
lemma measurable_CateFull_toObs {d : ℕ} :
    Measurable (CateFull.toObs (d := d)) := by
  rw [measurable_comap_iff]
  change Measurable fun U : CateFull d =>
    ((if U.A = 1 then U.Y1 else U.Y0), U.A, U.X)
  exact ((Measurable.ite
      (measurableSet_eq_fun measurable_CateFull_A measurable_const)
      measurable_CateFull_Y1 measurable_CateFull_Y0)).prodMk
    (measurable_CateFull_A.prodMk measurable_CateFull_X)

/-- The covariate cube `[0,1]^d`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The sup-norm `r`-neighborhood of `x₀` inside `(Fin d → ℝ)`. -/
def supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i - x0 i| ≤ r}

/-- The half-min localization radius
`r_* = (1/2) min{r₀, x_{0,1}, 1-x_{0,1}, …, x_{0,d}, 1-x_{0,d}}` used in the
two-point / interpolation constructions. -/
noncomputable def rStar {d : ℕ} (r0 : ℝ) (x0 : Fin d → ℝ) : ℝ :=
  (1 / 2) * min r0 (⨅ i : Fin d, min (x0 i) (1 - x0 i))

/-- Standard-convention multivariate Hölder ball of order `order` and radius `M`
on `S ⊆ (Fin d → ℝ)`: all iterated Fréchet derivatives up to `k = ⌈order⌉ - 1`
exist and are continuous on `S` (`ContDiffOn`), are bounded by `M` in operator
norm, and the `k`-th derivative is
`(order - k)`-Hölder with constant `M` (the standard nonparametric
`C^{⌈order⌉-1, order-⌈order⌉+1}` ball, exponent `order - k ∈ (0,1]`). This is the
standard `⌈s⌉-1` convention; it is NOT the `⌊order⌋` convention of
`DoseResponseMinimax.HolderBallND`.
@realizes H^s([0,1]^d,L)(the standard `⌈s⌉-1`-convention multivariate Hölder ball of order `order` and radius `M` on `S ⊆ (Fin d → ℝ)`; the sets `H^α`, `H^β`, `H^γ` are its instances `PiHolder`/`MuHolder`/`TauHolder` on `cube d`) -/
def HolderBallStd {d : ℕ} (f : (Fin d → ℝ) → ℝ) (order M : ℝ)
    (S : Set (Fin d → ℝ)) : Prop :=
  ContDiffOn ℝ (⌈order⌉₊ - 1) f S ∧
    (∀ j : ℕ, j ≤ ⌈order⌉₊ - 1 → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (⌈order⌉₊ - 1) f x - iteratedFDeriv ℝ (⌈order⌉₊ - 1) f y‖
        ≤ M * ‖x - y‖ ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)))

/-- Build-inline causal-law object: the LATENT joint law of `(Y(0), Y(1), A, X)`
(the potential-outcome process, carried on the law's own probability space), the
per-draw OBSERVED law of `O = (Y, A, X)` — which `Consistency` pins to be the image
of the latent law under `Y = Y(A)` — the covariate marginal, and the law-side
nuisances `π_P, μ_{0,P}, μ_{1,P}, p_P`.

**Potential outcomes are LATENT.** `fullMeasure` is a law on `CateFull d`, NOT a
function of the observed record: the counterfactual `Y(1-A)` is never recoverable
from `O`. The observed law is DERIVED from it (`Consistency`), which is exactly the
potential-outcome framework. -/
structure CateLaw (d : ℕ) where
  fullMeasure : Measure (CateFull d)  -- @realizes Y(a)(the LATENT joint law of the potential-outcome pair (Y(0),Y(1)) together with (A,X), on the law's own probability space; its a.s. range [-1,1] for a∈{0,1} is pinned by PotentialOutcomeRange) @realizes a(treatment level a∈{0,1} indexing the potential outcome Y(a) — the `Y0`/`Y1` coordinates of `CateFull` — and the arm regressions μ_{a,P})
  dataMeasure : Measure (CateObs d)   -- @realizes P(the single-observation OBSERVED data law of O=(Y,A,X); pinned by `Consistency` to be the pushforward of `fullMeasure` under Y=Y(A); the i.i.d. n-sample O_1,…,O_n is the n-fold product of this law, carried by IidSampling + dpMinimaxRisk)
  PX : Measure (Fin d → ℝ)            -- @realizes P_X(marginal law of X induced by P)
  pi : (Fin d → ℝ) → ℝ                -- @realizes pi_P(carrier [0,1]^d→ℝ; =P(A=1∣X=x), range [0,1] pinned by StrongOverlap and tied to the law by PiIsPropensity)
  mu0 : (Fin d → ℝ) → ℝ               -- @realizes mu_{0,P}(carrier [0,1]^d→ℝ; =E[Y∣A=0,X=x], tied to the law by MuIsRegression)
  mu1 : (Fin d → ℝ) → ℝ               -- @realizes mu_{1,P}(carrier [0,1]^d→ℝ; =E[Y∣A=1,X=x], tied to the law by MuIsRegression)
  px : (Fin d → ℝ) → ℝ                -- @realizes p_P(carrier [0,1]^d→ℝ; density of P_X, tied to the law by PxIsXDensity, range [f_0,f_1] locally by LocalDensity)

/-- The CATE (contrast) function `τ_P = μ_{1,P} - μ_{0,P}`.
@realizes tau_P(τ_P(x) = μ_{1,P}(x) - μ_{0,P}(x); the causal target contrast) -/
def CateLaw.tau {d : ℕ} (P : CateLaw d) : (Fin d → ℝ) → ℝ :=
  fun x => P.mu1 x - P.mu0 x

/-! ## Assumption `def`s -/

-- @node: ass:iid
/-- `O_1, …, O_n ~ P^n`. Carries the full i.i.d. content by reusing
`Causalean.Stat.IIDSample` (mutually independent, identically distributed
measurable maps with law `P.dataMeasure`), `IsProbabilityMeasure P.dataMeasure`
(so the `n`-fold product `Measure.pi` is a probability measure), and the a.s.
support clauses `Y ∈ [-1,1]`, `A ∈ {0,1}`, `X ∈ [0,1]^d`. -/
def IidSampling {d : ℕ} (P : CateLaw d) : Prop :=
  IsProbabilityMeasure P.dataMeasure ∧
    (∀ᵐ O ∂P.dataMeasure, O.Y ∈ Set.Icc (-1 : ℝ) 1) ∧
      -- @realizes Y(a.s. outcome range Y ∈ [-1,1] under P — enforcing predicate pinning the carrier `CateObs.Y : ℝ` to [-1,1])
    (∀ᵐ O ∂P.dataMeasure, O.A ∈ ({0, 1} : Set ℝ)) ∧
      -- @realizes A(a.s. treatment range A ∈ {0,1} under P — enforcing predicate pinning the carrier `CateObs.A : ℝ` to {0,1})
    (∀ᵐ O ∂P.dataMeasure, O.X ∈ cube d) ∧
      -- @realizes X(a.s. covariate range X ∈ [0,1]^d under P — enforcing predicate pinning the carrier `CateObs.X : Fin d → ℝ` to the cube)
    -- @realizes O_1, ..., O_n(i.i.d. n-sample: mutually independent, identically `P.dataMeasure`-distributed measurable draws via `Causalean.Stat.IIDSample`; the n-fold product law `Measure.pi (fun _:Fin n => P.dataMeasure)` in `dpMinimaxRisk` is their joint law)
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : @MeasureTheory.Measure Ω _mΩ),
      Nonempty (@Causalean.Stat.IIDSample Ω (CateObs d) _mΩ
        instMeasurableSpaceCateObs μ P.dataMeasure)

-- @node: ass:consistency
/-- **Consistency** `Y = Y(A)`: the OBSERVED law is the image of the LATENT joint
potential-outcome law under the consistency map `(Y(0),Y(1),A,X) ↦ (Y(A),A,X)`
(`CateFull.toObs`), and the latent law is a probability law. Because the potential
outcomes are latent, `Y = Y(A)` is not an equation between two functions of the
observed record (which would make the counterfactual observable); it is exactly the
statement that the data one SEES is generated by revealing the arm-`A` potential
outcome. -/
def Consistency {d : ℕ} (P : CateLaw d) : Prop :=
  IsProbabilityMeasure P.fullMeasure ∧
    P.dataMeasure = P.fullMeasure.map CateFull.toObs

-- @node: ass:exchangeability
/-- JOINT conditional exchangeability `(Y(0), Y(1)) ⟂ A ∣ X` ON THE LATENT LAW,
encoded in the faithful tested form `E[f(Y(0),Y(1)) ∣ A, X] = E[f(Y(0),Y(1)) ∣ X]`
for every bounded measurable test `f` of the PAIR `(Y(0), Y(1))`. Testing the pair
(rather than each `Y(a)` separately) captures JOINT conditional independence of the
potential-outcome vector from `A` given `X`, not merely each coordinate's
conditional independence. The conditional expectations are taken under
`P.fullMeasure` — the law on which the potential outcomes actually live. -/
def CondExchangeability {d : ℕ} (P : CateLaw d) : Prop :=
  ∀ (f : ℝ × ℝ → ℝ), Measurable f → (∃ Mf : ℝ, ∀ p : ℝ × ℝ, |f p| ≤ Mf) →
    P.fullMeasure[(fun U => f (U.Y0, U.Y1)) |
        MeasurableSpace.comap (fun U : CateFull d => (U.A, U.X)) inferInstance]
      =ᵐ[P.fullMeasure]
    P.fullMeasure[(fun U => f (U.Y0, U.Y1)) |
        MeasurableSpace.comap (fun U : CateFull d => U.X) inferInstance]

-- @node: ass:overlap
/-- Strong overlap `e₀ ≤ π_P(x) ≤ 1 - e₀` for every `x ∈ [0,1]^d`.
@realizes e_0(overlap floor pinning π_P into `[e_0, 1-e_0] ⊆ (0,1)`) -/
def StrongOverlap {d : ℕ} (P : CateLaw d) (e0 : ℝ) : Prop :=
  ∀ x ∈ cube d, e0 ≤ P.pi x ∧ P.pi x ≤ 1 - e0

-- @node: ass:pi-holder
/-- Propensity smoothness `π_P ∈ H^α([0,1]^d, L)` in the standard `⌈α⌉-1`
Hölder-ball convention (`HolderBallStd`, NOT `HolderBallND`). -/
def PiHolder {d : ℕ} (P : CateLaw d) (alpha L : ℝ) : Prop :=
  HolderBallStd (fun x => P.pi x) alpha L (cube d)

-- @node: ass:mu-holder
/-- Outcome-regression smoothness `μ_{0,P}, μ_{1,P} ∈ H^β([0,1]^d, L)` in the
standard `⌈β⌉-1` Hölder-ball convention. -/
def MuHolder {d : ℕ} (P : CateLaw d) (beta L : ℝ) : Prop :=
  HolderBallStd (fun x => P.mu0 x) beta L (cube d) ∧
    HolderBallStd (fun x => P.mu1 x) beta L (cube d)

-- @node: ass:tau-holder
/-- CATE smoothness `τ_P = μ_{1,P} - μ_{0,P} ∈ H^γ([0,1]^d, L)` in the standard
`⌈γ⌉-1` Hölder-ball convention. -/
def TauHolder {d : ℕ} (P : CateLaw d) (gamma L : ℝ) : Prop :=
  HolderBallStd (fun x => P.mu1 x - P.mu0 x) gamma L (cube d)

-- @node: ass:smoothness-order
/-- CATE-at-least-outcome smoothness regime `0 < β ≤ γ`.
@realizes beta(0 < β lower endpoint) @realizes gamma(β ≤ γ regime tie) -/
def SmoothnessOrder (beta gamma : ℝ) : Prop :=
  0 < beta ∧ beta ≤ gamma

-- @node: ass:local-density
/-- Local design-density boundedness `f₀ ≤ p_P(x) ≤ f₁` for every `x` in the
sup-norm `r₀`-neighborhood of `x₀` INTERSECTED with the ambient cube `[0,1]^d`
(the paper quantifies only over `supBall x₀ r₀ ∩ [0,1]^d`, not every ambient point
satisfying the sup-norm bound).
@realizes f_0(lower local design-density bound) @realizes f_1(upper local design-density bound) @realizes r_0(design-regularity radius of the neighborhood of x_0) -/
def LocalDensity {d : ℕ} (P : CateLaw d) (f0 f1 r0 : ℝ) (x0 : Fin d → ℝ) : Prop :=
  ∀ x, x ∈ supBall x0 r0 → x ∈ cube d → f0 ≤ P.px x ∧ P.px x ≤ f1

/-! ### Semantic ties (definitional realization of the nuisance symbols)

The core symbols `μ_{a,P}(x) = E_P[Y∣A=a,X=x]`, `π_P(x) = P(A=1∣X=x)`, and
`p_P = dP_X/dLeb` are DEFINED as functionals of the law `P`. The three `def`s
below pin the free `CateLaw` fields to these definitions; they are the note's
stated MEANING of the nuisance symbols (encoding fidelity), not added
restrictions. Without them `τ_P = μ_{1,P} - μ_{0,P}` would be disconnected from
`dataMeasure`, and `thm:causal_dp_two_point_barrier`
(`TV(P,Q) ≥ c·|τ_P(x₀)-τ_Q(x₀)|^{1+d/γ}`) would be false (a Dirac data law with
the separation carried only by the free fields). They enter `HolderCateClass` so
that `dpMinimaxRisk` over it is the genuine causal risk. -/

/-- **Semantic tie (arm regressions).** `E[Y ∣ A,X]` equals the arm-selected
regression `μ_{A,P}(X)`, pinning `μ_{0,P}, μ_{1,P}` to the law.
@realizes mu_{0,P}(A=0 branch of E[Y∣A,X]=μ_{A,P}(X)) @realizes mu_{1,P}(A=1 branch of E[Y∣A,X]=μ_{A,P}(X)) -/
def MuIsRegression {d : ℕ} (P : CateLaw d) : Prop :=
  P.dataMeasure[(fun O => O.Y) |
      MeasurableSpace.comap (fun O : CateObs d => (O.A, O.X)) inferInstance]
    =ᵐ[P.dataMeasure] (fun O => if O.A = 1 then P.mu1 O.X else P.mu0 O.X)

/-- **Semantic tie (X-marginal density).** The pushforward of the data law under
`X` is `p_P·(Lebesgue ↾ [0,1]^d)`, pinning `p_P` to the covariate law.
@realizes p_P(P.map X = (Leb↾cube).withDensity (ofReal ∘ p_P); the density tie) -/
def PxIsXDensity {d : ℕ} (P : CateLaw d) : Prop :=
  P.dataMeasure.map (fun O => O.X)
    = (volume.restrict (cube d)).withDensity (fun x => ENNReal.ofReal (P.px x))

/-- **Semantic tie (propensity).** `E[1(A=1) ∣ X]` equals `π_P(X)`, pinning
`π_P` to the conditional treatment probability `P(A=1∣X)`.
@realizes pi_P(E[1(A=1)∣X]=π_P(X); the propensity tie) -/
def PiIsPropensity {d : ℕ} (P : CateLaw d) : Prop :=
  P.dataMeasure[(fun O => if O.A = 1 then (1 : ℝ) else 0) |
      MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance]
    =ᵐ[P.dataMeasure] (fun O => P.pi O.X)

/-- **Semantic tie (X-marginal).** The free covariate-marginal field `P_X` equals
the induced pushforward `P.dataMeasure.map (fun O => O.X)`, pinning `P_X` to the
`X`-marginal of the observation law (without this tie `P.PX` is a free measure
disconnected from the data law).
@realizes P_X(P.PX = P.dataMeasure.map (fun O => O.X); the induced X-marginal tie) -/
def PXIsXMarginal {d : ℕ} (P : CateLaw d) : Prop :=
  P.PX = P.dataMeasure.map (fun O => O.X)

/-- **Potential-outcome range invariant.** BOTH latent potential outcomes `Y(0)`
and `Y(1)` lie a.s. in `[-1,1]` under the latent joint law, pinning the range of the
potential-outcome pair at BOTH treatment levels (including the counterfactual arm,
which is never observed).
@realizes Y(a)(a.s. range `Y(a) ∈ [-1,1]` for a∈{0,1} under `P.fullMeasure` — enforcing predicate pinning the latent `CateFull.Y0`/`CateFull.Y1` carriers) @realizes a(the two treatment levels a∈{0,1} at which the potential-outcome range holds) -/
def PotentialOutcomeRange {d : ℕ} (P : CateLaw d) : Prop :=
  (∀ᵐ U ∂P.fullMeasure, U.Y0 ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ᵐ U ∂P.fullMeasure, U.Y1 ∈ Set.Icc (-1 : ℝ) 1)

-- @node: def:holder-cate-class
/-- The observational Hölder CATE model class
`P_{α,β,γ}(L,e₀,f₀,f₁,r₀,x₀)`: the bundle of the member-atom properties, plus the
three SEMANTIC TIES pinning `μ`, `p`, `π` to the law so that `dpMinimaxRisk` over
it is the genuine causal risk and `τ_P = μ_{1,P} - μ_{0,P}` is the true CATE. The
i.i.d.-sampling atom `ass:iid` is NOT a class field — it is threaded as an explicit
hypothesis where needed and realized internally by the `Measure.pi` product law in
`dpMinimaxRisk`. -/
structure HolderCateClass (d : ℕ) (alpha beta gamma L e0 f0 f1 r0 : ℝ)
    (x0 : Fin d → ℝ) (P : CateLaw d) : Prop where
  consistency : Consistency P
  exchangeability : CondExchangeability P
  overlap : StrongOverlap P e0
  piH : PiHolder P alpha L
  muH : MuHolder P beta L
  tauH : TauHolder P gamma L
  order : SmoothnessOrder beta gamma
  localDensity : LocalDensity P f0 f1 r0 x0
  muReg : MuIsRegression P
  pxDens : PxIsXDensity P
  pxMarginal : PXIsXMarginal P    -- @realizes P_X(pins the covariate-marginal field to the induced X-pushforward of the data law)
  piProp : PiIsPropensity P
  potRange : PotentialOutcomeRange P   -- @realizes Y(a)(a.s. potential-outcome range [-1,1] for both a∈{0,1})

-- @node: ass:model-nonempty
/-- Standard nonempty-minimax-model assumption: the Hölder CATE class is nonempty
AND its witness is a GENUINE i.i.d. probability law (`IidSampling P`), not merely a
finite/non-probability `dataMeasure` (supplies the retained covariate density for the
lower-bound two-point families). The `IidSampling P` conjunct pins the model member
to be an actual observational-data law, as the paper's nonempty model requires. -/
def ModelNonempty (d : ℕ) (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ) : Prop :=
  ∃ P : CateLaw d, HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P ∧ IidSampling P

/-! ## Environment S2 — central approximate-DP release overlay -/

-- @env: S2
/-- Two datasets are replacement-adjacent when they agree away from one coordinate. -/
def ReplacementAdjacent {ι Ω : Type} (D D' : ι → Ω) : Prop :=
  ∃ i : ι, ∀ j : ι, j ≠ i → D j = D' j

/-- The paper's declared observation sample space `[-1,1] × {0,1} × [0,1]^d`. -/
def sampleSpace (d : ℕ) : Set (CateObs d) :=
  {O | O.Y ∈ Set.Icc (-1 : ℝ) 1 ∧ O.A ∈ ({0, 1} : Set ℝ) ∧ O.X ∈ cube d}

lemma measurableSet_sampleSpace {d : ℕ} : MeasurableSet (sampleSpace d) := by
  have hcube : MeasurableSet (cube d) := by
    rw [show cube d = ⋂ i : Fin d, (fun x : Fin d → ℝ => x i) ⁻¹' Set.Icc 0 1 by
      ext x
      simp [cube]]
    exact MeasurableSet.iInter fun i =>
      measurableSet_Icc.preimage (measurable_pi_apply i)
  exact (measurableSet_Icc.preimage measurable_CateObs_Y).inter
    ((by measurability : MeasurableSet ({0, 1} : Set ℝ)).preimage measurable_CateObs_A |>.inter
      (hcube.preimage measurable_CateObs_X))

/-- A law satisfying the sampling assumption is a.s. supported on the declared sample space. -/
lemma iidSampling_ae_sampleSpace {d : ℕ} {P : CateLaw d} (h : IidSampling P) :
    P.dataMeasure (sampleSpace d)ᶜ = 0 := by
  rw [← mem_ae_iff]
  filter_upwards [h.2.1, h.2.2.1, h.2.2.2.1] with O hY hA hX
  exact ⟨hY, hA, hX⟩

-- @node: ass:central-dp
/-- Central approximate-`(ε_n, δ_n)`-differential privacy of a possibly randomized
mechanism `M_n : (Fin n → CateObs d) → Measure ℝ`, modeled as a genuine Markov
PROBABILITY kernel to Borel `ℝ` (an output-law mechanism): each `M D` is a
probability measure, `M` is measurable as a `Measure ℝ`-valued map (kernel
measurability), and for every pair of neighboring datasets `D, D'` (differing in
exactly one record) and every Borel output event `B`,
`Pr{M_n(D) ∈ B} ≤ exp(ε_n)·Pr{M_n(D') ∈ B} + δ_n`. The probability-measure and
measurability clauses ensure the bound quantifies over objects that DO define
output probability laws (a Markov kernel), not arbitrary non-probability
measure-valued functions. The privacy guarantee is required exactly on the paper's
declared observation sample space.
@realizes M_n(the randomized release kernel `M : (Fin n → CateObs d) → Measure ℝ`, a measurable probability kernel) @realizes D,D'(neighboring datasets: the `∃ i, ∀ j ≠ i, D j = D' j` clause) @realizes B(the measurable output event `B : Set ℝ`) -/
def CentralDP {d : ℕ} (n : ℕ) (epsN delN : ℝ)
    (M : (Fin n → CateObs d) → Measure ℝ) : Prop :=
  (∀ D : Fin n → CateObs d, IsProbabilityMeasure (M D)) ∧
    Measurable M ∧
    ∀ D D' : Fin n → CateObs d,
      (∀ i, D i ∈ sampleSpace d) → (∀ i, D' i ∈ sampleSpace d) →
      ReplacementAdjacent D D' →
      ∀ B : Set ℝ, MeasurableSet B →
        (M D).real B ≤ Real.exp epsN * (M D').real B + delN
        -- @realizes epsilon_n(the multiplicative privacy budget exp(ε_n)) @realizes delta_n(the additive approximate-privacy failure δ_n)

/-- Well-formedness of the deterministic privacy-budget sequences: for every
`n ≥ 1`, `ε_n ∈ [n^{-1}, 1]` and `δ_n ∈ (0, n^{-2}]`.
@realizes epsilon_n(ε_n ∈ [n^{-1},1] range) @realizes delta_n(δ_n ∈ (0,n^{-2}] range) -/
def PrivacyBudget (eps del : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (n : ℝ)⁻¹ ≤ eps n ∧ eps n ≤ 1 ∧ 0 < del n ∧ del n ≤ (n : ℝ) ^ (-(2 : ℝ))

/-! ## Environment S3 — regime constants -/

-- @env: S3
/-- Standing well-formedness of the regime constants: `α, β, γ, L, f₀ ∈ (0,∞)`,
`e₀ ∈ (0,1/2)`, `f₀ ≤ f₁`, `r₀ ∈ (0,1/2)`, and `x₀ ∈ (0,1)^d`. Threaded as a
hypothesis into every regime lemma/theorem so no constant is used outside its
declared space.
@realizes alpha(0 < α; Hölder order of the propensity) @realizes gamma(0 < γ; Hölder order of the CATE) @realizes L(0 < L; common Hölder radius) @realizes e_0(e₀ ∈ (0,1/2); overlap constant) @realizes f_0(0 < f₀; lower density bound) @realizes f_1(f₀ ≤ f₁; upper density bound) @realizes r_0(r₀ ∈ (0,1/2); localization radius) @realizes x_0(x₀ ∈ (0,1)^d; interior evaluation point) -/
def RegimeConstants {d : ℕ} (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ) : Prop :=
  0 < alpha ∧ 0 < beta ∧ 0 < gamma ∧ 0 < L ∧
    e0 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
    0 < f0 ∧ f0 ≤ f1 ∧
    r0 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
    (∀ i, x0 i ∈ Set.Ioo (0 : ℝ) 1)

/-! ## Construction `def`s -/

-- @node: def:dp-minimax-risk
/-- Central-DP minimax expected absolute error for `τ_P(x₀)`:
`R_n^{DP} = inf_{M_n central-DP} sup_{P ∈ class} E_P|M_n(O_1,…,O_n) - τ_P(x₀)|`,
the error integrated over both the `n`-fold i.i.d. sample law and the mechanism
randomness.

**Well-posedness (junk-value guard).** The infimum ranges over central-DP Markov
PROBABILITY kernels (`CentralDP` already carries `IsProbabilityMeasure (M s)` and
kernel measurability) whose per-sample release law is CLIPPED to the estimand range
`[-2,2]`. The supremum ranges only over GENUINE i.i.d. probability laws in the class
(`IidSampling P`) whose estimand `|μ_{1,P}(x₀) - μ_{0,P}(x₀)| ≤ 2` sits in the
clip range, so clipping is value-preserving and never increases the absolute error
(every such `τ_P(x₀) ∈ [-2,2]` since `μ ∈ [-1,1]`); this keeps the inner integrand
`|z - τ_P(x₀)|` bounded by `4` under each release law, so the `⨅`/`⨆` are well-posed
with no junk-`0` inflation of the converse (mirrors the sibling
`DoseResponseMinimax.minimaxRisk` truncation). -/
noncomputable def dpMinimaxRisk {d : ℕ} (n : ℕ) (epsN delN : ℝ)
    (C : CateLaw d → Prop) (x0 : Fin d → ℝ) : ℝ :=
  ⨅ M : {M : (Fin n → CateObs d) → Measure ℝ //
      CentralDP n epsN delN M ∧
        (∀ s, (M s) (Set.Icc (-2 : ℝ) 2)ᶜ = 0)},
      -- @realizes O_1, ..., O_n(mechanism domain is the size-`n` sample `Fin n → CateObs d`)
    ⨆ P : {P : CateLaw d // C P ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2},
      -- @realizes O_1, ..., O_n(the i.i.d. n-sample as the n-fold PRODUCT LAW `Measure.pi (fun _:Fin n => P.dataMeasure)`; its factors are mutually independent and identically `P.dataMeasure`-distributed by the `IIDSample` conjunct of `IidSampling`; the sup domain is restricted to genuine i.i.d. probability laws with in-range estimand)
    ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(M.1 s))
      ∂(Measure.pi fun _ : Fin n => (P.1).dataMeasure)

-- @node: def:nonprivate-cate-rate
/-- Kennedy–Balakrishnan–Robins–Wasserman non-private pointwise benchmark
`r_n^{CATE} = n^{-κ}`, with
`κ = min{1/(2 + d/γ), 1/(1 + d/(2γ) + d/(2(α+β)))}` (the exponent `κ` inlined).
@realizes r_n^CATE(the benchmark rate `n^{-κ}` computed by this def) @realizes kappa(the exponent `κ = min{1/(2+d/γ), 1/(1+d/(2γ)+d/(2(α+β)))}` inlined in the `rpow` exponent) -/
noncomputable def nonprivateCateRate (n : ℕ) (alpha beta gamma : ℝ) (d : ℕ) : ℝ :=
  (n : ℝ) ^ (-(min (1 / (2 + (d : ℝ) / gamma))
      (1 / (1 + (d : ℝ) / (2 * gamma) + (d : ℝ) / (2 * (alpha + beta))))))

-- @node: def:private-regression-calibration
/-- Central-DP pointwise-regression calibration
`r_n^{regDP} = inf_{0 < h ≤ r₀}{ h^γ + (n h^d)^{-1/2} + 1/(n ε_n h^d) }`.
@realizes r_n^regDP(the calibration rate — the bandwidth infimum computed by this def) -/
noncomputable def privateRegressionCalibration (n : ℕ) (r0 gamma : ℝ) (d : ℕ)
    (epsN : ℝ) : ℝ :=
  ⨅ h : {h : ℝ // 0 < h ∧ h ≤ r0},
    h.1 ^ gamma + ((n : ℝ) * h.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
      + 1 / ((n : ℝ) * epsN * h.1 ^ (d : ℝ))

/-- The FORMAL algebraic objective `E_n^{alg}(h,k)` of the causal-private frontier
handle (`q = α + β`) — a SUPPORTING helper of the anchored node
`causalPrivateFrontierHandle` below (NOT the node's decl on its own):
`E_n^{alg}(h,k) = h^γ + (h/k^{1/d})^q + (n h^d)^{-1/2} + √k/(n h^d) + k/(n ε_n h^d)`.
This is a formal definition object only — NOT a proved risk envelope, attainable
rate, or minimax frontier (see `causalPrivateFrontierHandle`). -/
noncomputable def causalPrivateFrontierObjective (n : ℕ) (alpha beta gamma : ℝ)
    (d : ℕ) (epsN h k : ℝ) : ℝ :=
  h ^ gamma + (h / k ^ (1 / (d : ℝ))) ^ (alpha + beta)
    + ((n : ℝ) * h ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
    + k ^ (1 / 2 : ℝ) / ((n : ℝ) * h ^ (d : ℝ))
    + k / ((n : ℝ) * epsN * h ^ (d : ℝ))

/-- The FORMAL exactly-optimized value of the algebraic frontier handle
`ρ_n^{alg} = r_n^{CATE} ∨ (n ε_n)^{-s/(s+d)}`, `q = α + β`, `s = min(γ, q)`
(equivalently `r_n^{CATE} ∨ (n ε_n)^{-γ/(γ+d)} ∨ (n ε_n)^{-q/(q+d)}`). It is
EXPLICITLY a formal algebraic object, NOT asserted as a proved risk envelope,
attainable rate, minimax frontier, or minimax elbow. -/
noncomputable def causalPrivateFrontierValue (n : ℕ) (alpha beta gamma : ℝ)
    (d : ℕ) (epsN : ℝ) : ℝ :=
  max (max (nonprivateCateRate n alpha beta gamma d)
        (((n : ℝ) * epsN) ^ (-(gamma / (gamma + (d : ℝ))))))
    (((n : ℝ) * epsN) ^ (-((alpha + beta) / ((alpha + beta) + (d : ℝ)))))

/-- Worst-case class absolute error of a release `M` over the (i.i.d., in-range) laws of
the frozen class — the inner `sup` of `dpMinimaxRisk`. A SUPPORTING helper of the anchored
node `causalPrivateFrontierHandle` (clause (g)), used to state, at the COMPONENT level, that
an actual private-HOIF program's release and its four internal fold releases are all
accounted within the program's claimed bound `V`. -/
noncomputable def worstCaseClassError {d : ℕ} (n : ℕ)
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (M : (Fin n → CateObs d) → Measure ℝ) : ℝ :=
  ⨆ P : {P : CateLaw d //
        HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P
          ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2},
    ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(M s))
      ∂(Measure.pi fun _ : Fin n => (P.1).dataMeasure)

/- Genuine GLOBAL-SENSITIVITY stabilization of a fold release `Mfold` — the
alternative to `CentralDP` that a non-privatized fold of a private-HOIF program must
satisfy, and DISTINCT from output clipping. There is a finite global sensitivity bound
`Δ ≥ 0` such that on EVERY pair of neighboring datasets `s, s'` (differing in exactly one
record) the two output laws differ by at most a `Δ`-shift: for every Borel event `B`,
`Pr{Mfold(s) ∈ B} ≤ Pr{Mfold(s') ∈ B_Δ}`, where `B_Δ = {z : ∃ y ∈ B, |z - y| ≤ Δ}` is the
`Δ`-thickening of `B`. This is bounded per-record influence (a genuine sensitivity bound,
enabling downstream privatization of the assembled release) — NOT the output-support /
clipping-to-`[-2,2]` constraint. A SUPPORTING helper of `causalPrivateFrontierHandle`
clause (g). -/
/-- A genuine release kernel: measurable in the dataset with a probability output
law at every dataset. -/
def ReleaseKernel {d : ℕ} (n : ℕ)
    (M : (Fin n → CateObs d) → Measure ℝ) : Prop :=
  (∀ s, IsProbabilityMeasure (M s)) ∧ Measurable M

def GloballyStabilized {d : ℕ} (n : ℕ)
    (Mfold : (Fin n → CateObs d) → Measure ℝ) : Prop :=
  ReleaseKernel n Mfold ∧ ∃ Δ : ℝ, 0 ≤ Δ ∧
    ∀ s s' : Fin n → CateObs d, (∃ i : Fin n, ∀ j : Fin n, j ≠ i → s j = s' j) →
      ∀ B : Set ℝ, MeasurableSet B →
        (Mfold s).real B ≤ (Mfold s').real {z : ℝ | ∃ y ∈ B, |z - y| ≤ Δ}

/-- The paper's fixed density/Gram-stable upper-bound submodel condition.  Laws in
the submodel share the known covariate density `pKnown`; that density is uniformly
bounded on the cube, and every localized quadratic Gram form is uniformly
equivalent to its Lebesgue counterpart.  Thus membership is pinned by the stated
density and Gram conditions, rather than by a freely chosen submodel predicate. -/
def KBRWDensityGramStable {d : ℕ} (alpha beta gamma L e0 f0 f1 r0 : ℝ)
    (x0 : Fin d → ℝ) (pKnown : (Fin d → ℝ) → ℝ) (P : CateLaw d) : Prop :=
  HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P ∧ IidSampling P ∧
    P.px = pKnown ∧ Continuous pKnown ∧
    (∀ x ∈ cube d, f0 ≤ pKnown x ∧ pKnown x ≤ f1) ∧
    ∃ cGram CGram : ℝ, 0 < cGram ∧ cGram ≤ CGram ∧
      ∀ h : ℝ, 0 < h → h ≤ r0 →
        ∀ g : (Fin d → ℝ) → ℝ,
          cGram * (∫ x in supBall x0 h, (g x) ^ (2 : ℕ))
              ≤ ∫ x in supBall x0 h, (g x) ^ (2 : ℕ) * pKnown x ∧
            (∫ x in supBall x0 h, (g x) ^ (2 : ℕ) * pKnown x)
              ≤ CGram * ∫ x in supBall x0 h, (g x) ^ (2 : ℕ)

/-- The canonical nonnegative magnitude contributed by a named scalar HOIF fold.
The fold output is integrated over its own release randomness and the i.i.d. sample,
then maximized over the frozen class.  This is deliberately not a CATE risk: it
measures the released component itself, so the nominal nuisance/Gram/score/second
terms below cannot be chosen independently of their corresponding releases. -/
noncomputable def hoifFoldContribution {d : ℕ} (n : ℕ)
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (Mfold : (Fin n → CateObs d) → Measure ℝ) : ℝ :=
  ⨆ P : {P : CateLaw d //
        HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P ∧ IidSampling P},
    ∫ s, (∫ z, |z| ∂(Mfold s))
      ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure)

/-- A measurable assembly genuinely uses each of the four *actual named fold
releases*: for every coordinate there are two datasets for which replacing only
that fold law, while holding the other three fold laws fixed, changes the assembled
output law.  Thus coordinate-essentiality is tested on the releases' realized laws,
not merely on off-support arguments of the assembly function. -/
def UsesEveryHOIFFold {d : ℕ} (n : ℕ)
    (assemble : ℝ × ℝ × ℝ × ℝ → ℝ)
    (Mnuis Mgram Mscore Msecond : (Fin n → CateObs d) → Measure ℝ) : Prop :=
  (∃ s s',
      ((Mnuis s).prod ((Mgram s).prod ((Mscore s).prod (Msecond s)))).map assemble ≠
        ((Mnuis s').prod ((Mgram s).prod ((Mscore s).prod (Msecond s)))).map assemble) ∧
  (∃ s s',
      ((Mnuis s).prod ((Mgram s).prod ((Mscore s).prod (Msecond s)))).map assemble ≠
        ((Mnuis s).prod ((Mgram s').prod ((Mscore s).prod (Msecond s)))).map assemble) ∧
  (∃ s s',
      ((Mnuis s).prod ((Mgram s).prod ((Mscore s).prod (Msecond s)))).map assemble ≠
        ((Mnuis s).prod ((Mgram s).prod ((Mscore s').prod (Msecond s)))).map assemble) ∧
  (∃ s s',
      ((Mnuis s).prod ((Mgram s).prod ((Mscore s).prod (Msecond s)))).map assemble ≠
        ((Mnuis s).prod ((Mgram s).prod ((Mscore s).prod (Msecond s')))).map assemble)

/-- The actual error decomposition asserted for a private-HOIF program.  The
assembled release's class risk is bounded by named bias, nuisance, Gram, score,
second-order, and third-order components.  Bias is pinned to `h^γ`; the four
stochastic components are pinned to the canonical magnitudes of their corresponding
named fold releases; and the third-order component is definitionally the retained
KBRW Gram/density term `k/(n ε h^d)`. -/
def PrivateHOIFErrorDecomposition {d : ℕ} (n : ℕ)
    (alpha beta gamma L e0 f0 f1 r0 epsN : ℝ) (x0 : Fin d → ℝ)
    (M Mnuis Mgram Mscore Msecond : (Fin n → CateObs d) → Measure ℝ)
    (V : ℝ) : Prop :=
  ∃ h k bias nuisance gram score second third : ℝ,
    0 < h ∧ h ≤ r0 ∧ 1 ≤ k ∧ k ≤ (n : ℝ) * h ^ (d : ℝ) ∧
    bias = h ^ gamma ∧
    nuisance = hoifFoldContribution n alpha beta gamma L e0 f0 f1 r0 x0 Mnuis ∧
    gram = hoifFoldContribution n alpha beta gamma L e0 f0 f1 r0 x0 Mgram ∧
    score = hoifFoldContribution n alpha beta gamma L e0 f0 f1 r0 x0 Mscore ∧
    second = hoifFoldContribution n alpha beta gamma L e0 f0 f1 r0 x0 Msecond ∧
    third = k / ((n : ℝ) * epsN * h ^ (d : ℝ)) ∧
    worstCaseClassError n alpha beta gamma L e0 f0 f1 r0 x0 M
      ≤ bias + nuisance + gram + score + second + third ∧
    V = bias + nuisance + gram + score + second + third

/-- An actual private-HOIF program/release: a measurable probability-kernel output
assembled from the joint measurable probability-kernel releases of the nuisance,
Gram, first-order-score, and second-order folds.  Every actual fold law is essential
to that assembly, and every named stochastic term in the program-level error
decomposition is pinned to its corresponding fold.  Unlike a CATE-risk predicate
applied to each fold, the decomposition bounds only the assembled release. -/
def PrivateHOIFProgram {d : ℕ} (n : ℕ)
    (alpha beta gamma L e0 f0 f1 r0 epsN : ℝ) (x0 : Fin d → ℝ)
    (M Mnuis Mgram Mscore Msecond : (Fin n → CateObs d) → Measure ℝ) (V : ℝ) : Prop :=
  ReleaseKernel n M ∧ ReleaseKernel n Mnuis ∧ ReleaseKernel n Mgram ∧
    ReleaseKernel n Mscore ∧ ReleaseKernel n Msecond ∧
    (∃ assemble : ℝ × ℝ × ℝ × ℝ → ℝ, Measurable assemble ∧
      (∀ s, M s = ((Mnuis s).prod
        ((Mgram s).prod ((Mscore s).prod (Msecond s)))).map assemble) ∧
      UsesEveryHOIFFold n assemble Mnuis Mgram Mscore Msecond) ∧
    PrivateHOIFErrorDecomposition n alpha beta gamma L e0 f0 f1 r0 epsN x0
      M Mnuis Mgram Mscore Msecond V

/-- The FULL formal causal-private frontier handle (`q = α + β`, `s = min(γ, q)`):
a `Prop` bundling the FORMAL algebraic data AND the note's substantive scope clauses —
(a) the constrained objective `E_n^{alg}(h,k)` over its domain `0 < h ≤ r₀`,
`1 ≤ k ≤ n h^d`; (b) the exactly optimized value `ρ_n^{alg}` as the constrained
infimum of `E_n^{alg}` and its closed form `causalPrivateFrontierValue`; (c) the
algebraic crossing budget `ε_n^{alg} = n^{-1 + κ(s+d)/s}` at which the non-private and
`s`-privacy powers coincide; (d) the PRIVACY-POWER COMPARISON (`q`- and `γ`-powers
coincide at `n·ε = 1`, the `q`-power strictly exceeds the `γ`-power only when
`n·ε > 1` and `q < γ`); (e) the TWO-POINT / TV-CONTRACTION BARRIER LIMITATION (any `Δ`
certified through the DP TV-contraction budget is capped at the `γ`-privacy order, so
the ordinary two-point route cannot reach the `q`-branch); (f) the DENSITY/GRAM-STABLE
QUALIFICATION (the KBRW nonprivate value matches the genuinely NONPRIVATE minimax risk
only on a nonempty density/Gram-stable submodel containing an admissible i.i.d. law,
not the full positive-density class); (g) the private-HOIF
COMPONENT-STABILIZATION NECESSITY, stated as a UNIVERSAL/CONDITIONAL requirement on an ACTUAL
ASSEMBLED, already-private HOIF upper program (a central-DP release `M` that is GENUINELY ASSEMBLED —
post-processed via a fixed measurable assembly map from the JOINT release of four NAMED
internal fold releases, nuisance-pilot/Gram/first-order-score/second-order, so each fold is a
COMPONENT TIED TO `M` and is essential on the actual fold laws; all five releases are
measurable probability kernels, and the assembled CATE release carries a named HOIF error
decomposition whose four stochastic terms are pinned to their corresponding fold releases
and whose third-order component is exactly the KBRW Gram/density remainder): for EVERY such
program, each of the four folds is
SEPARATELY either an actual privatized release (`CentralDP`) or GENUINELY GLOBALLY STABILIZED
(`GloballyStabilized`: a finite global-sensitivity Δ-shift bound on neighboring output laws,
NOT output clipping). Privacy is one of the two per-fold alternatives; the requirement is
per COMPONENT and conditional on being an actual assembled program — NOT an existential
asserting a program exists, NOT inferred from a single-release risk-control premise, no
foldwise CATE-risk premises, and no whole-release clipping. **NON-CERTIFICATION.**
None of these clauses is a proved risk envelope, attainable rate, minimax frontier, or
minimax elbow; this is a formal `def` object only (never a theorem, no proof) consumed
as context by `CausalDpFrontierQuestion`. The class parameters `L, e₀, f₀, f₁, x₀` are
carried so clauses (f)–(g) can name the actual model class. Clause (e) is a VERBATIM
mirror of the headline theorem `causal_dp_two_point_barrier` part (ii): it quantifies over
its OWN admissible budget SEQUENCE `(ε_·, δ_·)` and a fresh sample-size binder `m`, with the
γ-branch constant `Ceta` chosen UNIFORMLY in `m` (`∃Ceta` before `∀m`) and ranging over
ARBITRARY class members (no `IidSampling` restriction); it does NOT use the handle's scalar
`ε_n, δ_n, n`, which serve the per-sample-size clauses (a)–(d), (f)–(g). -/
-- @node: def:causal-private-frontier-handle
noncomputable def causalPrivateFrontierHandle {d : ℕ} (n : ℕ)
    (alpha beta gamma L e0 f0 f1 : ℝ) (epsN delN r0 : ℝ) (x0 : Fin d → ℝ) : Prop :=
  -- (a) the formal objective E_n^alg is defined (nonnegative) on its stated domain
  (∀ h k : ℝ, 0 < h → h ≤ r0 → 1 ≤ k → k ≤ (n : ℝ) * h ^ (d : ℝ) →
      0 ≤ causalPrivateFrontierObjective n alpha beta gamma d epsN h k)
    ∧ -- (b) the exactly optimized value ρ_n^alg over the constrained domain
      (⨅ hk : {p : ℝ × ℝ //
            0 < p.1 ∧ p.1 ≤ r0 ∧ 1 ≤ p.2 ∧ p.2 ≤ (n : ℝ) * p.1 ^ (d : ℝ)},
          causalPrivateFrontierObjective n alpha beta gamma d epsN hk.1.1 hk.1.2)
        = causalPrivateFrontierValue n alpha beta gamma d epsN
    ∧ -- (c) the algebraic crossing budget ε_n^alg = n^{-1 + κ(s+d)/s}, s = min(γ, q)
      (∃ epsCross : ℝ,
        epsCross = (n : ℝ) ^ (-(1 : ℝ)
            + (min gamma (alpha + beta) + (d : ℝ)) / min gamma (alpha + beta)
              * min (1 / (2 + (d : ℝ) / gamma))
                  (1 / (1 + (d : ℝ) / (2 * gamma) + (d : ℝ) / (2 * (alpha + beta)))))
          ∧ nonprivateCateRate n alpha beta gamma d
              = ((n : ℝ) * epsCross)
                  ^ (-(min gamma (alpha + beta) / (min gamma (alpha + beta) + (d : ℝ)))))
    ∧ -- (d) PRIVACY-POWER COMPARISON: at n·ε = 1 the q- and γ-privacy powers coincide;
      --   and (the note's NECESSARY condition, "the q-power is strictly larger ONLY WHEN
      --   n·ε > 1") the strict dominance of the q-power over the γ-power IMPLIES n·ε > 1
      --   (in the q = α+β < γ regime) — NOT the sufficient converse
      ((n : ℝ) * epsN = 1 →
          ((n : ℝ) * epsN) ^ (-((alpha + beta) / ((alpha + beta) + (d : ℝ))))
            = ((n : ℝ) * epsN) ^ (-(gamma / (gamma + (d : ℝ)))))
    ∧ (alpha + beta < gamma →
          (((n : ℝ) * epsN) ^ (-(gamma / (gamma + (d : ℝ))))
              < ((n : ℝ) * epsN) ^ (-((alpha + beta) / ((alpha + beta) + (d : ℝ))))
            → 1 < (n : ℝ) * epsN))
    ∧ -- (e) TWO-POINT / TV-CONTRACTION BARRIER LIMITATION — a VERBATIM mirror of the
      --   headline theorem `causal_dp_two_point_barrier` part (ii): the UNIFORM-in-sample-size
      --   γ-branch cap. For every admissible privacy-budget SEQUENCE `(ε_·, δ_·)` and every
      --   η ∈ (0,1) there is a constant `Ceta` chosen BEFORE the sample size (`∃Ceta` before
      --   `∀m`, so `Ceta` is UNIFORM in `m` — encoding the paper's uniform γ-branch rate bound,
      --   NOT a per-sample-size constant) such that for EVERY sample size `m ≥ 1` and EVERY
      --   pair of ARBITRARY class members `P, Q` (only `HolderCateClass` — NO extra `IidSampling`
      --   restriction; the cited barrier ranges over the whole frozen class) whose FULL
      --   approximate-DP TV-contraction budget certifies
      --   `m·(exp ε_m − 1 + δ_m)·TV(P,Q) ≤ η`, the target separation
      --   `Δ = |τ_P(x₀) − τ_Q(x₀)|` is capped at the γ-privacy order `(m·ε_m)^{-γ/(γ+d)}` — so
      --   the ordinary two-point route cannot reach the q-branch. The handle's own scalar
      --   `ε_n, δ_n, n` are NOT used here: the barrier is a statement about the budget sequence,
      --   so budgets vary with `m` (no free `m` against frozen budgets).
      (∀ eps del : ℕ → ℝ, PrivacyBudget eps del →
        ∀ η : ℝ, 0 < η → η < 1 → ∃ Ceta : ℝ, 0 < Ceta ∧
          ∀ m : ℕ, 1 ≤ m → ∀ P Q : CateLaw d,
            HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P →
            HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 Q →
            (m : ℝ) * (Real.exp (eps m) - 1 + del m)
                * tvDist P.dataMeasure Q.dataMeasure ≤ η →
              |(P.mu1 x0 - P.mu0 x0) - (Q.mu1 x0 - Q.mu0 x0)|
                ≤ Ceta * ((m : ℝ) * eps m) ^ (-(gamma / (gamma + (d : ℝ)))))
    ∧ -- (f) DENSITY/GRAM-STABLE QUALIFICATION (fixed stability + KBRW-rate matching): the
      --   KBRW nonprivate value `r_n^CATE` is matched two-sided by the genuinely NONPRIVATE
      --   minimax risk (an infimum over measurable clipped estimators, with NO central-DP
      --   restriction), with constants independent of the sample size, ONLY on a NONEMPTY
      --   density/Gram-STABLE submodel whose witness is an admissible i.i.d. law included in
      --   the risk supremum — laws whose covariate density is GLOBALLY
      --   (not merely locally) bounded in `[f₀,f₁]` AND CONTINUOUS on the cube (the
      --   Gram-stability qualification) — NOT on the full positive-density class
      (∃ pKnown : (Fin d → ℝ) → ℝ,
          (∃ P : CateLaw d,
            KBRWDensityGramStable alpha beta gamma L e0 f0 f1 r0 x0 pKnown P ∧
            |P.mu1 x0 - P.mu0 x0| ≤ 2) ∧
          (∃ cK CK : ℝ, 0 < cK ∧ 0 < CK ∧ ∀ᶠ m : ℕ in Filter.atTop,
              cK * nonprivateCateRate m alpha beta gamma d
                  ≤ (⨅ T : {T : (Fin m → CateObs d) → ℝ //
                        Measurable T ∧ ∀ s, T s ∈ Set.Icc (-2 : ℝ) 2},
                      ⨆ P : {P : CateLaw d //
                          KBRWDensityGramStable alpha beta gamma L e0 f0 f1 r0
                            x0 pKnown P ∧
                          |P.mu1 x0 - P.mu0 x0| ≤ 2},
                        ∫ s, |T.1 s - (P.1.mu1 x0 - P.1.mu0 x0)|
                          ∂(Measure.pi fun _ : Fin m => P.1.dataMeasure))
                ∧ (⨅ T : {T : (Fin m → CateObs d) → ℝ //
                        Measurable T ∧ ∀ s, T s ∈ Set.Icc (-2 : ℝ) 2},
                      ⨆ P : {P : CateLaw d //
                          KBRWDensityGramStable alpha beta gamma L e0 f0 f1 r0
                            x0 pKnown P ∧
                          |P.mu1 x0 - P.mu0 x0| ≤ 2},
                        ∫ s, |T.1 s - (P.1.mu1 x0 - P.1.mu0 x0)|
                          ∂(Measure.pi fun _ : Fin m => P.1.dataMeasure))
                    ≤ CK * nonprivateCateRate m alpha beta gamma d))
    ∧ -- (g) PRIVATE-HOIF COMPONENT-STABILIZATION NECESSITY (universal/conditional, on an
      --   ACTUAL ASSEMBLED program — NOT an existential over program-unrelated kernels). An
      --   actual private-HOIF upper program is a central-DP release `M` that is GENUINELY
      --   ASSEMBLED (post-processed) from four NAMED internal fold releases — nuisance-pilot
      --   `Mnuis`, Gram `Mgram`, first-order-score `Mscore`, second-order `Msecond`. The
      --   `PrivateHOIFProgram` predicate requires all five objects to be measurable probability
      --   kernels, ties the folds to `M` through a fixed measurable assembly map that is
      --   coordinate-essential on the ACTUAL fold laws, and applies an ACTUAL named HOIF error
      --   decomposition only to the assembled release (the nuisance, Gram, and score folds are
      --   not themselves CATE estimators). That decomposition pins each stochastic term to the
      --   canonical contribution of its corresponding fold and bounds the assembled worst-case
      --   error by those terms plus a third-order term definitionally equal to
      --   `k/(n ε_n h^d)`. For EVERY
      --   such assembled, already-private program the note's NECESSITY holds: each of the four folds is
      --   SEPARATELY either an actual privatized release (`CentralDP`) OR GENUINELY GLOBALLY
      --   STABILIZED (`GloballyStabilized`: a finite global-sensitivity Δ-shift bound on
      --   neighboring output laws — NOT output clipping to `[-2,2]`). The requirement is per
      --   COMPONENT and conditional on being an actual assembled program whose release is
      --   already central-DP. There is NO existential asserting a program
      --   exists, NO foldwise CATE-risk premise, and NO whole-release clipping. **NON-CERTIFICATION.**
      (∀ (M Mnuis Mgram Mscore Msecond : (Fin n → CateObs d) → Measure ℝ) (V : ℝ),
          PrivateHOIFProgram n alpha beta gamma L e0 f0 f1 r0 epsN x0
              M Mnuis Mgram Mscore Msecond V →
          CentralDP n epsN delN M →
            (CentralDP n epsN delN Mnuis ∨ GloballyStabilized n Mnuis)
              ∧ (CentralDP n epsN delN Mgram ∨ GloballyStabilized n Mgram)
              ∧ (CentralDP n epsN delN Mscore ∨ GloballyStabilized n Mscore)
              ∧ (CentralDP n epsN delN Msecond ∨ GloballyStabilized n Msecond))

/-! ## Open-ended residual -/

-- @node: oeq:causal-dp-frontier
/-- **OPEN QUESTION (acknowledged open problem, not a theorem).** Under the frozen
privacy budgets (`PrivacyBudget eps del`) and the regime `0 < β ≤ γ`, the residual
frontier question over the full positive-density class
`P_{α,β,γ}(L,e₀,f₀,f₁,r₀,x₀)` records the note's UNRESOLVED ALTERNATIVES — NOT a flat
conjunction asserting three simultaneous global equivalences (which would be false in
general, as the bracket is non-matching for `β < γ`). It poses the existence of a
sharp two-sided rate `r`, WITH the note's stipulated causal-lower-bound requirement,
and leaves the phase structure as a genuine DISJUNCTION:

* the sharp rate `r` characterizes `R_n^{DP}` two-sided, AND any matching lower bound
  is witnessed by a CAUSAL LOCALIZED FAMILY (a two-point pair in the class with
  `μ₀ = 0`, constant propensity `e₀`, shared covariate design, and a localized
  `γ`-Hölder `μ₁` perturbation) — a regression stand-in is NOT permitted;
* **phase alternatives (disjunction — "which regimes occur"):** `r` is EITHER the
  formal frontier `ρ_n^{alg}` alone (`causalPrivateFrontierValue`), OR the
  pointwise-regression calibration `r_n^{regDP}` adds a regime, OR private nuisance
  estimation adds ONE OR MORE further leading regimes (an extra rate dominating
  `ρ_n^{alg}`);
* **privacy-free reduction (open sub-question):** whether the maximal-budget
  (`ε_n = 1`) proxy for the privacy-free full-class limit REDUCES to the KBRW
  benchmark `r_n^{CATE}` (`nonprivateCateRate`) — posed as the disjunction "reduces,
  OR there is a strictly larger sharp rate", not asserted.

It is stated here as a Prop `def` ONLY; it is NOT a theorem, carries NO proof, and NO
theorem in this development depends on it. -/
def CausalDpFrontierQuestion {d : ℕ} (alpha beta gamma L e0 f0 f1 r0 : ℝ)
    (x0 : Fin d → ℝ) (eps del : ℕ → ℝ) : Prop :=
  PrivacyBudget eps del → SmoothnessOrder beta gamma →
    ∃ r : ℕ → ℝ,
      -- the residual asks for a SHARP two-sided rate `r` for R_n^DP …
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
            c * r n ≤ dpMinimaxRisk n (eps n) (del n)
                (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
          ∧ dpMinimaxRisk n (eps n) (del n)
                (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
              ≤ C * r n)
      -- … with any matching lower bound WITNESSED BY A CAUSAL LOCALIZED FAMILY
      --   (the note's stipulated condition: two-point pair, μ₀ = 0, constant
      --    propensity e₀, shared covariate design, localized γ-Hölder μ₁ bump)
      ∧ (∀ᶠ n : ℕ in Filter.atTop, ∃ P0 P1 : CateLaw d,
            HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P0 ∧
            HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P1 ∧
            (∀ x, P0.mu0 x = 0) ∧ (∀ x, P0.mu1 x = 0) ∧ (∀ x, P0.pi x = e0) ∧
            (∀ x, P1.mu0 x = 0) ∧ (∀ x, P1.pi x = e0) ∧
            P1.PX = P0.PX ∧ (∀ x, P1.px x = P0.px x) ∧
            (∃ h cB : ℝ, ∃ B : (Fin d → ℝ) → ℝ,
                0 < h ∧ h ≤ r0 ∧ 0 < cB ∧ B 0 = 1 ∧
                (∀ u : Fin d → ℝ, (∃ j, 1 < |u j|) → B u = 0) ∧
                (∀ x, P1.mu1 x = cB * h ^ gamma * B (fun j => (x j - x0 j) / h))) ∧
            r n ≤ |(P1.mu1 x0 - P1.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)|)
      -- … and the UNRESOLVED phase alternatives (a DISJUNCTION over the candidate
      --   leading regimes, "one or more additional regimes"):
      ∧ ( (∀ᶠ n : ℕ in Filter.atTop,
              r n = causalPrivateFrontierValue n alpha beta gamma d (eps n))
          ∨ (∀ᶠ n : ℕ in Filter.atTop,
              r n = max (causalPrivateFrontierValue n alpha beta gamma d (eps n))
                        (privateRegressionCalibration n r0 gamma d (eps n)))
          ∨ (∃ t : ℕ → ℝ,
              (∀ᶠ n : ℕ in Filter.atTop,
                  causalPrivateFrontierValue n alpha beta gamma d (eps n) ≤ t n)
                ∧ ∀ᶠ n : ℕ in Filter.atTop,
                    r n = max (max (causalPrivateFrontierValue n alpha beta gamma d (eps n))
                                (privateRegressionCalibration n r0 gamma d (eps n))) (t n)) )
      -- … and the privacy-free reduction sub-question (open): whether the ε_n = 1
      --   proxy reduces to r_n^CATE, OR a strictly larger sharp rate governs it.
      ∧ ( (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
              c * nonprivateCateRate n alpha beta gamma d
                  ≤ dpMinimaxRisk n 1 (del n)
                      (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
                ∧ dpMinimaxRisk n 1 (del n)
                      (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
                    ≤ C * nonprivateCateRate n alpha beta gamma d)
          ∨ (∃ t : ℕ → ℝ, (∀ᶠ n : ℕ in Filter.atTop,
                  nonprivateCateRate n alpha beta gamma d < t n)
                ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
                    c * t n ≤ dpMinimaxRisk n 1 (del n)
                        (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
                      ∧ dpMinimaxRisk n 1 (del n)
                          (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
                        ≤ C * t n) )

end CausalSmith.Stat.DpCateMinimax
