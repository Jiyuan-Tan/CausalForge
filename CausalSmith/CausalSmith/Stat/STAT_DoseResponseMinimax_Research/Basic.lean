/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sharp minimax lower frontier for interior continuous-dose response: shared core

Stage-2 scaffold for `stat_dose_response_minimax` (specialization
`holder_anisotropic_converse`).

This file carries the shared environment S-blocks (the i.i.d. observational
sampling world `DoseObs`/`DoseLaw`, the potential-outcome overlay, and the regime
constants), the assumption-atom `def`s, the model-class structure
`HolderDoseClass`, and the construction `def`s (`thetaFunctional`, `minimaxRisk`,
`publishedHoifRate`). Each emitted declaration carries its own node tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Estimation.MinimaxATE.Model` (Obs/productLaw/nMSE) | bypass-justified | Finite-covariate (`X : Fin M`, `Y : Bool`) PMF world; here `X ∈ [0,1]^d`, `A ∈ [0,1]` with a continuous-in-treatment bump, so the single-observation law is a genuine `Measure` over Mathlib `MeasureTheory` + `Measure.pi`. |
| `Causalean.PO.*` (`POSystem`, `Consistency`, `CondIndepCF`) | bypass-justified | Graph/regime-indexed PO skeleton heavier than the scalar continuous-dose overlay; consistency + ignorability are kept as threaded `Prop`s on the constructed law, verified on the explicit two-point construction (F3). |
| `Causalean.Stat.Sample.IIDSample` | reuse (in `IidSampling`) | the i.i.d. sampling content of `ass:iid-sampling`. |
| `Causalean.Stat.Minimax.{LeCam,MinimaxRisk,Pinsker,ChiSquared}` | reuse target (Helpers) | Le Cam / TV ≤ √(KL/2) / χ² tensorization feed the divergence helpers; built on rather than discharged one-to-one. |
| `Causalean.Mathlib.Probability.BernoulliMeasure` | reuse target (Helpers/Divergence) | `bernoulliLaw_klDiv_le_four_sq_sub` is the `{0,1}` KL band ingredient. |

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
import Causalean.Stat.Sample

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory
open scoped BigOperators

/-! ## Environment S1 — i.i.d. observational continuous-dose sampling world -/

-- @env: S1
/-- Observed unit `O = (Y, A, X)` with outcome `Y ∈ ℝ`, continuous treatment
`A ∈ [0,1]`, and covariate vector `X ∈ [0,1]^d`. The carrier fields are typed over
`ℝ` / `Fin d → ℝ` (the witness measure constructions require `ℝ`-valued ranges),
and the declared treatment range `[0,1]` and covariate cube `[0,1]^d` are pinned as
a STANDING a.s. support clause on the law by the two `IidSampling` support conjuncts
(`A ∈ [0,1]` and `X ∈ [0,1]^d` almost surely under `P`), which every law in
`HolderDoseClass` carries via `HolderDoseClass.iid`. `Y` is unconstrained (`ℝ`).
@realizes O -/
structure DoseObs (d : ℕ) where
  Y : ℝ -- @realizes Y(carrier ℝ)
  A : ℝ -- @realizes A(carrier ℝ; range [0,1] pinned a.s. by the IidSampling A-support conjunct)
  X : Fin d → ℝ -- @realizes X(carrier Fin d→ℝ; range [0,1]^d pinned a.s. by the IidSampling X-support conjunct)

/-- The observed-data type is made measurable by identifying each observation with
its outcome, treatment, and covariate tuple. -/
instance instMeasurableSpaceDoseObs {d : ℕ} : MeasurableSpace (DoseObs d) :=
  MeasurableSpace.comap (fun O : DoseObs d => (O.Y, O.A, O.X)) inferInstance

/-- The covariate cube `[0,1]^d`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The interior treatment window `[t_0 - ε_0, t_0 + ε_0]`. -/
def doseWindow (t0 eps0 : ℝ) : Set ℝ := Set.Icc (t0 - eps0) (t0 + eps0)

/-- Univariate Hölder ball of order `order` and radius `M` on a set `S ⊆ ℝ`:
all derivatives up to the largest integer `k = ⌈order⌉ - 1` strictly below
`order` exist continuously on `S`, are bounded by `M`, and the `k`-th derivative
is `(order - k)`-Hölder with constant `M`. This is the standard nonparametric
`C^{⌈order⌉-1, order-⌈order⌉+1}` convention, including integer orders. -/
def HolderBall1D (f : ℝ → ℝ) (order M : ℝ) (S : Set ℝ) : Prop :=
  ContDiffOn ℝ (⌈order⌉₊ - 1) f S ∧
    (∀ j : ℕ, j ≤ ⌈order⌉₊ - 1 → ∀ x ∈ S, |iteratedDeriv j f x| ≤ M) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      |iteratedDeriv (⌈order⌉₊ - 1) f x - iteratedDeriv (⌈order⌉₊ - 1) f y|
        ≤ M * |x - y| ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)))

/-- Multivariate Hölder ball of order `order` and radius `M` on a set
`S ⊆ (Fin d → ℝ)`: all iterated Fréchet derivatives up to the largest integer
`k = ⌈order⌉ - 1` strictly below `order` exist continuously on `S`, are bounded
by `M` in operator norm, and the `k`-th derivative is `(order - k)`-Hölder with
constant `M`. -/
def HolderBallND {d : ℕ} (f : (Fin d → ℝ) → ℝ) (order M : ℝ)
    (S : Set (Fin d → ℝ)) : Prop :=
  ContDiffOn ℝ (⌈order⌉₊ - 1) f S ∧
    (∀ j : ℕ, j ≤ ⌈order⌉₊ - 1 → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (⌈order⌉₊ - 1) f x - iteratedFDeriv ℝ (⌈order⌉₊ - 1) f y‖
        ≤ M * ‖x - y‖ ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)))

/-- Build-inline observed-law object: the per-draw observation law, the covariate
marginal, the law-side nuisances `μ_P, π_P, p_{X,P}`, and the potential-outcome
process `Y(·)` (the causal overlay S2). -/
structure DoseLaw (d : ℕ) where
  dataMeasure : Measure (DoseObs d) -- @realizes P(the single-observation data law of the unit O = (Y,A,X); the i.i.d. n-sample O_1,…,O_n is NOT realized here — it is the n-fold product of this law, carried by IidSampling + minimaxRisk, see their @realizes tags)
  PX : Measure (Fin d → ℝ) -- @realizes P_X(marginal law of X)
  mu : ℝ → (Fin d → ℝ) → ℝ -- @realizes mu_P(carrier [0,1]×[0,1]^d→ℝ; =E[Y∣A=a,X=x])
  pi : ℝ → (Fin d → ℝ) → ℝ -- @realizes pi_P(carrier [0,1]×[0,1]^d→ℝ; the conditional density A∣X, its declared range [0,∞) enforced by the `0 ≤ π_P` conjunct of `PiIsCondTreatmentDensity` and pinned to the law by that tie's joint factorization)
  px : (Fin d → ℝ) → ℝ -- @realizes p_{X,P}(carrier [0,1]^d→ℝ; density of P_X, its declared range [0,∞) enforced by the `0 ≤ p_{X,P}` conjunct of `PxHolder` and pinned to the law by the `PxIsXDensity` tie)
  pot : ℝ → DoseObs d → ℝ -- @realizes Y(a)(potential outcome process a ↦ Y(a) on the obs space)

/-! ## Assumption `def`s -/

-- @node: ass:iid-sampling
/-- `O_1, …, O_n` are i.i.d. draws from `P`. Carries the full i.i.d. content by
reusing `Causalean.Stat.IIDSample` (mutually independent, identically distributed
measurable maps with law `P.dataMeasure`), together with
`IsProbabilityMeasure P.dataMeasure` certifying that the per-draw law — hence the
`n`-fold product `Measure.pi (fun _ : Fin n => P.dataMeasure)` formed in
`minimaxRisk` — is a probability measure. Also pins the observed-unit support
`O = (Y,A,X)` to the sampling space `{(Y,A,X): Y∈ℝ, A∈[0,1], X∈[0,1]^d}`: under `P`
the treatment `A ∈ [0,1]` and the covariate vector `X ∈ [0,1]^d` almost surely.
@realizes O(the `IidSampling` conjunction pins the observed-unit law a.s. to {(Y,A,X): Y∈ℝ, A∈[0,1], X∈[0,1]^d} through its A-support and X-support conjuncts) -/
def IidSampling {d : ℕ} (P : DoseLaw d) : Prop :=
  IsProbabilityMeasure P.dataMeasure ∧
    (∀ᵐ O ∂P.dataMeasure, O.A ∈ Set.Icc (0 : ℝ) 1) ∧
      -- @realizes A(a.s. treatment-coordinate support A ∈ [0,1] under P, enforcing the declared treatment range [0,1])
    (∀ᵐ O ∂P.dataMeasure, O.X ∈ cube d) ∧
      -- @realizes X(a.s. covariate-coordinate support X ∈ [0,1]^d under P, enforcing the declared covariate range [0,1]^d)
    -- @realizes O_1, ..., O_n(i.i.d. n-sample: mutually independent, identically `P.dataMeasure`-distributed measurable draws via `Causalean.Stat.IIDSample` — THIS `IidSampling` i.i.d. realizer is one of the two load-bearing realizers of the sample symbol `O_1,…,O_n` (the other is the `minimaxRisk` `Measure.pi` product law). It is NOT realized by the FOLLOWING `Consistency` declaration; the tag is placed BEFORE the existential so it attaches to `IidSampling`, not to the next decl. Each draw is a.s. in `{A∈[0,1], X∈[0,1]^d}`, and the n-fold product `Measure.pi (fun _ : Fin n => P.dataMeasure)` formed in `minimaxRisk` is their joint law.)
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : @MeasureTheory.Measure Ω _mΩ),
      Nonempty (@Causalean.Stat.IIDSample Ω (DoseObs d) _mΩ
        instMeasurableSpaceDoseObs μ P.dataMeasure)

-- @node: ass:consistency
/-- Consistency `Y = Y(A)` almost surely under `P`: the realized outcome equals the
potential outcome at the realized treatment level. -/
def Consistency {d : ℕ} (P : DoseLaw d) : Prop :=
  ∀ᵐ O ∂P.dataMeasure, O.Y = P.pot O.A O

-- @node: ass:no-unmeasured-confounding
/-- Conditional ignorability for the continuous treatment: for every level
`a ∈ [0,1]`, the potential outcome `Y(a)` is independent of `A` given `X` under `P`
(the note restricts the dose to the treatment range `[0,1]`). Encoded in
the faithful tested form `E[f(Y(a)) ∣ A, X] = E[f(Y(a)) ∣ X]` for every bounded
measurable test `f` of the potential outcome (the standard conditional-independence
characterization, no `StandardBorelSpace` requirement). -/
def NoUnmeasuredConfounding {d : ℕ} (P : DoseLaw d) : Prop :=
  ∀ a ∈ Set.Icc (0 : ℝ) 1,
    Measurable (P.pot a) ∧
    ∀ (f : ℝ → ℝ), Measurable f → (∃ Mf : ℝ, ∀ y, |f y| ≤ Mf) →
      Integrable (fun O => f (P.pot a O)) P.dataMeasure ∧
      P.dataMeasure[(fun O => f (P.pot a O)) |
          MeasurableSpace.comap (fun O : DoseObs d => (O.A, O.X)) inferInstance]
        =ᵐ[P.dataMeasure]
      P.dataMeasure[(fun O => f (P.pot a O)) |
          MeasurableSpace.comap (fun O : DoseObs d => O.X) inferInstance]

-- @node: ass:bounded-outcome
/-- Bounded outcome `|Y| ≤ M` almost surely under `P`. -/
def BoundedOutcome {d : ℕ} (P : DoseLaw d) (M : ℝ) : Prop :=
  ∀ᵐ O ∂P.dataMeasure, |O.Y| ≤ M

-- @node: ass:interior-dose
/-- Interior evaluation point: `[t_0 - ε_0, t_0 + ε_0] ⊆ (0,1)`. -/
def InteriorDose (t0 eps0 : ℝ) : Prop :=
  doseWindow t0 eps0 ⊆ Set.Ioo (0 : ℝ) 1

-- @node: ass:local-positivity
/-- Local positivity: `π_P(a∣x) ≥ c_0` for every `a` in the `ε_0`-window and every
`x ∈ [0,1]^d`. -/
def LocalPositivity {d : ℕ} (P : DoseLaw d) (c0 t0 eps0 : ℝ) : Prop :=
  ∀ a ∈ doseWindow t0 eps0, ∀ x ∈ cube d, c0 ≤ P.pi a x

-- @node: ass:mu-treatment-holder
/-- Treatment-direction smoothness: for every `x ∈ [0,1]^d`, the slice
`a ↦ μ_P(a,x)` lies in a Hölder ball of order `α`, radius `M`, on the window. -/
def MuTreatmentHolder {d : ℕ} (P : DoseLaw d) (alpha M t0 eps0 : ℝ) : Prop :=
  ∀ x ∈ cube d, HolderBall1D (fun a => P.mu a x) alpha M (doseWindow t0 eps0)

-- @node: ass:pi-treatment-holder
/-- Treatment-direction smoothness of the conditional treatment density: for every
`x ∈ [0,1]^d`, `a ↦ π_P(a∣x)` lies in a Hölder ball of order `β`, radius `M`, on
the window. -/
def PiTreatmentHolder {d : ℕ} (P : DoseLaw d) (beta M t0 eps0 : ℝ) : Prop :=
  ∀ x ∈ cube d, HolderBall1D (fun a => P.pi a x) beta M (doseWindow t0 eps0)

-- @node: ass:mu-covariate-holder
/-- Covariate-direction smoothness: `x ↦ μ_P(t_0,x)` lies in a Hölder ball of
order `s`, radius `M`, on `[0,1]^d`. -/
def MuCovariateHolder {d : ℕ} (P : DoseLaw d) (s M t0 : ℝ) : Prop :=
  HolderBallND (fun x => P.mu t0 x) s M (cube d)

-- @node: ass:pi-covariate-holder
/-- Covariate-direction smoothness of the conditional treatment density:
`x ↦ π_P(t_0∣x)` lies in a Hölder ball of order `s`, radius `M`, on `[0,1]^d`. -/
def PiCovariateHolder {d : ℕ} (P : DoseLaw d) (s M t0 : ℝ) : Prop :=
  HolderBallND (fun x => P.pi t0 x) s M (cube d)

-- @node: ass:px-holder
/-- Covariate-density smoothness and range: `p_{X,P}` lies in a Hölder ball of order
`s`, radius `M`, on `[0,1]^d`, is NONNEGATIVE (`0 ≤ p_{X,P}` on the cube — the declared
density range `[0,∞)`), and is bounded above by `M`. The nonnegativity conjunct makes
`p_{X,P}` a genuine density object: with it `ENNReal.ofReal (P.px x) = P.px x` on the
cube, so the `PxIsXDensity` tie realizes the ACTUAL `p_{X,P}` density rather than only
its `ofReal` positive part. -/
def PxHolder {d : ℕ} (P : DoseLaw d) (s M : ℝ) : Prop :=
  HolderBallND P.px s M (cube d) ∧
    (∀ x ∈ cube d, 0 ≤ P.px x) ∧     -- @realizes p_{X,P}(0 ≤ p_{X,P} on cube; enforces the declared density range [0,∞), so the `ofReal` `PxIsXDensity` tie realizes the actual nonnegative density object)
    (∀ x ∈ cube d, P.px x ≤ M)

-- @node: ass:baseline-submodel-slack
/-- Nonempty-interior-of-model (strict-slack baseline) existence hypothesis: there
exist a covariate density `p_0` on `[0,1]^d`, a conditional treatment density `q_0`
on `[0,1]`, a slack `η_0 > 0`, and an outcome scale `B_0 ∈ (0,M)`, such that `p_0`
and `q_0` have Hölder norms at most `M - η_0` in the classes required of `p_{X,P}`
and `π_P`, `q_0(a) ≥ c_0 + η_0` on the `ε_0`-window, `p_0 ≤ M - η_0`, and the
constant-zero outcome regression admits a symmetric two-point channel on
`{-B_0, B_0} ⊆ [-M,M]`. Provisional D0.R refinement (`user_approved = false`). -/
def BaselineSubmodelSlack (d : ℕ) (beta s M c0 eps0 t0 : ℝ) : Prop :=
  ∃ (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ) (eta0 B0 : ℝ),
    0 < eta0 ∧ 0 < B0 ∧ B0 < M ∧
    (∀ x ∈ cube d, 0 ≤ p0 x) ∧ (∀ a, 0 ≤ q0 a) ∧
    (∫ x in cube d, p0 x) = 1 ∧ (∫ a in Set.Icc (0 : ℝ) 1, q0 a) = 1 ∧
    HolderBallND p0 s (M - eta0) (cube d) ∧ (∀ x ∈ cube d, p0 x ≤ M - eta0) ∧
    HolderBall1D q0 beta (M - eta0) (doseWindow t0 eps0) ∧
    (∀ a ∈ doseWindow t0 eps0, c0 + eta0 ≤ q0 a)

-- @node: ass:mu-is-regression
/-- **Semantic tie (`μ` is the data regression).** The conditional mean of `Y` given
`(A,X)` under the data law equals `μ_P(A,X)`. This pins the free `mu` field to the
actual law, so `thetaFunctional = ∫ μ_P(t_0,·)·p_{X,P}` is the GENUINE causal value
`E_P[Y(t_0)]` (under consistency + ignorability). Without it `mu` is disconnected from
`dataMeasure`, which permits a vacuous two-point construction (a Dirac data law with
the separation carried only by the free `mu`); enforcing it makes `minimaxRisk` the
true causal minimax risk. -/
def MuIsRegression {d : ℕ} (P : DoseLaw d) : Prop :=
  P.dataMeasure[(fun O => O.Y) |
      MeasurableSpace.comap (fun O : DoseObs d => (O.A, O.X)) inferInstance]
    =ᵐ[P.dataMeasure] (fun O => P.mu O.A O.X)

-- @node: ass:px-is-x-density
/-- **Semantic tie (`p_{X,P}` is the X-marginal density).** The pushforward of the
data law under `X` is `p_{X,P}·(Lebesgue ↾ [0,1]^d)`, tying the free `px` field to the
actual covariate law so `thetaFunctional` integrates `μ` against the genuine `P_X`. -/
def PxIsXDensity {d : ℕ} (P : DoseLaw d) : Prop :=
  P.dataMeasure.map (fun O => O.X)
    = (volume.restrict (cube d)).withDensity (fun x => ENNReal.ofReal (P.px x))

-- @node: ass:pi-is-cond-treatment-density
/-- **Semantic tie / range-normalization (`π_P` is the conditional treatment density).**
The pushforward of the data law under `(A,X)` equals the measure with joint density
`(a,x) ↦ π_P(a∣x)·p_{X,P}(x)` w.r.t. Lebesgue on `[0,1]×[0,1]^d`. Together with
`PxIsXDensity` (the `X`-marginal is `p_{X,P}·Leb`) this pins `π_P(·∣x)` to be the GENUINE
conditional density of `A` given `X = x` under `P` — it is normalized
(`∫_{[0,1]} π_P(a∣x) da = 1` for `P_X`-a.e. `x`, forced by consistency of the joint with
its `X`-marginal) and tied to `dataMeasure`. Without it the `pi` field is disconnected
from `dataMeasure`, so the class `P_{α,β,s}` would be strictly BROADER than the paper
class (an arbitrary `π` field satisfying only the Hölder/positivity atoms, never required
to be the law's actual treatment density). The core symbol `pi_P(a∣x)` is *defined* as the
conditional density of `A` given `X = x` under `P`, so this tie is exactly the note's
stated meaning of `π_P`, not an added restriction. The leading conjunct ENFORCES the
declared density range `0 ≤ π_P` on `[0,1]×[0,1]^d`: with it `ENNReal.ofReal (π_P·p_{X,P})`
genuinely equals `π_P·p_{X,P}` (both factors nonnegative, using `PxHolder`'s `0 ≤ p_{X,P}`),
so the tie realizes the ACTUAL nonnegative conditional treatment density object, not only
its `ofReal` positive part.
@realizes pi_P(`0 ≤ π_P` on `[0,1]×cube` enforcing the declared range `[0,∞)`, AND `P.dataMeasure.map (A,X) = (Leb↾[0,1] ⊗ Leb↾[0,1]^d).withDensity (π_P·p_{X,P})`; together the range-clause + joint-factorization tie pin `pi` to the law's genuine nonnegative conditional treatment density) -/
def PiIsCondTreatmentDensity {d : ℕ} (P : DoseLaw d) : Prop :=
  (∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ cube d, 0 ≤ P.pi a x) ∧   -- @realizes pi_P(0 ≤ pi_P on [0,1]×cube; enforces the declared density range [0,∞), so the `ofReal` joint-density tie realizes the actual nonnegative conditional treatment density)
    P.dataMeasure.map (fun O => (O.A, O.X))
      = ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (cube d))).withDensity
          (fun p => ENNReal.ofReal (P.pi p.1 p.2 * P.px p.2))

-- @node: def:holder-dose-class
/-- The anisotropic Hölder dose-response model class
`P_{α,β,s}(M,c_0,ε_0,t_0)`: the bundle of the member-atom properties, including the three
SEMANTIC TIES (`μ_P` is the data regression, `p_{X,P}` is the X-marginal density, and
`π_P` is the law's conditional treatment density) that make it a genuine CAUSAL class and
pin it to EXACTLY the paper class (so `minimaxRisk` over it is the true causal minimax
risk and `thetaFunctional` is `E_P[Y(t_0)]`, not a free-field artifact, and the class is
not strictly broader than `P_{α,β,s}` through a free `π` field).
(`ass:baseline-submodel-slack` is NOT a member; it is a separate theorem hypothesis.)
The two regime theorems take `(hP : HolderDoseClass … P)`. -/
structure HolderDoseClass (d : ℕ) (alpha beta s M c0 eps0 t0 : ℝ)
    (P : DoseLaw d) : Prop where
  iid : IidSampling P
  consistency : Consistency P
  ignorability : NoUnmeasuredConfounding P
  bdd : BoundedOutcome P M
  interior : InteriorDose t0 eps0
  positivity : LocalPositivity P c0 t0 eps0
  muT : MuTreatmentHolder P alpha M t0 eps0
  piT : PiTreatmentHolder P beta M t0 eps0
  muX : MuCovariateHolder P s M t0
  piX : PiCovariateHolder P s M t0
  pxH : PxHolder P s M
  muReg : MuIsRegression P
  pxDens : PxIsXDensity P
  piCond : PiIsCondTreatmentDensity P

/-! ## Environment S3 — regime constants and frontier sequences

These are the plain real/nat regime parameters and the two frontier sequences. They
enter every theorem as free binders (no measure-theoretic world of their own); their
declared spaces are ENFORCED by the standing well-formedness predicate
`RegimeConstants` below, which is threaded as a hypothesis into every regime
lemma/theorem so that no constant is ever used outside its declared space. The
per-symbol `@realizes` tags below are descriptive; the load-bearing realization is
the conjunction of `RegimeConstants` (for `alpha,beta,s,M,c_0,t_0,epsilon_0`) and the
`minimaxRisk` / `publishedHoifRate` defs (for `R_n,rho_n`).

@env: S3
@realizes alpha(regime constant `alpha : ℝ`, declared space `(0,∞)`; treatment-direction Hölder order)
@realizes beta(regime constant `beta : ℝ`, declared space `(0,∞)`; treatment-density Hölder order)
@realizes s(regime constant `s : ℝ`, declared space `(0,∞)`; covariate-direction Hölder order)
@realizes M(regime constant `M : ℝ`, declared space `(0,∞)`; common Hölder radius and outcome bound)
@realizes c_0(regime constant `c0 : ℝ`, declared space `(0,∞)`; local-positivity floor)
@realizes t_0(regime constant `t0 : ℝ`, declared space `(0,1)`; interior evaluation dose)
@realizes epsilon_0(regime constant `eps0 : ℝ`, declared space `(0,1/2)`; half-width of the evaluation window)
rho_n is realized by `publishedHoifRate` and its nonnegativity theorem.
@realizes R_n(frontier sequence `n ↦ minimaxRisk M n C t0 : ℝ`, declared space `[0,∞)^ℕ`; pointwise minimax MSE, `def:minimax-risk`)

Note: the i.i.d. `n`-sample setup symbol is NOT realized in this S3 regime-constants
block, and neither `publishedHoifRate`/`R_n` nor any other S3 object realizes it — S3
carries no sampling content. Its TWO load-bearing realizers (tagged on their own decls,
NOT here) are: (i) `IidSampling` (S1), whose `Causalean.Stat.IIDSample` conjunct supplies
the mutual independence + identical `P.dataMeasure` law and whose two a.s.-support
conjuncts pin each draw to `{A ∈ [0,1], X ∈ [0,1]^d}`; and (ii) the `n`-fold PRODUCT LAW
`Measure.pi (fun _ : Fin n => P.dataMeasure)` in `minimaxRisk`, the joint law of the
sample over `Fin n → DoseObs d`. (Neither `Consistency` nor `publishedHoifRate` realizes
the sample.)
-/

/-- Standing well-formedness of the S3 regime constants: each lies in its declared
space — `α, β, s, M, c_0 ∈ (0,∞)`, `t_0 ∈ (0,1)`, `ε_0 ∈ (0,1/2)`. This is the
ENFORCING realization cluster for those setup symbols; it is threaded as a
hypothesis into every regime lemma/theorem so the constants are never used outside
their declared spaces. -/
def RegimeConstants (alpha beta s M c0 eps0 t0 : ℝ) : Prop :=
  0 < alpha ∧       -- @realizes alpha(0 < alpha; declared space (0,∞), treatment-direction Hölder order)
    0 < beta ∧      -- @realizes beta(0 < beta; declared space (0,∞), treatment-density Hölder order)
    0 < s ∧         -- @realizes s(0 < s; declared space (0,∞), covariate-direction Hölder order)
    0 < M ∧         -- @realizes M(0 < M; declared space (0,∞), common Hölder radius / outcome bound)
    0 < c0 ∧        -- @realizes c_0(0 < c0; declared space (0,∞), local-positivity floor)
    t0 ∈ Set.Ioo (0 : ℝ) 1 ∧            -- @realizes t_0(t0 ∈ (0,1); declared interior evaluation-point space)
    eps0 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧    -- @realizes epsilon_0(eps0 ∈ (0,1/2); declared interior-radius half-width space)
    InteriorDose t0 eps0                -- @realizes evaluation window(`[t_0-ε_0,t_0+ε_0] ⊆ (0,1)`)

/-! ## Construction `def`s -/

-- @node: def:theta-functional
/-- Identifying partial-mean (backdoor-adjustment) functional
`θ_P(t_0) = ∫_{[0,1]^d} μ_P(t_0,x) p_{X,P}(x) dx` (Lebesgue). Under consistency and
ignorability this equals the causal dose-response value `E_P[Y(t_0)]`. -/
noncomputable def thetaFunctional {d : ℕ} (P : DoseLaw d) (t0 : ℝ) : ℝ :=
  ∫ x in cube d, P.mu t0 x * P.px x

-- @node: def:minimax-risk
/-- Pointwise minimax mean-squared risk
`R_n(C, t_0) = inf_{θ̂_n} sup_{P ∈ C} E_P[(θ̂_n - θ_P(t_0))^2]`.
The infimum ranges over MEASURABLE estimators truncated to `[-M,M]` (the
bounded-estimand range: truncating to the interval containing every `θ_P(t_0)`
never increases MSE and yields the SAME minimax value, while keeping the inner
squared loss bounded by `(2M)^2` under each `n`-fold probability law — so the
`⨆`/`⨅` are well-posed, with no junk-`0` inflation of the converse). -/
noncomputable def minimaxRisk {d : ℕ} (M : ℝ) (n : ℕ)
    (C : DoseLaw d → Prop) (t0 : ℝ) : ℝ :=
  ⨅ est : {est : (Fin n → DoseObs d) → ℝ //
      Measurable est ∧ ∀ s, est s ∈ Set.Icc (-M) M},
      -- @realizes O_1, ..., O_n(estimator domain is the size-`n` sample `Fin n → DoseObs d`)
    ⨆ P : {P : DoseLaw d // C P},
      -- @realizes O_1, ..., O_n(the i.i.d. `n`-sample as the `n`-fold PRODUCT LAW `Measure.pi (fun _ : Fin n => P.dataMeasure)` over `Fin n → DoseObs d` — THIS `minimaxRisk` product law is the second of the two load-bearing realizers of the sample symbol (the first is the `IidSampling` i.i.d. realizer); its factors are mutually independent and identically `P.dataMeasure`-distributed exactly by the `Causalean.Stat.IIDSample` conjunct of `IidSampling`. It is NOT realized by the FOLLOWING `publishedHoifRate` declaration; the tag is placed BEFORE the integral so it attaches to `minimaxRisk`, not to the next decl.)
      ∫ s, (est.1 s - thetaFunctional P.1 t0) ^ 2
        ∂(Measure.pi fun _ : Fin n => (P.1).dataMeasure)

-- @node: def:published-hoif-rate
/-- Published Bonvini–Kennedy benchmark rate
`ρ_n = n^{-2α/(2α+1)} ∨ n^{-2/(1 + d/(4s) + 1/α)}`.
@realizes rho_n -/
noncomputable def publishedHoifRate (n : ℕ) (alpha s : ℝ) (d : ℕ) : ℝ :=
  max ((n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))))
      ((n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha))))

/-- The published-rate frontier sequence is nonnegative, enforcing the declared range
`ρ_n ∈ [0,∞)` of the setup symbol `rho_n`: each branch `(n:ℝ)^(·)` is an `rpow` of the
nonnegative base `(n:ℝ) ≥ 0`, hence `≥ 0`, and the `max` preserves it.
@realizes rho_n -/
theorem publishedHoifRate_nonneg (n : ℕ) (alpha s : ℝ) (d : ℕ) :
    0 ≤ publishedHoifRate n alpha s d :=
  (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans (le_max_left _ _)

end CausalSmith.Stat.DoseResponseMinimax
