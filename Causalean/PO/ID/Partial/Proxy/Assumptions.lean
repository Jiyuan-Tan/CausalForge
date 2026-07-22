/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Proxy.Setup
import Mathlib.Probability.Independence.Conditional

/-!
# Proximal partial-identification assumption bundles

Three weakened assumption bundles, one per partial-identification theorem
of Ghassami-Shpitser-Tchetgen Tchetgen (2024):

* `WBasedAssumptions`   — outcome-confounding-proxy bounds (Theorem 1).
* `ZBasedAssumptions`   — treatment-confounding-proxy bounds (Theorem 2).
* `TwoProxyAssumptions` — two conditionally independent invalid proxies
                            (Theorem 3).

All three weaken the exact-identification bundle
`POProximalSystem.Assumptions` by dropping the completeness condition (and,
for the W- and Z-only cases, dropping the unused proxy's assumptions).

The bridge function `h` (W side) and bridge function `q` (Z side) are bundled
as fields, exactly as in the exact-ID bundle. The treatment-side bridge `q`
satisfies `E[q(Z, A, X) | A, X, U] = p(U | ¬A, X) / p(U | A, X)`. In the
general standard-Borel setting the right-hand side is a Radon-Nikodym
derivative whose existence is non-trivial; we package it as a user-supplied
measurable function `likelihoodRatio_swapA` together with its defining
relation.
-/


namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POProximalSystem

variable {P : POSystem}
  {γ_X γ_Z γ_W γ_U : Type*}
  [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
  [MeasurableSpace γ_W] [MeasurableSpace γ_U]

/-! ## W-only bundle (Theorem 1) -/

/-- Assumption bundle for the W-proxy partial-identification theorem
(Ghassami-Shpitser-Tchetgen Tchetgen 2024, Thm 1).

Drops `proxy_YZ`, `completeness`, and Z-related fields from the exact-ID bundle.

Econometric reading of the assumptions.  We observe treatment `A`, an outcome
`Y`, covariates `X`, and an *outcome-confounding proxy* `W` (a noisy view of the
unmeasured confounder `U`).  Identification is only partial because the
treatment-confounding proxy `Z` and the completeness ("the proxies are rich
enough to pin down `U`") condition of the exact theorem are dropped.  The
bundle then assumes: (i) **consistency** — the observed `Y` is the potential
outcome at the realized treatment; (ii) **latent ignorability** (`latent_exch`)
— conditional on the latent `U` and `X`, treatment is as good as random,
`Y(a) ⟂ A | (U, X)`; (iii) **proxy exclusion** (`proxy_WA`, paper Assumption 1)
— the outcome proxy `W` is independent of treatment given `(U, X)`, so `W`
influences `A` only through `U`; (iv) **outcome bridge** (`h`, `bridge`, paper
Assumption 2) — there exists a function `h(A, W, X)` reproducing the latent
outcome regression, `E[Y - h(A, W, X) | A, U, X] = 0`, and (`h_nonneg`) it can
be taken non-negative; (v) **bounded outcome** (`Y_bdd_below`/`Y_bdd_above`) —
`Y` is essentially bounded, which clamps the reported interval to
`[essinf Y, essup Y]`; (vi) **strong overlap** (`overlap_strong`) — positivity
`P(A = a | U, X) > 0`, needed to lift single-arm a.e. equalities globally.

Fields:
- `consistency`     : the ambient PO system satisfies POSystem.Consistency.
- `latent_exch`     : Y(a) ⟂ A | (U, X) for each a ∈ {0, 1}.
- `proxy_WA`        : W ⟂ A | (U, X). (Paper Assumption 1.)
- `h`               : outcome-side bridge function `Bool × γ_W × γ_X → ℝ`.
- `h_nonneg`        : `h` is pointwise nonneg (paper Assumption 2: a non-negative
                       bridge is posited to exist; not derived from `Y ⊆ [0, ∞)`).
- `bridge`          : E[Y - h(A, W, X) | σ(A, U, X)] = 0 a.s. (Paper Assumption 2,
                       latent-side encoding.)
- `Y_bdd_below` / `Y_bdd_above`  : essential bounds on Y, used to clamp the
                                    bound to `[essinfY, essupY]`.

The finite essential upper bound makes this a finite-support variant of the
Ghassami-Shpitser-Tchetgen Tchetgen Theorem 1 assumptions, stronger than the
paper's nonnegative-support plus sup-clamp formulation. -/
structure WBasedAssumptions
    (S : POProximalSystem P γ_X γ_Z γ_W γ_U)
    (μ : Measure P.Ω := P.μ) [IsFiniteMeasure μ]
    [StandardBorelSpace P.Ω] where
  /-- Consistency axiom for the ambient PO system. -/
  consistency : POSystem.Consistency P
  /-- Latent exchangeability: Y(a) ⟂ A | (U, X) for each treatment level. -/
  latent_exch : ∀ a : Bool,
    CondIndepFun S.σ_UX S.σ_UX_le (S.YofA a) S.A μ
  /-- Outcome-proxy assumption: W ⟂ A | (U, X). -/
  proxy_WA : CondIndepFun S.σ_UX S.σ_UX_le S.W S.A μ
  /-- Outcome bridge function `h : Bool × γ_W × γ_X → ℝ`. -/
  h : Bool × γ_W × γ_X → ℝ
  /-- `h` is measurable. -/
  measurable_h : Measurable h
  /-- `h` is pointwise non-negative.  This is the paper's Assumption 2, which
  *posits the existence* of a non-negative outcome bridge `h`.  (It is not a
  consequence of `Y ≥ 0`: even when `Y ⊆ [0, ∞)`, a bridge solving the integral
  equation need not itself be non-negative, so this is assumed, not derived.) -/
  h_nonneg : ∀ x, 0 ≤ h x
  /-- Latent bridge equation: `E[Y - h(A, W, X) | σ(A, U, X)] = 0` a.s. -/
  bridge : (μ[fun ω => S.Y ω - h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) =ᵐ[μ] 0
  /-- `h(A, W, X)` is integrable. -/
  integrable_h : Integrable (fun ω => h (S.A ω, S.W ω, S.X ω)) μ
  /-- For each `a`, `h(a, W, X)` is integrable (used by the upper-envelope step). -/
  integrable_h_arm : ∀ a : Bool, Integrable (fun ω => h (a, S.W ω, S.X ω)) μ
  /-- `Y` is integrable. -/
  integrable_Y : Integrable S.Y μ
  /-- Each `Y(a)` is integrable. -/
  integrable_YofA : ∀ a : Bool, Integrable (S.YofA a) μ
  /-- Essential lower bound on `Y` (paper: `Y ⊆ [0, +∞)`, generalised). -/
  Y_bdd_below : ∃ M : ℝ, ∀ᵐ ω ∂μ, M ≤ S.Y ω
  /-- Essential upper bound on `Y` used by the trivial-bound clamp. This finite
  bound is a formal strengthening of the paper's displayed nonnegative-support
  convention, which writes the upper clamp with `sup Y`; the theorem here uses
  a real-valued essential upper bound instead of an extended-real top element. -/
  Y_bdd_above : ∃ M : ℝ, ∀ᵐ ω ∂μ, S.Y ω ≤ M
  /-- Strong overlap: for each arm `a`, `P(A = a | U, X) > 0` a.e., expressed
  as: every σ_UX-measurable set that meets `{A = a}` in a null set is itself null.
  Required for lifting single-arm a.e.-equalities to global a.e.-equalities. -/
  overlap_strong : ∀ a : Bool, ∀ s : Set P.Ω, MeasurableSet[S.σ_UX] s →
      μ (s ∩ {ω | S.A ω = a}) = 0 → μ s = 0

/-! ## Z-only bundle (Theorem 2) -/

/-- Assumption bundle for the Z-proxy partial-identification theorem
(Thm 2). Drops `proxy_WAZ`, `completeness`, and W-related fields.

Econometric reading of the assumptions.  Here the available proxy is a
*treatment-confounding proxy* `Z` (a noisy view of `U` on the treatment side);
the outcome proxy `W` and the completeness condition of the exact theorem are
dropped, so identification is only partial.  The bundle assumes: (i)
**consistency**; (ii) **latent ignorability** `Y(a) ⟂ A | (U, X)`; (iii) **proxy
exclusion** (`proxy_YZ`) — `Z ⟂ Y | (A, U, X)`, so `Z` is informative about `U`
but has no direct effect on the outcome; (iv) **treatment bridge** (`q`,
`bridge_q`, paper Assumption 5) — there exists a non-negative function
`q(Z, A, X)` whose latent conditional expectation reproduces the
treatment-stratum likelihood ratio `p(¬A | U, X) / p(A | U, X)`; (v) **strong
overlap** (`overlap_strong`) — positivity `P(A = a | U, X) > 0`.  Unlike the
W-only bundle, `Y` need NOT be bounded (paper Remark 5: the Z-bound sits inside
`[inf Y, sup Y]` automatically), but three explicit `L¹` integrability fields
are added to cover finiteness gaps that strict overlap alone does not entail.

The bridge `q` satisfies the **probability-ratio** form
`E[q(Z, A, X) | A, X, U] = p(¬A | U, X) / p(A | U, X)` on the support
`{p(A | U, X) > 0}`. We avoid Radon-Nikodym derivatives and instead bundle
the ratio as a user-supplied σ_UX-measurable function `likelihoodRatio_swapA`,
defined operationally by the change-of-measure equation
`E[𝟙{A=a} | σ_UX] · likelihoodRatio_swapA a =ᵐ E[𝟙{A=¬a} | σ_UX]`
(see `likelihoodRatio_swapA_spec`). On the support of `E[𝟙{A=a} | σ_UX]`
this divides to `likelihoodRatio_swapA a = p(¬a | U, X) / p(a | U, X)`.

This is the codebase's q convention; it differs from the paper's
density-ratio q `p(U | ¬a, X) / p(U | a, X)` by a factor of
`stratumOddsRatio` (= `π_{1-a}(X)/π_a(X)`). Both conventions yield the same
public observable bound; the prob-ratio form is preferred here because it
avoids RN derivatives.

Note: `Y` boundedness is not required (Remark 5 of the paper — the Z-bound
sits inside `[inf Y, sup Y]` automatically via the inner conditional
expectation).

Paper Assumption 3 positivity (`p(A = a | U, X) > 0`) is bundled as
`overlap_strong`.

Three integrability fields cover finiteness gaps that paper Assumption 3
(strict overlap) does not entail:
* `integrable_likelihoodRatio_swapA` — `L = p(¬a|U,X)/p(a|U,X)` is in L¹.
* `integrable_condExpYofA_mul_L`     — the L¹-pairing `μ[Y(a)|σ_UX] · L`
  used inside the upper/lower bridge-substitution chain (Theorem 2).
* `integrable_condExpY_mul_q`        — the L¹-pairing `μ[Y|σ_AZX] · q(Z,a,X)`
  used inside the σ_AZX-conditional envelope step of the same chain
  (Theorem 2, paper "all integrals are finite" convention; Remark 5
  forbids a Y-clamp). -/
structure ZBasedAssumptions
    (S : POProximalSystem P γ_X γ_Z γ_W γ_U)
    (μ : Measure P.Ω := P.μ) [IsFiniteMeasure μ]
    [StandardBorelSpace P.Ω] where
  /-- Consistency axiom for the ambient PO system. -/
  consistency : POSystem.Consistency P
  /-- Latent exchangeability: Y(a) ⟂ A | (U, X) for each treatment level. -/
  latent_exch : ∀ a : Bool,
    CondIndepFun S.σ_UX S.σ_UX_le (S.YofA a) S.A μ
  /-- Treatment-proxy assumption: Z ⟂ Y | (A, U, X). -/
  proxy_YZ : CondIndepFun S.σ_AUX S.σ_AUX_le S.Y S.Z μ
  /-- Treatment-side bridge function `q : γ_Z × Bool × γ_X → ℝ`. -/
  q : γ_Z × Bool × γ_X → ℝ
  /-- `q` is measurable. -/
  measurable_q : Measurable q
  /-- `q` is non-negative (paper Assumption 5). -/
  q_nonneg : ∀ x, 0 ≤ q x
  /-- Probability-ratio `p(¬a | U, X) / p(a | U, X)`, σ_UX-measurable,
  supplied by the user (see structure docstring). -/
  likelihoodRatio_swapA : Bool → P.Ω → ℝ
  measurable_likelihoodRatio_swapA :
    ∀ a, Measurable[S.σ_UX] (likelihoodRatio_swapA a)
  /-- Defining change-of-measure equation
  `E[𝟙{A=a} | σ_UX] · likelihoodRatio_swapA a =ᵐ E[𝟙{A=¬a} | σ_UX]`.
  On the support of `E[𝟙{A=a} | σ_UX]`, this gives
  `likelihoodRatio_swapA a = p(¬a | U, X) / p(a | U, X)`. -/
  likelihoodRatio_swapA_spec : ∀ a : Bool,
    (fun ω => (μ[Set.indicator {ω' | S.A ω' = a} (fun _ => (1:ℝ)) | S.σ_UX]) ω
              * likelihoodRatio_swapA a ω)
      =ᵐ[μ]
    (μ[Set.indicator {ω' | S.A ω' ≠ a} (fun _ => (1:ℝ)) | S.σ_UX])
  /-- `likelihoodRatio_swapA a` is integrable. Paper Assumption 3 (strict
  overlap) does not produce a uniform bound on `L`, so finiteness of its
  expectation is surfaced as a separate explicit assumption. -/
  integrable_likelihoodRatio_swapA : ∀ a : Bool,
    Integrable (likelihoodRatio_swapA a) μ
  /-- Product `μ[Y(a) | σ_UX] · L` is integrable. The bundle does not
  give Y or `μ[Y(a)|σ_UX]` boundedness in the Z-only theorem (Remark 5),
  so L¹·L¹ closure is not automatic; we surface it explicitly. -/
  integrable_condExpYofA_mul_L : ∀ a : Bool,
    Integrable (fun ω => (μ[S.YofA a | S.σ_UX]) ω
                          * likelihoodRatio_swapA a ω) μ
  /-- Product `μ[Y | σ_AZX] · q(Z, a, X)` is integrable. Required by the
  σ_AZX-conditional envelope step inside the bridge-substitution chain
  (Theorem 2). The bundle does not give Y or `μ[Y|σ_AZX]` boundedness
  (Remark 5 forbids a Y-clamp), so L¹·L¹ closure is not automatic; we
  surface it explicitly per the paper's "all integrals are finite"
  convention. -/
  integrable_condExpY_mul_q : ∀ a : Bool,
    Integrable (fun ω => (μ[S.Y | S.σ_AZX]) ω
                          * q (S.Z ω, a, S.X ω)) μ
  /-- Product `Y · q(Z, a, X)` is integrable. Required by the
  bridge-substitution arm chain (Theorem 2): we factor
  `μ[Y · q | σ_AUX] = μ[Y|σ_AUX] · μ[q|σ_AUX]` under proxy_YZ and tower
  back to `∫_s Y · q dμ`, both of which need this L¹ closure. The bundle
  does not give Y boundedness (Remark 5 forbids a Y-clamp), so L¹·L¹
  closure is not automatic; we surface it explicitly per the paper's
  "all integrals are finite" convention. -/
  integrable_Y_mul_q : ∀ a : Bool,
    Integrable (fun ω => S.Y ω * q (S.Z ω, a, S.X ω)) μ
  /-- Treatment-side bridge equation:
  `E[q(Z, a, X) | σ(A, U, X)] = likelihoodRatio_swapA a` a.s. on `{A = a}`. -/
  bridge_q : ∀ a : Bool,
    (μ[fun ω => q (S.Z ω, a, S.X ω) | S.σ_AUX])
      =ᵐ[μ.restrict {ω | S.A ω = a}]
    likelihoodRatio_swapA a
  /-- For each `a`, `q(Z, a, X)` is integrable. -/
  integrable_q : ∀ a : Bool, Integrable (fun ω => q (S.Z ω, a, S.X ω)) μ
  /-- `Y` is integrable. -/
  integrable_Y : Integrable S.Y μ
  /-- Each `Y(a)` is integrable. -/
  integrable_YofA : ∀ a : Bool, Integrable (S.YofA a) μ
  /-- Strong overlap: `p(A = a | U, X) > 0` (paper Assumption 3 positivity).
  Same condition as `WBasedAssumptions.overlap_strong`. -/
  overlap_strong : ∀ a : Bool, ∀ s : Set P.Ω, MeasurableSet[S.σ_UX] s →
      μ (s ∩ {ω | S.A ω = a}) = 0 → μ s = 0

/-! ## Two-proxy bundle (Theorem 3) -/

/-- Assumption bundle for the two-proxy partial-identification theorem
(Thm 3). Both proxies `W` and `Z` are present, but the strong exclusion
restrictions `W ⟂ A | (U, X)` and `Y ⟂ Z | (A, U, X)` may FAIL — that is
the "invalid proxy" angle. The only proxy-side conditional independence
required is `proxy_WZ_indep : W ⟂ Z | (A, X, U)` (paper Assumption 6); in
particular, no `W ⟂ A | (U, X)` requirement is bundled. Both bridge
functions `h` and `q` are kept as fields, with their latent-side defining
equations.

`h` is required to be pointwise non-negative (`h_nonneg`); this is the paper's
Assumption 2 (a non-negative bridge is posited to exist — it is not forced by
`Y ⊆ [0, ∞)`). The treatment-side bridge `q` is also non-negative (paper
Assumption 5).

Same `likelihoodRatio_swapA` packaging convention as in
`ZBasedAssumptions` (probability-ratio convention, defined operationally
by the change-of-measure spec — no RN derivatives), and the same two
explicit integrability fields (`integrable_likelihoodRatio_swapA`,
`integrable_condExpYofA_mul_L`) covering finiteness gaps not implied by
strict overlap.

This is a finite-support variant of the Ghassami-Shpitser-Tchetgen Tchetgen
Theorem 3 assumptions: the finite essential upper bound on `Y` is stronger than
the paper's nonnegative-support plus sup-clamp formulation. -/
structure TwoProxyAssumptions
    (S : POProximalSystem P γ_X γ_Z γ_W γ_U)
    (μ : Measure P.Ω := P.μ) [IsFiniteMeasure μ]
    [StandardBorelSpace P.Ω] where
  /-- Consistency axiom for the ambient PO system. -/
  consistency : POSystem.Consistency P
  /-- Latent exchangeability: Y(a) ⟂ A | (U, X) for each treatment level. -/
  latent_exch : ∀ a : Bool,
    CondIndepFun S.σ_UX S.σ_UX_le (S.YofA a) S.A μ
  /-- Conditional independence of the two proxies given `(A, U, X)`
  (paper Assumption 6). -/
  proxy_WZ_indep : CondIndepFun S.σ_AUX S.σ_AUX_le S.W S.Z μ
  /-- Outcome-side bridge function. -/
  h : Bool × γ_W × γ_X → ℝ
  /-- `h` is measurable. -/
  measurable_h : Measurable h
  /-- `h` is pointwise non-negative.  This is the paper's Assumption 2, which
  *posits the existence* of a non-negative outcome bridge `h`.  (It is not a
  consequence of `Y ≥ 0`: even when `Y ⊆ [0, ∞)`, a bridge solving the integral
  equation need not itself be non-negative, so this is assumed, not derived.) -/
  h_nonneg : ∀ x, 0 ≤ h x
  /-- Outcome bridge equation `E[Y - h(A,W,X) | σ(A,U,X)] = 0`. -/
  bridge_h : (μ[fun ω => S.Y ω - h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) =ᵐ[μ] 0
  /-- `h(A, W, X)` is integrable. -/
  integrable_h : Integrable (fun ω => h (S.A ω, S.W ω, S.X ω)) μ
  /-- For each treatment arm `a`, `h(a, W, X)` is integrable. -/
  integrable_h_arm : ∀ a : Bool, Integrable (fun ω => h (a, S.W ω, S.X ω)) μ
  /-- Treatment-side bridge function. -/
  q : γ_Z × Bool × γ_X → ℝ
  /-- `q` is measurable. -/
  measurable_q : Measurable q
  /-- `q` is non-negative (paper Assumption 5). -/
  q_nonneg : ∀ x, 0 ≤ q x
  /-- Treatment-stratum likelihood ratio (see `ZBasedAssumptions` for spec). -/
  likelihoodRatio_swapA : Bool → P.Ω → ℝ
  measurable_likelihoodRatio_swapA :
    ∀ a, Measurable[S.σ_UX] (likelihoodRatio_swapA a)
  /-- Defining change-of-measure equation for the probability-ratio convention:
  `E[𝟙{A=a} | σ_UX] · likelihoodRatio_swapA a =ᵐ E[𝟙{A≠a} | σ_UX]`. -/
  likelihoodRatio_swapA_spec : ∀ a : Bool,
    (fun ω => (μ[Set.indicator {ω' | S.A ω' = a} (fun _ => (1:ℝ)) | S.σ_UX]) ω
              * likelihoodRatio_swapA a ω)
      =ᵐ[μ]
    (μ[Set.indicator {ω' | S.A ω' ≠ a} (fun _ => (1:ℝ)) | S.σ_UX])
  /-- `L` is integrable. Paper Assumption 3 does not yield a uniform bound. -/
  integrable_likelihoodRatio_swapA : ∀ a : Bool,
    Integrable (likelihoodRatio_swapA a) μ
  /-- Product `μ[Y(a) | σ_UX] · L` is integrable (used in arm-swap step). -/
  integrable_condExpYofA_mul_L : ∀ a : Bool,
    Integrable (fun ω => (μ[S.YofA a | S.σ_UX]) ω
                          * likelihoodRatio_swapA a ω) μ
  /-- Treatment-side bridge equation:
  `E[q(Z, a, X) | σ(A, U, X)] = likelihoodRatio_swapA a` a.s. on `{A = a}`. -/
  bridge_q : ∀ a : Bool,
    (μ[fun ω => q (S.Z ω, a, S.X ω) | S.σ_AUX])
      =ᵐ[μ.restrict {ω | S.A ω = a}]
    likelihoodRatio_swapA a
  /-- For each `a`, `q(Z, a, X)` is integrable. -/
  integrable_q : ∀ a : Bool, Integrable (fun ω => q (S.Z ω, a, S.X ω)) μ
  /-- Product `h(a, W, X) · q(Z, a, X)` is integrable. Required by the
  bridge-substitution identity and the envelope chain (separate L¹ for `h`
  and `q` does not imply L¹ for the product). -/
  integrable_hq_arm : ∀ a : Bool,
    Integrable (fun ω => h (a, S.W ω, S.X ω) * q (S.Z ω, a, S.X ω)) μ
  /-- `Y` is integrable. -/
  integrable_Y : Integrable S.Y μ
  /-- Each `Y(a)` is integrable. -/
  integrable_YofA : ∀ a : Bool, Integrable (S.YofA a) μ
  /-- Essential lower bound on `Y`. -/
  Y_bdd_below : ∃ M : ℝ, ∀ᵐ ω ∂μ, M ≤ S.Y ω
  /-- Essential upper bound on `Y`. This finite bound is a formal strengthening
  of the paper's displayed nonnegative-support assumption plus the formal
  `sup Y` clamp; the theorem here exposes a real-valued essential upper bound. -/
  Y_bdd_above : ∃ M : ℝ, ∀ᵐ ω ∂μ, S.Y ω ≤ M
  /-- Strong overlap: same condition as `WBasedAssumptions.overlap_strong`. -/
  overlap_strong : ∀ a : Bool, ∀ s : Set P.Ω, MeasurableSet[S.σ_UX] s →
      μ (s ∩ {ω | S.A ω = a}) = 0 → μ s = 0

end POProximalSystem

end PO
end Causalean
