/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.SourceCondition
import Causalean.Estimation.NPIV.Primal.Estimator
import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Algebra

/-! # Localized Empirical-Process Regimes

This file bundles the localized empirical-process hypotheses required for the
primal NPIV rate theorem. `LocalizedRegimeBundle` packages one abstract
localized loss class with its sample map, critical-radius certificate, and
radius-uniform boundedness/integrability assumptions. `LocalizedRegimes`
assembles the four concrete bundles used downstream, for `H · F`, `m ∘ F`,
`F`, and `H`, together with the law bridge, realizability, closedness, diameter,
pair-gap interpretation, and peeling-slack fields needed by the class-specific
deviation events and the empirical-process discharge.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A localized regime bundle packages an empirical-process regime with the
critical-radius, boundedness, and integrability hypotheses needed for localized
uniform deviation bounds.

`LocalizedRegimeBundle` bundles one `LocalizedRegime` together with the
critical-radius and integrability hypotheses required by
`localized_uniform_deviation`.

**Radius-uniform boundedness/integrability.**  The fields `rad_bdd`
and `rad_int` are quantified over **all radii `r ≥ δ_n`** (rather than
only `r = δ_n`).  This is needed by the candidate / centred-regulariser
helper `localized_omega_event_for_H`, which applies localized deviation
at the bilinear radius `‖h₁ − h₂‖ + δ_n ≥ δ_n` (proof-sketch line 345).
The other three helpers instantiate `r := δ_n` and only consume the
`r = δ_n` slice. -/
structure LocalizedRegimeBundle (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (δ_n : ℝ) where
  ι : Type
  𝒳 : Type
  [meas_𝒳 : MeasurableSpace 𝒳]
  [nonempty_𝒳 : Nonempty 𝒳]
  [nonempty_ι : Nonempty ι]
  [countable_ι : Countable ι]
  /-- Loss-class family. -/
  F : ι → 𝒳 → ℝ
  /-- Norm/seminorm used for star-hull localization. -/
  norm : (𝒳 → ℝ) → ℝ
  /-- Nonnegativity of the localization norm on the indexed class.  The
      paper's localized concentration inputs use genuine radii/norms; Lean
      keeps the class norm abstract, so this implicit mathematical fact is
      carried explicitly. -/
  norm_nonneg : ∀ i, 0 ≤ norm (F i)
  /-- Sample-side embedding `Ω → 𝒳`. -/
  X : Ω → 𝒳
  X_meas : Measurable X
  F_meas : ∀ i, Measurable (F i)
  regime : LocalizedRegime Ω ι 𝒳 F norm μ X
  crit_le : criticalRadius (regime.ψ n) ≤ δ_n
  crit_pos : 0 < criticalRadius (regime.ψ n)
  crit_fp : regime.ψ n (criticalRadius (regime.ψ n))
              ≤ (criticalRadius (regime.ψ n)) ^ 2
  /-- **Radius-uniform boundedness** of the empirical Rademacher process
      on the zero-out star-hull. Quantified over all radii `r ≥ δ_n`,
      so that `localized_omega_event_for_H` may apply at the bilinear
      radius `‖h₁ − h₂‖ + δ_n`. -/
  rad_bdd : ∀ r : ℝ, δ_n ≤ r →
    ∀ Ssamp : Fin n → 𝒳, ∀ σ : Signs n,
      BddAbove (Set.range fun p : starHullParam ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r p (Ssamp k)|)
  /-- **Radius-uniform integrability** of the empirical Rademacher
      complexity on the zero-out star-hull, quantified over all radii
      `r ≥ δ_n` for the same reason as `rad_bdd`. -/
  rad_int : ∀ r : ℝ, δ_n ≤ r →
    Integrable
      (fun ω : Fin n → Ω =>
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω))
      (Measure.pi (fun _ => μ))

attribute [instance] LocalizedRegimeBundle.meas_𝒳
  LocalizedRegimeBundle.nonempty_𝒳
  LocalizedRegimeBundle.nonempty_ι
  LocalizedRegimeBundle.countable_ι

/-- Bundle of four `LocalizedRegimeBundle` instances, one for each of
the function classes appearing in the EP / centred-regulariser
arguments of `thm:est-trae-rate-theorem`, plus the deterministic
hypotheses (`law_W`, `realizability`, `bounded`, `closedness`) and
per-bundle interpretation fields needed to discharge the EP and
centred-regulariser bounds.

**Observation-space convention.**  Each bundle lives over `(S.𝒲, P_W)`
— the per-observation outcome space and its law — so that the deviation
event produced by `localized_uniform_deviation` is a subset of
`Fin n → S.𝒲` (which is exactly the codomain of the IID-sample joint
observable `fun ω k => sample.Z k ω` in
`Causalean/Stat/Sample/PiTransport.lean`, line 36).  The pullback to
`Ω` happens via `event_pullback_along_iidSample`.

**Sample-size convention.**  The `n` parameter of this structure is
the **sample size at which the localized deviation is applied**, i.e.
`split.n₁ horizon` for fold-A deviations.  Public theorems below take
`regimes : ∀ horizon, LocalizedRegimes ... (split.n₁ horizon) (delta horizon)`,
so `bundle_*.regime.ψ n = bundle_*.regime.ψ (split.n₁ horizon)` is the
fold-A envelope at that horizon.

**Per-bundle interpretation fields** (`interp_*_idx`, `interp_*_norm`,
`interp_*_eval`) link the abstract bundle data `(ι, F, X)` to the
concrete loss attached to each candidate / critic in `TC.H, TC.F`.  Each
interpretation field gives, for every concrete element of the relevant
class, an index into `bundle.ι` whose `bundle.norm`-radius is bounded by
`δ_n` and whose composed value `bundle.F i ∘ bundle.X` evaluates to the
concrete loss at every `w : S.𝒲`.

The deterministic fields do not depend on `n, δ_n`; they are bundled
here so that callers pass a single `LocalizedRegimes` value to the
discharge lemmas. -/
structure LocalizedRegimes
    (S : OperatorSystem Ω μ) (TC : TRAEClasses S)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    {β lambda : ℝ}
    (sc : SourceCondition S β)
    (tb : TikhonovBiasBound S β lambda sc)
    (n : ℕ) (δ_n : ℝ) where
  /-- Regime for the product class `star(H · F)` over `(S.𝒲, P_W)`. -/
  bundle_HF : LocalizedRegimeBundle S.𝒲 P_W n δ_n
  /-- Regime for the moment class `star(m ∘ F)` over `(S.𝒲, P_W)`. -/
  bundle_mF : LocalizedRegimeBundle S.𝒲 P_W n δ_n
  /-- Regime for the critic class `star(F)` over `(S.𝒲, P_W)`. -/
  bundle_F  : LocalizedRegimeBundle S.𝒲 P_W n δ_n
  /-- Regime for the candidate class `star(H)` (centred regulariser),
      over `(S.𝒲, P_W)`. -/
  bundle_H  : LocalizedRegimeBundle S.𝒲 P_W n δ_n
  /-- **Law bridge.**  The observation random variable `S.W` has law
      `P_W` under `μ`.  This is *not* implied by the existing fields of
      `OperatorSystem` or `IIDSample` (the latter only constrains
      `μ.map (sample.Z 0) = P_W`).  Without this hypothesis the helpers
      below cannot equate `∫ ω' f(S.W ω') ∂μ` with the population mean
      `μ_{P_W}[f]` produced by `localized_uniform_deviation`. -/
  law_W : μ.map S.W = P_W
  /-- **Realizability**: the population Tikhonov solution lies in the
      statistical class.  Needed to apply `is_estimator.opt` against
      `tb.h_lambda_star_fun`. -/
  realizability : tb.h_lambda_star_fun ∈ TC.H
  /-- **Boundedness**: a.s. uniform bound on `m(W; f), h(X), f(Z)` over
      `h ∈ TC.H, f ∈ TC.F`.  Needed for the centred-regulariser
      Cauchy–Schwarz step (controls `‖h*‖ + ‖ĥ‖`) and the McDiarmid
      step inside `localized_uniform_deviation`. -/
  bounded :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ᵐ ω ∂μ,
        (∀ f ∈ TC.F, |S.m (S.W ω) f| ≤ B) ∧
        (∀ h ∈ TC.H, |h (S.xOf (S.W ω))| ≤ B) ∧
        (∀ f ∈ TC.F, |f (S.zOf (S.W ω))| ≤ B))
  /-- **Closedness (Hilbert form)**: for every `h ∈ TC.H` there is a
      critic `f ∈ TC.F` whose `L²` lift coincides with the projected
      residual `T(h₀ − h)` *as elements of* `Lp ℝ 2 μ`.

      This is the standard NPIV closedness assumption (Dikkala–Lewis–
      Mackey–Syrgkanis; Chen–Pouzo): the projected residual is realized
      by an element of the critic class.  Needed to convert the empirical
      sup-min comparison into operator-side `weakNorm` expressions in
      step (iii) below — a weak (test-against-`Qbar` inner-product) form
      does not suffice unless `{q_L2 g | g ∈ Qbar}` is total in
      `Qbar_L2`, which is not currently part of the `OperatorSystem`
      interface. -/
  closedness :
    ∀ h, ∀ hh : h ∈ TC.H,
      ∃ f, ∃ hf : f ∈ TC.F,
        S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
          = S.qL2 (TC.F_subset hf)
  /-- **Critic max order.**  The paper states the critic objective with
      `max_{f ∈ F}`.  Since Lean encodes it as `supObjective`, we expose
      the corresponding maximum-order facts explicitly: every feasible
      inner objective is below the max, and the max is attained. -/
  inner_le_supObjective :
    ∀ (split' : OneShotSplit sample) (horizon : ℕ) (ω : Ω),
      ∀ h, h ∈ TC.H → ∀ f, f ∈ TC.F →
        innerObjective S sample split' lambda h f horizon ω
          ≤ supObjective S TC sample split' lambda h horizon ω
  supObjective_attained :
    ∀ (split' : OneShotSplit sample) (horizon : ℕ) (ω : Ω),
      ∀ h, h ∈ TC.H →
        ∃ f, ∃ _hf : f ∈ TC.F,
          supObjective S TC sample split' lambda h horizon ω
            ≤ innerObjective S sample split' lambda h f horizon ω
  /-- **`TC.H` strong-norm diameter cap.**  Upper bound on the
      strongNorm-gap `‖h₁ − h₂‖_{strong}` for every pair `(h₁, h₂) ∈ TC.H × TC.H`.

      This caps the radius scale over which the peeled H-side localized
      deviation operates — `localized_omega_event_for_H` peels dyadically
      across `[δ_n, H_diameter]` to produce a *single* high-probability
      event simultaneously valid for all pairs, with the bilinear
      scaling `4 · (‖h₁ − h₂‖ + δ_n) · critRad` plus an extra peeling
      `√(log(H_diameter/δ_n + 1)/n)` log-factor. -/
  H_diameter : ℝ
  H_diameter_lb : δ_n ≤ H_diameter
  H_diameter_bound :
    ∀ h₁ h₂ (hh₁ : h₁ ∈ TC.H) (hh₂ : h₂ ∈ TC.H),
      S.strongNorm
          (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
        ≤ H_diameter
  /-- **Interpretation: centred-regulariser class.**  For each pair
      `(h₁, h₂) ∈ TC.H × TC.H` there is a `bundle_H`-index whose
      composed evaluation equals the *difference* of squared candidate
      losses, `h₁(S.xOf w)² − h₂(S.xOf w)²`.  The
      `bundle_H.norm`-radius of this index is bounded by the **gap norm**
      `‖h₁ − h₂‖_{L²(P_X)}`, so the localized deviation rate scales with
      `‖h₁ − h₂‖ · δ_n + δ_n²` — matching proof-sketch line 345.

      This is the star-hull-localized form needed for the centred
      regulariser bound (the uniform-radius form `‖h‖_X · δ_n + δ_n²` per
      single `h ∈ TC.H` does not suffice, since the bilinear gap
      `(h*-ĥ)(h*+ĥ)` is what controls `D_n`). -/
  interp_H_idx  : ∀ h₁ h₂, h₁ ∈ TC.H → h₂ ∈ TC.H → bundle_H.ι
  interp_H_norm :
    ∀ h₁ h₂ (hh₁ : h₁ ∈ TC.H) (hh₂ : h₂ ∈ TC.H),
      bundle_H.norm (bundle_H.F (interp_H_idx h₁ h₂ hh₁ hh₂))
        ≤ S.strongNorm
            (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
  interp_H_eval :
    ∀ h₁ h₂ (hh₁ : h₁ ∈ TC.H) (hh₂ : h₂ ∈ TC.H), ∀ w : S.𝒲,
      bundle_H.F (interp_H_idx h₁ h₂ hh₁ hh₂) (bundle_H.X w)
        = (h₁ (S.xOf w)) ^ 2 - (h₂ (S.xOf w)) ^ 2
  /-- **Interpretation: product class `star(H · F)` (single-index form).**
      Each pair `(h, f) ∈ TC.H × TC.F` has a `bundle_HF`-index of radius
      `≤ δ_n` whose composed evaluation equals `h(S.xOf ·) · f(S.zOf ·)`.
      Used in the `h*_λ`-side realizability step where the comparison
      point is fixed and only the critic varies. -/
  interp_HF_idx  : ∀ h, h ∈ TC.H → ∀ f, f ∈ TC.F → bundle_HF.ι
  interp_HF_norm : ∀ h (hh : h ∈ TC.H), ∀ f (hf : f ∈ TC.F),
      bundle_HF.norm (bundle_HF.F (interp_HF_idx h hh f hf)) ≤ δ_n
  interp_HF_eval : ∀ h (hh : h ∈ TC.H), ∀ f (hf : f ∈ TC.F), ∀ w : S.𝒲,
      bundle_HF.F (interp_HF_idx h hh f hf) (bundle_HF.X w)
        = h (S.xOf w) * f (S.zOf w)
  /-- **Foster constant for HF cross-terms.**  An upper bound on the
      bundle radius for the cross-class integrand `(h₁ - h₂)(X) · f(Z)`,
      bilinear in the strong-norm gap `‖h₁ - h₂‖_{strong}` and the
      critic-side scale `δ_n`.  Concretely `HF_pair_const ≤ B` (the
      boundedness constant from `bounded`) by Cauchy–Schwarz with the
      sup-norm bound on `f`. -/
  HF_pair_const : ℝ
  HF_pair_const_nonneg : 0 ≤ HF_pair_const
  /-- **Interpretation: pair-gap form for `star(H · F)` (Foster pair-gap).**
      For each triple `(h₁, h₂, f) ∈ TC.H × TC.H × TC.F`, an index whose
      `bundle_HF.norm`-radius scales bilinearly with
      `HF_pair_const · ‖h₁ - h₂‖_{strong} · δ_n` and whose composed
      evaluation equals the *difference* `(h₁ - h₂)(X) · f(Z)`.

      This is the Foster pair-gap form (Foster–Syrgkanis Lemma 11; TRAE
      paper, Bennett–Kallus–Mao–Newey–Syrgkanis–Uehara 2023): the
      localized deviation on the cross class scales with the *actual*
      L²-norm of the loss-difference at the comparison point, not with
      a fixed star-hull radius.  Required to obtain the cross term
      `δ_n · weak_gap` on the EP RHS (where
      `weak_gap = ‖T(ĥ - h*_λ)‖`); the single-index form alone yields
      only the weaker `(R_b + δ_n) · rate` envelope.

      **Note (consistency with existing helpers).**  The deviation
      helper for HF that consumes this pair-form interpretation is
      `localized_omega_event_for_HF_pair`, which instantiates the
      localized concentration at the *worst-case* radius
      `HF_pair_const · H_diameter · δ_n + δ_n` (mirroring the design of
      `localized_omega_event_for_H`, which uses `H_diameter + δ_n`),
      not at the per-pair radius — strict Foster pair-gap requires
      peeling infrastructure analogous to the H-side.  The pair-gap
      norm field below provides the *interpretation* the EP proof
      consumes; tightening the deviation rate from worst-case to
      per-pair is a separate (peeling) upgrade. -/
  interp_HF_idx_pair :
    ∀ h₁ h₂, h₁ ∈ TC.H → h₂ ∈ TC.H → ∀ f, f ∈ TC.F → bundle_HF.ι
  interp_HF_norm_pair :
    ∀ h₁ h₂ (hh₁ : h₁ ∈ TC.H) (hh₂ : h₂ ∈ TC.H), ∀ f (hf : f ∈ TC.F),
      bundle_HF.norm
          (bundle_HF.F (interp_HF_idx_pair h₁ h₂ hh₁ hh₂ f hf))
        ≤ HF_pair_const *
            S.strongNorm
              (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂)) *
            δ_n
  interp_HF_eval_pair :
    ∀ h₁ h₂ (hh₁ : h₁ ∈ TC.H) (hh₂ : h₂ ∈ TC.H), ∀ f (hf : f ∈ TC.F), ∀ w : S.𝒲,
      bundle_HF.F (interp_HF_idx_pair h₁ h₂ hh₁ hh₂ f hf) (bundle_HF.X w)
        = (h₁ (S.xOf w) - h₂ (S.xOf w)) * f (S.zOf w)
  /-- **L²-norm constant for the moment class** `m(W; f)`: an explicit
      bound `‖m(W;f)‖_{L²(P_W)} ≤ mF_L2_const · ‖f‖_{L²(P_Z)}` for every
      `f ∈ TC.F`, i.e. `√C_m` from the mean-square continuity hypothesis
      `PrimalRateHypotheses.msc`.  Carried at the bundle layer because
      the EP loss-difference L²-norm calculation (Foster Lemma 11
      input) needs it, but the import cycle with `Rate.lean` would
      otherwise force replication.  Bundle norm `interp_mF_norm` is
      kept at `≤ δ_n` (separate from the L²-radius). -/
  mF_L2_const : ℝ
  mF_L2_const_nonneg : 0 ≤ mF_L2_const
  /-- **`TC.F` diameter cap.**  Upper bound on critic L² gaps.  This is a
      formal consequence of the paper's a.s. uniform boundedness
      assumption, exposed here as the radius cap needed by dyadic
      peeling for the `m∘F` and `F²` pair-difference classes. -/
  F_diameter : ℝ
  F_diameter_lb : δ_n ≤ F_diameter
  F_diameter_bound :
    ∀ f₁ f₂ (hf₁ : f₁ ∈ TC.F) (hf₂ : f₂ ∈ TC.F),
      S.strongNorm
          (S.qL2 (TC.F_subset hf₁) - S.qL2 (TC.F_subset hf₂))
        ≤ F_diameter
  /-- Radius lower bound for the `m∘F` pair class at this localization
      scale.  In concrete applications this is discharged by increasing
      the critical-radius floor constant. -/
  mF_pair_radius_lb : δ_n ≤ mF_L2_const * F_diameter
  /-- **Interpretation: moment class `star(m ∘ F)`.** Each `f ∈ TC.F` has
      a `bundle_mF`-index of bundle-radius `≤ δ_n` whose composed
      evaluation equals `S.m · f`. -/
  interp_mF_idx  : ∀ f, f ∈ TC.F → bundle_mF.ι
  interp_mF_norm : ∀ f (hf : f ∈ TC.F),
      bundle_mF.norm (bundle_mF.F (interp_mF_idx f hf)) ≤ δ_n
  interp_mF_eval : ∀ f (hf : f ∈ TC.F), ∀ w : S.𝒲,
      bundle_mF.F (interp_mF_idx f hf) (bundle_mF.X w) = S.m w f
  /-- **Pair interpretation: moment class.**  Difference form
      `m(W; f₁) - m(W; f₂)` with bundle radius controlled by the
      mean-square-continuity constant and the critic L² gap. -/
  interp_mF_idx_pair :
    ∀ f₁ f₂, f₁ ∈ TC.F → f₂ ∈ TC.F → bundle_mF.ι
  interp_mF_norm_pair :
    ∀ f₁ f₂ (hf₁ : f₁ ∈ TC.F) (hf₂ : f₂ ∈ TC.F),
      bundle_mF.norm (bundle_mF.F (interp_mF_idx_pair f₁ f₂ hf₁ hf₂))
        ≤ mF_L2_const *
            S.strongNorm
              (S.qL2 (TC.F_subset hf₁) - S.qL2 (TC.F_subset hf₂))
  interp_mF_eval_pair :
    ∀ f₁ f₂ (hf₁ : f₁ ∈ TC.F) (hf₂ : f₂ ∈ TC.F), ∀ w : S.𝒲,
      bundle_mF.F (interp_mF_idx_pair f₁ f₂ hf₁ hf₂) (bundle_mF.X w)
        = S.m w f₁ - S.m w f₂
  /-- **L²-norm constant for the squared-critic class** `f²`: an explicit
      bound `‖f²‖_{L²(P_W)} ≤ F_L2_const · ‖f‖_{L²(P_Z)}` for every
      `f ∈ TC.F`, equal to the critic sup-norm `B` from `bounded` (since
      `f²(z) ≤ B · |f(z)|`).  Used by Foster's loss-norm input. -/
  F_L2_const : ℝ
  F_L2_const_nonneg : 0 ≤ F_L2_const
  /-- Radius lower bound for the squared-critic pair class at this
      localization scale, discharged from boundedness and the δ floor in
      concrete applications. -/
  F_pair_radius_lb : δ_n ≤ F_L2_const * F_diameter
  /-- **Interpretation: critic class `star(F)`.** Each `f ∈ TC.F` has
      a `bundle_F`-index of bundle-radius `≤ δ_n` whose composed
      evaluation equals `(f ∘ S.zOf)²`. -/
  interp_F_idx  : ∀ f, f ∈ TC.F → bundle_F.ι
  interp_F_norm : ∀ f (hf : f ∈ TC.F),
      bundle_F.norm (bundle_F.F (interp_F_idx f hf)) ≤ δ_n
  interp_F_eval : ∀ f (hf : f ∈ TC.F), ∀ w : S.𝒲,
      bundle_F.F (interp_F_idx f hf) (bundle_F.X w) = (f (S.zOf w)) ^ 2
  /-- **Pair interpretation: squared critic class.**  Difference form
      `f₁(Z)² - f₂(Z)²` with bundle radius controlled by the critic
      sup-norm constant and the critic L² gap. -/
  interp_F_idx_pair :
    ∀ f₁ f₂, f₁ ∈ TC.F → f₂ ∈ TC.F → bundle_F.ι
  interp_F_norm_pair :
    ∀ f₁ f₂ (hf₁ : f₁ ∈ TC.F) (hf₂ : f₂ ∈ TC.F),
      bundle_F.norm (bundle_F.F (interp_F_idx_pair f₁ f₂ hf₁ hf₂))
        ≤ F_L2_const *
            S.strongNorm
              (S.qL2 (TC.F_subset hf₁) - S.qL2 (TC.F_subset hf₂))
  interp_F_eval_pair :
    ∀ f₁ f₂ (hf₁ : f₁ ∈ TC.F) (hf₂ : f₂ ∈ TC.F), ∀ w : S.𝒲,
      bundle_F.F (interp_F_idx_pair f₁ f₂ hf₁ hf₂) (bundle_F.X w)
        = (f₁ (S.zOf w)) ^ 2 - (f₂ (S.zOf w)) ^ 2
  /-- **FS peeling lower bound for HF pair deviations.**  This is the
      localized-concentration lower-bound condition used to absorb the
      per-shell McDiarmid slack in Foster--Syrgkanis Lemma 29. -/
  peeling_slack_HF :
    ∀ K : ℕ, ∀ η : ℝ, 0 < η → η ≤ 1 → 0 < n →
      HF_pair_const * H_diameter * δ_n ≤ δ_n * (2 : ℝ) ^ K →
        bundle_HF.regime.b *
          Real.sqrt (2 * Real.log (2 * ((K : ℝ) + 1) / η) / n)
        ≤ δ_n ^ 2
  /-- **FS peeling lower bound for `m∘F` pair deviations.** -/
  peeling_slack_mF :
    ∀ K : ℕ, ∀ η : ℝ, 0 < η → η ≤ 1 → 0 < n →
      mF_L2_const * F_diameter ≤ δ_n * (2 : ℝ) ^ K →
        bundle_mF.regime.b *
          Real.sqrt (2 * Real.log (2 * ((K : ℝ) + 1) / η) / n)
        ≤ δ_n ^ 2
  /-- **FS peeling lower bound for squared-critic pair deviations.** -/
  peeling_slack_F :
    ∀ K : ℕ, ∀ η : ℝ, 0 < η → η ≤ 1 → 0 < n →
      F_L2_const * F_diameter ≤ δ_n * (2 : ℝ) ^ K →
        bundle_F.regime.b *
          Real.sqrt (2 * Real.log (2 * ((K : ℝ) + 1) / η) / n)
        ≤ δ_n ^ 2



end Primal
end NPIV
end Estimation
end Causalean
