/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Quantile Treatment Effect identification (backdoor, Firpo 2007)

The literature-facing marginal quantile treatment effect at level `τ ∈ (0,1)` is

    QTE(τ) = F_{Y(1)}^{-1}(τ) − F_{Y(0)}^{-1}(τ),

the difference of the `τ`-quantiles of the two potential-outcome distributions
(`Causalean/PO/Analysis/Quantile.lean`).  The declarations in this file use the
library's totalized generalized-quantile functional, so `qte` and
`qte_backdoor` are stated for every real `τ`; the standard econometric QTE is
the interior-level case.  This file states the backdoor identification of `QTE`
reusing the `POBackdoorSystem` of `PO/ID/Exact/ATE.lean`.
Covariates `X` enter only in identification, not in the estimand (the standard
*marginal* QTE of Firpo 2007).

Identification of the potential-outcome laws uses the weaker distributional
backdoor bundle: consistency, conditional independence `(Y(0),Y(1)) ⊥ T | X`,
and common support `0 < p(x) < 1`.  Outcome integrability and strict overlap
`c ≤ p ≤ 1−c` are not required for the distributional identity.

The key conceptual point — what the quantile infrastructure buys — is that
**QTE is a functional of the two potential-outcome laws**: once those laws are
identified by observable measures `ν₁, ν₀`, the QTE is the difference of their
quantiles.  This is `qte_eq_of_law_eq` (proved).  The remaining content is the
*distributional* identification of each potential-outcome law, the
inverse-probability-weighting / distributional-adjustment generalisation of the
mean-level `ate_backdoor`.

The distributional engine (`ipwDensity`, `ipwLaw`, `cfUnderLaw_eq_ipwLaw`) lives
in `PO/ID/Exact/QTE/DistributionalBackdoor.lean` and is imported here; this file
adds the quantile layer on top.

## Main results
* `POBackdoorSystem.qte` — the QTE estimand `F_{Y(1)}^{-1}(τ) − F_{Y(0)}^{-1}(τ)`.
* `POBackdoorSystem.qte_eq_of_law_eq` — QTE as a functional of the identified
  potential-outcome laws (**proved**).
* `POBackdoorSystem.qte_backdoor` — `QTE(τ) = quantile(ipwLaw 1) τ −
  quantile(ipwLaw 0) τ`, the observable identification: chains `qte_eq_of_law_eq`
  with the (now proven) `cfUnderLaw_eq_ipwLaw` from `DistributionalBackdoor.lean`.
-/

import Causalean.PO.ID.Exact.QTE.DistributionalBackdoor

/-! # Quantile Treatment Effect

This file identifies the totalized generalized-quantile version of the
marginal quantile treatment effect. It defines `qtdQuantile`, the arm-specific
quantile of `Y(d)`, and `qte`, the difference between the treatment and control
quantiles for any real level `τ`.

The theorem `qte_eq_of_law_eq` is the assumption-free functional step: if the
two potential-outcome laws are identified by measures `ν₁` and `ν₀`, then QTE
is the difference of their quantiles. The theorem `qte_backdoor` supplies the
causal backdoor corollary by using `cfUnderLaw_eq_ipwLaw` from
`DistributionalBackdoor` to identify those two laws with observable IPW laws. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The `τ`-quantile of the potential outcome `Y(d)`. -/
noncomputable def qtdQuantile (d : Bool) (μ : Measure P.Ω) (τ : ℝ) : ℝ :=
  S.yVar.cfUnderQuantile S.dVar d μ τ

/-- **Totalized quantile treatment effect** at level `τ`: the difference
between the two generalized quantile functionals, defined for every real `τ`.
Literature-facing quantile effects normally restrict `τ` to the unit interval. -/
noncomputable def qte (μ : Measure P.Ω) (τ : ℝ) : ℝ :=
  S.qtdQuantile true μ τ - S.qtdQuantile false μ τ

/-- The quantile of `Y(d)` is the quantile of the law of `Y(d)`. -/
lemma qtdQuantile_eq_quantile_cfUnderLaw (d : Bool) (μ : Measure P.Ω) (τ : ℝ) :
    S.qtdQuantile d μ τ
      = Causalean.Stat.quantile (S.yVar.cfUnderLaw S.dVar d μ) τ := rfl

/-- **QTE as a functional of the identified potential-outcome laws.** If [the
law of the potential outcome `Y(1)` equals a given observable measure
`ν₁`](hyp:h₁) and [the law of the potential outcome `Y(0)` equals a given
observable measure `ν₀`](hyp:h₀), then for every real quantile level `τ`,
[the totalized quantile treatment effect equals the difference of the
`τ`-quantiles of `ν₁` and `ν₀`](goal). This is the payoff of the quantile
layer: identification of the QTE reduces to distributional identification of
the two potential-outcome laws.

This is the purely measure-theoretic step — it carries **no causal assumptions**,
only the hypotheses `h₁`/`h₀` that the potential-outcome laws equal given
measures.  It is deliberately kept separate from the causal corollary
`qte_backdoor` (which is *not* a duplicate): any route that identifies the two
laws — backdoor, IV, a future design — feeds into this same functional, so the
reduction is stated once and reused. -/
theorem qte_eq_of_law_eq (μ : Measure P.Ω) (τ : ℝ) {ν₁ ν₀ : Measure ℝ}
    (h₁ : S.yVar.cfUnderLaw S.dVar true μ = ν₁)
    (h₀ : S.yVar.cfUnderLaw S.dVar false μ = ν₀) :
    S.qte μ τ = Causalean.Stat.quantile ν₁ τ - Causalean.Stat.quantile ν₀ τ := by
  unfold qte
  rw [S.qtdQuantile_eq_quantile_cfUnderLaw true μ τ,
      S.qtdQuantile_eq_quantile_cfUnderLaw false μ τ, h₁, h₀]

/-- **Backdoor QTE identification.** Under [the ATE backdoor identifying
assumption bundle](hyp:hA), [the totalized generalized-quantile treatment
effect at any real level `τ` equals the difference of the quantiles of the
two observable inverse-probability-weighted outcome laws](goal):

    QTE(τ) = quantile(ipwLaw 1) τ − quantile(ipwLaw 0) τ.

For the usual literature-facing QTE, read this identity at an interior quantile
level `0 < τ < 1`.

This is the causal layer: it discharges the law-identification hypotheses of
`qte_eq_of_law_eq` using the backdoor result `cfUnderLaw_eq_ipwLaw`.  The two are
kept distinct on purpose — `qte_eq_of_law_eq` is the assumption-free functional,
this is the causal corollary that supplies the identified laws. -/
theorem qte_backdoor [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.Assumptions) (τ : ℝ) :
    S.qte P.μ τ
      = Causalean.Stat.quantile (S.ipwLaw true P.μ) τ
        - Causalean.Stat.quantile (S.ipwLaw false P.μ) τ :=
  S.qte_eq_of_law_eq P.μ τ
    (S.cfUnderLaw_eq_ipwLaw hA.toDistributional true)
    (S.cfUnderLaw_eq_ipwLaw hA.toDistributional false)

end POBackdoorSystem

end PO
end Causalean
