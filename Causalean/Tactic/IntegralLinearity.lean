/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp

/-!
# The `integral_linearity` tactic

**What it does (one sentence): it pushes a Bochner integral through the linear structure of
its integrand — `+`, `-`, `-·`, `•`, multiplication or division by a factor that does not
depend on the integration variable, and a finite sum — discharging the integrability side
conditions itself, first from the local context and then with `fun_prop`.**

This is the Lean spelling of the phrase a causal-inference paper writes without proof:
"by linearity of expectation". The tactic exists because the *mathematics* of such a step is
nil while its Lean cost is not: the library holds 579 uses of the hypothesis-bearing
linearity lemmas across 228 files, and 85% of them hand-supply the integrability witnesses by
name, one `have` block per witness. Those witnesses are exactly what the `@[fun_prop]`
side-condition layer now produces on demand, so the whole step collapses to one word.

## Usage

```lean
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (c : ℝ) :
    ∫ x, (c * f x - g x) ∂μ = c * (∫ x, f x ∂μ) - ∫ x, g x ∂μ := by integral_linearity
```

It is a *normalizer*, not a finisher: it rewrites both sides of the goal into the normal form
above and then closes the goal if what remains is `rfl`. When a goal needs more than
linearity, run it first and continue — `integral_linearity` followed by `ring`, by a domain
`rw`, or by `linarith` is the intended idiom. It fails loudly (naming the normal form) when it
cannot rewrite anything, so it is safe inside `first | … | …`.

## What it deliberately leaves alone

- **`integral_congr_ae` and every `=ᵐ[μ]`-valued step.** Replacing the integrand by an a.e.
  equal one is mathematics — a bridge identity, a consistency assumption, a conditional
  expectation property — and a census of those call sites found 58% of them to be exactly
  that. Prove the a.e. equality, then `rw [integral_congr_ae h]`, then normalize.
- **`integral_const`.** `∫ _, c ∂μ = μ.real univ • c` evaluates an integral rather than
  distributing one, and it drags `μ.real univ` into goals that were about linearity. Follow up
  with `rw [integral_const]` (plus `measure_univ`/`probReal_univ`) where you want the value.
- **Products of two non-constant factors, and integrability that is analytic content.** The
  discharger is `assumption` then `fun_prop`; an a.e.-bounded product (`Integrable.bdd_mul`),
  a Cauchy–Schwarz factor, or an integrability fact gated on a modelling assumption is a step
  to state, not to automate. Where the discharger cannot produce a witness the rewrite simply
  does not fire, and the site keeps its `have`.
- **The merging (`←`) direction.** The set normalizes outward — integrals of combinations
  become combinations of integrals — because that is how 91% of the library's call sites use
  these lemmas. Assembling `∫ f + ∫ g` back into `∫ (f + g)` stays an explicit
  `rw [← integral_add hf hg]`.
- **Set integrals, `lintegral`, and `intervalIntegral`.** Their linearity lemmas live in
  separate namespaces with different side conditions; this tactic is about `∫ x, f x ∂μ`.

## Cost note

`fun_prop` costs roughly 100 ms per call, so the discharger tries `assumption` first: at the
majority of sites the integrability witness is already a hypothesis, and those pay nothing.
-/

open MeasureTheory

namespace Causalean.Tactic

/-- Normalize a Bochner integral through the linear structure of its integrand: `+`, `-`,
negation, `•`, multiplication or division by a factor independent of the integration variable,
and finite sums all move outside the `∫`, and the integrability side conditions are discharged
from the local context or by `fun_prop`.

A normalizer rather than a finisher — it closes the goal only when linearity alone suffices;
otherwise follow it with `ring`, a domain rewrite, or `linarith`. It does not touch `=ᵐ[μ]`
steps (`integral_congr_ae` is mathematics, not plumbing), does not evaluate `∫ _, c ∂μ`
(`integral_const`), and does not run in the merging direction. Fails with a message when it
can rewrite nothing, so it composes with `first`. See `doc/TACTICS.md`. -/
syntax (name := integralLinearity) "integral_linearity" : tactic

macro_rules
  | `(tactic| integral_linearity) =>
    `(tactic| first
        | simp (disch := first | assumption | fun_prop) only
            [MeasureTheory.integral_add, MeasureTheory.integral_add',
              MeasureTheory.integral_sub, MeasureTheory.integral_sub',
              MeasureTheory.integral_neg, MeasureTheory.integral_neg',
              MeasureTheory.integral_finsetSum,
              MeasureTheory.integral_smul, MeasureTheory.integral_const_mul,
              MeasureTheory.integral_mul_const, MeasureTheory.integral_div]
        | fail "integral_linearity: nothing to normalize.\n\
            The normal form is: `+`, `-`, negation, `•`, a factor independent of the \
            integration variable, and finite sums all outside the `∫`. Either the goal is \
            already in that form, or the integrand's linear structure is hidden (unfold or \
            `integral_congr_ae` first), or an integrability side condition could not be \
            discharged by `assumption` or `fun_prop` (state it as a `have`).")

end Causalean.Tactic
