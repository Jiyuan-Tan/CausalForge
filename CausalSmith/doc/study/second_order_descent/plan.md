## Status (round 2 — ground truth verified)
`CausalSmith/Substrate/SecondOrderDescent/Basic.lean` (224 lines, module
`CausalSmith.Substrate.SecondOrderDescent.Basic`). lean-lsp diagnostics: **empty** (no
errors, no warnings, no `sorry`). `lean_verify` on `second_order_upper_bound`,
`second_order_descent_gap_min`, `second_order_descent_gap_half`: axioms are exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## Done (all proven, zero sorries)
- `descentStep M c T := if M = 0 then T else min T (c / M)` (noncomputable def)
- `descentStep_of_eq_zero`, `descentStep_of_pos`, `descentStep_mem_Icc`
- `second_order_upper_bound` — core Taylor/Lagrange bound
- `first_order_upper_bound` — `deriv (deriv f) ≤ 0` corollary
- `second_order_descent_gap` — raw `≥ c*s − (M/2)*s²` + feasibility
- `second_order_descent_gap_min` — `≥ (c/2) * min T (c/M)` for `M > 0`
- `first_order_descent_gap` — `≥ c*T` for `M = 0`
- `second_order_descent_gap_half` — uniform `≥ (c/2) * descentStep M c T` + feasibility

## Remaining
None.

## Blocked
Nothing.

## Decisions
- Hypotheses (faithful to Requirement's "may assume"): `hT : 0 ≤ T`,
  `hf : ContDiffOn ℝ 2 f (Icc 0 T)`, `hf0 : DifferentiableAt ℝ f 0`,
  `hM : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ M`, `hslope : deriv f 0 ≤ -c`, `0 < c`, `0 ≤ M`.
- `hf0 : DifferentiableAt ℝ f 0` is a genuine bridge, not laundering: Mathlib's Taylor
  expansion produces the one-sided `derivWithin f (Icc 0 t) 0`; the Requirement's statements
  use two-sided `deriv f 0`. Rejected alternative: restate everything with `derivWithin`
  (unusable for the intended caller).
- Core proof: `taylor_mean_remainder_lagrange_iteratedDeriv` at `n = 1` on `Icc 0 t`
  (shrink `hf` via `.mono (Icc_subset_Icc le_rfl ht.2)`), `taylorWithinEval_succ` +
  `taylor_within_zero_eval` + `iteratedDerivWithin_one` to evaluate the order-1 polynomial,
  `iteratedDeriv_succ`/`iteratedDeriv_one` for `iteratedDeriv 2 f = deriv (deriv f)`,
  then `nlinarith`.
- `M = 0` corollaries generalized to `deriv (deriv f) ≤ 0` (strictly stronger, still true).
- Both the raw and closed forms exposed, per the Requirement's "expose both".
- Objective-agnostic: no `varEnvelope`/`dirModulus`/`sSup` extraction (caller-side, per Non-goals).

## Non-vacuity
Hypotheses are jointly satisfiable by e.g. `f = fun x => -x` (`T = 1`, `M = 0`, `c = 1`) and
by `f = fun x => x^2 - x` (`M = 2`, `c = 1`), so every theorem has inhabited inputs.

## Next
Ready for review; nothing to fill.