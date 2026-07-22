# converging_together_clt — build ledger (round 2, VERIFIED COMPLETE)

Module: `CausalSmith.Substrate.ConvergingTogetherClt` (2 files). Both compile with ZERO sorries
and ZERO diagnostics. Verified this turn by `lake build CausalSmith.Substrate.ConvergingTogetherClt.Diagonal`
(success, 2950 jobs) + `lean_diagnostic_messages` (empty) + `lean_verify` on all four public decls.

## Done (all proven, axiom-clean)
Every public theorem verifies with only `propext`, `Classical.choice`, `Quot.sound` — **no `sorryAx`**.
- `CharFunBound.lean`:
  - `norm_cexp_mul_I_sub_cexp_mul_I_le (a b : ℝ) : ‖cexp(a·I) − cexp(b·I)‖ ≤ |a−b|`. PROVEN.
  - `tendsto_charFun_sub_le` — L¹ bound `‖charFun(μ.map S) t − charFun(μ.map T) t‖ ≤ |t|·∫|S−T|`. PROVEN.
  - `tendsto_charFun_sub_le_L2` — L² Cauchy–Schwarz upgrade `≤ |t|·√(∫(S−T)²)`. PROVEN.
  - (private helpers `tendsto_charFun_sub_le_ae`, `integral_abs_le_sqrt_integral_sq` — PROVEN.)
- `Diagonal.lean`:
  - `lawPM` / `lawPM_coe` — ProbabilityMeasure bundling wrapper. PROVEN.
  - `tendsto_inDistribution_of_l2_approx` — the converging-together theorem (diagonal ε/3 via
    charFun + Lévy continuity). PROVEN, axiom-clean.
  - `clt_of_l2_approx` — standard-normal corollary `G = gaussianReal 0 1`. PROVEN, axiom-clean.

## Remaining
- None. No open sorries in either file.

## Blocked
- None.

## Decisions
- API split CharFunBound (analytic) / Diagonal (Lévy + diagonal) retained — both <300 lines.
- H2 stated in ℝ≥0∞ via `ENNReal.ofReal` + `Filter.limsup … atTop`: faithful rendering of
  Billingsley's `∀ε>0 ∃M ∀m≥M, limsupₙ ∫|S−T|² ≤ ε`, canonical mathlib limsup type. NOT laundering.
- Diagonal proof route = metric/`eventually` (δ→ε via `eventually_lt_of_limsup_lt` + real L² bound
  + per-row charFun convergence from H1). Avoids limsup arithmetic side-conditions.
- Upstream `Clt.Prokhorov` carries a `sorry` warning during build, but it is NOT in our dependency
  path: `lean_verify` confirms our four public theorems depend only on the 3 standard axioms.
- Integrity: statements are the genuine general real-RV results; hypotheses H1/H2 are satisfiable
  and load-bearing (non-vacuous); `lawPM` hides no difficulty. No laundering.

## Verification log (this turn)
- `grep sorry/admit/native_decide/axiom`: none in module files.
- `lean_diagnostic_messages` CharFunBound + Diagonal: both `[]`.
- `lake build …Diagonal`: success, 2950 jobs (only warning = upstream Prokhorov sorry).
- `lean_verify`: tendsto_inDistribution_of_l2_approx, clt_of_l2_approx, tendsto_charFun_sub_le,
  tendsto_charFun_sub_le_L2 — all `{propext, Classical.choice, Quot.sound}`, no warnings.