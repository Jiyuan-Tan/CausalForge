## Module
`CausalSmith.Substrate.FiniteEntropyCore.Core` — single file at
`CausalSmith/Substrate/FiniteEntropyCore/Core.lean` (162 lines). Imports:
`Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`, `Mathlib.Data.Fintype.BigOperators`.
Namespace `CausalSmith.Substrate.FiniteEntropyCore`, `variable {α : Type*} [Fintype α]`.

## Done (ALL declarations proven; verified from ground truth this round)
- `entropy (p : α → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)` — noncomputable def. ✅
- `entropy_def` — `@[simp]` rfl unfolding lemma. ✅
- `entropy_nonneg` — `Finset.sum_nonneg` + `Real.negMulLog_nonneg`. ✅
- `negMulLog_sub_mul_log_le` — per-coordinate Gibbs lever (case split x=0 / x>0,
  uses `Real.log_le_sub_one_of_pos`, `Real.log_inv`, `Real.log_mul`, `field_simp`). ✅
- `entropy_le_log_card` — HEADLINE max-entropy bound; `Finset.sum_le_sum` of the lever
  + telescoping RHS `n·(1/n)−1 = 0` using `∑ p i = 1`. ✅
- `entropy_const_eq_log_card` — sharpness: uniform pmf attains the bound. ✅

## Verification performed this turn (ground truth)
- `grep -rn "sorry"` over FiniteEntropyCore dir: NO matches.
- lean-lsp diagnostics on `Core.lean`: `{"success":true,"items":[]}` — zero errors, zero warnings.
- `lean_verify` on `entropy_le_log_card`: axioms = `[propext, Classical.choice, Quot.sound]`,
  NO `sorryAx` — the headline is genuinely proven, not laundered.

## Remaining
- None. Zero open sorries.

## Blocked
- None.

## Decisions
- Entropy defined on arbitrary `p : α → ℝ` (no pmf gate in the def); hypotheses live in
  lemmas — matches API contract, avoids laundering.
- Statements generic over `Fintype α` (NOT `Fin M`/`Bool`), per reuse mandate.
- Max-entropy bound proven from `Real.log_le_sub_one_of_pos` (elementary Gibbs), NOT by
  citing an unproven Jensen/max-entropy axiom — as the Requirement mandates.
- Non-vacuity certified by `entropy_const_eq_log_card` (uniform pmf is a real inhabited
  input that attains the bound), and pmf hypotheses are satisfiable.
- `entropy_const_eq_log_card` uses explicit binder `fun _ : α => ...` to avoid a stuck
  Fintype metavariable.
- Confirmed `Mathlib.Algebra.BigOperators.Order` does NOT exist in this toolchain; the two
  imports above suffice.

## Status
COMPLETE — ready for review. All four API-contract items present, compile clean, no sorries,
no laundering, non-vacuous (sharpness witnessed).