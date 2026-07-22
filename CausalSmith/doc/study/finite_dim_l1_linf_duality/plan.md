## Module: CausalSmith.Substrate.FiniteDimL1LinfDuality
Finite-dim ℓ¹/ℓ∞ duality for min-norm node representation. Nodes hyp = `Function.Injective p`, `β ≤ k`. Main: `l1_repr_eq_sup_dual : sInf (primalNormSet p β) = sSup (dualValSet p β)`.

## Status: COMPLETE — verified this turn from ground truth
- `grep sorry` over the dir: 0 hits.
- LSP diagnostics on Duality/StrongDuality/HahnBanachSetup: all `success:true`, empty items (no errors, no warnings, no sorry-warnings), no failed_dependencies.
- `lean_verify` on `l1_repr_eq_sup_dual`: axioms = {propext, Classical.choice, Quot.sound}; NO `sorryAx`.

## Done (fully proven, all files)
- Basic.lean: MomentSol/primalNormSet/dualValSet defs; dualValSet_nonempty, primalNormSet_bddBelow/_nonneg, momentSol_nonempty (Vandermonde vecMul), primalNormSet_nonempty.
- WeakDuality.lean: repr_identity, dual_le_primal, dualValSet_bddAbove, sSup_dual_le_sInf_primal.
- HahnBanachSetup.lean: coeffPoly/Ev/contrastL/ninf defs + all support lemmas incl. Ev_injective (Vandermonde) and contrastL_le_dual_mul_ninf (the estimate).
- StrongDuality.lean: exists_moment_le_dual_hahn_banach_gap (full sublinear-HB assembly via `exists_extension_of_le_sublinear`), exists_moment_le_dual, sInf_primal_le_sSup_dual.
- Duality.lean: l1_repr_eq_sup_dual, l1_repr_sq_eq_sup_dual_sq (via le_antisymm).

## Remaining
- None (0 sorries).

## Blocked
- None.

## Integrity check
- Statements are the genuine general results: arbitrary distinct nodes + arbitrary β ≤ k, exact identity from Requirement, plus optional squared form and W-nonemptiness. Strong direction proved (not axiom); no weakened/added hypotheses; sets are non-vacuous (dualValSet nonempty via 0, primal nonempty via Vandermonde witness).

## Decisions (retained)
- Strong direction via sublinear Hahn–Banach `exists_extension_of_le_sublinear` on plain `Fin (k+1)→ℝ` (no PiLp/operator-norm). Majorant N x = M·ninf x, M = sSup dualValSet. Contrast functional on `range (Ev p β)`, well-defined by Ev injectivity (Vandermonde). w j = g (Pi.single j 1); sign vector σ gives ∑|wⱼ| = g σ ≤ N σ = M.
