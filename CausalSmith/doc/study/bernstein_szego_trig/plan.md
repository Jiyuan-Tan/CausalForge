## Module: `CausalSmith.Substrate.BernsteinSzegoTrig`
Deliverable: `Szego.szego_deriv_sq_bound` — for `R : ℝ[X]`, `R.natDegree ≤ β`, `M` with `∀ t, |R(cos t)| ≤ M`: `(d/dt R(cos t))² + β²·R(cos t)² ≤ β²·M²` (sharp Szegő/Bernstein trig inequality, squared form; contract verbatim).

## Ground-truth status this round (round 4 — VERIFIED)
- `lake build CausalSmith.Substrate.BernsteinSzegoTrig.Szego` → **Build completed successfully (8073 jobs)**, zero errors.
- Source scan across all 4 files (`Basic`, `Interp`, `TrigPoly`, `Szego`): **zero** `sorry`/`admit`/`native_decide`/`axiom`.
- `lean_verify` on `szego_deriv_sq_bound`: axioms = `{propext, Classical.choice, Quot.sound}` — **no `sorryAx`**.
- `lean_diagnostic_messages` on `Szego.lean`: empty (no errors/warnings/infos).
- Statement (Szego.lean:255–258) matches the API contract verbatim: `(R : Polynomial ℝ) (β : ℕ) (hβ : R.natDegree ≤ β) (M : ℝ) (hM : ∀ t, |R.eval (Real.cos t)| ≤ M) : ∀ t, (deriv (fun s => R.eval (Real.cos s)) t)^2 + (β:ℝ)^2 * (R.eval (Real.cos t))^2 ≤ (β:ℝ)^2 * M^2`.
- Non-vacuous: `hM` is satisfiable for every `R`, `β` (take any sup-bound of the continuous 2π-periodic `Q`); intended inhabited inputs apply.

## Done (proven, 0 sorries — verified this round)
- `Basic`: `hasDerivAt_cosComp`, `deriv_cosComp`.
- `TrigPoly`: `IsTrigPolyLE.{const,mono,sub}`, `card_zeros_le`, `card_simple_add_double_le` (multiplicity-refined count), `exp_mul_I_injOn_Ico`; all count lemmas generalized to period `[c, c+2π)`.
- `Interp`: `szegoInterp` def, `szegoInterp_self`, `szegoInterp_hasDerivAt`, `szegoInterp_amplitude`, `szegoInterp_abs_le`.
- `Szego`: `szegoInterp_isTrigPolyLE`, `cosComp_isTrigPolyLE`, and the headline `szego_deriv_sq_bound` — fully proven including the final IVT sign-alternation zero-count assembly (the former `hcount` sorry is CLOSED).

## Remaining (open sorries, by file)
- None. All four files build clean with zero sorries.

## Blocked
- Nothing. Deliverable complete.

## Decisions
- Period generalized to `[c, c+2π)` and assembly instantiates `c = u_m` (extremum just left of `t₀`), avoiding any mod-2π reduction.
- Uses multiplicity count (`card_simple_add_double_le`), counting `t₀` as an order-≥2 zero, plus 2β−1 simple IVT zeros from the non-`t₀` gaps — distinct counting was rejected (cubic-inflection counterexample).
- Contract kept verbatim (squared form, `M` any sup-bound). No hypothesis weakening; statement is the genuine general R-of-degree-≤β result.

## Handoff
Module is complete and verified from ground truth this turn. Recommending `review`.