## Module: gaussian_kl
Target file: `CausalSmith/Substrate/GaussianKl/Basic.lean`
Namespace: `CausalSmith.Substrate.GaussianKl`. Single file (~190 lines).
Build round 2/10.

## Status: COMPLETE — ready for review
Ground-truth verified this turn:
- `lean_diagnostic_messages` on Basic.lean → `[]` (zero errors, zero warnings).
- Source scan: no `sorry`/`admit`/`axiom`/`native_decide`.
- `lean_verify` on `gaussianKL_eq` → axioms `{propext, Classical.choice, Quot.sound}` only (no sorryAx), no warnings.

## Done (all decls proven, no sorry)
- `gaussianReal_ac_gaussianReal` (v ≠ 0): `gaussianReal m₀ v ≪ gaussianReal m₁ v` via `volume` intermediary (`gaussianReal_absolutelyContinuous`.trans `gaussianReal_absolutelyContinuous'`).
- `rnDeriv_toReal_gaussianReal_ae` (v ≠ 0): `(rnDeriv μ ν ·).toReal =ᵐ[μ] gaussianPDFReal m₀ v / gaussianPDFReal m₁ v` via `rnDeriv_mul_rnDeriv` chain (μ→volume→ν), `rnDeriv_gaussianReal`, `Measure.inv_rnDeriv'`.
- `llr_gaussianReal_ae` (v ≠ 0): `llr =ᵐ[μ] x ↦ (m₀-m₁)*(2x-m₀-m₁)/(2v)`; normalising constants cancel, `Real.log_div`/`log_exp`/`ring`.
- `integrable_llr_gaussianReal` (v ≠ 0): integrable via `memLp_id_gaussianReal` (finite first moment) + affine integrability + `congr` with the a.e. form.
- `integral_llr_gaussianReal` (v ≠ 0): `∫ llr ∂μ = (m₀-m₁)²/(2v)` via `integral_congr_ae` + linearity + `integral_id_gaussianReal`.
- `gaussianKL_eq` (MAIN, 0 < v): `klDiv (gaussianReal m₀ v) (gaussianReal m₁ v) = ENNReal.ofReal ((m₀-m₁)²/(2v))` via `klDiv_of_ac_of_integrable` (the `.real univ` terms cancel for probability measures via the final `simp`). EXACTLY the REQUIRED contract; non-vacuous (`0 < v` satisfiable).

## Remaining
- None. (Optional `gaussianKL_general` two-variance form deliberately skipped per Requirement — `gaussianKL_eq` alone fulfils the goal; not adding a sorry for it.)

## Blocked
- None.

## Decisions
- Helper lemmas use `v ≠ 0`; `gaussianKL_eq` takes `0 < v` and derives `hv0 := hv.ne'`.
- rnDeriv-ratio route (chosen, verified end-to-end): `rnDeriv_mul_rnDeriv` with κ=ν, intermediary volume; `volume.rnDeriv ν` via `Measure.inv_rnDeriv'` of `rnDeriv_gaussianReal m₁ v`.
- Used `InformationTheory.klDiv_of_ac_of_integrable`; `Measure.real univ = 1` handled by final `simp` (no explicit `probReal_univ` needed).
- Skipped `gaussianKL_general` (allowed stretch goal).