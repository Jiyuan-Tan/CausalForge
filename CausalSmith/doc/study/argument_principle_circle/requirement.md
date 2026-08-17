# Substrate requirement: argument_principle_circle

## Goal

Formalize the circle argument principle and the Rouché/homotopy invariance consequence needed to certify a logarithmic-derivative contour count.

## Provides (API contract)

- For a complex function analytic on a neighborhood of a closed disk and nonzero on its boundary circle, the normalized contour integral of `f' / f` equals the finite number of zeros strictly inside the disk, counted with analytic multiplicity.
- The normalized integral is therefore a nonnegative integer and is positive when the disk contains a zero.
- If two analytic functions are joined by the straight-line homotopy and every intermediate function is nonzero on the boundary circle, their normalized logarithmic-derivative contour counts agree. A standard Rouché inequality may be supplied as a corollary.

The API may use Mathlib's native zero divisor/order and circle-integral notions, but should expose a compact wrapper sufficient to instantiate `ArgumentPrincipleInterface`.

## Statement / milestones

1. Establish local logarithmic-derivative residues from Mathlib analytic order/multiplicity.
2. Reduce a closed-disk function to finitely many interior zeros and sum those residues around the circle.
3. Identify the normalized circle integral with the multiplicity sum and derive integrality, nonnegativity, and positivity.
4. Prove invariance under a boundary-zero-free analytic homotopy; derive the straight-line/Rouché form.

## Standard reference

The argument principle and Rouché's theorem for positively oriented circles, as in
Conway, *Functions of One Complex Variable*, or Ahlfors, *Complex Analysis*.  The
formal development should specialize these classical results to Mathlib's analytic
order/multiplicity, Cauchy integral, Jensen formula, meromorphic divisor, and circle
integral APIs listed below.

## Intended reuse

This discharges external interface X-2 of research run `stat_sa_plm_cumulant_converse / nongaussian_spectral_annihilation`. It is consumed by the finite translated-dyadic contour-bank lemma and the pilot/population winding-count comparison. The paper-specific Jensen bound, dyadic pigeonhole construction, Blaschke/Harnack estimates, estimator, and minimax argument remain local.

## May assume / must derive

- MAY assume Mathlib complex differentiability, analytic order, meromorphic divisors, Cauchy and circle integrals, Jensen's formula, compactness, and finite-set machinery.
- MUST derive the argument-principle equality and homotopy/Rouché result with no axioms, `sorry`, `admit`, or `native_decide`.
- If Mathlib lacks one decisive residue or winding bridge, isolate and prove the smallest general lemma possible; if a genuine attempt shows that bridge requires a major new theory, stop with the exact statement and dependency trace.

## Non-goals

General contour homology, arbitrary rectifiable Jordan curves, meromorphic functions with poles, and the PLM application are out of scope. A positively oriented circle and analytic functions suffice.

## Known building blocks

- `Mathlib.Analysis.Complex.CauchyIntegral`
- `Mathlib.Analysis.Complex.JensenFormula`
- `Mathlib.Analysis.Analytic.Order`
- `Mathlib.Analysis.Meromorphic.Divisor`
- Mathlib circle integrals and compactness of closed disks/circles

## Target module

Temporary staging under `CausalSmith.Substrate.ArgumentPrincipleCircle`; final placement is chosen by the study coordinator.
