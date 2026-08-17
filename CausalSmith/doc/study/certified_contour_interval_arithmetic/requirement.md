# Substrate requirement: certified_contour_interval_arithmetic

## Goal

Build the smallest reusable certified-real and outward-rounded rational interval layer needed to turn finite contour statistics into total, measurable computations with certified error bounds.

## Provides (API contract)

- A certified name for a real number, represented by nested rational intervals containing the value, with effectively vanishing width.
- Sound outward-rounded interval evaluation for addition, subtraction, multiplication, division away from zero, `exp`, `log` on positive intervals, and real powers on their valid domain.
- A refinement theorem: for every positive rational target width, refinement terminates with an enclosing interval of at most that width.
- A finite-mesh enclosure theorem: a supplied Lipschitz bound on a continuous real- or complex-valued function on a circle turns rational node enclosures into a sound enclosure of its infimum, supremum, and contour integral, with error bounded by mesh error plus node-enclosure widths.
- Borel measurability of the resulting finite refinement, tie-breaking, and enclosure outputs as functions of the finite sample values.

The exposed API should be strong enough to instantiate a structure named `CertifiedIntervalArithmetic` without mentioning the spectral PLM paper or its estimator.

## Statement / milestones

1. Define rational closed intervals, containment, width, and outward-rounded primitive operations; prove soundness and width monotonicity.
2. Define certified real names and a refinement operation; prove termination to every positive rational tolerance.
3. Add sound interval extensions for `exp`, `log`, and real powers on explicitly certified domains.
4. Prove the finite uniform-mesh enclosure bound for Lipschitz functions on a circle, including contour integrals represented by a deterministic quadrature rule plus an explicit discretization error.
5. Package finite searches and least-index tie breaking, proving totality and Borel measurability.

## Standard reference

Validated numerics / interval arithmetic in the sense of Moore--Kearfott--Cloud,
*Introduction to Interval Analysis*, together with standard certified-real (nested
rational enclosure) representations from computable analysis.  The circle mesh and
quadrature estimates are the elementary Lipschitz error bounds for the trapezoidal
rule on a periodic parametrization; Mathlib's rational/real order, continuity,
measurability, `exp`, `log`, finite-search, and finite-sum APIs are the intended
formal primitives.

## Intended reuse

This discharges external interface X-1 of research run `stat_sa_plm_cumulant_converse / nongaussian_spectral_annihilation`. Its consumers are the contour-bank construction, the certified adaptive contour estimator, the fixed-separation C/n MSE theorem, and the common-experiment summary theorem. The paper-specific Lipschitz envelopes, stopping margins, empirical transforms, selector, and risk proof remain local and must not be moved into this substrate.

## May assume / must derive

- MAY assume Mathlib rational/real order topology, continuity and measurability results, finite sums, elementary `exp`/`log` inequalities, and standard deterministic quadrature identities.
- MUST derive the enclosure soundness, effective refinement/termination, circle-mesh error bounds, total finite search, and measurability. Do not encode these conclusions as axioms, typeclass fields without constructors, or `sorry`.
- If the full transcendental interval layer is too large, prove a genuinely reusable smaller layer and report the exact irreducible missing theorem. Do not replace certified computation by a noncomputable existence witness.

## Non-goals

The PLM estimator, empirical-process bounds, winding-count correctness, and the paper's dyadic contour-bank argument are out of scope.

## Target module

Temporary staging under `CausalSmith.Substrate.CertifiedContourIntervalArithmetic`; final placement is chosen by the study coordinator.
