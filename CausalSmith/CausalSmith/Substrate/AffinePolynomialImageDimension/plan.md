## Done

- Round-7 ground truth: `lake env lean .../Jacobian.lean` and `lake build CausalSmith.Substrate.AffinePolynomialImageDimension` both exit 0; the neutral module contains zero `sorry`, `admit`, custom `axiom`, or `sorryAx` occurrences.
- `CoordinateRing.lean` proves `polynomialImageClosure_vanishingIdeal`, `polynomialImageClosure_coordinateRing`, and `affineZariskiDimension_iff_coordinateRingKrullDim` against the existing chain predicate.
- `Transcendence.lean` proves the finite-type-domain Krull-dimension/trdeg theorem, `polynomialImageClosure_dimension_of_trdeg`, and the surjective-presentation upper certificate.
- `Jacobian.lean` proves the polynomial chain rule and derivative-degree core, the genuine characteristic-zero nonzero-minor algebraic-independence criterion, and exact image-closure dimension from matching trdeg or surjective-presentation upper bounds.
- `AxiomAudit.lean` compiles; the neutral import scan contains no LiNGAM research path, `ExactID`, `EID_Lingam`, or `Helpers/` dependency.
- Library search found no packaged multivariable Jacobian criterion. Primary-source check confirmed finite-type domain dimension = trdeg in Stacks 10.116.1 and the characteristic-zero Jacobian criterion in Mittmann--Saxena--Scheiblechner, arXiv:1202.4301; direct arXiv source download was retried and failed only because DNS is unavailable.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Preserve the concrete coordinate subalgebra as the `MvPolynomial.aeval` range and bridge it canonically to the closure coordinate ring.
- Preserve the genuine nonzero polynomial Jacobian-minor hypothesis over `ℂ`; exactness uses a separate, reusable matching upper certificate rather than assuming image dimension.
- Use zero filler subagents this round because the verified module is complete and ready for review.
