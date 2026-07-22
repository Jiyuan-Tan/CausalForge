## Done

- Round-7 ground truth: direct `Jacobian.lean` compilation and `lake build CausalSmith.Substrate.AffinePolynomialImageDimension` both exit 0; neutral Lean sources contain zero `sorry`, `admit`, custom `axiom`, or `sorryAx` occurrences.
- `CoordinateRing.lean` proves the vanishing-ideal/kernel identification, canonical coordinate-ring equivalence, and bridge from the existing chain predicate to coordinate-ring Krull dimension.
- `Transcendence.lean` proves finite-type-domain dimension = trdeg, exact polynomial-image-closure dimension from trdeg, and the surjective-presentation upper certificate.
- `Jacobian.lean` proves the chain-rule/degree algebra, genuine characteristic-zero nonzero-minor independence criterion, and exact dimension from matching trdeg or presentation upper bounds.
- `AxiomAudit.lean` compiles. Neutral imports contain no LiNGAM research path, `ExactID`, `EID_Lingam`, or `Helpers/` dependency.
- Library search found no packaged multivariable Jacobian criterion. Stacks 10.116.1 confirms finite-type-domain dimension = trdeg; arXiv:1202.4301 confirms the characteristic-zero Jacobian criterion. Direct arXiv source download was retried but DNS was unavailable.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Keep the coordinate subalgebra as the canonical `MvPolynomial.aeval` range.
- Keep the genuine nonzero polynomial Jacobian-minor criterion over `ℂ`; exactness uses a separate reusable upper certificate rather than assuming image dimension.
- Use zero filler subagents because the verified module is complete and ready for review.