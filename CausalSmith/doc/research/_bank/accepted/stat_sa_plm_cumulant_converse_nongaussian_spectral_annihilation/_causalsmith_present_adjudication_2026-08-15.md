# PRESENT P1 adjudication — 2026-08-15

This record documents the accepted-bank refinements made while constructing the
P1 formal layer for `stat_sa_plm_cumulant_converse` under the specification
`nongaussian_spectral_annihilation`.

## Statement audit

The post-P1 statement audit reconciled the frozen natural-language bodies of the
following environments with their accepted Lean declarations:

- `def:gaussian-class`
- `def:jms-ace-class`
- `def:zero-instrument`
- `def:contour-functional`
- `def:minimax-risks`
- `def:sine-estimator`
- `def:local-gaussian-handle`
- `def:contour-bank-handle`
- `def:adaptive-contour-estimator`
- `lem:zero-localization`
- `prop:jms-ace-alignment`
- `thm:common-experiment-dichotomy`
- `lem:l1-nuisance-zero-free`
- `thm:local-to-gaussian-partial-benchmarks`

The audit reported every frozen environment faithful to Lean. These edits
clarify exposition and notation ownership; they do not strengthen the accepted
mathematical claims.

## Notation adjudication

The P1 notation scan found no unresolved notation homes, duplicate formal-layer
blocks, missing placements, extra placements, definition-order problems, or
content-hash mismatches. In particular:

- the residual variables `eta` and `xi` are introduced by
  `def:non-gaussian-class`;
- the zero instrument `M(z)` is introduced by `def:zero-instrument`; and
- the bank handles `Name(x)` and `Name_+(x)`, which are confined to the
  certified-construction appendix, are introduced by
  `def:contour-bank-handle`.

The itemized frozen body for `lem:zero-localization` was checked against
`AutoID/Counterexamples/Helpers/Cumulant.lean`: under `EtaSubGaussian` and
`CumulantSeparation`, it states the existence of a zero of the moment-generating
function within `zeroRadius`. The Gaussian-class frozen body begins with its
definitional equality so dependency ordering is explicit.

## Verification and scope

The resulting P1 layer contains 105 verified blocks. The generated notation
review reports `ok: true` in one iteration with no advisories, and the P1 state
has no hard-gate failures. The outline checkpoint remains deliberately pending;
P2--P5 and the later manual equation/equivalence review have not been run.
