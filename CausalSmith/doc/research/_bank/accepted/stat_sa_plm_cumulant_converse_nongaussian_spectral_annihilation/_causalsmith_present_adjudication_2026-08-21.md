# Adjudication record — sa_plm presentation, 2026-08-21

## Bundled-environment statement audits (four reseeds)

The P1 statement audit flagged four locked environments as drifting from Lean. All four are
operator-frozen environments that deliberately **bundle several adjacent Lean declarations**,
and the auditor is shown only the single mapped declaration — so it reports the remaining
bundled quantities as undelivered. Every complaint had the same shape: "the listed Lean
counterpart only delivers X, while the paper body also defines Y and Z."

The four frozen bodies were **byte-identical** to the ones verified decl-by-decl on
2026-08-20 (sha1 prefixes: `def:model-parameters` 72f51a21f147 / 1219 bytes;
`def:plm-model` 75e9daa7425c / 1047; `def:jms-eligibility-quantities` acb536e34eb4 / 719;
`def:contour-functional` ab5bca316313 / 595). Nothing about the bodies changed — only the
audit's view of them did. This was therefore a re-verification, and no frozen body was
rewritten to satisfy the auditor.

Mapping, quantity to backing declaration:

- **def:model-parameters** — `Parameters`, `fold0`, `fold1`, `EtaSubGaussian`, `XiSubGaussian`
  (Basic.lean); `empiricalMean` (Helpers/SineScore.lean:25); the N(m,v) Gaussian-law
  convention maps to Mathlib's `ProbabilityTheory.gaussianReal`, used at Basic.lean:421.
- **def:plm-model** — `Model`, `Obs`, `eta`, `xi`, `barG`, `barQ`, `covariateLaw` (Basic.lean).
- **def:jms-eligibility-quantities** — `jmsA1`, `jmsB1`, `jmsA2`, `jmsB2`
  (Helpers/JmsComparator.lean).
- **def:contour-functional** — `contourFunctional`, `contourCount`, and the transforms the body
  bundles: `treatmentMGF`, `nuisanceMGF`, `residualMGF`, `outcomeResidualTransform`
  (Helpers/Transforms.lean).

Caveat recorded with the mapping: two first-pass name guesses (`empiricalMean`,
`gaussianReal`) initially returned zero hits and were chased rather than assumed to be gaps —
both were wrong guesses, not missing Lean.

Reseeded via four per-entry edits with stored keys untouched; `equivalence_cache.json` is
56/56 faithful.

## Algorithm box for the estimator

`def:adaptive-contour-estimator` was re-kinded to `algorithmv` and moved from
"Appendix C: certified construction and executable correspondence" to
"Main fixed-separation result", immediately before the theorem it serves; the certified
arithmetic realization stays in Appendix C. The rendered box carries 10 numbered steps and
**displays N_j** by its argument-principle formula together with theta-hat as the clipped
midpoint — closing the reader-facing gap where the paper divided by N_j without ever saying
what it equals. The re-rendered body passed the statement audit ("all frozen envs faithful to
Lean"), which retires the not-machine-audited disclosure shipped with the interim N_j display
in commit da75d506.

## Notation repairs made to converge P1

- `M` re-homed from `def:zero-instrument` (where M is a generic bound variable) to
  `thm:known-zero-instrument`, the first environment that defines M as the MGF.
- `\mathsf{contourBank}` replaced by the already-defined bank data `B`.
- `searchRadius(p) = R_1` named at its home in `def:contour-bank-handle`.
- `D_KL` named as the Kullback-Leibler divergence in-lemma.
- The log-MGF derivative functional rewritten as `kappa_k(eta)`, after confirming Lean's
  `kappaEta` is literally that real part of the k-th derivative at zero — a notation change,
  not a restatement.

## Residue

Three placement advisories stand: `def:contour-bank-handle` sits in Appendix C while
`thm:exact-contour-identification`, `lem:population-numerator-envelope` and
`thm:common-experiment-dichotomy` each use it **in their statements** from main-body sections.
Same class as the estimator move landed here, and the natural next one.
