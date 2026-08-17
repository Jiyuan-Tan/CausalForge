## Done

- Promoted proved `Trace`, `Geometry`, `Cover`, and `Score` modules to neutral Causalean, exported them from `Causalean.lean`, and retained compatibility imports.
- The neutral modules prove moving-ball/annulus trace bounds, odd radial powers, finite signed arms, shared-center boxed polynomials, and radial residual-score polynomial `L²` covers uniformly over arbitrary probability laws, including atomic laws.
- Proved `HasPolynomialEmpiricalL2Cover.pullback` with the necessary measurable-class hypothesis and `.monoEnvelope`; `EntropyChaining.lean` now uses the neutral pullback rather than a paper-local duplicate.
- Proved `winsorizedScore_hasVCUniformEntropy` from the named uniform radial cover and `winsorizedScore_hasUniformL2Radius`.
- Added headline curation for `Trace`, `Geometry`, `Cover`, and `Score`; regenerated `doc/library_index.json`, `doc/API.md`, and both embedding views (7724 declarations), with doc/embedding freshness checks green.
- Fresh full Causalean build passed (4518 jobs); task-target CausalSmith build passed (3108 jobs). Source audit found no `sorry`, `admit`, `sorryAx`, `native_decide`, or new axioms in the task modules.
- `#print axioms` for the main trace, pseudo-dimension, cover, score, empirical pullback, and winsorized adapter theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Library search confirmed reuse of existing cover algebra/empirical bridges; Goldberg--Jerrum (1995), Theorem 2.2, was fetched as the primary semialgebraic VC reference.

## Remaining

- None for this substrate requirement; ready for review.

## Blocked

- The global 571-module CausalSmith orphan sweep is not green because of unrelated pre-existing broken/missing staging paths, temporary probe modules, and `EXP_PrognosticDesignAdmissibility_Research/Helpers/ExtremePoints.lean`; the complete Causalean library and all task targets are green.

## Decisions

- Keep empirical pullback/envelope closure in neutral Causalean; pullback replaces external centers by occupied representatives and explicitly assumes measurability because the Bochner-integral `measureL2Dist` triangle bridge requires it.
- Preserve the trace-level squared-distance/Boolean proof and arbitrary-law validity; use no continuity net or boundary-null assumption.
- Treat the pre-existing `Separability.lean` placeholder and unrelated full-tree failures as outside this substrate requirement; axiom auditing confirms they are not dependencies of `winsorizedScore_hasVCUniformEntropy`.
