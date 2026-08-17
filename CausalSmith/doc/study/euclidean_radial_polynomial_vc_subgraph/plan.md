## Done

- Promoted proved `Trace`, `Geometry`, `Cover`, and `Score` modules to neutral Causalean and exported them from `Causalean.lean`.
- Proved arbitrary-law moving-ball/annulus trace bounds, odd radial powers, finite signed arms, shared-center boxed polynomials, and radial residual-score polynomial L² covers.
- Proved measurable `HasPolynomialEmpiricalL2Cover.pullback`, `.monoEnvelope`, and `winsorizedScore_hasVCUniformEntropy`; removed the paper-local pullback duplicate.
- Corrected the pullback API to require measurability because the Bochner-integral distance lacks the needed triangle law for arbitrary nonmeasurable functions.
- Added headline curation and regenerated the index, API tables, and both embedding views (7724 declarations); freshness checks pass.
- Fresh full Causalean build passed (4518 jobs), CausalSmith root build passed (3627 jobs), and task-target build passed (3108 jobs).
- Task-source audit found no `sorry`, `admit`, `sorryAx`, `native_decide`, or new axioms.
- `#print axioms` for the main trace, pseudo-dimension, covering, residual-score, empirical-pullback, and winsorized-adapter theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Library search confirmed reuse of existing covering algebra and empirical bridges; [Goldberg--Jerrum (1995)](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/GJ-ML95.pdf), Theorem 2.2, was checked as the primary semialgebraic VC reference.

## Remaining

- None for this substrate requirement; ready for review.

## Blocked

- The global 571-module CausalSmith orphan sweep remains non-green solely because of unrelated pre-existing missing staging paths, temporary probes, and `EXP_PrognosticDesignAdmissibility_Research/Helpers/ExtremePoints.lean`. The complete Causalean library, CausalSmith root graph, and every task target are green.

## Decisions

- Keep empirical pullback/envelope closure in neutral Causalean; replace external centers with occupied representatives and state the necessary measurability hypothesis explicitly.
- Preserve squared-distance finite-trace/Boolean reasoning and arbitrary-law validity; use no continuity net or boundary-null assumption.
- Treat the pre-existing `Separability.lean` placeholder and unrelated orphan-sweep failures as outside this substrate; axiom auditing confirms they are not dependencies of `winsorizedScore_hasVCUniformEntropy`.