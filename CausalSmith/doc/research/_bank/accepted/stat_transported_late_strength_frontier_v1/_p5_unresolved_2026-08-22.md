# stat_transported_late_strength_frontier / v1 — P5 findings left unresolved (2026-08-22)

Final referee round: `major_revision`, score 6.8. Five referee passes were run.

## Calibration

The 2026-08-17 bundle also scored `major_revision`, score 7. The paper is therefore at parity on
the referee's number while being materially more correct: the oracle theorem statement now claims
what its Lean declaration proves, all 18 proofs pass the equivalence audit, and roughly a dozen
objects that the old paper used without ever defining are now defined.

## Why the passes stopped

Across passes 2-5 the score moved 7 -> 6.8 -> 7 -> 7 -> 6.8 and the majors recycled the same five
themes with different wording. Each operator edit resolved the named finding and the next pass
objected to the new phrasing, frequently on the affirmative-contribution contract. Two of the
majors in later rounds were introduced by the operator's own added prose (an absence-list
comparison paragraph; a "relaxing any of the three" sentence in a setup section). Continuing was
trading one major for another rather than converging, so the passes were stopped deliberately.

## Unresolved

- **Global structure.** The manuscript leads with formal scaffolding, inhabitation lemmas, and
  repeated assumption restatements before the reader gets a compact view of the contribution. The
  fix is a reorganization — moving auxiliary inhabitation material to the appendix and leading with
  the frontier — which is author-scope, not a prose patch.
- **Related-work depth.** The per-paper comparison names estimand, design, first-stage regime,
  weight status, parameter geometry and guarantee for each benchmark, but the referee wants
  theorem-level specifics (exact guarantee type, whether expected length is studied) for Ma and
  Smucler-Lanni-Masip in particular. This is literature work requiring reading those papers.
- **Assumption motivation.** Domination, the envelope `w <= 2k_n`, `kappa_n <= k_n`, and
  `k_n = o(sqrt n)` are stated and partly motivated in "Reading the design restrictions", but the
  referee wants each condition tied to a concrete empirical setting.
- **Feasible-scope framing.** Sentences such as "turns that benchmark into a feasible finite-cell
  construction" still read broader than the two verified classes, despite three rounds of scoping.
- **Abstract phrasing** of the two information sets.

## Bank edits made during this run

Definitions added for the covariate space, covariate marginal, transport weight as a
Radon-Nikodym derivative, envelope scale, weight second moment, both transported means, the
noncoverage level, the covariate, the critical constant, the joint two-sample law, and the centre
of the witness family. The frontier risk was scoped to positive thresholds and oracle procedures
with the declaration's actual measurability and invariance. The geometry handle was restated as the
bundled condition Lean defines rather than a universally quantified claim, and requires the full
least-favourable witness predicate on the stated radius. The oracle score-inversion theorem
statement gained the oracle-value lower bound and the two-sided fixed-geometry bounds it had been
omitting. A cross-reference target and a `\ne`-for-`e` input were corrected.

Eleven helper lemmas were promoted across three automatic rounds; a fourth round was stopped
deliberately (see the run report). The two lemmas from that fourth round remain in the graph but
are not paper environments, and nothing in the prose depends on them.
