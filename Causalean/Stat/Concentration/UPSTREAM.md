# Stat/Concentration vendoring audit trail

This directory selectively vendors content from
[auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher).
The plan in [.claude/plans/i-just-added-a-rosy-hennessy.md](../../.claude/plans/i-just-added-a-rosy-hennessy.md)
(Phase 4a) describes the rationale.

## Upstream

* Repo: `https://github.com/auto-res/lean-rademacher`
* Pinned commit: `72d28921dc960f47691640fb973303a1be9d13ca`
* Date pulled: 2026-05-08
* Upstream Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
* Causalean Lean toolchain: `leanprover/lean4:v4.29.0-rc3` (mathlib pinned at `bf8875c7`)
* Upstream license: **MIT License** (Copyright (c) 2025 AutoRes) — verified
  in `/tmp/lean-rademacher/LICENSE` of the pinned commit.

Each ported file carries an `Adapted from auto-res/lean-rademacher`
header citing the upstream file and commit, and a per-deviation
`UPSTREAM-DELTA` block listing API drift and porting changes.

## Vendored files (Phase 4a)

| Causalean file                                  | Upstream source                    | Scope                                        |
|----------------------------------------------|------------------------------------|----------------------------------------------|
| `Rademacher/Rademacher.lean`                 | `FoML/Defs.lean`, parts of `FoML/Rademacher.lean` and `FoML/RademacherVariableProperty.lean` | Definitions only: `Signs`, `empiricalRademacherComplexity`, `rademacherComplexity`. Measurability lemmas as needed. |
| `UniformDeviation/BoundedDifference.lean`    | `FoML/BoundedDifference.lean`      | Bounded-difference predicate and the `uniformDeviation_bounded_difference` lemma. |
| `TailBounds/McDiarmid.lean`                  | `FoML/McDiarmid.lean` (+ deps from `Hoeffding.lean`, `MaximalInequality.lean`, `ExpectationInequalities.lean`) | Headline tail bound only: `mcdiarmid_inequality_pos'`. |
| `Rademacher/Symmetrization.lean`             | `FoML/Symmetrization.lean`         | Headline only: `expectation_le_rademacher` (a.k.a. the symmetrization bound on `E[supₐ |Pₙfₐ − Pfₐ|]`). |
| `Covering/Separable.lean`                    | `FoML/SeparableSpaceSup.lean`      | `separableSpaceSup_eq_real`: countable-dense lifting for `sup` over uncountable separable index. |

## Files NOT vendored in Phase 4a

The plan deliberately defers these until a downstream caller demands them:

* `FoML/DudleyEntropy.lean`, `FoML/CoveringNumber.lean`,
  `FoML/PseudoMetric.lean` — entropy-integral rates.
* `FoML/Massart.lean` — finite-class shortcut.
* `FoML/LinearPredictorL1.lean`, `FoML/LinearPredictorL2.lean` —
  application layer; Causalean-flavoured equivalents go in
  `Estimation/CATE/OSL/Modulus/DRLearner.lean`.
* `FoML/MeasurePiLemmas.lean` — pulled in only as inline helpers if
  needed; not as a standalone vendored file.
* `FoML/ForMathlib/Probability/Moments.lean` — assumed already covered
  by Causalean's mathlib pin or inlined locally as a small porting layer.

## Porting policy

* Each ported file's leading docstring documents `UPSTREAM-DELTA:` —
  every non-trivial deviation from the original (mathlib API rename,
  namespace changes, removed unused lemmas, weakened hypotheses, etc.).
* Where upstream proofs do not compile under our Lean/mathlib pin, the
  scaffold leaves a `sorry` with a `-- TODO(port):` comment pointing to
  the upstream file/line. These sorries are filled iteratively after
  scaffolding lands.
* No upstream file is copied verbatim. Even where the proof is
  unchanged, the file lives under the `Causalean.Stat.Concentration`
  namespace and its imports are normalised to Causalean conventions.

## Re-syncing with upstream

When a new commit of `auto-res/lean-rademacher` should be pulled:

1. Update the **Pinned commit** field above.
2. For each vendored file, diff the upstream slice between the old and
   new SHA, and update the corresponding `UPSTREAM-DELTA` block.
3. Re-run `lake build Causalean.Stat.Concentration` and the bridge file
   smoke-test to confirm no regression.
