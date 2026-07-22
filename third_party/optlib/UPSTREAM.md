# Vendored dependency: optlib (KKT / constrained-optimization optimality)

This directory is a **vendored, adapted copy** of the `optlib` project, consumed
by Causalean as the `optlib` Lake dependency for the first-order **KKT
(Karush–Kuhn–Tucker) necessary conditions** under LICQ and affine constraint
qualification (`first_order_neccessary_LICQ`, `first_order_neccessary_LinearCQ`,
and the `first_order_neccessary_general` they reduce to), plus the Farkas' lemma
engine they rest on.

## Upstream

- **Origin:** https://github.com/optsuite/optlib (OptSuite, Peking University)
- **Paper:** "Formalization of Optimality Conditions for Smooth Constrained
  Optimization Problems," arXiv:2503.18821 (March 2025)
- **License:** Apache-2.0 — see `LICENSE` in this directory.

## Why vendored (not a git require)

Upstream pins `leanprover/lean4:v4.13.0` / `mathlib@v4.13.0` (late 2024). AutoID
is on `leanprover/lean4:v4.29.0-rc3` with mathlib pinned to
`bf8875c7dc7162b23cdb881f33cc97caab1c688a`. The ~16-major-version gap makes a
plain `git`-require unbuildable, so the adapted source is carried in-tree and
drift-fixed against AutoID's pin (mirrors the FoML / lean-rademacher vendoring in
`third_party/lean-rademacher`).

## What is vendored (KKT dependency closure only)

Only the transitive closure needed for the KKT theorems is carried — NOT the
optimizer/convergence suite (GD, ADMM, Nesterov, …):

- `Optlib/Convex/ConicCaratheodory.lean`
- `Optlib/Convex/ClosedCone.lean`
- `Optlib/Convex/Farkas.lean`
- `Optlib/Differential/Calculation.lean`
- `Optlib/Differential/Lemmas.lean`
- `Optlib/Optimality/Constrained_Problem.lean`

## Provenance / drift fixes

Adapted from upstream `main` (commit as cloned 2026-07-08). Changes are limited
to toolchain-drift fixes needed to compile against AutoID's mathlib pin; no
mathematical content was altered. Notably, mathlib v4.29 supplies
`tangentConeAt` / `posTangentConeAt` natively, so unfolding-based rewrites were
adjusted to the current definition. Upstream is referenced here only for
provenance and license attribution.
