# Vendored dependency: lean-rademacher (FoML)

This directory is a **vendored, adapted copy** of the `lean-rademacher` project,
consumed by Causalean as the `FoML` Lake dependency (Rademacher complexity,
McDiarmid / bounded-differences, symmetrization, separable-sup, Dudley entropy;
imported across `Causalean/Stat/Concentration/`, `Causalean/Estimation/`, and
`Causalean/ML/`).

## Upstream

- **Origin:** https://github.com/auto-res/lean-rademacher
- **Paper:** "Lean Formalization of Generalization Error Bound by Rademacher
  Complexity and Dudley's Entropy Integral," arXiv:2503.19605
- **License:** MIT (Copyright (c) 2025 AutoRes) — see `LICENSE` in this directory.

## Why vendored (not a git require)

This copy is **adapted for AutoID's Lean/Mathlib pin** and diverges from upstream:

- Bumped to `leanprover/lean4:v4.29.0-rc3` and pinned Mathlib to
  `bf8875c7dc7162b23cdb881f33cc97caab1c688a` (matching Causalean's `lakefile.toml`).
- Toolchain-drift fixes to `FoML/McDiarmid`, `FoML/MaximalInequality` (Massart),
  and `FoML/DudleyEntropy` to compile against that pin.

Because it diverges, a plain `git`-require against upstream would not build; the
adapted source is carried in-tree instead. Upstream is referenced here only for
provenance and license attribution.

## Provenance

- Vendored from local adaptation at upstream-derived commit
  `ec8acbe8f74bd12a13bff1d737f7fee9d4b2506a`
  ("fill: Codex Job D — close 4 hard McDiarmid + 3 Massart drift errors"),
  plus a working-tree fix to `FoML/DudleyEntropy.lean`.

## Updating

To re-sync with upstream: rebase the AutoID adaptations onto a newer
`auto-res/lean-rademacher` commit, re-fix any toolchain drift against the current
Mathlib pin, and re-copy the source here (excluding `.lake`/`.git`). Keep this
file's provenance section current.
