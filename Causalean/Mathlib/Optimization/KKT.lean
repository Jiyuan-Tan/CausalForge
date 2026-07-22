/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# First-order KKT conditions (thin re-export of `Optlib.Optimality.Constrained_Problem`)

Thin re-export of the vendored `optlib` first-order Karush–Kuhn–Tucker (KKT)
necessary conditions and the Farkas' lemma engine they rest on. Original from
`optsuite/optlib` (Apache-2.0), paper "Formalization of Optimality Conditions
for Smooth Constrained Optimization Problems," arXiv:2503.18821 — see
`third_party/optlib/UPSTREAM.md` for full provenance, license, and the drift
fixes applied to compile against AutoID's Mathlib pin.

The optlib symbols (`first_order_neccessary_general`,
`first_order_neccessary_LICQ`, `first_order_neccessary_LinearCQ`, and the
`Farkas` lemma) live in the root namespace and are re-imported here for
unqualified use, following the same convention as the vendored `FoML`
re-exports; deliberately no `abbrev` aliases (which would make the root-namespace
symbols ambiguous).
-/

import Optlib.Optimality.Constrained_Problem
import Optlib.Convex.Farkas

/-! # First-order KKT optimality conditions

This file re-exports optlib's first-order Karush–Kuhn–Tucker necessary
conditions for a smooth constrained optimization problem — the classical
statement that at a local minimizer satisfying a constraint qualification there
exist Lagrange multipliers for which the Lagrangian is stationary, the
inequality multipliers are nonnegative (dual feasibility), and complementary
slackness holds. Available theorems: `first_order_neccessary_general` (the
descent-direction form, proved via Farkas' lemma), `first_order_neccessary_LICQ`
(under the linear-independence constraint qualification), and
`first_order_neccessary_LinearCQ` (under the affine constraint qualification),
together with the underlying `Farkas` lemma over `EuclideanSpace ℝ (Fin n)`.
These are the necessary-conditions direction only; convex sufficiency and
Slater-type qualifications are not part of the vendored development.
-/

namespace Causalean.Mathlib.Optimization

end Causalean.Mathlib.Optimization
