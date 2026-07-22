/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Model
import Causalean.Discovery.LinearDisentanglement.KeyIdentity
import Causalean.Discovery.LinearDisentanglement.SigmaSolutions
import Causalean.Discovery.LinearDisentanglement.PartialOrderRQ
import Causalean.Discovery.LinearDisentanglement.Rowspan
import Causalean.Discovery.LinearDisentanglement.Uniqueness
import Causalean.Discovery.LinearDisentanglement.Identifiability

/-!
# Linear causal disentanglement via interventions — umbrella

Entry point for the formalization of Squires, Seigal, Bhate & Uhler, *Linear Causal
Disentanglement via Interventions* (ICML 2023, `arXiv:2211.16467`).  Import this file to
get the whole development; the headline results are listed here so the main theorem is not
buried among the supporting linear-algebra files.

## Main results

* `Solution` (`Model.lean`) — the model: `d` latent variables following a linear SEM,
  observed only through a full-rank mixing `X = G Z`, with one perfect single-node
  intervention per context; the observable content is the precision matrices
  `Θ_k = Hᵀ Bₖᵀ Bₖ H`.
* `disentanglement_identifiability` (`Identifiability.lean`) — **the flagship (Theorem 2).**
  With one intervention per latent node and non-degenerate interventions, two solutions
  with the same `{Θ_k}` are related by a single order-preserving relabeling `σ ∈ S(𝒢)` and
  a nonzero signed diagonal scaling of the latent directions (the `(⊆)` direction).
* `sigma_solutions` (`SigmaSolutions.lean`) — the `(⊇)` direction: every `σ ∈ S(𝒢)` yields a
  solution with the same precision matrices. Together with the flagship this characterizes
  the solution set as the `S(𝒢)`-orbit (up to signed scaling).

## Supporting machinery

`KeyIdentity.lean` (the rank-one precision-difference identity), `Rowspan.lean` (Lemma 1,
linking precision differences to the latent graph), `PartialOrderRQ.lean` (the partial-order
RQ decomposition), `Uniqueness.lean` (the orthogonal-correctness assembly), and
`Causalean/Mathlib/LinearAlgebra/Cholesky.lean` (real Cholesky existence/uniqueness).
The non-Gaussianity engine is **not** used here — disentanglement identifies via
interventions + second moments, reusing only LiNGAM's structural pinning
(`Causalean.Discovery.LiNGAM`).
-/
