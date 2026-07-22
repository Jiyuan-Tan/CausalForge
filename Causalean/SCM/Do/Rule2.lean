/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 of do-calculus — kernel-level plumbing aggregator

The kernel-native Rule 2 *statement* itself is the witness-route a.e.
theorem `obsCondKernel_fixSet_eq_ae_witness` in `Rule2AE.lean` (surfaced as
`do_rule2_kernel` in `DoCalculus.lean`).  The earlier pointwise/`fillZrW`
form `obsCondKernel_fixSet_eq` was retired: it pinned `obsCondKernel` on the
`μ_C`-null `{Z.random = ζ_s}` slice, which is ill-posed for continuous
treatment.

This module now only re-exports the value-space / global-Markov / overlap
plumbing (`RectIdentity`, `ObsMarkov`, `ID.Overlap`) that the Rule 2 a.e.
proof and downstream identification arguments consume.

## References

* Basic Concepts.tex, Proposition (do-Calculus), Rule 2.
-/

import Causalean.SCM.Do.Rule2Kernel.RectIdentity
import Causalean.SCM.Do.ObsMarkov
import Causalean.SCM.ID.Overlap

/-! # Rule 2 kernel-level plumbing aggregator

This module re-exports the value-space, global-Markov, and overlap helpers used
by the kernel-native Rule 2 a.e. statement (`Rule2AE.lean`) and the downstream
backdoor / frontdoor identification arguments.  The Rule 2 statement itself lives
in `Rule2AE.lean`. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

end SCM

end Causalean
