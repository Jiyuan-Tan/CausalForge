/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.MarkovEquiv.Decompose

/-! # Markov equivalence — the hard direction (via the covered-edge route)

The hard direction of Verma–Pearl: two DAGs with the same skeleton and the same
v-structures (immoralities) declare exactly the same d-separations, hence are Markov
equivalent. We obtain it from the **covered-edge route** (Andersson–Madigan–Perlman 1997):
a same-skeleton/same-immoralities pair differs by a sequence of single covered-edge
reversals, each of which preserves every d-separation (`markovEquiv_flipEdge`); the assembly
is `markovEquiv_of_sameSkeleton_sameImmoralities_covered` (`Decompose.lean`).
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Hard direction of Verma–Pearl.** DAGs with the same skeleton and the same
v-structures are Markov equivalent. -/
theorem markovEquiv_of_sameSkeleton_sameImmoralities {G₁ G₂ : DAG V}
    (hskel : SameSkeleton G₁ G₂) (himm : SameImmoralities G₁ G₂) :
    MarkovEquiv G₁ G₂ :=
  markovEquiv_of_sameSkeleton_sameImmoralities_covered hskel himm

end Causalean
