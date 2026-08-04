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
is `markovEquiv_of_sameSkeleton_sameImmoralities` (`Decompose.lean`).
-/

namespace Causalean

end Causalean
