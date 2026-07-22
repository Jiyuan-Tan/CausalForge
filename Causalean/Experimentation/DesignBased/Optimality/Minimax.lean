/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Minimax designs and regret

When the risk of a design depends on an unknown *state of nature* `y` (e.g. the finite population's
potential-outcome table), the experimenter ranks designs by their **worst-case risk** over a family
of states.  This file defines the worst-case risk of a design over a nonempty finite set of states,
the **minimax** design (one minimizing the worst-case risk in a family), and the **regret** of a
design at a state (its risk minus the best risk achievable in the family there).  Minimax existence
over a finite design family is immediate from the generic optimal-design existence theorem applied
to the worst-case-risk criterion.
-/

import Causalean.Experimentation.DesignBased.Optimality

/-! # Minimax design criteria

Minimax designs minimize worst-case risk over a finite family of states of nature.

The definition `worstRisk` takes the maximum of `R y D` over a nonempty finite state set, and
`IsMinimaxOn` asks a design to minimize that criterion inside a design family. The theorem
`exists_isMinimaxOn` inherits finite-family existence from `exists_isOptimalOn`. The declarations
`bestRisk`, `regret`, and `regret_nonneg` formalize statewise regret relative to the best design
available in the same finite family.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω] {Y : Type*}

/-- The **worst-case risk** of a design `D` over a nonempty finite set `s` of states of nature: the
largest risk `R y D` incurred as the state `y` ranges over `s`. -/
noncomputable def worstRisk (s : Finset Y) (hs : s.Nonempty) (R : Y → FiniteDesign Ω → ℝ)
    (D : FiniteDesign Ω) : ℝ :=
  s.sup' hs (fun y => R y D)

/-- The worst-case risk dominates the risk at every state in the family. -/
lemma le_worstRisk (s : Finset Y) (hs : s.Nonempty) (R : Y → FiniteDesign Ω → ℝ)
    (D : FiniteDesign Ω) {y : Y} (hy : y ∈ s) : R y D ≤ worstRisk s hs R D :=
  Finset.le_sup' (fun y => R y D) hy

/-- A design is **minimax** in the family `𝒟` over the states `s` when it belongs to `𝒟` and has the
least worst-case risk among all members. -/
def IsMinimaxOn (𝒟 : DesignFamily Ω) (s : Finset Y) (hs : s.Nonempty)
    (R : Y → FiniteDesign Ω → ℝ) (D₀ : FiniteDesign Ω) : Prop :=
  D₀ ∈ 𝒟 ∧ ∀ D ∈ 𝒟, worstRisk s hs R D₀ ≤ worstRisk s hs R D

/-- **Existence of a minimax design.** Over a nonempty finite design family, some design
minimizes the worst-case risk. Immediate from `exists_isOptimalOn` applied to the
worst-case-risk criterion. -/
theorem exists_isMinimaxOn (𝒟 : DesignFamily Ω) (s : Finset Y) (hs : s.Nonempty)
    (R : Y → FiniteDesign Ω → ℝ) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty) :
    ∃ D₀, IsMinimaxOn 𝒟 s hs R D₀ :=
  exists_isOptimalOn 𝒟 (worstRisk s hs R) hfin hne

/-- The **best achievable risk** at state `y` over the finite design family `𝒟`: the least risk
`R y D` as `D` ranges over `𝒟`. (Defined via a chosen minimizer, which exists by
`exists_isOptimalOn`; `bestRisk_le` and `le_bestRisk` characterize it.) -/
noncomputable def bestRisk (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty)
    (R : Y → FiniteDesign Ω → ℝ) (y : Y) : ℝ :=
  R y (Classical.choose (exists_isOptimalOn 𝒟 (R y) hfin hne))

/-- The best achievable risk is attained, hence no larger than the risk of any family member. -/
lemma bestRisk_le (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty)
    (R : Y → FiniteDesign Ω → ℝ) (y : Y) {D : FiniteDesign Ω} (hD : D ∈ 𝒟) :
    bestRisk 𝒟 hfin hne R y ≤ R y D :=
  (Classical.choose_spec (exists_isOptimalOn 𝒟 (R y) hfin hne)).2 D hD

/-- The **regret** of a design `D` at state `y`, relative to the finite family `𝒟`: how much worse
its risk is than the best risk achievable in `𝒟` at that state. -/
noncomputable def regret (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty)
    (R : Y → FiniteDesign Ω → ℝ) (y : Y) (D : FiniteDesign Ω) : ℝ :=
  R y D - bestRisk 𝒟 hfin hne R y

/-- Regret is nonnegative for every member of the family. -/
lemma regret_nonneg (𝒟 : DesignFamily Ω) (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty)
    (R : Y → FiniteDesign Ω → ℝ) (y : Y) {D : FiniteDesign Ω} (hD : D ∈ 𝒟) :
    0 ≤ regret 𝒟 hfin hne R y D :=
  sub_nonneg.mpr (bestRisk_le 𝒟 hfin hne R y hD)

end DesignBased
end Experimentation
end Causalean
