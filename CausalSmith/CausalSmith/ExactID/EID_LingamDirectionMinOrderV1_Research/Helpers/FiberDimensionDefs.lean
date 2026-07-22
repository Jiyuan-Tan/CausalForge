/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Relative Zariski dimension predicates for LiNGAM fibers
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.Varieties

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

/-- A relatively Zariski-closed parameter set is irreducible inside the retained
finite-band ambient. -/
def IsIrreducibleZariskiClosedParamIn {m : ℕ} (L : ℕ)
    (Z : Set (ParamSpace ℂ m)) : Prop :=
  zariskiClosureParamIn L Z = Z ∧ Z.Nonempty ∧
    ∀ Z₁ Z₂ : Set (ParamSpace ℂ m),
      zariskiClosureParamIn L Z₁ = Z₁ → zariskiClosureParamIn L Z₂ = Z₂ →
      Z = Z₁ ∪ Z₂ → Z = Z₁ ∨ Z = Z₂

/-- Exact relative Krull dimension, measured by strict chains of irreducible
closed subsets inside the paper's retained-band parameter ambient. -/
def HasRelativeZariskiDimension {m : ℕ} (L d : ℕ)
    (Z : Set (ParamSpace ℂ m)) : Prop :=
  (∃ chain : Fin (d + 1) → Set (ParamSpace ℂ m),
      StrictMono chain ∧
      (∀ i, IsIrreducibleZariskiClosedParamIn L (chain i)) ∧
      (∀ i, chain i ⊆ Z)) ∧
  ¬ ∃ chain : Fin (d + 2) → Set (ParamSpace ℂ m),
      StrictMono chain ∧
      (∀ i, IsIrreducibleZariskiClosedParamIn L (chain i)) ∧
      (∀ i, chain i ⊆ Z)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
