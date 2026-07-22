/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! # Measurable Embedding Extras

This file collects general measure-theoretic facts about measurable embeddings that are
independent of the library's structural causal model and SWIG infrastructure. Its main
result, `restrict_range_eq_of_forall_image`, shows that agreement on all embedded
measurable images implies agreement after restricting both measures to the embedding
range. -/

namespace MeasureTheory

open scoped MeasureTheory

variable {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} {F : α → β}

/-- If a measurable embedding `F : α → β` satisfies
    `μ (F '' A) = ν (F '' A)` for every measurable `A ⊆ α`, then
    `μ.restrict (Set.range F) = ν.restrict (Set.range F)`.

    Proof: by `MeasurableEmbedding.comap_apply`, the assumption shows
    `μ.comap F = ν.comap F` as measures on `α`; pushing forward through
    the measurable embedding `F` (via `MeasurableEmbedding.map_comap`)
    yields the displayed restriction equality on `range F`. -/
theorem restrict_range_eq_of_forall_image (hF : MeasurableEmbedding F)
    (μ ν : Measure β)
    (h : ∀ A, MeasurableSet A → μ (F '' A) = ν (F '' A)) :
    μ.restrict (Set.range F) = ν.restrict (Set.range F) := by
  -- Step 1: μ.comap F = ν.comap F on α (both interpret each measurable
  -- A ⊆ α as μ (F '' A), resp. ν (F '' A)).
  have h_comap : μ.comap F = ν.comap F := by
    refine Measure.ext (fun A hA => ?_)
    rw [hF.comap_apply, hF.comap_apply]
    exact h A hA
  -- Step 2: push forward via F, using map_comap.
  calc μ.restrict (Set.range F)
      = (μ.comap F).map F := (hF.map_comap μ).symm
    _ = (ν.comap F).map F := by rw [h_comap]
    _ = ν.restrict (Set.range F) := hF.map_comap ν

end MeasureTheory
