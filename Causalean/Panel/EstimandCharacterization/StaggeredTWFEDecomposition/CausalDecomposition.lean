/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): fused causal TWFE decomposition

**Role in the folder.** ★ *Causal headline — the paper's main result.* Adds the
potential-outcome layer on top of the algebraic headline
`AlgebraicDecomposition.lean`. See `StaggeredTWFEDecomposition.lean` for the
folder layer-map.

Fuses the algebraic Goodman-Bacon identity `twfe_eq_weighted_avg`
(`betaTWFE P = ∑ weight · contrast`) with the Layer C causal corollaries
(`Δ_TN_eq_ATT`, `Δ_EL_eq_ATT`, `Δ_LE_eq_bad_comparison`) into a single
statement: under the two-state potential-outcome assumptions
`CausalAssumptions P Y0 Y1`, the TWFE coefficient equals the totalized weighted
sum of the *potential-outcome* window contrasts `ATT_window Y0 Y1` (with the
late-versus-early bad-comparison adjustment). A weighted-average
interpretation additionally requires positive residualized-treatment variance.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.AlgebraicDecomposition
import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Causal

/-! # Goodman-Bacon fused causal decomposition

This file composes the algebraic TWFE totalized weighted-sum identity with the
causal window-ATT corollaries, expressing the two-way fixed-effect coefficient
as a sum of normalized comparison weights times potential-outcome window
contrasts, with the late-versus-early bad-comparison term made explicit. A
weighted-average interpretation requires the separate positive-variance
condition used by `weights_sum_one`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

open Classical in
/-- The **causal** 2x2 contrast on the full index `CompTag × 𝒢 × 𝒢`: on an
admissible comparison it returns the potential-outcome window contrast identified
by the Layer C corollaries — `ATT_window` for TN/EL and the bad-comparison
adjustment for LE — and `0` otherwise. This is the causal counterpart of the
algebraic `contrast`. -/
noncomputable def contrastCausal (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (k : CompTag × 𝒢 × 𝒢) : ℝ :=
  if admissible P k then
    match k.1 with
    | CompTag.TN => ATT_window Y0 Y1 k.2.1 (S1_TN P k.2.1)
    | CompTag.EL => ATT_window Y0 Y1 k.2.1 (S1_EL P k.2.1 k.2.2)
    | CompTag.LE =>
        ATT_window Y0 Y1 k.2.2 (S1_LE P k.2.1 k.2.2)
          - (ATT_window Y0 Y1 k.2.1 (S1_LE P k.2.1 k.2.2)
              - ATT_window Y0 Y1 k.2.1 (S0_LE P k.2.1 k.2.2))
  else 0

/-- On an admissible comparison, the algebraic contrast equals the causal
potential-outcome contrast, by the Layer C corollaries. -/
theorem contrast_eq_contrastCausal (P : CohortPanel 𝒢 T)
    (Y0 Y1 : 𝒢 → Fin T → ℝ) (hA : CausalAssumptions P Y0 Y1)
    {k : CompTag × 𝒢 × 𝒢} (hk : admissible P k) :
    contrast P k = contrastCausal P Y0 Y1 k := by
  unfold contrast contrastCausal
  rw [if_pos hk, if_pos hk]
  rcases k with ⟨tag, g, u⟩
  cases tag
  · obtain ⟨hg, hu, _, _⟩ := hk
    exact Δ_TN_eq_ATT P Y0 Y1 hA g u hg hu
  · obtain ⟨hlt, hfin, _, _⟩ := hk
    exact Δ_EL_eq_ATT P Y0 Y1 hA g u hlt hfin
  · obtain ⟨hlt, hfin, _, _⟩ := hk
    exact Δ_LE_eq_bad_comparison P Y0 Y1 hA g u hlt hfin

/-- **Fused causal Goodman-Bacon decomposition.** Under the two-state
potential-outcome assumptions and strictly positive residualized-treatment
variance, the TWFE coefficient equals the Goodman-Bacon weighted average of
potential-outcome window contrasts `ATT_window Y0 Y1`, with the late-versus-early
bad-comparison adjustment.

The positive-variance hypothesis is the nondegenerate condition needed for the
normalized comparison weights to have their coefficient interpretation and sum
to one. -/
theorem twfe_po_decomposition (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (hVD_pos : 0 < VD P) :
    betaTWFE P = ∑ k ∈ 𝒦 P, weight P k * contrastCausal P Y0 Y1 k := by
  rw [twfe_eq_weighted_avg P hVD_pos]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk' : admissible P k := by simpa [𝒦] using hk
  rw [contrast_eq_contrastCausal P Y0 Y1 hA hk']

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
