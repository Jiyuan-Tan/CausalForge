/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Gaussian half-line tail control

A single generic fact about the centered Gaussian law: each one-sided half-line
tail of `N(0, v)` can be made smaller than any `ε > 0` by pushing the cutoff out.
Both half-line families `(-∞, -n]` and `[n, ∞)` shrink to `∅`, so continuity from
above of the (finite) measure sends their mass to `0`.

Factored out of the sample-quantile rate proof (where it discharges the L4 tail
ingredient) so it can be reused by the Imbens–Manski coverage argument in
`PO/ID/Partial/Inference/ImbensManski.lean` without importing the
quantile-Bahadur tower.
-/

import Causalean.Stat.CLT.AsymptoticLinearity

/-! # Gaussian Tail Control

This file proves that both one-sided tails of a centered Gaussian distribution
can be made arbitrarily small by choosing a sufficiently large cutoff. The result
is a reusable tightness ingredient for quantile and partial-identification
asymptotic arguments.

The exported lemma `gaussian_tail_small` applies to the project's
`gaussianMeasure 0 v`, including the clipped degenerate case for nonpositive
variance parameters, and returns one positive cutoff controlling both the lower
and upper half-line tails. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Gaussian-measure half-line tail control.**  For the project's
`gaussianMeasure`, both symmetric half-line tails can be made smaller than any
positive tolerance by taking the cutoff large. This includes the clipped
degenerate case produced by nonpositive variance parameters. -/
lemma gaussian_tail_small {v ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      gaussianMeasure 0 v (Set.Iic (-R)) ≤ ENNReal.ofReal ε ∧
      gaussianMeasure 0 v (Set.Ici R) ≤ ENNReal.ofReal ε := by
  set Q : Measure ℝ := gaussianMeasure 0 v with hQ
  haveI : IsProbabilityMeasure Q := by rw [hQ]; infer_instance
  -- Both one-sided tails over the integer cutoffs shrink to `∅`, so their
  -- measure tends to `0`; pick a cutoff `> 0` below level `ε`.
  have htail : ∀ (s : ℕ → Set ℝ), Antitone s → (⋂ n, s n) = ∅ →
      (∀ n, MeasurableSet (s n)) →
      ∃ N : ℕ, Q (s N) ≤ ENNReal.ofReal ε := by
    intro s hanti hinter hmeas
    have hlim : Tendsto (fun n => Q (s n)) atTop (𝓝 0) := by
      have hf : ∃ n, Q (s n) ≠ ⊤ := ⟨0, measure_ne_top Q _⟩
      have ht := tendsto_measure_iInter_atTop
        (fun n => (hmeas n).nullMeasurableSet) hanti hf
      simpa [hinter] using ht
    have hpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    obtain ⟨N, hN⟩ := ((ENNReal.tendsto_nhds_zero.mp hlim) (ENNReal.ofReal ε) hpos).exists
    exact ⟨N, hN⟩
  -- Lower tail family `Iic (−n)`.
  obtain ⟨N₁, hN₁⟩ := htail (fun n => Set.Iic (-(n : ℝ)))
    (fun i j hij => by
      apply Set.Iic_subset_Iic.mpr
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith)
    (by
      ext x; simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, by linarith [hn]⟩)
    (fun n => measurableSet_Iic)
  -- Upper tail family `Ici n`.
  obtain ⟨N₂, hN₂⟩ := htail (fun n => Set.Ici (n : ℝ))
    (fun i j hij => by
      apply Set.Ici_subset_Ici.mpr; exact_mod_cast hij)
    (by
      ext x; simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact ⟨n, hn⟩)
    (fun n => measurableSet_Ici)
  -- Take `R = max(N₁, N₂) + 1 > 0`; both tails are sub-events of the chosen ones.
  refine ⟨(max N₁ N₂ : ℝ) + 1, by positivity, ?_, ?_⟩
  · refine le_trans (measure_mono ?_) hN₁
    apply Set.Iic_subset_Iic.mpr
    have h1 : (N₁ : ℝ) ≤ (max N₁ N₂ : ℝ) := by exact_mod_cast le_max_left N₁ N₂
    linarith
  · refine le_trans (measure_mono ?_) hN₂
    apply Set.Ici_subset_Ici.mpr
    have h2 : (N₂ : ℝ) ≤ (max N₁ N₂ : ℝ) := by exact_mod_cast le_max_right N₁ N₂
    linarith

end Causalean.Stat
