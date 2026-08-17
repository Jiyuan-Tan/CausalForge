/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Experimentation.DesignBased.InProb

/-!
# Design-based converging-together (CDF-level Slutsky)

The finite-design counterpart of the classical converging-together / Slutsky theorem, stated
directly on `FiniteDesign.Pr` at the level of pointwise CDF convergence. If `Sₙ` and `Tₙ` are
asymptotically indistinguishable in probability and the CDFs of `Tₙ` converge to a continuous limit
CDF `Φ`, then the CDFs of `Sₙ` converge to the same `Φ`. It transfers a limiting CDF across an
in-probability-negligible perturbation — the exact step a studentized design-based estimator needs
to pass from an oracle statistic to its feasible (plug-in standard error) version — without leaving
the finite-design layer for the measure-theoretic weak-convergence API.
-/

open scoped Topology
open Filter

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]

/-- **Finite-design CDF converging-together.** Along [a sequence of finite designs](hyp:D) on
[two sequences of real-valued statistics `Sₙ` and `Tₙ`](hyp:S,T), suppose [`Sₙ` is
asymptotically indistinguishable from `Tₙ` in probability: for every `η > 0`,
`Pr(η ≤ |Sₙ − Tₙ|) → 0`](hyp:hApprox), [the CDFs of `Tₙ` converge pointwise to a limit
function `Φ`](hyp:hT), and [`Φ` is continuous](hyp:hΦ). Then [the CDFs of `Sₙ` converge
pointwise to the same `Φ`](goal). -/
lemma finiteDesign_cdf_converging_together
    (D : ∀ n, FiniteDesign (Ω n)) (S T : ∀ n, Ω n → ℝ) (Φ : ℝ → ℝ)
    (hApprox : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (D n).Pr (fun z => η ≤ |S n z - T n z|)) atTop (𝓝 0))
    (hT : ∀ x : ℝ,
      Tendsto (fun n => (D n).Pr (fun z => T n z ≤ x)) atTop (𝓝 (Φ x)))
    (hΦ : Continuous Φ) :
    ∀ x : ℝ,
      Tendsto (fun n => (D n).Pr (fun z => S n z ≤ x)) atTop (𝓝 (Φ x)) := by
  classical
  intro x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨η, hηpos, hη⟩ :=
    (Metric.continuousAt_iff.mp hΦ.continuousAt) (ε / 4) hε4
  set γ : ℝ := η / 2 with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; linarith
  have hγ_lt_η : γ < η := by rw [hγdef]; linarith
  have hΦ_plus_abs : dist (Φ (x + γ)) (Φ x) < ε / 4 := by
    apply hη
    rw [Real.dist_eq]
    have : x + γ - x = γ := by ring
    rw [this, abs_of_pos hγpos]
    exact hγ_lt_η
  have hΦ_minus_abs : dist (Φ (x - γ)) (Φ x) < ε / 4 := by
    apply hη
    rw [Real.dist_eq]
    have : x - γ - x = -γ := by ring
    rw [this, abs_neg, abs_of_pos hγpos]
    exact hγ_lt_η
  rw [Real.dist_eq] at hΦ_plus_abs hΦ_minus_abs
  have hΦ_plus_lt : Φ (x + γ) < Φ x + ε / 4 := by
    linarith [(abs_lt.mp hΦ_plus_abs).2]
  have hΦ_minus_gt : Φ x - ε / 4 < Φ (x - γ) := by
    linarith [(abs_lt.mp hΦ_minus_abs).1]
  have hR := hApprox γ hγpos
  have hTplus := hT (x + γ)
  have hTminus := hT (x - γ)
  have hRev : ∀ᶠ n in atTop, (D n).Pr (fun z => γ ≤ |S n z - T n z|) < ε / 4 :=
    by
      have h := (Metric.tendsto_nhds.mp hR) (ε / 4) hε4
      filter_upwards [h] with n hn
      rw [Real.dist_eq] at hn
      have hnonneg : 0 ≤ (D n).Pr (fun z => γ ≤ |S n z - T n z|) :=
        (D n).Pr_nonneg _
      have habs :
          |((D n).Pr (fun z => γ ≤ |S n z - T n z|)) - 0|
            = (D n).Pr (fun z => γ ≤ |S n z - T n z|) := by
        rw [sub_zero, abs_of_nonneg hnonneg]
      rwa [habs] at hn
  have hTplus_ev : ∀ᶠ n in atTop,
      (D n).Pr (fun z => T n z ≤ x + γ) < Φ (x + γ) + ε / 4 := by
    have h := (Metric.tendsto_nhds.mp hTplus) (ε / 4) hε4
    filter_upwards [h] with n hn
    rw [Real.dist_eq] at hn
    linarith [(abs_lt.mp hn).2]
  have hTminus_ev : ∀ᶠ n in atTop,
      Φ (x - γ) - ε / 4 < (D n).Pr (fun z => T n z ≤ x - γ) := by
    have h := (Metric.tendsto_nhds.mp hTminus) (ε / 4) hε4
    filter_upwards [h] with n hn
    rw [Real.dist_eq] at hn
    linarith [(abs_lt.mp hn).1]
  refine Filter.eventually_atTop.1 ?_
  filter_upwards [hRev, hTplus_ev, hTminus_ev] with n hRn hTpn hTmn
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · have hupper_event :
        (D n).Pr (fun z => S n z ≤ x)
          ≤ (D n).Pr (fun z => T n z ≤ x + γ)
            + (D n).Pr (fun z => γ ≤ |S n z - T n z|) := by
      calc
        (D n).Pr (fun z => S n z ≤ x)
            ≤ (D n).Pr (fun z =>
                T n z ≤ x + γ ∨ γ ≤ |S n z - T n z|) := by
              apply (D n).Pr_mono
              intro z hzS
              by_cases hfar : γ ≤ |S n z - T n z|
              · exact Or.inr hfar
              · left
                rw [not_le] at hfar
                have hdist : |T n z - S n z| < γ := by
                  rwa [abs_sub_comm] at hfar
                have hle : T n z ≤ S n z + γ := by
                  rw [abs_sub_lt_iff] at hdist
                  linarith
                linarith
        _ ≤ (D n).Pr (fun z => T n z ≤ x + γ)
              + (D n).Pr (fun z => γ ≤ |S n z - T n z|) :=
              FiniteDesign.Pr_or_le (D n) _ _
    linarith
  · have hlower_event :
        (D n).Pr (fun z => T n z ≤ x - γ)
          ≤ (D n).Pr (fun z => S n z ≤ x)
            + (D n).Pr (fun z => γ ≤ |S n z - T n z|) := by
      calc
        (D n).Pr (fun z => T n z ≤ x - γ)
            ≤ (D n).Pr (fun z =>
                S n z ≤ x ∨ γ ≤ |S n z - T n z|) := by
              apply (D n).Pr_mono
              intro z hzT
              by_cases hfar : γ ≤ |S n z - T n z|
              · exact Or.inr hfar
              · left
                rw [not_le] at hfar
                have hdist : |S n z - T n z| < γ := hfar
                have hle : S n z ≤ T n z + γ := by
                  rw [abs_sub_lt_iff] at hdist
                  linarith
                linarith
        _ ≤ (D n).Pr (fun z => S n z ≤ x)
              + (D n).Pr (fun z => γ ≤ |S n z - T n z|) :=
              FiniteDesign.Pr_or_le (D n) _ _
    linarith

end DesignBased
end Experimentation
end Causalean
