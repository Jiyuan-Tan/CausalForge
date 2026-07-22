/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.Separation

namespace CausalSmith.Experimentation.SaturationSkew
open MeasureTheory
open scoped BigOperators

-- @node: lem:finite-dimensional-supporting-hyperplane
/-- A compact convex set and a disjoint open convex set admit a separating hyperplane. -/
lemma fin_dim_supporting_hyperplane {n : ℕ} (C O : Set (Fin n → ℝ))
    (hC : IsCompact C) (hCc : Convex ℝ C) (hCne : C.Nonempty) (hO : IsOpen O) (hOc : Convex ℝ O)
    (hdisj : Disjoint C O) (hOne : O.Nonempty) :
    ∃ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
      (∀ x ∈ C, c ≤ f x) ∧ (∀ y ∈ O, f y ≤ c) := by sorry

-- @node: lem:moment-image-compact-convex
/-- The four-moment image of the supported-laws set is compact and convex. -/
lemma moment_image_isCompact_convex (pbar : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    IsCompact {y : Fin 4 → ℝ | ∃ μ : Law,
        (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        y 0 = ∫ d, (1 : ℝ) ∂(μ : Measure ℝ) ∧ y 1 = ∫ d, d ∂(μ : Measure ℝ) ∧
        y 2 = ∫ d, d ^ 2 ∂(μ : Measure ℝ) ∧ y 3 = ∫ d, f d ∂(μ : Measure ℝ)} ∧
      Convex ℝ {y : Fin 4 → ℝ | ∃ μ : Law,
        (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        y 0 = ∫ d, (1 : ℝ) ∂(μ : Measure ℝ) ∧ y 1 = ∫ d, d ∂(μ : Measure ℝ) ∧
        y 2 = ∫ d, d ^ 2 ∂(μ : Measure ℝ) ∧ y 3 = ∫ d, f d ∂(μ : Measure ℝ)} := by sorry

end CausalSmith.Experimentation.SaturationSkew
