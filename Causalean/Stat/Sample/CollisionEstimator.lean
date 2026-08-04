/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Collision and cross-sample estimators

This module defines an ordered-pair collision estimator for inverse-frequency
functionals, together with cell-weighted moments and cross-sample averages for
observations equipped with an explicit projection to their cell labels.
-/

namespace Causalean.Stat

open scoped BigOperators

/-- The collision kernel contributes the inverse mass of a cell when two observations have the
same label and zero otherwise. -/
noncomputable def collisionKernel {𝒳 : Type*} (q : 𝒳 → ℝ) (x y : 𝒳) : ℝ :=
  by
    classical
    exact if x = y then 1 / q x else 0

/-- The collision scale averages inverse-frequency collisions over distinct ordered pairs in a
sample. -/
noncomputable def collisionScale {𝒳 : Type*} (q : 𝒳 → ℝ) {N : ℕ}
    (target : Fin N → 𝒳) : ℝ :=
  ((N : ℝ) * (N - 1 : ℕ))⁻¹ *
    ∑ j, ∑ l, if j ≠ l then collisionKernel q (target j) (target l) else 0

/-- A cell moment is the sample average of a statistic within one projected cell, rescaled by that
cell's inverse population frequency. -/
noncomputable def cellMoment {𝒳 Ω : Type*} (q : 𝒳 → ℝ) (proj : Ω → 𝒳)
    {n : ℕ} (sample : Fin n → Ω) (G : Ω → ℝ) (x : 𝒳) : ℝ :=
  by
    classical
    exact (n : ℝ)⁻¹ / q x *
      ∑ i, if proj (sample i) = x then G (sample i) else 0

/-- A cross-sample average evaluates source-sample cell moments at every target observation and
averages the resulting values over the target sample. -/
noncomputable def crossAverage {𝒳 Ω : Type*} (q : 𝒳 → ℝ) (proj : Ω → 𝒳)
    {n N : ℕ} (source : Fin n → Ω) (target : Fin N → 𝒳)
    (G : Ω → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, cellMoment q proj source G (target j)

end Causalean.Stat
