/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

-- @node: lem:centered-pushforward-program
/-- Centered pushforward program: the centering map carries admissible laws to the
mean-zero centered program and the decentering map inverts it. -/
lemma centered_pushforward_program (pbar : ℝ) (hb : BudgetInterior pbar) :
    (∀ ν : Law, IsAdmissible pbar ν →
        (centeredPush pbar ν : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        ∫ d, d ∂(centeredPush pbar ν : Measure ℝ) = 0 ∧
        (∀ r : ℕ, ∫ d, d ^ r ∂(centeredPush pbar ν : Measure ℝ) = centeredMoment pbar r ν) ∧
        0 ≤ centeredMoment pbar 2 ν ∧ centeredMoment pbar 2 ν ≤ pbar * (1 - pbar)) ∧
      (∀ μ : Law, (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 →
        ∫ d, d ∂(μ : Measure ℝ) = 0 → IsAdmissible pbar (decenterPush pbar μ)) := by sorry

-- @node: lem:empirical-centered-moment-continuity
/-- Empirical centered-moment continuity: weak convergence of empirical laws
transfers to convergence of the centered moments of order 2, 3, and 4. The note's
`[0,1]`-support hypotheses are carried explicitly: the empirical saturation vectors
take values in `[0,1]` (`hpi`) and the weak limit `ν` is supported on `[0,1]`
(`hνsupp`), so the test functions `(u - pbar)^r` are bounded on the joint support. -/
lemma empirical_centered_moment_continuity (pbar : ℝ) (Mseq : ℕ → ℕ)
    (piseq : (n : ℕ) → Fin (Mseq n) → ℝ) (ν : Law)
    (hpi : ∀ (n : ℕ) (j : Fin (Mseq n)), piseq n j ∈ Set.Icc (0 : ℝ) 1)
    (hνsupp : SupportedOn01 ν)
    (hw : Filter.Tendsto (fun n => empiricalLaw (Mseq n) (piseq n)) Filter.atTop (nhds ν)) :
    ∀ r : ℕ, r = 2 ∨ r = 3 ∨ r = 4 →
      Filter.Tendsto (fun n => centeredMoment pbar r (empiricalLaw (Mseq n) (piseq n)))
        Filter.atTop (nhds (centeredMoment pbar r ν)) := by sorry

end CausalSmith.Experimentation.SaturationSkew
