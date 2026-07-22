/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Vector-valued centered empirical process

The empirical-process object underlying stochastic equicontinuity / Donsker
theory at the *parametric* (`Z`-estimator) scale.  For a normed value space `E`
and a single function `f : X → E`, the centered, `√n`-scaled empirical process
evaluated along the i.i.d. sample is

    Gₙ(f)(ω) := (√n)⁻¹ • Σ_{i<n} f(Zᵢ ω) − √n • ∫ f dP.

For `f := ψ(θ, ·) − ψ(θ₀, ·)` this is exactly the centered empirical-process gap
`R_n` appearing in `Causalean.Stat.StochEquicontAt`
(`Causalean/Stat/EmpiricalProcess/Equicontinuity/StochEquicont.lean`): see
`empProcVec_eq_stochEquicont_gap`.  Splitting the definition out here lets the
*class-level* asymptotic-equicontinuity property (`Equicontinuity/Modulus.lean`)
and its second-moment control (`Equicontinuity/SecondMoment.lean`) be stated
without reference to any particular estimator sequence `θn`.

Causal-agnostic; candidate for upstream contribution to Mathlib.
-/

import Causalean.Stat.Sample
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Centered Empirical Process

This file defines the vector-valued centered empirical process at the
\(\sqrt n\) scale for a single function of an i.i.d. sample. The construction is
the empirical-process gap controlled by the stochastic-equicontinuity modules
and used in parametric estimator expansions.  The definition
`IIDSample.empProcVec` provides the reusable vector process, and
`IIDSample.empProcVec_eq_stochEquicont_gap` identifies it with the gap appearing
in `StochEquicontAt`. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- **Vector-valued centered empirical process.**

`Gₙ(f)(ω) = (√n)⁻¹ • Σ_{i<n} f(Zᵢ ω) − √n • ∫ f dP`, the `E`-valued analogue of
`IIDSample.empiricalProcess` (which is the `ℝ`-valued version in
`EmpiricalProcess/Basic.lean`).  The object whose weak limit is a Gaussian
process; its supremum over a shrinking parameter ball is the modulus controlled
by Donsker / bracketing-entropy theory. -/
noncomputable def empProcVec (S : IIDSample Ω X μ P) (f : X → E) (n : ℕ) :
    Ω → E :=
  fun ω => (Real.sqrt (n : ℝ))⁻¹ • (∑ i ∈ Finset.range n, f (S.Z i ω))
    - Real.sqrt (n : ℝ) • ∫ z, f z ∂P

/-- The centered empirical-process gap `R_n` of `StochEquicontAt`, evaluated at a
parameter `θ`, is `empProcVec` of the score difference `ψ(θ,·) − ψ(θ₀,·)`.  This
is a definitional unfolding; it is the bridge between the estimator-indexed
`StochEquicontAt` and the class-level `AsymptoticEquicont`. -/
theorem empProcVec_eq_stochEquicont_gap (S : IIDSample Ω X μ P)
    (ψ : E → X → E) (θ θ₀ : E) (n : ℕ) (ω : Ω) :
    S.empProcVec (fun z => ψ θ z - ψ θ₀ z) n ω
      = (Real.sqrt (n : ℝ))⁻¹ •
          (∑ i ∈ Finset.range n, (ψ θ (S.Z i ω) - ψ θ₀ (S.Z i ω)))
        - Real.sqrt (n : ℝ) • ∫ z, (ψ θ z - ψ θ₀ z) ∂P :=
  rfl

end IIDSample

end Causalean.Stat
