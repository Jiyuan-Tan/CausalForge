/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Equality of measures from equality of Radon–Nikodym derivatives

The theorem `Measure.eq_of_rnDeriv_eq` says that two measures which are both absolutely
continuous with respect to a common reference and whose Radon–Nikodym derivatives against
that reference agree almost everywhere are equal.  This is the "uniqueness" direction of
the Radon–Nikodym theorem, packaged as a term-mode lemma so that it can be applied by
unification rather than by syntactic rewriting — the latter is brittle when the measures
carry heavy dependent-type indexing.

It is a project-independent statement about measures over a generic measurable
space and a candidate Mathlib contribution.
-/

namespace MeasureTheory.Measure

variable {α : Type*} {m : MeasurableSpace α}

/-- **A measure is determined by its Radon–Nikodym derivative against a fixed
reference.**  If `μ` and `ν` are both absolutely continuous with respect to `ρ`
and their densities `dμ/dρ` and `dν/dρ` agree `ρ`-almost everywhere, then
`μ = ν`.

Stated for application by unification (`exact`/`apply`) instead of rewriting, so
the reference `ρ` is inferred from the supplied absolute-continuity proofs and the
two measures need not be syntactically aligned with any rewrite pattern. -/
theorem eq_of_rnDeriv_eq {μ ν ρ : Measure α} [SigmaFinite ρ]
    (hμfin : IsFiniteMeasure μ) (hνfin : IsFiniteMeasure ν)
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ)
    (h : μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ) : μ = ν := by
  haveI := hμfin
  haveI := hνfin
  rw [← Measure.withDensity_rnDeriv_eq μ ρ hμ, ← Measure.withDensity_rnDeriv_eq ν ρ hν]
  exact MeasureTheory.withDensity_congr_ae h

end MeasureTheory.Measure
