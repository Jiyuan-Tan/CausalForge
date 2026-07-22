/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rademacher complexity imports from `FoML.Defs`

This file imports the FoML definitions of Rademacher complexity and bounded
difference tools, then adds Causalean-specific congruence lemmas in the
`Causalean.Stat.Concentration` namespace. The FoML definitions themselves
remain root-namespace symbols exposed by the imports; this file does not create
Causalean-qualified aliases for them.

The imported FoML development is MIT-licensed; see the FoML package metadata
for provenance and license terms.
-/

import FoML.Defs
import FoML.BoundedDifference

/-!
Re-exports FoML Rademacher-complexity primitives and adds congruence lemmas for empirical and
population complexities.

The FoML symbols (`Signs`, `empiricalRademacherComplexity`,
`rademacherComplexity`, `empiricalRademacherComplexity_without_abs`,
`uniformDeviation`, `uniformDeviation_measurable`) live in the root
namespace and are imported transitively above. We declare the namespace
`Causalean.Stat.Concentration` so that downstream `open
Causalean.Stat.Concentration` continues to elaborate, but we do not
re-export the FoML names — root-namespace symbols are already in scope
unqualified, and declaring `abbrev` aliases here would trigger
ambiguous-term errors when both forms are visible.

We also collect a few generic congruence facts for empirical and population
Rademacher complexity (invariance under sample-pointwise / almost-everywhere
agreement of the function family). The public lemmas are
`empiricalRademacherComplexity_congr_sample`,
`rademacherComplexity_congr_ae`, and `rademacherComplexity_congr_ae_all`,
which let callers replace a function class by an equal-on-samples or
almost-everywhere equal representative without changing the corresponding
Rademacher complexity.
-/

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory

/-- The empirical Rademacher complexity sees the function family only through its
values on the observed sample: two families that agree at every sample point have
equal empirical Rademacher complexity. -/
lemma empiricalRademacherComplexity_congr_sample
    {𝒳 ι : Type*} (n : ℕ) (f f' : ι → 𝒳 → ℝ) (sample : Fin n → 𝒳)
    (h : ∀ i k, f i (sample k) = f' i (sample k)) :
    empiricalRademacherComplexity n f sample =
      empiricalRademacherComplexity n f' sample := by
  dsimp [empiricalRademacherComplexity]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _hσ
  congr 1
  ext i
  congr 2
  apply Finset.sum_congr rfl
  intro k _hk
  rw [h i k]

/-- The population Rademacher complexity is unchanged when each member of the
function family is replaced by an almost-everywhere-equal version: if
`f i ∘ sample` equals `f' i ∘ sample` almost everywhere for every index `i`, the
two families have equal Rademacher complexity. -/
lemma rademacherComplexity_congr_ae
    {Ω 𝒳 ι : Type*} [MeasurableSpace Ω]
    [Countable ι]
    (n : ℕ) (f f' : ι → 𝒳 → ℝ) (μ : MeasureTheory.Measure Ω)
    [SigmaFinite μ]
    (sample : Ω → 𝒳)
    (h : ∀ i, (fun ω => f i (sample ω)) =ᵐ[μ]
      fun ω => f' i (sample ω)) :
    rademacherComplexity n f μ sample =
      rademacherComplexity n f' μ sample := by
  dsimp [rademacherComplexity]
  apply integral_congr_ae
  have hall : ∀ᵐ ω ∂μ, ∀ i : ι,
      f i (sample ω) = f' i (sample ω) := ae_all_iff.2 h
  have hprod : ∀ᵐ s : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i : ι, ∀ k : Fin n,
        f i (sample (s k)) = f' i (sample (s k)) := by
    filter_upwards [Filter.eventually_all.2 fun k : Fin n =>
      Measure.tendsto_eval_ae_ae.eventually hall] with s hs i k
    exact hs k i
  filter_upwards [hprod] with s hs
  exact empiricalRademacherComplexity_congr_sample n f f' (sample ∘ s)
    (fun i k => hs i k)

/-- The population Rademacher complexity is unchanged under an
almost-everywhere agreement of the whole family at once: if almost every `ω`
satisfies `f i (sample ω) = f' i (sample ω)` for all indices `i`
simultaneously, the two families have equal Rademacher complexity.

This is the joint-event variant of `rademacherComplexity_congr_ae`: it consumes
a single a.e. statement quantified over all indices, rather than one a.e.
statement per index, so it does not need `[Countable ι]`. -/
lemma rademacherComplexity_congr_ae_all
    {Ω 𝒳 ι : Type*} [MeasurableSpace Ω]
    (n : ℕ) (f f' : ι → 𝒳 → ℝ) (μ : MeasureTheory.Measure Ω)
    [SigmaFinite μ]
    (sample : Ω → 𝒳)
    (h : ∀ᵐ ω ∂μ, ∀ i : ι, f i (sample ω) = f' i (sample ω)) :
    rademacherComplexity n f μ sample =
      rademacherComplexity n f' μ sample := by
  dsimp [rademacherComplexity]
  apply integral_congr_ae
  have hprod : ∀ᵐ s : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i : ι, ∀ k : Fin n,
        f i (sample (s k)) = f' i (sample (s k)) := by
    filter_upwards [Filter.eventually_all.2 fun k : Fin n =>
      Measure.tendsto_eval_ae_ae.eventually h] with s hs i k
    exact hs k i
  filter_upwards [hprod] with s hs
  exact empiricalRademacherComplexity_congr_sample n f f' (sample ∘ s)
    (fun i k => hs i k)

end Concentration
end Stat
end Causalean
