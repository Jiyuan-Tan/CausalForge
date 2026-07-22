-- Adapted from auto-res/lean-rademacher FoML/CoveringNumber.lean (commit 72d28921dc960f47691640fb973303a1be9d13ca, MIT License (c) 2025 AutoRes)
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Defines metric covering numbers for totally bounded sets and proves their basic
properties.

This file provides `coveringNumber`, the chosen minimizing net
`coveringFinset`, and the basic facts used by the Dudley entropy-integral
bound: positivity on nonempty sets, antitonicity in the radius, and
almost-everywhere measurability of the covering-number function.

UPSTREAM-DELTA: declarations are placed in the `Causalean.Stat.Concentration`
namespace. The proof terms are otherwise kept close to upstream, with only
Mathlib API-drift adjustments for Lean 4.29.
-/

namespace Causalean.Stat.Concentration

attribute [local instance] Classical.propDecidable

/-- A totally bounded set has a finite positive-radius net, with the net size
recorded as a natural number. -/
lemma coveringNumber_exists {X : Type*} {A : Set X} [PseudoMetricSpace X]
    (ha : TotallyBounded A) {ε : ℝ} (εpos : ε > 0) :
    ∃ n : Nat, ∃ t : Finset X, t.card = n ∧ A ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  have hball := Metric.finite_approx_of_totallyBounded ha ε εpos
  have ⟨t, ⟨_ht, tfin, tball⟩⟩ := hball
  have : Fintype t := tfin.fintype
  let n : Nat := this.card
  exists n
  exists t.toFinset
  constructor
  · exact Set.toFinset_card t
  · convert tball
    ext _
    simp only [Set.mem_toFinset]

/-- The covering number is the smallest size of a finite positive-radius net
for a totally bounded set, and is zero at nonpositive radii. -/
noncomputable def coveringNumber {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) (ε : ℝ) : ℕ :=
  if h : ε > 0 then
    Nat.find (coveringNumber_exists ha h)
  else 0

/-- At a positive radius, the covering number unfolds to the minimal finite
cover cardinality supplied by total boundedness. -/
theorem coveringNumber_eq {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    coveringNumber ha ε = Nat.find (coveringNumber_exists ha hε) :=
  dif_pos hε

/-- Covering numbers weakly decrease as the positive covering radius grows. -/
theorem converingNumber_antitone {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) :
    AntitoneOn (coveringNumber ha) (Set.Ioi 0) := by
  intro ε₁ hε₁ ε₂ hε₂ hε₁ε₂
  rw [coveringNumber_eq ha hε₁, coveringNumber_eq ha hε₂]
  apply Nat.find_mono
  intro n ⟨t, ht₁, ht₂⟩
  exists t, ht₁
  apply ht₂.trans
  apply Set.iUnion_mono
  intro _
  apply Set.iUnion_mono
  intro _
  exact Metric.ball_subset_ball hε₁ε₂

/-- A nonempty totally bounded set has a positive covering number at every
positive radius. -/
theorem coveringNumber_nonzero {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (hs : A.Nonempty) (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    0 < coveringNumber ha ε := by
  rw [coveringNumber_eq ha hε]
  rw [Nat.find_pos]
  simpa using Set.nonempty_iff_ne_empty.mp hs

/-- The covering-number function of the radius is almost-everywhere measurable
on the real line. -/
theorem converingNumber_aemeasurable {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) :
    AEMeasurable (coveringNumber ha) MeasureTheory.volume := by
  have h₀ : AEMeasurable (coveringNumber ha) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (converingNumber_antitone ha)
  convert (aemeasurable_indicator_iff measurableSet_Ioi).mpr h₀
  ext ε
  if h : ε ∈ Set.Ioi 0 then
    rw [Set.indicator_of_mem h]
  else
    rw [Set.indicator_of_notMem h]
    rw [coveringNumber, dif_neg (by exact h)]

/-- A chosen finite positive-radius net attains the covering number. -/
noncomputable def coveringFinset
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) : Finset X :=
  Classical.choose (Nat.find_spec (coveringNumber_exists (X := X) (A := A) ha hε))

/-- The chosen covering finset covers the target set by balls of the requested
positive radius. -/
lemma coveringFinset_cover
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    A ⊆ ⋃ y ∈ coveringFinset ha hε, Metric.ball y ε := by
  simpa [coveringFinset, coveringNumber_exists] using
    (Classical.choose_spec
      (Nat.find_spec (coveringNumber_exists (X := X) (A := A) ha hε))).2

/-- The chosen covering finset has cardinality equal to the covering number. -/
lemma coveringFinset_card
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    (coveringFinset ha hε).card = coveringNumber ha ε := by
  have h :=
    (Classical.choose_spec
      (Nat.find_spec (coveringNumber_exists (X := X) (A := A) ha hε))).1
  simpa [coveringFinset, coveringNumber_eq (X := X) (A := A) ha hε,
    coveringNumber_exists] using h

end Causalean.Stat.Concentration
