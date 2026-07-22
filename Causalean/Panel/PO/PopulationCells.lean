/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Shared population cell substrate for panel estimand characterizations

Every genuine "population bridge" in `Panel/EstimandCharacterization/*` is the
same construction: a probability space `(Ω, μ)`, a finite measurable partition
of `Ω` into cells, and potential outcomes on `Ω`; each causal field of a
paper-specific finite structure is a **cell-conditional mean of a potential
outcome** (`eventCondExp μ (cell i) f`), and the structure's consistency field
is *derived* from pointwise potential-outcome consistency on cells.

This file factors that shared substrate out once:

* `CellPartition μ ι` — a finite measurable partition of `Ω` (indexed by a
  `Fintype ι`) with positive-mass cells.
* `CellPartition.mass` / `CellPartition.mean` — the cell probability
  `π_i = ℙ(cell i)` and the cell-conditional mean `E[f ∣ cell i]`.
* the mass-sums-to-one identity, the finite-partition total law, and the
  congruence/algebra lemmas each paper's bridge reuses.

The canonical cell mean is `Causalean.PO.eventCondExp` (an event-level integral
divided by the event's real mass); `CellPartition.mean` is a thin wrapper so the
`eventCondExp` algebra (`eventCondExp_congr_on`, `eventCondExp_sub`, the total
law `integral_eq_sum_measure_mul_eventCondExp`) is available cell-indexed.
-/

import Causalean.PO.Conditioning.EventCondExp

/-! # Population cell partition

This file provides the shared finite-cell population substrate on which the
panel estimand-characterization population bridges are built: a finite
measurable partition of a probability space into positive-mass cells, together
with cell masses, cell-conditional means, and their basic identities. -/

namespace Causalean.Panel.PO

open MeasureTheory
open Causalean.PO

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite measurable partition of a probability space `(Ω, μ)` into
positive-mass cells indexed by a finite type `ι`. Bundles the measurability,
pairwise disjointness, covering, and positive-mass side conditions that every
population bridge otherwise carries loose. -/
structure CellPartition (μ : Measure Ω) (ι : Type*) [Fintype ι] where
  /-- The cell assigned to index `i` (e.g. `{ω | G ω = i}`). -/
  cell : ι → Set Ω
  /-- Each cell is measurable. -/
  cell_meas : ∀ i, MeasurableSet (cell i)
  /-- Distinct cells are disjoint. -/
  cell_disj : Pairwise (Function.onFun Disjoint cell)
  /-- The cells cover the whole space. -/
  cell_cov : (⋃ i, cell i) = Set.univ
  /-- Every cell has positive real mass. -/
  cell_pos : ∀ i, 0 < (μ (cell i)).toReal

/-- Build a cell partition from a **finite classifier** `g : Ω → ι`: the cells
are the level sets `{ω | g ω = i}`. Disjointness and covering are automatic;
the caller supplies measurability and positive mass of each level set. This is
the common way panel bridges obtain their partition (cohort map, treated/untreated
classifier, cohort-period map, …). -/
noncomputable def cellPartitionOfClassifier {ι : Type*} [Fintype ι]
    (μ : Measure Ω) (g : Ω → ι)
    (hmeas : ∀ i, MeasurableSet (g ⁻¹' {i}))
    (hpos : ∀ i, 0 < (μ (g ⁻¹' {i})).toReal) :
    CellPartition μ ι where
  cell i := g ⁻¹' {i}
  cell_meas := hmeas
  cell_disj := fun _a _b hab => Disjoint.preimage g (Set.disjoint_singleton.mpr hab)
  cell_cov := by ext ω; simp
  cell_pos := hpos

namespace CellPartition

variable {μ : Measure Ω} {ι : Type*} [Fintype ι]

@[simp] theorem cellPartitionOfClassifier_cell {ι : Type*} [Fintype ι]
    (μ : Measure Ω) (g : Ω → ι)
    (hmeas : ∀ i, MeasurableSet (g ⁻¹' {i}))
    (hpos : ∀ i, 0 < (μ (g ⁻¹' {i})).toReal) (i : ι) :
    (cellPartitionOfClassifier μ g hmeas hpos).cell i = g ⁻¹' {i} := rfl

/-- Cell probability `π_i = ℙ(cell i)`, as a real number. -/
def mass (P : CellPartition μ ι) (i : ι) : ℝ := (μ (P.cell i)).toReal

/-- Cell-conditional mean `E[f ∣ cell i]`, i.e. the average of `f` over the
cell computed as its integral over the cell divided by the cell's real mass. -/
noncomputable def mean (P : CellPartition μ ι) (f : Ω → ℝ) (i : ι) : ℝ :=
  eventCondExp μ (P.cell i) f

/-- Every cell has strictly positive mass. -/
theorem mass_pos (P : CellPartition μ ι) (i : ι) : 0 < P.mass i := P.cell_pos i

/-- Every cell has nonzero mass. -/
theorem mass_ne_zero (P : CellPartition μ ι) (i : ι) : P.mass i ≠ 0 :=
  (P.mass_pos i).ne'

/-- **Masses sum to one.** The cell probabilities of a partition of a
probability space add to `1`. -/
theorem mass_sum_one (P : CellPartition μ ι) [IsProbabilityMeasure μ] :
    ∑ i, P.mass i = 1 := by
  have hsum : ∑ i, μ (P.cell i) = 1 := by
    have h := measure_iUnion (μ := μ) P.cell_disj P.cell_meas
    rw [P.cell_cov, measure_univ, tsum_fintype] at h
    exact h.symm
  calc
    ∑ i, P.mass i = (∑ i, μ (P.cell i)).toReal :=
      (ENNReal.toReal_sum (fun i _ => measure_ne_top μ (P.cell i))).symm
    _ = (1 : ENNReal).toReal := by rw [hsum]
    _ = 1 := ENNReal.toReal_one

/-- **Finite-partition total law.** The integral of `f` is the mass-weighted sum
of its cell means: `∫ f = ∑ i, π_i · E[f ∣ cell i]`. -/
theorem integral_eq_sum_mass_mul_mean (P : CellPartition μ ι)
    [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ i, P.mass i * P.mean f i :=
  integral_eq_sum_measure_mul_eventCondExp μ P.cell P.cell_meas P.cell_disj
    P.cell_cov f hf

/-- Cell means agree when the integrands agree pointwise on the cell. This is the
workhorse "consistency descent" step: on a cell where an observed quantity
equals a potential-outcome slice, their cell means coincide. -/
theorem mean_congr_on (P : CellPartition μ ι) {f g : Ω → ℝ} (i : ι)
    (h : ∀ ω ∈ P.cell i, f ω = g ω) :
    P.mean f i = P.mean g i :=
  eventCondExp_congr_on μ (P.cell_meas i) h

/-- Cell means agree for a.e.-equal integrands. -/
theorem mean_congr_ae (P : CellPartition μ ι) {f g : Ω → ℝ} (i : ι)
    (h : f =ᵐ[μ] g) :
    P.mean f i = P.mean g i :=
  eventCondExp_congr_ae μ (P.cell i) h

/-- Cell means are additive over subtraction of integrable integrands. -/
theorem mean_sub (P : CellPartition μ ι) {f g : Ω → ℝ} (i : ι)
    (hf : IntegrableOn f (P.cell i) μ) (hg : IntegrableOn g (P.cell i) μ) :
    P.mean (f - g) i = P.mean f i - P.mean g i :=
  eventCondExp_sub μ (P.cell i) hf hg

/-- Cell means are additive over sums of integrable integrands. -/
theorem mean_add (P : CellPartition μ ι) {f g : Ω → ℝ} (i : ι)
    (hf : IntegrableOn f (P.cell i) μ) (hg : IntegrableOn g (P.cell i) μ) :
    P.mean (f + g) i = P.mean f i + P.mean g i :=
  eventCondExp_add μ (P.cell i) hf hg

/-- Cell means are homogeneous under real scalar multiplication. -/
theorem mean_smul (P : CellPartition μ ι) (c : ℝ) (f : Ω → ℝ) (i : ι) :
    P.mean (fun ω => c * f ω) i = c * P.mean f i :=
  eventCondExp_smul μ (P.cell i) c f

/-- **Cell-mean consistency descent.** On a cell where treatment is constant
`d ∈ {0,1}` and pointwise potential-outcome consistency `Y = Y0 + d·(Y1 − Y0)`
holds, the cell-conditional means satisfy the same identity:
`E[Y ∣ cell] = E[Y0 ∣ cell] + d·(E[Y1 ∣ cell] − E[Y0 ∣ cell])`. This is the
shared "observed-mean = untreated-mean + effect" step every binary-treatment
population bridge uses; the cell effect `E[Y1 ∣ cell] − E[Y0 ∣ cell]` is a
genuine potential-outcome contrast. -/
theorem mean_consistency (P : CellPartition μ ι) (i : ι) (Y Y0 Y1 : Ω → ℝ)
    {d : ℝ} (hd : d = 0 ∨ d = 1)
    (hcons : ∀ ω ∈ P.cell i, Y ω = Y0 ω + d * (Y1 ω - Y0 ω)) :
    P.mean Y i = P.mean Y0 i + d * (P.mean Y1 i - P.mean Y0 i) := by
  rcases hd with h0 | h1
  · subst h0
    have hY : P.mean Y i = P.mean Y0 i :=
      P.mean_congr_on i (fun ω hω => by rw [hcons ω hω]; ring)
    rw [hY]; ring
  · subst h1
    have hY : P.mean Y i = P.mean Y1 i :=
      P.mean_congr_on i (fun ω hω => by rw [hcons ω hω]; ring)
    rw [hY]; ring

end CellPartition

end Causalean.Panel.PO
