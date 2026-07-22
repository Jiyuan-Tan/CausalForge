/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Conditional distributions for product kernels

Let `ρ` be a finite base measure on `α`, and let `κ : Kernel α β` and
`η : Kernel α γ` be Markov kernels.  After sampling `(B, C)` from the product kernel
`Kernel.prod κ η` over the base coordinate, the conditional distribution of `B` given the
base coordinate is `κ`, and the conditional distribution of `C` given the base coordinate
is `η`.

The public theorems `condDistrib_fst_of_compProd_prod` and
`condDistrib_snd_of_compProd_prod` record these two coordinate conditionals for
`Measure.compProd ρ (Kernel.prod κ η)`.
-/

namespace Causalean.Mathlib.ProbabilityTheory.ProductCondDistrib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- For `Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)`, the conditional
distribution of the first product-kernel coordinate, given the base coordinate, is `κ`
for `ρ`-almost every base point. -/
theorem condDistrib_fst_of_compProd_prod
    [StandardBorelSpace β] [Nonempty β]
    {ρ : Measure α} [IsFiniteMeasure ρ]
    (κ : ProbabilityTheory.Kernel α β) (η : ProbabilityTheory.Kernel α γ)
    [ProbabilityTheory.IsMarkovKernel κ] [ProbabilityTheory.IsMarkovKernel η] :
    (ProbabilityTheory.condDistrib
        (Y := fun z : α × (β × γ) => z.2.1)
        (X := fun z : α × (β × γ) => z.1)
        (μ := Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η))) =ᵐ[ρ] κ := by
  have hX : Measurable (fun z : α × (β × γ) => z.1) := measurable_fst
  have hY : Measurable (fun z : α × (β × γ) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hbase :
      (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
        (fun z : α × (β × γ) => z.1) = ρ := by
    simpa [Measure.fst] using (Measure.fst_compProd ρ (ProbabilityTheory.Kernel.prod κ η))
  have hfst : (ProbabilityTheory.Kernel.prod κ η).map Prod.fst = κ := by
    simpa [ProbabilityTheory.Kernel.fst_eq] using
      (ProbabilityTheory.Kernel.fst_prod κ η)
  have hjoint :
      (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
        (fun z : α × (β × γ) => (z.1, z.2.1))
        = Measure.compProd ρ κ := by
    calc
      (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
          (fun z : α × (β × γ) => (z.1, z.2.1))
          = (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
              (Prod.map id Prod.fst) := by
            rfl
      _ = Measure.compProd ρ ((ProbabilityTheory.Kernel.prod κ η).map Prod.fst) := by
            rw [← Measure.compProd_map (μ := ρ)
              (κ := ProbabilityTheory.Kernel.prod κ η) measurable_fst]
      _ = Measure.compProd ρ κ := by
            rw [hfst]
  have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)) hX hY (κ := κ) (by
        simpa [hbase] using hjoint)
  rwa [hbase] at h

/-- For `Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)`, the conditional
distribution of the second product-kernel coordinate, given the base coordinate, is `η`
for `ρ`-almost every base point. -/
theorem condDistrib_snd_of_compProd_prod
    [StandardBorelSpace γ] [Nonempty γ]
    {ρ : Measure α} [IsFiniteMeasure ρ]
    (κ : ProbabilityTheory.Kernel α β) (η : ProbabilityTheory.Kernel α γ)
    [ProbabilityTheory.IsMarkovKernel κ] [ProbabilityTheory.IsMarkovKernel η] :
    (ProbabilityTheory.condDistrib
        (Y := fun z : α × (β × γ) => z.2.2)
        (X := fun z : α × (β × γ) => z.1)
        (μ := Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η))) =ᵐ[ρ] η := by
  have hX : Measurable (fun z : α × (β × γ) => z.1) := measurable_fst
  have hY : Measurable (fun z : α × (β × γ) => z.2.2) :=
    measurable_snd.comp measurable_snd
  have hbase :
      (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
        (fun z : α × (β × γ) => z.1) = ρ := by
    simpa [Measure.fst] using (Measure.fst_compProd ρ (ProbabilityTheory.Kernel.prod κ η))
  have hsnd : (ProbabilityTheory.Kernel.prod κ η).map Prod.snd = η := by
    simpa [ProbabilityTheory.Kernel.snd_eq] using
      (ProbabilityTheory.Kernel.snd_prod κ η)
  have hjoint :
      (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
        (fun z : α × (β × γ) => (z.1, z.2.2))
        = Measure.compProd ρ η := by
    calc
      (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
          (fun z : α × (β × γ) => (z.1, z.2.2))
          = (Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)).map
              (Prod.map id Prod.snd) := by
            rfl
      _ = Measure.compProd ρ ((ProbabilityTheory.Kernel.prod κ η).map Prod.snd) := by
            rw [← Measure.compProd_map (μ := ρ)
              (κ := ProbabilityTheory.Kernel.prod κ η) measurable_snd]
      _ = Measure.compProd ρ η := by
            rw [hsnd]
  have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Measure.compProd ρ (ProbabilityTheory.Kernel.prod κ η)) hX hY (κ := η) (by
        simpa [hbase] using hjoint)
  rwa [hbase] at h

end Causalean.Mathlib.ProbabilityTheory.ProductCondDistrib
