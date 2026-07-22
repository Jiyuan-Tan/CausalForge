/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.DiscreteID.Mass
import Causalean.SCM.ID.Density.ChainRuleDensity

/-!
# Point-mass bridges for finite discrete densities

This file exposes the measure-level identities that turn Radon--Nikodym
derivatives and conditional kernels into singleton-mass ratios on finite
measurable-singleton spaces.  The statements are reference-measure agnostic:
they apply to any faithful finite reference family, not only counting measure.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- On a measurable singleton, the RN derivative multiplied by the base mass
recovers the numerator singleton mass. -/
theorem rnDeriv_mul_measure_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [SFinite ν]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) (x : α) :
    ν ({x} : Set α) * μ.rnDeriv ν x = μ ({x} : Set α) := by
  have h1 : μ ({x} : Set α) = ∫⁻ y in ({x} : Set α), μ.rnDeriv ν y ∂ν :=
    (Measure.setLIntegral_rnDeriv hμν ({x} : Set α)).symm
  have h2 :
      (∫⁻ y in ({x} : Set α), μ.rnDeriv ν y ∂ν)
        = μ.rnDeriv ν x * ν ({x} : Set α) := by
    rw [lintegral_singleton]
  rw [h1, h2, mul_comm]

/-- On a positive finite singleton of the reference measure, the RN derivative
is the ratio of numerator mass to reference mass. -/
theorem rnDeriv_singleton_eq_div {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [SFinite ν]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) (x : α)
    (hν0 : ν ({x} : Set α) ≠ 0) (hνtop : ν ({x} : Set α) ≠ ∞) :
    μ.rnDeriv ν x = μ ({x} : Set α) / ν ({x} : Set α) := by
  rw [ENNReal.eq_div_iff hν0 hνtop]
  exact rnDeriv_mul_measure_singleton μ ν hμν x

/-- The singleton mass of a finite product reference is the product of the
coordinate singleton masses. -/
theorem jointRef_singleton_eq_prod (ref : ReferenceMeasures Ω)
    (I : Finset (SWIGNode N)) (x : ValuesOn I (swigΩ Ω)) :
    jointRef ref I ({x} : Set (ValuesOn I (swigΩ Ω))) =
      ∏ i : {i // i ∈ I}, ref.μ i.val ({x i} : Set (swigΩ Ω i.val)) := by
  classical
  unfold jointRef
  rw [Measure.pi_singleton]

/-- Mapping an observational kernel to a subcollection of observed coordinates
turns a singleton mass into the latent-product mass of the corresponding
agreement event. -/
theorem obsKernel_marginal_singleton_eq_latentProduct_agree
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {P : Finset (SWIGNode N)} (hP : P ⊆ M.observed)
    [MeasurableSingletonClass (ValuesOn P (swigΩ Ω))]
    (x : M.ObservedValues) :
    ((M.obsKernel s).map (valuesProjection hP))
        ({valuesProjection hP x} : Set (ValuesOn P (swigΩ Ω))) =
      M.latentProduct
        {ℓ | ∀ v : {v // v ∈ P},
          M.evalMap s ℓ
              ⟨v.val, Finset.mem_union_left M.unobserved (hP v.property)⟩ =
            x ⟨v.val, hP v.property⟩} := by
  classical
  have hproj : Measurable (valuesProjection (Ω := swigΩ Ω) hP) :=
    measurable_valuesProjection hP
  have hcomp :
      Measurable
        ((valuesProjection (Ω := swigΩ Ω) hP) ∘ M.randomToObserved) :=
    hproj.comp M.measurable_randomToObserved
  have heval : Measurable (fun ℓ : M.LatentValues => M.evalMap s ℓ) :=
    M.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  rw [SCM.obsKernel, Kernel.map_apply _ M.measurable_randomToObserved,
    Measure.map_map hproj M.measurable_randomToObserved]
  rw [M.jointKernel_apply_eq s, Measure.map_map hcomp heval]
  rw [Measure.map_apply]
  · congr 1
    ext ℓ
    constructor
    · intro h v
      have hv := congrFun h v
      simpa [Function.comp_def, valuesProjection, SCM.randomToObserved] using hv
    · intro h
      ext v
      exact h v
  · exact hcomp.comp heval
  · exact MeasurableSet.singleton _

/-- The singleton mass of a measure-kernel composition product factors as the
conditioning singleton mass times the fibre singleton mass. -/
theorem compProd_singleton_mass {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] (b : α) (y : β) :
    (μ ⊗ₘ κ) ({(b, y)} : Set (α × β)) =
      μ ({b} : Set α) * κ b ({y} : Set β) := by
  have hset : ({b} : Set α) ×ˢ ({y} : Set β) = ({(b, y)} : Set (α × β)) := by
    ext p
    rcases p with ⟨b', y'⟩
    simp
  calc
    (μ ⊗ₘ κ) ({(b, y)} : Set (α × β))
        = (μ ⊗ₘ κ) (({b} : Set α) ×ˢ ({y} : Set β)) := by
          rw [hset]
    _ = ∫⁻ a in ({b} : Set α), κ a ({y} : Set β) ∂μ := by
          rw [Measure.compProd_apply_prod
            (MeasurableSet.singleton b) (MeasurableSet.singleton y)]
    _ = κ b ({y} : Set β) * μ ({b} : Set α) := by
          rw [lintegral_singleton]
    _ = μ ({b} : Set α) * κ b ({y} : Set β) := by
          rw [mul_comm]

/-- A disintegration conditional kernel at a positive conditioning atom is the
joint singleton mass divided by the conditioning singleton mass. -/
theorem condKernel_singleton_mass_of_ne_zero {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace β]
    [Nonempty β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (b : α) (y : β)
    (hb : ρ.fst ({b} : Set α) ≠ 0) :
    ρ.condKernel b ({y} : Set β) =
      ρ ({(b, y)} : Set (α × β)) / ρ.fst ({b} : Set α) := by
  have hset : ({b} : Set α) ×ˢ ({y} : Set β) = ({(b, y)} : Set (α × β)) := by
    ext p
    rcases p with ⟨b', y'⟩
    simp
  rw [Measure.condKernel_apply_of_ne_zero (ρ := ρ) hb ({y} : Set β)]
  rw [hset, ENNReal.div_eq_inv_mul]

/-- Mathlib's measure-level conditional distribution has singleton mass equal
to the corresponding joint singleton mass divided by the conditioning mass. -/
theorem condDistrib_singleton_mass_of_ne_zero
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {μ : Measure α} [IsFiniteMeasure μ]
    {Y : α → γ} {Z : α → β} (hY : Measurable Y)
    (z : β) (y : γ) (hz : (μ.map Z) ({z} : Set β) ≠ 0) :
    (condDistrib Y Z μ z) ({y} : Set γ) =
      (μ.map (fun ω => (Z ω, Y ω))) ({(z, y)} : Set (β × γ)) /
        (μ.map Z) ({z} : Set β) := by
  have hset : ({z} : Set β) ×ˢ ({y} : Set γ) = ({(z, y)} : Set (β × γ)) := by
    ext p
    rcases p with ⟨z', y'⟩
    simp
  rw [condDistrib_apply_of_ne_zero hY z hz ({y} : Set γ)]
  rw [hset, ENNReal.div_eq_inv_mul]

/-- A conditional distribution singleton mass agrees with the discrete
`conditionalMass` ratio of the pushed-forward joint law. -/
theorem condDistrib_singleton_mass_eq_conditionalMass
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {μ : Measure α} [IsFiniteMeasure μ]
    {Y : α → γ} {Z : α → β} (hY : Measurable Y) (hZ : Measurable Z)
    (z : β) (y : γ) (hz : (μ.map Z) ({z} : Set β) ≠ 0) :
    (condDistrib Y Z μ z) ({y} : Set γ) =
      Causalean.SCM.ID.DiscreteID.conditionalMass
        (μ.map fun ω => (Y ω, Z ω)) y z := by
  rw [condDistrib_singleton_mass_of_ne_zero hY z y hz]
  unfold Causalean.SCM.ID.DiscreteID.conditionalMass
  unfold Causalean.SCM.ID.DiscreteID.singletonMass
  have hswap :
      (μ.map (fun ω => (Z ω, Y ω))) ({(z, y)} : Set (β × γ)) =
        (μ.map (fun ω => (Y ω, Z ω))) ({(y, z)} : Set (γ × β)) := by
    rw [Measure.map_apply (hZ.prod hY) (MeasurableSet.singleton (z, y))]
    rw [Measure.map_apply (hY.prod hZ) (MeasurableSet.singleton (y, z))]
    congr 1
    ext ω
    simp [and_comm]
  rw [← hswap]
  rw [Measure.map_map measurable_snd (hY.prod hZ)]
  rfl

/-- The observational conditional kernel singleton mass is the corresponding
observed pair singleton mass divided by the conditioning singleton mass. -/
theorem obsCondKernel_singleton_mass_of_ne_zero
    (M : Causalean.SCM N Ω) (Y CC : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed) (hCC : CC ⊆ M.observed)
    [MeasurableSingletonClass (ValuesOn CC (swigΩ Ω))]
    [MeasurableSingletonClass (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [∀ s : M.FixedValues, IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn CC (swigΩ Ω))]
    (s : M.FixedValues) (c : ValuesOn CC (swigΩ Ω))
    (y : ValuesOn Y (swigΩ Ω))
    (hc0 : ((M.obsKernel s).map (valuesProjection hCC))
        ({c} : Set (ValuesOn CC (swigΩ Ω))) ≠ 0)
    (hctop : ((M.obsKernel s).map (valuesProjection hCC))
        ({c} : Set (ValuesOn CC (swigΩ Ω))) ≠ ∞) :
    M.obsCondKernel Y CC hY hCC (s, c)
        ({y} : Set (ValuesOn Y (swigΩ Ω))) =
      ((M.obsKernel s).map
          (fun ω => (valuesProjection hCC ω, valuesProjection hY ω)))
          ({(c, y)} : Set (ValuesOn CC (swigΩ Ω) × ValuesOn Y (swigΩ Ω))) /
        ((M.obsKernel s).map (valuesProjection hCC))
          ({c} : Set (ValuesOn CC (swigΩ Ω))) := by
  classical
  have hpair :
      M.obsCondPairKernel Y CC hY hCC s =
        (M.obsKernel s).map
          (fun ω => (valuesProjection hCC ω, valuesProjection hY ω)) := by
    unfold obsCondPairKernel
    exact Kernel.map_apply M.obsKernel
      ((measurable_valuesProjection hCC).prodMk (measurable_valuesProjection hY)) s
  have hcomp := M.obsCondPairKernel_apply_eq_compProd Y CC hY hCC s
  haveI : IsMarkovKernel (M.obsCondKernel Y CC hY hCC) := by
    unfold obsCondKernel
    infer_instance
  have hmass :
      (M.obsCondPairKernel Y CC hY hCC s)
          ({(c, y)} : Set (ValuesOn CC (swigΩ Ω) × ValuesOn Y (swigΩ Ω))) =
        ((M.obsKernel s).map (valuesProjection hCC) ⊗ₘ
            (M.obsCondKernel Y CC hY hCC).sectR s)
          ({(c, y)} : Set (ValuesOn CC (swigΩ Ω) × ValuesOn Y (swigΩ Ω))) := by
    simpa using congrArg
      (fun ρ : Measure (ValuesOn CC (swigΩ Ω) × ValuesOn Y (swigΩ Ω)) =>
        ρ ({(c, y)} : Set (ValuesOn CC (swigΩ Ω) × ValuesOn Y (swigΩ Ω))))
      hcomp
  rw [compProd_singleton_mass] at hmass
  rw [hpair] at hmass
  rw [ENNReal.eq_div_iff hc0 hctop]
  simpa [Kernel.sectR] using hmass.symm

/-- A one-node observational step density is the conditional singleton mass
divided by the one-node reference singleton mass. -/
theorem obsStepCondDensity_eq_mass_ratio
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (i : Fin M.observed.card)
    [MeasurableSingletonClass (swigΩ Ω (M.observedAt i).val)]
    [∀ s' : M.FixedValues, IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω))
    (hac :
      (M.obsStepCondKernel i.isLt)
          (s, valuesProjection (M.prefixNodes_subset_observed i.val) x) ≪
        ref.μ (M.observedAt i).val)
    (href0 :
      ref.μ (M.observedAt i).val
          ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) ≠ 0)
    (hreftop :
      ref.μ (M.observedAt i).val
          ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) ≠ ∞) :
    M.obsStepCondDensity ref s i x =
      (M.obsStepCondKernel i.isLt)
          (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)
          ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) /
        ref.μ (M.observedAt i).val
          ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) := by
  unfold obsStepCondDensity
  exact rnDeriv_singleton_eq_div _ _ hac (x (M.observedAt i)) href0 hreftop

end Causalean.SCM
