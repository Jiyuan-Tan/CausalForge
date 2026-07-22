/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.FiniteReference
import Causalean.SCM.ID.Density.PiUnion
import Causalean.SCM.ID.GraphicalThms.CComponentFactor
import Causalean.Mathlib.MeasureTheory.RnDerivCompProdSigmaFinite
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff

/-! # Observational chain-rule density

For a dominated structural causal model with σ-finite node reference measures, the
joint observational density factors along the topological order of the observed
nodes as a product of one-node conditional densities, assuming the stepwise fibre
Radon--Nikodym data (fibre domination and a jointly measurable fibre derivative) is
available.  This is the density analogue of the kernel chain rule
`obsKernel_eq_qFactorProduct`; unlike the kernel version it holds for continuous
(Lebesgue-referenced) nodes, not just finite/discrete ones.

The right-hand side below is deliberately not a tautological copy of
`obsDensity`: each factor is the Radon--Nikodym derivative of the one-node
conditional kernel `obsStepCondKernel` against the corresponding one-node
reference measure, evaluated at the prefix and coordinate read from the full
observed assignment.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The **one-node conditional density factor** at an observed coordinate.

Given a full observed assignment, this reads the prefix before coordinate `i`,
applies the conditional kernel for the next observed node, and takes its
Radon--Nikodym derivative with respect to that node's reference measure. -/
noncomputable def obsStepCondDensity
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (i : Fin M.observed.card)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))] :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    ((M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)).rnDeriv
      (ref.μ (M.observedAt i).val)
      (x (M.observedAt i))

/-- The **chain-rule density product** for the observational law.

This is the product, in observed topological order, of the one-node conditional
density factors.  The product is scalar-valued, so later regrouping into
c-components is legitimate in a way that regrouping composed kernels is not. -/
noncomputable def qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x => ∏ i : Fin M.observed.card, M.obsStepCondDensity ref s i x

/-- Prefix node sets are monotone in the prefix length. -/
lemma prefixNodes_mono (M : Causalean.SCM N Ω) {m k : ℕ} (h : m ≤ k) :
    M.prefixNodes m ⊆ M.prefixNodes k := by
  intro v hv
  rcases (M.mem_prefixNodes_iff m v).mp hv with ⟨hobs, hlt⟩
  exact (M.mem_prefixNodes_iff k v).mpr ⟨hobs, lt_of_lt_of_le hlt h⟩

/-- The recursive prefix density product matching `obsChainKernel`.

At successor prefixes this multiplies the previous-prefix density by the
one-node conditional RN derivative for the newly adjoined observed node. -/
noncomputable def prefixDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    (k : ℕ) → ValuesOn (M.prefixNodes k) (swigΩ Ω) → ENNReal
  | 0, _ => 1
  | k + 1, z =>
      M.prefixDensityProduct ref s k
        (valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z) *
        if h : k < M.observed.card then
          ((M.obsStepCondKernel h)
              (s, valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z)).rnDeriv
            (ref.μ (M.observedAt ⟨k, h⟩).val)
            (z ⟨(M.observedAt ⟨k, h⟩).val,
              by
                rw [M.prefixNodes_succ h]
                exact Finset.mem_union_right _
                  (Finset.mem_singleton_self _)⟩)
        else
          1

/-- Per-step analytic hypotheses needed to expose the fibre Radon--Nikodym
derivative against a σ-finite one-node reference.

The global domination assumption gives joint domination of each successor prefix.
For an infinite σ-finite reference, Mathlib does not currently extract the
corresponding fibre domination or jointly measurable fibre RN representative, so
the chain-rule density theorem carries those as explicit assumptions. -/
def ObsStepFiberRN
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    Prop :=
  ∀ (k : ℕ) (hk : k < M.observed.card),
    let node : SWIGNode N := (M.observedAt ⟨k, hk⟩).val
    let νk : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
      jointRef ref (M.prefixNodes k)
    let chain : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
      M.obsChainKernel k (Nat.le_of_lt hk) s
    let stepK : ProbabilityTheory.Kernel
        (ValuesOn (M.prefixNodes k) (swigΩ Ω)) (swigΩ Ω node) :=
      (M.obsStepCondKernel hk).sectR s
    (∀ᵐ a ∂chain, stepK a ≪ ref.μ node) ∧
      AEMeasurable
        (fun p : ValuesOn (M.prefixNodes k) (swigΩ Ω) × swigΩ Ω node =>
          (stepK p.1).rnDeriv (ref.μ node) p.2)
        (νk.prod (ref.μ node))

/-- `Measure.pi` reindexes along `valuesEquivOfEq`, with **no** probability-measure
hypothesis (the index equality reduces the equiv to the identity).  This is the
σ-finite-friendly companion of `measurePreserving_valuesEquivOfEq`. -/
lemma map_pi_valuesEquivOfEq {M' : Type*} [DecidableEq M'] [Fintype M']
    {I J : Finset M'} {Ω' : M' → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (h : I = J) (μ : (i : {i // i ∈ I}) → MeasureTheory.Measure (Ω' i.val)) :
    (MeasureTheory.Measure.pi μ).map (valuesEquivOfEq (Ω := Ω') h)
      = MeasureTheory.Measure.pi (fun j : {j // j ∈ J} => μ ⟨j.val, h ▸ j.property⟩) := by
  subst h
  have hid : (⇑(valuesEquivOfEq (Ω := Ω') (rfl : I = I))
      : ValuesOn I Ω' → ValuesOn I Ω') = id := by
    funext ξ; rfl
  rw [hid, MeasureTheory.Measure.map_id]

/-- The scalar reference on one node maps to the singleton product reference. -/
lemma singletonValues_map_ref_eq_jointRef
    (ref : ReferenceMeasures Ω) (v : SWIGNode N) :
    (ref.μ v).map (singletonValues (Ω := Ω) (v := v))
      = jointRef ref ({v} : Finset (SWIGNode N)) := by
  classical
  rw [jointRef]
  let e := MeasurableEquiv.piUnique
    (fun i : {i // i ∈ ({v} : Finset (SWIGNode N))} => swigΩ Ω i.val)
  have hfun :
      (singletonValues (Ω := Ω) (v := v))
        = (fun x : swigΩ Ω v => (e.symm) (by simpa using x)) := by
    funext x
    ext i
    obtain ⟨w, hw⟩ := i
    have hwv : w = v := by simpa using hw
    subst w
    rfl
  calc
    MeasureTheory.Measure.map (singletonValues (Ω := Ω) (v := v)) (ref.μ v)
        = MeasureTheory.Measure.map
            (fun x : swigΩ Ω v => (e.symm) (by simpa using x)) (ref.μ v) := by
          rw [hfun]
    _ = MeasureTheory.Measure.pi
        (fun i : {i // i ∈ ({v} : Finset (SWIGNode N))} => ref.μ i.val) := by
      have hmp :=
        (MeasureTheory.measurePreserving_piUnique
          (fun i : {i // i ∈ ({v} : Finset (SWIGNode N))} => ref.μ i.val)).symm e
      simpa using hmp.map_eq

/-- Transport the full-prefix reference measure to the observed-value reference.

This is the final `Measure.pi` reindexing along
`prefixNodes observed.card = observed`. -/
lemma jointRef_prefix_card_map
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) :
    (jointRef ref (M.prefixNodes M.observed.card)).map
        (valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card)
      = jointRef ref M.observed := by
  rw [jointRef, jointRef,
    map_pi_valuesEquivOfEq M.prefixNodes_card (fun i => ref.μ i.val)]

/-- The successor prefix extension carries the product of the old-prefix reference
and the next-node reference to the successor-prefix reference. -/
lemma jointRef_extendObsPrefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    {k : ℕ} (hk : k < M.observed.card) :
    ((jointRef ref (M.prefixNodes k)).prod
        (ref.μ (M.observedAt ⟨k, hk⟩).val)).map (M.extendObsPrefix hk)
      = jointRef ref (M.prefixNodes (k + 1)) := by
  classical
  let v : SWIGNode N := (M.observedAt ⟨k, hk⟩).val
  let A : Finset (SWIGNode N) := M.prefixNodes k
  let B : Finset (SWIGNode N) := ({v} : Finset (SWIGNode N))
  let hDisj : Disjoint A B := by
    simpa [A, B, v] using M.prefixNodes_disjoint_singleton_next hk
  have hsing :
      (ref.μ v).map (singletonValues (Ω := Ω) (v := v)) = jointRef ref B := by
    simpa [B] using singletonValues_map_ref_eq_jointRef (Ω := Ω) ref v
  have hprod :
      ((jointRef ref A).prod (ref.μ v)).map
          (Prod.map id (singletonValues (Ω := Ω) (v := v)))
        = (jointRef ref A).prod (jointRef ref B) := by
    rw [← MeasureTheory.Measure.map_prod_map
      (jointRef ref A) (ref.μ v) measurable_id (measurable_singletonValues (Ω := Ω))]
    simp [hsing]
  have hunion :
      ((jointRef ref A).prod (jointRef ref B)).map
          ((valuesUnionEquiv (Ω := Ω) hDisj).symm)
        = jointRef ref (A ∪ B) := by
    have hmp :=
      (measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ).symm
        (valuesUnionEquiv (Ω := Ω) hDisj)
    simpa [jointRef] using hmp.map_eq
  unfold extendObsPrefix
  change
    (((jointRef ref A).prod (ref.μ v)).map
      ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hk).symm) ∘
        (fun p : ValuesOn A (swigΩ Ω) × swigΩ Ω v =>
          valuesUnionMk p.1 (singletonValues (Ω := Ω) (v := v) p.2))))
      = jointRef ref (M.prefixNodes (k + 1))
  rw [← MeasureTheory.Measure.map_map]
  · have hinner :
        (fun p : ValuesOn A (swigΩ Ω) × swigΩ Ω v =>
          valuesUnionMk p.1 (singletonValues (Ω := Ω) (v := v) p.2))
          =
        ((fun q : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
            valuesUnionMk q.1 q.2) ∘
          (Prod.map id (singletonValues (Ω := Ω) (v := v)))) := by
      rfl
    rw [hinner]
    rw [← MeasureTheory.Measure.map_map]
    · have hunion_fun :
          (fun q : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
              valuesUnionMk q.1 q.2)
            = ((valuesUnionEquiv (Ω := Ω) hDisj).symm) := by
        rfl
      rw [hunion_fun, hprod, hunion]
      rw [jointRef, map_pi_valuesEquivOfEq]
      rfl
    · exact measurable_valuesUnionMk (Ω := swigΩ Ω)
    · exact measurable_id.prodMap (measurable_singletonValues (Ω := Ω))
  · exact (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hk).symm).measurable
  · exact (measurable_valuesUnionMk (Ω := swigΩ Ω)).comp
      (measurable_id.prodMap (measurable_singletonValues (Ω := Ω)))

/-- The `i`-th one-step density factor read from a `k`-prefix assignment. -/
noncomputable def prefixStepDensityInPrefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (i : ℕ) (hi : i < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (i : ℕ) (hi : i < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ i : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes i) (swigΩ Ω))]
    (k : ℕ) (z : ValuesOn (M.prefixNodes k) (swigΩ Ω)) (i : ℕ) : ENNReal :=
  if hi : i < k then
    if hcard : i < M.observed.card then
      ((M.obsStepCondKernel hcard)
          (s, valuesProjection (M.prefixNodes_mono (Nat.le_of_lt hi)) z)).rnDeriv
        (ref.μ (M.observedAt ⟨i, hcard⟩).val)
        (z ⟨(M.observedAt ⟨i, hcard⟩).val,
          by
            rw [M.observedAt_mem_prefixNodes_iff k ⟨i, hcard⟩]
            exact hi⟩)
    else
      1
  else
    1

/-- The recursive prefix density product is the range product of its one-step
factors. -/
lemma prefixDensityProduct_eq_range_product
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (k : ℕ) (hk : k ≤ M.observed.card)
    (z : ValuesOn (M.prefixNodes k) (swigΩ Ω)) :
    M.prefixDensityProduct ref s k z =
      ∏ i ∈ Finset.range k, M.prefixStepDensityInPrefix ref s k z i := by
  induction k with
  | zero =>
      simp [prefixDensityProduct]
  | succ k ih =>
      have hkcard : k < M.observed.card := Nat.lt_of_succ_le hk
      rw [prefixDensityProduct]
      rw [ih (Nat.le_of_succ_le hk)
        (valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z)]
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl ?_
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have hisucc : i < k + 1 := Nat.lt_succ_of_lt hik
        have hicard : i < M.observed.card :=
          lt_of_lt_of_le hik (Nat.le_of_succ_le hk)
        have hproj :
            valuesProjection (M.prefixNodes_mono (Nat.le_of_lt hik))
                (valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z)
              =
            valuesProjection (M.prefixNodes_mono (Nat.le_of_lt hisucc)) z := by
          funext a
          rfl
        simp [prefixStepDensityInPrefix, hik, hisucc, hicard, hproj, valuesProjection]
      · simp [prefixStepDensityInPrefix, hkcard]

/-- At the full observed prefix, the recursive prefix density product is the
existing finite product over observed indices. -/
lemma prefixDensityProduct_card_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (y : ValuesOn (M.prefixNodes M.observed.card) (swigΩ Ω)) :
    M.prefixDensityProduct ref s M.observed.card y =
      M.qFactorDensityProduct ref s
        ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card) y) := by
  rw [prefixDensityProduct_eq_range_product M ref s M.observed.card (le_refl _) y]
  rw [Finset.prod_range]
  simp only [qFactorDensityProduct, obsStepCondDensity, prefixStepDensityInPrefix,
    valuesEquivOfEq]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  have hproj :
      valuesProjection (M.prefixNodes_subset_observed i.val)
          (valuesProjection (le_of_eq M.prefixNodes_card.symm) y)
        =
      valuesProjection (M.prefixNodes_mono (Nat.le_of_lt i.isLt)) y := by
    funext a
    rfl
  simp [i.isLt, hproj, valuesProjection]

/-- **Conditional factor of the composition-product Radon–Nikodym derivative.**

For composition-products with the *same* first measure `μ`, the density of
`μ ⊗ₘ κ` against `μ ⊗ₘ η` is the per-slice (kernel) Radon–Nikodym derivative
`dκ/dη`.  This is the disintegration form Mathlib's `rnDeriv_compProd` leaves
implicit; it is what turns the second factor there into a one-step conditional
density. -/
lemma rnDeriv_compProd_same_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : MeasureTheory.Measure α)
    (κ η : ProbabilityTheory.Kernel α β)
    [MeasureTheory.IsFiniteMeasure μ]
    [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel η]
    (h_ac : ∀ a, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)
      =ᵐ[μ ⊗ₘ η] fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2 := by
  have hκeq : η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η) = κ :=
    ProbabilityTheory.Kernel.ext fun a =>
      ProbabilityTheory.Kernel.withDensity_rnDeriv_eq (h_ac a)
  haveI : ProbabilityTheory.IsSFiniteKernel
      (η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η)) := by
    rw [hκeq]; infer_instance
  have hcp : μ ⊗ₘ κ
      = (μ ⊗ₘ η).withDensity (fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2) := by
    conv_lhs => rw [← hκeq]
    exact MeasureTheory.Measure.compProd_withDensity
      (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)
  rw [hcp]
  exact MeasureTheory.Measure.rnDeriv_withDensity (μ ⊗ₘ η)
    (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)

/-- Pull absolute continuity back through a measurable embedding. -/
lemma absolutelyContinuous_of_map_measurableEmbedding {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) {μ ν : MeasureTheory.Measure α}
    (h : μ.map f ≪ ν.map f) :
    μ ≪ ν := by
  intro A hνA
  have hν_image : ν.map f (f '' A) = 0 := by
    rw [hf.map_apply ν (f '' A), hf.injective.preimage_image]
    exact hνA
  have hμ_image : μ.map f (f '' A) = 0 := h hν_image
  rw [hf.map_apply μ (f '' A), hf.injective.preimage_image] at hμ_image
  exact hμ_image

/-- Same-left composition-product RN derivative under a.e. fibre absolute
continuity.  This is the a.e. variant needed after extracting fibre domination
from product domination. -/
lemma rnDeriv_compProd_same_left_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : MeasureTheory.Measure α)
    (κ η : ProbabilityTheory.Kernel α β)
    [MeasureTheory.IsFiniteMeasure μ]
    [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel η]
    (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)
      =ᵐ[μ ⊗ₘ η] fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2 := by
  have hκeq : κ =ᵐ[μ]
      η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η) := by
    filter_upwards [h_ac] with a ha
    exact (ProbabilityTheory.Kernel.withDensity_rnDeriv_eq ha).symm
  haveI : ProbabilityTheory.IsSFiniteKernel
      (η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η)) := by
    infer_instance
  have hcp : μ ⊗ₘ κ
      = (μ ⊗ₘ η).withDensity (fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2) := by
    calc
      μ ⊗ₘ κ = μ ⊗ₘ
          (η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η)) :=
        MeasureTheory.Measure.compProd_congr hκeq
      _ = (μ ⊗ₘ η).withDensity
          (fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2) := by
        exact MeasureTheory.Measure.compProd_withDensity
          (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)
  rw [hcp]
  exact MeasureTheory.Measure.rnDeriv_withDensity (μ ⊗ₘ η)
    (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)

/-- σ-finite product-reference RN derivative for a finite kernel, under explicit
fibre domination and fibre-density measurability.

This is the measure-level replacement for `ProbabilityTheory.rnDeriv_compProd`
when the second reference is a σ-finite measure, not a finite kernel. -/
lemma rnDeriv_compProd_prod_sigmaFinite_of_fiber_ac {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : MeasureTheory.Measure α) (ρ : MeasureTheory.Measure β)
    (κ : ProbabilityTheory.Kernel α β)
    (f : α → ENNReal)
    [MeasureTheory.IsFiniteMeasure μ]
    [MeasureTheory.SigmaFinite ν] [MeasureTheory.SigmaFinite ρ]
    [ProbabilityTheory.IsFiniteKernel κ]
    (hμν : μ ≪ ν) (hfiber : ∀ᵐ a ∂μ, κ a ≪ ρ)
    (hfiber_meas :
      AEMeasurable
        (fun p : α × β => (κ p.1).rnDeriv ρ p.2) (ν.prod ρ))
    (hf : μ.rnDeriv ν =ᵐ[ν] f) :
    (μ ⊗ₘ κ).rnDeriv (ν.prod ρ)
      =ᵐ[ν.prod ρ] fun p => f p.1 * (κ p.1).rnDeriv ρ p.2 := by
  exact MeasureTheory.rnDeriv_compProd_prod_sigmaFinite
    μ ν ρ κ f hμν hfiber hfiber_meas hf

/-- Domination of the recursive observed-prefix chain by the prefix reference.

Proof plan: use `obsKernel_map_prefixNodes` to identify the chain as the
push-forward of `obsKernel s`; push `hdom s` forward; then prove the
finite-index `Measure.pi` marginal helper
`(jointRef ref M.observed).map (valuesProjection ...) ≪ jointRef ref (prefixNodes k)`.
-/
lemma obsChainKernel_absolutelyContinuous_jointRef_prefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (k : ℕ) (hk : k ≤ M.observed.card) :
    M.obsChainKernel k hk s ≪ jointRef ref (M.prefixNodes k) := by
  classical
  -- The chain kernel is the prefix marginal of the (dominated) observational law.
  rw [← M.obsKernel_map_prefixNodes s k hk]
  have hsubset : M.prefixNodes k ⊆ M.observed := M.prefixNodes_subset_observed k
  have hDisj : Disjoint (M.prefixNodes k) (M.observed \ M.prefixNodes k) :=
    disjoint_sdiff_self_right
  have hAB : M.prefixNodes k ∪ (M.observed \ M.prefixNodes k) = M.observed :=
    Finset.union_sdiff_of_subset hsubset
  -- The prefix projection factors as `fst ∘ union-equiv ∘ reindex`.
  have hfun :
      (valuesProjection (Ω := swigΩ Ω) hsubset)
        = Prod.fst ∘ (valuesUnionEquiv (Ω := Ω) hDisj) ∘
            (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm) := by
    funext ω i; rfl
  -- The reference marginal is a scalar multiple of the prefix reference.
  have hmarg :
      (jointRef ref M.observed).map (valuesProjection hsubset)
        = (jointRef ref (M.observed \ M.prefixNodes k) Set.univ)
            • jointRef ref (M.prefixNodes k) := by
    rw [hfun]
    rw [← MeasureTheory.Measure.map_map measurable_fst
        ((valuesUnionEquiv (Ω := Ω) hDisj).measurable.comp
          (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable)]
    rw [← MeasureTheory.Measure.map_map
        (valuesUnionEquiv (Ω := Ω) hDisj).measurable
        (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable]
    rw [jointRef,
      map_pi_valuesEquivOfEq hAB.symm (fun i : {i // i ∈ M.observed} => ref.μ i.val)]
    have hsplit :
        (MeasureTheory.Measure.pi
            (fun j : {j // j ∈ M.prefixNodes k ∪ (M.observed \ M.prefixNodes k)} =>
              ref.μ j.val)).map (valuesUnionEquiv (Ω := Ω) hDisj)
          = (jointRef ref (M.prefixNodes k)).prod
              (jointRef ref (M.observed \ M.prefixNodes k)) := by
      have hmp := measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ
      simpa [jointRef] using hmp.map_eq
    rw [hsplit, MeasureTheory.Measure.map_fst_prod]
  -- Push the joint domination forward and absorb the scalar.
  refine ((hdom s).map (measurable_valuesProjection hsubset)).trans ?_
  rw [hmarg]
  intro t ht
  simp [MeasureTheory.Measure.smul_apply, ht]

/-- General prefix-level RN derivative for the recursive observational chain. -/
lemma obsChainKernel_rnDeriv_eq_prefixDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    ∀ (k : ℕ) (hk : k ≤ M.observed.card),
      (M.obsChainKernel k hk s).rnDeriv (jointRef ref (M.prefixNodes k))
        =ᵐ[jointRef ref (M.prefixNodes k)]
          M.prefixDensityProduct ref s k := by
  intro k
  induction k with
  | zero =>
      intro hk
      -- `ValuesOn (prefixNodes 0)` is a one-point space; both measures are probability
      -- measures there, hence equal, and `rnDeriv_self =ᵐ 1 = prefixDensityProduct 0`.
      have hsub : Subsingleton (ValuesOn (M.prefixNodes 0) (swigΩ Ω)) :=
        ⟨fun a b => funext fun i =>
          absurd (M.prefixNodes_zero ▸ i.property) (Finset.notMem_empty i.val)⟩
      have heq : M.obsChainKernel 0 hk s = jointRef ref (M.prefixNodes 0) := by
        refine MeasureTheory.Measure.ext fun A _ => ?_
        rcases Set.eq_empty_or_nonempty A with rfl | hA
        · simp
        · obtain ⟨a, ha⟩ := hA
          have hAuniv : A = Set.univ :=
            Set.eq_univ_of_forall fun x => (hsub.elim x a) ▸ ha
          subst hAuniv
          rw [MeasureTheory.measure_univ, jointRef, MeasureTheory.Measure.pi_univ]
          symm
          apply Finset.prod_eq_one
          intro i _
          obtain ⟨_, hlt⟩ := (M.mem_prefixNodes_iff 0 i.val).mp i.property
          exact absurd hlt (Nat.not_lt_zero _)
      rw [heq]
      have h1 : M.prefixDensityProduct ref s 0 = (fun _ => (1 : ENNReal)) := rfl
      rw [h1]
      exact MeasureTheory.Measure.rnDeriv_self _
  | succ k ih =>
      intro hk
      classical
      have hkc : k < M.observed.card := Nat.lt_of_succ_le hk
      have hkprev : k ≤ M.observed.card := Nat.le_of_succ_le hk
      let node : SWIGNode N := (M.observedAt ⟨k, hkc⟩).val
      let νk : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
        jointRef ref (M.prefixNodes k)
      let refnode : MeasureTheory.Measure (swigΩ Ω node) := ref.μ node
      let chain : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
        M.obsChainKernel k hkprev s
      let stepK : ProbabilityTheory.Kernel
          (ValuesOn (M.prefixNodes k) (swigΩ Ω)) (swigΩ Ω node) :=
        (M.obsStepCondKernel hkc).sectR s
      let ext :
          ValuesOn (M.prefixNodes k) (swigΩ Ω) × swigΩ Ω node →
            ValuesOn (M.prefixNodes (k + 1)) (swigΩ Ω) :=
        M.extendObsPrefix hkc
      have hchainSucc :
          M.obsChainKernel (k + 1) hk s = (chain ⊗ₘ stepK).map ext := by
        dsimp [chain, stepK, ext]
        change ((((M.obsChainKernel k hkprev) ⊗ₖ
          (M.obsStepCondKernel hkc)).map (M.extendObsPrefix hkc)) s)
            = (((M.obsChainKernel k hkprev) s) ⊗ₘ
              ((M.obsStepCondKernel hkc).sectR s)).map (M.extendObsPrefix hkc)
        rw [ProbabilityTheory.Kernel.map_apply _ (M.measurable_extendObsPrefix hkc)]
        rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
      have hrefSucc :
          jointRef ref (M.prefixNodes (k + 1))
            = (νk.prod refnode).map ext := by
        dsimp [νk, refnode, node, ext]
        exact (jointRef_extendObsPrefix M ref hkc).symm
      have hsingle_emb : MeasurableEmbedding
          (singletonValues (Ω := Ω) (v := node)) := by
        refine ⟨?_, measurable_singletonValues (Ω := Ω), ?_⟩
        · intro x y hxy
          have := congrArg (singletonValue (Ω := Ω) (v := node)) hxy
          simpa using this
        · intro A hA
          have hpre :
              singletonValues (Ω := Ω) (v := node) '' A
                = (singletonValue (Ω := Ω) (v := node)) ⁻¹' A := by
            ext x
            constructor
            · rintro ⟨a, ha, rfl⟩
              simpa using ha
            · intro hx
              refine ⟨singletonValue (Ω := Ω) (v := node) x, hx, ?_⟩
              exact singletonValues_singletonValue (Ω := Ω) x
          rw [hpre]
          exact hA.preimage (measurable_singletonValue (Ω := Ω))
      have hext_emb : MeasurableEmbedding ext := by
        dsimp [ext, node]
        unfold extendObsPrefix
        refine
          (valuesEquivOfEq (Ω := swigΩ Ω)
            (M.prefixNodes_succ hkc).symm).measurableEmbedding.comp ?_
        change MeasurableEmbedding
          ((fun q : ValuesOn (M.prefixNodes k) (swigΩ Ω) ×
              ValuesOn ({(M.observedAt ⟨k, hkc⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) =>
              valuesUnionMk q.1 q.2) ∘
            Prod.map id
              (singletonValues (Ω := Ω) (v := (M.observedAt ⟨k, hkc⟩).val)))
        refine ((valuesUnionEquiv (Ω := Ω)
          (M.prefixNodes_disjoint_singleton_next hkc)).symm.measurableEmbedding).comp ?_
        exact MeasurableEmbedding.id.prodMap hsingle_emb
      have hcore :
          (chain ⊗ₘ stepK).rnDeriv (νk.prod refnode)
            =ᵐ[νk.prod refnode]
              fun p =>
                M.prefixDensityProduct ref s k p.1 *
                  (stepK p.1).rnDeriv refnode p.2 := by
        have hchain_ac : chain ≪ νk := by
          dsimp [chain, νk]
          exact M.obsChainKernel_absolutelyContinuous_jointRef_prefix ref hdom s k hkprev
        have hfiber := hstep k hkc
        have hfiber_meas :
            AEMeasurable
              (fun p : ValuesOn (M.prefixNodes k) (swigΩ Ω) × swigΩ Ω node =>
                (stepK p.1).rnDeriv refnode p.2)
              (νk.prod refnode) :=
          hfiber.2
        exact rnDeriv_compProd_prod_sigmaFinite_of_fiber_ac
          chain νk refnode stepK (M.prefixDensityProduct ref s k)
          hchain_ac hfiber.1 hfiber_meas (ih hkprev)
      rw [hchainSucc, hrefSucc, Filter.EventuallyEq, hext_emb.ae_map_iff]
      filter_upwards [hext_emb.rnDeriv_map (chain ⊗ₘ stepK) (νk.prod refnode),
        hcore] with p hmap hp
      rw [hmap, hp]
      dsimp [ext, stepK, node]
      have hpair := M.valuesUnionEquiv_extendObsPrefix hkc p
      have hproj_ext :
          valuesProjection (M.prefixNodes_mono (Nat.le_succ k))
              (M.extendObsPrefix hkc p) = p.1 := by
        funext i
        have hi := congrArg (fun q => q.1 i) hpair
        simpa [valuesUnionEquiv, valuesProjection] using hi
      have hcoord_ext :
          M.extendObsPrefix hkc p ⟨(M.observedAt ⟨k, hkc⟩).val, by
            rw [M.prefixNodes_succ hkc]
            exact Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩ = p.2 := by
        have hnext :=
          congrArg
            (fun q => singletonValue (Ω := Ω)
              (v := (M.observedAt ⟨k, hkc⟩).val) q.2) hpair
        simpa using hnext
      rw [prefixDensityProduct]
      simp [hkc, hproj_ext, hcoord_ext, refnode]
      rfl

/-- RN-derivative transport for `qFactorProduct`, assuming the final reference
transport has already been identified. -/
lemma qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback_of_jointRef
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (href :
      (jointRef ref (M.prefixNodes M.observed.card)).map
          (valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card)
        = jointRef ref M.observed)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    (M.qFactorProduct s).rnDeriv (jointRef ref M.observed)
      =ᵐ[jointRef ref M.observed]
        fun x =>
          ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
            (jointRef ref (M.prefixNodes M.observed.card)))
            ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card).symm x) := by
  classical
  set e := valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card with he
  have hf : MeasurableEmbedding
      (e : ValuesOn (M.prefixNodes M.observed.card) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω)) := e.measurableEmbedding
  have hq : M.qFactorProduct s
      = (M.obsChainKernel M.observed.card (le_refl _) s).map e := by
    rw [qFactorProduct, ProbabilityTheory.Kernel.map_apply _ e.measurable]
  rw [hq, ← href, Filter.EventuallyEq, hf.ae_map_iff]
  filter_upwards [hf.rnDeriv_map (M.obsChainKernel M.observed.card (le_refl _) s)
    (jointRef ref (M.prefixNodes M.observed.card))] with y hy
  simpa using hy

/-- Peel the final `qFactorProduct` map back to the full prefix chain kernel.

This is the `MeasurableEmbedding.rnDeriv_map` transport step for
`qFactorProduct = (obsChainKernel card).map (valuesEquivOfEq prefixNodes_card)`. -/
lemma qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    (M.qFactorProduct s).rnDeriv (jointRef ref M.observed)
      =ᵐ[jointRef ref M.observed]
        fun x =>
          ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
            (jointRef ref (M.prefixNodes M.observed.card)))
            ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card).symm x) := by
  exact
    qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback_of_jointRef
      M ref s (jointRef_prefix_card_map M ref)

/-- The analytic prefix induction for the density chain rule.

Inducting over `obsChainKernel` identifies the Radon--Nikodym derivative of the
full observed-prefix chain with the recursive prefix density product.  Each
successor step uses `jointRef_extendObsPrefix`, the measurable embedding
transport for Radon--Nikodym derivatives, and the comp-product derivative rule,
then the final prefix product is rewritten as `qFactorDensityProduct`. -/
lemma obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix_induction
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card))
      =ᵐ[jointRef ref (M.prefixNodes M.observed.card)]
        fun y =>
          M.qFactorDensityProduct ref s
            ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card) y) := by
  exact
    (obsChainKernel_rnDeriv_eq_prefixDensityProduct M ref hdom s hstep
      M.observed.card (le_refl _)).trans
      (Filter.EventuallyEq.of_eq
        (funext (prefixDensityProduct_card_eq_qFactorDensityProduct M ref s)))

/-- Prefix-level analytic chain rule at the full observed prefix.

The right side is the full density product, read after transporting a full-prefix
assignment to an observed assignment.  This wrapper exposes the completed prefix
induction in the shape consumed by the final observed-coordinate transport. -/
lemma obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card))
      =ᵐ[jointRef ref (M.prefixNodes M.observed.card)]
        fun y =>
          M.qFactorDensityProduct ref s
            ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card) y) := by
  exact obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix_induction
    M ref hdom s hstep

/-- Push the full-prefix a.e. density identity forward, assuming the reference
transport and prefix-level chain rule. -/
lemma obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct_of_prefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (href :
      (jointRef ref (M.prefixNodes M.observed.card)).map
          (valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card)
        = jointRef ref M.observed)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hprefix :
      (M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
          (jointRef ref (M.prefixNodes M.observed.card))
        =ᵐ[jointRef ref (M.prefixNodes M.observed.card)]
          fun y =>
            M.qFactorDensityProduct ref s
              ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card) y)) :
    (fun x =>
      ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card)))
        ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card).symm x))
      =ᵐ[jointRef ref M.observed]
        M.qFactorDensityProduct ref s := by
  classical
  set e := valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card with he
  have hf : MeasurableEmbedding
      (e : ValuesOn (M.prefixNodes M.observed.card) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω)) := e.measurableEmbedding
  rw [← href, Filter.EventuallyEq, hf.ae_map_iff]
  filter_upwards [hprefix] with y hy
  simpa using hy

/-- Push the full-prefix a.e. density identity forward to observed coordinates. -/
lemma obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (fun x =>
      ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card)))
        ((valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card).symm x))
      =ᵐ[jointRef ref M.observed]
        M.qFactorDensityProduct ref s := by
  exact
    obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct_of_prefix
      M ref s (jointRef_prefix_card_map M ref)
      (obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix M ref hdom s hstep)

/-- **Analytic chain rule for the mapped observational product kernel.**

The Radon--Nikodym derivative of the kernel-native observational chain product
with respect to the product reference equals the product of the per-step
conditional Radon--Nikodym derivatives.  This is the measure-theoretic core:
one proves it by induction over `obsChainKernel`, applying
`ProbabilityTheory.rnDeriv_compProd` at each successor step and transporting
the result through `extendObsPrefix` and `valuesEquivOfEq`.

The domination hypothesis `DominatedObs M ref` is essential: without absolute
continuity the joint law can have a part singular to the reference, where the
Radon--Nikodym derivative vanishes while the product of conditional densities
need not, so the identity would be false. -/
theorem qFactorProduct_rnDeriv_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (M.qFactorProduct s).rnDeriv (jointRef ref M.observed)
      =ᵐ[jointRef ref M.observed]
        M.qFactorDensityProduct ref s := by
  exact
    (qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback M ref s).trans
      (obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct M ref hdom s hstep)

/-- **Observational density chain rule.**

The joint observational density equals, almost everywhere with respect to the
joint reference measure, the product of the one-node conditional densities along
the observed topological order, provided the model is dominated, every node
reference measure is σ-finite, and the stepwise fibre Radon--Nikodym condition
holds.  Unlike a finite/discrete statement this covers continuous reference
measures. -/
theorem obsDensity_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    M.obsDensity ref s =ᵐ[jointRef ref M.observed]
      M.qFactorDensityProduct ref s := by
  unfold obsDensity
  rw [c_component_factorization M s]
  exact M.qFactorProduct_rnDeriv_eq_qFactorDensityProduct ref hdom s hstep

end Causalean.SCM
