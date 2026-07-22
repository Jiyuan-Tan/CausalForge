/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.GraphicalThms.DoGFormula
import Causalean.SCM.Do.ObsMarkov
import Causalean.SCM.ID.Density.QFactor
import Causalean.SCM.ID.Density.DoLawMarginal
import Causalean.SCM.ID.GraphicalThms.QFactorIdentity
import Causalean.Graph.DSep.InduceTransport

/-!
# Tian density assembly for the ID do-law g-formula

This file states the Tian density factorization used by the graphical ID
algorithm: the post-intervention law on the observed ancestors of the query is
identified by a product of district factors recovered from the observational
density.

The statements avoid `SCM.induce` for the post-intervention ancestral law: all
district factors of the do-law marginal are defined from the marginal measure
itself, using Tian's prefix-ratio/conditional construction on
`D = An_{G_X}(Y) ∩ observed`.

The main results are:

* `rnDeriv_eq_tianDensityProduct`, a measure-only chain rule expressing a
  dominated finite law's density as a product of one-coordinate conditional
  densities in graph order.
* `markov_tian_cfactorization_density`, which regroups that product into Tian
  district factors for a globally Markov finite law.
* `doObsKernelAncestralMarginal_globalMarkovOn`, the SCM-to-measure Markov bridge
  for the ancestral do-law marginal.
* `doAncestralDistrictDensity_recovered_from_obs` and
  `doObsKernelAncestralMarginal_tian_cfactorization_density`, the ID-specific
  recovery and factorization statements used by the discrete soundness layer.
-/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- Membership in a graph-ordered prefix of `D` is exactly index membership
below the prefix length. -/
lemma mem_prefixIn_iff (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (n : ℕ) (v : SWIGNode N) :
    v ∈ H.prefixIn D n ↔
      ∃ h : v ∈ D, (H.nodeIndex D ⟨v, h⟩).val < n := by
  unfold SWIGGraph.prefixIn
  constructor
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hD, hltif⟩
    exact ⟨hD, by simpa [hD] using hltif⟩
  · rintro ⟨hD, hlt⟩
    exact Finset.mem_filter.mpr ⟨hD, by simpa [hD] using hlt⟩

/-- The `D`-prefix of length zero is empty. -/
lemma prefixIn_zero (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D 0 = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_prefixIn_iff H D 0 v).mp hv with ⟨_, hlt⟩
    omega
  · simp

/-- The node at index `i` belongs to the first `n` `D`-nodes iff `i < n`. -/
lemma nodesAt_mem_prefixIn_iff (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (n : ℕ) (i : Fin D.card) :
    (H.nodesAt D i).val ∈ H.prefixIn D n ↔ i.val < n := by
  rw [mem_prefixIn_iff]
  constructor
  · rintro ⟨hD, hlt⟩
    have hidx : H.nodeIndex D ⟨(H.nodesAt D i).val, hD⟩ = i := by
      have hsub :
          (⟨(H.nodesAt D i).val, hD⟩ : {v // v ∈ D}) = H.nodesAt D i :=
        Subtype.ext rfl
      rw [hsub]
      simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
    rwa [hidx] at hlt
  · intro hlt
    exact ⟨(H.nodesAt D i).property,
      by
        have hidx : H.nodeIndex D (H.nodesAt D i) = i := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        simpa [hidx] using hlt⟩

/-- The full `D`-prefix is `D`. -/
lemma prefixIn_card (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D D.card = D := by
  ext v
  constructor
  · exact fun hv => H.prefixIn_subset D D.card hv
  · intro hv
    exact (mem_prefixIn_iff H D D.card v).mpr
      ⟨hv, (H.nodeIndex D ⟨v, hv⟩).isLt⟩

/-- Prefix sets are monotone in the prefix length. -/
lemma prefixIn_mono (H : SWIGGraph N) (D : Finset (SWIGNode N)) {m k : ℕ}
    (h : m ≤ k) :
    H.prefixIn D m ⊆ H.prefixIn D k := by
  intro v hv
  rcases (mem_prefixIn_iff H D m v).mp hv with ⟨hD, hlt⟩
  exact (mem_prefixIn_iff H D k v).mpr ⟨hD, lt_of_lt_of_le hlt h⟩

/-- The next `D`-node is not in the previous `D`-prefix. -/
lemma nodesAt_not_mem_prefixIn (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    (H.nodesAt D ⟨n, hn⟩).val ∉ H.prefixIn D n := by
  rw [nodesAt_mem_prefixIn_iff H D n ⟨n, hn⟩]
  exact Nat.lt_irrefl n

/-- The successor `D`-prefix is obtained by adjoining the next `D`-node. -/
lemma prefixIn_succ (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    H.prefixIn D (n + 1) =
      H.prefixIn D n ∪ {(H.nodesAt D ⟨n, hn⟩).val} := by
  ext v
  constructor
  · intro hv
    rcases (mem_prefixIn_iff H D (n + 1) v).mp hv with ⟨hD, hlt⟩
    by_cases hlt_n : (H.nodeIndex D ⟨v, hD⟩).val < n
    · exact Finset.mem_union_left _ ((mem_prefixIn_iff H D n v).mpr ⟨hD, hlt_n⟩)
    · have hidx_val : (H.nodeIndex D ⟨v, hD⟩).val = n := by omega
      have hidx : H.nodeIndex D ⟨v, hD⟩ = ⟨n, hn⟩ := Fin.ext hidx_val
      have hv_eq : v = (H.nodesAt D ⟨n, hn⟩).val := by
        have hround : H.nodesAt D (H.nodeIndex D ⟨v, hD⟩) = ⟨v, hD⟩ := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        rw [hidx] at hround
        exact congrArg Subtype.val hround.symm
      exact Finset.mem_union_right _ (by simp [hv_eq])
  · intro hv
    rcases Finset.mem_union.mp hv with hvpre | hvlast
    · rcases (mem_prefixIn_iff H D n v).mp hvpre with ⟨hD, hlt⟩
      exact (mem_prefixIn_iff H D (n + 1) v).mpr ⟨hD, by omega⟩
    · have hv_eq : v = (H.nodesAt D ⟨n, hn⟩).val := by simpa using hvlast
      subst hv_eq
      rw [nodesAt_mem_prefixIn_iff H D (n + 1) ⟨n, hn⟩]
      exact Nat.lt_succ_self n

/-- The previous `D`-prefix is disjoint from the singleton next node. -/
lemma prefixIn_disjoint_singleton_next (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    Disjoint (H.prefixIn D n)
      ({(H.nodesAt D ⟨n, hn⟩).val} : Finset (SWIGNode N)) := by
  rw [Finset.disjoint_singleton_right]
  exact nodesAt_not_mem_prefixIn H D hn

/-- Extend a `D`-prefix assignment by the next singleton coordinate. -/
noncomputable def extendTianPrefix (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    ValuesOn (H.prefixIn D n) (swigΩ Ω) ×
        ValuesOn ({(H.nodesAt D ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) →
      ValuesOn (H.prefixIn D (n + 1)) (swigΩ Ω) :=
  fun p =>
    (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn).symm)
      (valuesUnionMk p.1 p.2)

/-- Prefix extension is measurable. -/
lemma measurable_extendTianPrefix (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    Measurable (extendTianPrefix (Ω := Ω) H D hn) := by
  unfold extendTianPrefix
  exact (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn).symm).measurable.comp
    (measurable_valuesUnionMk (Ω := swigΩ Ω))

/-- The successor-prefix extension is inverse to the union-equivalence view of
the successor prefix. -/
lemma valuesUnionEquiv_extendTianPrefix (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card)
    (p : ValuesOn (H.prefixIn D n) (swigΩ Ω) ×
        ValuesOn ({(H.nodesAt D ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω)) :
    valuesUnionEquiv (Ω := Ω) (prefixIn_disjoint_singleton_next H D hn)
        ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn))
          (extendTianPrefix (Ω := Ω) H D hn p))
      = p := by
  change valuesUnionEquiv (Ω := Ω) (prefixIn_disjoint_singleton_next H D hn)
      ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn))
        ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn)).symm
          (valuesUnionMk p.1 p.2))) = p
  have hcast :
      (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn))
        ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn)).symm
          (valuesUnionMk p.1 p.2))
        =
      valuesUnionMk p.1 p.2 := by
    change (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn)).toFun
        ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn)).invFun
          (valuesUnionMk p.1 p.2))
      = valuesUnionMk p.1 p.2
    exact (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn)).right_inv _
  rw [hcast]
  change (valuesUnionEquiv (Ω := Ω) (prefixIn_disjoint_singleton_next H D hn)).toFun
      ((valuesUnionEquiv (Ω := Ω) (prefixIn_disjoint_singleton_next H D hn)).invFun p) = p
  exact (valuesUnionEquiv (Ω := Ω) (prefixIn_disjoint_singleton_next H D hn)).right_inv p

/-- The successor prefix extension carries the product of the old-prefix
reference and the next singleton reference to the successor-prefix reference. -/
lemma jointRef_extendTianPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    {k : ℕ} (hk : k < D.card) :
    ((Causalean.SCM.jointRef ref (H.prefixIn D k)).prod
        (Causalean.SCM.jointRef ref
          ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)))).map
        (extendTianPrefix (Ω := Ω) H D hk)
      = Causalean.SCM.jointRef ref (H.prefixIn D (k + 1)) := by
  classical
  let v : SWIGNode N := (H.nodesAt D ⟨k, hk⟩).val
  let A : Finset (SWIGNode N) := H.prefixIn D k
  let B : Finset (SWIGNode N) := ({v} : Finset (SWIGNode N))
  let hDisj : Disjoint A B := by
    simpa [A, B, v] using prefixIn_disjoint_singleton_next H D hk
  have hunion :
      ((Causalean.SCM.jointRef ref A).prod (Causalean.SCM.jointRef ref B)).map
          ((valuesUnionEquiv (Ω := Ω) hDisj).symm)
        = Causalean.SCM.jointRef ref (A ∪ B) := by
    have hmp :=
      (Causalean.SCM.measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ).symm
        (valuesUnionEquiv (Ω := Ω) hDisj)
    simpa [Causalean.SCM.jointRef] using hmp.map_eq
  unfold extendTianPrefix
  change
    (((Causalean.SCM.jointRef ref A).prod (Causalean.SCM.jointRef ref B)).map
      ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hk).symm) ∘
        (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
          valuesUnionMk p.1 p.2)))
      = Causalean.SCM.jointRef ref (H.prefixIn D (k + 1))
  rw [← MeasureTheory.Measure.map_map]
  · have hinner :
        (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
          valuesUnionMk p.1 p.2)
          = ((valuesUnionEquiv (Ω := Ω) hDisj).symm) := by
      rfl
    rw [hinner, hunion]
    rw [Causalean.SCM.jointRef, Causalean.SCM.map_pi_valuesEquivOfEq]
    rfl
  · exact (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hk).symm).measurable
  · exact measurable_valuesUnionMk (Ω := swigΩ Ω)

/-- The reference marginal of any `D`-prefix is absolutely continuous with
respect to the corresponding product reference. -/
lemma jointRef_map_prefixIn_absolutelyContinuous
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (k : ℕ) :
    (Causalean.SCM.jointRef ref D).map
        (valuesProjection (H.prefixIn_subset D k))
      ≪ Causalean.SCM.jointRef ref (H.prefixIn D k) := by
  classical
  have hsubset : H.prefixIn D k ⊆ D := H.prefixIn_subset D k
  have hDisj : Disjoint (H.prefixIn D k) (D \ H.prefixIn D k) :=
    disjoint_sdiff_self_right
  have hAB : H.prefixIn D k ∪ (D \ H.prefixIn D k) = D :=
    Finset.union_sdiff_of_subset hsubset
  have hfun :
      (valuesProjection (Ω := swigΩ Ω) hsubset)
        = Prod.fst ∘ (valuesUnionEquiv (Ω := Ω) hDisj) ∘
            (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm) := by
    funext ω i
    rfl
  have hmarg :
      (Causalean.SCM.jointRef ref D).map (valuesProjection hsubset)
        = (Causalean.SCM.jointRef ref (D \ H.prefixIn D k) Set.univ)
            • Causalean.SCM.jointRef ref (H.prefixIn D k) := by
    rw [hfun]
    rw [← MeasureTheory.Measure.map_map measurable_fst
        ((valuesUnionEquiv (Ω := Ω) hDisj).measurable.comp
          (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable)]
    rw [← MeasureTheory.Measure.map_map
        (valuesUnionEquiv (Ω := Ω) hDisj).measurable
        (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable]
    rw [Causalean.SCM.jointRef,
      Causalean.SCM.map_pi_valuesEquivOfEq hAB.symm
        (fun i : {i // i ∈ D} => ref.μ i.val)]
    have hsplit :
        (MeasureTheory.Measure.pi
            (fun j : {j // j ∈ H.prefixIn D k ∪ (D \ H.prefixIn D k)} =>
              ref.μ j.val)).map (valuesUnionEquiv (Ω := Ω) hDisj)
          = (Causalean.SCM.jointRef ref (H.prefixIn D k)).prod
              (Causalean.SCM.jointRef ref (D \ H.prefixIn D k)) := by
      have hmp := Causalean.SCM.measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ
      simpa [Causalean.SCM.jointRef] using hmp.map_eq
    rw [hsplit, MeasureTheory.Measure.map_fst_prod]
  rw [hmarg]
  intro t ht
  simp [MeasureTheory.Measure.smul_apply, ht]

/-- Domination of a dominated law's prefix marginal by the prefix reference. -/
lemma measure_map_prefixIn_absolutelyContinuous_jointRef
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (hdom : μ ≪ Causalean.SCM.jointRef ref D)
    (k : ℕ) :
    μ.map (valuesProjection (H.prefixIn_subset D k))
      ≪ Causalean.SCM.jointRef ref (H.prefixIn D k) := by
  exact ((hdom.map (measurable_valuesProjection (H.prefixIn_subset D k))).trans
    (jointRef_map_prefixIn_absolutelyContinuous H D ref k))

/-- Recursive Tian prefix density product on an intermediate prefix. -/
noncomputable def tianPrefixDensityProductInPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    (k : ℕ) → ValuesOn (H.prefixIn D k) (swigΩ Ω) → ENNReal
  | 0, _ => 1
  | k + 1, z =>
      tianPrefixDensityProductInPrefix H D μ ref k
        (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z) *
        if hk : k < D.card then
          ((ProbabilityTheory.condDistrib
              (valuesProjection
                (show ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) ⊆ D from by
                  intro v hv
                  rw [Finset.mem_singleton] at hv
                  exact hv ▸ (H.nodesAt D ⟨k, hk⟩).property))
              (valuesProjection (H.prefixIn_subset D k))
              μ)
              (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)).rnDeriv
            (Causalean.SCM.jointRef ref
              ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)))
            (valuesProjection
              (show ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) ⊆
                  H.prefixIn D (k + 1) from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                subst hv
                rw [nodesAt_mem_prefixIn_iff H D (k + 1) ⟨k, hk⟩]
                exact Nat.lt_succ_self k) z)
        else
          1

/-- One-step Tian density read from a `k`-prefix assignment. -/
noncomputable def tianPrefixStepDensityInPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (i : ℕ) (hi : i < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (i : ℕ) (hi : i < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (k : ℕ) (z : ValuesOn (H.prefixIn D k) (swigΩ Ω)) (i : ℕ) : ENNReal :=
  if hi : i < k then
    if hcard : i < D.card then
      ((ProbabilityTheory.condDistrib
          (valuesProjection
            (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D ⟨i, hcard⟩).property))
          (valuesProjection (H.prefixIn_subset D i))
          μ)
          (valuesProjection (prefixIn_mono H D (Nat.le_of_lt hi)) z)).rnDeriv
        (Causalean.SCM.jointRef ref
          ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)))
        (valuesProjection
          (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆
              H.prefixIn D k from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            subst hv
            rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hcard⟩]
            exact hi) z)
    else
      1
  else
    1

/-- The recursive prefix density product is the range product of its one-step
factors. -/
lemma tianPrefixDensityProductInPrefix_eq_range_product
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (k : ℕ) (hk : k ≤ D.card)
    (z : ValuesOn (H.prefixIn D k) (swigΩ Ω)) :
    tianPrefixDensityProductInPrefix H D μ ref k z =
      ∏ i ∈ Finset.range k, tianPrefixStepDensityInPrefix H D μ ref k z i := by
  induction k with
  | zero =>
      simp [tianPrefixDensityProductInPrefix]
  | succ k ih =>
      have hkcard : k < D.card := Nat.lt_of_succ_le hk
      rw [tianPrefixDensityProductInPrefix]
      rw [ih (Nat.le_of_succ_le hk)
        (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)]
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl ?_
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have hisucc : i < k + 1 := Nat.lt_succ_of_lt hik
        have hicard : i < D.card := lt_of_lt_of_le hik (Nat.le_of_succ_le hk)
        have hproj :
            valuesProjection (prefixIn_mono H D (Nat.le_of_lt hik))
                (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)
              =
            valuesProjection (prefixIn_mono H D (Nat.le_of_lt hisucc)) z := by
          funext a
          rfl
        have hnode :
            valuesProjection
                (show ({(H.nodesAt D ⟨i, hicard⟩).val} : Finset (SWIGNode N)) ⊆
                    H.prefixIn D k from by
                  intro v hv
                  rw [Finset.mem_singleton] at hv
                  subst hv
                  rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hicard⟩]
                  exact hik)
                (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)
              =
            valuesProjection
                (show ({(H.nodesAt D ⟨i, hicard⟩).val} : Finset (SWIGNode N)) ⊆
                    H.prefixIn D (k + 1) from by
                  intro v hv
                  rw [Finset.mem_singleton] at hv
                  subst hv
                  rw [nodesAt_mem_prefixIn_iff H D (k + 1) ⟨i, hicard⟩]
                  exact hisucc) z := by
          funext a
          rfl
        simp [tianPrefixStepDensityInPrefix, hik, hisucc, hicard, hproj, hnode]
      · simp [tianPrefixStepDensityInPrefix, hkcard]

/-- At the full `D` prefix, the recursive prefix density product is Tian's
finite product over all `D` indices. -/
lemma tianPrefixDensityProductInPrefix_card_eq_tianDensityProduct
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (y : ValuesOn (H.prefixIn D D.card) (swigΩ Ω)) :
    tianPrefixDensityProductInPrefix H D μ ref D.card y =
      tianDensityProduct H D μ ref
        ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_card H D)) y) := by
  rw [tianPrefixDensityProductInPrefix_eq_range_product H D μ ref D.card (le_refl _) y]
  rw [Finset.prod_range]
  simp only [tianDensityProduct, tianPrefixStepDensity, tianPrefixStepDensityInPrefix,
    valuesEquivOfEq]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  have hproj :
      valuesProjection (H.prefixIn_subset D i.val)
          (valuesProjection (le_of_eq (prefixIn_card H D).symm) y)
        =
      valuesProjection (prefixIn_mono H D (Nat.le_of_lt i.isLt)) y := by
    funext a
    rfl
  have hnode :
      valuesProjection
          (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (H.nodesAt D i).property)
          (valuesProjection (le_of_eq (prefixIn_card H D).symm) y)
        =
      valuesProjection
          (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆
              H.prefixIn D D.card from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            subst hv
            rw [nodesAt_mem_prefixIn_iff H D D.card i]
            exact i.isLt) y := by
    funext a
    rfl
  simp [i.isLt, hproj, hnode]

/-- Prefix-level Radon--Nikodym chain rule for Tian's arbitrary-measure
conditional density product. -/
lemma measure_prefixIn_rnDeriv_eq_tianPrefixDensityProductInPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsProbabilityMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (hdom : μ ≪ Causalean.SCM.jointRef ref D) :
    ∀ (k : ℕ) (_hk : k ≤ D.card),
      (μ.map (valuesProjection (H.prefixIn_subset D k))).rnDeriv
          (Causalean.SCM.jointRef ref (H.prefixIn D k))
        =ᵐ[Causalean.SCM.jointRef ref (H.prefixIn D k)]
          tianPrefixDensityProductInPrefix H D μ ref k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      have hsub : Subsingleton (ValuesOn (H.prefixIn D 0) (swigΩ Ω)) :=
        ⟨fun a b => funext fun i =>
          absurd (prefixIn_zero H D ▸ i.property) (Finset.notMem_empty i.val)⟩
      have heq :
          μ.map (valuesProjection (H.prefixIn_subset D 0))
            = Causalean.SCM.jointRef ref (H.prefixIn D 0) := by
        refine MeasureTheory.Measure.ext fun A _ => ?_
        rcases Set.eq_empty_or_nonempty A with rfl | hA
        · simp
        · obtain ⟨a, ha⟩ := hA
          have hAuniv : A = Set.univ :=
            Set.eq_univ_of_forall fun x => (hsub.elim x a) ▸ ha
          subst hAuniv
          rw [MeasureTheory.Measure.map_apply
            (measurable_valuesProjection (H.prefixIn_subset D 0)) MeasurableSet.univ]
          simp only [Set.preimage_univ]
          rw [MeasureTheory.measure_univ, Causalean.SCM.jointRef,
            MeasureTheory.Measure.pi_univ]
          symm
          apply Finset.prod_eq_one
          intro i hi
          have : i.val ∈ (∅ : Finset (SWIGNode N)) := by
            simpa [prefixIn_zero H D] using i.property
          simp at this
      rw [heq]
      have h1 :
          tianPrefixDensityProductInPrefix H D μ ref 0 =
            (fun _ => (1 : ENNReal)) := rfl
      rw [h1]
      exact MeasureTheory.Measure.rnDeriv_self _
  | succ k ih =>
      intro hk
      classical
      have hkc : k < D.card := Nat.lt_of_succ_le hk
      have hkprev : k ≤ D.card := Nat.le_of_succ_le hk
      let node : SWIGNode N := (H.nodesAt D ⟨k, hkc⟩).val
      let A : Finset (SWIGNode N) := H.prefixIn D k
      let B : Finset (SWIGNode N) := ({node} : Finset (SWIGNode N))
      let νk : MeasureTheory.Measure (ValuesOn A (swigΩ Ω)) :=
        Causalean.SCM.jointRef ref A
      let ρ : MeasureTheory.Measure (ValuesOn B (swigΩ Ω)) :=
        Causalean.SCM.jointRef ref B
      let prefixMap : ValuesOn D (swigΩ Ω) → ValuesOn A (swigΩ Ω) :=
        valuesProjection (H.prefixIn_subset D k)
      let nodeMap : ValuesOn D (swigΩ Ω) → ValuesOn B (swigΩ Ω) :=
        valuesProjection
          (show B ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (H.nodesAt D ⟨k, hkc⟩).property)
      let succMap : ValuesOn D (swigΩ Ω) →
          ValuesOn (H.prefixIn D (k + 1)) (swigΩ Ω) :=
        valuesProjection (H.prefixIn_subset D (k + 1))
      let chain : MeasureTheory.Measure (ValuesOn A (swigΩ Ω)) :=
        μ.map prefixMap
      let stepK : ProbabilityTheory.Kernel (ValuesOn A (swigΩ Ω)) (ValuesOn B (swigΩ Ω)) :=
        ProbabilityTheory.condDistrib nodeMap prefixMap μ
      let ext : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) →
          ValuesOn (H.prefixIn D (k + 1)) (swigΩ Ω) :=
        extendTianPrefix (Ω := Ω) H D hkc
      have hcomp_ext : ext ∘ (fun x : ValuesOn D (swigΩ Ω) => (prefixMap x, nodeMap x))
          = succMap := by
        funext x
        ext a
        by_cases hmem : a.val ∈ H.prefixIn D k
        · simp [ext, prefixMap, nodeMap, succMap, A, B, node, extendTianPrefix,
            valuesEquivOfEq, valuesProjection, valuesUnionMk, hmem]
        · simp [ext, prefixMap, nodeMap, succMap, A, B, node, extendTianPrefix,
            valuesEquivOfEq, valuesProjection, valuesUnionMk, hmem]
      have hchainSucc :
          μ.map succMap = (chain ⊗ₘ stepK).map ext := by
        have hpair :
            chain ⊗ₘ stepK
              = μ.map (fun x : ValuesOn D (swigΩ Ω) => (prefixMap x, nodeMap x)) := by
          dsimp [chain, stepK]
          exact ProbabilityTheory.compProd_map_condDistrib
            ((measurable_valuesProjection (Ω' := swigΩ Ω)
              (show B ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D ⟨k, hkc⟩).property)).aemeasurable)
        rw [hpair]
        rw [MeasureTheory.Measure.map_map]
        · rw [hcomp_ext]
        · exact measurable_extendTianPrefix (Ω := Ω) H D hkc
        · exact (measurable_valuesProjection (Ω' := swigΩ Ω) (H.prefixIn_subset D k)).prod
            (measurable_valuesProjection (Ω' := swigΩ Ω)
              (show B ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D ⟨k, hkc⟩).property))
      have hrefSucc :
          Causalean.SCM.jointRef ref (H.prefixIn D (k + 1))
            = (νk.prod ρ).map ext := by
        dsimp [νk, ρ, A, B, node, ext]
        exact (jointRef_extendTianPrefix H D ref hkc).symm
      have hext_emb : MeasurableEmbedding ext := by
        dsimp [ext, A, B, node]
        unfold extendTianPrefix
        refine
          (valuesEquivOfEq (Ω := swigΩ Ω)
            (prefixIn_succ H D hkc).symm).measurableEmbedding.comp ?_
        change MeasurableEmbedding
          (fun p : ValuesOn (H.prefixIn D k) (swigΩ Ω) ×
              ValuesOn ({(H.nodesAt D ⟨k, hkc⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) =>
            valuesUnionMk p.1 p.2)
        have hfun :
            (fun p : ValuesOn (H.prefixIn D k) (swigΩ Ω) ×
                ValuesOn ({(H.nodesAt D ⟨k, hkc⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) =>
              valuesUnionMk p.1 p.2)
              =
            ((valuesUnionEquiv (Ω := Ω)
              (prefixIn_disjoint_singleton_next H D hkc)).symm) := by
          rfl
        rw [hfun]
        exact ((valuesUnionEquiv (Ω := Ω)
          (prefixIn_disjoint_singleton_next H D hkc)).symm.measurableEmbedding)
      have hcore :
          (chain ⊗ₘ stepK).rnDeriv (νk.prod ρ)
            =ᵐ[νk.prod ρ]
              fun p =>
                tianPrefixDensityProductInPrefix H D μ ref k p.1 *
                  (stepK p.1).rnDeriv ρ p.2 := by
        have hchain_ac : chain ≪ νk := by
          dsimp [chain, νk, prefixMap, A]
          exact measure_map_prefixIn_absolutelyContinuous_jointRef H D μ ref hdom k
        have hsucc_ac :
            μ.map succMap ≪ Causalean.SCM.jointRef ref (H.prefixIn D (k + 1)) := by
          dsimp [succMap]
          exact measure_map_prefixIn_absolutelyContinuous_jointRef H D μ ref hdom (k + 1)
        have hjoint_map : (chain ⊗ₘ stepK).map ext ≪ (νk.prod ρ).map ext := by
          simpa [hchainSucc, hrefSucc] using hsucc_ac
        have hjoint : chain ⊗ₘ stepK ≪ νk.prod ρ :=
          Causalean.SCM.absolutelyContinuous_of_map_measurableEmbedding hext_emb hjoint_map
        -- In this finite/discrete setting `ρ` is finite, so `Kernel.const _ ρ` is a
        -- finite kernel and fibre domination follows from joint domination.
        have hfiber : ∀ᵐ a ∂chain, stepK a ≪ ρ := by
          have hjoint_const :
              chain ⊗ₘ stepK ≪ νk ⊗ₘ ProbabilityTheory.Kernel.const _ ρ := by
            rwa [MeasureTheory.Measure.compProd_const]
          filter_upwards [hjoint_const.kernel_of_compProd] with a ha
          simpa [ProbabilityTheory.Kernel.const_apply] using ha
        have hfiber_meas :
            AEMeasurable
              (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
                (stepK p.1).rnDeriv ρ p.2)
              (νk.prod ρ) :=
          Causalean.SCM.aemeasurable_fiber_rnDeriv_of_finite νk ρ stepK
        exact MeasureTheory.rnDeriv_compProd_prod_sigmaFinite
          chain νk ρ stepK (tianPrefixDensityProductInPrefix H D μ ref k)
          hchain_ac hfiber hfiber_meas (ih hkprev)
      rw [hchainSucc, hrefSucc, Filter.EventuallyEq, hext_emb.ae_map_iff]
      filter_upwards [hext_emb.rnDeriv_map (chain ⊗ₘ stepK) (νk.prod ρ),
        hcore] with p hmap hp
      rw [hmap, hp]
      dsimp [ext, stepK, ρ, B, node]
      have hpair := valuesUnionEquiv_extendTianPrefix H D hkc p
      have hproj_ext :
          valuesProjection (prefixIn_mono H D (Nat.le_succ k))
              (extendTianPrefix (Ω := Ω) H D hkc p) = p.1 := by
        funext i
        have hi := congrArg (fun q => q.1 i) hpair
        simpa [valuesUnionEquiv, valuesProjection] using hi
      have hnode_ext :
          valuesProjection
              (show ({(H.nodesAt D ⟨k, hkc⟩).val} : Finset (SWIGNode N)) ⊆
                  H.prefixIn D (k + 1) from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                subst hv
                rw [nodesAt_mem_prefixIn_iff H D (k + 1) ⟨k, hkc⟩]
                exact Nat.lt_succ_self k)
              (extendTianPrefix (Ω := Ω) H D hkc p) = p.2 := by
        funext i
        have hi := congrArg (fun q => q.2 i) hpair
        simpa [valuesUnionEquiv, valuesProjection] using hi
      rw [tianPrefixDensityProductInPrefix]
      simp [hkc, hproj_ext, hnode_ext, A, B, node, prefixMap, nodeMap]

/-- The density of any dominated finite law on a finite coordinate set factors
as the product of its one-coordinate conditional densities along the chosen
topological order.  The conditional density at each coordinate is computed from
Mathlib's regular conditional distribution given the preceding prefix.

This is the measure-only analogue of `SCM.obsDensity_eq_qFactorDensityProduct`.
The proof should induct over the prefixes of `D`: split the successor reference
as a product of the prefix reference and the next-node reference, rewrite the
successor law as the composition product of the prefix marginal and the
`condDistrib` kernel, and apply the σ-finite composition-product
Radon--Nikodym derivative lemma already isolated in
`Causalean.Mathlib.MeasureTheory.RnDerivCompProdSigmaFinite`. -/
theorem rnDeriv_eq_tianDensityProduct
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsProbabilityMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (hdom : μ ≪ Causalean.SCM.jointRef ref D) :
    μ.rnDeriv (Causalean.SCM.jointRef ref D)
      =ᵐ[Causalean.SCM.jointRef ref D] tianDensityProduct H D μ ref := by
  classical
  set e := valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_card H D) with he
  have hf : MeasurableEmbedding
      (e : ValuesOn (H.prefixIn D D.card) (swigΩ Ω) →
        ValuesOn D (swigΩ Ω)) := e.measurableEmbedding
  have hμe :
      (μ.map e.symm).map e = μ := by
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    have hcomp : (e : ValuesOn (H.prefixIn D D.card) (swigΩ Ω) →
        ValuesOn D (swigΩ Ω)) ∘ e.symm = id := by
      funext x
      exact e.right_inv x
    rw [hcomp, MeasureTheory.Measure.map_id]
  have href :
      (Causalean.SCM.jointRef ref (H.prefixIn D D.card)).map e
        = Causalean.SCM.jointRef ref D := by
    rw [Causalean.SCM.jointRef, Causalean.SCM.jointRef,
      Causalean.SCM.map_pi_valuesEquivOfEq]
  have hprefixMap :
      valuesProjection (H.prefixIn_subset D D.card)
        =
      (e.symm : ValuesOn D (swigΩ Ω) → ValuesOn (H.prefixIn D D.card) (swigΩ Ω)) := by
    funext x i
    rfl
  have hprefix :
      (μ.map e.symm).rnDeriv (Causalean.SCM.jointRef ref (H.prefixIn D D.card))
        =ᵐ[Causalean.SCM.jointRef ref (H.prefixIn D D.card)]
          tianPrefixDensityProductInPrefix H D μ ref D.card := by
    simpa [hprefixMap] using
      (measure_prefixIn_rnDeriv_eq_tianPrefixDensityProductInPrefix
        H D μ ref hdom D.card (le_refl _))
  have hmap :
      μ.rnDeriv (Causalean.SCM.jointRef ref D)
        =ᵐ[Causalean.SCM.jointRef ref D]
          fun x =>
            ((μ.map e.symm).rnDeriv
              (Causalean.SCM.jointRef ref (H.prefixIn D D.card))) (e.symm x) := by
    rw [← href, Filter.EventuallyEq, hf.ae_map_iff]
    filter_upwards [hf.rnDeriv_map (μ.map e.symm)
      (Causalean.SCM.jointRef ref (H.prefixIn D D.card))] with y hy
    simpa [hμe] using hy
  refine hmap.trans ?_
  rw [← href, Filter.EventuallyEq, hf.ae_map_iff]
  filter_upwards [hprefix] with y hy
  have hleft : e.symm (e y) = y := e.left_inv y
  rw [hleft, hy]
  simpa using tianPrefixDensityProductInPrefix_card_eq_tianDensityProduct H D μ ref y

/-- Density form of the Markov-to-c-factorization theorem.  If a finite measure on `D` is globally Markov with
respect to the pure graph `H` whose observed nodes are exactly `D`, and is
dominated by the product reference on `D`, its density is the product of Tian
district factors over the c-components of `H`.

The statement is intentionally measure-native rather than an `SCM.induce`
specialization, so it can be applied directly to ancestral do-law marginals. -/
theorem markov_tian_cfactorization_density
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (hD : H.observed = D)
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsProbabilityMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (hdom : μ ≪ Causalean.SCM.jointRef ref D) :
    μ.rnDeriv (Causalean.SCM.jointRef ref D)
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun x => ∏ S ∈ H.cComponentSet, tianDistrictDensity H D μ ref S x := by
  exact (rnDeriv_eq_tianDensityProduct H D μ ref hdom).trans
    (Filter.EventuallyEq.of_eq
      (prod_tianDistrictDensity_eq_tianDensityProduct H D hD μ ref).symm)

/-- The do-law ancestral marginal is globally Markov with respect to the pure
ancestral graph `G_X[D]`.  This is the SCM-to-measure bridge for T1; it does
not assert that `D` is an ancestrally closed SCM support. -/
theorem doObsKernelAncestralMarginal_globalMarkovOn
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    [StandardBorelSpace (M.fixSet X hObs hFix).RandomValues]
    [StandardBorelSpace (M.fixSet X hObs hFix).ObservedValues]
    [∀ s : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).jointKernel s)]
    [∀ s : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).obsKernel s)]
    (s : (M.fixSet X hObs hFix).FixedValues)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y s)] :
    let A := fixAncestralSet M X hObs hFix Y
      let D := fixObservedAncestralSet M X hObs hFix Y
      let H := (M.fixSet X hObs hFix).toSWIGGraph.induce A
      KernelGlobalMarkovOn H D (by rfl)
        (doObsKernelAncestralMarginal M X hObs hFix Y s) := by
  classical
  let M' := M.fixSet X hObs hFix
  let A := fixAncestralSet M X hObs hFix Y
  let D := fixObservedAncestralSet M X hObs hFix Y
  change KernelGlobalMarkovOn (M'.toSWIGGraph.induce A) D (by rfl)
    ((doObsKernelAncestralMarginal M X hObs hFix Y) s)
  dsimp [KernelGlobalMarkovOn]
  intro X' Y' Z' hX hY hZ hXY hXZ hYZ hdSep
  have hD_obs : D ⊆ M'.observed := by
    intro v hv
    exact (Finset.mem_inter.mp hv).2
  have hX_obs : X' ⊆ M'.observed := fun v hv => hD_obs (hX hv)
  have hY_obs : Y' ⊆ M'.observed := fun v hv => hD_obs (hY hv)
  have hZ_obs : Z' ⊆ M'.observed := fun v hv => hD_obs (hZ hv)
  have hA_closed : M'.dag.ancestralSet A = A := by
    simpa [A, fixAncestralSet, M'] using
      (M'.dag.ancestralSet_idem Y)
  have hdSep_fixed : M'.dag.dSep X' Y' (Z' ∪ M'.fixed) := by
    simpa [A, D, M'] using
      (M'.toSWIGGraph.dSep_union_fixed_of_induce_dSep A X' Y' Z'
        hX hY hZ hA_closed hdSep)
  have hCI_obs : SCM.ObsCondIndep M' X' Y' Z' hX_obs hY_obs hZ_obs
      (M'.obsKernel s) :=
    SCM.globalMarkov_with_fixed M' X' Y' Z' M'.fixed
      hX_obs hY_obs hZ_obs (by intro v hv; exact hv)
      hXY hXZ hYZ hdSep_fixed s
  unfold KernelObsCondIndepOn
  unfold SCM.ObsCondIndep at hCI_obs
  have hCI_pre :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap
          (valuesProjection hZ ∘ valuesProjection hD_obs) inferInstance)
        (Measurable.comap_le
          ((measurable_valuesProjection hZ).comp
            (measurable_valuesProjection hD_obs)))
        (valuesProjection hX ∘ valuesProjection hD_obs)
        (valuesProjection hY ∘ valuesProjection hD_obs)
        (M'.obsKernel s) := by
    convert hCI_obs using 2
  have hCI_map :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap (valuesProjection hZ) inferInstance)
        (comap_valuesProjection_le hZ)
        (valuesProjection hX) (valuesProjection hY)
        ((M'.obsKernel s).map (valuesProjection hD_obs)) :=
    condIndepFun_of_map
      (φ := valuesProjection hD_obs)
      (measurable_valuesProjection hD_obs)
      (measurable_valuesProjection hX)
      (measurable_valuesProjection hY)
      (measurable_valuesProjection hZ)
      hCI_pre
  convert hCI_map using 2
  rw [doObsKernelAncestralMarginal,
    ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection hD_obs)]

/-- The graph-level topological enumeration agrees definitionally with the
SCM-level observed-node enumeration. -/
lemma nodesAt_toSWIGGraph_observed_eq_observedAt
    (M : Causalean.SCM N Ω) (i : Fin M.observed.card) :
    M.toSWIGGraph.nodesAt M.observed i = M.observedAt i := by
  rfl

/-- Core Tian c-factor recovery for a full observational c-component.

For a district `S` of the post-intervention ancestral graph that is also a full
c-component of `M`, the district prefix-density factor of the do-law on
`D = An_{G_X}(Y) ∩ observed` equals the observational c-component density
factor `Q[S]`, evaluated after any extension of a `D` assignment to the full
observed space.

Mathematically this packages the valid-branch Tian and Pearl
whole-c-component invariance `Q[S]_{do(X)} = Q[S]_{obs}` together with the
support fact needed for the `extend` argument.  In that branch, the c-factor
only depends on `S` and its observed parents; for a do-ancestral district those
observed parents lie in `D`, while intervened parents are read from
`M.fixSetProj X ... sDo`, so coordinates outside `D` are irrelevant.
The proof delegates to the direct finite recovery theorem from the q-factor
identity layer, which performs the reverse-topological summation and identifies
the surviving product with the `D`-prefix district product. -/
lemma tian_full_cComponent_density_recovery_core
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hSfull : S ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (hExtendX : ∀ xD (D : N) (hD : D ∈ X),
      extend xD ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun xD =>
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) S (extend xD) := by
  exact tian_full_cComponent_density_recovery_core_direct
    M X hStd hObs hFix Y ref href sDo S hS hSfull hpos hYX extend hExtend hExtendX

/-- Finite same-district recovery: the do-law's `S`-district density factor equals
`S`'s observational c-component density factor (after extension), for a district `S`
that is already a full observational c-component.

This is Tian's identification at the DISTRICT level.  Both sides collapse to the
c-factor `Q[S]`: `tianDistrictDensity` (the do-law's `D`-prefix conditional product)
to `Q[S]` of the do-model, and `cComponentDensityFactor` (the full-observed-prefix
conditional product) to `Q[S]` of `M`; the two `Q[S]` kernels agree by
`district_id`/`q_factor_identity`.  It is NOT a per-coordinate identity — the D-prefix
and full-observed-prefix conditionals differ node-by-node and only telescope to the
same district product. -/
lemma doAncestralDistrictDensity_recovered_from_obs_core_self
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hSfull : S ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (hExtendX : ∀ xD (D : N) (hD : D ∈ X),
      extend xD ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun xD =>
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) S (extend xD) := by
  exact tian_full_cComponent_density_recovery_core
    M X hStd hObs hFix Y ref href sDo S hS hSfull hpos hYX extend hExtend hExtendX
/-- T2 density-recovery core.

For one district `S` of the post-intervention ancestral graph, the product of
Tian prefix conditional densities computed from the ancestral do-law marginal
agrees a.e. with the matching full observational c-component density factor,
pulled back along any extension that agrees on the ancestral observed
coordinates.  The proof is the finite atomic bridge from the kernel-level
`district_id`/`q_factor_identity` recovery to the scalar `rnDeriv` factors,
together with the index bijection between the `D`-topological `S` nodes and the
full observed `C` nodes and extension-independence off `D`. -/
lemma doAncestralDistrictDensity_recovered_from_obs_core
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S C : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hReach : cFactorReachable M.toSWIGGraph C S)
    (hCmem : C ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (hExtendX : ∀ xD (D : N) (hD : D ∈ X),
      extend xD ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun xD =>
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) C (extend xD) := by
  classical
  rcases hReach with ⟨hSnonempty, hSsubC, hSmem⟩
  have hCS : C = S := by
    by_contra hne
    rcases hSnonempty with ⟨v, hvS⟩
    have hvC : v ∈ C := hSsubC hvS
    have hdisj := M.toSWIGGraph.cComponentSet_pairwise_disjoint hCmem hSmem hne
    exact (Finset.disjoint_left.mp hdisj) hvC hvS
  subst C
  exact doAncestralDistrictDensity_recovered_from_obs_core_self
    M X hStd hObs hFix Y ref href sDo S hS hSmem hpos hYX extend hExtend hExtendX

/-- T2, abstract density recovery statement.  For a district `S` of the
post-intervention ancestral graph, the district factor computed from the
do-law marginal is the corresponding recovered full-graph district factor,
pulled back along an extension from ancestral assignments to full observed
assignments.

The extension parameter makes the statement honest about the type mismatch:
the left side lives on `D = An_{G_X}(Y) ∩ observed`, while the already-proven
full-graph factor `cComponentDensityFactor` lives on the original observed
state.  The right side is extension-independent under the
reachability/no-descendant hypotheses. -/
theorem doAncestralDistrictDensity_recovered_from_obs
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S C : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hReach : cFactorReachable M.toSWIGGraph C S)
    (hCmem : C ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (hExtendX : ∀ xD (D : N) (hD : D ∈ X),
      extend xD ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun xD =>
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) C (extend xD) := by
  exact doAncestralDistrictDensity_recovered_from_obs_core
    M X hStd hObs hFix Y ref href sDo S C hS hReach hCmem hpos hYX extend hExtend
      hExtendX

/-- ID-specific T1 wrapper: the density of `ν_M =
(M.fixSet X).obsKernel.map π_D` factors over the districts of `G_X[D]`. -/
theorem doObsKernelAncestralMarginal_tian_cfactorization_density
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (s : (M.fixSet X hObs hFix).FixedValues)
    [StandardBorelSpace
      (ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω))]
    [StandardBorelSpace (M.fixSet X hObs hFix).RandomValues]
    [StandardBorelSpace (M.fixSet X hObs hFix).ObservedValues]
    [∀ s' : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).jointKernel s')]
    [∀ s' : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).obsKernel s')]
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y s)]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    (hdomD :
      doObsKernelAncestralMarginal M X hObs hFix Y s ≪
        Causalean.SCM.jointRef ref (fixObservedAncestralSet M X hObs hFix Y)) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    (doObsKernelAncestralMarginal M X hObs hFix Y s).rnDeriv
        (Causalean.SCM.jointRef ref D)
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun x => ∏ S ∈ H.cComponentSet,
          tianDistrictDensity H D
            (doObsKernelAncestralMarginal M X hObs hFix Y s) ref S x := by
  intro D H
  exact markov_tian_cfactorization_density H D rfl
    (doObsKernelAncestralMarginal M X hObs hFix Y s) ref hdomD

end SCM.ID
end Causalean
