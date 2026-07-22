/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 helpers — value-space fill utilities

Defines `zFixedAsRandom`, `valuesUnionMk`, and `fillZrW`, the injection
from `ValuesOn W` into `ValuesOn (Z.image .random ∪ W)` needed for Rule 2.
-/

import Causalean.SCM.Model.Kernel
import Causalean.Mathlib.MeasureTheory.FinsetValues

/-! # Value-Space Helpers for Rule 2

This file builds the value-space maps that insert intervention values into a
conditioning assignment. These maps provide the bookkeeping needed to compare
conditioning on an observed random copy with conditioning on the corresponding
intervention value in Rule 2. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § Value-space fill helpers used by Rule 2
--
-- Rule 2 needs a canonical injection from `ValuesOn W` to
-- `ValuesOn (Z.image .random ∪ W)` that inserts the `do(z)` values extracted
-- from a double-intervention FixedValues slice.  Built in two steps:
--   * `zFixedAsRandom` reindexes a `.fixed Z`-slice onto `.random Z`
--     (uses `swigΩ Ω (.fixed D) = swigΩ Ω (.random D) = Ω D` definitionally);
--   * `valuesUnionMk` piecewise-combines two disjoint slices into their union.
-- Their composition is `fillZrW`.
-- ============================================================

/-- This map reads intervention values as values of the corresponding observed random variables.

It reuses the shared base-node value space of each fixed and random copy; the
fixed-node branch is unreachable for the requested random-node output. -/
noncomputable def zFixedAsRandom {Z : Finset N}
    (z : ValuesOn (Z.image SWIGNode.fixed) (swigΩ Ω)) :
    ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) := fun ⟨v, hv⟩ =>
  match v, hv with
  | SWIGNode.random D, hv =>
      have hD : D ∈ Z := by
        rcases Finset.mem_image.mp hv with ⟨D', hD', heq⟩
        cases heq; exact hD'
      z ⟨SWIGNode.fixed D, Finset.mem_image.mpr ⟨D, hD, rfl⟩⟩
  | SWIGNode.fixed _, hv => by
      exfalso
      rcases Finset.mem_image.mp hv with ⟨_, _, heq⟩
      cases heq

-- `valuesUnionMk` (and its projection/measurability lemmas) are the generic
-- value-space union-injection; they now live in
-- `Causalean/Mathlib/MeasureTheory/FinsetValues.lean` (namespace `Causalean`,
-- over an arbitrary finite index) and are used here at `M := SWIGNode N`.

/-- Reading intervention values as observed random-variable values is a measurable operation.

At every output coordinate the map is just a coordinate projection of the input
fixed-value assignment. -/
lemma measurable_zFixedAsRandom {Z : Finset N} :
    Measurable (zFixedAsRandom (Ω := Ω) (Z := Z)) := by
  refine measurable_pi_iff.mpr ?_
  rintro ⟨v, hv⟩
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hv
  -- v = SWIGNode.random D; output is `z ⟨.fixed D, _⟩`
  exact measurable_pi_apply _

/-- The Rule 2 filler inserts intervention values into a conditioning assignment.

It reads the fixed treatment values from the post-intervention fixed slice,
relabels them as observed random treatment values, and combines them with the
free conditioning coordinates. -/
noncomputable def fillZrW
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ValuesOn W (swigΩ Ω) →
      ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) :=
  fun w =>
    valuesUnionMk
      (zFixedAsRandom
        (valuesProjection
          (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s'))
      w

/-- A value assignment on a disjoint union is measurably equivalent to the pair of assignments on the two parts.

The forward map projects to each part and the inverse recombines them; disjointness
ensures the first part's priority cannot overwrite the second part. -/
noncomputable def valuesUnionEquiv {A B : Finset (SWIGNode N)}
    (hDisj : Disjoint A B) :
    ValuesOn (A ∪ B) (swigΩ Ω) ≃ᵐ
      ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) where
  toFun ξ :=
    (valuesProjection (Finset.subset_union_left) ξ,
     valuesProjection (Finset.subset_union_right) ξ)
  invFun p := valuesUnionMk p.1 p.2
  left_inv ξ := by
    funext ⟨v, hv⟩
    by_cases hA : v ∈ A
    · simp [valuesUnionMk_apply_left _ _ hv hA, valuesProjection]
    · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hA
      simp [valuesUnionMk_apply_right _ _ hv hA hB, valuesProjection]
  right_inv := by
    rintro ⟨a, b⟩
    ext
    · rename_i i
      obtain ⟨v, hvA⟩ := i
      have hv : v ∈ A ∪ B := Finset.subset_union_left hvA
      simp [valuesProjection, valuesUnionMk_apply_left _ _ hv hvA]
    · rename_i i
      obtain ⟨v, hvB⟩ := i
      have hv : v ∈ A ∪ B := Finset.subset_union_right hvB
      have hA : v ∉ A := fun hA' =>
        (Finset.disjoint_left.mp hDisj hA') hvB
      simp [valuesProjection, valuesUnionMk_apply_right _ _ hv hA hvB]
  measurable_toFun :=
    (measurable_valuesProjection _).prodMk (measurable_valuesProjection _)
  measurable_invFun := by
    change Measurable (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
      valuesUnionMk p.1 p.2)
    refine measurable_pi_iff.mpr ?_
    rintro ⟨v, hv⟩
    by_cases hA : v ∈ A
    · have h_eq :
          (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
              valuesUnionMk p.1 p.2 ⟨v, hv⟩)
            = (fun p => p.1 ⟨v, hA⟩) :=
        funext fun _ => valuesUnionMk_apply_left _ _ hv hA
      rw [h_eq]
      exact (measurable_pi_apply _).comp measurable_fst
    · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hA
      have h_eq :
          (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
              valuesUnionMk p.1 p.2 ⟨v, hv⟩)
            = (fun p => p.2 ⟨v, hB⟩) :=
        funext fun _ => valuesUnionMk_apply_right _ _ hv hA
      rw [h_eq]
      exact (measurable_pi_apply _).comp measurable_snd

/-- The Rule 2 filler is measurable as a function of the free conditioning assignment.

The post-intervention fixed slice contributes only a constant assignment, while
the free coordinates enter through coordinate projections. -/
theorem measurable_fillZrW (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    Measurable (M'.fillZrW Z hZ_obs hZ_fixed W s') := by
  unfold fillZrW
  exact measurable_valuesUnionMk_right _

/-- The Rule 2 filler is jointly measurable in the post-intervention fixed slice and the free conditioning coordinates.

This is the local bridge used to pull the observational conditional kernel back
along the map that pairs the base fixed slice with the filled conditioning value. -/
theorem measurable_fillZrW_prod (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N)) :
    Measurable
      (fun p : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues × ValuesOn W (swigΩ Ω) =>
        M'.fillZrW Z hZ_obs hZ_fixed W p.1 p.2) := by
  unfold fillZrW
  change Measurable
    ((fun q : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω) =>
        valuesUnionMk q.1 q.2) ∘
      (fun p : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues × ValuesOn W (swigΩ Ω) =>
        (zFixedAsRandom
          (valuesProjection (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) p.1),
         p.2)))
  refine (measurable_valuesUnionMk
    (Ω := swigΩ Ω) (A := Z.image SWIGNode.random) (B := W)).comp ?_
  refine Measurable.prodMk ?_ measurable_snd
  exact measurable_zFixedAsRandom.comp
    ((measurable_valuesProjection _).comp measurable_fst)

/-- This map reads observed treatment values as values for the corresponding intervention coordinates.

It is the mirror image of the map from fixed intervention values to random
observed values. -/
noncomputable def xRandomAsFixed {X : Finset N}
    (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    ValuesOn (X.image SWIGNode.fixed) (swigΩ Ω) := fun ⟨v, hv⟩ =>
  match v, hv with
  | SWIGNode.fixed D, hv =>
      have hD : D ∈ X := by
        rcases Finset.mem_image.mp hv with ⟨D', hD', heq⟩; cases heq; exact hD'
      t ⟨SWIGNode.random D, Finset.mem_image.mpr ⟨D, hD, rfl⟩⟩
  | SWIGNode.random _, hv => by
      exfalso; rcases Finset.mem_image.mp hv with ⟨_, _, heq⟩; cases heq

/-- Reading observed treatment values as intervention-coordinate values is measurable. -/
lemma measurable_xRandomAsFixed {X : Finset N} :
    Measurable (xRandomAsFixed (Ω := Ω) (X := X)) := by
  refine measurable_pi_iff.mpr ?_
  rintro ⟨v, hv⟩
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hv
  exact measurable_pi_apply _

/-- This map extends a base fixed-value assignment with treatment values for a post-intervention model.

Existing fixed coordinates are read from the base assignment, while newly fixed
treatment coordinates are read from the treatment assignment after relabeling. -/
noncomputable def fixSetExtend (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (s0 : M.FixedValues) (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    (M.fixSet X hObs hFix).FixedValues := fun ⟨v, hv⟩ =>
  if hM : v ∈ M.fixed then s0 ⟨v, hM⟩
  else
    have hXf : v ∈ X.image SWIGNode.fixed :=
      (Finset.mem_union.mp (by simpa using hv)).resolve_left hM
    xRandomAsFixed t ⟨v, hXf⟩

/-- A newly fixed coordinate in `fixSetExtend` reads the matching observed
intervention coordinate. -/
@[simp] lemma fixSetExtend_apply_new_fixed
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (s0 : M.FixedValues) (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
    {D : N} (hD : D ∈ X) :
    M.fixSetExtend X hObs hFix s0 t
        ⟨SWIGNode.fixed D, SCM.fixed_mem_fixSet M X hObs hFix hD⟩ =
      t ⟨SWIGNode.random D, Finset.mem_image.mpr ⟨D, hD, rfl⟩⟩ := by
  simp [fixSetExtend, hFix D hD, xRandomAsFixed]

/-- Extending a base fixed-value assignment is measurable in the treatment
value when the base assignment is held fixed. -/
lemma measurable_fixSetExtend (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) (s0 : M.FixedValues) :
    Measurable (M.fixSetExtend X hObs hFix s0) := by
  refine measurable_pi_iff.mpr ?_
  rintro ⟨v, hv⟩
  by_cases hM : v ∈ M.fixed
  · simp only [fixSetExtend, dif_pos hM]; exact measurable_const
  · have hXf : v ∈ X.image SWIGNode.fixed :=
      (Finset.mem_union.mp (by simpa using hv)).resolve_left hM
    have : (fun t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω) =>
        M.fixSetExtend X hObs hFix s0 t ⟨v, hv⟩)
        = fun t => xRandomAsFixed t ⟨v, hXf⟩ := by
      funext t; simp only [fixSetExtend, dif_neg hM]
    rw [this]
    exact (measurable_xRandomAsFixed).eval

/-- Projecting the extended post-intervention fixed assignment back to the original fixed coordinates recovers the base assignment. -/
lemma fixSetProj_fixSetExtend (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (s0 : M.FixedValues) (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    M.fixSetProj X hObs hFix (M.fixSetExtend X hObs hFix s0 t) = s0 := by
  funext ⟨v, hv⟩
  simp only [fixSetProj, valuesProjection, fixSetExtend, dif_pos hv]

/-- Relabeling the treatment part of the extended fixed assignment back to observed coordinates recovers the treatment assignment.

This is the random-coordinate analogue of recovering the base fixed slice and is
used to simplify the Rule 2 filler after extension. -/
lemma zFixedAsRandom_proj_fixSetExtend
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (s0 : M.FixedValues) (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    SCM.zFixedAsRandom
        (valuesProjection (SCM.fixSet_image_fixed_subset M X hObs hFix)
          (M.fixSetExtend X hObs hFix s0 t))
      = t := by
  funext ⟨v, hv⟩
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hv
  -- LHS unfolds: zFixedAsRandom at .random D reads the .fixed D coordinate.
  simp only [SCM.zFixedAsRandom, valuesProjection]
  -- The .fixed D coordinate of fixSetExtend: .fixed D ∉ M.fixed, so it is
  -- xRandomAsFixed t ⟨.fixed D, _⟩ = t ⟨.random D, _⟩.
  have hMf : SWIGNode.fixed D ∉ M.fixed := hFix D hD
  simp only [SCM.fixSetExtend, dif_neg hMf, SCM.xRandomAsFixed]

/-- Filling from an extended post-intervention fixed assignment is the same as directly combining the treatment and conditioning assignments. -/
lemma fillZrW_fixSetExtend
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Z : Finset (SWIGNode N))
    (s0 : M.FixedValues) (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
    (z : ValuesOn Z (swigΩ Ω)) :
    M.fillZrW X hObs hFix Z (M.fixSetExtend X hObs hFix s0 t) z
      = valuesUnionMk t z := by
  rw [SCM.fillZrW, SCM.zFixedAsRandom_proj_fixSetExtend]

end SCM

end Causalean
