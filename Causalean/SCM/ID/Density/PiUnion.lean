/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Do.Rule2Kernel.Helpers
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Product measure over a disjoint union of value coordinates

For disjoint node sets `A` and `B`, the canonical measurable equivalence
`valuesUnionEquiv : ValuesOn (A ∪ B) ≃ᵐ ValuesOn A × ValuesOn B` carries the
finite product reference measure on `A ∪ B` to the product of the references on
`A` and on `B`.  In other words `Measure.pi` over a disjoint union is the product
of the two `Measure.pi`'s.  This is the reference-splitting fact that lets the
density chain rule peel off one coordinate at a time.

The proof routes the project's union equivalence through Mathlib's
`sumPiEquivProdPi` (the value reindexing along the `Sum` decomposition of the
union index) and `piCongrLeft` (the index reindexing), both measure-preserving.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory
open MeasureTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Value assignments on finite SWIG-node sets are finite when each base node
value space is finite. -/
instance instFintypeValuesOnSwigΩ [∀ n, Fintype (Ω n)]
    (I : Finset (SWIGNode N)) : Fintype (ValuesOn I (swigΩ Ω)) := by
  classical
  haveI : ∀ v : SWIGNode N, Fintype (swigΩ Ω v)
    | .random _ => inferInstance
    | .fixed _ => inferInstance
  infer_instance

/-- Override the coordinates in `W` of an assignment on `I`, leaving the other
coordinates unchanged. -/
def overrideOn {I W : Finset (SWIGNode N)} (_hWI : W ⊆ I)
    (x : ValuesOn I (swigΩ Ω)) (y : ValuesOn W (swigΩ Ω)) :
    ValuesOn I (swigΩ Ω) :=
  fun i => if h : i.val ∈ W then y ⟨i.val, h⟩ else x i

/-- On overridden coordinates, `overrideOn` reads from the replacement
assignment. -/
@[simp] lemma overrideOn_mem {I W : Finset (SWIGNode N)} (hWI : W ⊆ I)
    (x : ValuesOn I (swigΩ Ω)) (y : ValuesOn W (swigΩ Ω))
    (i : {i // i ∈ I}) (hiW : i.val ∈ W) :
    overrideOn hWI x y i = y ⟨i.val, hiW⟩ := by
  simp [overrideOn, hiW]

/-- Away from overridden coordinates, `overrideOn` keeps the original
assignment. -/
@[simp] lemma overrideOn_notMem {I W : Finset (SWIGNode N)} (hWI : W ⊆ I)
    (x : ValuesOn I (swigΩ Ω)) (y : ValuesOn W (swigΩ Ω))
    (i : {i // i ∈ I}) (hiW : i.val ∉ W) :
    overrideOn hWI x y i = x i := by
  simp [overrideOn, hiW]

/-- Re-overriding the same coordinate set keeps the last replacement
assignment. -/
@[simp] lemma overrideOn_overrideOn {I W : Finset (SWIGNode N)} (hWI : W ⊆ I)
    (x : ValuesOn I (swigΩ Ω)) (y z : ValuesOn W (swigΩ Ω)) :
    overrideOn hWI (overrideOn hWI x y) z = overrideOn hWI x z := by
  funext i
  by_cases hiW : i.val ∈ W
  · simp [hiW]
  · simp [hiW]

/-- Projecting an override back to the overridden coordinates returns the
replacement assignment. -/
@[simp] lemma valuesProjection_overrideOn {I W : Finset (SWIGNode N)} (hWI : W ⊆ I)
    (x : ValuesOn I (swigΩ Ω)) (y : ValuesOn W (swigΩ Ω)) :
    valuesProjection hWI (overrideOn hWI x y) = y := by
  funext i
  exact overrideOn_mem hWI x y ⟨i.val, hWI i.property⟩ i.property

/-- The index equivalence `{a ∈ A} ⊕ {b ∈ B} ≃ {i ∈ A ∪ B}` for disjoint `A`, `B`. -/
def unionSumEquiv {A B : Finset (SWIGNode N)} (hDisj : Disjoint A B) :
    ({a // a ∈ A} ⊕ {b // b ∈ B}) ≃ {i // i ∈ A ∪ B} where
  toFun := Sum.elim
    (fun a => ⟨a.val, Finset.mem_union_left _ a.property⟩)
    (fun b => ⟨b.val, Finset.mem_union_right _ b.property⟩)
  invFun i :=
    if h : i.val ∈ A then Sum.inl ⟨i.val, h⟩
    else Sum.inr ⟨i.val, (Finset.mem_union.mp i.property).resolve_left h⟩
  left_inv := by
    rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · simp [ha]
    · have hbA : b ∉ A := fun h => (Finset.disjoint_left.mp hDisj h) hb
      simp [hbA]
  right_inv := by
    rintro ⟨i, hi⟩
    by_cases h : i ∈ A
    · simp [h]
    · simp [h]

/-- **`Measure.pi` splits over a disjoint union.**  The product reference on
`A ∪ B` is carried by `valuesUnionEquiv` to the product of the references on `A`
and `B`. -/
lemma measurePreserving_valuesUnionEquiv {A B : Finset (SWIGNode N)}
    (hDisj : Disjoint A B)
    (μ : ∀ v : SWIGNode N, MeasureTheory.Measure (swigΩ Ω v))
    [∀ v, MeasureTheory.SigmaFinite (μ v)] :
    MeasureTheory.MeasurePreserving (valuesUnionEquiv (A := A) (B := B) hDisj)
      (MeasureTheory.Measure.pi (fun i : {i // i ∈ A ∪ B} => μ i.val))
      ((MeasureTheory.Measure.pi (fun a : {a // a ∈ A} => μ a.val)).prod
        (MeasureTheory.Measure.pi (fun b : {b // b ∈ B} => μ b.val))) := by
  classical
  set g := unionSumEquiv hDisj with hg
  have mpc :
      MeasureTheory.MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun i : {i // i ∈ A ∪ B} => swigΩ Ω i.val) g)
        (MeasureTheory.Measure.pi (fun j => μ (g j).val))
        (MeasureTheory.Measure.pi (fun i : {i // i ∈ A ∪ B} => μ i.val)) :=
    measurePreserving_piCongrLeft (fun i : {i // i ∈ A ∪ B} => μ i.val) g
  have mps :
      MeasureTheory.MeasurePreserving
        (MeasurableEquiv.sumPiEquivProdPi (fun j => swigΩ Ω (g j).val))
        (MeasureTheory.Measure.pi (fun j => μ (g j).val))
        ((MeasureTheory.Measure.pi fun a : {a // a ∈ A} => μ (g (Sum.inl a)).val).prod
          (MeasureTheory.Measure.pi fun b : {b // b ∈ B} => μ (g (Sum.inr b)).val)) :=
    measurePreserving_sumPiEquivProdPi (fun j => μ (g j).val)
  have hcomp := mps.comp (mpc.symm (MeasurableEquiv.piCongrLeft _ g))
  have hfun :
      ⇑(valuesUnionEquiv (A := A) (B := B) hDisj)
        = ⇑(MeasurableEquiv.sumPiEquivProdPi (fun j => swigΩ Ω (g j).val))
          ∘ ⇑(MeasurableEquiv.piCongrLeft
              (fun i : {i // i ∈ A ∪ B} => swigΩ Ω i.val) g).symm := by
    funext ξ
    apply Prod.ext
    · funext a; rfl
    · funext b; rfl
  refine ⟨(valuesUnionEquiv hDisj).measurable, ?_⟩
  rw [hfun]
  exact hcomp.map_eq

end Causalean.SCM
