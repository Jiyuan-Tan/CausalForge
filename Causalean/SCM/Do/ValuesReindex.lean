/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.Do.Rule2Kernel.Helpers

/-!
# `ValuesOn` reindexing layer (do-calculus identification toolkit)

Equational laws for `valuesUnionMk` (combine two coordinate blocks into one on
their union) under **union reordering** and **`∅` collapse**, stated as `Eq`s
transported along `valuesEquivOfEq` (the canonical measurable equivalence for
propositionally-equal index `Finset`s) rather than as `HEq`s.

`ValuesOn (A ∪ B)` and `ValuesOn (B ∪ A)` are equal but not *definitionally*
equal, which is what forces `HEq`/cast gymnastics in the identification proofs
(e.g. the front-door derivation).  Routing through `valuesEquivOfEq` keeps every
statement an `Eq`, so `rw`/`simp` consume them directly and call sites never
construct an `HEq` by hand. The `valuesUnionMk_comm`,
`valuesUnionMk_empty_right`, and `valuesOn_heq_of_coord` lemmas are the public
reindexing helpers used by do-calculus identification proofs.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Union commutativity.** When [`A` and `B` are disjoint](hyp:hAB), [reindexing
    `valuesUnionMk a b` (a block on `A ∪ B`) along `A ∪ B = B ∪ A` yields
    `valuesUnionMk b a`](goal). -/
lemma valuesUnionMk_comm {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A B : Finset M} (hAB : Disjoint A B)
    (a : ValuesOn A Ω) (b : ValuesOn B Ω) :
    valuesEquivOfEq (Finset.union_comm A B) (valuesUnionMk a b)
      = valuesUnionMk b a := by
  funext ⟨v, hv⟩
  have hvAB : v ∈ A ∪ B := by rwa [Finset.union_comm]
  show valuesUnionMk a b ⟨v, hvAB⟩ = valuesUnionMk b a ⟨v, hv⟩
  by_cases hA : v ∈ A
  · have hB : v ∉ B := fun h => Finset.disjoint_left.mp hAB hA h
    simp only [valuesUnionMk, dif_pos hA, dif_neg hB]
  · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_right hA
    simp only [valuesUnionMk, dif_pos hB, dif_neg hA]

/-- **Right `∅` collapse.**  Reindexing `valuesUnionMk a e` (with `e` the trivial
    block on `∅`) along `A ∪ ∅ = A` recovers `a`. -/
lemma valuesUnionMk_empty_right {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A : Finset M}
    (a : ValuesOn A Ω) (e : ValuesOn (∅ : Finset M) Ω) :
    valuesEquivOfEq (Finset.union_empty A) (valuesUnionMk a e) = a := by
  funext ⟨v, hv⟩
  have hvA : v ∈ A ∪ (∅ : Finset M) := by rwa [Finset.union_empty]
  show valuesUnionMk a e ⟨v, hvA⟩ = a ⟨v, hv⟩
  simp only [valuesUnionMk, dif_pos hv]

/-- A value block is `HEq` to its reindexing along a `Finset` equality.  The
    bridge that lets the equiv-mediated `Eq` laws above discharge legacy `HEq`
    goals in one line. -/
lemma valuesEquivOfEq_heq {M : Type*} {Ω : M → Type*} [∀ m, MeasurableSpace (Ω m)]
    {I J : Finset M} (h : I = J) (x : ValuesOn I Ω) :
    HEq (valuesEquivOfEq h x) x := by
  subst h
  exact heq_of_eq rfl

/-- **Union commutativity, `HEq` form.**  Supersedes the ad-hoc per-proof `HEq`
    construction: a one-line corollary of `valuesUnionMk_comm`. -/
lemma valuesUnionMk_comm_heq {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A B : Finset M} (hAB : Disjoint A B)
    (a : ValuesOn A Ω) (b : ValuesOn B Ω) :
    HEq (valuesUnionMk a b) (valuesUnionMk b a) := by
  rw [← valuesUnionMk_comm hAB a b]
  exact (valuesEquivOfEq_heq _ _).symm

/-- **Right `∅` collapse, `HEq` form.**  `valuesUnionMk a e` (trivial `∅` block)
    is `HEq` to `a`; a one-line corollary of `valuesUnionMk_empty_right`. -/
lemma valuesUnionMk_empty_right_heq {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A : Finset M}
    (a : ValuesOn A Ω) (e : ValuesOn (∅ : Finset M) Ω) :
    HEq (valuesUnionMk a e) a := by
  have h : valuesEquivOfEq (Finset.union_empty A) (valuesUnionMk a e) = a :=
    valuesUnionMk_empty_right a e
  have hx : HEq (valuesUnionMk a e)
      (valuesEquivOfEq (Finset.union_empty A) (valuesUnionMk a e)) :=
    (valuesEquivOfEq_heq (Finset.union_empty A) (valuesUnionMk a e)).symm
  rw [h] at hx
  exact hx

/-- **HEq of value assignments from coordinatewise agreement.** Given [two node sets `I` and
    `J` that are equal as sets](hyp:hIJ) and value assignments `f` on `I` and `g` on `J`, if
    [`f` and `g` agree at every node common to both index sets](hyp:h), then [`f` and `g` are
    heterogeneously equal (`HEq`)](goal).

    This packages the recurring `Function.hfunext` + `Subtype.heq_iff_coe_eq` + `heq_of_eq`
    boilerplate that every `ValuesOn` reindexing step (e.g. splicing/dropping a coordinate
    block when a conditioning set grows in a fixing sequence) would otherwise spell out by
    hand. -/
lemma valuesOn_heq_of_coord {M : Type*} {Ω : M → Type*} [∀ m, MeasurableSpace (Ω m)]
    {I J : Finset M} (hIJ : I = J) (f : ValuesOn I Ω) (g : ValuesOn J Ω)
    (h : ∀ (v : M) (hI : v ∈ I) (hJ : v ∈ J), f ⟨v, hI⟩ = g ⟨v, hJ⟩) :
    HEq f g := by
  apply Function.hfunext (congrArg (fun S : Finset M => {i // i ∈ S}) hIJ)
  rintro ⟨v, hvI⟩ ⟨v', hvJ⟩ hidx
  have hv_eq : v = v' := (Subtype.heq_iff_coe_eq (by intro x; rw [hIJ])).mp hidx
  subst hv_eq
  exact heq_of_eq (h v hvI hvJ)

end SCM

end Causalean
