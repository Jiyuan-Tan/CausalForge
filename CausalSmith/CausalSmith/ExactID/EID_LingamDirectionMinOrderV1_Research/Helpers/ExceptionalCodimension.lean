/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Chain codimension for the exceptional locus
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.Varieties

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

/-- `C` is an irreducible component of the Zariski-closed set `Z`. -/
def IsIrreducibleComponent (C Z : Set (CumVec ℂ)) : Prop :=
  IsIrreducibleZariskiClosed C ∧ C ⊆ Z ∧
    ∀ C', IsIrreducibleZariskiClosed C' → C ⊆ C' → C' ⊆ Z → C' = C

/-- Exact minimum codimension of a closed set in an ambient irreducible variety,
measured by strict irreducible chains from its components. -/
def HasCodimensionIn (d : ℕ) (Z X : Set (CumVec ℂ)) : Prop :=
  (∀ C, IsIrreducibleComponent C Z →
    ∃ chain : Fin (d + 1) → Set (CumVec ℂ),
      StrictMono chain ∧ (∀ i, IsIrreducibleZariskiClosed (chain i)) ∧
      chain 0 = C ∧ chain (Fin.last d) = X) ∧
  ∃ C, IsIrreducibleComponent C Z ∧
    ¬ ∃ chain : Fin (d + 2) → Set (CumVec ℂ),
      StrictMono chain ∧ (∀ i, IsIrreducibleZariskiClosed (chain i)) ∧
      chain 0 = C ∧ chain (Fin.last (d + 1)) = X

private def threeIndices (d : ℕ) (hd : 2 ≤ d) (i : Fin 3) : Fin (d + 1) :=
  ⟨if i.val = 2 then d else i.val, by split <;> omega⟩

private lemma threeIndices_strictMono (d : ℕ) (hd : 2 ≤ d) :
    StrictMono (threeIndices d hd) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  change (threeIndices d hd (Fin.castSucc i)).val <
    (threeIndices d hd i.succ).val
  simp only [threeIndices]
  fin_cases i <;> simp [threeIndices] <;> omega

private lemma threeIndices_zero (d : ℕ) (hd : 2 ≤ d) :
    threeIndices d hd 0 = 0 := by
  apply Fin.ext
  simp [threeIndices]

private lemma threeIndices_last (d : ℕ) (hd : 2 ≤ d) :
    threeIndices d hd (Fin.last 2) = Fin.last d := by
  apply Fin.ext
  simp [threeIndices, Fin.last]

/-- Exact codimension one excludes every claimed exact codimension `d ≥ 2`. -/
lemma HasCodimensionIn.not_of_one {Z X : Set (CumVec ℂ)}
    (h1 : HasCodimensionIn 1 Z X) {d : ℕ} (hd : 2 ≤ d) :
    ¬ HasCodimensionIn d Z X := by
  rintro hdimen
  obtain ⟨C, hC, hno3⟩ := h1.2
  obtain ⟨chain, hmono, hirr, hzero, hlast⟩ := hdimen.1 C hC
  apply hno3
  refine ⟨chain ∘ threeIndices d hd, hmono.comp (threeIndices_strictMono d hd),
    ?_, ?_, ?_⟩
  · exact fun i => hirr (threeIndices d hd i)
  · rw [Function.comp_apply, threeIndices_zero, hzero]
  · rw [Function.comp_apply, threeIndices_last, hlast]

private def twoSetChain (C X : Set (CumVec ℂ)) : Fin 2 → Set (CumVec ℂ)
  | ⟨0, _⟩ => C
  | ⟨1, _⟩ => X
  | ⟨n + 2, hn⟩ => by omega

private lemma twoSetChain_strictMono {C X : Set (CumVec ℂ)} (hCX : C ⊂ X) :
    StrictMono (twoSetChain C X) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  change C ⊂ X
  exact hCX

/-- A proper closed subset of an irreducible ambient has codimension at least
one; one component with no intermediate irreducible closed set makes the
minimum codimension exactly one. -/
lemma hasCodimensionIn_one_of_component
    {Z X : Set (CumVec ℂ)}
    (hX : IsIrreducibleZariskiClosed X)
    (hZX : Z ⊆ X) (hne : Z ≠ X)
    (hw : ∃ C, IsIrreducibleComponent C Z ∧
      ¬ ∃ chain : Fin 3 → Set (CumVec ℂ),
        StrictMono chain ∧ (∀ i, IsIrreducibleZariskiClosed (chain i)) ∧
        chain 0 = C ∧ chain (Fin.last 2) = X) :
    HasCodimensionIn 1 Z X := by
  constructor
  · intro C hC
    have hCX : C ⊂ X := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨hC.2.1.trans hZX, ?_⟩
      intro hEq
      apply hne
      apply Set.Subset.antisymm hZX
      simpa [hEq] using hC.2.1
    refine ⟨twoSetChain C X, twoSetChain_strictMono hCX, ?_, rfl, rfl⟩
    intro i
    fin_cases i
    · exact hC.1
    · exact hX
  · exact hw

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
