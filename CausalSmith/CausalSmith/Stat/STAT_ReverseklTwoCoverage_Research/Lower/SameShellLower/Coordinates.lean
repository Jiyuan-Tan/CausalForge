import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Analysis
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionConstruction

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

def hardUIndex {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) : Fin d :=
  ⟨2 * j + 1, by
    unfold hardCoordinateCount at j
    have hj := j.isLt
    omega⟩

def hardWIndex {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) : Fin d :=
  ⟨2 * j + 2, by
    unfold hardCoordinateCount at j
    have hj := j.isLt
    omega⟩

def hardE0 {d : ℕ} (hd : 4 ≤ d) : Fin d → ℝ :=
  indexBasis ⟨0, by omega⟩

def hardU {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) : Fin d → ℝ :=
  indexBasis (hardUIndex hd j)

def hardW {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) : Fin d → ℝ :=
  indexBasis (hardWIndex hd j)

def hardZ {d : ℕ} (hd : 4 ≤ d) : Fin d → ℝ :=
  indexBasis ⟨d - 1, by omega⟩

lemma dot_indexBasis {d : ℕ} (i j : Fin d) :
    dotProduct (indexBasis i) (indexBasis j) = if i = j then 1 else 0 := by
  unfold dotProduct indexBasis
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

lemma dot_indexBasis_right {d : ℕ} (y : Fin d → ℝ) (j : Fin d) :
    dotProduct y (indexBasis j) = y j := by
  simp [dotProduct, indexBasis]

lemma hardUIndex_ne_zero {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) :
    hardUIndex hd j ≠ (⟨0, by omega⟩ : Fin d) := by
  intro h
  have := Fin.mk.inj h
  simp [hardUIndex] at this

lemma hardWIndex_ne_zero {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) :
    hardWIndex hd j ≠ (⟨0, by omega⟩ : Fin d) := by
  intro h
  have := Fin.mk.inj h
  simp [hardWIndex] at this

lemma hardUIndex_injective {d : ℕ} (hd : 4 ≤ d) :
    Function.Injective (hardUIndex hd) := by
  intro j l h
  apply Fin.ext
  have := Fin.mk.inj h
  simp [hardUIndex] at this
  omega

lemma hardWIndex_injective {d : ℕ} (hd : 4 ≤ d) :
    Function.Injective (hardWIndex hd) := by
  intro j l h
  apply Fin.ext
  have := Fin.mk.inj h
  simp [hardWIndex] at this
  omega

lemma hardUIndex_ne_hardWIndex {d : ℕ} (hd : 4 ≤ d)
    (j l : Fin (hardCoordinateCount d)) :
    hardUIndex hd j ≠ hardWIndex hd l := by
  intro h
  have := Fin.mk.inj h
  simp [hardUIndex, hardWIndex] at this
  omega

lemma hardWIndex_ne_hardUIndex {d : ℕ} (hd : 4 ≤ d)
    (j l : Fin (hardCoordinateCount d)) :
    hardWIndex hd j ≠ hardUIndex hd l :=
  Ne.symm (hardUIndex_ne_hardWIndex hd l j)

lemma hardUIndex_ne_last_of_even {d : ℕ} (hd : 4 ≤ d)
    (heven : Even d) (j : Fin (hardCoordinateCount d)) :
    hardUIndex hd j ≠ (⟨d - 1, by omega⟩ : Fin d) := by
  intro h
  have hj := j.isLt
  unfold hardCoordinateCount at hj
  have hh := Fin.mk.inj h
  simp [hardUIndex] at hh
  rcases heven with ⟨r, rfl⟩
  omega

lemma hardWIndex_ne_last_of_even {d : ℕ} (hd : 4 ≤ d)
    (heven : Even d) (j : Fin (hardCoordinateCount d)) :
    hardWIndex hd j ≠ (⟨d - 1, by omega⟩ : Fin d) := by
  intro h
  have hj := j.isLt
  unfold hardCoordinateCount at hj
  have hh := Fin.mk.inj h
  simp [hardWIndex] at hh
  rcases heven with ⟨r, rfl⟩
  omega

lemma hard_coordinate_orthonormal {d : ℕ} (hd : 4 ≤ d) :
    (∀ j, dotProduct (hardE0 hd) (hardU hd j) = 0 ∧
      dotProduct (hardE0 hd) (hardW hd j) = 0 ∧
      dotProduct (hardU hd j) (hardU hd j) = 1 ∧
      dotProduct (hardW hd j) (hardW hd j) = 1 ∧
      dotProduct (hardU hd j) (hardW hd j) = 0) ∧
    (∀ j l, j ≠ l →
      dotProduct (hardU hd j) (hardU hd l) = 0 ∧
      dotProduct (hardU hd j) (hardW hd l) = 0 ∧
      dotProduct (hardW hd j) (hardU hd l) = 0 ∧
      dotProduct (hardW hd j) (hardW hd l) = 0) ∧
    dotProduct (hardE0 hd) (hardE0 hd) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp only [hardE0, hardU, hardW, dot_indexBasis]
    simp [Ne.symm (hardUIndex_ne_zero hd j),
      Ne.symm (hardWIndex_ne_zero hd j),
      hardUIndex_ne_hardWIndex hd j j]
  · intro j l hjl
    simp only [hardU, hardW, dot_indexBasis]
    rw [if_neg (fun h => hjl (hardUIndex_injective hd h)),
      if_neg (hardUIndex_ne_hardWIndex hd j l),
      if_neg (hardWIndex_ne_hardUIndex hd j l),
      if_neg (fun h => hjl (hardWIndex_injective hd h))]
    simp
  · simp [hardE0, dot_indexBasis]

lemma hard_z_orthonormal_of_even {d : ℕ} (hd : 4 ≤ d)
    (heven : Even d) :
    dotProduct (hardZ hd) (hardZ hd) = 1 ∧
    dotProduct (hardE0 hd) (hardZ hd) = 0 ∧
    ∀ j, dotProduct (hardU hd j) (hardZ hd) = 0 ∧
      dotProduct (hardW hd j) (hardZ hd) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [hardZ, dot_indexBasis]
  · simp only [hardE0, hardZ, dot_indexBasis]
    rw [if_neg]
    intro h
    have := Fin.mk.inj h
    simp at this
    omega
  · intro j
    simp only [hardU, hardW, hardZ, dot_indexBasis]
    rw [if_neg (hardUIndex_ne_last_of_even hd heven j),
      if_neg (hardWIndex_ne_last_of_even hd heven j)]
    simp

end CausalSmith.Stat.ReverseKLTwoCoverage
