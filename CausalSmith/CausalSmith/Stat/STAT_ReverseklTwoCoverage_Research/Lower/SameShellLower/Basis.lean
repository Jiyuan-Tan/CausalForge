import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Coordinates

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

abbrev HardBasisCarrier (d : ℕ) :=
  Fin 1 ⊕ (Fin (hardCoordinateCount d) ⊕
    (Fin (hardCoordinateCount d) ⊕ Fin (if Even d then 1 else 0)))

lemma hardBasisCarrier_card {d : ℕ} (hd : 4 ≤ d) :
    Fintype.card (HardBasisCarrier d) = d := by
  simp only [HardBasisCarrier, Fintype.card_sum, Fintype.card_fin]
  rcases Nat.even_or_odd d with heven | hodd
  · rcases heven with ⟨r, hr⟩
    subst d
    rw [if_pos (show Even (r + r) from ⟨r, rfl⟩)]
    unfold hardCoordinateCount
    omega
  · have hneven : ¬ Even d := Nat.not_even_iff_odd.mpr hodd
    rw [if_neg hneven]
    rcases hodd with ⟨r, hr⟩
    subst d
    unfold hardCoordinateCount
    omega

noncomputable def hardBasisEquiv {d : ℕ} (hd : 4 ≤ d) :
    HardBasisCarrier d ≃ Fin d :=
  Fintype.equivOfCardEq (by
    simpa using hardBasisCarrier_card hd)

noncomputable def hardBasisE0 {d : ℕ} (hd : 4 ≤ d) : Fin d → ℝ :=
  indexBasis (hardBasisEquiv hd (Sum.inl 0))

noncomputable def hardBasisU {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) : Fin d → ℝ :=
  indexBasis (hardBasisEquiv hd (Sum.inr (Sum.inl j)))

noncomputable def hardBasisW {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) : Fin d → ℝ :=
  indexBasis (hardBasisEquiv hd (Sum.inr (Sum.inr (Sum.inl j))))

noncomputable def hardBasisZ {d : ℕ} (hd : 4 ≤ d) : Fin d → ℝ := by
  classical
  by_cases heven : Even d
  · exact indexBasis
      (hardBasisEquiv hd
        (Sum.inr (Sum.inr (Sum.inr ⟨0, by simp [heven]⟩))))
  · exact hardBasisE0 hd

lemma sum_fin_ite_one {P : Prop} [Decidable P] (hP : P)
    (f : Fin (if P then 1 else 0) → ℝ) :
    (∑ i, f i) = f ⟨0, by simp [hP]⟩ := by
  let e : Fin (if P then 1 else 0) ≃ Fin 1 :=
    finCongr (by simp [hP])
  calc
    (∑ i, f i) = ∑ j : Fin 1, f (e.symm j) := by
      symm
      exact Equiv.sum_comp e.symm f
    _ = f (e.symm 0) := Fin.sum_univ_one _
    _ = f ⟨0, by simp [hP]⟩ := by
      congr 1

lemma sum_fin_ite_zero {P : Prop} [Decidable P] (hP : ¬ P)
    (f : Fin (if P then 1 else 0) → ℝ) :
    (∑ i, f i) = 0 := by
  haveI : IsEmpty (Fin (if P then 1 else 0)) := by
    simpa [hP] using (inferInstance : IsEmpty (Fin 0))
  rw [Finset.univ_eq_empty]
  simp

lemma hardBasis_coordinate_orthonormal {d : ℕ} (hd : 4 ≤ d) :
    (∀ j, dotProduct (hardBasisE0 hd) (hardBasisU hd j) = 0 ∧
      dotProduct (hardBasisE0 hd) (hardBasisW hd j) = 0 ∧
      dotProduct (hardBasisU hd j) (hardBasisU hd j) = 1 ∧
      dotProduct (hardBasisW hd j) (hardBasisW hd j) = 1 ∧
      dotProduct (hardBasisU hd j) (hardBasisW hd j) = 0) ∧
    (∀ j l, j ≠ l →
      dotProduct (hardBasisU hd j) (hardBasisU hd l) = 0 ∧
      dotProduct (hardBasisU hd j) (hardBasisW hd l) = 0 ∧
      dotProduct (hardBasisW hd j) (hardBasisU hd l) = 0 ∧
      dotProduct (hardBasisW hd j) (hardBasisW hd l) = 0) ∧
    dotProduct (hardBasisE0 hd) (hardBasisE0 hd) = 1 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp only [hardBasisE0, hardBasisU, hardBasisW, dot_indexBasis]
    simp
  · intro j l hjl
    simp only [hardBasisU, hardBasisW, dot_indexBasis]
    simp [hjl]
  · simp [hardBasisE0, dot_indexBasis]

lemma hardBasis_z_orthonormal_of_even {d : ℕ} (hd : 4 ≤ d)
    (heven : Even d) :
    dotProduct (hardBasisZ hd) (hardBasisZ hd) = 1 ∧
    dotProduct (hardBasisE0 hd) (hardBasisZ hd) = 0 ∧
    ∀ j, dotProduct (hardBasisU hd j) (hardBasisZ hd) = 0 ∧
      dotProduct (hardBasisW hd j) (hardBasisZ hd) = 0 := by
  classical
  simp only [hardBasisZ, dif_pos heven, hardBasisE0, hardBasisU,
    hardBasisW, dot_indexBasis]
  simp

lemma hardBasis_decomposition {d : ℕ} (hd : 4 ≤ d)
    (y : Fin d → ℝ) (i : Fin d) :
    y i = dotProduct y (hardBasisE0 hd) * hardBasisE0 hd i +
      ∑ j, (dotProduct y (hardBasisU hd j) * hardBasisU hd j i +
        dotProduct y (hardBasisW hd j) * hardBasisW hd j i) +
      if Even d then dotProduct y (hardBasisZ hd) * hardBasisZ hd i else 0 := by
  classical
  calc
    y i = ∑ q : Fin d, y q * indexBasis q i := by
      simp [indexBasis]
    _ = ∑ b : HardBasisCarrier d,
        y (hardBasisEquiv hd b) * indexBasis (hardBasisEquiv hd b) i := by
      symm
      exact Equiv.sum_comp (hardBasisEquiv hd)
        (fun q : Fin d => y q * indexBasis q i)
    _ = dotProduct y (hardBasisE0 hd) * hardBasisE0 hd i +
        ∑ j, (dotProduct y (hardBasisU hd j) * hardBasisU hd j i +
          dotProduct y (hardBasisW hd j) * hardBasisW hd j i) +
        if Even d then dotProduct y (hardBasisZ hd) * hardBasisZ hd i else 0 := by
      simp only [hardBasisE0, hardBasisU, hardBasisW,
        dot_indexBasis_right]
      by_cases heven : Even d
      · simp only [if_pos heven]
        rw [show hardBasisZ hd = indexBasis
            (hardBasisEquiv hd
              (Sum.inr (Sum.inr (Sum.inr ⟨0, by simp [heven]⟩)))) by
              simp [hardBasisZ, heven],
          dot_indexBasis_right]
        simp [HardBasisCarrier, heven]
        rw [Finset.sum_add_distrib]
        rw [sum_fin_ite_one heven]
        ring
      · simp [HardBasisCarrier, hardBasisZ, heven]
        rw [Finset.sum_add_distrib]
        rw [sum_fin_ite_zero heven]
        ring

end CausalSmith.Stat.ReverseKLTwoCoverage
