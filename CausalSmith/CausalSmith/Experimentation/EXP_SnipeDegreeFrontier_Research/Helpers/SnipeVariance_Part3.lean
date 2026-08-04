import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenter
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.OverlapCount
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance_Part2

/-!
# The degree-weighted second-moment bound

Bounds the second moment of a sum of block-dependent terms by the maximum degree
times the total energy, and applies it to the SNIPE score to obtain the
single-overlap variance bound.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The variance of a sum of centered block-dependent functions is bounded
by one out-degree charge times the sum of their individual energies. -/
lemma E_sum_sq_le_degree_mul_sum_energy
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (G : V → V → Prop) (d : ℕ) (hdegree : BoundedDegree G d)
    (F : V → (V → Bool) → ℝ)
    (hmean : ∀ i,
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E (F i) = 0)
    (hdep : ∀ i, DependsOnBlock (nbhd G i) (F i)) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
        (fun z => (∑ i : V, F i z) ^ 2) ≤
      (d : ℝ) * ∑ i : V,
        (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E (fun z => F i z ^ 2) := by
  classical
  choose a ha using fun i =>
    exists_globalCenteredMonomial_expansion (V := V) p (F i)
  have ha0 (i : V) : a i ∅ = 0 :=
    globalCenteredMonomial_empty_coef_eq_zero p
      (le_of_lt hp0) (le_of_lt hp1) (F i) (a i) (ha i) (hmean i)
  have haOut (i : V) (S : Finset V)
      (hS : S ∈ (Finset.univ : Finset V).powerset)
      (hSN : ¬ S ⊆ nbhd G i) :
      a i S = 0 :=
    globalCenteredMonomial_coef_eq_zero_of_not_subset p hp0 hp1
      (nbhd G i) (F i) (hdep i) (a i) (ha i) S hS hSN
  let I : Finset V → Finset V := fun S =>
    Finset.univ.filter (fun i => S ⊆ nbhd G i)
  have hcardI (S : Finset V) (hSne : S.Nonempty) :
      (I S).card ≤ d := by
    obtain ⟨j, hjS⟩ := hSne
    have hsub : I S ⊆ outNbhd G j := by
      intro i hi
      have hSi : S ⊆ nbhd G i := (Finset.mem_filter.mp hi).2
      have hji : j ∈ nbhd G i := hSi hjS
      simpa [outNbhd, nbhd] using hji
    exact (Finset.card_le_card hsub).trans (hdegree.2 j)
  have hsumI (S : Finset V)
      (hS : S ∈ (Finset.univ : Finset V).powerset) :
      (∑ i : V, a i S) = ∑ i ∈ I S, a i S := by
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · exact Finset.subset_univ _
    · intro i hi
      apply haOut i S hS
      simpa [I] using (Finset.mem_sdiff.mp hi).2
    · intro i hi
      rfl
  let A : Finset V → ℝ := fun S => ∑ i : V, a i S
  have hsumExpansion (z : V → Bool) :
      (∑ i : V, F i z) =
        ∑ S ∈ (Finset.univ : Finset V).powerset,
          A S * globalCenteredMonomial p S z := by
    simp_rw [ha]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S hS
    dsimp [A]
    rw [Finset.sum_mul]
  rw [globalCenteredMonomial_expansion_energy p
    (le_of_lt hp0) (le_of_lt hp1)
    (fun z => ∑ i : V, F i z) A hsumExpansion]
  calc
    (∑ S ∈ (Finset.univ : Finset V).powerset,
        A S ^ 2 * (p * (1 - p)) ^ S.card) ≤
      ∑ S ∈ (Finset.univ : Finset V).powerset,
        (d : ℝ) * (∑ i : V, (a i S) ^ 2) *
          (p * (1 - p)) ^ S.card := by
      apply Finset.sum_le_sum
      intro S hS
      by_cases hSne : S.Nonempty
      · have hCS :
            (∑ i ∈ I S, a i S) ^ 2 ≤
              ((I S).card : ℝ) * ∑ i ∈ I S, (a i S) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        have hcardR : ((I S).card : ℝ) ≤ d := by
          exact_mod_cast hcardI S hSne
        have hsquares : 0 ≤ ∑ i ∈ I S, (a i S) ^ 2 := by
          positivity
        have hCS' :
            A S ^ 2 ≤ (d : ℝ) * ∑ i : V, (a i S) ^ 2 := by
          rw [show A S = ∑ i ∈ I S, a i S by
            exact hsumI S hS]
          calc
            (∑ i ∈ I S, a i S) ^ 2 ≤
                ((I S).card : ℝ) * ∑ i ∈ I S, (a i S) ^ 2 := hCS
            _ ≤ (d : ℝ) * ∑ i ∈ I S, (a i S) ^ 2 :=
              mul_le_mul_of_nonneg_right hcardR hsquares
            _ ≤ (d : ℝ) * ∑ i : V, (a i S) ^ 2 := by
              apply mul_le_mul_of_nonneg_left
              · exact Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
              · positivity
        exact mul_le_mul_of_nonneg_right hCS'
          (pow_nonneg (mul_nonneg (le_of_lt hp0)
            (le_of_lt (sub_pos.mpr hp1))) _)
      · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
        subst S
        simp [A, ha0]
    _ = (d : ℝ) * ∑ i : V,
        ∑ S ∈ (Finset.univ : Finset V).powerset,
          (a i S) ^ 2 * (p * (1 - p)) ^ S.card := by
      rw [show
          (∑ S ∈ (Finset.univ : Finset V).powerset,
            (d : ℝ) * (∑ i : V, (a i S) ^ 2) *
              (p * (1 - p)) ^ S.card) =
          ∑ S ∈ (Finset.univ : Finset V).powerset,
            ∑ i : V, (d : ℝ) * (a i S) ^ 2 *
              (p * (1 - p)) ^ S.card by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mul_sum, Finset.sum_mul]]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = (d : ℝ) * ∑ i : V,
        (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E (fun z => F i z ^ 2) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro i hi
      symm
      exact globalCenteredMonomial_expansion_energy p
        (le_of_lt hp0) (le_of_lt hp1) (F i) (a i) (ha i)

/-- Exact second moment of a global SNIPE score. -/
lemma snipeScore_sq_expectation_for_variance
    (G : V → V → Bool) (β : ℕ) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (i : V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).E
        (fun z => snipeScore G β p i z ^ 2) =
      blockEnergy β p (nbhdB G i).card := by
  let v := p * (1 - p)
  have hv : v ≠ 0 :=
    mul_ne_zero hp0.ne' (sub_pos.mpr hp1).ne'
  simp only [snipeScore, pow_two, Finset.sum_mul, Finset.mul_sum,
    FiniteDesign.E_sum]
  have hmoment (r q : ℕ) (S T : Finset V) :
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
        (fun z =>
          (bernoulliContrast p q / v ^ q *
              globalCenteredMonomial p T z) *
            (bernoulliContrast p r / v ^ r *
              globalCenteredMonomial p S z)) =
        (bernoulliContrast p q / v ^ q) *
          (bernoulliContrast p r / v ^ r) *
            (if T = S then v ^ T.card else 0) := by
    calc
      _ = (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E
          (fun z =>
            ((bernoulliContrast p q / v ^ q) *
              (bernoulliContrast p r / v ^ r)) *
                (globalCenteredMonomial p T z *
                  globalCenteredMonomial p S z)) := by
        apply FiniteDesign.E_congr
        intro z
        ring
      _ = _ := by
        rw [FiniteDesign.E_const_mul,
          E_globalCenteredMonomial_mul p (le_of_lt hp0) (le_of_lt hp1)]
  simpa only [globalCenteredMonomial] using (show
      (∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
        ∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
          ∑ q ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
            ∑ T ∈ (nbhdB G i).powerset.filter (fun T => T.card = q),
              (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
                (fun _ => le_of_lt hp1)).E
                (fun z =>
                  (bernoulliContrast p q / (p * (1 - p)) ^ q *
                    globalCenteredMonomial p T z) *
                  (bernoulliContrast p r / (p * (1 - p)) ^ r *
                    globalCenteredMonomial p S z))) =
        blockEnergy β p (nbhdB G i).card by
    dsimp [v] at hmoment
    simp_rw [hmoment]
    simp [blockEnergy]
    apply Finset.sum_congr rfl
    intro r hr
    have hrle : r ≤ effBeta β (nbhdB G i).card :=
      (Finset.mem_Icc.mp hr).2
    rw [show
        (∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
          ∑ q ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
            if S ⊆ nbhdB G i ∧ S.card = q then
              bernoulliContrast p q / (p * (1 - p)) ^ q *
                (bernoulliContrast p r / (p * (1 - p)) ^ r) *
                  (p * (1 - p)) ^ S.card
            else 0) =
        ∑ _S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
          bernoulliContrast p r / (p * (1 - p)) ^ r *
            (bernoulliContrast p r / (p * (1 - p)) ^ r) *
              (p * (1 - p)) ^ r by
      apply Finset.sum_congr rfl
      intro S hS
      have hSmem := Finset.mem_filter.mp hS
      have hSsub := Finset.mem_powerset.mp hSmem.1
      have hScard := hSmem.2
      rw [Finset.sum_eq_single r]
      · simp [hSsub, hScard, hr]
      · intro q hq hqr
        simp [hScard, hqr.symm]
      · intro hnot
        exact (hnot hr).elim]
    rw [show
        (nbhdB G i).powerset.filter (fun S => S.card = r) =
          (nbhdB G i).powersetCard r by
      ext S
      simp [Finset.mem_powersetCard]]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp only [nsmul_eq_mul]
    field_simp)

/-- A potential outcome depends only on its graph neighborhood. -/
lemma potentialOutcome_dependsOnBlock
    (G : V → V → Prop) (c : V → Finset V → ℝ) (i : V) :
    DependsOnBlock (nbhd G i) (potentialOutcome G c i) := by
  intro z z' hzz
  unfold potentialOutcome
  apply Finset.sum_congr rfl
  intro S hS
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [hzz j ((Finset.mem_powerset.mp hS) hj)]

/-- A SNIPE score depends only on the neighborhood read from its graph
argument. -/
lemma snipeScore_dependsOnBlock
    (G : V → V → Bool) (β : ℕ) (p : ℝ) (i : V) :
    DependsOnBlock (nbhdB G i) (snipeScore G β p i) := by
  intro z z' hzz
  unfold snipeScore
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.prod_congr rfl
  intro j hj
  rw [hzz j ((Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) hj)]

end CausalSmith.Experimentation.SnipeDegreeFrontier
