import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenter
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.OverlapCount
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance_Part2
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance_Part3

/-!
# Mean-squared error and worst-case risk of the SNIPE estimator

Assembles the variance bound into a mean-squared-error bound for the estimator
at a fixed model, then takes worst cases to bound the risk over the
coefficient-mass and bounded-outcome model classes.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The modelwise SNIPE MSE bound used by both model classes. -/
private lemma snipe_model_mse_le
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (G : V → V → Prop) [DecidableRel G]
    (c : V → Finset V → ℝ) (d β : ℕ) (B : ℝ)
    (hdegree : BoundedDegree G d) (hlow : LowOrder c β)
    (hbound : ∀ i z, |potentialOutcome G c i z| ≤ B) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).mse
      (fun z =>
        snipeEstimator β p (fun j i => decide (G j i)) z
          (obsOutcome G c z))
      (tte G c) ≤
      B ^ 2 * (d : ℝ) * blockEnergy β p d / Fintype.card V := by
  classical
  let D := bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
    (fun _ => le_of_lt hp1)
  let W : V → (V → Bool) → ℝ := fun i z =>
    potentialOutcome G c i z *
      snipeScore (fun j i => decide (G j i)) β p i z
  let F : V → (V → Bool) → ℝ := fun i z => W i z - D.E (W i)
  have hN (i : V) :
      nbhdB (fun j i => decide (G j i)) i = nbhd G i := by
    ext j
    simp [nbhdB, nbhd]
  have hWmean (i : V) :
      D.E (W i) =
        potentialOutcome G c i (fun _ => true) -
          potentialOutcome G c i (fun _ => false) := by
    dsimp [D, W]
    rw [show (fun z =>
        potentialOutcome G c i z *
          snipeScore (fun j i => decide (G j i)) β p i z) =
      (fun z =>
        snipeScore (fun j i => decide (G j i)) β p i z *
          potentialOutcome G c i z) by
      funext z
      ring]
    exact snipeScore_potentialOutcome_moment G c β hlow p hp0 hp1 i
  have hFmean (i : V) : D.E (F i) = 0 := by
    dsimp [F]
    rw [D.E_sub, D.E_const]
    ring
  have hFdep (i : V) : DependsOnBlock (nbhd G i) (F i) := by
    intro z z' hzz
    dsimp [F, W]
    have hy := potentialOutcome_dependsOnBlock G c i z z' hzz
    have hg :
        snipeScore (fun j i => decide (G j i)) β p i z =
          snipeScore (fun j i => decide (G j i)) β p i z' := by
      apply snipeScore_dependsOnBlock
      intro j hj
      exact hzz j (by simpa [hN i] using hj)
    rw [hy, hg]
  have hscore (i : V) :
      D.E (fun z =>
        snipeScore (fun j i => decide (G j i)) β p i z ^ 2) ≤
        blockEnergy β p d := by
    calc
      D.E (fun z =>
          snipeScore (fun j i => decide (G j i)) β p i z ^ 2) =
          blockEnergy β p
            (nbhdB (fun j i => decide (G j i)) i).card := by
        dsimp [D]
        exact snipeScore_sq_expectation_for_variance
          (fun j i => decide (G j i)) β p hp0 hp1 i
      _ = localEnergy G β p i := by
        rw [hN]
        rfl
      _ ≤ blockEnergy β p d :=
        localEnergy_le_blockEnergy G d β p hp0 hp1 hdegree i
  have hFenergy (i : V) :
      D.E (fun z => F i z ^ 2) ≤ B ^ 2 * blockEnergy β p d := by
    have hsecond :
        D.E (fun z => W i z ^ 2) ≤
          B ^ 2 * D.E (fun z =>
            snipeScore (fun j i => decide (G j i)) β p i z ^ 2) := by
      have hpoint (z : V → Bool) :
          W i z ^ 2 ≤
            B ^ 2 *
              snipeScore (fun j i => decide (G j i)) β p i z ^ 2 := by
        have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbound i z)
        have hYsq :
            potentialOutcome G c i z ^ 2 ≤ B ^ 2 := by
          apply (sq_le_sq).2
          simpa [abs_of_nonneg hB0] using hbound i z
        dsimp [W]
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hYsq (sq_nonneg _)
      have hn := D.E_nonneg (fun z => sub_nonneg.mpr (hpoint z))
      rw [D.E_sub, D.E_const_mul] at hn
      linarith
    calc
      D.E (fun z => F i z ^ 2) = D.Var (W i) := by
        rfl
      _ ≤ D.E (fun z => W i z ^ 2) := by
        rw [D.Var_eq]
        exact sub_le_self _ (sq_nonneg _)
      _ ≤ B ^ 2 * D.E (fun z =>
          snipeScore (fun j i => decide (G j i)) β p i z ^ 2) :=
        hsecond
      _ ≤ B ^ 2 * blockEnergy β p d :=
        mul_le_mul_of_nonneg_left (hscore i) (sq_nonneg B)
  have hsumF :
      D.E (fun z => (∑ i : V, F i z) ^ 2) ≤
        (d : ℝ) * ∑ i : V, D.E (fun z => F i z ^ 2) :=
    E_sum_sq_le_degree_mul_sum_energy p hp0 hp1 G d hdegree
      F hFmean hFdep
  have hsumEnergy :
      D.E (fun z => (∑ i : V, F i z) ^ 2) ≤
        (d : ℝ) * Fintype.card V * (B ^ 2 * blockEnergy β p d) := by
    calc
      D.E (fun z => (∑ i : V, F i z) ^ 2) ≤
          (d : ℝ) * ∑ i : V, D.E (fun z => F i z ^ 2) := hsumF
      _ ≤ (d : ℝ) * ∑ _i : V, B ^ 2 * blockEnergy β p d := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun i _ => hFenergy i)
        · positivity
      _ = (d : ℝ) * Fintype.card V *
          (B ^ 2 * blockEnergy β p d) := by
        rw [Finset.sum_const]
        simp
        ring
  have hUnbiased :
      D.Unbiased
        (fun z =>
          snipeEstimator β p (fun j i => decide (G j i)) z
            (obsOutcome G c z))
        (tte G c) := by
    unfold FiniteDesign.Unbiased snipeEstimator tte
    rw [D.E_const_mul, D.E_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hWmean i
  rw [D.mse_eq_var_of_unbiased hUnbiased]
  rw [show (fun z =>
      snipeEstimator β p (fun j i => decide (G j i)) z
        (obsOutcome G c z)) =
      (fun z => (Fintype.card V : ℝ)⁻¹ * ∑ i : V, W i z) by
    rfl, D.Var_const_mul]
  have hVarSum :
      D.Var (fun z => ∑ i : V, W i z) =
        D.E (fun z => (∑ i : V, F i z) ^ 2) := by
    unfold FiniteDesign.Var
    rw [D.E_sum]
    apply D.E_congr
    intro z
    congr 1
    dsimp [F]
    rw [Finset.sum_sub_distrib]
  rw [hVarSum]
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
    calc
      ((Fintype.card V : ℝ)⁻¹) ^ 2 *
          D.E (fun z => (∑ i : V, F i z) ^ 2) ≤
        ((Fintype.card V : ℝ)⁻¹) ^ 2 *
          ((d : ℝ) * Fintype.card V *
            (B ^ 2 * blockEnergy β p d)) :=
          mul_le_mul_of_nonneg_left hsumEnergy (sq_nonneg _)
      _ = B ^ 2 * (d : ℝ) * blockEnergy β p d /
          Fintype.card V := by
        field_simp

/-- A raw coefficient-mass bound implies the corresponding uniform outcome
bound. -/
private lemma potentialOutcome_abs_le_of_mass
    (G : V → V → Prop) (c : V → Finset V → ℝ) (B : ℝ)
    (hmass : BoundedCoeffMass G c B) :
    ∀ i z, |potentialOutcome G c i z| ≤ B := by
  intro i z
  calc
    |potentialOutcome G c i z| ≤
        ∑ S ∈ (nbhd G i).powerset,
          |c i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0| := by
      unfold potentialOutcome
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (nbhd G i).powerset, |c i S| := by
      apply Finset.sum_le_sum
      intro S hS
      rw [abs_mul]
      have hprod0 :
          0 ≤ ∏ j ∈ S, if z j then (1 : ℝ) else 0 := by
        positivity
      rw [abs_of_nonneg hprod0]
      apply mul_le_of_le_one_right (abs_nonneg _)
      apply Finset.prod_le_one
      · intro j hj
        split <;> norm_num
      · intro j hj
        split <;> norm_num
    _ ≤ B := hmass i

/-- Modelwise form of the sharp coefficient-class SNIPE risk bound. -/
lemma riskAt_snipe_le
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (M : ModelClass V d β B) :
    riskAt p (le_of_lt hp0) (le_of_lt hp1) M
        (snipeEstimator β p) ≤
      B ^ 2 * (d : ℝ) * blockEnergy β p d / Fintype.card V := by
  letI : DecidableRel M.edge := M.decEdge
  unfold riskAt edgeFn
  exact snipe_model_mse_le p hp0 hp1 M.edge M.coef d β B
    M.degree_le M.low_order
    (potentialOutcome_abs_le_of_mass M.edge M.coef B M.mass_le)

/-- Modelwise form of the sharp bounded-outcome SNIPE risk bound. -/
lemma riskAtBdd_snipe_le
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (M : BddOutcomeModelClass V d β B) :
    riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M
        (snipeEstimator β p) ≤
      B ^ 2 * (d : ℝ) * blockEnergy β p d / Fintype.card V := by
  letI : DecidableRel M.edge := M.decEdge
  unfold riskAtBdd edgeFnBdd
  exact snipe_model_mse_le p hp0 hp1 M.edge M.coef d β B
    M.degree_le M.low_order M.outcome_bound

/-- The unclipped coefficient-class worst risk has the sharp unit constant. -/
lemma worstRisk_snipe_le
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d β : ℕ) (B : ℝ) :
    worstRisk (V := V) p (le_of_lt hp0) (le_of_lt hp1) d β B
        (snipeEstimator β p) ≤
      B ^ 2 * (d : ℝ) * blockEnergy β p d / Fintype.card V := by
  unfold worstRisk
  by_cases hM : Nonempty (ModelClass V d β B)
  · apply csSup_le
    · exact Set.range_nonempty _
    · intro r hr
      rcases hr with ⟨M, rfl⟩
      letI : DecidableRel M.edge := M.decEdge
      unfold riskAt edgeFn
      exact snipe_model_mse_le p hp0 hp1 M.edge M.coef d β B
        M.degree_le M.low_order
        (potentialOutcome_abs_le_of_mass M.edge M.coef B M.mass_le)
  · have hrange :
        Set.range (fun M : ModelClass V d β B =>
          riskAt p (le_of_lt hp0) (le_of_lt hp1) M
            (snipeEstimator β p)) = ∅ := by
      ext r
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨M, rfl⟩
      exact hM ⟨M⟩
    rw [hrange, Real.sSup_empty]
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (sq_nonneg B)
        positivity
      · unfold blockEnergy
        apply Finset.sum_nonneg
        intro r hr
        apply div_nonneg
        · positivity
        · exact pow_nonneg
            (mul_nonneg (le_of_lt hp0) (sub_nonneg.mpr (le_of_lt hp1))) _
    · positivity

/-- The identical unclipped bound holds on the bounded-outcome class. -/
lemma worstRiskBdd_snipe_le
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d β : ℕ) (B : ℝ) :
    worstRiskBdd (V := V) p (le_of_lt hp0) (le_of_lt hp1) d β B
        (snipeEstimator β p) ≤
      B ^ 2 * (d : ℝ) * blockEnergy β p d / Fintype.card V := by
  unfold worstRiskBdd
  by_cases hM : Nonempty (BddOutcomeModelClass V d β B)
  · apply csSup_le
    · exact Set.range_nonempty _
    · intro r hr
      rcases hr with ⟨M, rfl⟩
      letI : DecidableRel M.edge := M.decEdge
      unfold riskAtBdd edgeFnBdd
      exact snipe_model_mse_le p hp0 hp1 M.edge M.coef d β B
        M.degree_le M.low_order M.outcome_bound
  · have hrange :
        Set.range (fun M : BddOutcomeModelClass V d β B =>
          riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M
            (snipeEstimator β p)) = ∅ := by
      ext r
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨M, rfl⟩
      exact hM ⟨M⟩
    rw [hrange, Real.sSup_empty]
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (sq_nonneg B)
        positivity
      · unfold blockEnergy
        apply Finset.sum_nonneg
        intro r hr
        apply div_nonneg
        · positivity
        · exact pow_nonneg
            (mul_nonneg (le_of_lt hp0) (sub_nonneg.mpr (le_of_lt hp1))) _
    · positivity

/-- An estimator's design mean-squared error at a coefficient-mass model is unchanged when
the assignment probability, its bounds, the model, and the estimator are replaced by equal
values. -/
add_decl_doc riskAt.congr_simp

/-- An estimator's design mean-squared error at a bounded-outcome model is unchanged when the
assignment probability, its bounds, the model, and the estimator are replaced by equal values. -/
add_decl_doc riskAtBdd.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
