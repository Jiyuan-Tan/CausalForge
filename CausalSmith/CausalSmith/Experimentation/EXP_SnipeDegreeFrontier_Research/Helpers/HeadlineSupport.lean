import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.ContinuousPriorConverse
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

/-- Establishes the stated mathematical result for tte abs le of model class. -/
lemma tte_abs_le_of_modelClass
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {d β : ℕ} {B : ℝ} (M : ModelClass V d β B) :
    |tte M.edge M.coef| ≤ B := by
  classical
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold tte
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn)]
  calc
    (Fintype.card V : ℝ)⁻¹ *
        |∑ i : V, (potentialOutcome M.edge M.coef i (fun _ => true) -
          potentialOutcome M.edge M.coef i (fun _ => false))| ≤
      (Fintype.card V : ℝ)⁻¹ *
        ∑ i : V, |potentialOutcome M.edge M.coef i (fun _ => true) -
          potentialOutcome M.edge M.coef i (fun _ => false)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ∑ _i : V, B := by
      gcongr with i
      have htrue :
          potentialOutcome M.edge M.coef i (fun _ => true) =
            ∑ S ∈ (nbhd M.edge i).powerset, M.coef i S := by
        simp [potentialOutcome]
      have hfalse :
          potentialOutcome M.edge M.coef i (fun _ => false) =
            M.coef i ∅ := by
        unfold potentialOutcome
        simp_rw [Finset.prod_const]
        rw [Finset.sum_eq_single ∅]
        · simp
        · intro S hS hS0
          have hcard : 0 < S.card :=
            Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [zero_pow (Nat.ne_of_gt hcard), mul_zero]
        · simp
      rw [htrue, hfalse]
      rw [show
          (∑ S ∈ (nbhd M.edge i).powerset, M.coef i S) - M.coef i ∅ =
            ∑ S ∈ (nbhd M.edge i).powerset,
              if S = ∅ then 0 else M.coef i S by
        rw [show M.coef i ∅ =
            ∑ S ∈ (nbhd M.edge i).powerset,
              if S = ∅ then M.coef i ∅ else 0 by simp]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hS0 : S = ∅
        · subst S
          simp
        · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
          simp [hS0, hSne]]
      calc
        |∑ S ∈ (nbhd M.edge i).powerset,
            if S = ∅ then 0 else M.coef i S| ≤
          ∑ S ∈ (nbhd M.edge i).powerset,
            |if S = ∅ then 0 else M.coef i S| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ S ∈ (nbhd M.edge i).powerset, |M.coef i S| := by
          apply Finset.sum_le_sum
          intro S hS
          split_ifs <;> simp
        _ ≤ B := M.mass_le i
    _ = B := by simp [hn.ne']

/-- Establishes the stated mathematical result for tte abs le of bdd model class. -/
lemma tte_abs_le_of_bddModelClass
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {d β : ℕ} {B : ℝ} (M : BddOutcomeModelClass V d β B) :
    |tte M.edge M.coef| ≤ 2 * B := by
  classical
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold tte
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn)]
  calc
    (Fintype.card V : ℝ)⁻¹ *
        |∑ i : V, (_ - _)| ≤
      (Fintype.card V : ℝ)⁻¹ *
        ∑ i : V, |potentialOutcome M.edge M.coef i (fun _ => true) -
          potentialOutcome M.edge M.coef i (fun _ => false)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ∑ _i : V, (2 * B) := by
      gcongr with i
      exact (abs_sub _ _).trans <| (add_le_add
        (M.outcome_bound i _) (M.outcome_bound i _)).trans_eq (by ring)
    _ = 2 * B := by simp [hn.ne']

/-- Establishes the stated mathematical result for clip to sq sub le. -/
lemma clipTo_sq_sub_le (R x t : ℝ) (hR : 0 ≤ R) (ht : |t| ≤ R) :
    (clipTo R x - t) ^ 2 ≤ (x - t) ^ 2 := by
  rw [abs_le] at ht
  unfold clipTo
  by_cases hxlo : x < -R
  · rw [min_eq_right (le_trans hxlo.le (neg_le_self hR)),
      max_eq_left hxlo.le]
    nlinarith
  · have hxlo' : -R ≤ x := le_of_not_gt hxlo
    by_cases hxhi : R < x
    · rw [min_eq_left hxhi.le, max_eq_right (by linarith)]
      nlinarith
    · rw [min_eq_right (le_of_not_gt hxhi), max_eq_right hxlo']

/-- Establishes the stated mathematical result for risk at clipped le raw. -/
lemma riskAt_clipped_le_raw
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {d β : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (M : ModelClass V d β B) :
    riskAt p hp0 hp1 M (snipeClipped B β p) ≤
      riskAt p hp0 hp1 M (snipeEstimator β p) := by
  unfold riskAt FiniteDesign.mse FiniteDesign.E
  apply Finset.sum_le_sum
  intro z hz
  apply mul_le_mul_of_nonneg_left _ <|
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0) (fun _ => hp1)).p_nonneg z
  exact clipTo_sq_sub_le B _ _ hB (tte_abs_le_of_modelClass M)

/-- Establishes the stated mathematical result for risk at bdd clipped le raw. -/
lemma riskAtBdd_clipped_le_raw
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {d β : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (M : BddOutcomeModelClass V d β B) :
    riskAtBdd p hp0 hp1 M (snipeClippedBdd B β p) ≤
      riskAtBdd p hp0 hp1 M (snipeEstimator β p) := by
  unfold riskAtBdd FiniteDesign.mse FiniteDesign.E
  apply Finset.sum_le_sum
  intro z hz
  apply mul_le_mul_of_nonneg_left _ <|
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0) (fun _ => hp1)).p_nonneg z
  exact clipTo_sq_sub_le (2 * B) _ _ (by positivity)
    (tte_abs_le_of_bddModelClass M)

/-- Establishes the stated mathematical result for worst risk clipped le min. -/
lemma worstRisk_clipped_le_min
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d β : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    worstRisk (V := V) p (le_of_lt hp0) (le_of_lt hp1) d β B
        (snipeClipped B β p) ≤
      4 * B ^ 2 * min 1
        ((d : ℝ) * blockEnergy β p d / Fintype.card V) := by
  unfold worstRisk
  let M0 : ModelClass V d β B :=
    { edge := fun _ _ => False
      decEdge := fun _ _ => inferInstance
      coef := fun _ _ => 0
      supported := by simp
      degree_le := by simp [BoundedDegree, nbhd, outNbhd]
      low_order := by simp [LowOrder]
      mass_le := by intro i; simpa [BoundedCoeffMass] using hB }
  apply csSup_le
  · exact ⟨riskAt p (le_of_lt hp0) (le_of_lt hp1) M0
        (snipeClipped B β p), ⟨M0, rfl⟩⟩
  · rintro _ ⟨M, rfl⟩
    have hraw := riskAt_clipped_le_raw p (le_of_lt hp0) (le_of_lt hp1) hB M
    have hsat : riskAt p (le_of_lt hp0) (le_of_lt hp1) M
        (snipeClipped B β p) ≤ 4 * B ^ 2 := by
      unfold riskAt FiniteDesign.mse FiniteDesign.E
      calc
        _ ≤ ∑ z, (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
            (fun _ => le_of_lt hp1)).p z * (4 * B ^ 2) := by
          apply Finset.sum_le_sum
          intro z hz
          apply mul_le_mul_of_nonneg_left _ <|
            (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
              (fun _ => le_of_lt hp1)).p_nonneg z
          have hc : |snipeClipped B β p (edgeFn M) z
              (obsOutcome M.edge M.coef z)| ≤ B := by
            unfold snipeClipped clipTo
            rw [abs_le]
            simp [hB]
          have ht := tte_abs_le_of_modelClass M
          have he := (abs_sub _ _).trans (add_le_add hc ht)
          have he2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 he
          rw [sq_abs] at he2
          nlinarith
        _ = 4 * B ^ 2 := by
          rw [← Finset.sum_mul,
            (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
              (fun _ => le_of_lt hp1)).p_sum, one_mul]
    by_cases hx : (d : ℝ) * blockEnergy β p d / Fintype.card V ≤ 1
    · rw [min_eq_right hx]
      have hx0 : 0 ≤ (d : ℝ) * blockEnergy β p d / Fintype.card V := by
        apply div_nonneg
        · apply mul_nonneg (by positivity)
          unfold blockEnergy
          apply Finset.sum_nonneg
          intro r hr
          apply div_nonneg
          · exact mul_nonneg (by positivity) (sq_nonneg _)
          · exact pow_nonneg
              (mul_nonneg (le_of_lt hp0) (sub_nonneg.mpr (le_of_lt hp1))) _
        · positivity
      exact hraw.trans <| (riskAt_snipe_le p hp0 hp1 M).trans
        (by
          have hpdt : 0 ≤ B ^ 2 *
              ((d : ℝ) * blockEnergy β p d / Fintype.card V) :=
            mul_nonneg (sq_nonneg B) hx0
          ring_nf at hpdt ⊢
          nlinarith)
    · rw [min_eq_left (le_of_not_ge hx)]
      simpa using hsat

/-- Establishes the stated mathematical result for worst risk bdd clipped le min. -/
lemma worstRiskBdd_clipped_le_min
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d β : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    worstRiskBdd (V := V) p (le_of_lt hp0) (le_of_lt hp1) d β B
        (snipeClippedBdd B β p) ≤
      16 * B ^ 2 * min 1
        ((d : ℝ) * blockEnergy β p d / Fintype.card V) := by
  unfold worstRiskBdd
  let M0 : BddOutcomeModelClass V d β B :=
    { edge := fun _ _ => False
      decEdge := fun _ _ => inferInstance
      coef := fun _ _ => 0
      supported := by simp
      degree_le := by simp [BoundedDegree, nbhd, outNbhd]
      low_order := by simp [LowOrder]
      outcome_bound := by
        intro i z
        simpa [potentialOutcome, nbhd] using hB }
  apply csSup_le
  · exact ⟨riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M0
        (snipeClippedBdd B β p), ⟨M0, rfl⟩⟩
  · rintro _ ⟨M, rfl⟩
    have hraw := riskAtBdd_clipped_le_raw p
      (le_of_lt hp0) (le_of_lt hp1) hB M
    have hsat : riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M
        (snipeClippedBdd B β p) ≤ 16 * B ^ 2 := by
      unfold riskAtBdd FiniteDesign.mse FiniteDesign.E
      calc
        _ ≤ ∑ z, (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
            (fun _ => le_of_lt hp1)).p z * (16 * B ^ 2) := by
          apply Finset.sum_le_sum
          intro z hz
          apply mul_le_mul_of_nonneg_left _ <|
            (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
              (fun _ => le_of_lt hp1)).p_nonneg z
          have hc : |snipeClippedBdd B β p (edgeFnBdd M) z
              (obsOutcome M.edge M.coef z)| ≤ 2 * B := by
            unfold snipeClippedBdd clipTo
            rw [abs_le]
            simp [hB]
          have ht := tte_abs_le_of_bddModelClass M
          have he := (abs_sub _ _).trans (add_le_add hc ht)
          have he2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 he
          rw [sq_abs] at he2
          nlinarith
        _ = 16 * B ^ 2 := by
          rw [← Finset.sum_mul,
            (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
              (fun _ => le_of_lt hp1)).p_sum, one_mul]
    let x : ℝ := (d : ℝ) * blockEnergy β p d / Fintype.card V
    have hx0 : 0 ≤ x := by
      dsimp [x]
      apply div_nonneg
      · apply mul_nonneg (by positivity)
        unfold blockEnergy
        apply Finset.sum_nonneg
        intro r hr
        apply div_nonneg
        · exact mul_nonneg (by positivity) (sq_nonneg _)
        · exact pow_nonneg
            (mul_nonneg (le_of_lt hp0) (sub_nonneg.mpr (le_of_lt hp1))) _
      · positivity
    by_cases hx : x ≤ 1
    · rw [min_eq_right hx]
      exact hraw.trans <| (riskAtBdd_snipe_le p hp0 hp1 M).trans
        (by
          have hnonneg : 0 ≤ B ^ 2 * x :=
            mul_nonneg (sq_nonneg B) hx0
          dsimp [x] at hnonneg ⊢
          ring_nf at hnonneg ⊢
          nlinarith)
    · rw [min_eq_left (le_of_not_ge hx)]
      simpa using hsat

/-- Establishes the stated mathematical result for snipe clipped bdd admissible. -/
lemma snipeClippedBdd_admissible
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d β : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    AdmissibleEstimatorBdd (V := V) p (le_of_lt hp0) (le_of_lt hp1)
      d β B (snipeClippedBdd B β p) := by
  constructor
  · intro G z
    unfold snipeClippedBdd clipTo snipeEstimator
    fun_prop
  · refine ⟨16 * B ^ 2, ?_⟩
    rintro _ ⟨M, rfl⟩
    exact le_trans
      (show riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M
          (snipeClippedBdd B β p) ≤ 16 * B ^ 2 by
        unfold riskAtBdd FiniteDesign.mse FiniteDesign.E
        calc
          _ ≤ ∑ z, (bernoulliDesign (fun _ : V => p)
              (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).p z *
              (16 * B ^ 2) := by
            apply Finset.sum_le_sum
            intro z hz
            apply mul_le_mul_of_nonneg_left _ <|
              (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
                (fun _ => le_of_lt hp1)).p_nonneg z
            have hc : |snipeClippedBdd B β p (edgeFnBdd M) z
                (obsOutcome M.edge M.coef z)| ≤ 2 * B := by
              unfold snipeClippedBdd clipTo
              rw [abs_le]
              simp [hB]
            have ht := tte_abs_le_of_bddModelClass M
            have he := (abs_sub _ _).trans (add_le_add hc ht)
            have he2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 he
            rw [sq_abs] at he2
            nlinarith
          _ = 16 * B ^ 2 := by
            rw [← Finset.sum_mul,
              (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
                (fun _ => le_of_lt hp1)).p_sum, one_mul])
      le_rfl

/-- Establishes the stated mathematical result for minimax risk bdd le clipped. -/
lemma minimaxRiskBdd_le_clipped
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d β : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    minimaxRiskBddOutcome (V := V) p (le_of_lt hp0) (le_of_lt hp1) d β B ≤
      worstRiskBdd (V := V) p (le_of_lt hp0) (le_of_lt hp1) d β B
        (snipeClippedBdd B β p) := by
  unfold minimaxRiskBddOutcome
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨est, hest, rfl⟩
    let M0 : BddOutcomeModelClass V d β B :=
      { edge := fun _ _ => False
        decEdge := fun _ _ => inferInstance
        coef := fun _ _ => 0
        supported := by simp
        degree_le := by simp [BoundedDegree, nbhd, outNbhd]
        low_order := by simp [LowOrder]
        outcome_bound := by
          intro i z
          simpa [potentialOutcome, nbhd] using hB }
    have hr0 : 0 ≤ riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) M0 est := by
      unfold riskAtBdd
      exact (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).mse_nonneg _ _
    exact hr0.trans (le_csSup hest.2 (Set.mem_range_self M0))
  · exact ⟨snipeClippedBdd B β p,
      snipeClippedBdd_admissible p hp0 hp1 d β B hB, rfl⟩

/-- Defines model class to bdd. -/
noncomputable def modelClassToBdd
    {V : Type*} [Fintype V] [DecidableEq V]
    {d β : ℕ} {B : ℝ} (M : ModelClass V d β B) :
    BddOutcomeModelClass V d β B :=
  { edge := M.edge
    decEdge := M.decEdge
    coef := M.coef
    supported := M.supported
    degree_le := M.degree_le
    low_order := M.low_order
    outcome_bound := fun i z => potentialOutcome_abs_le_mass M.mass_le i z }

/-- Establishes the stated mathematical result for risk at model class to bdd. -/
lemma riskAt_modelClassToBdd
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {d β : ℕ} {B : ℝ} (M : ModelClass V d β B)
    (est : Estimator V) :
    riskAtBdd p hp0 hp1 (modelClassToBdd M) est =
      riskAt p hp0 hp1 M est := by
  rfl

/-- Establishes the stated mathematical result for minimax risk l1 le minimax risk bdd. -/
lemma minimaxRiskL1_le_minimaxRiskBdd
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d β : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    minimaxRiskL1 (V := V) p (le_of_lt hp0) (le_of_lt hp1) d β B ≤
      minimaxRiskBddOutcome (V := V) p (le_of_lt hp0) (le_of_lt hp1)
        d β B := by
  unfold minimaxRiskL1 minimaxRisk minimaxRiskBddOutcome
  apply le_csInf
  · exact ⟨worstRiskBdd p (le_of_lt hp0) (le_of_lt hp1) d β B
      (snipeClippedBdd B β p),
      ⟨snipeClippedBdd B β p,
        snipeClippedBdd_admissible p hp0 hp1 d β B hB, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨est, hest, rfl⟩
    have hbounded : BddAbove (Set.range fun M : ModelClass V d β B =>
        riskAt p (le_of_lt hp0) (le_of_lt hp1) M est) := by
      obtain ⟨C, hC⟩ := hest.2
      refine ⟨C, ?_⟩
      rintro _ ⟨M, rfl⟩
      change riskAt p (le_of_lt hp0) (le_of_lt hp1) M est ≤ C
      rw [← riskAt_modelClassToBdd p (le_of_lt hp0) (le_of_lt hp1) M est]
      exact hC ⟨modelClassToBdd M, rfl⟩
    have had : AdmissibleEstimator p (le_of_lt hp0) (le_of_lt hp1)
        d β B est := ⟨hest.1, hbounded⟩
    apply (csInf_le
      (show BddBelow {r : ℝ | ∃ e : Estimator V,
          AdmissibleEstimator p (le_of_lt hp0) (le_of_lt hp1) d β B e ∧
            r = worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B e} from
        ⟨0, by
          rintro _ ⟨e, he, rfl⟩
          let M0 : ModelClass V d β B :=
            { edge := fun _ _ => False
              decEdge := fun _ _ => inferInstance
              coef := fun _ _ => 0
              supported := by simp
              degree_le := by simp [BoundedDegree, nbhd, outNbhd]
              low_order := by simp [LowOrder]
              mass_le := by intro i; simpa using hB }
          have hr0 : 0 ≤ riskAt p (le_of_lt hp0) (le_of_lt hp1) M0 e := by
            unfold riskAt
            exact (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
              (fun _ => le_of_lt hp1)).mse_nonneg _ _
          exact hr0.trans (le_csSup he.2 (Set.mem_range_self M0))⟩)
      (show ∃ e : Estimator V,
          AdmissibleEstimator p (le_of_lt hp0) (le_of_lt hp1) d β B e ∧
            worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B est =
              worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B e from
        ⟨est, had, rfl⟩)).trans
    unfold worstRisk worstRiskBdd
    apply csSup_le
    · let M0 : ModelClass V d β B :=
        { edge := fun _ _ => False
          decEdge := fun _ _ => inferInstance
          coef := fun _ _ => 0
          supported := by simp
          degree_le := by simp [BoundedDegree, nbhd, outNbhd]
          low_order := by simp [LowOrder]
          mass_le := by intro i; simpa using hB }
      exact ⟨riskAt p (le_of_lt hp0) (le_of_lt hp1) M0 est, ⟨M0, rfl⟩⟩
    · rintro _ ⟨M, rfl⟩
      change riskAt p (le_of_lt hp0) (le_of_lt hp1) M est ≤
        sSup (Set.range fun N : BddOutcomeModelClass V d β B =>
          riskAtBdd p (le_of_lt hp0) (le_of_lt hp1) N est)
      rw [← riskAt_modelClassToBdd p (le_of_lt hp0) (le_of_lt hp1) M est]
      exact le_csSup hest.2 (Set.mem_range_self (modelClassToBdd M))

end CausalSmith.Experimentation.SnipeDegreeFrontier
