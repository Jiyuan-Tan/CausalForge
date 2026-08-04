import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenter
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.OverlapCount
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance
import Mathlib.Algebra.Order.Chebyshev

/-!
# SNIPE score moments, local energy, and unbiasedness

Computes the raw and centred moments of the SNIPE score under the Bernoulli
design, shows the score has mean zero, defines the local score energy and
compares it with the block energy, and proves the estimator is unbiased in both
the coefficient-mass and bounded-outcome model classes.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The Boolean graph encoding has exactly the original relation's neighborhood. -/
lemma nbhdB_edgeFn_eq_nbhd (M : ModelClass V d β B) (i : V) :
    nbhdB (edgeFn M) i = nbhd M.edge i := by
  ext j
  simp [nbhdB, edgeFn, nbhd]

/-- The bounded-outcome graph encoding has exactly the original relation's neighborhood. -/
lemma nbhdB_edgeFnBdd_eq_nbhd (M : BddOutcomeModelClass V d β B) (i : V) :
    nbhdB (edgeFnBdd M) i = nbhd M.edge i := by
  ext j
  simp [nbhdB, edgeFnBdd, nbhd]

/-- Coordinatewise products factor under a common-probability Bernoulli design. -/
lemma E_global_coordinate_prod
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : V → Bool → ℝ) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0) (fun _ => hp1)).E
        (fun z => ∏ i, g i (z i)) =
      ∏ i, (p * g i true + (1 - p) * g i false) := by
  unfold bernoulliDesign
  rw [FiniteDesign.E_prod_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [coinDesign_E]

/-- A global SNIPE score has the required raw-monomial moment on its
neighborhood. -/
lemma snipeScore_raw_moment
    (G : V → V → Bool) (β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (i : V) (T : Finset V) (hT : T.Nonempty)
    (hTN : T ⊆ nbhdB G i)
    (hTcard : T.card ≤ effBeta β (nbhdB G i).card) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
      (fun z => snipeScore G β p i z *
        ∏ j ∈ T, if z j then (1 : ℝ) else 0) = 1 := by
  let v := p * (1 - p)
  have hv : v ≠ 0 :=
    mul_ne_zero (ne_of_gt hp0) (ne_of_gt (sub_pos.mpr hp1))
  have hmoment (S : Finset V) (hS : S.Nonempty) :
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E
        (fun z => (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) =
        if S ⊆ T then v ^ S.card * p ^ (T.card - S.card) else 0 := by
    -- This is the coordinate-free form of the product calculation in
    -- `E_centeredMonomial_mul_raw`.
    let x : Bool → ℝ := fun b => (if b then 1 else 0) - p
    let y : Bool → ℝ := fun b => if b then 1 else 0
    rw [show (fun z : V → Bool =>
        (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) =
        (fun z => ∏ j, ((if j ∈ S then x (z j) else 1) *
          (if j ∈ T then y (z j) else 1))) by
      funext z
      rw [Finset.prod_mul_distrib]
      simp [x, y]]
    rw [E_global_coordinate_prod (V := V) p (le_of_lt hp0) (le_of_lt hp1)
      (fun j b => (if j ∈ S then x b else 1) *
        (if j ∈ T then y b else 1))]
    by_cases hsub : S ⊆ T
    · rw [if_pos hsub]
      have hfactor (j : V) :
          p * ((if j ∈ S then x true else 1) *
              (if j ∈ T then y true else 1)) +
            (1 - p) * ((if j ∈ S then x false else 1) *
              (if j ∈ T then y false else 1)) =
            if j ∈ S then p * (1 - p) else if j ∈ T then p else 1 := by
        by_cases hjS : j ∈ S
        · have hjT : j ∈ T := hsub hjS
          simp [hjS, hjT, x, y]
        · by_cases hjT : j ∈ T <;> simp [hjS, hjT, x, y] <;> ring
      simp_rw [hfactor]
      have hsplit (j : V) :
          (if j ∈ S then p * (1 - p) else if j ∈ T then p else 1) =
            (if j ∈ S then p * (1 - p) else 1) *
              (if j ∈ T \ S then p else 1) := by
        by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;>
          simp [hjS, hjT]
      simp_rw [hsplit, Finset.prod_mul_distrib]
      rw [Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
      simp only [Finset.prod_const, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.cast_id, mul_one]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    · rw [if_neg hsub]
      obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∉ T := by
        simpa only [Finset.not_subset] using hsub
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hjS, hjT, x, y]
      ring
  simp only [snipeScore, Finset.sum_mul, Finset.mul_sum, FiniteDesign.E_sum]
  simp_rw [mul_assoc, FiniteDesign.E_const_mul]
  rw [show
    (∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
      ∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
        bernoulliContrast p r / (p * (1 - p)) ^ r *
          (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
            (fun _ => le_of_lt hp1)).E
            (fun z => (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) *
              ∏ j ∈ T, if z j then (1 : ℝ) else 0)) =
      ∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
        ∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
          bernoulliContrast p r / v ^ r *
            (if S ⊆ T then v ^ S.card * p ^ (T.card - S.card) else 0) by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro S hS
    have hScard : S.card = r := (Finset.mem_filter.mp hS).2
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    rw [hmoment S (Finset.card_pos.mp (by omega))]
    ]
  rw [show
      (∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
        ∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
          bernoulliContrast p r / v ^ r *
            (if S ⊆ T then v ^ S.card * p ^ (T.card - S.card) else 0)) =
      ∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
        (Nat.choose T.card r : ℝ) * bernoulliContrast p r *
          p ^ (T.card - r) by
    apply Finset.sum_congr rfl
    intro r hr
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    rw [show
      ((nbhdB G i).powerset.filter (fun S => S.card = r)).filter
          (fun S => S ⊆ T) = T.powersetCard r by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨_, hc⟩, hST⟩
        exact ⟨hST, hc⟩
      · rintro ⟨hST, hc⟩
        exact ⟨⟨hST.trans hTN, hc⟩, hST⟩]
    rw [show
      (∑ S ∈ T.powersetCard r,
        bernoulliContrast p r / v ^ r *
          (v ^ S.card * p ^ (T.card - S.card))) =
        ∑ _S ∈ T.powersetCard r,
          bernoulliContrast p r * p ^ (T.card - r) by
      apply Finset.sum_congr rfl
      intro S hS
      have hs := Finset.mem_powersetCard.mp hS
      simp only [hs.2]
      field_simp]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp
    ring]
  rw [show
    (∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
      (Nat.choose T.card r : ℝ) * bernoulliContrast p r *
        p ^ (T.card - r)) =
      ∑ r ∈ Finset.Icc 1 T.card,
        (Nat.choose T.card r : ℝ) * bernoulliContrast p r *
          p ^ (T.card - r) by
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      exact ⟨hr.1, le_trans hr.2 hTcard⟩
    · intro r hr
      have hlt : T.card < r := by
        simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and_or] at hr
        omega
      simp [Nat.choose_eq_zero_of_lt hlt]
    · intro r hr
      rfl]
  exact
    CausalSmith.Experimentation.SnipeDegreeFrontier.blockContrast_binomial
      p T.card (Finset.card_pos.mpr hT)

/-- A global SNIPE score is centered. -/
lemma snipeScore_mean_zero
    (G : V → V → Bool) (β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (i : V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E (snipeScore G β p i) = 0 := by
  have hcenter (S : Finset V) (hS : S.Nonempty) :
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E
        (fun z => ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) = 0 := by
    rw [show (fun z : V → Bool =>
        ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) =
      (fun z => ∏ j, if j ∈ S then ((if z j then (1 : ℝ) else 0) - p)
        else 1) by
      funext z
      simp]
    rw [E_global_coordinate_prod (V := V) p (le_of_lt hp0) (le_of_lt hp1)
      (fun j b => if j ∈ S then ((if b then (1 : ℝ) else 0) - p) else 1)]
    obtain ⟨j, hj⟩ := hS
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]
    ring
  rw [show snipeScore G β p i = fun z =>
      ∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
        (bernoulliContrast p r / (p * (1 - p)) ^ r) *
          ∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
            ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p) by rfl]
  rw [FiniteDesign.E_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [FiniteDesign.E_const_mul, FiniteDesign.E_sum]
  rw [show
    (∑ S ∈ (nbhdB G i).powerset.filter (fun S => S.card = r),
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
        (fun z => ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p))) = 0 by
    apply Finset.sum_eq_zero
    intro S hS
    have hc : S.card = r := (Finset.mem_filter.mp hS).2
    exact hcenter S (Finset.card_pos.mp (by
      have := (Finset.mem_Icc.mp hr).1
      omega))]
  ring

/-- Pairing a SNIPE score with one unit's low-order polynomial gives that
unit's all-treated versus all-control contrast. -/
lemma snipeScore_potentialOutcome_moment
    (G : V → V → Prop) [DecidableRel G]
    (c : V → Finset V → ℝ) (β : ℕ)
    (hlow : LowOrder c β)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (i : V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
      (fun z => snipeScore (fun j i => decide (G j i)) β p i z *
        potentialOutcome G c i z) =
      potentialOutcome G c i (fun _ => true) -
        potentialOutcome G c i (fun _ => false) := by
  let GB : V → V → Bool := fun j i => decide (G j i)
  have hN : nbhdB GB i = nbhd G i := by
    ext j
    simp [GB, nbhdB, nbhd]
  unfold potentialOutcome
  rw [show (fun z =>
      snipeScore GB β p i z *
        ∑ S ∈ (nbhd G i).powerset,
          c i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0) =
      (fun z => ∑ S ∈ (nbhd G i).powerset,
        snipeScore GB β p i z *
          (c i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0)) by
    funext z
    rw [Finset.mul_sum]]
  rw [FiniteDesign.E_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [show (fun z =>
      snipeScore GB β p i z *
        (c i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0)) =
      (fun z => c i S * (snipeScore GB β p i z *
        ∏ j ∈ S, if z j then (1 : ℝ) else 0)) by
    funext z
    ring]
  rw [FiniteDesign.E_const_mul]
  by_cases hSne : S.Nonempty
  · have hSN : S ⊆ nbhdB GB i := by
      rw [hN]
      exact Finset.mem_powerset.mp hS
    by_cases hcard : S.card ≤ effBeta β (nbhdB GB i).card
    · rw [snipeScore_raw_moment GB β p hp0 hp1 i S hSne hSN hcard]
      simp [Finset.card_ne_zero.mpr hSne]
    · have hβcard : β < S.card := by
        have hSlen : S.card ≤ (nbhdB GB i).card := by
          rw [hN]
          exact Finset.card_le_card (Finset.mem_powerset.mp hS)
        simp only [effBeta] at hcard
        omega
      rw [hlow i S hβcard]
      simp
  · have hSempty := Finset.not_nonempty_iff_eq_empty.mp hSne
    subst S
    simp only [Finset.prod_empty]
    rw [show
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
          (fun z => snipeScore GB β p i z * 1) = 0 by
      simpa using snipeScore_mean_zero GB β p hp0 hp1 i]
    simp

/-- Exact score energy for an outcome unit. -/
noncomputable def localEnergy
    (G : V → V → Prop) (β : ℕ) (p : ℝ) (i : V) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (effBeta β (nbhd G i).card),
    (Nat.choose (nbhd G i).card r : ℝ) *
      (bernoulliContrast p r) ^ 2 / (p * (1 - p)) ^ r
-- @realizes A_i(exact score energy at unit i)

/-- SNIPE is design-unbiased at every coefficient-mass model. -/
lemma snipe_unbiased
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (M : ModelClass V d β B) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).Unbiased
      (fun z => snipeEstimator β p (edgeFn M) z (obsOutcome M.edge M.coef z))
      (tte M.edge M.coef) := by
  letI : DecidableRel M.edge := M.decEdge
  unfold FiniteDesign.Unbiased snipeEstimator tte
  rw [FiniteDesign.E_const_mul, FiniteDesign.E_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).E
        (fun z => potentialOutcome M.edge M.coef i z *
          snipeScore (edgeFn M) β p i z) =
      potentialOutcome M.edge M.coef i (fun _ => true) -
        potentialOutcome M.edge M.coef i (fun _ => false)
  rw [show (fun z => potentialOutcome M.edge M.coef i z *
      snipeScore (edgeFn M) β p i z) =
      (fun z => snipeScore (edgeFn M) β p i z *
        potentialOutcome M.edge M.coef i z) by
    funext z
    ring]
  exact snipeScore_potentialOutcome_moment M.edge M.coef β M.low_order
    p hp0 hp1 i

/-- The same unbiasedness assertion on the uniformly bounded-outcome class. -/
lemma snipe_unbiased_bdd
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (M : BddOutcomeModelClass V d β B) :
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).Unbiased
      (fun z => snipeEstimator β p (edgeFnBdd M) z (obsOutcome M.edge M.coef z))
      (tte M.edge M.coef) := by
  letI : DecidableRel M.edge := M.decEdge
  unfold FiniteDesign.Unbiased snipeEstimator tte
  rw [FiniteDesign.E_const_mul, FiniteDesign.E_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change
    (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).E
        (fun z => potentialOutcome M.edge M.coef i z *
          snipeScore (edgeFnBdd M) β p i z) =
      potentialOutcome M.edge M.coef i (fun _ => true) -
        potentialOutcome M.edge M.coef i (fun _ => false)
  rw [show (fun z => potentialOutcome M.edge M.coef i z *
      snipeScore (edgeFnBdd M) β p i z) =
      (fun z => snipeScore (edgeFnBdd M) β p i z *
        potentialOutcome M.edge M.coef i z) by
    funext z
    ring]
  exact snipeScore_potentialOutcome_moment M.edge M.coef β M.low_order
    p hp0 hp1 i

/-- Actual local score energy is at most complete-block energy at the degree
bound. -/
lemma localEnergy_le_blockEnergy
    (G : V → V → Prop) (d β : ℕ) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hdegree : BoundedDegree G d) (i : V) :
    localEnergy G β p i ≤ blockEnergy β p d := by
  have hcard : (nbhd G i).card ≤ d := hdegree.1 i
  have heff : effBeta β (nbhd G i).card ≤ effBeta β d := by
    simp only [effBeta]
    omega
  have hq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  unfold localEnergy blockEnergy
  calc
    (∑ r ∈ Finset.Icc 1 (effBeta β (nbhd G i).card),
        (Nat.choose (nbhd G i).card r : ℝ) *
          bernoulliContrast p r ^ 2 / (p * (1 - p)) ^ r) ≤
      ∑ r ∈ Finset.Icc 1 (effBeta β (nbhd G i).card),
        (Nat.choose d r : ℝ) *
          bernoulliContrast p r ^ 2 / (p * (1 - p)) ^ r := by
      apply Finset.sum_le_sum
      intro r hr
      have hchoose : Nat.choose (nbhd G i).card r ≤ Nat.choose d r :=
        Nat.choose_le_choose r hcard
      gcongr
    _ ≤ ∑ r ∈ Finset.Icc 1 (effBeta β d),
        (Nat.choose d r : ℝ) *
          bernoulliContrast p r ^ 2 / (p * (1 - p)) ^ r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        simp only [Finset.mem_Icc] at hr ⊢
        exact ⟨hr.1, le_trans hr.2 heff⟩
      · intro r _ _
        positivity

/-- The independent Bernoulli design is unchanged when its unit-level assignment-probability
function is replaced by an equal function and the associated bounds are transported accordingly. -/
add_decl_doc bernoulliDesign.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
