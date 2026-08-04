import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BernoulliFourier
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance

/-!
# Block representer identities

This file states the Bernoulli Riesz identities, the two unique minimizer
claims, the binomial comparison, and the uniform raw-coefficient bound.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

/-- Weight feasibility phrased directly against an arbitrary finite design. -/
def WeightFeasibleAt {d : ℕ}
    (D : FiniteDesign (Fin d → Bool)) (β : ℕ)
    (w : (Fin d → Bool) → ℝ) : Prop :=
  D.E w = 0 ∧
    ∀ S : Finset (Fin d), S.Nonempty → S.card ≤ effBeta β d →
      D.E (fun z => w z * rawMonomial S z) = 1

/-- The finite binomial identity underlying the representer moment. -/
lemma blockContrast_binomial (p : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ∑ r ∈ Finset.Icc 1 t,
        (Nat.choose t r : ℝ) * bernoulliContrast p r * p ^ (t - r) = 1 := by
  have hfull :
      (∑ r ∈ Finset.range (t + 1),
          (Nat.choose t r : ℝ) * bernoulliContrast p r * p ^ (t - r)) = 1 := by
    simp only [bernoulliContrast]
    rw [show
      (fun r => (Nat.choose t r : ℝ) * ((1 - p) ^ r - (-p) ^ r) * p ^ (t - r)) =
        (fun r => (Nat.choose t r : ℝ) * (1 - p) ^ r * p ^ (t - r) -
          (Nat.choose t r : ℝ) * (-p) ^ r * p ^ (t - r)) by
      funext r
      ring]
    rw [Finset.sum_sub_distrib]
    have h1 :
        (∑ r ∈ Finset.range (t + 1),
            (Nat.choose t r : ℝ) * (1 - p) ^ r * p ^ (t - r)) = 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (add_pow (1 - p) p t).symm
    have h2 :
        (∑ r ∈ Finset.range (t + 1),
            (Nat.choose t r : ℝ) * (-p) ^ r * p ^ (t - r)) = 0 := by
      have ht0 : t ≠ 0 := by omega
      simpa [mul_comm, mul_left_comm, mul_assoc, ht0] using
        (add_pow (-p) p t).symm
    rw [h1, h2]
    norm_num
  rw [← hfull]
  apply Finset.sum_subset
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    simp [hr.2]
  · intro r hrange hnot
    have hr0 : r = 0 := by
      simp only [Finset.mem_range] at hrange
      simp only [Finset.mem_Icc, not_and_or] at hnot
      omega
    subst r
    simp [bernoulliContrast]

/-- The score pairs to one with every eligible nonconstant raw monomial. -/
lemma blockScore_raw_moment
    (β d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (T : Finset (Fin d)) (hT : T.Nonempty)
    (hTcard : T.card ≤ effBeta β d) :
    (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
        (fun z => blockScore β p d z * rawMonomial T z) = 1 := by
  let v := p * (1 - p)
  have hv : v ≠ 0 :=
    mul_ne_zero (ne_of_gt hp0) (ne_of_gt (sub_pos.mpr hp1))
  have hmoment (S : Finset (Fin d)) (hS : S.Nonempty) :
      (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
          (fun z => (∏ j ∈ S, (blockInd z j - p)) * rawMonomial T z) =
        if S ⊆ T then v ^ S.card * p ^ (T.card - S.card) else 0 := by
    exact E_centeredMonomial_mul_raw d p (le_of_lt hp0) (le_of_lt hp1) S T hS
  simp only [blockScore, Finset.sum_mul, Finset.mul_sum, FiniteDesign.E_sum]
  simp_rw [mul_assoc, FiniteDesign.E_const_mul]
  rw [show
    (∑ r ∈ Finset.Icc 1 (effBeta β d),
      ∑ S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin d) => S.card = r),
        bernoulliContrast p r / v ^ r *
          (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
            (fun z => (∏ j ∈ S, (blockInd z j - p)) * rawMonomial T z)) =
      ∑ r ∈ Finset.Icc 1 (effBeta β d),
        ∑ S ∈ Finset.univ.powerset.filter
            (fun S : Finset (Fin d) => S.card = r),
          bernoulliContrast p r / v ^ r *
            (if S ⊆ T then v ^ S.card * p ^ (T.card - S.card) else 0) by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro S hS
    have hc : S.card = r := (Finset.mem_filter.mp hS).2
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    rw [hmoment S (Finset.card_pos.mp (by omega))]]
  rw [show
    (∑ r ∈ Finset.Icc 1 (effBeta β d),
      ∑ S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin d) => S.card = r),
        bernoulliContrast p r / v ^ r *
          (if S ⊆ T then v ^ S.card * p ^ (T.card - S.card) else 0)) =
      ∑ r ∈ Finset.Icc 1 (effBeta β d),
        (Nat.choose T.card r : ℝ) * bernoulliContrast p r *
          p ^ (T.card - r) by
    apply Finset.sum_congr rfl
    intro r hr
    rw [show
      Finset.univ.powerset.filter (fun S : Finset (Fin d) => S.card = r) =
        Finset.univ.powersetCard r by
      ext S
      simp [Finset.mem_powersetCard, eq_comm]]
    rw [show
      (∑ S ∈ Finset.univ.powersetCard r,
        bernoulliContrast p r / v ^ r *
          (if S ⊆ T then v ^ S.card * p ^ (T.card - S.card) else 0)) =
        ∑ S ∈ Finset.univ.powersetCard r,
          if S ⊆ T then bernoulliContrast p r * p ^ (T.card - r) else 0 by
      apply Finset.sum_congr rfl
      intro S hS
      have hScard : S.card = r := (Finset.mem_powersetCard.mp hS).2
      rw [hScard]
      by_cases hs : S ⊆ T
      · simp only [if_pos hs]
        field_simp
      · simp [hs]]
    rw [← Finset.sum_filter]
    rw [show
      (Finset.univ.powersetCard r).filter (fun S => S ⊆ T) =
        T.powersetCard r by
      ext S
      simp [Finset.mem_powersetCard, and_comm]]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp [mul_assoc]]
  rw [show
    (∑ r ∈ Finset.Icc 1 (effBeta β d),
      (Nat.choose T.card r : ℝ) * bernoulliContrast p r * p ^ (T.card - r)) =
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
  exact blockContrast_binomial p T.card (Finset.card_pos.mpr hT)

/-- The block score is centered under its product Bernoulli design. -/
lemma blockScore_mean_zero
    (β d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
        (blockScore β p d) = 0 := by
  have hmoment (S : Finset (Fin d)) (hS : S.Nonempty) :
      (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
          (fun z => ∏ j ∈ S, (blockInd z j - p)) = 0 := by
    have h := E_centeredMonomial_mul_raw d p
      (le_of_lt hp0) (le_of_lt hp1) S ∅ hS
    simpa [centeredMonomial, rawMonomial, hS.ne_empty] using h
  change
    (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
      (fun z => blockScore β p d z) = 0
  simp only [blockScore]
  rw [FiniteDesign.E_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [FiniteDesign.E_const_mul]
  rw [FiniteDesign.E_sum]
  rw [show
    (∑ S ∈ Finset.univ.powerset.filter
        (fun S : Finset (Fin d) => S.card = r),
      (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
        (fun z => ∏ j ∈ S, (blockInd z j - p))) = 0 by
    apply Finset.sum_eq_zero
    intro S hS
    have hScard : S.card = r := (Finset.mem_filter.mp hS).2
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    rw [hmoment S (Finset.card_pos.mp (by omega))]]
  ring

/-- The canonical block score satisfies all unbiased-weight moment
restrictions. -/
lemma blockScore_weightFeasibleAt
    (β d : ℕ) (p : ℝ) (D : FiniteDesign (Fin d → Bool))
    (hD : IsProductBernoulli D p) :
    WeightFeasibleAt D β (blockScore β p d) := by
  have hDeq :
      D = blockDesign d p (le_of_lt hD.1) (le_of_lt hD.2.1) := by
    rcases hD with ⟨hp, hp', hp0, hp1, rfl⟩
    unfold blockDesign
    congr
  constructor
  · rw [hDeq]
    exact blockScore_mean_zero β d p hD.1 hD.2.1
  · intro S hS hScard
    rw [hDeq]
    exact blockScore_raw_moment β d p hD.1 hD.2.1 S hS hScard

/-- The block score represents the all-one versus all-zero contrast on the
low-order polynomial space. -/
lemma blockScore_represents
    (β d : ℕ) (p : ℝ) (D : FiniteDesign (Fin d → Bool))
    (hD : IsProductBernoulli D p) (f : (Fin d → Bool) → ℝ)
    (hf : f ∈ polySpace β d) :
    D.E (fun z => blockScore β p d z * f z) = contrastFunctional f := by
  have hDeq :
      D = blockDesign d p (le_of_lt hD.1) (le_of_lt hD.2.1) := by
    rcases hD with ⟨hp, hp', hp0, hp1, rfl⟩
    unfold blockDesign
    congr
  rw [hDeq]
  rw [polySpace] at hf
  refine Submodule.span_induction (p := fun f _ =>
    (blockDesign d p (le_of_lt hD.1) (le_of_lt hD.2.1)).E
        (fun z => blockScore β p d z * f z) = contrastFunctional f)
      ?_ ?_ ?_ ?_ hf
  · intro f hf
    rcases hf with ⟨S, hScard, rfl⟩
    by_cases hS : S.Nonempty
    · rw [blockScore_raw_moment β d p hD.1 hD.2.1 S hS hScard]
      have hfalse :
          (∏ j ∈ S, blockInd (fun _ : Fin d => false) j) = 0 := by
        obtain ⟨j, hj⟩ := hS
        apply Finset.prod_eq_zero hj
        simp [blockInd]
      unfold contrastFunctional rawMonomial
      rw [hfalse]
      simp [blockInd]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simpa [rawMonomial, contrastFunctional] using
        blockScore_mean_zero β d p hD.1 hD.2.1
  · simp [contrastFunctional]
  · intro f g _ _ hf hg
    rw [show (fun z => blockScore β p d z * (f + g) z) =
      (fun z => blockScore β p d z * f z +
        blockScore β p d z * g z) by
      funext z
      simp [mul_add]]
    rw [FiniteDesign.E_add, hf, hg]
    simp [contrastFunctional]
    ring
  · intro a f _ hf
    rw [show (fun z => blockScore β p d z * (a • f) z) =
      (fun z => a * (blockScore β p d z * f z)) by
      funext z
      change blockScore β p d z * (a * f z) =
        a * (blockScore β p d z * f z)
      ring]
    rw [FiniteDesign.E_const_mul, hf]
    simp [contrastFunctional, mul_sub]

/-- The block score's second moment is exactly `A_d`. -/
lemma blockScore_sq_expectation
    (β d : ℕ) (p : ℝ) (D : FiniteDesign (Fin d → Bool))
    (hD : IsProductBernoulli D p) :
    D.E (fun z => blockScore β p d z ^ 2) = blockEnergy β p d := by
  have hDeq :
      D = blockDesign d p (le_of_lt hD.1) (le_of_lt hD.2.1) := by
    rcases hD with ⟨hp, hp', hp0, hp1, rfl⟩
    unfold blockDesign
    congr
  rw [hDeq]
  let hp0 : 0 ≤ p := le_of_lt hD.1
  let hp1 : p ≤ 1 := le_of_lt hD.2.1
  simp only [blockScore, pow_two, Finset.sum_mul, Finset.mul_sum,
    FiniteDesign.E_sum]
  have hmoment (r q : ℕ) (S T : Finset (Fin d)) :
      (blockDesign d p hp0 hp1).E
          (fun z =>
            (bernoulliContrast p q / (p * (1 - p)) ^ q *
                ∏ j ∈ T, (blockInd z j - p)) *
              (bernoulliContrast p r / (p * (1 - p)) ^ r *
                ∏ j ∈ S, (blockInd z j - p))) =
        (bernoulliContrast p q / (p * (1 - p)) ^ q) *
          (bernoulliContrast p r / (p * (1 - p)) ^ r) *
            (if T = S then (p * (1 - p)) ^ T.card else 0) := by
    rw [show (fun z =>
            (bernoulliContrast p q / (p * (1 - p)) ^ q *
                ∏ j ∈ T, (blockInd z j - p)) *
              (bernoulliContrast p r / (p * (1 - p)) ^ r *
                ∏ j ∈ S, (blockInd z j - p))) =
          (fun z =>
            ((bernoulliContrast p q / (p * (1 - p)) ^ q) *
              (bernoulliContrast p r / (p * (1 - p)) ^ r)) *
              (centeredMonomial p T z * centeredMonomial p S z)) by
        funext z
        simp only [centeredMonomial]
        ring]
    rw [FiniteDesign.E_const_mul]
    rw [E_centeredMonomial_mul]
  simp_rw [hmoment]
  simp [blockEnergy]
  apply Finset.sum_congr rfl
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hrle : r ≤ effBeta β d := (Finset.mem_Icc.mp hr).2
  rw [show (∑ S ∈ Finset.univ.powersetCard r,
      if S.Nonempty ∧ S.card ≤ effBeta β d then
        bernoulliContrast p S.card / (p * (1 - p)) ^ S.card *
            (bernoulliContrast p r / (p * (1 - p)) ^ r) *
              (p * (1 - p)) ^ S.card
      else 0) =
      ∑ _S ∈ Finset.univ.powersetCard r,
        bernoulliContrast p r / (p * (1 - p)) ^ r *
          (bernoulliContrast p r / (p * (1 - p)) ^ r) *
            (p * (1 - p)) ^ r by
      apply Finset.sum_congr rfl
      intro S hS
      have hScard : S.card = r :=
        (Finset.mem_powersetCard.mp hS).2
      have hSnonempty : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        subst S
        simp at hScard
        omega
      simp [hScard, hSnonempty, hrle]]
  rw [Finset.sum_const, Finset.card_powersetCard]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hv : p * (1 - p) ≠ 0 :=
    mul_ne_zero (ne_of_gt hD.1) (ne_of_gt (sub_pos.mpr hD.2.1))
  field_simp

/-- The canonical score gives the upper bound in the weight program. -/
lemma weightProg_le_blockEnergy
    (β d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    weightProg β d p (le_of_lt hp0) (le_of_lt hp1) ≤
      blockEnergy β p d := by
  let D := blockDesign d p (le_of_lt hp0) (le_of_lt hp1)
  have hD : IsProductBernoulli D p := by
    exact ⟨hp0, hp1, ⟨fun _ => le_of_lt hp0, fun _ => le_of_lt hp1, rfl⟩⟩
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro q ⟨w, _hw, rfl⟩
    exact D.E_nonneg (fun z => sq_nonneg (w z))
  · refine ⟨blockScore β p d, ?_, ?_⟩
    · exact blockScore_weightFeasibleAt β d p D hD
    · exact (blockScore_sq_expectation β d p D hD).symm

/-- The contrast of the unnormalized score is its squared energy. -/
lemma blockScore_contrast (β d : ℕ) (p : ℝ) :
    contrastFunctional (blockScore β p d) = blockEnergy β p d := by
  simp only [contrastFunctional, blockScore, blockInd, blockEnergy,
    Finset.sum_mul, Finset.sum_sub_distrib]
  have hsum_true (r : ℕ) :
      (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, (1 - p) ^ S.card) =
        (Nat.choose d r : ℝ) * (1 - p) ^ r := by
    rw [show (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        (1 - p) ^ S.card) =
        ∑ _S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, (1 - p) ^ r by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum_false (r : ℕ) :
      (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, (-p) ^ S.card) =
        (Nat.choose d r : ℝ) * (-p) ^ r := by
    rw [show (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        (-p) ^ S.card) =
        ∑ _S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, (-p) ^ r by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [if_true, Bool.false_eq_true, if_false, Finset.prod_const]
  rw [show (Finset.univ.powerset.filter
      (fun S : Finset (Fin d) => S.card = r)) =
      (Finset.univ : Finset (Fin d)).powersetCard r by
    ext S
    simp [Finset.mem_powersetCard, eq_comm]]
  simp only [zero_sub]
  rw [hsum_true r, hsum_false r]
  simp only [bernoulliContrast]
  ring

/-- The block energy is positive under the paper's nondegenerate parameters. -/
lemma blockEnergy_pos (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < blockEnergy β p d := by
  have heff : 1 ≤ effBeta β d := by
    simp [effBeta, hβ, hd]
  have hmem : 1 ∈ Finset.Icc 1 (effBeta β d) :=
    Finset.mem_Icc.mpr ⟨le_rfl, heff⟩
  have hq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hterm_nonneg (r : ℕ) :
      0 ≤ (Nat.choose d r : ℝ) * bernoulliContrast p r ^ 2 /
        (p * (1 - p)) ^ r := by positivity
  have hterm_pos :
      0 < (Nat.choose d 1 : ℝ) * bernoulliContrast p 1 ^ 2 /
        (p * (1 - p)) ^ 1 := by
    simp only [Nat.choose_one_right, bernoulliContrast, pow_one, neg_neg]
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
    convert div_pos hdpos hq using 1 <;> ring
  unfold blockEnergy
  exact lt_of_lt_of_le hterm_pos
    (Finset.single_le_sum (fun r hr => hterm_nonneg r) hmem)

/-- The normalized representer has unit contrast and reciprocal energy. -/
lemma blockRepresenter_contrast_energy
    (β d : ℕ) (p : ℝ) (D : FiniteDesign (Fin d → Bool))
    (hD : IsProductBernoulli D p) (hβ : 1 ≤ β) (hd : 1 ≤ d) :
    contrastFunctional (blockRepresenter β p d) = 1 ∧
      D.E (fun z => blockRepresenter β p d z ^ 2) =
        (blockEnergy β p d)⁻¹ := by
  have hApos := blockEnergy_pos β d p hβ hd hD.1 hD.2.1
  have hdz : d ≠ 0 := Nat.ne_of_gt hd
  constructor
  · unfold contrastFunctional
    simp only [blockRepresenter, if_neg hdz]
    rw [← sub_div]
    rw [show blockScore β p d (fun _ => true) -
        blockScore β p d (fun _ => false) = blockEnergy β p d from
      blockScore_contrast β d p]
    exact div_self hApos.ne'
  · rw [show (fun z => blockRepresenter β p d z ^ 2) =
        (fun z => (blockEnergy β p d)⁻¹ ^ 2 * blockScore β p d z ^ 2) by
      funext z
      simp only [blockRepresenter, if_neg hdz]
      field_simp [hApos.ne']]
    rw [FiniteDesign.E_const_mul, blockScore_sq_expectation β d p D hD]
    field_simp [hApos.ne']

/-- Expansion of a centered monomial in the raw-monomial basis. -/
lemma centeredMonomial_raw_expansion (d : ℕ) (p : ℝ)
    (S : Finset (Fin d)) (z : Fin d → Bool) :
    ∏ j ∈ S, (blockInd z j - p) =
      ∑ T ∈ S.powerset,
        (-p) ^ (S.card - T.card) * rawMonomial T z := by
  rw [show (∏ j ∈ S, (blockInd z j - p)) =
      ∏ j ∈ S, (blockInd z j + (-p)) by
    simp [sub_eq_add_neg]]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  have hsub : T ⊆ S := Finset.mem_powerset.mp hT
  rw [show (∏ i ∈ T, blockInd z i) = rawMonomial T z by rfl]
  rw [Finset.prod_const]
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  ring

/-- Exchange a sum over all subsets with a sum over their supersets. -/
lemma sum_powerset_subset_exchange
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset (Finset α)) (F : Finset α → Finset α → ℝ) :
    ∑ T ∈ (Finset.univ : Finset α).powerset,
        ∑ S ∈ A, (if T ⊆ S then F S T else 0) =
      ∑ S ∈ A, ∑ T ∈ S.powerset, F S T := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [← Finset.sum_filter]
  rw [show
      (Finset.univ : Finset α).powerset.filter (fun T => T ⊆ S) =
        S.powerset by
    ext T
    simp]

/-- The raw coefficients reconstruct the normalized representer. -/
lemma blockRepresenter_raw_expansion
    (β d : ℕ) (p : ℝ) (hd : 1 ≤ d) (z : Fin d → Bool) :
    blockRepresenter β p d z =
      ∑ T ∈ Finset.univ.powerset,
        blockRawCoef β p d T * rawMonomial T z := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  simp only [blockRepresenter, blockRawCoef, if_neg hd0, div_eq_inv_mul,
    blockScore]
  simp_rw [centeredMonomial_raw_expansion]
  let R := Finset.Icc 1 (effBeta β d)
  let A : ℕ → Finset (Finset (Fin d)) := fun r =>
    Finset.univ.powerset.filter (fun S : Finset (Fin d) => S.card = r)
  let c : ℕ → ℝ := fun r =>
    ((p * (1 - p)) ^ r)⁻¹ * bernoulliContrast p r
  let q : Finset (Fin d) → Finset (Fin d) → ℝ := fun S T =>
    (-p) ^ (S.card - T.card) * rawMonomial T z
  change
    (blockEnergy β p d)⁻¹ *
      ∑ r ∈ R, c r * ∑ S ∈ A r, ∑ T ∈ S.powerset, q S T =
    ∑ T ∈ Finset.univ.powerset,
      ((blockEnergy β p d)⁻¹ *
        ∑ r ∈ R, ∑ S ∈ A r,
          if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0) *
        rawMonomial T z
  calc
    _ = (blockEnergy β p d)⁻¹ *
        ∑ r ∈ R, ∑ S ∈ A r, ∑ T ∈ S.powerset, c r * q S T := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mul_sum]
    _ = (blockEnergy β p d)⁻¹ *
        ∑ r ∈ R, ∑ T ∈ Finset.univ.powerset,
          ∑ S ∈ A r, (if T ⊆ S then c r * q S T else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [sum_powerset_subset_exchange (A r) (fun S T => c r * q S T)]
    _ = (blockEnergy β p d)⁻¹ *
        ∑ T ∈ Finset.univ.powerset, ∑ r ∈ R,
          ∑ S ∈ A r, (if T ⊆ S then c r * q S T else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [show
        (∑ r ∈ R, ∑ S ∈ A r,
          if T ⊆ S then c r * q S T else 0) =
          (∑ r ∈ R, ∑ S ∈ A r,
            if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0) *
              rawMonomial T z by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro S hS
        dsimp [q]
        by_cases hsub : T ⊆ S
        · simp only [if_pos hsub]
          ring
        · simp [hsub]]
      ring

/-- Under the nondegenerate paper parameters, the exposed-order set is
nonempty and `kStar` belongs to it. -/
lemma kStar_mem_exposedOrder
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d) :
    kStar d β p ∈
      (Finset.Icc 1 (effBeta β d)).filter
        (fun r => bernoulliContrast p r ≠ 0) := by
  let exposed :=
    (Finset.Icc 1 (effBeta β d)).filter
      (fun r => bernoulliContrast p r ≠ 0)
  have heff : 1 ≤ effBeta β d := by
    simp [effBeta, hβ, hd]
  have hone : 1 ∈ exposed := by
    simp [exposed, heff, bernoulliContrast]
  have hne : exposed.Nonempty := ⟨1, hone⟩
  rw [show kStar d β p = exposed.max' hne by
    simp only [kStar, exposed]
    rw [dif_pos hne]]
  exact Finset.max'_mem exposed hne

/-- The top exposed summand supplies the pointwise lower comparison used in
the block-energy asymptotics. -/
lemma blockEnergy_topExposed_le
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (Nat.choose d (kStar d β p) : ℝ) *
        bernoulliContrast p (kStar d β p) ^ 2 /
          (p * (1 - p)) ^ kStar d β p ≤
      blockEnergy β p d := by
  have hk := kStar_mem_exposedOrder β d p hβ hd
  have hkIcc : kStar d β p ∈ Finset.Icc 1 (effBeta β d) :=
    (Finset.mem_filter.mp hk).1
  have hv : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  unfold blockEnergy
  exact Finset.single_le_sum
    (fun r _ => show
      0 ≤ (Nat.choose d r : ℝ) * bernoulliContrast p r ^ 2 /
        (p * (1 - p)) ^ r by positivity) hkIcc

/-- The common-probability Bernoulli design for a block is unchanged when its assignment
probability is replaced by an equal probability and the associated probability bounds are
transported along that equality. -/
add_decl_doc blockDesign.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
