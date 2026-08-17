import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenterCore

/-!
# Uniform block-energy and raw-coefficient bounds
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

/-- Exposed orders among the fixed paper orders `1,...,β`. -/
noncomputable def fixedExposed (β : ℕ) (p : ℝ) : Finset ℕ :=
  (Finset.Icc 1 β).filter (fun r => bernoulliContrast p r ≠ 0)

/-- The positive coefficient multiplying the order-`r` binomial term. -/
noncomputable def energyCoeff (p : ℝ) (r : ℕ) : ℝ :=
  bernoulliContrast p r ^ 2 / (p * (1 - p)) ^ r

/-- The coefficient occurring after expanding centered into raw monomials. -/
noncomputable def rawMassCoeff (p : ℝ) (r : ℕ) : ℝ :=
  |bernoulliContrast p r| / (p * (1 - p)) ^ r * (1 + p) ^ r

/-- Minimum positive exposed coefficient at the finitely many fixed orders. -/
noncomputable def blockLowerConst (β : ℕ) (p : ℝ) : ℝ :=
  if h : (fixedExposed β p).Nonempty then
    (fixedExposed β p).image (energyCoeff p) |>.min'
      ((Finset.image_nonempty).mpr h)
  else 1

/-- A uniform upper comparison constant for block energy. -/
noncomputable def blockUpperConst (β : ℕ) (p : ℝ) : ℝ :=
  ((2 ^ β : ℕ) : ℝ) * ∑ r ∈ Finset.Icc 1 β, energyCoeff p r

/-- A uniform bound for the normalized raw coefficient mass. -/
noncomputable def blockRawMassConst (β : ℕ) (p : ℝ) : ℝ :=
  blockLowerConst β p +
    (((2 ^ β : ℕ) : ℝ) *
      ∑ r ∈ Finset.Icc 1 β, rawMassCoeff p r) / blockLowerConst β p

/-- Fixed-order binomial coefficients are uniformly controlled by the
largest exposed-order coefficient. -/
lemma choose_le_pow_mul_choose (d r k β : ℕ)
    (hrk : r ≤ k) (hkd : k ≤ d) (hkβ : k ≤ β) :
    Nat.choose d r ≤ 2 ^ β * Nat.choose d k := by
  have hid := Nat.choose_mul (n := d) (k := k) (s := r) hrk
  have hone : 1 ≤ Nat.choose (d - r) (k - r) :=
    Nat.choose_pos (by omega)
  have hfirst :
      Nat.choose d r ≤ Nat.choose d k * Nat.choose k r := by
    calc
      Nat.choose d r ≤ Nat.choose d r * Nat.choose (d - r) (k - r) := by
        nlinarith
      _ = Nat.choose d k * Nat.choose k r := hid.symm
  have hpow : Nat.choose k r ≤ 2 ^ β := by
    calc
      Nat.choose k r ≤ 2 ^ k := Nat.choose_le_two_pow k r
      _ ≤ 2 ^ β := Nat.pow_le_pow_right (by omega) hkβ
  nlinarith

/-- Every nonzero eligible order is at most the largest exposed order. -/
lemma eligibleOrder_le_kStar
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (r : ℕ) (hr : r ∈ Finset.Icc 1 (effBeta β d))
    (hrnz : bernoulliContrast p r ≠ 0) :
    r ≤ kStar d β p := by
  let exposed :=
    (Finset.Icc 1 (effBeta β d)).filter
      (fun q => bernoulliContrast p q ≠ 0)
  have heff : 1 ≤ effBeta β d := by simp [effBeta, hβ, hd]
  have hone : 1 ∈ exposed := by
    simp only [exposed, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, heff⟩, by norm_num [bernoulliContrast]⟩
  have hne : exposed.Nonempty := ⟨1, hone⟩
  have hrmem : r ∈ exposed := Finset.mem_filter.mpr ⟨hr, hrnz⟩
  rw [show kStar d β p = exposed.max' hne by
    simp only [kStar, exposed]
    rw [dif_pos hne]]
  exact Finset.le_max' exposed r hrmem

/-- The fixed-order lower constant is positive and bounds every exposed
coefficient from below. -/
lemma blockLowerConst_spec
    (β : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < blockLowerConst β p ∧
      ∀ r ∈ fixedExposed β p,
        blockLowerConst β p ≤ energyCoeff p r := by
  have hone : 1 ∈ fixedExposed β p := by
    simp only [fixedExposed, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hβ⟩, by norm_num [bernoulliContrast]⟩
  have hne : (fixedExposed β p).Nonempty := ⟨1, hone⟩
  rw [blockLowerConst, dif_pos hne]
  constructor
  · have hm := Finset.min'_mem
      ((fixedExposed β p).image (energyCoeff p))
      ((Finset.image_nonempty).mpr hne)
    rcases Finset.mem_image.mp hm with ⟨r, hr, heq⟩
    rw [← heq]
    simp only [energyCoeff]
    have hrnz := (Finset.mem_filter.mp hr).2
    exact div_pos (sq_pos_of_ne_zero hrnz)
      (pow_pos (mul_pos hp0 (sub_pos.mpr hp1)) r)
  · intro r hr
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

/-- Uniform two-sided comparison of block energy with the top exposed
binomial coefficient. -/
lemma blockEnergy_uniform_compare
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    blockLowerConst β p * (Nat.choose d (kStar d β p) : ℝ) ≤
        blockEnergy β p d ∧
      blockEnergy β p d ≤
        blockUpperConst β p * (Nat.choose d (kStar d β p) : ℝ) := by
  have hk := kStar_mem_exposedOrder β d p hβ hd
  have hkIcc := (Finset.mem_filter.mp hk).1
  have hkd : kStar d β p ≤ d :=
    (Finset.mem_Icc.mp hkIcc).2.trans (min_le_right β d)
  have hkβ : kStar d β p ≤ β :=
    (Finset.mem_Icc.mp hkIcc).2.trans (min_le_left β d)
  have hkc : blockLowerConst β p ≤ energyCoeff p (kStar d β p) := by
    exact (blockLowerConst_spec β p hβ hp0 hp1).2 _ <|
      Finset.mem_filter.mpr ⟨
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hkIcc).1, hkβ⟩,
        (Finset.mem_filter.mp hk).2⟩
  constructor
  · calc
      blockLowerConst β p * (Nat.choose d (kStar d β p) : ℝ) ≤
          (Nat.choose d (kStar d β p) : ℝ) *
            energyCoeff p (kStar d β p) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hkc (by positivity)
      _ ≤ blockEnergy β p d := by
        convert blockEnergy_topExposed_le β d p hβ hd hp0 hp1 using 1 <;>
          simp [energyCoeff] <;> ring
  · unfold blockUpperConst
    rw [show blockEnergy β p d =
        ∑ r ∈ Finset.Icc 1 (effBeta β d),
          (Nat.choose d r : ℝ) * energyCoeff p r by
      unfold blockEnergy
      apply Finset.sum_congr rfl
      intro r hr
      simp only [energyCoeff]
      ring]
    calc
      (∑ r ∈ Finset.Icc 1 (effBeta β d),
          (Nat.choose d r : ℝ) * energyCoeff p r) ≤
        ∑ r ∈ Finset.Icc 1 (effBeta β d),
          (((2 ^ β : ℕ) : ℝ) * Nat.choose d (kStar d β p)) *
            energyCoeff p r := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases hrnz : bernoulliContrast p r = 0
        · simp [hrnz, energyCoeff]
        · have hc := choose_le_pow_mul_choose d r (kStar d β p) β
              (eligibleOrder_le_kStar β d p hβ hd r hr hrnz) hkd hkβ
          have hcoef : 0 ≤ energyCoeff p r := by
            simp only [energyCoeff]
            exact div_nonneg (sq_nonneg _)
              (pow_nonneg
                (mul_nonneg (le_of_lt hp0) (le_of_lt (sub_pos.mpr hp1))) r)
          gcongr
          exact_mod_cast hc
      _ ≤ ∑ r ∈ Finset.Icc 1 β,
          (((2 ^ β : ℕ) : ℝ) * Nat.choose d (kStar d β p)) *
            energyCoeff p r := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          simp only [Finset.mem_Icc] at hr ⊢
          exact ⟨hr.1, hr.2.trans (min_le_left β d)⟩
        · intro r _ _
          simp only [energyCoeff]
          exact mul_nonneg (by positivity) <|
            div_nonneg (sq_nonneg _)
              (pow_nonneg
                (mul_nonneg (le_of_lt hp0) (le_of_lt (sub_pos.mpr hp1))) r)
      _ = (((2 ^ β : ℕ) : ℝ) *
            ∑ r ∈ Finset.Icc 1 β, energyCoeff p r) *
            Nat.choose d (kStar d β p) := by
        rw [← Finset.mul_sum]
        ring

/-- Direct triangle-inequality estimate after expanding centered monomials
in the raw basis. -/
lemma blockRawCoef_mass_estimate
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∑ T ∈ Finset.univ.powerset, |blockRawCoef β p d T|) ≤
      (blockEnergy β p d)⁻¹ *
        ∑ r ∈ Finset.Icc 1 (effBeta β d),
          (Nat.choose d r : ℝ) * rawMassCoeff p r := by
  let A := blockEnergy β p d
  have hA : 0 < A := blockEnergy_pos β d p hβ hd hp0 hp1
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  let R := Finset.Icc 1 (effBeta β d)
  let F : ℕ → Finset (Finset (Fin d)) := fun r =>
    Finset.univ.powerset.filter (fun S : Finset (Fin d) => S.card = r)
  let c : ℕ → ℝ := fun r =>
    bernoulliContrast p r / (p * (1 - p)) ^ r
  simp only [blockRawCoef, if_neg hd0]
  rw [show
      (∑ T ∈ Finset.univ.powerset,
        |A⁻¹ * ∑ r ∈ R, ∑ S ∈ F r,
          if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0|) =
      A⁻¹ * ∑ T ∈ Finset.univ.powerset,
        |∑ r ∈ R, ∑ S ∈ F r,
          if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0| by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [abs_mul, abs_inv, abs_of_pos hA]]
  apply mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hA))
  calc
    (∑ T ∈ Finset.univ.powerset,
        |∑ r ∈ R, ∑ S ∈ F r,
          if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0|) ≤
      ∑ T ∈ Finset.univ.powerset, ∑ r ∈ R, ∑ S ∈ F r,
        |if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0| := by
      apply Finset.sum_le_sum
      intro T hT
      calc
        |∑ r ∈ R, ∑ S ∈ F r,
            if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0| ≤
          ∑ r ∈ R, |∑ S ∈ F r,
            if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro r hr
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ R, ∑ S ∈ F r, ∑ T ∈ S.powerset,
          |c r * (-p) ^ (S.card - T.card)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [show
          (∑ T ∈ Finset.univ.powerset, ∑ S ∈ F r,
            |if T ⊆ S then c r * (-p) ^ (S.card - T.card) else 0|) =
          ∑ T ∈ Finset.univ.powerset, ∑ S ∈ F r,
            if T ⊆ S then |c r * (-p) ^ (S.card - T.card)| else 0 by
        apply Finset.sum_congr rfl
        intro T hT
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hsub : T ⊆ S <;> simp [hsub]]
      exact sum_powerset_subset_exchange (F r)
        (fun S T => |c r * (-p) ^ (S.card - T.card)|)
    _ = ∑ r ∈ R, (Nat.choose d r : ℝ) * rawMassCoeff p r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [show
          (∑ S ∈ F r, ∑ T ∈ S.powerset,
            |c r * (-p) ^ (S.card - T.card)|) =
          ∑ S ∈ F r, (|c r| * (1 + p) ^ r) by
        apply Finset.sum_congr rfl
        intro S hS
        have hScard : S.card = r := (Finset.mem_filter.mp hS).2
        rw [show
            (∑ T ∈ S.powerset,
              |c r * (-p) ^ (S.card - T.card)|) =
            |c r| * ∑ T ∈ S.powerset,
              (1 : ℝ) ^ T.card * p ^ (S.card - T.card) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T hT
          rw [abs_mul, abs_pow, abs_neg, abs_of_pos hp0]
          simp]
        rw [Finset.sum_pow_mul_eq_add_pow, hScard]]
      rw [Finset.sum_const, show (F r).card = Nat.choose d r by
        simp [F, Finset.card_powersetCard]]
      simp only [nsmul_eq_mul, c, rawMassCoeff, abs_div, abs_pow,
        abs_of_pos (mul_pos hp0 (sub_pos.mpr hp1))]

/-- The normalized raw coefficient mass is bounded uniformly in block size. -/
lemma blockRawCoef_mass_uniform
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∑ T ∈ Finset.univ.powerset, |blockRawCoef β p d T|) ≤
      blockRawMassConst β p := by
  let c₁ := blockLowerConst β p
  let C := ((2 ^ β : ℕ) : ℝ) *
    ∑ r ∈ Finset.Icc 1 β, rawMassCoeff p r
  let K : ℝ := Nat.choose d (kStar d β p)
  let A := blockEnergy β p d
  have hc₁ : 0 < c₁ := (blockLowerConst_spec β p hβ hp0 hp1).1
  have hA : 0 < A := blockEnergy_pos β d p hβ hd hp0 hp1
  have hk := kStar_mem_exposedOrder β d p hβ hd
  have hkIcc := (Finset.mem_filter.mp hk).1
  have hkd : kStar d β p ≤ d :=
    (Finset.mem_Icc.mp hkIcc).2.trans (min_le_right β d)
  have hkβ : kStar d β p ≤ β :=
    (Finset.mem_Icc.mp hkIcc).2.trans (min_le_left β d)
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast Nat.choose_pos hkd
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) <| Finset.sum_nonneg fun r hr =>
      mul_nonneg
        (div_nonneg (abs_nonneg _)
          (pow_nonneg
            (mul_nonneg (le_of_lt hp0) (le_of_lt (sub_pos.mpr hp1))) r))
        (pow_nonneg (by linarith) r)
  have hnum :
      (∑ r ∈ Finset.Icc 1 (effBeta β d),
          (Nat.choose d r : ℝ) * rawMassCoeff p r) ≤ C * K := by
    calc
      (∑ r ∈ Finset.Icc 1 (effBeta β d),
          (Nat.choose d r : ℝ) * rawMassCoeff p r) ≤
        ∑ r ∈ Finset.Icc 1 (effBeta β d),
          (((2 ^ β : ℕ) : ℝ) * Nat.choose d (kStar d β p)) *
            rawMassCoeff p r := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases hrnz : bernoulliContrast p r = 0
        · simp [hrnz, rawMassCoeff]
        · have hc := choose_le_pow_mul_choose d r (kStar d β p) β
              (eligibleOrder_le_kStar β d p hβ hd r hr hrnz) hkd hkβ
          have hcoef : 0 ≤ rawMassCoeff p r := by
            simp only [rawMassCoeff]
            exact mul_nonneg
              (div_nonneg (abs_nonneg _)
                (pow_nonneg
                  (mul_nonneg (le_of_lt hp0) (le_of_lt (sub_pos.mpr hp1))) r))
              (pow_nonneg (by linarith) r)
          gcongr
          exact_mod_cast hc
      _ ≤ ∑ r ∈ Finset.Icc 1 β,
          (((2 ^ β : ℕ) : ℝ) * Nat.choose d (kStar d β p)) *
            rawMassCoeff p r := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          simp only [Finset.mem_Icc] at hr ⊢
          exact ⟨hr.1, hr.2.trans (min_le_left β d)⟩
        · intro r _ _
          simp only [rawMassCoeff]
          exact mul_nonneg (by positivity) <| mul_nonneg
            (div_nonneg (abs_nonneg _)
              (pow_nonneg
                (mul_nonneg (le_of_lt hp0) (le_of_lt (sub_pos.mpr hp1))) r))
            (pow_nonneg (by linarith) r)
      _ = C * K := by
        dsimp [C, K]
        rw [← Finset.mul_sum]
        ring
  have hlower : c₁ * K ≤ A := by
    exact (blockEnergy_uniform_compare β d p hβ hd hp0 hp1).1
  calc
    (∑ T ∈ Finset.univ.powerset, |blockRawCoef β p d T|) ≤
        A⁻¹ * ∑ r ∈ Finset.Icc 1 (effBeta β d),
          (Nat.choose d r : ℝ) * rawMassCoeff p r :=
      blockRawCoef_mass_estimate β d p hβ hd hp0 hp1
    _ ≤ A⁻¹ * (C * K) := by
      gcongr
    _ ≤ C / c₁ := by
      rw [show A⁻¹ * (C * K) = C * K / A by
        field_simp [hA.ne']]
      rw [div_le_iff₀ hA]
      calc
        C * K = (C / c₁) * (c₁ * K) := by
          field_simp [hc₁.ne']
        _ ≤ (C / c₁) * A :=
          mul_le_mul_of_nonneg_left hlower
            (div_nonneg hC (le_of_lt hc₁))
    _ ≤ blockRawMassConst β p := by
      dsimp [blockRawMassConst, c₁, C]
      linarith

end CausalSmith.Experimentation.SnipeDegreeFrontier
