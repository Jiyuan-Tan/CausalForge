import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmShiftedObstruction

/-!
# Overlap-calibrated grid scale

The smallest positive node shrinks by `κ⁴`; the rational pole is `κ` times
that node.  This keeps endpoint polynomial variation on the same `κ²` scale
as the shifted three-point signal.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The smallest positive node of the overlap-shifted approximation grid,
`κ⁴ / (10¹⁰ D²)`.  Shrinking it like `κ⁴` and like `1/D²` keeps the polynomial
variation across the three small nodes on the same `κ²` scale as the
three-point signal being obstructed. -/
noncomputable def oneArmShiftedNodeScale (κ : ℝ) (D : ℕ) : ℝ :=
  κ ^ 4 / (10000000000 * (D : ℝ) ^ 2)

/-- The location of the pole of the rational target, placed at `κ` times the
smallest grid node.  It therefore sits just below the grid, at a distance
calibrated by the overlap ratio `κ`. -/
noncomputable def oneArmShiftedPoleScale (κ : ℝ) (D : ℕ) : ℝ :=
  κ * oneArmShiftedNodeScale κ D

/-- The smallest grid node is strictly positive whenever the overlap ratio is
positive and the degree budget is at least one. -/
lemma oneArmShiftedNodeScale_pos {κ : ℝ} {D : ℕ}
    (hκ : 0 < κ) (hD : 1 ≤ D) : 0 < oneArmShiftedNodeScale κ D := by
  unfold oneArmShiftedNodeScale
  have hDR : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  positivity

/-- The pole location is strictly positive whenever the overlap ratio is
positive and the degree budget is at least one. -/
lemma oneArmShiftedPoleScale_pos {κ : ℝ} {D : ℕ}
    (hκ : 0 < κ) (hD : 1 ≤ D) : 0 < oneArmShiftedPoleScale κ D := by
  exact mul_pos hκ (oneArmShiftedNodeScale_pos hκ hD)

/-- Three times the smallest grid node is still at most one, so the three
special nodes used by the three-point obstruction all lie inside the unit
interval. -/
lemma oneArmShiftedNodeScale_three_le_one {κ : ℝ} {D : ℕ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D) :
    3 * oneArmShiftedNodeScale κ D ≤ 1 := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hκ2 : κ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hκ0 (sub_nonneg.mpr hκ1)]
  have hκ4 : κ ^ 4 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg κ) (sub_nonneg.mpr hκ2)]
  unfold oneArmShiftedNodeScale
  rw [show 3 * (κ ^ 4 / (10000000000 * (D : ℝ) ^ 2)) =
    (3 * κ ^ 4) / (10000000000 * (D : ℝ) ^ 2) by ring]
  apply (div_le_one (by positivity : (0 : ℝ) < 10000000000 * (D : ℝ) ^ 2)).2
  nlinarith [sq_nonneg ((D : ℝ) - 1)]

/-- The endpoint angular variation is at most `κ²/10000`. -/
lemma oneArm_shifted_calibrated_angular_scale
    (D : ℕ) (hD : 1 ≤ D) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (D : ℝ) * Real.sqrt
        (4 * oneArmShiftedNodeScale κ D / (1 - oneArmShiftedNodeScale κ D)) ≤
      κ ^ 2 / 10000 := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := zero_lt_one.trans_le hDR
  let a := oneArmShiftedNodeScale κ D
  have ha0 : 0 ≤ a := by
    dsimp [a, oneArmShiftedNodeScale]
    positivity
  have ha_half : a ≤ 1 / 2 := by
    have hκ2 : κ ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hκ0 (sub_nonneg.mpr hκ1)]
    have hκ4 : κ ^ 4 ≤ 1 := by
      nlinarith [mul_nonneg (sq_nonneg κ) (sub_nonneg.mpr hκ2)]
    dsimp [a, oneArmShiftedNodeScale]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 10000000000 * (D : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((D : ℝ) - 1)]
  have hden : 0 < 1 - a := by linarith
  have hinside : 4 * a / (1 - a) ≤
      (κ ^ 2 / (10000 * (D : ℝ))) ^ 2 := by
    have hκ2 : κ ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hκ0 (sub_nonneg.mpr hκ1)]
    have hκ4 : κ ^ 4 ≤ 1 := by
      nlinarith [mul_nonneg (sq_nonneg κ) (sub_nonneg.mpr hκ2)]
    have hDsq : (1 : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
    have hroom : 4 * (D : ℝ) ^ 2 * 10000 ^ 2 ≤
        10000000000 * (D : ℝ) ^ 2 - κ ^ 4 := by nlinarith
    have hmulroom := mul_nonneg (sq_nonneg (κ ^ 2))
      (sub_nonneg.mpr hroom)
    apply (div_le_iff₀ hden).2
    dsimp [a, oneArmShiftedNodeScale]
    field_simp
    nlinarith
  have hsqrt : Real.sqrt (4 * a / (1 - a)) ≤
      κ ^ 2 / (10000 * (D : ℝ)) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · simpa using hinside
  calc
    (D : ℝ) * Real.sqrt (4 * a / (1 - a)) ≤
        (D : ℝ) * (κ ^ 2 / (10000 * (D : ℝ))) :=
      mul_le_mul_of_nonneg_left hsqrt hD0.le
    _ = κ ^ 2 / 10000 := by field_simp

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
