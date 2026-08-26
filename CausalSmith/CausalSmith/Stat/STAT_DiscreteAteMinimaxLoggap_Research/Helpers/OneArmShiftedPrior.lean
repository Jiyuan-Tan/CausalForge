import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPriorLift

/-!
# Decoupled-shift signed priors for the one-arm converse

This module separates the lower endpoint of the Lobatto grid from the inverse-
tilt shift.  The extra degree of freedom keeps the propensity inside
`[epsilon, 1-epsilon]` for every `epsilon < 1/2`, while retaining the same
order of rational-functional separation.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open CausalSmith.Experimentation.RolloutChebyshev
open scoped BigOperators

/-- Standard-coordinate image of the exterior point `-b` for the Lobatto grid
on `[a,1]`. -/
noncomputable def oneArmShiftedExterior (a b : ℝ) : ℝ :=
  (1 + a + 2 * b) / (1 - a)

lemma oneArmShiftedExterior_gt_one {a b : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) :
    1 < oneArmShiftedExterior a b := by
  unfold oneArmShiftedExterior
  rw [lt_div_iff₀ (sub_pos.mpr ha1)]
  linarith

lemma oneArmLobatto_affine_shiftedExterior {a b : ℝ} (ha1 : a < 1) :
    (1 + a) / 2 - ((1 - a) / 2) * oneArmShiftedExterior a b = -b := by
  unfold oneArmShiftedExterior
  field_simp [ne_of_gt (sub_pos.mpr ha1)]
  ring

/-- Exact Lagrange-mass formula at the independently chosen exterior point
`-b`. -/
lemma oneArmLobatto_shifted_lagrange_abs_sum_eq (n : ℕ) {a b : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) :
    ∑ i ∈ Finset.Iic n,
        |(Lagrange.basis (Finset.Iic n) (oneArmLobattoNode n a) i).eval (-b)| =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (oneArmShiftedExterior a b) := by
  let c : ℝ := (1 + a) / 2
  let r : ℝ := -((1 - a) / 2)
  let z : ℝ := oneArmShiftedExterior a b
  have hr : r ≠ 0 := by
    dsimp [r]
    exact neg_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr (ne_of_lt ha1).symm) (by norm_num))
  have hx : Set.InjOn (Polynomial.Chebyshev.node n) (Finset.Iic n) := by
    simpa [Nat.range_succ_eq_Iic] using
      (Polynomial.Chebyshev.strictAntiOn_node n).injOn
  have hz : c + r * z = -b := by
    simpa [c, r, z, sub_eq_add_neg] using oneArmLobatto_affine_shiftedExterior ha1
  rw [← chebyshev_exterior_lagrange_abs_sum_eq n z
    (oneArmShiftedExterior_gt_one ha0 ha1 hb0)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hz]
  have hnodes : oneArmLobattoNode n a =
      (fun j => c + r * Polynomial.Chebyshev.node n j) := by
    funext j
    simp [oneArmLobattoNode, c, r]
    ring
  rw [hnodes]
  exact congrArg abs (lagrange_basis_eval_affine hx hi c r z hr)

/-- Product-times-variation bound at the decoupled exterior point. -/
lemma oneArmLobatto_shifted_jordan_product_bound (n : ℕ) {a b : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) :
    |∏ i ∈ Finset.Iic n, (-b - oneArmLobattoNode n a i)| *
        (∑ i ∈ Finset.Iic n,
          |oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i|) ≤
      (1 + b) * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (oneArmShiftedExterior a b) := by
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ Finset.Iic n,
        |∏ j ∈ Finset.Iic n, (-b - oneArmLobattoNode n a j)| *
          |oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i| =
      ∑ i ∈ Finset.Iic n,
        |(-b - oneArmLobattoNode n a i) * oneArmLobattoNode n a i *
          (Lagrange.basis (Finset.Iic n) (oneArmLobattoNode n a) i).eval (-b)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← abs_mul]
      exact congrArg abs (prod_sub_mul_nodeBarycentricWeight_eq hi (by
        have hxi := (oneArmLobattoNode_in_Icc ha0 ha1 (n := n) (i := i)).1
        linarith))
    _ ≤ ∑ i ∈ Finset.Iic n,
        (1 + b) *
          |(Lagrange.basis (Finset.Iic n) (oneArmLobattoNode n a) i).eval (-b)| := by
      apply Finset.sum_le_sum
      intro i hi
      have hxi := oneArmLobattoNode_in_Icc ha0 ha1 (n := n) (i := i)
      have hnonneg : 0 ≤ oneArmLobattoNode n a i := hxi.1.trans' ha0.le
      rw [abs_mul, abs_mul, abs_of_nonneg hnonneg]
      rw [show |-b - oneArmLobattoNode n a i| =
          b + oneArmLobattoNode n a i by
        rw [abs_of_nonpos (by linarith)]
        ring]
      have hsquare : oneArmLobattoNode n a i * oneArmLobattoNode n a i ≤
          oneArmLobattoNode n a i :=
        mul_le_of_le_one_left hnonneg hxi.2
      have hbmul : b * oneArmLobattoNode n a i ≤ b := by
        simpa using mul_le_mul_of_nonneg_left hxi.2 hb0.le
      have hfactor : (b + oneArmLobattoNode n a i) *
          oneArmLobattoNode n a i ≤ 1 + b := by nlinarith
      exact mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
    _ = (1 + b) * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (oneArmShiftedExterior a b) := by
      rw [← Finset.mul_sum,
        oneArmLobatto_shifted_lagrange_abs_sum_eq n ha0 ha1 hb0]

/-- Quantitative normalized rational separation with grid endpoint `a` and
inverse-tilt shift `b`. -/
lemma oneArmLobatto_shifted_normalized_rational_gap (n : ℕ) (hn : 1 ≤ n)
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) :
    2 * b ^ 2 /
        ((1 + b) * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
          (oneArmShiftedExterior a b)) ≤
      |(∑ i ∈ Finset.Iic n,
          (oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i) *
              (b / (oneArmLobattoNode n a i + b))) /
        ((∑ i ∈ Finset.Iic n,
          |oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i|) / 2)| := by
  let s : Finset ℕ := Finset.Iic n
  let x : ℕ → ℝ := oneArmLobattoNode n a
  let w : ℕ → ℝ := fun i => x i * barycentricWeight s x i
  let B : ℝ := ∏ i ∈ s, (-b - x i)
  let S : ℝ := ∑ i ∈ s, |w i|
  let T : ℝ := (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (oneArmShiftedExterior a b)
  have hs : s.Nonempty := by simp [s]
  have hx : Set.InjOn x s := by
    simpa [s, x] using oneArmLobattoNode_injectiveOn n ha1
  have hxpos : ∀ i ∈ s, 0 < x i := by
    intro i hi
    exact lt_of_lt_of_le ha0 (oneArmLobattoNode_in_Icc ha0 ha1).1
  have hraw : ∑ i ∈ s, w i * (b / (x i + b)) = b ^ 2 * B⁻¹ := by
    simpa [s, x, w, B] using
      nodeBarycentric_rational_separation hs hx (by simp [s]; omega) hb0 hxpos
  have hBne : B ≠ 0 := by
    dsimp [B]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    linarith [hxpos i hi]
  have hSpos : 0 < S := by
    have hi : 0 ∈ s := by simp [s]
    have hbary : barycentricWeight s x 0 ≠ 0 := by
      simpa [barycentricWeight, Lagrange.nodalWeight] using
        Lagrange.nodalWeight_ne_zero hx hi
    exact Finset.sum_pos' (fun i _ => abs_nonneg (w i))
      ⟨0, hi, abs_pos.mpr (mul_ne_zero (ne_of_gt (hxpos 0 hi)) hbary)⟩
  have hbound : |B| * S ≤ (1 + b) * T := by
    simpa [s, x, w, B, S, T] using
      oneArmLobatto_shifted_jordan_product_bound n ha0 ha1 hb0
  have hBSpos : 0 < |B| * S := mul_pos (abs_pos.mpr hBne) hSpos
  have hprodTpos : 0 < (1 + b) * T := hBSpos.trans_le hbound
  have hTpos : 0 < T := by
    rcases mul_pos_iff.mp hprodTpos with h | h
    · exact h.2
    · linarith
  have hDpos : 0 < |B| * (S / 2) := mul_pos (abs_pos.mpr hBne) (by positivity)
  have hdenpos : 0 < (1 + b) * T := mul_pos (by linarith) hTpos
  have hDle : |B| * (S / 2) ≤ ((1 + b) * T) / 2 := by nlinarith
  have hgap : |(b ^ 2 * B⁻¹) / (S / 2)| = b ^ 2 / (|B| * (S / 2)) := by
    rw [abs_div, abs_mul, abs_inv, abs_of_nonneg (sq_nonneg b),
      abs_of_pos (div_pos hSpos (by norm_num))]
    field_simp [hBne, ne_of_gt hSpos]
  change 2 * b ^ 2 / ((1 + b) * T) ≤
    |(∑ i ∈ s, w i * (b / (x i + b))) / (S / 2)|
  rw [hraw, hgap]
  rw [div_le_div_iff₀ hdenpos hDpos]
  nlinarith [mul_le_mul_of_nonneg_left hDle (sq_nonneg b)]

/-- Grid endpoint calibrated so the decoupled exterior coordinate is
`cosh(1/n)`. -/
noncomputable def oneArmShiftedScale (n : ℕ) (κ : ℝ) : ℝ :=
  (Real.cosh ((n : ℝ)⁻¹) - 1) /
    (Real.cosh ((n : ℝ)⁻¹) + 1 + 2 * κ)

lemma oneArmShiftedScale_pos {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) :
    0 < oneArmShiftedScale n κ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : 1 < Real.cosh ((n : ℝ)⁻¹) := Real.one_lt_cosh.mpr (inv_ne_zero hn0)
  unfold oneArmShiftedScale
  positivity

lemma oneArmShiftedScale_lt_one {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) :
    oneArmShiftedScale n κ < 1 := by
  have hc0 : 0 < Real.cosh ((n : ℝ)⁻¹) := Real.cosh_pos _
  unfold oneArmShiftedScale
  rw [div_lt_one (by positivity)]
  linarith

/-- Explicit inverse-square lower bound for the decoupled grid endpoint. -/
lemma oneArmShiftedScale_lower {n : ℕ} (hn : 1 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ((n : ℝ)⁻¹) ^ 2 /
        ((Real.cosh 1 + 1) * (Real.cosh 1 + 1 + 2 * κ)) ≤
      oneArmShiftedScale n κ := by
  let t : ℝ := (n : ℝ)⁻¹
  let c : ℝ := Real.cosh t
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact inv_le_one_of_one_le₀ hnR
  have hc1 : c ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh]
    simpa [abs_of_nonneg ht0] using ht1
  have hc_ge : 1 ≤ c := by
    dsimp [c]
    exact Real.one_le_cosh _
  have hsinh : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr ht0
  have hsq : t ^ 2 ≤ Real.sinh t ^ 2 :=
    pow_le_pow_left₀ ht0 hsinh 2
  have hid : Real.sinh t ^ 2 = (c - 1) * (c + 1) := by
    dsimp [c]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hbase : t ^ 2 ≤ (c - 1) * (c + 1) := by rw [← hid]; exact hsq
  have hcden : 0 < c + 1 + 2 * κ := by
    have := Real.cosh_pos t
    dsimp [c]
    linarith
  have hC1 : 0 < Real.cosh 1 + 1 := by
    have := Real.cosh_pos 1
    linarith
  have hCden : 0 < Real.cosh 1 + 1 + 2 * κ := by
    have := Real.cosh_pos 1
    linarith
  have hCprod : 0 < (Real.cosh 1 + 1) * (Real.cosh 1 + 1 + 2 * κ) :=
    mul_pos hC1 hCden
  unfold oneArmShiftedScale
  change t ^ 2 / ((Real.cosh 1 + 1) * (Real.cosh 1 + 1 + 2 * κ)) ≤
    (c - 1) / (c + 1 + 2 * κ)
  rw [div_le_div_iff₀ hCprod hcden]
  calc
    t ^ 2 * (c + 1 + 2 * κ) ≤
        ((c - 1) * (c + 1)) * (c + 1 + 2 * κ) :=
      mul_le_mul_of_nonneg_right hbase hcden.le
    _ = (c - 1) * ((c + 1) * (c + 1 + 2 * κ)) := by ring
    _ ≤ (c - 1) *
        ((Real.cosh 1 + 1) * (Real.cosh 1 + 1 + 2 * κ)) := by
      gcongr

lemma oneArmShiftedExterior_scale (n : ℕ) (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) :
    oneArmShiftedExterior (oneArmShiftedScale n κ)
      (κ * oneArmShiftedScale n κ) = Real.cosh ((n : ℝ)⁻¹) := by
  have hden : Real.cosh ((n : ℝ)⁻¹) + 1 + 2 * κ ≠ 0 := by positivity
  have hscale1 : oneArmShiftedScale n κ < 1 := oneArmShiftedScale_lt_one hn hκ
  unfold oneArmShiftedExterior
  rw [div_eq_iff (sub_ne_zero.mpr (ne_of_lt hscale1).symm)]
  unfold oneArmShiftedScale
  field_simp [hden]
  ring

/-- Calibrated decoupled priors retain an explicit positive normalized gap. -/
lemma oneArmLobatto_shifted_uniform_gap (n : ℕ) (hn : 1 ≤ n)
    {κ : ℝ} (hκ : 0 < κ) :
    2 * (κ * oneArmShiftedScale n κ) ^ 2 /
        ((1 + κ * oneArmShiftedScale n κ) * Real.cosh 1) ≤
      |(∑ i ∈ Finset.Iic n,
          (oneArmLobattoNode n (oneArmShiftedScale n κ) i *
            barycentricWeight (Finset.Iic n)
              (oneArmLobattoNode n (oneArmShiftedScale n κ)) i) *
            ((κ * oneArmShiftedScale n κ) /
              (oneArmLobattoNode n (oneArmShiftedScale n κ) i +
                κ * oneArmShiftedScale n κ))) /
        ((∑ i ∈ Finset.Iic n,
          |oneArmLobattoNode n (oneArmShiftedScale n κ) i *
            barycentricWeight (Finset.Iic n)
              (oneArmLobattoNode n (oneArmShiftedScale n κ)) i|) / 2)| := by
  have hbase := oneArmLobatto_shifted_normalized_rational_gap n hn
    (oneArmShiftedScale_pos hn hκ) (oneArmShiftedScale_lt_one hn hκ)
    (mul_pos hκ (oneArmShiftedScale_pos hn hκ))
  rw [oneArmShiftedExterior_scale n hn hκ] at hbase
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simpa [show (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
      (Real.cosh ((n : ℝ)⁻¹)) = Real.cosh 1 by
        calc
          _ = Real.cosh ((n : ℝ) * (n : ℝ)⁻¹) := by simp
          _ = Real.cosh 1 := by rw [mul_inv_cancel₀ hn0]] using hbase

/-- Explicit shift ratio that keeps `epsilon * (1 + κ)` strictly below the
upper overlap endpoint for every `epsilon < 1/2`. -/
noncomputable def oneArmOverlapShiftRatio (epsilon : ℝ) : ℝ :=
  min 1 ((1 - 2 * epsilon) / (2 * epsilon))

lemma oneArmOverlapShiftRatio_pos {epsilon : ℝ}
    (he0 : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    0 < oneArmOverlapShiftRatio epsilon := by
  unfold oneArmOverlapShiftRatio
  exact lt_min (by norm_num) (div_pos (by linarith) (by positivity))

lemma oneArmOverlapShiftRatio_le_one (epsilon : ℝ) :
    oneArmOverlapShiftRatio epsilon ≤ 1 := by
  exact min_le_left _ _

lemma epsilon_mul_one_add_overlapShiftRatio_le {epsilon : ℝ}
    (he0 : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    epsilon * (1 + oneArmOverlapShiftRatio epsilon) ≤ 1 - epsilon := by
  have hκ : oneArmOverlapShiftRatio epsilon ≤
      (1 - 2 * epsilon) / (2 * epsilon) := min_le_right _ _
  have heq : epsilon * (1 + (1 - 2 * epsilon) / (2 * epsilon)) = 1 / 2 := by
    field_simp [ne_of_gt he0]
    ring
  have hupper : epsilon * (1 + oneArmOverlapShiftRatio epsilon) ≤ 1 / 2 := by
    calc
      epsilon * (1 + oneArmOverlapShiftRatio epsilon) ≤
          epsilon * (1 + (1 - 2 * epsilon) / (2 * epsilon)) := by gcongr
      _ = 1 / 2 := heq
  linarith

/-- The calibrated inverse-tilt shift stays below every Lobatto node. -/
lemma oneArm_calibratedShift_le_node (n i : ℕ) (hn : 1 ≤ n)
    {epsilon : ℝ} (he0 : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    oneArmOverlapShiftRatio epsilon *
        oneArmShiftedScale n (oneArmOverlapShiftRatio epsilon) ≤
      oneArmLobattoNode n
        (oneArmShiftedScale n (oneArmOverlapShiftRatio epsilon)) i := by
  let κ := oneArmOverlapShiftRatio epsilon
  let a := oneArmShiftedScale n κ
  have hκ0 : 0 ≤ κ := (oneArmOverlapShiftRatio_pos he0 hehalf).le
  have hκ1 : κ ≤ 1 := oneArmOverlapShiftRatio_le_one epsilon
  have ha0 : 0 ≤ a := (oneArmShiftedScale_pos hn
    (oneArmOverlapShiftRatio_pos he0 hehalf)).le
  have hnode : a ≤ oneArmLobattoNode n a i :=
    (oneArmLobattoNode_in_Icc (oneArmShiftedScale_pos hn
      (oneArmOverlapShiftRatio_pos he0 hehalf))
      (oneArmShiftedScale_lt_one hn
        (oneArmOverlapShiftRatio_pos he0 hehalf))).1
  calc
    κ * a ≤ 1 * a := mul_le_mul_of_nonneg_right hκ1 ha0
    _ = a := one_mul a
    _ ≤ oneArmLobattoNode n a i := hnode

/-- The calibrated decoupled construction has nonnegative inverse-tilt
weights for every positive-node prior. -/
lemma oneArm_calibrated_inverseTiltWeight_nonneg {ι : Type*} [Fintype ι]
    (ω : PMF ι) (n : ℕ) (hn : 1 ≤ n)
    {epsilon : ℝ} (he0 : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (index : ι → ℕ) :
    ∀ z, 0 ≤ inverseTiltWeight ω
      (fun i => oneArmLobattoNode n
        (oneArmShiftedScale n (oneArmOverlapShiftRatio epsilon)) (index i))
      (oneArmOverlapShiftRatio epsilon *
        oneArmShiftedScale n (oneArmOverlapShiftRatio epsilon)) z := by
  apply inverseTiltWeight_nonneg
  · exact mul_nonneg (oneArmOverlapShiftRatio_pos he0 hehalf).le
      (oneArmShiftedScale_pos hn (oneArmOverlapShiftRatio_pos he0 hehalf)).le
  · intro i
    exact oneArm_calibratedShift_le_node n (index i) hn he0 hehalf

/-- Every calibrated lifted propensity lies in the full public overlap range
for arbitrary `0 < epsilon < 1/2`. -/
lemma oneArm_calibrated_liftedPropensity_mem_Icc
    (n i : ℕ) (hn : 1 ≤ n) {epsilon : ℝ}
    (he0 : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    liftedPropensity epsilon
        (oneArmOverlapShiftRatio epsilon *
          oneArmShiftedScale n (oneArmOverlapShiftRatio epsilon))
        (oneArmLobattoNode n
          (oneArmShiftedScale n (oneArmOverlapShiftRatio epsilon))) i ∈
      Set.Icc epsilon (1 - epsilon) := by
  let κ := oneArmOverlapShiftRatio epsilon
  let a := oneArmShiftedScale n κ
  let b := κ * a
  have ha0 : 0 < a := oneArmShiftedScale_pos hn
    (oneArmOverlapShiftRatio_pos he0 hehalf)
  have hnode : 0 < oneArmLobattoNode n a i :=
    lt_of_lt_of_le ha0 (oneArmLobattoNode_in_Icc ha0
      (oneArmShiftedScale_lt_one hn (oneArmOverlapShiftRatio_pos he0 hehalf))).1
  have hbx : b ≤ κ * oneArmLobattoNode n a i := by
    exact mul_le_mul_of_nonneg_left
      (oneArmLobattoNode_in_Icc ha0
        (oneArmShiftedScale_lt_one hn (oneArmOverlapShiftRatio_pos he0 hehalf))).1
      (oneArmOverlapShiftRatio_pos he0 hehalf).le
  exact liftedPropensity_mem_Icc_of_shift_le he0.le
    (mul_nonneg (oneArmOverlapShiftRatio_pos he0 hehalf).le ha0.le)
    (oneArmOverlapShiftRatio_pos he0 hehalf).le
    (fun _ => hnode) (fun _ => hbx)
    (epsilon_mul_one_add_overlapShiftRatio_le he0 hehalf) (some i)

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
