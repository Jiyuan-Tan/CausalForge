import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmShiftedGridScale
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.FiniteGridSelection
import Causalean.Mathlib.Analysis.EhlichZellerMesh.Mesh

/-!
# Overlap-shifted finite approximation grid

The smallest node is `aκ`, while the rational target has pole `bκ = κaκ`.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open Polynomial
open Causalean.Mathlib.Analysis.EhlichZellerMesh
open Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

/-- The `j`-th Chebyshev–Ehlich–Zeller mesh node of order `2D`, rescaled by the
affine map that sends `[-1, 1]` onto the interval from the smallest grid node
`a` to `1`.  These are the oversampling nodes on which polynomial approximation
error is controlled. -/
noncomputable def oneArmShiftedAffineMeshNode (κ : ℝ) (D j : ℕ) : ℝ :=
  let a := oneArmShiftedNodeScale κ D
  (1 + a) / 2 + (1 - a) / 2 * czNode (2 * D) j

/-- The finite approximation grid of `2D + 4` points: the three special small
nodes `a`, `2a`, `3a` (where `a` is the smallest grid node) that carry the
three-point obstruction, followed by the `2D + 1` affine Chebyshev mesh nodes
that pin down the polynomial's size on the whole interval. -/
noncomputable def oneArmShiftedSelectionGrid (κ : ℝ) (D : ℕ) :
    Fin (2 * D + 4) → ℝ := fun i =>
  if i.1 < 3 then (i.1 + 1 : ℕ) * oneArmShiftedNodeScale κ D
  else oneArmShiftedAffineMeshNode κ D (i.1 - 3)

/-- The target function evaluated on the grid: at a node `x` it is the value
`x / (x + b)` of the rational function with pole at `-b`, where `b` is the
calibrated pole location.  This is the function the reciprocal-plus-polynomial
space must fail to approximate. -/
noncomputable def oneArmShiftedSelectionTarget (κ : ℝ) (D : ℕ) :
    Fin (2 * D + 4) → ℝ := fun i =>
  oneArmShiftedSelectionGrid κ D i /
    (oneArmShiftedSelectionGrid κ D i + oneArmShiftedPoleScale κ D)

/-- The approximating family on the grid, indexed by `D + 2` functions: the
reciprocal `1/x` together with the monomials `1, x, …, x^D`.  Its span is the
set of functions a prior can match through its reciprocal moment and its first
`D` ordinary moments. -/
noncomputable def oneArmShiftedSelectionBasis (κ : ℝ) (D : ℕ) :
    Fin (D + 2) → Fin (2 * D + 4) → ℝ := fun j i =>
  if j.1 = 0 then (oneArmShiftedSelectionGrid κ D i)⁻¹
  else (oneArmShiftedSelectionGrid κ D i) ^ (j.1 - 1)

/-- Every affine mesh node lies between the smallest grid node and `1`. -/
lemma oneArmShiftedAffineMeshNode_mem_Icc
    {κ : ℝ} {D j : ℕ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D) :
    oneArmShiftedAffineMeshNode κ D j ∈
      Set.Icc (oneArmShiftedNodeScale κ D) 1 := by
  let a := oneArmShiftedNodeScale κ D
  have ha0 : 0 ≤ a := by dsimp [a, oneArmShiftedNodeScale]; positivity
  have ha1 : a ≤ 1 := by
    linarith [oneArmShiftedNodeScale_three_le_one hκ.le hκ1 hD]
  have hz := czNode_mem_Icc (2 * D) j
  dsimp [oneArmShiftedAffineMeshNode]
  change a ≤ (1 + a) / 2 + (1 - a) / 2 * czNode (2 * D) j ∧
    (1 + a) / 2 + (1 - a) / 2 * czNode (2 * D) j ≤ 1
  constructor
  · have := mul_le_mul_of_nonneg_left hz.1
      (div_nonneg (sub_nonneg.mpr ha1) (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  · have := mul_le_mul_of_nonneg_left hz.2
      (div_nonneg (sub_nonneg.mpr ha1) (by norm_num : (0 : ℝ) ≤ 2))
    linarith

/-- The first three grid points are exactly `a`, `2a` and `3a`, where `a` is the
smallest grid node. -/
lemma oneArmShiftedSelectionGrid_special (κ : ℝ) (D : ℕ) (r : Fin 3) :
    oneArmShiftedSelectionGrid κ D ⟨r.1, by omega⟩ =
      ((r.1 + 1 : ℕ) : ℝ) * oneArmShiftedNodeScale κ D := by
  simp [oneArmShiftedSelectionGrid, r.2]

/-- Past the three special points, grid point number `j + 3` is the `j`-th
affine mesh node. -/
lemma oneArmShiftedSelectionGrid_mesh (κ : ℝ) (D j : ℕ) (hj : j ≤ 2 * D) :
    oneArmShiftedSelectionGrid κ D ⟨j + 3, by omega⟩ =
      oneArmShiftedAffineMeshNode κ D j := by
  simp [oneArmShiftedSelectionGrid]

/-- Every point of the finite grid — special or mesh — lies between the smallest
grid node and `1`. -/
lemma oneArmShiftedSelectionGrid_mem_Icc
    {κ : ℝ} {D : ℕ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D)
    (i : Fin (2 * D + 4)) :
    oneArmShiftedSelectionGrid κ D i ∈
      Set.Icc (oneArmShiftedNodeScale κ D) 1 := by
  by_cases hi : i.1 < 3
  · rw [oneArmShiftedSelectionGrid]
    simp only [hi, if_true]
    have ha0 : 0 ≤ oneArmShiftedNodeScale κ D := by
      unfold oneArmShiftedNodeScale
      positivity
    constructor
    · have hc : (1 : ℝ) ≤ (i.1 + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
      nlinarith
    · have hc : (((i.1 + 1 : ℕ) : ℝ)) ≤ 3 := by exact_mod_cast hi
      exact (mul_le_mul_of_nonneg_right hc ha0).trans
        (oneArmShiftedNodeScale_three_le_one hκ.le hκ1 hD)
  · rw [oneArmShiftedSelectionGrid]
    simp only [hi, if_false]
    exact oneArmShiftedAffineMeshNode_mem_Icc hκ hκ1 hD

/-- A degree-`D` polynomial that approximates the rational-plus-reciprocal
target to within `e` at every affine mesh node is uniformly bounded on the whole
interval from the smallest node to `1`, by twice `1 + |alpha/a| + e`.  This is
the Ehlich–Zeller oversampling step: control at `2D + 1` mesh points upgrades to
control everywhere. -/
lemma oneArmShifted_mesh_polynomial_bound
    {D : ℕ} (hD : 1 ≤ D) {κ alpha e : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {P : Polynomial ℝ} (hdeg : P.natDegree ≤ D)
    (hmesh : ∀ j ∈ Finset.range (2 * D + 1),
      |oneArmShiftedAffineMeshNode κ D j /
          (oneArmShiftedAffineMeshNode κ D j + oneArmShiftedPoleScale κ D) +
        alpha / oneArmShiftedAffineMeshNode κ D j -
          P.eval (oneArmShiftedAffineMeshNode κ D j)| ≤ e) :
    ∀ x ∈ Set.Icc (oneArmShiftedNodeScale κ D) 1,
      |P.eval x| ≤ 2 * (1 + |alpha / oneArmShiftedNodeScale κ D| + e) := by
  let a := oneArmShiftedNodeScale κ D
  let b := oneArmShiftedPoleScale κ D
  let R := oneArmAffinePoly P a
  let B := 1 + |alpha / a| + e
  have ha0 : 0 ≤ a := by dsimp [a, oneArmShiftedNodeScale]; positivity
  have hb0 : 0 ≤ b := by dsimp [b, oneArmShiftedPoleScale]; positivity
  have ha1 : a ≤ 1 := by linarith [oneArmShiftedNodeScale_three_le_one hκ.le hκ1 hD]
  have hB0 : 0 ≤ B := by
    have he0 : 0 ≤ e := (abs_nonneg _).trans (hmesh 0 (by simp))
    dsimp [B]
    positivity
  have hnode (j : ℕ) (hj : j ∈ Finset.range (2 * D + 1)) :
      |R.eval (czNode (2 * D) j)| ≤ B := by
    let x := oneArmShiftedAffineMeshNode κ D j
    have hx := oneArmShiftedAffineMeshNode_mem_Icc hκ hκ1 hD (j := j)
    have hrat : 0 ≤ x / (x + b) ∧ x / (x + b) ≤ 1 := by
      have hx0 : 0 ≤ x := ha0.trans hx.1
      have hden : 0 < x + b := by
        have hapos : 0 < a := oneArmShiftedNodeScale_pos hκ hD
        exact add_pos_of_pos_of_nonneg (hapos.trans_le hx.1) hb0
      exact ⟨div_nonneg hx0 hden.le, (div_le_one hden).2 (by linarith)⟩
    have halpha : |alpha / x| ≤ |alpha / a| := by
      have ha : 0 < a := oneArmShiftedNodeScale_pos hκ hD
      have hxpos := ha.trans_le hx.1
      rw [abs_div, abs_div, abs_of_pos hxpos, abs_of_pos ha]
      exact div_le_div_of_nonneg_left (abs_nonneg alpha) ha hx.1
    have hp := hmesh j hj
    have ht : |x / (x + b) + alpha / x| ≤ 1 + |alpha / a| := by
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hrat.1]; exact add_le_add hrat.2 halpha)
    have : |P.eval x| ≤ B := by
      have hd : P.eval x = (x / (x + b) + alpha / x) -
          (x / (x + b) + alpha / x - P.eval x) := by ring
      rw [hd]
      exact (abs_sub _ _).trans (by simpa [B] using add_le_add ht hp)
    simpa [R, x, a, oneArmAffinePoly_eval, oneArmShiftedAffineMeshNode] using this
  have hmeshMax : czMeshMax R (2 * D) ≤ B := by
    rw [czMeshMax]
    apply Real.iSup_le
    · intro j
      apply Real.iSup_le
      · intro hj; exact hnode j hj
      · exact hB0
    · exact hB0
  have hnorm := oversampled_norming R D (2 * D) 2 (by norm_num) hD
    (oneArmAffinePoly_natDegree_le P a D hdeg) (by norm_num)
  have hcoef : 1 / Real.cos (Real.pi / (2 * (2 : ℝ))) ≤ 2 := by
    rw [show Real.pi / (2 * (2 : ℝ)) = Real.pi / 4 by ring, Real.cos_pi_div_four,
      one_div_div]
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  let y := (2 * x - (1 + a)) / (1 - a)
  have hden : 0 < 1 - a := by
    have ha3 := oneArmShiftedNodeScale_three_le_one hκ.le hκ1 hD
    have hapos := oneArmShiftedNodeScale_pos hκ hD
    nlinarith
  have hy : y ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp [y]
    constructor
    · rw [le_div_iff₀ hden]; linarith [hx.1]
    · rw [div_le_iff₀ hden]; linarith [hx.2]
  have heval : R.eval y = P.eval x := by
    rw [show R = oneArmAffinePoly P a by rfl, oneArmAffinePoly_eval]
    congr 1
    dsimp [y]
    field_simp [ne_of_gt hden]
    ring
  have hpoint : |R.eval y| ≤ sSup ((fun z => |R.eval z|) '' Set.Icc (-1 : ℝ) 1) := by
    apply le_csSup
    · exact isCompact_Icc.bddAbove_image R.continuous.abs.continuousOn
    · exact ⟨y, hy, rfl⟩
  rw [← heval]
  exact hpoint.trans (hnorm.trans ((mul_le_mul hcoef hmeshMax
    (czMeshMax_nonneg R (2 * D)) (by positivity)).trans_eq (by ring)))

/-- The shifted selected grid retains a positive approximation obstruction;
its size is allowed to depend on the fixed overlap ratio `κ`. -/
theorem oneArmShiftedSelectionGrid_approximation_lower
    (D : ℕ) (hD : 1 ≤ D) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (alpha e : ℝ) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ D)
    (hgrid : ∀ i : Fin (2 * D + 4),
      |oneArmShiftedSelectionTarget κ D i +
        alpha / oneArmShiftedSelectionGrid κ D i -
          P.eval (oneArmShiftedSelectionGrid κ D i)| ≤ e) :
    (2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))) / 20 ≤ e := by
  let a := oneArmShiftedNodeScale κ D
  let b := oneArmShiftedPoleScale κ D
  let U := |alpha / a|
  let B := 2 * (1 + U + e)
  let S := 2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))
  have ha0 : 0 < a := oneArmShiftedNodeScale_pos hκ hD
  have ha3 : 3 * a ≤ 1 := oneArmShiftedNodeScale_three_le_one hκ.le hκ1 hD
  have hκ0 : 0 ≤ κ := hκ.le
  have hκ2 : κ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hκ0 (sub_nonneg.mpr hκ1)]
  have hdenpos : 0 < (1 + κ) * (2 + κ) * (3 + κ) := by positivity
  have hdenle : (1 + κ) * (2 + κ) * (3 + κ) ≤ 24 := by nlinarith
  have hSge : κ ^ 2 / 12 ≤ S := by
    dsimp [S]
    rw [show κ ^ 2 / 12 = (2 * κ ^ 2) / 24 by ring]
    exact div_le_div_of_nonneg_left (by positivity) hdenpos hdenle
  have hSle : S ≤ κ ^ 2 := by
    dsimp [S]
    rw [div_le_iff₀ hdenpos]
    have : 2 ≤ (1 + κ) * (2 + κ) * (3 + κ) := by nlinarith
    nlinarith [sq_nonneg κ]
  have hspecial (r : Fin 3) :
      |(((r.1 + 1 : ℕ) : ℝ) * a) /
          ((((r.1 + 1 : ℕ) : ℝ) * a) + b) +
        alpha / (((r.1 + 1 : ℕ) : ℝ) * a) -
          P.eval (((r.1 + 1 : ℕ) : ℝ) * a)| ≤ e := by
    simpa [oneArmShiftedSelectionTarget, a, b,
      oneArmShiftedSelectionGrid_special] using hgrid ⟨r.1, by omega⟩
  have he0 : 0 ≤ e := (abs_nonneg _).trans (hspecial 0)
  have hU0 : 0 ≤ U := abs_nonneg _
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hmesh : ∀ j ∈ Finset.range (2 * D + 1),
      |oneArmShiftedAffineMeshNode κ D j /
          (oneArmShiftedAffineMeshNode κ D j + b) +
        alpha / oneArmShiftedAffineMeshNode κ D j -
          P.eval (oneArmShiftedAffineMeshNode κ D j)| ≤ e := by
    intro j hj
    have hjlt : j < 2 * D + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ 2 * D := by omega
    simpa [oneArmShiftedSelectionTarget, b,
      oneArmShiftedSelectionGrid_mesh κ D j hjle] using
        hgrid ⟨j + 3, by omega⟩
  have hP : ∀ x ∈ Set.Icc a 1, |P.eval x| ≤ B := by
    simpa [a, B, U] using
      oneArmShifted_mesh_polynomial_bound hD hκ hκ1 hdeg hmesh
  have hang := oneArm_shifted_calibrated_angular_scale D hD hκ.le hκ1
  change (D : ℝ) * Real.sqrt (4 * a / (1 - a)) ≤ κ ^ 2 / 10000 at hang
  have hsqrt : Real.sqrt (2 * a / (1 - a)) ≤
      Real.sqrt (4 * a / (1 - a)) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by nlinarith) (by nlinarith : 0 ≤ 1 - a)
  have h12raw := oneArm_poly_two_mul_variation ha0 ha3 hdeg hP
  have h13raw := oneArm_poly_three_mul_variation ha0 ha3 hdeg hP
  have h12 : |P.eval a - P.eval (2 * a)| ≤ 4 * B * κ ^ 2 / 10000 := by
    calc
      _ ≤ 4 * (D : ℝ) * B * Real.sqrt (2 * a / (1 - a)) := h12raw
      _ ≤ 4 * B * ((D : ℝ) * Real.sqrt (4 * a / (1 - a))) := by
        have := mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4) (by positivity)) hB0)
        nlinarith
      _ ≤ 4 * B * (κ ^ 2 / 10000) :=
        mul_le_mul_of_nonneg_left hang (mul_nonneg (by norm_num) hB0)
      _ = _ := by ring
  have h13 : |P.eval a - P.eval (3 * a)| ≤ 4 * B * κ ^ 2 / 10000 := by
    calc
      _ ≤ 4 * (D : ℝ) * B * Real.sqrt (4 * a / (1 - a)) := h13raw
      _ = 4 * B * ((D : ℝ) * Real.sqrt (4 * a / (1 - a))) := by ring
      _ ≤ 4 * B * (κ ^ 2 / 10000) :=
        mul_le_mul_of_nonneg_left hang (mul_nonneg (by norm_num) hB0)
      _ = _ := by ring
  have h32 : |P.eval (3 * a) - P.eval (2 * a)| ≤ 8 * B * κ ^ 2 / 10000 := by
    have hd : P.eval (3 * a) - P.eval (2 * a) =
        (P.eval (3 * a) - P.eval a) + (P.eval a - P.eval (2 * a)) := by ring
    rw [hd]
    calc
      _ ≤ |P.eval (3 * a) - P.eval a| + |P.eval a - P.eval (2 * a)| := abs_add_le _ _
      _ ≤ 4 * B * κ ^ 2 / 10000 + 4 * B * κ ^ 2 / 10000 := by
        rw [abs_sub_comm (P.eval (3 * a))]
        exact add_le_add h13 h12
      _ = _ := by ring
  have hobs := oneArm_shifted_rational_three_point_obstruction
    (a := a) (κ := κ) (alpha := alpha) (e := e)
    (V := 8 * B * κ ^ 2 / 10000) (ne_of_gt ha0)
    (by positivity) (by positivity) (by positivity) hκ.le (fun x => P.eval x)
    (by simpa [b, oneArmShiftedPoleScale] using hspecial 0)
    (by simpa [b, oneArmShiftedPoleScale] using hspecial 1)
    (by simpa [b, oneArmShiftedPoleScale] using hspecial 2)
    (h12.trans (by nlinarith [hB0, sq_nonneg κ])) h32
  change S ≤ 8 * e + 4 * (8 * B * κ ^ 2 / 10000) at hobs
  let f : ℝ → ℝ := fun x => x / (x + b) + alpha / x
  have hf : f a - f (2 * a) = alpha / a / 2 - κ / ((1 + κ) * (2 + κ)) := by
    change a / (a + b) + alpha / a -
        ((2 * a) / (2 * a + b) + alpha / (2 * a)) = _
    rw [show b = κ * a by rfl]
    field_simp [ne_of_gt ha0, show (1 + κ) ≠ 0 by positivity,
      show (2 + κ) ≠ 0 by positivity]
    ring
  have hlower : U / 2 - 1 / 2 ≤ |f a - f (2 * a)| := by
    rw [hf]
    have habsdiv : |alpha / a / 2| = U / 2 := by simp [U, abs_div]
    have hrat : |κ / ((1 + κ) * (2 + κ))| ≤ 1 / 2 := by
      rw [abs_of_nonneg (div_nonneg hκ.le (by positivity))]
      rw [div_le_iff₀ (by positivity : 0 < (1 + κ) * (2 + κ))]
      nlinarith
    calc
      U / 2 - 1 / 2 ≤ U / 2 - |κ / ((1 + κ) * (2 + κ))| :=
        sub_le_sub_left hrat (U / 2)
      _ = |alpha / a / 2| - |κ / ((1 + κ) * (2 + κ))| := by rw [habsdiv]
      _ ≤ |alpha / a / 2 - κ / ((1 + κ) * (2 + κ))| :=
        abs_sub_abs_le_abs_sub _ _
  have hupper : |f a - f (2 * a)| ≤ 2 * e + 4 * B * κ ^ 2 / 10000 := by
    have hd : f a - f (2 * a) = (f a - P.eval a) +
        (P.eval a - P.eval (2 * a)) - (f (2 * a) - P.eval (2 * a)) := by ring
    rw [hd]
    calc
      _ ≤ |f a - P.eval a| + |P.eval a - P.eval (2 * a)| +
          |P.eval (2 * a) - f (2 * a)| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_three (f a - P.eval a) (P.eval a - P.eval (2 * a))
            (-(f (2 * a) - P.eval (2 * a)))
      _ = |f a - P.eval a| + |P.eval a - P.eval (2 * a)| +
          |f (2 * a) - P.eval (2 * a)| := by rw [abs_sub_comm (P.eval (2 * a))]
      _ ≤ e + 4 * B * κ ^ 2 / 10000 + e := by
        exact add_le_add (add_le_add (by simpa [f] using hspecial 0) h12)
          (by simpa [f] using hspecial 1)
      _ = _ := by ring
  have hU : U ≤ 2 + 10 * e := by
    dsimp [B] at hupper
    nlinarith [hlower.trans hupper]
  dsimp [B] at hobs
  change S / 20 ≤ e
  nlinarith [hobs, hSge, hSle]

/-- A linear combination of the basis functions splits at each grid point into
the reciprocal term `c₀ / x` plus the value at `x` of the polynomial whose
coefficients are the remaining entries of `c`. -/
lemma oneArmShiftedSelectionBasis_sum_eq
    (κ : ℝ) (D : ℕ) (c : Fin (D + 2) → ℝ) (i : Fin (2 * D + 4)) :
    ∑ j, c j * oneArmShiftedSelectionBasis κ D j i =
      c 0 / oneArmShiftedSelectionGrid κ D i +
        (oneArmSelectionPolynomial D c).eval (oneArmShiftedSelectionGrid κ D i) := by
  classical
  let x := oneArmShiftedSelectionGrid κ D i
  calc
    ∑ j, c j * oneArmShiftedSelectionBasis κ D j i =
        c 0 * x⁻¹ + ∑ j ∈ Finset.univ.erase (0 : Fin (D + 2)),
          c j * x ^ (j.1 - 1) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j => c j * oneArmShiftedSelectionBasis κ D j i)
        (Finset.mem_univ (0 : Fin (D + 2)))]
      simp only [oneArmShiftedSelectionBasis, Fin.isValue, Fin.val_zero, if_pos,
        Nat.cast_one, one_mul, x]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj0 : j.1 ≠ 0 := by
        intro h
        exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
      simp [oneArmShiftedSelectionBasis, hj0, x]
    _ = c 0 / x + (oneArmSelectionPolynomial D c).eval x := by
      rw [div_eq_mul_inv]
      congr 1
      calc
        ∑ j ∈ Finset.univ.erase (0 : Fin (D + 2)), c j * x ^ (j.1 - 1) =
            ∑ j ∈ Finset.univ.erase (0 : Fin (D + 2)),
              (if j.1 = 0 then 0
                else Polynomial.C (c j) * Polynomial.X ^ (j.1 - 1)).eval x := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj0 : j.1 ≠ 0 := by
            intro h
            exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
          simp [hj0]
        _ = ∑ j : Fin (D + 2), (if j.1 = 0 then 0
              else Polynomial.C (c j) * Polynomial.X ^ (j.1 - 1)).eval x := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (D + 2)))]
          simp
        _ = (oneArmSelectionPolynomial D c).eval x := by
          rw [oneArmSelectionPolynomial, Polynomial.eval_finset_sum]
    _ = _ := rfl

/-- The shifted reciprocal-monomial space has a positive best approximation
error equal to a fixed positive function of `κ`. -/
theorem oneArmShiftedSelectionGrid_bestError_lower
    (D : ℕ) (hD : 1 ≤ D) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))) / 20 ≤
      finiteGridBestError
        (finiteGridBasisEval (oneArmShiftedSelectionBasis κ D))
        (oneArmShiftedSelectionTarget κ D) := by
  apply le_csInf (finiteGridErrorSet_nonempty _ _)
  rintro e ⟨c, rfl⟩
  let P := oneArmSelectionPolynomial D c
  apply oneArmShiftedSelectionGrid_approximation_lower D hD hκ hκ1 (-c 0)
    (ninf (oneArmShiftedSelectionTarget κ D -
      finiteGridBasisEval (oneArmShiftedSelectionBasis κ D) c)) P
    (oneArmSelectionPolynomial_natDegree_le D c)
  intro i
  have hi := le_ninf
    (oneArmShiftedSelectionTarget κ D -
      finiteGridBasisEval (oneArmShiftedSelectionBasis κ D) c) i
  change |oneArmShiftedSelectionTarget κ D i -
    ∑ j, c j * oneArmShiftedSelectionBasis κ D j i| ≤ _ at hi
  rw [oneArmShiftedSelectionBasis_sum_eq] at hi
  simpa [P, sub_eq_add_neg, div_eq_mul_inv, add_assoc, add_comm, add_left_comm] using hi

/-- The constant function `1` lies in the span of the basis: taking the
coefficient vector that selects the degree-zero monomial reproduces `1` at every
grid point.  This is what lets the Jordan decomposition of a signed weight
vector be normalized into two probability measures. -/
lemma oneArmShiftedSelectionBasis_contains_one (κ : ℝ) (D : ℕ) :
    finiteGridBasisEval (oneArmShiftedSelectionBasis κ D)
      (oneArmSelectionConstantCoeff D) = fun _ => 1 := by
  classical
  ext i
  rw [finiteGridBasisEval_apply,
    Fintype.sum_eq_single (⟨1, by omega⟩ : Fin (D + 2))]
  · simp [oneArmSelectionConstantCoeff, oneArmShiftedSelectionBasis]
  · intro j hj
    have hval : j.1 ≠ 1 := by
      intro h
      exact hj (Fin.ext h)
    simp [oneArmSelectionConstantCoeff, hval]

/-- Jordan PMFs on the shifted selected grid match the reciprocal and all
ordinary moments through degree `D`, while retaining a positive target gap. -/
theorem exists_oneArmShiftedSelectionGrid_jordan_priors
    (D : ℕ) (hD : 1 ≤ D) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ (w : Fin (2 * D + 4) → ℝ)
      (hzero : ∑ i, w i = 0)
      (hmass : 0 < positiveJordanMass w),
      (∑ i, |w i| ≤ 1) ∧
      (∀ c,
        ∑ i, (positiveJordanPMF w hmass i).toReal *
            finiteGridBasisEval (oneArmShiftedSelectionBasis κ D) c i =
          ∑ i, (negativeJordanPMF w
            (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
              finiteGridBasisEval (oneArmShiftedSelectionBasis κ D) c i) ∧
      (2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))) / 10 ≤
        (∑ i, (positiveJordanPMF w hmass i).toReal *
            oneArmShiftedSelectionTarget κ D i) -
          ∑ i, (negativeJordanPMF w
            (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
              oneArmShiftedSelectionTarget κ D i := by
  have hbest := oneArmShiftedSelectionGrid_bestError_lower D hD hκ hκ1
  have hpos : 0 < finiteGridBestError
      (finiteGridBasisEval (oneArmShiftedSelectionBasis κ D))
      (oneArmShiftedSelectionTarget κ D) := by
    have hsignal : 0 <
        (2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))) / 20 := by positivity
    exact hsignal.trans_le hbest
  obtain ⟨w, hzero, hmass, hnorm, hmom, hgap⟩ :=
    exists_finiteGrid_jordan_priors
      (finiteGridBasisEval (oneArmShiftedSelectionBasis κ D))
      (oneArmShiftedSelectionTarget κ D)
      (oneArmSelectionConstantCoeff D)
      (oneArmShiftedSelectionBasis_contains_one κ D) hpos
  refine ⟨w, hzero, hmass, hnorm, hmom, ?_⟩
  exact (by nlinarith :
    (2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))) / 10 ≤
      2 * finiteGridBestError
        (finiteGridBasisEval (oneArmShiftedSelectionBasis κ D))
        (oneArmShiftedSelectionTarget κ D)).trans hgap

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
