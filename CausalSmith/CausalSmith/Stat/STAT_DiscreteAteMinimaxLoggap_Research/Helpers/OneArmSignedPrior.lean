/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Signed finite priors for the one-arm minimax converse

This module isolates the algebraic certificate used by the moment-matching
construction.  Barycentric weights on distinct positive nodes annihilate every
required monomial, including the inverse moment after multiplying the usual
weights by the node.  It also records the exact exterior rational separation
and the elementary Jordan decomposition used to turn the signed certificate
into two finite probability vectors.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevEndpoint
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open CausalSmith.Experimentation.RolloutChebyshev

/-- The usual barycentric weight at a node of a finite, indexed node set. -/
noncomputable def barycentricWeight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (i : ι) : ℝ :=
  (∏ j ∈ s.erase i, (x i - x j))⁻¹

/-- Distinct-node barycentric weights annihilate every monomial whose degree is
at least two below the number of nodes. -/
lemma sum_barycentricWeight_mul_pow_eq_zero {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → ℝ} (hx : Set.InjOn x s) {k : ℕ}
    (hk : k + 1 < s.card) :
    ∑ i ∈ s, barycentricWeight s x i * x i ^ k = 0 := by
  let P : Polynomial ℝ := Polynomial.X ^ k
  have hdegree : P.degree < (s.card : WithBot ℕ) := by
    dsimp [P]
    rw [Polynomial.degree_X_pow]
    exact_mod_cast (Nat.lt_of_succ_lt hk)
  have hcoeff := Lagrange.coeff_eq_sum hx hdegree
  have hcoeff_zero : P.coeff (s.card - 1) = 0 := by
    dsimp [P]
    rw [Polynomial.coeff_X_pow]
    simp only [ite_eq_right_iff]
    intro h
    have : k + 1 = s.card := by omega
    omega
  rw [hcoeff_zero] at hcoeff
  simpa [P, barycentricWeight, div_eq_mul_inv, mul_comm] using hcoeff.symm

/-- Distinct-node barycentric weights annihilate evaluation of every polynomial
whose degree is at least two below the number of nodes. -/
lemma sum_barycentricWeight_mul_eval_eq_zero {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → ℝ} (hx : Set.InjOn x s) (P : Polynomial ℝ)
    (hP : P.natDegree + 1 < s.card) :
    ∑ i ∈ s, barycentricWeight s x i * P.eval (x i) = 0 := by
  have hdegree : P.degree < (s.card : WithBot ℕ) := by
    exact lt_of_le_of_lt P.degree_le_natDegree (by exact_mod_cast (Nat.lt_of_succ_lt hP))
  have hcoeff := Lagrange.coeff_eq_sum hx hdegree
  have hcoeff_zero : P.coeff (s.card - 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  rw [hcoeff_zero] at hcoeff
  simpa [barycentricWeight, div_eq_mul_inv, mul_comm] using hcoeff.symm

/-- Multiplying each barycentric weight by its positive node shifts the
annihilated moment range down by one, so the exponent `-1` becomes the ordinary
zeroth barycentric identity. -/
lemma sum_nodeBarycentricWeight_mul_zpow_eq_zero {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → ℝ} (hx : Set.InjOn x s)
    (hxpos : ∀ i ∈ s, 0 < x i) {ell : ℤ}
    (hell_lo : -(1 : ℤ) ≤ ell) (hell_hi : ell + 2 < s.card) :
    ∑ i ∈ s, (x i * barycentricWeight s x i) * x i ^ ell = 0 := by
  let k : ℕ := (ell + 1).toNat
  have hell_nonneg : 0 ≤ ell + 1 := by omega
  have hkcast : (k : ℤ) = ell + 1 := by
    simp [k, Int.toNat_of_nonneg hell_nonneg]
  have hk : k + 1 < s.card := by
    have hk' : (k : ℤ) + 1 < (s.card : ℤ) := by omega
    exact_mod_cast hk'
  have hcancel := sum_barycentricWeight_mul_pow_eq_zero hx hk
  rw [← hcancel]
  apply Finset.sum_congr rfl
  intro i hi
  have hxi : x i ≠ 0 := ne_of_gt (hxpos i hi)
  calc
    (x i * barycentricWeight s x i) * x i ^ ell =
        barycentricWeight s x i * (x i ^ (1 : ℤ) * x i ^ ell) := by
          rw [zpow_one]
          ring
    _ = barycentricWeight s x i * x i ^ ((1 : ℤ) + ell) := by
          rw [zpow_add₀ hxi]
    _ = barycentricWeight s x i * x i ^ k := by
          rw [show (1 : ℤ) + ell = k by omega]
          simp

/-- Exact resolvent identity for barycentric weights at a point exterior to all
nodes. -/
lemma sum_barycentricWeight_div_sub_eq_inv_prod {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → ℝ} (hs : s.Nonempty) (hx : Set.InjOn x s) {z : ℝ}
    (hz : ∀ i ∈ s, z ≠ x i) :
    ∑ i ∈ s, barycentricWeight s x i / (z - x i) =
      (∏ i ∈ s, (z - x i))⁻¹ := by
  have h := Lagrange.eval_interpolate_not_at_node (s := s) (v := x)
    (r := fun _ => (1 : ℝ)) hz
  have hsum : Lagrange.interpolate s x (fun _ => (1 : ℝ)) = 1 := by
    have hconst := Lagrange.eq_interpolate (f := (1 : Polynomial ℝ)) hx (by simp [hs])
    simpa using hconst.symm
  rw [hsum] at h
  simp only [Polynomial.eval_one, Lagrange.eval_nodal] at h
  have hprod_ne : ∏ i ∈ s, (z - x i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (hz i hi)
  apply eq_inv_of_mul_eq_one_left
  simpa [barycentricWeight, Lagrange.nodalWeight, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]
    using h.symm

/-- Exact separation of the rational functional used in the one-arm fuzzy
hypotheses.  Multiplying the resolvent by `a` produces the source formula
`a^2 / prod_i (x_i+a)`, up to the explicit parity sign retained here by writing
the denominator as `prod_i (-a-x_i)`. -/
lemma nodeBarycentric_rational_separation {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → ℝ} (hs : s.Nonempty) (hx : Set.InjOn x s)
    (hcard : 1 < s.card) {a : ℝ} (ha : 0 < a)
    (hxpos : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, (x i * barycentricWeight s x i) * (a / (x i + a)) =
      a ^ 2 * (∏ i ∈ s, (-a - x i))⁻¹ := by
  have hcancel : ∑ i ∈ s, barycentricWeight s x i = 0 := by
    have h := sum_barycentricWeight_mul_pow_eq_zero hx (k := 0) (by omega)
    simpa using h
  have hz : ∀ i ∈ s, -a ≠ x i := by
    intro i hi hax
    have := hxpos i hi
    linarith
  have hres := sum_barycentricWeight_div_sub_eq_inv_prod hs hx hz
  have hres' :
      ∑ i ∈ s, barycentricWeight s x i / (x i + a) =
        -(∏ i ∈ s, (-a - x i))⁻¹ := by
    calc
      ∑ i ∈ s, barycentricWeight s x i / (x i + a) =
          -(∑ i ∈ s, barycentricWeight s x i / (-a - x i)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            have hden : x i + a ≠ 0 := ne_of_gt (add_pos (hxpos i hi) ha)
            rw [show -a - x i = -(x i + a) by ring]
            field_simp
      _ = -(∏ i ∈ s, (-a - x i))⁻¹ := by rw [hres]
  calc
    ∑ i ∈ s, (x i * barycentricWeight s x i) * (a / (x i + a)) =
        ∑ i ∈ s, (a * barycentricWeight s x i -
          a ^ 2 * (barycentricWeight s x i / (x i + a))) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hden : x i + a ≠ 0 := ne_of_gt (add_pos (hxpos i hi) ha)
            field_simp
            ring
    _ = a * (∑ i ∈ s, barycentricWeight s x i) -
          a ^ 2 * (∑ i ∈ s, barycentricWeight s x i / (x i + a)) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = a ^ 2 * (∏ i ∈ s, (-a - x i))⁻¹ := by rw [hcancel, hres']; ring

/-- At a point to the right of the Chebyshev interval, the total absolute
Lagrange interpolation mass on the Lobatto nodes is exactly the exterior
Chebyshev value.  This packages the sign computation from
`chebyshev_exterior_lagrange_coeff_nonneg` in the form needed to control the
Jordan mass of the signed prior. -/
lemma chebyshev_exterior_lagrange_abs_sum_eq (n : ℕ) (x0 : ℝ) (hx0 : 1 < x0) :
    ∑ i ∈ Finset.Iic n,
        |(Lagrange.basis (Finset.Iic n) (Polynomial.Chebyshev.node n) i).eval x0| =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x0 := by
  classical
  let s : Finset ℕ := Finset.Iic n
  let v : ℕ → ℝ := Polynomial.Chebyshev.node n
  let T : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hvs : Set.InjOn v s := by
    simpa [s, v, Nat.range_succ_eq_Iic] using
      (Polynomial.Chebyshev.strictAntiOn_node n).injOn
  have hcard : s.card = n + 1 := by simp [s]
  have hTdegree : T.degree < (s.card : WithBot ℕ) := by
    dsimp [T]
    rw [hcard, Polynomial.Chebyshev.degree_T, Int.natAbs_natCast]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n)
  have hTinterp := Lagrange.eq_interpolate hvs hTdegree
  have hTeval :
      T.eval x0 = ∑ i ∈ s, T.eval (v i) * (Lagrange.basis s v i).eval x0 := by
    have h := congrArg (fun R : Polynomial ℝ => R.eval x0) hTinterp
    simpa [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  rw [hTeval]
  apply Finset.sum_congr rfl
  intro i hi
  have hsign :
      0 ≤ (-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0 := by
    simpa [s, v] using
      chebyshev_exterior_lagrange_coeff_nonneg (n := n) (i := i)
        (by simpa [s] using hi) hx0
  have habs :
      |(Lagrange.basis s v i).eval x0| =
        (-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0 := by
    calc
      |(Lagrange.basis s v i).eval x0| =
          |(-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0| := by
            rw [abs_mul, abs_neg_one_pow, one_mul]
      _ = _ := abs_of_nonneg hsign
  rw [habs]
  change (-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0 =
    (Polynomial.Chebyshev.T ℝ (n : ℕ)).eval
      (Polynomial.Chebyshev.node n i) * (Lagrange.basis s v i).eval x0
  rw [Polynomial.Chebyshev.eval_T_real_node (by simpa [s] using hi)]

/-- Lagrange basis evaluations are invariant under a common nondegenerate
affine change of all nodes and of the evaluation point. -/
lemma lagrange_basis_eval_affine {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → ℝ} (hx : Set.InjOn x s) {i : ι} (hi : i ∈ s)
    (c r z : ℝ) (hr : r ≠ 0) :
    (Lagrange.basis s (fun j => c + r * x j) i).eval (c + r * z) =
      (Lagrange.basis s x i).eval z := by
  rw [Lagrange.basis, Lagrange.basis, Polynomial.eval_prod, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hjmem : j ∈ s := (Finset.mem_erase.mp hj).2
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hxne : x i ≠ x j := by
    intro h
    exact hji (hx hi hjmem h).symm
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  rw [show c + r * z - (c + r * x j) = r * (z - x j) by ring,
    show c + r * x i - (c + r * x j) = r * (x i - x j) by ring]
  field_simp [hr, hxne]

/-- Clearing the exterior nodal product converts a barycentric weight into the
corresponding Lagrange coefficient. -/
lemma prod_sub_mul_nodeBarycentricWeight_eq {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → ℝ} {i : ι} (hi : i ∈ s) {z : ℝ} (hzi : z ≠ x i) :
    (∏ j ∈ s, (z - x j)) * (x i * barycentricWeight s x i) =
      (z - x i) * x i * (Lagrange.basis s x i).eval z := by
  rw [Lagrange.eval_basis_not_at_node hi hzi]
  simp only [Lagrange.eval_nodal]
  unfold barycentricWeight Lagrange.nodalWeight
  field_simp [hzi]
  simp only [div_eq_mul_inv]
  rw [← Finset.prod_inv_distrib]
  simp

/-- The increasing Chebyshev--Lobatto grid on `[a,1]` used by the signed-prior
certificate. -/
noncomputable def oneArmLobattoNode (n : ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  (1 + a) / 2 - ((1 - a) / 2) * Polynomial.Chebyshev.node n i

/-- The standard-coordinate image of the exterior point `-a` for the affine
grid on `[a,1]`. -/
noncomputable def oneArmLobattoExterior (a : ℝ) : ℝ :=
  (1 + 3 * a) / (1 - a)

/-- Every Chebyshev–Lobatto node of the grid lies between the left endpoint `a`
and `1`. -/
lemma oneArmLobattoNode_in_Icc {n i : ℕ} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    oneArmLobattoNode n a i ∈ Set.Icc a 1 := by
  have hnode := Polynomial.Chebyshev.node_mem_Icc (n := n) (i := i)
  have hscale : 0 ≤ (1 - a) / 2 := by linarith
  have hlower : ((1 - a) / 2) * Polynomial.Chebyshev.node n i ≤ (1 - a) / 2 :=
    mul_le_of_le_one_right hscale hnode.2
  have hupper : -((1 - a) / 2) ≤
      ((1 - a) / 2) * Polynomial.Chebyshev.node n i := by
    nlinarith [mul_le_mul_of_nonneg_left hnode.1 hscale]
  unfold oneArmLobattoNode
  constructor <;> linarith

/-- The first `n + 1` grid nodes are pairwise distinct, so the barycentric
weights and Lagrange bases attached to them are well defined. -/
lemma oneArmLobattoNode_injectiveOn (n : ℕ) {a : ℝ} (ha1 : a < 1) :
    Set.InjOn (oneArmLobattoNode n a) (Finset.Iic n) := by
  intro i hi j hj hij
  have hscale : (1 - a) / 2 ≠ 0 := by positivity
  have hnodes : Polynomial.Chebyshev.node n i = Polynomial.Chebyshev.node n j := by
    unfold oneArmLobattoNode at hij
    apply (mul_left_cancel₀ hscale)
    linarith
  have hi' : i ∈ Finset.range (n + 1) := by simpa [Nat.range_succ_eq_Iic] using hi
  have hj' : j ∈ Finset.range (n + 1) := by simpa [Nat.range_succ_eq_Iic] using hj
  exact (Polynomial.Chebyshev.strictAntiOn_node n).injOn hi' hj' hnodes

/-- The exterior point lies strictly outside the standard interval: its standard
coordinate exceeds `1` whenever the left endpoint lies in `(0,1)`. -/
lemma oneArmLobattoExterior_gt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    1 < oneArmLobattoExterior a := by
  unfold oneArmLobattoExterior
  rw [lt_div_iff₀ (sub_pos.mpr ha1)]
  linarith

/-- The affine map carrying the standard interval onto `[a,1]` sends the
exterior standard coordinate back to `-a`, confirming that it is the correct
preimage of the exterior evaluation point. -/
lemma oneArmLobatto_affine_exterior {a : ℝ} (ha1 : a < 1) :
    (1 + a) / 2 - ((1 - a) / 2) * oneArmLobattoExterior a = -a := by
  unfold oneArmLobattoExterior
  field_simp [ne_of_gt (sub_pos.mpr ha1)]
  ring

/-- Exact Lagrange-mass formula for the shifted grid at the exterior point
`-a`. -/
lemma oneArmLobatto_lagrange_abs_sum_eq (n : ℕ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∑ i ∈ Finset.Iic n,
        |(Lagrange.basis (Finset.Iic n) (oneArmLobattoNode n a) i).eval (-a)| =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (oneArmLobattoExterior a) := by
  let c : ℝ := (1 + a) / 2
  let r : ℝ := -((1 - a) / 2)
  let z : ℝ := oneArmLobattoExterior a
  have hr : r ≠ 0 := by
    dsimp [r]
    apply neg_ne_zero.mpr
    exact div_ne_zero (sub_ne_zero.mpr (ne_of_lt ha1).symm) (by norm_num)
  have hx : Set.InjOn (Polynomial.Chebyshev.node n) (Finset.Iic n) := by
    simpa [Nat.range_succ_eq_Iic] using
      (Polynomial.Chebyshev.strictAntiOn_node n).injOn
  have hz : c + r * z = -a := by
    simpa [c, r, z, sub_eq_add_neg] using oneArmLobatto_affine_exterior ha1
  rw [← chebyshev_exterior_lagrange_abs_sum_eq n z
    (oneArmLobattoExterior_gt_one ha0 ha1)]
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

/-- The exterior nodal product times the total variation of the raw signed
barycentric vector is bounded by twice the exterior Chebyshev value. -/
lemma oneArmLobatto_jordan_product_bound (n : ℕ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    |∏ i ∈ Finset.Iic n, (-a - oneArmLobattoNode n a i)| *
        (∑ i ∈ Finset.Iic n,
          |oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i|) ≤
      2 * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (oneArmLobattoExterior a) := by
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ Finset.Iic n,
        |∏ j ∈ Finset.Iic n, (-a - oneArmLobattoNode n a j)| *
          |oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i| =
      ∑ i ∈ Finset.Iic n,
        |(-a - oneArmLobattoNode n a i) * oneArmLobattoNode n a i *
          (Lagrange.basis (Finset.Iic n) (oneArmLobattoNode n a) i).eval (-a)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← abs_mul]
      exact congrArg abs (prod_sub_mul_nodeBarycentricWeight_eq hi (by
        have hxi := (oneArmLobattoNode_in_Icc ha0 ha1 (n := n) (i := i)).1
        linarith))
    _ ≤ ∑ i ∈ Finset.Iic n,
        2 * |(Lagrange.basis (Finset.Iic n) (oneArmLobattoNode n a) i).eval (-a)| := by
      apply Finset.sum_le_sum
      intro i hi
      have hxi := oneArmLobattoNode_in_Icc ha0 ha1 (n := n) (i := i)
      have hnonneg : 0 ≤ oneArmLobattoNode n a i := hxi.1.trans' ha0.le
      have hax : 0 ≤ a + oneArmLobattoNode n a i := add_nonneg ha0.le hnonneg
      rw [abs_mul, abs_mul, abs_of_nonneg hnonneg]
      rw [show |-a - oneArmLobattoNode n a i| =
          a + oneArmLobattoNode n a i by
        rw [abs_of_nonpos (by linarith)]
        ring]
      have hfactor : (a + oneArmLobattoNode n a i) *
          oneArmLobattoNode n a i ≤ 2 := by nlinarith [hxi.2]
      exact mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
    _ = 2 * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (oneArmLobattoExterior a) := by
      rw [← Finset.mul_sum, oneArmLobatto_lagrange_abs_sum_eq n ha0 ha1]

/-- After division by the Jordan mass, the two signed priors separate the
rational functional by at least `a^2 / T_n(x_a)`.  Choosing `a` of order
`n^{-2}` makes the exterior Chebyshev factor uniformly bounded. -/
lemma oneArmLobatto_normalized_rational_gap (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    a ^ 2 /
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (oneArmLobattoExterior a) ≤
      |(∑ i ∈ Finset.Iic n,
          (oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i) *
              (a / (oneArmLobattoNode n a i + a))) /
        ((∑ i ∈ Finset.Iic n,
          |oneArmLobattoNode n a i *
            barycentricWeight (Finset.Iic n) (oneArmLobattoNode n a) i|) / 2)| := by
  let s : Finset ℕ := Finset.Iic n
  let x : ℕ → ℝ := oneArmLobattoNode n a
  let w : ℕ → ℝ := fun i => x i * barycentricWeight s x i
  let B : ℝ := ∏ i ∈ s, (-a - x i)
  let S : ℝ := ∑ i ∈ s, |w i|
  let T : ℝ := (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (oneArmLobattoExterior a)
  have hs : s.Nonempty := by simp [s]
  have hx : Set.InjOn x s := by
    simpa [s, x] using oneArmLobattoNode_injectiveOn n ha1
  have hxpos : ∀ i ∈ s, 0 < x i := by
    intro i hi
    exact lt_of_lt_of_le ha0 (oneArmLobattoNode_in_Icc ha0 ha1).1
  have hraw : ∑ i ∈ s, w i * (a / (x i + a)) = a ^ 2 * B⁻¹ := by
    simpa [s, x, w, B] using
      nodeBarycentric_rational_separation hs hx (by simp [s]; omega) ha0 hxpos
  have hBne : B ≠ 0 := by
    dsimp [B]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have := hxpos i hi
    linarith
  have hBpos : 0 < |B| := abs_pos.mpr hBne
  have hSpos : 0 < S := by
    have hi : 0 ∈ s := by simp [s]
    have hb : barycentricWeight s x 0 ≠ 0 := by
      simpa [barycentricWeight, Lagrange.nodalWeight] using
        Lagrange.nodalWeight_ne_zero hx hi
    have hw : w 0 ≠ 0 := mul_ne_zero (ne_of_gt (hxpos 0 hi)) hb
    exact Finset.sum_pos' (fun i _ => abs_nonneg (w i)) ⟨0, hi, abs_pos.mpr hw⟩
  have hDpos : 0 < |B| * (S / 2) := mul_pos hBpos (div_pos hSpos (by norm_num))
  have hbound : |B| * S ≤ 2 * T := by
    dsimp only [s, x, w, B, S, T]
    exact oneArmLobatto_jordan_product_bound n ha0 ha1
  have hDle : |B| * (S / 2) ≤ T := by nlinarith
  have hTpos : 0 < T := lt_of_lt_of_le hDpos hDle
  have hgap : |(a ^ 2 * B⁻¹) / (S / 2)| = a ^ 2 / (|B| * (S / 2)) := by
    rw [abs_div, abs_mul, abs_inv, abs_of_nonneg (sq_nonneg a),
      abs_of_pos (div_pos hSpos (by norm_num))]
    field_simp [hBne, ne_of_gt hSpos]
  change a ^ 2 / T ≤ |(∑ i ∈ s, w i * (a / (x i + a))) / (S / 2)|
  rw [hraw, hgap]
  rw [div_le_div_iff₀ hTpos hDpos]
  exact mul_le_mul_of_nonneg_left hDle (sq_nonneg a)

/-- Scale choice whose shifted exterior point is exactly `cosh(1/n)`. -/
noncomputable def oneArmChebyshevScale (n : ℕ) : ℝ :=
  (Real.cosh ((n : ℝ)⁻¹) - 1) / (Real.cosh ((n : ℝ)⁻¹) + 3)

/-- The calibrated scale is strictly positive for every `n ≥ 1`. -/
lemma oneArmChebyshevScale_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < oneArmChebyshevScale n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcosh : 1 < Real.cosh ((n : ℝ)⁻¹) :=
    Real.one_lt_cosh.mpr (inv_ne_zero hn0)
  unfold oneArmChebyshevScale
  positivity

/-- The calibrated scale is strictly below `1`, so the grid interval `[a,1]` is
nondegenerate. -/
lemma oneArmChebyshevScale_lt_one {n : ℕ} (hn : 1 ≤ n) :
    oneArmChebyshevScale n < 1 := by
  have hcosh0 : 0 < Real.cosh ((n : ℝ)⁻¹) := Real.cosh_pos _
  unfold oneArmChebyshevScale
  rw [div_lt_one (by linarith)]
  linarith

/-- Explicit `n^{-2}` lower bound for the Chebyshev scale. -/
lemma oneArmChebyshevScale_lower {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ)⁻¹) ^ 2 /
        ((Real.cosh 1 + 1) * (Real.cosh 1 + 3)) ≤
      oneArmChebyshevScale n := by
  let t : ℝ := (n : ℝ)⁻¹
  let c : ℝ := Real.cosh t
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact inv_le_one_of_one_le₀ hnR
  have hc1 : c ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh]
    simp only [abs_of_nonneg ht0, abs_one]
    exact ht1
  have hc_ge : 1 ≤ c := by
    dsimp [c]
    exact Real.one_le_cosh _
  have hsinh : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr ht0
  have hsinh0 : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht0
  have hsq : t ^ 2 ≤ Real.sinh t ^ 2 :=
    pow_le_pow_left₀ ht0 hsinh 2
  have hid : Real.sinh t ^ 2 = (c - 1) * (c + 1) := by
    dsimp [c]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hbase : t ^ 2 ≤ (c - 1) * (c + 1) := by rw [← hid]; exact hsq
  have hc3 : 0 < c + 3 := by have := Real.cosh_pos t; dsimp [c]; linarith
  have hC1 : 0 < Real.cosh 1 + 1 := by have := Real.cosh_pos 1; linarith
  have hC3 : 0 < Real.cosh 1 + 3 := by have := Real.cosh_pos 1; linarith
  have hC : 0 < (Real.cosh 1 + 1) * (Real.cosh 1 + 3) := mul_pos hC1 hC3
  unfold oneArmChebyshevScale
  change t ^ 2 / ((Real.cosh 1 + 1) * (Real.cosh 1 + 3)) ≤ (c - 1) / (c + 3)
  rw [div_le_div_iff₀ hC hc3]
  calc
    t ^ 2 * (c + 3) ≤ ((c - 1) * (c + 1)) * (c + 3) :=
      mul_le_mul_of_nonneg_right hbase hc3.le
    _ ≤ (c - 1) * ((Real.cosh 1 + 1) * (Real.cosh 1 + 3)) := by
      have hprod : (c + 1) * (c + 3) ≤
          (Real.cosh 1 + 1) * (Real.cosh 1 + 3) := by
        exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (by linarith)

/-- With the calibrated scale as the left grid endpoint, the standard coordinate
of the exterior point is exactly `cosh(1/n)`. -/
lemma oneArmLobattoExterior_chebyshevScale {n : ℕ} (hn : 1 ≤ n) :
    oneArmLobattoExterior (oneArmChebyshevScale n) =
      Real.cosh ((n : ℝ)⁻¹) := by
  have hden : Real.cosh ((n : ℝ)⁻¹) + 3 ≠ 0 := by
    have := Real.cosh_pos ((n : ℝ)⁻¹)
    linarith
  unfold oneArmLobattoExterior oneArmChebyshevScale
  field_simp [hden]
  ring

/-- At the calibrated scale the degree-`n` Chebyshev polynomial evaluates at the
exterior point to the absolute constant `cosh 1`, using `T_n(cosh t) = cosh(nt)`
with `t = 1/n`.  This is what makes the total Lagrange mass at the exterior
point bounded uniformly in `n`. -/
lemma chebyshev_eval_oneArmExterior_eq_cosh_one {n : ℕ} (hn : 1 ≤ n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (oneArmLobattoExterior (oneArmChebyshevScale n)) = Real.cosh 1 := by
  rw [oneArmLobattoExterior_chebyshevScale hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (Real.cosh ((n : ℝ)⁻¹)) =
        Real.cosh ((n : ℝ) * (n : ℝ)⁻¹) := by simp
    _ = Real.cosh 1 := by rw [mul_inv_cancel₀ hn0]

/-- Uniform positive normalized separation for the scale used in the one-arm
construction.  The only remaining size conversion is the elementary estimate
`oneArmChebyshevScale n` is of order `n^{-2}`. -/
lemma oneArmLobatto_uniform_normalized_rational_gap (n : ℕ) (hn : 1 ≤ n) :
    oneArmChebyshevScale n ^ 2 / Real.cosh 1 ≤
      |(∑ i ∈ Finset.Iic n,
          (oneArmLobattoNode n (oneArmChebyshevScale n) i *
            barycentricWeight (Finset.Iic n)
              (oneArmLobattoNode n (oneArmChebyshevScale n)) i) *
              (oneArmChebyshevScale n /
                (oneArmLobattoNode n (oneArmChebyshevScale n) i +
                  oneArmChebyshevScale n))) /
        ((∑ i ∈ Finset.Iic n,
          |oneArmLobattoNode n (oneArmChebyshevScale n) i *
            barycentricWeight (Finset.Iic n)
              (oneArmLobattoNode n (oneArmChebyshevScale n)) i|) / 2)| := by
  simpa [chebyshev_eval_oneArmExterior_eq_cosh_one hn] using
    oneArmLobatto_normalized_rational_gap n hn
      (oneArmChebyshevScale_pos hn) (oneArmChebyshevScale_lt_one hn)

/-- The positive Jordan mass of a finite signed vector. -/
noncomputable def positiveJordanMass {ι : Type*} [Fintype ι]
    (w : ι → ℝ) : ℝ := ∑ i, max (w i) 0

/-- The negative Jordan mass of a finite signed vector. -/
noncomputable def negativeJordanMass {ι : Type*} [Fintype ι]
    (w : ι → ℝ) : ℝ := ∑ i, max (-w i) 0

/-- A zero-total finite signed vector has equal positive and negative Jordan
masses. -/
lemma positiveJordanMass_eq_negativeJordanMass {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hzero : ∑ i, w i = 0) :
    positiveJordanMass w = negativeJordanMass w := by
  unfold positiveJordanMass negativeJordanMass
  have hpoint : ∀ i, max (w i) 0 - max (-w i) 0 = w i := by
    intro i
    rcases le_total 0 (w i) with hi | hi
    · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
    · simp [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
  have hdiff : (∑ i, max (w i) 0) - (∑ i, max (-w i) 0) = 0 := by
    rw [← Finset.sum_sub_distrib]
    calc
      ∑ i, (max (w i) 0 - max (-w i) 0) = ∑ i, w i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hpoint i
      _ = 0 := hzero
  linarith

/-- The common Jordan mass equals half of the total variation of the signed
vector. -/
lemma two_mul_positiveJordanMass_eq_sum_abs {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hzero : ∑ i, w i = 0) :
    2 * positiveJordanMass w = ∑ i, |w i| := by
  have heq := positiveJordanMass_eq_negativeJordanMass w hzero
  calc
    2 * positiveJordanMass w =
        positiveJordanMass w + negativeJordanMass w := by rw [two_mul, heq]
    _ = ∑ i, |w i| := by
      unfold positiveJordanMass negativeJordanMass
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rcases le_total 0 (w i) with hi | hi
      · simp [abs_of_nonneg hi, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
      · simp [abs_of_nonpos hi, max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]

/-- The probability mass function obtained by normalizing the positive Jordan
part of a nonzero finite signed vector. -/
noncomputable def positiveJordanPMF {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hmass : 0 < positiveJordanMass w) : PMF ι :=
  PMF.ofFintype
    (fun i => ENNReal.ofReal (max (w i) 0 / positiveJordanMass w))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [← Finset.sum_div, show (∑ i, max (w i) 0) = positiveJordanMass w by rfl]
        simp [ne_of_gt hmass]
      · intro i _
        exact div_nonneg (le_max_right _ _) (le_of_lt hmass))

/-- The probability mass function obtained by normalizing the negative Jordan
part of a nonzero finite signed vector. -/
noncomputable def negativeJordanPMF {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hmass : 0 < negativeJordanMass w) : PMF ι :=
  PMF.ofFintype
    (fun i => ENNReal.ofReal (max (-w i) 0 / negativeJordanMass w))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [← Finset.sum_div, show (∑ i, max (-w i) 0) = negativeJordanMass w by rfl]
        simp [ne_of_gt hmass]
      · intro i _
        exact div_nonneg (le_max_right _ _) (le_of_lt hmass))

/-- Pointwise real-mass difference of the two normalized Jordan priors. -/
lemma positiveJordanPMF_toReal_sub_negativeJordanPMF_toReal
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hzero : ∑ i, w i = 0)
    (hmass : 0 < positiveJordanMass w) (i : ι) :
    (positiveJordanPMF w hmass i).toReal -
        (negativeJordanPMF w
          (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal =
      w i / positiveJordanMass w := by
  unfold positiveJordanPMF negativeJordanPMF
  rw [PMF.ofFintype_apply, PMF.ofFintype_apply]
  rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · rw [← positiveJordanMass_eq_negativeJordanMass w hzero]
    rcases le_total 0 (w i) with hi | hi
    · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
    · simp [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
      ring
  · exact div_nonneg (le_max_right _ _) (by
      rw [← positiveJordanMass_eq_negativeJordanMass w hzero]
      exact hmass.le)
  · exact div_nonneg (le_max_right _ _) hmass.le

/-- Difference of expectations under the normalized Jordan priors. -/
lemma positiveJordanPMF_sum_sub_negativeJordanPMF_sum
    {ι : Type*} [Fintype ι] (w g : ι → ℝ) (hzero : ∑ i, w i = 0)
    (hmass : 0 < positiveJordanMass w) :
    (∑ i, (positiveJordanPMF w hmass i).toReal * g i) -
        (∑ i, (negativeJordanPMF w
          (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
            g i) =
      (∑ i, w i * g i) / positiveJordanMass w := by
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ i, ((positiveJordanPMF w hmass i).toReal * g i -
        (negativeJordanPMF w
          (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
            g i) =
      ∑ i, (w i / positiveJordanMass w) * g i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← sub_mul,
          positiveJordanPMF_toReal_sub_negativeJordanPMF_toReal w hzero hmass i]
    _ = (∑ i, w i * g i) / positiveJordanMass w := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Any test function annihilated by the raw signed vector has the same
expectation under the two Jordan priors. -/
lemma positiveJordanPMF_sum_eq_negativeJordanPMF_sum_of_weighted_sum_eq_zero
    {ι : Type*} [Fintype ι] (w g : ι → ℝ) (hzero : ∑ i, w i = 0)
    (hmass : 0 < positiveJordanMass w) (hg : ∑ i, w i * g i = 0) :
    ∑ i, (positiveJordanPMF w hmass i).toReal * g i =
      ∑ i, (negativeJordanPMF w
        (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
          g i := by
  have h := positiveJordanPMF_sum_sub_negativeJordanPMF_sum w g hzero hmass
  rw [hg, zero_div] at h
  linarith

/-- A lower bound expressed using the raw signed vector and half of its
ℓ¹-mass is exactly the corresponding separation of the two Jordan priors. -/
lemma jordanPMF_gap_of_raw_gap {ι : Type*} [Fintype ι]
    (w g : ι → ℝ) (hzero : ∑ i, w i = 0)
    (hmass : 0 < positiveJordanMass w) {gap : ℝ}
    (hgap : gap ≤ |(∑ i, w i * g i) / ((∑ i, |w i|) / 2)|) :
    gap ≤ |(∑ i, (positiveJordanPMF w hmass i).toReal * g i) -
      ∑ i, (negativeJordanPMF w
        (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
          g i| := by
  rw [positiveJordanPMF_sum_sub_negativeJordanPMF_sum w g hzero hmass]
  have hmass_eq : positiveJordanMass w = (∑ i, |w i|) / 2 := by
    have h := two_mul_positiveJordanMass_eq_sum_abs w hzero
    linarith
  rwa [hmass_eq]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
