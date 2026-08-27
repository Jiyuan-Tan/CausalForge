import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmApproximation
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.FiniteGridBestApproximation
import Causalean.Mathlib.Analysis.EhlichZellerMesh.Mesh

/-!
# Selected finite grid for the one-arm approximation obstruction

This file builds the explicit finite grid used by the one-arm hard-prior
construction — three boundary-layer points near the pole together with an
oversampled Chebyshev--Lobatto mesh of the remaining interval — and shows that on
this grid the propensity-type target `x / (x + a)` cannot be approximated to
better than a fixed constant by the span of the reciprocal and the monomials up
to degree `n`.  The resulting positive best-approximation error is converted into
a pair of Jordan priors matching all of those test functions.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open Polynomial
open Causalean.Mathlib.Analysis.EhlichZellerMesh
open Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

/-- The pole offset `a = 1 / (10¹⁰ n²)` used throughout the one-arm construction.
It is the amount by which the propensity-type target `x / (x + a)` is shifted away
from a genuine singularity at the origin; the inverse-square dependence on `n` is
calibrated so that a degree-`n` polynomial cannot resolve the boundary layer. -/
noncomputable def oneArmPoleScale (n : ℕ) : ℝ :=
  1 / (10000000000 * (n : ℝ) ^ 2)

/-- The `j`-th node of a Chebyshev--Lobatto mesh of order `2n`, mapped by the
increasing affine change of variables that carries `[-1, 1]` onto the interval
`[a, 1]` from the pole offset up to one.  These are the interior mesh points of
the selected grid. -/
noncomputable def oneArmAffineMeshNode (n j : ℕ) : ℝ :=
  let a := oneArmPoleScale n
  (1 + a) / 2 + (1 - a) / 2 * czNode (2 * n) j

/-- Three boundary-layer points followed by a twice-oversampled affine
Chebyshev--Lobatto mesh of `[a,1]`. -/
noncomputable def oneArmSelectionGrid (n : ℕ) : Fin (2 * n + 4) → ℝ := fun i =>
  if i.1 < 3 then (i.1 + 1 : ℕ) * oneArmPoleScale n
  else oneArmAffineMeshNode n (i.1 - 3)

/-- Every Chebyshev--Lobatto node lies in the interval `[-1, 1]`, being a cosine
value.  This is the range fact that lets the affine change of variables land the
mesh inside the intended interval. -/
lemma czNode_mem_Icc (k j : ℕ) : czNode k j ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · dsimp [czNode]
    linarith [Real.cos_le_one (Real.pi * j / k)]
  · dsimp [czNode]
    linarith [Real.neg_one_le_cos (Real.pi * j / k)]

/-- Once the degree parameter `n` is at least one, every affine mesh node lies
between the pole offset `a` and one.  In particular the nodes stay strictly to the
right of the pole, so the target and the reciprocal are finite there. -/
lemma oneArmAffineMeshNode_mem_Icc {n j : ℕ} (hn : 1 ≤ n) :
    oneArmAffineMeshNode n j ∈ Set.Icc (oneArmPoleScale n) 1 := by
  let a := oneArmPoleScale n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha0 : 0 < a := by dsimp [a, oneArmPoleScale]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a, oneArmPoleScale]
    apply (div_le_one (by positivity : (0 : ℝ) < 10000000000 * (n : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hz := czNode_mem_Icc (2 * n) j
  dsimp [oneArmAffineMeshNode]
  change a ≤ (1 + a) / 2 + (1 - a) / 2 * czNode (2 * n) j ∧
    (1 + a) / 2 + (1 - a) / 2 * czNode (2 * n) j ≤ 1
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hz.1
      (div_nonneg (sub_nonneg.mpr ha1) (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  · have hmul := mul_le_mul_of_nonneg_left hz.2
      (div_nonneg (sub_nonneg.mpr ha1) (by norm_num : (0 : ℝ) ≤ 2))
    linarith

/-- The polynomial obtained from `P` by precomposing with the affine map that sends
`[-1, 1]` onto `[a, 1]`.  Rewriting a polynomial on the working interval as a
polynomial on the reference interval is what lets the Chebyshev norming
inequalities be applied. -/
noncomputable def oneArmAffinePolynomial (n : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  let a := oneArmPoleScale n
  P.comp (Polynomial.C ((1 + a) / 2) + Polynomial.C ((1 - a) / 2) * Polynomial.X)

/-- The rescaled polynomial evaluated at a reference point `t` agrees with the
original polynomial evaluated at the corresponding point of `[a, 1]`.  This is the
computation rule for the affine change of variables. -/
@[simp] lemma oneArmAffinePolynomial_eval (n : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    (oneArmAffinePolynomial n P).eval t =
      P.eval ((1 + oneArmPoleScale n) / 2 + (1 - oneArmPoleScale n) / 2 * t) := by
  simp [oneArmAffinePolynomial]

/-- The affine change of variables does not raise the degree: a polynomial of
degree at most `n` stays of degree at most `n` after rescaling.  Needed so that
the Chebyshev norming inequality can be applied at the same degree. -/
lemma oneArmAffinePolynomial_natDegree_le {n : ℕ} {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ n) :
    (oneArmAffinePolynomial n P).natDegree ≤ n := by
  calc
    (oneArmAffinePolynomial n P).natDegree ≤
        P.natDegree *
          (Polynomial.C ((1 + oneArmPoleScale n) / 2) +
            Polynomial.C ((1 - oneArmPoleScale n) / 2) * Polynomial.X).natDegree := by
      exact Polynomial.natDegree_comp_le
    _ ≤ n := by
      have hlin :
          (Polynomial.C ((1 + oneArmPoleScale n) / 2) +
            Polynomial.C ((1 - oneArmPoleScale n) / 2) * Polynomial.X).natDegree ≤ 1 := by
        have hprod :
            (Polynomial.C ((1 - oneArmPoleScale n) / 2) * Polynomial.X).natDegree ≤ 1 := by
          simpa only [pow_one] using
            Polynomial.natDegree_C_mul_X_pow_le ((1 - oneArmPoleScale n) / 2) 1
        exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) hprod)
      calc
        P.natDegree * _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hlin
        _ = P.natDegree := Nat.mul_one _
        _ ≤ n := hdeg

/-- A degree-`n` polynomial that approximates the shifted target `x/(x+a) + α/x`
to within `e` at every node of the twice-oversampled mesh is uniformly bounded by
`2(1 + |α/a| + e)` on the whole interval `[a, 1]`.  Oversampling is what upgrades
control at finitely many nodes to control everywhere, via the Ehlich--Zeller
norming inequality; the resulting envelope feeds the three-point variation
argument. -/
lemma oneArm_mesh_polynomial_bound
    {n : ℕ} (hn : 1 ≤ n) {alpha e : ℝ} {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ n)
    (hmesh : ∀ j ∈ Finset.range (2 * n + 1),
      |oneArmAffineMeshNode n j /
          (oneArmAffineMeshNode n j + oneArmPoleScale n) +
        alpha / oneArmAffineMeshNode n j - P.eval (oneArmAffineMeshNode n j)| ≤ e) :
    ∀ x ∈ Set.Icc (oneArmPoleScale n) 1,
      |P.eval x| ≤ 2 * (1 + |alpha / oneArmPoleScale n| + e) := by
  let a := oneArmPoleScale n
  let R := oneArmAffinePolynomial n P
  let B := 1 + |alpha / a| + e
  have ha0 : 0 < a := by dsimp [a, oneArmPoleScale]; positivity
  have hB0 : 0 ≤ B := by
    have he0 : 0 ≤ e :=
      (abs_nonneg _).trans (hmesh 0 (by simp))
    dsimp [B]
    positivity
  have hnode (j : ℕ) (hj : j ∈ Finset.range (2 * n + 1)) :
      |R.eval (czNode (2 * n) j)| ≤ B := by
    let x := oneArmAffineMeshNode n j
    have hx := oneArmAffineMeshNode_mem_Icc (j := j) hn
    have hx0 : 0 < x := ha0.trans_le hx.1
    have hxa : 0 < x + a := add_pos hx0 ha0
    have hrat0 : 0 ≤ x / (x + a) := div_nonneg hx0.le hxa.le
    have hrat1 : x / (x + a) ≤ 1 := (div_le_one hxa).2 (by linarith)
    have halpha : |alpha / x| ≤ |alpha / a| := by
      rw [abs_div, abs_div, abs_of_pos hx0, abs_of_pos ha0]
      exact div_le_div_of_nonneg_left (abs_nonneg alpha) ha0 hx.1
    have htarget : |x / (x + a) + alpha / x| ≤ 1 + |alpha / a| := by
      calc
        |x / (x + a) + alpha / x| ≤ |x / (x + a)| + |alpha / x| := abs_add_le _ _
        _ ≤ 1 + |alpha / a| := by
          rw [abs_of_nonneg hrat0]
          exact add_le_add hrat1 halpha
    have happ : |x / (x + a) + alpha / x - P.eval x| ≤ e := by
      simpa [x, a] using hmesh j hj
    have hp : |P.eval x| ≤ B := by
      have hdecomp : P.eval x =
          (x / (x + a) + alpha / x) -
            (x / (x + a) + alpha / x - P.eval x) := by ring
      rw [hdecomp]
      exact (abs_sub _ _).trans (by simpa [B] using add_le_add htarget happ)
    simpa [R, x, a, oneArmAffineMeshNode] using hp
  have hmeshMax : czMeshMax R (2 * n) ≤ B := by
    rw [czMeshMax]
    apply Real.iSup_le
    · intro j
      apply Real.iSup_le
      · intro hj
        exact hnode j hj
      · exact hB0
    · exact hB0
  have hnorm := oversampled_norming R n (2 * n) 2 (by norm_num) hn
    (oneArmAffinePolynomial_natDegree_le hdeg) (by norm_num)
  have hcoef : 1 / Real.cos (Real.pi / (2 * (2 : ℝ))) ≤ 2 := by
    rw [show Real.pi / (2 * (2 : ℝ)) = Real.pi / 4 by ring, Real.cos_pi_div_four]
    have hsqrt : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    rw [one_div_div]
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    nlinarith
  intro x hx
  let t := (2 * x - (1 + a)) / (1 - a)
  have hden : 0 < 1 - a := by
    have ha3 : 3 * a ≤ 1 := by
      dsimp [a, oneArmPoleScale]
      rw [mul_one_div]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10000000000 * (n : ℝ) ^ 2)]
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    linarith
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp [t]
    constructor
    · rw [le_div_iff₀ hden]
      linarith [hx.1]
    · rw [div_le_iff₀ hden]
      linarith [hx.2]
  have heval : R.eval t = P.eval x := by
    rw [show R = oneArmAffinePolynomial n P by rfl, oneArmAffinePolynomial_eval]
    congr 1
    change (1 + a) / 2 + (1 - a) / 2 * ((2 * x - (1 + a)) / (1 - a)) = x
    field_simp [ne_of_gt hden]
    ring
  have hpoint : |R.eval t| ≤
      sSup ((fun y => |R.eval y|) '' Set.Icc (-1 : ℝ) 1) := by
    apply le_csSup
    · exact isCompact_Icc.bddAbove_image
        (R.continuous.abs.continuousOn)
    · exact ⟨t, ht, rfl⟩
  rw [← heval]
  calc
    |R.eval t| ≤ sSup ((fun y => |R.eval y|) '' Set.Icc (-1 : ℝ) 1) := hpoint
    _ ≤ (1 / Real.cos (Real.pi / (2 * (2 : ℝ)))) * czMeshMax R (2 * n) := hnorm
    _ ≤ 2 * B := by
      exact (mul_le_mul hcoef hmeshMax (czMeshMax_nonneg R (2 * n)) (by positivity)).trans_eq
        (by ring)
    _ = 2 * (1 + |alpha / oneArmPoleScale n| + e) := by rfl

/-- The first three points of the selected grid are the boundary-layer points
`a`, `2a` and `3a`.  These are the points on which the three-point rational
obstruction is run. -/
lemma oneArmSelectionGrid_special (n : ℕ) (r : Fin 3) :
    oneArmSelectionGrid n
        ⟨r.1, by omega⟩ = ((r.1 + 1 : ℕ) : ℝ) * oneArmPoleScale n := by
  simp [oneArmSelectionGrid, r.2]

/-- Past the three boundary-layer points, the selected grid is exactly the affine
Chebyshev--Lobatto mesh: the point at index `j + 3` is the `j`-th mesh node.
This is the indexing bridge between the grid and the mesh bounds. -/
lemma oneArmSelectionGrid_mesh (n j : ℕ) (hj : j ≤ 2 * n) :
    oneArmSelectionGrid n
        ⟨j + 3, by omega⟩ = oneArmAffineMeshNode n j := by
  simp [oneArmSelectionGrid]

/-- The selected finite grid retains the calibrated constant approximation
obstruction. -/
theorem oneArmSelectionGrid_approximation_lower
    (n : ℕ) (hn : 1 ≤ n) (alpha e : ℝ) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ n)
    (hgrid : ∀ i : Fin (2 * n + 4),
      |oneArmSelectionGrid n i /
          (oneArmSelectionGrid n i + oneArmPoleScale n) +
        alpha / oneArmSelectionGrid n i - P.eval (oneArmSelectionGrid n i)| ≤ e) :
    1 / 1000 ≤ e := by
  let a := oneArmPoleScale n
  let U := |alpha / a|
  let B := 2 * (1 + U + e)
  have ha0 : 0 < a := by dsimp [a, oneArmPoleScale]; positivity
  have ha3 : 3 * a ≤ 1 := by
    dsimp [a, oneArmPoleScale]
    rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 10000000000 * (n : ℝ) ^ 2)]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have ha1 : a < 1 := by nlinarith
  have hspecial (r : Fin 3) :
      |(((r.1 + 1 : ℕ) : ℝ) * a) /
          ((((r.1 + 1 : ℕ) : ℝ) * a) + a) +
        alpha / (((r.1 + 1 : ℕ) : ℝ) * a) -
          P.eval (((r.1 + 1 : ℕ) : ℝ) * a)| ≤ e := by
    simpa [a, oneArmSelectionGrid_special] using
      hgrid ⟨r.1, by omega⟩
  have he0 : 0 ≤ e := (abs_nonneg _).trans (hspecial 0)
  have hU0 : 0 ≤ U := abs_nonneg _
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hmesh : ∀ j ∈ Finset.range (2 * n + 1),
      |oneArmAffineMeshNode n j /
          (oneArmAffineMeshNode n j + a) +
        alpha / oneArmAffineMeshNode n j - P.eval (oneArmAffineMeshNode n j)| ≤ e := by
    intro j hj
    have hjlt : j < 2 * n + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ 2 * n := by omega
    simpa [a, oneArmSelectionGrid_mesh n j hjle] using hgrid ⟨j + 3, by omega⟩
  have hP : ∀ x ∈ Set.Icc a 1, |P.eval x| ≤ B := by
    simpa [a, B, U] using oneArm_mesh_polynomial_bound hn hdeg hmesh
  have hscale := oneArm_calibrated_angular_scale n hn
  change (n : ℝ) * Real.sqrt (4 * a / (1 - a)) ≤ 1 / 10000 at hscale
  have hsqrt : Real.sqrt (2 * a / (1 - a)) ≤ Real.sqrt (4 * a / (1 - a)) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by nlinarith) (by linarith : 0 ≤ 1 - a)
  have h12raw := oneArm_poly_two_mul_variation ha0 ha3 hdeg hP
  have h13raw := oneArm_poly_three_mul_variation ha0 ha3 hdeg hP
  have h12 : |P.eval a - P.eval (2 * a)| ≤ 4 * B / 10000 := by
    calc
      |P.eval a - P.eval (2 * a)|
          ≤ 4 * (n : ℝ) * B * Real.sqrt (2 * a / (1 - a)) := h12raw
      _ ≤ 4 * B * ((n : ℝ) * Real.sqrt (4 * a / (1 - a))) := by
        have hmul := mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4) (by positivity)) hB0)
        nlinarith
      _ ≤ 4 * B * (1 / 10000) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hB0)
      _ = 4 * B / 10000 := by ring
  have h13 : |P.eval a - P.eval (3 * a)| ≤ 4 * B / 10000 := by
    calc
      |P.eval a - P.eval (3 * a)|
          ≤ 4 * (n : ℝ) * B * Real.sqrt (4 * a / (1 - a)) := h13raw
      _ = 4 * B * ((n : ℝ) * Real.sqrt (4 * a / (1 - a))) := by ring
      _ ≤ 4 * B * (1 / 10000) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hB0)
      _ = 4 * B / 10000 := by ring
  have h32 : |P.eval (3 * a) - P.eval (2 * a)| ≤ 8 * B / 10000 := by
    have hdecomp : P.eval (3 * a) - P.eval (2 * a) =
        (P.eval (3 * a) - P.eval a) + (P.eval a - P.eval (2 * a)) := by ring
    rw [hdecomp]
    calc
      |(P.eval (3 * a) - P.eval a) + (P.eval a - P.eval (2 * a))|
          ≤ |P.eval (3 * a) - P.eval a| + |P.eval a - P.eval (2 * a)| :=
            abs_add_le _ _
      _ ≤ 4 * B / 10000 + 4 * B / 10000 := by
        rw [abs_sub_comm (P.eval (3 * a))]
        exact add_le_add h13 h12
      _ = 8 * B / 10000 := by ring
  by_cases hU : U ≤ 1
  · have hobs := oneArm_rational_three_point_obstruction
      (a := a) (alpha := alpha) (e := e) (V := 8 * B / 10000)
      (ne_of_gt ha0) (fun x => P.eval x)
      (by simpa using hspecial 0)
      (by simpa using hspecial 1)
      (by simpa using hspecial 2)
      (h12.trans (by nlinarith [hB0])) h32
    dsimp [B] at hobs
    nlinarith
  · have hUlarge : 1 < U := lt_of_not_ge hU
    let f : ℝ → ℝ := fun x => x / (x + a) + alpha / x
    have hf : f a - f (2 * a) = alpha / a / 2 - 1 / 6 := by
      dsimp [f]
      field_simp [ne_of_gt ha0]
      ring
    have hlower : U / 2 - 1 / 6 ≤ |f a - f (2 * a)| := by
      rw [hf]
      have habsdiv : |alpha / a / 2| = U / 2 := by simp [U, abs_div]
      have hrev := abs_sub_abs_le_abs_sub (alpha / a / 2) (1 / 6)
      rw [habsdiv] at hrev
      norm_num at hrev ⊢
      exact hrev
    have hupper : |f a - f (2 * a)| ≤ 2 * e + 4 * B / 10000 := by
      have hdecomp : f a - f (2 * a) =
          (f a - P.eval a) + (P.eval a - P.eval (2 * a))
            - (f (2 * a) - P.eval (2 * a)) := by ring
      rw [hdecomp]
      calc
        |(f a - P.eval a) + (P.eval a - P.eval (2 * a)) -
            (f (2 * a) - P.eval (2 * a))|
            ≤ |f a - P.eval a| + |P.eval a - P.eval (2 * a)| +
                |P.eval (2 * a) - f (2 * a)| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_three (f a - P.eval a) (P.eval a - P.eval (2 * a))
                  (-(f (2 * a) - P.eval (2 * a)))
        _ = |f a - P.eval a| + |P.eval a - P.eval (2 * a)| +
                |f (2 * a) - P.eval (2 * a)| := by
              rw [abs_sub_comm (P.eval (2 * a))]
        _ ≤ e + 4 * B / 10000 + e := by
          exact add_le_add (add_le_add
            (by simpa [f] using hspecial 0) h12)
            (by simpa [f] using hspecial 1)
        _ = 2 * e + 4 * B / 10000 := by ring
    dsimp [B] at hupper
    nlinarith [hlower.trans hupper]

/-- The reciprocal monomial followed by ordinary monomials through degree
`n`, evaluated on the selected grid. -/
noncomputable def oneArmSelectionBasis (n : ℕ) :
    Fin (n + 2) → Fin (2 * n + 4) → ℝ := fun j i =>
  if j.1 = 0 then (oneArmSelectionGrid n i)⁻¹
  else (oneArmSelectionGrid n i) ^ (j.1 - 1)

/-- The target function `x / (x + a)` sampled on the selected grid.  This is the
propensity-shaped quantity the hard prior must separate, and the object whose
best approximation error is bounded below. -/
noncomputable def oneArmSelectionTarget (n : ℕ) : Fin (2 * n + 4) → ℝ := fun i =>
  oneArmSelectionGrid n i / (oneArmSelectionGrid n i + oneArmPoleScale n)

/-- The polynomial part of a coefficient vector for the selection basis: the
reciprocal coefficient is discarded and the remaining coefficients are read as the
coefficients of `1, x, …, xⁿ`.  This splits an arbitrary element of the
approximation space into a reciprocal term plus an honest polynomial. -/
noncomputable def oneArmSelectionPolynomial (n : ℕ) (c : Fin (n + 2) → ℝ) :
    Polynomial ℝ :=
  ∑ j, if j.1 = 0 then 0
    else Polynomial.C (c j) * Polynomial.X ^ (j.1 - 1)

/-- The polynomial part of any selection-basis coefficient vector has degree at
most `n`, so the degree-`n` approximation-theory bounds apply to it. -/
lemma oneArmSelectionPolynomial_natDegree_le
    (n : ℕ) (c : Fin (n + 2) → ℝ) :
    (oneArmSelectionPolynomial n c).natDegree ≤ n := by
  rw [oneArmSelectionPolynomial]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ) (f := fun j =>
    if j.1 = 0 then 0 else Polynomial.C (c j) * Polynomial.X ^ (j.1 - 1)) ?_
  intro j hj
  split_ifs
  · simp
  · exact (Polynomial.natDegree_C_mul_X_pow_le (c j) (j.1 - 1)).trans (by omega)

/-- A linear combination of the selection basis evaluated at a grid point equals
the reciprocal term `c₀ / x` plus the value of the polynomial part at that point.
This is the explicit decomposition of the approximation space into "one pole plus
a polynomial". -/
lemma oneArmSelectionBasis_sum_eq
    (n : ℕ) (c : Fin (n + 2) → ℝ) (i : Fin (2 * n + 4)) :
    ∑ j, c j * oneArmSelectionBasis n j i =
      c 0 / oneArmSelectionGrid n i + (oneArmSelectionPolynomial n c).eval
        (oneArmSelectionGrid n i) := by
  classical
  let x := oneArmSelectionGrid n i
  calc
    ∑ j, c j * oneArmSelectionBasis n j i =
        c 0 * x⁻¹ + ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)), c j * x ^ (j.1 - 1) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j => c j * oneArmSelectionBasis n j i)
        (Finset.mem_univ (0 : Fin (n + 2)))]
      simp only [oneArmSelectionBasis, Fin.isValue, Fin.val_zero, if_pos, Nat.cast_one,
        one_mul, x]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj0 : j.1 ≠ 0 := by
        intro h
        exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
      simp [oneArmSelectionBasis, hj0, x]
    _ = c 0 / x + (oneArmSelectionPolynomial n c).eval x := by
      rw [div_eq_mul_inv]
      congr 1
      calc
        ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)), c j * x ^ (j.1 - 1) =
            ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
              (if j.1 = 0 then 0
                else Polynomial.C (c j) * Polynomial.X ^ (j.1 - 1)).eval x := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj0 : j.1 ≠ 0 := by
            intro h
            exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
          simp [hj0]
        _ = ∑ j : Fin (n + 2), (if j.1 = 0 then 0
                else Polynomial.C (c j) * Polynomial.X ^ (j.1 - 1)).eval x := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
          simp
        _ = (oneArmSelectionPolynomial n c).eval x := by
          rw [oneArmSelectionPolynomial, Polynomial.eval_finset_sum]
    _ = _ := rfl

/-- On the selected grid, the target `x / (x + a)` cannot be approximated in the
uniform norm to better than `1/1000` by any combination of the reciprocal and the
monomials of degree at most `n`.  This fixed positive gap, uniform in `n`, is the
approximation obstruction that the hard prior is built on. -/
theorem oneArmSelectionGrid_bestError_lower (n : ℕ) (hn : 1 ≤ n) :
    1 / 1000 ≤ finiteGridBestError
      (finiteGridBasisEval (oneArmSelectionBasis n)) (oneArmSelectionTarget n) := by
  apply le_csInf (finiteGridErrorSet_nonempty _ _)
  rintro e ⟨c, rfl⟩
  let P := oneArmSelectionPolynomial n c
  apply oneArmSelectionGrid_approximation_lower n hn (-c 0)
    (ninf (oneArmSelectionTarget n - finiteGridBasisEval (oneArmSelectionBasis n) c)) P
    (oneArmSelectionPolynomial_natDegree_le n c)
  intro i
  have hi := le_ninf
    (oneArmSelectionTarget n - finiteGridBasisEval (oneArmSelectionBasis n) c) i
  change |oneArmSelectionTarget n i -
    ∑ j, c j * oneArmSelectionBasis n j i| ≤ _ at hi
  rw [oneArmSelectionBasis_sum_eq] at hi
  simpa [oneArmSelectionTarget, P, sub_eq_add_neg, div_eq_mul_inv, add_assoc,
    add_comm, add_left_comm] using hi

/-- The coefficient vector that selects the constant function out of the selection
basis: weight one on the degree-zero monomial and zero elsewhere.  It witnesses
that the approximation space contains constants. -/
def oneArmSelectionConstantCoeff (n : ℕ) : Fin (n + 2) → ℝ := fun j =>
  if j.1 = 1 then 1 else 0

/-- The constant function one lies in the span of the selection basis.  This is the
hypothesis the Jordan-decomposition machinery needs in order to conclude that the
dual witness has zero total mass and therefore splits into two probability
measures. -/
lemma oneArmSelectionBasis_contains_one (n : ℕ) :
    finiteGridBasisEval (oneArmSelectionBasis n)
      (oneArmSelectionConstantCoeff n) = fun _ => 1 := by
  classical
  ext i
  rw [finiteGridBasisEval_apply,
    Fintype.sum_eq_single (⟨1, by omega⟩ : Fin (n + 2))]
  · simp [oneArmSelectionConstantCoeff, oneArmSelectionBasis]
  · intro j hj
    have hval : j.1 ≠ 1 := by
      intro h
      exact hj (Fin.ext h)
    simp [oneArmSelectionConstantCoeff, hval]

/-- Jordan PMFs on the selected grid, matching the reciprocal and all moments
through degree `n`, with fixed separation for `x/(x+a)`. -/
theorem exists_oneArmSelectionGrid_jordan_priors (n : ℕ) (hn : 1 ≤ n) :
    ∃ (w : Fin (2 * n + 4) → ℝ)
      (hzero : ∑ i, w i = 0)
      (hmass : 0 < positiveJordanMass w),
      (∑ i, |w i| ≤ 1) ∧
      (∀ c,
        ∑ i, (positiveJordanPMF w hmass i).toReal *
            finiteGridBasisEval (oneArmSelectionBasis n) c i =
          ∑ i, (negativeJordanPMF w
            (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
              finiteGridBasisEval (oneArmSelectionBasis n) c i) ∧
      1 / 500 ≤
        (∑ i, (positiveJordanPMF w hmass i).toReal * oneArmSelectionTarget n i) -
          ∑ i, (negativeJordanPMF w
            (by simpa [positiveJordanMass_eq_negativeJordanMass w hzero] using hmass) i).toReal *
              oneArmSelectionTarget n i := by
  have hbest := oneArmSelectionGrid_bestError_lower n hn
  have hpos : 0 < finiteGridBestError
      (finiteGridBasisEval (oneArmSelectionBasis n)) (oneArmSelectionTarget n) := by
    linarith
  obtain ⟨w, hzero, hmass, hnorm, hmom, hgap⟩ :=
    exists_finiteGrid_jordan_priors
      (finiteGridBasisEval (oneArmSelectionBasis n)) (oneArmSelectionTarget n)
      (oneArmSelectionConstantCoeff n)
      (oneArmSelectionBasis_contains_one n) hpos
  refine ⟨w, hzero, hmass, hnorm, hmom, ?_⟩
  exact (by nlinarith : (1 : ℝ) / 500 ≤
    2 * finiteGridBestError
      (finiteGridBasisEval (oneArmSelectionBasis n)) (oneArmSelectionTarget n)).trans hgap

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
