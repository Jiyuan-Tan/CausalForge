/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.FrobeniusCenter
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SpectralCoordinates
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SymRedDesign

/-! # Robust-corner helper lemmas -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

-- @node: iidDesign_sign_pair_sum_zero
/-- Under the uniform iid sign law, the raw sum of two distinct coordinate signs is zero. -/
lemma iidDesign_sign_pair_sum_zero (m : ℕ) (i j : Fin (2 * m)) (hij : i ≠ j) :
    (∑ z : Fin (2 * m) → Bool, signOf m z i * signOf m z j) = 0 := by
  classical
  have hji : j ≠ i := fun h => hij h.symm
  let e : (Fin (2 * m) → Bool) ≃ (Fin (2 * m) → Bool) :=
    { toFun := fun z k => if k = i then ! z k else z k
      invFun := fun z k => if k = i then ! z k else z k
      left_inv := by
        intro z
        funext k
        by_cases hk : k = i <;> simp [hk]
      right_inv := by
        intro z
        funext k
        by_cases hk : k = i <;> simp [hk] }
  have hflip : ∀ z : Fin (2 * m) → Bool,
      signOf m (e z) i * signOf m (e z) j = - (signOf m z i * signOf m z j) := by
    intro z
    unfold signOf
    simp [e, hji]
    by_cases zi : z i <;> by_cases zj : z j <;> simp [zi, zj]
  have hsum_eq : (∑ z : Fin (2 * m) → Bool, signOf m z i * signOf m z j)
      = ∑ z : Fin (2 * m) → Bool, signOf m (e z) i * signOf m (e z) j := by
    simpa using
      (Equiv.sum_comp e
        (fun z : Fin (2 * m) → Bool => signOf m z i * signOf m z j)).symm
  have hsum_neg : (∑ z : Fin (2 * m) → Bool, signOf m z i * signOf m z j)
      = - (∑ z : Fin (2 * m) → Bool, signOf m z i * signOf m z j) := by
    calc
      (∑ z : Fin (2 * m) → Bool, signOf m z i * signOf m z j)
          = ∑ z : Fin (2 * m) → Bool, signOf m (e z) i * signOf m (e z) j := hsum_eq
      _ = ∑ z : Fin (2 * m) → Bool, - (signOf m z i * signOf m z j) := by
            exact Finset.sum_congr rfl (fun z _ => hflip z)
      _ = - (∑ z : Fin (2 * m) → Bool, signOf m z i * signOf m z j) := by simp
  linarith

-- @node: iidDesign_secondMoment
/-- The iid Rademacher design has identity second-moment matrix. -/
lemma iidDesign_secondMoment (m : ℕ) :
    assignmentSecondMoment m (iidDesign m) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [assignmentSecondMoment_diag]
  · have hsum0 := iidDesign_sign_pair_sum_zero m i j hij
    calc
      assignmentSecondMoment m (iidDesign m) i j
          = (Fintype.card (Fin (2 * m) → Bool) : ℝ)⁻¹ *
              (∑ z : Fin (2 * m) → Bool, signOf m z i * signOf m z j) := by
            simp [assignmentSecondMoment, iidDesign, FiniteDesign.E, Finset.mul_sum, mul_comm]
      _ = 0 := by simp [hsum0]
      _ = (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) i j := by
            simp [hij]

-- @node: identity_mem_blockElliptope
/-- The identity covariance is the block-symmetric center `(u,v)=(0,0)`, hence lies in
`E_m^blk` under two-block homophily. -/
lemma identity_mem_blockElliptope (m : ℕ) (a b : ℝ) (hHom : TwoBlockHomophily m a b) :
    (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) ∈ blockElliptope m a b := by
  have hspec := block_spectral_coordinates m a b 0 0 0 0 hHom
  have hcenter := hspec.2.2.2.2
  have htri : InReducedTriangle m (1 - (0 : ℝ))
      (1 + ((m : ℝ) - 1) * (0 : ℝ) - (m : ℝ) * (0 : ℝ))
      (1 + ((m : ℝ) - 1) * (0 : ℝ) + (m : ℝ) * (0 : ℝ)) := by
    simpa [hcenter] using
      (frobenius_center_certificate m 0 0 0 1 (by
        rcases hHom with ⟨hm, _, _⟩
        unfold qParam
        have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith)).1.1
  rw [identity_eq_blockSym]
  exact hspec.1.mpr htri

-- @node: robust_coeff_r_eq_of_center
/-- The center first-order equality `c_x/q = c_y` forces `r = 2b(a+b)`. -/
lemma robust_coeff_r_eq_of_center (m : ℕ) (a b r : ℝ)
    (hHom : TwoBlockHomophily m a b)
    (hxy : cX m a b r / qParam m = cY b r) :
    r = 2 * b * (a + b) := by
  rcases hHom with ⟨hm, hba, hb⟩
  have hq : qParam m ≠ 0 := by
    unfold qParam
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hsum : a + b ≠ 0 := by nlinarith
  have hb2 : 2 * b ≠ 0 := by positivity
  have hdiff : a - b ≠ 0 := by nlinarith
  unfold cX cY at hxy
  have hraw : a + b + r / (a + b) = 2 * b + r / (2 * b) := by
    have hcancel : qParam m * (a + b + r / (a + b)) / qParam m =
        a + b + r / (a + b) := by
      field_simp [hq]
    simpa [hcancel] using hxy
  have hmul : (a - b) * (1 - r / (2 * b * (a + b))) = 0 := by
    have hrearr : (a + b + r / (a + b)) - (2 * b + r / (2 * b)) =
        (a - b) * (1 - r / (2 * b * (a + b))) := by
      field_simp [hsum, hb2]
      ring
    nlinarith
  have hunit : 1 - r / (2 * b * (a + b)) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hdiff
  have hden : 2 * b * (a + b) ≠ 0 := by nlinarith
  field_simp [hden] at hunit
  linarith

-- @node: robust_locus_of_center_coeffs
/-- The two center coefficient equalities are equivalent to the affine-balanced locus. -/
lemma robust_locus_of_center_coeffs (m : ℕ) (a b r : ℝ)
    (hHom : TwoBlockHomophily m a b)
    (hxy : cX m a b r / qParam m = cY b r) (hyz : cY b r = cZ m) :
    a + 3 * b = 2 * (m : ℝ) ∧ r = 2 * b * (a + b) := by
  have hr : r = 2 * b * (a + b) :=
    robust_coeff_r_eq_of_center m a b r hHom hxy
  constructor
  · rcases hHom with ⟨_, _, hb⟩
    have hb2 : 2 * b ≠ 0 := by positivity
    unfold cY cZ at hyz
    rw [hr] at hyz
    field_simp [hb2] at hyz
    linarith
  · exact hr

-- @node: robust_center_coeffs_of_locus
/-- On the affine-balanced locus, the reduced linear coefficients are all equal. -/
lemma robust_center_coeffs_of_locus (m : ℕ) (a b r : ℝ)
    (hHom : TwoBlockHomophily m a b)
    (hloc : a + 3 * b = 2 * (m : ℝ) ∧ r = 2 * b * (a + b)) :
    cX m a b r / qParam m = cY b r ∧ cY b r = cZ m := by
  rcases hHom with ⟨hm, hba, hb⟩
  have hq : qParam m ≠ 0 := by
    unfold qParam
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hsum : a + b ≠ 0 := by nlinarith
  have hb2 : 2 * b ≠ 0 := by positivity
  constructor
  · unfold cX cY
    rw [hloc.2]
    field_simp [hq, hsum, hb2]
    ring
  · unfold cY cZ
    rw [hloc.2]
    field_simp [hb2]
    linarith [hloc.1]

-- @node: reduced_coord_inverse
/-- Inverse map from reduced coordinates to block-symmetric `(u,v)` coordinates. -/
lemma reduced_coord_inverse (m : ℕ) (x y z : ℝ) (hm : 2 ≤ m)
    (htri : InReducedTriangle m x y z) :
    let u := 1 - x
    let v := (z - y) / (2 * (m : ℝ))
    (1 - u = x) ∧
      (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v = y) ∧
      (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v = z) := by
  intro u v
  rcases htri with ⟨_hx, _hy, _hz, hsum⟩
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℕ) < m := lt_of_lt_of_le (by decide : 0 < 2) hm
    exact_mod_cast (ne_of_gt this)
  have hq : qParam m = 2 * ((m : ℝ) - 1) := rfl
  constructor
  · simp [u]
  constructor
  · dsimp [u, v]
    rw [hq] at hsum
    field_simp [hm0]
    nlinarith [hsum]
  · dsimp [u, v]
    rw [hq] at hsum
    field_simp [hm0]
    nlinarith [hsum]

-- @node: identity_objective_eq_reduced_center
/-- The matrix objective at `I_n` is the reduced objective at `(1,1,1)`. -/
lemma identity_objective_eq_reduced_center (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) :
    designObjective m a b r kappa (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
      = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa 1 1 1 := by
  have hspec := block_spectral_coordinates m a b r kappa 0 0 hHom
  have hcoords := hspec.2.2.2.2
  rw [identity_eq_blockSym]
  simpa [hcoords] using hspec.2.1

-- @node: center_coeffs_of_identity_relaxed_min
/-- If `I_n` minimizes the matrix objective on the block elliptope, the reduced center
first-order coefficient equalities hold. -/
lemma center_coeffs_of_identity_relaxed_min (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b)
    (hmin : ∀ X ∈ blockElliptope m a b,
      designObjective m a b r kappa (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
        ≤ designObjective m a b r kappa X) :
    cX m a b r / qParam m = cY b r ∧ cY b r = cZ m := by
  have hm : 2 ≤ m := hHom.1
  have hq : 0 < qParam m := by
    unfold qParam
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hcert := frobenius_center_certificate m (cX m a b r) (cY b r) (cZ m) kappa hq
  refine hcert.2.1 ?_
  intro x y z htri
  let u : ℝ := 1 - x
  let v : ℝ := (z - y) / (2 * (m : ℝ))
  have hcoords := reduced_coord_inverse m x y z hm htri
  have htri_uv : InReducedTriangle m (1 - u)
      (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
      (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
    simpa [u, v, hcoords.1, hcoords.2.1, hcoords.2.2] using htri
  have hspec := block_spectral_coordinates m a b r kappa u v hHom
  have hmem : blockSymMatrix m u v ∈ blockElliptope m a b := hspec.1.mpr htri_uv
  calc
    reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa 1 1 1
        = designObjective m a b r kappa
            (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :=
          (identity_objective_eq_reduced_center m a b r kappa hHom).symm
    _ ≤ designObjective m a b r kappa (blockSymMatrix m u v) :=
          hmin (blockSymMatrix m u v) hmem
    _ = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
          simpa [u, v, hcoords.1, hcoords.2.1, hcoords.2.2] using hspec.2.1

-- @node: identity_strict_relaxed_min_of_locus
/-- On the affine-balanced locus and for `κ>0`, `I_n` is the strict relaxed minimizer
over the block elliptope. -/
lemma identity_strict_relaxed_min_of_locus (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 < kappa)
    (hloc : a + 3 * b = 2 * (m : ℝ) ∧ r = 2 * b * (a + b)) :
    (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) ∈ blockElliptope m a b ∧
      ∀ X ∈ blockElliptope m a b, X ≠ 1 →
        designObjective m a b r kappa (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
          < designObjective m a b r kappa X := by
  have hm : 2 ≤ m := hHom.1
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hq : 0 < qParam m := by
    unfold qParam
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hcoeff := robust_center_coeffs_of_locus m a b r hHom hloc
  have hcert := frobenius_center_certificate m (cX m a b r) (cY b r) (cZ m) kappa hq
  constructor
  · exact identity_mem_blockElliptope m a b hHom
  · intro X hX hne
    rcases hX with ⟨u, v, rfl, hmem⟩
    have hspec := block_spectral_coordinates m a b r kappa u v hHom
    have htri : InReducedTriangle m (1 - u)
        (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) :=
      hspec.1.mp ⟨u, v, rfl, hmem⟩
    have hcoord_ne :
        ((1 - u,
          1 + ((m : ℝ) - 1) * u - (m : ℝ) * v,
          1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) : ℝ × ℝ × ℝ) ≠
          (1, 1, 1) := by
      intro hcoord
      have hx1 : 1 - u = 1 := congrArg Prod.fst hcoord
      have hz1 : 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v = 1 :=
        congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hcoord
      have hu : u = 0 := by linarith
      have hv : v = 0 := by
        subst u
        have hmv : (m : ℝ) * v = 0 := by nlinarith
        exact (mul_eq_zero.mp hmv).resolve_left hm0
      apply hne
      rw [identity_eq_blockSym, hu, hv]
    calc
      designObjective m a b r kappa
          (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
          = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa 1 1 1 :=
            identity_objective_eq_reduced_center m a b r kappa hHom
      _ < reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
          (1 - u)
          (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) :=
            hcert.2.2 hk hcoeff.1 hcoeff.2 _ _ _ htri hcoord_ne
      _ = designObjective m a b r kappa (blockSymMatrix m u v) := hspec.2.1.symm

end CausalSmith.Experimentation.DesignPm1
