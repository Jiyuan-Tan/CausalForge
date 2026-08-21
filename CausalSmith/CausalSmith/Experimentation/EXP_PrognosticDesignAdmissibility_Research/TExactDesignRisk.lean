/- Exact design-unbiasedness and MSE identity. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Basic

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

open Causalean.Experimentation.DesignBased
open scoped BigOperators

-- @node: lem:exact-design-risk
/-- Every balanced mean-zero design makes the balanced difference in means unbiased,
and its exact MSE is the stated covariance quadratic form. -/
lemma exact_design_risk
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n)
    (D : FiniteDesign (Assignment n)) (hD : D ∈ balancedDesignSpace n)
    (Y : Fin n → Bool → Assignment n → ℝ)
    (yr : Fin n → Assignment n → ℝ)
    (hfixed : FixedPotentialOutcomes Y)
    (hcons : ConsistencyNoInterference Y yr) :
    D.E (diffInMeans yr) = sate Y ∧
      D.E (fun z => (diffInMeans yr z - sate Y) ^ 2) =
        (4 / (n : ℝ) ^ 2) * quadraticForm (designCovariance D) (centeredOutcomeMean Y) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 4) hn))
  let m : EVec n := WithLp.toLp 2
    (fun i => (fixedOutcome Y i true + fixedOutcome Y i false) / 2)
  have hm (i : Fin n) : m i = (fixedOutcome Y i true + fixedOutcome Y i false) / 2 := rfl
  have hobs (z : Assignment n) :
      diffInMeans yr z = sate Y + 2 * (n : ℝ)⁻¹ * ∑ i, signOf z i * m i := by
    have hterm (i : Fin n) :
        2 * (signOf z i * yr i z) =
          (fixedOutcome Y i true - fixedOutcome Y i false) + 2 * (signOf z i * m i) := by
      rw [hcons i z, hm]
      cases hzi : z i <;> simp [fixedOutcome, signOf, hzi] <;> ring
    unfold diffInMeans sate
    have hmsum : ∑ i, 2 * (signOf z i * m i) = 2 * ∑ i, signOf z i * m i := by
      rw [Finset.mul_sum]
    have hsum : 2 * ∑ i, signOf z i * yr i z =
        ∑ i, (fixedOutcome Y i true - fixedOutcome Y i false) +
          2 * ∑ i, signOf z i * m i := by
      rw [Finset.mul_sum]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, hmsum]
    rw [show 2 * (n : ℝ)⁻¹ * ∑ i, signOf z i * yr i z =
        (n : ℝ)⁻¹ * (2 * ∑ i, signOf z i * yr i z) by ring, hsum]
    ring
  have hproj (z : Assignment n) (hz : IsBalanced z) :
      ∑ i, signOf z i * m i = ∑ i, signOf z i * centeredOutcomeMean Y i := by
    let zs : centeredSubspace n := ⟨signVector z, hz⟩
    have hip := centeredSubspace n |>.inner_orthogonalProjection_eq_of_mem_left zs m
    change inner ℝ (signVector z) (centeredOutcomeMean Y) = inner ℝ (signVector z) m at hip
    rw [PiLp.inner_apply, PiLp.inner_apply] at hip
    have hreal (a b : ℝ) : inner ℝ a b = b * a := rfl
    simp_rw [hreal] at hip
    change (∑ i, centeredOutcomeMean Y i * signOf z i) = ∑ i, m i * signOf z i at hip
    calc
      ∑ i, signOf z i * m i = ∑ i, m i * signOf z i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, centeredOutcomeMean Y i * signOf z i := hip.symm
      _ = ∑ i, signOf z i * centeredOutcomeMean Y i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  have herr (z : Assignment n) (hz : IsBalanced z) :
      diffInMeans yr z - sate Y =
        2 * (n : ℝ)⁻¹ * ∑ i, signOf z i * centeredOutcomeMean Y i := by
    rw [hobs z, hproj z hz]
    ring
  have hmeanm : D.E (fun z => ∑ i, signOf z i * m i) = 0 := by
    rw [D.E_sum Finset.univ (fun i z => signOf z i * m i)]
    apply Finset.sum_eq_zero
    intro i _
    rw [D.E_mul_const, hD.2 i, zero_mul]
  constructor
  · rw [D.E_congr (fun z => hobs z), D.E_add, D.E_const_mul, hmeanm, mul_zero,
      D.E_const, add_zero]
  · have hsupp (z : Assignment n) (hp : D.p z ≠ 0) : IsBalanced z := hD.1 z hp
    have hEerr :
        D.E (fun z => (diffInMeans yr z - sate Y) ^ 2) =
          D.E (fun z => (2 * (n : ℝ)⁻¹ *
            ∑ i, signOf z i * centeredOutcomeMean Y i) ^ 2) := by
      unfold FiniteDesign.E
      apply Finset.sum_congr rfl
      intro z _
      by_cases hp : D.p z = 0
      · simp [hp]
      · dsimp
        rw [herr z (hsupp z hp)]
    rw [hEerr]
    rw [show D.E (fun z => (2 * (n : ℝ)⁻¹ *
          ∑ i, signOf z i * centeredOutcomeMean Y i) ^ 2) =
        (2 * (n : ℝ)⁻¹) ^ 2 *
          D.E (fun z => (∑ i, signOf z i * centeredOutcomeMean Y i) ^ 2) by
      rw [← D.E_const_mul]
      apply D.E_congr
      intro z
      ring]
    have hquad :
        D.E (fun z => (∑ i, signOf z i * centeredOutcomeMean Y i) ^ 2) =
          quadraticForm (designCovariance D) (centeredOutcomeMean Y) := by
      calc
        D.E (fun z => (∑ i, signOf z i * centeredOutcomeMean Y i) ^ 2) =
            D.E (fun z => ∑ i, ∑ j,
              (centeredOutcomeMean Y i * centeredOutcomeMean Y j) *
                (signOf z i * signOf z j)) := by
          apply D.E_congr
          intro z
          rw [sq, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ i, ∑ j, (centeredOutcomeMean Y i * centeredOutcomeMean Y j) *
              D.E (fun z => signOf z i * signOf z j) := by
          rw [D.E_sum Finset.univ]
          apply Finset.sum_congr rfl
          intro i _
          rw [D.E_sum Finset.univ]
          apply Finset.sum_congr rfl
          intro j _
          rw [D.E_const_mul]
        _ = quadraticForm (designCovariance D) (centeredOutcomeMean Y) := by
          unfold quadraticForm designCovariance Matrix.mulVec dotProduct
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    rw [hquad]
    field_simp
    ring

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
