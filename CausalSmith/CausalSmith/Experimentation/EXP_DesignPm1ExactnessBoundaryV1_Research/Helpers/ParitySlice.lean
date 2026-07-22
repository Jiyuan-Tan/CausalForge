/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceForward
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceDesigns

/-! # ±1 reduced-slice characterization (parity content)

After full two-block symmetrization, the ±1 covariance image in spectral
coordinates is `T_m` (m even) or `T_m ∩ {y+z ≥ 2/m}` (m odd), via
`y + z = m⁻¹ E[S_A² + S_B²]` and the parity bound `S_A², S_B² ≥ 1` for odd `m`. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

-- @node: lem:pm-reduced-slice-characterization
/-- The ±1 covariance image of the block-exchangeable class in spectral
coordinates is exactly the reduced triangle truncated by the parity threshold
`d_m` (`0` for even `m`, `2/m` for odd `m`). In particular, for odd `m` the spread
vertex `(m/(m−1), 0, 0)` is not implementable, while for even `m` the whole slice is.

Requires `2 ≤ m`: for `m ∈ {0,1}` the within-block parameter `u` does not appear in
`X(u,v)` (blocks have no within-block off-diagonal pair), so `X(u,v)` is independent
of `u` while the reduced coordinates are not, and the characterization fails. -/
lemma pm_reduced_slice_characterization (m : ℕ) (hm : 2 ≤ m) (u v : ℝ) :
    blockSymMatrix m u v ∈ implementableCovarianceClass m ↔
      (InReducedTriangle m (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) ∧
        parityThreshold m ≤ (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v)) := by
  constructor
  · rintro ⟨D, hDmem, hDeq⟩
    exact pm_slice_forward m hm u v D hDeq.symm
  · rintro ⟨htri, hpar⟩
    exact pm_slice_backward m hm u v htri hpar

/-- For even `m`, the whole block elliptope slice is implementable. -/
lemma blockElliptope_subset_implementable_of_even (m : ℕ) (a b : ℝ) (hEven : Even m) :
    blockElliptope m a b ⊆ implementableCovarianceClass m := by
  intro X hX
  rcases hX with ⟨u, v, hXeq, hmem⟩
  subst X
  rw [pm_reduced_slice_characterization m hmem.homophily.1]
  constructor
  · simp [InReducedTriangle, qParam, hmem.psd_x, hmem.psd_y, hmem.psd_z]
    ring
  · simp [parityThreshold, hEven]
    linarith [hmem.psd_y, hmem.psd_z]

/-- For odd `m ≥ 2`, the spread covariance is not ±1 implementable. -/
lemma spreadCovariance_not_implementable_of_odd (m : ℕ) (hm : 2 ≤ m) (hOdd : Odd m) :
    spreadCovariance m ∉ implementableCovarianceClass m := by
  intro h
  rw [spreadCovariance, pm_reduced_slice_characterization m hm] at h
  have hNotEven : ¬ Even m := Nat.not_even_iff_odd.mpr hOdd
  have hm_ne : (m : ℝ) - 1 ≠ 0 := by
    have hmR : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_of_succ_le hm)
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := lt_of_lt_of_le (by decide : 0 < 2) hm
    exact_mod_cast this
  have hyz :
      1 + ((m : ℝ) - 1) * (-1 / ((m : ℝ) - 1)) +
          (1 + ((m : ℝ) - 1) * (-1 / ((m : ℝ) - 1))) = 0 := by
    field_simp [hm_ne]
    ring
  have hthr : 0 < 2 / (m : ℝ) := div_pos (by norm_num) hm_pos
  simp [InReducedTriangle, parityThreshold, hNotEven, qParam] at h
  nlinarith [h.2, hyz, hthr]

end CausalSmith.Experimentation.DesignPm1
