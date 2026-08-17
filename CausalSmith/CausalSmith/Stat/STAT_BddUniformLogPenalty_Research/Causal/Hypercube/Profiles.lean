import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.ScoreLaw

/-!
# Bounded potential-outcome profiles for the causal hard square

This file specializes the existing smooth packing regression to the wider
fixed square.  The smaller affine slope leaves room for one positive local
bump while keeping every Bernoulli parameter in the middle half.
-/

open Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The common control-arm Bernoulli success profile. -/
-- @node: causalHardControlProfile
noncomputable def causalHardControlProfile (_x : Score) : ℝ := 1 / 2

/-- The treatment-arm profile with one smooth local bump per active bit. -/
-- @node: causalHardTreatmentProfile
noncomputable def causalHardTreatmentProfile {M : ℕ} (delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) : Score → ℝ :=
  clippedPackingRegression (1 / 16) delta w centers omega

/-- Both hard-family potential-outcome profiles are Borel measurable. -/
-- @node: causalHardProfiles_measurable
lemma causalHardProfiles_measurable {M : ℕ} (delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    Measurable causalHardControlProfile ∧
      Measurable (causalHardTreatmentProfile delta w centers omega) := by
  exact ⟨measurable_const,
    clippedPackingRegression_measurable (1 / 16) delta w centers omega⟩

/-- The globally clipped profiles take values in the unit interval. -/
-- @node: causalHardProfiles_mem_unitInterval
lemma causalHardProfiles_mem_unitInterval {M : ℕ} (delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (x : Score) :
    causalHardControlProfile x ∈ Icc (0 : ℝ) 1 ∧
      causalHardTreatmentProfile delta w centers omega x ∈ Icc (0 : ℝ) 1 := by
  exact ⟨by norm_num [causalHardControlProfile],
    clippedPackingRegression_mem_Icc (1 / 16) delta w centers omega x⟩

/-- On the fixed square, the underlying smooth packing regression remains in
the middle half of the unit interval. -/
-- @node: causalHardPackingRegression_mem_middleHalf
lemma causalHardPackingRegression_mem_middleHalf {M : ℕ} {delta w : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 16) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ causalHardSquare) :
    packingRegression (1 / 16) delta w centers omega x ∈
      Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hsum := packingRegression_bump_sum_mem_Icc hdelta0 hw hsep omega x
  have hx0 := hx (0 : Fin 2)
  unfold packingRegression packingAffineBaseline
  constructor <;> nlinarith [hsum.1, hsum.2]

/-- On the fixed square, a bump of amplitude at most `1/16` keeps the
treatment profile in `[1/4,3/4]`, so global clipping is silent there. -/
-- @node: causalHardTreatmentProfile_mem_middleHalf
lemma causalHardTreatmentProfile_mem_middleHalf {M : ℕ} {delta w : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 16) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ causalHardSquare) :
    causalHardTreatmentProfile delta w centers omega x ∈
      Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hraw := causalHardPackingRegression_mem_middleHalf
    hdelta0 hdelta hw hsep omega hx
  unfold causalHardTreatmentProfile
  rw [clippedPackingRegression_eq_of_mem_Icc
    (show packingRegression (1 / 16) delta w centers omega x ∈
      Icc (0 : ℝ) 1 by
        exact ⟨hraw.1.trans' (by norm_num), hraw.2.trans (by norm_num)⟩)]
  exact hraw

/-- On the hard square the global clip is inactive, so the treatment profile
agrees with the underlying smooth affine-plus-bump regression. -/
-- @node: causalHardTreatmentProfile_eq_packingRegression_on_square
lemma causalHardTreatmentProfile_eq_packingRegression_on_square {M : ℕ}
    {delta w : ℝ} (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 16)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) :
    Set.EqOn (causalHardTreatmentProfile delta w centers omega)
      (packingRegression (1 / 16) delta w centers omega) causalHardSquare := by
  intro x hx
  unfold causalHardTreatmentProfile
  apply clippedPackingRegression_eq_of_mem_Icc
  have hm := causalHardPackingRegression_mem_middleHalf hdelta0 hdelta hw hsep
    omega hx
  exact ⟨hm.1.trans' (by norm_num), hm.2.trans (by norm_num)⟩

/-- The treatment profile on the hard square is the restriction of a globally
smooth affine-plus-bump function. -/
-- @node: causalHardTreatmentProfile_has_smooth_extension
lemma causalHardTreatmentProfile_has_smooth_extension {M : ℕ} (j : ℕ)
    {delta w : ℝ} (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 16)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) :
    ∃ g : Score → ℝ, ContDiff ℝ j g ∧
      Set.EqOn g (causalHardTreatmentProfile delta w centers omega)
        causalHardSquare := by
  refine ⟨packingRegression (1 / 16) delta w centers omega,
    (packingRegression_contDiff (1 / 16) delta w centers omega).of_le
      (WithTop.coe_le_coe.mpr le_top), ?_⟩
  exact (causalHardTreatmentProfile_eq_packingRegression_on_square hdelta0
    hdelta hw hsep omega).symm

/-- Flipping one bit changes the treatment regression at its center by
exactly the bump amplitude. -/
-- @node: causalHardTreatmentProfile_center_flip
lemma causalHardTreatmentProfile_center_flip {M : ℕ} {delta w : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 16) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : ∀ j, centers j ∈ causalHardSquare)
    (omega : Fin M → Bool) (j : Fin M) :
    |causalHardTreatmentProfile delta w centers omega (centers j) -
      causalHardTreatmentProfile delta w centers
        (Function.update omega j (!omega j)) (centers j)| = delta := by
  have hraw (eta : Fin M → Bool) :
      causalHardTreatmentProfile delta w centers eta (centers j) =
        packingRegression (1 / 16) delta w centers eta (centers j) := by
    unfold causalHardTreatmentProfile
    apply clippedPackingRegression_eq_of_mem_Icc
    have hm := causalHardPackingRegression_mem_middleHalf hdelta0 hdelta hw hsep
      eta (hcenter j)
    exact ⟨hm.1.trans' (by norm_num), hm.2.trans (by norm_num)⟩
  rw [hraw omega, hraw (Function.update omega j (!omega j)),
    packingRegression_center omega j hw hsep,
    packingRegression_center (Function.update omega j (!omega j)) j hw hsep]
  simp only [Function.update_self]
  cases omega j <;> simp [abs_of_nonneg hdelta0]

end CausalSmith.Stat.BddUniformLogPenalty
