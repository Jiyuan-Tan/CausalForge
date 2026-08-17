import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Family
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularHolder
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularScaledDelta

/-!
# Smooth extension leaf for the hard-square treatment profile

This module converts the normalized bump derivative bounds into the exact
coordinate-partial extension envelope required by `A1A2Class`.
-/

open Set
open scoped Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- If the finitely many normalized bump derivatives through order `p + 1`
obey their paper-scale bounds, the hard treatment profile has the required
Euclidean smooth extension for every envelope at least `48`. -/
-- @node: causalHardTreatmentProfile_euclideanCExtEnvelope_of_scaling_bounds
lemma causalHardTreatmentProfile_euclideanCExtEnvelope_of_scaling_bounds
    {M : ℕ} (p : ℕ) {L delta w : ℝ}
    (hL : 48 ≤ L) (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (C : ℕ → ℝ) (hC0 : ∀ j, 0 ≤ C j)
    (hC : ∀ j z, ‖iteratedFDeriv ℝ j packingBump z‖ ≤ C j)
    (hscale : ∀ j, j ≤ p + 1 → |delta| * (w⁻¹) ^ j * C j ≤ 1) :
    EuclideanCExtEnvelope
      (causalHardTreatmentProfile delta w centers omega) p L
      causalHardSquare := by
  let bumps : Score → ℝ := fun y ↦ ∑ i, if omega i then
    localizedPackingBump delta w (centers i) y else 0
  let g := packingRegression (1 / 16) delta w centers omega
  have hbumps : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) bumps :=
    packingBumpSum_contDiff delta w centers omega
  have hreg (j : ℕ) (x : Score) :
      iteratedFDeriv ℝ j g x =
        iteratedFDeriv ℝ j (packingAffineBaseline (1 / 16)) x +
          iteratedFDeriv ℝ j bumps x := by
    change iteratedFDeriv ℝ j (packingAffineBaseline (1 / 16) + bumps) x = _
    rw [iteratedFDeriv_add_apply
      ((packingAffineBaseline_contDiff (1 / 16)).of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      (hbumps.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  apply euclideanCExtEnvelope_of_iteratedFDeriv_bounds
    (causalHardTreatmentProfile delta w centers omega) g p L 2 2
      causalHardSquare
  · exact ⟨scorePoint 0 0, by
      intro i
      fin_cases i <;> norm_num [causalHardSquare, scorePoint]⟩
  · refine ⟨scorePoint 0 0, ?_, scorePoint 1 0, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [causalHardSquare, scorePoint]
    · intro i
      fin_cases i <;> norm_num [causalHardSquare, scorePoint]
    · intro heq
      have hcoord := congrArg (fun x : Score ↦ x 0) heq
      norm_num [scorePoint] at hcoord
  · exact (packingRegression_contDiff (1 / 16) delta w centers omega).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact (causalHardTreatmentProfile_eq_packingRegression_on_square
      hdelta.le hdeltaSmall hw hsep omega).symm
  · linarith
  · intro alpha ha x hx
    rw [hreg]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha)
            (packingAffineBaseline (1 / 16)) x‖ +
          ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha) bumps x‖ :=
        norm_add_le _ _
      _ ≤ 1 + 1 := by
        gcongr
        · by_cases hj0 : coordinateMultiOrder alpha = 0
          · rw [hj0, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
            have hx0 := hx (0 : Fin 2)
            dsimp [causalHardSquare] at hx0
            unfold packingAffineBaseline
            rw [abs_le]
            constructor <;> nlinarith [abs_nonneg (x 0)]
          · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hj0) with
              hj1 | hj2
            · rw [← hj1]
              exact (packingAffineBaseline_iteratedFDeriv_one_norm_le
                (1 / 16) x).trans (by norm_num)
            · rw [packingAffineBaseline_iteratedFDeriv_eq_zero (1 / 16)
                _ (by omega) x, norm_zero]
              norm_num
        · exact (packingBumpSum_iteratedFDeriv_bound_with
            (coordinateMultiOrder alpha) delta hw hsep omega
            (hC0 _) (hC _) x).trans (hscale _ (by omega))
      _ = 2 := by norm_num
  · intro alpha ha x hx z hz
    rw [hreg, hreg]
    calc
      _ = ‖(iteratedFDeriv ℝ (coordinateMultiOrder alpha)
              (packingAffineBaseline (1 / 16)) x -
            iteratedFDeriv ℝ (coordinateMultiOrder alpha)
              (packingAffineBaseline (1 / 16)) z) +
          (iteratedFDeriv ℝ (coordinateMultiOrder alpha) bumps x -
            iteratedFDeriv ℝ (coordinateMultiOrder alpha) bumps z)‖ := by
          congr 1 <;> abel
      _ ≤ ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha)
              (packingAffineBaseline (1 / 16)) x -
            iteratedFDeriv ℝ (coordinateMultiOrder alpha)
              (packingAffineBaseline (1 / 16)) z‖ +
          ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha) bumps x -
            iteratedFDeriv ℝ (coordinateMultiOrder alpha) bumps z‖ :=
        norm_add_le _ _
      _ ≤ 1 * ‖x - z‖ + 1 * ‖x - z‖ := by
        gcongr
        · by_cases hj0 : coordinateMultiOrder alpha = 0
          · rw [hj0]
            simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
              ← map_sub, LinearIsometryEquiv.norm_map]
            unfold packingAffineBaseline
            rw [show (1 / 2 + (1 / 16) * x 0) -
                (1 / 2 + (1 / 16) * z 0) = (1 / 16) * ((x - z) 0) by
              rw [PiLp.sub_apply]
              ring,
              Real.norm_eq_abs, abs_mul]
            calc
              _ ≤ (1 / 16 : ℝ) * ‖x - z‖ := by
                rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)]
                gcongr
                simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x - z) 0
              _ ≤ 1 * ‖x - z‖ := by
                gcongr <;> norm_num
          · rw [packingAffineBaseline_iteratedFDeriv_sub_eq_zero (1 / 16)
                _ (Nat.one_le_iff_ne_zero.mpr hj0) x z, norm_zero]
            positivity
        · exact (packingBumpSum_iteratedFDeriv_lipschitz_with
              (coordinateMultiOrder alpha) delta hw hsep omega (hC0 _)
              (hC _) x z).trans (by
              have hs := hscale (coordinateMultiOrder alpha + 1) (by omega)
              have hn := norm_nonneg (x - z)
              nlinarith)
      _ = 2 * ‖x - z‖ := by ring

/-- At a power-law bandwidth, a bound on each normalized bump derivative
by the bandwidth constant reduces the positive-order scaling inequalities to
the elementary comparison `delta * u⁻ʲ ≤ 1`, where `u^q = delta`. -/
-- @node: causalHardTreatmentProfile_powerBandwidth_derivative_scaling
lemma causalHardTreatmentProfile_powerBandwidth_derivative_scaling
    (q : ℕ) {A delta : ℝ} (hq : 1 ≤ q) (hA : 1 ≤ A)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hAderiv : ∀ j, j ≤ q → packingBumpDerivativeBound j ≤ A)
    (hzero : delta * packingBumpDerivativeBound 0 ≤ 1) :
    ∀ j, j ≤ q →
      |delta| *
          ((A * Real.rpow delta ((1 : ℝ) / q))⁻¹) ^ j *
            packingBumpDerivativeBound j ≤ 1 := by
  intro j hjq
  by_cases hj0 : j = 0
  · subst j
    simpa [abs_of_pos hdelta] using hzero
  let u := Real.rpow delta ((1 : ℝ) / q)
  have hu0 : 0 < u := Real.rpow_pos_of_pos hdelta _
  have hueq : u ^ q = delta := by
    dsimp [u]
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow hdelta.le (show q ≠ 0 by omega))
  have hu1 : u ≤ 1 := by
    exact Real.rpow_le_one hdelta.le hdeltaOne (by positivity)
  have hupows : u ^ q ≤ u ^ j :=
    pow_le_pow_of_le_one hu0.le hu1 hjq
  have huradial : delta * (u⁻¹) ^ j ≤ 1 := by
    rw [inv_pow, ← hueq]
    simpa [div_eq_mul_inv] using (div_le_one (pow_pos hu0 j)).2 hupows
  have hAj : A ≤ A ^ j := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    rw [pow_succ]
    exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ hA)
  have hfrac0 : 0 ≤ packingBumpDerivativeBound j / A ^ j :=
    div_nonneg (packingBumpDerivativeBound_nonneg j) (by positivity)
  have hfrac1 : packingBumpDerivativeBound j / A ^ j ≤ 1 :=
    (div_le_one (by positivity : 0 < A ^ j)).2
      ((hAderiv j hjq).trans hAj)
  have hmul := mul_le_one₀ huradial hfrac0 hfrac1
  rw [abs_of_pos hdelta]
  change delta * ((A * u)⁻¹) ^ j * packingBumpDerivativeBound j ≤ 1
  calc
    delta * ((A * u)⁻¹) ^ j * packingBumpDerivativeBound j =
        (delta * (u⁻¹) ^ j) *
          (packingBumpDerivativeBound j / A ^ j) := by ring
    _ ≤ 1 := hmul

/-- The paper-scale power bandwidth supplies the treatment-profile smooth
extension once its zeroth derivative is controlled and the bandwidth
constant dominates all normalized derivatives through order `p + 1`. -/
-- @node: causalHardTreatmentProfile_euclideanCExtEnvelope_powerBandwidth
lemma causalHardTreatmentProfile_euclideanCExtEnvelope_powerBandwidth
    {M : ℕ} (p : ℕ) {L A delta : ℝ}
    (hL : 48 ≤ L) (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 16) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k →
      3 * (A * Real.rpow delta ((1 : ℝ) / (p + 1 : ℝ))) ≤
        dist (centers i) (centers k))
    (omega : Fin M → Bool)
    (hAderiv : ∀ j, j ≤ p + 1 → packingBumpDerivativeBound j ≤ A)
    (hzero : delta * packingBumpDerivativeBound 0 ≤ 1) :
    EuclideanCExtEnvelope
      (causalHardTreatmentProfile delta
        (A * Real.rpow delta ((1 : ℝ) / (p + 1 : ℝ))) centers omega)
      p L causalHardSquare := by
  have hdeltaOne : delta ≤ 1 := by linarith
  have hw : 0 < A * Real.rpow delta ((1 : ℝ) / (p + 1 : ℝ)) :=
    mul_pos (lt_of_lt_of_le (by norm_num) hA)
      (Real.rpow_pos_of_pos hdelta _)
  apply causalHardTreatmentProfile_euclideanCExtEnvelope_of_scaling_bounds
    p hL hdelta hdeltaSmall hw hsep omega packingBumpDerivativeBound
    packingBumpDerivativeBound_nonneg
    packingBump_iteratedFDeriv_le_derivativeBound
  simpa [Nat.cast_add, Nat.cast_one] using
    (causalHardTreatmentProfile_powerBandwidth_derivative_scaling
      (p + 1) (by omega) hA hdelta hdeltaOne hAderiv hzero)

end CausalSmith.Stat.BddUniformLogPenalty
