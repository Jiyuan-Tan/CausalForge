import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareAnalytic
import Causalean.Stat.Nonparametric.LocalPolynomial.GramCoercivity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Polynomial coercivity for the hard-square Gram certificate

This module isolates the finite-dimensional compactness argument behind the
population-Gram floor.  Its radial energy is the polar-coordinate integral
of the squared degree-`p` local polynomial on a fixed nondegenerate interval.
-/

open MeasureTheory Set
open scoped BigOperators Interval Polynomial

namespace CausalSmith.Stat.BddUniformLogPenalty


open Causalean.Stat.Nonparametric.LocalPolynomial

/-- A radial integrand over the open first-quadrant sector of a disk has the
expected polar-coordinate representation.  The omitted coordinate axes are
Lebesgue-null, so this is the fixed `π / 2` sector used at rectangle corners. -/
-- @node: firstQuadrant_radial_integral
lemma firstQuadrant_radial_integral (g : ℝ → ℝ) (r : ℝ) :
    (∫ z : ℝ × ℝ in
        {z | 0 < z.1 ∧ 0 < z.2 ∧ planarRadius z ≤ r}, g (planarRadius z)) =
      ∫ s : ℝ in Ioc 0 r, (Real.pi / 2) * s * g s := by
  let D : Set (ℝ × ℝ) :=
    {z | 0 < z.1 ∧ 0 < z.2 ∧ planarRadius z ≤ r}
  let E : Set (ℝ × ℝ) := Ioc 0 r ×ˢ Ioo 0 (Real.pi / 2)
  have hD : MeasurableSet D := by
    change MeasurableSet {z : ℝ × ℝ |
      0 < z.1 ∧ 0 < z.2 ∧ planarRadius z ≤ r}
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le planarRadius_measurable measurable_const))
  have hE : MeasurableSet E := measurableSet_Ioc.prod measurableSet_Ioo
  change (∫ z : ℝ × ℝ in D, g (planarRadius z)) = _
  rw [← integral_indicator hD, ← integral_comp_polarCoord_symm]
  rw [show (∫ q in polarCoord.target,
      q.1 • D.indicator (fun z => g (planarRadius z)) (polarCoord.symm q)) =
      ∫ q in E, q.1 * g q.1 by
    rw [← integral_indicator polarCoord.open_target.measurableSet,
      ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards with q
    by_cases hq : q ∈ polarCoord.target
    · have hqtarget := hq
      simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] at hq
      have hinv := polarCoord.right_inv hq
      have hrs : planarRadius (polarCoord.symm q) = q.1 :=
        congrArg Prod.fst hinv
      have hsin : 0 < Real.sin q.2 ↔ 0 < q.2 := by
        constructor
        · intro hs
          by_contra hn
          exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le
            (le_of_not_gt hn) hq.2.1.le)) hs
        · intro htheta
          exact Real.sin_pos_of_pos_of_lt_pi htheta hq.2.2
      have hcos (htheta0 : 0 < q.2) :
          0 < Real.cos q.2 ↔ q.2 < Real.pi / 2 := by
        constructor
        · intro hc
          by_contra hn
          exact (not_lt_of_ge (Real.cos_nonpos_of_pi_div_two_le_of_le
            (le_of_not_gt hn) (by linarith [Real.pi_pos]))) hc
        · intro htheta
          exact Real.cos_pos_of_mem_Ioo ⟨by linarith, htheta⟩
      have hy : 0 < q.1 * Real.sin q.2 ↔ 0 < q.2 :=
        (mul_pos_iff_of_pos_left hq.1).trans hsin
      have hmem : polarCoord.symm q ∈ D ↔ q ∈ E := by
        change (0 < (polarCoord.symm q).1 ∧
            0 < (polarCoord.symm q).2 ∧
            planarRadius (polarCoord.symm q) ≤ r) ↔
          (0 < q.1 ∧ q.1 ≤ r) ∧ 0 < q.2 ∧ q.2 < Real.pi / 2
        rw [hrs]
        simp only [polarCoord_symm_apply]
        constructor
        · rintro ⟨hx, hy', hr⟩
          have htheta0 := hy.mp hy'
          exact ⟨⟨hq.1, hr⟩, htheta0,
            (hcos htheta0).mp ((mul_pos_iff_of_pos_left hq.1).mp hx)⟩
        · rintro ⟨⟨_, hr⟩, htheta0, htheta1⟩
          exact ⟨(mul_pos_iff_of_pos_left hq.1).mpr
              ((hcos htheta0).mpr htheta1),
            hy.mpr htheta0, hr⟩
      by_cases hmemD : polarCoord.symm q ∈ D
      · rw [indicator_of_mem hqtarget, indicator_of_mem hmemD,
          indicator_of_mem (hmem.mp hmemD), hrs]
        simp [smul_eq_mul]
      · rw [indicator_of_mem hqtarget]
        simp only [Set.indicator]
        rw [if_neg hmemD, if_neg (mt hmem.mpr hmemD)]
        simp
    · have hqE : q ∉ E := by
        rintro ⟨⟨hq0, _⟩, htheta0, htheta1⟩
        apply hq
        simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo]
        exact ⟨hq0, lt_trans (neg_lt_zero.mpr Real.pi_pos) htheta0,
          htheta1.trans (by linarith [Real.pi_pos])⟩
      simp only [Set.indicator]
      rw [if_neg hq, if_neg hqE]
    ]
  rw [show (fun q : ℝ × ℝ => q.1 * g q.1) =
      fun q => (q.1 * g q.1) * (1 : ℝ) by funext q; ring]
  change (∫ q in Ioc 0 r ×ˢ Ioo 0 (Real.pi / 2),
    (q.1 * g q.1) * (1 : ℝ)) = _
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun s : ℝ => s * g s) (fun _ : ℝ => (1 : ℝ))
    (Ioc 0 r) (Ioo 0 (Real.pi / 2))]
  rw [setIntegral_one_eq_measureReal, Measure.real_def, Real.volume_Ioo]
  simp only [sub_zero, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 2)]
  rw [mul_comm, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  ring

/-- After bandwidth rescaling, the normalized squared-polynomial integral
over the first-quadrant sector is exactly `π / 2` times its radial energy. -/
-- @node: firstQuadrant_scaledPolynomial_integral
lemma firstQuadrant_scaledPolynomial_integral (p : ℕ) (t : Bool)
    (v : Fin (p + 1) → ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ z : ℝ × ℝ in
        {z | 0 < z.1 ∧ 0 < z.2 ∧ planarRadius z ≤ h},
      h⁻¹ ^ 2 *
        (∑ i, v i * (if t then planarRadius z / h else
          -(planarRadius z / h)) ^ (i : ℕ)) ^ 2) =
      (Real.pi / 2) *
        ∫ u in (0 : ℝ)..1,
          (∑ i, v i * (if t then u else -u) ^ (i : ℕ)) ^ 2 * u := by
  let F : ℝ → ℝ := fun u =>
    (∑ i, v i * (if t then u else -u) ^ (i : ℕ)) ^ 2 * u
  change (∫ z : ℝ × ℝ in
      {z | 0 < z.1 ∧ 0 < z.2 ∧ planarRadius z ≤ h},
    (fun s => h⁻¹ ^ 2 *
      (∑ i, v i * (if t then s / h else -(s / h)) ^ (i : ℕ)) ^ 2)
        (planarRadius z)) = _
  rw [firstQuadrant_radial_integral
    (fun s => h⁻¹ ^ 2 *
      (∑ i, v i * (if t then s / h else -(s / h)) ^ (i : ℕ)) ^ 2) h]
  rw [← intervalIntegral.integral_of_le hh.le]
  have hfun : (fun s : ℝ => (Real.pi / 2) * s *
      (h⁻¹ ^ 2 *
        (∑ i, v i * (if t then s / h else -(s / h)) ^ (i : ℕ)) ^ 2)) =
      fun s => (Real.pi / 2 * h⁻¹) * F (s / h) := by
    funext s
    dsimp [F]
    field_simp
    <;> ring
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_div F hh.ne']
  simp only [zero_div, div_self hh.ne', smul_eq_mul]
  change (Real.pi / 2 * h⁻¹) *
      (h * ∫ u in (0 : ℝ)..1, F u) = _
  calc
    _ = ((Real.pi / 2 * h⁻¹) * h) *
        ∫ u in (0 : ℝ)..1, F u := by ring
    _ = (Real.pi / 2) * ∫ u in (0 : ℝ)..1, F u := by
      rw [show (Real.pi / 2 * h⁻¹) * h = Real.pi / 2 by field_simp]
    _ = _ := rfl

/-- The population Gram quadratic form is the integral of the squared local
polynomial against the nonnegative arm and kernel weight. -/
-- @node: populationGram_quadratic_eq_integral
lemma populationGram_quadratic_eq_integral (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) {h : ℝ} (hh : h ≠ 0)
    (v : Fin (p + 1) → ℝ) :
    matrixQuadratic (populationGram P p t x h) v =
      ∫ w, h⁻¹ ^ 2 *
        (if (if t then 0 ≤ signedDistance (knownGeometry P) x (causalScore w)
          else signedDistance (knownGeometry P) x (causalScore w) < 0)
          then 1 else 0) *
        uniformKernel (signedDistance (knownGeometry P) x (causalScore w) / h) *
        (∑ i, v i * (signedDistance (knownGeometry P) x (causalScore w) / h) ^
          (i : ℕ)) ^ 2 ∂P.law := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let d : CausalObservation → ℝ := fun w =>
    signedDistance (knownGeometry P) x (causalScore w)
  let a : CausalObservation → ℝ := fun w => h⁻¹ ^ 2 *
    (if (if t then 0 ≤ d w else d w < 0) then 1 else 0) *
    uniformKernel (d w / h)
  have hscore : Measurable causalScore := measurable_snd.comp measurable_snd
  have hA0 : MeasurableSet P.A0 := P.A0_measurable
  have hA1 : MeasurableSet P.A1 := P.A1_measurable
  have hd : Measurable d := by
    dsimp [d, signedDistance, knownGeometry]
    apply Measurable.mul
    · apply Measurable.sub
      · exact (measurable_const.indicator hA1).comp hscore
      · exact (measurable_const.indicator hA0).comp hscore
    · exact continuous_dist.measurable.comp (hscore.prodMk measurable_const)
  have harmMeas : MeasurableSet {w | if t then 0 ≤ d w else d w < 0} := by
    cases t
    · exact measurableSet_lt hd measurable_const
    · exact measurableSet_le measurable_const hd
  have hkMeas : Measurable (fun w => uniformKernel (d w / h)) := by
    unfold uniformKernel
    exact (measurable_const.indicator measurableSet_Icc).comp (hd.div_const h)
  have ha : Measurable a := by
    dsimp [a]
    have hind : Measurable
        (fun w => if (if t then 0 ≤ d w else d w < 0) then (1 : ℝ) else 0) := by
      exact measurable_const.ite harmMeas measurable_const
    exact (measurable_const.mul hind).mul hkMeas
  have habs (w : CausalObservation) : |a w| ≤ |h⁻¹ ^ 2| := by
    dsimp [a]
    by_cases harm : if t then 0 ≤ d w else d w < 0
    · simp only [harm, if_true]
      by_cases hk : d w / h ∈ Icc (-1 : ℝ) 1
      · rw [uniformKernel, indicator_of_mem hk]
        simp
      · rw [uniformKernel, indicator_of_notMem hk, mul_zero, abs_zero]
        exact abs_nonneg _
    · simp [harm, sq_nonneg]
  have hentry (i j : Fin (p + 1)) : Integrable
      (fun w => a w * polyBasis p (d w / h) i * polyBasis p (d w / h) j)
      P.law := by
    apply Integrable.of_bound
      ((ha.fun_mul ((hd.div_const h).pow_const _)).fun_mul
        ((hd.div_const h).pow_const _) |>.aestronglyMeasurable)
      (h⁻¹ ^ 2)
    filter_upwards with w
    by_cases hk : d w / h ∈ Icc (-1 : ℝ) 1
    · have hdu : |d w / h| ≤ 1 := abs_le.mpr hk
      have hi : |(d w / h) ^ (i : ℕ)| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hdu
      have hj : |(d w / h) ^ (j : ℕ)| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hdu
      have haw : 0 ≤ a w := by
        dsimp [a]
        by_cases harm : if t then 0 ≤ d w else d w < 0
        · rw [if_pos harm, uniformKernel, indicator_of_mem hk]
          positivity
        · simp [harm]
      have haw' : a w ≤ h⁻¹ ^ 2 := by
        rw [← abs_of_nonneg haw, ← abs_of_nonneg (sq_nonneg h⁻¹)]
        exact habs w
      dsimp [polyBasis]
      rw [abs_mul, abs_mul]
      calc
        |a w| * |(d w / h) ^ (i : ℕ)| * |(d w / h) ^ (j : ℕ)|
            ≤ |h⁻¹ ^ 2| * 1 * 1 := by gcongr
        _ = h⁻¹ ^ 2 := by rw [abs_of_nonneg (sq_nonneg _)]; ring
    · have hzero : a w = 0 := by
        dsimp [a]
        rw [uniformKernel, indicator_of_notMem hk, mul_zero]
      rw [hzero]
      simp [sq_nonneg]
  unfold matrixQuadratic populationGram
  change (∑ i, ∑ j, v i * (∫ w, a w * polyBasis p (d w / h) i *
      polyBasis p (d w / h) j ∂P.law) * v j) = _
  calc
    _ = ∑ i, ∑ j, ∫ w, v i *
        (a w * polyBasis p (d w / h) i * polyBasis p (d w / h) j) * v j
        ∂P.law := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← integral_const_mul, ← integral_mul_const]
    _ = ∫ w, ∑ i, ∑ j, v i *
        (a w * polyBasis p (d w / h) i * polyBasis p (d w / h) j) * v j
        ∂P.law := by
      symm
      rw [integral_finset_sum Finset.univ (fun i _ =>
        integrable_finset_sum _ fun j _ =>
          ((hentry i j).const_mul (v i)).mul_const (v j))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum Finset.univ (fun j _ =>
        ((hentry i j).const_mul (v i)).mul_const (v j))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      have hrank := matrixQuadratic_polyBasis_rankOne p (a w) (d w / h) v
      change (∑ i, ∑ j, v i *
        (a w * polyBasis p (d w / h) i * polyBasis p (d w / h) j) * v j) =
        a w * (∑ i, v i * (d w / h) ^ (i : ℕ)) ^ 2
      simpa only [matrixQuadratic, mul_assoc, mul_left_comm, mul_comm] using hrank

end CausalSmith.Stat.BddUniformLogPenalty
