import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.Separability
import Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Population L² radius of the winsorized score

This module isolates the analytic localization estimate used by the
variance-adaptive entropy theorem.  The Euclidean density bound controls the
probability of a bandwidth ball, while the selected conditional moment bound
controls the winsorized response without introducing the winsorization level
into the population `L²` radius.
-/

open Causalean.Stat.Concentration
open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

private lemma winsorize_abs_le_abs (B y : ℝ) (hB : 0 ≤ B) :
    |winsorize B y| ≤ |y| := by
  unfold winsorize
  split_ifs with hy hy0
  · rw [abs_neg, abs_of_nonneg (le_min (abs_nonneg y) hB)]
    exact min_le_left _ _
  · simp [hy0]
  · rw [abs_of_nonneg (le_min (abs_nonneg y) hB)]
    exact min_le_left _ _

private lemma winsorize_abs_le (B y : ℝ) (hB : 0 ≤ B) :
    |winsorize B y| ≤ B := by
  unfold winsorize
  split_ifs with hy hy0
  · rw [abs_neg, abs_of_nonneg (le_min (abs_nonneg y) hB)]
    exact min_le_right _ _
  · simpa [hy0] using hB
  · rw [abs_of_nonneg (le_min (abs_nonneg y) hB)]
    exact min_le_right _ _

private lemma abs_clip_le (C y : ℝ) (hC : 0 ≤ C) : |clip C y| ≤ C := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

private lemma winsorizedScoreFunction_measurable (P : A1A2Law) (p : ℕ)
    (h B C : ℝ) (i : WinsorizedScoreIndex p) :
    Measurable (winsorizedScoreFunction P p h B C i) := by
  classical
  have hscore : Measurable causalScore := by
    unfold causalScore
    fun_prop
  have hA0 : MeasurableSet P.A0 := P.A0_measurable
  have hA1 : MeasurableSet P.A1 := P.A1_measurable
  have htreat : Measurable (treatment P) := by
    unfold treatment
    exact measurable_const.indicator (hA1.preimage hscore)
  have harm (t : Bool) : Measurable (armCoord t) := by
    cases t <;> unfold armCoord <;> simp only [Bool.false_eq_true, if_false,
      if_true] <;> fun_prop
  have hout : Measurable (observedOutcome P) := by
    unfold observedOutcome
    exact (htreat.mul (harm true)).add
      ((measurable_const.sub htreat).mul (harm false))
  have hd : Measurable (fun z =>
      signedDistance (knownGeometry P) i.2.1 (causalScore z)) := by
    have hi1 : Measurable (fun z => P.A1.indicator (fun _ => (1 : ℝ))
        (causalScore z)) := measurable_const.indicator (hA1.preimage hscore)
    have hi0 : Measurable (fun z => P.A0.indicator (fun _ => (1 : ℝ))
        (causalScore z)) := measurable_const.indicator (hA0.preimage hscore)
    have hdist : Measurable (fun z => dist (causalScore z) i.2.1) :=
      hscore.dist measurable_const
    exact (hi1.sub hi0).mul hdist
  have hsigned : Measurable (fun z => if signedArm i.1
      (signedDistance (knownGeometry P) i.2.1 (causalScore z)) then (1 : ℝ) else 0) := by
    cases i.1
    · exact Measurable.ite (measurableSet_lt hd measurable_const)
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le measurable_const hd)
        measurable_const measurable_const
  unfold winsorizedScoreFunction
  dsimp only
  exact (((hsigned.mul (uniformKernel_measurable.comp (hd.div_const h))).mul
    ((polyBasis_apply_measurable p i.2.2.2).comp (hd.div_const h))).mul
      (((winsorize_measurable B).comp hout).sub
        (Finset.measurable_sum _ fun k _ =>
          ((polyBasis_apply_measurable p k).comp (hd.div_const h)).mul
            measurable_const)))

private lemma condKer_sq_lintegral_le (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (t : Bool) (x : Score) (hx : x ∈ P.support) :
    (∫⁻ y, ENNReal.ofReal (y ^ 2) ∂selectedA1A2CondKer P ν L t x) ≤
      ENNReal.ofReal (1 + L) := by
  have hK : Nonempty (A1A2KernelWitness P ν L) :=
    hP.2.2.2.2.2.2.2.1.1
  letI : IsProbabilityMeasure (selectedA1A2CondKer P ν L t x) :=
    (selectedA1A2CondKer_markov hK t).isProbabilityMeasure x
  have hν : 2 ≤ ν := hP.1
  have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
  have hpoint (y : ℝ) : y ^ 2 ≤ 1 + |y| ^ (2 + ν) := by
    by_cases hy : |y| ≤ 1
    · have : y ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg y]
      exact this.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg y) _))
    · have hy1 : 1 ≤ |y| := le_of_not_ge hy
      have hp : |y| ^ (2 : ℝ) ≤ |y| ^ (2 + ν) :=
        Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      rw [Real.rpow_two] at hp
      nlinarith [sq_abs y]
  calc
    (∫⁻ y, ENNReal.ofReal (y ^ 2) ∂selectedA1A2CondKer P ν L t x) ≤
        ∫⁻ y, (1 + ENNReal.ofReal (|y| ^ (2 + ν)))
          ∂selectedA1A2CondKer P ν L t x := by
      exact lintegral_mono fun y => by
        calc
          ENNReal.ofReal (y ^ 2) ≤
              ENNReal.ofReal (1 + |y| ^ (2 + ν)) :=
            ENNReal.ofReal_le_ofReal (hpoint y)
          _ = ENNReal.ofReal 1 + ENNReal.ofReal (|y| ^ (2 + ν)) :=
            ENNReal.ofReal_add (by norm_num)
              (Real.rpow_nonneg (abs_nonneg y) _)
          _ = 1 + ENNReal.ofReal (|y| ^ (2 + ν)) := by simp
    _ = 1 + selectedA1A2CondAbsMoment P ν L t x := by
      rw [lintegral_add_left (by fun_prop), lintegral_const]
      simp [selectedA1A2CondAbsMoment]
    _ ≤ 1 + ENNReal.ofReal L := add_le_add_right
      (hP.2.2.2.2.2.2.2.2.2.1 t x hx) 1
    _ = ENNReal.ofReal (1 + L) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hL]

-- @node: marginal_closedBall_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma marginal_closedBall_le (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (x : Score) (h : ℝ) (hh : 0 < h) :
    Measure.map causalScore P.law (Metric.closedBall x h) ≤
      ENNReal.ofReal (4 * L * h ^ 2) := by
  have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
  rw [P.marginal_eq, withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  calc
    (∫⁻ z in Metric.closedBall x h,
        ENNReal.ofReal (P.support.indicator P.density z) ∂volume) ≤
        ∫⁻ _z in Metric.closedBall x h, ENNReal.ofReal L ∂volume := by
      apply lintegral_mono_ae
      filter_upwards with z
      by_cases hz : z ∈ P.support
      · rw [indicator_of_mem hz]
        exact ENNReal.ofReal_le_ofReal (hP.2.2.2.2.1 z hz).2
      · rw [indicator_of_notMem hz]
        simp
    _ = ENNReal.ofReal L * volume (Metric.closedBall x h) := by
      rw [setLIntegral_const]
    _ = ENNReal.ofReal (L * (Real.pi * h ^ 2)) := by
      rw [EuclideanSpace.volume_closedBall_fin_two,
        ← ENNReal.ofReal_pow hh.le,
        ← ENNReal.ofReal_mul (sq_nonneg h), ← ENNReal.ofReal_mul hL]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (4 * L * h ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have hmul := mul_le_mul_of_nonneg_right Real.pi_le_four
        (mul_nonneg hL (sq_nonneg h))
      nlinarith

-- @node: localized_arm_sq_lintegral_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma localized_arm_sq_lintegral_le (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (t : Bool) (x : Score) (h : ℝ) (hh : 0 < h) :
    (∫⁻ w, (Metric.closedBall x h).indicator
      (fun _ => ENNReal.ofReal ((armCoord t w) ^ 2)) (causalScore w) ∂P.law) ≤
      ENNReal.ofReal ((1 + L) * (4 * L * h ^ 2)) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hK : Nonempty (A1A2KernelWitness P ν L) :=
    hP.2.2.2.2.2.2.2.1.1
  letI : ProbabilityTheory.IsMarkovKernel (selectedA1A2CondKer P ν L t) :=
    selectedA1A2CondKer_markov hK t
  let μ := Measure.map causalScore P.law
  let F : (Score × ℝ) → ENNReal := fun q =>
    (Metric.closedBall x h).indicator (fun _ => ENNReal.ofReal (q.2 ^ 2)) q.1
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have harm : Measurable (armCoord t) := by
    cases t <;> unfold armCoord <;> simp only [Bool.false_eq_true, if_false,
      if_true] <;> fun_prop
  have hpair : Measurable (fun w => (causalScore w, armCoord t w)) :=
    hscore.prodMk harm
  have hF : Measurable F := by
    apply Measurable.indicator
    · fun_prop
    · exact Metric.isClosed_closedBall.measurableSet.preimage measurable_fst
  have hsupp : ∀ᵐ z ∂μ, z ∈ P.support := by
    change ∀ᵐ z ∂Measure.map causalScore P.law, z ∈ P.support
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  calc
    (∫⁻ w, (Metric.closedBall x h).indicator
        (fun _ => ENNReal.ofReal ((armCoord t w) ^ 2)) (causalScore w) ∂P.law) =
        ∫⁻ q, F q ∂Measure.map (fun w => (causalScore w, armCoord t w)) P.law := by
      rw [lintegral_map hF hpair]
    _ = ∫⁻ z, ∫⁻ y, F (z, y) ∂selectedA1A2CondKer P ν L t z ∂μ := by
      rw [← selectedA1A2CondKer_disint hK t, Measure.lintegral_compProd hF]
    _ ≤ ∫⁻ z, (Metric.closedBall x h).indicator
        (fun _ => ENNReal.ofReal (1 + L)) z ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hsupp] with z hz
      by_cases hzb : z ∈ Metric.closedBall x h
      · simp only [F, indicator_of_mem hzb]
        exact condKer_sq_lintegral_le p ν L P hP t z hz
      · simp [F, indicator_of_notMem hzb]
    _ = ENNReal.ofReal (1 + L) * μ (Metric.closedBall x h) := by
      rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        setLIntegral_const]
    _ ≤ ENNReal.ofReal (1 + L) * ENNReal.ofReal (4 * L * h ^ 2) :=
      mul_le_mul_right (marginal_closedBall_le p ν L P hP x h hh) _
    _ = ENNReal.ofReal ((1 + L) * (4 * L * h ^ 2)) := by
      have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
      rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + L)]

private lemma poly_clip_sum_abs_le (p : ℕ) (u R : ℝ)
    (b : Fin (p + 1) → ℝ) (hu : |u| ≤ 1) (hR : 0 ≤ R) :
    |∑ k, polyBasis p u k * clip R (b k)| ≤ (p + 1 : ℝ) * R := by
  calc
    |∑ k, polyBasis p u k * clip R (b k)| ≤
        ∑ k, |polyBasis p u k * clip R (b k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (p + 1), R := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [abs_mul]
      apply (mul_le_mul
        (show |polyBasis p u k| ≤ 1 by
          unfold polyBasis
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg u) hu)
        (abs_clip_le R (b k) hR) (abs_nonneg _) (by norm_num)).trans_eq
      · ring
    _ = (p + 1 : ℝ) * R := by simp

-- @node: winsorizedScore_sq_pointwise_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma winsorizedScore_sq_pointwise_le (P : A1A2Law) (p : ℕ)
    (h B R : ℝ) (hh : 0 < h) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (i : WinsorizedScoreIndex p) (w : CausalObservation)
    (hw : causalScore w ∈ P.support) :
    (winsorizedScoreFunction P p h B R i w) ^ 2 ≤
      2 * (Metric.closedBall i.2.1 h).indicator
        (fun _ => (armCoord false w) ^ 2 + (armCoord true w) ^ 2 +
          ((p + 1 : ℝ) * R) ^ 2) (causalScore w) := by
  classical
  let z := causalScore w
  let x := i.2.1
  let d := signedDistance (knownGeometry P) x z
  have hpart : z ∈ P.A0 ∪ P.A1 := by
    rw [P.assignment_partition.1]
    exact hw
  rcases hpart with hz0 | hz1
  · have hz1n : z ∉ P.A1 := fun hz1 => P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
    have hd : d = -dist z x := by
      simp [d, signedDistance, knownGeometry, indicator_of_mem hz0,
        indicator_of_notMem hz1n]
    have hout : observedOutcome P w = armCoord false w := by
      rw [observedOutcome, treatment,
        indicator_of_notMem (by simpa [z] using hz1n)]
      ring
    by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
    · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
      have hball : z ∈ Metric.closedBall x h := by
        rw [Metric.mem_closedBall]
        rw [hd, abs_div, abs_neg, abs_of_pos hh] at hu
        have := (div_le_iff₀ hh).mp hu
        simpa [abs_of_nonneg (dist_nonneg : 0 ≤ dist z x)] using this
      have hpolyj : |polyBasis p (d / h) i.2.2.2| ≤ 1 := by
        unfold polyBasis
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hu
      have hsum := poly_clip_sum_abs_le p (d / h) R i.2.2.1 hu hR
      have hwin := winsorize_abs_le_abs B (armCoord false w) hB
      rw [winsorizedScoreFunction, show observedOutcome P w = armCoord false w from hout,
        uniformKernel, indicator_of_mem hk, indicator_of_mem hball]
      split_ifs
      · have habs : |polyBasis p (d / h) i.2.2.2 *
            (winsorize B (armCoord false w) -
              ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k))| ≤
            |armCoord false w| + (p + 1 : ℝ) * R := by
          rw [abs_mul]
          calc
            _ ≤ 1 * |winsorize B (armCoord false w) -
                ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k)| :=
              mul_le_mul_of_nonneg_right hpolyj (abs_nonneg _)
            _ ≤ _ := by
              rw [one_mul]
              exact (abs_sub _ _).trans (add_le_add hwin hsum)
        have hsq := mul_self_le_mul_self (abs_nonneg _) habs
        rw [← pow_two, ← pow_two, sq_abs] at hsq
        have hfinal : (polyBasis p (d / h) i.2.2.2 *
            (winsorize B (armCoord false w) -
              ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k))) ^ 2 ≤
            2 * ((armCoord false w) ^ 2 + (armCoord true w) ^ 2 +
              ((p + 1 : ℝ) * R) ^ 2) := by
          nlinarith [sq_abs (armCoord false w), sq_nonneg (armCoord true w),
            sq_nonneg (|armCoord false w| - (p + 1 : ℝ) * R)]
        simpa [d, z, x] using hfinal
      · nlinarith [sq_nonneg (armCoord false w), sq_nonneg (armCoord true w),
          sq_nonneg ((p + 1 : ℝ) * R)]
    · rw [winsorizedScoreFunction, uniformKernel, indicator_of_notMem hk]
      simp
      exact indicator_nonneg (fun _ _ => by
        nlinarith [sq_nonneg (armCoord false w), sq_nonneg (armCoord true w),
          sq_nonneg ((p + 1 : ℝ) * R)]) (causalScore w)
  · have hz0n : z ∉ P.A0 := fun hz0 => P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
    have hd : d = dist z x := by
      simp [d, signedDistance, knownGeometry, indicator_of_mem hz1,
        indicator_of_notMem hz0n]
    have hout : observedOutcome P w = armCoord true w := by
      rw [observedOutcome, treatment,
        indicator_of_mem (by simpa [z] using hz1)]
      ring
    by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
    · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
      have hball : z ∈ Metric.closedBall x h := by
        rw [Metric.mem_closedBall]
        rw [hd, abs_div, abs_of_pos hh] at hu
        have := (div_le_iff₀ hh).mp hu
        simpa [abs_of_nonneg (dist_nonneg : 0 ≤ dist z x)] using this
      have hpolyj : |polyBasis p (d / h) i.2.2.2| ≤ 1 := by
        unfold polyBasis
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hu
      have hsum := poly_clip_sum_abs_le p (d / h) R i.2.2.1 hu hR
      have hwin := winsorize_abs_le_abs B (armCoord true w) hB
      rw [winsorizedScoreFunction, show observedOutcome P w = armCoord true w from hout,
        uniformKernel, indicator_of_mem hk, indicator_of_mem hball]
      split_ifs
      · have habs : |polyBasis p (d / h) i.2.2.2 *
            (winsorize B (armCoord true w) -
              ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k))| ≤
            |armCoord true w| + (p + 1 : ℝ) * R := by
          rw [abs_mul]
          calc
            _ ≤ 1 * |winsorize B (armCoord true w) -
                ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k)| :=
              mul_le_mul_of_nonneg_right hpolyj (abs_nonneg _)
            _ ≤ _ := by
              rw [one_mul]
              exact (abs_sub _ _).trans (add_le_add hwin hsum)
        have hsq := mul_self_le_mul_self (abs_nonneg _) habs
        rw [← pow_two, ← pow_two, sq_abs] at hsq
        have hfinal : (polyBasis p (d / h) i.2.2.2 *
            (winsorize B (armCoord true w) -
              ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k))) ^ 2 ≤
            2 * ((armCoord false w) ^ 2 + (armCoord true w) ^ 2 +
              ((p + 1 : ℝ) * R) ^ 2) := by
          nlinarith [sq_abs (armCoord true w), sq_nonneg (armCoord false w),
            sq_nonneg (|armCoord true w| - (p + 1 : ℝ) * R)]
        simpa [d, z, x] using hfinal
      · nlinarith [sq_nonneg (armCoord false w), sq_nonneg (armCoord true w),
          sq_nonneg ((p + 1 : ℝ) * R)]
    · rw [winsorizedScoreFunction, uniformKernel, indicator_of_notMem hk]
      simp
      exact indicator_nonneg (fun _ _ => by
        nlinarith [sq_nonneg (armCoord false w), sq_nonneg (armCoord true w),
          sq_nonneg ((p + 1 : ℝ) * R)]) (causalScore w)

private lemma winsorizedScore_abs_le_envelope (P : A1A2Law) (p : ℕ)
    (h B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (i : WinsorizedScoreIndex p) (w : CausalObservation) :
    |winsorizedScoreFunction P p h B R i w| ≤ B + (p + 1 : ℝ) * R := by
  classical
  let d := signedDistance (knownGeometry P) i.2.1 (causalScore w)
  by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
  · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
    have hpolyj : |polyBasis p (d / h) i.2.2.2| ≤ 1 := by
      unfold polyBasis
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hu
    have hsum := poly_clip_sum_abs_le p (d / h) R i.2.2.1 hu hR
    have hwin := winsorize_abs_le B (observedOutcome P w) hB
    rw [winsorizedScoreFunction, uniformKernel, indicator_of_mem hk]
    split_ifs
    · simp only [one_mul, abs_mul]
      calc
        |polyBasis p (d / h) i.2.2.2| *
            |winsorize B (observedOutcome P w) -
              ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k)| ≤
            1 * |winsorize B (observedOutcome P w) -
              ∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k)| :=
          mul_le_mul_of_nonneg_right hpolyj (abs_nonneg _)
        _ ≤ _ := by
          rw [one_mul]
          exact (abs_sub _ _).trans (add_le_add hwin hsum)
    · simp
      exact add_nonneg hB (by positivity)
  · rw [winsorizedScoreFunction, uniformKernel, indicator_of_notMem hk]
    simp
    exact add_nonneg hB (by positivity)

private lemma localized_const_sq_lintegral_le (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (x : Score) (h q : ℝ) (hh : 0 < h) :
    (∫⁻ w, (Metric.closedBall x h).indicator
      (fun _ => ENNReal.ofReal (q ^ 2)) (causalScore w) ∂P.law) ≤
      ENNReal.ofReal (q ^ 2 * (4 * L * h ^ 2)) := by
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have hfun : Measurable (fun z : Score =>
      (Metric.closedBall x h).indicator (fun _ => ENNReal.ofReal (q ^ 2)) z) := by
    apply Measurable.indicator measurable_const
    exact Metric.isClosed_closedBall.measurableSet
  calc
    (∫⁻ w, (Metric.closedBall x h).indicator
        (fun _ => ENNReal.ofReal (q ^ 2)) (causalScore w) ∂P.law) =
        ∫⁻ z, (Metric.closedBall x h).indicator
          (fun _ => ENNReal.ofReal (q ^ 2)) z ∂Measure.map causalScore P.law := by
      rw [lintegral_map hfun hscore]
    _ = ENNReal.ofReal (q ^ 2) *
        Measure.map causalScore P.law (Metric.closedBall x h) := by
      rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        setLIntegral_const]
    _ ≤ ENNReal.ofReal (q ^ 2) * ENNReal.ofReal (4 * L * h ^ 2) :=
      mul_le_mul_right (marginal_closedBall_le p ν L P hP x h hh) _
    _ = ENNReal.ofReal (q ^ 2 * (4 * L * h ^ 2)) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg q)]

-- @node: separableWinsorizedScore_sq_pointwise_le
/-- The squared separable winsorized score is bounded pointwise by a localized
sum of the two arm squares and the clipped polynomial-envelope square. -/
lemma separableWinsorizedScore_sq_pointwise_le
    (P : A1A2Law) (p : ℕ) (h B R : ℝ) (hh : 0 < h) (hB : 0 ≤ B)
    (hR : 0 ≤ R)
    (i : SeparableWinsorizedScoreIndex P p h)
    (w : CausalObservation) (hw : causalScore w ∈ P.support) :
    (separableWinsorizedScoreFunction P p h B R i w) ^ 2 ≤
      3 * ((2 : ℝ) ^ p) ^ 2 *
        (Metric.closedBall i.2.2.1.1 (2 * h)).indicator
          (fun _ => (armCoord false w) ^ 2 + (armCoord true w) ^ 2 +
            ((p + 1 : ℝ) * (2 : ℝ) ^ p * R) ^ 2)
          (causalScore w) := by
  let d := signedDistance (knownGeometry P) i.2.2.1.1 (causalScore w)
  have hq : 0 < i.1.1 := lt_of_lt_of_le hh i.1.2.1
  have habs : |d| = dist (causalScore w) i.2.2.1.1 := by
    rcases (show causalScore w ∈ P.A0 ∪ P.A1 by
      simpa [P.assignment_partition.1] using hw) with hw0 | hw1
    · have hw1n : causalScore w ∉ P.A1 := fun hw1 =>
        P.assignment_partition.2.le_bot ⟨hw0, hw1⟩
      simp [d, signedDistance, knownGeometry, indicator_of_mem hw0,
        indicator_of_notMem hw1n]
    · have hw0n : causalScore w ∉ P.A0 := fun hw0 =>
        P.assignment_partition.2.le_bot ⟨hw0, hw1⟩
      simp [d, signedDistance, knownGeometry, indicator_of_mem hw1,
        indicator_of_notMem hw0n]
  by_cases hactive : |d| ≤ i.1.1
  · have hdist2 : dist (causalScore w) i.2.2.1.1 ≤ 2 * h := by
      rw [← habs]
      exact hactive.trans i.1.2.2.le
    have hball : causalScore w ∈ Metric.closedBall i.2.2.1.1 (2 * h) := by
      simpa [Metric.mem_closedBall, dist_comm] using hdist2
    have hbound := separableWinsorizedScoreFunction_bound P p h B R hh hB hR i w
    rw [indicator_of_mem hball]
    have ha0 : 0 ≤ |armCoord false w| := abs_nonneg _
    have ha1 : 0 ≤ |armCoord true w| := abs_nonneg _
    let c₀ : ℝ := (p + 1 : ℝ) * (2 : ℝ) ^ p * R
    have hbound' :
        |separableWinsorizedScoreFunction P p h B R i w| ≤
          (2 : ℝ) ^ p *
            (|armCoord false w| + |armCoord true w| + c₀) := by
      simpa [c₀] using hbound
    have hc : 0 ≤ c₀ := by dsimp [c₀]; positivity
    have hM : 0 ≤ (2 : ℝ) ^ p := by positivity
    have hsquare := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hM (add_nonneg (add_nonneg ha0 ha1) hc))).2 hbound'
    rw [sq_abs] at hsquare
    nlinarith [sq_nonneg (|armCoord false w| - |armCoord true w|),
      sq_nonneg (|armCoord false w| - c₀),
      sq_nonneg (|armCoord true w| - c₀), sq_abs (armCoord false w),
      sq_abs (armCoord true w)]
  · have hk : uniformKernel (d / i.1.1) = 0 := by
      rw [uniformKernel_div_eq_if_abs_le d i.1.1 hq, if_neg hactive]
    simp [separableWinsorizedScoreFunction, d, hk]
    apply mul_nonneg
    · positivity
    · by_cases hball : causalScore w ∈ Metric.closedBall i.2.2.1.1 (2 * h)
      · rw [indicator_of_mem hball]
        positivity
      · rw [indicator_of_notMem hball]

-- @node: separableWinsorizedScore_abs_le_envelope
/-- The absolute separable winsorized score is uniformly bounded by the
winsorization level plus the clipped polynomial envelope. -/
lemma separableWinsorizedScore_abs_le_envelope
    (P : A1A2Law) (p : ℕ) (h B R : ℝ) (hh : 0 < h) (hB : 0 ≤ B)
    (hR : 0 ≤ R)
    (i : SeparableWinsorizedScoreIndex P p h) (w : CausalObservation) :
    |separableWinsorizedScoreFunction P p h B R i w| ≤
      (2 : ℝ) ^ p * (B + (p + 1 : ℝ) * (2 : ℝ) ^ p * R) := by
  classical
  let d := signedDistance (knownGeometry P) i.2.2.1.1 (causalScore w)
  have hq : 0 < i.1.1 := lt_of_lt_of_le hh i.1.2.1
  simp only [separableWinsorizedScoreFunction]
  rw [show uniformKernel (d / i.1.1) = if |d| ≤ i.1.1 then 1 else 0 from
    uniformKernel_div_eq_if_abs_le d i.1.1 hq]
  by_cases hdq : |d| ≤ i.1.1
  · rw [if_pos hdq]
    have hu : |d / h| ≤ 2 := by
      rw [abs_div, abs_of_pos hh]
      exact (div_le_div_of_nonneg_right hdq hh.le).trans
        ((div_lt_iff₀ hh).2 i.1.2.2).le
    have hpoly (k : Fin (p + 1)) : |polyBasis p (d / h) k| ≤ (2 : ℝ) ^ p := by
      unfold polyBasis
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) hu k).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ k.isLt))
    have hsum : |∑ k, polyBasis p (d / h) k * clip R (i.2.2.2.1 k)| ≤
        (p + 1 : ℝ) * (2 : ℝ) ^ p * R := by
      calc
        _ ≤ ∑ k, |polyBasis p (d / h) k * clip R (i.2.2.2.1 k)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (p + 1), (2 : ℝ) ^ p * R := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (hpoly k) (abs_clip_le R _ hR)
            (abs_nonneg _) (by positivity)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring
    have hwin := winsorize_abs_le B (observedOutcome P w) hB
    split_ifs
    · simp only [one_mul, abs_mul]
      exact mul_le_mul (hpoly _) ((abs_sub _ _).trans (add_le_add hwin hsum))
        (abs_nonneg _) (by positivity)
    · simp
      positivity
  · have hdq' : ¬ |signedDistance (knownGeometry P) i.2.2.1.1
        (causalScore w)| ≤ i.1.1 := by simpa [d] using hdq
    rw [if_neg hdq']
    simp only [mul_zero, zero_mul, abs_zero]
    exact mul_nonneg (by positivity) (add_nonneg hB (by positivity))

/-- The one-sided bandwidth enlargement has population `L²` radius `O(h)`.
The proof uses the defining bound `q < 2h` to localize every nonzero score in
the radius-`2h` Euclidean ball. -/
-- @node: separableWinsorizedScore_hasUniformL2Radius_explicit
lemma separableWinsorizedScore_hasUniformL2Radius_explicit
    (p : ℕ) (ν L R : ℝ) (hR : 0 < R) :
    ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
      ∀ i : SeparableWinsorizedScoreIndex P p h,
        measureL2Dist P.law
          (separableWinsorizedScoreFunction P p h B R i)
          (fun _ => 0) ≤
            (1 + |3 * ((2 : ℝ) ^ p) ^ 2 *
              (2 * (1 + L) + ((p + 1 : ℝ) * (2 : ℝ) ^ p * R) ^ 2) *
              (16 * L)|) * h := by
  let M : ℝ := (2 : ℝ) ^ p
  let q : ℝ := (p + 1 : ℝ) * M * R
  let K : ℝ := 3 * M ^ 2 * (2 * (1 + L) + q ^ 2) * (16 * L)
  intro P hP h B hh _hhB hB i
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let f := separableWinsorizedScoreFunction P p h B R i
  have hfmeas : Measurable f :=
    separableWinsorizedScoreFunction_measurable P p h B R i
  have hfint : Integrable (fun w => (f w) ^ 2) P.law := by
    let U := M * (B + (p + 1 : ℝ) * M * R)
    apply Integrable.of_bound (hfmeas.pow_const 2).aestronglyMeasurable (U ^ 2)
    filter_upwards with w
    have hf := separableWinsorizedScore_abs_le_envelope P p h B R hh hB0 hR.le i w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hs := (sq_le_sq₀ (abs_nonneg (f w)) hU).2 (by
      simpa [f, U, M] using hf)
    simpa [sq_abs] using hs
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have hsmeas : MeasurableSet P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.isClosed_support.measurableSet
  have hsuppMap : ∀ᵐ z ∂Measure.map causalScore P.law, z ∈ P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  have hsupp : ∀ᵐ w ∂P.law, causalScore w ∈ P.support :=
    (ae_map_iff hscore.aemeasurable hsmeas).mp hsuppMap
  let g0 : CausalObservation → ENNReal := fun w =>
    (Metric.closedBall i.2.2.1.1 (2 * h)).indicator
      (fun _ => ENNReal.ofReal ((armCoord false w) ^ 2)) (causalScore w)
  let g1 : CausalObservation → ENNReal := fun w =>
    (Metric.closedBall i.2.2.1.1 (2 * h)).indicator
      (fun _ => ENNReal.ofReal ((armCoord true w) ^ 2)) (causalScore w)
  let gc : CausalObservation → ENNReal := fun w =>
    (Metric.closedBall i.2.2.1.1 (2 * h)).indicator
      (fun _ => ENNReal.ofReal (q ^ 2)) (causalScore w)
  have hg0 : Measurable g0 := by
    apply Measurable.indicator
    · have harm : Measurable (armCoord false) := by
        unfold armCoord; simp only [Bool.false_eq_true, if_false]; fun_prop
      exact (harm.pow_const 2).ennreal_ofReal
    · exact Metric.isClosed_closedBall.measurableSet.preimage hscore
  have hg1 : Measurable g1 := by
    apply Measurable.indicator
    · have harm : Measurable (armCoord true) := by
        unfold armCoord; simp only [if_true]; fun_prop
      exact (harm.pow_const 2).ennreal_ofReal
    · exact Metric.isClosed_closedBall.measurableSet.preimage hscore
  have hgc : Measurable gc := by
    apply Measurable.indicator measurable_const
    exact Metric.isClosed_closedBall.measurableSet.preimage hscore
  have hlin : (∫⁻ w, ENNReal.ofReal ((f w) ^ 2) ∂P.law) ≤
      ENNReal.ofReal (K * h ^ 2) := by
    calc
      (∫⁻ w, ENNReal.ofReal ((f w) ^ 2) ∂P.law) ≤
          ∫⁻ w, ENNReal.ofReal (3 * M ^ 2) * (g0 w + g1 w + gc w) ∂P.law := by
        apply lintegral_mono_ae
        filter_upwards [hsupp] with w hw
        have hp := separableWinsorizedScore_sq_pointwise_le
          P p h B R hh hB0 hR.le i w hw
        apply ENNReal.ofReal_le_ofReal at hp
        by_cases hball : causalScore w ∈ Metric.closedBall i.2.2.1.1 (2 * h)
        · simpa [f, g0, g1, gc, q, M, indicator_of_mem hball,
            ENNReal.ofReal_mul (by positivity : 0 ≤ 3 * ((2 : ℝ) ^ p) ^ 2),
            ENNReal.ofReal_add (sq_nonneg (armCoord false w))
              (sq_nonneg (armCoord true w)),
            ENNReal.ofReal_add
              (add_nonneg (sq_nonneg (armCoord false w)) (sq_nonneg (armCoord true w)))
              (sq_nonneg ((p + 1 : ℝ) * (2 : ℝ) ^ p * R))] using hp
        · simpa [f, g0, g1, gc, indicator_of_notMem hball] using hp
      _ = ENNReal.ofReal (3 * M ^ 2) *
          ((∫⁻ w, g0 w ∂P.law) + (∫⁻ w, g1 w ∂P.law) +
            (∫⁻ w, gc w ∂P.law)) := by
        rw [lintegral_const_mul (ENNReal.ofReal (3 * M ^ 2))
            ((hg0.fun_add hg1).fun_add hgc),
          lintegral_add_left (hg0.fun_add hg1), lintegral_add_left hg0]
      _ ≤ ENNReal.ofReal (3 * M ^ 2) *
          (ENNReal.ofReal ((1 + L) * (4 * L * (2 * h) ^ 2)) +
            ENNReal.ofReal ((1 + L) * (4 * L * (2 * h) ^ 2)) +
            ENNReal.ofReal (q ^ 2 * (4 * L * (2 * h) ^ 2))) := by
        gcongr
        · exact localized_arm_sq_lintegral_le p ν L P hP false
            i.2.2.1.1 (2 * h) (by positivity)
        · exact localized_arm_sq_lintegral_le p ν L P hP true
            i.2.2.1.1 (2 * h) (by positivity)
        · exact localized_const_sq_lintegral_le p ν L P hP
            i.2.2.1.1 (2 * h) q (by positivity)
      _ = ENNReal.ofReal (K * h ^ 2) := by
        have hA : 0 ≤ (1 + L) * (4 * L * (2 * h) ^ 2) := by positivity
        have hD : 0 ≤ q ^ 2 * (4 * L * (2 * h) ^ 2) := by positivity
        rw [← ENNReal.ofReal_add hA hA,
          ← ENNReal.ofReal_add (add_nonneg hA hA) hD,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 * M ^ 2)]
        congr 1
        dsimp [K]
        ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hint : ∫ w, (f w) ^ 2 ∂P.law ≤ K * h ^ 2 := by
    rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (sq_nonneg h))]
    rw [ofReal_integral_eq_lintegral_ofReal hfint
      (ae_of_all _ fun w => sq_nonneg (f w))]
    exact hlin
  unfold measureL2Dist
  simp only [sub_zero]
  have hsqrt := Real.sqrt_le_sqrt hint
  rw [Real.sqrt_mul hK (h ^ 2), Real.sqrt_sq_eq_abs, abs_of_pos hh] at hsqrt
  have hsqrtK : Real.sqrt K ≤ 1 + K := by
    nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K,
      sq_nonneg (Real.sqrt K - 1)]
  have hKabs : |K| = K := abs_of_nonneg hK
  simpa only [f, K, M, q, hKabs] using
    hsqrt.trans (mul_le_mul_of_nonneg_right hsqrtK hh.le)

/-- The explicit separable score radius packaged in the existential form used
by the entropy layer. -/
-- @node: separableWinsorizedScore_hasUniformL2Radius_at
lemma separableWinsorizedScore_hasUniformL2Radius_at
    (p : ℕ) (ν L R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
      ∀ i : SeparableWinsorizedScoreIndex P p h,
        measureL2Dist P.law
          (separableWinsorizedScoreFunction P p h B R i)
          (fun _ => 0) ≤ C * h := by
  refine ⟨1 + |3 * ((2 : ℝ) ^ p) ^ 2 *
      (2 * (1 + L) + ((p + 1 : ℝ) * (2 : ℝ) ^ p * R) ^ 2) *
      (16 * L)|, by positivity, ?_⟩
  exact separableWinsorizedScore_hasUniformL2Radius_explicit p ν L R hR

/-- The unit-radius specialization of the separable population `L²` bound. -/
-- @node: separableWinsorizedScore_hasUniformL2Radius
lemma separableWinsorizedScore_hasUniformL2Radius
    (p : ℕ) (ν L : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
      ∀ i : SeparableWinsorizedScoreIndex P p h,
        measureL2Dist P.law
          (separableWinsorizedScoreFunction P p h B 1 i)
          (fun _ => 0) ≤ C * h := by
  exact separableWinsorizedScore_hasUniformL2Radius_at p ν L 1 (by norm_num)

/-- At every positive coefficient clipping radius, admissible winsorized scores
have population `L²` norm at most `C h`, uniformly over centers, arms,
coordinates, and winsorization levels `B > h` with `B ≥ 1`. -/
-- @node: winsorizedScore_hasUniformL2Radius_at
lemma winsorizedScore_hasUniformL2Radius_at
    (p : ℕ) (ν L R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
      ∀ i : WinsorizedScoreIndex p,
        measureL2Dist P.law (winsorizedScoreFunction P p h B R i)
          (fun _ => 0) ≤ C * h := by
  let q : ℝ := p + 1
  let K : ℝ := 2 * (2 * (1 + L) + (q * R) ^ 2) * (4 * L)
  refine ⟨1 + |K|, by positivity, ?_⟩
  intro P hP h B hh _hhB hB i
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
  have hq : 0 ≤ q := by positivity
  let f := winsorizedScoreFunction P p h B R i
  have hfmeas : Measurable f := winsorizedScoreFunction_measurable P p h B R i
  have hfint : Integrable (fun w => (f w) ^ 2) P.law := by
    apply Integrable.of_bound (hfmeas.pow_const 2).aestronglyMeasurable
      ((B + q * R) ^ 2)
    filter_upwards with w
    have hf := winsorizedScore_abs_le_envelope P p h B R hB0 hR.le i w
    have henv : B + (p + 1 : ℝ) * R = B + q * R := by simp [q]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (add_nonneg hB0 (mul_nonneg hq hR.le))).2
        (by simpa only [henv] using hf)
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have hsmeas : MeasurableSet P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.isClosed_support.measurableSet
  have hsuppMap : ∀ᵐ z ∂Measure.map causalScore P.law, z ∈ P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  have hsupp : ∀ᵐ w ∂P.law, causalScore w ∈ P.support :=
    (ae_map_iff hscore.aemeasurable hsmeas).mp hsuppMap
  let g0 : CausalObservation → ENNReal := fun w =>
    (Metric.closedBall i.2.1 h).indicator
      (fun _ => ENNReal.ofReal ((armCoord false w) ^ 2)) (causalScore w)
  let g1 : CausalObservation → ENNReal := fun w =>
    (Metric.closedBall i.2.1 h).indicator
      (fun _ => ENNReal.ofReal ((armCoord true w) ^ 2)) (causalScore w)
  let gc : CausalObservation → ENNReal := fun w =>
    (Metric.closedBall i.2.1 h).indicator
      (fun _ => ENNReal.ofReal ((q * R) ^ 2)) (causalScore w)
  have hg0 : Measurable g0 := by
    apply Measurable.indicator
    · have harm : Measurable (armCoord false) := by
        unfold armCoord
        simp only [Bool.false_eq_true, if_false]
        fun_prop
      exact (harm.pow_const 2).ennreal_ofReal
    · exact Metric.isClosed_closedBall.measurableSet.preimage hscore
  have hg1 : Measurable g1 := by
    apply Measurable.indicator
    · have harm : Measurable (armCoord true) := by
        unfold armCoord
        simp only [if_true]
        fun_prop
      exact (harm.pow_const 2).ennreal_ofReal
    · exact Metric.isClosed_closedBall.measurableSet.preimage hscore
  have hgc : Measurable gc := by
    apply Measurable.indicator measurable_const
    exact Metric.isClosed_closedBall.measurableSet.preimage hscore
  have hlin : (∫⁻ w, ENNReal.ofReal ((f w) ^ 2) ∂P.law) ≤
      ENNReal.ofReal (K * h ^ 2) := by
    calc
      (∫⁻ w, ENNReal.ofReal ((f w) ^ 2) ∂P.law) ≤
          ∫⁻ w, 2 * (g0 w + g1 w + gc w) ∂P.law := by
        apply lintegral_mono_ae
        filter_upwards [hsupp] with w hw
        have hp := winsorizedScore_sq_pointwise_le P p h B R hh hB0 hR.le i w hw
        apply ENNReal.ofReal_le_ofReal at hp
        by_cases hball : causalScore w ∈ Metric.closedBall i.2.1 h
        · simpa [f, g0, g1, gc, q, indicator_of_mem hball,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_add (sq_nonneg (armCoord false w))
              (sq_nonneg (armCoord true w)),
            ENNReal.ofReal_add
              (add_nonneg (sq_nonneg (armCoord false w)) (sq_nonneg (armCoord true w)))
              (by positivity : 0 ≤ ((p + 1 : ℝ) * R) ^ 2)] using hp
        · simpa [f, g0, g1, gc, q, indicator_of_notMem hball] using hp
      _ = 2 * ((∫⁻ w, g0 w ∂P.law) + (∫⁻ w, g1 w ∂P.law) +
          (∫⁻ w, gc w ∂P.law)) := by
        rw [lintegral_const_mul 2 ((hg0.fun_add hg1).fun_add hgc),
          lintegral_add_left (hg0.fun_add hg1),
          lintegral_add_left hg0]
      _ ≤ 2 * (ENNReal.ofReal ((1 + L) * (4 * L * h ^ 2)) +
          ENNReal.ofReal ((1 + L) * (4 * L * h ^ 2)) +
          ENNReal.ofReal ((q * R) ^ 2 * (4 * L * h ^ 2))) := by
        gcongr
        · exact localized_arm_sq_lintegral_le p ν L P hP false i.2.1 h hh
        · exact localized_arm_sq_lintegral_le p ν L P hP true i.2.1 h hh
        · exact localized_const_sq_lintegral_le p ν L P hP i.2.1 h (q * R) hh
      _ = ENNReal.ofReal (K * h ^ 2) := by
        have hA : 0 ≤ (1 + L) * (4 * L * h ^ 2) := by positivity
        have hD : 0 ≤ (q * R) ^ 2 * (4 * L * h ^ 2) := by positivity
        have htwo : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
        rw [htwo, ← ENNReal.ofReal_add hA hA,
          ← ENNReal.ofReal_add (add_nonneg hA hA) hD,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        dsimp [K]
        ring
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hint : ∫ w, (f w) ^ 2 ∂P.law ≤ K * h ^ 2 := by
    rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (sq_nonneg h))]
    rw [ofReal_integral_eq_lintegral_ofReal hfint
      (ae_of_all _ fun w => sq_nonneg (f w))]
    exact hlin
  unfold measureL2Dist
  simp only [sub_zero]
  have hsqrt : Real.sqrt (∫ w, (f w) ^ 2 ∂P.law) ≤ Real.sqrt K * h := by
    have hsqrtMono := Real.sqrt_le_sqrt hint
    rw [Real.sqrt_mul hK (h ^ 2), Real.sqrt_sq_eq_abs,
      abs_of_pos hh] at hsqrtMono
    exact hsqrtMono
  have hsqrtK : Real.sqrt K ≤ 1 + K := by
    nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K, sq_nonneg (Real.sqrt K - 1)]
  have hKabs : |K| = K := abs_of_nonneg hK
  simpa only [f, q, K, hKabs] using
    hsqrt.trans (mul_le_mul_of_nonneg_right hsqrtK hh.le)

/-- For every fixed polynomial degree and law-class envelope there are a
positive coefficient clipping radius and a positive constant such that every
admissible winsorized score has population `L²` norm at most `C h`, uniformly
over centers, arms, coordinates, and all winsorization levels `B > h` with
`B ≥ 1`. -/
lemma winsorizedScore_hasUniformL2Radius
    (p : ℕ) (ν L : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
      ∀ i : WinsorizedScoreIndex p,
        measureL2Dist P.law (winsorizedScoreFunction P p h B R i)
          (fun _ => 0) ≤ C * h := by
  obtain ⟨C, hC, hbound⟩ :=
    winsorizedScore_hasUniformL2Radius_at p ν L 1 (by norm_num)
  exact ⟨1, C, by norm_num, hC, hbound⟩

end CausalSmith.Stat.BddUniformLogPenalty
