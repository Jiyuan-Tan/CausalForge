import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.ScoreL2
import Mathlib.Analysis.Matrix.PosDef

/-!
# Uniform population-coefficient radius

This module bounds the original population score and then uses the class's
quadratic-form Gram floor to put every population coefficient in one fixed
ball.  This is the adapter needed to embed the actual score process into the
bounded-coefficient entropy class.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

-- @node: populationScore_apply_uniform_bound
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma populationScore_apply_uniform_bound (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (t : Bool) (x : Score) (hx : x ∈ P.boundary)
    (h : ℝ) (hh : 0 < h) (hhL : h ≤ L⁻¹) (j : Fin (p + 1)) :
    |populationScore P p t x h j| ≤ 16 * L * (2 + L) := by
  classical
  let d : CausalObservation → ℝ := fun w =>
    signedDistance (knownGeometry P) x (causalScore w)
  let g : CausalObservation → ℝ := fun w =>
    (if signedArm t (d w) then 1 else 0) * uniformKernel (d w / h) *
      polyBasis p (d w / h) j * observedOutcome P w
  let F : CausalObservation → ℝ := fun w => h⁻¹ ^ 2 * g w
  have hpoint (w : CausalObservation) (hw : causalScore w ∈ P.support) :
      ‖F w‖ₑ ≤ ENNReal.ofReal (h⁻¹ ^ 2) *
        (Metric.closedBall x h).indicator (fun _ =>
          1 + 2 * ENNReal.ofReal ((armCoord false w) ^ 2) +
            2 * ENNReal.ofReal ((armCoord true w) ^ 2)) (causalScore w) := by
    let i : WinsorizedScoreIndex p := (t, x, (0, j))
    have hsquare := winsorizedScore_sq_pointwise_le P p h
      |observedOutcome P w| 0 hh (abs_nonneg _) (le_refl 0) i w hw
    have hwinsor : winsorize |observedOutcome P w| (observedOutcome P w) =
        observedOutcome P w := by
      unfold winsorize
      by_cases hy : observedOutcome P w < 0
      · simp [hy, abs_of_neg hy]
      · by_cases hy0 : observedOutcome P w = 0
        · simp [hy0]
        · have hypos : 0 < observedOutcome P w := lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm hy0)
          simp [hy, hy0, abs_of_pos hypos]
    have heq : winsorizedScoreFunction P p h |observedOutcome P w| 0 i w = g w := by
      simp [i, g, winsorizedScoreFunction, d, clip, hwinsor]
    rw [heq] at hsquare
    have habs : |g w| ≤ (Metric.closedBall x h).indicator (fun _ =>
        1 + 2 * (armCoord false w) ^ 2 + 2 * (armCoord true w) ^ 2)
        (causalScore w) := by
      by_cases hb : causalScore w ∈ Metric.closedBall x h
      · simp only [indicator_of_mem hb]
        simp only [i, indicator_of_mem hb, Nat.cast_add, Nat.cast_one, mul_zero,
          zero_pow, Fin.isValue, add_zero] at hsquare
        nlinarith [sq_abs (g w), sq_nonneg (|g w| - 1),
          sq_nonneg (armCoord false w), sq_nonneg (armCoord true w)]
      · simp only [indicator_of_notMem hb]
        simp only [i, indicator_of_notMem hb, mul_zero] at hsquare
        have : g w = 0 := by nlinarith [sq_nonneg (g w)]
        simp [this]
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    change ENNReal.ofReal |h⁻¹ ^ 2 * g w| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h⁻¹ ^ 2)]
    by_cases hb : causalScore w ∈ Metric.closedBall x h
    · simp only [indicator_of_mem hb] at habs ⊢
      have hnonneg : 0 ≤ 1 + 2 * (armCoord false w) ^ 2 +
          2 * (armCoord true w) ^ 2 := by positivity
      calc
        ENNReal.ofReal (h⁻¹ ^ 2 * |g w|) ≤
            ENNReal.ofReal (h⁻¹ ^ 2 * (1 + 2 * (armCoord false w) ^ 2 +
              2 * (armCoord true w) ^ 2)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left habs (by positivity))
        _ = ENNReal.ofReal (h⁻¹ ^ 2) *
            (1 + 2 * ENNReal.ofReal ((armCoord false w) ^ 2) +
              2 * ENNReal.ofReal ((armCoord true w) ^ 2)) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_ofNat,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ h⁻¹ ^ 2)]
    · simp only [indicator_of_notMem hb]
      rw [indicator_of_notMem hb] at habs
      have hg0 : |g w| = 0 := le_antisymm habs (abs_nonneg _)
      simp [hg0]
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  let S : Set CausalObservation := causalScore ⁻¹' Metric.closedBall x h
  let Gc : CausalObservation → ℝ≥0∞ := S.indicator (fun _ => 1)
  let G0 : CausalObservation → ℝ≥0∞ := S.indicator
    (fun w => ENNReal.ofReal ((armCoord false w) ^ 2))
  let G1 : CausalObservation → ℝ≥0∞ := S.indicator
    (fun w => ENNReal.ofReal ((armCoord true w) ^ 2))
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet.preimage hscore
  have harm (t : Bool) : Measurable (armCoord t) := by
    cases t <;> unfold armCoord <;> simp only [Bool.false_eq_true, if_false,
      if_true] <;> fun_prop
  have hGc : Measurable Gc := Measurable.indicator measurable_const hS
  have hG0 : Measurable G0 := Measurable.indicator ((harm false).pow_const 2).ennreal_ofReal hS
  have hG1 : Measurable G1 := Measurable.indicator ((harm true).pow_const 2).ennreal_ofReal hS
  have htotalMeas : Measurable (fun w =>
      (Metric.closedBall x h).indicator (fun _ =>
        1 + 2 * ENNReal.ofReal ((armCoord false w) ^ 2) +
          2 * ENNReal.ofReal ((armCoord true w) ^ 2)) (causalScore w)) := by
    rw [show (fun w => (Metric.closedBall x h).indicator (fun _ =>
        1 + 2 * ENNReal.ofReal ((armCoord false w) ^ 2) +
          2 * ENNReal.ofReal ((armCoord true w) ^ 2)) (causalScore w)) =
        fun w => Gc w + (2 : ENNReal) * G0 w + (2 : ENNReal) * G1 w by
      funext w
      by_cases hw : causalScore w ∈ Metric.closedBall x h <;>
        simp [S, Gc, G0, G1, hw]]
    exact (hGc.add (measurable_const.mul hG0)).add (measurable_const.mul hG1)
  have hsplit : (∫⁻ w, (Metric.closedBall x h).indicator (fun _ =>
      1 + 2 * ENNReal.ofReal ((armCoord false w) ^ 2) +
        2 * ENNReal.ofReal ((armCoord true w) ^ 2)) (causalScore w) ∂P.law) =
      (Measure.map causalScore P.law) (Metric.closedBall x h) +
        2 * (∫⁻ w, G0 w ∂P.law) + 2 * (∫⁻ w, G1 w ∂P.law) := by
    have hfun : (fun w => (Metric.closedBall x h).indicator (fun _ =>
        1 + 2 * ENNReal.ofReal ((armCoord false w) ^ 2) +
          2 * ENNReal.ofReal ((armCoord true w) ^ 2)) (causalScore w)) =
        fun w => Gc w + 2 * G0 w + 2 * G1 w := by
      funext w
      by_cases hw : causalScore w ∈ Metric.closedBall x h <;>
        simp [S, Gc, G0, G1, hw]
    rw [hfun, lintegral_add_left (hGc.fun_add (measurable_const.fun_mul hG0)),
      lintegral_add_left hGc, lintegral_const_mul 2 hG0,
      lintegral_const_mul 2 hG1]
    have hGcInt : (∫⁻ w, Gc w ∂P.law) =
        (Measure.map causalScore P.law) (Metric.closedBall x h) := by
      rw [show Gc = S.indicator (fun _ => 1) by rfl,
        lintegral_indicator hS, setLIntegral_one]
      exact (Measure.map_apply_of_aemeasurable hscore.aemeasurable
        Metric.isClosed_closedBall.measurableSet).symm
    rw [hGcInt]
  have hsuppMap : ∀ᵐ z ∂Measure.map causalScore P.law, z ∈ P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  have hsupp : ∀ᵐ w ∂P.law, causalScore w ∈ P.support :=
    MeasureTheory.ae_of_ae_map hscore.aemeasurable hsuppMap
  have hlin : (∫⁻ w, ‖F w‖ₑ ∂P.law) ≤
      ENNReal.ofReal (16 * L * (2 + L)) := by
    calc
      _ ≤ ENNReal.ofReal (h⁻¹ ^ 2) *
          (∫⁻ w, (Metric.closedBall x h).indicator (fun _ =>
            1 + 2 * ENNReal.ofReal ((armCoord false w) ^ 2) +
              2 * ENNReal.ofReal ((armCoord true w) ^ 2))
                (causalScore w) ∂P.law) := by
        rw [← lintegral_const_mul _ htotalMeas]
        exact lintegral_mono_ae (hsupp.mono fun w hw => hpoint w hw)
      _ = ENNReal.ofReal (h⁻¹ ^ 2) *
          ((Measure.map causalScore P.law) (Metric.closedBall x h) +
            2 * (∫⁻ w, G0 w ∂P.law) + 2 * (∫⁻ w, G1 w ∂P.law)) := by rw [hsplit]
      _ ≤ ENNReal.ofReal (h⁻¹ ^ 2) *
          (ENNReal.ofReal (4 * L * h ^ 2) +
            2 * ENNReal.ofReal ((1 + L) * (4 * L * h ^ 2)) +
            2 * ENNReal.ofReal ((1 + L) * (4 * L * h ^ 2))) := by
        gcongr
        · exact marginal_closedBall_le p ν L P hP x h hh
        · exact localized_arm_sq_lintegral_le p ν L P hP false x h hh
        · exact localized_arm_sq_lintegral_le p ν L P hP true x h hh
      _ ≤ ENNReal.ofReal (16 * L * (2 + L)) := by
        have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
        have hcancel : h⁻¹ ^ 2 * h ^ 2 = 1 := by field_simp
        rw [show (2 : ENNReal) * ENNReal.ofReal ((1 + L) * (4 * L * h ^ 2)) =
            ENNReal.ofReal (2 * ((1 + L) * (4 * L * h ^ 2))) by
              rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
                ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)],
          ← ENNReal.ofReal_add (by positivity : 0 ≤ 4 * L * h ^ 2) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ h⁻¹ ^ 2)]
        apply ENNReal.ofReal_le_ofReal
        calc
          h⁻¹ ^ 2 * (4 * L * h ^ 2 + 2 * ((1 + L) * (4 * L * h ^ 2)) +
              2 * ((1 + L) * (4 * L * h ^ 2))) =
              (h⁻¹ ^ 2 * h ^ 2) *
                (4 * L + 2 * ((1 + L) * (4 * L)) + 2 * ((1 + L) * (4 * L))) := by ring
          _ ≤ 16 * L * (2 + L) := by rw [hcancel]; nlinarith
  have hi := MeasureTheory.enorm_integral_le_lintegral_enorm F (μ := P.law)
  have hE : ENNReal.ofReal |∫ w, F w ∂P.law| ≤
      ENNReal.ofReal (16 * L * (2 + L)) := by
    simpa [← ofReal_norm_eq_enorm, Real.norm_eq_abs] using hi.trans hlin
  have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (by norm_num) hL) (by linarith))).mp hE
  have heqint : populationScore P p t x h j = ∫ w, F w ∂P.law := by
    simp only [populationScore, F, g, d]
    congr 1
    funext w
    ring
  rw [heqint]
  exact hreal

-- @node: populationGram_posDef
/-- The stated bandwidth is strictly positive at every sample size. -/
lemma populationGram_posDef (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (t : Bool) (x : Score) (hx : x ∈ P.boundary)
    (h : ℝ) (hh : 0 < h) (hhL : h ≤ L⁻¹) :
    (populationGram P p t x h).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · unfold Matrix.IsHermitian
    ext j k
    simp only [Matrix.conjTranspose_apply, starRingEnd_apply, star_trivial]
    unfold populationGram
    apply integral_congr_ae
    filter_upwards with w
    ring
  · intro v hv
    have hfloor := hP.2.2.2.2.2.2.2.2.2.2.2.2.1 t x h hx hh hhL v
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hv (funext hn)
    have hsum : 0 < ∑ i, (v i) ^ 2 := Finset.sum_pos'
      (fun i _ => sq_nonneg (v i)) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have hL : 0 < L := lt_of_lt_of_le (by norm_num) hP.2.1
    rw [show matrixQuadratic (populationGram P p t x h) v =
      dotProduct v (Matrix.mulVec (populationGram P p t x h) v) by
        simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]; ring] at hfloor
    exact lt_of_lt_of_le (mul_pos (inv_pos.mpr hL) hsum) hfloor

-- @node: populationGram_mulVec_populationCoefficient
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma populationGram_mulVec_populationCoefficient (p : ℕ) (ν L : ℝ)
    (P : A1A2Law) (hP : A1A2Class p ν L P) (t : Bool) (x : Score)
    (hx : x ∈ P.boundary) (h : ℝ) (hh : 0 < h) (hhL : h ≤ L⁻¹) :
    Matrix.mulVec (populationGram P p t x h)
      (populationCoefficient P p t x h) = populationScore P p t x h := by
  have hp := populationGram_posDef p ν L P hP t x hx h hh hhL
  rw [populationCoefficient, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]
  simp

-- @node: populationCoefficient_uniform_bound_explicit
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma populationCoefficient_uniform_bound_explicit (p : ℕ) (ν L : ℝ) :
    ∀ P : A1A2Law, A1A2Class p ν L P →
    ∀ t x h, x ∈ P.boundary → 0 < h → h ≤ L⁻¹ →
      ∀ j, |populationCoefficient P p t x h j| ≤
        1 + |L * (p + 1 : ℝ) * (16 * L * (2 + L))| := by
  let K : ℝ := 16 * L * (2 + L)
  let R : ℝ := 1 + |L * (p + 1 : ℝ) * K|
  intro P hP t x h hx hh hhL j
  · let A := populationGram P p t x h
    let s := populationScore P p t x h
    let beta := populationCoefficient P p t x h
    obtain ⟨j0, _hj0, hj0max⟩ := Finset.exists_max_image Finset.univ
      (fun k : Fin (p + 1) => |beta k|) Finset.univ_nonempty
    have hnorm : ‖beta‖ = |beta j0| := by
      apply le_antisymm
      · rw [pi_norm_le_iff_of_nonneg (abs_nonneg (beta j0))]
        intro k
        simpa [Real.norm_eq_abs] using hj0max k (Finset.mem_univ k)
      · simpa [Real.norm_eq_abs] using norm_le_pi_norm beta j0
    have hfloor := hP.2.2.2.2.2.2.2.2.2.2.2.2.1 t x h hx hh hhL beta
    have hmul := populationGram_mulVec_populationCoefficient p ν L P hP t x hx h hh hhL
    have hquad : matrixQuadratic A beta = dotProduct beta s := by
      rw [show matrixQuadratic A beta = dotProduct beta (Matrix.mulVec A beta) by
        simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]; ring]
      simpa [A, s, beta] using congrArg (dotProduct beta) hmul
    have hs (k : Fin (p + 1)) : |s k| ≤ K := by
      simpa [s, K] using populationScore_apply_uniform_bound p ν L P hP t x hx h hh hhL k
    have hdot : dotProduct beta s ≤ (p + 1 : ℝ) * ‖beta‖ * K := by
      calc
        dotProduct beta s ≤ |dotProduct beta s| := le_abs_self _
        _ ≤ ∑ k, |beta k * s k| := by
          unfold dotProduct
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (p + 1), ‖beta‖ * K := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm beta k)
            (hs k) (abs_nonneg _) (norm_nonneg _)
        _ = (p + 1 : ℝ) * ‖beta‖ * K := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring
    have hsum : ‖beta‖ ^ 2 ≤ ∑ k, (beta k) ^ 2 := by
      rw [hnorm, sq_abs]
      exact Finset.single_le_sum (fun k _ => sq_nonneg (beta k)) (Finset.mem_univ j0)
    have hL : 0 < L := lt_of_lt_of_le (by norm_num) hP.2.1
    have hmain : L⁻¹ * ‖beta‖ ^ 2 ≤ (p + 1 : ℝ) * ‖beta‖ * K := by
      calc
        _ ≤ L⁻¹ * ∑ k, (beta k) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hL.le)
        _ ≤ matrixQuadratic A beta := by simpa [A, beta] using hfloor
        _ = dotProduct beta s := hquad
        _ ≤ _ := hdot
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hbeta : ‖beta‖ ≤ L * (p + 1 : ℝ) * K := by
      by_cases hb0 : ‖beta‖ = 0
      · rw [hb0]
        positivity
      · have hb : 0 < ‖beta‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
        have hLi : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
        nlinarith
    calc
      |populationCoefficient P p t x h j| ≤ ‖beta‖ := by
        simpa [beta, Real.norm_eq_abs] using norm_le_pi_norm beta j
      _ ≤ L * (p + 1 : ℝ) * K := hbeta
      _ ≤ R := by
        dsimp [R, K]
        exact (le_abs_self _).trans (by linarith)

/-- The explicit population-coefficient radius in existential form. -/
-- @node: populationCoefficient_uniform_bound
lemma populationCoefficient_uniform_bound (p : ℕ) (ν L : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ t x h, x ∈ P.boundary → 0 < h → h ≤ L⁻¹ →
        ∀ j, |populationCoefficient P p t x h j| ≤ R := by
  refine ⟨1 + |L * (p + 1 : ℝ) * (16 * L * (2 + L))|, by positivity, ?_⟩
  exact populationCoefficient_uniform_bound_explicit p ν L

end CausalSmith.Stat.BddUniformLogPenalty
