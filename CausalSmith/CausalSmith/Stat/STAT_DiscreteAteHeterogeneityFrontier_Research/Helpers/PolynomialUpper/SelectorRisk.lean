/- Clipped finite-selector risk transport for the polynomial estimator. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.SelectorBridge
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Pilot
import Causalean.Stat.SampleSplit.FiniteSelector

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

/-- If [the target lies in the clipping interval](hyp:ht), [the squared clipped normalized error
  is at most four](goal). -/
lemma clippedNormalizedError_sq_le_four (x t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    (clip (-1) 1 x - t) ^ 2 ≤ 4 := by
  have hc : clip (-1) 1 x ∈ Icc (-1 : ℝ) 1 := by
    unfold clip
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hprod : 0 ≤
      (clip (-1) 1 x - t + 2) * (2 - (clip (-1) 1 x - t)) := by
    exact mul_nonneg (by linarith [hc.1, ht.2]) (by linarith [hc.2, ht.1])
  nlinarith

/-- [the clipped normalized error for a selected polynomial branch is measurable](goal). -/
lemma polynomialClippedBranchError_measurable {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (M : ℝ) (H : Finset (Fin d)) (t : ℝ) :
    Measurable (fun x : (polynomialBalancedSplit P).foldB n → Obs d =>
      clip (-1) 1 (t + polynomialFixedTotalError P base M H x) - t) := by
  have hraw : Measurable (fun x : (polynomialBalancedSplit P).foldB n → Obs d =>
      t + polynomialFixedTotalError P base M H x) :=
    measurable_const.add
      (polynomialFixedTotalError_measurable (n := n) P base M H)
  exact (measurable_const.max (measurable_const.min hraw)).sub measurable_const

/-- If [the bad-event contribution is bounded as stated](hyp:hbad), [the probability that a pilot
  fold is bad satisfies the stated exponential bound](goal). -/
lemma polynomialPilotFoldGood_compl_probability_le {n d : ℕ}
    (P : RealLaw d) (base : Obs d) (lowerBand upperBand delta : ℝ)
    (hbad : (Measure.infinitePi fun _ : ℕ => P.observedLaw).real
      (polynomialPilotGood (n := n) P lowerBand upperBand)ᶜ ≤ delta) :
    (Measure.infinitePi fun _ : ℕ => P.observedLaw).real
      ((fun omega : ℕ → Obs d =>
        fun i : (polynomialBalancedSplit P).foldA n => omega i) ⁻¹'
          (polynomialPilotFoldGood P base lowerBand upperBand)ᶜ) ≤ delta := by
  apply (measureReal_mono (μ := Measure.infinitePi fun _ : ℕ => P.observedLaw)
    (s₂ := (polynomialPilotGood (n := n) P lowerBand upperBand)ᶜ) ?_).trans hbad
  intro omega homega hgood
  exact homega (polynomialPilotGood_implies_foldGood P base lowerBand upperBand
    omega hgood)

-- @node: polynomial_clipped_finiteSelector_risk
/-- If [the stated lower bound holds](hyp:hlower) and [the branchwise risk is bounded as
  stated](hyp:hR) and [the bad-event probability is bounded as stated](hyp:hdelta) and [each fixed
  branch has the stated risk bound](hyp:hfixed) and [the bad-event contribution is bounded as
  stated](hyp:hbad), [a uniform deterministic fixed-branch bound transfers through the measurable
  pilot selector. Clipping supplies the global envelope on the bad pilot event](goal). -/
lemma polynomial_clipped_finiteSelector_risk {n d : ℕ}
    {epsilon M sigma lowerBand upperBand R delta : ℝ}
    (P : ModelClass d epsilon M sigma) (base : Obs d)
    (hlower : 0 < lowerBand) (hR : 0 ≤ R) (hdelta : 0 ≤ delta)
    (hfixed : ∀ H : Finset (Fin d),
      polynomialSelectorEligible P.law lowerBand upperBand H →
      ∫ z : Fin (n - n / 2) → Obs d,
          (polynomialFixedBranchNormalizedError (K := polynomialDegree n)
            P.law M (4096 * logEN n / (n - n / 2 : ℕ)) H z) ^ 2
          ∂(productLaw (n - n / 2) P.law) ≤ R)
    (hbad : (Measure.infinitePi fun _ : ℕ => P.law.observedLaw).real
      (polynomialPilotGood (n := n) P.law lowerBand upperBand)ᶜ ≤ delta) :
    ∫ omega : ℕ → Obs d,
        (clip (-1) 1 (polynomialNormalizedSum M
            (fun i : Fin n => omega i)) - rawAteFormula P.law / M) ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => P.law.observedLaw) ≤ R + 4 * delta := by
  let mu := Measure.infinitePi fun _ : ℕ => P.law.observedLaw
  let pilot : (ℕ → Obs d) →
      ((polynomialBalancedSplit P.law).foldA n → Obs d) :=
    fun omega i => omega i
  let tail : (ℕ → Obs d) →
      ((polynomialBalancedSplit P.law).foldB n → Obs d) :=
    fun omega i => omega i
  let select := polynomialPilotHeavySet (n := n) P.law base
  let t := rawAteFormula P.law / M
  let err : Finset (Fin d) →
      ((polynomialBalancedSplit P.law).foldB n → Obs d) → ℝ :=
    fun H x => clip (-1) 1 (t + polynomialFixedTotalError P.law base M H x) - t
  have ht : t ∈ Icc (-1 : ℝ) 1 := modelClass_normalized_ate_mem_Icc P
  have hpilot : Measurable pilot := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (i : ℕ)
  have htail : Measurable tail := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (i : ℕ)
  have herr : ∀ H, Measurable (err H) := fun H =>
    polynomialClippedBranchError_measurable P.law base M H t
  have hbranchInt : ∀ H, polynomialSelectorEligible P.law lowerBand upperBand H →
      Integrable (fun x => (err H x) ^ 2) (mu.map tail) := by
    intro H _
    apply Integrable.of_bound (C := 4)
    · exact ((herr H).pow_const 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact clippedNormalizedError_sq_le_four _ _ ht
  have hbranch : ∀ H, polynomialSelectorEligible P.law lowerBand upperBand H →
      ∫ x, (err H x) ^ 2 ∂(mu.map tail) ≤ R := by
    intro H hH
    have hpos : ∀ k ∈ H, 0 < P.law.cellMass k := fun k hk =>
      hlower.trans_le (hH.1 k hk)
    have hrawInt := polynomialFixedBranchNormalizedError_sq_integrable
      (m := n - n / 2) (K := polynomialDegree n)
      (B := 4096 * logEN n / (n - n / 2 : ℕ)) P H
    let reindex := polynomialFoldBReindex (n := n) P.law
    have hreindex : Measurable reindex := by
      apply measurable_pi_lambda
      intro j
      exact measurable_pi_apply (polynomialFoldBEquiv P.law j)
    have hmap : (mu.map tail).map reindex =
        productLaw (n - n / 2) P.law := by
      rw [Measure.map_map hreindex htail]
      exact map_polynomialFoldBReindex_iid_eq_productLaw P.law
    have hrawFold : Integrable (fun x =>
        (polynomialFixedBranchNormalizedError (K := polynomialDegree n)
          P.law M (4096 * logEN n / (n - n / 2 : ℕ)) H
          (reindex x)) ^ 2) (mu.map tail) := by
      have hi : Integrable (fun z =>
          (polynomialFixedBranchNormalizedError (K := polynomialDegree n)
            P.law M (4096 * logEN n / (n - n / 2 : ℕ)) H z) ^ 2)
          ((mu.map tail).map reindex) := by
        rw [hmap]
        exact hrawInt
      simpa [Function.comp_def] using hi.comp_measurable hreindex
    apply (integral_mono (hbranchInt H hH) hrawFold ?_).trans ?_
    intro x
    dsimp [err]
    rw [polynomialFixedTotalError_eq_fixedBranch P base H x hpos]
    have hc := clip_normalized_sq_error_le
      (t + polynomialFixedBranchNormalizedError (K := polynomialDegree n)
        P.law M (4096 * logEN n / (n - n / 2 : ℕ)) H
        (polynomialFoldBReindex P.law x)) t ht
    simpa [reindex] using hc
    let f : (Fin (n - n / 2) → Obs d) → ℝ := fun z =>
      (polynomialFixedBranchNormalizedError (K := polynomialDegree n)
        P.law M (4096 * logEN n / (n - n / 2 : ℕ)) H z) ^ 2
    have hfsm : AEStronglyMeasurable f ((mu.map tail).map reindex) := by
      rw [hmap]
      exact hrawInt.aestronglyMeasurable
    calc
      (∫ x, f (reindex x) ∂(mu.map tail)) =
          ∫ z, f z ∂((mu.map tail).map reindex) :=
        (integral_map hreindex.aemeasurable hfsm).symm
      _ = ∫ z, f z ∂productLaw (n - n / 2) P.law := by rw [hmap]
      _ ≤ R := hfixed H hH
  have hsel := IndepFun.integral_finiteSelector_sq_le_add_bad
    ((polynomialBalancedSplit P.law).folds_indep n)
    hpilot htail (polynomialPilotHeavySet_measurable P.law base) herr
    (polynomialPilotFoldGood_measurable P.law base lowerBand upperBand)
    hR (by norm_num : (0 : ℝ) ≤ 4)
    (fun a ha => ha) hbranchInt hbranch
    (fun omega => clippedNormalizedError_sq_le_four _ _ ht)
    (polynomialPilotFoldGood_compl_probability_le P.law base lowerBand upperBand
      delta hbad)
  calc
    (∫ omega : ℕ → Obs d,
        (clip (-1) 1 (polynomialNormalizedSum M
            (fun i : Fin n => omega i)) - rawAteFormula P.law / M) ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => P.law.observedLaw)) =
      ∫ omega : ℕ → Obs d,
        (err (select (pilot omega)) (tail omega)) ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards with omega
      dsimp [err, select, pilot, tail, t]
      rw [polynomialFixedTotalError_iidPrefix]
      congr 2
      ring
    _ ≤ R + 4 * delta := by
      simpa [mu, pilot, tail, Causalean.Stat.iidSample_infinitePi] using hsel

/-- If [the indicated calibration branch applies](hyp:hbranch) and [the stated stream condition
  holds](hyp:hstream), [the polynomial estimator's mean squared error is bounded by the
  corresponding clipped-stream normalized risk after rescaling](goal). -/
lemma mse_polyEstimator_le_of_clipped_stream {n d N : ℕ}
    {epsilon M sigma rho R : ℝ} (P : ModelClass d epsilon M sigma)
    (hbranch : N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n)
    (hstream : ∫ omega : ℕ → Obs d,
        (clip (-1) 1 (polynomialNormalizedSum M
            (fun i : Fin n => omega i)) - rawAteFormula P.law / M) ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => P.law.observedLaw) ≤ R) :
    mse P.law (rawPolyEstimator (n := n) (d := d) N rho M) ≤ M ^ 2 * R := by
  let S := Causalean.Stat.iidSample_infinitePi P.law.observedLaw
  let pref : (ℕ → Obs d) → (Fin n → Obs d) := fun omega i => omega i
  let f : (Fin n → Obs d) → ℝ := fun sample =>
    (clip (-1) 1 (polynomialNormalizedSum M sample) -
      rawAteFormula P.law / M) ^ 2
  have hM : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one P.M_ge_one)
  have hpoly : Measurable (rawPolyEstimator (n := n) (d := d) N rho M) :=
    (polyEstimator_admissible (n := n) (d := d) (N := N) (rho := rho)
      (le_trans zero_le_one P.M_ge_one)).1
  have hclip : Measurable (fun sample : Fin n → Obs d =>
      clip (-1) 1 (polynomialNormalizedSum M sample)) := by
    have heq : (fun sample : Fin n → Obs d =>
        clip (-1) 1 (polynomialNormalizedSum M sample)) =
        fun sample => (rawPolyEstimator N rho M sample) / M := by
      funext sample
      rw [polyEstimator_eq_scaled_clip_of_calibrated hbranch]
      field_simp [hM]
    rw [heq]
    exact hpoly.div measurable_const
  have hf : Measurable f := ((hclip.sub measurable_const).pow_const 2)
  have hpref : Measurable pref :=
    Causalean.Stat.iidSample_finN_measurable S n
  have hmap : (Measure.infinitePi fun _ : ℕ => P.law.observedLaw).map pref =
      productLaw n P.law := by
    unfold productLaw
    exact Causalean.Stat.iidSample_finN_pushforward S n
  have hprod : ∫ sample, f sample ∂productLaw n P.law ≤ R := by
    rw [← hmap, integral_map hpref.aemeasurable hf.aestronglyMeasurable]
    exact hstream
  have hid (sample : Fin n → Obs d) :
      (rawPolyEstimator N rho M sample - rawAteFormula P.law) ^ 2 =
        M ^ 2 * f sample := by
    rw [polyEstimator_eq_scaled_clip_of_calibrated hbranch]
    dsimp [f]
    field_simp [hM]
  unfold mse
  simp_rw [hid]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hprod (sq_nonneg M)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
