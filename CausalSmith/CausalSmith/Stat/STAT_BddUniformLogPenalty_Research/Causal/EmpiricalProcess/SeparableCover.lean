import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.RadialCover

/-!
# Polynomial covering for the one-sided bandwidth enlargement

This file inserts the independently parameterized closed-ball support into the
fixed-normalization radial-polynomial cover.  The diagonal pullback then ties
the ball center to the polynomial center.  The degree-zero term off the known
assignment support is kept separate because signed distance is identically
zero there.
-/

open Causalean.Stat.Concentration
open Causalean.Stat.Concentration.EuclideanRadialPolynomial
open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The separable score class, whose kernel bandwidth ranges over `[h,2h)`,
has polynomial covering witnesses uniform in the law, bandwidth, and
winsorization level. -/
-- @node: separableWinsorizedScore_hasUniformPolynomialL2Cover
lemma separableWinsorizedScore_hasUniformPolynomialL2Cover
    (p : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ A v : ℝ, Real.exp 1 ≤ A ∧ 1 ≤ v ∧
      ∀ (P : A1A2Law), P.boundary.Nonempty → ∀ {h B : ℝ}, 0 < h → 0 < B →
        HasPolynomialL2Cover
            (separableWinsorizedScoreFunction P p h B R)
            ((2 * ((2 : ℝ) ^ p) ^ 2 + 2) *
              (B + ((p + 1 : ℕ) : ℝ) * R)) ∧
          HasPolynomialEmpiricalL2Cover
            (separableWinsorizedScoreFunction P p h B R)
            ((2 * ((2 : ℝ) ^ p) ^ 2 + 2) *
              (B + ((p + 1 : ℕ) : ℝ) * R)) A v := by
  classical
  let Arm := Bool × Fin (p + 1)
  obtain ⟨C, n, hradial⟩ :=
    radialResidualScore_hasUniformPolynomialL2CoverWith
      (Ω := CausalObservation) (A := Arm) 2 p
  let Cball : ℝ := 16
  let nball : ℕ := 8 * ((2 + 2) + 1)
  let Cmul := 8 * C * Cball
  let nmul := n + nball + 2
  let C₁ := 2 * Cmul
  let C₂ := 8 * C₁ * C₁
  let n₂ := nmul + nmul + 2
  let C₃ := 8 * C₂ * (2 * C)
  let n₃ := n₂ + n + 2
  let C₄ := 8 * C₃ * (2 * C)
  let n₄ := n₃ + n + 2
  let M : ℝ := (2 : ℝ) ^ p
  let c : ℝ := 2 * M ^ 2 + 2
  let Cfinal := 2 * C₄
  refine ⟨max (Real.exp 1) (2 * Cfinal), ((n₄ + 1 : ℕ) : ℝ),
    le_max_left _ _, ?_, ?_⟩
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n₄)
  · intro P hbdy h B hh hB
    letI : Nonempty {x : Score // x ∈ P.boundary} := hbdy.to_subtype
    letI : Nonempty (SeparableWinsorizedScoreIndex P p h) := ⟨
      ⟨⟨h, ⟨le_rfl, by linarith⟩⟩,
        ⟨false, ⟨Classical.arbitrary _, ⟨0, Classical.arbitrary _⟩⟩⟩⟩⟩
    have hscore : Measurable causalScore := by unfold causalScore; fun_prop
    have htreat : Measurable (treatment P) := by
      unfold treatment
      exact measurable_const.indicator (P.A1_measurable.preimage hscore)
    have harmCoord (t : Bool) : Measurable (armCoord t) := by
      cases t <;> unfold armCoord <;> simp only [Bool.false_eq_true, if_false,
        if_true] <;> fun_prop
    have houtcome : Measurable (observedOutcome P) := by
      unfold observedOutcome
      exact (htreat.mul (harmCoord true)).add
        ((measurable_const.sub htreat).mul (harmCoord false))
    let response : CausalObservation → ℝ := fun w =>
      winsorize B (observedOutcome P w)
    have hresponseMeas : Measurable response :=
      (winsorize_measurable B).comp houtcome
    have hwinsorize (y : ℝ) : |winsorize B y| ≤ B := by
      unfold winsorize
      split_ifs with hy hy0
      · rw [abs_neg, abs_of_nonneg (le_min (abs_nonneg y) hB.le)]
        exact min_le_right _ _
      · simpa [hy0] using hB.le
      · rw [abs_of_nonneg (le_min (abs_nonneg y) hB.le)]
        exact min_le_right _ _
    have hresponseBound (w : CausalObservation) : |response w| ≤ B := hwinsorize _
    have hclip (y : ℝ) : |clip R y| ≤ R := by
      unfold clip
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    let posArm : Arm → CausalObservation → ℝ := fun a w =>
      if a.1 then P.A1.indicator (fun _ => (1 : ℝ)) (causalScore w) else 0
    let negArm : Arm → CausalObservation → ℝ := fun a w =>
      if a.1 then 0 else (-1 : ℝ) ^ a.2.1 *
        P.A0.indicator (fun _ => (1 : ℝ)) (causalScore w)
    let zeroArm : Arm → CausalObservation → ℝ := fun a w =>
      (if a.1 then (1 : ℝ) else -1) *
        P.A0.indicator (fun _ => (1 : ℝ)) (causalScore w)
    let outsideArm : Arm → CausalObservation → ℝ := fun a w =>
      if a.1 then (P.A0 ∪ P.A1)ᶜ.indicator (fun _ => (1 : ℝ)) (causalScore w)
      else 0
    have hposMeas (a : Arm) : Measurable (posArm a) := by
      dsimp [posArm]
      split
      · exact measurable_const.indicator (P.A1_measurable.preimage hscore)
      · exact measurable_const
    have hnegMeas (a : Arm) : Measurable (negArm a) := by
      dsimp [negArm]
      split
      · exact measurable_const
      · exact measurable_const.mul
          (measurable_const.indicator (P.A0_measurable.preimage hscore))
    have hzeroMeas (a : Arm) : Measurable (zeroArm a) := by
      exact measurable_const.mul
        (measurable_const.indicator (P.A0_measurable.preimage hscore))
    have houtsideMeas (a : Arm) : Measurable (outsideArm a) := by
      dsimp [outsideArm]
      split
      · exact measurable_const.indicator
          ((P.A0_measurable.union P.A1_measurable).compl.preimage hscore)
      · exact measurable_const
    have hposBound (a : Arm) (w : CausalObservation) : |posArm a w| ≤ 1 := by
      rcases a with ⟨t, j⟩; cases t <;>
        simp [posArm, Set.indicator] <;> split_ifs <;> norm_num
    have hnegBound (a : Arm) (w : CausalObservation) : |negArm a w| ≤ 1 := by
      rcases a with ⟨t, j⟩; cases t <;>
        simp [negArm, Set.indicator] <;> split_ifs <;> simp [abs_pow]
    have hzeroBound (a : Arm) (w : CausalObservation) : |zeroArm a w| ≤ 1 := by
      rcases a with ⟨t, j⟩; cases t <;>
        simp [zeroArm, Set.indicator] <;> split_ifs <;> norm_num
    have houtsideBound (a : Arm) (w : CausalObservation) :
        |outsideArm a w| ≤ 1 := by
      rcases a with ⟨t, j⟩; cases t <;>
        simp [outsideArm, Set.indicator] <;> split_ifs <;> norm_num
    let ballIndicator : ClosedBallParam 2 → CausalObservation → ℝ :=
      fun cr w => if euclideanClosedBallClassifier 2 cr (causalScore w) then 1 else 0
    have hball : HasPolynomialL2CoverWith ballIndicator 1 Cball nball := by
      have hpdim := HasPseudoDimAtMost.compDomain
        (HasVCAtMost.indicatorClass_hasPseudoDimAtMost
          (euclideanClosedBallClassifier 2) (2 + 2)
          (euclideanClosedBall_hasVCAtMost 2)) causalScore
      simpa [ballIndicator, Cball, nball] using hpdim.hasPolynomialL2CoverWith
        (fun cr => by
          simpa [euclideanClosedBallClassifier] using
            Measurable.ite
              (measurableSet_le (hscore.nndist measurable_const) measurable_const)
              measurable_const measurable_const)
        (by norm_num : (0 : ℝ) < 1)
        (fun cr w => by cases euclideanClosedBallClassifier 2 cr (causalScore w) <;> simp)
    let hboxPos (i : SeparableWinsorizedScoreIndex P p h) :
        CoeffBox (Fin (p + 1)) R :=
      ⟨fun k => clip R (i.2.2.2.1 k), fun k => hclip _⟩
    let hboxNeg (i : SeparableWinsorizedScoreIndex P p h) :
        CoeffBox (Fin (p + 1)) R :=
      ⟨fun k => (-1 : ℝ) ^ k.1 * clip R (i.2.2.2.1 k), fun k => by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact hclip _⟩
    have hpos0 := hradial causalScore posArm response
      hscore hposMeas hposBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2) hR hB
    have hneg0 := hradial causalScore negArm response
      hscore hnegMeas hnegBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2) hR hB
    have hzero0 := hradial causalScore zeroArm response
      hscore hzeroMeas hzeroBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0) hR hB
    have hout0 := hradial (fun _ => (0 : Score)) outsideArm response
      measurable_const houtsideMeas houtsideBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0) hR hB
    let ballParam (i : SeparableWinsorizedScoreIndex P p h) : ClosedBallParam 2 :=
      ⟨i.2.2.1.1, ⟨i.1.1, (lt_of_lt_of_le hh i.1.2.1).le⟩⟩
    let epos (i : SeparableWinsorizedScoreIndex P p h) :=
      (((((i.2.2.1.1, hboxPos i)), (i.2.1, i.2.2.2.2)), i.2.2.2.2), ballParam i)
    let eneg (i : SeparableWinsorizedScoreIndex P p h) :=
      (((((i.2.2.1.1, hboxNeg i)), (i.2.1, i.2.2.2.2)), i.2.2.2.2), ballParam i)
    let ezero (i : SeparableWinsorizedScoreIndex P p h) :
        RadialResidualScoreParam 2 p R Arm × Fin (p + 1) :=
      ((((i.2.2.1.1, hboxPos i)), (i.2.1, i.2.2.2.2)), i.2.2.2.2)
    let eout (i : SeparableWinsorizedScoreIndex P p h) :
        RadialResidualScoreParam 2 p R Arm × Fin (p + 1) :=
      (((((0 : Score), hboxPos i)), (i.2.1, i.2.2.2.2)), i.2.2.2.2)
    have hpos := HasPolynomialL2CoverWith.pullback (hpos0.mul hball) epos
    have hneg := HasPolynomialL2CoverWith.pullback (hneg0.mul hball) eneg
    have hzero := HasPolynomialL2CoverWith.pullback hzero0 ezero
    have hout := HasPolynomialL2CoverWith.pullback hout0 eout
    have hsum := ((hpos.add hneg).add hzero).add hout
    have hV : 0 < B + ((p + 1 : ℕ) : ℝ) * R := by positivity
    have hM : 1 ≤ M := by dsimp [M]; exact one_le_pow₀ (by norm_num)
    have hc : 1 ≤ c := by dsimp [c]; nlinarith [sq_nonneg M]
    have henvLe :
        (radialResidualScoreEnvelope 2 p R B * 1 +
            radialResidualScoreEnvelope 2 p R B * 1 +
            radialResidualScoreEnvelope 0 p R B +
            radialResidualScoreEnvelope 0 p R B) ≤
          c * (B + ((p + 1 : ℕ) : ℝ) * R) := by
      have htwo : radialMonomialEnvelope 2 p = M := by
        simp [radialMonomialEnvelope, M, max_eq_right hM]
      have hzero : radialMonomialEnvelope 0 p = 1 := by
        simp [radialMonomialEnvelope]
      simp only [radialResidualScoreEnvelope, radialPolynomialEnvelope]
      simp_rw [htwo, hzero]
      dsimp [c]
      have hB0 := hB.le
      have hpR : 0 ≤ ((p + 1 : ℕ) : ℝ) * R := by positivity
      have hM0 : 0 ≤ (2 : ℝ) ^ p := by positivity
      nlinarith [mul_nonneg hB0 hM0, mul_nonneg hpR hM0,
        mul_nonneg (add_nonneg hB0 hpR) (sq_nonneg ((2 : ℝ) ^ p))]
    have hrelaxed := hsum.enlargeEnvelope henvLe
    have heq (i : SeparableWinsorizedScoreIndex P p h) (w : CausalObservation) :
        separableWinsorizedScoreFunction P p h B R i w =
          (radialResidualScore 2 p causalScore posArm response h 0 2 R
              i.2.2.2.2 (epos i).1.1 w * ballIndicator (epos i).2 w +
            radialResidualScore 2 p causalScore negArm response h 0 2 R
              i.2.2.2.2 (eneg i).1.1 w * ballIndicator (eneg i).2 w) +
          radialResidualScore 2 p causalScore zeroArm response h 0 0 R
              i.2.2.2.2 (ezero i).1 w +
            radialResidualScore 2 p (fun _ => (0 : Score)) outsideArm response
              h 0 0 R i.2.2.2.2 (eout i).1 w := by
      let z := causalScore w
      let x := i.2.2.1.1
      let q := i.1.1
      let r := dist z x
      have hq : 0 < q := lt_of_lt_of_le hh i.1.2.1
      have hq2 : q < 2 * h := i.1.2.2
      have hr0 : 0 ≤ r := dist_nonneg
      have hballEq : ballIndicator (ballParam i) w = if r ≤ q then 1 else 0 := by
        simp only [ballIndicator, ballParam, euclideanClosedBallClassifier,
          Bool.decide_coe, decide_eq_true_eq]
        change (if dist z x ≤ q then 1 else 0) = if r ≤ q then 1 else 0
        rfl
      have hkpos : uniformKernel (r / q) = if r ≤ q then 1 else 0 := by
        rw [uniformKernel_div_eq_if_abs_le r q hq, abs_of_nonneg hr0]
      have hkneg : uniformKernel (-r / q) = if r ≤ q then 1 else 0 := by
        rw [uniformKernel_div_eq_if_abs_le (-r) q hq, abs_neg,
          abs_of_nonneg hr0]
      have hkneg' : uniformKernel (-(r / q)) = if r ≤ q then 1 else 0 := by
        simpa [neg_div] using hkneg
      have hkzero : uniformKernel 0 = 1 := by simp [uniformKernel]
      have hzeroKernel : (0 : ℝ) / h ∈ Set.Icc (-1 : ℝ) 1 := by simp
      have hzeroRadial : (0 : ℝ) * h ≤ 0 ∧ 0 ≤ 0 * h := by simp
      have hmulComm (u : ℝ) :
          ∑ k : Fin (p + 1), u ^ (k : ℕ) * clip R (i.2.2.2.1 k) =
            ∑ k : Fin (p + 1), clip R (i.2.2.2.1 k) * u ^ (k : ℕ) := by
        apply Finset.sum_congr rfl; intro k _; ring
      have hnegTerm (u : ℝ) (k : Fin (p + 1)) :
          (-1 : ℝ) ^ (k : ℕ) * clip R (i.2.2.2.1 k) * u ^ (k : ℕ) =
            (-u) ^ (k : ℕ) * clip R (i.2.2.2.1 k) := by rw [neg_pow]; ring
      have hnegSum (u : ℝ) :
          ∑ k : Fin (p + 1), (-1 : ℝ) ^ (k : ℕ) *
              clip R (i.2.2.2.1 k) * u ^ (k : ℕ) =
            ∑ k : Fin (p + 1), (-u) ^ (k : ℕ) * clip R (i.2.2.2.1 k) :=
        Finset.sum_congr rfl fun k _ => hnegTerm u k
      have hnegLead (u : ℝ) :
          (-1 : ℝ) ^ (i.2.2.2.2 : ℕ) * u ^ (i.2.2.2.2 : ℕ) =
            (-u) ^ (i.2.2.2.2 : ℕ) := (neg_pow u _).symm
      by_cases hz1 : z ∈ P.A1
      · have hz0 : z ∉ P.A0 := fun hz0 =>
          P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
        have hd : signedDistance (knownGeometry P) x z = r := by
          simp [signedDistance, knownGeometry, indicator_of_mem hz1,
            indicator_of_notMem hz0, r]
        by_cases hr : r ≤ q
        · have hr2 : r ≤ 2 * h := hr.trans hq2.le
          cases hi : i.2.1 <;>
            simp [separableWinsorizedScoreFunction, signedArm,
              radialResidualScore, boundedRadialPolynomial, radialAnnulusMonomial,
              polyBasis, response, posArm, negArm, zeroArm, outsideArm,
              ballParam, epos, eneg,
              ezero, eout, hboxPos, hboxNeg, z, x, q, r, hd, hz1, hz0, hr,
              hr2, hballEq, hkpos, hkneg, hkneg', hkzero, hq.le, hh.le, hi] <;>
              exact Or.inl (hmulComm _)
        · have hrn : ¬ r ≤ q := hr
          cases hi : i.2.1 <;>
            simp [separableWinsorizedScoreFunction, signedArm,
              radialResidualScore, boundedRadialPolynomial, radialAnnulusMonomial,
              polyBasis, response, posArm, negArm, zeroArm, outsideArm,
              ballParam, epos, eneg,
              ezero, eout, hboxPos, hboxNeg, z, x, q, r, hd, hz1, hz0, hrn,
              hballEq, hkpos, hkneg, hkneg', hkzero, hq.le, hh.le, hi]
      · by_cases hz0 : z ∈ P.A0
        · have hd : signedDistance (knownGeometry P) x z = -r := by
            simp [signedDistance, knownGeometry, indicator_of_notMem hz1,
              indicator_of_mem hz0, r]
          by_cases hre : r = 0
          · cases hi : i.2.1 <;>
              simp [separableWinsorizedScoreFunction, signedArm,
                radialResidualScore, boundedRadialPolynomial, radialAnnulusMonomial,
                polyBasis, response, posArm, negArm, zeroArm, outsideArm,
                ballParam, epos, eneg,
                ezero, eout, hboxPos, hboxNeg, z, x, q, r, hd, hz1, hz0, hre,
                hzeroKernel, hzeroRadial, hmulComm, hnegTerm, hnegSum, hnegLead,
                hballEq, hkpos, hkneg, hkneg', hkzero, hq.le, hh.le, hi]
          · by_cases hr : r ≤ q
            · have hr2 : r ≤ 2 * h := hr.trans hq2.le
              have hzx : z ≠ x := by intro hzx; apply hre; simp [r, hzx]
              cases hi : i.2.1 <;>
                simp [separableWinsorizedScoreFunction, signedArm,
                  radialResidualScore, boundedRadialPolynomial, radialAnnulusMonomial,
                  polyBasis, response, posArm, negArm, zeroArm, outsideArm,
                  ballParam, epos, eneg,
                  ezero, eout, hboxPos, hboxNeg, z, x, q, r, hd, hz1, hz0, hre,
                  hr, hr2, hr0, hzx, hq.le, hh.le, hmulComm, hnegTerm, hnegSum,
                  hnegLead, hballEq, hkpos, hkneg, hkneg', hkzero, neg_div, hi]
            · have hzx : z ≠ x := by intro hzx; apply hre; simp [r, hzx]
              cases hi : i.2.1 <;>
                simp [separableWinsorizedScoreFunction, signedArm,
                  radialResidualScore, boundedRadialPolynomial, radialAnnulusMonomial,
                  polyBasis, response, posArm, negArm, zeroArm, outsideArm,
                  ballParam, epos, eneg,
                  ezero, eout, hboxPos, hboxNeg, z, x, q, r, hd, hz1, hz0, hre,
                  hr, hr0, hzx, hq.le, hh.le, hmulComm, hnegTerm, hnegSum,
                  hnegLead, hballEq, hkpos, hkneg, hkneg', hkzero, neg_div, hi]
        · have hzout : z ∈ (P.A0 ∪ P.A1)ᶜ := by simp [hz0, hz1]
          have hd : signedDistance (knownGeometry P) x z = 0 := by
            simp [signedDistance, knownGeometry, indicator_of_notMem hz1,
              indicator_of_notMem hz0]
          cases hi : i.2.1 <;>
            simp [separableWinsorizedScoreFunction, signedArm,
              radialResidualScore, boundedRadialPolynomial, radialAnnulusMonomial,
              polyBasis, response, posArm, negArm, zeroArm, outsideArm,
              ballParam, epos, eneg,
              ezero, eout, hboxPos, hboxNeg, z, x, q, r, hd, hz1, hz0, hzout,
              hzeroKernel, hzeroRadial, hmulComm, hballEq, hkpos, hkneg, hkneg', hkzero,
              hq.le, hh.le, hi]
    have hdiag := HasPolynomialL2CoverWith.pullback hrelaxed
      (fun i : SeparableWinsorizedScoreIndex P p h => (((i, i), i), i))
    have hconverted : HasPolynomialL2CoverWith
        (separableWinsorizedScoreFunction P p h B R)
        (c * (B + ((p + 1 : ℕ) : ℝ) * R)) Cfinal n₄ := by
      convert hdiag using 1
      · funext i w
        simpa using heq i w
    exact ⟨hconverted.forget, hconverted.hasPolynomialEmpiricalL2Cover⟩

end CausalSmith.Stat.BddUniformLogPenalty
