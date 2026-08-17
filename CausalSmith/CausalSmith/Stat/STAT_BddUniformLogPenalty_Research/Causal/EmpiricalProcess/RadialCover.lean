import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.Separability
import Causalean.Stat.Concentration.Covering.EuclideanRadialPolynomial
import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.Basic

/-!
# Radial covering adapter for the winsorized score

This module specializes the neutral moving-center Euclidean radial-polynomial
certificate to the paper's signed-distance, uniform-kernel score.  The proof
keeps the strict and non-strict signed arms separate, including the radius-zero
trace, so it remains uniform for empirical laws with atoms on moving
boundaries.
-/

open Causalean.Stat.Concentration
open Causalean.Stat.Concentration.EuclideanRadialPolynomial
open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- At every positive coefficient clipping radius there are polynomial
covering constants depending only on the degree such that all laws,
bandwidths, and positive winsorization levels share both an arbitrary-law
`L²(Q)` certificate and the same empirical covering constants, with envelope
`B + (p+1)R`. -/
lemma winsorizedScore_hasUniformPolynomialL2Cover
    (p : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ A v : ℝ, Real.exp 1 ≤ A ∧ 1 ≤ v ∧
      ∀ (P : A1A2Law) {h B : ℝ}, 0 < h → 0 < B →
        HasPolynomialL2Cover (winsorizedScoreFunction P p h B R)
            (B + ((p + 1 : ℕ) : ℝ) * R) ∧
          HasPolynomialEmpiricalL2Cover (winsorizedScoreFunction P p h B R)
            (B + ((p + 1 : ℕ) : ℝ) * R) A v := by
  classical
  let Arm := Bool × Fin (p + 1)
  obtain ⟨C, n, hradial⟩ :=
    radialResidualScore_hasUniformPolynomialL2CoverWith
      (Ω := CausalObservation) (A := Arm) 2 p
  let C₁ := 2 * C
  let C₂ := 8 * C₁ * C₁
  let n₂ := n + n + 2
  let C₃ := 8 * C₂ * C₁
  let n₃ := n₂ + n + 2
  let C₄ := 8 * C₃ * C₁
  let n₄ := n₃ + n + 2
  let Cdiag := 2 * C₄
  let Cfinal := 4 * Cdiag
  refine ⟨max (Real.exp 1) (2 * Cfinal), ((n₄ + 1 : ℕ) : ℝ),
    le_max_left _ _, ?_, ?_⟩
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n₄)
  · intro P h B hh hB
    have hscore : Measurable causalScore := by
      unfold causalScore
      fun_prop
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
    let response : CausalObservation → ℝ :=
      fun w => winsorize B (observedOutcome P w)
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
    have hresponseBound (w : CausalObservation) : |response w| ≤ B :=
      hwinsorize _
    have hclip (y : ℝ) : |clip R y| ≤ R := by
      unfold clip
      rw [abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith) (min_le_left _ _)
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
      rcases a with ⟨t, j⟩
      cases t <;> simp [posArm, Set.indicator] <;> split_ifs <;> norm_num
    have hnegBound (a : Arm) (w : CausalObservation) : |negArm a w| ≤ 1 := by
      rcases a with ⟨t, j⟩
      cases t <;> simp [negArm, Set.indicator] <;> split_ifs <;>
        simp [abs_pow]
    have hzeroBound (a : Arm) (w : CausalObservation) : |zeroArm a w| ≤ 1 := by
      rcases a with ⟨t, j⟩
      cases t <;> simp [zeroArm, Set.indicator] <;> split_ifs <;> norm_num
    have houtsideBound (a : Arm) (w : CausalObservation) :
        |outsideArm a w| ≤ 1 := by
      rcases a with ⟨t, j⟩
      cases t <;> simp [outsideArm, Set.indicator] <;> split_ifs <;> norm_num
    let hboxPos (i : WinsorizedScoreIndex p) :
        CoeffBox (Fin (p + 1)) R :=
      ⟨fun k => clip R (i.2.2.1 k), fun k => hclip _⟩
    let hboxNeg (i : WinsorizedScoreIndex p) :
        CoeffBox (Fin (p + 1)) R :=
      ⟨fun k => (-1 : ℝ) ^ k.1 * clip R (i.2.2.1 k), fun k => by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact hclip _⟩
    have hpos0 := hradial causalScore posArm response
      hscore hposMeas hposBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) hR hB
    have hneg0 := hradial causalScore negArm response
      hscore hnegMeas hnegBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) hR hB
    have hzero0 := hradial causalScore zeroArm response
      hscore hzeroMeas hzeroBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0) hR hB
    have hout0 := hradial (fun _ => (0 : Score)) outsideArm response
      measurable_const houtsideMeas houtsideBound hresponseMeas hresponseBound hh
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0) hR hB
    let epos : WinsorizedScoreIndex p →
        RadialResidualScoreParam 2 p R Arm × Fin (p + 1) := fun i =>
      ((((i.2.1, hboxPos i)), (i.1, i.2.2.2)), i.2.2.2)
    let eneg : WinsorizedScoreIndex p →
        RadialResidualScoreParam 2 p R Arm × Fin (p + 1) := fun i =>
      ((((i.2.1, hboxNeg i)), (i.1, i.2.2.2)), i.2.2.2)
    let ezero : WinsorizedScoreIndex p →
        RadialResidualScoreParam 2 p R Arm × Fin (p + 1) := fun i =>
      ((((i.2.1, hboxPos i)), (i.1, i.2.2.2)), i.2.2.2)
    let eout : WinsorizedScoreIndex p →
        RadialResidualScoreParam 2 p R Arm × Fin (p + 1) := fun i =>
      (((((0 : Score), hboxPos i)), (i.1, i.2.2.2)), i.2.2.2)
    have hpos := HasPolynomialL2CoverWith.pullback hpos0 epos
    have hneg := HasPolynomialL2CoverWith.pullback hneg0 eneg
    have hzero := HasPolynomialL2CoverWith.pullback hzero0 ezero
    have hout := HasPolynomialL2CoverWith.pullback hout0 eout
    have hsum := ((hpos.add hneg).add hzero).add hout
    have henvelope : 0 < B + ((p + 1 : ℕ) : ℝ) * R := by positivity
    have heq (i : WinsorizedScoreIndex p) (w : CausalObservation) :
        winsorizedScoreFunction P p h B R i w =
          radialResidualScore 2 p causalScore posArm response h 0 1 R
              i.2.2.2 (epos i).1 w +
            radialResidualScore 2 p causalScore negArm response h 0 1 R
              i.2.2.2 (eneg i).1 w +
            radialResidualScore 2 p causalScore zeroArm response h 0 0 R
              i.2.2.2 (ezero i).1 w +
            radialResidualScore 2 p (fun _ => (0 : Score)) outsideArm response
              h 0 0 R i.2.2.2 (eout i).1 w := by
      let z := causalScore w
      let x := i.2.1
      let r := dist z x
      have hr0 : 0 ≤ r := dist_nonneg
      have hzeroKernel : (0 : ℝ) / h ∈ Set.Icc (-1 : ℝ) 1 := by
        simp
      have hzeroRadial : (0 : ℝ) * h ≤ 0 ∧ 0 ≤ 0 * h := by simp
      have hmulComm (u : ℝ) :
          ∑ k : Fin (p + 1), u ^ (k : ℕ) * clip R (i.2.2.1 k) =
            ∑ k : Fin (p + 1), clip R (i.2.2.1 k) * u ^ (k : ℕ) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      have hnegTerm (u : ℝ) (k : Fin (p + 1)) :
          (-1 : ℝ) ^ (k : ℕ) * clip R (i.2.2.1 k) * u ^ (k : ℕ) =
            (-u) ^ (k : ℕ) * clip R (i.2.2.1 k) := by
        rw [neg_pow]
        ring
      have hnegSum (u : ℝ) :
          ∑ k : Fin (p + 1),
              (-1 : ℝ) ^ (k : ℕ) * clip R (i.2.2.1 k) * u ^ (k : ℕ) =
            ∑ k : Fin (p + 1), (-u) ^ (k : ℕ) * clip R (i.2.2.1 k) := by
        exact Finset.sum_congr rfl fun k _ => hnegTerm u k
      have hnegLead (u : ℝ) :
          (-1 : ℝ) ^ (i.2.2.2 : ℕ) * u ^ (i.2.2.2 : ℕ) =
            (-u) ^ (i.2.2.2 : ℕ) := by
        exact (neg_pow u (i.2.2.2 : ℕ)).symm
      by_cases hz1 : z ∈ P.A1
      · have hz0 : z ∉ P.A0 := fun hz0 =>
          P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
        have hd : signedDistance (knownGeometry P) x z = r := by
          simp [signedDistance, knownGeometry, indicator_of_mem hz1,
            indicator_of_notMem hz0, r]
        by_cases hr : r ≤ h
        · have hdiv : r / h ∈ Set.Icc (-1 : ℝ) 1 := by
            constructor
            · exact le_trans (by norm_num) (div_nonneg hr0 hh.le)
            · exact (div_le_one hh).2 hr
          cases hi : i.1 <;>
            simp [winsorizedScoreFunction, signedArm, uniformKernel,
              radialResidualScore, boundedRadialPolynomial,
              radialAnnulusMonomial, polyBasis, response, posArm, negArm,
              zeroArm, outsideArm, epos, eneg, ezero, eout, hboxPos,
              hboxNeg, z, x, r, hd, hz1, hz0, hr, hdiv, hh.le, hi]
              <;> exact Or.inl (hmulComm _)
        · have hdiv : r / h ∉ Set.Icc (-1 : ℝ) 1 := by
            intro hk
            exact hr ((div_le_one hh).1 hk.2)
          cases hi : i.1 <;>
            simp [winsorizedScoreFunction, signedArm, uniformKernel,
              radialResidualScore, boundedRadialPolynomial,
              radialAnnulusMonomial, polyBasis, response, posArm, negArm,
              zeroArm, outsideArm, epos, eneg, ezero, eout, hboxPos,
              hboxNeg, z, x, r, hd, hz1, hz0, hr, hdiv, hh.le, hi]
      · by_cases hz0 : z ∈ P.A0
        · have hd : signedDistance (knownGeometry P) x z = -r := by
            simp [signedDistance, knownGeometry, indicator_of_notMem hz1,
              indicator_of_mem hz0, r]
          by_cases hre : r = 0
          · cases hi : i.1 <;>
              simp [winsorizedScoreFunction, signedArm, uniformKernel,
                radialResidualScore, boundedRadialPolynomial,
                radialAnnulusMonomial, polyBasis, response, posArm, negArm,
                zeroArm, outsideArm, epos, eneg, ezero, eout, hboxPos,
                hboxNeg, z, x, r, hd, hz1, hz0, hre, hzeroKernel,
                hzeroRadial, hmulComm, hnegTerm, hnegSum, hnegLead, hh.le, hi]
          · by_cases hr : r ≤ h
            · have hdiv : -r / h ∈ Set.Icc (-1 : ℝ) 1 := by
                constructor
                · rw [neg_div]
                  exact (neg_le_neg_iff.mpr ((div_le_one hh).2 hr))
                · exact le_trans (by
                    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr0) hh.le)
                    (by norm_num)
              have hposDiv : r / h ≤ 1 := (div_le_one hh).2 hr
              have hdiv' : -(r / h) ∈ Set.Icc (-1 : ℝ) 1 := by
                simpa [neg_div] using hdiv
              have hzx : z ≠ x := by
                intro hzx
                apply hre
                simp [r, hzx]
              cases hi : i.1 <;>
                simp [winsorizedScoreFunction, signedArm, uniformKernel,
                  radialResidualScore, boundedRadialPolynomial,
                  radialAnnulusMonomial, polyBasis, response, posArm, negArm,
                  zeroArm, outsideArm, epos, eneg, ezero, eout, hboxPos,
                  hboxNeg, z, x, r, hd, hz1, hz0, hre, hr, hdiv,
                  hdiv', hposDiv, hr0, hh.le, hzx, hmulComm, hnegTerm, hnegSum,
                  hnegLead, neg_div, hi]
            · have hdiv : -r / h ∉ Set.Icc (-1 : ℝ) 1 := by
                intro hk
                apply hr
                apply (div_le_one hh).1
                have htmp := neg_le_neg hk.1
                rw [neg_neg, neg_div] at htmp
                linarith
              have hzx : z ≠ x := by
                intro hzx
                apply hre
                simp [r, hzx]
              cases hi : i.1 <;>
                simp [winsorizedScoreFunction, signedArm, uniformKernel,
                  radialResidualScore, boundedRadialPolynomial,
                  radialAnnulusMonomial, polyBasis, response, posArm, negArm,
                  zeroArm, outsideArm, epos, eneg, ezero, eout, hboxPos,
                  hboxNeg, z, x, r, hd, hz1, hz0, hre, hr, hdiv,
                  hr0, hh.le, hzx, hmulComm, hnegTerm, hnegSum, hnegLead, hi]
        · have hzout : z ∈ (P.A0 ∪ P.A1)ᶜ := by simp [hz0, hz1]
          have hd : signedDistance (knownGeometry P) x z = 0 := by
            simp [signedDistance, knownGeometry, indicator_of_notMem hz1,
              indicator_of_notMem hz0]
          cases hi : i.1 <;>
            simp [winsorizedScoreFunction, signedArm, uniformKernel,
              radialResidualScore, boundedRadialPolynomial,
              radialAnnulusMonomial, polyBasis, response, posArm, negArm,
              zeroArm, outsideArm, epos, eneg, ezero, eout, hboxPos,
              hboxNeg, z, x, r, hd, hz1, hz0, hzout, hzeroKernel,
              hzeroRadial, hmulComm, hi]
    have htight : HasPolynomialL2CoverWith
        (winsorizedScoreFunction P p h B R)
        (B + ((p + 1 : ℕ) : ℝ) * R) Cfinal n₄ := by
      have hbound (i : WinsorizedScoreIndex p) (w : CausalObservation) :
          |winsorizedScoreFunction P p h B R i w| ≤
            B + ((p + 1 : ℕ) : ℝ) * R := by
        let d := signedDistance (knownGeometry P) i.2.1 (causalScore w)
        by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
        · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
          have hpolyj : |polyBasis p (d / h) i.2.2.2| ≤ 1 := by
            unfold polyBasis
            rw [abs_pow]
            exact pow_le_one₀ (abs_nonneg _) hu
          have hpoly :
              |∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k)| ≤
                ((p + 1 : ℕ) : ℝ) * R := by
            calc
              |∑ k, polyBasis p (d / h) k * clip R (i.2.2.1 k)| ≤
                  ∑ k, |polyBasis p (d / h) k * clip R (i.2.2.1 k)| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _k : Fin (p + 1), R := by
                apply Finset.sum_le_sum
                intro k _
                rw [abs_mul]
                exact (mul_le_mul
                  (by
                    unfold polyBasis
                    rw [abs_pow]
                    exact pow_le_one₀ (abs_nonneg _) hu)
                  (hclip _) (abs_nonneg _) (by positivity)).trans_eq (one_mul R)
              _ = ((p + 1 : ℕ) : ℝ) * R := by simp
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
                exact (abs_sub _ _).trans
                  (add_le_add (hwinsorize _) hpoly)
          · simp
            positivity
        · rw [winsorizedScoreFunction, uniformKernel, indicator_of_notMem hk]
          simp
          positivity
      have hsum' : HasPolynomialL2CoverWith
          (fun i w => winsorizedScoreFunction P p h B R i w)
          (4 * (B + ((p + 1 : ℕ) : ℝ) * R)) Cdiag n₄ := by
        have hsumDiag := HasPolynomialL2CoverWith.pullback hsum
          (fun i : WinsorizedScoreIndex p => (((i, i), i), i))
        convert hsumDiag using 1
        · funext i w
          simpa using heq i w
        · simp [radialResidualScoreEnvelope, radialMonomialEnvelope,
            radialPolynomialEnvelope]
          ring
      simpa [Cfinal, mul_assoc] using
        hsum'.tightenEnvelopeBy (c := 4) (by norm_num) henvelope hbound
    exact ⟨htight.forget, htight.hasPolynomialEmpiricalL2Cover⟩

/-- For a positive bandwidth, winsorization level, and coefficient clipping
radius, the entire finite-arm, finite-coordinate winsorized score class has a
uniform polynomial `L²(Q)` cover over every probability measure `Q`, with
envelope `B + (p+1)R`. -/
lemma winsorizedScore_hasPolynomialL2Cover
    (P : A1A2Law) (p : ℕ) {h B R : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hR : 0 < R) :
    HasPolynomialL2Cover (winsorizedScoreFunction P p h B R)
      (B + ((p + 1 : ℕ) : ℝ) * R) := by
  obtain ⟨A, v, hA, hv, hcover⟩ :=
    winsorizedScore_hasUniformPolynomialL2Cover p hR
  exact (hcover P hh hB).1


end CausalSmith.Stat.BddUniformLogPenalty
