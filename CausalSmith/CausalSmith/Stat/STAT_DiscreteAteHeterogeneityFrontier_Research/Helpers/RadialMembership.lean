/- Ambient membership of the padded Bernoulli-contracted radial family. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialTarget

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set

private abbrev ControlZeroLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw

-- @node: radialPaddedAffine_approximateHomogeneity
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the overlap constant is
  positive](hyp:he0) and [the outcome scale satisfies its stated bound](hyp:hM) and [the
  heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [the contracted control-zero construction has realization-wise radius at most
  `sigma * M`, including the zero-radius endpoint](goal). -/
lemma radialPaddedAffine_approximateHomogeneity {n m d : ℕ}
    {epsilon M sigma : ℝ} (P : ControlZeroLaw n m epsilon) (hmd : m ≤ d)
    (he0 : 0 < epsilon) (hM : 0 ≤ M)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    ApproximateHomogeneity M sigma
      (affineBinaryRealLaw M
        (binaryPadLaw hmd (radialContractedBinaryLaw P.1 sigma hs0 hs2))) := by
  intro k hk
  have hraw := radialPaddedAffine_rawAteFormula (M := M) P hmd he0 hs0 hs2
  by_cases himage : ∃ r : Fin m,
      (⟨r, lt_of_lt_of_le r.isLt hmd⟩ : Fin d) = k
  · obtain ⟨r, rfl⟩ := himage
    have hmass :
        0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 r := by
      change 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
        (binaryPadLaw hmd (radialContractedBinaryLaw P.1 sigma hs0 hs2))
          ⟨r, lt_of_lt_of_le r.isLt hmd⟩ at hk
      rw [binaryPadLaw_cellMass_image, radialContractedBinaryLaw_cellMass] at hk
      exact hk
    have hpi := P.2.overlap r hmass
    have htrue :
        0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 r true := by
      rw [show CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 r true =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 r *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 r by
            unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity
            field_simp]
      exact mul_pos (he0.trans_le hpi.1) hmass
    have hfalse :
        0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 r false := by
      have hadd :=
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass_add_eq_cellMass P.1 r
      have htrue_eq :
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 r true =
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 r *
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 r := by
        unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity
        field_simp
      rw [htrue_eq] at hadd
      have hpilt :
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 r < 1 := by
        linarith
      nlinarith
    rcases
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval
          P.1 true r with ⟨heta0, heta1⟩
    have hpsi0 :
        0 ≤ CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 := by
      unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional
      exact Finset.sum_nonneg fun j _ => mul_nonneg
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass_mem_unitInterval
          P.1 j).1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval
          P.1 true j).1
    have hpsi1 :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 ≤ 1 := by
      unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional
      calc
        ∑ j : Fin m, CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 j *
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P.1 true j ≤
            ∑ j : Fin m,
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 j * 1 := by
              gcongr with j
              · exact
                  (CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass_mem_unitInterval
                    P.1 j).1
              · exact
                  (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval
                    P.1 true j).2
        _ = 1 := by
          simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.sum_cellMass_eq_one]
    unfold cellDeviation cellEffect
    change |M * (_ - 1 / 2) - M * (_ - 1 / 2) - _| ≤ sigma * M
    rw [binaryPadLaw_outcomeMean_image, binaryPadLaw_outcomeMean_image,
      radialContractedBinaryLaw_outcomeMean P.1 sigma hs0 hs2 r true htrue,
      radialContractedBinaryLaw_outcomeMean P.1 sigma hs0 hs2 r false hfalse,
      P.2.control_zero r, hraw]
    have hscale : 0 ≤ M * sigma / 2 := by positivity
    have hdiff :
        |CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P.1 true r -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1| ≤ 1 :=
      (abs_le).2 ⟨by linarith, by linarith⟩
    have heq :
        M * (1 / 2 + sigma / 2 *
              (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P.1 true r -
                1 / 2) - 1 / 2) -
          M * (1 / 2 + sigma / 2 * (0 - 1 / 2) - 1 / 2) -
          M * sigma / 2 *
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 =
          (M * sigma / 2) *
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P.1 true r -
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1) := by
      ring
    rw [heq, abs_mul, abs_of_nonneg hscale]
    calc
      (M * sigma / 2) *
          |CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P.1 true r -
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1| ≤
          (M * sigma / 2) * 1 := mul_le_mul_of_nonneg_left hdiff hscale
      _ ≤ sigma * M := by nlinarith [mul_nonneg hM hs0]
  · have hoff := binaryPadLaw_cellMass_off_image hmd
      (radialContractedBinaryLaw P.1 sigma hs0 hs2) k (by simpa using himage)
    change CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
      (binaryPadLaw hmd (radialContractedBinaryLaw P.1 sigma hs0 hs2)) k > 0 at hk
    linarith

-- @node: radialPaddedAffineLaw_model
/-- The concrete padded radial channel is an ambient model-class element. -/
noncomputable def radialPaddedAffineLaw_model {n m d : ℕ} (hmd : m ≤ d)
    {epsilon M sigma : ℝ} (P : ControlZeroLaw n m epsilon)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (hM : 1 ≤ M)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    ModelClass d epsilon M sigma where
  law := affineBinaryRealLaw M
    (binaryPadLaw hmd (radialContractedBinaryLaw P.1 sigma hs0 hs2))
  epsilon_pos := he0
  epsilon_lt_half := he1
  M_ge_one := hM
  sigma_nonneg := hs0
  sigma_le_two := hs2
  consistency := affineBinaryRealLaw_consistency M _
  exchangeability := affineBinaryRealLaw_exchangeability M _
  overlap := affineBinaryRealLaw_overlap
    (binaryPadLaw_overlap hmd
      (radialContractedBinaryLaw_overlap P.1 hs0 hs2 P.2.overlap))
  mean_normalization := affineBinaryRealLaw_meanNormalization
    (le_trans zero_le_one hM)
  second_moment := affineBinaryRealLaw_secondCentralMoment
    (le_trans zero_le_one hM)
  homogeneity := radialPaddedAffine_approximateHomogeneity P hmd he0
    (le_trans zero_le_one hM) hs0 hs2

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
