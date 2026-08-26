import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.BinaryPadding
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialContractedBinary

/-!
# Target scaling under the radial Bernoulli channel

This file proves the exact conditional-mean and ATE scaling identities used by
the concrete least-favorable radial handle.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set

private abbrev BinLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw

private abbrev ControlZeroLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw

-- @node: radialContractedBinaryLaw_outcomeMean
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2) and [the transport scale satisfies the stated condition](hyp:ha), [on every
  positive source arm, the common Bernoulli contraction sends the conditional response mean
  through its declared affine channel](goal). -/
lemma radialContractedBinaryLaw_outcomeMean {d : ℕ} (P : BinLaw d) (sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (k : Fin d) (a : Bool)
    (ha : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean
        (radialContractedBinaryLaw P sigma hs0 hs2) a k =
      1 / 2 + sigma / 2 *
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k - 1 / 2) := by
  have hane : CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a ≠ 0 :=
    ne_of_gt ha
  have hy :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a true =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a := by
    rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean]
    field_simp
  have harm :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a false +
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a true := by
    simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass]
    ring
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean
  rw [radialContractedBinaryLaw_jointMass,
    radialContractedBinaryLaw_armMass, Fintype.sum_bool]
  unfold bernoulliContractionSuccess
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [hy]
  have hfalse :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a false =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k *
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a := by
    linarith [harm, hy]
  rw [hfalse]
  field_simp
  ring

-- @node: radialContractedBinaryLaw_ateFunctional_controlZero
/-- If [the overlap constant is positive](hyp:he0) and [the heterogeneity radius is
  nonnegative](hyp:hs0) and [the heterogeneity radius is at most two](hyp:hs2), [on the
  control-zero source family, contraction multiplies the binary ATE by exactly `sigma / 2`,
  including the zero-radius endpoint](goal). -/
lemma radialContractedBinaryLaw_ateFunctional_controlZero {n d : ℕ}
    {epsilon sigma : ℝ} (P : ControlZeroLaw n d epsilon)
    (he0 : 0 < epsilon) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional
        (radialContractedBinaryLaw P.1 sigma hs0 hs2) =
      sigma / 2 *
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 := by
  rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_weighted_regression
    _ (radialContractedBinaryLaw_overlap P.1 hs0 hs2 P.2.overlap)]
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k
  · have hpi := P.2.overlap k hk
    have hmass_ne : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k ≠ 0 :=
      ne_of_gt hk
    have htrue :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k true =
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 k *
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k := by
      rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity]
      field_simp
    have hmass :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k =
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k false +
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k true := by
      simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass,
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass]
      ring
    have hprop_pos :
        0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 k :=
      lt_of_lt_of_le he0 hpi.1
    have hprop_lt :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 k < 1 := by
      linarith
    have htrue_pos :
        0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k true := by
      rw [htrue]
      exact mul_pos hprop_pos hk
    have hfalse :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k false =
          (1 - CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 k) *
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k := by
      rw [htrue] at hmass
      linarith
    have hfalse_pos :
        0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k false := by
      rw [hfalse]
      exact mul_pos (sub_pos.mpr hprop_lt) hk
    rw [radialContractedBinaryLaw_cellMass,
      radialContractedBinaryLaw_outcomeMean P.1 sigma hs0 hs2 k true htrue_pos,
      radialContractedBinaryLaw_outcomeMean P.1 sigma hs0 hs2 k false hfalse_pos,
      P.2.control_zero k]
    ring
  · have hk0 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k = 0 :=
      le_antisymm (le_of_not_gt hk)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass_mem_unitInterval P.1 k).1
    rw [radialContractedBinaryLaw_cellMass, hk0]
    ring

-- @node: radialPaddedAffine_rawAteFormula
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the overlap constant is
  positive](hyp:he0) and [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity
  radius is at most two](hyp:hs2), [zero-mass padding and affine outcome scaling preserve the
  radial target identity, giving the exact slope used by Markov-kernel risk transport](goal). -/
lemma radialPaddedAffine_rawAteFormula {n m d : ℕ} {epsilon M sigma : ℝ}
    (P : ControlZeroLaw n m epsilon) (hmd : m ≤ d)
    (he0 : 0 < epsilon) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    rawAteFormula
        (affineBinaryRealLaw M
          (binaryPadLaw hmd (radialContractedBinaryLaw P.1 sigma hs0 hs2))) =
      (M * sigma / 2) *
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 := by
  rw [rawAteFormula_eq_mul_binaryAte_of_embedding
      (affineBinaryRealLaw_embedding M _) (binaryPadLaw_overlap hmd
        (radialContractedBinaryLaw_overlap P.1 hs0 hs2 P.2.overlap)),
    binaryPadLaw_ateFunctional hmd
      (radialContractedBinaryLaw_overlap P.1 hs0 hs2 P.2.overlap),
    radialContractedBinaryLaw_ateFunctional_controlZero P he0 hs0 hs2]
  ring

-- @node: targetSeparationCertificate_of_pointwise_targets
/-- If [the transport scale satisfies the stated condition](hyp:ha) and [the radial target formula
  holds](hyp:hradial) and [the exact risk-transfer identity holds](hyp:hexact), [pointwise affine
  target formulas for the radial and exact source families imply the pairwise separation
  certificate by subtraction](goal). -/
lemma targetSeparationCertificate_of_pointwise_targets {n d : ℕ}
    {epsilon M sigma a b : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (ha : a = M * H.lambda)
    (hradial : ∀ P ∈ H.radialSource,
      rawAteFormula (H.radialEmbedding P) =
        a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 + b)
    (hexact : ∀ P ∈ H.exactSource,
      rawAteFormula (H.exactEmbedding P) =
        M * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) :
    TargetSeparationCertificate H := by
  constructor
  · intro P0 hP0 P1 hP1
    rw [hradial P1 hP1, hradial P0 hP0, ha]
    ring
  · intro P0 hP0 P1 hP1
    rw [hexact P1 hP1, hexact P0 hP0]
    ring

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
