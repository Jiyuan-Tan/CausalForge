import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ConcreteRadialHandle

/-!
# Full-data coupling under the radial Bernoulli channel

This module proves the finite PMF identity behind the full-data radial-channel
certificate, including the zero-mass-cell boundary case.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

private abbrev BinLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw

-- @node: contractedFullPMF
/-- This is the full-data probability mass function obtained after radial Bernoulli contraction. -/
noncomputable def contractedFullPMF {m : ℕ} (P : BinLaw m) (sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) : PMF (BinaryFullObs m) :=
  (binaryIndependentFullPMF P).bind fun z =>
    (radialContractionPMF sigma z.b0 hs0 hs2).bind fun c0 =>
      (radialContractionPMF sigma z.b1 hs0 hs2).map fun c1 =>
        ⟨z.x, z.a, c0, c1⟩

-- @node: binaryOutcomePMF_radialContracted
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2) and [the transport scale satisfies the stated condition](hyp:ha), [the outcome
  distribution of a radially contracted binary law is the corresponding Bernoulli contraction
  distribution](goal). -/
lemma binaryOutcomePMF_radialContracted {m : ℕ} (P : BinLaw m)
    (sigma : ℝ) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (k : Fin m)
    (a : Bool) (ha : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a) :
    binaryOutcomePMF (radialContractedBinaryLaw P sigma hs0 hs2) a k =
      (binaryOutcomePMF P a k).bind fun b =>
        radialContractionPMF sigma b hs0 hs2 := by
  apply PMF.ext
  intro c
  suffices hreal :
      (binaryOutcomePMF (radialContractedBinaryLaw P sigma hs0 hs2) a k c).toReal =
        (((binaryOutcomePMF P a k).bind fun b =>
          radialContractionPMF sigma b hs0 hs2) c).toReal by
    rw [ENNReal.toReal_eq_toReal_iff] at hreal
    rcases hreal with h | h | h
    · exact h
    · exact False.elim ((PMF.apply_ne_top _ _) h.2)
    · exact False.elim ((PMF.apply_ne_top _ _) h.1)
  cases c
  · rw [binaryOutcomePMF_false_toReal, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum]
    · rw [Fintype.sum_bool, ENNReal.toReal_mul, ENNReal.toReal_mul,
        binaryOutcomePMF_true_toReal, binaryOutcomePMF_false_toReal,
        radialContractionPMF_false_toReal,
        radialContractionPMF_false_toReal,
        radialContractedBinaryLaw_outcomeMean P sigma hs0 hs2 k a ha]
      unfold bernoulliContractionSuccess
      simp only [if_true, Bool.false_eq_true, if_false]
      ring
    · intro b _hb
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  · rw [binaryOutcomePMF_true_toReal, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum]
    · rw [Fintype.sum_bool, ENNReal.toReal_mul, ENNReal.toReal_mul,
        binaryOutcomePMF_true_toReal, binaryOutcomePMF_false_toReal,
        radialContractionPMF_true_toReal,
        radialContractionPMF_true_toReal,
        radialContractedBinaryLaw_outcomeMean P sigma hs0 hs2 k a ha]
      unfold bernoulliContractionSuccess
      simp only [if_true, Bool.false_eq_true, if_false]
      ring
    · intro b _hb
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

-- @node: contractedFullPMF_eq_independent
/-- If [the overlap constant is positive](hyp:he0) and [the heterogeneity radius is
  nonnegative](hyp:hs0) and [the heterogeneity radius is at most two](hyp:hs2), [the contracted
  full-data distribution equals the independent coupling generated from the contracted observed
  law](goal). -/
lemma contractedFullPMF_eq_independent {n m : ℕ} {epsilon : ℝ}
    (P : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n m epsilon)
    (he0 : 0 < epsilon) (sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    contractedFullPMF P.1 sigma hs0 hs2 =
      binaryIndependentFullPMF (radialContractedBinaryLaw P.1 sigma hs0 hs2) := by
  apply PMF.ext
  rintro ⟨k, a, c0, c1⟩
  by_cases hk : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k
  · have hpi := P.2.overlap k hk
    have hmne : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k ≠ 0 :=
      ne_of_gt hk
    have htrue_eq :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k true =
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 k *
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k := by
      rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity]
      field_simp
    have htrue : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k true := by
      rw [htrue_eq]
      exact mul_pos (lt_of_lt_of_le he0 hpi.1) hk
    have hmass_eq :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k =
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k false +
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k true := by
      simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass,
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass]
      ring
    have hfalse_eq :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k false =
          (1 - CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P.1 k) *
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k := by
      rw [htrue_eq] at hmass_eq
      linarith
    have hfalse : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P.1 k false := by
      rw [hfalse_eq]
      exact mul_pos (by linarith [hpi.2]) hk
    have hout_true (c : Bool) :
        (binaryOutcomePMF
          ({ pmf := P.1.pmf.bind fun z =>
              (radialContractionPMF sigma z.2.2 hs0 hs2).map
                (fun b' => (⟨z.1, z.2.1, b'⟩ :
                  CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs m)) } : BinLaw m)
          true k) c =
          (((binaryOutcomePMF P.1 true k).bind fun b =>
            radialContractionPMF sigma b hs0 hs2) c) := by
      simpa only [radialContractedBinaryLaw] using congrArg (fun q : PMF Bool => q c)
        (binaryOutcomePMF_radialContracted P.1 sigma hs0 hs2 k true htrue)
    have hout_false (c : Bool) :
        (binaryOutcomePMF
          ({ pmf := P.1.pmf.bind fun z =>
              (radialContractionPMF sigma z.2.2 hs0 hs2).map
                (fun b' => (⟨z.1, z.2.1, b'⟩ :
                  CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs m)) } : BinLaw m)
          false k) c =
          (((binaryOutcomePMF P.1 false k).bind fun b =>
            radialContractionPMF sigma b hs0 hs2) c) := by
      simpa only [radialContractedBinaryLaw] using congrArg (fun q : PMF Bool => q c)
        (binaryOutcomePMF_radialContracted P.1 sigma hs0 hs2 k false hfalse)
    cases a <;> cases c0 <;> cases c1 <;>
      simp [contractedFullPMF, binaryIndependentFullPMF, radialContractedBinaryLaw,
        binaryIndependentLift, PMF.bind_apply, PMF.map_apply, tsum_fintype,
        Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_eq_single k,
        binaryOutcomePMF_radialContracted P.1 sigma hs0 hs2 k true htrue,
        binaryOutcomePMF_radialContracted P.1 sigma hs0 hs2 k false hfalse]
    all_goals
      rw [Finset.sum_eq_single k]
      · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        simp [hout_true, hout_false, PMF.bind_apply, tsum_fintype,
          Fintype.sum_bool] <;> ring
      · intro x _hx hxk
        simp [hxk, Ne.symm hxk]
      · simp
  · have hk0 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k = 0 :=
      le_antisymm (le_of_not_gt hk)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass_mem_unitInterval P.1 k).1
    have hp (a y : Bool) : P.1.pmf (k, a, y) = 0 := by
      have hj :=
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass_eq_zero_of_cellMass_eq_zero
          P.1 k hk0 a y
      unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass at hj
      rw [ENNReal.toReal_eq_zero_iff] at hj
      rcases hj with h | h
      · exact h
      · exact False.elim ((PMF.apply_ne_top P.1.pmf (k, a, y)) h)
    cases a <;> cases c0 <;> cases c1 <;>
      simp [contractedFullPMF, binaryIndependentFullPMF, radialContractedBinaryLaw,
        binaryIndependentLift, PMF.bind_apply, PMF.map_apply, tsum_fintype,
        Fintype.sum_prod_type, Fintype.sum_bool, hp]
    all_goals
      rw [Finset.sum_eq_single k]
      · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        simp [hp]
      · intro x _hx hxk
        simp [hxk, Ne.symm hxk]
      · simp

-- @node: radialPaddedAffine_fullLaw_eq_binaryFullChannel
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the overlap constant is
  positive](hyp:he0) and [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity
  radius is at most two](hyp:hs2), [the concrete affine radial embedding is exactly the paper's
  common two-potential-outcome Bernoulli channel applied to the independent source
  coupling](goal). -/
lemma radialPaddedAffine_fullLaw_eq_binaryFullChannel {n m d : ℕ}
    {epsilon : ℝ}
    (P : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n m epsilon)
    (hmd : m ≤ d) (he0 : 0 < epsilon) (M sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    (affineBinaryRealLaw M
      (binaryPadLaw hmd (radialContractedBinaryLaw P.1 sigma hs0 hs2))).fullLaw =
      binaryFullChannel
        (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩)
        (bernoulliContractionSuccess sigma)
        (fun b => M * ((if b then 1 else 0) - 1 / 2))
        (binaryIndependentFullPMF P.1).toMeasure := by
  let P0 : BinLaw m := P.1
  change (affineBinaryRealLaw M
      (binaryPadLaw hmd (radialContractedBinaryLaw P0 sigma hs0 hs2))).fullLaw =
    binaryFullChannel _ _ _ (binaryIndependentFullPMF P0).toMeasure
  have hc : contractedFullPMF P0 sigma hs0 hs2 =
      binaryIndependentFullPMF (radialContractedBinaryLaw P0 sigma hs0 hs2) := by
    simpa [P0] using contractedFullPMF_eq_independent P he0 sigma hs0 hs2
  rw [affineBinaryPadded_fullLaw, ← hc]
  ext E hE
  rw [Measure.map_apply (by fun_prop) hE]
  unfold contractedFullPMF
  rw [PMF.toMeasure_bind_apply
    (p := binaryIndependentFullPMF P0)
    (f := fun z =>
      (radialContractionPMF sigma z.b0 hs0 hs2).bind fun c0 =>
        (radialContractionPMF sigma z.b1 hs0 hs2).map fun c1 =>
          ⟨z.x, z.a, c0, c1⟩)
    (s := (BinaryFullObs.affine M
      (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩)) ⁻¹' E)
    (hE.preimage (by fun_prop))]
  unfold binaryFullChannel
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [show (binaryIndependentFullPMF P0).toMeasure {z} =
      binaryIndependentFullPMF P0 z by
    exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton z)]
  rw [PMF.toMeasure_bind_apply
    (p := radialContractionPMF sigma z.b0 hs0 hs2)
    (f := fun c0 =>
      (radialContractionPMF sigma z.b1 hs0 hs2).map fun c1 =>
        ⟨z.x, z.a, c0, c1⟩)
    (s := (BinaryFullObs.affine M
      (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩)) ⁻¹' E)
    (hE.preimage (by fun_prop)), tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c0 _hc0
  rw [PMF.toMeasure_map_apply
    (f := fun c1 : Bool => (⟨z.x, z.a, c0, c1⟩ : BinaryFullObs m))
    (p := radialContractionPMF sigma z.b1 hs0 hs2)
    (s := (BinaryFullObs.affine M
      (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩)) ⁻¹' E)
    (measurable_of_finite _) (hE.preimage (by fun_prop))]
  rw [PMF.toMeasure_apply (p := radialContractionPMF sigma z.b1 hs0 hs2)
    ((hE.preimage (by fun_prop)).preimage (measurable_of_finite _)), tsum_fintype]
  by_cases h1 : BinaryFullObs.affine M
      (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩)
      (⟨z.x, z.a, c0, true⟩ : BinaryFullObs m) ∈ E <;>
    by_cases h0 : BinaryFullObs.affine M
      (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩)
      (⟨z.x, z.a, c0, false⟩ : BinaryFullObs m) ∈ E <;>
    simp [BinaryFullObs.affine] at h1 h0 <;>
    simp [Measure.dirac_apply' _ hE, radialContractionPMF,
      PMF.ofFintype_apply, BinaryFullObs.affine, h1, h0, mul_add, mul_assoc]

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
