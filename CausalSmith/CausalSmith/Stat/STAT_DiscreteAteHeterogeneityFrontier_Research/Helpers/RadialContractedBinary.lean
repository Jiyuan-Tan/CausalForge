import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialChannelKernel

/-!
# Contracted binary source law for the radial converse

This file constructs the binary observation law obtained by passing the source
response through the paper's hypothesis-independent Bernoulli contraction.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

private abbrev BinLaw := CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw
private abbrev BinObs := CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

-- @node: radialContractionPMF
/-- Conditional law of the contracted response bit given the source bit. -/
noncomputable def radialContractionPMF (sigma : ℝ) (b : Bool)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) : PMF Bool :=
  PMF.ofFintype
    (fun b' => ENNReal.ofReal
      (if b' then bernoulliContractionSuccess sigma b
        else 1 - bernoulliContractionSuccess sigma b)) (by
      rw [Fintype.sum_bool]
      simp only [if_true]
      rw [← ENNReal.ofReal_add]
      · norm_num
      · exact (bernoulliContractionSuccess_mem_unitInterval hs0 hs2 b).1
      · exact sub_nonneg.mpr
          (bernoulliContractionSuccess_mem_unitInterval hs0 hs2 b).2)

-- @node: radialContractionPMF_true_toReal
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [the success atom of the contraction PMF has the declared channel mass](goal). -/
lemma radialContractionPMF_true_toReal {sigma : ℝ} (b : Bool)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    ((radialContractionPMF sigma b hs0 hs2) true).toReal =
      bernoulliContractionSuccess sigma b := by
  rw [radialContractionPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (bernoulliContractionSuccess_mem_unitInterval hs0 hs2 b).1

-- @node: radialContractionPMF_false_toReal
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [the failure atom of the contraction PMF has the complementary mass](goal). -/
lemma radialContractionPMF_false_toReal {sigma : ℝ} (b : Bool)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    ((radialContractionPMF sigma b hs0 hs2) false).toReal =
      1 - bernoulliContractionSuccess sigma b := by
  rw [radialContractionPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr
    (bernoulliContractionSuccess_mem_unitInterval hs0 hs2 b).2)

-- @node: radialContractedBinaryLaw
/-- The source observation law after retaining `(X,A)` and independently
drawing the contracted response bit conditional on the source response. -/
noncomputable def radialContractedBinaryLaw {d : ℕ} (P : BinLaw d)
    (sigma : ℝ) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) : BinLaw d where
  pmf := P.pmf.bind fun z =>
    (radialContractionPMF sigma z.2.2 hs0 hs2).map
      (fun b' => (⟨z.1, z.2.1, b'⟩ : BinObs d))

-- @node: radialContractedBinaryLaw_cellTreatment_margin
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [the contraction leaves the joint `(X,A)` margin exactly unchanged](goal). -/
lemma radialContractedBinaryLaw_cellTreatment_margin {d : ℕ} (P : BinLaw d)
    (sigma : ℝ) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    (radialContractedBinaryLaw P sigma hs0 hs2).pmf.map
        (fun z => (z.1, z.2.1)) =
      P.pmf.map (fun z => (z.1, z.2.1)) := by
  rw [radialContractedBinaryLaw, PMF.map_bind]
  simp_rw [PMF.map_comp]
  have hmap (z : BinObs d) :
      PMF.map ((fun w : BinObs d => (w.1, w.2.1)) ∘
          fun b' => (⟨z.1, z.2.1, b'⟩ : BinObs d))
          (radialContractionPMF sigma z.2.2 hs0 hs2) =
        PMF.pure (z.1, z.2.1) := by
    rw [← PMF.map_const]
    congr 1
  simp_rw [hmap]
  change P.pmf.bind (PMF.pure ∘ fun z : BinObs d => (z.1, z.2.1)) = _
  exact PMF.bind_pure_comp _ _

-- @node: radialContractedBinaryLaw_jointMass
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [each output atom is the source-bit mixture prescribed by the common Bernoulli
  contraction channel](goal). -/
lemma radialContractedBinaryLaw_jointMass {d : ℕ} (P : BinLaw d) (sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (k : Fin d) (a b' : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass
        (radialContractedBinaryLaw P sigma hs0 hs2) k a b' =
      ∑ b : Bool,
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a b *
          (if b' then bernoulliContractionSuccess sigma b
            else 1 - bernoulliContractionSuccess sigma b) := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass
  rw [radialContractedBinaryLaw, PMF.bind_apply]
  rw [tsum_fintype]
  simp_rw [PMF.map_apply, tsum_fintype]
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
  · cases a <;> cases b' <;>
      simp [Fintype.sum_prod_type, Fintype.sum_bool] <;>
      rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_mul] <;>
      simp [Fintype.sum_prod_type, radialContractionPMF_true_toReal,
        radialContractionPMF_false_toReal, PMF.apply_ne_top]
    all_goals apply ENNReal.mul_ne_top <;> apply PMF.apply_ne_top
  · intro j _ hj
    simp [hj, Ne.symm hj]
  · simp

-- @node: radialContractedBinaryLaw_armMass
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [summing over the contracted response shows that the channel preserves each
  cell-treatment mass exactly](goal). -/
lemma radialContractedBinaryLaw_armMass {d : ℕ} (P : BinLaw d) (sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (k : Fin d) (a : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass
        (radialContractedBinaryLaw P sigma hs0 hs2) k a =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass
  simp_rw [radialContractedBinaryLaw_jointMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_bool]
  unfold bernoulliContractionSuccess
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

-- @node: radialContractedBinaryLaw_cellMass
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [the Bernoulli contraction preserves every source cell mass](goal). -/
lemma radialContractedBinaryLaw_cellMass {d : ℕ} (P : BinLaw d) (sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (k : Fin d) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
        (radialContractedBinaryLaw P sigma hs0 hs2) k =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
  change (∑ a : Bool, CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass
      (radialContractedBinaryLaw P sigma hs0 hs2) k a) = _
  simp_rw [radialContractedBinaryLaw_armMass]
  rfl

-- @node: radialContractedBinaryLaw_overlap
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2) and [the source law satisfies the stated model condition](hyp:hP), [because both
  cell and cell-treatment masses are preserved, contraction preserves the strong-overlap
  certificate](goal). -/
lemma radialContractedBinaryLaw_overlap {d : ℕ} {epsilon sigma : ℝ} (P : BinLaw d)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2)
    (hP : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon
      (radialContractedBinaryLaw P sigma hs0 hs2) := by
  intro k hk
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity
  rw [radialContractedBinaryLaw_armMass, radialContractedBinaryLaw_cellMass]
  exact hP k (by simpa [radialContractedBinaryLaw_cellMass] using hk)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
