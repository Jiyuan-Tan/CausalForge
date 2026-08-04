import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.Certificate
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionOffDiagonal
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionNecessity
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

/-- A lower family that preserves the logging and Gibbs covariance pair. -/
def CovariancePreservingLowerFamily (P : BanditLaw E) (C D : ℝ)
    (family : Set (BanditLaw E)) : Prop :=
  family.Nonempty ∧ P ∈ family ∧ (∃ Q ∈ family, Q ≠ P) ∧
    family ⊆ exactShellSet E C D ∧
    ∀ Q ∈ family,
      loggingCovariance E Q = loggingCovariance E P ∧
      targetCovariance E Q = targetCovariance E P

/-- Programmatic search space for covariance-preserving lower families.
The note presents this as a handle: subsequent work may construct an element
of this set or prove that the set is empty.  It does not assert a chosen
feasibility, attainment, identification, or nonexistence certificate. -/
-- @node: def:feasible-frontier-handle
def feasibleFrontierHandle (P : BanditLaw E) (C D : ℝ) :
    Set (Set (BanditLaw E)) :=
  {family | CovariancePreservingLowerFamily E P C D family}

-- @node: thm:zero-risk-boundary
theorem zero_risk_boundary
    (hnonempty : ∃ P : BanditLaw E, ExactShell E P 1 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∀ P : BanditLaw E, ExactShell E P 1 1 →
      (∀ x a, 0 < contextMass P x → 0 < E.reference x a →
        gibbsPolicy E P x a = E.reference x a) ∧
      featureCoverage E P = 1 ∧
      regularizedWelfare E P (gibbsPolicy E P) -
        regularizedWelfare E P E.reference = 0) ∧
    sampleComplexityPositive E eps 1 1 heps = 1 := by
  have hfacts :
      ∀ P : BanditLaw E, ExactShell E P 1 1 →
        (∀ x a, 0 < contextMass P x → 0 < E.reference x a →
          gibbsPolicy E P x a = E.reference x a) ∧
        featureCoverage E P = 1 ∧
        regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P E.reference = 0 := by
    intro P hP
    have hpolicy :
        ∀ x a, 0 < contextMass P x → 0 < E.reference x a →
          gibbsPolicy E P x a = E.reference x a := by
      intro x a hx ha
      have hfinite :
          {c : ℝ | ∃ x a, 0 < contextMass P x ∧ 0 < E.reference x a ∧
            c = gibbsPolicy E P x a / E.reference x a}.Finite := by
        apply Set.Finite.subset (Set.finite_range
          (fun p : 𝒳 × 𝒜 => gibbsPolicy E P p.1 p.2 / E.reference p.1 p.2))
        rintro c ⟨y, b, _, _, rfl⟩
        exact Set.mem_range_self (y, b)
      have hrow_le : ∀ b, gibbsPolicy E P x b ≤ E.reference x b := by
        intro b
        by_cases hb : E.reference x b = 0
        · simp [gibbsPolicy, hb]
        · have hbpos : 0 < E.reference x b :=
            lt_of_le_of_ne (E.reference_isPolicy.1 x b) (Ne.symm hb)
          apply (div_le_one hbpos).mp
          calc
            gibbsPolicy E P x b / E.reference x b ≤ pointwiseCoverage E P := by
              rw [pointwiseCoverage]
              exact le_csSup hfinite.bddAbove ⟨x, b, hx, hbpos, rfl⟩
            _ = 1 := hP.pointwiseExactShell.2
      apply le_antisymm (hrow_le a)
      by_contra hnot
      have hlt : gibbsPolicy E P x a < E.reference x a := lt_of_not_ge hnot
      have hsum_lt :
          ∑ b, gibbsPolicy E P x b < ∑ b, E.reference x b :=
        Finset.sum_lt_sum (fun b _ => hrow_le b)
          ⟨a, Finset.mem_univ a, hlt⟩
      rw [(gibbsPolicy_isPolicy E P).2 x, E.reference_isPolicy.2 x] at hsum_lt
      exact lt_irrefl 1 hsum_lt
    refine ⟨hpolicy, hP.featureExactShell.2, ?_⟩
    rw [gibbs_regret_identity E P 1 1 hP E.reference
      E.reference_isPolicy (fun _ _ h => h)]
    have hsum : ∑ x, contextMass P x *
        policyKL E.reference (gibbsPolicy E P) x = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : 0 < contextMass P x
      · simp only [policyKL]
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : E.reference x a = 0
        · simp [ha]
        · have ha_pos : 0 < E.reference x a :=
            lt_of_le_of_ne (E.reference_isPolicy.1 x a) (Ne.symm ha)
          rw [hpolicy x a hx ha_pos]
          simp [ha]
      · have hx0 : contextMass P x = 0 :=
          le_antisymm (not_lt.mp hx) ENNReal.toReal_nonneg
        simp [hx0]
    rw [hsum, mul_zero]
  refine ⟨hfacts, ?_⟩
  let L : Learner 1 (𝒳 := 𝒳) (𝒜 := 𝒜) :=
    fun _ _ => E.reference
  have htotal :
      ∀ sample, learnerPolicyOnSample E L sample = E.reference := by
    intro sample
    funext x a
    simp [learnerPolicyOnSample, L]
  have hLfull : IsMeasurableFullLearner E L := by
    constructor
    · intro x a
      simpa only [htotal] using
        (measurable_const : Measurable (fun _ : LoggedSample 1 𝒳 𝒜 =>
          E.reference x a))
    · intro sample hs
      exact E.reference_isPolicy
  have hrisk_zero :
      ∀ P : BanditLaw E, ExactShell E P 1 1 →
        fullSimplexLearnerRisk E P 1 L = 0 := by
    intro P hP
    have hintegrand :
        ∀ sample, extendedRegret E P (learnerPolicyOnSample E L sample) = 0 := by
      intro sample
      rw [htotal sample]
      have hno : ¬ HasActiveSupportViolation E P E.reference := by
        rintro ⟨x, hx, hbad⟩
        apply hbad
        intro a ha
        exact ha
      simp [extendedRegret, hno, (hfacts P hP).2.2]
    simp only [fullSimplexLearnerRisk]
    simp_rw [hintegrand]
    exact MeasureTheory.lintegral_zero
  have hfull_zero :
      fullSimplexMinimaxRisk E 1 (exactShellSet E 1 1) = 0 := by
    apply le_antisymm
    · apply sInf_le
      refine ⟨L, hLfull, ?_⟩
      apply le_antisymm
      · exact bot_le
      · apply sSup_le
        rintro q ⟨P, hP, rfl⟩
        simpa [exactShellSet] using hrisk_zero P hP
    · exact bot_le
  have hmodel : (exactShellSet E 1 1).Nonempty := by
    rcases hnonempty with ⟨P, hP⟩
    exact ⟨P, hP⟩
  have hmin_zero : minimaxRisk E 1 (exactShellSet E 1 1) = 0 := by
    obtain ⟨hmin_nonneg, heq⟩ :=
      minimaxRisk_eq_fullSimplex E 1 (exactShellSet E 1 1) hmodel
    rw [hfull_zero] at heq
    have hof : ENNReal.ofReal (minimaxRisk E 1 (exactShellSet E 1 1)) = 0 := heq
    rw [ENNReal.ofReal_eq_zero] at hof
    linarith
  rw [sampleComplexityPositive, if_pos hmodel]
  apply le_antisymm
  · apply csInf_le
    · exact ⟨1, by
        rintro m ⟨n, hn, rfl, _⟩
        exact_mod_cast hn⟩
    · exact ⟨1, by omega, rfl, by rw [hmin_zero]; exact heps.le⟩
  · apply le_csInf
    · exact ⟨(1 : WithTop ℕ),
        ⟨1, by omega, rfl, by rw [hmin_zero]; exact heps.le⟩⟩
    · rintro m ⟨n, hn, rfl, _⟩
      exact_mod_cast hn

/-- Canonical cell-coordinate features. -/
def IsCanonicalTabular (coord : 𝒳 → 𝒜 → Fin d) : Prop :=
  Function.Bijective (fun p : 𝒳 × 𝒜 => coord p.1 p.2) ∧
  ∀ x a i, E.feature x a i = if i = coord x a then 1 else 0
  -- @realizes e_{(x,a)}(canonical coordinate vector indexed by S)

-- @node: canonicalLoggingQuadraticForm
lemma canonicalLoggingQuadraticForm
    (P : BanditLaw E) (coord : 𝒳 → 𝒜 → Fin d)
    (htab : IsCanonicalTabular E coord) (v : Fin d → ℝ) :
    quadraticForm (loggingCovariance E P) v =
      ∑ x, contextMass P x * ∑ a, E.reference x a * (v (coord x a)) ^ 2 := by
  simp only [quadraticForm, loggingCovariance]
  simp_rw [htab.2]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, x, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  simp
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  ring

-- @node: canonicalTargetQuadraticForm
lemma canonicalTargetQuadraticForm
    (P : BanditLaw E) (coord : 𝒳 → 𝒜 → Fin d)
    (htab : IsCanonicalTabular E coord) (v : Fin d → ℝ) :
    quadraticForm (targetCovariance E P) v =
      ∑ x, contextMass P x * ∑ a,
        gibbsPolicy E P x a * (v (coord x a)) ^ 2 := by
  simp only [quadraticForm, targetCovariance]
  simp_rw [htab.2]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, x, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  simp
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  ring

-- @node: canonicalQuadraticForm_eq_map
lemma canonicalQuadraticForm_eq_map
    (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadraticForm M v = M.toQuadraticMap' v := by
  simp only [quadraticForm, Matrix.toQuadraticMap',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  congr 1 with i
  congr 1 with j
  ring

-- @node: canonicalCellMass_pos
lemma canonicalCellMass_pos
    (P : BanditLaw E) (coord : 𝒳 → 𝒜 → Fin d)
    (htab : IsCanonicalTabular E coord)
    (hpos : Matrix.PosDef (loggingCovariance E P)) (x : 𝒳) (a : 𝒜) :
    0 < contextMass P x ∧ 0 < E.reference x a := by
  let v : Fin d → ℝ := fun i => if i = coord x a then 1 else 0
  have hvne : v ≠ 0 := by
    intro hv
    have := congrFun hv (coord x a)
    simp [v] at this
  have hquad := hpos.toQuadraticForm' v hvne
  rw [← canonicalQuadraticForm_eq_map,
    canonicalLoggingQuadraticForm E P coord htab v] at hquad
  have hcollapse :
      (∑ y, contextMass P y *
        ∑ b, E.reference y b * (v (coord y b)) ^ 2) =
          contextMass P x * E.reference x a := by
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single a]
      · simp [v]
      · intro b _ hba
        have hcoord : coord x b ≠ coord x a := by
          intro heq
          have hp : (x, b) = (x, a) := htab.1.1 heq
          exact hba (congrArg Prod.snd hp)
        simp [v, hcoord]
      · simp
    · intro y _ hyx
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro b _
      have hcoord : coord y b ≠ coord x a := by
        intro heq
        have hp : (y, b) = (x, a) := htab.1.1 heq
        exact hyx (congrArg Prod.fst hp)
      simp [v, hcoord]
    · simp
  rw [hcollapse] at hquad
  exact (mul_pos_iff.mp hquad).resolve_right
    (fun hneg => (not_lt_of_ge (E.reference_isPolicy.1 x a)) hneg.2)

-- @node: canonicalCoverage_eq_pointwise
lemma canonicalCoverage_eq_pointwise
    (P : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P C D)
    (coord : 𝒳 → 𝒜 → Fin d) (htab : IsCanonicalTabular E coord) :
    featureCoverage E P = pointwiseCoverage E P ∧ D = C := by
  have hcell :
      ∀ x a, 0 < contextMass P x ∧ 0 < E.reference x a :=
    fun x a => canonicalCellMass_pos E P coord htab
      hshell.nonsingularLoggingGeometry x a
  let R : Set ℝ :=
    {c | ∃ x a, 0 < contextMass P x ∧ 0 < E.reference x a ∧
      c = gibbsPolicy E P x a / E.reference x a}
  have hRfinite : R.Finite := by
    apply Set.Finite.subset (Set.finite_range
      (fun p : 𝒳 × 𝒜 => gibbsPolicy E P p.1 p.2 / E.reference p.1 p.2))
    rintro c ⟨x, a, _, _, rfl⟩
    exact Set.mem_range_self (x, a)
  have hRnonempty : R.Nonempty := by
    by_contra h
    have hRempty : R = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hcov0 : pointwiseCoverage E P = 0 := by
      rw [pointwiseCoverage]
      change sSup R = 0
      rw [hRempty]
      simp
    have hC0 : C = 0 := hshell.pointwiseExactShell.2.symm.trans hcov0
    linarith [hshell.pointwiseExactShell.1]
  have hattain : ∃ x a,
      pointwiseCoverage E P =
        gibbsPolicy E P x a / E.reference x a := by
    have hmem : sSup R ∈ R := hRnonempty.csSup_mem hRfinite
    rcases hmem with ⟨x, a, _, _, hx⟩
    exact ⟨x, a, by simpa [pointwiseCoverage, R] using hx⟩
  have hratio :
      ∀ x a, gibbsPolicy E P x a / E.reference x a ≤
        pointwiseCoverage E P := by
    intro x a
    rw [pointwiseCoverage]
    exact le_csSup hRfinite.bddAbove
      ⟨x, a, (hcell x a).1, (hcell x a).2, rfl⟩
  rcases hattain with ⟨x, a, hattain⟩
  let v : Fin d → ℝ := fun i => if i = coord x a then 1 else 0
  have hvne : v ≠ 0 := by
    intro hv
    have := congrFun hv (coord x a)
    simp [v] at this
  have hquad_le :
      ∀ w : Fin d → ℝ,
        quadraticForm (targetCovariance E P) w ≤
          pointwiseCoverage E P *
            quadraticForm (loggingCovariance E P) w := by
    intro w
    rw [canonicalTargetQuadraticForm E P coord htab,
      canonicalLoggingQuadraticForm E P coord htab]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    calc
      contextMass P y *
          ∑ b, gibbsPolicy E P y b * w (coord y b) ^ 2 ≤
        contextMass P y *
          (pointwiseCoverage E P *
            ∑ b, E.reference y b * w (coord y b) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro b _
          have hpolicy :
              gibbsPolicy E P y b ≤
                pointwiseCoverage E P * E.reference y b :=
            (div_le_iff₀ (hcell y b).2).mp (hratio y b)
          nlinarith [sq_nonneg (w (coord y b))]
      _ = pointwiseCoverage E P *
          (contextMass P y *
            ∑ b, E.reference y b * w (coord y b) ^ 2) := by ring
  have hall :
      ∀ q ∈ {q : ℝ | ∃ w : Fin d → ℝ, w ≠ 0 ∧
        q = quadraticForm (targetCovariance E P) w /
          quadraticForm (loggingCovariance E P) w},
        q ≤ pointwiseCoverage E P := by
    rintro q ⟨w, hw, rfl⟩
    have hden : 0 < quadraticForm (loggingCovariance E P) w := by
      rw [canonicalQuadraticForm_eq_map]
      exact hshell.nonsingularLoggingGeometry.toQuadraticForm' w hw
    exact (div_le_iff₀ hden).2 (hquad_le w)
  have hfeature_le :
      featureCoverage E P ≤ pointwiseCoverage E P := by
    unfold featureCoverage maxGeneralizedEigenvalue
    apply csSup_le
    · exact ⟨quadraticForm (targetCovariance E P) v /
          quadraticForm (loggingCovariance E P) v, v, hvne, rfl⟩
    · exact hall
  have hlog :
      quadraticForm (loggingCovariance E P) v =
        contextMass P x * E.reference x a := by
    rw [canonicalLoggingQuadraticForm E P coord htab]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single a]
      · simp [v]
      · intro b _ hba
        have hcoord : coord x b ≠ coord x a := by
          intro heq
          have hp : (x, b) = (x, a) := htab.1.1 heq
          exact hba (congrArg Prod.snd hp)
        simp [v, hcoord]
      · simp
    · intro y _ hyx
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro b _
      have hcoord : coord y b ≠ coord x a := by
        intro heq
        have hp : (y, b) = (x, a) := htab.1.1 heq
        exact hyx (congrArg Prod.fst hp)
      simp [v, hcoord]
    · simp
  have htarget :
      quadraticForm (targetCovariance E P) v =
        contextMass P x * gibbsPolicy E P x a := by
    rw [canonicalTargetQuadraticForm E P coord htab]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single a]
      · simp [v]
      · intro b _ hba
        have hcoord : coord x b ≠ coord x a := by
          intro heq
          have hp : (x, b) = (x, a) := htab.1.1 heq
          exact hba (congrArg Prod.snd hp)
        simp [v, hcoord]
      · simp
    · intro y _ hyx
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro b _
      have hcoord : coord y b ≠ coord x a := by
        intro heq
        have hp : (y, b) = (x, a) := htab.1.1 heq
        exact hyx (congrArg Prod.fst hp)
      simp [v, hcoord]
    · simp
  have hratio_quad :
      quadraticForm (targetCovariance E P) v /
          quadraticForm (loggingCovariance E P) v =
        gibbsPolicy E P x a / E.reference x a := by
    rw [hlog, htarget]
    field_simp [ne_of_gt (hcell x a).1, ne_of_gt (hcell x a).2]
  have hfeature_ge :
      pointwiseCoverage E P ≤ featureCoverage E P := by
    rw [hattain, ← hratio_quad]
    unfold featureCoverage maxGeneralizedEigenvalue
    apply le_csSup
    · exact ⟨pointwiseCoverage E P, hall⟩
    · exact ⟨v, hvne, rfl⟩
  have heq := le_antisymm hfeature_le hfeature_ge
  refine ⟨heq, ?_⟩
  rw [← hshell.featureExactShell.2, ← hshell.pointwiseExactShell.2]
  exact heq

-- @node: prop:canonical-tabular-reduction
theorem canonical_tabular_reduction
    (P : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P C D)
    (coord : 𝒳 → 𝒜 → Fin d) (htab : IsCanonicalTabular E coord) :
    (∀ i j, i ≠ j →
      (loggingCovariance E P) i j = 0 ∧ (targetCovariance E P) i j = 0) ∧
    featureCoverage E P = pointwiseCoverage E P ∧ D = C := by
  refine ⟨?_, canonicalCoverage_eq_pointwise E P C D hshell coord htab⟩
  intro i j hij
  constructor
  · simp only [loggingCovariance]
    apply Finset.sum_eq_zero
    intro x _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro a _
    rw [htab.2 x a i, htab.2 x a j]
    split_ifs with hi hj
    · exact (hij (hi.trans hj.symm)).elim
    · simp
    · simp
    · simp
  · simp only [targetCovariance]
    apply Finset.sum_eq_zero
    intro x _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro a _
    rw [htab.2 x a i, htab.2 x a j]
    split_ifs with hi hj
    · exact (hij (hi.trans hj.symm)).elim
    · simp
    · simp
    · simp

/-- Contextwise covariance block for a candidate coefficient. -/
-- @node: thm:feasible-index-region
theorem feasible_index_region :
    (∀ (P : BanditLaw E) (C D : ℝ), ExactShell E P C D →
      1 ≤ D ∧ D ≤ C ∧ C < Real.exp E.eta ∧
        ((C = 1 ∧ D = 1) ∨ (1 < D ∧ D ≤ C))) ∧
    (∀ C D : ℝ, 1 < D → D ≤ C → C < Real.exp E.eta →
      ∃ (mX mA : ℕ)
        (E' : CommonExperiment d (Fin mX) (Fin mA))
        (P : BanditLaw E'), E'.eta = E.eta ∧ ExactShell E' P C D) ∧
    (∃ (mX mA : ℕ)
      (E' : CommonExperiment d (Fin mX) (Fin mA))
      (P : BanditLaw E'), E'.eta = E.eta ∧ ExactShell E' P 1 1) ∧
    (∀ (P : BanditLaw E) (C D : ℝ), ExactShell E P C D →
      ∀ coord : 𝒳 → 𝒜 → Fin d, IsCanonicalTabular E coord → D = C) ∧
    (∀ C D : ℝ, 1 < D → D < C → C < Real.exp E.eta →
      ∃ (mX mA : ℕ)
        (E' : CommonExperiment d (Fin mX) (Fin mA))
        (P : BanditLaw E'),
          E'.eta = E.eta ∧ ExactShell E' P C D ∧
          (∃ xC xA : Fin mX, ∃ aC aA : Fin mA,
            xC ≠ xA ∧
            (∀ i, E'.feature xC aC i = E'.feature xA aA i) ∧
            ∃ i, E'.feature xC aC i ≠ 0) ∧
          ¬ ∃ coord : Fin mX → Fin mA → Fin d, IsCanonicalTabular E' coord) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P C D hP
    exact exactShell_index_constraints E P C D hP
  · intro C D hD hDC hCexp
    by_cases hEq : D = C
    · subst C
      let E' := diagonalIndexExperiment d E.dim_ge_four E.eta D
        E.eta_pos hD.le hCexp
      obtain ⟨P, hP⟩ := diagonalIndex_exactShell d E.dim_ge_four E.eta D
        E.eta_pos hD.le hCexp
      exact ⟨d, 2, E', P, rfl, hP⟩
    · have hDC' : D < C := lt_of_le_of_ne hDC hEq
      let E' := offDiagonalExperiment d E.dim_ge_four E.eta C D
        E.eta_pos hD hDC' hCexp
      obtain ⟨P, hP⟩ := offDiagonal_exactShell d E.dim_ge_four E.eta C D
        E.eta_pos hD hDC' hCexp
      exact ⟨d + 1, 2, E', P, rfl, hP⟩
  · have hOneExp : (1 : ℝ) < Real.exp E.eta :=
      (Real.one_lt_exp_iff).2 E.eta_pos
    let E' := diagonalIndexExperiment d E.dim_ge_four E.eta 1
      E.eta_pos le_rfl hOneExp
    obtain ⟨P, hP⟩ := diagonalIndex_exactShell d E.dim_ge_four E.eta 1
      E.eta_pos le_rfl hOneExp
    exact ⟨d, 2, E', P, rfl, hP⟩
  · intro P C D hP coord htab
    exact (canonical_tabular_reduction E P C D hP coord htab).2.2
  · intro C D hD hDC hCexp
    let E' := offDiagonalExperiment d E.dim_ge_four E.eta C D
      E.eta_pos hD hDC hCexp
    obtain ⟨P, hP⟩ := offDiagonal_exactShell d E.dim_ge_four E.eta C D
      E.eta_pos hD hDC hCexp
    have hshared := offDiagonal_shared_feature d E.dim_ge_four E.eta C D
      E.eta_pos hD hDC hCexp
    refine ⟨d + 1, 2, E', P, rfl, hP, hshared, ?_⟩
    rintro ⟨coord, htab⟩
    rcases hshared with ⟨xC, xA, aC, aA, hx, hfeat, i, hi⟩
    have hiA : E'.feature xA aA i ≠ 0 := by
      rw [← hfeat i]
      exact hi
    have hcoordC : i = coord xC aC := by
      by_contra hne
      rw [htab.2 xC aC i, if_neg hne] at hi
      exact hi rfl
    have hcoordA : i = coord xA aA := by
      by_contra hne
      rw [htab.2 xA aA i, if_neg hne] at hiA
      exact hiA rfl
    have hp : (xC, aC) = (xA, aA) :=
      htab.1.1 (hcoordC.symm.trans hcoordA)
    exact hx (congrArg Prod.fst hp)

end CausalSmith.Stat.ReverseKLTwoCoverage
