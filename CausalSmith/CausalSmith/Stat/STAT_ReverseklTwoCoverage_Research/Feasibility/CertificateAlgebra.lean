import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.CertificateDefinitions
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentityCore
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.CertificateRayleigh
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.CertificateLaw

set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

lemma certificate_contextMass_sum_one (P : BanditLaw E) :
    ∑ x, contextMass P x = 1 := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  have hcontext : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => z.context) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact (comap_measurable _).fst
  have h := sum_measureReal_preimage_singleton
    (μ := P.dataMeasure) (f := fun z : BanditObservation 𝒳 𝒜 => z.context)
    (Finset.univ : Finset 𝒳)
    (fun x _ => hcontext (measurableSet_singleton x))
  simpa [contextMass, measureReal_univ_eq_one] using h

lemma candidateNormalizer_eq_gibbsNormalizer
    (P : BanditLaw E) (x : 𝒳) :
    candidateNormalizer E P.theta x = gibbsNormalizer E P x := rfl

lemma gibbsPolicy_eq_candidate
    (P : BanditLaw E) (x : 𝒳) (a : 𝒜) :
    gibbsPolicy E P x a =
      E.reference x a * candidateWeight E P.theta x a := by
  rw [gibbsPolicy, candidateWeight,
    candidateNormalizer_eq_gibbsNormalizer E P x]
  simp only [linearReward]
  ring

lemma loggingBlock_isHermitian (x : 𝒳) :
    (loggingBlock E x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, loggingBlock]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma targetBlock_isHermitian (theta : Fin d → ℝ) (x : 𝒳) :
    (targetBlock E theta x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, targetBlock]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma sum_loggingBlock_isHermitian
    (I : Finset 𝒳) (rho : I → ℝ) :
    (∑ x : I, rho x • loggingBlock E x.1).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  have h := (loggingBlock_isHermitian E x.1).apply i j
  simpa using congrArg (fun z : ℝ => rho x * z) h

lemma sum_targetBlock_isHermitian
    (I : Finset 𝒳) (rho : I → ℝ) (theta : Fin d → ℝ) :
    (∑ x : I, rho x • targetBlock E theta x.1).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  have h := (targetBlock_isHermitian E theta x.1).apply i j
  simpa using congrArg (fun z : ℝ => rho x * z) h

lemma active_context_sum
    (P : BanditLaw E) :
    ∑ x : (Finset.univ.filter fun x => 0 < contextMass P x),
      contextMass P x.1 = 1 := by
  let I : Finset 𝒳 := Finset.univ.filter fun x => 0 < contextMass P x
  rw [← certificate_contextMass_sum_one E P]
  classical
  calc
    (∑ x : I, contextMass P x.1) =
        ∑ x ∈ I, contextMass P x := by
          exact (Finset.sum_subtype I (fun _ => Iff.rfl)
            (fun x => contextMass P x)).symm
    _ = ∑ x : 𝒳, contextMass P x := by
          apply Finset.sum_subset (Finset.subset_univ I)
          intro x _ hx
          have hnot : ¬ 0 < contextMass P x := by
            simpa [I] using hx
          exact le_antisymm (not_lt.mp hnot) ENNReal.toReal_nonneg

lemma active_logging_eq
    (P : BanditLaw E) :
    (∑ x : (Finset.univ.filter fun x => 0 < contextMass P x),
      contextMass P x.1 • loggingBlock E x.1) =
      loggingCovariance E P := by
  let I : Finset 𝒳 := Finset.univ.filter fun x => 0 < contextMass P x
  ext i j
  simp only [loggingCovariance, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, loggingBlock]
  classical
  calc
    (∑ x : I, contextMass P x.1 *
        ∑ a, E.reference x.1 a *
          (E.feature x.1 a i * E.feature x.1 a j)) =
        ∑ x ∈ I, contextMass P x *
          ∑ a, E.reference x a *
            (E.feature x a i * E.feature x a j) := by
              exact (Finset.sum_subtype I (fun _ => Iff.rfl)
                (fun x => contextMass P x *
                  ∑ a, E.reference x a *
                    (E.feature x a i * E.feature x a j))).symm
    _ = ∑ x : 𝒳, contextMass P x *
          ∑ a, E.reference x a *
            (E.feature x a i * E.feature x a j) := by
              apply Finset.sum_subset (Finset.subset_univ I)
              intro x _ hx
              have hzero : contextMass P x = 0 := by
                have : ¬ 0 < contextMass P x := by simpa [I] using hx
                exact le_antisymm (not_lt.mp this) ENNReal.toReal_nonneg
              simp [hzero]

lemma active_target_eq
    (P : BanditLaw E) :
    (∑ x : (Finset.univ.filter fun x => 0 < contextMass P x),
      contextMass P x.1 • targetBlock E P.theta x.1) =
      targetCovariance E P := by
  let I : Finset 𝒳 := Finset.univ.filter fun x => 0 < contextMass P x
  ext i j
  simp only [targetCovariance, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, targetBlock]
  simp_rw [← gibbsPolicy_eq_candidate E P]
  classical
  calc
    (∑ x : I, contextMass P x.1 *
        ∑ a, gibbsPolicy E P x.1 a *
          (E.feature x.1 a i * E.feature x.1 a j)) =
        ∑ x ∈ I, contextMass P x *
          ∑ a, gibbsPolicy E P x a *
            (E.feature x a i * E.feature x a j) := by
              exact (Finset.sum_subtype I (fun _ => Iff.rfl)
                (fun x => contextMass P x *
                  ∑ a, gibbsPolicy E P x a *
                    (E.feature x a i * E.feature x a j))).symm
    _ = ∑ x : 𝒳, contextMass P x *
          ∑ a, gibbsPolicy E P x a *
            (E.feature x a i * E.feature x a j) := by
              apply Finset.sum_subset (Finset.subset_univ I)
              intro x _ hx
              have hzero : contextMass P x = 0 := by
                have : ¬ 0 < contextMass P x := by simpa [I] using hx
                exact le_antisymm (not_lt.mp this) ENNReal.toReal_nonneg
              simp [hzero]

lemma candidateNormalizer_pos (theta : Fin d → ℝ) (x : 𝒳) :
    0 < candidateNormalizer E theta x := by
  unfold candidateNormalizer
  apply Finset.sum_pos'
  · intro a _
    exact mul_nonneg (E.reference_isPolicy.1 x a) (Real.exp_pos _).le
  · by_contra h
    push_neg at h
    have hz : ∀ a, E.reference x a = 0 := by
      intro a
      have hn := h a (Finset.mem_univ a)
      have hp : 0 ≤ E.reference x a *
          Real.exp (E.eta * ∑ i, E.feature x a i * theta i) :=
        mul_nonneg (E.reference_isPolicy.1 x a) (Real.exp_pos _).le
      exact (mul_eq_zero.mp (le_antisymm hn hp)).resolve_right
        (ne_of_gt (Real.exp_pos _))
    have := E.reference_isPolicy.2 x
    simp_rw [hz] at this
    norm_num at this

lemma candidate_ratio_eq
    (P : BanditLaw E) (x : 𝒳) (a : 𝒜)
    (href : 0 < E.reference x a) :
    gibbsPolicy E P x a / E.reference x a =
      Real.exp (E.eta * ∑ i, E.feature x a i * P.theta i) /
        candidateNormalizer E P.theta x := by
  rw [gibbsPolicy_eq_candidate E P, candidateWeight]
  field_simp [ne_of_gt href]

lemma weightedFeatureQuadratic
    {ι : Type*} [Fintype ι]
    (feature : ι → Fin d → ℝ) (weight : ι → ℝ)
    (v : Fin d → ℝ) :
    quadraticForm
        (fun i j => ∑ s : ι, weight s * (feature s i * feature s j)) v =
      ∑ s : ι, weight s * (∑ i, feature s i * v i) ^ 2 := by
  symm
  simp only [quadraticForm, pow_two]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  ring_nf
  calc
    _ = ∑ s, ∑ i, ∑ j,
        weight s * feature s i * v i * feature s j * v j := by
          congr 1 with s
    _ = ∑ i, ∑ s, ∑ j,
        weight s * feature s i * v i * feature s j * v j := by
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ s,
        weight s * feature s i * v i * feature s j * v j := by
          congr 1 with i
          rw [Finset.sum_comm]
    _ = _ := by
      congr 1 with i
      congr 1 with j
      rw [Finset.sum_mul]
      congr 1 with s
      ring

lemma candidate_target_posDef
    (I : Finset 𝒳) (rho : I → ℝ) (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 < rho x)
    (hB : Matrix.PosDef (∑ x : I, rho x • loggingBlock E x.1)) :
    Matrix.PosDef (∑ x : I, rho x • targetBlock E theta x.1) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (sum_targetBlock_isHermitian E I rho theta)
  intro v hv
  have hBq : 0 < quadraticForm
      (∑ x : I, rho x • loggingBlock E x.1) v := by
    rw [quadraticForm_eq_toQuadraticMap]
    exact hB.toQuadraticForm' v hv
  have hBlog :
      quadraticForm (∑ x : I, rho x • loggingBlock E x.1) v =
        ∑ p : I × 𝒜,
          (rho p.1 * E.reference p.1.1 p.2) *
            (∑ i, E.feature p.1.1 p.2 i * v i) ^ 2 := by
    rw [show (∑ x : I, rho x • loggingBlock E x.1) =
        fun i j => ∑ p : I × 𝒜,
          (rho p.1 * E.reference p.1.1 p.2) *
            (E.feature p.1.1 p.2 i * E.feature p.1.1 p.2 j) by
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        loggingBlock, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring]
    exact weightedFeatureQuadratic
      (fun p : I × 𝒜 => E.feature p.1.1 p.2)
      (fun p => rho p.1 * E.reference p.1.1 p.2) v
  rw [hBlog] at hBq
  have hterm_nonneg : ∀ p ∈ (Finset.univ : Finset (I × 𝒜)),
      0 ≤ (rho p.1 * E.reference p.1.1 p.2) *
        (∑ i, E.feature p.1.1 p.2 i * v i) ^ 2 := by
    intro p _
    exact mul_nonneg
      (mul_nonneg (hrho p.1).le
        (E.reference_isPolicy.1 p.1.1 p.2))
      (sq_nonneg _)
  obtain ⟨p, _, hppos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hterm_nonneg).mp hBq
  let x : I := p.1
  let a : 𝒜 := p.2
  have href : 0 < E.reference x.1 a := by
    by_contra h
    have hz : E.reference x.1 a = 0 :=
      le_antisymm (not_lt.mp h) (E.reference_isPolicy.1 x.1 a)
    simp [x, a, hz] at hppos
  have hscore : (∑ i, E.feature x.1 a i * v i) ^ 2 > 0 := by
    change 0 < (rho x * E.reference x.1 a) *
      (∑ i, E.feature x.1 a i * v i) ^ 2 at hppos
    rcases mul_pos_iff.mp hppos with h | h
    · exact h.2
    · exact ((not_lt_of_ge
        (mul_nonneg (hrho x).le href.le)) h.1).elim
  have hweight : 0 < candidateWeight E theta x.1 a :=
    div_pos (Real.exp_pos _) (candidateNormalizer_pos E theta x.1)
  rw [← quadraticForm_eq_dotProduct_mulVec]
  rw [show quadraticForm (∑ x : I, rho x • targetBlock E theta x.1) v =
      ∑ p : I × 𝒜,
        (rho p.1 * E.reference p.1.1 p.2 *
          candidateWeight E theta p.1.1 p.2) *
          (∑ i, E.feature p.1.1 p.2 i * v i) ^ 2 by
    rw [show (∑ x : I, rho x • targetBlock E theta x.1) =
        fun i j => ∑ p : I × 𝒜,
          (rho p.1 * E.reference p.1.1 p.2 *
            candidateWeight E theta p.1.1 p.2) *
            (E.feature p.1.1 p.2 i * E.feature p.1.1 p.2 j) by
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        targetBlock, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring]
    exact weightedFeatureQuadratic
      (fun p : I × 𝒜 => E.feature p.1.1 p.2)
      (fun p => rho p.1 * E.reference p.1.1 p.2 *
        candidateWeight E theta p.1.1 p.2) v]
  apply Finset.sum_pos'
  · intro p _
    have hw : 0 ≤ candidateWeight E theta p.1.1 p.2 :=
      div_nonneg (Real.exp_pos _).le
        (candidateNormalizer_pos E theta p.1.1).le
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (hrho p.1).le
          (E.reference_isPolicy.1 p.1.1 p.2))
        hw)
      (sq_nonneg _)
  · refine ⟨p, Finset.mem_univ p, ?_⟩
    change 0 < (rho x * E.reference x.1 a *
      candidateWeight E theta x.1 a) *
        (∑ i, E.feature x.1 a i * v i) ^ 2
    exact mul_pos
      (mul_pos (mul_pos (hrho x) href) hweight) hscore

lemma fixed_experiment_shell_certificate_equiv (C D : ℝ) :
    (∃ P : BanditLaw E, ExactShell E P C D) ↔
      BoundedFeatures E ∧ FixedExperimentFeasibilitySystem E C D := by
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨hP.boundedFeatures, ?_⟩
    let I : Finset 𝒳 := Finset.univ.filter fun x => 0 < contextMass P x
    have hIsum : ∑ x : I, contextMass P x.1 = 1 :=
      active_context_sum E P
    have hI : I.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hIsum
      simp at hIsum
    let R : Set ℝ :=
      {c | ∃ x a, 0 < contextMass P x ∧ 0 < E.reference x a ∧
        c = gibbsPolicy E P x a / E.reference x a}
    have hRfinite : R.Finite := by
      apply Set.Finite.subset (Set.finite_range
        (fun p : 𝒳 × 𝒜 => gibbsPolicy E P p.1 p.2 / E.reference p.1 p.2))
      rintro c ⟨x, a, _, _, rfl⟩
      exact Set.mem_range_self (x, a)
    have hRnonempty : R.Nonempty := by
      by_contra hn
      have : pointwiseCoverage E P = 0 := by
        unfold pointwiseCoverage
        change sSup R = 0
        rw [Set.not_nonempty_iff_eq_empty.mp hn]
        simp
      have hCzero : C = 0 := hP.pointwiseExactShell.2.symm.trans this
      linarith [hP.pointwiseExactShell.1]
    have hmem : sSup R ∈ R := hRnonempty.csSup_mem hRfinite
    rcases hmem with ⟨x0, a0, hx0, ha0, hattain⟩
    have hx0I : x0 ∈ I := by simp [I, hx0]
    let sx0 : I := ⟨x0, hx0I⟩
    have hB :
        (∑ x : I, contextMass P x.1 • loggingBlock E x.1) =
          loggingCovariance E P := by
      simpa [I] using active_logging_eq E P
    have hG :
        (∑ x : I, contextMass P x.1 • targetBlock E P.theta x.1) =
          targetCovariance E P := by
      simpa [I] using active_target_eq E P
    have hBpos :
        Matrix.PosDef
          (∑ x : I, contextMass P x.1 • loggingBlock E x.1) := by
      rw [hB]
      exact hP.nonsingularLoggingGeometry
    have hmax :
        maxGeneralizedEigenvalue
            (∑ x : I, contextMass P x.1 • loggingBlock E x.1)
            (∑ x : I, contextMass P x.1 • targetBlock E P.theta x.1) = D := by
      rw [hB, hG]
      exact hP.featureExactShell.2
    obtain ⟨hPSD, u, hker, hunorm⟩ :=
      (generalizedRayleigh_certificate_iff
        (lt_of_lt_of_le (by omega : 0 < 4) E.dim_ge_four) hBpos
        (sum_targetBlock_isHermitian E I
          (fun x => contextMass P x.1) P.theta)).mp hmax
    refine ⟨I, hI, sx0, a0, P.theta,
      fun x => contextMass P x.1, u, ha0,
      hP.linearRealizability.1, ?_, hIsum, hBpos, ?_, ?_,
      hPSD, hker, hunorm⟩
    · intro x
      have hx := x.2
      change x.1 ∈ Finset.univ.filter
        (fun y => 0 < contextMass P y) at hx
      exact (Finset.mem_filter.mp hx).2
    · intro x a ha
      have hle :
          gibbsPolicy E P x.1 a / E.reference x.1 a ≤ C := by
        rw [← hP.pointwiseExactShell.2, pointwiseCoverage]
        have hx := x.2
        change x.1 ∈ Finset.univ.filter
          (fun y => 0 < contextMass P y) at hx
        have hxpos := (Finset.mem_filter.mp hx).2
        exact le_csSup hRfinite.bddAbove
          ⟨x.1, a, hxpos, ha, rfl⟩
      rw [candidate_ratio_eq E P x.1 a ha] at hle
      exact (div_le_iff₀ (candidateNormalizer_pos E P.theta x.1)).mp hle
    · have hattainC :
          C = gibbsPolicy E P x0 a0 / E.reference x0 a0 := by
        rw [← hP.pointwiseExactShell.2]
        exact hattain
      rw [candidate_ratio_eq E P x0 a0 ha0] at hattainC
      exact (div_eq_iff
        (ne_of_gt (candidateNormalizer_pos E P.theta x0))).mp hattainC.symm
  · rintro ⟨hbounded, I, hI, x0, a0, theta, rho, u,
      ha0, hbound, hrho, hsum, hBpos, hcovle, hcoveq,
      hPSD, hker, hunorm⟩
    let P := certificateLaw E I theta rho (fun x => (hrho x).le)
      hsum hbound
    have hcontext (x : 𝒳) :
        contextMass P x = certificateRho I rho x :=
      certificateLaw_contextMass E I theta rho (fun x => (hrho x).le)
        hsum hbound x
    have hB :
        loggingCovariance E P =
          ∑ x : I, rho x • loggingBlock E x.1 := by
      ext i j
      simp only [loggingCovariance, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, loggingBlock, hcontext]
      calc
        (∑ x : 𝒳, certificateRho I rho x *
            ∑ a, E.reference x a *
              (E.feature x a i * E.feature x a j)) =
            ∑ x ∈ I, certificateRho I rho x *
              ∑ a, E.reference x a *
                (E.feature x a i * E.feature x a j) := by
                  symm
                  apply Finset.sum_subset (Finset.subset_univ I)
                  intro x _ hx
                  simp [certificateRho, hx]
        _ = ∑ x : I, rho x *
              ∑ a, E.reference x.1 a *
                (E.feature x.1 a i * E.feature x.1 a j) := by
                  rw [← Finset.sum_attach]
                  simp [certificateRho]
    have hG :
        targetCovariance E P =
          ∑ x : I, rho x • targetBlock E theta x.1 := by
      ext i j
      simp only [targetCovariance, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, targetBlock, hcontext]
      change (∑ x : 𝒳, certificateRho I rho x *
          ∑ a, gibbsPolicy E P x a *
            (E.feature x a i * E.feature x a j)) =
        ∑ x : I, rho x *
          ∑ a, E.reference x.1 a * candidateWeight E theta x.1 a *
            (E.feature x.1 a i * E.feature x.1 a j)
      simp_rw [gibbsPolicy_eq_candidate E P]
      change (∑ x : 𝒳, certificateRho I rho x *
          ∑ a, E.reference x a * candidateWeight E theta x a *
            (E.feature x a i * E.feature x a j)) =
        ∑ x : I, rho x *
          ∑ a, E.reference x.1 a * candidateWeight E theta x.1 a *
            (E.feature x.1 a i * E.feature x.1 a j)
      calc
        (∑ x : 𝒳, certificateRho I rho x *
            ∑ a, E.reference x a * candidateWeight E theta x a *
              (E.feature x a i * E.feature x a j)) =
            ∑ x ∈ I, certificateRho I rho x *
              ∑ a, E.reference x a * candidateWeight E theta x a *
                (E.feature x a i * E.feature x a j) := by
                  symm
                  apply Finset.sum_subset (Finset.subset_univ I)
                  intro x _ hx
                  simp [certificateRho, hx]
        _ = ∑ x : I, rho x *
              ∑ a, E.reference x.1 a * candidateWeight E theta x.1 a *
                (E.feature x.1 a i * E.feature x.1 a j) := by
                  rw [← Finset.sum_attach]
                  simp [certificateRho]
    have hGpos :
        Matrix.PosDef (∑ x : I, rho x • targetBlock E theta x.1) :=
      candidate_target_posDef E I rho theta hrho hBpos
    have hmax :
        maxGeneralizedEigenvalue
            (∑ x : I, rho x • loggingBlock E x.1)
            (∑ x : I, rho x • targetBlock E theta x.1) = D :=
      (generalizedRayleigh_certificate_iff
        (lt_of_lt_of_le (by omega : 0 < 4) E.dim_ge_four) hBpos
        (sum_targetBlock_isHermitian E I rho theta)).mpr
          ⟨hPSD, u, hker, hunorm⟩
    have hDpos : 0 < D := by
      rw [← hmax]
      unfold maxGeneralizedEigenvalue
      have hune : u ≠ 0 := by
        intro hu
        simp [hu] at hunorm
      have hBq := hBpos.toQuadraticForm' u hune
      have hGq := hGpos.toQuadraticForm' u hune
      rw [← quadraticForm_eq_toQuadraticMap] at hBq hGq
      exact lt_of_lt_of_le (div_pos hGq hBq)
        (le_csSup (generalizedRayleigh_bddAbove hBpos)
          ⟨u, hune, rfl⟩)
    refine ⟨P, {
      finiteContexts := ⟨inferInstance⟩
      finiteActions := ⟨inferInstance⟩
      boundedFeatures := hbounded
      linearRealizability := ?_
      referenceLogging := ?_
      nonsingularLoggingGeometry := ?_
      pointwiseExactShell := ?_
      featureExactShell := ?_ }⟩
    · constructor
      · simpa [P] using hbound
      · intro x a hcell
        exact certificateLaw_rewardMean E I theta rho
          (fun x => (hrho x).le) hsum hbound x a hcell
    · intro x a
      exact certificateLaw_cellMass E I theta rho
        (fun x => (hrho x).le) hsum hbound x a
    · unfold NonsingularLoggingGeometry
      rw [hB]
      exact hBpos
    · let R : Set ℝ :=
        {c | ∃ x a, 0 < contextMass P x ∧ 0 < E.reference x a ∧
          c = gibbsPolicy E P x a / E.reference x a}
      have hRfinite : R.Finite := by
        apply Set.Finite.subset (Set.finite_range
          (fun p : 𝒳 × 𝒜 => gibbsPolicy E P p.1 p.2 / E.reference p.1 p.2))
        rintro c ⟨x, a, _, _, rfl⟩
        exact Set.mem_range_self (x, a)
      have hupper : ∀ c ∈ R, c ≤ C := by
        rintro c ⟨x, a, hx, ha, rfl⟩
        have hxI : x ∈ I := by
          by_contra hn
          rw [hcontext x] at hx
          simp [certificateRho, hn] at hx
        rw [candidate_ratio_eq E P x a ha]
        apply (div_le_iff₀ (candidateNormalizer_pos E theta x)).2
        exact hcovle ⟨x, hxI⟩ a ha
      have hx0mass : 0 < contextMass P x0.1 := by
        rw [hcontext]
        simp [certificateRho, x0.2, hrho x0]
      have hCmem : C ∈ R := by
        refine ⟨x0.1, a0, hx0mass, ha0, ?_⟩
        rw [candidate_ratio_eq E P x0.1 a0 ha0]
        symm
        simpa [P] using (div_eq_iff
          (ne_of_gt (candidateNormalizer_pos E theta x0.1))).2 hcoveq
      have hCge : 1 ≤ C := by
        have hrow := (gibbsPolicy_isPolicy E P).2 x0.1
        have hrefrow := E.reference_isPolicy.2 x0.1
        have hcell_le : ∀ a,
            gibbsPolicy E P x0.1 a ≤ C * E.reference x0.1 a := by
          intro a
          by_cases ha : E.reference x0.1 a = 0
          · simp [gibbsPolicy, ha]
          · have hapos : 0 < E.reference x0.1 a :=
              lt_of_le_of_ne (E.reference_isPolicy.1 x0.1 a) (Ne.symm ha)
            have := hcovle x0 a hapos
            rw [gibbsPolicy_eq_candidate E P, candidateWeight]
            calc
              E.reference x0.1 a *
                    (Real.exp (E.eta *
                      ∑ i, E.feature x0.1 a i * theta i) /
                        candidateNormalizer E theta x0.1) ≤
                  E.reference x0.1 a * C := by
                    apply mul_le_mul_of_nonneg_left
                    · exact (div_le_iff₀
                        (candidateNormalizer_pos E theta x0.1)).2 this
                    · exact E.reference_isPolicy.1 x0.1 a
              _ = C * E.reference x0.1 a := by ring
        have hsumle :
            (∑ a : 𝒜, gibbsPolicy E P x0.1 a) ≤
              ∑ a : 𝒜, C * E.reference x0.1 a :=
          Finset.sum_le_sum (fun a _ => hcell_le a)
        rw [hrow, ← Finset.mul_sum, hrefrow, mul_one] at hsumle
        exact hsumle
      refine ⟨hCge, ?_⟩
      unfold pointwiseCoverage
      apply le_antisymm
      · exact csSup_le ⟨C, hCmem⟩ hupper
      · exact le_csSup hRfinite.bddAbove hCmem
    · refine ⟨hDpos, ?_⟩
      unfold featureCoverage
      rw [hB, hG]
      exact hmax

end CausalSmith.Stat.ReverseKLTwoCoverage
