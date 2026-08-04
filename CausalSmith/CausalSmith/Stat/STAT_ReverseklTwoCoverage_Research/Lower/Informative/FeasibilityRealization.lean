import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.BernoulliLaw

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

noncomputable section

lemma ibBernoulliLaw_exactShell_of_certificate
    (E : CommonExperiment d 𝒳 𝒜) (C D : ℝ)
    (theta : Fin d → ℝ) (rho : 𝒳 → ℝ)
    (x0 : 𝒳) (a0 : 𝒜) (u : Fin d → ℝ)
    (hbounded : BoundedFeatures E)
    (ha0 : 0 < E.reference x0 a0)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (hrho : ∀ x, 0 < rho x)
    (hsum : ∑ x, rho x = 1)
    (hBpos : Matrix.PosDef
      (∑ x : 𝒳, rho x • loggingBlock E x))
    (hcovle : ∀ x a, 0 < E.reference x a →
      Real.exp (E.eta * ∑ i, E.feature x a i * theta i) ≤
        C * candidateNormalizer E theta x)
    (hcoveq :
      Real.exp (E.eta * ∑ i, E.feature x0 a0 i * theta i) =
        C * candidateNormalizer E theta x0)
    (hPSD : Matrix.PosSemidef
      (D • (∑ x : 𝒳, rho x • loggingBlock E x) -
        ∑ x : 𝒳, rho x • targetBlock E theta x))
    (hker :
      (D • (∑ x : 𝒳, rho x • loggingBlock E x) -
        ∑ x : 𝒳, rho x • targetBlock E theta x).mulVec u = 0)
    (hunorm : dotProduct u u = 1) :
    ExactShell E
      (ibBernoulliLaw E rho theta (fun x => (hrho x).le)
        hsum hbound) C D := by
  let P := ibBernoulliLaw E rho theta (fun x => (hrho x).le) hsum hbound
  have hcontext (x : 𝒳) : contextMass P x = rho x := by
    exact ibBernoulliLaw_contextMass E rho theta
      (fun x => (hrho x).le) hsum hbound x
  have hB :
      loggingCovariance E P = ∑ x : 𝒳, rho x • loggingBlock E x := by
    ext i j
    simp only [loggingCovariance, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, loggingBlock, hcontext]
  have hG :
      targetCovariance E P = ∑ x : 𝒳, rho x • targetBlock E theta x := by
    ext i j
    simp only [targetCovariance, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, targetBlock, hcontext]
    simp_rw [gibbsPolicy_eq_candidate E P]
    rfl
  have hGpos :
      Matrix.PosDef (∑ x : 𝒳, rho x • targetBlock E theta x) := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using
      candidate_target_posDef E (Finset.univ : Finset 𝒳)
        (fun x : (Finset.univ : Finset 𝒳) => rho x.1) theta
        (fun x => hrho x.1) (by
          simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using hBpos)
  have hmax :
      maxGeneralizedEigenvalue
          (∑ x : 𝒳, rho x • loggingBlock E x)
          (∑ x : 𝒳, rho x • targetBlock E theta x) = D := by
    apply (generalizedRayleigh_certificate_iff
      (lt_of_lt_of_le (by omega : 0 < 4) E.dim_ge_four) hBpos
      (by
        simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using
          sum_targetBlock_isHermitian E (Finset.univ : Finset 𝒳)
            (fun x : (Finset.univ : Finset 𝒳) => rho x.1) theta)).mpr
    refine ⟨hPSD, u, hker, ?_⟩
    simpa [dotProduct, pow_two] using hunorm
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
  refine {
    finiteContexts := ⟨inferInstance⟩
    finiteActions := ⟨inferInstance⟩
    boundedFeatures := hbounded
    linearRealizability :=
      ibBernoulliLaw_linearRealizability E rho theta
        (fun x => (hrho x).le) hsum hbound
    referenceLogging :=
      ibBernoulliLaw_referenceLogging E rho theta
        (fun x => (hrho x).le) hsum hbound
    nonsingularLoggingGeometry := ?_
    pointwiseExactShell := ?_
    featureExactShell := ?_ }
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
      rintro c ⟨x, a, _, ha, rfl⟩
      rw [candidate_ratio_eq E P x a ha]
      apply (div_le_iff₀ (candidateNormalizer_pos E theta x)).2
      exact hcovle x a ha
    have hx0mass : 0 < contextMass P x0 := by
      rw [hcontext]
      exact hrho x0
    have hCmem : C ∈ R := by
      refine ⟨x0, a0, hx0mass, ha0, ?_⟩
      rw [candidate_ratio_eq E P x0 a0 ha0]
      symm
      exact (div_eq_iff
        (ne_of_gt (candidateNormalizer_pos E theta x0))).2 hcoveq
    have hCge : 1 ≤ C := by
      have hrow := (gibbsPolicy_isPolicy E P).2 x0
      have hrefrow := E.reference_isPolicy.2 x0
      have hcell_le : ∀ a,
          gibbsPolicy E P x0 a ≤ C * E.reference x0 a := by
        intro a
        by_cases ha : E.reference x0 a = 0
        · simp [gibbsPolicy, ha]
        · have hapos : 0 < E.reference x0 a :=
            lt_of_le_of_ne (E.reference_isPolicy.1 x0 a) (Ne.symm ha)
          rw [gibbsPolicy_eq_candidate E P, candidateWeight]
          calc
            E.reference x0 a *
                  (Real.exp (E.eta *
                    ∑ i, E.feature x0 a i * theta i) /
                      candidateNormalizer E theta x0) ≤
                E.reference x0 a * C := by
                  apply mul_le_mul_of_nonneg_left
                  · exact (div_le_iff₀
                      (candidateNormalizer_pos E theta x0)).2
                      (hcovle x0 a hapos)
                  · exact E.reference_isPolicy.1 x0 a
            _ = C * E.reference x0 a := by ring
      have hsumle :
          (∑ a : 𝒜, gibbsPolicy E P x0 a) ≤
            ∑ a : 𝒜, C * E.reference x0 a :=
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

end

end CausalSmith.Stat.ReverseKLTwoCoverage
