import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.ExactShell

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

theorem hard_blueprint {d : ℕ} (hd : 4 ≤ d)
    {eta C D eps gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) (hTwo : 2 * D - 1 < Real.exp eta)
    (heps : 0 < eps) (hepsAcc : eps ≤ hardAccuracyRange C D eta)
    (hgammaEq : gamma = hardPerturbation eps eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (hpert : gamma ≤
      min (hardScale D eta)
        (min (1 / 4)
          (min (hardBeta D eta gamma)
            (1 - hardBeta D eta gamma))))
    (v : Fin (hardCoordinateCount d) → Bool) :
    HardFamilyBlueprint
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma hgammaBeta hgammaOne)
      C D eps v hardPlus hardMinus hardZero
      (hardContextEquiv d C D hardContextCalibration)
      (hardContextEquiv d C D hardContextAnchor)
      (hardContextEquiv d C D hardContextResidual)
      (fun j => hardContextEquiv d C D (hardContextHard j))
      (hardBasisE0 hd) (hardBasisZ hd) (hardBasisU hd) (hardBasisW hd) := by
  subst gamma
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  let P := hardLaw hd eta C D (hardPerturbation eps eta)
    heta hD hDC hCexp v hgamma hgammaBeta hgammaOne
  have href : ReferenceLogging E P :=
    hardLaw_referenceLogging hd heta hD hDC hCexp v
      hgamma hgammaBeta hgammaOne
  have hregion : (C, D) ∈ hardRegion d eta :=
    ⟨hD, hDC, hCexp, hTwo, hd⟩
  have hxinj : Function.Injective
      (fun j : Fin (hardCoordinateCount d) =>
        hardContextEquiv d C D (hardContextHard j)) := by
    intro j l hjl
    apply Sum.inl.inj
    exact (hardContextEquiv d C D).injective hjl
  have hxdist : ∀ j : Fin (hardCoordinateCount d),
      hardContextEquiv d C D (hardContextHard j) ≠
          hardContextEquiv d C D hardContextCalibration ∧
        (C > D →
          hardContextEquiv d C D (hardContextHard j) ≠
            hardContextEquiv d C D hardContextAnchor) ∧
        (Even d →
          hardContextEquiv d C D (hardContextHard j) ≠
            hardContextEquiv d C D hardContextResidual) := by
    intro j
    constructor
    · intro h
      have := (hardContextEquiv d C D).injective h
      simp [hardContextHard, hardContextCalibration] at this
    constructor
    · intro hCD h
      have := (hardContextEquiv d C D).injective h
      simp [hardContextHard, hardContextAnchor, hCD] at this
    · intro heven h
      have := (hardContextEquiv d C D).injective h
      simp [hardContextHard, hardContextResidual, heven] at this
  have hxA :
      C > D →
        hardContextEquiv d C D hardContextAnchor ≠
          hardContextEquiv d C D hardContextCalibration := by
    intro hCD h
    have := (hardContextEquiv d C D).injective h
    simp [hardContextAnchor, hardContextCalibration, hCD] at this
  have hxZ :
      Even d →
        hardContextEquiv d C D hardContextResidual ≠
            hardContextEquiv d C D hardContextCalibration ∧
          (C > D →
            hardContextEquiv d C D hardContextResidual ≠
              hardContextEquiv d C D hardContextAnchor) := by
    intro heven
    constructor
    · intro h
      have := (hardContextEquiv d C D).injective h
      simp [hardContextResidual, hardContextCalibration, heven] at this
    · intro hCD h
      have := (hardContextEquiv d C D).injective h
      simp [hardContextResidual, hardContextAnchor, heven, hCD] at this
  have hxcover : ∀ x : Fin (hardContextCard d C D),
      x = hardContextEquiv d C D hardContextCalibration ∨
        (C > D ∧ x = hardContextEquiv d C D hardContextAnchor) ∨
        (∃ j, x = hardContextEquiv d C D (hardContextHard j)) ∨
        (Even d ∧ x = hardContextEquiv d C D hardContextResidual) := by
    intro x
    let y := (hardContextEquiv d C D).symm x
    have hxy : x = hardContextEquiv d C D y :=
      (hardContextEquiv d C D).apply_symm_apply x |>.symm
    rcases y with j | (hcal | (hanchor | hz))
    · exact Or.inr (Or.inr (Or.inl ⟨j, hxy⟩))
    · have : hcal = 0 := Subsingleton.elim _ _
      subst hcal
      exact Or.inl hxy
    · have hCD : C > D := by
        by_contra hn
        have hzero : Fin 0 := by simpa [hn] using hanchor
        exact Fin.elim0 hzero
      have hanchor0 : hanchor = ⟨0, by simp [hCD]⟩ := by
        apply Fin.ext
        have hh := hanchor.isLt
        simp [hCD] at hh
        omega
      rw [hanchor0] at hxy
      exact Or.inr (Or.inl ⟨hCD, by
        simpa [hardContextAnchor, hCD] using hxy⟩)
    · have heven : Even d := by
        by_contra hn
        have hzero : Fin 0 := by simpa [hn] using hz
        exact Fin.elim0 hzero
      have hz0 : hz = ⟨0, by simp [heven]⟩ := by
        apply Fin.ext
        have hh := hz.isLt
        simp [heven] at hh
        omega
      rw [hz0] at hxy
      exact Or.inr (Or.inr (Or.inr ⟨heven, by
        simpa [hardContextResidual, heven] using hxy⟩))
  have hfeatCplus : ∀ i,
      E.feature (hardContextEquiv d C D hardContextCalibration)
          hardPlus i = hardBasisE0 hd i := by
    intro i
    simp [E, hardExperiment, hardContextCalibration,
      hardFeatureOnContext, hardPlus]
  have hfeatCzero : ∀ i,
      E.feature (hardContextEquiv d C D hardContextCalibration)
          hardMinus i = 0 ∧
        E.feature (hardContextEquiv d C D hardContextCalibration)
          hardZero i = 0 := by
    intro i
    simp [E, hardExperiment, hardContextCalibration,
      hardFeatureOnContext, hardPlus, hardMinus, hardZero]
  have hrefCplus :
      E.reference (hardContextEquiv d C D hardContextCalibration)
          hardPlus = hardQ C eta := by
    simp [E, hardExperiment, hardContextCalibration,
      hardReferenceOnContext, hardPlus]
  have hrefCminus : 0 <
      E.reference (hardContextEquiv d C D hardContextCalibration)
        hardMinus := by
    simp only [E, hardExperiment, Equiv.symm_apply_apply,
      hardContextCalibration, hardReferenceOnContext, hardMinus, hardPlus,
      Fin.mk.injEq, OfNat.ofNat_ne_zero, if_false]
    exact div_pos (sub_pos.mpr (hardQ_lt_one heta hD hDC)) (by norm_num)
  have hrefCzero : 0 <
      E.reference (hardContextEquiv d C D hardContextCalibration)
        hardZero := by
    simp only [E, hardExperiment, Equiv.symm_apply_apply,
      hardContextCalibration, hardReferenceOnContext, hardZero, hardPlus,
      Fin.mk.injEq, OfNat.ofNat_ne_zero, if_false]
    exact div_pos (sub_pos.mpr (hardQ_lt_one heta hD hDC)) (by norm_num)
  have hrefCsum :
      E.reference (hardContextEquiv d C D hardContextCalibration)
          hardMinus +
        E.reference (hardContextEquiv d C D hardContextCalibration)
          hardZero = 1 - hardQ C eta := by
    simp [E, hardExperiment, hardContextCalibration,
      hardReferenceOnContext, hardPlus, hardMinus, hardZero]
  have hfeatPlus : ∀ j i,
      E.feature (hardContextEquiv d C D (hardContextHard j))
          hardPlus i =
        (hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2 := by
    intro j i
    simp [E, hardExperiment, hardContextHard,
      hardFeatureOnContext, hardPlus]
  have hfeatMinus : ∀ j i,
      E.feature (hardContextEquiv d C D (hardContextHard j))
          hardMinus i =
        (hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2 := by
    intro j i
    simp [E, hardExperiment, hardContextHard,
      hardFeatureOnContext, hardPlus, hardMinus]
  have hfeatZero : ∀ j i,
      E.feature (hardContextEquiv d C D (hardContextHard j))
          hardZero i = 0 := by
    intro j i
    simp [E, hardExperiment, hardContextHard,
      hardFeatureOnContext, hardPlus, hardMinus, hardZero]
  have hrefHard : ∀ j,
      E.reference (hardContextEquiv d C D (hardContextHard j))
            hardPlus = hardP D ∧
        E.reference (hardContextEquiv d C D (hardContextHard j))
            hardMinus = hardP D ∧
        E.reference (hardContextEquiv d C D (hardContextHard j))
            hardZero = 1 - 2 * hardP D := by
    intro j
    simp [E, hardExperiment, hardContextHard,
      hardReferenceOnContext, hardPlus, hardMinus, hardZero]
  have horth := (hardBasis_coordinate_orthonormal hd).1
  have hcross := (hardBasis_coordinate_orthonormal hd).2.1
  have he0norm := (hardBasis_coordinate_orthonormal hd).2.2
  have hzfacts : Even d →
      dotProduct (hardBasisZ hd) (hardBasisZ hd) = 1 ∧
        dotProduct (hardBasisE0 hd) (hardBasisZ hd) = 0 ∧
        (∀ j,
          dotProduct (hardBasisU hd j) (hardBasisZ hd) = 0 ∧
          dotProduct (hardBasisW hd j) (hardBasisZ hd) = 0) ∧
        (∀ a i,
          E.feature (hardContextEquiv d C D hardContextResidual) a i =
            hardBasisZ hd i) ∧
        dotProduct P.theta (hardBasisZ hd) = 0 := by
    intro heven
    have hzorth := hardBasis_z_orthonormal_of_even hd heven
    refine ⟨hzorth.1, hzorth.2.1, hzorth.2.2, ?_, ?_⟩
    · intro a i
      simp [E, hardExperiment, hardContextResidual, heven,
        hardFeatureOnContext]
    · simpa [P, hardLaw] using
        hardTheta_dot_z_of_even hd D eta (hardPerturbation eps eta) v heven
  have hdecomp : ∀ y : Fin d → ℝ, ∀ i,
      y i =
        dotProduct y (hardBasisE0 hd) * hardBasisE0 hd i +
          ∑ j,
            (dotProduct y (hardBasisU hd j) * hardBasisU hd j i +
              dotProduct y (hardBasisW hd j) * hardBasisW hd j i) +
          if Even d then
            dotProduct y (hardBasisZ hd) * hardBasisZ hd i else 0 :=
    hardBasis_decomposition hd
  have hthetaE0 : dotProduct P.theta (hardBasisE0 hd) = 1 := by
    simpa [P, hardLaw] using
      hardTheta_dot_e0 hd D eta (hardPerturbation eps eta) v
  have hthetaU : ∀ j,
      dotProduct P.theta (hardBasisU hd j) =
        Real.sqrt 2 *
          hardBeta D eta (hardPerturbation eps eta) := by
    intro j
    simpa [P, hardLaw] using
      hardTheta_dot_u hd D eta (hardPerturbation eps eta) v j
  have hthetaW : ∀ j,
      dotProduct P.theta (hardBasisW hd j) =
        Real.sqrt 2 * hardPerturbation eps eta *
          (if v j then 1 else -1) := by
    intro j
    simpa [P, hardLaw] using
      hardTheta_dot_w hd D eta (hardPerturbation eps eta) v j
  have hfeatureA : C > D → ∀ a i,
      E.feature (hardContextEquiv d C D hardContextAnchor) a i =
        hardBasisE0 hd i := by
    intro hCD a i
    simp [E, hardExperiment, hardContextAnchor, hCD, hardFeatureOnContext]
  have hmass : ∃ H tau anchor : ℝ,
      0 < H ∧ tau = (4 * (1 + anchor))⁻¹ ∧
        anchor = hardQ C eta * (C - D) / (D - 1) ∧
        H = 1 + tau + (if C > D then tau * anchor else 0) +
          (if Even d then 1 / 4 else 0) ∧
        contextMass P
            (hardContextEquiv d C D hardContextCalibration) = tau / H ∧
        (C > D → contextMass P
            (hardContextEquiv d C D hardContextAnchor) =
          tau * anchor / H) ∧
        (∀ j, contextMass P
            (hardContextEquiv d C D (hardContextHard j)) =
          (hardCoordinateCount d : ℝ)⁻¹ / H) ∧
        (Even d → contextMass P
            (hardContextEquiv d C D hardContextResidual) =
          (1 / 4) / H) := by
    refine ⟨hardTotal d C D eta, hardTau C D eta,
      hardAnchorRaw C D eta, hardTotal_pos (d := d) heta hD hDC hCexp,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hardLaw_contextMass]
      simp [hardRho, hardContextCalibration, hardContextRawMass]
    · intro hCD
      rw [hardLaw_contextMass]
      simp [hardRho, hardContextAnchor, hCD, hardContextRawMass]
    · intro j
      rw [hardLaw_contextMass]
      simp [hardRho, hardContextHard, hardContextRawMass]
    · intro heven
      rw [hardLaw_contextMass]
      simp [hardRho, hardContextResidual, heven, hardContextRawMass]
  have hnorm : ∀ j,
      gibbsNormalizer E P
          (hardContextEquiv d C D (hardContextHard j)) =
        1 - 2 * hardP D +
          2 * hardP D * hardT D eta (hardPerturbation eps eta) *
            Real.cosh (eta * hardPerturbation eps eta) := by
    intro j
    simpa [E, P] using
      hard_hard_normalizer hd heta hD hDC hCexp hden v j
  have hbern : ∀ x a,
      ConditionalBernoulliCell E P x a (linearReward P x a) := by
    simpa [E, P] using
      hardLaw_conditionalCell hd heta hD hDC hCexp v
        hgamma hgammaBeta hgammaOne
  exact ⟨href, hregion, heps, hepsAcc, hard_actions_exactly_three,
    hxinj, hxdist, hxA, hxZ, hxcover, hfeatCplus, hfeatCzero,
    hrefCplus, hrefCminus, hrefCzero, hrefCsum, hfeatPlus, hfeatMinus,
    hfeatZero, hrefHard, horth, hcross, he0norm, hzfacts, hdecomp,
    hthetaE0, hthetaU, hthetaW, hpert, hfeatureA, hmass, hnorm, hbern⟩

end

end CausalSmith.Stat.ReverseKLTwoCoverage
