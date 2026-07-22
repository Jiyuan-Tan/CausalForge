import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Collapse

/-! Correct-specification reduction under a homogeneous proportional effect. -/

open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

-- @node: prop:homogeneous-effect-reduction
/-- A common treated-cell log effect is recovered exactly by the collapsed PPML projection. -/
theorem homogeneous_effect_reduction (T : ℕ) (C : Finset (Cohort T))
    (Omega : ℕ → Type*) (P : ∀ N, SamplingLaw (Omega N))
    (Y : ∀ N, Fin N → Fin T → Fin 2 → Omega N → ℝ)
    (b : ∀ N, Fin N → PosReal) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (delta0 : ℝ)
    (hMean : UnitUntreatedExponentialMean T Omega P Y b gamma)
    (hRank : CollapsedDesignRank T C pi)
    (hHomogeneous : ∀ g ∈ C, ∀ t : Fin T,
      treatmentIndicator T g t = 1 → delta (g, t) = delta0) :
    betaStar T C pi barB gamma delta = delta0 ∧
    ∀ g ∈ C, ∀ t : Fin T,
      fittedMean T C pi barB gamma delta g t =
        untreatedMean T barB gamma g t * Real.exp (treatmentIndicator T g t * delta0) := by
  classical
  let theta0 : CollapsedParameter T C :=
    (fun j => match j with
      | Sum.inl _ => Real.log (barB ⊤ : ℝ)
      | Sum.inr (Sum.inl c) =>
          Real.log (barB c.1.1 : ℝ) - Real.log (barB ⊤ : ℝ)
      | Sum.inr (Sum.inr u) => gamma u.1,
     delta0)
  have hgamma : ∀ t : Fin T, t.val = 0 → gamma t = 0 := hMean.2
  have htime (t : Fin T) :
      (∑ u : TimeDummy T, if t = u.1 then gamma u.1 else 0) = gamma t := by
    by_cases ht : t.val = 0
    · have hne : ∀ u : TimeDummy T, t ≠ u.1 := by
        intro u heq
        exact u.2 (by simpa [← heq] using ht)
      simp [hne, hgamma t ht]
    · let u : TimeDummy T := ⟨t, ht⟩
      rw [Fintype.sum_eq_single u]
      · simp [u]
      · intro v hv
        split_ifs with heq
        · exact False.elim (hv (Subtype.ext heq.symm))
        · rfl
  have hcohort (g : Cohort T) (hg : g ∈ C) :
      (∑ c : CohortDummy T C,
        if g = c.1.1 then
          Real.log (barB c.1.1 : ℝ) - Real.log (barB ⊤ : ℝ) else 0) =
        if g = ⊤ then 0 else Real.log (barB g : ℝ) - Real.log (barB ⊤ : ℝ) := by
    by_cases hgTop : g = ⊤
    · subst g
      simp only [if_pos]
      apply Fintype.sum_eq_zero
      intro c
      split_ifs with heq
      · exact False.elim (c.2 heq.symm)
      · rfl
    · let c : CohortDummy T C := ⟨⟨g, hg⟩, hgTop⟩
      rw [Fintype.sum_eq_single c]
      · simp [c, hgTop]
      · intro d hd
        split_ifs with heq
        · exact False.elim (hd (Subtype.ext (Subtype.ext heq.symm)))
        · rfl
  have hindex (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      collapsedIndex T C (collapsedRegressor T C g t) theta0 =
        Real.log (barB g : ℝ) + gamma t + treatmentIndicator T g t * delta0 := by
    rw [collapsedIndex, collapsedRegressor]
    rcases eq_or_ne g (⊤ : Cohort T) with rfl | hgTop
    · simp [theta0, collapsedNuisanceRegressor, htime, hcohort _ hg]
    · obtain ⟨g0, rfl⟩ := WithTop.ne_top_iff_exists.mp hgTop
      simp [theta0, collapsedNuisanceRegressor, htime, hcohort _ hg]
      ring
  have heffect (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      treatmentIndicator T g t * delta (g, t) = treatmentIndicator T g t * delta0 := by
    unfold treatmentIndicator
    rw [Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
    split_ifs with htreated
    · rw [hHomogeneous g hg t (by simp [treatmentIndicator, htreated])]
    · simp
  have hfit (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      observedCohortMean T barB gamma delta g t =
        Real.exp (collapsedIndex T C (collapsedRegressor T C g t) theta0) := by
    rw [observedCohortMean, untreatedMean, hindex g hg t, heffect g hg t]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (barB g).property]
  have hobserved_pos (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      0 < observedCohortMean T barB gamma delta g t := by
    rw [hfit g hg t]
    exact Real.exp_pos _
  have hcell_le (m eta : ℝ) (hm : 0 < m) :
      m * eta - Real.exp eta ≤ m * Real.log m - Real.exp (Real.log m) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (eta - Real.log m)) hm.le
    rw [Real.exp_sub, Real.exp_log hm] at h
    field_simp at h ⊢
    rw [Real.exp_log hm]
    linarith
  have hcell_lt (m eta : ℝ) (hm : 0 < m) (hne : eta ≠ Real.log m) :
      m * eta - Real.exp eta < m * Real.log m - Real.exp (Real.log m) := by
    have hd : eta - Real.log m ≠ 0 := sub_ne_zero.mpr hne
    have h := mul_lt_mul_of_pos_left (Real.add_one_lt_exp hd) hm
    rw [Real.exp_sub, Real.exp_log hm] at h
    field_simp at h ⊢
    rw [Real.exp_log hm]
    linarith
  have hmass (g : Cohort T) (t : Fin T) : 0 < limitingCellMass T pi g := by
    have hT : 0 < T := by
      by_contra h
      have hT0 : T = 0 := Nat.eq_zero_of_not_pos h
      subst T
      have hr := hRank (0, 1) (by simp)
      simp at hr
    exact div_pos (pi g).property.1 (by exact_mod_cast hT)
  have hmax (theta : CollapsedParameter T C) :
      limitingCriterion T C pi barB gamma delta theta ≤
        limitingCriterion T C pi barB gamma delta theta0 := by
    rw [limitingCriterion, limitingCriterion]
    apply Finset.sum_le_sum
    intro g hg
    apply Finset.sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (hmass g t).le
    have hlog : Real.log (observedCohortMean T barB gamma delta g t) =
        collapsedIndex T C (collapsedRegressor T C g t) theta0 := by
      rw [hfit g hg t, Real.log_exp]
    rw [← hlog]
    exact hcell_le _ _ (hobserved_pos g hg t)
  have hunique (theta : CollapsedParameter T C)
      (htheta : limitingCriterion T C pi barB gamma delta theta =
        limitingCriterion T C pi barB gamma delta theta0) : theta = theta0 := by
    by_contra hne
    have hneSub : theta - theta0 ≠ 0 := sub_ne_zero.mpr hne
    have hrank := hRank (theta - theta0) hneSub
    have hex : ∃ g ∈ C, ∃ t : Fin T,
        collapsedIndex T C (collapsedRegressor T C g t) theta ≠
          collapsedIndex T C (collapsedRegressor T C g t) theta0 := by
      by_contra hnone
      push_neg at hnone
      have hzero :
          (∑ g ∈ C, ∑ t : Fin T,
            limitingCellMass T pi g *
              (collapsedIndex T C (collapsedRegressor T C g t) (theta - theta0)) ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro g hg
        apply Finset.sum_eq_zero
        intro t ht
        have heq := hnone g hg t
        have hind : collapsedIndex T C (collapsedRegressor T C g t) (theta - theta0) = 0 := by
          unfold collapsedIndex at heq ⊢
          change (∑ j, (collapsedRegressor T C g t).1 j *
              (theta.1 j - theta0.1 j)) +
            (collapsedRegressor T C g t).2 * (theta.2 - theta0.2) = 0
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          linarith
        rw [hind]
        simp
      linarith
    obtain ⟨g0, hg0, t0, hdiff⟩ := hex
    have hstrictCell :
        limitingCellMass T pi g0 *
            (observedCohortMean T barB gamma delta g0 t0 *
                collapsedIndex T C (collapsedRegressor T C g0 t0) theta -
              Real.exp (collapsedIndex T C (collapsedRegressor T C g0 t0) theta)) <
          limitingCellMass T pi g0 *
            (observedCohortMean T barB gamma delta g0 t0 *
                collapsedIndex T C (collapsedRegressor T C g0 t0) theta0 -
              Real.exp (collapsedIndex T C (collapsedRegressor T C g0 t0) theta0)) := by
      apply mul_lt_mul_of_pos_left _ (hmass g0 t0)
      have hlog : Real.log (observedCohortMean T barB gamma delta g0 t0) =
          collapsedIndex T C (collapsedRegressor T C g0 t0) theta0 := by
        rw [hfit g0 hg0 t0, Real.log_exp]
      have hdiff' : collapsedIndex T C (collapsedRegressor T C g0 t0) theta ≠
          Real.log (observedCohortMean T barB gamma delta g0 t0) := by
        rw [hlog]
        exact hdiff
      rw [← hlog]
      exact hcell_lt _ _ (hobserved_pos g0 hg0 t0) hdiff'
    have hstrict : limitingCriterion T C pi barB gamma delta theta <
        limitingCriterion T C pi barB gamma delta theta0 := by
      rw [limitingCriterion, limitingCriterion]
      apply Finset.sum_lt_sum
      · intro g hg
        apply Finset.sum_le_sum
        intro t ht
        apply mul_le_mul_of_nonneg_left _ (hmass g t).le
        have hlog : Real.log (observedCohortMean T barB gamma delta g t) =
            collapsedIndex T C (collapsedRegressor T C g t) theta0 := by
          rw [hfit g hg t, Real.log_exp]
        rw [← hlog]
        exact hcell_le _ _ (hobserved_pos g hg t)
      · refine ⟨g0, hg0, ?_⟩
        apply Finset.sum_lt_sum
        · intro t ht
          apply mul_le_mul_of_nonneg_left _ (hmass g0 t).le
          have hlog : Real.log (observedCohortMean T barB gamma delta g0 t) =
              collapsedIndex T C (collapsedRegressor T C g0 t) theta0 := by
            rw [hfit g0 hg0 t, Real.log_exp]
          rw [← hlog]
          exact hcell_le _ _ (hobserved_pos g0 hg0 t)
        · exact ⟨t0, Finset.mem_univ _, hstrictCell⟩
    exact (hstrict.ne htheta)
  have hexists : ∃ x, ∀ y,
      limitingCriterion T C pi barB gamma delta y ≤
        limitingCriterion T C pi barB gamma delta x := ⟨theta0, hmax⟩
  have hprojection : collapsedPopulationProjection T C pi barB gamma delta = theta0 := by
    rw [collapsedPopulationProjection, maximizerOrZero, dif_pos hexists]
    apply hunique
    apply le_antisymm
    · exact hmax _
    · exact (Classical.choose_spec hexists) theta0
  constructor
  · rw [betaStar, hprojection]
  · intro g hg t
    rw [fittedMean, hprojection, hindex g hg t]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (barB g).property, untreatedMean]

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
