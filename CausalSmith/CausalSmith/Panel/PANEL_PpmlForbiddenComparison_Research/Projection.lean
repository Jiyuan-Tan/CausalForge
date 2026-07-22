import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Basic
import Causalean.Stat.MEstimation.FinitePoisson

/-! Existence, uniqueness, and score characterization of the collapsed PPML projection. -/

open scoped BigOperators
open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

-- @node: collapsedDesignMap
/-- The collapsed design as a linear map into its finite supported-cell table. -/
noncomputable def collapsedDesignMap (T : ℕ) (C : Finset (Cohort T)) :
    CollapsedParameter T C →ₗ[ℝ] (SupportedCell T C → ℝ) :=
  { toFun := fun theta z =>
      collapsedIndex T C (collapsedRegressor T C z.1.1 z.2) theta
    map_add' := by
      intro x y
      funext z
      unfold collapsedIndex
      simp [mul_add, Finset.sum_add_distrib]
      ring
    map_smul' := by
      intro c x
      funext z
      unfold collapsedIndex
      change (∑ j, _ * (c * x.1 j)) + _ * (c * x.2) = c * ((∑ j, _ * x.1 j) + _ * x.2)
      rw [mul_add, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        ring
      · ring }

-- @node: limitingCriterion_eq_finitePoissonObjective
/-- The nested cohort/time criterion is the generic finite Poisson objective on
the supported-cell product. -/
lemma limitingCriterion_eq_finitePoissonObjective (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) (theta : CollapsedParameter T C) :
    limitingCriterion T C pi barB gamma delta theta =
      finitePoissonObjective
        (fun z : SupportedCell T C => limitingCellMass T pi z.1.1)
        (fun z : SupportedCell T C => observedCohortMean T barB gamma delta z.1.1 z.2)
        (collapsedDesignMap T C) theta := by
  classical
  rw [limitingCriterion, finitePoissonObjective, Fintype.sum_prod_type]
  rw [← Finset.sum_attach]
  rfl

-- @node: lem:pseudo-true-ppml-projection
/-- The pseudo-true collapsed parameter is unique and solves every score equation. -/
lemma pseudo_true_ppml_projection (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (hRank : CollapsedDesignRank T C pi) :
    IsUniqueGlobalMax (limitingCriterion T C pi barB gamma delta)
      (collapsedPopulationProjection T C pi barB gamma delta) ∧
    (∀ j : CollapsedNuisanceIndex T C,
      ∑ g ∈ C, ∑ t : Fin T,
        limitingCellMass T pi g * collapsedNuisanceRegressor T C g t j *
          (observedCohortMean T barB gamma delta g t -
            fittedMean T C pi barB gamma delta g t) = 0) ∧
    ∑ g ∈ C, ∑ t : Fin T,
      limitingCellMass T pi g * treatmentIndicator T g t *
        (observedCohortMean T barB gamma delta g t -
            fittedMean T C pi barB gamma delta g t) = 0 := by
  classical
  have hT : 0 < T := by
    by_contra h
    have hT0 : T = 0 := Nat.eq_zero_of_not_pos h
    subst T
    have hr := hRank (0, 1) (by simp)
    simp [CollapsedDesignRank] at hr
  have hC : C.Nonempty := by
    by_contra h
    have hC0 : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst C
    have hr := hRank (0, 1) (by simp)
    simp [CollapsedDesignRank] at hr
  let q : SupportedCell T C → ℝ := fun z => limitingCellMass T pi z.1.1
  let m : SupportedCell T C → ℝ := fun z =>
    observedCohortMean T barB gamma delta z.1.1 z.2
  let A := collapsedDesignMap T C
  have hq : ∀ z, 0 < q z := by
    intro z
    exact div_pos (pi z.1.1).property.1 (by exact_mod_cast hT)
  have hm : ∀ z, 0 < m z := by
    intro z
    exact mul_pos (mul_pos (barB z.1.1).property (Real.exp_pos _)) (Real.exp_pos _)
  have hA : Function.Injective A := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hr := hRank (x - y) hsub
    have hmap : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzero :
        (∑ g ∈ C, ∑ t : Fin T,
          limitingCellMass T pi g *
            (collapsedIndex T C (collapsedRegressor T C g t) (x - y)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      apply Finset.sum_eq_zero
      intro t ht
      have hz := congrFun hmap (⟨g, hg⟩, t)
      change collapsedIndex T C (collapsedRegressor T C g t) (x - y) = 0 at hz
      rw [hz]
      simp
    linarith
  letI : Nonempty (SupportedCell T C) :=
    ⟨(⟨hC.choose, hC.choose_spec⟩, ⟨0, hT⟩)⟩
  obtain ⟨xstar, hxmax, hxunique⟩ :=
    finitePoissonObjective_exists_unique_max q m A hq hm hA
  have hcriterion (theta : CollapsedParameter T C) :
      limitingCriterion T C pi barB gamma delta theta =
        finitePoissonObjective q m A theta := by
    exact limitingCriterion_eq_finitePoissonObjective T C pi barB gamma delta theta
  have hlimmax : ∀ y, limitingCriterion T C pi barB gamma delta y ≤
      limitingCriterion T C pi barB gamma delta xstar := by
    intro y
    simpa only [hcriterion] using hxmax y
  have hexists : ∃ x, ∀ y, limitingCriterion T C pi barB gamma delta y ≤
      limitingCriterion T C pi barB gamma delta x := ⟨xstar, hlimmax⟩
  have hprojection : collapsedPopulationProjection T C pi barB gamma delta = xstar := by
    rw [collapsedPopulationProjection, maximizerOrZero, dif_pos hexists]
    apply hxunique
    intro y
    rw [← hcriterion, ← hcriterion]
    exact Classical.choose_spec hexists y
  have hisUnique : IsUniqueGlobalMax (limitingCriterion T C pi barB gamma delta)
      (collapsedPopulationProjection T C pi barB gamma delta) := by
    rw [hprojection]
    refine ⟨hlimmax, ?_⟩
    intro y hy
    apply hxunique
    intro z
    rw [← hcriterion, ← hcriterion]
    exact (hlimmax z).trans_eq hy.symm
  have hscore (d : CollapsedParameter T C) :
      ∑ z : SupportedCell T C,
        q z * A d z * (m z - Real.exp (A xstar z)) = 0 :=
    finitePoissonObjective_score q m A xstar d hxmax
  refine ⟨hisUnique, ?_, ?_⟩
  · intro j
    let d : CollapsedParameter T C := (fun k => if k = j then 1 else 0, 0)
    have hs := hscore d
    have hd (z : SupportedCell T C) : A d z =
        collapsedNuisanceRegressor T C z.1.1 z.2 j := by
      change (∑ k, collapsedNuisanceRegressor T C z.1.1 z.2 k *
        (if k = j then 1 else 0)) + treatmentIndicator T z.1.1 z.2 * 0 = _
      rw [Fintype.sum_eq_single j]
      · simp
      · intro k hk
        simp [hk]
    have hx (z : SupportedCell T C) : A xstar z =
        collapsedIndex T C (collapsedRegressor T C z.1.1 z.2) xstar := rfl
    simp only [hd, hx] at hs
    rw [Fintype.sum_prod_type] at hs
    rw [← Finset.sum_attach]
    simpa [q, m, fittedMean, hprojection] using hs
  · let d : CollapsedParameter T C := (0, 1)
    have hs := hscore d
    have hd (z : SupportedCell T C) : A d z = treatmentIndicator T z.1.1 z.2 := by
      simp [A, d, collapsedDesignMap, collapsedIndex, collapsedRegressor]
    have hx (z : SupportedCell T C) : A xstar z =
        collapsedIndex T C (collapsedRegressor T C z.1.1 z.2) xstar := rfl
    simp only [hd, hx] at hs
    rw [Fintype.sum_prod_type] at hs
    rw [← Finset.sum_attach]
    simpa [q, m, fittedMean, hprojection] using hs

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
