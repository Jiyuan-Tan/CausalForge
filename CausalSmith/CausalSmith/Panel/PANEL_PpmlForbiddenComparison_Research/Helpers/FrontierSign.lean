import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.Frontier
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FiniteCollapse
import Causalean.Stat.MEstimation.FinitePoissonSign

/-! Algebra connecting the primitive margin frontier to the conditional Poisson score. -/

open scoped BigOperators
open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

-- @node: frontierPrimitiveH_pos
/-- Every primitive cohort-period mass is strictly positive. -/
lemma frontierPrimitiveH_pos (T : ℕ) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (t : Fin T) :
    0 < primitiveH T pi barB gamma delta g t := by
  exact mul_pos
    (mul_pos (pi g).property.1
      (mul_pos (barB g).property (Real.exp_pos (gamma t))))
    (Real.exp_pos _)

-- @node: frontierPrimitiveRow_pos
/-- The primitive mass summed over all periods is strictly positive for every cohort. -/
lemma frontierPrimitiveRow_pos (T : ℕ) (hT : 0 < T) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) : 0 < primitiveRow T pi barB gamma delta g := by
  unfold primitiveRow
  apply Finset.sum_pos'
  · intro t _
    exact (frontierPrimitiveH_pos T pi barB gamma delta g t).le
  · exact ⟨⟨0, hT⟩, Finset.mem_univ _,
      frontierPrimitiveH_pos T pi barB gamma delta g ⟨0, hT⟩⟩

-- @node: frontierPrimitiveColumn_pos
/-- The primitive mass summed over supported cohorts is strictly positive in every period. -/
lemma frontierPrimitiveColumn_pos (T : ℕ) (C : Finset (Cohort T))
    (hC : C.Nonempty) (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) (t : Fin T) :
    0 < primitiveColumn T C pi barB gamma delta t := by
  unfold primitiveColumn
  apply Finset.sum_pos'
  · intro g hg
    exact (frontierPrimitiveH_pos T pi barB gamma delta g t).le
  · obtain ⟨g, hg⟩ := hC
    exact ⟨g, hg, frontierPrimitiveH_pos T pi barB gamma delta g t⟩

-- @node: frontierPrimitiveTotal_pos
/-- The total primitive mass over all supported cohort-period cells is strictly positive. -/
lemma frontierPrimitiveTotal_pos (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    0 < primitiveTotal T C pi barB gamma delta := by
  unfold primitiveTotal
  apply Finset.sum_pos'
  · intro g hg
    exact (frontierPrimitiveRow_pos T hT pi barB gamma delta g).le
  · obtain ⟨g, hg⟩ := hC
    exact ⟨g, hg, frontierPrimitiveRow_pos T hT pi barB gamma delta g⟩

-- @node: frontierPrimitiveColumn_sum
/-- Adding the period-specific primitive masses yields the total primitive mass. -/
lemma frontierPrimitiveColumn_sum (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    (∑ t, primitiveColumn T C pi barB gamma delta t) =
      primitiveTotal T C pi barB gamma delta := by
  classical
  unfold primitiveColumn primitiveTotal primitiveRow
  rw [Finset.sum_comm]

-- @node: frontierNuisanceParameter
/-- The beta-zero fixed-effects parameter matches primitive row and column margins through a
normalized row-column construction. -/
noncomputable def frontierNuisanceParameter (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    CollapsedParameter T C :=
  let rowLog := fun g => Real.log (primitiveRow T pi barB gamma delta g / (pi g : ℝ))
  let columnLog := fun t => Real.log (primitiveColumn T C pi barB gamma delta t)
  let totalLog := Real.log (primitiveTotal T C pi barB gamma delta)
  ((fun j => match j with
    | Sum.inl _ => rowLog ⊤ + columnLog ⟨0, hT⟩ - totalLog
    | Sum.inr (Sum.inl g) => rowLog g.1.1 - rowLog ⊤
    | Sum.inr (Sum.inr t) => columnLog t.1 - columnLog ⟨0, hT⟩), 0)

/-- The beta-zero frontier fixed-effects parameter is unchanged when the panel, cohort support,
and all primitive mean-model inputs are replaced by equal values. -/
add_decl_doc frontierNuisanceParameter.congr_simp

-- @node: frontierNuisanceParameter_index
lemma frontierNuisanceParameter_index (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
    collapsedDesignMap T C
        (frontierNuisanceParameter T C hT hTop pi barB gamma delta) (⟨g, hg⟩, t) =
      Real.log (primitiveRow T pi barB gamma delta g / (pi g : ℝ)) +
        Real.log (primitiveColumn T C pi barB gamma delta t) -
          Real.log (primitiveTotal T C pi barB gamma delta) := by
  classical
  change collapsedIndex T C (collapsedRegressor T C g t)
      (frontierNuisanceParameter T C hT hTop pi barB gamma delta) = _
  rw [collapsedIndex_eq_levels T C _ g hg t]
  unfold collapsedCohortLevel collapsedTimeLevel frontierNuisanceParameter
  dsimp only
  by_cases hgTop : g = ⊤
  · subst g
    rw [dif_neg (by simp)]
    by_cases ht : t.val ≠ 0
    · rw [dif_pos ht]
      simp
      ring
    · rw [dif_neg ht]
      have ht0 : t = ⟨0, hT⟩ := Fin.ext (Nat.eq_zero_of_not_pos (by omega))
      subst t
      simp
  · rw [dif_pos hgTop, dif_pos hg]
    by_cases ht : t.val ≠ 0
    · rw [dif_pos ht]
      simp
      ring
    · rw [dif_neg ht]
      have ht0 : t = ⟨0, hT⟩ := Fin.ext (Nat.eq_zero_of_not_pos (by omega))
      subst t
      simp
      ring

-- @node: frontierNuisanceParameter_exp
/-- At the frontier parameter, each fitted mean is the product of its row and column primitive
margins, divided by its cohort share and the total primitive mass. -/
lemma frontierNuisanceParameter_exp (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
    Real.exp (collapsedDesignMap T C
        (frontierNuisanceParameter T C hT hTop pi barB gamma delta) (⟨g, hg⟩, t)) =
      primitiveRow T pi barB gamma delta g *
        primitiveColumn T C pi barB gamma delta t /
          ((pi g : ℝ) * primitiveTotal T C pi barB gamma delta) := by
  rw [frontierNuisanceParameter_index T C hT hTop pi barB gamma delta g hg t]
  have hrow := frontierPrimitiveRow_pos T hT pi barB gamma delta g
  have hcol := frontierPrimitiveColumn_pos T C ⟨⊤, hTop⟩ pi barB gamma delta t
  have htotal := frontierPrimitiveTotal_pos T C hT ⟨⊤, hTop⟩ pi barB gamma delta
  have hpi := (pi g).property.1
  rw [Real.exp_sub, Real.exp_add, Real.exp_log (div_pos hrow hpi),
    Real.exp_log hcol, Real.exp_log htotal]
  field_simp
  <;> ring

-- @node: frontierConditionalResidual
/-- The conditional residual is the cell-mass-weighted difference between the observed mean and
the beta-zero row-column fitted mean. -/
noncomputable def frontierConditionalResidual (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (hg : g ∈ C) (t : Fin T) : ℝ :=
  limitingCellMass T pi g *
    (observedCohortMean T barB gamma delta g t -
      Real.exp (collapsedDesignMap T C
        (frontierNuisanceParameter T C hT hTop pi barB gamma delta) (⟨g, hg⟩, t)))

/-- The conditional residual at the beta-zero frontier is unchanged when the panel, support,
mean-model inputs, cohort, and period are replaced by equal values. -/
add_decl_doc frontierConditionalResidual.congr_simp

-- @node: frontierConditionalResidual_eq
lemma frontierConditionalResidual_eq (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
    frontierConditionalResidual T C hT hTop pi barB gamma delta g hg t =
      (primitiveH T pi barB gamma delta g t -
        primitiveRow T pi barB gamma delta g *
          primitiveColumn T C pi barB gamma delta t /
            primitiveTotal T C pi barB gamma delta) / T := by
  rw [frontierConditionalResidual, frontierNuisanceParameter_exp T C hT hTop]
  unfold limitingCellMass primitiveH observedCohortMean
  have hpi : (pi g : ℝ) ≠ 0 := ne_of_gt (pi g).property.1
  have htotal : primitiveTotal T C pi barB gamma delta ≠ 0 :=
    ne_of_gt (frontierPrimitiveTotal_pos T C hT ⟨⊤, hTop⟩ pi barB gamma delta)
  field_simp

-- @node: frontierConditionalResidual_row_sum
/-- The conditional residuals sum to zero within every supported cohort. -/
lemma frontierConditionalResidual_row_sum (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (hg : g ∈ C) :
    (∑ t, frontierConditionalResidual T C hT hTop pi barB gamma delta g hg t) = 0 := by
  simp_rw [frontierConditionalResidual_eq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  change (primitiveRow T pi barB gamma delta g -
    ∑ t, primitiveRow T pi barB gamma delta g *
      primitiveColumn T C pi barB gamma delta t /
        primitiveTotal T C pi barB gamma delta) / T = 0
  rw [← Finset.sum_div, ← Finset.mul_sum, frontierPrimitiveColumn_sum]
  have htotal : primitiveTotal T C pi barB gamma delta ≠ 0 :=
    ne_of_gt (frontierPrimitiveTotal_pos T C hT ⟨⊤, hTop⟩ pi barB gamma delta)
  field_simp
  ring

-- @node: frontierConditionalResidual_column_sum
/-- The conditional residuals sum to zero across supported cohorts in every period. -/
lemma frontierConditionalResidual_column_sum (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (t : Fin T) :
    (∑ g : ↑C, frontierConditionalResidual T C hT hTop pi barB gamma delta
      g.1 g.2 t) = 0 := by
  simp_rw [frontierConditionalResidual_eq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [show (∑ g : ↑C, primitiveH T pi barB gamma delta g.1 t) =
      primitiveColumn T C pi barB gamma delta t by
    unfold primitiveColumn
    simpa using Finset.sum_attach (s := C)
      (f := fun g => primitiveH T pi barB gamma delta g t)]
  change (primitiveColumn T C pi barB gamma delta t -
    ∑ g : ↑C, primitiveRow T pi barB gamma delta g.1 *
      primitiveColumn T C pi barB gamma delta t /
        primitiveTotal T C pi barB gamma delta) / T = 0
  rw [← Finset.sum_div]
  simp_rw [mul_comm (primitiveRow T pi barB gamma delta _)]
  rw [← Finset.mul_sum]
  rw [show (∑ g : ↑C, primitiveRow T pi barB gamma delta g.1) =
      primitiveTotal T C pi barB gamma delta by
    unfold primitiveTotal
    simpa using Finset.sum_attach (s := C)
      (f := fun g => primitiveRow T pi barB gamma delta g)]
  change (primitiveColumn T C pi barB gamma delta t -
    primitiveColumn T C pi barB gamma delta t *
      primitiveTotal T C pi barB gamma delta /
        primitiveTotal T C pi barB gamma delta) / T = 0
  have htotal : primitiveTotal T C pi barB gamma delta ≠ 0 :=
    ne_of_gt (frontierPrimitiveTotal_pos T C hT ⟨⊤, hTop⟩ pi barB gamma delta)
  field_simp
  ring

-- @node: frontierConditionalNuisanceScore
/-- At the beta-zero frontier fit, every nuisance-regressor score of the PPML objective is zero. -/
lemma frontierConditionalNuisanceScore (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (u : CollapsedNuisanceIndex T C → ℝ) :
    ∑ z : SupportedCell T C,
      limitingCellMass T pi z.1.1 * collapsedDesignMap T C (u, 0) z *
        (observedCohortMean T barB gamma delta z.1.1 z.2 -
          Real.exp (collapsedDesignMap T C
            (frontierNuisanceParameter T C hT hTop pi barB gamma delta) z)) = 0 := by
  classical
  rw [Fintype.sum_prod_type]
  have hreg (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      collapsedDesignMap T C (u, 0) (⟨g, hg⟩, t) =
        ∑ j, collapsedNuisanceRegressor T C g t j * u j := by
    simp [collapsedDesignMap, collapsedIndex, collapsedRegressor]
  simp_rw [hreg]
  rw [show (∑ g : ↑C, ∑ t,
      (limitingCellMass T pi g.1 *
        ∑ j, collapsedNuisanceRegressor T C g.1 t j * u j) *
          (observedCohortMean T barB gamma delta g.1 t -
            Real.exp (collapsedDesignMap T C
              (frontierNuisanceParameter T C hT hTop pi barB gamma delta) (g, t)))) =
      ∑ g : ↑C, ∑ t,
        (∑ j, collapsedNuisanceRegressor T C g.1 t j * u j) *
          frontierConditionalResidual T C hT hTop pi barB gamma delta g.1 g.2 t by
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro t _
    unfold frontierConditionalResidual
    ring]
  rw [show (∑ g : ↑C, ∑ t, (∑ j, collapsedNuisanceRegressor T C g.1 t j * u j) *
      frontierConditionalResidual T C hT hTop pi barB gamma delta g.1 g.2 t) =
      ∑ j, u j * ∑ g : ↑C, ∑ t,
        collapsedNuisanceRegressor T C g.1 t j *
          frontierConditionalResidual T C hT hTop pi barB gamma delta g.1 g.2 t by
    simp_rw [Finset.sum_mul]
    calc
      (∑ g : ↑C, ∑ t, ∑ j,
          collapsedNuisanceRegressor T C g.1 t j * u j *
            frontierConditionalResidual T C hT hTop pi barB gamma delta g.1 g.2 t) =
          ∑ g : ↑C, ∑ j, ∑ t,
            collapsedNuisanceRegressor T C g.1 t j * u j *
              frontierConditionalResidual T C hT hTop pi barB gamma delta g.1 g.2 t := by
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.sum_comm]
      _ = ∑ j, ∑ g : ↑C, ∑ t,
            collapsedNuisanceRegressor T C g.1 t j * u j *
              frontierConditionalResidual T C hT hTop pi barB gamma delta g.1 g.2 t := by
        rw [Finset.sum_comm]
      _ = _ := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro t _
        ring]
  apply Finset.sum_eq_zero
  intro j _
  apply mul_eq_zero_of_right
  rcases j with (_ | j)
  · simp only [collapsedNuisanceRegressor, one_mul]
    rw [Finset.sum_eq_zero]
    intro g _
    exact frontierConditionalResidual_row_sum T C hT hTop pi barB gamma delta g.1 g.2
  · rcases j with (j | j)
    · simp only [collapsedNuisanceRegressor]
      rw [Finset.sum_eq_single j.1]
      · simpa using frontierConditionalResidual_row_sum T C hT hTop pi barB gamma delta
          j.1.1 j.1.2
      · intro g hg hne
        simp [hne]
      · simp
    · simp only [collapsedNuisanceRegressor]
      rw [Finset.sum_comm, Finset.sum_eq_single j.1]
      · simpa using frontierConditionalResidual_column_sum T C hT hTop pi barB gamma delta j.1
      · intro t ht hne
        simp [hne]
      · simp

-- @node: frontierConditionalScalarScore
/-- At the beta-zero frontier fit, the treatment score equals the frontier elimination handle
divided by the horizon and total primitive mass. -/
lemma frontierConditionalScalarScore (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    ∑ z : SupportedCell T C,
      limitingCellMass T pi z.1.1 * collapsedDesignMap T C (0, 1) z *
        (observedCohortMean T barB gamma delta z.1.1 z.2 -
          Real.exp (collapsedDesignMap T C
            (frontierNuisanceParameter T C hT hTop pi barB gamma delta) z)) =
      frontierEliminationHandle T C pi barB gamma delta /
        (T * primitiveTotal T C pi barB gamma delta) := by
  classical
  rw [Fintype.sum_prod_type]
  have hD (g : ↑C) (t : Fin T) :
      collapsedDesignMap T C (0, 1) (g, t) = treatmentIndicator T g.1 t := by
    simp [collapsedDesignMap, collapsedIndex, collapsedRegressor]
  simp_rw [hD]
  rw [show (∑ g : ↑C, ∑ t,
      limitingCellMass T pi g.1 * treatmentIndicator T g.1 t *
        (observedCohortMean T barB gamma delta g.1 t -
          Real.exp (collapsedDesignMap T C
            (frontierNuisanceParameter T C hT hTop pi barB gamma delta) (g, t)))) =
      ∑ g : ↑C, ∑ t, treatmentIndicator T g.1 t *
        frontierConditionalResidual T C hT hTop pi barB gamma delta g.1 g.2 t by
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro t _
    unfold frontierConditionalResidual
    ring]
  simp_rw [frontierConditionalResidual_eq]
  rw [show (∑ g : ↑C, ∑ t, treatmentIndicator T g.1 t *
      ((primitiveH T pi barB gamma delta g.1 t -
        primitiveRow T pi barB gamma delta g.1 *
          primitiveColumn T C pi barB gamma delta t /
            primitiveTotal T C pi barB gamma delta) / T)) =
      (∑ g : ↑C, ∑ t, treatmentIndicator T g.1 t *
        (primitiveH T pi barB gamma delta g.1 t -
          primitiveRow T pi barB gamma delta g.1 *
            primitiveColumn T C pi barB gamma delta t /
              primitiveTotal T C pi barB gamma delta)) / T by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    ring]
  have hattach (f : Cohort T → Fin T → ℝ) :
      (∑ g : ↑C, ∑ t, f g.1 t) = ∑ g ∈ C, ∑ t, f g t := by
    simpa using Finset.sum_attach (s := C) (f := fun g => ∑ t, f g t)
  rw [show (∑ g : ↑C, ∑ t, treatmentIndicator T g.1 t *
      (primitiveH T pi barB gamma delta g.1 t -
        primitiveRow T pi barB gamma delta g.1 *
          primitiveColumn T C pi barB gamma delta t /
            primitiveTotal T C pi barB gamma delta)) =
      ∑ g ∈ C, ∑ t, treatmentIndicator T g t *
        (primitiveH T pi barB gamma delta g t -
          primitiveRow T pi barB gamma delta g *
            primitiveColumn T C pi barB gamma delta t /
              primitiveTotal T C pi barB gamma delta) by
    exact hattach (fun g t => treatmentIndicator T g t *
      (primitiveH T pi barB gamma delta g t -
        primitiveRow T pi barB gamma delta g *
          primitiveColumn T C pi barB gamma delta t /
            primitiveTotal T C pi barB gamma delta))]
  unfold frontierEliminationHandle primitiveTreatedTotal
  rw [show (∑ g ∈ C, ∑ t,
      treatmentIndicator T g t *
        (primitiveH T pi barB gamma delta g t -
          primitiveRow T pi barB gamma delta g *
            primitiveColumn T C pi barB gamma delta t /
              primitiveTotal T C pi barB gamma delta)) =
      primitiveTreatedTotal T C pi barB gamma delta -
        (∑ g ∈ C, ∑ t, treatmentIndicator T g t *
          primitiveRow T pi barB gamma delta g *
            primitiveColumn T C pi barB gamma delta t) /
              primitiveTotal T C pi barB gamma delta by
    unfold primitiveTreatedTotal
    simp_rw [mul_sub]
    simp_rw [Finset.sum_sub_distrib]
    apply congrArg₂ (· - ·) rfl
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t ht
    ring]
  have htotal : primitiveTotal T C pi barB gamma delta ≠ 0 :=
    ne_of_gt (frontierPrimitiveTotal_pos T C hT ⟨⊤, hTop⟩ pi barB gamma delta)
  field_simp
  unfold primitiveTreatedTotal
  ring

-- @node: betaStar_sign_frontierEliminationHandle
/-- The collapsed pseudo-true treatment coefficient has exactly the sign of the
primitive elimination handle. -/
lemma betaStar_sign_frontierEliminationHandle (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hTop : (⊤ : Cohort T) ∈ C) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (hRank : CollapsedDesignRank T C pi) :
    (betaStar T C pi barB gamma delta < 0 ↔
      frontierEliminationHandle T C pi barB gamma delta < 0) ∧
    (betaStar T C pi barB gamma delta = 0 ↔
      frontierEliminationHandle T C pi barB gamma delta = 0) ∧
    (0 < betaStar T C pi barB gamma delta ↔
      0 < frontierEliminationHandle T C pi barB gamma delta) := by
  classical
  let q : SupportedCell T C → ℝ := fun z => limitingCellMass T pi z.1.1
  let m : SupportedCell T C → ℝ := fun z =>
    observedCohortMean T barB gamma delta z.1.1 z.2
  let A := collapsedDesignMap T C
  let theta0 := frontierNuisanceParameter T C hT hTop pi barB gamma delta
  let u0 := theta0.1
  letI : Nonempty (SupportedCell T C) := ⟨(⟨⊤, hTop⟩, ⟨0, hT⟩)⟩
  have hq : ∀ z, 0 < q z := by
    intro z
    exact div_pos (pi z.1.1).property.1 (by exact_mod_cast hT)
  have hm : ∀ z, 0 < m z := by
    intro z
    unfold m observedCohortMean untreatedMean
    exact mul_pos (mul_pos (barB z.1.1).property (Real.exp_pos _)) (Real.exp_pos _)
  have htheta : (u0, (0 : ℝ)) = theta0 := by
    ext <;> simp [u0, theta0, frontierNuisanceParameter]
  have hNuisance (u : CollapsedNuisanceIndex T C → ℝ) :
      ∑ z, q z * A (u, 0) z * (m z - Real.exp (A (u0, 0) z)) = 0 := by
    simpa only [q, m, A, htheta, theta0] using
      frontierConditionalNuisanceScore T C hT hTop pi barB gamma delta u
  have hs := finitePoissonObjective_snd_sign_of_nuisance_score
    q m A u0 hq hm (collapsedDesignMap_injective T C pi hRank) hNuisance
  let score : ℝ := ∑ z, q z * A (0, 1) z *
    (m z - Real.exp (A (u0, 0) z))
  have hscore : score = frontierEliminationHandle T C pi barB gamma delta /
      (T * primitiveTotal T C pi barB gamma delta) := by
    simpa only [score, q, m, A, htheta, theta0] using
      frontierConditionalScalarScore T C hT hTop pi barB gamma delta
  have hdenom : 0 < (T : ℝ) * primitiveTotal T C pi barB gamma delta :=
    mul_pos (by exact_mod_cast hT)
      (frontierPrimitiveTotal_pos T C hT ⟨⊤, hTop⟩ pi barB gamma delta)
  have hcriterion : finitePoissonObjective q m A =
      limitingCriterion T C pi barB gamma delta := by
    funext theta
    exact (limitingCriterion_eq_finitePoissonObjective
      T C pi barB gamma delta theta).symm
  have hbeta : (maximizerOrZero (finitePoissonObjective q m A)).2 =
      betaStar T C pi barB gamma delta := by
    rw [hcriterion]
    rfl
  dsimp only at hs
  rw [hbeta] at hs
  change (betaStar T C pi barB gamma delta < 0 ↔ score < 0) ∧
    (betaStar T C pi barB gamma delta = 0 ↔ score = 0) ∧
    (0 < betaStar T C pi barB gamma delta ↔ 0 < score) at hs
  rw [hscore] at hs
  have hnegdiv :
      frontierEliminationHandle T C pi barB gamma delta /
          ((T : ℝ) * primitiveTotal T C pi barB gamma delta) < 0 ↔
        frontierEliminationHandle T C pi barB gamma delta < 0 := by
    constructor
    · intro h
      rcases div_neg_iff.mp h with hbad | hgood
      · exact (not_lt_of_ge hdenom.le hbad.2).elim
      · exact hgood.1
    · intro h
      exact div_neg_of_neg_of_pos h hdenom
  have hzerodiv :
      frontierEliminationHandle T C pi barB gamma delta /
          ((T : ℝ) * primitiveTotal T C pi barB gamma delta) = 0 ↔
        frontierEliminationHandle T C pi barB gamma delta = 0 := by
    constructor
    · intro h
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact (ne_of_gt hdenom h).elim
    · intro h
      simp [h]
  have hposdiv :
      0 < frontierEliminationHandle T C pi barB gamma delta /
          ((T : ℝ) * primitiveTotal T C pi barB gamma delta) ↔
        0 < frontierEliminationHandle T C pi barB gamma delta := by
    constructor
    · intro h
      rcases div_pos_iff.mp h with hgood | hbad
      · exact hgood.1
      · exact (not_lt_of_ge hdenom.le hbad.2).elim
    · intro h
      exact div_pos h hdenom
  constructor
  · exact hs.1.trans hnegdiv
  · constructor
    · exact hs.2.1.trans hzerodiv
    · exact hs.2.2.trans hposdiv

-- @node: primitiveLimitingCriterion_restrict
/-- The limiting criterion generated by the restricted primitive data is exactly the collapsed
limiting PPML criterion. -/
lemma primitiveLimitingCriterion_restrict (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    primitiveLimitingCriterion T C
        (restrictSignReversalPrimitive T C pi barB gamma delta) =
      limitingCriterion T C pi barB gamma delta := by
  funext theta
  classical
  unfold primitiveLimitingCriterion limitingCriterion restrictSignReversalPrimitive
  rw [Fintype.sum_prod_type]
  rw [show (∑ g ∈ C, ∑ t : Fin T,
      limitingCellMass T pi g *
        (observedCohortMean T barB gamma delta g t *
            collapsedIndex T C (collapsedRegressor T C g t) theta -
          Real.exp (collapsedIndex T C (collapsedRegressor T C g t) theta))) =
      ∑ g : ↑C, ∑ t : Fin T,
        limitingCellMass T pi g.1 *
          (observedCohortMean T barB gamma delta g.1 t *
              collapsedIndex T C (collapsedRegressor T C g.1 t) theta -
            Real.exp (collapsedIndex T C (collapsedRegressor T C g.1 t) theta)) by
    symm
    simpa using Finset.sum_attach (s := C) (f := fun g => ∑ t : Fin T,
      limitingCellMass T pi g *
        (observedCohortMean T barB gamma delta g t *
            collapsedIndex T C (collapsedRegressor T C g t) theta -
          Real.exp (collapsedIndex T C (collapsedRegressor T C g t) theta)))]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro t ht
  have hD : treatmentIndicator T g.1 t = 0 ∨ treatmentIndicator T g.1 t = 1 := by
    unfold treatmentIndicator
    rw [Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
    split <;> simp
  rcases hD with hD | hD
  · simp [hD, observedCohortMean, limitingCellMass]
  · simp [hD, observedCohortMean, limitingCellMass]

-- @node: primitiveBetaStar_restrict
/-- The pseudo-true treatment coefficient from the restricted primitive data equals the
collapsed-model pseudo-true coefficient. -/
lemma primitiveBetaStar_restrict (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    primitiveBetaStar T C (restrictSignReversalPrimitive T C pi barB gamma delta) =
      betaStar T C pi barB gamma delta := by
  unfold primitiveBetaStar betaStar collapsedPopulationProjection
  rw [primitiveLimitingCriterion_restrict]

-- @node: cohortShareLimit_sum_eq_one
/-- Limiting shares over the supported cohorts add up to one. -/
lemma cohortShareLimit_sum_eq_one (T : ℕ) (C : Finset (Cohort T))
    (G : ∀ N, Fin N → Cohort T) (pi : Cohort T → OpenUnit)
    (hGSupport : ∀ N i, G N i ∈ C) (hShare : CohortShareLimit T C G pi) :
    (∑ g : ↑C, (pi g : ℝ)) = 1 := by
  classical
  have hconv : Filter.Tendsto (fun N => ∑ g : ↑C, cohortShare T (G N) g.1)
      Filter.atTop (nhds (∑ g : ↑C, (pi g : ℝ))) := by
    apply tendsto_finset_sum
    intro g hg
    exact hShare.2 g.1 g.2
  have heq : ∀ᶠ N in Filter.atTop,
      (∑ g : ↑C, cohortShare T (G N) g.1) = 1 := by
    filter_upwards [Filter.eventually_ge_atTop C.card] with N hN
    have hNpos := (hShare.1 N hN).1
    have hcard : N = ∑ g ∈ C, cohortCount T (G N) g := by
      simpa [cohortCount] using
        (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin N)))
          (t := C) (f := G N) (fun i hi => hGSupport N i))
    unfold cohortShare
    rw [show (∑ g : ↑C, (cohortCount T (G N) g.1 : ℝ) / N) =
        (∑ g : ↑C, (cohortCount T (G N) g.1 : ℝ)) / N by
      rw [Finset.sum_div]]
    rw [show (∑ g : ↑C, (cohortCount T (G N) g.1 : ℝ)) = N by
      rw [show (∑ g : ↑C, (cohortCount T (G N) g.1 : ℝ)) =
          ∑ g ∈ C, (cohortCount T (G N) g : ℝ) by
        simpa using Finset.sum_attach (s := C)
          (f := fun g => (cohortCount T (G N) g : ℝ))]
      exact_mod_cast hcard.symm]
    exact div_self (by exact_mod_cast ne_of_gt hNpos)
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hone' : Filter.Tendsto (fun N => ∑ g : ↑C, cohortShare T (G N) g.1)
      Filter.atTop (nhds 1) := hone.congr' (Filter.EventuallyEq.symm heq)
  exact tendsto_nhds_unique hconv hone'

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
