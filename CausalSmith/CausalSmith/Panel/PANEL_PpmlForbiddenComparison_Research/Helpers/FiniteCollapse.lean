import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Projection
import Causalean.Stat.MEstimation.FinitePoissonConsistency
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite unit fixed-effect collapse

This module contains the panel-specific algebra for collapsing a finite unit
fixed-effect Poisson criterion to supported cohort-time cells.
-/

open scoped BigOperators Topology
open Filter
open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

-- @node: finiteCollapsedCriterion_eq_finitePoissonObjective
/-- The finite collapsed criterion is the generic finite Poisson objective on
the supported cohort-time table. -/
lemma finiteCollapsedCriterion_eq_finitePoissonObjective (T : ℕ)
    (C : Finset (Cohort T)) {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (theta : CollapsedParameter T C) :
    finiteCollapsedCriterion T C G b gamma delta theta =
      finitePoissonObjective
        (fun z : SupportedCell T C => finiteCellMass T G z.1.1)
        (fun z : SupportedCell T C =>
          finiteObservedCohortMean T G b gamma delta z.1.1 z.2)
        (collapsedDesignMap T C) theta := by
  classical
  rw [finiteCollapsedCriterion, finitePoissonObjective, Fintype.sum_prod_type]
  rw [← Finset.sum_attach]
  rfl

-- @node: collapsedDesignMap_injective
/-- The paper's positive-weight rank condition makes the collapsed design map
injective. -/
lemma collapsedDesignMap_injective (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (hRank : CollapsedDesignRank T C pi) :
    Function.Injective (collapsedDesignMap T C) := by
  intro x y hxy
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hr := hRank (x - y) hsub
  have hmap : collapsedDesignMap T C (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
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

-- @node: finiteCollapsedCriterion_exists_unique_max
/-- Positive supported counts and collapsed full rank give a unique finite
collapsed maximizer. -/
lemma finiteCollapsedCriterion_exists_unique_max (T : ℕ)
    (C : Finset (Cohort T)) {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (pi : Cohort T → OpenUnit) (hT : 0 < T) (hC : C.Nonempty)
    (hCount : ∀ g ∈ C, 0 < cohortCount T G g)
    (hRank : CollapsedDesignRank T C pi) :
    ∃! theta : CollapsedParameter T C,
      ∀ eta, finiteCollapsedCriterion T C G b gamma delta eta ≤
        finiteCollapsedCriterion T C G b gamma delta theta := by
  classical
  let q : SupportedCell T C → ℝ := fun z => finiteCellMass T G z.1.1
  let m : SupportedCell T C → ℝ := fun z =>
    finiteObservedCohortMean T G b gamma delta z.1.1 z.2
  letI : Nonempty (SupportedCell T C) :=
    ⟨(⟨hC.choose, hC.choose_spec⟩, ⟨0, hT⟩)⟩
  have hN : 0 < N := by
    obtain ⟨i, hi⟩ := (Finset.card_pos.mp
      (show 0 < (Finset.univ.filter fun i => G i = hC.choose).card by
        simpa [cohortCount] using hCount hC.choose hC.choose_spec))
    exact Nat.zero_lt_of_lt i.isLt
  have hq : ∀ z, 0 < q z := by
    intro z
    exact div_pos (Nat.cast_pos.mpr (hCount z.1.1 z.1.2))
      (mul_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hT))
  have hm : ∀ z, 0 < m z := by
    intro z
    exact finiteObservedCohortMean_pos T G b gamma delta z.1.1 z.2
      (hCount z.1.1 z.1.2)
  obtain ⟨theta, hmax, hunique⟩ := finitePoissonObjective_exists_unique_max
    q m (collapsedDesignMap T C) hq hm
      (collapsedDesignMap_injective T C pi hRank)
  refine ⟨theta, ?_, ?_⟩
  · intro eta
    simpa only [finiteCollapsedCriterion_eq_finitePoissonObjective] using hmax eta
  · intro eta heta
    apply hunique
    intro z
    simpa only [finiteCollapsedCriterion_eq_finitePoissonObjective] using heta z

-- @node: unitLevel
/-- The normalized intercept-plus-unit-effect represented by unit nuisance
coordinates. -/
noncomputable def unitLevel (T N : ℕ) (theta : UnitParameter N T) (i : Fin N) : ℝ :=
  theta.1 (Sum.inl ()) + if hi : i.val ≠ 0 then
    theta.1 (Sum.inr (Sum.inl ⟨i, hi⟩)) else 0

-- @node: unitTimeLevel
/-- The normalized time effect represented by unit nuisance coordinates. -/
noncomputable def unitTimeLevel (T N : ℕ) (theta : UnitParameter N T) (t : Fin T) : ℝ :=
  if ht : t.val ≠ 0 then theta.1 (Sum.inr (Sum.inr ⟨t, ht⟩)) else 0

-- @node: unitIndex_eq_levels
lemma unitIndex_eq_levels (T N : ℕ) (G : Fin N → Cohort T)
    (theta : UnitParameter N T) (i : Fin N) (t : Fin T) :
    unitIndex T N (unitRegressor T N G i t) theta =
      unitLevel T N theta i + unitTimeLevel T N theta t +
        theta.2 * treatmentIndicator T (G i) t := by
  classical
  unfold unitIndex unitRegressor unitNuisanceRegressor unitTreatment unitLevel unitTimeLevel
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
  have hsumUnit : (∑ x : {j : Fin N // j.val ≠ 0},
      if i = x.1 then theta.1 (Sum.inr (Sum.inl x)) else 0) =
      if hi : i.val ≠ 0 then theta.1 (Sum.inr (Sum.inl ⟨i, hi⟩)) else 0 := by
    by_cases hi : i.val ≠ 0
    · rw [dif_pos hi, Finset.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro x hx hne
        simp only [ite_eq_right_iff]
        intro heq
        exact (hne (Subtype.ext heq.symm)).elim
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [ite_eq_right_iff]
      intro heq
      exact (hi (heq ▸ x.2)).elim
  have hsumTime : (∑ x : {s : Fin T // s.val ≠ 0},
      if t = x.1 then theta.1 (Sum.inr (Sum.inr x)) else 0) =
      if ht : t.val ≠ 0 then theta.1 (Sum.inr (Sum.inr ⟨t, ht⟩)) else 0 := by
    by_cases ht : t.val ≠ 0
    · rw [dif_pos ht, Finset.sum_eq_single ⟨t, ht⟩]
      · simp
      · intro x hx hne
        simp only [ite_eq_right_iff]
        intro heq
        exact (hne (Subtype.ext heq.symm)).elim
      · simp
    · rw [dif_neg ht]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [ite_eq_right_iff]
      intro heq
      exact (ht (heq ▸ x.2)).elim
  simp only [ite_mul, one_mul, zero_mul]
  rw [hsumUnit, hsumTime]
  ring

-- @node: collapsedCohortLevel
/-- The intercept-plus-cohort-effect represented by collapsed nuisance
coordinates. -/
noncomputable def collapsedCohortLevel (T : ℕ) (C : Finset (Cohort T))
    (theta : CollapsedParameter T C) (g : Cohort T) : ℝ :=
  theta.1 (Sum.inl ()) + if hg : g ≠ ⊤ then
    if hmem : g ∈ C then theta.1 (Sum.inr (Sum.inl ⟨⟨g, hmem⟩, hg⟩)) else 0 else 0

-- @node: collapsedTimeLevel
noncomputable def collapsedTimeLevel (T : ℕ) (C : Finset (Cohort T))
    (theta : CollapsedParameter T C) (t : Fin T) : ℝ :=
  if ht : t.val ≠ 0 then theta.1 (Sum.inr (Sum.inr ⟨t, ht⟩)) else 0

-- @node: collapsedIndex_eq_levels
lemma collapsedIndex_eq_levels (T : ℕ) (C : Finset (Cohort T))
    (theta : CollapsedParameter T C) (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
    collapsedIndex T C (collapsedRegressor T C g t) theta =
      collapsedCohortLevel T C theta g + collapsedTimeLevel T C theta t +
        theta.2 * treatmentIndicator T g t := by
  classical
  unfold collapsedIndex collapsedRegressor collapsedNuisanceRegressor
    collapsedCohortLevel collapsedTimeLevel
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
  have hsumCohort : (∑ x : {c : {g : Cohort T // g ∈ C} // c.1 ≠ ⊤},
      if g = x.1.1 then theta.1 (Sum.inr (Sum.inl x)) else 0) =
      if hgt : g ≠ ⊤ then theta.1 (Sum.inr (Sum.inl ⟨⟨g, hg⟩, hgt⟩)) else 0 := by
    by_cases hgt : g ≠ ⊤
    · rw [dif_pos hgt, Finset.sum_eq_single ⟨⟨g, hg⟩, hgt⟩]
      · simp
      · intro x hx hne
        simp only [ite_eq_right_iff]
        intro heq
        exfalso
        apply hne
        exact Subtype.ext (Subtype.ext heq.symm)
      · simp
    · rw [dif_neg hgt]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [ite_eq_right_iff]
      intro heq
      exact (x.2 (by simpa [heq] using not_not.mp hgt)).elim
  have hsumTime : (∑ x : {s : Fin T // s.val ≠ 0},
      if t = x.1 then theta.1 (Sum.inr (Sum.inr x)) else 0) =
      if ht : t.val ≠ 0 then theta.1 (Sum.inr (Sum.inr ⟨t, ht⟩)) else 0 := by
    by_cases ht : t.val ≠ 0
    · rw [dif_pos ht, Finset.sum_eq_single ⟨t, ht⟩]
      · simp
      · intro x hx hne
        simp only [ite_eq_right_iff]
        intro heq
        exact (hne (Subtype.ext heq.symm)).elim
      · simp
    · rw [dif_neg ht]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [ite_eq_right_iff]
      intro heq
      exact (ht (heq ▸ x.2)).elim
  simp only [ite_mul, one_mul, zero_mul]
  rw [hsumCohort, hsumTime]
  simp [hg]
  ring

-- @node: unitDesignMap
/-- The unit-and-time fixed-effect design as a finite linear map. -/
noncomputable def unitDesignMap (T N : ℕ) (G : Fin N → Cohort T) :
    UnitParameter N T →ₗ[ℝ] (Fin N × Fin T → ℝ) :=
  { toFun := fun theta z => unitIndex T N (unitRegressor T N G z.1 z.2) theta
    map_add' := by
      intro x y
      funext z
      unfold unitIndex
      simp [mul_add, Finset.sum_add_distrib]
      ring
    map_smul' := by
      intro c x
      funext z
      unfold unitIndex
      change (∑ j, _ * (c * x.1 j)) + _ * (c * x.2) =
        c * ((∑ j, _ * x.1 j) + _ * x.2)
      rw [mul_add, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        ring
      · ring }

-- @node: unitDesignMap_injective
/-- If every supported cohort occurs, collapsed full rank implies full column
rank of the corresponding unit fixed-effect design. -/
lemma unitDesignMap_injective (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (pi : Cohort T → OpenUnit)
    (hTop : (⊤ : Cohort T) ∈ C) (hT : 0 < T)
    (hG : ∀ i, G i ∈ C) (hCount : ∀ g ∈ C, 0 < cohortCount T G g)
    (hRank : CollapsedDesignRank T C pi) : Function.Injective (unitDesignMap T N G) := by
  classical
  have hex (g : Cohort T) (hg : g ∈ C) : ∃ i, G i = g := by
    have hc := hCount g hg
    rw [cohortCount, Finset.card_pos] at hc
    obtain ⟨i, hi⟩ := hc
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  let rep : (g : Cohort T) → g ∈ C → Fin N := fun g hg => Classical.choose (hex g hg)
  have hrep (g : Cohort T) (hg : g ∈ C) : G (rep g hg) = g :=
    Classical.choose_spec (hex g hg)
  intro x y hxy
  have hmap : unitDesignMap T N G (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let d := x - y
  let a : CollapsedParameter T C :=
    (fun j => match j with
      | Sum.inl _ => unitLevel T N d (rep ⊤ hTop)
      | Sum.inr (Sum.inl c) =>
          unitLevel T N d (rep c.1.1 c.1.2) - unitLevel T N d (rep ⊤ hTop)
      | Sum.inr (Sum.inr t) => unitTimeLevel T N d t.1,
      d.2)
  have haIndex (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      collapsedIndex T C (collapsedRegressor T C g t) a = 0 := by
    have hz := congrFun hmap (rep g hg, t)
    change unitIndex T N (unitRegressor T N G (rep g hg) t) d = 0 at hz
    rw [unitIndex_eq_levels, hrep g hg] at hz
    rw [collapsedIndex_eq_levels T C a g hg t]
    have hcohort : collapsedCohortLevel T C a g = unitLevel T N d (rep g hg) := by
      by_cases hgt : g = ⊤
      · subst g
        simp [collapsedCohortLevel, a]
      · simp [collapsedCohortLevel, a, hgt, hg]
    have htime : collapsedTimeLevel T C a t = unitTimeLevel T N d t := by
      by_cases ht : t.val = 0
      · simp [collapsedTimeLevel, unitTimeLevel, ht]
      · simp [collapsedTimeLevel, unitTimeLevel, ht, a]
    rw [hcohort, htime]
    exact hz
  have ha : a = 0 := by
    by_contra hane
    have hr := hRank a hane
    have hz : (∑ g ∈ C, ∑ t : Fin T,
        limitingCellMass T pi g *
          (collapsedIndex T C (collapsedRegressor T C g t) a) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      apply Finset.sum_eq_zero
      intro t ht
      rw [haIndex g hg t]
      simp
    linarith
  have hbeta : d.2 = 0 := congrArg Prod.snd ha
  have htime (t : Fin T) : unitTimeLevel T N d t = 0 := by
    by_cases ht : t.val = 0
    · simp [unitTimeLevel, ht]
    · have hj := congrFun (congrArg Prod.fst ha) (Sum.inr (Sum.inr ⟨t, ht⟩))
      simpa [a, unitTimeLevel, ht] using hj
  have hlevel (i : Fin N) : unitLevel T N d i = 0 := by
    let t0 : Fin T := ⟨0, hT⟩
    have hz := congrFun hmap (i, t0)
    change unitIndex T N (unitRegressor T N G i t0) d = 0 at hz
    rw [unitIndex_eq_levels] at hz
    rw [hbeta, htime t0] at hz
    simp at hz
    exact hz
  have hd : d = 0 := by
    apply Prod.ext
    · funext j
      rcases j with (_ | j)
      · have hN : 0 < N := by
          obtain ⟨i, hi⟩ := hex ⊤ hTop
          exact Nat.zero_lt_of_lt i.isLt
        let i0 : Fin N := ⟨0, hN⟩
        simpa [unitLevel, i0] using hlevel i0
      · rcases j with (j | t)
        · have hj := hlevel j.1
          have hzero : d.1 (Sum.inl ()) = 0 := by
            have hN : 0 < N := Nat.zero_lt_of_lt j.1.isLt
            let i0 : Fin N := ⟨0, hN⟩
            simpa [unitLevel, i0] using hlevel i0
          simp [unitLevel, j.2, hzero] at hj
          exact hj
        · simpa [unitTimeLevel, t.2] using htime t.1
    · exact hbeta
  exact sub_eq_zero.mp hd

-- @node: unitCriterion_eq_finitePoissonObjective
/-- The unit-level PPML criterion is exactly the finite Poisson objective with equal weight on
each unit-period observation. -/
lemma unitCriterion_eq_finitePoissonObjective (T N : ℕ)
    (G : Fin N → Cohort T) (b : Fin N → PosReal) (gamma : Fin T → ℝ)
    (delta : Cell T → ℝ) (theta : UnitParameter N T) :
    unitCriterion T N G b gamma delta theta =
      finitePoissonObjective
        (fun _ : Fin N × Fin T => (((N * T : ℕ) : ℝ)⁻¹))
        (fun z : Fin N × Fin T => unitObservedMean T N G b gamma delta z.1 z.2)
        (unitDesignMap T N G) theta := by
  rw [unitCriterion, finitePoissonObjective, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  rfl

-- @node: liftCollapsedParameter
/-- A collapsed parameter can be lifted to unit fixed effects by adding each unit's log
baseline ratio within its cohort. -/
noncomputable def liftCollapsedParameter (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (b : Fin N → PosReal) (hN : 0 < N)
    (theta : CollapsedParameter T C) : UnitParameter N T :=
  let i0 : Fin N := ⟨0, hN⟩
  let r : Fin N → ℝ := fun i =>
    Real.log ((b i : ℝ) / withinCohortBaseline T G b (G i)) +
      collapsedCohortLevel T C theta (G i)
  (fun j => match j with
    | Sum.inl _ => r i0
    | Sum.inr (Sum.inl i) => r i.1 - r i0
    | Sum.inr (Sum.inr t) => collapsedTimeLevel T C theta t.1,
   theta.2)

/-- The unit-level parameter obtained by lifting collapsed fixed effects is unchanged when the
panel, support, unit assignment, baselines, and collapsed parameter are replaced by equal values. -/
add_decl_doc liftCollapsedParameter.congr_simp

-- @node: unitIndex_liftCollapsedParameter
lemma unitIndex_liftCollapsedParameter (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (b : Fin N → PosReal) (hN : 0 < N)
    (hG : ∀ i, G i ∈ C) (theta : CollapsedParameter T C) (i : Fin N) (t : Fin T) :
    unitIndex T N (unitRegressor T N G i t)
        (liftCollapsedParameter T C G b hN theta) =
      Real.log ((b i : ℝ) / withinCohortBaseline T G b (G i)) +
        collapsedIndex T C (collapsedRegressor T C (G i) t) theta := by
  classical
  rw [unitIndex_eq_levels, collapsedIndex_eq_levels T C theta (G i) (hG i) t]
  have hlevel : unitLevel T N (liftCollapsedParameter T C G b hN theta) i =
      Real.log ((b i : ℝ) / withinCohortBaseline T G b (G i)) +
        collapsedCohortLevel T C theta (G i) := by
    by_cases hi : i.val = 0
    · have hii : i = ⟨0, hN⟩ := Fin.ext hi
      subst i
      simp [unitLevel, liftCollapsedParameter]
    · simp [unitLevel, liftCollapsedParameter, hi]
  have htime : unitTimeLevel T N (liftCollapsedParameter T C G b hN theta) t =
      collapsedTimeLevel T C theta t := by
    by_cases ht : t.val = 0
    · simp [unitTimeLevel, collapsedTimeLevel, ht]
    · simp [unitTimeLevel, collapsedTimeLevel, liftCollapsedParameter, ht]
  rw [hlevel, htime]
  simp [liftCollapsedParameter]
  ring

-- @node: sum_baselineRatio_within_cohort
/-- Baseline ratios sum to the cohort count. -/
lemma sum_baselineRatio_within_cohort (T : ℕ) {N : ℕ}
    (G : Fin N → Cohort T) (b : Fin N → PosReal) (g : Cohort T)
    (hCount : 0 < cohortCount T G g) :
    ∑ i ∈ cohortIndexSet T G g,
        (b i : ℝ) / withinCohortBaseline T G b g = cohortCount T G g := by
  have hspos : 0 < ∑ i ∈ cohortIndexSet T G g, (b i : ℝ) := by
    apply Finset.sum_pos'
    · intro i hi
      exact (b i).property.le
    · rw [cohortCount] at hCount
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hCount
      exact ⟨i, by simpa [cohortIndexSet] using hi, (b i).property⟩
  rw [withinCohortBaseline, ← Finset.sum_div]
  have hc : (cohortCount T G g : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hCount)
  field_simp

-- @node: sum_baselineRatio_fiberwise
/-- A weighted sum over units whose summand is cohort-constant collapses to a
count-weighted sum over supported cohorts. -/
lemma sum_baselineRatio_fiberwise (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (b : Fin N → PosReal)
    (hG : ∀ i, G i ∈ C) (hCount : ∀ g ∈ C, 0 < cohortCount T G g)
    (f : Cohort T → ℝ) :
    ∑ i, ((b i : ℝ) / withinCohortBaseline T G b (G i)) * f (G i) =
      ∑ g ∈ C, (cohortCount T G g : ℝ) * f g := by
  classical
  calc
    ∑ i, ((b i : ℝ) / withinCohortBaseline T G b (G i)) * f (G i) =
        ∑ g ∈ C, ∑ i ∈ cohortIndexSet T G g,
          ((b i : ℝ) / withinCohortBaseline T G b g) * f g := by
      simp_rw [cohortIndexSet, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single (G i)]
      · simp [hG i]
      · intro g hg hne
        rw [if_neg (fun heq => hne heq.symm)]
      · intro hnot
        exact (hnot (hG i)).elim
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← Finset.sum_mul]
      congr 1
      exact sum_baselineRatio_within_cohort T G b g (hCount g hg)

-- @node: sum_units_by_supported_cohort
/-- Summing any quantity over units equals summing it first within each supported adoption cohort
and then across cohorts. -/
lemma sum_units_by_supported_cohort (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (hG : ∀ i, G i ∈ C) (f : Fin N → ℝ) :
    ∑ i, f i = ∑ g ∈ C, ∑ i ∈ cohortIndexSet T G g, f i := by
  classical
  simp_rw [cohortIndexSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (G i)]
  · simp [hG i]
  · intro g hg hne
    rw [if_neg (fun heq => hne heq.symm)]
  · intro hnot
    exact (hnot (hG i)).elim

-- @node: aggregateUnitDirection
/-- An arbitrary unit-level parameter direction can be collapsed by taking baseline-ratio-weighted
averages of unit fixed-effect levels within each cohort. -/
noncomputable def aggregateUnitDirection (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (b : Fin N → PosReal) (hTop : (⊤ : Cohort T) ∈ C)
    (d : UnitParameter N T) : CollapsedParameter T C :=
  let level : (g : Cohort T) → g ∈ C → ℝ := fun g _ =>
    (cohortCount T G g : ℝ)⁻¹ *
      ∑ i ∈ cohortIndexSet T G g,
        ((b i : ℝ) / withinCohortBaseline T G b g) * unitLevel T N d i
  (fun j => match j with
    | Sum.inl _ => level ⊤ hTop
    | Sum.inr (Sum.inl c) => level c.1.1 c.1.2 - level ⊤ hTop
    | Sum.inr (Sum.inr t) => unitTimeLevel T N d t.1,
   d.2)

/-- The collapsed direction formed by baseline-ratio-weighted averaging of unit fixed effects is
unchanged when the panel, support, unit data, and original direction are replaced by equal values. -/
add_decl_doc aggregateUnitDirection.congr_simp

-- @node: collapsedIndex_aggregateUnitDirection
lemma collapsedIndex_aggregateUnitDirection (T : ℕ) (C : Finset (Cohort T))
    {N : ℕ} (G : Fin N → Cohort T) (b : Fin N → PosReal)
    (hTop : (⊤ : Cohort T) ∈ C) (d : UnitParameter N T)
    (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
    collapsedIndex T C (collapsedRegressor T C g t)
        (aggregateUnitDirection T C G b hTop d) =
      (cohortCount T G g : ℝ)⁻¹ *
          ∑ i ∈ cohortIndexSet T G g,
            ((b i : ℝ) / withinCohortBaseline T G b g) * unitLevel T N d i +
        unitTimeLevel T N d t + d.2 * treatmentIndicator T g t := by
  classical
  rw [collapsedIndex_eq_levels T C _ g hg t]
  have hc : collapsedCohortLevel T C (aggregateUnitDirection T C G b hTop d) g =
      (cohortCount T G g : ℝ)⁻¹ *
        ∑ i ∈ cohortIndexSet T G g,
          ((b i : ℝ) / withinCohortBaseline T G b g) * unitLevel T N d i := by
    by_cases hgt : g = ⊤
    · subst g
      simp [collapsedCohortLevel, aggregateUnitDirection]
    · simp [collapsedCohortLevel, aggregateUnitDirection, hgt, hg]
  have ht : collapsedTimeLevel T C (aggregateUnitDirection T C G b hTop d) t =
      unitTimeLevel T N d t := by
    by_cases htz : t.val = 0
    · simp [collapsedTimeLevel, unitTimeLevel, htz]
    · simp [collapsedTimeLevel, unitTimeLevel, aggregateUnitDirection, htz]
  rw [hc, ht]
  rfl

-- @node: unitResidual_liftCollapsedParameter
/-- At a lifted parameter, a unit residual is its baseline ratio times the
corresponding collapsed cell residual. -/
lemma unitResidual_liftCollapsedParameter (T : ℕ) (C : Finset (Cohort T))
    {N : ℕ} (G : Fin N → Cohort T) (b : Fin N → PosReal) (hN : 0 < N)
    (hG : ∀ i, G i ∈ C) (hCount : ∀ g ∈ C, 0 < cohortCount T G g)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (theta : CollapsedParameter T C) (i : Fin N) (t : Fin T) :
    unitObservedMean T N G b gamma delta i t -
        Real.exp (unitIndex T N (unitRegressor T N G i t)
          (liftCollapsedParameter T C G b hN theta)) =
      ((b i : ℝ) / withinCohortBaseline T G b (G i)) *
        (finiteObservedCohortMean T G b gamma delta (G i) t -
          Real.exp (collapsedIndex T C (collapsedRegressor T C (G i) t) theta)) := by
  rw [unitIndex_liftCollapsedParameter T C G b hN hG]
  have hb := withinCohortBaseline_pos T G b (G i) (hCount (G i) (hG i))
  have hratio : 0 < (b i : ℝ) / withinCohortBaseline T G b (G i) :=
    div_pos (b i).property hb
  rw [Real.exp_add, Real.exp_log hratio]
  unfold unitObservedMean finiteObservedCohortMean finiteUntreatedMean unitTreatment
  rw [Real.exp_add]
  field_simp [ne_of_gt hb]

-- @node: unitScore_eq_collapsedScore
/-- The score of a lifted collapsed parameter in any unit direction equals
the collapsed score in the baseline-ratio-aggregated direction. -/
lemma unitScore_eq_collapsedScore (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (b : Fin N → PosReal) (hN : 0 < N) (hT : 0 < T)
    (hTop : (⊤ : Cohort T) ∈ C) (hG : ∀ i, G i ∈ C)
    (hCount : ∀ g ∈ C, 0 < cohortCount T G g)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (theta : CollapsedParameter T C) (d : UnitParameter N T) :
    ∑ z : Fin N × Fin T,
        (((N * T : ℕ) : ℝ)⁻¹) * unitDesignMap T N G d z *
          (unitObservedMean T N G b gamma delta z.1 z.2 -
            Real.exp (unitDesignMap T N G
              (liftCollapsedParameter T C G b hN theta) z)) =
      ∑ z : SupportedCell T C,
        finiteCellMass T G z.1.1 *
          collapsedDesignMap T C (aggregateUnitDirection T C G b hTop d) z *
          (finiteObservedCohortMean T G b gamma delta z.1.1 z.2 -
            Real.exp (collapsedDesignMap T C theta z)) := by
  classical
  let R : Cohort T → Fin T → ℝ := fun g t =>
    finiteObservedCohortMean T G b gamma delta g t -
      Real.exp (collapsedIndex T C (collapsedRegressor T C g t) theta)
  have hinner (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      ∑ i ∈ cohortIndexSet T G g,
          (((b i : ℝ) / withinCohortBaseline T G b g) *
            unitIndex T N (unitRegressor T N G i t) d * R g t) =
        (cohortCount T G g : ℝ) *
          collapsedIndex T C (collapsedRegressor T C g t)
            (aggregateUnitDirection T C G b hTop d) * R g t := by
    have hc0 : (cohortCount T G g : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (hCount g hg))
    have hratio := sum_baselineRatio_within_cohort T G b g (hCount g hg)
    rw [collapsedIndex_aggregateUnitDirection T C G b hTop d g hg t]
    simp_rw [unitIndex_eq_levels]
    have hGi : ∀ i ∈ cohortIndexSet T G g, G i = g := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hreplace : (∑ i ∈ cohortIndexSet T G g,
        ((b i : ℝ) / withinCohortBaseline T G b g) *
          (unitLevel T N d i + unitTimeLevel T N d t +
            d.2 * treatmentIndicator T (G i) t) * R g t) =
        ∑ i ∈ cohortIndexSet T G g,
        ((b i : ℝ) / withinCohortBaseline T G b g) *
          (unitLevel T N d i + unitTimeLevel T N d t +
            d.2 * treatmentIndicator T g t) * R g t := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hGi i hi]
    rw [hreplace]
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hratio]
    field_simp
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have sum_supported (f : {g : Cohort T // g ∈ C} → ℝ) :
      (∑ g, f g) = ∑ g ∈ C.attach, f g := by
    rw [show (Finset.univ : Finset {g : Cohort T // g ∈ C}) = C.attach by
      ext g
      simp]
  rw [sum_supported]
  simp only [unitDesignMap, collapsedDesignMap]
  change (∑ i, ∑ t, (((N * T : ℕ) : ℝ)⁻¹) *
      unitIndex T N (unitRegressor T N G i t) d *
        (unitObservedMean T N G b gamma delta i t -
          Real.exp (unitIndex T N (unitRegressor T N G i t)
            (liftCollapsedParameter T C G b hN theta)))) = _
  simp_rw [unitResidual_liftCollapsedParameter T C G b hN hG hCount gamma delta theta]
  change (∑ i, ∑ t, (((N * T : ℕ) : ℝ)⁻¹) *
      unitIndex T N (unitRegressor T N G i t) d *
        (((b i : ℝ) / withinCohortBaseline T G b (G i)) * R (G i) t)) = _
  simp_rw [mul_assoc]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := C.attach) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [sum_units_by_supported_cohort T C G hG]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro g hg
  have hGi : ∀ i ∈ cohortIndexSet T G g.1, G i = g.1 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hNT : (((N * T : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (ne_of_gt hN) (ne_of_gt hT))
  calc
    (∑ i ∈ cohortIndexSet T G g.1, (((N * T : ℕ) : ℝ)⁻¹) *
        (unitIndex T N (unitRegressor T N G i t) d *
          ((b i : ℝ) / withinCohortBaseline T G b (G i) * R (G i) t))) =
        (((N * T : ℕ) : ℝ)⁻¹) *
          ∑ i ∈ cohortIndexSet T G g.1,
            ((b i : ℝ) / withinCohortBaseline T G b g.1) *
              unitIndex T N (unitRegressor T N G i t) d * R g.1 t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hGi i hi]
      ring
    _ = (((N * T : ℕ) : ℝ)⁻¹) *
        ((cohortCount T G g.1 : ℝ) *
          collapsedIndex T C (collapsedRegressor T C g.1 t)
            (aggregateUnitDirection T C G b hTop d) * R g.1 t) := by
      rw [hinner g.1 g.2 t]
    _ = _ := by
      unfold finiteCellMass
      dsimp [collapsedDesignMap, R]
      rw [Nat.cast_mul]
      field_simp

-- @node: finite_unit_and_collapsed_unique_beta
/-- At every finite array with positive supported counts, the unique unit-FE
and collapsed maximizers have exactly the same treatment coordinate. -/
lemma finite_unit_and_collapsed_unique_beta (T : ℕ) (C : Finset (Cohort T))
    {N : ℕ} (G : Fin N → Cohort T) (b : Fin N → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (pi : Cohort T → OpenUnit) (hN : 0 < N) (hT : 0 < T) (hC : C.Nonempty)
    (hTop : (⊤ : Cohort T) ∈ C) (hG : ∀ i, G i ∈ C)
    (hCount : ∀ g ∈ C, 0 < cohortCount T G g)
    (hRank : CollapsedDesignRank T C pi) :
    IsUniqueGlobalMax (unitCriterion T N G b gamma delta)
        (maximizerOrZero (unitCriterion T N G b gamma delta)) ∧
      IsUniqueGlobalMax (finiteCollapsedCriterion T C G b gamma delta)
        (maximizerOrZero (finiteCollapsedCriterion T C G b gamma delta)) ∧
      (maximizerOrZero (unitCriterion T N G b gamma delta)).2 =
        (maximizerOrZero (finiteCollapsedCriterion T C G b gamma delta)).2 := by
  classical
  let fc := finiteCollapsedCriterion T C G b gamma delta
  obtain ⟨theta, htheta, hthetaUnique⟩ :=
    finiteCollapsedCriterion_exists_unique_max T C G b gamma delta pi hT hC hCount hRank
  have hcUnique : IsUniqueGlobalMax fc (maximizerOrZero fc) :=
    uniqueGlobalMax_maximizerOrZero fc ⟨theta, htheta, hthetaUnique⟩
  have hcsel : maximizerOrZero fc = theta := by
    exact hthetaUnique _ hcUnique.1
  let q : Fin N × Fin T → ℝ := fun _ => (((N * T : ℕ) : ℝ)⁻¹)
  let m : Fin N × Fin T → ℝ := fun z =>
    unitObservedMean T N G b gamma delta z.1 z.2
  let A := unitDesignMap T N G
  let lifted := liftCollapsedParameter T C G b hN theta
  have hqpos : ∀ z, 0 < q z := by
    intro z
    exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.mul_pos hN hT))
  have hmpos : ∀ z, 0 < m z := by
    intro z
    exact mul_pos (b z.1).property (Real.exp_pos _)
  letI : Nonempty (Fin N × Fin T) := ⟨(⟨0, hN⟩, ⟨0, hT⟩)⟩
  have hcollapsedScore (a : CollapsedParameter T C) :
      ∑ z : SupportedCell T C,
        finiteCellMass T G z.1.1 * collapsedDesignMap T C a z *
          (finiteObservedCohortMean T G b gamma delta z.1.1 z.2 -
            Real.exp (collapsedDesignMap T C theta z)) = 0 := by
    apply finitePoissonObjective_score
    intro eta
    simpa only [← finiteCollapsedCriterion_eq_finitePoissonObjective] using htheta eta
  have hunitScore (d : UnitParameter N T) :
      ∑ z, q z * A d z * (m z - Real.exp (A lifted z)) = 0 := by
    rw [unitScore_eq_collapsedScore T C G b hN hT hTop hG hCount gamma delta theta d]
    exact hcollapsedScore (aggregateUnitDirection T C G b hTop d)
  have hliftMaxObj : ∀ eta, finitePoissonObjective q m A eta ≤
      finitePoissonObjective q m A lifted :=
    finitePoissonObjective_isMax_of_score q m A lifted
      (fun z => (hqpos z).le) hunitScore
  have hliftMax : ∀ eta, unitCriterion T N G b gamma delta eta ≤
      unitCriterion T N G b gamma delta lifted := by
    intro eta
    simpa only [unitCriterion_eq_finitePoissonObjective] using hliftMaxObj eta
  obtain ⟨ustar, hustar, huunique⟩ := finitePoissonObjective_exists_unique_max
    q m A hqpos hmpos (unitDesignMap_injective T C G pi hTop hT hG hCount hRank)
  have hulift : ustar = lifted := by
    exact (huunique lifted hliftMaxObj).symm
  have huExistsUnique : ∃! u, ∀ eta, unitCriterion T N G b gamma delta eta ≤
      unitCriterion T N G b gamma delta u := by
    refine ⟨lifted, hliftMax, ?_⟩
    intro u hu
    have huobj : ∀ eta, finitePoissonObjective q m A eta ≤
        finitePoissonObjective q m A u := by
      intro eta
      simpa only [q, m, A, unitCriterion_eq_finitePoissonObjective] using hu eta
    calc
      u = ustar := huunique u huobj
      _ = lifted := hulift
  have huUnique := uniqueGlobalMax_maximizerOrZero
    (unitCriterion T N G b gamma delta) huExistsUnique
  refine ⟨huUnique, hcUnique, ?_⟩
  have husel : maximizerOrZero (unitCriterion T N G b gamma delta) = lifted := by
    exact huExistsUnique.unique huUnique.1 hliftMax
  rw [husel, hcsel]
  rfl

-- @node: selectedFiniteCollapsed_tendsto
/-- The selected finite collapsed projections converge to the limiting
collapsed projection under the paper's share and baseline limits. -/
lemma selectedFiniteCollapsed_tendsto (T : ℕ) (C : Finset (Cohort T))
    (G : ∀ N, Fin N → Cohort T) (b : ∀ N, Fin N → PosReal)
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (hHorizon : ValidPanelHorizon T) (hSupport : ValidCohortSupport T C)
    (hShare : CohortShareLimit T C G pi)
    (hBaseline : WithinCohortBaselineLimit T C G b barB)
    (hRank : CollapsedDesignRank T C pi) :
    Tendsto
      (fun N => maximizerOrZero (finiteCollapsedCriterion T C (G N) (b N) gamma delta))
      atTop (nhds (collapsedPopulationProjection T C pi barB gamma delta)) := by
  classical
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hHorizon
  have hC : C.Nonempty := ⟨⊤, hSupport.1⟩
  let qN : ℕ → SupportedCell T C → ℝ := fun N z =>
    finiteCellMass T (G N) z.1.1
  let mN : ℕ → SupportedCell T C → ℝ := fun N z =>
    finiteObservedCohortMean T (G N) (b N) gamma delta z.1.1 z.2
  let q : SupportedCell T C → ℝ := fun z => limitingCellMass T pi z.1.1
  let m : SupportedCell T C → ℝ := fun z =>
    observedCohortMean T barB gamma delta z.1.1 z.2
  let A := collapsedDesignMap T C
  let arg : ℕ → CollapsedParameter T C := fun N =>
    maximizerOrZero (finiteCollapsedCriterion T C (G N) (b N) gamma delta)
  let lim := collapsedPopulationProjection T C pi barB gamma delta
  have hqpos : ∀ z, 0 < q z := by
    intro z
    exact div_pos (pi z.1.1).property.1 (Nat.cast_pos.mpr hT)
  have hmpos : ∀ z, 0 < m z := by
    intro z
    exact mul_pos (mul_pos (barB z.1.1).property (Real.exp_pos _)) (Real.exp_pos _)
  have hqconv : ∀ z, Tendsto (fun N => qN N z) atTop (nhds (q z)) := by
    intro z
    have hs := hShare.2 z.1.1 z.1.2
    have hd := hs.div_const (T : ℝ)
    apply hd.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    dsimp [qN, q]
    unfold finiteCellMass cohortShare
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
    norm_num [Nat.cast_mul]
    field_simp
  have hmconv : ∀ z, Tendsto (fun N => mN N z) atTop (nhds (m z)) := by
    intro z
    have hb := hBaseline z.1.1 z.1.2
    have hh := (hb.mul_const (Real.exp (gamma z.2))).mul_const
      (Real.exp (treatmentIndicator T z.1.1 z.2 * delta (z.1.1, z.2)))
    simpa [mN, m, finiteObservedCohortMean, finiteUntreatedMean,
      observedCohortMean, untreatedMean, mul_assoc] using hh
  have hargmax : ∀ᶠ N in atTop, ∀ y,
      finitePoissonObjective (qN N) (mN N) A y ≤
        finitePoissonObjective (qN N) (mN N) A (arg N) := by
    filter_upwards [Filter.eventually_ge_atTop C.card] with N hcard
    have hcounts := (hShare.1 N hcard).2
    have hu := finiteCollapsedCriterion_exists_unique_max T C (G N) (b N) gamma delta
      pi hT hC hcounts hRank
    have hs := uniqueGlobalMax_maximizerOrZero
      (finiteCollapsedCriterion T C (G N) (b N) gamma delta) hu
    intro y
    simpa only [finiteCollapsedCriterion_eq_finitePoissonObjective] using hs.1 y
  have hlimit : IsUniqueGlobalMax (finitePoissonObjective q m A) lim := by
    have hp := (pseudo_true_ppml_projection T C pi barB gamma delta hRank).1
    constructor
    · intro y
      simpa only [q, m, A, lim, limitingCriterion_eq_finitePoissonObjective] using hp.1 y
    · intro y hy
      apply hp.2 y
      simpa only [q, m, A, lim, limitingCriterion_eq_finitePoissonObjective] using hy
  exact finitePoissonObjective_argmax_tendsto qN mN q m A arg lim hqpos hmpos
    (collapsedDesignMap_injective T C pi hRank) hqconv hmconv hargmax hlimit

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
