import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.ForbiddenSign
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.Frontier
import Causalean.Stat.MEstimation.FinitePoissonSign
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWLContinuity
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Homogeneous
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.PrimitiveFrontier
import Mathlib.Tactic.NormNum

/-! The explicit four-cohort sign-reversal fixture and its local diagnostic. -/

open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

/-- The mean-weighted support is unchanged when the panel dimension, supported cohorts, and all
inputs determining the cohort shares and fitted means are replaced by equal values. -/
add_decl_doc meanWeightedSupport.congr_simp

/-- The numerator matrix of the no-effect two-way residual table. -/
def fourResidualNumerator (g : Cohort 4) (t : Fin 4) : ℝ :=
  if g = ((⟨1, by decide⟩ : Fin 4) : Cohort 4) then
    if t.val = 0 then -3 else if t.val = 1 then 3 else if t.val = 2 then 1 else -1
  else if g = ((⟨2, by decide⟩ : Fin 4) : Cohort 4) then
    if t.val = 0 then -1 else if t.val = 1 then -3 else if t.val = 2 then 3 else 1
  else if g = ((⟨3, by decide⟩ : Fin 4) : Cohort 4) then
    if t.val = 0 then 1 else if t.val = 1 then -1 else if t.val = 2 then -3 else 3
  else
    if t.val = 0 then 3 else if t.val = 1 then 1 else if t.val = 2 then -1 else -3

/-- The exact no-effect residual table displayed in the paper. -/
noncomputable def fourResidualTable (g : Cohort 4) (t : Fin 4) : ℝ :=
  fourResidualNumerator g t / 8

/-- The homogeneous no-effect vector used only for the derivative diagnostic. -/
def zeroEffects4 (_z : Cell 4) : ℝ := 0

def fourHorizonPositive : 0 < 4 := by decide

def fourSupportNonempty : fourCohortSupport.Nonempty :=
  ⟨⊤, by simp [fourCohortSupport]⟩

def fourLateCohort : Cohort 4 := ((⟨1, by decide⟩ : Fin 4) : Cohort 4)

def fourLatePeriod : Fin 4 := ⟨3, by decide⟩

noncomputable def fourLateSupportedCell : SupportedCell 4 fourCohortSupport :=
  (⟨fourLateCohort, by simp [fourLateCohort, fourCohortSupport]⟩, fourLatePeriod)

lemma fourCohortCollapsedDesignRank :
    CollapsedDesignRank 4 fourCohortSupport fourCohortShare := by
  intro a ha
  have hnonneg (g : Cohort 4) (t : Fin 4) :
      0 ≤ limitingCellMass 4 fourCohortShare g *
        (collapsedIndex 4 fourCohortSupport
          (collapsedRegressor 4 fourCohortSupport g t) a) ^ 2 :=
    mul_nonneg (by
      simp only [limitingCellMass, fourCohortShare]
      positivity) (sq_nonneg _)
  by_contra hpos
  have hsum :
      (∑ g ∈ fourCohortSupport, ∑ t : Fin 4,
        limitingCellMass 4 fourCohortShare g *
          (collapsedIndex 4 fourCohortSupport
            (collapsedRegressor 4 fourCohortSupport g t) a) ^ 2) = 0 := by
    apply le_antisymm (le_of_not_gt hpos)
    exact Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun t _ => hnonneg g t
  have hindex (g : Cohort 4) (hg : g ∈ fourCohortSupport) (t : Fin 4) :
      collapsedIndex 4 fourCohortSupport
        (collapsedRegressor 4 fourCohortSupport g t) a = 0 := by
    have hgzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun g hg => Finset.sum_nonneg fun t _ => hnonneg g t)).mp hsum g hg
    have htzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => hnonneg g t)).mp hgzero t (Finset.mem_univ t)
    have hmass : limitingCellMass 4 fourCohortShare g ≠ 0 := by
      norm_num [limitingCellMass, fourCohortShare]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp htzero).resolve_left hmass)
  have hzero : a = 0 := by
    rcases a with ⟨u, beta⟩
    have htop (n : Fin 4) := hindex (⊤ : Cohort 4)
      (by simp [fourCohortSupport]) n
    have hc1 (n : Fin 4) := hindex fourLateCohort
      (by simp [fourLateCohort, fourCohortSupport]) n
    have hc2 (n : Fin 4) := hindex
      ((⟨2, by decide⟩ : Fin 4) : Cohort 4)
      (by simp [fourCohortSupport]) n
    have hc3 (n : Fin 4) := hindex
      ((⟨3, by decide⟩ : Fin 4) : Cohort 4)
      (by simp [fourCohortSupport]) n
    have hcohortTop : (∑ x : CohortDummy 4 fourCohortSupport,
        if (⊤ : Cohort 4) = x.1.1 then u (Sum.inr (Sum.inl x)) else 0) = 0 := by
      apply Fintype.sum_eq_zero
      intro x
      rw [if_neg]
      exact x.2 ∘ Eq.symm
    have htimeZero : (∑ x : TimeDummy 4,
        if (⟨0, by decide⟩ : Fin 4) = x.1 then u (Sum.inr (Sum.inr x)) else 0) = 0 := by
      apply Fintype.sum_eq_zero
      intro x
      rw [if_neg]
      intro h
      exact x.2 (by simpa [← h])
    have hcohort (x : CohortDummy 4 fourCohortSupport) :
        (∑ y : CohortDummy 4 fourCohortSupport,
          if x.1.1 = y.1.1 then u (Sum.inr (Sum.inl y)) else 0) =
            u (Sum.inr (Sum.inl x)) := by
      rw [Fintype.sum_eq_single x]
      · simp
      · intro y hy
        rw [if_neg]
        intro h
        exact hy (Subtype.ext (Subtype.ext h.symm))
    have htime (x : TimeDummy 4) :
        (∑ y : TimeDummy 4,
          if x.1 = y.1 then u (Sum.inr (Sum.inr y)) else 0) =
            u (Sum.inr (Sum.inr x)) := by
      rw [Fintype.sum_eq_single x]
      · simp
      · intro y hy
        rw [if_neg]
        intro h
        exact hy (Subtype.ext h.symm)
    have hintercept : u (Sum.inl ()) = 0 := by
      have hx := htop (⟨0, by decide⟩ : Fin 4)
      simp only [collapsedIndex, collapsedRegressor, collapsedNuisanceRegressor,
        Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, one_mul] at hx
      simp only [ite_mul, one_mul, zero_mul] at hx
      rw [hcohortTop, htimeZero] at hx
      norm_num [treatmentIndicator,
        Causalean.Panel.AdoptionPath.absorbingTreatment_eq] at hx
      exact hx
    have hcohortZero (x : CohortDummy 4 fourCohortSupport) :
        u (Sum.inr (Sum.inl x)) = 0 := by
      have hxmem := x.1.2
      simp only [fourCohortSupport, Finset.mem_insert, Finset.mem_singleton] at hxmem
      rcases hxmem with h | h | h | h
      · have heq : x.1.1 = fourLateCohort := by simpa [fourLateCohort] using h
        have hx := hindex x.1.1 x.1.2 (⟨0, by decide⟩ : Fin 4)
        simp only [collapsedIndex, collapsedRegressor, collapsedNuisanceRegressor,
          Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, one_mul] at hx
        simp only [ite_mul, one_mul, zero_mul] at hx
        rw [hcohort x, htimeZero, hintercept] at hx
        have huntreated : treatmentIndicator 4 x.1.1 (⟨0, by decide⟩ : Fin 4) = 0 := by
          rw [heq]
          rw [treatmentIndicator, Causalean.Panel.AdoptionPath.absorbingTreatment_eq,
            if_neg (by
              apply not_le.mpr
              change ((⟨0, by decide⟩ : Fin 4) : WithTop (Fin 4)) <
                ((⟨1, by decide⟩ : Fin 4) : WithTop (Fin 4))
              exact WithTop.coe_lt_coe.mpr (by decide))]
        rw [huntreated] at hx
        norm_num at hx ⊢
        exact hx
      · have hx := hindex x.1.1 x.1.2 (⟨0, by decide⟩ : Fin 4)
        simp only [collapsedIndex, collapsedRegressor, collapsedNuisanceRegressor,
          Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, one_mul] at hx
        simp only [ite_mul, one_mul, zero_mul] at hx
        rw [hcohort x, htimeZero, hintercept] at hx
        norm_num [h, treatmentIndicator,
          Causalean.Panel.AdoptionPath.absorbingTreatment_eq] at hx
        exact hx
      · have hx := hindex x.1.1 x.1.2 (⟨0, by decide⟩ : Fin 4)
        simp only [collapsedIndex, collapsedRegressor, collapsedNuisanceRegressor,
          Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, one_mul] at hx
        simp only [ite_mul, one_mul, zero_mul] at hx
        rw [hcohort x, htimeZero, hintercept] at hx
        norm_num [h, treatmentIndicator,
          Causalean.Panel.AdoptionPath.absorbingTreatment_eq] at hx
        exact hx
      · exact (x.2 h).elim
    have htimeZero' (x : TimeDummy 4) : u (Sum.inr (Sum.inr x)) = 0 := by
      have hx := htop x.1
      simp only [collapsedIndex, collapsedRegressor, collapsedNuisanceRegressor,
        Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, one_mul] at hx
      simp only [ite_mul, one_mul, zero_mul] at hx
      rw [hcohortTop, htime x, hintercept] at hx
      simp [treatmentIndicator,
        Causalean.Panel.AdoptionPath.absorbingTreatment_eq] at hx
      exact hx
    have hu : u = 0 := by
      funext j
      rcases j with (_ | j)
      · exact hintercept
      · rcases j with (j | j)
        · exact hcohortZero j
        · exact htimeZero' j
    have hbeta : beta = 0 := by
      have hx := hc1 (⟨1, by decide⟩ : Fin 4)
      simp [collapsedIndex, collapsedRegressor, hu] at hx
      norm_num [fourLateCohort, treatmentIndicator,
        Causalean.Panel.AdoptionPath.absorbingTreatment_eq] at hx
      exact hx
    ext j
    · exact congrFun hu j
    · exact hbeta
  exact ha hzero

/-- With zero treatment effects, the fitted mean equals one in every supported four-cohort cell. -/
lemma fourFittedMean_zeroEffects (g : Cohort 4) (hg : g ∈ fourCohortSupport)
    (t : Fin 4) :
    fittedMean 4 fourCohortSupport fourCohortShare fourCohortLimitBaseline
      fourCohortGamma zeroEffects4 g t = 1 := by
  let Omega : ℕ → Type := fun _ => Unit
  let P : ∀ N, SamplingLaw (Omega N) := fun _ f => f ()
  let Y : ∀ N, Fin N → Fin 4 → Fin 2 → Omega N → ℝ := fun _ _ _ _ _ => 1
  let b : ∀ N, Fin N → PosReal := fun _ _ => ⟨1, zero_lt_one⟩
  have hMean : UnitUntreatedExponentialMean 4 Omega P Y b fourCohortGamma := by
    constructor
    · intro N i s
      simp [P, Y, b, fourCohortGamma, expectationUnder]
    · intro s hs
      rfl
  have hhom : ∀ k ∈ fourCohortSupport, ∀ s : Fin 4,
      treatmentIndicator 4 k s = 1 → zeroEffects4 (k, s) = 0 := by
    simp [zeroEffects4]
  have hfit := (homogeneous_effect_reduction 4 fourCohortSupport Omega P Y b
    fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4 0
    hMean fourCohortCollapsedDesignRank hhom).2 g hg t
  simpa [untreatedMean, fourCohortLimitBaseline, fourCohortGamma] using hfit

/-- Each cohort's entries in the explicit four-cohort residual table sum to zero over time. -/
lemma fourResidualTable_row_sum (g : Cohort 4) (hg : g ∈ fourCohortSupport) :
    (∑ t : Fin 4, fourResidualTable g t) = 0 := by
  simp only [fourCohortSupport, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    norm_num [fourResidualTable, fourResidualNumerator, Fin.sum_univ_succ]

/-- The explicit four-cohort residual table sums to zero across cohorts in every period. -/
lemma fourResidualTable_column_sum (t : Fin 4) :
    (∑ g ∈ fourCohortSupport, fourResidualTable g t) = 0 := by
  fin_cases t <;>
    norm_num [fourCohortSupport, fourResidualTable, fourResidualNumerator]

/-- Any supported-cell function that is additive in an intercept, cohort component, and time
component belongs to the collapsed fixed-effects nuisance space. -/
lemma additive_supported_mem_collapsedNuisanceSubspace
    (T : ℕ) (hT : 0 < T) (C : Finset (Cohort T))
    (alpha : ℝ) (cohortPart : Cohort T → ℝ) (timePart : Fin T → ℝ)
    (hcohortTop : cohortPart ⊤ = 0)
    (htimeZero : timePart ⟨0, hT⟩ = 0) :
    (fun z : SupportedCell T C => alpha + cohortPart z.1.1 + timePart z.2) ∈
      collapsedNuisanceSubspace T C := by
  classical
  let rho : CollapsedNuisanceIndex T C → ℝ
    | Sum.inl _ => alpha
    | Sum.inr (Sum.inl g) => cohortPart g.1.1
    | Sum.inr (Sum.inr t) => timePart t.1
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨rho, ?_⟩
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    collapsedNuisanceSubspace, collapsedNuisanceRegressor,
    Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, one_mul]
  have hcohort : (∑ g : CohortDummy T C,
      if z.1.1 = g.1.1 then cohortPart g.1.1 else 0) = cohortPart z.1.1 := by
    by_cases htop : z.1.1 = ⊤
    · rw [htop, hcohortTop]
      apply Fintype.sum_eq_zero
      intro g
      simp only [ite_eq_right_iff]
      intro heq
      exact (g.2 heq.symm).elim
    · let g : CohortDummy T C := ⟨z.1, htop⟩
      rw [Fintype.sum_eq_single g]
      · simp [g]
      · intro y hy
        rw [if_neg]
        intro heq
        exact hy (Subtype.ext (Subtype.ext heq.symm))
  have htime : (∑ t : TimeDummy T,
      if z.2 = t.1 then timePart t.1 else 0) = timePart z.2 := by
    by_cases hz : z.2 = ⟨0, hT⟩
    · rw [hz, htimeZero]
      apply Fintype.sum_eq_zero
      intro t
      simp only [ite_eq_right_iff]
      intro heq
      exact (t.2 (by simpa [← heq])).elim
    · have hzval : z.2.val ≠ 0 := by
        intro hv
        apply hz
        apply Fin.ext
        simpa using hv
      let t : TimeDummy T := ⟨z.2, hzval⟩
      rw [Fintype.sum_eq_single t]
      · simp [t]
      · intro y hy
        rw [if_neg]
        intro heq
        exact hy (Subtype.ext heq.symm)
  simp only [rho, one_mul, mul_ite, mul_one, mul_zero]
  rw [hcohort, htime]
  ring

/-- In the four-cohort design, treatment minus the displayed residual table is a fixed-effects
nuisance component. -/
lemma fourResidualProjection_mem :
    (fun z : SupportedCell 4 fourCohortSupport =>
      treatmentIndicator 4 z.1.1 z.2 - fourResidualTable z.1.1 z.2) ∈
      collapsedNuisanceSubspace 4 fourCohortSupport := by
  let cohortPart : Cohort 4 → ℝ := fun g =>
    if g = fourLateCohort then 3 / 4
    else if g = ((⟨2, by decide⟩ : Fin 4) : Cohort 4) then 1 / 2
    else if g = ((⟨3, by decide⟩ : Fin 4) : Cohort 4) then 1 / 4
    else 0
  let timePart : Fin 4 → ℝ := fun t => t.val / 4
  have hadd := additive_supported_mem_collapsedNuisanceSubspace 4 fourHorizonPositive
    fourCohortSupport (-(3 : ℝ) / 8) cohortPart timePart (by simp [cohortPart, fourLateCohort])
      (by simp [timePart])
  convert hadd using 1
  funext z
  rcases z with ⟨⟨g, hg⟩, t⟩
  simp only [fourCohortSupport, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with h | h | h | h
  · subst g
    have h10 : ¬((((⟨1, by decide⟩ : Fin 4) : Cohort 4)) ≤
        (((⟨0, by decide⟩ : Fin 4) : Cohort 4))) := by
      simp only [WithTop.coe_le_coe, Fin.mk_le_mk]
      omega
    fin_cases t <;> simp [cohortPart, timePart, fourLateCohort, h10,
      fourResidualTable, fourResidualNumerator, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq] <;> norm_num <;>
        exact WithTop.coe_lt_coe.mpr (by decide)
  · subst g
    fin_cases t <;> simp [cohortPart, timePart, fourLateCohort,
      fourResidualTable, fourResidualNumerator, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq] <;> norm_num
  · subst g
    fin_cases t <;> simp [cohortPart, timePart, fourLateCohort,
      fourResidualTable, fourResidualNumerator, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq] <;> norm_num
  · subst g
    fin_cases t <;> simp [cohortPart, timePart, fourLateCohort,
      fourResidualTable, fourResidualNumerator, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq] <;> norm_num

/-- Under zero treatment effects, every supported cell receives equal mean-projection weight,
namely one sixteenth. -/
lemma fourMeanWeightedSupport_weight (z : SupportedCell 4 fourCohortSupport) :
    (meanWeightedSupport 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
      fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4).weight z =
      (1 : ℝ) / 16 := by
  unfold meanWeightedSupport normalizedPositiveSupport
  simp only [Finset.mem_univ, ↓reduceIte]
  simp only [meanFWLWeight]
  have hfit (y : SupportedCell 4 fourCohortSupport) :
      fittedMean 4 fourCohortSupport fourCohortShare fourCohortLimitBaseline
        fourCohortGamma zeroEffects4 y.1.1 y.2 = 1 :=
    fourFittedMean_zeroEffects y.1.1 y.1.2 y.2
  simp_rw [hfit]
  norm_num [meanFWLWeight, limitingCellMass, fourCohortShare,
    Fintype.sum_prod_type, fourCohortSupport]
  norm_num [div_eq_mul_inv]
  rfl

/-- The explicit residual table has zero unweighted inner product with every nuisance regressor. -/
lemma fourResidualTable_nuisance_normal
    (j : CollapsedNuisanceIndex 4 fourCohortSupport) :
    (∑ z : SupportedCell 4 fourCohortSupport,
      fourResidualTable z.1.1 z.2 *
        collapsedNuisanceRegressor 4 fourCohortSupport z.1.1 z.2 j) = 0 := by
  rw [Fintype.sum_prod_type]
  rcases j with (_ | j)
  · simp only [collapsedNuisanceRegressor, mul_one]
    apply Fintype.sum_eq_zero
    intro g
    exact fourResidualTable_row_sum g.1 g.2
  · rcases j with (j | j)
    · apply Fintype.sum_eq_zero
      intro g
      simp only [collapsedNuisanceRegressor]
      by_cases hgj : g.1 = j.1.1
      · simp only [hgj, ↓reduceIte, mul_one]
        exact fourResidualTable_row_sum j.1.1 j.1.2
      · simp [hgj]
    · rw [Finset.sum_comm]
      apply Fintype.sum_eq_zero
      intro t
      by_cases htj : t = j.1
      · subst t
        simp only [collapsedNuisanceRegressor, ↓reduceIte, mul_one]
        simpa using fourResidualTable_column_sum j.1
      · simp [collapsedNuisanceRegressor, htj]

/-- The explicit residual table is orthogonal, under the mean weights, to the entire
fixed-effects nuisance space. -/
lemma fourResidualTable_orthogonal :
    let c := meanWeightedSupport 4 fourCohortSupport fourHorizonPositive
      fourSupportNonempty fourCohortShare fourCohortLimitBaseline
      fourCohortGamma zeroEffects4
    let H := collapsedNuisanceSubspace 4 fourCohortSupport
    let R : SupportedCell 4 fourCohortSupport → ℝ :=
      fun z => fourResidualTable z.1.1 z.2
    ∀ h ∈ H, c.ip R h = 0 := by
  classical
  dsimp only
  intro h hh
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
  · rintro x ⟨j, rfl⟩
    simp only [Causalean.Panel.Weighted.WeightedSupport.ip_def]
    change (∑ r : SupportedCell 4 fourCohortSupport,
      (meanWeightedSupport 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
        fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4).weight r *
        fourResidualTable r.1.1 r.2 *
          collapsedNuisanceRegressor 4 fourCohortSupport r.1.1 r.2 j) = 0
    simp_rw [fourMeanWeightedSupport_weight]
    rw [show (∑ r : SupportedCell 4 fourCohortSupport,
        (1 / 16 : ℝ) * fourResidualTable r.1.1 r.2 *
          collapsedNuisanceRegressor 4 fourCohortSupport r.1.1 r.2 j) =
        (1 / 16 : ℝ) * ∑ r : SupportedCell 4 fourCohortSupport,
          fourResidualTable r.1.1 r.2 *
            collapsedNuisanceRegressor 4 fourCohortSupport r.1.1 r.2 j by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring]
    rw [fourResidualTable_nuisance_normal, mul_zero]
  · simp [Causalean.Panel.Weighted.WeightedSupport.ip]
  · intro x y _ _ hx hy
    rw [Causalean.Panel.Weighted.WeightedSupport.ip_add_right, hx, hy, add_zero]
  · intro s x _ hx
    rw [Causalean.Panel.Weighted.WeightedSupport.ip_smul_right, hx, mul_zero]

/-- In the four-cohort zero-effect design, the weighted FWL treatment residual equals the
explicit residual-table entry in every cell. -/
lemma fourWeightedFWLResidual_table (z : SupportedCell 4 fourCohortSupport) :
    weightedFWLResidual 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
      fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4 z =
      fourResidualTable z.1.1 z.2 := by
  let c := meanWeightedSupport 4 fourCohortSupport fourHorizonPositive
    fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4
  let H := collapsedNuisanceSubspace 4 fourCohortSupport
  let D : SupportedCell 4 fourCohortSupport → ℝ :=
    fun y => treatmentIndicator 4 y.1.1 y.2
  let P : SupportedCell 4 fourCohortSupport → ℝ :=
    fun y => D y - fourResidualTable y.1.1 y.2
  have hP : P ∈ H := fourResidualProjection_mem
  have horth : ∀ h ∈ H, c.ip (D - P) h = 0 := by
    intro h hh
    simpa [c, D, P, Pi.sub_apply] using fourResidualTable_orthogonal h hh
  have hproj : c.proj H D z = P z :=
    c.proj_apply_eq_of_mem_orthogonal H D hP horth z
      (by simp [c, meanWeightedSupport, normalizedPositiveSupport])
  rw [weightedFWLResidual]
  change D z - c.proj H D z = _
  rw [hproj]
  simp [P]

/-- The specified four-cohort effects coincide with the multiplier-effect family evaluated at
multipliers 1.01 and 4. -/
lemma fourCohortDelta_eq_multiplier :
    fourCohortDelta = fourMultiplierEffects ((101 : ℝ) / 100) 4 := by
  funext z
  simp [fourCohortDelta, fourMultiplierEffects]

/-- For the specified four-cohort effects, the frontier elimination handle is exactly
negative 11559 divided by 32000. -/
lemma fourFrontierEliminationHandle_exact :
    frontierEliminationHandle 4 fourCohortSupport fourCohortShare
      fourCohortLimitBaseline fourCohortGamma fourCohortDelta =
        -(11559 : ℝ) / 32000 := by
  have hp : frontierEliminationHandle 4 fourCohortSupport fourCohortShare
      fourCohortLimitBaseline fourCohortGamma
        (fourMultiplierEffects ((101 : ℝ) / 100) 4) =
      (5 * ((101 : ℝ) / 100) ^ 2 + 12 * ((101 : ℝ) / 100) - 2 * 4 - 15) / 16 := by
    simp [frontierEliminationHandle, primitiveTotal, primitiveTreatedTotal,
      primitiveRow, primitiveColumn, primitiveH, fourCohortSupport, fourCohortShare,
      fourCohortLimitBaseline, fourCohortGamma, fourMultiplierEffects,
      untreatedMean, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
    norm_num [Fin.sum_univ_succ]
    simp [Real.exp_log (by norm_num : (0 : ℝ) < 101 / 100),
      Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    ring
  rw [fourCohortDelta_eq_multiplier, hp]
  norm_num

/-- The four-cohort design's pseudo-true PPML treatment coefficient is negative. -/
lemma fourBetaStar_negative :
    betaStar 4 fourCohortSupport fourCohortShare fourCohortLimitBaseline
      fourCohortGamma fourCohortDelta < 0 := by
  apply (betaStar_sign_frontierEliminationHandle 4 fourCohortSupport
    fourHorizonPositive (by simp [fourCohortSupport]) fourCohortShare
    fourCohortLimitBaseline fourCohortGamma fourCohortDelta
    fourCohortCollapsedDesignRank).1.mpr
  rw [fourFrontierEliminationHandle_exact]
  norm_num

/-- Every treated cell in the four-cohort example has a strictly positive log treatment effect. -/
lemma fourCohortDelta_positive :
    ∀ g ∈ fourCohortSupport, ∀ t : Fin 4,
      treatmentIndicator 4 g t = 1 → 0 < fourCohortDelta (g, t) := by
  intro g hg t hD
  rw [fourCohortDelta, if_pos hD]
  split
  · exact Real.log_pos (by norm_num)
  · exact Real.log_pos (by norm_num)

/-- The late treated cell has a strictly larger log treatment effect than every other treated cell. -/
lemma fourCohortDelta_late_largest :
    ∀ g ∈ fourCohortSupport, ∀ t : Fin 4,
      treatmentIndicator 4 g t = 1 →
      (g, t) ≠ (fourLateCohort, fourLatePeriod) →
      fourCohortDelta (g, t) < fourCohortDelta (fourLateCohort, fourLatePeriod) := by
  intro g hg t hD hne
  have hnot : ¬(g = fourLateCohort ∧ t = fourLatePeriod) := by
    intro h
    exact hne (Prod.ext h.1 h.2)
  rw [fourCohortDelta, if_pos hD]
  have hnot' : ¬(g = ((⟨1, by decide⟩ : Fin 4) : Cohort 4) ∧
      t = (⟨3, by decide⟩ : Fin 4)) := by
    simpa [fourLateCohort, fourLatePeriod] using hnot
  rw [if_neg hnot']
  have hlateD : treatmentIndicator 4 fourLateCohort fourLatePeriod = 1 := by
    norm_num [fourLateCohort, fourLatePeriod, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq, Fin.mk_le_mk]
  rw [fourCohortDelta, if_pos hlateD, if_pos ⟨rfl, rfl⟩]
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

/-- The four-cohort primitive data satisfy all conditions defining the sign-reversal region. -/
lemma fourPrimitive_mem_signReversalRegion :
    restrictSignReversalPrimitive 4 fourCohortSupport fourCohortShare
      fourCohortLimitBaseline fourCohortGamma fourCohortDelta ∈
        signReversalRegion 4 fourCohortSupport fourCohortGamma := by
  unfold signReversalRegion
  refine ⟨(by show 4 ≤ 4; norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · simp [fourCohortSupport]
    · intro g hg
      simp only [fourCohortSupport, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with h | h | h | h <;> simp_all
  · refine ⟨⟨⟨1, by decide⟩, rfl, by simp [fourCohortSupport]⟩,
      ⟨⟨2, by decide⟩, rfl, by simp [fourCohortSupport]⟩,
      ⟨⟨3, by decide⟩, rfl, by simp [fourCohortSupport]⟩,
      by simp [fourCohortSupport]⟩
  · norm_num [restrictSignReversalPrimitive, fourCohortSupport, fourCohortShare] <;> rfl
  · refine ⟨fun _ => ⟨1, zero_lt_one⟩, ?_⟩
    intro z
    simp [restrictSignReversalPrimitive, untreatedMean, fourCohortLimitBaseline,
      fourCohortGamma]
  · intro z
    exact fourCohortDelta_positive z.1.1.1 z.1.1.2 z.1.2 z.2
  · intro a ha
    change 0 < ∑ z : SupportedCell 4 fourCohortSupport,
      ((fourCohortShare z.1.1 : ℝ) / 4) *
        collapsedIndex 4 fourCohortSupport
          (collapsedRegressor 4 fourCohortSupport z.1.1 z.2) a ^ 2
    rw [Fintype.sum_prod_type]
    have hr := fourCohortCollapsedDesignRank a ha
    rw [show (∑ z : ↑fourCohortSupport, ∑ t : Fin 4,
        ((fourCohortShare z.1 : ℝ) / 4) *
          collapsedIndex 4 fourCohortSupport
            (collapsedRegressor 4 fourCohortSupport z.1 t) a ^ 2) =
        ∑ g ∈ fourCohortSupport, ∑ t : Fin 4,
          ((fourCohortShare g : ℝ) / 4) *
            collapsedIndex 4 fourCohortSupport
              (collapsedRegressor 4 fourCohortSupport g t) a ^ 2 by
      simpa using Finset.sum_attach (s := fourCohortSupport)
        (f := fun g => ∑ t : Fin 4, ((fourCohortShare g : ℝ) / 4) *
          collapsedIndex 4 fourCohortSupport
            (collapsedRegressor 4 fourCohortSupport g t) a ^ 2)]
    simpa [limitingCellMass] using hr
  · rw [primitiveBetaStar_restrict]
    exact fourBetaStar_negative

/-- The weighted FWL residual in the designated late-treated cell is exactly negative one eighth. -/
lemma fourLateResidual_exact :
    weightedFWLResidual 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
      fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4
        fourLateSupportedCell = -(1 : ℝ) / 8 := by
  rw [fourWeightedFWLResidual_table]
  norm_num [fourLateSupportedCell, fourLateCohort, fourLatePeriod,
    fourResidualTable, fourResidualNumerator]

/-- With zero treatment effects, the weighted FWL residual energy is exactly five sixty-fourths. -/
lemma fourFWLEnergy_zeroEffects :
    fwlEnergy 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
      fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4 =
        (5 : ℝ) / 64 := by
  unfold fwlEnergy
  have hfit (z : SupportedCell 4 fourCohortSupport) :
      fittedMean 4 fourCohortSupport fourCohortShare fourCohortLimitBaseline
        fourCohortGamma zeroEffects4 z.1.1 z.2 = 1 :=
    fourFittedMean_zeroEffects z.1.1 z.1.2 z.2
  simp_rw [hfit, fourWeightedFWLResidual_table]
  rw [Fintype.sum_prod_type]
  rw [show (∑ g : ↑fourCohortSupport, ∑ t : Fin 4,
      limitingCellMass 4 fourCohortShare g.1 * 1 * fourResidualTable g.1 t ^ 2) =
      ∑ g ∈ fourCohortSupport, ∑ t : Fin 4,
        limitingCellMass 4 fourCohortShare g * 1 * fourResidualTable g t ^ 2 by
    simpa using Finset.sum_attach (s := fourCohortSupport)
      (f := fun g => ∑ t : Fin 4,
        limitingCellMass 4 fourCohortShare g * 1 * fourResidualTable g t ^ 2)]
  norm_num [fourCohortSupport, limitingCellMass, fourCohortShare,
    fourResidualTable, fourResidualNumerator, Fin.sum_univ_succ]

/-- At zero effects, increasing the late cell's log effect changes the pseudo-true PPML
treatment coefficient at the exact rate negative one tenth. -/
lemma fourLateDerivative_exact :
    HasDerivAt
      (fun x => betaStar 4 fourCohortSupport fourCohortShare fourCohortLimitBaseline
        fourCohortGamma
        (Function.update zeroEffects4 (fourLateCohort, fourLatePeriod) x))
      (-(1 : ℝ) / 10) 0 := by
  have hlateMem : fourLateCohort ∈ fourCohortSupport := by
    simp [fourLateCohort, fourCohortSupport]
  have hlateD : treatmentIndicator 4 fourLateCohort fourLatePeriod = 1 := by
    norm_num [fourLateCohort, fourLatePeriod, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq, Fin.mk_le_mk]
  have hs := (sharp_ppml_forbidden_sign 4 fourCohortSupport fourHorizonPositive
    fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma
    zeroEffects4 fourLateCohort hlateMem fourLatePeriod hlateD
    fourCohortCollapsedDesignRank).1
  convert hs using 1
  · rw [fourFWLEnergy_zeroEffects]
    have hW := fourLateResidual_exact
    change -(1 : ℝ) / 10 = limitingCellMass 4 fourCohortShare fourLateCohort *
      untreatedMean 4 fourCohortLimitBaseline fourCohortGamma fourLateCohort
        fourLatePeriod * Real.exp (zeroEffects4 (fourLateCohort, fourLatePeriod)) *
      weightedFWLResidual 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
        fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4
          (⟨fourLateCohort, hlateMem⟩, fourLatePeriod) / (5 / 64)
    rw [show weightedFWLResidual 4 fourCohortSupport fourHorizonPositive
        fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma
        zeroEffects4 (⟨fourLateCohort, hlateMem⟩, fourLatePeriod) = -1 / 8 by
      simpa [fourLateSupportedCell] using hW]
    norm_num [limitingCellMass, fourCohortShare, untreatedMean,
      fourCohortLimitBaseline, fourCohortGamma, zeroEffects4]

/-- Changing treatment effects outside the supported cohorts leaves the limiting PPML criterion
unchanged. -/
lemma limitingCriterion_congr_supported
    (T : ℕ) (C : Finset (Cohort T)) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (delta delta' : Cell T → ℝ)
    (hdelta : ∀ g ∈ C, ∀ t, delta (g, t) = delta' (g, t)) :
    limitingCriterion T C pi barB gamma delta =
      limitingCriterion T C pi barB gamma delta' := by
  funext theta
  unfold limitingCriterion
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro t ht
  rw [show observedCohortMean T barB gamma delta g t =
      observedCohortMean T barB gamma delta' g t by
    unfold observedCohortMean
    rw [hdelta g hg t]]

/-- Changing treatment effects outside the supported cohorts leaves every fitted mean unchanged. -/
lemma fittedMean_congr_supported
    (T : ℕ) (C : Finset (Cohort T)) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (delta delta' : Cell T → ℝ)
    (hdelta : ∀ g ∈ C, ∀ t, delta (g, t) = delta' (g, t))
    (g : Cohort T) (t : Fin T) :
    fittedMean T C pi barB gamma delta g t =
      fittedMean T C pi barB gamma delta' g t := by
  unfold fittedMean collapsedPopulationProjection
  rw [limitingCriterion_congr_supported T C pi barB gamma delta delta' hdelta]

/-- Changing treatment effects outside the supported cohorts leaves the weighted FWL treatment
residual unchanged. -/
lemma weightedFWLResidual_congr_supported
    (T : ℕ) (C : Finset (Cohort T)) (hT : 0 < T) (hC : C.Nonempty)
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (delta delta' : Cell T → ℝ)
    (hdelta : ∀ g ∈ C, ∀ t, delta (g, t) = delta' (g, t)) :
    weightedFWLResidual T C hT hC pi barB gamma delta =
      weightedFWLResidual T C hT hC pi barB gamma delta' := by
  have hc : meanWeightedSupport T C hT hC pi barB gamma delta =
      meanWeightedSupport T C hT hC pi barB gamma delta' := by
    unfold meanWeightedSupport
    congr 1
    funext z
    unfold meanFWLWeight
    rw [fittedMean_congr_supported T C pi barB gamma delta delta' hdelta]
  unfold weightedFWLResidual
  rw [hc]

/-- There is a neighborhood of zero effects in which positive effects still give a negative
marginal effect of the late cell on the pseudo-true PPML treatment coefficient. -/
lemma fourLateDerivative_negative_neighborhood :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ delta' : Cell 4 → ℝ,
        (∀ g ∈ fourCohortSupport, ∀ t : Fin 4, |delta' (g, t)| < epsilon) →
        StrictPositiveEffects 4 fourCohortSupport delta' →
        deriv (fun x => betaStar 4 fourCohortSupport fourCohortShare
          fourCohortLimitBaseline fourCohortGamma
          (Function.update delta' (fourLateCohort, fourLatePeriod) x))
          (delta' (fourLateCohort, fourLatePeriod)) < 0 := by
  let W : (Cell 4 → ℝ) → ℝ := fun delta =>
    weightedFWLResidual 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
      fourCohortShare fourCohortLimitBaseline fourCohortGamma delta
        fourLateSupportedCell
  have hcont : ContinuousAt W zeroEffects4 :=
    weightedFWLResidual_continuousAt_effects 4 fourCohortSupport
      fourHorizonPositive fourSupportNonempty fourCohortShare fourCohortLimitBaseline
      fourCohortGamma fourCohortCollapsedDesignRank zeroEffects4 fourLateSupportedCell
  have hWzero : W zeroEffects4 < 0 := by
    rw [show W zeroEffects4 = -(1 : ℝ) / 8 by exact fourLateResidual_exact]
    norm_num
  have hopen : Set.Iio (0 : ℝ) ∈ nhds (W zeroEffects4) :=
    IsOpen.mem_nhds isOpen_Iio hWzero
  have hpre : W ⁻¹' Set.Iio (0 : ℝ) ∈ nhds zeroEffects4 := hcont hopen
  obtain ⟨I, target, htarget, hpi⟩ :
      ∃ (I : Finset (Cell 4)) (target : Cell 4 → Set ℝ),
        (∀ i, target i ∈ nhds (zeroEffects4 i)) ∧
          Set.pi I target ⊆ W ⁻¹' Set.Iio (0 : ℝ) := by
    rw [nhds_pi, Filter.mem_pi] at hpre
    obtain ⟨s, hs, target, htarget, hpi⟩ := hpre
    exact ⟨hs.toFinset, target, htarget, by simpa using hpi⟩
  have hradius : ∀ i : Cell 4, ∃ r : ℝ, 0 < r ∧
      Metric.ball (zeroEffects4 i) r ⊆ target i := by
    intro i
    exact Metric.mem_nhds_iff.mp (htarget i)
  choose radius hradiusPos hradiusSub using hradius
  let epsilon : ℝ := if hI : I.Nonempty then
      (I.image radius).min' (hI.image radius) else 1
  have hepsilon : 0 < epsilon := by
    by_cases hI : I.Nonempty
    · rw [show epsilon = (I.image radius).min' (hI.image radius) by simp [epsilon, hI]]
      have hmem := (I.image radius).min'_mem (hI.image radius)
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
      rw [← heq]
      exact hradiusPos i
    · simp [epsilon, hI]
  have hepsilon_le (i : Cell 4) (hi : i ∈ I) : epsilon ≤ radius i := by
    have hI : I.Nonempty := ⟨i, hi⟩
    rw [show epsilon = (I.image radius).min' (hI.image radius) by simp [epsilon, hI]]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro delta' hsmall hpositive
  let deltaSupported : Cell 4 → ℝ := fun z =>
    if z.1 ∈ fourCohortSupport then delta' z else 0
  have hdeltaSupported : deltaSupported ∈ Set.pi I target := by
    intro z hzI
    apply hradiusSub z
    rw [Metric.mem_ball]
    apply lt_of_lt_of_le _ (hepsilon_le z hzI)
    by_cases hz : z.1 ∈ fourCohortSupport
    · simpa [deltaSupported, hz, zeroEffects4, Real.dist_eq] using
        hsmall z.1 hz z.2
    · simpa [deltaSupported, hz, zeroEffects4] using hepsilon
  have hWsupported : W deltaSupported < 0 := hpi hdeltaSupported
  have hcongr : weightedFWLResidual 4 fourCohortSupport fourHorizonPositive
      fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma
      delta' = weightedFWLResidual 4 fourCohortSupport fourHorizonPositive
        fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma
        deltaSupported := by
    apply weightedFWLResidual_congr_supported
    intro g hg t
    simp [deltaSupported, hg]
  have hWneg : weightedFWLResidual 4 fourCohortSupport fourHorizonPositive
      fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma
      delta' fourLateSupportedCell < 0 := by
    rw [hcongr]
    exact hWsupported
  have hlateMem : fourLateCohort ∈ fourCohortSupport := by
    simp [fourLateCohort, fourCohortSupport]
  have hlateD : treatmentIndicator 4 fourLateCohort fourLatePeriod = 1 := by
    norm_num [fourLateCohort, fourLatePeriod, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq, Fin.mk_le_mk]
  have hs := sharp_ppml_forbidden_sign 4 fourCohortSupport fourHorizonPositive
    fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma
    delta' fourLateCohort hlateMem fourLatePeriod hlateD
    fourCohortCollapsedDesignRank
  have hWneg' : weightedFWLResidual 4 fourCohortSupport fourHorizonPositive
      fourSupportNonempty fourCohortShare fourCohortLimitBaseline fourCohortGamma
      delta' (⟨fourLateCohort, hlateMem⟩, fourLatePeriod) < 0 := by
    simpa [fourLateSupportedCell] using hWneg
  have hformulaNeg := hs.2.2.1.mpr hWneg'
  rw [hs.1.deriv]
  exact hformulaNeg

-- @node: prop:four-cohort-sign-reversal
/-- W4 is an all-positive sign reversal and has the stated negative late-cell derivative. -/
theorem four_cohort_sign_reversal :
    restrictSignReversalPrimitive 4 fourCohortSupport fourCohortShare
      fourCohortLimitBaseline fourCohortGamma fourCohortDelta ∈
        signReversalRegion 4 fourCohortSupport fourCohortGamma ∧
    (∀ g ∈ fourCohortSupport, ∀ t : Fin 4,
      treatmentIndicator 4 g t = 1 → 0 < fourCohortDelta (g, t)) ∧
    (∀ g ∈ fourCohortSupport, ∀ t : Fin 4,
      treatmentIndicator 4 g t = 1 →
      (g, t) ≠ (fourLateCohort, fourLatePeriod) →
      fourCohortDelta (g, t) <
        fourCohortDelta (fourLateCohort, fourLatePeriod)) ∧
    (∀ z : SupportedCell 4 fourCohortSupport,
      weightedFWLResidual 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
        fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4
        z = fourResidualTable z.1.1 z.2) ∧
    weightedFWLResidual 4 fourCohortSupport fourHorizonPositive fourSupportNonempty
      fourCohortShare fourCohortLimitBaseline fourCohortGamma zeroEffects4
      fourLateSupportedCell = -(1 : ℝ) / 8 ∧
    HasDerivAt
      (fun x => betaStar 4 fourCohortSupport fourCohortShare fourCohortLimitBaseline
        fourCohortGamma
        (Function.update zeroEffects4 (fourLateCohort, fourLatePeriod) x))
      (-(1 : ℝ) / 10) 0 ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ delta' : Cell 4 → ℝ,
        (∀ g ∈ fourCohortSupport, ∀ t : Fin 4, |delta' (g, t)| < epsilon) →
        StrictPositiveEffects 4 fourCohortSupport delta' →
        deriv (fun x => betaStar 4 fourCohortSupport fourCohortShare fourCohortLimitBaseline
          fourCohortGamma
          (Function.update delta' (fourLateCohort, fourLatePeriod) x))
          (delta' (fourLateCohort, fourLatePeriod)) < 0 := by
  exact ⟨fourPrimitive_mem_signReversalRegion, fourCohortDelta_positive,
    fourCohortDelta_late_largest, fourWeightedFWLResidual_table,
    fourLateResidual_exact, fourLateDerivative_exact,
    fourLateDerivative_negative_neighborhood⟩

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
