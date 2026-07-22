/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: latent type table

Introduces the 16-cell latent type partition `(D(0),D(1),Y(0),Y(1)) ∈ Bool⁴`
and proves:
1. `measurableSet_latentSet`   — each cell is measurable.
2. `latentProb_nonneg`         — cell probabilities are nonneg.
3. `latentProb_sum_eq_one`     — the 16 cells partition Ω (sum = 1).
4. `ATE_eq_sum_latent`         — ATE = ∑ (y1-y0) * latentProb.
5. `cellProb_eq_sum_latent`    — observed cell probs = weighted sum over
                                  compatible latent types.
-/

import Causalean.PO.ID.Partial.BalkePearl.Assumptions

/-! # Balke-Pearl Latent Table

This file defines the 16-cell latent type table for Balke-Pearl bounds and
relates it to the average treatment effect and observed conditional cell
probabilities. The latent cells partition the population by the two treatment
potential outcomes and the two outcome potential outcomes. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### Helper selectors -/

/-- The treatment arm under instrument value z: d₀ if z=false, d₁ if z=true. -/
def dArm (z d0 d1 : Bool) : Bool := if z then d1 else d0

/-- The outcome arm under treatment d: y₀ if d=false, y₁ if d=true. -/
def yArm (d y0 y1 : Bool) : Bool := if d then y1 else y0

/-! ### Latent set and probability -/

/-- The event that unit ω has latent type (d0,d1,y0,y1). -/
def latentSet (d0 d1 y0 y1 : Bool) : Set P.Ω :=
  {ω | S.DofZ false ω = d0 ∧ S.DofZ true ω = d1
        ∧ S.YofD false ω = y0 ∧ S.YofD true ω = y1}

/-- Probability of the latent type (d0,d1,y0,y1). -/
noncomputable def latentProb (d0 d1 y0 y1 : Bool) : ℝ :=
  (P.μ (S.latentSet d0 d1 y0 y1)).toReal

/-! ### Easy lemmas -/

/-- Each latent type event is measurable. -/
lemma measurableSet_latentSet (d0 d1 y0 y1 : Bool) :
    MeasurableSet (S.latentSet d0 d1 y0 y1) := by
  show MeasurableSet
    ({a | S.DofZ false a = d0} ∩
      ({a | S.DofZ true a = d1} ∩
        ({a | S.YofD false a = y0} ∩ {a | S.YofD true a = y1})))
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · exact S.measurable_DofZ false (measurableSet_singleton d0)
  · exact S.measurable_DofZ true (measurableSet_singleton d1)
  · exact S.measurable_YofD false (measurableSet_singleton y0)
  · exact S.measurable_YofD true (measurableSet_singleton y1)

/-- Latent type probabilities are nonnegative. -/
lemma latentProb_nonneg (d0 d1 y0 y1 : Bool) : 0 ≤ S.latentProb d0 d1 y0 y1 :=
  ENNReal.toReal_nonneg

/-! ### Partition lemmas -/

/-- The 16 latent sets are pairwise disjoint. -/
private lemma latentSet_disjoint {d0 d1 y0 y1 d0' d1' y0' y1' : Bool}
    (hne : (d0, d1, y0, y1) ≠ (d0', d1', y0', y1')) :
    Disjoint (S.latentSet d0 d1 y0 y1) (S.latentSet d0' d1' y0' y1') := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  apply hne
  obtain ⟨hd0, hd1, hy0, hy1⟩ := h1
  obtain ⟨hd0', hd1', hy0', hy1'⟩ := h2
  simp_all

-- Flat covering using Bool × Bool × Bool × Bool
private lemma latentSet_iUnion_prod_eq_univ :
    ⋃ i : Bool × Bool × Bool × Bool,
      S.latentSet i.1 i.2.1 i.2.2.1 i.2.2.2 = Set.univ := by
  ext ω; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨⟨S.DofZ false ω, S.DofZ true ω, S.YofD false ω, S.YofD true ω⟩,
    rfl, rfl, rfl, rfl⟩

/-- The 16 latent sets partition Ω, so their probabilities sum to 1. -/
lemma latentProb_sum_eq_one :
    ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        S.latentProb d0 d1 y0 y1 = 1 := by
  -- Work with flat index type.
  set f : Bool × Bool × Bool × Bool → Set P.Ω :=
    fun i => S.latentSet i.1 i.2.1 i.2.2.1 i.2.2.2
  have hmeas : ∀ i : Bool × Bool × Bool × Bool, MeasurableSet (f i) :=
    fun ⟨d0, d1, y0, y1⟩ => S.measurableSet_latentSet d0 d1 y0 y1
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro ⟨d0, d1, y0, y1⟩ ⟨d0', d1', y0', y1'⟩ hne
    apply S.latentSet_disjoint
    intro h; exact absurd h hne
  have hcov : ⋃ i : Bool × Bool × Bool × Bool, f i = Set.univ :=
    S.latentSet_iUnion_prod_eq_univ
  -- Sum of ENNReal measures = 1.
  have hENNsum : ∑ i : Bool × Bool × Bool × Bool, P.μ (f i) = 1 := by
    have h1 := measure_iUnion (μ := P.μ) hdisj hmeas
    rw [hcov, measure_univ] at h1
    rw [tsum_fintype] at h1
    exact h1.symm
  -- Take .toReal of hENNsum using additivity.
  have hne_top : ∀ i : Bool × Bool × Bool × Bool, P.μ (f i) ≠ ⊤ :=
    fun i => measure_ne_top _ _
  have hreal : ∑ i : Bool × Bool × Bool × Bool, (P.μ (f i)).toReal = 1 := by
    have := congr_arg ENNReal.toReal hENNsum
    rw [ENNReal.toReal_sum (fun i _ => hne_top i)] at this
    simpa using this
  -- The nested sum equals the flat sum (latentProb = (P.μ (f ·)).toReal).
  have hflat : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      S.latentProb d0 d1 y0 y1
      = ∑ i : Bool × Bool × Bool × Bool, (P.μ (f i)).toReal := by
    simp only [latentProb, f, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hflat, hreal]

/-! ### ATE as sum over latent types -/

private lemma integrable_YofD_real_sub :
    Integrable (fun ω => S.YofD_real true ω - S.YofD_real false ω) P.μ := by
  apply Integrable.sub
  all_goals {
    apply MeasureTheory.Integrable.of_bound (C := 1)
      (S.measurable_YofD_real _).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    simp only [YofD_real, Function.comp, boolToReal]
    cases S.YofD _ ω <;> norm_num
  }

/-- The average treatment effect is the weighted sum of treatment effects over
the 16 latent types.

ATE = ∑_{d0,d1,y0,y1} (boolToReal y1 - boolToReal y0) * latentProb d0 d1 y0 y1 -/
theorem ATE_eq_sum_latent :
    S.ATE = ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (boolToReal y1 - boolToReal y0) * S.latentProb d0 d1 y0 y1 := by
  unfold ATE
  set f : Bool × Bool × Bool × Bool → Set P.Ω :=
    fun i => S.latentSet i.1 i.2.1 i.2.2.1 i.2.2.2
  have hmeas : ∀ i : Bool × Bool × Bool × Bool, MeasurableSet (f i) :=
    fun ⟨d0, d1, y0, y1⟩ => S.measurableSet_latentSet d0 d1 y0 y1
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro ⟨d0, d1, y0, y1⟩ ⟨d0', d1', y0', y1'⟩ hne
    apply S.latentSet_disjoint
    intro h; exact absurd h hne
  have hcov : ⋃ i : Bool × Bool × Bool × Bool, f i = Set.univ :=
    S.latentSet_iUnion_prod_eq_univ
  have hint := S.integrable_YofD_real_sub
  -- Partition the integral over the 16 cells.
  have hsplit :
      ∫ ω, (S.YofD_real true ω - S.YofD_real false ω) ∂P.μ
        = ∑ i : Bool × Bool × Bool × Bool,
            ∫ ω in f i, (S.YofD_real true ω - S.YofD_real false ω) ∂P.μ := by
    rw [← setIntegral_univ, ← hcov,
        integral_iUnion_fintype hmeas hdisj (fun i => hint.integrableOn)]
  rw [hsplit]
  -- On each cell the integrand is constant = boolToReal y1 - boolToReal y0.
  have hconst : ∀ (d0 d1 y0 y1 : Bool) ω,
      ω ∈ S.latentSet d0 d1 y0 y1 →
        S.YofD_real true ω - S.YofD_real false ω = boolToReal y1 - boolToReal y0 := by
    intro d0 d1 y0 y1 ω ⟨_, _, hy0, hy1⟩
    simp [YofD_real, hy0, hy1]
  -- Each set integral = constant * latentProb.
  have hcell : ∀ (d0 d1 y0 y1 : Bool),
      ∫ ω in S.latentSet d0 d1 y0 y1, (S.YofD_real true ω - S.YofD_real false ω) ∂P.μ
        = (boolToReal y1 - boolToReal y0) * S.latentProb d0 d1 y0 y1 := by
    intro d0 d1 y0 y1
    rw [MeasureTheory.setIntegral_congr_fun (S.measurableSet_latentSet d0 d1 y0 y1)
          (fun ω hω => hconst d0 d1 y0 y1 ω hω),
        MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, latentProb, measureReal_def]
    ring
  -- Combine flat and nested sums.
  have hflat : ∀ i : Bool × Bool × Bool × Bool,
      ∫ ω in f i, (S.YofD_real true ω - S.YofD_real false ω) ∂P.μ
        = (boolToReal i.2.2.2 - boolToReal i.2.2.1) * S.latentProb i.1 i.2.1 i.2.2.1 i.2.2.2 :=
    fun ⟨d0, d1, y0, y1⟩ => hcell d0 d1 y0 y1
  simp_rw [hflat, Fintype.sum_prod_type]

/-! ### Observed cell probabilities vs latent types -/

/-- The "cf-cell" event `E_{z,d,y} = {DofZ z = d ∧ YofD d = y}`. -/
private def cfCellEvent (z d y : Bool) : Set P.Ω :=
  {ω | S.DofZ z ω = d ∧ S.YofD d ω = y}

private lemma measurableSet_cfCellEvent (z d y : Bool) :
    MeasurableSet (S.cfCellEvent z d y) := by
  refine MeasurableSet.inter ?_ ?_
  · exact (S.measurable_DofZ z) (measurableSet_singleton d)
  · exact (S.measurable_YofD d) (measurableSet_singleton y)

/-- Step 1 (IV-specific consistency): on `{Z=z}`, the factual cell agrees with the
counterfactual cell `E_{z,d,y}`. -/
private lemma zEvent_inter_cell_eq (hA : S.BaseAssumptions) (z d y : Bool) :
    S.zEvent z ∩ S.yEvent y ∩ S.dEvent d
      = S.zEvent z ∩ S.cfCellEvent z d y := by
  ext ω
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨hZω, hYω⟩, hDω⟩
    refine ⟨hZω, ?_, ?_⟩
    · have := hA.consistency_D z hZω
      change S.DofZ z ω = d
      rw [this]
      exact hDω
    · have hDfact : S.dVar.factual ω = d := hDω
      have := hA.consistency_Y d hDfact
      change S.YofD d ω = y
      rw [this]
      exact hYω
  · rintro ⟨hZω, hDcf, hYcf⟩
    have hDω : S.dVar.factual ω = d := by
      have := hA.consistency_D z hZω
      change S.factualD ω = d
      rw [← this]; exact hDcf
    have hYω : S.yVar.factual ω = y := by
      have := hA.consistency_Y d hDω
      change S.factualY ω = y
      rw [← this]; exact hYcf
    exact ⟨⟨hZω, hYω⟩, hDω⟩

/-- The product map `(D(0), D(1), Y(0), Y(1)) : Ω → Bool⁴`.  Equals
`ψ ∘ cfBundle.jointValue` for the obvious selector `ψ`, hence inherits
independence from `Z` via `IndepCF.project`. -/
private noncomputable def cfTuple : P.Ω → Bool × Bool × Bool × Bool :=
  fun ω => (S.DofZ false ω, S.DofZ true ω, S.YofD false ω, S.YofD true ω)

private lemma indepFun_factualZ_cfTuple (hA : S.BaseAssumptions) :
    ProbabilityTheory.IndepFun S.factualZ S.cfTuple P.μ := by
  let ψ : (∀ i : Fin 4, S.cfBundle.type i) → Bool × Bool × Bool × Bool :=
    fun f => (f 0, f 1, f 2, f 3)
  have hψmeas : Measurable ψ := by
    refine Measurable.prodMk (measurable_pi_apply _) ?_
    refine Measurable.prodMk (measurable_pi_apply _) ?_
    exact Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
  have hcomp : ψ ∘ S.cfBundle.jointValue = S.cfTuple := rfl
  have h := hA.exogeneity.project (ψ := ψ) hψmeas
  simpa [hcomp] using h

/-- The cf-cell as a preimage of `cfTuple`. -/
private lemma cfCellEvent_eq_preimage (z d y : Bool) :
    S.cfCellEvent z d y
      = S.cfTuple ⁻¹' {p | dArm z p.1 p.2.1 = d ∧ yArm d p.2.2.1 p.2.2.2 = y} := by
  ext ω
  unfold cfCellEvent cfTuple dArm yArm
  cases z <;> cases d <;> simp

/-- The 4 cf-tuple coordinates evaluated on `latentSet`. -/
private lemma cfTuple_on_latentSet (d0 d1 y0 y1 : Bool) {ω : P.Ω}
    (hω : ω ∈ S.latentSet d0 d1 y0 y1) :
    S.cfTuple ω = (d0, d1, y0, y1) := by
  obtain ⟨h0, h1, h2, h3⟩ := hω
  simp [cfTuple, h0, h1, h2, h3]

/-- Each observed conditional cell probability equals the sum of compatible
latent type probabilities. -/
theorem cellProb_eq_sum_latent (hA : S.BaseAssumptions) (y d z : Bool) :
    S.cellProb y d z
      = ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
          (if dArm z d0 d1 = d ∧ yArm d y0 y1 = y then 1 else 0)
            * S.latentProb d0 d1 y0 y1 := by
  -- Abbreviations.
  set E : Set P.Ω := S.cfCellEvent z d y with hE
  set T : Set (Bool × Bool × Bool × Bool) :=
    {p | dArm z p.1 p.2.1 = d ∧ yArm d p.2.2.1 p.2.2.2 = y} with hT
  have hEpre : E = S.cfTuple ⁻¹' T := S.cfCellEvent_eq_preimage z d y
  have hT_meas : MeasurableSet T := (Set.toFinite T).measurableSet
  have hE_meas : MeasurableSet E := S.measurableSet_cfCellEvent z d y
  -- Step 1: consistency gives the set equality on numerator.
  have h1 : S.zEvent z ∩ S.yEvent y ∩ S.dEvent d = S.zEvent z ∩ E :=
    S.zEvent_inter_cell_eq hA z d y
  -- Step 2: exogeneity factorization.
  have hindep : ProbabilityTheory.IndepFun S.factualZ S.cfTuple P.μ :=
    S.indepFun_factualZ_cfTuple hA
  have hZeqEv : S.zEvent z = S.factualZ ⁻¹' {z} := rfl
  have h2 : P.μ (S.zEvent z ∩ E) = P.μ (S.zEvent z) * P.μ E := by
    rw [hEpre, hZeqEv]
    exact hindep.measure_inter_preimage_eq_mul {z} T (measurableSet_singleton _) hT_meas
  -- Step 3: decompose μ(E) over 16 latent cells.
  set fset : Bool × Bool × Bool × Bool → Set P.Ω :=
    fun i => S.latentSet i.1 i.2.1 i.2.2.1 i.2.2.2 with hfset
  have hmeas : ∀ i, MeasurableSet (fset i) :=
    fun ⟨d0, d1, y0, y1⟩ => S.measurableSet_latentSet d0 d1 y0 y1
  have hdisj : Pairwise (Function.onFun Disjoint fset) := by
    intro ⟨d0, d1, y0, y1⟩ ⟨d0', d1', y0', y1'⟩ hne
    apply S.latentSet_disjoint; intro h; exact absurd h hne
  have hcov : ⋃ i, fset i = Set.univ := S.latentSet_iUnion_prod_eq_univ
  -- Express μ(E) as a sum over latent cells.
  have hE_decomp : P.μ E
      = ∑ i : Bool × Bool × Bool × Bool,
          (if dArm z i.1 i.2.1 = d ∧ yArm d i.2.2.1 i.2.2.2 = y then 1 else 0)
            * P.μ (fset i) := by
    -- E = E ∩ univ = E ∩ ⋃ fset = ⋃ (E ∩ fset i), and disjoint.
    have hE_union : E = ⋃ i, E ∩ fset i := by
      rw [← Set.inter_iUnion, hcov, Set.inter_univ]
    have hdisj' : Pairwise (Function.onFun Disjoint (fun i => E ∩ fset i)) := by
      intro i j hij
      exact (hdisj hij).inter_left' E |>.inter_right' E
    have hmeas' : ∀ i, MeasurableSet (E ∩ fset i) := fun i => hE_meas.inter (hmeas i)
    have hμsum : P.μ E = ∑ i, P.μ (E ∩ fset i) := by
      conv_lhs => rw [hE_union]
      rw [measure_iUnion hdisj' hmeas', tsum_fintype]
    -- For each i, E ∩ fset i = fset i if compatible, else ∅.
    have hcell : ∀ i, P.μ (E ∩ fset i)
        = (if dArm z i.1 i.2.1 = d ∧ yArm d i.2.2.1 i.2.2.2 = y then 1 else 0)
            * P.μ (fset i) := by
      rintro ⟨d0, d1, y0, y1⟩
      by_cases hcompat : dArm z d0 d1 = d ∧ yArm d y0 y1 = y
      · -- E ⊇ fset (d0,d1,y0,y1): on latentSet, cfTuple = (d0,d1,y0,y1) and that point ∈ T.
        have hsub : fset (d0, d1, y0, y1) ⊆ E := by
          intro ω hω
          rw [hEpre]
          change S.cfTuple ω ∈ T
          rw [S.cfTuple_on_latentSet d0 d1 y0 y1 hω]
          exact hcompat
        rw [Set.inter_eq_right.mpr hsub]
        simp [hcompat]
      · -- Disjoint: cfTuple = (d0,d1,y0,y1) ∉ T on latentSet.
        have hdisjE : Disjoint E (fset (d0, d1, y0, y1)) := by
          rw [Set.disjoint_right]
          intro ω hω hωE
          rw [hEpre] at hωE
          have : S.cfTuple ω ∈ T := hωE
          rw [S.cfTuple_on_latentSet d0 d1 y0 y1 hω] at this
          exact hcompat this
        rw [Set.disjoint_iff_inter_eq_empty.mp hdisjE]
        simp [hcompat]
    rw [hμsum]
    exact Finset.sum_congr rfl (fun i _ => hcell i)
  -- Combine: numerator = μ(Z=z) * μ(E).
  have hnum : P.μ (S.zEvent z ∩ S.yEvent y ∩ S.dEvent d) = P.μ (S.zEvent z) * P.μ E := by
    rw [h1, h2]
  -- Now go to ℝ via .toReal.
  unfold cellProb
  rw [hnum, ENNReal.toReal_mul]
  rw [hE_decomp]
  -- Convert sum-toReal and divide.
  have hpZne : (P.μ (S.zEvent z)).toReal ≠ 0 := hA.posZ_toReal_pos z |>.ne'
  rw [mul_div_cancel_left₀ _ hpZne]
  -- Now show: (∑ i, indicator * μ(fset i)).toReal = ∑ ... * latentProb.
  have hne_top : ∀ i : Bool × Bool × Bool × Bool,
      (if dArm z i.1 i.2.1 = d ∧ yArm d i.2.2.1 i.2.2.2 = y then (1 : ENNReal) else 0)
        * P.μ (fset i) ≠ ⊤ := by
    intro i
    by_cases h : dArm z i.1 i.2.1 = d ∧ yArm d i.2.2.1 i.2.2.2 = y
    · simp [h, measure_ne_top]
    · simp [h]
  rw [ENNReal.toReal_sum (fun i _ => hne_top i)]
  -- Flatten Bool × Bool × Bool × Bool sum into nested Bool sums.
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun d0 _ => ?_)
  refine Finset.sum_congr rfl (fun d1 _ => ?_)
  refine Finset.sum_congr rfl (fun y0 _ => ?_)
  refine Finset.sum_congr rfl (fun y1 _ => ?_)
  simp only [fset, latentProb]
  by_cases hcompat : dArm z d0 d1 = d ∧ yArm d y0 y1 = y
  · simp [hcompat]
  · simp [hcompat]

end POBalkePearlSystem

end PO
end Causalean
