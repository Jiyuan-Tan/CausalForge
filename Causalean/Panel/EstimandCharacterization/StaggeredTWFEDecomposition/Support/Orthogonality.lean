/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021) Layer B: per-axis orthogonality

For the saturated cohort + period class, orthogonality of a residual
against `panelClass` reduces (by `integral_mul_panelClass_eq_zero_of_axes`)
to orthogonality against every cohort indicator and every period
indicator.

This file proves the per-axis orthogonality lemmas for the residuals of
`D` and `Y` against their `panelPropensity` / `panelMeanReg` projections.
**The cohort-axis orthogonality is automatic from the defining identity
of `cohortBarD`; the period-axis orthogonality requires the balanced-cell
hypothesis `B_balanced : cellMass = cohortMass · periodMass`** to make the
cross-cohort sum collapse to `E[D]`.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Support.Integrals

/-! # Goodman-Bacon Bridge Orthogonality

This file proves the cohort-axis and period-axis orthogonality conditions needed
for the measure-theoretic Goodman-Bacon bridge. Under the balanced cell-mass
product condition, residuals from the panel propensity and mean regressions are
orthogonal to the saturated cohort and period indicator class. -/

namespace Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

variable {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢] [DecidableEq 𝒢]
  [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] {T : ℕ}

/-- The "balanced cell-mass product" hypothesis. Says the joint law of
`(G, T_rv)` factors as a product on each cohort × period cell:

    cellMass μ G T_rv g t = cohortMass μ G g · periodMass μ T_rv t

This is the Lean form of Goodman-Bacon (2021)'s balanced-panel assumption
`ℙ(G = g, T = t) = p_g · q_t`. Listed as `B_balanced` in the residWitness /
bridge theorem signatures. -/
def IsBalancedPanelLaw (μ : Measure Ω) (G : Ω → 𝒢) (T_rv : Ω → Fin T) : Prop :=
  ∀ g t, cellMass μ G T_rv g t = cohortMass μ G g * periodMass μ T_rv t

private theorem memLp_two_of_binary
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Ω → ℝ)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) :
    MemLp D 2 μ := by
  have hD_bounded : ∀ᵐ ω ∂μ, D ω ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [D_binary] with ω hD
    rcases hD with hD0 | hD1
    · simp [hD0]
    · simp [hD1]
  exact memLp_of_bounded (f := D) hD_bounded
    D_meas.aestronglyMeasurable (2 : ENNReal)

private theorem integral_cohort_sum_mul_cohort_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → 𝒢) (G_meas : Measurable G)
    (a : 𝒢 → ℝ) (g : 𝒢) :
    ∫ ω, (∑ g', a g'
          * Set.indicator {ω' | G ω' = g'} (fun _ => (1 : ℝ)) ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ
      = a g * cohortMass μ G g := by
  let I : 𝒢 → Ω → ℝ := fun g ω =>
    Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω
  let term : 𝒢 → Ω → ℝ := fun g' ω => (a g' * I g' ω) * I g ω
  have hterm_int : ∀ g' ∈ (Finset.univ : Finset 𝒢), Integrable (term g') μ := by
    intro g' _
    have hI' : MemLp (I g') 2 μ := by
      simpa [I] using indicator_cohort_memLp μ G G_meas g'
    have hI : MemLp (I g) 2 μ := by
      simpa [I] using indicator_cohort_memLp μ G G_meas g
    have haI' : MemLp (fun ω => a g' * I g' ω) 2 μ := by
      simpa using hI'.const_mul (a g')
    simpa [term] using haI'.integrable_mul hI
  have hterm_eval : ∀ g', ∫ ω, term g' ω ∂μ =
      if g' = g then a g * cohortMass μ G g else 0 := by
    intro g'
    by_cases hgg : g' = g
    · subst g'
      simp only [eq_self, ↓reduceIte]
      calc
        ∫ ω, term g ω ∂μ = ∫ ω, a g * I g ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          by_cases hω : G ω = g <;> simp [term, I, Set.indicator, hω]
        _ = a g * cohortMass μ G g := by
          rw [integral_const_mul]
          simp [I, integral_cohort_indicator_one_eq_cohortMass μ G G_meas g]
    · have hzero : term g' =ᵐ[μ] 0 := by
        filter_upwards [] with ω
        by_cases hω : G ω = g'
        · have hnot : ¬ G ω = g := by
            intro hg
            exact hgg (hω.symm.trans hg)
          have hIzero : I g ω = 0 := by
            simp [I, Set.indicator, hnot]
          have hIone : I g' ω = 1 := by
            simp [I, Set.indicator, hω]
          simp [term, hIzero, hIone]
        · have hIzero : I g' ω = 0 := by
            simp [I, Set.indicator, hω]
          simp [term, hIzero]
      simp [hgg, integral_eq_zero_of_ae hzero]
  calc
    ∫ ω, (∑ g', a g' * I g' ω) * I g ω ∂μ
        = ∫ ω, ∑ g', term g' ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          simp [term, Finset.sum_mul]
    _ = ∑ g', ∫ ω, term g' ω ∂μ := by
          simpa using
            (MeasureTheory.integral_finset_sum
              (Finset.univ : Finset 𝒢) (f := term) hterm_int)
    _ = ∑ g', (if g' = g then a g * cohortMass μ G g else 0) := by
          exact Finset.sum_congr rfl (fun g' _ => hterm_eval g')
    _ = a g * cohortMass μ G g := by
          rw [Finset.sum_eq_single g]
          · simp
          · intro b _ hbg
            simp [hbg]
          · intro hg
            exact False.elim (hg (Finset.mem_univ _))

private theorem integral_period_sum_mul_period_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T_rv : Ω → Fin T) (T_meas : Measurable T_rv)
    (b : Fin T → ℝ) (t : Fin T) :
    ∫ ω, (∑ t', b t'
          * Set.indicator {ω' | T_rv ω' = t'} (fun _ => (1 : ℝ)) ω)
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ
      = b t * periodMass μ T_rv t := by
  let I : Fin T → Ω → ℝ := fun t ω =>
    Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω
  let term : Fin T → Ω → ℝ := fun t' ω => (b t' * I t' ω) * I t ω
  have hterm_int :
      ∀ t' ∈ (Finset.univ : Finset (Fin T)), Integrable (term t') μ := by
    intro t' _
    have hI' : MemLp (I t') 2 μ := by
      simpa [I] using indicator_period_memLp μ T_rv T_meas t'
    have hI : MemLp (I t) 2 μ := by
      simpa [I] using indicator_period_memLp μ T_rv T_meas t
    have hbI' : MemLp (fun ω => b t' * I t' ω) 2 μ := by
      simpa using hI'.const_mul (b t')
    simpa [term] using hbI'.integrable_mul hI
  have hterm_eval : ∀ t', ∫ ω, term t' ω ∂μ =
      if t' = t then b t * periodMass μ T_rv t else 0 := by
    intro t'
    by_cases htt : t' = t
    · subst t'
      simp only [eq_self, ↓reduceIte]
      calc
        ∫ ω, term t ω ∂μ = ∫ ω, b t * I t ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          by_cases hω : T_rv ω = t <;> simp [term, I, Set.indicator, hω]
        _ = b t * periodMass μ T_rv t := by
          rw [integral_const_mul]
          simp [I, integral_period_indicator_one_eq_periodMass μ T_rv T_meas t]
    · have hzero : term t' =ᵐ[μ] 0 := by
        filter_upwards [] with ω
        by_cases hω : T_rv ω = t'
        · have hnot : ¬ T_rv ω = t := by
            intro ht
            exact htt (hω.symm.trans ht)
          have hIzero : I t ω = 0 := by
            simp [I, Set.indicator, hnot]
          have hIone : I t' ω = 1 := by
            simp [I, Set.indicator, hω]
          simp [term, hIzero, hIone]
        · have hIzero : I t' ω = 0 := by
            simp [I, Set.indicator, hω]
          simp [term, hIzero]
      simp [htt, integral_eq_zero_of_ae hzero]
  calc
    ∫ ω, (∑ t', b t' * I t' ω) * I t ω ∂μ
        = ∫ ω, ∑ t', term t' ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          simp [term, Finset.sum_mul]
    _ = ∑ t', ∫ ω, term t' ω ∂μ := by
          simpa using
            (MeasureTheory.integral_finset_sum
              (Finset.univ : Finset (Fin T)) (f := term) hterm_int)
    _ = ∑ t', (if t' = t then b t * periodMass μ T_rv t else 0) := by
          exact Finset.sum_congr rfl (fun t' _ => hterm_eval t')
    _ = b t * periodMass μ T_rv t := by
          rw [Finset.sum_eq_single t]
          · simp
          · intro b' _ hbt
            simp [hbt]
          · intro ht
            exact False.elim (ht (Finset.mem_univ _))

private theorem integral_period_sum_mul_cohort_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (b : Fin T → ℝ) (g : 𝒢) :
    ∫ ω, (∑ t, b t
          * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ
      = ∑ t, b t * cellMass μ G T_rv g t := by
  let IG : Ω → ℝ := fun ω =>
    Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω
  let IT : Fin T → Ω → ℝ := fun t ω =>
    Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω
  let term : Fin T → Ω → ℝ := fun t ω => (b t * IT t ω) * IG ω
  have hterm_int :
      ∀ t ∈ (Finset.univ : Finset (Fin T)), Integrable (term t) μ := by
    intro t _
    have hIT : MemLp (IT t) 2 μ := by
      simpa [IT] using indicator_period_memLp μ T_rv T_meas t
    have hIG : MemLp IG 2 μ := by
      simpa [IG] using indicator_cohort_memLp μ G G_meas g
    have hbIT : MemLp (fun ω => b t * IT t ω) 2 μ := by
      simpa using hIT.const_mul (b t)
    simpa [term] using hbIT.integrable_mul hIG
  have hterm_eval : ∀ t, ∫ ω, term t ω ∂μ =
      b t * cellMass μ G T_rv g t := by
    intro t
    calc
      ∫ ω, term t ω ∂μ
          = ∫ ω, b t
              * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                  (fun _ => (1 : ℝ)) ω ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [] with ω
            by_cases hGω : G ω = g
            · by_cases hTω : T_rv ω = t <;>
                simp [term, IG, IT, Set.indicator, hGω, hTω]
            · simp [term, IG, IT, Set.indicator, hGω]
      _ = b t * cellMass μ G T_rv g t := by
            rw [integral_const_mul]
            simp [integral_panel_cell_indicator_one_eq_cellMass
              μ G T_rv G_meas T_meas g t]
  calc
    ∫ ω, (∑ t, b t * IT t ω) * IG ω ∂μ
        = ∫ ω, ∑ t, term t ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          simp [term, Finset.sum_mul]
    _ = ∑ t, ∫ ω, term t ω ∂μ := by
          simpa using
            (MeasureTheory.integral_finset_sum
              (Finset.univ : Finset (Fin T)) (f := term) hterm_int)
    _ = ∑ t, b t * cellMass μ G T_rv g t := by
          exact Finset.sum_congr rfl (fun t _ => hterm_eval t)

private theorem integral_cohort_sum_mul_period_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (a : 𝒢 → ℝ) (t : Fin T) :
    ∫ ω, (∑ g, a g
          * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ
      = ∑ g, a g * cellMass μ G T_rv g t := by
  let IG : 𝒢 → Ω → ℝ := fun g ω =>
    Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω
  let IT : Ω → ℝ := fun ω =>
    Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω
  let term : 𝒢 → Ω → ℝ := fun g ω => (a g * IG g ω) * IT ω
  have hterm_int : ∀ g ∈ (Finset.univ : Finset 𝒢), Integrable (term g) μ := by
    intro g _
    have hIG : MemLp (IG g) 2 μ := by
      simpa [IG] using indicator_cohort_memLp μ G G_meas g
    have hIT : MemLp IT 2 μ := by
      simpa [IT] using indicator_period_memLp μ T_rv T_meas t
    have haIG : MemLp (fun ω => a g * IG g ω) 2 μ := by
      simpa using hIG.const_mul (a g)
    simpa [term] using haIG.integrable_mul hIT
  have hterm_eval : ∀ g, ∫ ω, term g ω ∂μ =
      a g * cellMass μ G T_rv g t := by
    intro g
    calc
      ∫ ω, term g ω ∂μ
          = ∫ ω, a g
              * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                  (fun _ => (1 : ℝ)) ω ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [] with ω
            by_cases hGω : G ω = g
            · by_cases hTω : T_rv ω = t <;>
                simp [term, IG, IT, Set.indicator, hGω, hTω]
            · simp [term, IG, IT, Set.indicator, hGω]
      _ = a g * cellMass μ G T_rv g t := by
            rw [integral_const_mul]
            simp [integral_panel_cell_indicator_one_eq_cellMass
              μ G T_rv G_meas T_meas g t]
  calc
    ∫ ω, (∑ g, a g * IG g ω) * IT ω ∂μ
        = ∫ ω, ∑ g, term g ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          simp [term, Finset.sum_mul]
    _ = ∑ g, ∫ ω, term g ω ∂μ := by
          simpa using
            (MeasureTheory.integral_finset_sum
              (Finset.univ : Finset 𝒢) (f := term) hterm_int)
    _ = ∑ g, a g * cellMass μ G T_rv g t := by
          exact Finset.sum_congr rfl (fun g _ => hterm_eval g)

private theorem sum_periodMass_eq_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T_rv : Ω → Fin T) (T_meas : Measurable T_rv) :
    ∑ t, periodMass μ T_rv t = 1 := by
  have hOneInt : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const (1 : ℝ)
  calc
    ∑ t, periodMass μ T_rv t
        = ∑ t, ∫ ω, (fun _ : Ω => (1 : ℝ)) ω
            * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro t _
          simpa [periodMass] using
            (CellBridge.integral_cell_indicator_one_eq_cellMass μ T_rv T_meas t).symm
    _ = ∫ ω, (1 : ℝ) ∂μ := by
          rw [CellBridge.integral_eq_sum_cell μ (fun _ : Ω => (1 : ℝ))
            T_rv T_meas hOneInt]
    _ = 1 := by simp

private theorem period_centered_sum_eq_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (T_rv : Ω → Fin T) (T_meas : Measurable T_rv)
    (F_int : Integrable F μ) :
    ∑ t, (((∫ ω, F ω
          * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ)
        / periodMass μ T_rv t) - ∫ ω, F ω ∂μ)
        * periodMass μ T_rv t = 0 := by
  have hdiv : ∀ t,
      ((∫ ω, F ω
          * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ)
        / periodMass μ T_rv t) * periodMass μ T_rv t =
        ∫ ω, F ω
          * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ :=
    fun t => period_integral_div_mul_periodMass μ F T_rv T_meas t
  calc
    ∑ t, (((∫ ω, F ω
          * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ)
        / periodMass μ T_rv t) - ∫ ω, F ω ∂μ)
        * periodMass μ T_rv t
        = (∑ t, ∫ ω, F ω
            * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ)
          - (∫ ω, F ω ∂μ) * ∑ t, periodMass μ T_rv t := by
          simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl (fun t _ => hdiv t)
    _ = (∫ ω, F ω ∂μ) - (∫ ω, F ω ∂μ) * 1 := by
          rw [← integral_eq_sum_period μ F T_rv T_meas F_int,
            sum_periodMass_eq_one μ T_rv T_meas]
    _ = 0 := by ring

private theorem panelMeanReg_cohort_axis_orthogonal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (F_memLp : MemLp F 2 μ)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) (g : 𝒢) :
    ∫ ω, (F ω - panelMeanReg μ F G T_rv ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  let IG : 𝒢 → Ω → ℝ := fun g ω =>
    Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω
  let IT : Fin T → Ω → ℝ := fun t ω =>
    Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω
  let a : 𝒢 → ℝ := fun g =>
    (∫ ω, F ω * IG g ω ∂μ) / cohortMass μ G g
  let b : Fin T → ℝ := fun t =>
    (∫ ω, F ω * IT t ω ∂μ) / periodMass μ T_rv t - ∫ ω, F ω ∂μ
  have hF_int : Integrable F μ :=
    F_memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hIG : MemLp (IG g) 2 μ := by
    simpa [IG] using indicator_cohort_memLp μ G G_meas g
  have hFI_int : Integrable (fun ω => F ω * IG g ω) μ :=
    F_memLp.integrable_mul hIG
  have hPanel_mem : MemLp (panelMeanReg μ F G T_rv) 2 μ :=
    (panelClass μ G T_rv G_meas T_meas).memLp
      (panelMeanReg_mem_panelClass μ F G T_rv G_meas T_meas)
  have hPanelI_int : Integrable (fun ω => panelMeanReg μ F G T_rv ω * IG g ω) μ :=
    hPanel_mem.integrable_mul hIG
  have hsumG_mem : MemLp (fun ω => ∑ g', a g' * IG g' ω) 2 μ :=
    (panelClass μ G T_rv G_meas T_meas).memLp
      ⟨a, fun _ => 0, by filter_upwards [] with ω; simp [IG]⟩
  have hsumT_mem : MemLp (fun ω => ∑ t, b t * IT t ω) 2 μ :=
    (panelClass μ G T_rv G_meas T_meas).memLp
      ⟨fun _ => 0, b, by filter_upwards [] with ω; simp [IT]⟩
  have hsumGI_int : Integrable
      (fun ω => (∑ g', a g' * IG g' ω) * IG g ω) μ :=
    hsumG_mem.integrable_mul hIG
  have hsumTI_int : Integrable
      (fun ω => (∑ t, b t * IT t ω) * IG g ω) μ :=
    hsumT_mem.integrable_mul hIG
  have hcohort :
      ∫ ω, (∑ g', a g' * IG g' ω) * IG g ω ∂μ =
        ∫ ω, F ω * IG g ω ∂μ := by
    calc
      ∫ ω, (∑ g', a g' * IG g' ω) * IG g ω ∂μ
          = a g * cohortMass μ G g := by
            simpa [IG, a] using
              integral_cohort_sum_mul_cohort_indicator μ G G_meas a g
      _ = ∫ ω, F ω * IG g ω ∂μ := by
            simpa [a, IG, mul_comm] using
              (cohort_integral_div_mul_cohortMass μ F G G_meas g)
  have hperiod :
      ∫ ω, (∑ t, b t * IT t ω) * IG g ω ∂μ = 0 := by
    calc
      ∫ ω, (∑ t, b t * IT t ω) * IG g ω ∂μ
          = ∑ t, b t * cellMass μ G T_rv g t := by
            simpa [IG, IT, b] using
              integral_period_sum_mul_cohort_indicator μ G T_rv
                G_meas T_meas b g
      _ = cohortMass μ G g * ∑ t, b t * periodMass μ T_rv t := by
            calc
              ∑ t, b t * cellMass μ G T_rv g t
                  = ∑ t, b t * (cohortMass μ G g * periodMass μ T_rv t) := by
                    refine Finset.sum_congr rfl ?_
                    intro t _
                    rw [B_balanced g t]
              _ = cohortMass μ G g * ∑ t, b t * periodMass μ T_rv t := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro t _
                    ring
      _ = 0 := by
            rw [period_centered_sum_eq_zero μ F T_rv T_meas hF_int]
            ring
  have hpanel :
      ∫ ω, panelMeanReg μ F G T_rv ω * IG g ω ∂μ =
        ∫ ω, F ω * IG g ω ∂μ := by
    calc
      ∫ ω, panelMeanReg μ F G T_rv ω * IG g ω ∂μ
          = ∫ ω, ((∑ g', a g' * IG g' ω) + (∑ t, b t * IT t ω))
              * IG g ω ∂μ := by
            simp [panelMeanReg, IG, IT, a, b]
      _ = ∫ ω, (∑ g', a g' * IG g' ω) * IG g ω
            + (∑ t, b t * IT t ω) * IG g ω ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [] with ω
            ring
      _ = ∫ ω, (∑ g', a g' * IG g' ω) * IG g ω ∂μ
            + ∫ ω, (∑ t, b t * IT t ω) * IG g ω ∂μ := by
            exact integral_add hsumGI_int hsumTI_int
      _ = ∫ ω, F ω * IG g ω ∂μ := by
            rw [hcohort, hperiod]
            ring
  calc
    ∫ ω, (F ω - panelMeanReg μ F G T_rv ω) * IG g ω ∂μ
        = ∫ ω, F ω * IG g ω ∂μ
          - ∫ ω, panelMeanReg μ F G T_rv ω * IG g ω ∂μ := by
          calc
            ∫ ω, (F ω - panelMeanReg μ F G T_rv ω) * IG g ω ∂μ
                = ∫ ω, F ω * IG g ω
                    - panelMeanReg μ F G T_rv ω * IG g ω ∂μ := by
                  refine integral_congr_ae ?_
                  filter_upwards [] with ω
                  ring
            _ = ∫ ω, F ω * IG g ω ∂μ
                - ∫ ω, panelMeanReg μ F G T_rv ω * IG g ω ∂μ :=
                  integral_sub hFI_int hPanelI_int
    _ = 0 := by rw [hpanel]; ring

private theorem panelMeanReg_period_axis_orthogonal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (F_memLp : MemLp F 2 μ)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) (t : Fin T) :
    ∫ ω, (F ω - panelMeanReg μ F G T_rv ω)
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  let IG : 𝒢 → Ω → ℝ := fun g ω =>
    Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω
  let IT : Fin T → Ω → ℝ := fun t ω =>
    Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω
  let a : 𝒢 → ℝ := fun g =>
    (∫ ω, F ω * IG g ω ∂μ) / cohortMass μ G g
  let b : Fin T → ℝ := fun t =>
    (∫ ω, F ω * IT t ω ∂μ) / periodMass μ T_rv t - ∫ ω, F ω ∂μ
  have hF_int : Integrable F μ :=
    F_memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hIT : MemLp (IT t) 2 μ := by
    simpa [IT] using indicator_period_memLp μ T_rv T_meas t
  have hFI_int : Integrable (fun ω => F ω * IT t ω) μ :=
    F_memLp.integrable_mul hIT
  have hPanel_mem : MemLp (panelMeanReg μ F G T_rv) 2 μ :=
    (panelClass μ G T_rv G_meas T_meas).memLp
      (panelMeanReg_mem_panelClass μ F G T_rv G_meas T_meas)
  have hPanelI_int : Integrable (fun ω => panelMeanReg μ F G T_rv ω * IT t ω) μ :=
    hPanel_mem.integrable_mul hIT
  have hsumG_mem : MemLp (fun ω => ∑ g, a g * IG g ω) 2 μ :=
    (panelClass μ G T_rv G_meas T_meas).memLp
      ⟨a, fun _ => 0, by filter_upwards [] with ω; simp [IG]⟩
  have hsumT_mem : MemLp (fun ω => ∑ t', b t' * IT t' ω) 2 μ :=
    (panelClass μ G T_rv G_meas T_meas).memLp
      ⟨fun _ => 0, b, by filter_upwards [] with ω; simp [IT]⟩
  have hsumGI_int : Integrable
      (fun ω => (∑ g, a g * IG g ω) * IT t ω) μ :=
    hsumG_mem.integrable_mul hIT
  have hsumTI_int : Integrable
      (fun ω => (∑ t', b t' * IT t' ω) * IT t ω) μ :=
    hsumT_mem.integrable_mul hIT
  have hcohort :
      ∫ ω, (∑ g, a g * IG g ω) * IT t ω ∂μ =
        (∫ ω, F ω ∂μ) * periodMass μ T_rv t := by
    calc
      ∫ ω, (∑ g, a g * IG g ω) * IT t ω ∂μ
          = ∑ g, a g * cellMass μ G T_rv g t := by
            simpa [IG, IT, a] using
              integral_cohort_sum_mul_period_indicator μ G T_rv
                G_meas T_meas a t
      _ = (∑ g, a g * cohortMass μ G g) * periodMass μ T_rv t := by
            calc
              ∑ g, a g * cellMass μ G T_rv g t
                  = ∑ g, a g * (cohortMass μ G g * periodMass μ T_rv t) := by
                    refine Finset.sum_congr rfl ?_
                    intro g _
                    rw [B_balanced g t]
              _ = (∑ g, a g * cohortMass μ G g) * periodMass μ T_rv t := by
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl ?_
                    intro g _
                    ring
      _ = (∫ ω, F ω ∂μ) * periodMass μ T_rv t := by
            congr 1
            calc
              ∑ g, a g * cohortMass μ G g
                  = ∑ g, ∫ ω, F ω * IG g ω ∂μ := by
                    refine Finset.sum_congr rfl ?_
                    intro g _
                    simpa [a, IG, mul_comm] using
                      (cohort_integral_div_mul_cohortMass μ F G G_meas g)
              _ = ∫ ω, F ω ∂μ := by
                    rw [integral_eq_sum_cohort μ F G G_meas hF_int]
  have hperiod :
      ∫ ω, (∑ t', b t' * IT t' ω) * IT t ω ∂μ =
        ∫ ω, F ω * IT t ω ∂μ - (∫ ω, F ω ∂μ) * periodMass μ T_rv t := by
    calc
      ∫ ω, (∑ t', b t' * IT t' ω) * IT t ω ∂μ
          = b t * periodMass μ T_rv t := by
            simpa [IT, b] using
              integral_period_sum_mul_period_indicator μ T_rv T_meas b t
      _ = ∫ ω, F ω * IT t ω ∂μ - (∫ ω, F ω ∂μ) * periodMass μ T_rv t := by
            have hdiv :
                ((∫ ω, F ω * IT t ω ∂μ) / periodMass μ T_rv t)
                    * periodMass μ T_rv t =
                  ∫ ω, F ω * IT t ω ∂μ := by
              simpa [IT] using
                period_integral_div_mul_periodMass μ F T_rv T_meas t
            dsimp [b]
            calc
              ((∫ ω, F ω * IT t ω ∂μ) / periodMass μ T_rv t
                    - ∫ ω, F ω ∂μ) * periodMass μ T_rv t
                  = ((∫ ω, F ω * IT t ω ∂μ) / periodMass μ T_rv t)
                      * periodMass μ T_rv t
                    - (∫ ω, F ω ∂μ) * periodMass μ T_rv t := by ring
              _ = ∫ ω, F ω * IT t ω ∂μ
                    - (∫ ω, F ω ∂μ) * periodMass μ T_rv t := by
                    rw [hdiv]
  have hpanel :
      ∫ ω, panelMeanReg μ F G T_rv ω * IT t ω ∂μ =
        ∫ ω, F ω * IT t ω ∂μ := by
    calc
      ∫ ω, panelMeanReg μ F G T_rv ω * IT t ω ∂μ
          = ∫ ω, ((∑ g, a g * IG g ω) + (∑ t', b t' * IT t' ω))
              * IT t ω ∂μ := by
            simp [panelMeanReg, IG, IT, a, b]
      _ = ∫ ω, (∑ g, a g * IG g ω) * IT t ω
            + (∑ t', b t' * IT t' ω) * IT t ω ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [] with ω
            ring
      _ = ∫ ω, (∑ g, a g * IG g ω) * IT t ω ∂μ
            + ∫ ω, (∑ t', b t' * IT t' ω) * IT t ω ∂μ := by
            exact integral_add hsumGI_int hsumTI_int
      _ = ∫ ω, F ω * IT t ω ∂μ := by
            rw [hcohort, hperiod]
            ring
  calc
    ∫ ω, (F ω - panelMeanReg μ F G T_rv ω) * IT t ω ∂μ
        = ∫ ω, F ω * IT t ω ∂μ
          - ∫ ω, panelMeanReg μ F G T_rv ω * IT t ω ∂μ := by
          calc
            ∫ ω, (F ω - panelMeanReg μ F G T_rv ω) * IT t ω ∂μ
                = ∫ ω, F ω * IT t ω
                    - panelMeanReg μ F G T_rv ω * IT t ω ∂μ := by
                  refine integral_congr_ae ?_
                  filter_upwards [] with ω
                  ring
            _ = ∫ ω, F ω * IT t ω ∂μ
                - ∫ ω, panelMeanReg μ F G T_rv ω * IT t ω ∂μ :=
                  integral_sub hFI_int hPanelI_int
    _ = 0 := by rw [hpanel]; ring

/-! ### Per-cohort orthogonality under the balanced-cell bridge hypotheses -/

/-- The treatment residual is orthogonal to every cohort indicator
`𝟙{G = g}`. Reduces to the defining identity of `cohortBarD`. -/
theorem residD_cohort_orthogonal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) (g : 𝒢) :
    ∫ ω, (D ω - panelPropensity μ D G T_rv ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  have hD_mem : MemLp D 2 μ :=
    memLp_two_of_binary μ D D_meas D_binary
  have hproj : panelPropensity μ D G T_rv = panelMeanReg μ D G T_rv := by
    funext ω
    simp [panelPropensity, panelMeanReg, cohortBarD]
  simpa [hproj] using
    panelMeanReg_cohort_axis_orthogonal μ D G T_rv G_meas T_meas
      hD_mem B_balanced g

/-- The outcome residual is orthogonal to every cohort indicator. -/
theorem residY_cohort_orthogonal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (Y_memLp : MemLp Y 2 μ)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) (g : 𝒢) :
    ∫ ω, (Y ω - panelMeanReg μ Y G T_rv ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  exact panelMeanReg_cohort_axis_orthogonal μ Y G T_rv G_meas T_meas
    Y_memLp B_balanced g

/-! ### Per-period orthogonality (requires balanced-cell hypothesis) -/

/-- The treatment residual is orthogonal to every period indicator
`𝟙{T_rv = t}`. Requires `B_balanced` to make the cross-cohort sum cancel. -/
theorem residD_period_orthogonal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) (t : Fin T) :
    ∫ ω, (D ω - panelPropensity μ D G T_rv ω)
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  have hD_mem : MemLp D 2 μ :=
    memLp_two_of_binary μ D D_meas D_binary
  have hproj : panelPropensity μ D G T_rv = panelMeanReg μ D G T_rv := by
    funext ω
    simp [panelPropensity, panelMeanReg, cohortBarD]
  simpa [hproj] using
    panelMeanReg_period_axis_orthogonal μ D G T_rv G_meas T_meas
      hD_mem B_balanced t

/-- The outcome residual is orthogonal to every period indicator. -/
theorem residY_period_orthogonal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (Y_memLp : MemLp Y 2 μ)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) (t : Fin T) :
    ∫ ω, (Y ω - panelMeanReg μ Y G T_rv ω)
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  exact panelMeanReg_period_axis_orthogonal μ Y G T_rv G_meas T_meas
    Y_memLp B_balanced t

end Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition
