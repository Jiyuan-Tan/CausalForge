/- Copyright (c) 2026 Jiyuan Tan. All rights reserved. -/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContraction
import Causalean.Stat.Minimax.LeCam

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Stat

lemma tvDist_bind_kernel_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : X → Measure Y) (hK : Measurable K)
    (hprob : ∀ x, IsProbabilityMeasure (K x)) :
    tvDist (μ.bind K) (ν.bind K) ≤ tvDist μ ν := by
  letI : ∀ x, IsProbabilityMeasure (K x) := hprob
  letI : IsProbabilityMeasure (μ.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hprob)
  letI : IsProbabilityMeasure (ν.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hprob)
  refine ciSup_le fun B => ?_
  rw [measureReal_bind_eq_integral μ K hK hprob B.1 B.2,
    measureReal_bind_eq_integral ν K hK hprob B.1 B.2]
  have h := tvDist_integral_range μ ν (fun x => (K x).real B.1)
    ((Measure.measurable_coe B.2).ennreal_toReal.comp hK) 0 1 (by norm_num)
    (fun x => ⟨measureReal_nonneg,
      by simpa using measureReal_le_one (μ := K x) (s := B.1)⟩)
  simpa using h

lemma integrable_abs_sub_bind_of_clipped {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (K : X → Measure ℝ) (hK : Measurable K)
    (hprob : ∀ x, IsProbabilityMeasure (K x))
    (hclip : ∀ x, K x (Set.Icc (-2 : ℝ) 2)ᶜ = 0)
    (θ : ℝ) (hθ : |θ| ≤ 2) :
    Integrable (fun z => |z - θ|) (μ.bind K) := by
  letI : ∀ x, IsProbabilityMeasure (K x) := hprob
  letI : IsProbabilityMeasure (μ.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hprob)
  have hsupp : ∀ᵐ z ∂μ.bind K, z ∈ Set.Icc (-2 : ℝ) 2 := by
    change Set.Icc (-2 : ℝ) 2 ∈ ae (μ.bind K)
    rw [mem_ae_iff]
    rw [Measure.bind_apply measurableSet_Icc.compl hK.aemeasurable]
    simp [hclip]
  apply Integrable.of_bound (by fun_prop) 4
  filter_upwards [hsupp] with z hz
  rw [Real.norm_eq_abs, abs_abs]
  rcases abs_le.mp hθ with ⟨hθ0, hθ1⟩
  rw [abs_le]
  constructor <;> linarith [hz.1, hz.2]

private lemma event_mul_measureReal_le_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hfm : Measurable f)
    {s : ℝ} (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    s * μ.real {x | s ≤ f x} ≤ ∫ x, f x ∂μ := by
  have hs : MeasurableSet {x | s ≤ f x} := measurableSet_le measurable_const hfm
  have hi : Integrable ({x | s ≤ f x}.indicator (fun _ : Ω => s)) μ :=
    (integrable_const s).indicator hs
  have hm : ∀ᵐ x ∂μ, {x | s ≤ f x}.indicator (fun _ => s) x ≤ f x := by
    filter_upwards [hf0] with x hx
    by_cases h : s ≤ f x <;> simp [Set.indicator, h, hx]
  have := integral_mono_ae hi hf hm
  rw [integral_indicator hs, setIntegral_const, smul_eq_mul, measureReal_def] at this
  simpa [mul_comm] using this

/-- Honest randomized Le Cam reduction on the two output laws. -/
lemma output_two_point_L1_lower (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (θ0 θ1 : ℝ)
    (hi0 : Integrable (fun z => |z - θ0|) μ)
    (hi1 : Integrable (fun z => |z - θ1|) ν)
    (htv : tvDist μ ν ≤ 1 / 2) :
    |θ1 - θ0| / 8 ≤ max (∫ z, |z - θ0| ∂μ) (∫ z, |z - θ1| ∂ν) := by
  let s := |θ1 - θ0| / 2
  have hsep : 2 * s ≤ dist θ0 θ1 := by
    apply le_of_eq
    calc
      2 * s = |θ1 - θ0| := by dsimp [s]; ring
      _ = dist θ0 θ1 := by rw [Real.dist_eq, abs_sub_comm]
  have hp := half_one_sub_tvDist_le_max_error (P₀ := μ) (P₁ := ν)
    (est := id) measurable_id hsep
  have hp4 : 1 / 4 ≤ max
      (μ.real {z | s ≤ dist (id z) θ0}) (ν.real {z | s ≤ dist (id z) θ1}) := by
    linarith
  have h0 : s * μ.real {z | s ≤ |z - θ0|} ≤ ∫ z, |z - θ0| ∂μ :=
    event_mul_measureReal_le_integral hi0 (by fun_prop) (ae_of_all _ fun z => abs_nonneg _)
  have h1 : s * ν.real {z | s ≤ |z - θ1|} ≤ ∫ z, |z - θ1| ∂ν :=
    event_mul_measureReal_le_integral hi1 (by fun_prop) (ae_of_all _ fun z => abs_nonneg _)
  simp only [id_eq, Real.dist_eq] at hp4
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  calc
    |θ1 - θ0| / 8 = s * (1 / 4) := by dsimp [s]; ring
    _ ≤ s * max (μ.real {z | s ≤ |z - θ0|})
        (ν.real {z | s ≤ |z - θ1|}) := mul_le_mul_of_nonneg_left hp4 hs0
    _ = max (s * μ.real {z | s ≤ |z - θ0|})
        (s * ν.real {z | s ≤ |z - θ1|}) := by rw [mul_max_of_nonneg _ _ hs0]
    _ ≤ max (∫ z, |z - θ0| ∂μ) (∫ z, |z - θ1| ∂ν) := max_le_max h0 h1

end CausalSmith.Stat.DpCateMinimax
