/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Vector convergence in distribution and vector Slutsky absorption

Companion to `Causalean/Stat/Limit/Convergence.lean`.  The scalar `Tendsto_dist`
predicate is hard-wired to `ℝ`-valued sequences; here we provide the
vector analogue `Tendsto_dist_vec` for sequences valued in a metric space
`E` (typically `EuclideanSpace ℝ (Fin d)`), together with the vector
Slutsky-absorption lemma needed by the multivariate Δ-method
(`Causalean/Stat/Inference/DeltaMethod.lean`) and the vector
asymptotic-normality corollary
(`Causalean/Stat/CLT/AsymptoticLinearityVec.lean`).

Mirrors `Tendsto_dist`, `Tendsto_dist.add_isLittleOp_one`, and
`Tendsto_dist.congr_ae` from the scalar file, replacing `|·|` with `‖·‖`
and `*` with `•` where needed.  The proofs port the scalar arguments
verbatim using `tendsto_iff_forall_lipschitz_integral_tendsto`
(Mathlib's portmanteau characterization in any pseudo-metric space) and
`tendstoInMeasure_iff_norm` (the `SeminormedAddCommGroup`-valued form of
convergence in measure).
-/

import Causalean.Stat.Limit.Convergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Vector convergence in distribution

This module extends the scalar convergence-in-distribution interface to
metric-space-valued random variables.  The definition `Tendsto_dist_vec`
formulates weak convergence through pushforward probability measures, while
`Tendsto_dist_vec.add_isLittleOp_one`, `Tendsto_dist_vec.congr_ae`, and
`Tendsto_dist_vec.map_continuous` provide the vector Slutsky, a.e.-congruence,
and continuous-mapping rules used by multivariate CLT and delta-method
arguments.
-/

namespace Causalean.Stat

open MeasureTheory Filter Topology

/-! ## Vector convergence in distribution -/

/-- `Tendsto_dist_vec Xn Q μ hXn` is convergence in distribution of an
`E`-valued sequence `Xn : ℕ → Ω → E` to a probability measure
`Q : Measure E`, formulated as weak convergence of pushforward measures.

Vector analogue of `Causalean.Stat.Tendsto_dist`; works for any pseudo-metric
space `E` carrying a `BorelSpace` instance. -/
def Tendsto_dist_vec {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (Xn : ℕ → Ω → E) (Q : Measure E) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ) : Prop :=
  Tendsto (β := ProbabilityMeasure E)
    (fun n =>
      ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩) atTop
    (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩)

/-! ## Vector Slutsky absorption

If `Xn ⇒ Q` in distribution and `‖Yn − Xn‖ = o_p(1)`, then `Yn ⇒ Q`.
This is the vector analogue of `Tendsto_dist.add_isLittleOp_one` in
`AsymptoticLinearity.lean`; the proof ports verbatim using
`tendstoInMeasure_iff_norm` and the metric-space portmanteau
characterization. -/

/-- **Vector Slutsky absorption.**  If `Xn ⇒ Q` in distribution and the
norm of the perturbation `‖Yn − Xn‖` is `o_p(1)`, then `Yn ⇒ Q`.

Vector analogue of `Causalean.Stat.Tendsto_dist.add_isLittleOp_one` (file
`Causalean/Stat/AsymptoticLinearity.lean`).  Used by the multivariate Δ-method
and by `IsAsymLinearVec.tendsto_normal_vec`. -/
theorem Tendsto_dist_vec.add_isLittleOp_one
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Xn Yn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn)
    (hRem : IsLittleOp (fun n ω => ‖Yn n ω - Xn n ω‖) (fun _ => (1 : ℝ)) μ) :
    Tendsto_dist_vec Yn Q μ hYn := by
  have hXY : TendstoInMeasure μ (fun n ω => Yn n ω - Xn n ω) atTop (0 : Ω → E) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hrem : Tendsto (fun n => μ {ω | ε / 2 < ‖Yn n ω - Xn n ω‖}) atTop (𝓝 0) := by
      have hrem' := hRem (ε / 2) hhalf
      simpa [abs_of_nonneg] using hrem'
    rw [ENNReal.tendsto_nhds_zero] at hrem ⊢
    intro δ hδ
    filter_upwards [hrem δ hδ] with n hn
    have hsubset :
        {x | ε ≤ ‖Yn n x - Xn n x - (0 : Ω → E) x‖}
          ⊆ {ω | ε / 2 < ‖Yn n ω - Xn n ω‖} := by
      intro ω hω
      have hω' : ε ≤ ‖Yn n ω - Xn n ω‖ := by
        simpa using hω
      exact lt_of_lt_of_le (by linarith) hω'
    exact le_trans (measure_mono hsubset) hn
  unfold Tendsto_dist_vec at hX ⊢
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ y, F y ∂(μ.map (Yn n))) atTop (𝓝 (∫ y, F y ∂Q)) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  have hM_nonneg : 0 ≤ M := by
    simpa using hF_bounded (0 : E) (0 : E)
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip (0 : E)
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ.map (Yn n)) := Measure.isProbabilityMeasure_map (hYn n)
    simp
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in atTop, |∫ y, F y ∂(μ.map (Yn n)) - ∫ y, F y ∂Q| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le n : |∫ y, F y ∂(μ.map (Yn n)) - ∫ y, F y ∂Q|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q| := by
    refine (abs_sub_le (∫ y, F y ∂(μ.map (Yn n))) (∫ y, F y ∂(μ.map (Xn n)))
      (∫ y, F y ∂Q)).trans ?_
    gcongr
    have hFY_meas : AEStronglyMeasurable (fun x ↦ F (Yn n x)) μ :=
      (hF_cont.measurable.comp_aemeasurable (hYn n)).aestronglyMeasurable
    have hFX_meas : AEStronglyMeasurable (fun x ↦ F (Xn n x)) μ :=
      (hF_cont.measurable.comp_aemeasurable (hXn n)).aestronglyMeasurable
    have h_int_Y : Integrable (fun x ↦ F (Yn n x)) μ := by
      refine Integrable.of_bound hFY_meas (‖F (0 : E)‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Yn n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Yn n a)) (F 0)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (Xn n x)) μ := by
      refine Integrable.of_bound hFX_meas (‖F (0 : E)‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Xn n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Xn n a)) (F 0)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Yn n a) - F (Xn n a)‖) μ :=
      (h_int_Y.sub h_int_X).norm
    have hD_aemeas : AEMeasurable (fun a ↦ ‖F (Yn n a) - F (Xn n a)‖) μ :=
      h_int_sub.aemeasurable
    rw [integral_map (hYn n) hF_cont.aestronglyMeasurable,
        integral_map (hXn n) hF_cont.aestronglyMeasurable,
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Yn n a) - F (Xn n a) ∂μ‖
    _ ≤ ∫ a, ‖F (Yn n a) - F (Xn n a)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ a in {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)},
          ‖F (Yn n a) - F (Xn n a)‖ ∂μ
        + ∫ a in {x | L * (ε / 2) ≤ ‖F (Yn n x) - F (Xn n x)‖},
          ‖F (Yn n a) - F (Xn n a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt hD_aemeas aemeasurable_const
    _ ≤ ∫ a in {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)}, L * (ε / 2) ∂μ
        + ∫ a in {x | L * (ε / 2) ≤ ‖F (Yn n x) - F (Xn n x)‖}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt hD_aemeas aemeasurable_const
        · exact fun x hx ↦ hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert hF_bounded _ _
    _ = L * (ε / 2) * μ.real {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)}
        + M * μ.real {ω | L * (ε / 2) ≤ ‖F (Yn n ω) - F (Xn n ω)‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
      have hD_subset :
          {ω | L * (ε / 2) ≤ ‖F (Yn n ω) - F (Xn n ω)‖}
            ⊆ {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
        intro ω hω
        have hLip : ‖F (Yn n ω) - F (Xn n ω)‖ ≤ L * ‖Yn n ω - Xn n ω‖ := by
          simpa [dist_eq_norm] using hF_lip.dist_le_mul (Yn n ω) (Xn n ω)
        have hmul : (L : ℝ) * (ε / 2) ≤ (L : ℝ) * ‖Yn n ω - Xn n ω‖ :=
          hω.trans hLip
        exact le_of_mul_le_mul_left hmul (by exact_mod_cast hL)
      apply add_le_add
      · calc
          L * (ε / 2) * μ.real {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)}
              ≤ L * (ε / 2) * 1 := by
                gcongr
                exact measureReal_le_one
          _ = L * (ε / 2) := by ring
      · exact mul_le_mul_of_nonneg_left
          (measureReal_mono hD_subset (measure_ne_top μ _)) hM_nonneg
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hX
      simpa [tendsto_iff_dist_tendsto_zero] using hX F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Vector convergence in distribution is invariant under eventual a.e.
equality of the random variables.  Vector analogue of
`Tendsto_dist.congr_ae`. -/
theorem Tendsto_dist_vec.congr_ae
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Xn Yn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn)
    (hXY : ∀ᶠ n in atTop, Xn n =ᵐ[μ] Yn n) :
    Tendsto_dist_vec Yn Q μ hYn := by
  unfold Tendsto_dist_vec at hX ⊢
  refine hX.congr' ?_
  filter_upwards [hXY] with n hn
  apply Subtype.ext
  exact Measure.map_congr hn

/-- Pushforward of `Tendsto_dist_vec` under a continuous map.  If
`Xn ⇒ Q` and `g : E → F` is continuous, then `g ∘ Xn ⇒ Q.map g`.

Vector analogue / wrapper around
`MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`. -/
theorem Tendsto_dist_vec.map_continuous
    {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {Xn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    {g : E → F} (hg : Continuous g)
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hgXn : ∀ n, AEMeasurable (fun ω => g (Xn n ω)) μ)
    [IsProbabilityMeasure (Q.map g)]
    (hX : Tendsto_dist_vec Xn Q μ hXn) :
    Tendsto_dist_vec (fun n ω => g (Xn n ω)) (Q.map g) μ hgXn := by
  unfold Tendsto_dist_vec at hX ⊢
  have hpm := MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩)
    ⟨Q, ‹IsProbabilityMeasure Q›⟩ hX hg
  refine hpm.congr' ?_
  filter_upwards with n
  apply Subtype.ext
  change Measure.map g (μ.map (Xn n)) = μ.map (fun ω => g (Xn n ω))
  rw [AEMeasurable.map_map_of_aemeasurable hg.measurable.aemeasurable (hXn n)]
  rfl

end Causalean.Stat
