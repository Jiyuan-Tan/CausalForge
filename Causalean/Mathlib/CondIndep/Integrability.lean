/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Integrability lemmas via conditional expectation of indicators

* `ae_pos_condExp_indicator_of_le` — σ-projection of indicator-conditional positivity:
  if `μ⟦𝟙_{A=a}|m₂⟧ > 0` a.e. and `m₁ ≤ m₂`, then `μ⟦𝟙_{A=a}|m₁⟧ > 0` a.e.
* `integrableOn_of_condExp_indicator_mul` — integrability on `B` of an `m`-measurable
  nonneg `g` whose product with `μ⟦𝟙_B|m⟧` equals `μ⟦𝟙_C|m⟧`.

Both are Mathlib-contribution candidates.  Used in
`PO/ID/Partial/Proxy/Helpers/CondExpQ.lean`.
-/

import Mathlib.Probability.Independence.Conditional

/-! # Integrability from Conditional-Expectation Indicators

This file proves measure-theoretic lemmas that turn conditional positivity and
conditional-expectation identities for indicators into positivity and integrability
conclusions. The results support proxy and partial-identification arguments that
reason through sub-σ-algebras.

The theorem `ae_pos_condExp_indicator_of_le` projects strict overlap from a
larger σ-algebra to a smaller one. The theorem
`integrableOn_of_condExp_indicator_mul` turns an `m`-measurable nonnegative
function satisfying an indicator conditional-expectation product identity into
an integrable-on-stratum conclusion. -/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

/-- **σ-projection of indicator-conditional positivity.**

If the indicator-conditional `μ⟦𝟙_{A=a} | m₂⟧` is strictly positive μ-a.e. on
some larger σ-algebra `m₂`, then the same holds when conditioning on a
sub-σ-algebra `m₁ ≤ m₂`. Concretely: from
`∀ᵐ ω ∂μ, μ⟦𝟙_{A=a} | m₂⟧ ω > 0` infer `∀ᵐ ω ∂μ, μ⟦𝟙_{A=a} | m₁⟧ ω > 0`.

Standard measure-theoretic argument:
- Let `S = {ω | μ⟦𝟙_{A=a}|m₁⟧ ω = 0}` (m₁-measurable).
- `∫_S 𝟙_{A=a} dμ = ∫_S μ⟦𝟙_{A=a}|m₁⟧ dμ = 0` by `setIntegral_condExp` and
  the integrand vanishing on S.
- Hence `μ(S ∩ {A=a}) = 0`.
- The "overlap_strong" hypothesis on m₂ (encoded here via the `m₂`-positivity
  of the indicator condExp, since m₁ ≤ m₂ via `MeasurableSet[m₁] ≤
  MeasurableSet[m₂]`) implies `μ(S) = 0`.

Mathlib-contribution candidate. Used in `Proxy/Helpers/CondExpQ.lean` for the
σ_X-projection of `likelihoodRatio_swapA_spec`. -/
theorem ae_pos_condExp_indicator_of_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @MeasureTheory.Measure Ω mΩ} [@MeasureTheory.IsFiniteMeasure Ω mΩ μ]
    {m₁ m₂ : MeasurableSpace Ω} (_h₁ : m₁ ≤ mΩ) (_h₂ : m₂ ≤ mΩ) (_h₁₂ : m₁ ≤ m₂)
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Ω → α} (_hA : @Measurable Ω α mΩ _ A) (a : α)
    (_h_overlap : ∀ s : Set Ω, MeasurableSet[m₂] s →
        μ (s ∩ {ω | A ω = a}) = 0 → μ s = 0) :
    ∀ᵐ ω ∂μ,
      0 < (μ[Set.indicator {ω' | A ω' = a} (fun _ => (1:ℝ)) | m₁]) ω := by
  let E : Set Ω := {ω | A ω = a}
  let f : Ω → ℝ := Set.indicator E (fun _ => (1 : ℝ))
  let p : Ω → ℝ := μ[f | m₁]
  let S : Set Ω := {ω | p ω = 0}
  haveI : MeasureTheory.IsFiniteMeasure (μ.trim _h₁) :=
    MeasureTheory.isFiniteMeasure_trim _h₁
  have hE : @MeasurableSet Ω mΩ E := by
    dsimp [E]
    exact _hA (measurableSet_singleton a)
  have hf_int : MeasureTheory.Integrable f μ := by
    dsimp [f]
    exact (MeasureTheory.integrable_const (μ := μ) (1 : ℝ)).indicator hE
  have hp_nonneg : 0 ≤ᵐ[μ] p := by
    dsimp [p, f, E]
    exact MeasureTheory.condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      by_cases h : A ω = a
      · simp [Set.indicator_of_mem, h]
      · simp [Set.indicator_of_notMem, h])
  have hp_sm : StronglyMeasurable[m₁] p := by
    dsimp [p, f]
    exact MeasureTheory.stronglyMeasurable_condExp
  have hS_m1 : MeasurableSet[m₁] S := by
    dsimp [S]
    exact hp_sm.measurable (measurableSet_singleton (0 : ℝ))
  have hS_mΩ : @MeasurableSet Ω mΩ S := _h₁ S hS_m1
  have hS_m2 : MeasurableSet[m₂] S := _h₁₂ S hS_m1
  have hset : ∫ ω in S, p ω ∂μ = ∫ ω in S, f ω ∂μ := by
    dsimp [p]
    exact MeasureTheory.setIntegral_condExp _h₁ hf_int hS_m1
  have hp_set_zero : ∫ ω in S, p ω ∂μ = 0 := by
    have hp_ae_zero_on_S : p =ᵐ[μ.restrict S] 0 := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := μ) hS_mΩ] with ω hω
      exact hω
    simpa using MeasureTheory.integral_congr_ae hp_ae_zero_on_S
  have hf_set_zero : ∫ ω in S, f ω ∂μ = 0 := by
    exact hset.symm.trans hp_set_zero
  have hf_set_real : ∫ ω in S, f ω ∂μ = μ.real (S ∩ E) := by
    dsimp [f]
    rw [MeasureTheory.setIntegral_indicator hE]
    simp [Set.inter_comm]
  have hSE_zero : μ (S ∩ E) = 0 := by
    rw [← MeasureTheory.measureReal_eq_zero_iff (μ := μ) (s := S ∩ E)]
    rw [← hf_set_real]
    exact hf_set_zero
  have hS_zero : μ S = 0 := by
    exact _h_overlap S hS_m2 (by simpa [E] using hSE_zero)
  have hS_ae : ∀ᵐ ω ∂μ, ω ∉ S := by
    rw [MeasureTheory.ae_iff]
    simpa using hS_zero
  filter_upwards [hp_nonneg, hS_ae] with ω hp_nonnegω hω_notS
  change 0 < p ω
  exact lt_of_le_of_ne hp_nonnegω (Ne.symm hω_notS)

/-- **Integrability on `B` of an `m`-measurable nonneg function whose product
with `μ⟦𝟙_B | m⟧` equals `μ⟦𝟙_C | m⟧`.**

If `g` is `m`-measurable and `μ`-a.e. nonneg, and satisfies the conditional
identity

    μ⟦𝟙_B | m⟧ · g  =ᵐ[μ]  μ⟦𝟙_C | m⟧,

then `g` is integrable on `B` (with `∫_B g dμ ≤ μ C`).

Proof: truncate `g_n := min (max g 0) n` (bounded, `m`-measurable); by the
bounded `m`-pull-out lemma,
`∫ 𝟙_B · g_n dμ = ∫ g_n · μ⟦𝟙_B|m⟧ dμ`. Since `g_n ≤ g` a.e. and
`μ⟦𝟙_B|m⟧ ≥ 0` a.e., the integrand is ≤
`g · μ⟦𝟙_B|m⟧ = μ⟦𝟙_C|m⟧` a.e., so
`∫_B g_n dμ ≤ ∫ μ⟦𝟙_C|m⟧ dμ = μ C < ∞`. Pass to the limit by MCT:
`∫_B g dμ ≤ μ C`. With `g` measurable (lifting `Measurable[m] g` via `hm`)
and a.e. nonneg, this gives `IntegrableOn g B μ`.

Mathlib-contribution candidate. Used in `Proxy/Helpers/CondExpQ.lean` to
bound the stratum odds ratio on the conditioning arm. -/
theorem integrableOn_of_condExp_indicator_mul
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @MeasureTheory.Measure Ω mΩ} [@MeasureTheory.IsFiniteMeasure Ω mΩ μ]
    {m : MeasurableSpace Ω} (_hm : m ≤ mΩ)
    {B C : Set Ω} (_hB : @MeasurableSet Ω mΩ B) (_hC : @MeasurableSet Ω mΩ C)
    {g : Ω → ℝ} (_hg_meas : Measurable[m] g) (_hg_nn : 0 ≤ᵐ[μ] g)
    (_h_eq :
      (fun ω =>
          (μ[Set.indicator B (fun _ => (1 : ℝ)) | m]) ω * g ω)
        =ᵐ[μ]
      (μ[Set.indicator C (fun _ => (1 : ℝ)) | m])) :
    MeasureTheory.IntegrableOn g B μ := by
  haveI : MeasureTheory.SigmaFinite (μ.trim _hm) := inferInstance
  let IB : Ω → ℝ := Set.indicator B (fun _ => (1 : ℝ))
  let IC : Ω → ℝ := Set.indicator C (fun _ => (1 : ℝ))
  have hIB_int : MeasureTheory.Integrable IB μ := by
    dsimp [IB]
    exact (MeasureTheory.integrable_const (μ := μ) (1 : ℝ)).indicator _hB
  have hIB_nn : 0 ≤ᵐ[μ] IB := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    dsimp [IB]
    by_cases hω : ω ∈ B
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hIB_bound : ∀ᵐ ω ∂μ, ‖IB ω‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    dsimp [IB]
    by_cases hω : ω ∈ B
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hpB_nn : 0 ≤ᵐ[μ] (μ[IB | m]) :=
    MeasureTheory.condExp_nonneg (f := IB) (m := m) (μ := μ) hIB_nn
  have hpC_int : MeasureTheory.Integrable (μ[IC | m]) μ :=
    MeasureTheory.integrable_condExp
  let gn : ℕ → Ω → ℝ := fun n ω => min (max (g ω) 0) (n : ℝ)
  have hgn_meas (n : ℕ) : Measurable[m] (gn n) := by
    dsimp [gn]
    exact (_hg_meas.max measurable_const).min measurable_const
  have hgn_sm (n : ℕ) :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ m (gn n) :=
    (hgn_meas n).stronglyMeasurable
  have hgn_nn (n : ℕ) : 0 ≤ᵐ[μ] gn n := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    dsimp [gn]
    exact le_min (le_max_right _ _) (Nat.cast_nonneg n)
  have hgn_bound (n : ℕ) : ∀ᵐ ω ∂μ, ‖gn n ω‖ ≤ (n : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hnon : 0 ≤ gn n ω :=
      le_min (le_max_right _ _) (Nat.cast_nonneg n)
    have hle : gn n ω ≤ (n : ℝ) := min_le_right _ _
    simpa [Real.norm_of_nonneg hnon] using hle
  have hgn_le_g (n : ℕ) : gn n ≤ᵐ[μ] g := by
    filter_upwards [_hg_nn] with ω hgω
    dsimp [gn]
    exact (min_le_left _ _).trans (max_eq_left hgω).le
  have hgn_int (n : ℕ) : MeasureTheory.Integrable (gn n) μ := by
    have hmeas : @Measurable Ω ℝ mΩ _ (gn n) :=
      (hgn_meas n).mono _hm le_rfl
    exact MeasureTheory.Integrable.of_bound
      hmeas.aestronglyMeasurable (n : ℝ) (hgn_bound n)
  have htrunc_bound :
      ∀ n : ℕ, ∫⁻ ω in B, ENNReal.ofReal (gn n ω) ∂μ ≤ μ C := by
    intro n
    have hpull : μ[(gn n) * IB | m] =ᵐ[μ] (gn n) * μ[IB | m] := by
      exact MeasureTheory.condExp_stronglyMeasurable_mul_of_bound
        _hm (hgn_sm n) hIB_int (n : ℝ) (hgn_bound n)
    have hreal_eq :
        ∫ ω in B, gn n ω ∂μ
          = ∫ ω, gn n ω * (μ[IB | m]) ω ∂μ := by
      calc
        ∫ ω in B, gn n ω ∂μ
            = ∫ ω, B.indicator (gn n) ω ∂μ :=
              (MeasureTheory.integral_indicator _hB).symm
        _ = ∫ ω, gn n ω * IB ω ∂μ := by
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall ?_)
          intro ω
          dsimp [IB]
          by_cases hω : ω ∈ B
          · simp [Set.indicator_of_mem hω]
          · simp [Set.indicator_of_notMem hω]
        _ = ∫ ω, μ[(gn n) * IB | m] ω ∂μ := by
          simpa [Pi.mul_apply] using
            (MeasureTheory.integral_condExp
              _hm (f := (gn n) * IB) (μ := μ)).symm
        _ = ∫ ω, gn n ω * (μ[IB | m]) ω ∂μ := by
          exact MeasureTheory.integral_congr_ae hpull
    have hprod_le :
        (fun ω => gn n ω * (μ[IB | m]) ω) ≤ᵐ[μ] (μ[IC | m]) := by
      filter_upwards [hgn_le_g n, hpB_nn, _h_eq] with ω hle hpB hEq
      calc
        gn n ω * (μ[IB | m]) ω
            ≤ g ω * (μ[IB | m]) ω :=
              mul_le_mul_of_nonneg_right hle hpB
        _ = (μ[IB | m]) ω * g ω := by ring
        _ = (μ[IC | m]) ω := hEq
    have hprod_int :
        MeasureTheory.Integrable
          (fun ω => gn n ω * (μ[IB | m]) ω) μ := by
      exact (MeasureTheory.integrable_condExp
        (f := (gn n) * IB) (m := m) (μ := μ)).congr hpull
    have hreal_le :
        ∫ ω in B, gn n ω ∂μ ≤ ∫ ω, (μ[IC | m]) ω ∂μ := by
      rw [hreal_eq]
      exact MeasureTheory.integral_mono_ae hprod_int hpC_int hprod_le
    have hreal_rhs : ∫ ω, (μ[IC | m]) ω ∂μ = μ.real C := by
      calc
        ∫ ω, (μ[IC | m]) ω ∂μ = ∫ ω, IC ω ∂μ :=
          MeasureTheory.integral_condExp _hm
        _ = μ.real C := by
          dsimp [IC]
          exact MeasureTheory.integral_indicator_one _hC
    have hlin_eq :
        ENNReal.ofReal (∫ ω in B, gn n ω ∂μ)
          = ∫⁻ ω in B, ENNReal.ofReal (gn n ω) ∂μ := by
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        ((hgn_int n).restrict) (MeasureTheory.ae_restrict_of_ae (hgn_nn n))
    calc
      ∫⁻ ω in B, ENNReal.ofReal (gn n ω) ∂μ
          = ENNReal.ofReal (∫ ω in B, gn n ω ∂μ) := hlin_eq.symm
      _ ≤ ENNReal.ofReal (∫ ω, (μ[IC | m]) ω ∂μ) :=
        ENNReal.ofReal_le_ofReal hreal_le
      _ = ENNReal.ofReal (μ.real C) := by rw [hreal_rhs]
      _ = μ C := by
        rw [MeasureTheory.measureReal_def,
          ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top μ C)]
  have hpoint_iSup :
      ∀ ω, (⨆ n : ℕ, ENNReal.ofReal (gn n ω)) = ENNReal.ofReal (g ω) := by
    intro ω
    have hmono : Monotone (fun n : ℕ => ENNReal.ofReal (gn n ω)) := by
      intro n k hnk
      dsimp [gn]
      exact ENNReal.ofReal_le_ofReal
        (min_le_min le_rfl (by exact_mod_cast hnk))
    apply iSup_eq_of_tendsto hmono
    have heq :
        (fun n : ℕ => ENNReal.ofReal (gn n ω))
          =ᶠ[Filter.atTop] fun _ => ENNReal.ofReal (g ω) := by
      rcases exists_nat_ge (max (g ω) 0) with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      have hn' : max (g ω) 0 ≤ (n : ℝ) :=
        hN.trans (by exact_mod_cast hn)
      have hmin : min (max (g ω) 0) (n : ℝ) = max (g ω) 0 :=
        min_eq_left hn'
      simp [gn, hmin, ENNReal.ofReal_max]
    exact heq.tendsto
  have hmono_ae :
      ∀ᵐ ω ∂μ.restrict B,
        Monotone fun n : ℕ => ENNReal.ofReal (gn n ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω n k hnk
    dsimp [gn]
    exact ENNReal.ofReal_le_ofReal
      (min_le_min le_rfl (by exact_mod_cast hnk))
  have haemeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun ω => ENNReal.ofReal (gn n ω)) (μ.restrict B) := by
    intro n
    have hmeas : @Measurable Ω ℝ mΩ _ (gn n) :=
      (hgn_meas n).mono _hm le_rfl
    exact (hmeas.ennreal_ofReal.aemeasurable).restrict
  have hmct :
      ∫⁻ ω in B, (⨆ n : ℕ, ENNReal.ofReal (gn n ω)) ∂μ
        = ⨆ n : ℕ, ∫⁻ ω in B, ENNReal.ofReal (gn n ω) ∂μ := by
    exact MeasureTheory.lintegral_iSup' (μ := μ.restrict B) haemeas hmono_ae
  have hlin_g_le : ∫⁻ ω in B, ENNReal.ofReal (g ω) ∂μ ≤ μ C := by
    calc
      ∫⁻ ω in B, ENNReal.ofReal (g ω) ∂μ
          = ∫⁻ ω in B, (⨆ n : ℕ, ENNReal.ofReal (gn n ω)) ∂μ := by
            refine MeasureTheory.lintegral_congr_ae
              (Filter.Eventually.of_forall ?_)
            intro ω
            exact (hpoint_iSup ω).symm
      _ = ⨆ n : ℕ, ∫⁻ ω in B, ENNReal.ofReal (gn n ω) ∂μ := hmct
      _ ≤ μ C := iSup_le htrunc_bound
  have hg_aesm :
      @MeasureTheory.AEStronglyMeasurable Ω ℝ _ mΩ mΩ
        g (μ.restrict B) := by
    have hg_meas : @Measurable Ω ℝ mΩ _ g := _hg_meas.mono _hm le_rfl
    exact hg_meas.aestronglyMeasurable.restrict
  have hg_hfi : MeasureTheory.HasFiniteIntegral g (μ.restrict B) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (MeasureTheory.ae_restrict_of_ae _hg_nn)]
    exact lt_of_le_of_lt hlin_g_le (MeasureTheory.measure_lt_top μ C)
  exact ⟨hg_aesm, hg_hfi⟩

end Causalean
