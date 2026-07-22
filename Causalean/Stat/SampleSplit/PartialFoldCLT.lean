/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fold-restricted CLT for one-shot sample splits

`Causalean/Stat/AsymptoticLinearity.lean` packages the i.i.d. CLT as
`IIDSample.clt_normalized_sum`: along an i.i.d. sample with mean-zero,
square-integrable transform `ψ`, the normalized partial sum
`(1/√n) Σ_{i<n} ψ(Z_i)` converges in distribution to `N(0, ∫ψ²dP)`.

For sample-split estimators (PlugIn, DML), the relevant normalized sum is

    (1/√|B(n)|) Σ_{i ∈ B(n)} ψ(Z_i)

over the estimation fold `B(n)`.  Because `(Z_i)_{i ∈ B(n)}` is itself an
i.i.d. sub-sample of size `|B(n)| → ∞` (by `OneShotSplit.cogrow`), the same
CLT applies — distributionally, the fold-B sum is the same as the full sum
of `|B(n)|` copies.

Under a *fixed split ratio* `|B(n)|/n → c ∈ (0, 1)`, the fold-B asymptotic
normality at rate `√|B(n)|` translates to √n-asymptotic normality with
inflated variance `σ²/c` — the standard cost of sample splitting.

This file provides:

* `IIDSample.clt_normalizedFoldB`            — fold-B CLT at rate `√|B(n)|`.
* `IsAsymLinear.tendsto_normal_foldB`        — `IsAsymLinear … split.foldB`
                                              ⇒ `√|B(n)|·(θn − θ₀) ⇒ N(0, σ²)`.
* `IsAsymLinear.tendsto_normal_foldB_sqrt_n` — under `|B(n)|/n → c ∈ (0, 1)`,
                                              `√n·(θn − θ₀) ⇒ N(0, σ²/c)`.

The proofs use `IIDSample.clt_normalized_sum` plus a re-indexing argument
that exploits `iIndepFun` + `IdentDistrib` to package fold-B as a fresh
i.i.d. sample.
-/

import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.CLT.AsymptoticLinearity

/-! # Fold-Restricted Central Limit Theorems

This file provides the central-limit-theorem contact point for one-shot sample
splits. It proves the fold-B normalized-sum CLT, converts fold-B asymptotic
linearity into asymptotic normality at rate `√|B(n)|`, and gives the √n-rate
conversion under a fixed split ratio with variance inflation. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]
  {S : IIDSample Ω X μ P}

/-! ## CLT contact for the fold-B normalized sum -/

namespace OneShotSplit

omit [IsProbabilityMeasure μ] in
/-- The estimation fold of a one-shot split is the interval from the split point to the sample size. -/
lemma foldB_eq_Ico (split : OneShotSplit S) (n : ℕ) :
    split.foldB n = Finset.Ico (split.n₁ n) n := by
  ext i
  simp [OneShotSplit.foldB, Finset.mem_Ico, and_comm]

omit [IsProbabilityMeasure μ] in
/-- The size of the estimation fold is the sample size minus the split point. -/
lemma card_foldB (split : OneShotSplit S) (n : ℕ) :
    (split.foldB n).card = n - split.n₁ n := by
  rw [split.foldB_eq_Ico n]
  exact Nat.card_Ico (split.n₁ n) n

end OneShotSplit

namespace IIDSample

/-- A normalized sum over any finite index set has the same characteristic function as a normalized initial block of the same size. -/
lemma charFun_normalizedSum_finset_eq_range_card
    (S : IIDSample Ω X μ P) {ψ : X → ℝ} (hψ_meas : Measurable ψ)
    (s : Finset ℕ) (t : ℝ) :
    charFun (μ.map (fun ω =>
      (Real.sqrt (s.card : ℝ))⁻¹ * ∑ i ∈ s, ψ (S.Z i ω))) t =
    charFun (μ.map (fun ω =>
      (Real.sqrt (s.card : ℝ))⁻¹ * ∑ i ∈ Finset.range s.card, ψ (S.Z i ω))) t := by
  let Y : ℕ → Ω → ℝ := fun i ω => ψ (S.Z i ω)
  let c : ℝ := (Real.sqrt (s.card : ℝ))⁻¹
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    exact hψ_meas.comp (S.meas i)
  have hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := by
    intro i
    simpa [Y, Function.comp_def] using (S.identDist i).symm.comp hψ_meas
  have hindep_Y : iIndepFun Y μ := by
    simpa [Y] using
      S.indep.comp (fun _ x => ψ x) (fun _ => hψ_meas)
  have hindep_s : iIndepFun (fun i : s => Y i) μ := by
    exact hindep_Y.precomp Subtype.val_injective
  have hleft_sum : (fun ω => ∑ i : s, Y i ω) = fun ω => ∑ i ∈ s, Y i ω := by
    funext ω
    exact Finset.sum_attach s (fun i => Y i ω)
  have hleft_unscaled :
      charFun (μ.map (fun ω => ∑ i ∈ s, Y i ω)) (c * t)
        = charFun (μ.map (Y 0)) (c * t) ^ s.card := by
    calc
      charFun (μ.map (fun ω => ∑ i ∈ s, Y i ω)) (c * t)
          = charFun (μ.map (fun ω => ∑ i : s, Y i ω)) (c * t) := by
              rw [hleft_sum]
      _ = (∏ i : s, charFun (μ.map (Y i)) (c * t)) := by
              simpa [Finset.prod_apply] using congrFun
                (iIndepFun.charFun_map_fun_sum_eq_prod
                  (fun i : s => (hY_meas i).aemeasurable) hindep_s)
                (c * t)
      _ = charFun (μ.map (Y 0)) (c * t) ^ s.card := by
              rw [show
                (∏ i : s, charFun (μ.map (Y i)) (c * t))
                  = ∏ _i : s, charFun (μ.map (Y 0)) (c * t) by
                apply Finset.prod_congr rfl
                intro i _hi
                exact congrFun (congrArg charFun ((hY_ident i).map_eq)) (c * t)]
              simp
  have hleft_scaled :
      charFun (μ.map (fun ω => c * ∑ i ∈ s, Y i ω)) t
        = charFun (μ.map (Y 0)) (c * t) ^ s.card := by
    calc
      charFun (μ.map (fun ω => c * ∑ i ∈ s, Y i ω)) t
          = charFun (μ.map (fun ω => ∑ i ∈ s, Y i ω)) (c * t) := by
              rw [show μ.map (fun ω => c * ∑ i ∈ s, Y i ω)
                  = (μ.map (fun ω => ∑ i ∈ s, Y i ω)).map (fun x => c * x) by
                rw [Measure.map_map]
                · rfl
                · exact measurable_const.mul measurable_id
                · exact Finset.measurable_sum _ (fun i _ => hY_meas i)]
              rw [charFun_map_mul]
      _ = charFun (μ.map (Y 0)) (c * t) ^ s.card := hleft_unscaled
  have hright_scaled :
      charFun (μ.map (fun ω => c * ∑ i ∈ Finset.range s.card, Y i ω)) t
        = charFun (μ.map (Y 0)) (c * t) ^ s.card := by
    calc
      charFun (μ.map (fun ω => c * ∑ i ∈ Finset.range s.card, Y i ω)) t
          = charFun (μ.map (invSqrtMulSum Y s.card)) t := by
              congr 1
              apply Measure.map_congr
              filter_upwards with ω
              dsimp [invSqrtMulSum, c]
              rw [← Fin.sum_univ_eq_sum_range]
      _ = charFun (μ.map (Y 0)) (c * t) ^ s.card := by
              simpa [c] using
                (ProbabilityTheory.charFun_invSqrtMulSum (fun i => hY_meas i)
                  (P := μ) hindep_Y (fun i => hY_ident i) (n := s.card) (t := t))
  simpa [Y, c] using hleft_scaled.trans hright_scaled.symm

/-- **Fold-B CLT.**  Along an i.i.d. sample `S` with mean-zero,
square-integrable transform `ψ`, the fold-B normalized partial sum
`(1/√|B(n)|) Σ_{i ∈ B(n)} ψ(Z_i)` converges in distribution to
`N(0, ∫ψ²dP)` under `μ`.

The hypothesis `OneShotSplit.cogrow` (`|B(n)| → ∞`) is built into `split`. -/
theorem clt_normalizedFoldB
    (S : IIDSample Ω X μ P) (split : OneShotSplit S) {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_mean : ∫ x, ψ x ∂P = 0)
    (hψ_sq_int : Integrable (fun x => (ψ x) ^ 2) P)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum S ψ split.foldB n) μ) :
    Tendsto_dist
      (IsAsymLinear.normalizedSum S ψ split.foldB)
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P))
      μ
      hSum_meas := by
  have hFull_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n) μ := by
    intro n
    unfold IsAsymLinear.normalizedSum
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun i _hi => hψ_meas.comp (S.meas i)))).aemeasurable
  have hFull :=
    IIDSample.clt_normalized_sum S hψ_meas hψ_mean hψ_sq_int hFull_meas
  have hcard_tendsto : Tendsto (fun n => (split.foldB n).card) atTop atTop := by
    convert split.cogrow using 1
    funext n
    exact split.card_foldB n
  unfold Tendsto_dist at hFull ⊢
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t => ?_
  have hFull_char :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hFull t).comp hcard_tendsto
  refine hFull_char.congr' ?_
  filter_upwards with n
  have hcf := charFun_normalizedSum_finset_eq_range_card S hψ_meas (split.foldB n) t
  change charFun
      (μ.map (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m)
        (split.foldB n).card)) t =
    charFun (μ.map (IsAsymLinear.normalizedSum S ψ split.foldB n)) t
  rw [show IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m)
      (split.foldB n).card =
        fun ω => (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ Finset.range (split.foldB n).card, ψ (S.Z i ω) by
    funext ω
    simp [IsAsymLinear.normalizedSum]]
  rw [show IsAsymLinear.normalizedSum S ψ split.foldB n =
      fun ω => (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n, ψ (S.Z i ω) by
    rfl]
  exact hcf.symm

end IIDSample

/-! ## Asymptotic-linearity ⇒ asymptotic normality, fold-B variant -/

variable {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}

/-- **Fold-B asymptotic linearity ⇒ asymptotic normality at rate `√|B(n)|`.**

If `IsAsymLinear θn θ₀ ψ S split.foldB`, then
`√|B(n)| · (θn n − θ₀) ⇒ N(0, ∫ ψ² dP)` under `μ`.

Direct combination of `clt_normalizedFoldB` (the fold-B CLT) with
`Tendsto_dist.add_isLittleOp_one` (Slutsky absorption). -/
theorem IsAsymLinear.tendsto_normal_foldB
    (split : OneShotSplit S)
    (h : IsAsymLinear θn θ₀ ψ S split.foldB)
    (hψ_meas : Measurable ψ)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator θn θ₀ split.foldB n) μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S ψ split.foldB n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator θn θ₀ split.foldB)
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P))
      μ
      hθn_meas := by
  have hCLT :=
    IIDSample.clt_normalizedFoldB S split hψ_meas h.mean_zero h.finite_var hSum_meas
  refine Tendsto_dist.add_isLittleOp_one hSum_meas hθn_meas hCLT ?_
  simpa [IsAsymLinear.normalizedSum, IsAsymLinear.rescaledEstimator] using h.remainder

/-- **Conversion to √n-rate under a fixed split ratio.**

If `|B(n)|/n → c ∈ (0, 1)` and the estimator is fold-B asymptotically
linear, then the √n-rescaled estimator converges in distribution to
`N(0, σ²/c)` with inflation factor `1/c`. -/
theorem IsAsymLinear.tendsto_normal_foldB_sqrt_n
    (split : OneShotSplit S) {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (h : IsAsymLinear θn θ₀ ψ S split.foldB)
    (hψ_meas : Measurable ψ)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (fun ω => Real.sqrt (n : ℝ) * (θn n ω - θ₀)) μ) :
    Tendsto_dist
      (fun n ω => Real.sqrt (n : ℝ) * (θn n ω - θ₀))
      (gaussianMeasure 0 ((∫ x, (ψ x) ^ 2 ∂P) / c))
      μ
      hθn_meas := by
  let a : ℕ → ℝ :=
    fun n => (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ * Real.sqrt (n : ℝ)
  let σ2 : ℝ := ∫ x, (ψ x) ^ 2 ∂P
  have hfold_meas : ∀ n : ℕ,
      AEMeasurable (IsAsymLinear.rescaledEstimator θn θ₀ split.foldB n) μ := by
    intro n
    by_cases hn : n = 0
    · subst n
      unfold IsAsymLinear.rescaledEstimator
      simp
    · have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn
      have hsqrtn_ne : Real.sqrt (n : ℝ) ≠ 0 := by
        rw [Real.sqrt_ne_zero']
        exact_mod_cast hn_pos_nat
      have h_eq : IsAsymLinear.rescaledEstimator θn θ₀ split.foldB n =
          fun ω => (Real.sqrt ((split.foldB n).card : ℝ) * (Real.sqrt (n : ℝ))⁻¹) *
            (Real.sqrt (n : ℝ) * (θn n ω - θ₀)) := by
        funext ω
        unfold IsAsymLinear.rescaledEstimator
        field_simp [hsqrtn_ne]
      rw [h_eq]
      exact (hθn_meas n).const_mul _
  have hSum_meas : ∀ n : ℕ,
      AEMeasurable (IsAsymLinear.normalizedSum S ψ split.foldB n) μ := by
    intro n
    unfold IsAsymLinear.normalizedSum
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun i _hi => hψ_meas.comp (S.meas i)))).aemeasurable
  have hfold :
      Tendsto_dist
        (IsAsymLinear.rescaledEstimator θn θ₀ split.foldB)
        (gaussianMeasure 0 σ2) μ hfold_meas := by
    simpa [σ2] using h.tendsto_normal_foldB split hψ_meas hfold_meas hSum_meas
  have hscaled_meas : ∀ n : ℕ,
      AEMeasurable
        (fun ω => a n * IsAsymLinear.rescaledEstimator θn θ₀ split.foldB n ω) μ := by
    intro n
    exact (hfold_meas n).const_mul (a n)
  have hcard_tendsto : Tendsto (fun n => (split.foldB n).card) atTop atTop := by
    convert split.cogrow using 1
    funext n
    exact split.card_foldB n
  have hscale_tendsto : Tendsto a atTop (𝓝 ((Real.sqrt c)⁻¹)) := by
    have h_inv : Tendsto (fun n => (((split.foldB n).card : ℝ) / n)⁻¹)
        atTop (𝓝 c⁻¹) := by
      exact h_split_rate.inv₀ hc_pos.ne'
    have h_sqrt : Tendsto
        (fun n => Real.sqrt ((((split.foldB n).card : ℝ) / n)⁻¹))
        atTop (𝓝 (Real.sqrt c⁻¹)) := h_inv.sqrt
    have hcard_pos_event : ∀ᶠ n in atTop, 0 < (split.foldB n).card :=
      hcard_tendsto.eventually (Ioi_mem_atTop 0)
    have hn_pos_event : ∀ᶠ n in atTop, 0 < n := eventually_gt_atTop 0
    refine h_sqrt.congr' ?_ |>.mono_right ?_
    · filter_upwards [hcard_pos_event, hn_pos_event] with n hcard hn
      have hcard_ne : ((split.foldB n).card : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hcard)
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hn)
      dsimp [a]
      rw [show ((((split.foldB n).card : ℝ) / n)⁻¹) =
          (n : ℝ) / (split.foldB n).card by
        field_simp [hcard_ne, hn_ne]]
      rw [Real.sqrt_div (by positivity : 0 ≤ (n : ℝ))]
      ring
    · rw [Real.sqrt_inv]
  have hscaled :
      Tendsto_dist
        (fun n ω => a n * IsAsymLinear.rescaledEstimator θn θ₀ split.foldB n ω)
        (gaussianMeasure 0 (((Real.sqrt c)⁻¹) ^ 2 * σ2)) μ hscaled_meas :=
    Tendsto_dist.const_mul_tendsto_gaussian hfold_meas hscaled_meas hfold hscale_tendsto
  have h_eventual_eq : ∀ᶠ n in atTop,
      (fun ω => a n * IsAsymLinear.rescaledEstimator θn θ₀ split.foldB n ω)
        =ᵐ[μ] (fun ω => Real.sqrt (n : ℝ) * (θn n ω - θ₀)) := by
    have hcard_pos_event : ∀ᶠ n in atTop, 0 < (split.foldB n).card :=
      hcard_tendsto.eventually (Ioi_mem_atTop 0)
    filter_upwards [hcard_pos_event] with n hcard
    apply ae_of_all
    intro ω
    unfold IsAsymLinear.rescaledEstimator
    have hsqrt_card_ne : Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      exact_mod_cast hcard
    dsimp [a]
    field_simp [hsqrt_card_ne]
  have hvar : (Real.sqrt c ^ 2)⁻¹ * σ2 = σ2 / c := by
    rw [Real.sq_sqrt hc_pos.le]
    ring
  exact Tendsto_dist.congr_ae hscaled_meas hθn_meas (by simpa [hvar, σ2] using hscaled)
    h_eventual_eq

end Causalean.Stat
