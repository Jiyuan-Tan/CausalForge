/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Distributional backdoor identification (Firpo 2007)

The mean-level backdoor (`PO/ID/Exact/ATE.lean`, `cate_backdoor` /
`ate_backdoor`) identifies `E[Y(d)]`.  This file identifies the *whole law* of
the potential outcome `Y(d)` under the distributional backdoor assumption bundle:
consistency, unconfoundedness, and two-sided common support `0 < e_d < 1`.
No outcome-integrability assumption is needed for distributional identification.
Under those hypotheses,
the distribution of `Y(d)` equals the observable inverse-probability-weighting law

    Law(Y(d)) = (μ.withDensity (1_{D=d}/e_d)).map Y      (`cfUnderLaw_eq_ipwLaw`).

This is the engine behind the quantile treatment effect identification
(`PO/ID/Exact/QTE/QuantileEffect.lean`).

## Proof outline
* `propScore_pos` — both arms have a.e.-positive propensity score (bare overlap).
* `integral_mul_indicator_eq_integral_mul_propScore` — the conditional-expectation
  pull-out `∫ h·1_{D=d} = ∫ h·e_d` for `σ(X)`-measurable `h`.
* `ipwDensity_integrable` — `1_{D=d}/e_d` is integrable, via a truncation /
  monotone-convergence argument (the delicate step under *bare*, non-strict
  overlap: there is no uniform lower bound on `e_d`, but `∫ 1_{D=d}/e_d = 1`).
* `integral_comp_YofD_eq` — the core distributional identity, the `g`-transform of
  `cate_backdoor`: `∫ g(Y(d)) = ∫ g(Y)·1_{D=d}/e_d` for bounded measurable `g`.
* `cfUnderLaw_eq_ipwLaw` — assemble via `Measure.ext` with `g = 1_A`.
-/

import Causalean.PO.ID.Exact.ATE
import Causalean.PO.Analysis.Quantile

/-! # Distributional Backdoor Identification

This file lifts backdoor identification from conditional means to full
potential-outcome laws under the Firpo distributional bundle: consistency,
unconfoundedness, and two-sided common support. It defines the observable IPW
density `ipwDensity`, the observable reweighted outcome law `ipwLaw`, and the
weaker causal bundle `DistributionalAssumptions`; `Assumptions.toDistributional`
projects the ordinary ATE backdoor assumptions to this distributional bundle.

The main technical steps are `propScore_pos`,
`integral_mul_indicator_eq_integral_mul_propScore`, `ipwDensity_integrable`,
and `integral_comp_YofD_eq`. The theorem `cfUnderLaw_eq_ipwLaw` identifies the
law of `Y(d)` with the observable IPW law, providing the distributional input
for quantile-treatment-effect identification. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- Observable inverse-probability-weighting density for arm `d`:
`1_{T=d} / e_d(X)`, where `e_d = P[T=d | σ(X)]` is the propensity score. -/
noncomputable def ipwDensity (d : Bool) : P.Ω → ℝ :=
  fun ω => S.dVar.indicator d ω / S.propScore d ω

/-- **Observable IPW law** of arm `d`: the factual outcome `Y` pushed forward
through the reweighted measure `(1_{T=d}/e_d) · μ`.  Under the distributional
backdoor assumption bundle used below, this is the law of `Y(d)`. -/
noncomputable def ipwLaw (d : Bool) (μ : Measure P.Ω) : Measure ℝ :=
  (μ.withDensity (fun ω => ENNReal.ofReal (S.ipwDensity d ω))).map S.factualY

/-- **Distributional backdoor assumptions.**  Firpo's distributional
identification of the potential-outcome law under arm `d` uses consistency,
conditional ignorability of treatment given covariates, and common support.  It
does not require the outcome-integrability assumptions bundled in the ATE
backdoor theorem, because laws and quantiles are defined without first moments. -/
structure DistributionalAssumptions (S : POBackdoorSystem P γ)
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] : Prop where
  /-- Consistency links the observed outcome to the potential outcome of the
  realized treatment arm. -/
  consistency : P.Consistency
  /-- Conditional ignorability: treatment is independent of `(Y(1), Y(0))`
  given covariates. -/
  unconfoundedness :
    P.CondIndepCF (RegimedVar.ofFactual S.dVar) S.cfBundle
      (RegimedVar.ofFactual S.xVar) P.μ
  /-- Common support: both treatment arms have positive conditional probability
  almost surely. -/
  overlap :
    ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1

/-- The ATE backdoor bundle projects to the weaker distributional bundle. -/
lemma Assumptions.toDistributional [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.Assumptions) : S.DistributionalAssumptions where
  consistency := hA.consistency
  unconfoundedness := hA.unconfoundedness
  overlap := hA.overlap

/-- `propScore d` is `σ(X)`-strongly-measurable (it is a conditional expectation). -/
lemma stronglyMeasurable_propScore [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (d : Bool) :
    StronglyMeasurable[S.sigmaX] (S.propScore d) :=
  S.xVar.stronglyMeasurable_condExpGiven_comap (S.dVar.indicator d)

/-- `propScore d ≥ 0` a.e. (conditional expectation of a nonnegative function). -/
lemma propScore_nonneg [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] (d : Bool) :
    0 ≤ᵐ[P.μ] S.propScore d :=
  condExp_nonneg (Filter.Eventually.of_forall
    (fun ω => by rcases S.dVar.indicator_eq_one_or_zero d ω with h | h <;> simp [h]))

/-- Under bare overlap, both arms have a.e.-positive propensity score. -/
lemma propScore_pos [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.DistributionalAssumptions) (d : Bool) :
    ∀ᵐ ω ∂P.μ, 0 < S.propScore d ω := by
  match d with
  | true => filter_upwards [hA.overlap] with ω hω; exact hω.1
  | false =>
    have hindD : ∀ e : Bool, Integrable (S.dVar.indicator e) P.μ :=
      fun e => S.dVar.integrable_indicator e
    have hsum_pt : (fun ω => S.dVar.indicator true ω + S.dVar.indicator false ω)
        = (fun _ : P.Ω => (1:ℝ)) := by
      funext ω; exact S.dVar.indicator_add_indicator_not ω
    have hsum : P.μ[fun ω => S.dVar.indicator true ω + S.dVar.indicator false ω | S.sigmaX]
        =ᵐ[P.μ] (fun _ => (1:ℝ)) := by
      rw [hsum_pt]
      exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const S.sigmaX_le (1:ℝ))
    have hadd : P.μ[fun ω => S.dVar.indicator true ω + S.dVar.indicator false ω | S.sigmaX]
        =ᵐ[P.μ] P.μ[S.dVar.indicator true | S.sigmaX]
          + P.μ[S.dVar.indicator false | S.sigmaX] :=
      MeasureTheory.condExp_add (hindD true) (hindD false) S.sigmaX
    filter_upwards [hsum, hadd, hA.overlap] with ω h1 h2 hT
    have heq : S.propScore true ω + S.propScore false ω = 1 := by
      have hh : P.μ[S.dVar.indicator true | S.sigmaX] ω
          + P.μ[S.dVar.indicator false | S.sigmaX] ω = 1 := by
        rw [← Pi.add_apply, ← h2, h1]
      unfold POBackdoorSystem.propScore; exact hh
    linarith [hT.2]

/-- **Conditional-expectation pull-out.**  For a `σ(X)`-strongly-measurable `h`,
`∫ h·1_{D=d} dμ = ∫ h·e_d dμ`. -/
lemma integral_mul_indicator_eq_integral_mul_propScore
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] (d : Bool)
    {h : P.Ω → ℝ} (hh_sm : StronglyMeasurable[S.sigmaX] h)
    (hh_ind_int : Integrable (fun ω => h ω * S.dVar.indicator d ω) P.μ) :
    ∫ ω, h ω * S.dVar.indicator d ω ∂P.μ
      = ∫ ω, h ω * S.propScore d ω ∂P.μ := by
  have hsm' : StronglyMeasurable[MeasurableSpace.comap S.xVar.factual inferInstance] h := hh_sm
  -- `μ[h·1_{D=d} | σX] =ᵐ h · μ[1_{D=d} | σX] = h · e_d`  (pull out the σX-meas factor `h`).
  have key : (fun ω => S.xVar.condExpGiven (fun ω => h ω * S.dVar.indicator d ω) P.μ ω)
      =ᵐ[P.μ] (fun ω => h ω * S.propScore d ω) :=
    S.xVar.condExpGiven_mul_of_stronglyMeasurable_left (f := h)
      (g := S.dVar.indicator d) hsm' hh_ind_int (S.dVar.integrable_indicator d)
  -- `∫ h·1_{D=d} = ∫ μ[h·1_{D=d}|σX]` then rewrite by `key`.
  have hint : ∫ ω, h ω * S.dVar.indicator d ω ∂P.μ
      = ∫ ω, S.xVar.condExpGiven (fun ω => h ω * S.dVar.indicator d ω) P.μ ω ∂P.μ := by
    unfold POVar.condExpGiven
    exact (MeasureTheory.integral_condExp S.xVar.comap_factual_le).symm
  rw [hint]
  exact MeasureTheory.integral_congr_ae key

/-- The truncated IPW weight `1_{D=d} · min n (1/e_d)`, bounded by `n`. -/
private noncomputable def ipwTrunc (d : Bool) (n : ℕ) : P.Ω → ℝ :=
  fun ω => S.dVar.indicator d ω * min (n : ℝ) (1 / S.propScore d ω)

/-- **Integrability of the IPW weight** under bare common support.

Bare overlap gives no uniform lower bound on `e_d`, so we truncate: the sequence
`f n = 1_{D=d}·min n (1/e_d)` is bounded by `n` (hence integrable), monotone, and
converges a.e. to `1_{D=d}/e_d` (since `e_d > 0` a.e.).  Its integrals satisfy
`∫ f n = ∫ min n (1/e_d)·e_d → ∫ 1 = 1` (pull-out + monotone convergence), so
`integrable_of_integral_tendsto_of_monotone` gives the limit integrable. -/
lemma ipwDensity_integrable [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.DistributionalAssumptions) (d : Bool) :
    Integrable (S.ipwDensity d) P.μ := by
  have hmeas : Measurable (S.ipwDensity d) :=
    (S.dVar.measurable_indicator d).div
      ((S.stronglyMeasurable_propScore d).mono S.sigmaX_le).measurable
  have he_sm : StronglyMeasurable[S.sigmaX] (S.propScore d) :=
    S.stronglyMeasurable_propScore d
  have he_meas : Measurable (S.propScore d) := (he_sm.mono S.sigmaX_le).measurable
  have he_pos : ∀ᵐ ω ∂P.μ, 0 < S.propScore d ω := S.propScore_pos hA d
  -- the truncations
  set f : ℕ → P.Ω → ℝ := S.ipwTrunc d with hf
  -- `min n (1/e_d)` is σX-strongly-measurable.
  have hmin_sm : ∀ n : ℕ, StronglyMeasurable[S.sigmaX]
      (fun ω => min (n : ℝ) (1 / S.propScore d ω)) := by
    intro n
    fun_prop
  -- measurability of each `f n`.
  have hf_meas : ∀ n, Measurable (f n) := by
    intro n
    rw [hf]
    exact (S.dVar.measurable_indicator d).mul
      (measurable_const.min (measurable_const.div he_meas))
  -- each `f n` is bounded by `n` a.e., hence integrable.
  have hf_int : ∀ n, Integrable (f n) P.μ := by
    intro n
    refine (integrable_const (n : ℝ)).mono' (hf_meas n).aestronglyMeasurable ?_
    filter_upwards [he_pos] with ω hω
    rw [hf]
    change ‖S.dVar.indicator d ω * min (n : ℝ) (1 / S.propScore d ω)‖ ≤ (n : ℝ)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |S.dVar.indicator d ω| ≤ 1 := by
      rcases S.dVar.indicator_eq_one_or_zero d ω with h | h <;> rw [h] <;> simp
    have hmn : 0 ≤ min (n : ℝ) (1 / S.propScore d ω) :=
      le_min (Nat.cast_nonneg n) (le_of_lt (one_div_pos.mpr hω))
    have h2 : |min (n : ℝ) (1 / S.propScore d ω)| ≤ (n : ℝ) := by
      rw [abs_of_nonneg hmn]; exact min_le_left _ _
    calc |S.dVar.indicator d ω| * |min (n : ℝ) (1 / S.propScore d ω)|
        ≤ 1 * (n : ℝ) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = (n : ℝ) := one_mul _
  -- monotone in `n`.
  have hf_mono : ∀ᵐ ω ∂P.μ, Monotone fun n => f n ω := by
    filter_upwards with ω
    intro a b hab
    simp only [hf, POBackdoorSystem.ipwTrunc]
    rcases S.dVar.indicator_eq_one_or_zero d ω with h | h
    · rw [h]
      exact mul_le_mul_of_nonneg_left (min_le_min (Nat.cast_le.mpr hab) le_rfl) zero_le_one
    · rw [h]; simp
  -- a.e. convergence `f n ω → ipwDensity d ω`.
  have hf_tend : ∀ᵐ ω ∂P.μ, Filter.Tendsto (fun n => f n ω) Filter.atTop
      (nhds (S.ipwDensity d ω)) := by
    filter_upwards [he_pos] with ω hω
    have hfω : (fun n => f n ω)
        = (fun n : ℕ => S.dVar.indicator d ω * min (n : ℝ) (1 / S.propScore d ω)) := rfl
    have hd : S.ipwDensity d ω = S.dVar.indicator d ω * (1 / S.propScore d ω) := by
      rw [POBackdoorSystem.ipwDensity, div_eq_mul_one_div]
    rw [hfω, hd]
    have hev : (fun n : ℕ => min (n : ℝ) (1 / S.propScore d ω))
        =ᶠ[Filter.atTop] (fun _ => 1 / S.propScore d ω) := by
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
        (1 / S.propScore d ω)] with n hn
      exact min_eq_right hn
    exact (((Filter.tendsto_congr' hev).mpr tendsto_const_nhds).const_mul
      (S.dVar.indicator d ω))
  -- nonnegativity of `f n` and of `ipwDensity d`.
  have hf_nn : ∀ n, 0 ≤ᵐ[P.μ] f n := by
    intro n; filter_upwards [he_pos] with ω hω
    rw [hf]
    refine mul_nonneg ?_ (le_min (Nat.cast_nonneg n) (le_of_lt (one_div_pos.mpr hω)))
    rcases S.dVar.indicator_eq_one_or_zero d ω with h | h <;> rw [h]; norm_num
  have hnn : 0 ≤ᵐ[P.μ] S.ipwDensity d := by
    filter_upwards [he_pos] with ω hω
    refine div_nonneg ?_ (le_of_lt hω)
    rcases S.dVar.indicator_eq_one_or_zero d ω with h | h <;> rw [h]; norm_num
  -- per-`n` integral bound `∫ f n ≤ 1`, via pull-out and `g n = min n (1/e_d)·e_d ≤ 1`.
  have hf_bd : ∀ n, ∫ ω, f n ω ∂P.μ ≤ 1 := by
    intro n
    have hcomm : (fun ω => f n ω)
        = (fun ω => min (n : ℝ) (1 / S.propScore d ω) * S.dVar.indicator d ω) := by
      funext ω; simp only [hf, POBackdoorSystem.ipwTrunc]; ring
    have hpull := S.integral_mul_indicator_eq_integral_mul_propScore d (hmin_sm n)
      (by rw [← hcomm]; exact hf_int n)
    have hg_int : Integrable
        (fun ω => min (n : ℝ) (1 / S.propScore d ω) * S.propScore d ω) P.μ := by
      refine (integrable_const (1 : ℝ)).mono'
        ((measurable_const.min (measurable_const.div he_meas)).mul he_meas).aestronglyMeasurable ?_
      filter_upwards [he_pos] with ω hω
      have h0 : 0 ≤ min (n : ℝ) (1 / S.propScore d ω) * S.propScore d ω :=
        mul_nonneg (le_min (Nat.cast_nonneg n) (le_of_lt (one_div_pos.mpr hω))) (le_of_lt hω)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      calc min (n : ℝ) (1 / S.propScore d ω) * S.propScore d ω
          ≤ (1 / S.propScore d ω) * S.propScore d ω :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hω)
        _ = 1 := by field_simp
    calc ∫ ω, f n ω ∂P.μ
        = ∫ ω, min (n : ℝ) (1 / S.propScore d ω) * S.dVar.indicator d ω ∂P.μ := by rw [hcomm]
      _ = ∫ ω, min (n : ℝ) (1 / S.propScore d ω) * S.propScore d ω ∂P.μ := hpull
      _ ≤ ∫ _ω, (1 : ℝ) ∂P.μ := by
          refine integral_mono_ae hg_int (integrable_const 1) ?_
          filter_upwards [he_pos] with ω hω
          calc min (n : ℝ) (1 / S.propScore d ω) * S.propScore d ω
              ≤ (1 / S.propScore d ω) * S.propScore d ω :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hω)
            _ = 1 := by field_simp
      _ = 1 := by simp
  -- `HasFiniteIntegral` via the ENNReal lintegral bound `∫⁻ ofReal (ipwDensity) ≤ 1 < ∞`.
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn]
  -- monotone convergence `∫⁻ ofReal (f n) → ∫⁻ ofReal (ipwDensity d)`.
  have htends : Filter.Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P.μ) Filter.atTop
      (nhds (∫⁻ ω, ENNReal.ofReal (S.ipwDensity d ω) ∂P.μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (ENNReal.measurable_ofReal.comp (hf_meas n)).aemeasurable) ?_ ?_
    · filter_upwards [hf_mono] with ω hmono a b hab
      exact ENNReal.ofReal_le_ofReal (hmono hab)
    · filter_upwards [hf_tend] with ω htend
      exact (ENNReal.continuous_ofReal.tendsto _).comp htend
  -- each `∫⁻ ofReal (f n) = ofReal (∫ f n) ≤ 1`.
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P.μ ≤ 1 := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf_int n) (hf_nn n)]
    exact ENNReal.ofReal_le_one.mpr (hf_bd n)
  exact lt_of_le_of_lt (le_of_tendsto' htends hbound) ENNReal.one_lt_top

/-- **Core distributional backdoor identity.**  For every bounded measurable
`g : ℝ → ℝ`, `∫ g(Y(d)) dμ = ∫ g(Y)·1_{D=d}/e_d dμ`. -/
lemma integral_comp_YofD_eq [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.DistributionalAssumptions) (d : Bool) {g : ℝ → ℝ} (hg : Measurable g)
    {C : ℝ} (hg_bdd : ∀ y, |g y| ≤ C) :
    ∫ ω, g (S.YofD d ω) ∂P.μ
      = ∫ ω, g (S.factualY ω) * S.ipwDensity d ω ∂P.μ := by
  classical
  -- Measurability of the composites and the indicator / propensity score.
  have hgY_meas : Measurable (fun ω => g (S.factualY ω)) := hg.comp S.measurable_factualY
  have hgYd_meas : Measurable (fun ω => g (S.YofD d ω)) := hg.comp (S.measurable_YofD d)
  have hind_meas : Measurable (S.dVar.indicator d) := S.dVar.measurable_indicator d
  have he_sm : StronglyMeasurable[S.sigmaX] (S.propScore d) := S.stronglyMeasurable_propScore d
  have he_pos : ∀ᵐ ω ∂P.μ, 0 < S.propScore d ω := S.propScore_pos hA d
  have hipw_meas : Measurable (S.ipwDensity d) :=
    hind_meas.div (he_sm.mono S.sigmaX_le).measurable
  have hipw_nn : 0 ≤ᵐ[P.μ] S.ipwDensity d := by
    filter_upwards [he_pos] with ω hω
    refine div_nonneg ?_ hω.le
    rcases S.dVar.indicator_eq_one_or_zero d ω with h | h <;> simp [h]
  -- Integrability of the pieces (everything bounded by `C`, resp. `C·ipw`).
  have hgYd_int : Integrable (fun ω => g (S.YofD d ω)) P.μ :=
    (integrable_const C).mono' hgYd_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hg_bdd _))
  have prod_int : Integrable (fun ω => S.dVar.indicator d ω * g (S.YofD d ω)) P.μ :=
    (integrable_const C).mono' (hind_meas.mul hgYd_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |S.dVar.indicator d ω| ≤ 1 := by
          rcases S.dVar.indicator_eq_one_or_zero d ω with h | h <;> rw [h] <;> simp
        calc |S.dVar.indicator d ω| * |g (S.YofD d ω)|
            ≤ 1 * C := mul_le_mul h1 (hg_bdd _) (abs_nonneg _) zero_le_one
          _ = C := one_mul _))
  have hgYd_ipw_int : Integrable (fun ω => g (S.YofD d ω) * S.ipwDensity d ω) P.μ := by
    refine ((S.ipwDensity_integrable hA d).const_mul C).mono'
      (hgYd_meas.mul hipw_meas).aestronglyMeasurable ?_
    filter_upwards [hipw_nn] with ω hω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hω]
    exact mul_le_mul_of_nonneg_right (hg_bdd _) hω
  -- (a) Consistency: `g(Y)·ipw = g(Y(d))·ipw` (agree on `{D=d}`, both `0` off it).
  have hcons : (fun ω => g (S.factualY ω) * S.ipwDensity d ω)
      = (fun ω => g (S.YofD d ω) * S.ipwDensity d ω) := by
    funext ω
    by_cases hω : ω ∈ S.dVar.event d
    · have hcf : S.YofD d ω = S.factualY ω :=
        POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar d (Ne.symm S.hDY) hω
      rw [hcf]
    · have hind0 : S.dVar.indicator d ω = 0 := Set.indicator_of_notMem hω _
      simp [POBackdoorSystem.ipwDensity, hind0]
  rw [hcons]
  -- (b) Conditional independence `Y(d) ⟂ D | σ(X)`, projected from unconfoundedness.
  let ψ : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
    fun f => match d with
      | true  => f (0 : Fin 2)
      | false => f (1 : Fin 2)
  have hψ_meas : Measurable ψ := by
    cases d with
    | true  => exact measurable_pi_apply (0 : Fin 2)
    | false => exact measurable_pi_apply (1 : Fin 2)
  have hYofD_eq : S.YofD d = ψ ∘ S.cfBundle.jointValue := by funext ω; cases d <;> rfl
  have hCI : ProbabilityTheory.CondIndepFun S.sigmaX S.sigmaX_le S.factualD (S.YofD d) P.μ := by
    have hproj := hA.unconfoundedness.project (ψ := ψ) hψ_meas
    rw [hYofD_eq]; exact hproj
  -- The set-indicator packaging `u (factualD ω) = 1_{D=d} ω`.
  let u : Bool → ℝ := ({d} : Set Bool).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u := measurable_const.indicator (MeasurableSet.singleton d)
  have hu_eq : (fun ω => u (S.factualD ω)) = S.dVar.indicator d := by
    funext ω
    unfold POVar.indicator
    by_cases h : S.factualD ω = d
    · have h1 : S.factualD ω ∈ ({d} : Set Bool) := h
      have h2 : ω ∈ S.dVar.event d := h
      rw [show u (S.factualD ω) = (1 : ℝ) from Set.indicator_of_mem h1 _,
          Set.indicator_of_mem h2]
    · have h1 : S.factualD ω ∉ ({d} : Set Bool) := h
      have h2 : ω ∉ S.dVar.event d := h
      rw [show u (S.factualD ω) = (0 : ℝ) from Set.indicator_of_notMem h1 _,
          Set.indicator_of_notMem h2]
  -- (★) `E[1_{D=d}·g(Y(d)) | σX] =ᵐ e_d · E[g(Y(d)) | σX]`.
  have hstar0 := condExp_mul_of_condIndep (μ := P.μ) (m := S.sigmaX) S.sigmaX_le
    (f := S.factualD) (g := S.YofD d) S.measurable_factualD (S.measurable_YofD d) hCI
    (u := u) (v := g) hu_meas hg
    (by rw [hu_eq]; exact S.dVar.integrable_indicator d) hgYd_int
    (by
      have e1 : (fun ω => u (S.factualD ω) * g (S.YofD d ω))
          = (fun ω => S.dVar.indicator d ω * g (S.YofD d ω)) := by
        funext ω; rw [congr_fun hu_eq ω]
      rw [e1]; exact prod_int)
  have hstar : P.μ[fun ω => S.dVar.indicator d ω * g (S.YofD d ω) | S.sigmaX]
      =ᵐ[P.μ] P.μ[S.dVar.indicator d | S.sigmaX]
        * P.μ[fun ω => g (S.YofD d ω) | S.sigmaX] := by
    have e1 : (fun ω => u (S.factualD ω) * g (S.YofD d ω))
        = (fun ω => S.dVar.indicator d ω * g (S.YofD d ω)) := by
      funext ω; rw [congr_fun hu_eq ω]
    rw [e1, hu_eq] at hstar0
    exact hstar0
  -- (c) Pull the `σ(X)`-measurable factor `1/e_d` out and cancel.
  set k : P.Ω → ℝ := fun ω => 1 / S.propScore d ω with hk_def
  have hkey : (fun ω => g (S.YofD d ω) * S.ipwDensity d ω)
      = (fun ω => k ω * (S.dVar.indicator d ω * g (S.YofD d ω))) := by
    funext ω; simp only [hk_def, POBackdoorSystem.ipwDensity]; ring
  have kprod_int : Integrable
      (fun ω => k ω * (S.dVar.indicator d ω * g (S.YofD d ω))) P.μ := by
    rw [← hkey]; exact hgYd_ipw_int
  have hk_sm : StronglyMeasurable[S.sigmaX] k := by
    rw [hk_def]
    exact (measurable_const.div he_sm.measurable).stronglyMeasurable
  have hfin : P.μ[fun ω => k ω * (S.dVar.indicator d ω * g (S.YofD d ω)) | S.sigmaX]
      =ᵐ[P.μ] P.μ[fun ω => g (S.YofD d ω) | S.sigmaX] := by
    have hpull : P.μ[fun ω => k ω * (S.dVar.indicator d ω * g (S.YofD d ω)) | S.sigmaX]
        =ᵐ[P.μ] (fun ω => k ω
          * (P.μ[fun ω => S.dVar.indicator d ω * g (S.YofD d ω) | S.sigmaX]) ω) := by
      have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (μ := P.μ)
        (m := S.sigmaX) (f := k)
        (g := fun ω => S.dVar.indicator d ω * g (S.YofD d ω)) hk_sm kprod_int prod_int
      filter_upwards [h] with ω hω; simpa [Pi.mul_apply] using hω
    filter_upwards [hpull, hstar, he_pos] with ω h1 h2 hpos
    rw [h1]
    simp only [Pi.mul_apply] at h2 ⊢
    rw [h2]
    have hps : (P.μ[S.dVar.indicator d | S.sigmaX]) ω = S.propScore d ω := rfl
    rw [hps]
    simp only [hk_def, one_div]
    exact inv_mul_cancel_left₀ hpos.ne' _
  -- Assemble the integral chain via `∫ φ = ∫ E[φ | σX]`.
  rw [hkey,
    ← MeasureTheory.integral_condExp S.sigmaX_le (f := fun ω => g (S.YofD d ω)),
    ← MeasureTheory.integral_condExp S.sigmaX_le
      (f := fun ω => k ω * (S.dVar.indicator d ω * g (S.YofD d ω)))]
  exact MeasureTheory.integral_congr_ae hfin.symm

/-- **Distributional backdoor identification.**  Under consistency,
unconfoundedness, and common support, the law of the potential outcome under
treatment arm `d` equals the observable inverse-probability-weighted outcome law
for that arm. -/
theorem cfUnderLaw_eq_ipwLaw [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.DistributionalAssumptions) (d : Bool) :
    S.yVar.cfUnderLaw S.dVar d P.μ = S.ipwLaw d P.μ := by
  have hipw_int : Integrable (S.ipwDensity d) P.μ := S.ipwDensity_integrable hA d
  have hipw_nn : 0 ≤ᵐ[P.μ] S.ipwDensity d := by
    filter_upwards [S.propScore_pos hA d] with ω hω
    refine div_nonneg ?_ hω.le
    rcases S.dVar.indicator_eq_one_or_zero d ω with h | h <;> simp [h]
  -- Compare the two measures on every measurable set, via the `g = 1_s` transform.
  refine MeasureTheory.Measure.ext fun s hs => ?_
  have hT_meas : MeasurableSet ((S.YofD d) ⁻¹' s) := S.measurable_YofD d hs
  have hU_meas : MeasurableSet (S.factualY ⁻¹' s) := S.measurable_factualY hs
  -- Bounded measurable test function `g = 1_s`.
  set g : ℝ → ℝ := s.indicator (fun _ => (1 : ℝ)) with hg_def
  have hg_meas : Measurable g := measurable_const.indicator hs
  have hg_bdd : ∀ y, |g y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ s
    · simp [hg_def, Set.indicator_of_mem hy]
    · simp [hg_def, Set.indicator_of_notMem hy]
  -- `g ∘ Y(d)` and `g ∘ Y · ipw` rewritten as set indicators.
  have hcompYd : (fun ω => g (S.YofD d ω))
      = ((S.YofD d) ⁻¹' s).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rw [hg_def]
    by_cases hω : S.YofD d ω ∈ s
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ (S.YofD d) ⁻¹' s from hω)]
    · rw [Set.indicator_of_notMem hω,
        Set.indicator_of_notMem (show ω ∉ (S.YofD d) ⁻¹' s from hω)]
  have hcompY : (fun ω => g (S.factualY ω) * S.ipwDensity d ω)
      = (S.factualY ⁻¹' s).indicator (S.ipwDensity d) := by
    funext ω
    by_cases hω : S.factualY ω ∈ s <;> simp [hg_def, hω]
  -- Express both sides as a preimage measure / set lintegral.
  have hLHS : S.yVar.cfUnderLaw S.dVar d P.μ s = P.μ ((S.YofD d) ⁻¹' s) := by
    change (P.μ.map (S.YofD d)) s = _
    exact MeasureTheory.Measure.map_apply (S.measurable_YofD d) hs
  have hRHS : S.ipwLaw d P.μ s
      = ∫⁻ ω in (S.factualY ⁻¹' s), ENNReal.ofReal (S.ipwDensity d ω) ∂P.μ := by
    change ((P.μ.withDensity (fun ω => ENNReal.ofReal (S.ipwDensity d ω))).map S.factualY) s = _
    rw [MeasureTheory.Measure.map_apply S.measurable_factualY hs,
        MeasureTheory.withDensity_apply _ hU_meas]
  -- Bochner-level identities.
  have key := S.integral_comp_YofD_eq hA d hg_meas hg_bdd
  have e_ind_Y : ∫ ω, g (S.factualY ω) * S.ipwDensity d ω ∂P.μ
      = ∫ ω in (S.factualY ⁻¹' s), S.ipwDensity d ω ∂P.μ := by
    rw [hcompY]; exact MeasureTheory.integral_indicator hU_meas
  have e_ind_Yd : ∫ ω, g (S.YofD d ω) ∂P.μ = (P.μ ((S.YofD d) ⁻¹' s)).toReal := by
    rw [hcompYd, MeasureTheory.integral_indicator hT_meas, MeasureTheory.integral_const,
        smul_eq_mul, mul_one, MeasureTheory.measureReal_restrict_apply_univ]
    rfl
  -- Glue everything through `ofReal`.
  have hchain : ∫⁻ ω in (S.factualY ⁻¹' s), ENNReal.ofReal (S.ipwDensity d ω) ∂P.μ
      = P.μ ((S.YofD d) ⁻¹' s) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hipw_int.restrict) (ae_restrict_of_ae hipw_nn),
        ← e_ind_Y, ← key, e_ind_Yd, ENNReal.ofReal_toReal (measure_ne_top P.μ _)]
  rw [hLHS, hRHS]
  exact hchain.symm

end POBackdoorSystem

end PO
end Causalean
