/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fold-B empirical-process bound under conditional independence

For sample-split estimators (PlugIn, DML), the asymptotic-linearity remainder
decomposes (after pulling out the centered IF main term) into

    G_n(ω) := (1/√|B(n)|) Σ_{i ∈ B(n)} (f(n, ω, Z_i ω) − ∫ f(n, ω, ·) dP)
              -- centered fold-B sum
    B_n(ω) := √|B(n)| · ∫ f(n, ω, ·) dP                -- bias term

where `f(n, ω, ·)` is fold-A-measurable in `ω` (it depends on the fitted
nuisances which use `(Z_i)_{i ∈ A(n)}` only).  Conditioning on the fold-A
σ-algebra, `(Z_i)_{i ∈ B(n)}` are i.i.d. copies of `P` and `f(n, ω, ·)` is
deterministic, so:

* conditional second moment of `G_n` is bounded by `‖f(n, ω, ·)‖²_{L²(P)}`
  (sum-of-i.i.d. variance ÷ √|B|² × |B| = variance);
* `|B_n| ≤ √|B(n)| · ‖f(n, ω, ·)‖_{L²(P)}` by Cauchy–Schwarz on a probability
  measure (`abs_integral_le_eLpNorm_two`).

Both then reduce to the L²-rate hypothesis on `‖f(n, ω, ·)‖_{L²(P)}` plus the
fixed-split-ratio condition `|B(n)|/n → c ∈ (0, 1)`.

This file provides:

* `foldB_centered_sum_isLittleOp_one`  — `G_n = o_p(1)` from `‖f‖₂ = o_p(1)`
                                          via conditional Chebyshev.
* `sqrtFoldB_integral_isLittleOp_one`  — `B_n = o_p(1)` from
                                          `‖f‖₂ = o_p(n^{-1/2})` plus
                                          `|B(n)|/n → c`.

Causal-agnostic; candidate Mathlib upstream once stable.
-/

import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Mathlib.ELpNormMeasurable
import Causalean.Mathlib.IIDCenteredSum
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fold-B empirical-process bounds

This module proves the empirical-process estimates used to turn sample-split
orthogonal expansions into stochastic remainders.  The main one-shot results are
`foldB_centered_sum_isLittleOp_one`, which makes a centered evaluation-fold sum
`o_p(1)` from an `L²(P)` `o_p(1)` nuisance rate, and
`sqrtFoldB_integral_isLittleOp_one`, which controls the fold-B bias term from an
`o_p(n^{-1/2})` `L²(P)` rate and a fixed split proportion.

The same abstract conditional-independence argument is reused for K-fold splits
through `KFoldSplit.fold_centered_sum_isLittleOp_one` and
`KFoldSplit.sqrtFold_integral_isLittleOp_one`.  The public helper `oneShot_iid`
records the fold-B product-law bridge needed by downstream local empirical
process modules.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure P]

/-! ## Abstract centered evaluation-fold empirical sum

The lemmas in this section are parameterised by:

* `eval n : Finset ℕ` — the evaluation-fold index set at horizon `n`
  (e.g. `OneShotSplit.foldB n` or `KFoldSplit.fold n k`),
* `m_train n : MeasurableSpace Ω` — the training-fold σ-algebra
  (e.g. the comap σ-algebra of the training-fold coordinate map),
* `h_train_le`, `h_indep`, `h_iid` — abstracted independence and i.i.d.
  product-law hypotheses.

This separates the conditional Chebyshev / second-moment / Cauchy–Schwarz
proof skeleton from the choice of split (one-shot vs K-fold). The
OneShot-specific public lemmas at the end of this file are thin wrappers
around these abstract versions, and the analogous KFold corollaries follow
without any additional analytic content. -/

/-- The fold-A σ-algebra is contained in the ambient σ-algebra on `Ω`,
because each `S.Z i` is measurable (so the fold-A coordinate map is
measurable, and `comap` of a measurable map is `≤` the source σ-algebra). -/
private lemma foldA_sigma_le
    {S : IIDSample Ω X μ P} (split : OneShotSplit S) (n : ℕ) :
    (MeasurableSpace.comap
      (fun ω (i : split.foldA n) => S.Z i ω) inferInstance :
        MeasurableSpace Ω) ≤ (inferInstance : MeasurableSpace Ω) := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact (measurable_pi_iff.mpr fun i : split.foldA n => S.meas i) ht

/-- The training-fold σ-algebra of a K-fold split (the comap σ-algebra of
the training-fold coordinate map) is contained in the ambient σ-algebra. -/
private lemma trainComplement_sigma_le
    {S : IIDSample Ω X μ P} {K : ℕ} (split : KFoldSplit S K)
    (n : ℕ) (k : Fin K) :
    (MeasurableSpace.comap
      (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance :
        MeasurableSpace Ω) ≤ (inferInstance : MeasurableSpace Ω) := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact (measurable_pi_iff.mpr
    fun i : split.trainComplement n k => S.meas i) ht

/-- **Abstract second-moment bound for the centered evaluation-fold sum.**

Direct application of `iid_centered_sum_sq_lintegral_le`. -/
private lemma centeredEvalSum_sq_lintegral_le_core
    (S : IIDSample Ω X μ P)
    (eval : ℕ → Finset ℕ)
    (m_train : ℕ → MeasurableSpace Ω)
    (h_train_le : ∀ n, m_train n ≤ (inferInstance : MeasurableSpace Ω))
    (h_indep :
      ∀ n,
        Indep (m_train n)
          (MeasurableSpace.comap
            (fun ω (i : eval n) => S.Z i ω) inferInstance) μ)
    (h_iid :
      ∀ n,
        μ.map (fun ω (i : eval n) => S.Z i ω) =
          Measure.pi (fun _ : eval n => P))
    (g : ℕ → Ω → X → ℝ)
    (hg_uncurry_train :
      ∀ n,
        Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
          (Function.uncurry (g n)))
    (hg_memLp : ∀ n ω, MemLp (g n ω) 2 P)
    (n : ℕ) (hn : 0 < (eval n).card) :
    ∫⁻ ω, ENNReal.ofReal (((Real.sqrt ((eval n).card : ℝ))⁻¹ *
        ∑ i ∈ eval n, (g n ω (S.Z i ω) - ∫ x, g n ω x ∂P)) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g n ω) 2 P).toReal ^ 2) ∂μ :=
  Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
    (s := eval n) hn (W := S.Z) (fun i _ => S.meas i)
    (m_train n) (h_train_le n) (h_indep n) (h_iid n)
    (g n) (hg_uncurry_train n) (hg_memLp n)

/-- Abstract wrapper for `centeredEvalSum_sq_lintegral_le_core`. -/
private lemma centeredEvalSum_sq_lintegral_le
    (S : IIDSample Ω X μ P)
    (eval : ℕ → Finset ℕ)
    (m_train : ℕ → MeasurableSpace Ω)
    (h_train_le : ∀ n, m_train n ≤ (inferInstance : MeasurableSpace Ω))
    (h_indep :
      ∀ n,
        Indep (m_train n)
          (MeasurableSpace.comap
            (fun ω (i : eval n) => S.Z i ω) inferInstance) μ)
    (h_iid :
      ∀ n,
        μ.map (fun ω (i : eval n) => S.Z i ω) =
          Measure.pi (fun _ : eval n => P))
    (g : ℕ → Ω → X → ℝ)
    (hg_uncurry_train :
      ∀ n,
        Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
          (Function.uncurry (g n)))
    (hg_memLp : ∀ n ω, MemLp (g n ω) 2 P)
    (n : ℕ) (hn : 0 < (eval n).card) :
    ∫⁻ ω, ENNReal.ofReal (((Real.sqrt ((eval n).card : ℝ))⁻¹ *
        ∑ i ∈ eval n, (g n ω (S.Z i ω) - ∫ x, g n ω x ∂P)) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g n ω) 2 P).toReal ^ 2) ∂μ :=
  centeredEvalSum_sq_lintegral_le_core S eval m_train h_train_le h_indep
    h_iid g hg_uncurry_train hg_memLp n hn

/-- **Abstract: truncated centered evaluation-fold sum is `o_p(1)`.**

Markov + the second-moment bound + bounded BCT applied at the eval/train
σ-algebra level. -/
private lemma evalSum_truncated_isLittleOp_one
    (S : IIDSample Ω X μ P)
    (eval : ℕ → Finset ℕ)
    (m_train : ℕ → MeasurableSpace Ω)
    (h_train_le : ∀ n, m_train n ≤ (inferInstance : MeasurableSpace Ω))
    (h_indep :
      ∀ n,
        Indep (m_train n)
          (MeasurableSpace.comap
            (fun ω (i : eval n) => S.Z i ω) inferInstance) μ)
    (h_iid :
      ∀ n,
        μ.map (fun ω (i : eval n) => S.Z i ω) =
          Measure.pi (fun _ : eval n => P))
    (h_eval_card_grow : Tendsto (fun n => (eval n).card) atTop atTop)
    (g : ℕ → Ω → X → ℝ)
    (hg_meas : ∀ n, Measurable (Function.uncurry (g n)))
    (hg_uncurry_train :
      ∀ n,
        Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
          (Function.uncurry (g n)))
    (hg_memLp : ∀ n ω, MemLp (g n ω) 2 P)
    (h_BCT :
      Tendsto
        (fun n => ∫⁻ ω,
          ENNReal.ofReal ((eLpNorm (g n ω) 2 P).toReal ^ 2) ∂μ)
        atTop (𝓝 0)) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((eval n).card : ℝ))⁻¹ *
          ∑ i ∈ eval n, (g n ω (S.Z i ω) - ∫ x, g n ω x ∂P))
      (fun _ => (1 : ℝ)) μ := by
  let Y : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt ((eval n).card : ℝ))⁻¹ *
      ∑ i ∈ eval n, (g n ω (S.Z i ω) - ∫ x, g n ω x ∂P)
  let B : ℕ → ENNReal := fun n =>
    ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g n ω) 2 P).toReal ^ 2) ∂μ
  have hcard_pos :
      ∀ᶠ n in atTop, 0 < (eval n).card :=
    h_eval_card_grow.eventually_gt_atTop 0
  have hY_sq_aemeas : ∀ n,
      AEMeasurable (fun ω => ENNReal.ofReal ((Y n ω) ^ 2)) μ := by
    intro n
    have hint : AEStronglyMeasurable (fun ω => ∫ x, g n ω x ∂P) μ := by
      exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        ((hg_meas n).aestronglyMeasurable)
    have hsum :
        AEStronglyMeasurable
          (fun ω => ∑ i ∈ eval n,
            (g n ω (S.Z i ω) - ∫ x, g n ω x ∂P)) μ := by
      convert Finset.aestronglyMeasurable_sum (s := eval n)
        (f := fun i ω => g n ω (S.Z i ω) - ∫ x, g n ω x ∂P)
        (fun i _ =>
          (((hg_meas n).comp
            (measurable_id.prodMk (S.meas i))).aestronglyMeasurable).sub hint) using 1
      ext ω
      simp
    have hY_ae : AEMeasurable (Y n) μ := by
      simpa [Y] using
        (hsum.const_mul (Real.sqrt ((eval n).card : ℝ))⁻¹).aemeasurable
    exact (hY_ae.pow_const 2).ennreal_ofReal
  intro ε hε
  have hmarkov_bound : ∀ᶠ n in atTop,
      μ {ω | ε < |Y n ω|} ≤
        (ENNReal.ofReal (ε ^ 2))⁻¹ * B n := by
    filter_upwards [hcard_pos] with n hn
    have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hε_ne_zero : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact hεsq_pos
    have hε_ne_top : ENNReal.ofReal (ε ^ 2) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hsubset :
        {ω | ε < |Y n ω|} ⊆
          {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal ((Y n ω) ^ 2)} := by
      intro ω hω
      have hsq : ε ^ 2 < (Y n ω) ^ 2 := by
        rw [← sq_abs (Y n ω), sq_lt_sq]
        simpa [abs_of_pos hε] using hω
      exact ENNReal.ofReal_le_ofReal (le_of_lt hsq)
    calc
      μ {ω | ε < |Y n ω|}
          ≤ μ {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal ((Y n ω) ^ 2)} :=
            measure_mono hsubset
      _ ≤ (∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂μ) / ENNReal.ofReal (ε ^ 2) :=
            MeasureTheory.meas_ge_le_lintegral_div (hY_sq_aemeas n)
              hε_ne_zero hε_ne_top
      _ ≤ B n / ENNReal.ofReal (ε ^ 2) := by
            gcongr
            simpa [Y, B] using
              centeredEvalSum_sq_lintegral_le S eval m_train h_train_le
                h_indep h_iid g hg_uncurry_train hg_memLp n hn
      _ = (ENNReal.ofReal (ε ^ 2))⁻¹ * B n := by
            rw [ENNReal.div_eq_inv_mul, mul_comm]
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  let e : ENNReal := ENNReal.ofReal (ε ^ 2)
  have he_pos : 0 < e := by
    dsimp [e]
    exact ENNReal.ofReal_pos.mpr hεsq_pos
  have he_ne_zero : e ≠ 0 := ne_of_gt he_pos
  have he_ne_top : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.ofReal_ne_top
  have hδe_pos : 0 < δ * e :=
    pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hδ) he_ne_zero)
  have hB_small := (ENNReal.tendsto_nhds_zero.mp h_BCT) (δ * e) hδe_pos
  filter_upwards [hmarkov_bound, hB_small] with n hmarkov hB
  have hscaled_le : e⁻¹ * B n ≤ δ := by
    have hmul : e * (e⁻¹ * B n) ≤ e * δ := by
      calc
        e * (e⁻¹ * B n) = B n := ENNReal.mul_inv_cancel_left he_ne_zero he_ne_top
        _ ≤ δ * e := hB
        _ = e * δ := by rw [mul_comm]
    exact (ENNReal.mul_le_mul_iff_right he_ne_zero he_ne_top).mp hmul
  simpa [Y, e] using hmarkov.trans hscaled_le

/-! ## OneShot- and KFold-specific independence and i.i.d. helpers

Bridge `OneShotSplit.folds_indep` / `KFoldSplit.folds_indep` and
`IIDSample.indep` to the abstract `h_indep` / `h_iid` parameters of the
abstract layer. -/

/-- OneShot independence specialisation: `IndepFun = Indep ∘ comap ∘ comap`. -/
private lemma oneShot_indep
    {S : IIDSample Ω X μ P} (split : OneShotSplit S) (n : ℕ) :
    Indep
      (MeasurableSpace.comap
        (fun ω (i : split.foldA n) => S.Z i ω) inferInstance)
      (MeasurableSpace.comap
        (fun ω (i : split.foldB n) => S.Z i ω) inferInstance) μ :=
  split.folds_indep n

/-- OneShot evaluation-fold i.i.d. product law. **Public** because the
orthogonal-learning modulus chain consumes it as the joint-law bridge between fold B and
`Measure.pi` (see `Estimation/OrthogonalLearning/LocalEmpProcess/Rademacher.lean`). -/
lemma oneShot_iid
    (S : IIDSample Ω X μ P) (split : OneShotSplit S) (n : ℕ) :
    μ.map (fun ω (i : split.foldB n) => S.Z i ω) =
      Measure.pi (fun _ : split.foldB n => P) := by
  have hindep_s : iIndepFun (fun i : split.foldB n => S.Z i) μ := by
    exact S.indep.precomp Subtype.val_injective
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : split.foldB n => (S.meas i).aemeasurable)).mp hindep_s
  calc
    μ.map (fun ω (i : split.foldB n) => S.Z i ω)
        = Measure.pi (fun i : split.foldB n => μ.map (S.Z i)) := hmap
    _ = Measure.pi (fun _ : split.foldB n => P) := by
        congr with i
        rw [← (S.identDist i).map_eq, S.law]

/-- KFold independence specialisation. -/
private lemma kFold_indep
    {S : IIDSample Ω X μ P} {K : ℕ} (split : KFoldSplit S K)
    (n : ℕ) (k : Fin K) :
    Indep
      (MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance)
      (MeasurableSpace.comap
        (fun ω (i : split.fold n k) => S.Z i ω) inferInstance) μ := by
  -- `folds_indep` gives `IndepFun (fold) (trainComplement)`; we want it
  -- with the arguments swapped.
  have hIF := (split.folds_indep n k).symm
  exact hIF

/-- KFold evaluation-fold i.i.d. product law. -/
private lemma kFold_iid
    (S : IIDSample Ω X μ P) {K : ℕ} (split : KFoldSplit S K)
    (n : ℕ) (k : Fin K) :
    μ.map (fun ω (i : split.fold n k) => S.Z i ω) =
      Measure.pi (fun _ : split.fold n k => P) := by
  have hindep_s : iIndepFun (fun i : split.fold n k => S.Z i) μ := by
    exact S.indep.precomp Subtype.val_injective
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : split.fold n k => (S.meas i).aemeasurable)).mp hindep_s
  calc
    μ.map (fun ω (i : split.fold n k) => S.Z i ω)
        = Measure.pi (fun i : split.fold n k => μ.map (S.Z i)) := hmap
    _ = Measure.pi (fun _ : split.fold n k => P) := by
        congr with i
        rw [← (S.identDist i).map_eq, S.law]

/-! ## Abstract bias term: `√|eval n| · ∫ f(n, ω, ·) dP` is `o_p(1)` -/

/-- **Abstract: bias term is `o_p(1)` under fixed-ratio split.**

Same proof as the OneShot version, but parameterised by an arbitrary
evaluation-fold index `eval n` with `((eval n).card : ℝ) / n → c ∈ (0, 1)`.
The fold-A measurability hypothesis is unnecessary because the integral
already collapses fold-dependence. -/
private lemma evalSum_bias_isLittleOp_one
    (_S : IIDSample Ω X μ P)
    (eval : ℕ → Finset ℕ)
    {c : ℝ} (hc_pos : 0 < c)
    (h_eval_ratio :
      Tendsto (fun n => ((eval n).card : ℝ) / n) atTop (𝓝 c))
    (f : ℕ → Ω → X → ℝ)
    (hf_memLp : ∀ n ω, MemLp (f n ω) 2 P)
    (hf_rate :
      IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsLittleOp
      (fun n ω => Real.sqrt ((eval n).card : ℝ) * ∫ x, f n ω x ∂P)
      (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  let C : ℝ := Real.sqrt c + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [Real.sqrt_nonneg c]
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hC2 : c < C ^ 2 := by
    dsimp [C]
    nlinarith [Real.sq_sqrt (le_of_lt hc_pos), Real.sqrt_nonneg c]
  have hratio_event :
      ∀ᶠ n in atTop, ((eval n).card : ℝ) / n < C ^ 2 :=
    h_eval_ratio.eventually_lt_const hC2
  have hn_event : ∀ᶠ n : ℕ in atTop, n ≠ 0 := eventually_ne_atTop 0
  have hnorm_event := (ENNReal.tendsto_nhds_zero.mp
    (hf_rate (ε / C) (div_pos hε hCpos))) δ hδ
  filter_upwards [hratio_event, hn_event, hnorm_event] with n hratio hn_ne hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn_ne
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrtn_pos
  have hcard_le : ((eval n).card : ℝ) ≤ C ^ 2 * (n : ℝ) := by
    have hlt : ((eval n).card : ℝ) < C ^ 2 * (n : ℝ) := by
      field_simp [hn_pos.ne'] at hratio ⊢
      nlinarith
    exact le_of_lt hlt
  have hsqrt_le :
      Real.sqrt ((eval n).card : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt ((eval n).card : ℝ) ≤ Real.sqrt (C ^ 2 * (n : ℝ)) :=
        Real.sqrt_le_sqrt hcard_le
      _ = Real.sqrt (C ^ 2) * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (sq_nonneg C)]
      _ = C * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_sq hCnonneg]
  have hI_le : |∫ x, f n ω x ∂P| ≤ (eLpNorm (f n ω) 2 P).toReal :=
    abs_integral_le_eLpNorm_two (hf_memLp n ω)
  have hsqrtcard_nonneg : 0 ≤ Real.sqrt ((eval n).card : ℝ) :=
    Real.sqrt_nonneg _
  have hlt_prod :
      ε < Real.sqrt ((eval n).card : ℝ) * |∫ x, f n ω x ∂P| := by
    simpa [abs_mul, abs_of_nonneg hsqrtcard_nonneg] using hω
  have hle_prod :
      Real.sqrt ((eval n).card : ℝ) * |∫ x, f n ω x ∂P| ≤
        (C * Real.sqrt (n : ℝ)) * (eLpNorm (f n ω) 2 P).toReal :=
    mul_le_mul hsqrt_le hI_le (abs_nonneg _)
      (mul_nonneg hCnonneg hsqrtn_nonneg)
  have hlt_bound :
      ε < (C * Real.sqrt (n : ℝ)) * (eLpNorm (f n ω) 2 P).toReal :=
    lt_of_lt_of_le hlt_prod hle_prod
  have hrn_eq : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.rpow_neg hn_nonneg]
    rw [← Real.sqrt_eq_rpow]
  have hdiv_lt :
      ε / (C * Real.sqrt (n : ℝ)) < (eLpNorm (f n ω) 2 P).toReal := by
    rw [div_lt_iff₀ (mul_pos hCpos hsqrtn_pos)]
    nlinarith [hlt_bound]
  have hsmall :
      (ε / C) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) <
        (eLpNorm (f n ω) 2 P).toReal := by
    rw [hrn_eq]
    convert hdiv_lt using 1
    field_simp [hCpos.ne', hsqrtn_pos.ne']
  exact hsmall.trans_le (le_abs_self _)

/-! ## Abstract centered evaluation-fold sum is `o_p(1)`

The truncation-based proof (split, BCT, Markov) lifted to the abstract
`(eval, m_train, ...)` parameters. Public OneShot/KFold wrappers below. -/

/-- **Abstract: centered evaluation-fold sum is `o_p(1)` from L²-rate `o_p(1)`.**

This is the abstract version of `foldB_centered_sum_isLittleOp_one`: same
truncation + BCT + Markov + variance proof skeleton, parameterised by
`(eval, m_train)`. -/
private lemma evalSum_isLittleOp_one
    (S : IIDSample Ω X μ P)
    (eval : ℕ → Finset ℕ)
    (m_train : ℕ → MeasurableSpace Ω)
    (h_train_le : ∀ n, m_train n ≤ (inferInstance : MeasurableSpace Ω))
    (h_indep :
      ∀ n,
        Indep (m_train n)
          (MeasurableSpace.comap
            (fun ω (i : eval n) => S.Z i ω) inferInstance) μ)
    (h_iid :
      ∀ n,
        μ.map (fun ω (i : eval n) => S.Z i ω) =
          Measure.pi (fun _ : eval n => P))
    (h_eval_card_grow : Tendsto (fun n => (eval n).card) atTop atTop)
    (f : ℕ → Ω → X → ℝ)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_train :
      ∀ n,
        Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
          (Function.uncurry (f n)))
    (hf_memLp : ∀ n ω, MemLp (f n ω) 2 P)
    (hf_rate :
      IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P).toReal)
        (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((eval n).card : ℝ))⁻¹ *
          ∑ i ∈ eval n, (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
      (fun _ => (1 : ℝ)) μ := by
  -- Truncated `f`: zero out `f n ω` whenever `‖f n ω‖₂ > 1`, otherwise keep.
  set ftil : ℕ → Ω → X → ℝ := fun n ω x =>
    if (eLpNorm (f n ω) 2 P).toReal ≤ 1 then f n ω x else 0
    with hftil_def
  -- Step 1: properties inherited by `ftil`.
  have hftil_meas : ∀ n, Measurable (Function.uncurry (ftil n)) := by
    intro n
    rw [hftil_def]
    have hnorm :
        Measurable (fun p : Ω × X => (eLpNorm (f n p.1) 2 P).toReal) :=
      (Causalean.Mathlib.measurable_eLpNorm_two_toReal_of_uncurry
          (P := P) (hf_meas n)).comp measurable_fst
    simpa using Measurable.ite (measurableSet_le hnorm measurable_const)
      (hf_meas n) measurable_const
  have hftil_uncurry_train : ∀ n,
      Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
        (Function.uncurry (ftil n)) := by
    intro n
    rw [hftil_def]
    have hnorm :
        Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
          (fun p : Ω × X => (eLpNorm (f n p.1) 2 P).toReal) := by
      exact (Causalean.Mathlib.measurable_eLpNorm_two_toReal_of_uncurry_of_factor
        (P := P) (hf_uncurry_train n)).comp measurable_fst
    simpa using Measurable.ite (measurableSet_le hnorm measurable_const)
      (hf_uncurry_train n) measurable_const
  have hftil_memLp : ∀ n ω, MemLp (ftil n ω) 2 P := by
    intro n ω
    rw [hftil_def]
    by_cases h : (eLpNorm (f n ω) 2 P).toReal ≤ 1
    · simpa [h] using hf_memLp n ω
    · simp [h]
  have hftil_bdd : ∀ n ω, (eLpNorm (ftil n ω) 2 P).toReal ≤ 1 := by
    intro n ω
    rw [hftil_def]
    by_cases h : (eLpNorm (f n ω) 2 P).toReal ≤ 1
    · simp [h]
    · simp [h]
  have hftil_norm_le : ∀ n ω,
      (eLpNorm (ftil n ω) 2 P).toReal ≤ (eLpNorm (f n ω) 2 P).toReal := by
    intro n ω
    rw [hftil_def]
    by_cases h : (eLpNorm (f n ω) 2 P).toReal ≤ 1
    · simp [h]
    · simp [h]
  have hftil_rate :
      IsLittleOp (fun n ω => (eLpNorm (ftil n ω) 2 P).toReal)
        (fun _ => (1 : ℝ)) μ := by
    intro ε hε
    have htarget := hf_rate ε hε
    rw [ENNReal.tendsto_nhds_zero] at htarget ⊢
    intro δ hδ
    exact (htarget δ hδ).mono fun n hn => (measure_mono (by
      intro ω hω
      have hω' : ε * (1 : ℝ) < (eLpNorm (ftil n ω) 2 P).toReal := by
        simpa [abs_of_nonneg ENNReal.toReal_nonneg] using hω
      exact (lt_of_lt_of_le hω' (hftil_norm_le n ω)).trans_le
        (le_abs_self _))).trans hn
  -- Step 2: reduce to truncated centered sum.
  have h_diff_to_zero :
      Tendsto (fun n =>
        μ {ω | (Real.sqrt ((eval n).card : ℝ))⁻¹ *
                ∑ i ∈ eval n, (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P) ≠
              (Real.sqrt ((eval n).card : ℝ))⁻¹ *
                ∑ i ∈ eval n, (ftil n ω (S.Z i ω) - ∫ x, ftil n ω x ∂P)})
        atTop (𝓝 0) := by
    have htarget := hf_rate 1 (by norm_num)
    rw [ENNReal.tendsto_nhds_zero] at htarget ⊢
    intro δ hδ
    exact (htarget δ hδ).mono fun n hn => (measure_mono (by
      intro ω hω
      by_contra hleabs
      have hle : (eLpNorm (f n ω) 2 P).toReal ≤ 1 := by
        by_contra hle
        have hgt : 1 < (eLpNorm (f n ω) 2 P).toReal := lt_of_not_ge hle
        have hgtabs :
            1 * (1 : ℝ) < |(eLpNorm (f n ω) 2 P).toReal| := by
          simpa [abs_of_nonneg ENNReal.toReal_nonneg] using hgt
        exact hleabs hgtabs
      simp [hftil_def, hle] at hω)).trans hn
  apply IsLittleOp.of_eq_on_asymptotic h_diff_to_zero
  -- Step 3: BCT step `E[‖ftil n ω‖²₂] → 0`.
  have h_BCT :
      Tendsto
        (fun n => ∫⁻ ω,
          ENNReal.ofReal ((eLpNorm (ftil n ω) 2 P).toReal ^ 2) ∂μ)
        atTop (𝓝 0) := by
    refine lintegral_ofReal_tendsto_zero_of_bdd_isLittleOp
      (μ := μ) (M := (1 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_
    · intro n
      have hnorm_meas :
          Measurable (fun ω => (eLpNorm (ftil n ω) 2 P).toReal) :=
        Causalean.Mathlib.measurable_eLpNorm_two_toReal_of_uncurry
          (P := P) (hftil_meas n)
      exact hnorm_meas.pow_const 2
    · intro n ω
      exact sq_nonneg _
    · intro n ω
      have h := hftil_bdd n ω
      have hnon : 0 ≤ (eLpNorm (ftil n ω) 2 P).toReal :=
        ENNReal.toReal_nonneg
      nlinarith [sq_nonneg ((eLpNorm (ftil n ω) 2 P).toReal)]
    · intro ε hε
      have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
      have htarget := hftil_rate (Real.sqrt ε) hsqrt_pos
      rw [ENNReal.tendsto_nhds_zero] at htarget ⊢
      intro δ hδ
      exact (htarget δ hδ).mono fun n hn => (measure_mono (by
        intro ω hω
        have hxnon : 0 ≤ (eLpNorm (ftil n ω) 2 P).toReal :=
          ENNReal.toReal_nonneg
        have hx2 : ε < (eLpNorm (ftil n ω) 2 P).toReal ^ 2 := by
          simpa [abs_of_nonneg
            (sq_nonneg ((eLpNorm (ftil n ω) 2 P).toReal))] using hω
        have hx : Real.sqrt ε < (eLpNorm (ftil n ω) 2 P).toReal :=
          (Real.sqrt_lt (le_of_lt hε) hxnon).mpr hx2
        simpa [abs_of_nonneg hxnon] using hx)).trans hn
  -- Markov + variance bound + BCT → o_p(1).
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  exact (ENNReal.tendsto_nhds_zero.mp
    (evalSum_truncated_isLittleOp_one S eval m_train h_train_le
      h_indep h_iid h_eval_card_grow ftil
      hftil_meas hftil_uncurry_train hftil_memLp h_BCT ε hε)) δ hδ


/-- **Centered fold-B empirical sum is `o_p(1)` from L²-rate `o_p(1)`.**

Setup:
* `S` an i.i.d. sample, `split` a one-shot split.
* `f : ℕ → Ω → X → ℝ` a family of random functions.
* `f n ω` is jointly measurable on fold-A training data and `X`.
* `f n ω ∈ L²(P)` for every `n, ω`.
* `‖f n ω‖_{L²(P)} = o_p(1)` under `μ`.

Then the centered fold-B empirical sum

    G_n(ω) := (1/√|B(n)|) Σ_{i ∈ B(n)} (f(n, ω, S.Z i ω) − ∫ f(n, ω, ·) dP)

is `o_p(1)` under `μ`.

**Proof outline.**  Truncate `f` at L²-norm `≤ 1`:

    f̃ n ω x := if ‖f n ω‖₂ ≤ 1 then f n ω x else 0.

Then `‖f̃ n ω‖₂ ≤ 1` deterministically, `f̃` inherits joint measurability,
fold-A measurability, and `MemLp`, and `f̃ n ω = f n ω` whenever
`‖f n ω‖₂ ≤ 1` — a set whose `μ`-complement has measure tending to `0` by
`hf_rate` at threshold `1`.  Hence the centered fold-B sums of `f` and `f̃`
agree on a set of asymptotic full measure (`IsLittleOp.of_eq_on_asymptotic`).

For the truncated sum `G̃_n`, Markov + the second-moment bound
(`centeredFoldBSum_sq_lintegral_le`) give

    μ{|G̃_n| > ε} ≤ E[G̃_n²] / ε² ≤ E[‖f̃_n‖²₂] / ε²

and `E[‖f̃_n‖²₂] → 0` by bounded convergence in probability
(`lintegral_ofReal_tendsto_zero_of_bdd_isLittleOp`), since `‖f̃_n‖₂ ≤ 1`
deterministically and `‖f̃_n‖₂ ≤ ‖f_n‖₂ = o_p(1)`.
-/
theorem foldB_centered_sum_isLittleOp_one
    (S : IIDSample Ω X μ P) (split : OneShotSplit S)
    (f : ℕ → Ω → X → ℝ)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => S.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace X)]
          (Function.uncurry (f n)))
    (hf_memLp : ∀ n ω, MemLp (f n ω) 2 P)
    (hf_rate :
      IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P).toReal)
        (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n, (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
      (fun _ => (1 : ℝ)) μ :=
  evalSum_isLittleOp_one S (fun n => split.foldB n)
    (fun n => MeasurableSpace.comap
      (fun ω (i : split.foldA n) => S.Z i ω) inferInstance)
    (fun n => foldA_sigma_le split n)
    (fun n => oneShot_indep split n)
    (fun n => oneShot_iid S split n)
    (by simpa [split.foldB_card] using split.cogrow)
    f hf_meas hf_uncurry_foldA hf_memLp hf_rate

/-! ## Bias term: `√|B(n)| · ∫ f(n, ω, ·) dP` is `o_p(1)`

Direct corollary of the constant-case Cauchy–Schwarz
`abs_integral_le_eLpNorm_two`, the rate hypothesis
`‖f‖_2 = o_p(n^{-1/2})`, and the bounded deterministic factor
`√(|B(n)|/n) → √c`. -/

/-- **Bias term is `o_p(1)` under fixed-ratio split.**

Given `|B(n)|/n → c` for `0 < c` and `‖f n ω‖_{L²(P)} = o_p(n^{-1/2})`, the
bias term `√|B(n)| · ∫ f(n, ω, ·) dP` is `o_p(1)` under `μ`.

**Proof.**  By Cauchy–Schwarz on the probability measure `P`,
`|∫ f(n, ω, ·) dP| ≤ ‖f(n, ω, ·)‖_{L²(P)}` (`abs_integral_le_eLpNorm_two`).
Multiplying by `√|B(n)| = √(|B(n)|/n) · √n` gives a deterministic factor
`√(|B(n)|/n) → √c` times `√n · ‖f(n, ω, ·)‖_2`, which is `o_p(1)` by the rate
hypothesis. -/
theorem sqrtFoldB_integral_isLittleOp_one
    (S : IIDSample Ω X μ P) (split : OneShotSplit S)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (f : ℕ → Ω → X → ℝ)
    (hf_memLp : ∀ n ω, MemLp (f n ω) 2 P)
    (hf_rate :
      IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((split.foldB n).card : ℝ) * ∫ x, f n ω x ∂P)
      (fun _ => (1 : ℝ)) μ :=
  evalSum_bias_isLittleOp_one S (fun n => split.foldB n) hc_pos
    h_split_rate f hf_memLp hf_rate

/-! ## K-fold per-fold corollaries

Same statements as the OneShot pair, but with the OneShot evaluation fold
`split.foldB n` replaced by the K-fold evaluation set `split.fold n k` and
the OneShot training σ-algebra by the comap σ-algebra of the training
complement `split.trainComplement n k`. -/

/-- **Per-fold centered evaluation sum is `o_p(1)` (K-fold).** -/
theorem KFoldSplit.fold_centered_sum_isLittleOp_one
    (S : IIDSample Ω X μ P) {K : ℕ} (split : KFoldSplit S K) (k : Fin K)
    (f : ℕ → Ω → X → ℝ)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_train : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace X)]
        (Function.uncurry (f n)))
    (hf_memLp : ∀ n ω, MemLp (f n ω) 2 P)
    (hf_rate : IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P).toReal)
        (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k, (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
      (fun _ => (1 : ℝ)) μ :=
  evalSum_isLittleOp_one S (fun n => split.fold n k)
    (fun n => MeasurableSpace.comap
      (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance)
    (fun n => trainComplement_sigma_le split n k)
    (fun n => kFold_indep split n k)
    (fun n => kFold_iid S split n k)
    (split.grow k)
    f hf_meas hf_uncurry_train hf_memLp hf_rate

/-- **Per-fold bias term is `o_p(1)` under a nonempty K-fold split.** -/
theorem KFoldSplit.sqrtFold_integral_isLittleOp_one
    (S : IIDSample Ω X μ P) {K : ℕ} (split : KFoldSplit S K) (k : Fin K)
    (hK_pos_nat : 0 < K)
    (f : ℕ → Ω → X → ℝ)
    (hf_memLp : ∀ n ω, MemLp (f n ω) 2 P)
    (hf_rate : IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((split.fold n k).card : ℝ) * ∫ x, f n ω x ∂P)
      (fun _ => (1 : ℝ)) μ := by
  have hK_pos : 0 < (K : ℝ) := by exact_mod_cast hK_pos_nat
  have hc_pos : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hK_pos
  exact evalSum_bias_isLittleOp_one S (fun n => split.fold n k)
    hc_pos (split.ratio k) f hf_memLp hf_rate

end Causalean.Stat
