/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TRAE-DR asymptotic-linearity criterion

This file states `thm:est-trae-dr-al-criterion` from
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`.

The headline statement: under an abstract sufficient bundle of range,
mixed-bias, empirical-process, and finite-variance conditions, the TRAE-DR
estimator is asymptotically linear at `θ₀` with influence function
`ρ₀(w) := φ_{h₀, q₀}(w) − θ₀`, indexed over the estimation fold
`split.foldB`.

The bundled hypothesis structure `TRAEDRRemainderHyps` factors:

* `primal_l2_consistency` — `ĥ_n(X)` converges to `h₀(X)` in L² in probability;
* `dual_l2_consistency`   — `q̂_n(Z)` converges to `q₀(Z)` in L² in probability;
* `candidate_mem` — `(ĥ_n, q̂_n)` lie in the candidate sets `(Hbar, Qbar)`;
* `mixed_bias`   — the conditional mixed-bias integral, scaled by
                   `√|B(n)|`, is `o_p(1)`;
* `ep_remainder` — empirical-process / mean-squared-continuity remainder
                   from replacing `(h₀, q₀)` by `(ĥ_n, q̂_n)` in the
                   estimation-fold average is `o_p(1)` after `√|B(n)|`
                   scaling;
* `finite_var`   — `E[ρ₀² ] < ∞` under `P_W`.

The mean-zero condition `E[ρ₀] = 0` is derived below from the primal and
dual moment identities by `mean_zero_of_DualSolution`; it is not an
independent hypothesis.

A Cauchy–Schwarz sufficient condition `mixed_bias_sufficient` is also
stated (the displayed `min{·,·}` form in the note), abstracting over a
deterministic upper-bound function.  The concrete conditional-expectation
operator `T`, its adjoint `T*`, and spectral calculus support live in the
`NPIV/Operator` modules; this DR criterion deliberately depends only on the
resulting scalar mixed-bias bound.
-/

import Causalean.Estimation.NPIV.MixedBias
import Causalean.Estimation.NPIV.DR.Estimator
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
import Causalean.Stat.SampleSplit
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.SampleSplit.PartialFoldCLT

/-!
States and proves asymptotic linearity for the doubly robust NPIV estimator
under bundled oracle-score and remainder conditions. The module identifies the
leading score term and controls the nuisance remainder.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace DR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

/-! ## Oracle score -/

/-- Oracle score `ρ₀(w) := φ_{h₀, q₀}(w) − θ₀`.

This is the influence function in `thm:est-trae-dr-al-criterion`. -/
noncomputable def ρ₀
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) (q₀ : S.𝒵 → ℝ) (w : S.𝒲) : ℝ :=
  S.phiVal S.h₀ q₀ w - S.θ₀

/-- Mean-zero of the oracle score under the structural law `μ`.

This is the population identity behind the influence-function centering:
`Θ(h₀, q₀) = θ₀` by the dual moment identity, hence
`E[φ_{h₀,q₀}(W) − θ₀] = 0`. -/
theorem mean_zero_of_DualSolution_mu
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀) :
    ∫ ω, ρ₀ S q₀ (S.W ω) ∂μ = 0 := by
  have hphi_int : Integrable (fun ω => S.phiVal S.h₀ q₀ (S.W ω)) μ := by
    unfold InverseProblemSystem.phiVal
    exact ((S.integrable_m_e S.h₀ S.h₀_mem).add
      (S.integrable_m q₀ hq₀.mem)).sub
      (S.integrable_qh S.h₀ S.h₀_mem q₀ hq₀.mem)
  have htheta_int : Integrable (fun _ : Ω => S.θ₀) μ := integrable_const _
  have hzero := Θ_q₀_eq_θ₀ S hq₀ S.h₀_mem
  unfold ρ₀
  rw [integral_sub hphi_int htheta_int]
  unfold InverseProblemSystem.Θ InverseProblemSystem.phi at hzero
  rw [hzero]
  simp

/-- Mean-zero of the oracle score under the observation law `P_W`.

The law bridge `μ.map S.W = P_W` records the standard statistical convention
that `P_W` is the distribution of the observed random variable `W`. -/
theorem mean_zero_of_DualSolution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲}
    (h_law_W : μ.map S.W = P_W)
    (hρ₀_meas : Measurable (ρ₀ S q₀)) :
    ∫ w, ρ₀ S q₀ w ∂P_W = 0 := by
  rw [← h_law_W]
  rw [MeasureTheory.integral_map S.meas_W.aemeasurable
    hρ₀_meas.aestronglyMeasurable]
  exact mean_zero_of_DualSolution_mu S hq₀

/-! ## Bundled sufficient remainder hypotheses -/

/-- The TRAE-DR remainder hypotheses require the fitted primal and dual
nuisances to be L²-consistent in probability, to stay in the candidate classes
needed by the mixed-bias identity, and to satisfy the mixed-bias,
empirical-process, and finite-variance conditions for asymptotic linearity. -/
structure TRAEDRRemainderHyps
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (_hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲}
    [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ)) : Prop where
  /-- (i) Primal L² consistency in probability:
      `‖ĥ_n(X) − h₀(X)‖_{L²(μ)} →ₚ 0`. -/
  primal_l2_consistency :
    Tendsto_inProb
      (fun n ω =>
        (eLpNorm
          (fun ω' => h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) 2 μ).toReal)
      (fun _ => 0) μ
  /-- (i) Dual L² consistency in probability:
      `‖q̂_n(Z) − q₀(Z)‖_{L²(μ)} →ₚ 0`. -/
  dual_l2_consistency :
    Tendsto_inProb
      (fun n ω =>
        (eLpNorm
          (fun ω' => q_hat n ω (S.zOf (S.W ω')) - q₀ (S.zOf (S.W ω'))) 2 μ).toReal)
      (fun _ => 0) μ
  /-- Support condition for the formal mixed-bias identity: the fitted primal
      and dual nuisance functions lie in the candidate classes for every
      sample size and outcome. -/
  candidate_mem : ∀ n ω, h_hat n ω ∈ S.Hbar ∧ q_hat n ω ∈ S.Qbar
  /-- Unconditional mixed-bias sufficient criterion: scaling the mixed-bias
      integral by `√|B(n)|` is `o_p(1)` under `μ`. This is the unconditional
      assumption used here rather than the conditional-on-training-fold
      hypothesis from the paper statement. -/
  mixed_bias :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
                  (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ)
      (fun _ => (1 : ℝ)) μ
  /-- Empirical-process / mean-squared-continuity remainder (iii):
        the centered fold-B sum of `φ̂_n − φ₀` is `o_p(1)` after `√|B(n)|`
        scaling. -/
  ep_remainder :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n,
            (S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω)
              - S.phiVal S.h₀ q₀ (sample.Z i ω))
            -
            Real.sqrt ((split.foldB n).card : ℝ) *
              ∫ ω', (S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')
                       - S.phiVal S.h₀ q₀ (S.W ω')) ∂μ)
      (fun _ => (1 : ℝ)) μ
  /-- (iv) Finite oracle-score variance: `E[ρ₀² ] < ∞` under `P_W`. -/
  finite_var :
    Integrable (fun w => (ρ₀ S q₀ w) ^ 2) P_W

/-! ## Headline asymptotic-linearity theorem -/

/-- **TRAE-DR asymptotic-linearity criterion** — `thm:est-trae-dr-al-criterion`.

Conclusion: the TRAE-DR estimator is asymptotically linear at `θ₀` with
influence function `ρ₀`, indexed over the estimation fold `split.foldB`.

The sufficient remainder hypotheses are supplied by `TRAEDRRemainderHyps`.
The law bridge `μ.map S.W = P_W` and oracle-score measurability are the
standard observation-law assumptions needed to derive the mean-zero
influence-function condition under `P_W`. -/
theorem trae_dr_isAsymLinear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲}
    [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (hρ₀_meas : Measurable (ρ₀ S q₀)) :
    IsAsymLinear
      (trae_dr_estimator S sample split h_hat q_hat)
      S.θ₀
      (ρ₀ S q₀)
      sample
      split.foldB := by
  refine ⟨mean_zero_of_DualSolution S hq₀ h_law_W hρ₀_meas, _hyps.finite_var, ?_⟩
  have h_add_one : ∀ {Xn Yn : ℕ → Ω → ℝ},
      IsLittleOp Xn (fun _ => (1 : ℝ)) μ →
        IsLittleOp Yn (fun _ => (1 : ℝ)) μ →
          IsLittleOp (fun n ω => Xn n ω + Yn n ω) (fun _ => (1 : ℝ)) μ := by
    intro Xn Yn hX hY ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    by_cases hδtop : δ = ⊤
    · filter_upwards with n
      simp [hδtop]
    have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
    let α : ℝ := δ.toReal / 4
    have hαpos : 0 < α := by
      dsimp [α]
      linarith
    let A : ℕ → Set Ω := fun n => {ω | (ε / 2) * (1 : ℝ) < |Xn n ω|}
    let B : ℕ → Set Ω := fun n => {ω | (ε / 2) * (1 : ℝ) < |Yn n ω|}
    let C : ℕ → Set Ω := fun n => {ω | ε * (1 : ℝ) < |Xn n ω + Yn n ω|}
    have hXevent_le := (ENNReal.tendsto_nhds_zero.mp (hX (ε / 2) (by linarith)))
      (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
    have hYevent_le := (ENNReal.tendsto_nhds_zero.mp (hY (ε / 2) (by linarith)))
      (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
    have htwo_alpha_lt_delta : ENNReal.ofReal (2 * α) < δ := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal]
      · dsimp [α]
        linarith
      · dsimp [α]
        linarith [le_of_lt hδpos]
      · exact hδtop
    filter_upwards [hXevent_le, hYevent_le] with n hXA hYB
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ ε / 2 < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl (by simpa [A] using hx))
      have hnotB : ¬ ε / 2 < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr (by simpa [B] using hy))
      have hXle : |Xn n ω| ≤ ε / 2 := le_of_not_gt hnotA
      have hYle : |Yn n ω| ≤ ε / 2 := le_of_not_gt hnotB
      have hsum : |Xn n ω + Yn n ω| ≤ ε := by
        calc
          |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| := abs_add_le _ _
          _ ≤ ε / 2 + ε / 2 := add_le_add hXle hYle
          _ = ε := by ring
      exact not_lt_of_ge hsum (by simpa [C] using hω)
    exact le_of_lt <| calc
      μ {ω | ε * (fun _ => (1 : ℝ)) n < |Xn n ω + Yn n ω|}
          = μ (C n) := by simp [C]
      _ ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
      _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hXA hYB
      _ = ENNReal.ofReal (2 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · linarith
        · linarith
      _ < δ := htwo_alpha_lt_delta
  let EP : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
      ∑ i ∈ split.foldB n,
        (S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω)
          - S.phiVal S.h₀ q₀ (sample.Z i ω))
      -
      Real.sqrt ((split.foldB n).card : ℝ) *
        ∫ ω', (S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')
                 - S.phiVal S.h₀ q₀ (S.W ω')) ∂μ
  let MB : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((split.foldB n).card : ℝ) *
      ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
              (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ
  have hsum : IsLittleOp (fun n ω => EP n ω + MB n ω) (fun _ => (1 : ℝ)) μ := by
    exact h_add_one _hyps.ep_remainder _hyps.mixed_bias
  have h_eq : ∀ n ω,
      Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
        - (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
            ∑ i ∈ split.foldB n, ρ₀ S q₀ (sample.Z i ω)
        = EP n ω + MB n ω := by
    intro n ω
    have hrange := _hyps.candidate_mem n ω
    have hphi_hat_int :
        Integrable
          (fun ω' => S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')) μ := by
      unfold InverseProblemSystem.phiVal
      exact ((S.integrable_m_e (h_hat n ω) hrange.1).add
        (S.integrable_m (q_hat n ω) hrange.2)).sub
        (S.integrable_qh (h_hat n ω) hrange.1 (q_hat n ω) hrange.2)
    have hphi_zero_int :
        Integrable
          (fun ω' => S.phiVal S.h₀ q₀ (S.W ω')) μ := by
      unfold InverseProblemSystem.phiVal
      exact ((S.integrable_m_e S.h₀ S.h₀_mem).add
        (S.integrable_m q₀ hq₀.mem)).sub
        (S.integrable_qh S.h₀ S.h₀_mem q₀ hq₀.mem)
    have h_int_eq :
        (∫ ω', (S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')
                 - S.phiVal S.h₀ q₀ (S.W ω')) ∂μ)
          =
        ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
                (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ := by
      rw [integral_sub hphi_hat_int hphi_zero_int]
      have hmb := mixed_bias_identity S hq₀ hrange.1 hrange.2
      have hzero := Θ_q₀_eq_θ₀ S hq₀ S.h₀_mem
      unfold InverseProblemSystem.Θ InverseProblemSystem.phi at hmb hzero
      rw [hzero]
      simpa [InverseProblemSystem.X, InverseProblemSystem.Z] using hmb
    by_cases hcard : (split.foldB n).card = 0
    · have hempty : split.foldB n = ∅ := Finset.card_eq_zero.mp hcard
      simp [EP, MB, h_int_eq, trae_dr_estimator, ρ₀, hempty]
    · have hcard_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hcard
      have hcard_pos_real : 0 < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard_pos_nat
      have hsqrt_ne :
          Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 := by
        intro hsqrt_zero
        have hzero_real : ((split.foldB n).card : ℝ) = 0 := by
          rw [← Real.mul_self_sqrt (le_of_lt hcard_pos_real), hsqrt_zero, zero_mul]
        exact (ne_of_gt hcard_pos_real) hzero_real
      have hsqrt_sq :
          Real.sqrt ((split.foldB n).card : ℝ) *
              Real.sqrt ((split.foldB n).card : ℝ)
            = ((split.foldB n).card : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have h_sqrt_mul_inv_card :
          Real.sqrt ((split.foldB n).card : ℝ) *
              (((split.foldB n).card : ℝ)⁻¹)
            = (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ := by
        let r : ℝ := Real.sqrt ((split.foldB n).card : ℝ)
        let c : ℝ := ((split.foldB n).card : ℝ)
        have hr : r ≠ 0 := by simpa [r] using hsqrt_ne
        have hsq : r * r = c := by simp [r, c, hsqrt_sq]
        change r * c⁻¹ = r⁻¹
        rw [← hsq]
        field_simp [hr]
      have h_inv_sqrt_mul_card :
          (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ((split.foldB n).card : ℝ)
            = Real.sqrt ((split.foldB n).card : ℝ) := by
        let r : ℝ := Real.sqrt ((split.foldB n).card : ℝ)
        let c : ℝ := ((split.foldB n).card : ℝ)
        have hr : r ≠ 0 := by simpa [r] using hsqrt_ne
        have hsq : r * r = c := by simp [r, c, hsqrt_sq]
        change r⁻¹ * c = r
        rw [← hsq]
        field_simp [hr]
      simp [EP, MB, h_int_eq, trae_dr_estimator, ρ₀, Finset.sum_sub_distrib]
      rw [mul_sub]
      rw [← mul_assoc (Real.sqrt ((split.foldB n).card : ℝ))
        (((split.foldB n).card : ℝ)⁻¹)
        (∑ i ∈ split.foldB n,
          S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω))]
      rw [h_sqrt_mul_inv_card]
      rw [mul_sub]
      rw [← mul_assoc (Real.sqrt ((split.foldB n).card : ℝ))⁻¹
        ((split.foldB n).card : ℝ) S.θ₀]
      rw [h_inv_sqrt_mul_card]
      ring
  convert hsum using 1
  ext n ω
  exact h_eq n ω

/-! ## Cauchy–Schwarz sufficient condition for the mixed-bias rate -/

/-- Sufficient condition for the mixed-bias hypothesis using either
operator side (the displayed `min{·,·}` form in
`thm:est-trae-dr-al-criterion`):

if either
    √|B(n)| · ‖q̂_n − q₀‖_{L²(P_Z)} · ‖T(ĥ_n − h₀)‖_{L²(P_Z)} = o_p(1)
or
    √|B(n)| · ‖T*(q̂_n − q₀)‖_{L²(P_X)} · ‖ĥ_n − h₀‖_{L²(P_X)} = o_p(1),
then the unconditional `mixed_bias` field of `TRAEDRRemainderHyps` holds.

The concrete operators `T` and `T*` are formalized in the `NPIV/Operator`
modules.  This theorem remains operator-agnostic: it is a forward implication
from any deterministic upper-bound function `bnd : ℕ → Ω → ℝ` that controls
the conditional mixed-bias integral pointwise. -/
theorem mixed_bias_sufficient
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    {P_W : Measure S.𝒲}
    [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (bnd : ℕ → Ω → ℝ)
    (_h_dom : ∀ n ω,
      |∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
              (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ|
        ≤ bnd n ω)
    (_h_rate :
      IsLittleOp (fun n ω => Real.sqrt ((split.foldB n).card : ℝ) * bnd n ω)
        (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
                  (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ)
      (fun _ => (1 : ℝ)) μ := by
  -- Reference to `sample` is intentional: the conclusion is the precise
  -- form of the `mixed_bias` field above, indexed by `split.foldB`.
  let _ := sample
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hrate := (ENNReal.tendsto_nhds_zero.mp (_h_rate ε hε)) δ hδ
  filter_upwards [hrate] with n hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  simp only [Set.mem_setOf_eq, mul_one] at hω ⊢
  let bias : ℝ :=
    ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
            (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ
  have h_bnd_nonneg : 0 ≤ bnd n ω := le_trans (abs_nonneg bias) (_h_dom n ω)
  have h_sqrt_nonneg : 0 ≤ Real.sqrt ((split.foldB n).card : ℝ) := Real.sqrt_nonneg _
  have h_abs_bias :
      |Real.sqrt ((split.foldB n).card : ℝ) * bias|
        = Real.sqrt ((split.foldB n).card : ℝ) * |bias| := by
    rw [abs_mul, abs_of_nonneg h_sqrt_nonneg]
  have h_abs_bnd :
      |Real.sqrt ((split.foldB n).card : ℝ) * bnd n ω|
        = Real.sqrt ((split.foldB n).card : ℝ) * bnd n ω := by
    rw [abs_of_nonneg (mul_nonneg h_sqrt_nonneg h_bnd_nonneg)]
  rw [show
      (∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
              (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ)
        = bias from rfl, h_abs_bias] at hω
  rw [h_abs_bnd]
  exact lt_of_lt_of_le hω (mul_le_mul_of_nonneg_left (_h_dom n ω) h_sqrt_nonneg)

end DR
end NPIV
end Estimation
end Causalean
