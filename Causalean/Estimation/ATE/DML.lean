/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# One-shot DML / AIPW estimator for the back-door ATE

`def:est-dml-ate` and `thm:est-dml-ate-al` instantiated for the
`BackdoorEstimationSystem` from `InfluenceFunction.lean`.

The estimator is

    θ̂ⁿ_DML := (1/|B(n)|) Σ_{i ∈ B(n)} m_AIPW( η̂(n), Zᵢ, 0 ) + θ_correction,

where `m_AIPW` is the AIPW moment from `InfluenceFunction.lean` (with the
`-θ` term absent here, since the estimator IS `θ`).  Concretely:

    θ̂ⁿ_DML := (1/|B(n)|) Σ_{i ∈ B(n)}
        [ μ̂(1, Xᵢ) − μ̂(0, Xᵢ)
          + (Aᵢ / ê(Xᵢ)) (Yᵢ − μ̂(1, Xᵢ))
          − ((1−Aᵢ) / (1−ê(Xᵢ))) (Yᵢ − μ̂(0, Xᵢ)) ].

The headline theorem gives asymptotic linearity at `θ₀` with influence
function `ψ_AIPW` from `InfluenceFunction.lean`, under the rate
hypothesis `|B(n)|/n → c` for some `c ∈ (0, 1)` and the AIPW product rate condition.

Proof sketch (NL doc, `thm:est-dml-ate-al`): main term + three remainders
(`R₁` killed by Neyman orthogonality + product rate; `R₂` killed by
empirical-process Markov + individual rates; `R₃` lower-order arithmetic).
-/

import Causalean.Estimation.ATE.InfluenceFunction
import Causalean.Estimation.ATE.Remainder
import Causalean.Estimation.ATE.Score.AIPWScoreL2
import Causalean.Estimation.OrthogonalMoments.AIPWInstance
import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.SampleSplit.PartialFoldCLT
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # Double Machine Learning for ATE

This file defines `dmlEstimator`, the one-shot sample-split augmented
inverse-probability weighted estimator for the back-door average treatment
effect. It proves `dml_ATE_isAsymLinear`, which connects the estimator to the
AIPW influence function under overlap, second-moment, sample-split, and
nuisance-rate conditions, and `dml_ATE_tendstoNormal`, the resulting fold-scaled
asymptotic normality statement. -/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- One-shot DML / AIPW estimator of the back-door ATE
(`def:est-dml-ate`).

Inputs:
* `S`         — back-door estimation system carrying the value-space
                truth `(μ_val, e_val)`.
* `sample`    — i.i.d. sample of triples `(X, A, Y) ∼ P_Z`.
* `split`     — one-shot split of the sample.
* `μ_hat`     — outcome regression estimator at horizon `n`.
* `e_hat`     — propensity estimator at horizon `n`.

Output: empirical mean over `B(n)` of `m_AIPW( η̂(n), Zᵢ, 0 )`.
Equivalently, the empirical AIPW pseudo-outcome. -/
noncomputable def dmlEstimator
    (S : BackdoorEstimationSystem P γ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (n : ℕ) : P.Ω → ℝ :=
  fun ω =>
    ((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n,
        aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) 0

-- The wrapper composes ~20 derived hypotheses (rate translations, score
-- measurability, integrability, two transport equalities) and applies the
-- abstract `aipw_dml_isAsymLinear`; the resulting elaboration exceeds the
-- default heartbeat budget when type-checking the final `refine ⟨…⟩` block.
set_option maxHeartbeats 1200000 in
/-- **Asymptotic linearity of the one-shot DML ATE** — `thm:est-dml-ate-al`.

Hypotheses (mirroring the NL doc verbatim, including the split-rate
hypothesis `|B(n)|/n → c`):

1. back-door `Assumptions`;
2. strict overlap for the truth and a.e. learner overlap: there exists
   `ε ∈ (0, 1/2]` with `ε ≤ e(X) ≤ 1-ε` a.s. and
   `ε ≤ ê(n,ω)(X) ≤ 1-ε` `P_X`-a.e. for each learner realization;
3. the truth and learners belong to the source-shaped `H_ε_aeL2` nuisance
   class used by `aipwGeneralMoment`;
4. `E[Y²] < ∞`;
5. one-shot split with `|B(n)|/n → c` for some `c ∈ (0, 1)`;
6. `μ̂(n)` and `ê(n)` depend only on the nuisance fold `A(n)`;
7. individual rates `‖μ̂(n)(a, X) − μ_val(a, X)‖_{L²(P_X)} = o_p(1)` and
   `‖ê(n)(X) − e_val(X)‖_{L²(P_X)} = o_p(1)`;
8. product rate
   `‖μ̂(n)(a, X) − μ_val(a, X)‖_{L²(P_X)} · ‖ê(n)(X) − e_val(X)‖_{L²(P_X)}
       = o_p(n^{-1/2})` for each `a ∈ {0, 1}`.

Conclusion: `IsAsymLinear (dmlEstimator …) θ₀ ψ_AIPW sample split.foldB`.

The proof is a thin wrapper over the abstract
`Causalean.Estimation.ATE.aipw_dml_isAsymLinear` (in
`Estimation/OrthogonalMoments/AIPWInstance.lean`): build the abstract `η_hat` from
`(μ_hat, e_hat)`, translate the rate / measurability / integrability
hypotheses, apply the abstract theorem, then transport the conclusion
along two algebraic equalities (a pointwise rescaled-error equality
`√|B(n)| · (dmlChern − θ₀) = √|B(n)| · (dmlEstimator − θ₀)` and the
influence-function equality `−J₀_inv · aipwMomentFunctional S.η₀ z S.θ₀
= S.ψ_AIPW z`). -/
theorem dml_ATE_isAsymLinear
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n ω a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n ω, ∀ᵐ x ∂S.P_X, ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (dmlEstimator S sample split μ_hat e_hat)
      S.θ₀
      (S.ψ_AIPW)
      sample
      split.foldB := by
  -- 1. Build the abstract `η_hat : ℕ → P.Ω → NuisanceVec γ` from `(μ_hat, e_hat)`.
  let η_hat : ℕ → P.Ω → NuisanceVec γ := fun n ω =>
    { μ_fn := μ_hat n ω
      e_fn := e_hat n ω
      μ_meas := fun a =>
        (h_mu_meas n a).comp
          (Measurable.prodMk measurable_const measurable_id)
      e_meas :=
        (h_e_meas n).comp
          (Measurable.prodMk measurable_const measurable_id) }
  -- `S.P_X` is a probability measure (used by `MemLp.of_bound` for `S.e_val`).
  haveI : IsProbabilityMeasure S.P_X := by
    unfold BackdoorEstimationSystem.P_X
    exact Measure.isProbabilityMeasure_map
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable
  -- `S.P_Z` is a probability measure (used by `MemLp.integrable` on the score).
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold BackdoorEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map
      S.measurable_factualZ.aemeasurable
  -- 2. `S.μ_val a` is L²(P_X) (via condExp of square-integrable counterfactual outcomes).
  have hμ_val_memLp : ∀ a : Bool, MemLp (S.μ_val a) 2 S.P_X := by
    intro a
    have hY_L2 : MemLp (S.toPOBackdoorSystem.YofD a) 2 P.μ :=
      (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD a).aestronglyMeasurable).2 (h_yd2 a)
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD a |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hY_L2.condExp
    have hcomp_L2 :
        MemLp (fun ω => S.μ_val a (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hcond_L2.ae_eq (S.μ_compat hA a)
    rw [BackdoorEstimationSystem.P_X]
    exact (memLp_map_measure_iff (S.μ_meas a).aestronglyMeasurable
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable).2 hcomp_L2
  -- 3. `S.e_val` is L²(P_X) (via boundedness in `[0, 1]`).
  have he_val_memLp : MemLp S.e_val 2 S.P_X := by
    refine MemLp.of_bound S.e_meas.aestronglyMeasurable 1 ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [S.e_pos x], by linarith [S.e_lt_one x]⟩
  have he_val_memLp_top : MemLp S.e_val ⊤ S.P_X := by
    refine MemLp.of_bound S.e_meas.aestronglyMeasurable 1 ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [S.e_pos x], by linarith [S.e_lt_one x]⟩
  have hη₀_mem : S.η₀ ∈ H_ε_aeL2 S ε := by
    refine ⟨?_, ?_, ?_⟩
    · have hset : MeasurableSet {x : γ | ε ≤ S.e_val x ∧ S.e_val x ≤ 1 - ε} := by
        exact measurableSet_Icc.preimage S.e_meas
      have hΩ : ∀ᵐ ω ∂P.μ,
          ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) ∧
            S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
        filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
        simpa [hcomp] using hover
      unfold BackdoorEstimationSystem.P_X
      exact (MeasureTheory.ae_map_iff
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable hset).mpr hΩ
    · exact hμ_val_memLp
    · exact he_val_memLp_top
  have h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε := by
    intro n ω
    refine ⟨h_e_overlap n ω, ?_, ?_⟩
    · exact h_mu_memLp n ω
    · refine MemLp.of_bound (η_hat n ω).e_meas.aestronglyMeasurable 1 ?_
      filter_upwards [h_e_overlap n ω] with x hx
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [h_overlap.1, hx.1],
        by linarith [h_overlap.1, hx.2]⟩
  -- 4. Per-η̂_n L² of the differences (needed by the abstract).
  have h_mu_diff_memLp :
      ∀ n ω a, MemLp
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X := by
    intro n ω a
    exact (h_mu_memLp n ω a).sub (hμ_val_memLp a)
  have h_e_diff_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X := by
    intro n ω
    exact (h_e_memLp n ω).sub he_val_memLp
  -- 5. Translate the production rate hypotheses to the abstract `ρ₁ / ρ₂`.
  --    `ρ₁ η η₀ = ‖Δμ_T‖ + ‖Δμ_F‖`, `ρ₂ η η₀ = ‖Δe‖`.
  have h_indiv_rate_ρ₁ :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    have h_add_one : ∀ {Xn Yn : ℕ → P.Ω → ℝ},
        IsLittleOp Xn (fun _ => (1 : ℝ)) P.μ →
          IsLittleOp Yn (fun _ => (1 : ℝ)) P.μ →
            IsLittleOp (fun n ω => Xn n ω + Yn n ω) (fun _ => (1 : ℝ)) P.μ := by
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
      let A : ℕ → Set P.Ω := fun n => {ω | (ε / 2) * (1 : ℝ) < |Xn n ω|}
      let B : ℕ → Set P.Ω := fun n => {ω | (ε / 2) * (1 : ℝ) < |Yn n ω|}
      let C : ℕ → Set P.Ω := fun n => {ω | ε * (1 : ℝ) < |Xn n ω + Yn n ω|}
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
        P.μ {ω | ε * (fun _ => (1 : ℝ)) n < |Xn n ω + Yn n ω|}
            = P.μ (C n) := by simp [C]
        _ ≤ P.μ (A n ∪ B n) := measure_mono hsubset
        _ ≤ P.μ (A n) + P.μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
        _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hXA hYB
        _ = ENNReal.ofReal (2 * α) := by
          rw [← ENNReal.ofReal_add]
          · congr 1
            ring
          · linarith
          · linarith
        _ < δ := htwo_alpha_lt_delta
    simpa [aipwGeneralMoment, BackdoorEstimationSystem.η₀, η_hat] using
      h_add_one (h_mu_rate true) (h_mu_rate false)
  have h_indiv_rate_ρ₂ :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₂
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [aipwGeneralMoment, BackdoorEstimationSystem.η₀] using h_e_rate
  have h_product_rate_abs :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ) *
            (((aipwGeneralMoment S hη₀_mem).ρ₂
                (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
    have h_add_rate : ∀ {Xn Yn : ℕ → P.Ω → ℝ} {rn : ℕ → ℝ},
        (∀ᶠ n : ℕ in atTop, 0 ≤ rn n) →
        IsLittleOp Xn rn P.μ → IsLittleOp Yn rn P.μ →
        IsLittleOp (fun n ω => Xn n ω + Yn n ω) rn P.μ := by
      intro Xn Yn rn hrn_nonneg hX hY ε hε
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
      let A : ℕ → Set P.Ω := fun n => {ω | (ε / 2) * rn n < |Xn n ω|}
      let B : ℕ → Set P.Ω := fun n => {ω | (ε / 2) * rn n < |Yn n ω|}
      let C : ℕ → Set P.Ω := fun n => {ω | ε * rn n < |Xn n ω + Yn n ω|}
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
      filter_upwards [hrn_nonneg, hXevent_le, hYevent_le] with n hrn hXA hYB
      have hsubset : C n ⊆ A n ∪ B n := by
        intro ω hω
        by_contra hnot
        have hnotA : ¬ (ε / 2) * rn n < |Xn n ω| := by
          intro hx
          exact hnot (Or.inl hx)
        have hnotB : ¬ (ε / 2) * rn n < |Yn n ω| := by
          intro hy
          exact hnot (Or.inr hy)
        have hXle : |Xn n ω| ≤ (ε / 2) * rn n := le_of_not_gt hnotA
        have hYle : |Yn n ω| ≤ (ε / 2) * rn n := le_of_not_gt hnotB
        have hsum : |Xn n ω + Yn n ω| ≤ ε * rn n := by
          calc
            |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| := abs_add_le _ _
            _ ≤ (ε / 2) * rn n + (ε / 2) * rn n := add_le_add hXle hYle
            _ = ε * rn n := by ring
        exact not_lt_of_ge hsum hω
      exact le_of_lt <| calc
        P.μ {ω | ε * rn n < |Xn n ω + Yn n ω|} = P.μ (C n) := by simp [C]
        _ ≤ P.μ (A n ∪ B n) := measure_mono hsubset
        _ ≤ P.μ (A n) + P.μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
        _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hXA hYB
        _ = ENNReal.ofReal (2 * α) := by
          rw [← ENNReal.ofReal_add]
          · congr 1
            ring
          · linarith
          · linarith
        _ < δ := htwo_alpha_lt_delta
    have hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      filter_upwards with n
      positivity
    simpa [aipwGeneralMoment, BackdoorEstimationSystem.η₀, η_hat, add_mul] using
      h_add_rate (rn := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) hrn_nonneg
        (h_product_rate true) (h_product_rate false)
  -- 6. Translate score measurability / integrability to the abstract form.
  have h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
    have hx : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => (p.1, p.2.1)) := by
      fun_prop
    have hzY : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => p.2.2.2) := by
      fun_prop
    have hAind : Measurable (fun p : P.Ω × (γ × Bool × ℝ) =>
        if p.2.2.1 = true then (1 : ℝ) else 0) := by
      have ha : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => p.2.2.1) := by
        fun_prop
      exact (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
    have hμt : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 true p.2.1) :=
      (h_mu_meas n true).comp hx
    have hμf : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 false p.2.1) :=
      (h_mu_meas n false).comp hx
    have het : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => e_hat n p.1 p.2.1) :=
      (h_e_meas n).comp hx
    exact ((((hμt.sub hμf).add ((hAind.div het).mul (hzY.sub hμt))).sub
      (((measurable_const.sub hAind).div (measurable_const.sub het)).mul
        (hzY.sub hμf))).sub measurable_const)
  have h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => aipwMomentFunctional (η_hat n ω) z S.θ₀) := by
    intro n
    unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
    fun_prop
  have h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
          (fun (p : P.Ω × (γ × Bool × ℝ)) =>
            aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    change Measurable[(MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
      (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
      (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀)
    unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
    let mA : MeasurableSpace P.Ω :=
      MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance
    have hproj :
        @Measurable (P.Ω × (γ × Bool × ℝ)) (P.Ω × γ)
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          (mA.prod (inferInstance : MeasurableSpace γ))
          (fun p => (p.1, p.2.1)) := by
      have hx :
          @Measurable (P.Ω × (γ × Bool × ℝ)) γ
            (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
            inferInstance
            (fun p => p.2.1) := measurable_snd.fst
      exact Measurable.prodMk measurable_fst hx
    have hzY :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun p => p.2.2.2) := measurable_snd.snd.snd
    have hAind :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun p => if p.2.2.1 = true then (1 : ℝ) else 0) := by
      have ha :
          @Measurable (P.Ω × (γ × Bool × ℝ)) Bool
            (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
            inferInstance
            (fun p => p.2.2.1) := measurable_snd.snd.fst
      exact (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
    have hμt : Measurable
        (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 true p.2.1) :=
      (h_mu_uncurry_foldA n true).comp hproj
    have hμf : Measurable
        (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 false p.2.1) :=
      (h_mu_uncurry_foldA n false).comp hproj
    have het : Measurable
        (fun p : P.Ω × (γ × Bool × ℝ) => e_hat n p.1 p.2.1) :=
      (h_e_uncurry_foldA n).comp hproj
    exact ((((hμt.sub hμf).add ((hAind.div het).mul (hzY.sub hμt))).sub
      (((measurable_const.sub hAind).div (measurable_const.sub het)).mul
        (hzY.sub hμf))).sub measurable_const)
  have h_m_int :
      ∀ n ω, Integrable
        (fun z => aipwMomentFunctional (η_hat n ω) z S.θ₀) S.P_Z := by
    intro n ω
    have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ :=
      (memLp_two_iff_integrable_sq
        S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
    have hμ_hat_comp_L2 :
        ∀ a : Bool,
          MemLp (fun ω' => μ_hat n ω a (S.toPOBackdoorSystem.factualX ω')) 2 P.μ := by
      intro a
      have hmap : MemLp (fun x => μ_hat n ω a x) 2 (P.μ.map S.toPOBackdoorSystem.factualX) := by
        simpa [BackdoorEstimationSystem.P_X] using h_mu_memLp n ω a
      exact (memLp_map_measure_iff hmap.aestronglyMeasurable
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable).1 hmap
    have hw_true_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S (h_in_Hε n ω)] with ω' hηω'
      have he := hηω'.1
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hpos : 0 < e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 he
        have hle : (e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos h_overlap.1).2 he
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hpos] using hle
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
    have hw_false_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖(1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S (h_in_Hε n ω)] with ω' hηω'
      have he := hηω'.2
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
      · have hden : ε ≤ 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') := by
          linarith
        have hdenpos : 0 < 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 hden
        have hle : (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hdenpos h_overlap.1).2 hden
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hdenpos] using hle
    have hw_true_Linf :
        MemLp
          (fun ω' => indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_true_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
          (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
              S.toPOBackdoorSystem.measurable_factualD
      exact hind.div ((h_e_meas n).comp
        (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX))
    have hw_false_Linf :
        MemLp
          (fun ω' => (1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_false_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
          (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
              S.toPOBackdoorSystem.measurable_factualD
      exact (measurable_const.sub hind).div
        (measurable_const.sub ((h_e_meas n).comp
          (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX)))
    have hterm_true_L2 :
        MemLp
          (fun ω' =>
            (indA (S.factualZ ω') /
              e_hat n ω (S.toPOBackdoorSystem.factualX ω')) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      simpa using (hY_L2.sub (hμ_hat_comp_L2 true)).mul hw_true_Linf
    have hterm_false_L2 :
        MemLp
          (fun ω' =>
            ((1 - indA (S.factualZ ω')) /
              (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      simpa using (hY_L2.sub (hμ_hat_comp_L2 false)).mul hw_false_Linf
    have hrand_comp_L2 :
        MemLp (fun ω' => aipwMomentFunctional (η_hat n ω) (S.factualZ ω') S.θ₀)
          2 P.μ := by
      have hbase_L2 :
          MemLp
            (fun ω' =>
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω') -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω')) 2 P.μ :=
        (hμ_hat_comp_L2 true).sub (hμ_hat_comp_L2 false)
      have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ :=
        memLp_const _
      have hsum_L2 :=
        ((hbase_L2.add hterm_true_L2).sub hterm_false_L2).sub hconst_L2
      simpa [aipwMomentFunctional, aipwMoment, BackdoorEstimationSystem.factualZ,
        projX, projY] using hsum_L2
    have hrand_meas :
        Measurable (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀) := by
      unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
      have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
      have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
      have hμt : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω true z.1) :=
        (h_mu_meas n true).comp (Measurable.prodMk measurable_const hx)
      have hμf : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω false z.1) :=
        (h_mu_meas n false).comp (Measurable.prodMk measurable_const hx)
      have he : Measurable (fun z : γ × Bool × ℝ => e_hat n ω z.1) :=
        (h_e_meas n).comp (Measurable.prodMk measurable_const hx)
      have hind : Measurable (fun z : γ × Bool × ℝ =>
          if z.2.1 = true then (1 : ℝ) else 0) := by
        have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
        exact (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
      exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
        (((measurable_const.sub hind).div (measurable_const.sub he)).mul
          (hy.sub hμf))).sub measurable_const)
    have hrand_L2 :
        MemLp (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀)
          2 S.P_Z := by
      rw [BackdoorEstimationSystem.P_Z]
      exact (memLp_map_measure_iff hrand_meas.aestronglyMeasurable
        S.measurable_factualZ.aemeasurable).2 hrand_comp_L2
    exact hrand_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h_m_sq_int :
      ∀ n ω, Integrable
        (fun z => (aipwMomentFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z := by
    intro n ω
    have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ :=
      (memLp_two_iff_integrable_sq
        S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
    have hμ_hat_comp_L2 :
        ∀ a : Bool,
          MemLp (fun ω' => μ_hat n ω a (S.toPOBackdoorSystem.factualX ω')) 2 P.μ := by
      intro a
      have hmap : MemLp (fun x => μ_hat n ω a x) 2 (P.μ.map S.toPOBackdoorSystem.factualX) := by
        simpa [BackdoorEstimationSystem.P_X] using h_mu_memLp n ω a
      exact (memLp_map_measure_iff hmap.aestronglyMeasurable
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable).1 hmap
    have hw_true_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S (h_in_Hε n ω)] with ω' hηω'
      have he := hηω'.1
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hpos : 0 < e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 he
        have hle : (e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos h_overlap.1).2 he
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hpos] using hle
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
    have hw_false_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖(1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S (h_in_Hε n ω)] with ω' hηω'
      have he := hηω'.2
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
      · have hden : ε ≤ 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') := by
          linarith
        have hdenpos : 0 < 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 hden
        have hle : (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hdenpos h_overlap.1).2 hden
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hdenpos] using hle
    have hw_true_Linf :
        MemLp
          (fun ω' => indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_true_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
          (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
              S.toPOBackdoorSystem.measurable_factualD
      exact hind.div ((h_e_meas n).comp
        (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX))
    have hw_false_Linf :
        MemLp
          (fun ω' => (1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_false_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
          (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
              S.toPOBackdoorSystem.measurable_factualD
      exact (measurable_const.sub hind).div
        (measurable_const.sub ((h_e_meas n).comp
          (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX)))
    have hterm_true_L2 :
        MemLp
          (fun ω' =>
            (indA (S.factualZ ω') /
              e_hat n ω (S.toPOBackdoorSystem.factualX ω')) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      simpa using (hY_L2.sub (hμ_hat_comp_L2 true)).mul hw_true_Linf
    have hterm_false_L2 :
        MemLp
          (fun ω' =>
            ((1 - indA (S.factualZ ω')) /
              (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      simpa using (hY_L2.sub (hμ_hat_comp_L2 false)).mul hw_false_Linf
    have hrand_comp_L2 :
        MemLp (fun ω' => aipwMomentFunctional (η_hat n ω) (S.factualZ ω') S.θ₀)
          2 P.μ := by
      have hbase_L2 :
          MemLp
            (fun ω' =>
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω') -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω')) 2 P.μ :=
        (hμ_hat_comp_L2 true).sub (hμ_hat_comp_L2 false)
      have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ :=
        memLp_const _
      have hsum_L2 :=
        ((hbase_L2.add hterm_true_L2).sub hterm_false_L2).sub hconst_L2
      simpa [aipwMomentFunctional, aipwMoment, BackdoorEstimationSystem.factualZ,
        projX, projY] using hsum_L2
    have hrand_meas :
        Measurable (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀) := by
      unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
      have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
      have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
      have hμt : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω true z.1) :=
        (h_mu_meas n true).comp (Measurable.prodMk measurable_const hx)
      have hμf : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω false z.1) :=
        (h_mu_meas n false).comp (Measurable.prodMk measurable_const hx)
      have he : Measurable (fun z : γ × Bool × ℝ => e_hat n ω z.1) :=
        (h_e_meas n).comp (Measurable.prodMk measurable_const hx)
      have hind : Measurable (fun z : γ × Bool × ℝ =>
          if z.2.1 = true then (1 : ℝ) else 0) := by
        have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
        exact (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
      exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
        (((measurable_const.sub hind).div (measurable_const.sub he)).mul
          (hy.sub hμf))).sub measurable_const)
    have hrand_L2 :
        MemLp (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀)
          2 S.P_Z := by
      rw [BackdoorEstimationSystem.P_Z]
      exact (memLp_map_measure_iff hrand_meas.aestronglyMeasurable
        S.measurable_factualZ.aemeasurable).2 hrand_comp_L2
    simpa using hrand_L2.integrable_sq
  -- 7. Apply the abstract theorem.
  have hAL :=
    aipw_dml_isAsymLinear S hη₀_mem h_overlap hA h_y2 h_yd2
      sample split hc_pos h_split_rate η_hat h_in_Hε
      h_mu_diff_memLp h_e_diff_memLp
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_indiv_rate_ρ₁ h_indiv_rate_ρ₂ h_product_rate_abs
  -- 8. Transport the conclusion to the production form.
  --
  -- Strategy (option (b) — handles the empty-fold case correctly).  The
  -- estimators `dmlChernozhukovEstimator` and `dmlEstimator` differ when
  -- `|B(n)| = 0` (the former equals `θ₀`, the latter equals `0`), but the
  -- *rescaled* errors `√|B(n)| · (θ̂ − θ₀)` agree pointwise in `(n, ω)`
  -- (both vanish in the empty case via `√0 = 0`), and that is the only
  -- estimator-dependent quantity inside `IsAsymLinear`.  We also prove the
  -- influence-function equality `−J₀_inv · aipwMomentFunctional S.η₀ z S.θ₀
  -- = S.ψ_AIPW z` and then build the production `IsAsymLinear` field-by-field.
  --
  -- IF equality (pointwise on `z`).
  have h_if_eq :
      (fun z => -(aipwGeneralMoment S hη₀_mem).J₀_inv *
                  aipwMomentFunctional S.η₀ z S.θ₀)
      = S.ψ_AIPW := by
    funext z
    -- `J₀ = -1`, so `J₀_inv = (-1)⁻¹ = -1`, hence `-J₀_inv = 1`.
    have hJ : -(aipwGeneralMoment S hη₀_mem).J₀_inv = 1 := by
      show -((aipwGeneralMoment S hη₀_mem).J₀)⁻¹ = 1
      show -((-1 : ℝ))⁻¹ = 1
      norm_num
    rw [hJ, one_mul]
    -- `aipwMomentFunctional S.η₀ z S.θ₀ = aipwMoment z S.μ_val S.e_val S.θ₀ = S.ψ_AIPW z`.
    rfl
  -- Rescaled-error equality (pointwise on `(n, ω)`).
  have h_resc_eq : ∀ n ω,
      Real.sqrt ((split.foldB n).card : ℝ) *
        (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
          (aipwGeneralMoment S hη₀_mem) sample split η_hat n ω - S.θ₀)
      = Real.sqrt ((split.foldB n).card : ℝ) *
        (dmlEstimator S sample split μ_hat e_hat n ω - S.θ₀) := by
    intro n ω
    by_cases hcard : (split.foldB n).card = 0
    · -- Empty fold: both sides reduce to `√0 · _ = 0`.
      have hzero : Real.sqrt ((split.foldB n).card : ℝ) = 0 := by
        rw [hcard]; simp
      rw [hzero, zero_mul, zero_mul]
    · -- Nonempty fold: `dmlEstimator n ω = dmlChern n ω`.
      have hcard_pos : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hcard
      have hcardR_pos : 0 < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard_pos
      have hcardR_ne : ((split.foldB n).card : ℝ) ≠ 0 := hcardR_pos.ne'
      -- `(aipwGeneralMoment S hη₀_mem).J₀_inv = -1`.
      have h_J : (aipwGeneralMoment S hη₀_mem).J₀_inv = -1 := by
        show ((-1 : ℝ))⁻¹ = -1
        norm_num
      -- Pointwise: `aipwMoment(z, μ̂, ê, 0) = aipwMoment(z, μ̂, ê, S.θ₀) + S.θ₀`.
      have hpoint : ∀ i,
          aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) 0 =
            aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) S.θ₀ + S.θ₀ := by
        intro i
        unfold aipwMoment
        ring
      -- Sum the pointwise identity.
      have hsum :
          ∑ i ∈ split.foldB n,
              aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) 0
            = (∑ i ∈ split.foldB n,
                aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) S.θ₀)
              + ((split.foldB n).card : ℝ) * S.θ₀ := by
        rw [Finset.sum_congr rfl (fun i _ => hpoint i),
          Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      -- Reduce the goal: cancel the common `√|B(n)| · _` factor.
      congr 1
      -- First rewrite `J₀_inv` to `-1` (relative to the unreduced `aipwGeneralMoment`).
      simp only [Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator, dmlEstimator]
      rw [h_J]
      -- Now unfold the remaining `M.*` projections (`θ₀`, `m`).  After this
      -- `M.m (η_hat n ω) z M.θ₀ = aipwMoment z (μ_hat n ω) (e_hat n ω) S.θ₀`.
      simp only [aipwGeneralMoment, aipwMomentFunctional]
      -- Goal: `S.θ₀ − (−1) · ((|B|⁻¹) · Σ aipwMoment(., μ̂, ê, S.θ₀)) − S.θ₀
      --       = (|B|⁻¹) · Σ aipwMoment(., μ̂, ê, 0) − S.θ₀`.
      rw [hsum]
      field_simp
      ring
  -- Build the production `IsAsymLinear` from `hAL` field-by-field.
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero: `∫ S.ψ_AIPW dP_Z = 0`.
    have h := hAL.mean_zero
    rw [← h_if_eq]
    exact h
  · -- finite_var: `Integrable (fun z => (S.ψ_AIPW z) ^ 2) S.P_Z`.
    have h := hAL.finite_var
    rw [← h_if_eq]
    exact h
  · -- remainder: the two `IsLittleOp` integrands agree pointwise.
    have h := hAL.remainder
    -- The abstract remainder integrand and the production one are equal as
    -- functions of `(n, ω)`: rescaled errors agree by `h_resc_eq`, and the
    -- influence-function partial sum agrees by `h_if_eq`.
    have hfun_eq :
        (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) *
              (dmlEstimator S sample split μ_hat e_hat n ω - S.θ₀) -
              (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                ∑ i ∈ split.foldB n, S.ψ_AIPW (sample.Z i ω))
        = (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) *
              (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
                (aipwGeneralMoment S hη₀_mem) sample split η_hat n ω - S.θ₀) -
              (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                ∑ i ∈ split.foldB n,
                  (-(aipwGeneralMoment S hη₀_mem).J₀_inv *
                    aipwMomentFunctional S.η₀ (sample.Z i ω) S.θ₀)) := by
      funext n ω
      rw [h_resc_eq n ω]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have := congrArg (fun f => f (sample.Z i ω)) h_if_eq
      simpa using this.symm
    rw [hfun_eq]
    exact h

/-- **Asymptotic normality of the one-shot DML ATE** (`thm:est-dml-ate-al`,
"In particular ..." clause).  Given the same hypotheses as
`dml_ATE_isAsymLinear`, the rescaled estimator `√|B(n)| (θ̂ⁿ − θ₀)` converges
in distribution to `N(0, ∫ ψ_AIPW² dP_Z)`.

Together with `|B(n)|/n → c ∈ (0,1)`, Slutsky scaling gives the
`√n`-rate form `√n (θ̂ⁿ − θ₀) ⇒ N(0, σ²/c)` (variance inflated by the
sample-splitting cost `1/c`).  That last step is left to the caller. -/
theorem dml_ATE_tendstoNormal
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n ω a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n ω, ∀ᵐ x ∂S.P_X, ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (hψ_meas : Measurable (S.ψ_AIPW))
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB n) P.μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum sample (S.ψ_AIPW) split.foldB n) P.μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB)
      (gaussianMeasure 0 (∫ x, (S.ψ_AIPW x) ^ 2 ∂S.P_Z))
      P.μ
      hθn_meas := by
  haveI : IsProbabilityMeasure P.μ := inferInstance
  have hAL :=
    dml_ATE_isAsymLinear S hA h_overlap h_y2 h_yd2 sample split
      hc_pos hc_lt h_split_rate μ_hat e_hat h_mu_meas h_e_meas
      h_mu_memLp h_e_memLp h_e_overlap
      h_mu_foldA h_e_foldA h_mu_uncurry_foldA h_e_uncurry_foldA
      h_mu_rate h_e_rate h_product_rate
  exact hAL.tendsto_normal_foldB split hψ_meas hθn_meas hSum_meas

end ATE
end Estimation
end Causalean
