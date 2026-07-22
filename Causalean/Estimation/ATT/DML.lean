/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# One-shot DML / AIPW estimator for the back-door ATT

`def:est-dml-att` and `thm:est-dml-att-al` instantiated for the
`TreatedEstimationSystem` used by the ATT estimation layer.

The estimator is

    θ̂ⁿ_DML^ATT := (1/π̂_T) · (1/|B(n)|) Σ_{i ∈ B(n)} m_AIPW^ATT( η̂(n), Zᵢ, 0 ),

where `m_AIPW^ATT` is the ATT AIPW moment (Hahn 1998 form).  Concretely, with
`Aᵢ`, `Yᵢ`, `Xᵢ` denoting the
i-th data triple:

    θ̂ⁿ_DML^ATT := (1/π̂_T) · (1/|B(n)|) Σ_{i ∈ B(n)}
        [ Aᵢ · (Yᵢ − μ̂₀(Xᵢ))
          − (1 − Aᵢ) · (ê(Xᵢ)/(1 − ê(Xᵢ))) · (Yᵢ − μ̂₀(Xᵢ)) ].

(For now we use the population marginal `S.π_val` as the rescale; the empirical
`π̂_T` can be substituted later via continuous-mapping plus delta-method
arguments — see `Stat/DeltaMethod.lean`.)

The headline theorem gives asymptotic linearity at `θ₀` with influence
function `ψ_ATT`, under the rate hypothesis
`|B(n)|/n → c` for some `c ∈ (0, 1)` and the ATT product rate condition.

The proof composes the abstract `att_dml_isAsymLinear` from `ATTInstance.lean`
with two transport equalities:

1. **Rescaled-error / IF transport** —
   the `−A·θ₀` term in the abstract Chernozhukov score cancels exactly against
   the same empirical treatment-indicator sum appearing when the population-π
   estimator is centered by the centered `ψ_ATT`.

Proof sketch (NL doc, `thm:est-dml-att-al`): main term + three remainders
(`R₁` killed by Neyman orthogonality + product rate on the ATT remainder
identity; `R₂` killed by empirical-process Markov + individual rates on the
ATT score-difference L² rate; `R₃` lower-order arithmetic). -/

import Causalean.Estimation.ATT.InfluenceFunction
import Causalean.Estimation.ATT.Remainder
import Causalean.Estimation.ATT.Score.AIPWScoreL2
import Causalean.Estimation.ATT.ATTInstance
import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.SampleSplit.PartialFoldCLT
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # Double Machine Learning for ATT

This file defines the one-shot sample-split augmented inverse-probability
weighted estimator for the back-door average treatment effect on the treated
and states its asymptotic linearity theorem. The theorem connects the estimator
to the ATT AIPW influence function under the one-sided ATT back-door assumption
bundle, an additional one-sided upper-overlap bound, second-moment,
sample-split, and nuisance-rate conditions. Parallel to
`Estimation/ATE/DML.lean`.

The main declarations are `dmlEstimator_ATT`, the derived influence-function
facts `ψ_ATT_integral_zero` and `ψ_ATT_finite_var`, and the production wrapper
`dml_ATT_isAsymLinear`, which transports the abstract
`att_dml_isAsymLinear` result to the population-π ATT estimator.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- One-shot DML / AIPW estimator of the back-door ATT
(`def:est-dml-att`).

Inputs:
* `S`         — treated estimation system carrying the value-space truth
                `(μ₀_val, e_val)` and marginal treatment probability `π_val`.
* `sample`    — i.i.d. sample of triples `(X, A, Y) ∼ P_Z`.
* `split`     — one-shot split of the sample.
* `μ₀_hat`    — control-arm outcome regression estimator at horizon `n`.
* `e_hat`     — propensity estimator at horizon `n`.

Output: `(1/π_val)` times the empirical mean over `B(n)` of
`m_AIPW^ATT( η̂(n), Zᵢ, 0 )`.  Equivalently, the empirical ATT AIPW
pseudo-outcome rescaled by the treatment marginal. -/
noncomputable def dmlEstimator_ATT
    (S : TreatedEstimationSystem P γ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (μ₀_hat : ℕ → P.Ω → (γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (n : ℕ) : P.Ω → ℝ :=
  fun ω =>
    (1 / S.π_val) *
    (((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n,
        aipwMomentATT (sample.Z i ω) (μ₀_hat n ω) (e_hat n ω) 0)

section ψ_ATT_IF_facts
open Causalean.Estimation.ATE.BackdoorEstimationSystem (indA projA)

/-- **Mean zero of the centered population-π ATT influence function** `ψ_ATT`.

`∫ ψ_ATT dP_Z = 0`.  Derived (not assumed) from `aipw_mean_zero_ATT` — mean-zero
of the AIPW moment at `θ₀` — together with `∫ A dP_Z = π_T` and the algebraic
identity `m_AIPW^ATT(η₀, z, 0) = m_AIPW^ATT(η₀, z, θ₀) + A·θ₀`:
`∫ ψ_ATT = (1/π_T)·(0 + θ₀·π_T) − θ₀ = 0`. -/
theorem ψ_ATT_integral_zero
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (hIPW : Integrable (fun ω =>
        (1 - S.toPOBackdoorSystem.dVar.indicator true ω)
          * (S.toPOBackdoorSystem.propScore true ω
              / (1 - S.toPOBackdoorSystem.propScore true ω))
          * (S.toPOBackdoorSystem.factualY ω
              - S.toPOBackdoorSystem.adjustedCE false ω)) P.μ) :
    ∫ z, S.ψ_ATT z ∂(S.P_Z) = 0 := by
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  have hπ_ne : S.π_val ≠ 0 := ne_of_gt hπ_pos
  have hmz : ∫ z, aipwMomentATT z S.μ₀_val S.e_val S.θ₀ ∂S.P_Z = 0 :=
    aipw_mean_zero_ATT S hA hπ_pos hIPW
  have hm_meas : Measurable (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) :=
    measurable_aipwMomentATT_at_θ₀ S
  have hm_int : Integrable (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) S.P_Z :=
    ((memLp_two_iff_integrable_sq hm_meas.aestronglyMeasurable).2
      (aipw_finite_var_ATT S h_overlap hA h_y2 h_y0_2)).integrable (by norm_num)
  have hindA_meas : Measurable (fun z : γ × Bool × ℝ => indA z) := by
    unfold indA projA
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurable_snd.fst (MeasurableSet.singleton true)
  have hindA_memLp : MemLp (fun z : γ × Bool × ℝ => indA z) 2 S.P_Z := by
    refine MemLp.of_bound hindA_meas.aestronglyMeasurable (1 : ℝ) ?_
    filter_upwards with z
    rcases hb : z.2.1 with _ | _ <;> simp [indA, projA, hb]
  have hindA_int : Integrable (fun z : γ × Bool × ℝ => indA z) S.P_Z :=
    hindA_memLp.integrable (by norm_num)
  have hindA_integral : ∫ z, indA z ∂S.P_Z = S.π_val := by
    rw [TreatedEstimationSystem.P_Z,
      integral_map S.measurable_factualZ.aemeasurable
        hindA_meas.aestronglyMeasurable]
    have hpt : (fun ω => indA (S.factualZ ω))
        = (fun ω => S.toPOBackdoorSystem.dVar.indicator true ω) := by
      funext ω
      by_cases hD : S.toPOBackdoorSystem.factualD ω = true
      · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
          S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
        simp [TreatedEstimationSystem.factualZ, indA, projA, hD, hInd]
      · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
          S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
        simp [TreatedEstimationSystem.factualZ, indA, projA, hD, hInd]
    rw [hpt]
    rfl
  have hsplit : ∀ z, aipwMomentATT z S.μ₀_val S.e_val 0
      = aipwMomentATT z S.μ₀_val S.e_val S.θ₀ + indA z * S.θ₀ := by
    intro z; unfold aipwMomentATT; ring
  have hm0_int : Integrable (fun z => aipwMomentATT z S.μ₀_val S.e_val 0) S.P_Z := by
    refine (hm_int.add (hindA_int.mul_const S.θ₀)).congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    rw [hsplit z]
  have hm0_integral :
      ∫ z, aipwMomentATT z S.μ₀_val S.e_val 0 ∂S.P_Z = S.θ₀ * S.π_val := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add hm_int (hindA_int.mul_const S.θ₀), hmz, zero_add,
      integral_mul_const, hindA_integral]
    ring
  have hconst : ∫ _z : γ × Bool × ℝ, S.θ₀ ∂S.P_Z = S.θ₀ := by
    rw [integral_const]; simp
  unfold TreatedEstimationSystem.ψ_ATT
  rw [integral_sub (hm0_int.const_mul (1 / S.π_val)) (integrable_const S.θ₀),
    integral_const_mul, hm0_integral, hconst, one_div,
    mul_comm S.θ₀ S.π_val, inv_mul_cancel_left₀ hπ_ne, sub_self]

/-- **Finite variance of the centered population-π ATT influence function.**
`Integrable ψ_ATT²` against `P_Z`.  Derived (not assumed) from
`aipw_finite_var_ATT` (square-integrability of the moment at `θ₀`) and
boundedness of the treatment indicator, via
`ψ_ATT = (1/π_T)·(m(η₀,·,θ₀) + θ₀·A) − θ₀ ∈ L²(P_Z)`. -/
theorem ψ_ATT_finite_var
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ) :
    Integrable (fun z => (S.ψ_ATT z) ^ 2) S.P_Z := by
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  have hm_meas : Measurable (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) :=
    measurable_aipwMomentATT_at_θ₀ S
  have hm_L2 : MemLp (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) 2 S.P_Z :=
    (memLp_two_iff_integrable_sq hm_meas.aestronglyMeasurable).2
      (aipw_finite_var_ATT S h_overlap hA h_y2 h_y0_2)
  have hindA_meas : Measurable (fun z : γ × Bool × ℝ => indA z) := by
    unfold indA projA
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurable_snd.fst (MeasurableSet.singleton true)
  have hindA_L2 : MemLp (fun z : γ × Bool × ℝ => indA z) 2 S.P_Z := by
    refine MemLp.of_bound hindA_meas.aestronglyMeasurable (1 : ℝ) ?_
    filter_upwards with z
    rcases hb : z.2.1 with _ | _ <;> simp [indA, projA, hb]
  have hm0_L2 : MemLp (fun z => aipwMomentATT z S.μ₀_val S.e_val 0) 2 S.P_Z :=
    (hm_L2.add (hindA_L2.const_smul S.θ₀)).ae_eq
      (Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        unfold aipwMomentATT; ring)
  have hψeq : (fun z => S.ψ_ATT z)
      = (fun z => (1 / S.π_val) • aipwMomentATT z S.μ₀_val S.e_val 0 - S.θ₀) := by
    funext z; unfold TreatedEstimationSystem.ψ_ATT; simp only [smul_eq_mul]
  have hψ_L2 : MemLp (fun z => S.ψ_ATT z) 2 S.P_Z := by
    rw [hψeq]
    exact (hm0_L2.const_smul (1 / S.π_val)).sub (memLp_const S.θ₀)
  exact hψ_L2.integrable_sq

end ψ_ATT_IF_facts

set_option maxHeartbeats 1200000 in
-- The wrapper composes ~20 derived hypotheses (rate translations, score
-- measurability, integrability, two transport equalities) and applies the
-- abstract `att_dml_isAsymLinear`; the resulting elaboration exceeds the
-- default heartbeat budget when type-checking the final `refine ⟨…⟩` block.
/-- **Asymptotic linearity of the one-shot DML ATT** — `thm:est-dml-att-al`.

Hypotheses (mirroring the NL doc verbatim, including the split-rate
hypothesis `|B(n)|/n → c`):

1. the one-sided PO back-door `ATTAssumptions` bundle;
2. one-sided upper overlap on the truth and learners:
   `e_val(x) ≤ 1 − ε` and `ê(n,ω,x) ≤ 1 − ε` hold `P_X`-a.e.;
3. the truth and learner nuisance functions lie in the a.e./L² class
   `H_ε S ε`;
4. positivity of the marginal treatment probability `0 < π_T`;
5. `E[Y²] < ∞` and `E[Y(0)²] < ∞`;
6. one-shot split with `|B(n)|/n → c` for some `c ∈ (0, 1)`;
7. `μ̂₀(n)` and `ê(n)` depend only on the nuisance fold `A(n)`;
8. joint and fold-A measurability, per-ω L² membership, and score
   integrability / finite-variance hypotheses for the nuisance-dependent ATT
   score;
9. individual rates `‖μ̂₀(n)(X) − μ₀_val(X)‖_{L²(P_X)} = o_p(1)` and
   `‖ê(n)(X) − e_val(X)‖_{L²(P_X)} = o_p(1)`;
10. product rate
    `‖μ̂₀(n)(X) − μ₀_val(X)‖_{L²(P_X)} · ‖ê(n)(X) − e_val(X)‖_{L²(P_X)}
        = o_p(n^{-1/2})`.

The IPW-correction integrability gates (truth and per-learner) are *derived*
internally via `ipw_truth_integrable` / `ipw_estimated_integrable`, not taken
as hypotheses.

Conclusion: `IsAsymLinear (dmlEstimator_ATT …) θ₀ ψ_ATT sample split.foldB`.

The proof is a thin wrapper over the abstract
`Causalean.Estimation.ATT.att_dml_isAsymLinear` (in
`Estimation/ATT/ATTInstance.lean`): build the abstract `η_hat` from
`(μ₀_hat, e_hat)`, translate the rate / measurability / integrability
hypotheses, apply the abstract theorem, then transport the conclusion by the
pointwise cancellation between the abstract `−A·θ₀` score term and the centered
population-π influence function `S.ψ_ATT`.

The `IsAsymLinear` mean-zero and finite-variance fields for `ψ_ATT` are
*derived* internally via `ψ_ATT_integral_zero` and `ψ_ATT_finite_var` (from
`aipw_mean_zero_ATT` / `aipw_finite_var_ATT`), not taken as hypotheses. -/
theorem dml_ATT_isAsymLinear
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_e_overlap : ∀ᵐ x ∂S.P_X, S.e_val x ≤ 1 - ε)
    (h_e_lb : ∀ x, 0 ≤ S.e_val x)
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ₀_hat : ℕ → P.Ω → (γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (h_e_hat_overlap : ∀ n ω, ∀ᵐ x ∂S.P_X, e_hat n ω x ≤ 1 - ε)
    (h_e_hat_lb : ∀ n ω x, 0 ≤ e_hat n ω x)
    (h_μ₀_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => μ₀_hat n p.1 p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_μ₀_memLp :
      ∀ n ω, MemLp (fun x => μ₀_hat n ω x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_μ₀_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ₀_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_μ₀_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ₀_hat n p.1 p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_m_int : ∀ n ω,
      Integrable
        (fun z => aipwMomentATT z (μ₀_hat n ω) (e_hat n ω) S.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable
        (fun z => (aipwMomentATT z (μ₀_hat n ω) (e_hat n ω) S.θ₀) ^ 2) S.P_Z)
    (h_mu_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => μ₀_hat n ω x - S.μ₀_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => μ₀_hat n ω x - S.μ₀_val x) 2 S.P_X).toReal *
            (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (dmlEstimator_ATT S sample split μ₀_hat e_hat)
      S.θ₀
      S.ψ_ATT
      sample
      split.foldB := by
  -- 0. Discharge the truth-nuisance IPW integrability gate from overlap + L².
  have hIPW := ipw_truth_integrable S h_overlap hA h_y2 h_y0_2
  -- 1. Build the abstract `η_hat : ℕ → P.Ω → TreatedNuisanceVec γ`.
  let η_hat : ℕ → P.Ω → TreatedNuisanceVec γ := fun n ω =>
    { μ₀_fn := μ₀_hat n ω
      e_fn := e_hat n ω
      μ₀_meas :=
        (h_μ₀_meas n).comp
          (Measurable.prodMk measurable_const measurable_id)
      e_meas :=
        (h_e_meas n).comp
          (Measurable.prodMk measurable_const measurable_id) }
  -- `S.P_X` is a probability measure (used by `MemLp.of_bound` for `S.e_val`).
  haveI : IsProbabilityMeasure S.P_X := by
    unfold TreatedEstimationSystem.P_X
    exact Measure.isProbabilityMeasure_map
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable
  -- `S.P_Z` is a probability measure (used by score integrability transport).
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  -- 2. Per-η̂ L² differences for the abstract remainder bound.
  have hμ₀_val_memLp : MemLp S.μ₀_val 2 S.P_X := by
    have hY0_L2 : MemLp (S.toPOBackdoorSystem.YofD false) 2 P.μ :=
      (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD false).aestronglyMeasurable).2 h_y0_2
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD false |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hY0_L2.condExp
    have hcomp_L2 :
        MemLp (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hcond_L2.ae_eq (S.μ₀_compat hA)
    rw [TreatedEstimationSystem.P_X]
    exact (memLp_map_measure_iff S.μ₀_meas.aestronglyMeasurable
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable).2 hcomp_L2
  have he_val_memLp : MemLp S.e_val 2 S.P_X := by
    refine MemLp.of_bound S.e_meas.aestronglyMeasurable 1 ?_
    filter_upwards [h_e_overlap] with x hx
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [h_e_lb x],
      by linarith [hx, h_overlap.1]⟩
  have he_val_memLp_top : MemLp S.e_val ⊤ S.P_X := by
    refine MemLp.of_bound S.e_meas.aestronglyMeasurable 1 ?_
    filter_upwards [h_e_overlap] with x hx
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [h_e_lb x],
      by linarith [hx, h_overlap.1]⟩
  have hη₀_mem : S.η₀ ∈ H_ε S ε := by
    refine ⟨h_e_overlap, ?_, ?_⟩
    · simpa [TreatedEstimationSystem.η₀] using hμ₀_val_memLp
    · simpa [TreatedEstimationSystem.η₀] using he_val_memLp_top
  have h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε S ε := by
    intro n ω
    refine ⟨h_e_hat_overlap n ω, ?_, ?_⟩
    · simpa [η_hat] using h_μ₀_memLp n ω
    · refine MemLp.of_bound (η_hat n ω).e_meas.aestronglyMeasurable 1 ?_
      filter_upwards [h_e_hat_overlap n ω] with x hx
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [h_e_hat_lb n ω x],
        by linarith [hx, h_overlap.1]⟩
  have h_mu_diff_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X := by
    intro n ω
    exact (h_μ₀_memLp n ω).sub hμ₀_val_memLp
  have h_e_diff_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X := by
    intro n ω
    exact (h_e_memLp n ω).sub he_val_memLp
  -- 3. Translate score measurability to the abstract interface.
  have h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    unfold aipwMomentATTFunctional aipwMomentATT
    unfold Causalean.Estimation.ATE.BackdoorEstimationSystem.indA
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projX
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projA
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projY
    dsimp [η_hat]
    have hA : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => p.2.2.1) :=
      measurable_snd.snd.fst
    have hY : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => p.2.2.2) :=
      measurable_snd.snd.snd
    have hproj : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => (p.1, p.2.1)) :=
      Measurable.prodMk measurable_fst measurable_snd.fst
    have hμ : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => μ₀_hat n p.1 p.2.1) :=
      (h_μ₀_meas n).comp hproj
    have he : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => e_hat n p.1 p.2.1) :=
      (h_e_meas n).comp hproj
    have hindA :
        Measurable (fun p : P.Ω × (γ × Bool × ℝ) =>
          if p.2.2.1 = true then (1 : ℝ) else 0) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact hA (MeasurableSet.singleton true)
    have hOne : Measurable (fun _ : P.Ω × (γ × Bool × ℝ) => (1 : ℝ)) :=
      measurable_const
    have hθ : Measurable (fun _ : P.Ω × (γ × Bool × ℝ) => S.θ₀) :=
      measurable_const
    simpa [mul_assoc] using
      (((hindA.mul (hY.sub hμ)).sub
        ((hOne.sub hindA).mul
          ((he.div (hOne.sub he)).mul (hY.sub hμ)))).sub
        (hindA.mul hθ))
  have h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀) := by
    intro n
    unfold aipwMomentATTFunctional aipwMomentATT
    unfold Causalean.Estimation.ATE.BackdoorEstimationSystem.indA
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projX
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projA
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projY
    dsimp [η_hat]
    fun_prop
  have h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
          (fun (p : P.Ω × (γ × Bool × ℝ)) =>
            aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    change Measurable[(MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
      (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
      (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀)
    unfold aipwMomentATTFunctional aipwMomentATT
    unfold Causalean.Estimation.ATE.BackdoorEstimationSystem.indA
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projX
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projA
      Causalean.Estimation.ATE.BackdoorEstimationSystem.projY
    dsimp [η_hat]
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
    have hμ :
        Measurable (fun p : P.Ω × (γ × Bool × ℝ) => μ₀_hat n p.1 p.2.1) :=
      (h_μ₀_uncurry_foldA n).comp hproj
    have he :
        Measurable (fun p : P.Ω × (γ × Bool × ℝ) => e_hat n p.1 p.2.1) :=
      (h_e_uncurry_foldA n).comp hproj
    have hA :
        @Measurable (P.Ω × (γ × Bool × ℝ)) Bool
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun p => p.2.2.1) :=
      measurable_snd.snd.fst
    have hY :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun p => p.2.2.2) :=
      measurable_snd.snd.snd
    have hindA :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun p => if p.2.2.1 = true then (1 : ℝ) else 0) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact hA (MeasurableSet.singleton true)
    have hOne :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun _ => (1 : ℝ)) :=
      measurable_const
    have hθ :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun _ => S.θ₀) :=
      measurable_const
    simpa [mul_assoc] using
      (((hindA.mul (hY.sub hμ)).sub
        ((hOne.sub hindA).mul
          ((he.div (hOne.sub he)).mul (hY.sub hμ)))).sub
        (hindA.mul hθ))
  have h_m_int_abs : ∀ n ω,
      Integrable (fun z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀) S.P_Z := by
    intro n ω
    simpa [aipwMomentATTFunctional, η_hat] using h_m_int n ω
  have h_m_sq_int_abs : ∀ n ω,
      Integrable (fun z => (aipwMomentATTFunctional (η_hat n ω) z S.θ₀) ^ 2)
        S.P_Z := by
    intro n ω
    simpa [aipwMomentATTFunctional, η_hat] using h_m_sq_int n ω
  have h_IPW_at_abs :
      ∀ n ω, Integrable (fun z =>
        (1 - Causalean.Estimation.ATE.BackdoorEstimationSystem.indA z)
          * ((η_hat n ω).e_fn
                (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)
              / (1 - (η_hat n ω).e_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
          * (Causalean.Estimation.ATE.BackdoorEstimationSystem.projY z
              - (η_hat n ω).μ₀_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
        S.P_Z := by
    intro n ω
    exact ipw_estimated_integrable S h_overlap.1 (η_hat n ω)
      (Filter.Eventually.of_forall (h_e_hat_lb n ω))
      (h_e_hat_overlap n ω)
      (h_μ₀_memLp n ω) h_y2
  -- 4. Translate the production rate hypotheses to the abstract `ρ₁ / ρ₂`.
  have h_indiv_rate_ρ₁ :
      IsLittleOp
        (fun n ω =>
          (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [attGeneralMoment, η₀, η_hat] using h_mu_rate
  have h_indiv_rate_ρ₂ :
      IsLittleOp
        (fun n ω =>
          (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [attGeneralMoment, η₀, η_hat] using h_e_rate
  have h_product_rate_abs :
      IsLittleOp
        (fun n ω =>
          (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ) *
            (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
                (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
    simpa [attGeneralMoment, η₀, η_hat] using h_product_rate
  -- 5. Apply the abstract theorem.
  have hAL :=
    att_dml_isAsymLinear S hη₀_mem h_e_lb h_overlap hA hπ_pos h_y2 h_y0_2 hIPW
      sample split hc_pos hc_lt h_split_rate η_hat h_in_Hε
      h_e_hat_lb h_mu_diff_memLp h_e_diff_memLp h_IPW_at_abs
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int_abs h_m_sq_int_abs
      h_indiv_rate_ρ₁ h_indiv_rate_ρ₂ h_product_rate_abs
  -- 6. Transport the remainder from the Chernozhukov form to the population-π
  -- estimator and centered ATT IF.
  refine ⟨ψ_ATT_integral_zero S h_overlap hA hπ_pos h_y2 h_y0_2 hIPW,
    ψ_ATT_finite_var S h_overlap hA h_y2 h_y0_2, ?_⟩
  have h := hAL.remainder
  have hfun_eq :
      (fun n ω =>
          Real.sqrt ((split.foldB n).card : ℝ) *
            (dmlEstimator_ATT S sample split μ₀_hat e_hat n ω - S.θ₀) -
            (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ∑ i ∈ split.foldB n, S.ψ_ATT (sample.Z i ω))
      = (fun n ω =>
          Real.sqrt ((split.foldB n).card : ℝ) *
            (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
              (attGeneralMoment S hη₀_mem hπ_pos) sample split η_hat n ω - S.θ₀) -
            (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ∑ i ∈ split.foldB n,
                (-(attGeneralMoment S hη₀_mem hπ_pos).J₀_inv *
                  aipwMomentATTFunctional S.η₀ (sample.Z i ω) S.θ₀)) := by
    funext n ω
    by_cases hcard : (split.foldB n).card = 0
    · have hzero : Real.sqrt ((split.foldB n).card : ℝ) = 0 := by
        rw [hcard]; simp
      simp [hzero]
    · have hcard_pos : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hcard
      have hcardR_pos : 0 < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard_pos
      have hcardR_ne : ((split.foldB n).card : ℝ) ≠ 0 := hcardR_pos.ne'
      have h_J : (attGeneralMoment S hη₀_mem hπ_pos).J₀_inv = -S.π_val⁻¹ := by
        change (-(S.π_val))⁻¹ = -S.π_val⁻¹
        simp
      have hpoint_hat : ∀ i,
          aipwMomentATT (sample.Z i ω) (μ₀_hat n ω) (e_hat n ω) 0 =
            aipwMomentATT (sample.Z i ω) (μ₀_hat n ω) (e_hat n ω) S.θ₀ +
              Causalean.Estimation.ATE.BackdoorEstimationSystem.indA (sample.Z i ω) * S.θ₀ := by
        intro i
        unfold aipwMomentATT
        ring
      have hpoint_true : ∀ i,
          S.ψ_ATT (sample.Z i ω) =
            S.π_val⁻¹ *
              aipwMomentATTFunctional S.η₀ (sample.Z i ω) S.θ₀ +
              S.π_val⁻¹ *
                (Causalean.Estimation.ATE.BackdoorEstimationSystem.indA (sample.Z i ω) * S.θ₀) -
              S.θ₀ := by
        intro i
        unfold TreatedEstimationSystem.ψ_ATT aipwMomentATTFunctional η₀
        rw [one_div]
        unfold aipwMomentATT
        ring
      have hsum_hat :
          ∑ i ∈ split.foldB n,
              aipwMomentATT (sample.Z i ω) (μ₀_hat n ω) (e_hat n ω) 0
            = (∑ i ∈ split.foldB n,
                aipwMomentATT (sample.Z i ω) (μ₀_hat n ω) (e_hat n ω) S.θ₀)
              + ∑ i ∈ split.foldB n,
                Causalean.Estimation.ATE.BackdoorEstimationSystem.indA (sample.Z i ω) * S.θ₀ := by
        rw [Finset.sum_congr rfl (fun i _ => hpoint_hat i), Finset.sum_add_distrib]
      have hsum_true :
          ∑ i ∈ split.foldB n, S.ψ_ATT (sample.Z i ω)
            = S.π_val⁻¹ * (∑ i ∈ split.foldB n,
                aipwMomentATTFunctional S.η₀ (sample.Z i ω) S.θ₀)
              + S.π_val⁻¹ * (∑ i ∈ split.foldB n,
                Causalean.Estimation.ATE.BackdoorEstimationSystem.indA (sample.Z i ω) * S.θ₀)
              - ((split.foldB n).card : ℝ) * S.θ₀ := by
        rw [Finset.sum_congr rfl (fun i _ => hpoint_true i),
          Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp only [Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator, dmlEstimator_ATT]
      rw [h_J]
      simp only [attGeneralMoment, aipwMomentATTFunctional]
      rw [hsum_hat, hsum_true]
      have hsqrt_ne : Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 :=
        (Real.sqrt_pos.2 hcardR_pos).ne'
      field_simp [hcardR_ne, hπ_pos.ne', hsqrt_ne]
      rw [Real.sq_sqrt hcardR_pos.le]
      simp only [aipwMomentATTFunctional, η_hat]
      rw [show
          (∑ x ∈ split.foldB n,
            S.θ₀ * Causalean.Estimation.ATE.BackdoorEstimationSystem.indA (sample.Z x ω)) =
          (∑ x ∈ split.foldB n,
            Causalean.Estimation.ATE.BackdoorEstimationSystem.indA (sample.Z x ω) * S.θ₀) by
            exact Finset.sum_congr rfl (fun x _ => by ring)]
      field_simp [hπ_pos.ne']
      ring_nf
      have hsum_cancel :
          S.π_val * (∑ x ∈ split.foldB n,
            aipwMomentATT (sample.Z x ω) S.η₀.μ₀_fn S.η₀.e_fn S.θ₀ * S.π_val⁻¹) =
            ∑ x ∈ split.foldB n,
              aipwMomentATT (sample.Z x ω) S.η₀.μ₀_fn S.η₀.e_fn S.θ₀ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by field_simp [hπ_pos.ne'])
      rw [hsum_cancel]
      have hAraw :
          (∑ i ∈ split.foldB n,
            aipwMomentATT (sample.Z i ω) (μ₀_hat n ω) (e_hat n ω) S.θ₀) *
              Nat.rawCast 1 =
            ∑ i ∈ split.foldB n,
              aipwMomentATT (sample.Z i ω) (μ₀_hat n ω) (e_hat n ω) S.θ₀ := by
        norm_num
      exact congrArg (fun a => a - (∑ x ∈ split.foldB n,
        aipwMomentATT (sample.Z x ω) S.η₀.μ₀_fn S.η₀.e_fn S.θ₀)) hAraw.symm
  rw [hfun_eq]
  exact h

end ATT
end Estimation
end Causalean
