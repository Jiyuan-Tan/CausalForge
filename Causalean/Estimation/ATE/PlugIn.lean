/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sample-split plug-in estimator for the back-door ATE

`def:est-plug-in-ate` and `thm:est-plug-in-ate-al` instantiated for the
`BackdoorEstimationSystem` from the ATE estimation setup.

The estimator is

    θ̂ⁿ_plugin := (1/|B(n)|) Σ_{i ∈ B(n)} ( μ̂(n)(1, Xᵢ) − μ̂(n)(0, Xᵢ) ),

with `B(n)` the estimation fold of a one-shot split, and `μ̂` an estimator of
the value-space outcome regression that depends only on the nuisance fold
`A(n)`.

The headline theorem gives asymptotic linearity at `θ₀` with influence
function `ψ_plugin(z) = μ(1, x) − μ(0, x) − θ₀`, under the rate
hypothesis `|B(n)|/n → c` for some `c ∈ (0, 1)`.

Proof sketch (NL doc, `thm:est-plug-in-ate-al`): two-piece argument on the
bias term — Cauchy–Schwarz on the conditional mean and Markov on the
conditional variance, both `o_p(1)` by hypothesis (4); main term is a
centered i.i.d. sum to which the CLT applies; on fold `B(n)` the scaling is
`√|B(n)|`. Since `|B(n)|/n → c`, this differs from `√n` by a fixed factor
`√c`.
-/

import Causalean.Estimation.ATE.InfluenceFunction
import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.SampleSplit.PartialFoldCLT
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Plug-In ATE Estimator

This file defines the sample-split plug-in estimator for the back-door average
treatment effect using only the estimated outcome regression. It also records
the corresponding influence function and the asymptotic-linearity statement
that compares this estimator with the target average treatment effect.

The main declarations are `plugInEstimator`, `ψ_plugin`,
`plugIn_isAsymLinear`, and `plugIn_tendstoNormal`.  The proofs use the
covariate-law representation of the ATE, fold-B empirical-process bounds, and
the L² rate of the outcome-regression nuisance to control the plug-in bias.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Sample-split plug-in estimator of the back-door ATE
(`def:est-plug-in-ate`).

Inputs:
* `S`           — back-door estimation system carrying the value-space
                  truth `(μ_val, e_val)`.
* `sample`      — i.i.d. sample of triples `(X, A, Y) ∼ P_Z`.
* `split`       — one-shot split of the sample.
* `μ̂`          — estimator of the outcome regression at horizon `n`,
                  evaluated on `Ω` (depends only on nuisance fold `A(n)`).

Output: `θ̂ⁿ_plugin = (1/|B(n)|) Σ_{i ∈ B(n)} ( μ̂(n)(1, Xᵢ) − μ̂(n)(0, Xᵢ) )`.
-/
noncomputable def plugInEstimator
    (S : BackdoorEstimationSystem P γ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (n : ℕ) : P.Ω → ℝ :=
  fun ω =>
    ((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n,
        (μ_hat n ω true (projX (sample.Z i ω))
          - μ_hat n ω false (projX (sample.Z i ω)))

/-- Plug-in influence function `ψ_plugin(z) := μ(1, x) − μ(0, x) − θ₀`
from `thm:est-plug-in-ate-al`. -/
noncomputable def ψ_plugin (S : BackdoorEstimationSystem P γ)
    (z : γ × Bool × ℝ) : ℝ :=
  S.μ_val true (projX z) - S.μ_val false (projX z) - S.θ₀

/-- **Asymptotic linearity of the plug-in ATE** — `thm:est-plug-in-ate-al`.

Hypotheses (mirroring the NL doc verbatim, including the split-rate
hypothesis `|B(n)|/n → c`):

1. back-door `Assumptions` (already imports consistency, unconfoundedness,
   overlap, integrabilities);
2. square-integrability of the counterfactual outcomes, used to put the
   plug-in influence function in `L²`;
3. one-shot split with `|B(n)|/n → c` for some `c ∈ (0, 1)`;
4. nuisance estimator `μ̂(n)` depends only on the nuisance fold and satisfies
   the joint `o_p(n^{-1/2})` rate
        ‖μ̂(n)(·, X) − μ_val(·, X)‖_{L²(P_X)} = o_p(n^{-1/2})
   — encoded here as an `IsLittleOp` of the per-`a`-summed L²-norm
   process against `n ↦ n^{-1/2}` under `P.μ`.

Conclusion: `IsAsymLinear (plugInEstimator …) θ₀ ψ_plugin sample split.foldB`. -/
theorem plugIn_isAsymLinear
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_mu_memLp :
      ∀ n ω a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_rate :
      IsLittleOp
        (fun n ω =>
          Real.sqrt
            (∑ a : Bool,
              (eLpNorm
                (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (plugInEstimator S sample split μ_hat)
      S.θ₀
      (ψ_plugin S)
      sample
      split.foldB := by
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero: `ψ_plugin = (μ_val 1 - μ_val 0) - θ₀` integrates to `θ₀ - θ₀ = 0`.
    have hψ_meas : Measurable (ψ_plugin S) := by
      unfold ψ_plugin
      exact ((S.μ_meas true).comp measurable_fst).sub ((S.μ_meas false).comp measurable_fst)
        |>.sub measurable_const
    rw [BackdoorEstimationSystem.P_Z,
      MeasureTheory.integral_map S.measurable_factualZ.aemeasurable hψ_meas.aestronglyMeasurable]
    have hbase_int :
        Integrable
          (fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω)) P.μ := by
      have hcate : ∀ d, Integrable (S.toPOBackdoorSystem.CATE d) P.μ := fun d => by
        unfold POBackdoorSystem.CATE
        exact MeasureTheory.integrable_condExp
      have h1 :
          Integrable (fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω)) P.μ :=
        (hcate true).congr (S.μ_compat hA true)
      have h0 :
          Integrable (fun ω => S.μ_val false (S.toPOBackdoorSystem.factualX ω)) P.μ :=
        (hcate false).congr (S.μ_compat hA false)
      exact h1.sub h0
    have hθ_int : Integrable (fun _ : P.Ω => (S.θ₀ : ℝ)) P.μ := integrable_const _
    have hθ_const : (∫ _ : P.Ω, (S.θ₀ : ℝ) ∂P.μ) = S.θ₀ := by
      haveI : IsProbabilityMeasure P.μ := inferInstance
      simp
    show ∫ ω, ψ_plugin S (S.factualZ ω) ∂P.μ = 0
    have heq : (fun ω => ψ_plugin S (S.factualZ ω))
        = (fun ω => (S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω)) - S.θ₀) := by
      funext ω; rfl
    rw [heq, integral_sub hbase_int hθ_int,
      ← theta_zero_factualX_integral S, hθ_const]
    ring
  · -- finite_var: ψ_plugin = (μ_val 1 ∘ X) − (μ_val 0 ∘ X) − θ₀ ∈ L²(P_Z).
    -- L² of `μ_val d ∘ factualX` follows from `h_yd2` via conditional Jensen
    -- (cf. `aipw_finite_var`); push to `P_Z` along `factualZ`.
    have hψ_meas : Measurable (ψ_plugin S) := by
      unfold ψ_plugin
      exact (((S.μ_meas true).comp measurable_fst).sub
        ((S.μ_meas false).comp measurable_fst)).sub measurable_const
    have hμ_L2 :
        ∀ d : Bool, MemLp
          (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
      intro d
      have hYd_L2 : MemLp (S.toPOBackdoorSystem.YofD d) 2 P.μ :=
        (memLp_two_iff_integrable_sq
          (S.toPOBackdoorSystem.measurable_YofD d).aestronglyMeasurable).2 (h_yd2 d)
      have hcond_L2 :
          MemLp (P.μ[S.toPOBackdoorSystem.YofD d |
            S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
        hYd_L2.condExp
      exact hcond_L2.ae_eq (S.μ_compat hA d)
    have hψ_comp_L2 : MemLp (fun ω => ψ_plugin S (S.factualZ ω)) 2 P.μ := by
      have hbase_L2 := (hμ_L2 true).sub (hμ_L2 false)
      have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ := memLp_const _
      simpa [ψ_plugin, BackdoorEstimationSystem.factualZ, projX]
        using hbase_L2.sub hconst_L2
    have hψ_L2 : MemLp (ψ_plugin S) 2 S.P_Z := by
      rw [BackdoorEstimationSystem.P_Z]
      exact (memLp_map_measure_iff hψ_meas.aestronglyMeasurable
        S.measurable_factualZ.aemeasurable).2 hψ_comp_L2
    exact hψ_L2.integrable_sq
  · -- remainder: decompose into centered fold-B fluctuation plus plug-in bias.
    let δ : ℕ → P.Ω → γ → ℝ := fun n ω x =>
      (μ_hat n ω true x - S.μ_val true x) -
        (μ_hat n ω false x - S.μ_val false x)
    let G : ℕ → P.Ω → ℝ := fun n ω =>
      (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n, (δ n ω (projX (sample.Z i ω)) -
          ∫ x, δ n ω x ∂S.P_X)
    let B : ℕ → P.Ω → ℝ := fun n ω =>
      Real.sqrt ((split.foldB n).card : ℝ) * ∫ x, δ n ω x ∂S.P_X
    let R : ℕ → P.Ω → ℝ := fun n ω =>
      Real.sqrt ((split.foldB n).card : ℝ) *
          (plugInEstimator S sample split μ_hat n ω - S.θ₀) -
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n, ψ_plugin S (sample.Z i ω)
    have hG : IsLittleOp G (fun _ => (1 : ℝ)) P.μ := by
      let fZ : ℕ → P.Ω → γ × Bool × ℝ → ℝ :=
        fun n ω z => δ n ω (projX z)
      haveI : IsProbabilityMeasure S.P_Z := by
        unfold BackdoorEstimationSystem.P_Z
        exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
      have hf_meas : ∀ n, Measurable (Function.uncurry (fZ n)) := by
        intro n
        change Measurable (fun p : P.Ω × (γ × Bool × ℝ) =>
          (μ_hat n p.1 true p.2.1 - S.μ_val true p.2.1) -
            (μ_hat n p.1 false p.2.1 - S.μ_val false p.2.1))
        have hproj : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => (p.1, p.2.1)) := by
          fun_prop
        exact (((h_mu_meas n true).comp hproj).sub
          ((S.μ_meas true).comp measurable_snd.fst)).sub
          (((h_mu_meas n false).comp hproj).sub
            ((S.μ_meas false).comp measurable_snd.fst))
      have hf_foldA :
          ∀ n,
            Measurable[MeasurableSpace.comap
              (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
              (fun ω => fZ n ω) := by
        intro n
        change Measurable[MeasurableSpace.comap
              (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω (z : γ × Bool × ℝ) =>
            (μ_hat n ω true z.1 - S.μ_val true z.1) -
              (μ_hat n ω false z.1 - S.μ_val false z.1))
        fun_prop
      have hf_uncurry_foldA :
          ∀ n,
            Measurable[(MeasurableSpace.comap
                (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
              (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
              (Function.uncurry (fZ n)) := by
        intro n
        change Measurable[(MeasurableSpace.comap
              (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
            (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
          (fun (p : P.Ω × (γ × Bool × ℝ)) =>
            (μ_hat n p.1 true p.2.1 - S.μ_val true p.2.1) -
              (μ_hat n p.1 false p.2.1 - S.μ_val false p.2.1))
        let mA : MeasurableSpace P.Ω :=
          MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance
        have hx :
            @Measurable (P.Ω × (γ × Bool × ℝ)) γ
              (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
              inferInstance
              (fun p => p.2.1) := measurable_snd.fst
        have hproj :
            @Measurable (P.Ω × (γ × Bool × ℝ)) (P.Ω × γ)
              (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
              (mA.prod (inferInstance : MeasurableSpace γ))
              (fun p => (p.1, p.2.1)) :=
          Measurable.prodMk measurable_fst hx
        simpa using (((h_mu_uncurry_foldA n true).comp hproj).sub
          ((S.μ_meas true).comp hx)).sub
          (((h_mu_uncurry_foldA n false).comp hproj).sub
            ((S.μ_meas false).comp hx))
      have hf_memLp : ∀ n ω, MemLp (fZ n ω) 2 S.P_Z := by
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
        intro n ω
        have hδ_memLp : MemLp (δ n ω) 2 S.P_X := by
          simpa [δ] using
            ((h_mu_memLp n ω true).sub (hμ_val_memLp true)).sub
              ((h_mu_memLp n ω false).sub (hμ_val_memLp false))
        have hmap : MemLp (δ n ω) 2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
          simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using hδ_memLp
        have hδ_aestrong :
            AEStronglyMeasurable (δ n ω) (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) :=
          hmap.aestronglyMeasurable
        have hproj_ae :
            AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
          measurable_fst.aemeasurable
        simpa [fZ, projX] using
          (memLp_map_measure_iff hδ_aestrong hproj_ae).1 hmap
      have hf_rate_one :
          IsLittleOp (fun n ω => (eLpNorm (fZ n ω) 2 S.P_Z).toReal)
            (fun _ => (1 : ℝ)) P.μ := by
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
        have hnorm_bound : ∀ n ω,
            (eLpNorm (fZ n ω) 2 S.P_Z).toReal ≤
              2 * Real.sqrt
                (∑ a : Bool,
                  (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2) := by
          intro n ω
          let dμ : Bool → γ → ℝ := fun a x => μ_hat n ω a x - S.μ_val a x
          have hdμ_memLp : ∀ a, MemLp (dμ a) 2 S.P_X := fun a => by
            simpa [dμ] using (h_mu_memLp n ω a).sub (hμ_val_memLp a)
          have hδ_memLp : MemLp (δ n ω) 2 S.P_X := by
            simpa [δ, dμ] using (hdμ_memLp true).sub (hdμ_memLp false)
          have hδ_aestrong : AEStronglyMeasurable (δ n ω)
              (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
            have hmap : MemLp (δ n ω) 2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
              simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using hδ_memLp
            exact hmap.aestronglyMeasurable
          have hnorm_map : (eLpNorm (fZ n ω) 2 S.P_Z).toReal =
              (eLpNorm (δ n ω) 2 S.P_X).toReal := by
            rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S]
            rw [eLpNorm_map_measure hδ_aestrong measurable_fst.aemeasurable]
            rfl
          have hδ_le : (eLpNorm (δ n ω) 2 S.P_X).toReal ≤
              (eLpNorm (dμ true) 2 S.P_X).toReal +
                (eLpNorm (dμ false) 2 S.P_X).toReal := by
            rw [toReal_eLpNorm hδ_memLp.aestronglyMeasurable,
              toReal_eLpNorm (hdμ_memLp true).aestronglyMeasurable,
              toReal_eLpNorm (hdμ_memLp false).aestronglyMeasurable]
            simpa [δ, dμ] using
              lpNorm_sub_le (hdμ_memLp true) (by norm_num : (1 : ENNReal) ≤ 2)
          have htrue_le : (eLpNorm (dμ true) 2 S.P_X).toReal ≤ Real.sqrt
              (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) := by
            apply Real.le_sqrt_of_sq_le
            exact Finset.single_le_sum
              (by intro b hb; exact sq_nonneg ((eLpNorm (dμ b) 2 S.P_X).toReal))
              (Finset.mem_univ true)
          have hfalse_le : (eLpNorm (dμ false) 2 S.P_X).toReal ≤ Real.sqrt
              (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) := by
            apply Real.le_sqrt_of_sq_le
            exact Finset.single_le_sum
              (by intro b hb; exact sq_nonneg ((eLpNorm (dμ b) 2 S.P_X).toReal))
              (Finset.mem_univ false)
          rw [hnorm_map]
          calc
            (eLpNorm (δ n ω) 2 S.P_X).toReal ≤
                (eLpNorm (dμ true) 2 S.P_X).toReal +
                  (eLpNorm (dμ false) 2 S.P_X).toReal := hδ_le
            _ ≤ Real.sqrt (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) +
                Real.sqrt (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) :=
              add_le_add htrue_le hfalse_le
            _ = 2 * Real.sqrt (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) := by
              ring
            _ = 2 * Real.sqrt (∑ a : Bool,
                  (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2) := by
              simp [dμ]
        intro eps heps
        rw [ENNReal.tendsto_nhds_zero]
        intro η hη
        have hsmall := (ENNReal.tendsto_nhds_zero.mp
          (h_rate (eps / 2) (by linarith))) η hη
        have hrn_event : ∀ᶠ n : ℕ in atTop,
            (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
          filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
          have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
          have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
          have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
          have hn_one : 1 ≤ (n : ℝ) := by exact_mod_cast hn
          rw [Real.rpow_neg hn_nonneg, ← Real.sqrt_eq_rpow]
          exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hn_one)
        filter_upwards [hsmall, hrn_event] with n hn hle
        refine (measure_mono ?_).trans hn
        intro ω hω
        let Yn : ℝ := Real.sqrt
          (∑ a : Bool,
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2)
        have hnorm_nonneg : 0 ≤ (eLpNorm (fZ n ω) 2 S.P_Z).toReal :=
          ENNReal.toReal_nonneg
        have hY_nonneg : 0 ≤ Yn := by
          dsimp [Yn]
          exact Real.sqrt_nonneg _
        have hnorm_lt : eps < (eLpNorm (fZ n ω) 2 S.P_Z).toReal := by
          simpa [abs_of_nonneg hnorm_nonneg] using hω
        have hlt_two : eps < 2 * Yn := by
          exact lt_of_lt_of_le hnorm_lt (by simpa [Yn] using hnorm_bound n ω)
        have hhalf_lt : eps / 2 < Yn := by nlinarith
        have hrate_event : (eps / 2) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) < |Yn| := by
          rw [abs_of_nonneg hY_nonneg]
          nlinarith [mul_le_mul_of_nonneg_left hle (by linarith : 0 ≤ eps / 2)]
        simpa [Yn] using hrate_event
      have hGZ :
          IsLittleOp
            (fun n ω =>
              (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                ∑ i ∈ split.foldB n, (fZ n ω (sample.Z i ω) -
                  ∫ z, fZ n ω z ∂S.P_Z))
            (fun _ => (1 : ℝ)) P.μ :=
        foldB_centered_sum_isLittleOp_one sample split fZ
          hf_meas hf_uncurry_foldA hf_memLp hf_rate_one
      change IsLittleOp
        (fun n ω =>
          (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
            ∑ i ∈ split.foldB n, (δ n ω (projX (sample.Z i ω)) -
              ∫ x, δ n ω x ∂S.P_X))
        (fun _ => (1 : ℝ)) P.μ
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
      have hInt : ∀ n ω,
          ∫ z, fZ n ω z ∂S.P_Z = ∫ x, δ n ω x ∂S.P_X := by
        intro n ω
        have hδ_memLp : MemLp (δ n ω) 2 S.P_X := by
          simpa [δ] using
            ((h_mu_memLp n ω true).sub (hμ_val_memLp true)).sub
              ((h_mu_memLp n ω false).sub (hμ_val_memLp false))
        have hδ_aestrong :
            AEStronglyMeasurable (δ n ω) (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
          simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using
            hδ_memLp.aestronglyMeasurable
        rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S]
        rw [integral_map measurable_fst.aemeasurable hδ_aestrong]
        rfl
      have hproc :
          (fun n ω =>
            (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ∑ i ∈ split.foldB n, (fZ n ω (sample.Z i ω) -
                ∫ z, fZ n ω z ∂S.P_Z)) =
          (fun n ω =>
            (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ∑ i ∈ split.foldB n, (δ n ω (projX (sample.Z i ω)) -
                ∫ x, δ n ω x ∂S.P_X)) := by
        funext n ω
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [hInt n ω]
      rw [← hproc]
      exact hGZ
    have hB : IsLittleOp B (fun _ => (1 : ℝ)) P.μ := by
      let fZ : ℕ → P.Ω → γ × Bool × ℝ → ℝ :=
        fun n ω z => δ n ω (projX z)
      haveI : IsProbabilityMeasure S.P_Z := by
        unfold BackdoorEstimationSystem.P_Z
        exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
      have hf_meas : ∀ n, Measurable (Function.uncurry (fZ n)) := by
        intro n
        change Measurable (fun p : P.Ω × (γ × Bool × ℝ) =>
          (μ_hat n p.1 true p.2.1 - S.μ_val true p.2.1) -
            (μ_hat n p.1 false p.2.1 - S.μ_val false p.2.1))
        have hproj : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => (p.1, p.2.1)) := by
          fun_prop
        exact (((h_mu_meas n true).comp hproj).sub
          ((S.μ_meas true).comp measurable_snd.fst)).sub
          (((h_mu_meas n false).comp hproj).sub
            ((S.μ_meas false).comp measurable_snd.fst))
      have hf_memLp : ∀ n ω, MemLp (fZ n ω) 2 S.P_Z := by
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
        intro n ω
        have hδ_memLp : MemLp (δ n ω) 2 S.P_X := by
          simpa [δ] using
            ((h_mu_memLp n ω true).sub (hμ_val_memLp true)).sub
              ((h_mu_memLp n ω false).sub (hμ_val_memLp false))
        have hmap : MemLp (δ n ω) 2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
          simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using hδ_memLp
        have hδ_aestrong :
            AEStronglyMeasurable (δ n ω) (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) :=
          hmap.aestronglyMeasurable
        have hproj_ae :
            AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
          measurable_fst.aemeasurable
        simpa [fZ, projX] using
          (memLp_map_measure_iff hδ_aestrong hproj_ae).1 hmap
      have hf_rate :
          IsLittleOp (fun n ω => (eLpNorm (fZ n ω) 2 S.P_Z).toReal)
            (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
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
        have hnorm_bound : ∀ n ω,
            (eLpNorm (fZ n ω) 2 S.P_Z).toReal ≤
              2 * Real.sqrt
                (∑ a : Bool,
                  (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2) := by
          intro n ω
          let dμ : Bool → γ → ℝ := fun a x => μ_hat n ω a x - S.μ_val a x
          have hdμ_memLp : ∀ a, MemLp (dμ a) 2 S.P_X := fun a => by
            simpa [dμ] using (h_mu_memLp n ω a).sub (hμ_val_memLp a)
          have hδ_memLp : MemLp (δ n ω) 2 S.P_X := by
            simpa [δ, dμ] using (hdμ_memLp true).sub (hdμ_memLp false)
          have hδ_aestrong : AEStronglyMeasurable (δ n ω)
              (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
            have hmap : MemLp (δ n ω) 2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
              simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using hδ_memLp
            exact hmap.aestronglyMeasurable
          have hnorm_map : (eLpNorm (fZ n ω) 2 S.P_Z).toReal =
              (eLpNorm (δ n ω) 2 S.P_X).toReal := by
            rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S]
            rw [eLpNorm_map_measure hδ_aestrong measurable_fst.aemeasurable]
            rfl
          have hδ_le : (eLpNorm (δ n ω) 2 S.P_X).toReal ≤
              (eLpNorm (dμ true) 2 S.P_X).toReal +
                (eLpNorm (dμ false) 2 S.P_X).toReal := by
            rw [toReal_eLpNorm hδ_memLp.aestronglyMeasurable,
              toReal_eLpNorm (hdμ_memLp true).aestronglyMeasurable,
              toReal_eLpNorm (hdμ_memLp false).aestronglyMeasurable]
            simpa [δ, dμ] using
              lpNorm_sub_le (hdμ_memLp true) (by norm_num : (1 : ENNReal) ≤ 2)
          have htrue_le : (eLpNorm (dμ true) 2 S.P_X).toReal ≤ Real.sqrt
              (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) := by
            apply Real.le_sqrt_of_sq_le
            exact Finset.single_le_sum
              (by intro b hb; exact sq_nonneg ((eLpNorm (dμ b) 2 S.P_X).toReal))
              (Finset.mem_univ true)
          have hfalse_le : (eLpNorm (dμ false) 2 S.P_X).toReal ≤ Real.sqrt
              (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) := by
            apply Real.le_sqrt_of_sq_le
            exact Finset.single_le_sum
              (by intro b hb; exact sq_nonneg ((eLpNorm (dμ b) 2 S.P_X).toReal))
              (Finset.mem_univ false)
          rw [hnorm_map]
          calc
            (eLpNorm (δ n ω) 2 S.P_X).toReal ≤
                (eLpNorm (dμ true) 2 S.P_X).toReal +
                  (eLpNorm (dμ false) 2 S.P_X).toReal := hδ_le
            _ ≤ Real.sqrt (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) +
                Real.sqrt (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) :=
              add_le_add htrue_le hfalse_le
            _ = 2 * Real.sqrt (∑ a : Bool, (eLpNorm (dμ a) 2 S.P_X).toReal ^ 2) := by
              ring
            _ = 2 * Real.sqrt (∑ a : Bool,
                  (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2) := by
              simp [dμ]
        intro eps heps
        rw [ENNReal.tendsto_nhds_zero]
        intro η hη
        have hsmall := (ENNReal.tendsto_nhds_zero.mp
          (h_rate (eps / 2) (by linarith))) η hη
        filter_upwards [hsmall] with n hn
        refine (measure_mono ?_).trans hn
        intro ω hω
        let Yn : ℝ := Real.sqrt
          (∑ a : Bool,
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2)
        have hnorm_nonneg : 0 ≤ (eLpNorm (fZ n ω) 2 S.P_Z).toReal :=
          ENNReal.toReal_nonneg
        have hY_nonneg : 0 ≤ Yn := by
          dsimp [Yn]
          exact Real.sqrt_nonneg _
        have hnorm_lt :
            eps * ((n : ℝ) ^ (-(1 / 2 : ℝ))) <
              (eLpNorm (fZ n ω) 2 S.P_Z).toReal := by
          simpa [abs_of_nonneg hnorm_nonneg] using hω
        have hlt_two : eps * ((n : ℝ) ^ (-(1 / 2 : ℝ))) < 2 * Yn := by
          exact lt_of_lt_of_le hnorm_lt (by simpa [Yn] using hnorm_bound n ω)
        have hrate_event :
            (eps / 2) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) < |Yn| := by
          rw [abs_of_nonneg hY_nonneg]
          nlinarith
        simpa [Yn] using hrate_event
      have hBZ :
          IsLittleOp
            (fun n ω =>
              Real.sqrt ((split.foldB n).card : ℝ) * ∫ z, fZ n ω z ∂S.P_Z)
            (fun _ => (1 : ℝ)) P.μ :=
        sqrtFoldB_integral_isLittleOp_one sample split
          hc_pos h_split_rate fZ hf_memLp hf_rate
      change IsLittleOp
        (fun n ω =>
          Real.sqrt ((split.foldB n).card : ℝ) * ∫ x, δ n ω x ∂S.P_X)
        (fun _ => (1 : ℝ)) P.μ
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
      have hInt : ∀ n ω,
          ∫ z, fZ n ω z ∂S.P_Z = ∫ x, δ n ω x ∂S.P_X := by
        intro n ω
        have hδ_memLp : MemLp (δ n ω) 2 S.P_X := by
          simpa [δ] using
            ((h_mu_memLp n ω true).sub (hμ_val_memLp true)).sub
              ((h_mu_memLp n ω false).sub (hμ_val_memLp false))
        have hδ_aestrong :
            AEStronglyMeasurable (δ n ω) (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
          simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using
            hδ_memLp.aestronglyMeasurable
        rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S]
        rw [integral_map measurable_fst.aemeasurable hδ_aestrong]
        rfl
      have hproc :
          (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) * ∫ z, fZ n ω z ∂S.P_Z) =
          (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) * ∫ x, δ n ω x ∂S.P_X) := by
        funext n ω
        rw [hInt n ω]
      rw [← hproc]
      exact hBZ
    have hsum : IsLittleOp (fun n ω => G n ω + B n ω) (fun _ => (1 : ℝ)) P.μ := by
      intro ε hε
      rw [ENNReal.tendsto_nhds_zero]
      intro η hη
      by_cases hηtop : η = ⊤
      · filter_upwards with n
        simp [hηtop]
      have hηpos : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) hηtop
      let α : ℝ := η.toReal / 4
      have hαpos : 0 < α := by
        dsimp [α]
        linarith
      let A : ℕ → Set P.Ω := fun n => {ω | (ε / 2) * 1 < |G n ω|}
      let C : ℕ → Set P.Ω := fun n => {ω | (ε / 2) * 1 < |B n ω|}
      let D : ℕ → Set P.Ω := fun n => {ω | ε * 1 < |G n ω + B n ω|}
      have hGevent_le := (ENNReal.tendsto_nhds_zero.mp (hG (ε / 2) (by linarith)))
        (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
      have hBevent_le := (ENNReal.tendsto_nhds_zero.mp (hB (ε / 2) (by linarith)))
        (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
      have htwo_alpha_lt_eta : ENNReal.ofReal (2 * α) < η := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal]
        · dsimp [α]
          linarith
        · dsimp [α]
          linarith [le_of_lt hηpos]
        · exact hηtop
      filter_upwards [hGevent_le, hBevent_le] with n hGA hBC
      have hsubset : D n ⊆ A n ∪ C n := by
        intro ω hω
        by_contra hnot
        have hnotA : ¬ (ε / 2) * 1 < |G n ω| := by
          intro hx
          exact hnot (Or.inl hx)
        have hnotC : ¬ (ε / 2) * 1 < |B n ω| := by
          intro hy
          exact hnot (Or.inr hy)
        have hGle : |G n ω| ≤ (ε / 2) * 1 := le_of_not_gt hnotA
        have hBle : |B n ω| ≤ (ε / 2) * 1 := le_of_not_gt hnotC
        have hsum_le : |G n ω + B n ω| ≤ ε * 1 := by
          calc
            |G n ω + B n ω| ≤ |G n ω| + |B n ω| :=
              abs_add_le (G n ω) (B n ω)
            _ ≤ (ε / 2) * 1 + (ε / 2) * 1 := add_le_add hGle hBle
            _ = ε * 1 := by ring
        exact not_lt_of_ge hsum_le hω
      exact le_of_lt <| calc
        P.μ {ω | ε * 1 < |G n ω + B n ω|} = P.μ (D n) := by
          simp [D]
        _ ≤ P.μ (A n ∪ C n) := measure_mono hsubset
        _ ≤ P.μ (A n) + P.μ (C n) := MeasureTheory.measure_union_le (A n) (C n)
        _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hGA hBC
        _ = ENNReal.ofReal (2 * α) := by
          rw [← ENNReal.ofReal_add]
          · congr 1
            ring
          · linarith
          · linarith
        _ < η := htwo_alpha_lt_eta
    have hdecomp : R = fun n ω => G n ω + B n ω := by
      funext n ω
      unfold R G B δ ψ_plugin plugInEstimator
      by_cases hcard : (split.foldB n).card = 0
      · simp [hcard]
      · have hcard_pos : 0 < ((split.foldB n).card : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hcard
        have hsqrt_pos : 0 < Real.sqrt ((split.foldB n).card : ℝ) :=
          Real.sqrt_pos.mpr hcard_pos
        have hsqrt_sq :
            Real.sqrt ((split.foldB n).card : ℝ) *
                Real.sqrt ((split.foldB n).card : ℝ) =
              ((split.foldB n).card : ℝ) :=
          Real.mul_self_sqrt hcard_pos.le
        field_simp [hsqrt_pos.ne', hsqrt_sq]
        simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
          nsmul_eq_mul, sub_eq_add_neg]
        ring
    change IsLittleOp R (fun _ => (1 : ℝ)) P.μ
    rw [hdecomp]
    exact hsum

/-- **Asymptotic normality of the plug-in ATE** (`thm:est-plug-in-ate-al`,
"In particular ..." clause).  Given the same hypotheses as
`plugIn_isAsymLinear`, the rescaled estimator `√|B(n)| (θ̂ⁿ − θ₀)` converges
in distribution to `N(0, ∫ ψ_plugin² dP_Z)`.

Together with `|B(n)|/n → c ∈ (0,1)`, Slutsky scaling gives the
`√n`-rate form `√n (θ̂ⁿ − θ₀) ⇒ N(0, σ²/c)` (variance inflated by the
sample-splitting cost `1/c`).  That last step is left to the caller. -/
theorem plugIn_tendstoNormal
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_mu_memLp :
      ∀ n ω a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_rate :
      IsLittleOp
        (fun n ω =>
          Real.sqrt
            (∑ a : Bool,
              (eLpNorm
                (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal ^ 2))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (plugInEstimator S sample split μ_hat) S.θ₀ split.foldB n) P.μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum sample (ψ_plugin S) split.foldB n) P.μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (plugInEstimator S sample split μ_hat) S.θ₀ split.foldB)
      (gaussianMeasure 0 (∫ x, (ψ_plugin S x) ^ 2 ∂S.P_Z))
      P.μ
      hθn_meas := by
  haveI : IsProbabilityMeasure P.μ := inferInstance
  have hAL :=
    plugIn_isAsymLinear S hA h_yd2 sample split
      hc_pos hc_lt h_split_rate μ_hat h_mu_meas h_mu_memLp h_mu_foldA
      h_mu_uncurry_foldA h_rate
  have hψ_meas : Measurable (ψ_plugin S) := by
    unfold ψ_plugin
    exact (((S.μ_meas true).comp measurable_fst).sub
      ((S.μ_meas false).comp measurable_fst)).sub measurable_const
  exact hAL.tendsto_normal_foldB split hψ_meas hθn_meas hSum_meas

end ATE
end Estimation
end Causalean
