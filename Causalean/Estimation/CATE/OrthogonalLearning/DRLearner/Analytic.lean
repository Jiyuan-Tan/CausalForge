/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Analytic discharge of the DR-Learner orthogonal-learning orthogonality witness

The headline file `Causalean.Estimation.CATE.OrthogonalLearning.DRLearner` proves
`drNeymanOrthog_witness` modulo three analytic hypotheses:

1. `M : HasMixedDirDeriv (drLearningSystem ...)` — a closed-form mixed
   directional-derivative bundle for the DR-learner squared loss.
2. `hBridge : MixedScoreDCTBridge ... M` — a dominated-convergence swap
   that interchanges the limit of the score difference quotient with the
   integral.
3. `hScoreFlat` — the score map `g ↦ ∫ z, (M.Dθ_at g).dℓ_θ θ z ∂P_Z` has
   zero derivative at `g₀` along every nuisance direction.

This file supplies the concrete mixed-derivative bundle and discharges the
score-flatness condition for the concrete loss

    ℓ z θ η = (phi_eta z η - eval θ z.1)^2,

under strict overlap (`H_ε`) and a directional-derivative bundle for the
candidate-evaluation map `eval : Θ → γ → ℝ`.  The dominated-convergence bridge
remains an external analytic hypothesis, so `drNeymanOrthog` proves
orthogonality conditional on the supplied `hBridge`.

The construction follows the natural-language proof of
`prop:est-osl-dr-loss-orthogonal`
(`doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
lines 143–160) and uses the σ(X)-conditional bias identity
`phi_eta_minus_phi₀_cond_exp` from `Estimation/CATE/ConditionalBias.lean`
together with the DR-corollary lemmas `condBias_zero_of_outcome_match`
and `condBias_zero_of_propensity_match`.
-/

import Causalean.Estimation.CATE.OrthogonalLearning.DRLearner
import Causalean.Estimation.CATE.Core.ConditionalBias
import Causalean.Estimation.ATE.Score.MeanZero

/-!
Packages analytic derivative data for the DR-Learner orthogonal-learning
system. It defines the `EvalDirDeriv` and `NuisanceDirDeriv` bundles, builds the
closed-form mixed derivative `drMixedDirDeriv`, proves the bounded-direction
score-zero lemma `dr_scoreZero_of_bounded`, derives score flatness in
`dr_scoreFlat`, and combines these ingredients in `drNeymanOrthog`.
-/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.CATE

/-! ## Directional-derivative bundle for the candidate-evaluation map -/

/-- Pointwise directional-derivative bundle for the candidate evaluation
map `eval : Θ → γ → ℝ` along the segment `θ₀ → θ`.

The orthogonal statistical-learning note treats `Θ` as a class of CATE
*functions*, in which case the directional derivative of `eval θ x = θ x` along
`ν_θ = θ - θ₀` is simply `ν_θ x`.  We carry the derivative as a separate datum
so that downstream callers can plug in either the linear evaluation map or a
parametric embedding.

* `dEval θ x` — the directional-derivative *value* at `θ₀` in direction
  `θ - θ₀`, evaluated at `x : γ`.
* `pointwise` — the difference quotient of `eval` at `θ₀` along the
  segment to `θ` converges to `dEval θ x` as the perturbation parameter
  `t → 0`.
* `meas` — measurability in `x`.
* `bound` — a uniform `L∞` bound on `dEval θ` for each `θ ∈ Θ_set`,
  required by the dominated-convergence swap. -/
structure EvalDirDeriv {Θ : Type*} [NormedAddCommGroup Θ]
    [InnerProductSpace ℝ Θ] {γ : Type*} [MeasurableSpace γ]
    (Θ_set : Set Θ) (θ₀ : Θ) (eval : Θ → γ → ℝ) where
  dEval : Θ → γ → ℝ
  pointwise : ∀ θ ∈ Θ_set, ∀ x : γ,
    Tendsto (fun t : ℝ => (eval (θ₀ + t • (θ - θ₀)) x - eval θ₀ x) / t)
      (𝓝[≠] 0) (𝓝 (dEval θ x))
  meas : ∀ θ, Measurable (dEval θ)
  bound : ∀ θ ∈ Θ_set, ∃ M_dEval : ℝ, ∀ x : γ, |dEval θ x| ≤ M_dEval

/-- A nuisance derivative bundle records the pointwise directional derivative of
the doubly robust pseudo-outcome in each nuisance direction, together with
measurability of the derivative.

`phi_eta` is *not* linear in `η` (it depends reciprocally on `η.e_fn`), so
the value-difference `phi_eta z η - phi_eta z η₀` is *not* the directional
derivative.  We therefore carry a separate hypothesis bundle supplying the
pointwise dir-derivative of `phi_eta` at `g₀` in the nuisance direction
`ν_g = η - g₀`.  Under strict overlap (`H_ε`), this derivative exists and
admits the closed form

    D_g phi_eta(z, g₀)[ν_g]
      =  (ν_g.μ_fn true X − ν_g.μ_fn false X)
       + indA(z) · ( −ν_g.e_fn(X) / g₀.e_fn(X)² · (Y − g₀.μ_fn true X)
                       − 1 / g₀.e_fn(X) · ν_g.μ_fn true X )
       − (1 − indA(z)) · ( ν_g.e_fn(X) / (1 − g₀.e_fn(X))² · (Y − g₀.μ_fn false X)
                              − 1 / (1 − g₀.e_fn(X)) · ν_g.μ_fn false X )

but downstream we only consume the *bundled* witness, not the closed
form. -/
structure NuisanceDirDeriv {γ : Type*} [MeasurableSpace γ]
    (g₀ : NuisanceVec γ) where
  /-- The dir-derivative value `D_g phi_eta(z, g₀)[η − g₀]`. -/
  dPhi : NuisanceVec γ → (γ × Bool × ℝ) → ℝ
  pointwise : ∀ η : NuisanceVec γ, ∀ z : γ × Bool × ℝ,
    Tendsto (fun t : ℝ => (phi_eta z (g₀ + t • (η - g₀)) - phi_eta z g₀) / t)
      (𝓝[≠] 0) (𝓝 (dPhi η z))
  meas : ∀ η, Measurable (dPhi η)

/-! ## Closed-form mixed directional derivative for the DR-Learner loss -/

/-- The closed-form `HasMixedDirDeriv` bundle for the DR-Learner orthogonal-learning
system.

Computing by hand on `ℓ z θ g = (phi_eta z g - eval θ z.1)^2`:

* `D_θ ℓ(θ₀, g)[ν_θ] (z) = -2 · (phi_eta z g - eval θ₀ z.1) · dEval θ z.1`,
  using `eval θ₀ z.1 = S.τ_val z.1` from the truth witness `eval_θ₀`.
* The mixed derivative differentiates the above in `g` at `g₀`:
  `D_g D_θ ℓ(θ₀, g₀)[ν_θ, ν_g] (z)
       = -2 · (D_g phi_eta z · ν_g) · dEval θ z.1`.

We expose both the family `Dθ_at η` and the closed-form `dℓ_θg` field
expressed in terms of the supplied `NuisanceDirDeriv` bundle `ND`. -/
noncomputable def drMixedDirDeriv
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (_hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (_hε_pos : 0 < ε)
    (_h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (D : EvalDirDeriv Θ_set θ₀ eval)
    (ND : NuisanceDirDeriv S.toBackdoorEstimationSystem.η₀) :
    HasMixedDirDeriv
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes) where
  Dθ_at := fun η =>
    { dℓ_θ := fun θ z =>
        -2 * (phi_eta z η - eval θ₀ z.1) * D.dEval θ z.1
      pointwise_tendsto := by
        intro θ hθ z
        have hq := D.pointwise θ hθ z.1
        have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        have hdiff :
            Tendsto
              (fun t : ℝ => eval (θ₀ + t • (θ - θ₀)) z.1 - eval θ₀ z.1)
              (𝓝[≠] 0) (𝓝 0) := by
          have hmul := ht.mul hq
          have hmul' :
              Tendsto
                (fun t : ℝ =>
                  t * ((eval (θ₀ + t • (θ - θ₀)) z.1 - eval θ₀ z.1) / t))
                (𝓝[≠] 0) (𝓝 0) := by
            simpa using hmul
          refine hmul'.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t htne
          have htne' : t ≠ 0 := by simpa using htne
          field_simp [htne']
        have heval :
            Tendsto (fun t : ℝ => eval (θ₀ + t • (θ - θ₀)) z.1)
              (𝓝[≠] 0) (𝓝 (eval θ₀ z.1)) := by
          have h := hdiff.add (tendsto_const_nhds (x := eval θ₀ z.1))
          simpa [sub_add_cancel] using h
        have hsum :
            Tendsto
              (fun t : ℝ =>
                (phi_eta z η - eval (θ₀ + t • (θ - θ₀)) z.1) +
                  (phi_eta z η - eval θ₀ z.1))
              (𝓝[≠] 0) (𝓝 (2 * (phi_eta z η - eval θ₀ z.1))) := by
          simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            ((tendsto_const_nhds (x := phi_eta z η)).sub heval).add
              (tendsto_const_nhds (x := phi_eta z η - eval θ₀ z.1))
        have hfirst :
            Tendsto
              (fun t : ℝ =>
                -((eval (θ₀ + t • (θ - θ₀)) z.1 - eval θ₀ z.1) / t))
              (𝓝[≠] 0) (𝓝 (-D.dEval θ z.1)) :=
          hq.neg
        have hprod :
            Tendsto
              (fun t : ℝ =>
                -((eval (θ₀ + t • (θ - θ₀)) z.1 - eval θ₀ z.1) / t) *
                  ((phi_eta z η - eval (θ₀ + t • (θ - θ₀)) z.1) +
                    (phi_eta z η - eval θ₀ z.1)))
              (𝓝[≠] 0)
              (𝓝 (-2 * (phi_eta z η - eval θ₀ z.1) * D.dEval θ z.1)) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hfirst.mul hsum
        refine hprod.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t htne
        have htne' : t ≠ 0 := by simpa using htne
        simp [drLearningSystem, pow_two]
        field_simp [htne']
        ring
      dℓ_θ_meas := by
        intro θ
        have hphi : Measurable (fun z : γ × Bool × ℝ => phi_eta z η) :=
          measurable_phi_eta η
        have heval : Measurable (fun z : γ × Bool × ℝ => eval θ₀ z.1) :=
          (eval_meas θ₀).comp measurable_fst
        have hdE : Measurable (fun z : γ × Bool × ℝ => D.dEval θ z.1) :=
          (D.meas θ).comp measurable_fst
        exact (((measurable_const.mul (hphi.sub heval)).mul hdE)) }
  dℓ_θg := fun θ η z =>
    -2 * ND.dPhi η z * D.dEval θ z.1
  pointwise_tendsto := by
    intro θ hθ η hη z
    have hphi := ND.pointwise η z
    have hlim :
        Tendsto
          (fun t : ℝ =>
            -2 *
              ((phi_eta z (S.toBackdoorEstimationSystem.η₀ +
                    t • (η - S.toBackdoorEstimationSystem.η₀)) -
                  phi_eta z S.toBackdoorEstimationSystem.η₀) / t) *
              D.dEval θ z.1)
          (𝓝[≠] 0) (𝓝 (-2 * ND.dPhi η z * D.dEval θ z.1)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (((tendsto_const_nhds (x := (-2 : ℝ))).mul hphi).mul
          (tendsto_const_nhds (x := D.dEval θ z.1)))
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t htne
    have htne' : t ≠ 0 := by simpa using htne
    simp [drLearningSystem]
    field_simp [htne']
    ring
  dℓ_θg_meas := by
    intro θ η
    have hdPhi : Measurable (fun z : γ × Bool × ℝ => ND.dPhi η z) :=
      ND.meas η
    have hdE : Measurable (fun z : γ × Bool × ℝ => D.dEval θ z.1) :=
      (D.meas θ).comp measurable_fst
    exact (measurable_const.mul hdPhi).mul hdE

/-! ## Discharge of the score-zero hypothesis for bounded perturbations -/

private lemma integrable_phi_eta_dir_deriv_factualZ
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (v : NuisanceVec γ)
    (h_v_μ_bdd : ∃ Cμ : ℝ, ∀ b : Bool, ∀ x : γ, |v.μ_fn b x| ≤ Cμ)
    (h_v_e_bdd : ∃ Ce : ℝ, ∀ x : γ, |v.e_fn x| ≤ Ce) :
    Integrable
      (fun ω => phi_eta_dir_deriv S.toBackdoorEstimationSystem.η₀ v
        (S.toBackdoorEstimationSystem.factualZ ω)) P.μ := by
  let X : P.Ω → γ := S.toPOBackdoorSystem.factualX
  let Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY
  let indT : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator true
  let indF : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator false
  let T1 : P.Ω → ℝ := fun ω => v.μ_fn true (X ω) - v.μ_fn false (X ω)
  let T2 : P.Ω → ℝ := fun ω =>
    (-v.e_fn (X ω) * (1 / S.e_val (X ω)) * (1 / S.e_val (X ω))) *
      (indT ω * (Y ω - S.μ_val true (X ω)))
  let T3 : P.Ω → ℝ := fun ω =>
    (-1 / S.e_val (X ω) * v.μ_fn true (X ω)) * indT ω
  let T4 : P.Ω → ℝ := fun ω =>
    (-v.e_fn (X ω) * (1 / (1 - S.e_val (X ω))) *
        (1 / (1 - S.e_val (X ω)))) *
      (indF ω * (Y ω - S.μ_val false (X ω)))
  let T5 : P.Ω → ℝ := fun ω =>
    (1 / (1 - S.e_val (X ω)) * v.μ_fn false (X ω)) * indF ω
  have hindA_true : ∀ ω, BackdoorEstimationSystem.indA
      (S.toBackdoorEstimationSystem.factualZ ω) = indT ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : indT ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
    · have hInd : indT ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
  have hφ_eq :
      (fun ω => phi_eta_dir_deriv S.toBackdoorEstimationSystem.η₀ v
          (S.toBackdoorEstimationSystem.factualZ ω))
        = (fun ω => T1 ω + T2 ω + T3 ω + T4 ω + T5 ω) := by
    funext ω
    have hind_true_z :
        BackdoorEstimationSystem.indA
          (S.toPOBackdoorSystem.factualX ω,
            S.toPOBackdoorSystem.factualD ω,
            S.toPOBackdoorSystem.factualY ω)
          = indT ω := by
      simpa [BackdoorEstimationSystem.factualZ] using hindA_true ω
    have hind_not : 1 - indT ω = indF ω := by
      have hsum : indT ω + indF ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
      linarith
    simp only [T1, T2, T3, T4, T5, X, Y, indT, indF, phi_eta_dir_deriv,
      BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.projX,
      BackdoorEstimationSystem.projY, BackdoorEstimationSystem.η₀,
      hind_true_z, hind_not]
    have hneT : S.e_val (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le hε_pos
        (h_overlap_η₀ (S.toPOBackdoorSystem.factualX ω)).1)
    have hden : ε ≤ 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) := by
      have hu : S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
        simpa [BackdoorEstimationSystem.η₀] using
          (h_overlap_η₀ (S.toPOBackdoorSystem.factualX ω)).2
      linarith
    have hneF : 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le hε_pos hden)
    field_simp [hneT, hneF]
    ring
  have hμ_val_int : ∀ d : Bool, Integrable (fun ω => S.μ_val d (X ω)) P.μ := by
    intro d
    have hcate_int : Integrable (S.toPOBackdoorSystem.CATE d) P.μ := by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ_compat hA d)
  rcases h_v_μ_bdd with ⟨Cμ, hCμ⟩
  rcases h_v_e_bdd with ⟨Ce, hCe⟩
  have hvμ_int : ∀ d : Bool, Integrable (fun ω => v.μ_fn d (X ω)) P.μ := by
    intro d
    refine MeasureTheory.Integrable.of_bound
      (((v.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX).aestronglyMeasurable)
      |Cμ| (Filter.Eventually.of_forall ?_)
    intro ω
    simpa [X, Real.norm_eq_abs] using le_trans (hCμ d (X ω)) (le_abs_self Cμ)
  have hv_e_top : MemLp (fun ω => v.e_fn (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ |Ce| (Filter.Eventually.of_forall ?_)
    · exact ((v.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)).aestronglyMeasurable
    · intro ω
      simpa [X, Real.norm_eq_abs] using le_trans (hCe (X ω)) (le_abs_self Ce)
  have hvμ_top : ∀ d : Bool, MemLp (fun ω => v.μ_fn d (X ω)) ⊤ P.μ := by
    intro d
    refine MemLp.of_bound ?_ |Cμ| (Filter.Eventually.of_forall ?_)
    · exact (((v.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX)).aestronglyMeasurable
    · intro ω
      simpa [X, Real.norm_eq_abs] using le_trans (hCμ d (X ω)) (le_abs_self Cμ)
  have hT1_int : Integrable T1 P.μ := by
    simpa [T1] using (hvμ_int true).sub (hvμ_int false)
  have h₀e_lower : ∀ ω, ε ≤ S.e_val (X ω) := by
    intro ω
    exact (h_overlap_η₀ (X ω)).1
  have h₀e_upper : ∀ ω, S.e_val (X ω) ≤ 1 - ε := by
    intro ω
    exact (h_overlap_η₀ (X ω)).2
  have hw₀T_Linf : MemLp (fun ω => 1 / S.e_val (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < S.e_val (X ω) := lt_of_lt_of_le hε_pos (h₀e_lower ω)
        have hle : (S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 (h₀e_lower ω)
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hw₀F_Linf : MemLp (fun ω => 1 / (1 - S.e_val (X ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (measurable_const.sub
          (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hden : ε ≤ 1 - S.e_val (X ω) := by linarith [h₀e_upper ω]
        have hpos : 0 < 1 - S.e_val (X ω) := lt_of_lt_of_le hε_pos hden
        have hle : (1 - S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 hden
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hYind_int : ∀ d : Bool,
      Integrable (fun ω => Y ω * S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    fun d => S.toPOBackdoorSystem.dVar.integrable_mul_indicator d
      hA.integrable_factualY S.toPOBackdoorSystem.measurable_factualY
  have hμind_int : ∀ d : Bool,
      Integrable (fun ω => S.μ_val d (X ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ := by
    intro d
    exact S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (hμ_val_int d)
      ((S.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX)
  have hresμ_int : ∀ d : Bool,
      Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (Y ω - S.μ_val d (X ω))) P.μ := by
    intro d
    have hY' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * Y ω) P.μ := by
      simpa [Y, mul_comm] using hYind_int d
    have hμ' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω)) P.μ := by
      simpa [mul_comm] using hμind_int d
    refine (hY'.sub hμ').congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      change S.toPOBackdoorSystem.dVar.indicator d ω * Y ω -
          S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω) =
        S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - S.μ_val d (X ω))
      ring_nf)
  have hgET_top : MemLp
      (fun ω => -v.e_fn (X ω) * (1 / S.e_val (X ω)) * (1 / S.e_val (X ω))) ⊤ P.μ := by
    have htmp : MemLp (fun ω => -v.e_fn (X ω) * (1 / S.e_val (X ω))) ⊤ P.μ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀T_Linf hv_e_top.neg
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀T_Linf htmp
  have hgEF_top : MemLp
      (fun ω => -v.e_fn (X ω) * (1 / (1 - S.e_val (X ω))) *
        (1 / (1 - S.e_val (X ω)))) ⊤ P.μ := by
    have htmp : MemLp (fun ω => -v.e_fn (X ω) * (1 / (1 - S.e_val (X ω)))) ⊤ P.μ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀F_Linf hv_e_top.neg
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀F_Linf htmp
  have hgMT_top : MemLp (fun ω => -1 / S.e_val (X ω) * v.μ_fn true (X ω)) ⊤ P.μ := by
    simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀T_Linf.neg (hvμ_top true)
  have hgMF_top : MemLp (fun ω => 1 / (1 - S.e_val (X ω)) * v.μ_fn false (X ω)) ⊤ P.μ := by
    simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀F_Linf (hvμ_top false)
  have hT2_int : Integrable T2 P.μ := by
    have hL1 : MemLp T2 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgET_top (memLp_one_iff_integrable.2 (hresμ_int true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T2, X, Y, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hT4_int : Integrable T4 P.μ := by
    have hL1 : MemLp T4 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgEF_top (memLp_one_iff_integrable.2 (hresμ_int false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T4, X, Y, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have hT3_int : Integrable T3 P.μ := by
    have hL1 : MemLp T3 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgMT_top (memLp_one_iff_integrable.2
          (S.toPOBackdoorSystem.dVar.integrable_indicator true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T3, X, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hT5_int : Integrable T5 P.μ := by
    have hL1 : MemLp T5 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgMF_top (memLp_one_iff_integrable.2
          (S.toPOBackdoorSystem.dVar.integrable_indicator false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T5, X, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have h12345_int :
      Integrable (fun ω => T1 ω + T2 ω + T3 ω + T4 ω + T5 ω) P.μ :=
    (((hT1_int.add hT2_int).add hT3_int).add hT4_int).add hT5_int
  simpa [hφ_eq] using h12345_int

/-- **Discharge of `hScoreZero` for bounded nuisance directions.**

For any bounded perturbation `η : NuisanceVec γ` (i.e. with `η - η₀`
having uniformly bounded `μ_fn` and `e_fn`) and any admissible candidate
target `θ ∈ Θ_set`, the integrated score derivative

    ∫ z, ND.dPhi η z · D.dEval θ z.1 ∂P_Z

vanishes.  Combining this lemma at every `η ∈ Set.univ` (when the
caller can supply uniform bounds for each `η`) discharges the
`hScoreZero` hypothesis of `dr_scoreFlat` and `drNeymanOrthog`.

Proof structure:
1. Apply uniqueness of pointwise limits to identify
   `ND.dPhi η z = phi_eta_dir_deriv η₀ (η - η₀) z` for every `z`,
   using `ND.pointwise` and `phi_eta_dir_deriv_tendsto`.
2. Convert the `P_Z`-integral to a `P.μ`-integral via
   `MeasureTheory.integral_map` and `BackdoorEstimationSystem.P_Z`
   (= `P.μ.map factualZ`).
3. Apply the conditional-expectation tower
   (`MeasureTheory.integral_condExp`) and pull the σ(X)-measurable
   factor `D.dEval θ ∘ factualX` out via
   `condExp_mul_of_stronglyMeasurable_left`.
4. Apply `cond_exp_phi_eta_dir_deriv_at_truth_zero` to get that the
   inner conditional expectation is zero a.e., hence the integrand is
   zero a.e., hence the integral is zero. -/
lemma dr_scoreZero_of_bounded
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (θ₀ : Θ)
    (eval : Θ → γ → ℝ)
    (D : EvalDirDeriv Θ_set θ₀ eval)
    (ND : NuisanceDirDeriv S.toBackdoorEstimationSystem.η₀)
    (θ : Θ) (hθ : θ ∈ Θ_set) (η : NuisanceVec γ)
    (h_v_μ_bdd : ∃ Cμ : ℝ, ∀ b : Bool, ∀ x : γ,
      |(η - S.toBackdoorEstimationSystem.η₀).μ_fn b x| ≤ Cμ)
    (h_v_e_bdd : ∃ Ce : ℝ, ∀ x : γ,
      |(η - S.toBackdoorEstimationSystem.η₀).e_fn x| ≤ Ce) :
    ∫ z, ND.dPhi η z * D.dEval θ z.1
      ∂S.toBackdoorEstimationSystem.P_Z = 0 := by
  let v : NuisanceVec γ := η - S.toBackdoorEstimationSystem.η₀
  let fZ : γ × Bool × ℝ → ℝ :=
    fun z => phi_eta_dir_deriv S.toBackdoorEstimationSystem.η₀ v z
  let scoreZ : γ × Bool × ℝ → ℝ := fun z => fZ z * D.dEval θ z.1
  have hND_eq : ∀ z : γ × Bool × ℝ, ND.dPhi η z = fZ z := by
    intro z
    have hND := ND.pointwise η z
    have hclosed :
        Tendsto
          (fun t : ℝ =>
            (phi_eta z
                (S.toBackdoorEstimationSystem.η₀ + t •
                  (η - S.toBackdoorEstimationSystem.η₀)) -
              phi_eta z S.toBackdoorEstimationSystem.η₀) / t)
          (𝓝[≠] 0) (𝓝 (fZ z)) := by
      simpa [v, fZ] using
        phi_eta_dir_deriv_tendsto S.toBackdoorEstimationSystem.η₀ v
          hε_pos h_overlap_η₀ z
    exact tendsto_nhds_unique' (NormedField.nhdsNE_neBot (0 : ℝ)) hND hclosed
  have hscoreZ_meas : Measurable scoreZ := by
    have hf : Measurable fZ := by
      simpa [fZ, v] using
        measurable_phi_eta_dir_deriv S.toBackdoorEstimationSystem.η₀ v
    have hg : Measurable (fun z : γ × Bool × ℝ => D.dEval θ z.1) :=
      (D.meas θ).comp measurable_fst
    exact hf.mul hg
  obtain ⟨M_dEval, hD_bdd⟩ := D.bound θ hθ
  have hf_int : Integrable
      (fun ω => fZ (S.toBackdoorEstimationSystem.factualZ ω)) P.μ := by
    simpa [fZ, v] using
      integrable_phi_eta_dir_deriv_factualZ S hA hε_pos h_overlap_η₀ v
        h_v_μ_bdd h_v_e_bdd
  have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => D.dEval θ (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => D.dEval θ (S.toPOBackdoorSystem.factualX ω))
    exact ((D.meas θ).comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hg_meas : Measurable
      (fun ω => D.dEval θ (S.toPOBackdoorSystem.factualX ω)) :=
    (D.meas θ).comp S.toPOBackdoorSystem.measurable_factualX
  have hg_aesm : AEStronglyMeasurable
      (fun ω => D.dEval θ (S.toPOBackdoorSystem.factualX ω)) P.μ :=
    hg_meas.aestronglyMeasurable
  have hg_bdd : ∀ᵐ ω ∂P.μ,
      ‖D.dEval θ (S.toPOBackdoorSystem.factualX ω)‖ ≤ M_dEval :=
    Filter.Eventually.of_forall (fun ω => by
      simpa [Real.norm_eq_abs] using hD_bdd (S.toPOBackdoorSystem.factualX ω))
  have hscore_Ω_int' : Integrable
      (fun ω => fZ (S.toBackdoorEstimationSystem.factualZ ω) *
        D.dEval θ (S.toPOBackdoorSystem.factualX ω)) P.μ :=
    hf_int.mul_bdd hg_aesm hg_bdd
  have hscore_comp_int : Integrable (scoreZ ∘ S.toBackdoorEstimationSystem.factualZ) P.μ := by
    refine hscore_Ω_int'.congr (Filter.Eventually.of_forall ?_)
    intro ω
    simp [scoreZ, BackdoorEstimationSystem.factualZ]
  have hscore_int :
      Integrable scoreZ
        (Measure.map S.toBackdoorEstimationSystem.factualZ P.μ) :=
    (MeasureTheory.integrable_map_measure
      hscoreZ_meas.aestronglyMeasurable
      S.toBackdoorEstimationSystem.measurable_factualZ.aemeasurable).2
      hscore_comp_int
  have hmap_congr :
      (fun z : γ × Bool × ℝ => ND.dPhi η z * D.dEval θ z.1)
        =ᵐ[S.toBackdoorEstimationSystem.P_Z] scoreZ := by
    exact Filter.Eventually.of_forall (fun z => by simp [scoreZ, hND_eq z])
  calc
    ∫ z, ND.dPhi η z * D.dEval θ z.1
        ∂S.toBackdoorEstimationSystem.P_Z
        = ∫ z, scoreZ z ∂S.toBackdoorEstimationSystem.P_Z :=
          MeasureTheory.integral_congr_ae hmap_congr
    _ = 0 := by
      rw [BackdoorEstimationSystem.P_Z]
      have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
        (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm
        hscore_Ω_int' hf_int
      have hinner :
          P.μ[fun ω => fZ (S.toBackdoorEstimationSystem.factualZ ω) |
              S.toPOBackdoorSystem.sigmaX]
            =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
        simpa [fZ, v] using
          cond_exp_phi_eta_dir_deriv_at_truth_zero S hA hε_pos h_overlap_η₀ v
            h_v_μ_bdd h_v_e_bdd
      have hcond_zero :
          P.μ[fun ω => fZ (S.toBackdoorEstimationSystem.factualZ ω) *
              D.dEval θ (S.toPOBackdoorSystem.factualX ω) |
              S.toPOBackdoorSystem.sigmaX]
            =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
        refine hpull.trans ?_
        filter_upwards [hinner] with ω hω
        rw [Pi.mul_apply, hω, zero_mul]
      calc
        ∫ z, scoreZ z
            ∂Measure.map S.toBackdoorEstimationSystem.factualZ P.μ
            = ∫ ω, scoreZ (S.toBackdoorEstimationSystem.factualZ ω) ∂P.μ := by
              rw [MeasureTheory.integral_map
                S.toBackdoorEstimationSystem.measurable_factualZ.aemeasurable
                hscoreZ_meas.aestronglyMeasurable]
        _ = ∫ ω, fZ (S.toBackdoorEstimationSystem.factualZ ω) *
              D.dEval θ (S.toPOBackdoorSystem.factualX ω) ∂P.μ := by
              refine MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall ?_)
              intro ω
              simp [scoreZ, BackdoorEstimationSystem.factualZ]
        _ = ∫ ω, P.μ[fun ω =>
              fZ (S.toBackdoorEstimationSystem.factualZ ω) *
                D.dEval θ (S.toPOBackdoorSystem.factualX ω) |
              S.toPOBackdoorSystem.sigmaX] ω ∂P.μ := by
              rw [MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le]
        _ = ∫ _, (0 : ℝ) ∂P.μ :=
              MeasureTheory.integral_congr_ae hcond_zero
        _ = 0 := MeasureTheory.integral_zero _ _

/-! ## Score flatness via the σ(X)-conditional bias identity -/

/-- The score-flatness hypothesis for `drMixedDirDeriv`.

For every admissible target `θ ∈ Θ_set` and nuisance direction
`η : NuisanceVec γ`, the integrated score

    g ↦ ∫ z, (M.Dθ_at g).dℓ_θ θ z ∂P_Z
       = -2 · ∫ z, (phi_eta z g - eval θ₀ z.1) · D.dEval θ z.1 ∂P_Z

has zero derivative at `g₀` along the ray `g₀ + t • (η - g₀)`.

Proof sketch: by `phi_eta_minus_phi₀_cond_exp`, the σ(X)-conditional of
`phi_eta z g - phi_eta z g₀ = phi_eta z g - phi₀ S z` equals
`condBias g g₀ ∘ factualX`.  Pulling `D.dEval θ ∘ factualX` out of the
conditional expectation as σ(X)-measurable, the integrated score
difference reduces to

    -2 · ∫ x, condBias (g₀ + t • (η - g₀)) g₀ x · D.dEval θ x ∂P_X.

Since `condBias` is bilinear in `(η.μ - η₀.μ, η.e - η₀.e)`, this is
quadratic in `t`; dividing by `t` and letting `t → 0` gives zero, by
`condBias_zero_of_outcome_match` and `condBias_zero_of_propensity_match`
applied at `t = 0`. -/
theorem dr_scoreFlat
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (D : EvalDirDeriv Θ_set θ₀ eval)
    (ND : NuisanceDirDeriv S.toBackdoorEstimationSystem.η₀)
    -- hBridge: dominated-convergence bridge for the integrated mixed score quotient.
    (hBridge :
      MixedScoreDCTBridge
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
        (drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
          θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND)) :
    ∀ θ ∈ Θ_set,
      ∀ η ∈ BoundedNuisanceDirs S.toBackdoorEstimationSystem.η₀,
        Tendsto (fun t : ℝ =>
          ((∫ z, ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex
                θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at
              (S.toBackdoorEstimationSystem.η₀ + t • (η -
                  S.toBackdoorEstimationSystem.η₀))).dℓ_θ θ z
              ∂S.toBackdoorEstimationSystem.P_Z)
            - (∫ z, ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex
                θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at
                  S.toBackdoorEstimationSystem.η₀).dℓ_θ θ z
                ∂S.toBackdoorEstimationSystem.P_Z)) / t)
          (𝓝[≠] 0) (𝓝 0) := by
  intro θ hθ η hη
  have hlim := hBridge θ hθ η hη
  obtain ⟨h_v_μ_bdd, h_v_e_bdd⟩ := hη
  have hScoreZero :
    ∫ z, ND.dPhi η z * D.dEval θ z.1
        ∂S.toBackdoorEstimationSystem.P_Z = 0 :=
    dr_scoreZero_of_bounded S hA hε_pos h_overlap_η₀ Θ Θ_set θ₀ eval D ND
      θ hθ η h_v_μ_bdd h_v_e_bdd
  have hzero :
      ∫ z, (drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).dℓ_θg θ η z
        ∂S.toBackdoorEstimationSystem.P_Z = 0 := by
    calc
      ∫ z, (drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
          θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).dℓ_θg θ η z
          ∂S.toBackdoorEstimationSystem.P_Z
          = -2 * ∫ z, ND.dPhi η z * D.dEval θ z.1
              ∂S.toBackdoorEstimationSystem.P_Z := by
            simp only [drMixedDirDeriv, neg_mul]
            rw [show
              (fun z : γ × Bool × ℝ => -(2 * ND.dPhi η z * D.dEval θ z.1)) =
                (fun z : γ × Bool × ℝ => (-2) * (ND.dPhi η z * D.dEval θ z.1))
                by
                  funext z
                  ring]
            rw [MeasureTheory.integral_const_mul]
            ring
      _ = 0 := by simp [hScoreZero]
  simpa [hzero] using hlim

/-! ## Orthogonality of the DR-Learner squared loss under a DCT bridge -/

/-- **DR-Learner loss orthogonality under a DCT bridge**
(`prop:est-osl-dr-loss-orthogonal`).

Combines the closed-form mixed directional derivative `drMixedDirDeriv`,
the DCT-swap hypothesis `hBridge`, and the score-flatness lemma
`dr_scoreFlat` into a Neyman-orthogonality witness for the DR-Learner
squared loss on bounded nuisance directions.

The score-zero obligation is now discharged inside `dr_scoreFlat` via
`dr_scoreZero_of_bounded`, using the fact that the orthogonal-learning system's nuisance
slice `G_set := BoundedNuisanceDirs η₀` already encodes the uniform
boundedness of the perturbation directions.  The only remaining
analytic hypothesis is the DCT swap `hBridge`. -/
theorem drNeymanOrthog
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (D : EvalDirDeriv Θ_set θ₀ eval)
    (ND : NuisanceDirDeriv S.toBackdoorEstimationSystem.η₀)
    (hBridge :
      MixedScoreDCTBridge
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
        (drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
          θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND)) :
    NeymanOrthogLoss
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      (drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND) :=
  (neymanOrthog_iff_score_deriv_zero _ _ hBridge).mpr
    (dr_scoreFlat S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
      eval eval_meas eval_θ₀ θ₀_minimizes D ND hBridge)

end OrthogonalLearning
end Estimation
end Causalean
