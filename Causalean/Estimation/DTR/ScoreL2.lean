/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sequential DR (DTR, n = 2) score L²(P_Z) continuity

Stagewise version of `Estimation/ATE/AIPWScoreL2.lean`.  Used by
`DTRInstance.lean` for the `R₂` empirical-process step: conditioning on
the fold-A σ-algebra, the centered fold-B sum of
`m_seqDR(η̂(n), Z_i, θ₀) − m_seqDR(η₀, Z_i, θ₀)` has conditional second
moment bounded by

    ‖m_seqDR(η̂(n), ·, θ₀) − m_seqDR(η₀, ·, θ₀)‖²_{L²(P_Z)},

so we need that this L²-norm is `o_p(1)` under `μ`.

Pointwise the sequential DR moment is Lipschitz in `η` on the
overlap-bounded set `H_ε`.  The Lipschitz constant `K_seqDR ε` tracks the
quadratic blow-up of the stage-0 inverse weight `1/ê₀` and the stage-1
double inverse weight `1/(ê₀ · ê₁)` on `H_ε`.  Squaring, applying
`(a+b+c+d)² ≤ 4·(a²+b²+c²+d²)`, and integrating against `P_Z` gives a
quantitative bound on `‖Δ_seqDR‖²_{L²(P_Z)}` in terms of stagewise
L²(P_H_k) norms of `Δμ_k` and `Δe_k`, plus the cross terms
`(Y − μ_val)² ∈ L¹(P_Z)`-controlled truncation pieces.

The headline corollary `seqDR_score_diff_isLittleOp_one` packages the L²
continuity with the four individual stagewise rates into the `o_p(1)`
form consumed by the `R₂` argument in `DTRInstance.lean`.

The file packages the stagewise pointwise bounds, their L² consequences, and
the headline stochastic-order continuity statement used by the DTR DML layer.
-/

import Causalean.Estimation.DTR.ScoreL2.Helpers

/-!
# Sequential DR score L² continuity for two-stage regimes

This module proves the L² continuity statement for the two-stage sequential
doubly robust DTR score. The headline theorem
`DTREstimationSystem.seqDR_score_diff_isLittleOp_one` says that

`‖m_seqDR(η_hat n, ·, θ₀) - m_seqDR(η₀, ·, θ₀)‖_{L²(P_Z)} = o_p(1)`

whenever the four stagewise nuisance errors for `μ₀`, `μ₁`, `e₀`, and `e₁`
converge in their natural history-space L² norms and the estimated propensities
remain in the overlap-bounded set `H_ε`.

The proof combines the pointwise Lipschitz bound from
`ScoreL2.Helpers`, L² norm transport from the history marginals to the full
observed data law `P_Z`, and a truncation lemma for residuals multiplied by
propensity-estimation errors. This is the score-difference input used by the
DTR double-machine-learning layer.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Headline L²(P_Z) `o_p(1)` -/

/-- **Sequential DR score L²(P_Z) continuity** — the L²(P_Z) norm of
`m_seqDR(η̂(n), ·, θ₀) − m_seqDR(η₀, ·, θ₀)` is `o_p(1)` under `μ`.

Stagewise version of
`BackdoorEstimationSystem.aipw_score_diff_isLittleOp_one`
(`Estimation/ATE/AIPWScoreL2.lean:1016`).

The proof:

* pointwise Lipschitz bound `|m_seqDR(η, z, θ₀) − m_seqDR(η₀, z, θ₀)|
  ≤ K_seqDR ε · (|Δμ₀(s₀)| + |Δμ₁(h₁)| + |Δe₀(s₀)|·R₀ + |Δe₁(h₁)|·R₁)`
  where `R₀, R₁` are residuals quadratically integrable under `P_Z`;
* square-integrate, apply `(Σ aᵢ)² ≤ 4 · Σ aᵢ²`, use the truncation
  argument from the ATE proof for the residual×Δe pieces;
* combine with the four `IsLittleOp _ 1` rate hypotheses.
-/
theorem seqDR_score_diff_isLittleOp_one
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ dbar : Fin 2 → δ,
      Integrable (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ DTREstimationSystem.H_ε ε)
    (h_mu0_memLp : ∀ n ω,
      MemLp (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀)
    (h_mu1_memLp : ∀ n ω,
      MemLp (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁)
    (h_e0_memLp : ∀ n ω,
      MemLp (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀)
    (h_e1_memLp : ∀ n ω,
      MemLp (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁)
    (h_mu0_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_mu1_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_e0_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_e1_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal)
      (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z =>
            S.seqDRMomentFunctional (η_hat n ω) z S.θ₀ -
              S.seqDRMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  have _hA_used := hA
  rcases h_overlap with ⟨hε_pos, hε_half, hprop⟩
  have h_overlap' : S.StrictOverlap ε := ⟨hε_pos, hε_half, hprop⟩
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold DTREstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  let R0 : γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun z =>
    |S.μ₁_val (histH₁ z) - S.μ₀_val (projS₀ z)|
      + |projY z - S.μ₁_val (histH₁ z)|
  let R1 : γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun z =>
    |projY z - S.μ₁_val (histH₁ z)|
  let dμ0Z : ℕ → P.Ω → γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun n ω z =>
    (η_hat n ω).μ₀_fn (projS₀ z) - S.μ₀_val (projS₀ z)
  let dμ1Z : ℕ → P.Ω → γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun n ω z =>
    (η_hat n ω).μ₁_fn (histH₁ z) - S.μ₁_val (histH₁ z)
  let de0Z : ℕ → P.Ω → γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun n ω z =>
    (η_hat n ω).e₀_fn (projS₀ z) - S.e₀_val (projS₀ z)
  let de1Z : ℕ → P.Ω → γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun n ω z =>
    (η_hat n ω).e₁_fn (histH₁ z) - S.e₁_val (histH₁ z)
  let cross0 : ℕ → P.Ω → γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun n ω z =>
    R0 z * |de0Z n ω z|
  let cross1 : ℕ → P.Ω → γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun n ω z =>
    R1 z * |de1Z n ω z|
  let score : ℕ → P.Ω → γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun n ω z =>
    S.seqDRMomentFunctional (η_hat n ω) z S.θ₀ -
      S.seqDRMomentFunctional S.η₀ z S.θ₀
  have hprojY_meas : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => projY z) := by
    unfold projY
    measurability
  have hμ0Z_val_memLp : MemLp (fun z => S.μ₀_val (projS₀ z)) 2 S.P_Z := by
    have hmap : MemLp S.μ₀_val 2
        (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z)) := by
      simpa [P_Z_map_projS₀_eq_P_H₀ S] using μ₀_val_memLp S hA h_yd2
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable
      measurable_projS₀.aemeasurable).1 hmap
  have hμ1Z_val_memLp : MemLp (fun z => S.μ₁_val (histH₁ z)) 2 S.P_Z := by
    have hmap : MemLp S.μ₁_val 2
        (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z)) := by
      simpa [P_Z_map_histH₁_eq_P_H₁ S] using μ₁_val_memLp S h_overlap' h_y2
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable
      measurable_histH₁.aemeasurable).1 hmap
  have hY_Z_memLp : MemLp (fun z : γ 0 × δ × γ 1 × δ × ℝ => projY z) 2 S.P_Z := by
    have hY_L2 : MemLp S.toPODTRSystem.factualY 2 P.μ :=
      (memLp_two_iff_integrable_sq
        S.toPODTRSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
    rw [DTREstimationSystem.P_Z]
    exact (memLp_map_measure_iff hprojY_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 (by
        simpa [DTREstimationSystem.factualZ, projY] using hY_L2)
  have hR1_meas : Measurable R1 := by
    simpa [R1, Function.comp_def] using
      (continuous_abs.measurable.comp
        (hprojY_meas.sub (S.μ₁_meas.comp measurable_histH₁)))
  have hR0_meas : Measurable R0 := by
    have hres : Measurable
        (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
          |S.μ₁_val (histH₁ z) - S.μ₀_val (projS₀ z)|) := by
      simpa [Function.comp_def] using
        (continuous_abs.measurable.comp
          ((S.μ₁_meas.comp measurable_histH₁).sub
            (S.μ₀_meas.comp measurable_projS₀)))
    simpa [R0] using hres.add hR1_meas
  have hR1_nonneg : ∀ z, 0 ≤ R1 z := by
    intro z
    dsimp [R1]
    positivity
  have hR0_nonneg : ∀ z, 0 ≤ R0 z := by
    intro z
    dsimp [R0]
    positivity
  have hR1_memLp : MemLp R1 2 S.P_Z := by
    simpa [R1, Real.norm_eq_abs] using (hY_Z_memLp.sub hμ1Z_val_memLp).norm
  have hR0_memLp : MemLp R0 2 S.P_Z := by
    have h01 : MemLp (fun z =>
        |S.μ₁_val (histH₁ z) - S.μ₀_val (projS₀ z)|) 2 S.P_Z := by
      simpa [Real.norm_eq_abs] using (hμ1Z_val_memLp.sub hμ0Z_val_memLp).norm
    simpa [R0] using h01.add hR1_memLp
  have hdμ0Z_memLp : ∀ n ω, MemLp (dμ0Z n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp
        (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2
        (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z)) := by
      simpa [P_Z_map_projS₀_eq_P_H₀ S] using h_mu0_memLp n ω
    simpa [dμ0Z] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable
        measurable_projS₀.aemeasurable).1 hmap
  have hdμ1Z_memLp : ∀ n ω, MemLp (dμ1Z n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp
        (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2
        (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z)) := by
      simpa [P_Z_map_histH₁_eq_P_H₁ S] using h_mu1_memLp n ω
    simpa [dμ1Z] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable
        measurable_histH₁.aemeasurable).1 hmap
  have hde0Z_memLp : ∀ n ω, MemLp (de0Z n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp
        (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2
        (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z)) := by
      simpa [P_Z_map_projS₀_eq_P_H₀ S] using h_e0_memLp n ω
    simpa [de0Z] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable
        measurable_projS₀.aemeasurable).1 hmap
  have hde1Z_memLp : ∀ n ω, MemLp (de1Z n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp
        (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2
        (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z)) := by
      simpa [P_Z_map_histH₁_eq_P_H₁ S] using h_e1_memLp n ω
    simpa [de1Z] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable
        measurable_histH₁.aemeasurable).1 hmap
  have hde0Z_meas : ∀ n ω, Measurable (de0Z n ω) := by
    intro n ω
    simpa [de0Z] using
      ((η_hat n ω).e₀_meas.comp measurable_projS₀).sub
        (S.e₀_meas.comp measurable_projS₀)
  have hde1Z_meas : ∀ n ω, Measurable (de1Z n ω) := by
    intro n ω
    simpa [de1Z] using
      ((η_hat n ω).e₁_meas.comp measurable_histH₁).sub
        (S.e₁_meas.comp measurable_histH₁)
  have hde0Z_bdd : ∀ n ω z, |de0Z n ω z| ≤ 1 := by
    intro n ω z
    have hη := h_in_H n ω
    have hη_nonneg : 0 ≤ (η_hat n ω).e₀_fn (projS₀ z) :=
      le_trans hε_pos.le ((hη.1 (projS₀ z)).1)
    have hη_le_one : (η_hat n ω).e₀_fn (projS₀ z) ≤ 1 := by
      linarith [(hη.1 (projS₀ z)).2, hε_pos.le]
    have hS_nonneg : 0 ≤ S.e₀_val (projS₀ z) := le_of_lt (S.e₀_pos _)
    have hS_le_one : S.e₀_val (projS₀ z) ≤ 1 := le_of_lt (S.e₀_lt_one _)
    dsimp [de0Z]
    rw [abs_le]
    constructor <;> linarith
  have hde1Z_bdd : ∀ n ω z, |de1Z n ω z| ≤ 1 := by
    intro n ω z
    have hη := h_in_H n ω
    have hη_nonneg : 0 ≤ (η_hat n ω).e₁_fn (histH₁ z) :=
      le_trans hε_pos.le ((hη.2 (histH₁ z)).1)
    have hη_le_one : (η_hat n ω).e₁_fn (histH₁ z) ≤ 1 := by
      linarith [(hη.2 (histH₁ z)).2, hε_pos.le]
    have hS_nonneg : 0 ≤ S.e₁_val (histH₁ z) := le_of_lt (S.e₁_pos _)
    have hS_le_one : S.e₁_val (histH₁ z) ≤ 1 := le_of_lt (S.e₁_lt_one _)
    dsimp [de1Z]
    rw [abs_le]
    constructor <;> linarith
  have hde0Z_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (de0Z n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    have heq :
        (fun n ω => (eLpNorm (de0Z n ω) 2 S.P_Z).toReal) =
          (fun n ω =>
            (eLpNorm
              (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal) := by
      funext n ω
      exact congrArg ENNReal.toReal
        (by
          dsimp [de0Z]
          exact eLpNorm_comp_projS₀_eq (S := S)
            (f := fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀)
            (h_e0_memLp n ω).aestronglyMeasurable)
    rw [heq]
    exact h_e0_rate
  have hde1Z_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (de1Z n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    have heq :
        (fun n ω => (eLpNorm (de1Z n ω) 2 S.P_Z).toReal) =
          (fun n ω =>
            (eLpNorm
              (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal) := by
      funext n ω
      exact congrArg ENNReal.toReal
        (by
          dsimp [de1Z]
          exact eLpNorm_comp_histH₁_eq (S := S)
            (f := fun h => (η_hat n ω).e₁_fn h - S.e₁_val h)
            (h_e1_memLp n ω).aestronglyMeasurable)
    rw [heq]
    exact h_e1_rate
  have hcross0_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (cross0 n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [cross0] using
      residual_mul_error_isLittleOp_one (ν := S.P_Z)
        hR0_meas hR0_nonneg hR0_memLp hde0Z_memLp hde0Z_meas hde0Z_bdd hde0Z_rate
  have hcross1_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (cross1 n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [cross1] using
      residual_mul_error_isLittleOp_one (ν := S.P_Z)
        hR1_meas hR1_nonneg hR1_memLp hde1Z_memLp hde1Z_meas hde1Z_bdd hde1Z_rate
  have hμ0Z_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (dμ0Z n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    have heq :
        (fun n ω => (eLpNorm (dμ0Z n ω) 2 S.P_Z).toReal) =
          (fun n ω =>
            (eLpNorm
              (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal) := by
      funext n ω
      exact congrArg ENNReal.toReal
        (by
          dsimp [dμ0Z]
          exact eLpNorm_comp_projS₀_eq (S := S)
            (f := fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀)
            (h_mu0_memLp n ω).aestronglyMeasurable)
    rw [heq]
    exact h_mu0_rate
  have hμ1Z_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (dμ1Z n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    have heq :
        (fun n ω => (eLpNorm (dμ1Z n ω) 2 S.P_Z).toReal) =
          (fun n ω =>
            (eLpNorm
              (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal) := by
      funext n ω
      exact congrArg ENNReal.toReal
        (by
          dsimp [dμ1Z]
          exact eLpNorm_comp_histH₁_eq (S := S)
            (f := fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h)
            (h_mu1_memLp n ω).aestronglyMeasurable)
    rw [heq]
    exact h_mu1_rate
  have hsum_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (dμ0Z n ω) 2 S.P_Z).toReal +
            (eLpNorm (dμ1Z n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross0 n ω) 2 S.P_Z).toReal +
                (eLpNorm (cross1 n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    exact IsLittleOp.add_one
      (IsLittleOp.add_one (IsLittleOp.add_one hμ0Z_rate hμ1Z_rate) hcross0_rate)
      hcross1_rate
  have hK_pos : 0 < K_seqDR ε := lt_of_lt_of_le zero_lt_one (K_seqDR_one_le hε_pos)
  refine IsLittleOp.of_abs_le_const_mul_one (C := K_seqDR ε) hK_pos hsum_rate ?_
  intro n ω
  have hpointwise :
      ∀ᵐ z ∂S.P_Z, |score n ω z| ≤
        K_seqDR ε * (|dμ0Z n ω z| + |dμ1Z n ω z| +
          cross0 n ω z + cross1 n ω z) := by
    simpa [score, dμ0Z, dμ1Z, de0Z, de1Z, cross0, cross1, R0, R1,
      add_assoc] using
      seqDR_score_diff_pointwise_bound S h_overlap' (η_hat n ω) (h_in_H n ω)
  have hcross0_memLp : MemLp (cross0 n ω) 2 S.P_Z := by
    have hcross_meas : Measurable (cross0 n ω) := by
      have h_abs : Measurable
          (fun z : γ 0 × δ × γ 1 × δ × ℝ => |de0Z n ω z|) := by
        simpa [Function.comp_def] using
          (continuous_abs.measurable.comp (hde0Z_meas n ω))
      simpa [cross0] using hR0_meas.mul h_abs
    refine hR0_memLp.mono' hcross_meas.aestronglyMeasurable ?_
    filter_upwards with z
    have hRz : 0 ≤ R0 z := hR0_nonneg z
    have hdez_le : |de0Z n ω z| ≤ 1 := hde0Z_bdd n ω z
    dsimp [cross0]
    rw [abs_mul, abs_of_nonneg hRz, abs_of_nonneg (abs_nonneg _)]
    exact mul_le_of_le_one_right hRz hdez_le
  have hcross1_memLp : MemLp (cross1 n ω) 2 S.P_Z := by
    have hcross_meas : Measurable (cross1 n ω) := by
      have h_abs : Measurable
          (fun z : γ 0 × δ × γ 1 × δ × ℝ => |de1Z n ω z|) := by
        simpa [Function.comp_def] using
          (continuous_abs.measurable.comp (hde1Z_meas n ω))
      simpa [cross1] using hR1_meas.mul h_abs
    refine hR1_memLp.mono' hcross_meas.aestronglyMeasurable ?_
    filter_upwards with z
    have hRz : 0 ≤ R1 z := hR1_nonneg z
    have hdez_le : |de1Z n ω z| ≤ 1 := hde1Z_bdd n ω z
    dsimp [cross1]
    rw [abs_mul, abs_of_nonneg hRz, abs_of_nonneg (abs_nonneg _)]
    exact mul_le_of_le_one_right hRz hdez_le
  let upper : γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun z =>
    K_seqDR ε * (|dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z + cross1 n ω z)
  have hupper_memLp : MemLp upper 2 S.P_Z := by
    have hsum : MemLp
        (fun z => |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z + cross1 n ω z)
        2 S.P_Z := by
      have h0 : MemLp (fun z => |dμ0Z n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμ0Z_memLp n ω).norm
      have h1 : MemLp (fun z => |dμ1Z n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμ1Z_memLp n ω).norm
      exact ((h0.add h1).add hcross0_memLp).add hcross1_memLp
    simpa [upper, Pi.smul_apply, smul_eq_mul] using hsum.const_smul (K_seqDR ε)
  have hmono :
      (eLpNorm (score n ω) 2 S.P_Z).toReal ≤
        (eLpNorm upper 2 S.P_Z).toReal := by
    have hle_enn : eLpNorm (score n ω) 2 S.P_Z ≤ eLpNorm upper 2 S.P_Z :=
      eLpNorm_mono_ae_real (by
        filter_upwards [hpointwise] with z hz
        simpa [Real.norm_eq_abs, upper] using hz)
    exact ENNReal.toReal_mono hupper_memLp.eLpNorm_ne_top hle_enn
  have hupper_bound :
      (eLpNorm upper 2 S.P_Z).toReal ≤
        K_seqDR ε *
          ((eLpNorm (dμ0Z n ω) 2 S.P_Z).toReal +
            (eLpNorm (dμ1Z n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross0 n ω) 2 S.P_Z).toReal +
                (eLpNorm (cross1 n ω) 2 S.P_Z).toReal) := by
    let total : γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun z =>
      |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z + cross1 n ω z
    have htotal_memLp : MemLp total 2 S.P_Z := by
      have h0 : MemLp (fun z => |dμ0Z n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμ0Z_memLp n ω).norm
      have h1 : MemLp (fun z => |dμ1Z n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμ1Z_memLp n ω).norm
      simpa [total] using ((h0.add h1).add hcross0_memLp).add hcross1_memLp
    have hupper_eq : upper = K_seqDR ε • total := by
      funext z
      simp [upper, total, smul_eq_mul]
    rw [hupper_eq]
    rw [toReal_eLpNorm (htotal_memLp.const_smul (K_seqDR ε)).aestronglyMeasurable]
    rw [lpNorm_const_smul]
    have hcoef : (↑‖K_seqDR ε‖₊ : ℝ) = K_seqDR ε := by
      simp [Real.norm_eq_abs, abs_of_pos hK_pos]
    rw [hcoef]
    gcongr
    have htri1 :
        lpNorm total 2 S.P_Z ≤
          lpNorm (fun z => |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z) 2 S.P_Z +
            lpNorm (cross1 n ω) 2 S.P_Z := by
      have htotal_eq :
          total =
            (fun z => |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z) + cross1 n ω := by
        funext z
        simp [total, Pi.add_apply, add_assoc]
      rw [htotal_eq]
      have hleft : MemLp
          (fun z => |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z) 2 S.P_Z := by
        have h0 : MemLp (fun z => |dμ0Z n ω z|) 2 S.P_Z := by
          simpa [Real.norm_eq_abs] using (hdμ0Z_memLp n ω).norm
        have h1 : MemLp (fun z => |dμ1Z n ω z|) 2 S.P_Z := by
          simpa [Real.norm_eq_abs] using (hdμ1Z_memLp n ω).norm
        exact (h0.add h1).add hcross0_memLp
      exact lpNorm_add_le
        (f := fun z => |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z)
        (g := cross1 n ω) (μ := S.P_Z) hleft
        (by norm_num : (1 : ENNReal) ≤ 2)
    have htri2 :
        lpNorm (fun z => |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z) 2 S.P_Z ≤
          lpNorm (fun z => |dμ0Z n ω z| + |dμ1Z n ω z|) 2 S.P_Z +
            lpNorm (cross0 n ω) 2 S.P_Z := by
      have hleft : MemLp (fun z => |dμ0Z n ω z| + |dμ1Z n ω z|) 2 S.P_Z := by
        have h0 : MemLp (fun z => |dμ0Z n ω z|) 2 S.P_Z := by
          simpa [Real.norm_eq_abs] using (hdμ0Z_memLp n ω).norm
        have h1 : MemLp (fun z => |dμ1Z n ω z|) 2 S.P_Z := by
          simpa [Real.norm_eq_abs] using (hdμ1Z_memLp n ω).norm
        exact h0.add h1
      have hsum_eq :
          (fun z => |dμ0Z n ω z| + |dμ1Z n ω z| + cross0 n ω z) =
            (fun z => |dμ0Z n ω z| + |dμ1Z n ω z|) + cross0 n ω := by
        funext z
        simp [Pi.add_apply, add_assoc]
      rw [hsum_eq]
      exact lpNorm_add_le
        (f := fun z => |dμ0Z n ω z| + |dμ1Z n ω z|)
        (g := cross0 n ω) (μ := S.P_Z) hleft
        (by norm_num : (1 : ENNReal) ≤ 2)
    have htri3 :
        lpNorm (fun z => |dμ0Z n ω z| + |dμ1Z n ω z|) 2 S.P_Z ≤
          lpNorm (fun z => |dμ0Z n ω z|) 2 S.P_Z +
            lpNorm (fun z => |dμ1Z n ω z|) 2 S.P_Z := by
      have h0 : MemLp (fun z => |dμ0Z n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμ0Z_memLp n ω).norm
      simpa using lpNorm_add_le
        (f := fun z => |dμ0Z n ω z|)
        (g := fun z => |dμ1Z n ω z|) (μ := S.P_Z) h0
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hnorm0 :
        lpNorm (fun z => |dμ0Z n ω z|) 2 S.P_Z =
          (eLpNorm (dμ0Z n ω) 2 S.P_Z).toReal := by
      rw [lpNorm_fun_abs (hdμ0Z_memLp n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdμ0Z_memLp n ω).aestronglyMeasurable]
    have hnorm1 :
        lpNorm (fun z => |dμ1Z n ω z|) 2 S.P_Z =
          (eLpNorm (dμ1Z n ω) 2 S.P_Z).toReal := by
      rw [lpNorm_fun_abs (hdμ1Z_memLp n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdμ1Z_memLp n ω).aestronglyMeasurable]
    have hnormC0 :
        lpNorm (cross0 n ω) 2 S.P_Z =
          (eLpNorm (cross0 n ω) 2 S.P_Z).toReal := by
      rw [← toReal_eLpNorm hcross0_memLp.aestronglyMeasurable]
    have hnormC1 :
        lpNorm (cross1 n ω) 2 S.P_Z =
          (eLpNorm (cross1 n ω) 2 S.P_Z).toReal := by
      rw [← toReal_eLpNorm hcross1_memLp.aestronglyMeasurable]
    linarith
  calc
    |(eLpNorm (score n ω) 2 S.P_Z).toReal|
        = (eLpNorm (score n ω) 2 S.P_Z).toReal := by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ (eLpNorm upper 2 S.P_Z).toReal := hmono
    _ ≤ K_seqDR ε *
        ((eLpNorm (dμ0Z n ω) 2 S.P_Z).toReal +
          (eLpNorm (dμ1Z n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross0 n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross1 n ω) 2 S.P_Z).toReal) := hupper_bound
    _ = K_seqDR ε *
        |(eLpNorm (dμ0Z n ω) 2 S.P_Z).toReal +
          (eLpNorm (dμ1Z n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross0 n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross1 n ω) 2 S.P_Z).toReal| := by
          rw [abs_of_nonneg]
          positivity

end DTREstimationSystem

end DTR
end Estimation
end Causalean
