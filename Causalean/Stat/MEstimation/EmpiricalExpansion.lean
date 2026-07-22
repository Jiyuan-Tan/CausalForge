/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Empirical-process expansion for Z-estimator asymptotic linearity

Empirical-process / linearization layer feeding
`Causalean/Stat/MEstimation/ZEstimatorCLT.lean`'s `zEstimator_clt`: starting from the
almost-everywhere integrable derivative envelope (`score_envelope`) of
`ZEstimatorRegularity` together with the
Fréchet-derivative spec, it provides four building blocks of the
classical asymptotic-linearization proof behind van der Vaart (1998),
Theorem 5.41:

1. `score_diff_L2_isLittleOp_sqrt`              — sample mean-square score
                                                    difference at a consistent
                                                    estimator is `o_p(1)`.
                                                    proved from the score
                                                    envelope.
2. `empiricalScoreDiff_isLittleOp_sqrt`          — centered empirical sum of
                                                    `(ψ(θn,·) − ψ(θ₀,·))` is
                                                    `o_p(√n)` (norm).
                                                    assumed through
                                                    `StochEquicontAt`.
3. `populationScoreDiff_eq_jacobian_plus_remainder`
                                                  — population Fréchet
                                                    expansion of
                                                    `∫ (ψ(θ,·) − ψ(θ₀,·)) dP`.
                                                    **Proved.**
4. `localStochasticExpansion`                    — the headline expansion,
                                                    combining the stochastic
                                                    equicontinuity input with
                                                    (c) under
                                                    the rate hypothesis
                                                    `‖θn − θ₀‖ = O_p(1/√n)`.
                                                    **Proved.**

References:
* `def:par-smoothness` and `thm:par-z-clt` in
  `doc/basic_concepts/Semi-parametric Inference/parametric_inference.tex`.
* van der Vaart (1998), §5.6, Theorem 5.41.
* Newey & McFadden (1994), §7.

The file proves the mean-square score control, the population derivative
expansion, and the local stochastic expansion. The centered empirical-process
term is represented by the explicit `StochEquicontAt` hypothesis used by the
downstream Z-estimator CLT, keeping the algebraic linearization separate from
whatever empirical-process theorem supplies that hypothesis in an application.
-/

import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.CLT.AsymptoticLinearityVec
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Sample
import Causalean.Stat.MEstimation.ZEstimator
import Causalean.Stat.EmpiricalProcess.Equicontinuity.StochEquicont
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Empirical expansion for Z-estimators

This module supplies the empirical-process and population-expansion layer used
by `zEstimator_clt`.  It proves the mean-square score control
`score_diff_L2_isLittleOp_sqrt`, packages local stochastic equicontinuity as
`StochEquicontAt`, derives `empiricalScoreDiff_isLittleOp_sqrt` from that
package and consistency, restates the population derivative as
`populationScoreDiff_eq_jacobian_plus_remainder`, and combines the pieces in
`localStochasticExpansion`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## (a) Sample mean-square score difference at a consistent estimator -/

/-- **(a) Score difference is `o_p(1)` in mean square.**

If `θn → θ₀` in probability and `ψ` has the almost-everywhere integrable derivative envelope
(`score_envelope`) of `ZEstimatorRegularity`, then the empirical mean-square
deviation of the score family vanishes in probability:
`(1/n) Σ_{i<n} ‖ψ(θn n ω, Z_i) − ψ(θ₀, Z_i)‖² = o_p(1)`.

This is the inner step in van der Vaart (1998), Theorem 5.41 — the
quantitative form of `L²`-stochastic equicontinuity used to control
the empirical-process error in the localisation argument. -/
theorem score_diff_L2_isLittleOp_sqrt
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0)) :
    IsLittleOp
      (fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖^2)
      (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  by_cases hγtop : γ = ⊤
  · filter_upwards with n
    simp [hγtop]
  have hγpos : 0 < γ.toReal := ENNReal.toReal_pos (ne_of_gt hγ) hγtop
  let α : ℝ := γ.toReal / 4
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  rcases reg.score_envelope with
    ⟨δenv, hδenv, F, hFmeas, hFnonneg, hFint, hFbound⟩
  let K : ℝ := ∫ z, F z ^ 2 ∂P
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact integral_nonneg fun z => sq_nonneg (F z)
  let M : ℝ := (K + 1) / α
  have hK1pos : 0 < K + 1 := by linarith
  have hMpos : 0 < M := div_pos hK1pos hαpos
  have hKM_nonneg : 0 ≤ K / M := div_nonneg hK_nonneg (le_of_lt hMpos)
  have hKM_le : K / M ≤ α := by
    dsimp [M]
    field_simp [hαpos.ne', hK1pos.ne']
    nlinarith [hK_nonneg, hαpos]
  let τ : ℝ := min δenv (Real.sqrt (ε / (M + 1)))
  have hM1pos : 0 < M + 1 := by linarith
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact lt_min hδenv (Real.sqrt_pos.mpr (div_pos hε hM1pos))
  have hτhalf_pos : 0 < τ / 2 := by linarith
  have hτ_le_env : τ ≤ δenv := by
    dsimp [τ]
    exact min_le_left _ _
  have hτ_le_sqrt : τ ≤ Real.sqrt (ε / (M + 1)) := by
    dsimp [τ]
    exact min_le_right _ _
  have hτsq_le : τ ^ 2 ≤ ε / (M + 1) := by
    have hs := pow_le_pow_left₀ (le_of_lt hτpos) hτ_le_sqrt 2
    simpa [Real.sq_sqrt (div_nonneg (le_of_lt hε) (le_of_lt hM1pos))] using hs
  have hτsqM_lt : τ ^ 2 * M < ε := by
    have hmul := mul_le_mul_of_nonneg_right hτsq_le (le_of_lt hMpos)
    have hfrac : ε / (M + 1) * M < ε := by
      rw [div_mul_eq_mul_div]
      rw [div_lt_iff₀ hM1pos]
      nlinarith [hε, hMpos]
    exact lt_of_le_of_lt hmul hfrac
  let Mn : ℕ → Ω → ℝ := fun n ω =>
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, F (S.Z i ω) ^ 2
  have hFpow_meas : Measurable fun z => F z ^ 2 := hFmeas.pow_const 2
  have hmap_i : ∀ i, μ.map (S.Z i) = P := by
    intro i
    calc
      μ.map (S.Z i) = μ.map (S.Z 0) := (S.identDist i).map_eq.symm
      _ = P := S.law
  have hint_i : ∀ i, Integrable (fun ω => F (S.Z i ω) ^ 2) μ := by
    intro i
    have hi : Integrable (fun z => F z ^ 2) (μ.map (S.Z i)) := by
      simpa [hmap_i i] using hFint
    simpa [Function.comp_def] using hi.comp_measurable (S.meas i)
  have hint_eq_i :
      ∀ i, (∫ ω, F (S.Z i ω) ^ 2 ∂μ) = K := by
    intro i
    calc
      (∫ ω, F (S.Z i ω) ^ 2 ∂μ)
          = ∫ z, F z ^ 2 ∂(μ.map (S.Z i)) := by
              exact (integral_map (S.meas i).aemeasurable
                hFpow_meas.aestronglyMeasurable).symm
      _ = K := by
              rw [hmap_i i]
  have hMn_nonneg_point : ∀ n ω, 0 ≤ Mn n ω := by
    intro n ω
    dsimp [Mn]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun i _hi => sq_nonneg (F (S.Z i ω)))
  have hMn_nonneg : ∀ n, 0 ≤ᵐ[μ] Mn n := by
    intro n
    exact Eventually.of_forall (hMn_nonneg_point n)
  have hMn_int : ∀ n, Integrable (Mn n) μ := by
    intro n
    dsimp [Mn]
    exact (integrable_finset_sum (Finset.range n)
      (fun i _hi => hint_i i)).const_mul _
  have hMn_integral_le : ∀ n, (∫ ω, Mn n ω ∂μ) ≤ K := by
    intro n
    by_cases hn : n = 0
    · subst n
      dsimp [Mn, K]
      simpa using hK_nonneg
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      dsimp [Mn]
      rw [integral_const_mul]
      rw [MeasureTheory.integral_finset_sum (Finset.range n)]
      · simp_rw [hint_eq_i]
        simp [Finset.sum_const, hnR]
      · intro i _hi
        exact hint_i i
  have hMn_markov :
      ∀ n, μ {ω | M < Mn n ω} ≤ ENNReal.ofReal (K / M) := by
    intro n
    have hge_real : (μ {ω | M ≤ Mn n ω}).toReal ≤ K / M := by
      have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (hMn_nonneg n) (hMn_int n) M
      have hdiv : μ.real {ω | M ≤ Mn n ω} ≤
          (∫ ω, Mn n ω ∂μ) / M := by
        rw [measureReal_def]
        exact (le_div_iff₀ hMpos).mpr (by simpa [measureReal_def, mul_comm] using hmark)
      exact le_trans hdiv (div_le_div_of_nonneg_right (hMn_integral_le n)
        (le_of_lt hMpos))
    exact le_trans (measure_mono (by
        intro ω hω
        change M ≤ Mn n ω
        exact le_of_lt hω))
      ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
        hKM_nonneg).mpr hge_real)
  have hCons_le := (ENNReal.tendsto_nhds_zero.mp
    (hConsistent (τ / 2) hτhalf_pos))
    (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
  have htwo_alpha_lt_gamma : ENNReal.ofReal (2 * α) < γ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hγpos]
    · exact hγtop
  filter_upwards [hCons_le] with n hnCons
  exact le_of_lt <| calc
      μ {ω |
        ε * (fun _ => (1 : ℝ)) n <
          |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2|}
        ≤ μ ({ω | τ / 2 < ‖θn n ω - θ₀‖} ∪ {ω | M < Mn n ω}) := by
            apply measure_mono_ae
            have hFbound_i :
                ∀ i : ℕ, ∀ᵐ ω ∂μ, ∀ θ : E, ‖θ - θ₀‖ < δenv →
                  ‖ψ θ (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ≤ ‖θ - θ₀‖ * F (S.Z i ω) := by
              intro i
              have hbound_map :
                  ∀ᵐ z ∂(μ.map (S.Z i)), ∀ θ : E, ‖θ - θ₀‖ < δenv →
                    ‖ψ θ z - ψ θ₀ z‖ ≤ ‖θ - θ₀‖ * F z := by
                simpa [hmap_i i] using hFbound
              exact ae_of_ae_map (S.meas i).aemeasurable hbound_map
            have hFbound_all :
                ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, ∀ θ : E, ‖θ - θ₀‖ < δenv →
                  ‖ψ θ (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ≤
                    ‖θ - θ₀‖ * F (S.Z i ω) := by
              rw [Finset.eventually_all]
              intro i _hi
              exact hFbound_i i
            filter_upwards [hFbound_all] with ω hFboundω hω
            by_cases hn0 : n = 0
            · subst n
              have hω0 : ε < 0 := by
                simpa using hω
              exact False.elim (not_lt_of_ge hε.le hω0)
            · have hnR_nonneg : 0 ≤ (n : ℝ)⁻¹ :=
                inv_nonneg.mpr (Nat.cast_nonneg n)
              have hT_nonneg :
                  0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                    ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2 := by
                exact mul_nonneg hnR_nonneg
                  (Finset.sum_nonneg fun i _hi => sq_nonneg _)
              have hTgt :
                  ε < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                    ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2 := by
                have hω' : ε <
                    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                      ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2| := by
                  simpa using hω
                simpa [abs_of_nonneg hT_nonneg] using hω'
              by_cases hθsmall : ‖θn n ω - θ₀‖ ≤ τ / 2
              · by_cases hMsmall : Mn n ω ≤ M
                · have hθ_lt_env : ‖θn n ω - θ₀‖ < δenv := by
                    have hθ_lt_τ : ‖θn n ω - θ₀‖ < τ := by linarith [hθsmall, hτpos]
                    exact lt_of_lt_of_le hθ_lt_τ hτ_le_env
                  have hsum_le :
                      (∑ i ∈ Finset.range n,
                        ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2)
                        ≤ ‖θn n ω - θ₀‖ ^ 2 *
                          ∑ i ∈ Finset.range n, F (S.Z i ω) ^ 2 := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_le_sum ?_
                    intro i _hi
                    have henv := hFboundω i _hi (θn n ω) hθ_lt_env
                    have hrhs_nonneg :
                        0 ≤ ‖θn n ω - θ₀‖ * F (S.Z i ω) :=
                      mul_nonneg (norm_nonneg _) (hFnonneg _)
                    have hsquare :
                        ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2
                          ≤ (‖θn n ω - θ₀‖ * F (S.Z i ω)) ^ 2 :=
                      by
                        have hnorm_nonneg :
                            0 ≤ ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ :=
                          norm_nonneg _
                        exact sq_le_sq' (by linarith) henv
                    simpa [mul_pow] using hsquare
                  have hT_le :
                      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                        ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2
                        ≤ ‖θn n ω - θ₀‖ ^ 2 * Mn n ω := by
                    have hmul := mul_le_mul_of_nonneg_left hsum_le hnR_nonneg
                    dsimp [Mn]
                    nlinarith
                  have hθsq_le : ‖θn n ω - θ₀‖ ^ 2 ≤ τ ^ 2 := by
                    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
                  have hprod_le : ‖θn n ω - θ₀‖ ^ 2 * Mn n ω ≤ τ ^ 2 * M := by
                    have hMn_nonnegω : 0 ≤ Mn n ω := hMn_nonneg_point n ω
                    exact mul_le_mul hθsq_le hMsmall hMn_nonnegω
                      (sq_nonneg τ)
                  have hT_lt : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                        ‖ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)‖ ^ 2 < ε :=
                    lt_of_le_of_lt (le_trans hT_le hprod_le) hτsqM_lt
                  exact False.elim (not_lt_of_ge hT_lt.le hTgt)
                · exact Or.inr (lt_of_not_ge hMsmall)
              · exact Or.inl (lt_of_not_ge hθsmall)
    _ ≤ μ {ω | τ / 2 < ‖θn n ω - θ₀‖} + μ {ω | M < Mn n ω} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal α + ENNReal.ofReal (K / M) :=
        add_le_add hnCons (hMn_markov n)
    _ ≤ ENNReal.ofReal α + ENNReal.ofReal α :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hKM_le)
    _ = ENNReal.ofReal (2 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · linarith
        · exact hKM_nonneg.trans hKM_le
    _ < γ := htwo_alpha_lt_gamma

/-! ## (b) Centered empirical-process control -/

-- `StochEquicontAt` (the estimator-indexed asymptotic-equicontinuity hypothesis
-- used below) now lives in the empirical-process layer, at
-- `Causalean/Stat/EmpiricalProcess/Equicontinuity/StochEquicont.lean`, so the
-- foundational equicontinuity modules need not depend on this expansion.

/-- **(b) Empirical-process score difference is `o_p(√n)`.**

Under `ZEstimatorRegularity`, consistency `θn →_p θ₀`, and asymptotic
equicontinuity `StochEquicontAt ψ θ₀ P μ S θn`, the centered empirical sum
`∑_{i<n} (ψ(θn,Z_i) − ψ(θ₀,Z_i)) − n · ∫ (ψ(θn,·) − ψ(θ₀,·)) dP`
divided by `√n` tends to zero in probability (in norm).

This is the empirical-process step of van der Vaart (1998), Theorem 5.41.
The hypothesis `hStochEquicont` packages the Donsker / chaining content
that converts the local `L²`-modulus into uniform linearisation; the
proof here only has to remove the conditioning on `{‖θn − θ₀‖ < δ}` using
`hConsistent`.  The inner Bochner integral is well-defined for `n` large
enough thanks to `reg.psi_int_neighborhood`. -/
theorem empiricalScoreDiff_isLittleOp_sqrt
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (_reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn) :
    IsLittleOp
      (fun n ω =>
        ‖(Real.sqrt (n : ℝ))⁻¹ •
            (∑ i ∈ Finset.range n,
              (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)))
          - Real.sqrt (n : ℝ) •
              ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P‖)
      (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  by_cases hγtop : γ = ⊤
  · filter_upwards with n
    simp [hγtop]
  have hγpos : 0 < γ.toReal := ENNReal.toReal_pos (ne_of_gt hγ) hγtop
  let α : ℝ := γ.toReal / 4
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  rcases hStochEquicont ε hε with ⟨δ, hδ_pos, hStoch⟩
  have hδhalf_pos : 0 < δ / 2 := by linarith
  have hStoch_le := (ENNReal.tendsto_nhds_zero.mp hStoch)
    (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
  have hCons_le := (ENNReal.tendsto_nhds_zero.mp
    (hConsistent (δ / 2) hδhalf_pos))
    (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
  have htwo_alpha_lt_gamma : ENNReal.ofReal (2 * α) < γ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hγpos]
    · exact hγtop
  filter_upwards [hStoch_le, hCons_le] with n hnStoch hnCons
  exact le_of_lt <| calc
    μ {ω |
        ε * (fun _ => (1 : ℝ)) n <
          |‖(Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n,
                (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)))
            - Real.sqrt (n : ℝ) •
                ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P‖|}
        ≤ μ ({ω | ‖θn n ω - θ₀‖ < δ ∧
              ε < ‖(Real.sqrt (n : ℝ))⁻¹ •
                    (∑ i ∈ Finset.range n,
                      (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)))
                  - Real.sqrt (n : ℝ) •
                      ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P‖}
              ∪ {ω | δ / 2 < ‖θn n ω - θ₀‖}) := by
            apply measure_mono
            intro ω hω
            have hR : ε <
                ‖(Real.sqrt (n : ℝ))⁻¹ •
                    (∑ i ∈ Finset.range n,
                      (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)))
                  - Real.sqrt (n : ℝ) •
                      ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P‖ := by
              simpa [abs_of_nonneg (norm_nonneg _)] using hω
            by_cases hθ : ‖θn n ω - θ₀‖ < δ
            · exact Or.inl ⟨hθ, hR⟩
            · exact Or.inr (by
                have hδle : δ ≤ ‖θn n ω - θ₀‖ := le_of_not_gt hθ
                have hhalf_lt_delta : δ / 2 < δ := by linarith [hδ_pos]
                exact lt_of_lt_of_le hhalf_lt_delta hδle)
    _ ≤ μ {ω | ‖θn n ω - θ₀‖ < δ ∧
              ε < ‖(Real.sqrt (n : ℝ))⁻¹ •
                    (∑ i ∈ Finset.range n,
                      (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)))
                  - Real.sqrt (n : ℝ) •
                      ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P‖}
          + μ {ω | δ / 2 < ‖θn n ω - θ₀‖} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal α + ENNReal.ofReal α :=
        add_le_add hnStoch hnCons
    _ = ENNReal.ofReal (2 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · linarith
        · linarith
    _ < γ := htwo_alpha_lt_gamma

/-! ## (c) Population Fréchet expansion -/

/-- **(c) Population Fréchet expansion of the score difference.**

The population mean of the score difference admits the linearisation
`∫ (ψ(θ,·) − ψ(θ₀,·)) dP = J₀ (θ − θ₀) + o(‖θ − θ₀‖)` near `θ₀`.

This is exactly `reg.J₀_spec` (Fréchet differentiability) restated as an
`Asymptotics.IsLittleO` of the remainder against `‖θ − θ₀‖`, a form
convenient for combining with empirical-process control in
`localStochasticExpansion`.  Corresponds to the population side of
`def:par-smoothness` / van der Vaart (1998), Theorem 5.41. -/
theorem populationScoreDiff_eq_jacobian_plus_remainder
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P) :
    (fun θ => ∫ z, (ψ θ z - ψ θ₀ z) ∂P
              - reg.J₀ (θ - θ₀))
      =o[𝓝 θ₀] fun θ => ‖θ - θ₀‖ := by
  rcases reg.psi_int_neighborhood with ⟨δ, hδ_pos, hδ_int⟩
  have hψ₀ : Integrable (ψ θ₀) P := by
    exact hδ_int θ₀ (by simpa using hδ_pos)
  have hbase :
      (fun θ => (∫ z, ψ θ z ∂P) - (∫ z, ψ θ₀ z ∂P)
          - reg.J₀ (θ - θ₀))
        =o[𝓝 θ₀] fun θ => θ - θ₀ :=
    reg.J₀_spec.isLittleO
  have hbase_norm :
      (fun θ => (∫ z, ψ θ z ∂P) - (∫ z, ψ θ₀ z ∂P)
          - reg.J₀ (θ - θ₀))
        =o[𝓝 θ₀] fun θ => ‖θ - θ₀‖ :=
    (Asymptotics.isLittleO_norm_right).mpr hbase
  refine hbase_norm.congr' ?_ EventuallyEq.rfl
  have hnear : ∀ᶠ θ in 𝓝 θ₀, ‖θ - θ₀‖ < δ := by
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ_pos, ?_⟩
    intro θ hθ
    simpa [dist_eq_norm] using hθ
  filter_upwards [hnear] with θ hθ
  rw [MeasureTheory.integral_sub (hδ_int θ (by simpa [dist_eq_norm] using hθ)) hψ₀]

/-! ## Headline local stochastic expansion -/

/-- **Local stochastic expansion for Z-estimators.**

Combining centered empirical-process control with the population Fréchet
expansion and the rate-of-convergence input
`‖θn − θ₀‖ = O_p(1/√n)` produces the linearisation
`(1/√n) Σ_{i<n} (ψ(θn,Z_i) − ψ(θ₀,Z_i)) − √n · J₀ (θn − θ₀) = o_p(1)`
in norm.

The hypothesis `hRate` (i.e. `θn − θ₀ = O_p(1/√n)`) is the rate-of-
convergence input.  Classically (van der Vaart 1998, §5.3) this rate is
itself a consequence of consistency together with non-singularity of the
Jacobian; we expose it as a hypothesis to keep the linearisation step
independent of the rate-derivation step.  The conclusion feeds directly
into `zEstimator_clt`. -/
theorem localStochasticExpansion
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - θ₀‖)
      (fun n => (Real.sqrt (n : ℝ))⁻¹) μ) :
    IsLittleOp
      (fun n ω =>
        ‖(Real.sqrt (n : ℝ))⁻¹ •
            ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
          - Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀)‖)
      (fun _ => (1 : ℝ)) μ := by
  let Sn : ℕ → Ω → E := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ •
      ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
  let In : ℕ → Ω → E := fun n ω =>
    Real.sqrt (n : ℝ) • ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P
  let Jn : ℕ → Ω → E := fun n ω =>
    Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀)
  have hI : IsLittleOp (fun n ω => ‖Sn n ω - In n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa [Sn, In] using
      empiricalScoreDiff_isLittleOp_sqrt ψ θ₀ P reg S θn hConsistent
        hStochEquicont
  have hF :
      (fun θ => ∫ z, (ψ θ z - ψ θ₀ z) ∂P
                - reg.J₀ (θ - θ₀))
        =o[𝓝 θ₀] fun θ => ‖θ - θ₀‖ :=
    populationScoreDiff_eq_jacobian_plus_remainder ψ θ₀ P reg
  have hII : IsLittleOp (fun n ω => ‖In n ω - Jn n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    by_cases hδtop : δ = ⊤
    · filter_upwards with n
      simp [hδtop]
    have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
    let α : ℝ := δ.toReal / 8
    have hαpos : 0 < α := by
      dsimp [α]
      linarith
    rcases hRate α hαpos with ⟨M0, hM0⟩
    let M : ℝ := max M0 1
    have hMpos : 0 < M := by
      dsimp [M]
      exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
    have hM0le : M0 ≤ M := by
      dsimp [M]
      exact le_max_left M0 1
    let A : ℕ → Set Ω := fun n =>
      {ω | M * (Real.sqrt (n : ℝ))⁻¹ < |‖θn n ω - θ₀‖|}
    have hlimA : Filter.limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal α := by
      refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
      intro n
      apply measure_mono
      intro ω hω
      dsimp [A] at hω ⊢
      have hrn_nonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ :=
        inv_nonneg.mpr (Real.sqrt_nonneg _)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hM0le hrn_nonneg) hω
    have halpha_two : ENNReal.ofReal α < ENNReal.ofReal (2 * α) := by
      rw [ENNReal.ofReal_lt_ofReal_iff]
      · linarith
      · linarith
    have hAevent := Filter.eventually_lt_of_limsup_lt
      (lt_of_le_of_lt hlimA halpha_two)
    let η : ℝ := ε / M
    have hηpos : 0 < η := by
      dsimp [η]
      exact div_pos hε hMpos
    have hderiv_event :
        ∀ᶠ θ in 𝓝 θ₀,
          ‖∫ z, (ψ θ z - ψ θ₀ z) ∂P - reg.J₀ (θ - θ₀)‖
            ≤ η * ‖θ - θ₀‖ := by
      have hderiv_event0 := hF.def hηpos
      filter_upwards [hderiv_event0] with θ hθ
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (θ - θ₀))] using hθ
    rcases Metric.eventually_nhds_iff.mp hderiv_event with ⟨ρ, hρpos, hρprop⟩
    let B : ℕ → Set Ω := fun n => {ω | ρ ≤ ‖θn n ω - θ₀‖}
    have hConsistentHalf := hConsistent (ρ / 2) (by linarith)
    have hBsmall0 := (ENNReal.tendsto_nhds_zero.mp hConsistentHalf)
      (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
    have hBevent : ∀ᶠ n in atTop, μ (B n) < ENNReal.ofReal (2 * α) := by
      filter_upwards [hBsmall0] with n hn
      exact lt_of_le_of_lt (le_trans (measure_mono (by
        intro ω hω
        dsimp [B] at hω
        have : ρ / 2 < ‖θn n ω - θ₀‖ := by linarith
        exact this)) hn) halpha_two
    let C : ℕ → Set Ω := fun n => {ω | ε < |‖In n ω - Jn n ω‖|}
    have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
      intro n
      have hsubset : C n ⊆ A n ∪ B n := by
        intro ω hω
        by_contra hnot
        have hnotA : ¬ M * (Real.sqrt (n : ℝ))⁻¹ < |‖θn n ω - θ₀‖| := by
          intro hx
          exact hnot (Or.inl hx)
        have hnotB : ¬ ρ ≤ ‖θn n ω - θ₀‖ := by
          intro hx
          exact hnot (Or.inr hx)
        have hθle : ‖θn n ω - θ₀‖ ≤ M * (Real.sqrt (n : ℝ))⁻¹ := by
          have := le_of_not_gt hnotA
          simpa [abs_of_nonneg (norm_nonneg (θn n ω - θ₀))] using this
        have hnear : ‖θn n ω - θ₀‖ < ρ := lt_of_not_ge hnotB
        have hder := hρprop (by simpa [dist_eq_norm] using hnear)
        have hscaled_le : Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖ ≤ M := by
          by_cases hn : n = 0
          · simp [hn, hMpos.le]
          · have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
            have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
            have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
            calc
              Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖
                  ≤ Real.sqrt (n : ℝ) * (M * (Real.sqrt (n : ℝ))⁻¹) :=
                    mul_le_mul_of_nonneg_left hθle (Real.sqrt_nonneg _)
              _ = M := by
                field_simp [hsqrt_pos.ne']
        have hRle : ‖In n ω - Jn n ω‖ ≤ ε := by
          calc
            ‖In n ω - Jn n ω‖
                = ‖Real.sqrt (n : ℝ) •
                    (∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P
                      - reg.J₀ (θn n ω - θ₀))‖ := by
                    simp [In, Jn, sub_eq_add_neg, smul_add, smul_neg]
            _ = Real.sqrt (n : ℝ) *
                  ‖∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P
                    - reg.J₀ (θn n ω - θ₀)‖ := by
                    rw [norm_smul, Real.norm_eq_abs,
                      abs_of_nonneg (Real.sqrt_nonneg _)]
            _ ≤ Real.sqrt (n : ℝ) * (η * ‖θn n ω - θ₀‖) := by
                    exact mul_le_mul_of_nonneg_left hder (Real.sqrt_nonneg _)
            _ = η * (Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖) := by ring
            _ ≤ η * M := mul_le_mul_of_nonneg_left hscaled_le (le_of_lt hηpos)
            _ = ε := by
              dsimp [η]
              field_simp [hMpos.ne']
        have hω' : ε < ‖In n ω - Jn n ω‖ := by
          simpa [C, abs_of_nonneg (norm_nonneg (In n ω - Jn n ω))] using hω
        exact not_lt_of_ge hRle hω'
      calc
        μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
        _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
    have hfour_alpha_lt_delta : ENNReal.ofReal (4 * α) < δ := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal]
      · dsimp [α]
        linarith
      · dsimp [α]
        linarith [le_of_lt hδpos]
      · exact hδtop
    filter_upwards [hAevent, hBevent] with n hAn hBn
    exact le_of_lt <| calc
      μ {ω | ε * (fun _ => (1 : ℝ)) n < |‖In n ω - Jn n ω‖|}
          = μ (C n) := by simp [C]
      _ ≤ μ (A n) + μ (B n) := hpoint n
      _ < ENNReal.ofReal (2 * α) + ENNReal.ofReal (2 * α) :=
        ENNReal.add_lt_add hAn hBn
      _ = ENNReal.ofReal (4 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · linarith
        · linarith
      _ < δ := hfour_alpha_lt_delta
  have hLittle_add_one :
      ∀ {Xn Yn : ℕ → Ω → ℝ},
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
    let A : ℕ → Set Ω := fun n => {ω | ε / 2 < |Xn n ω|}
    let B : ℕ → Set Ω := fun n => {ω | ε / 2 < |Yn n ω|}
    let C : ℕ → Set Ω := fun n => {ω | ε < |Xn n ω + Yn n ω|}
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
    have hXA' : μ (A n) ≤ ENNReal.ofReal α := by
      simpa [A] using hXA
    have hYB' : μ (B n) ≤ ENNReal.ofReal α := by
      simpa [B] using hYB
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ ε / 2 < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl hx)
      have hnotB : ¬ ε / 2 < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr hy)
      have hXle : |Xn n ω| ≤ ε / 2 := le_of_not_gt hnotA
      have hYle : |Yn n ω| ≤ ε / 2 := le_of_not_gt hnotB
      have hsum : |Xn n ω + Yn n ω| ≤ ε := by
        calc
          |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| := abs_add_le _ _
          _ ≤ ε / 2 + ε / 2 := add_le_add hXle hYle
          _ = ε := by ring
      exact not_lt_of_ge hsum hω
    exact le_of_lt <| calc
      μ {ω | ε * (fun _ => (1 : ℝ)) n < |Xn n ω + Yn n ω|}
          = μ (C n) := by simp [C]
      _ ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
      _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hXA' hYB'
      _ = ENNReal.ofReal (2 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · linarith
        · linarith
      _ < δ := htwo_alpha_lt_delta
  have hsum : IsLittleOp
      (fun n ω => ‖Sn n ω - In n ω‖ + ‖In n ω - Jn n ω‖)
      (fun _ => (1 : ℝ)) μ :=
    hLittle_add_one hI hII
  have hmono_one :
      ∀ {Xn Yn : ℕ → Ω → ℝ},
        IsLittleOp Yn (fun _ => (1 : ℝ)) μ →
        (∀ n ω, |Xn n ω| ≤ |Yn n ω|) →
        IsLittleOp Xn (fun _ => (1 : ℝ)) μ := by
    intro Xn Yn hY hbound ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have hYevent := (ENNReal.tendsto_nhds_zero.mp (hY ε hε)) δ hδ
    filter_upwards [hYevent] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hω
    exact lt_of_lt_of_le hω (hbound n ω)
  refine hmono_one hsum ?_
  intro n ω
  have htri :
      ‖Sn n ω - Jn n ω‖
        ≤ ‖Sn n ω - In n ω‖ + ‖In n ω - Jn n ω‖ := by
    calc
      ‖Sn n ω - Jn n ω‖
          = ‖(Sn n ω - In n ω) + (In n ω - Jn n ω)‖ := by
              congr 1
              abel
      _ ≤ ‖Sn n ω - In n ω‖ + ‖In n ω - Jn n ω‖ := norm_add_le _ _
  have hsum_nonneg :
      0 ≤ ‖Sn n ω - In n ω‖ + ‖In n ω - Jn n ω‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    |‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
      - Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀)‖|
        = ‖Sn n ω - Jn n ω‖ := by
            simp [Sn, Jn]
    _ ≤ ‖Sn n ω - In n ω‖ + ‖In n ω - Jn n ω‖ := htri
    _ = |‖Sn n ω - In n ω‖ + ‖In n ω - Jn n ω‖| := by
            rw [abs_of_nonneg hsum_nonneg]

end Causalean.Stat
