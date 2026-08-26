/- Assembly of the all-alphabet heavy/light polynomial upper bound. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Heavy
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.HeavyRisk
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Calibration
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Pilot
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Fallback
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.ClippingAssembly
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.SelectionDecomposition
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.SplitBridge
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.RateAlgebra
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Complexity
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.FixedLightRisk
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.FixedBranchAssembly
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.AggregateBridge
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.RateClosure
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovarianceAssembly
import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse
import Causalean.Stat.SampleSplit.FiniteCategoryPilot
import Causalean.Stat.SampleSplit.FiniteSelector

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Set MeasureTheory

-- @node: lem:continuous-ratio-polynomial-upper-all-d
/-- [The explicit heavy/light signed one-mark estimator is total and has the capped all-alphabet
  polynomial risk bound under conditional second moments](goal). -/
lemma continuous_ratio_polynomial_upper_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, ∃ handle : PolynomialHandle,
      0 < C_epsilon ∧
      PolynomialComplexityBound handle ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        Measurable
          (polyEstimator handle (n := n) (d := d) M) ∧
        (∀ s : Fin n → Obs d,
          polyEstimator handle (n := n) (d := d) M s ∈ Icc (-M) M) ∧
        (∀ P : ModelClass d epsilon M sigma,
          mse P.law
              (polyEstimator handle (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + min 1 (polynomialComponent n d))) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨Cfix, hCfix, hfixed⟩ :=
    polynomial_fixedBranch_uniform_bound epsilon hepsilon hepsilon_half
  obtain ⟨Ndeg, hNdeg⟩ := polynomialDegree_eventually_two
  obtain ⟨Nlog, hNlog⟩ := logEN_eventually_ge_240
  let N : ℕ := max 8 (max Ndeg Nlog)
  let rho : ℝ := 1
  have hrho : 0 < rho := by simp [rho]
  let handle : PolynomialHandle :=
    ⟨(N, rho), hrho, by
        intro n d hn hd hactive
        exact hNdeg n ((le_max_left Ndeg Nlog).trans
          ((le_max_right 8 (max Ndeg Nlog)).trans hactive.1))⟩
  obtain ⟨Cfall, hCfall, hfallback⟩ :=
    polyEstimator_uncalibrated_rate (N := N) hrho
  let D : ℝ := 128 / epsilon + 96 + 2 / epsilon ^ 4 + 4 * Cfix +
    6 * Cfix * 8192 ^ 2 +
    2 * (32768 / (epsilon * polynomialAlpha0 ^ 2)) ^ 2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  let C : ℝ := max Cfall (D + 1)
  have hC : 0 < C := hCfall.trans_le (le_max_left _ _)
  refine ⟨C, handle, hC, polynomialComplexityBound handle, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two
  have htotal := polyEstimator_total_and_clipped
    (n := n) (d := d) (N := N) (M := M) (rho := rho)
    (le_trans zero_le_one hM)
  have htotal' :
      Measurable (polyEstimator handle (n := n) (d := d) M) ∧
      ∀ s : Fin n → Obs d,
        polyEstimator handle (n := n) (d := d) M s ∈ Icc (-M) M := by
    change Measurable
        (rawPolyEstimator (n := n) (d := d) handle.N handle.rho M) ∧
      ∀ s : Fin n → Obs d,
        rawPolyEstimator handle.N handle.rho M s ∈ Icc (-M) M
    simpa [handle, PolynomialHandle.N, PolynomialHandle.rho] using htotal
  refine ⟨htotal'.1, htotal'.2, ?_⟩
  · intro P
    by_cases hcal : N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n
    · have hn8 : 8 ≤ n := (le_max_left 8 (max Ndeg Nlog)).trans hcal.1
      have hnNdeg : Ndeg ≤ n :=
        (le_max_left Ndeg Nlog).trans
          ((le_max_right 8 (max Ndeg Nlog)).trans hcal.1)
      have hnNlog : Nlog ≤ n :=
        (le_max_right Ndeg Nlog).trans
          ((le_max_right 8 (max Ndeg Nlog)).trans hcal.1)
      have hK : 2 ≤ polynomialDegree n := hNdeg n hnNdeg
      have hL : 240 ≤ logEN n := hNlog n hnNlog
      have hn2 : 2 ≤ n := by omega
      have hlower : 0 < polynomialPilotLowerBand n := by
        unfold polynomialPilotLowerBand
        have hp : 0 < n / 2 := Nat.div_pos (by omega) (by norm_num)
        have hlog : 0 < logEN n := by linarith
        positivity
      have hrate0 : 0 ≤ 1 / (n : ℝ) + polynomialComponent n d := by
        unfold polynomialComponent
        positivity
      have hR : 0 ≤ D *
          (1 / (n : ℝ) + polynomialComponent n d) :=
        mul_nonneg hD.le hrate0
      let base : Obs d := ⟨⟨0, hd⟩, false, 0⟩
      have hbranchFixed : ∀ H : Finset (Fin d),
          polynomialSelectorEligible P.law (polynomialPilotLowerBand n)
              (polynomialPilotUpperBand n) H →
          ∫ z : Fin (n - n / 2) → Obs d,
              (polynomialFixedBranchNormalizedError
                (K := polynomialDegree n) P.law M
                (4096 * logEN n / (n - n / 2 : ℕ)) H z) ^ 2
              ∂(productLaw (n - n / 2) P.law) ≤
            D * (1 / (n : ℝ) + polynomialComponent n d) := by
        intro H helig
        apply (hfixed n d M sigma (polynomialPilotLowerBand n)
          (polynomialPilotUpperBand n) P H helig hK hlower hn2
          (polynomialPilotUpperBand_le_lightScale_quarter hn2)
          (polynomial_fixedBranch_size_condition hn hL)
          (polynomial_shift_condition hn)).trans
        exact polynomial_uniformBranch_expression_le_rate hn8 hepsilon hCfix
          hK hL
      let delta : ℝ := 2 * (d : ℝ) * Real.exp (-32 * logEN n)
      have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
      have hpilotBad :
          (Measure.infinitePi fun _ : ℕ => P.law.observedLaw).real
            (polynomialPilotGood (n := n) P.law
              (polynomialPilotLowerBand n) (polynomialPilotUpperBand n))ᶜ ≤
            delta := by
        exact polynomialPilotGood_compl_probability_calibrated_le P.law hn2
      have hstream := polynomial_clipped_finiteSelector_risk P base hlower hR
        hdelta hbranchFixed hpilotBad
      have hdcal : (d : ℝ) ≤ (n : ℝ) * logEN n := by
        simpa [rho] using hcal.2
      have hbadAbs := polynomial_bad_event_absorption hn hL hdcal
      have hstreamRate :
          ∫ omega : ℕ → Obs d,
              (clip (-1) 1 (polynomialNormalizedSum M
                  (fun i : Fin n => omega i)) - rawAteFormula P.law / M) ^ 2
              ∂(Measure.infinitePi fun _ : ℕ => P.law.observedLaw) ≤
            (D + 1) * (1 / (n : ℝ) + polynomialComponent n d) := by
        apply hstream.trans
        dsimp [delta]
        have hinvRate : 1 / (n : ℝ) ≤
            1 / (n : ℝ) + polynomialComponent n d := by
          apply le_add_of_nonneg_right
          unfold polynomialComponent
          positivity
        nlinarith
      have hmse := mse_polyEstimator_le_of_clipped_stream P hcal hstreamRate
      apply hmse.trans
      have hDC : D + 1 ≤ C := le_max_right _ _
      have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
      calc
        M ^ 2 * ((D + 1) *
            (1 / (n : ℝ) + polynomialComponent n d)) ≤
          M ^ 2 * (C *
            (1 / (n : ℝ) + polynomialComponent n d)) := by gcongr
        _ = C * M ^ 2 *
            (1 / (n : ℝ) + min 1 (polynomialComponent n d)) := by
          have hpolyLe : polynomialComponent n d ≤ 1 := by
            by_contra hnot
            have hone : 1 < polynomialComponent n d := lt_of_not_ge hnot
            have hdlarge : (n : ℝ) * logEN n < (d : ℝ) := by
              unfold polynomialComponent at hone
              have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
              have hlog : 0 < logEN n := by linarith
              have hden : 0 < (n : ℝ) ^ 2 * logEN n ^ 2 := by positivity
              rw [lt_div_iff₀ hden] at hone
              nlinarith [sq_nonneg ((d : ℝ) - (n : ℝ) * logEN n)]
            linarith
          rw [min_eq_right hpolyLe]
          ring
    · have hfb := hfallback hn hd hcal P
      exact hfb.trans (by
        have hFC : Cfall ≤ C := le_max_left _ _
        have hnonneg : 0 ≤ M ^ 2 *
            (1 / (n : ℝ) + min 1 (polynomialComponent n d)) := by
          have hpoly : 0 ≤ polynomialComponent n d := by
            unfold polynomialComponent
            positivity
          positivity
        nlinarith)

-- @node: lem:continuous-ratio-polynomial-upper
/-- [Restricted-range form of the polynomial upper bound](goal). -/
lemma continuous_ratio_polynomial_upper :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon c_epsilon : ℝ, ∃ handle : PolynomialHandle,
      0 < C_epsilon ∧ 0 < c_epsilon ∧
      PolynomialComplexityBound handle ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
        Measurable
          (polyEstimator handle (n := n) (d := d) M) ∧
        (∀ s : Fin n → Obs d,
          polyEstimator handle (n := n) (d := d) M s ∈ Icc (-M) M) ∧
        (∀ P : ModelClass d epsilon M sigma,
          mse P.law
              (polyEstimator handle (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + min 1 (polynomialComponent n d))) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C_epsilon, handle, hC, hcomplexity, hbound⟩ :=
    continuous_ratio_polynomial_upper_all_d epsilon hepsilon hepsilon_half
  refine ⟨C_epsilon, 1, handle, hC, zero_lt_one, hcomplexity, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two _
  exact hbound n d M sigma hn hd hM hsigma hsigma_two

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
