/- Resolution of the robust upper-construction problem. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.OccupancyUpperAssembly

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Set

-- @node: thm:robust-upper-construction-resolution-all-d
/-- [The explicit polynomial and collision constructions are admissible and obey their two
  all-alphabet risk envelopes without an additional logarithmic factor](goal). -/
theorem robust_upper_construction_resolution_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, ∃ handle : PolynomialHandle,
      0 < C_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        Measurable
          (polyEstimator handle (n := n) (d := d) M) ∧
        (∀ s : Fin n → Obs d,
          polyEstimator handle (n := n) (d := d) M s ∈ Icc (-M) M) ∧
        Measurable (collisionEstimator (n := n) (d := d) M) ∧
        (∀ s : Fin n → Obs d,
          collisionEstimator (n := n) (d := d) M s ∈ Icc (-M) M) ∧
        ∀ P : ModelClass d epsilon M sigma,
          mse P.law
              (polyEstimator handle (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ∧
          mse P.law (collisionEstimator (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨Cpoly, handle, hCpoly, _hcomplexity, hpoly⟩ :=
    continuous_ratio_polynomial_upper_all_d epsilon hepsilon hepsilon_half
  obtain ⟨Ccollision, hCcollision, hcollision⟩ :=
    continuous_occupancy_collision_upper_all_d
      epsilon hepsilon hepsilon_half
  refine ⟨max Cpoly Ccollision, handle,
    lt_of_lt_of_le hCpoly (le_max_left _ _), ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two
  obtain ⟨hpoly_meas, hpoly_mem, hpoly_risk⟩ :=
    hpoly n d M sigma hn hd hM hsigma hsigma_two
  obtain ⟨hcollision_meas, hcollision_mem⟩ :=
    collisionEstimator_admissible (le_trans zero_le_one hM)
  refine ⟨hpoly_meas, hpoly_mem, hcollision_meas, hcollision_mem, ?_⟩
  intro P
  constructor
  · refine hpoly_risk P |>.trans ?_
    gcongr
    · apply add_nonneg
      · positivity
      · exact le_min zero_le_one (by
          unfold polynomialComponent
          positivity)
    · exact le_max_left Cpoly Ccollision
  · refine hcollision n d M sigma hn hd P |>.trans ?_
    gcongr
    exact le_max_right Cpoly Ccollision

-- @node: thm:robust-upper-construction-resolution
/-- [Restricted-dimension form of the robust upper-construction theorem](goal). -/
theorem robust_upper_construction_resolution :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon c_epsilon : ℝ, ∃ handle : PolynomialHandle,
      0 < C_epsilon ∧ 0 < c_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        Measurable
          (polyEstimator handle (n := n) (d := d) M) ∧
        (∀ s : Fin n → Obs d,
          polyEstimator handle (n := n) (d := d) M s ∈ Icc (-M) M) ∧
        Measurable (collisionEstimator (n := n) (d := d) M) ∧
        (∀ s : Fin n → Obs d,
          collisionEstimator (n := n) (d := d) M s ∈ Icc (-M) M) ∧
        ((d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
        ∀ P : ModelClass d epsilon M sigma,
          mse P.law
              (polyEstimator handle (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ∧
          mse P.law (collisionEstimator (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2)) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C_epsilon, handle, hC, hbound⟩ :=
    robust_upper_construction_resolution_all_d
      epsilon hepsilon hepsilon_half
  refine ⟨C_epsilon, 1, handle,
    hC, zero_lt_one, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two
  have hall := hbound n d M sigma hn hd hM hsigma hsigma_two
  refine ⟨hall.1, hall.2.1, hall.2.2.1, hall.2.2.2.1, ?_⟩
  intro _
  exact hall.2.2.2.2

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
