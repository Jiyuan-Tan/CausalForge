import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularHolder
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularGrid

/-!
# Smoothness-normalized angular amplitude

This module fixes the derivative scale used by the angular hard family and
records both its exact fourth-power budget and the eventual comparison with
the logarithm of the boundary-grid size.
-/

open Filter

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- A fixed choice of a uniform bound for the `j`th derivative of the
normalized packing bump. -/
-- @node: packingBumpDerivativeBound
noncomputable def packingBumpDerivativeBound (j : ℕ) : ℝ :=
  Classical.choose (packingBump_iteratedFDeriv_bound j)

/-- The chosen normalized-bump derivative bound is nonnegative. -/
-- @node: packingBumpDerivativeBound_nonneg
lemma packingBumpDerivativeBound_nonneg (j : ℕ) :
    0 ≤ packingBumpDerivativeBound j :=
  (Classical.choose_spec (packingBump_iteratedFDeriv_bound j)).1

/-- The chosen constant bounds the corresponding normalized-bump derivative
at every score. -/
-- @node: packingBump_iteratedFDeriv_le_derivativeBound
lemma packingBump_iteratedFDeriv_le_derivativeBound (j : ℕ) (z : Score) :
    ‖iteratedFDeriv ℝ j packingBump z‖ ≤ packingBumpDerivativeBound j :=
  (Classical.choose_spec (packingBump_iteratedFDeriv_bound j)).2 z

/-- A fixed numerical envelope for the construction-specific one-observation
radial KL estimate. -/
-- @node: angularPackingOnePointKLConstant
def angularPackingOnePointKLConstant : ℝ := 1310720

/-- A positive, smoothness-dependent scale dominating all derivative bounds
needed through order `q`, while explicitly absorbing the smoothness order and
the construction-specific one-observation KL envelope. -/
-- @node: packingBumpDerivativeScale
noncomputable def packingBumpDerivativeScale (q : ℕ) : ℝ :=
  1 + (q : ℝ) + 1310720 +
    ∑ j ∈ Finset.range (q + 1), packingBumpDerivativeBound j

/-- The derivative scale is positive. -/
-- @node: packingBumpDerivativeScale_pos
lemma packingBumpDerivativeScale_pos (q : ℕ) :
    0 < packingBumpDerivativeScale q := by
  unfold packingBumpDerivativeScale
  have hsum : 0 ≤ ∑ j ∈ Finset.range (q + 1), packingBumpDerivativeBound j :=
    Finset.sum_nonneg fun j _ => packingBumpDerivativeBound_nonneg j
  linarith

/-- Every derivative bound through order `q` is dominated by the common
smoothness-dependent scale. -/
-- @node: packingBumpDerivativeBound_le_scale
lemma packingBumpDerivativeBound_le_scale {j q : ℕ} (hjq : j ≤ q) :
    packingBumpDerivativeBound j ≤ packingBumpDerivativeScale q := by
  have hjmem : j ∈ Finset.range (q + 1) := Finset.mem_range.mpr (by omega)
  have hjle : packingBumpDerivativeBound j ≤
      ∑ k ∈ Finset.range (q + 1), packingBumpDerivativeBound k :=
    Finset.single_le_sum
      (fun k _ => packingBumpDerivativeBound_nonneg k) hjmem
  unfold packingBumpDerivativeScale
  linarith

/-- The bump amplitude with its smoothness-dependent derivative normalization.
It remains a fixed positive multiple of the paper's frontier rate. -/
-- @node: angularPackingScaledDelta
noncomputable def angularPackingScaledDelta (q n : ℕ) : ℝ :=
  frontierRate n / (1024 * packingBumpDerivativeScale q)

/-- The smoothness-normalized amplitude is an exact fixed positive multiple
of the frontier rate. -/
-- @node: angularPackingScaledDelta_eq_scale_mul_frontierRate
lemma angularPackingScaledDelta_eq_scale_mul_frontierRate (q n : ℕ) :
    angularPackingScaledDelta q n =
      (1 / (1024 * packingBumpDerivativeScale q)) * frontierRate n := by
  unfold angularPackingScaledDelta
  ring

/-- The smoothness-normalized amplitude has the exact fourth-power budget
needed by the one-point radial KL estimate. -/
-- @node: angularPackingScaledDelta_fourth_power
lemma angularPackingScaledDelta_fourth_power (q n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * angularPackingScaledDelta q n ^ 4 =
      Real.log n / (1024 * packingBumpDerivativeScale q) ^ 4 := by
  unfold angularPackingScaledDelta
  rw [div_pow]
  calc
    (n : ℝ) * (frontierRate n ^ 4 /
        (1024 * packingBumpDerivativeScale q) ^ 4) =
        ((n : ℝ) * frontierRate n ^ 4) /
          (1024 * packingBumpDerivativeScale q) ^ 4 := by ring
    _ = _ := by rw [frontierRate_fourth_power n hn]

/-- Any construction-specific one-point KL constant small enough for the
fixed derivative normalization eventually fits under one sixteenth of the
logarithmic grid budget. -/
-- @node: angularPackingScaledDelta_eventually_klBudget
lemma angularPackingScaledDelta_eventually_klBudget
    (q : ℕ) (hq : 1 ≤ q) (C : ℝ)
    (hC : 256 * (q : ℝ) * C ≤
      (1024 * packingBumpDerivativeScale q) ^ 4) :
    ∀ᶠ n in atTop,
      angularGridRadius n q ≤ 1 / 24 →
      (n : ℝ) * (C * angularPackingScaledDelta q n ^ 4) ≤
        (1 / 16 : ℝ) * Real.log (angularGridSize (angularGridRadius n q)) := by
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_pos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) :=
    hlog_atTop.eventually_gt_atTop 0
  have hloglog_bound : ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
    filter_upwards [hlog_atTop.eventually_ge_atTop 16, hlog_pos] with n hnlog hnlogpos
    have hnlog0 : 0 ≤ Real.log (n : ℝ) := le_trans (by norm_num) hnlog
    have hbase := Real.log_le_rpow_div hnlog0
      (show (0 : ℝ) < 1 / 2 by norm_num)
    have hsqrt : Real.log (Real.log (n : ℝ)) ≤
        2 * Real.sqrt (Real.log (n : ℝ)) := by
      simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using hbase
    have hfour : 4 ≤ Real.sqrt (Real.log (n : ℝ)) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
      apply Real.sqrt_le_sqrt
      norm_num
      exact hnlog
    nlinarith [Real.sq_sqrt hnlog0]
  have hconst : ∀ᶠ n : ℕ in atTop,
      2 * Real.log 24 ≤
        (1 / (256 * (q : ℝ))) * Real.log (n : ℝ) := by
    have hcoef : 0 < (1 / (256 * (q : ℝ)) : ℝ) := by positivity
    exact (hlog_atTop.const_mul_atTop hcoef).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (2 : ℕ), hloglog_bound, hconst]
      with n hn hloglog hconstn
  intro hsmall
  have hnreal : (0 : ℝ) < n := by positivity
  have hrate : 0 < frontierRate n := frontierRate_pos hn
  have hqreal : (0 : ℝ) < q := by positivity
  have hMlow := angularGridSize_frontier_lower n q hn hsmall
  have hlowpos : 0 < (1 / 24 : ℝ) *
      Real.rpow (frontierRate n) (-(1 : ℝ) / q) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hrate _)
  have hlogM := Real.log_le_log hlowpos hMlow
  rw [show Real.log ((1 / 24 : ℝ) *
      Real.rpow (frontierRate n) (-(1 : ℝ) / q)) =
      Real.log (1 / 24 : ℝ) +
        Real.log (Real.rpow (frontierRate n) (-(1 : ℝ) / q)) by
      exact Real.log_mul (by norm_num)
        (ne_of_gt (Real.rpow_pos_of_pos hrate _))] at hlogM
  rw [show Real.log (Real.rpow (frontierRate n) (-(1 : ℝ) / q)) =
      (-(1 : ℝ) / q) * Real.log (frontierRate n) by
        exact Real.log_rpow hrate _] at hlogM
  have hlograte : Real.log (frontierRate n) =
      (1 / 4 : ℝ) * (Real.log (Real.log n) - Real.log n) := by
    unfold frontierRate
    have hn1r : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1r
    rw [show Real.log (Real.rpow (Real.log n / n) (1 / 4 : ℝ)) =
        (1 / 4 : ℝ) * Real.log (Real.log n / n) by
          exact Real.log_rpow (div_pos hlogn hnreal) _]
    rw [Real.log_div hlogn.ne' hnreal.ne']
  rw [hlograte] at hlogM
  have hlog24 : Real.log (1 / 24 : ℝ) = -Real.log 24 := by
    rw [one_div, Real.log_inv]
  rw [hlog24] at hlogM
  rw [show (n : ℝ) * (C * angularPackingScaledDelta q n ^ 4) =
      C * ((n : ℝ) * angularPackingScaledDelta q n ^ 4) by ring,
    angularPackingScaledDelta_fourth_power q n hn]
  have htarget :
      C * (Real.log n / (1024 * packingBumpDerivativeScale q) ^ 4) ≤
        (1 / 16 : ℝ) *
          (-Real.log 24 + (1 / (8 * (q : ℝ))) * Real.log n) := by
    have hKpos : 0 < (1024 * packingBumpDerivativeScale q) ^ 4 :=
      pow_pos (mul_pos (by norm_num) (packingBumpDerivativeScale_pos q)) _
    have hcoef : C / (1024 * packingBumpDerivativeScale q) ^ 4 ≤
        1 / (256 * (q : ℝ)) := by
      apply (div_le_iff₀ hKpos).2
      rw [one_div, inv_mul_eq_div]
      apply (le_div_iff₀ (mul_pos (by norm_num) hqreal)).2
      calc
        C * (256 * (q : ℝ)) = 256 * (q : ℝ) * C := by ring
        _ ≤ _ := hC
    have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    rw [show C * (Real.log n / (1024 * packingBumpDerivativeScale q) ^ 4) =
        (C / (1024 * packingBumpDerivativeScale q) ^ 4) * Real.log n by ring]
    have hp := mul_le_mul_of_nonneg_right hcoef hlogn0
    calc
      _ ≤ (1 / (256 * (q : ℝ))) * Real.log n := hp
      _ ≤ (1 / 16 : ℝ) *
          (-Real.log 24 + (1 / (8 * (q : ℝ))) * Real.log n) := by
        have hid : (1 / (8 * (q : ℝ))) * Real.log n =
            32 * ((1 / (256 * (q : ℝ))) * Real.log n) := by field_simp; ring
        rw [hid]
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 24)]
  have hlogM' : -Real.log 24 + (1 / (8 * (q : ℝ))) * Real.log n ≤
      Real.log (angularGridSize (angularGridRadius n q)) := by
    have hterm : (1 / (8 * (q : ℝ))) * Real.log n ≤
        (-1 / (q : ℝ)) *
          ((1 / 4 : ℝ) * (Real.log (Real.log n) - Real.log n)) := by
      rw [show (1 / (8 * (q : ℝ))) * Real.log n =
          ((1 / 8 : ℝ) * Real.log n) / q by ring,
        show (-1 / (q : ℝ)) * ((1 / 4 : ℝ) *
            (Real.log (Real.log n) - Real.log n)) =
          (-(1 / 4 : ℝ) * (Real.log (Real.log n) - Real.log n)) / q by ring]
      exact (div_le_div_iff_of_pos_right hqreal).2 (by linarith)
    have hadd := add_le_add_left hterm (-Real.log 24)
    have hadd' : -Real.log 24 + (1 / (8 * (q : ℝ))) * Real.log n ≤
        -Real.log 24 + (-1 / (q : ℝ)) *
          ((1 / 4 : ℝ) * (Real.log (Real.log n) - Real.log n)) := by
      simpa [add_comm] using hadd
    exact hadd'.trans hlogM
  exact htarget.trans (mul_le_mul_of_nonneg_left hlogM' (by norm_num))

end CausalSmith.Stat.BddUniformLogPenalty
