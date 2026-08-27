import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmConcentrationEnvelope
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmLogCalibration
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmFuzzyReduction

/-!
# Final scalar calibration for the one-arm converse
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The explicit Jordan separation used by the shifted finite-grid priors. -/
noncomputable def oneArmShiftedJordanGap (κ : ℝ) : ℝ :=
  (2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))) / 10

/-- For a shift parameter `κ` between zero and one, the explicit Jordan separation
is at least `κ² / 120`.  This clean polynomial lower bound is what the downstream
rate accounting uses in place of the exact rational expression. -/
lemma oneArmShiftedJordanGap_lower {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    κ ^ 2 / 120 ≤ oneArmShiftedJordanGap κ := by
  have hdenpos : 0 < (1 + κ) * (2 + κ) * (3 + κ) := by positivity
  have hdenle : (1 + κ) * (2 + κ) * (3 + κ) ≤ 24 := by
    have h1 : 1 + κ ≤ 2 := by linarith
    have h2 : 2 + κ ≤ 3 := by linarith
    have h3 : 3 + κ ≤ 4 := by linarith
    calc
      (1 + κ) * (2 + κ) * (3 + κ) ≤ 2 * 3 * 4 := by gcongr <;> linarith
      _ = 24 := by norm_num
  unfold oneArmShiftedJordanGap
  have hden5 : 5 * ((1 + κ) * (2 + κ) * (3 + κ)) ≤ 120 := by linarith
  calc
    κ ^ 2 / 120 ≤ κ ^ 2 /
        (5 * ((1 + κ) * (2 + κ) * (3 + κ))) :=
      div_le_div_of_nonneg_left (sq_nonneg κ) (by positivity) hden5
    _ = (2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ))) / 10 := by
      field_simp
      <;> ring

/-- One active coordinate contributes at least this calibrated functional
separation. -/
lemma oneArmCalibratedSignal_lower {n D : ℕ} {κ : ℝ}
    (hn : 0 < n) (hD : 1 ≤ D) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    κ ^ 7 / (153600000000000 * (n : ℝ) * (D : ℝ)) ≤
      ((D : ℝ) / (128 * (n : ℝ))) * oneArmShiftedPoleScale κ D *
        oneArmShiftedJordanGap κ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hD))
  have hscale : 0 ≤ (D : ℝ) / (128 * (n : ℝ)) := by positivity
  have hpole : 0 ≤ oneArmShiftedPoleScale κ D :=
    (oneArmShiftedPoleScale_pos hκ hD).le
  calc
    κ ^ 7 / (153600000000000 * (n : ℝ) * (D : ℝ)) =
        ((D : ℝ) / (128 * (n : ℝ))) * oneArmShiftedPoleScale κ D *
          (κ ^ 2 / 120) := by
      unfold oneArmShiftedPoleScale oneArmShiftedNodeScale
      field_simp [hnR, hDR]
      ring
    _ ≤ ((D : ℝ) / (128 * (n : ℝ))) * oneArmShiftedPoleScale κ D *
          oneArmShiftedJordanGap κ :=
      mul_le_mul_of_nonneg_left (oneArmShiftedJordanGap_lower hκ hκ1)
        (mul_nonneg hscale hpole)

/-- The fixed D.2 numerical accounting used after choosing functional radius
`Δ/8`, testing threshold `Δ/2`, and conditioned TV at most `1/4`. -/
lemma oneArmD2_numeric_budget {Δ tail : ℝ} (hΔ : 0 ≤ Δ)
    (htail : tail ≤ Δ ^ 2 / 32) :
    Δ ^ 2 / 64 ≤
      (((Δ / 2) ^ 2 * ((1 - (1 / 4 : ℝ)) / 2)) -
          2 * (Δ / 8) ^ 2 - tail) / 2 := by
  nlinarith [sq_nonneg Δ]

/-- Calibrated D.2 transfer once the two conditioned count risks and the
Poisson-tail term have been established. -/
lemma oneArmCalibratedD2_lower
    {Δ tail risk₀ risk₁ fixed : ℝ} (hΔ : 0 ≤ Δ)
    (htail : tail ≤ Δ ^ 2 / 32)
    (htest : (Δ / 2) ^ 2 * ((1 - (1 / 4 : ℝ)) / 2) ≤ max risk₀ risk₁)
    (hrisk₀ : risk₀ ≤ 2 * fixed + 2 * (Δ / 8) ^ 2 + tail)
    (hrisk₁ : risk₁ ≤ 2 * fixed + 2 * (Δ / 8) ^ 2 + tail) :
    Δ ^ 2 / 64 ≤ fixed := by
  exact (oneArmD2_numeric_budget hΔ htail).trans
    (d2_fixedRisk_lower_of_countRisk_bounds htest hrisk₀ hrisk₁)

/-- Replace the calibrated degree by `20 log n` in the final squared signal.
This is the last scalar step from the D.2 output to the dimensional summand. -/
lemma oneArmHighDimensional_rate_of_calibrated_signal
    {n d D : ℕ} {κ risk : ℝ} (hn : 0 < n) (hlog : 0 < Real.log n)
    (hDnat : 1 ≤ D)
    (hD : (D : ℝ) ≤ 20 * Real.log n)
    (hsignal :
      (((d : ℝ) * κ ^ 7 /
        (153600000000000 * (n : ℝ) * (D : ℝ))) ^ 2) / 64 ≤ risk) :
    (κ ^ 14 / (25600 * (153600000000000 : ℝ) ^ 2)) *
        ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) ≤ risk := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDR : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hDnat)
  have hκ14 : 0 ≤ κ ^ 14 := by positivity
  have hcompare :
      (κ ^ 14 / (25600 * (153600000000000 : ℝ) ^ 2)) *
          ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) ≤
        (((d : ℝ) * κ ^ 7 /
          (153600000000000 * (n : ℝ) * (D : ℝ))) ^ 2) / 64 := by
    have hDsq : (D : ℝ) ^ 2 ≤ 400 * (Real.log n) ^ 2 := by nlinarith
    have hκpow : κ ^ 14 = (κ ^ 7) ^ 2 := by ring
    rw [hκpow]
    field_simp
    nlinarith [sq_nonneg (d : ℝ), sq_nonneg (κ ^ 7),
      mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg (κ ^ 7))]
  exact hcompare.trans hsignal

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
