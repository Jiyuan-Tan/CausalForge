import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmApproximation

/-!
# Shifted-pole three-point obstruction

The rational pole may be a positive fraction `κ` of the smallest grid node.
This is the version needed for every overlap level below one half.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The nuisance reciprocal term cancels at `a,2a,3a`; a pole at `κa`
leaves the strictly positive signal `2κ²/((1+κ)(2+κ)(3+κ))`. -/
lemma oneArm_shifted_rational_three_point_identity
    {a κ alpha : ℝ} (ha : a ≠ 0)
    (hκ1 : 1 + κ ≠ 0) (hκ2 : 2 + κ ≠ 0) (hκ3 : 3 + κ ≠ 0) :
    (a / (a + κ * a) + alpha / a)
      - 4 * ((2 * a) / (2 * a + κ * a) + alpha / (2 * a))
      + 3 * ((3 * a) / (3 * a + κ * a) + alpha / (3 * a)) =
        2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ)) := by
  field_simp [ha, hκ1, hκ2, hκ3]
  ring

/-- Pointwise approximation at the first three grid nodes and small local
oscillation must pay at least the shifted-pole signal. -/
lemma oneArm_shifted_rational_three_point_obstruction
    {a κ alpha e V : ℝ} (ha : a ≠ 0)
    (hκ1 : 1 + κ ≠ 0) (hκ2 : 2 + κ ≠ 0) (hκ3 : 3 + κ ≠ 0)
    (hκ : 0 ≤ κ) (P : ℝ → ℝ)
    (h₁ : |a / (a + κ * a) + alpha / a - P a| ≤ e)
    (h₂ : |(2 * a) / (2 * a + κ * a) + alpha / (2 * a) - P (2 * a)| ≤ e)
    (h₃ : |(3 * a) / (3 * a + κ * a) + alpha / (3 * a) - P (3 * a)| ≤ e)
    (h₁₂ : |P a - P (2 * a)| ≤ V)
    (h₃₂ : |P (3 * a) - P (2 * a)| ≤ V) :
    2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ)) ≤ 8 * e + 4 * V := by
  let f : ℝ → ℝ := fun x => x / (x + κ * a) + alpha / x
  have hid : f a - 4 * f (2 * a) + 3 * f (3 * a) =
      2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ)) := by
    simpa [f] using
      oneArm_shifted_rational_three_point_identity ha hκ1 hκ2 hκ3
  have herr :
      |(f a - P a) - 4 * (f (2 * a) - P (2 * a))
          + 3 * (f (3 * a) - P (3 * a))| ≤ 8 * e := by
    have htri := abs_add_three (f a - P a)
      (-4 * (f (2 * a) - P (2 * a)))
      (3 * (f (3 * a) - P (3 * a)))
    norm_num [abs_mul] at htri
    have hf₁ : |f a - P a| ≤ e := by simpa [f] using h₁
    have hf₂ : |f (2 * a) - P (2 * a)| ≤ e := by simpa [f] using h₂
    have hf₃ : |f (3 * a) - P (3 * a)| ≤ e := by simpa [f] using h₃
    have htri' :
        |(f a - P a) - 4 * (f (2 * a) - P (2 * a))
          + 3 * (f (3 * a) - P (3 * a))| ≤
          |f a - P a| + 4 * |f (2 * a) - P (2 * a)|
            + 3 * |f (3 * a) - P (3 * a)| := by
      simpa [sub_eq_add_neg] using htri
    nlinarith
  have hP : |P a - 4 * P (2 * a) + 3 * P (3 * a)| ≤ 4 * V := by
    have hrewrite : P a - 4 * P (2 * a) + 3 * P (3 * a) =
        (P a - P (2 * a)) + 3 * (P (3 * a) - P (2 * a)) := by ring
    rw [hrewrite]
    have htri := abs_add_le (P a - P (2 * a))
      (3 * (P (3 * a) - P (2 * a)))
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at htri
    nlinarith
  have hsplit : f a - 4 * f (2 * a) + 3 * f (3 * a) =
      ((f a - P a) - 4 * (f (2 * a) - P (2 * a))
        + 3 * (f (3 * a) - P (3 * a)))
      + (P a - 4 * P (2 * a) + 3 * P (3 * a)) := by ring
  have hsignal : 0 ≤
      2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ)) := by positivity
  rw [hsplit] at hid
  have habs : 2 * κ ^ 2 / ((1 + κ) * (2 + κ) * (3 + κ)) ≤
      |((f a - P a) - 4 * (f (2 * a) - P (2 * a))
        + 3 * (f (3 * a) - P (3 * a)))
        + (P a - 4 * P (2 * a) + 3 * P (3 * a))| := by
    calc
      _ = ((f a - P a) - 4 * (f (2 * a) - P (2 * a))
          + 3 * (f (3 * a) - P (3 * a)))
          + (P a - 4 * P (2 * a) + 3 * P (3 * a)) := hid.symm
      _ ≤ |((f a - P a) - 4 * (f (2 * a) - P (2 * a))
          + 3 * (f (3 * a) - P (3 * a)))
          + (P a - 4 * P (2 * a) + 3 * P (3 * a))| := le_abs_self _
  exact habs.trans ((abs_add_le _ _).trans (add_le_add herr hP))

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
