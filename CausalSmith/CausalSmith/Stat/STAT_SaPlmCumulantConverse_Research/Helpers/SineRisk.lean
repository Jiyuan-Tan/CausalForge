import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.UniformDiskSeries

/-! # Generic clipped sine-ratio risk reductions -/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- The clipped ratio estimator built from two per-observation scores: average
the denominator score and the remainder score over the sample; if the average
denominator reaches the threshold, return the ratio of the target value times the
average denominator plus the average remainder to the average denominator,
truncated to the symmetric interval given by the clipping bound; otherwise return
zero.

The threshold is a denominator-safety device: below it the estimator refuses to
divide and reports zero. -/
def clippedRatioFromScores {Ω : Type*} (Ctheta theta : ℝ) (n : ℕ)
    (threshold : ℝ) (W R : Ω → ℝ) (data : Fin n → Ω) : ℝ :=
  let den := (n : ℝ)⁻¹ * ∑ i, W (data i)
  let rem := (n : ℝ)⁻¹ * ∑ i, R (data i)
  if threshold ≤ den then
    min (max ((theta * den + rem) / den) (-Ctheta)) Ctheta
  else 0

/-- With [at least one observation](hyp:hn), a [target value inside the clipping
bound](hyp:htheta), a [strictly positive denominator level](hyp:hA) and a
[population denominator mean of at least half that level](hyp:hmu), the [squared
error of the clipped ratio estimator run at a threshold of one quarter of the
level is at most sixteen over the squared level, times the sum of the squared
sample average of the remainder scores and the squared clipping bound times the
squared sample average of the centered denominator scores](goal).

The bound holds pathwise, on every sample: the branch where the threshold fails
is absorbed because the denominator must then be far from its population mean. -/
lemma clippedRatioFromScores_sq_le {Ω : Type*} (Ctheta theta A : ℝ)
    (n : ℕ) (W R : Ω → ℝ) (muW : ℝ)
    (hn : 0 < n) (htheta : |theta| ≤ Ctheta) (hA : 0 < A) (hmu : A / 2 ≤ muW)
    (data : Fin n → Ω) :
    (clippedRatioFromScores Ctheta theta n (A / 4) W R data - theta) ^ 2 ≤
      16 / A ^ 2 *
        (((n : ℝ)⁻¹ * ∑ i, R (data i)) ^ 2 +
          Ctheta ^ 2 * (((n : ℝ)⁻¹ * ∑ i, (W (data i) - muW)) ^ 2)) := by
  let den := (n : ℝ)⁻¹ * ∑ i, W (data i)
  let rem := (n : ℝ)⁻¹ * ∑ i, R (data i)
  have hcenter : (n : ℝ)⁻¹ * ∑ i, (W (data i) - muW) = den - muW := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul]
    dsimp [den]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  rw [hcenter]
  unfold clippedRatioFromScores
  dsimp only
  split_ifs with hgood
  · have hden : 0 < den := lt_of_lt_of_le (by positivity : 0 < A / 4) hgood
    have hclip : |min (max ((theta * den + rem) / den) (-Ctheta)) Ctheta - theta| ≤
        |((theta * den + rem) / den) - theta| := by
      have hθclip : min (max theta (-Ctheta)) Ctheta = theta := by
        rw [max_eq_left]
        · exact min_eq_left (le_trans (le_abs_self theta) htheta)
        · linarith [neg_le_of_abs_le htheta]
      calc
        _ = |min (max ((theta * den + rem) / den) (-Ctheta)) Ctheta -
            min (max theta (-Ctheta)) Ctheta| := by rw [hθclip]
        _ ≤ max |max ((theta * den + rem) / den) (-Ctheta) -
            max theta (-Ctheta)| |Ctheta - Ctheta| :=
          abs_min_sub_min_le_max _ _ _ _
        _ ≤ |((theta * den + rem) / den) - theta| := by
          simp only [sub_self, abs_zero, max_le_iff]
          exact ⟨(abs_max_sub_max_le_max _ _ _ _).trans (by simp), abs_nonneg _⟩
    have hratio : ((theta * den + rem) / den) - theta = rem / den := by
      field_simp [hden.ne']
      ring
    have hsquare := sq_le_sq₀ (abs_nonneg _) (abs_nonneg _) |>.2 hclip
    rw [sq_abs, sq_abs, hratio] at hsquare
    calc
      _ ≤ (rem / den) ^ 2 := hsquare
      _ ≤ 16 / A ^ 2 * rem ^ 2 := by
        rw [div_pow]
        have hdenSq : (A / 4) ^ 2 ≤ den ^ 2 :=
          sq_le_sq₀ (by positivity) hden.le |>.2 hgood
        have hd2 : 0 < den ^ 2 := sq_pos_of_pos hden
        rw [div_le_iff₀ hd2]
        field_simp [hA.ne']
        nlinarith [sq_nonneg rem]
      _ ≤ 16 / A ^ 2 * (rem ^ 2 + Ctheta ^ 2 * (den - muW) ^ 2) := by
        have hc : 0 ≤ 16 / A ^ 2 := by positivity
        have hp : 0 ≤ Ctheta ^ 2 * (den - muW) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        nlinarith
  · have hbad : den < A / 4 := lt_of_not_ge hgood
    have hdev : A / 4 ≤ muW - den := by linarith
    have hC : 0 ≤ Ctheta := (abs_nonneg theta).trans htheta
    have hthetaSq : theta ^ 2 ≤ Ctheta ^ 2 := by
      have hu : theta ≤ Ctheta := (le_abs_self theta).trans htheta
      have hl : -Ctheta ≤ theta := by linarith [neg_le_of_abs_le htheta]
      nlinarith
    have hfail : Ctheta ^ 2 ≤ 16 / A ^ 2 *
        (Ctheta ^ 2 * (den - muW) ^ 2) := by
      field_simp [hA.ne']
      have hsq : A ^ 2 ≤ 16 * (den - muW) ^ 2 := by
        nlinarith [sq_nonneg (4 * (muW - den) - A)]
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg Ctheta)]
    calc
      (0 - theta) ^ 2 = theta ^ 2 := by ring
      _ ≤ Ctheta ^ 2 := hthetaSq
      _ ≤ 16 / A ^ 2 * (Ctheta ^ 2 * (den - muW) ^ 2) := hfail
      _ ≤ 16 / A ^ 2 * (rem ^ 2 + Ctheta ^ 2 * (den - muW) ^ 2) := by
        have hc : 0 ≤ 16 / A ^ 2 := by positivity
        nlinarith [sq_nonneg rem]

/-- Whenever the [target value lies inside the clipping bound](hyp:htheta), the
[squared error of the clipped ratio estimator never exceeds four times the
squared clipping bound](goal), on every sample and whatever the denominator
level. This is the crude fallback used where the sharp bound is unavailable. -/
lemma clippedRatioFromScores_sq_le_global {Ω : Type*} (Ctheta theta A : ℝ)
    (n : ℕ) (W R : Ω → ℝ) (muW : ℝ)
    (htheta : |theta| ≤ Ctheta) (data : Fin n → Ω) :
    (clippedRatioFromScores Ctheta theta n (A / 4) W R data - theta) ^ 2 ≤
      4 * Ctheta ^ 2 := by
  have hC : 0 ≤ Ctheta := (abs_nonneg theta).trans htheta
  unfold clippedRatioFromScores
  dsimp only
  split_ifs
  · have hlo : -Ctheta ≤ min
        (max ((theta * ((n : ℝ)⁻¹ * ∑ i, W (data i)) +
          (n : ℝ)⁻¹ * ∑ i, R (data i)) /
          ((n : ℝ)⁻¹ * ∑ i, W (data i))) (-Ctheta)) Ctheta :=
      le_min (le_trans (le_max_right _ _) (le_refl _)) (by linarith)
    have hhi : min
        (max ((theta * ((n : ℝ)⁻¹ * ∑ i, W (data i)) +
          (n : ℝ)⁻¹ * ∑ i, R (data i)) /
          ((n : ℝ)⁻¹ * ∑ i, W (data i))) (-Ctheta)) Ctheta ≤ Ctheta := min_le_right _ _
    have htlo : -Ctheta ≤ theta := by linarith [neg_le_of_abs_le htheta]
    have hthi : theta ≤ Ctheta := (le_abs_self theta).trans htheta
    nlinarith [sq_nonneg (min
      (max ((theta * ((n : ℝ)⁻¹ * ∑ i, W (data i)) +
        (n : ℝ)⁻¹ * ∑ i, R (data i)) /
        ((n : ℝ)⁻¹ * ∑ i, W (data i))) (-Ctheta)) Ctheta - theta)]
  · have ht : theta ^ 2 ≤ Ctheta ^ 2 := by
      have htlo : -Ctheta ≤ theta := by linarith [neg_le_of_abs_le htheta]
      have hthi : theta ≤ Ctheta := (le_abs_self theta).trans htheta
      nlinarith
    nlinarith

/-- For an independent sample of [size at least one](hyp:hn) from a probability
law, with a [target value inside the clipping bound](hyp:htheta), a [strictly
positive denominator level](hyp:hA) and a [population denominator mean of at
least half that level](hyp:hmu), and with [measurable](hyp:hWmeas,hRmeas) and
[square-integrable](hyp:hW,hR) denominator and remainder scores whose
[population means are that denominator mean and zero respectively](hyp:hWmean,hRmean),
the [expected squared error of the clipped ratio estimator run at a threshold of
one quarter of the level is at most sixteen over the squared level, divided by
the sample size, times the sum of the second moment of the remainder score and
the squared clipping bound times the second moment of the denominator
score](goal).

This is the sample-average version of the pathwise bound: averaging independent
centered scores contributes the usual one-over-sample-size factor. -/
lemma clippedRatioFromScores_lintegral_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Ctheta theta A : ℝ) (n : ℕ) (W R : Ω → ℝ) (muW : ℝ)
    (hn : 0 < n) (htheta : |theta| ≤ Ctheta) (hA : 0 < A) (hmu : A / 2 ≤ muW)
    (hWmeas : Measurable W) (hRmeas : Measurable R)
    (hW : MemLp W 2 P) (hR : MemLp R 2 P)
    (hWmean : ∫ o, W o ∂P = muW) (hRmean : ∫ o, R o ∂P = 0) :
    ∫⁻ data : Fin n → Ω, ENNReal.ofReal
      ((clippedRatioFromScores Ctheta theta n (A / 4) W R data - theta) ^ 2)
        ∂Measure.pi (fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (16 / A ^ 2) * (n : ENNReal)⁻¹ *
        (ENNReal.ofReal ((eLpNorm R 2 P).toReal ^ 2) +
          ENNReal.ofReal (Ctheta ^ 2) *
            ENNReal.ofReal ((eLpNorm W 2 P).toReal ^ 2)) := by
  let rbar : (Fin n → Ω) → ℝ := fun data ↦
    (n : ℝ)⁻¹ * ∑ i, (R (data i) - ∫ o, R o ∂P)
  let wbar : (Fin n → Ω) → ℝ := fun data ↦
    (n : ℝ)⁻¹ * ∑ i, (W (data i) - ∫ o, W o ∂P)
  have hr := pi_centered_average_sq_lintegral_le
    (ι := Fin n) (P := P) (by simpa using hn) hR
  have hw := pi_centered_average_sq_lintegral_le
    (ι := Fin n) (P := P) (by simpa using hn) hW
  have hrbarMeas : Measurable rbar := by
    dsimp [rbar]
    fun_prop
  have hwbarMeas : Measurable wbar := by
    dsimp [wbar]
    fun_prop
  have hpoint : ∀ data : Fin n → Ω,
      ENNReal.ofReal
        ((clippedRatioFromScores Ctheta theta n (A / 4) W R data - theta) ^ 2) ≤
      ENNReal.ofReal (16 / A ^ 2) *
        (ENNReal.ofReal (rbar data ^ 2) +
          ENNReal.ofReal (Ctheta ^ 2) * ENNReal.ofReal (wbar data ^ 2)) := by
    intro data
    apply (ENNReal.ofReal_le_ofReal
      (clippedRatioFromScores_sq_le Ctheta theta A n W R muW hn htheta hA hmu data)).trans_eq
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 16 / A ^ 2)]
    rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [ENNReal.ofReal_mul (sq_nonneg Ctheta)]
    simp only [rbar, wbar, hRmean, hWmean, sub_zero]
  refine (lintegral_mono hpoint).trans ?_
  rw [lintegral_const_mul'']
  rw [lintegral_add_left (hrbarMeas.pow_const 2).ennreal_ofReal]
  rw [lintegral_const_mul'']
  calc
    ENNReal.ofReal (16 / A ^ 2) *
        ((∫⁻ data, ENNReal.ofReal (rbar data ^ 2)
            ∂Measure.pi (fun _ : Fin n ↦ P)) +
          ENNReal.ofReal (Ctheta ^ 2) *
            ∫⁻ data, ENNReal.ofReal (wbar data ^ 2)
              ∂Measure.pi (fun _ : Fin n ↦ P)) ≤
      ENNReal.ofReal (16 / A ^ 2) *
        ((n : ENNReal)⁻¹ * ENNReal.ofReal ((eLpNorm R 2 P).toReal ^ 2) +
          ENNReal.ofReal (Ctheta ^ 2) *
            ((n : ENNReal)⁻¹ * ENNReal.ofReal ((eLpNorm W 2 P).toReal ^ 2))) := by
      apply mul_le_mul_right
      apply add_le_add
      · simpa [rbar, Fintype.card_fin] using hr
      · apply mul_le_mul_right
        simpa [wbar, Fintype.card_fin] using hw
    _ = _ := by ring
  all_goals fun_prop

end CausalSmith.Stat.SaPlmCumulantConverse
