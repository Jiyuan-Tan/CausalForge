import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Independent-Poisson usable-occupancy bounds

This module isolates the deterministic light/heavy aggregation used in the
Laplace-transform argument for usable Poisson occupancies.  A light cell pays
quadratically in its intensity, while a heavy cell pays linearly.  The result
combines these local estimates into the birthday-scale exponent
`n^2 / max n d` with explicit conservative constants.
-/

namespace CausalSmith.Mathlib.Probability

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- The Poisson probability-generating identity at `exp (-1)`, derived
directly from Mathlib's Poisson integral formula. -/
theorem integral_exp_neg_nat_poissonMeasure (r : NNReal) :
    (∫ m : ℕ, Real.exp (-(m : ℝ)) ∂poissonMeasure r) =
      Real.exp (-(1 - Real.exp (-1)) * (r : ℝ)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    ∑' m : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ) ^ m / Nat.factorial m *
          Real.exp (-(m : ℝ)) =
        Real.exp (-(r : ℝ)) *
          ∑' m : ℕ, (((r : ℝ) * Real.exp (-1)) ^ m / Nat.factorial m) := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro m
            rw [show -(m : ℝ) = (m : ℝ) * (-1) by ring, Real.exp_nat_mul]
            ring
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * Real.exp (-1)) := by
      have hseries := (NormedSpace.expSeries_div_hasSum_exp
        ((r : ℝ) * Real.exp (-1))).tsum_eq
      rw [← Real.exp_eq_exp_ℝ] at hseries
      rw [hseries]
    _ = Real.exp (-(1 - Real.exp (-1)) * (r : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The zero atom of a Poisson law, written as an integral for later product
factorizations. -/
theorem integral_poissonZeroIndicator (r : NNReal) :
    (∫ m : ℕ, (if m = 0 then (1 : ℝ) else 0) ∂poissonMeasure r) =
      Real.exp (-(r : ℝ)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [tsum_eq_single 0]
  · norm_num
  · intro m hm
    simp [hm]

/-- The one atom of a Poisson law, in real-valued integral form. -/
theorem integral_poissonOneIndicator (r : NNReal) :
    (∫ m : ℕ, (if m = 1 then (1 : ℝ) else 0) ∂poissonMeasure r) =
      Real.exp (-(r : ℝ)) * r := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [tsum_eq_single 1]
  · norm_num
  · intro m hm
    simp [hm]

/-- The number of observations in a two-arm cell when both arms occur, and
zero otherwise. -/
def poissonUsableCellCount (z : ℕ × ℕ) : ℕ :=
  if 0 < z.1 ∧ 0 < z.2 then z.1 + z.2 else 0

/-- The Laplace factor at parameter one for a cell whose two arm counts are
independent Poisson variables. -/
noncomputable def poissonUsableCellLaplace (mu0 mu1 : NNReal) : ℝ :=
  ∫ z : ℕ × ℕ, Real.exp (-(poissonUsableCellCount z : ℝ))
    ∂(poissonMeasure mu0).prod (poissonMeasure mu1)

/-- Pointwise heavy-cell envelope: on a usable cell the first term is exact;
on an unusable cell one of the two indicators pays for the value one. -/
theorem exp_neg_poissonUsableCellCount_le_heavyEnvelope (z : ℕ × ℕ) :
    Real.exp (-(poissonUsableCellCount z : ℝ)) ≤
      Real.exp (-((z.1 : ℝ) + z.2)) +
        (if z.1 = 0 then 1 else 0) + (if z.2 = 0 then 1 else 0) := by
  rcases z with ⟨m, j⟩
  by_cases hm : m = 0
  · subst m
    simp only [poissonUsableCellCount, lt_self_iff_false, false_and, ↓reduceIte,
      Nat.cast_zero, neg_zero, Real.exp_zero, ↓reduceIte]
    have hexp : 0 ≤ Real.exp (-((0 : ℝ) + j)) := (Real.exp_pos _).le
    split <;> linarith
  by_cases hj : j = 0
  · subst j
    simp only [poissonUsableCellCount, lt_self_iff_false, and_false, ↓reduceIte,
      Nat.cast_zero, add_zero, neg_zero, Real.exp_zero, hm, ↓reduceIte]
    have hexp : 0 ≤ Real.exp (-(m : ℝ)) := (Real.exp_pos _).le
    linarith
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj
  simp [poissonUsableCellCount, hm, hj, hmpos, hjpos]

/-- Pointwise light-cell envelope obtained by retaining only the atom with
exactly one observation in each arm. -/
theorem exp_neg_poissonUsableCellCount_le_lightEnvelope (z : ℕ × ℕ) :
    Real.exp (-(poissonUsableCellCount z : ℝ)) ≤
      1 - (1 - Real.exp (-2)) * (if z = (1, 1) then 1 else 0) := by
  by_cases hz : z = (1, 1)
  · subst z
    norm_num [poissonUsableCellCount]
  · rw [if_neg hz, mul_zero, sub_zero]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

private theorem integrable_exp_neg_poissonUsableCellCount (mu0 mu1 : NNReal) :
    Integrable (fun z : ℕ × ℕ ↦ Real.exp (-(poissonUsableCellCount z : ℝ)))
      ((poissonMeasure mu0).prod (poissonMeasure mu1)) := by
  refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

private theorem integrable_exp_neg_pairSum (mu0 mu1 : NNReal) :
    Integrable (fun z : ℕ × ℕ ↦ Real.exp (-((z.1 : ℝ) + z.2)))
      ((poissonMeasure mu0).prod (poissonMeasure mu1)) := by
  refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem integrable_firstZeroIndicator (mu0 mu1 : NNReal) :
    Integrable (fun z : ℕ × ℕ ↦ if z.1 = 0 then (1 : ℝ) else 0)
      ((poissonMeasure mu0).prod (poissonMeasure mu1)) := by
  refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
  filter_upwards with z
  split <;> simp

private theorem integrable_secondZeroIndicator (mu0 mu1 : NNReal) :
    Integrable (fun z : ℕ × ℕ ↦ if z.2 = 0 then (1 : ℝ) else 0)
      ((poissonMeasure mu0).prod (poissonMeasure mu1)) := by
  refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
  filter_upwards with z
  split <;> simp

private theorem integrable_pairOneIndicator (mu0 mu1 : NNReal) :
    Integrable (fun z : ℕ × ℕ ↦ if z = (1, 1) then (1 : ℝ) else 0)
      ((poissonMeasure mu0).prod (poissonMeasure mu1)) := by
  refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
  filter_upwards with z
  split <;> simp

/-- Integrating the heavy pointwise envelope gives three explicit exponential
terms.  This is the local independent-Poisson PGF bound. -/
theorem poissonUsableCellLaplace_le_threeExp (mu0 mu1 : NNReal) :
    poissonUsableCellLaplace mu0 mu1 ≤
      Real.exp (-(1 - Real.exp (-1)) * ((mu0 : ℝ) + mu1)) +
        Real.exp (-(mu0 : ℝ)) + Real.exp (-(mu1 : ℝ)) := by
  let μ := (poissonMeasure mu0).prod (poissonMeasure mu1)
  have hExp := integrable_exp_neg_pairSum mu0 mu1
  have hZero0 := integrable_firstZeroIndicator mu0 mu1
  have hZero1 := integrable_secondZeroIndicator mu0 mu1
  have hEnvelope : Integrable (fun z : ℕ × ℕ ↦
      Real.exp (-((z.1 : ℝ) + z.2)) +
        (if z.1 = 0 then 1 else 0) + (if z.2 = 0 then 1 else 0)) μ :=
    (hExp.add hZero0).add hZero1
  have hmono := integral_mono_ae
    (integrable_exp_neg_poissonUsableCellCount mu0 mu1) hEnvelope
    (Filter.Eventually.of_forall exp_neg_poissonUsableCellCount_le_heavyEnvelope)
  have hPair : (∫ z : ℕ × ℕ, Real.exp (-((z.1 : ℝ) + z.2)) ∂μ) =
      Real.exp (-(1 - Real.exp (-1)) * ((mu0 : ℝ) + mu1)) := by
    calc
      (∫ z : ℕ × ℕ, Real.exp (-((z.1 : ℝ) + z.2)) ∂μ) =
          (∫ z : ℕ × ℕ, Real.exp (-(z.1 : ℝ)) * Real.exp (-(z.2 : ℝ)) ∂μ) := by
            congr with z
            rw [← Real.exp_add]
            congr 1
            ring
      _ = (∫ m : ℕ, Real.exp (-(m : ℝ)) ∂poissonMeasure mu0) *
          ∫ j : ℕ, Real.exp (-(j : ℝ)) ∂poissonMeasure mu1 := by
            simpa only [μ] using (integral_prod_mul
              (μ := poissonMeasure mu0) (ν := poissonMeasure mu1) (L := ℝ)
              (fun m : ℕ ↦ Real.exp (-(m : ℝ)))
              (fun j : ℕ ↦ Real.exp (-(j : ℝ))))
      _ = Real.exp (-(1 - Real.exp (-1)) * ((mu0 : ℝ) + mu1)) := by
        rw [integral_exp_neg_nat_poissonMeasure, integral_exp_neg_nat_poissonMeasure,
          ← Real.exp_add]
        congr 1
        ring
  have hFirst : (∫ z : ℕ × ℕ, (if z.1 = 0 then (1 : ℝ) else 0) ∂μ) =
      Real.exp (-(mu0 : ℝ)) := by
    calc
      _ = (∫ m : ℕ, (if m = 0 then (1 : ℝ) else 0) ∂poissonMeasure mu0) *
          ∫ _j : ℕ, (1 : ℝ) ∂poissonMeasure mu1 := by
            simpa using (integral_prod_mul
              (μ := poissonMeasure mu0) (ν := poissonMeasure mu1) (L := ℝ)
              (fun m : ℕ ↦ if m = 0 then (1 : ℝ) else 0) (fun _j : ℕ ↦ (1 : ℝ)))
      _ = _ := by rw [integral_poissonZeroIndicator]; simp
  have hSecond : (∫ z : ℕ × ℕ, (if z.2 = 0 then (1 : ℝ) else 0) ∂μ) =
      Real.exp (-(mu1 : ℝ)) := by
    calc
      _ = (∫ _m : ℕ, (1 : ℝ) ∂poissonMeasure mu0) *
          ∫ j : ℕ, (if j = 0 then (1 : ℝ) else 0) ∂poissonMeasure mu1 := by
            simpa using (integral_prod_mul
              (μ := poissonMeasure mu0) (ν := poissonMeasure mu1) (L := ℝ)
              (fun _m : ℕ ↦ (1 : ℝ)) (fun j : ℕ ↦ if j = 0 then (1 : ℝ) else 0))
      _ = _ := by rw [integral_poissonZeroIndicator]; simp
  unfold poissonUsableCellLaplace
  calc
    _ ≤ ∫ z : ℕ × ℕ, (Real.exp (-((z.1 : ℝ) + z.2)) +
        (if z.1 = 0 then 1 else 0)) + (if z.2 = 0 then 1 else 0) ∂μ := hmono
    _ = _ := by
      dsimp only [μ] at hPair hFirst hSecond ⊢
      have hAdd01 : (∫ z : ℕ × ℕ, Real.exp (-((z.1 : ℝ) + z.2)) +
          (if z.1 = 0 then 1 else 0) ∂(poissonMeasure mu0).prod (poissonMeasure mu1)) =
          (∫ z : ℕ × ℕ, Real.exp (-((z.1 : ℝ) + z.2))
            ∂(poissonMeasure mu0).prod (poissonMeasure mu1)) +
          ∫ z : ℕ × ℕ, (if z.1 = 0 then 1 else 0)
            ∂(poissonMeasure mu0).prod (poissonMeasure mu1) := by
        simpa only [Pi.add_apply] using integral_add hExp hZero0
      have hAddAll : (∫ z : ℕ × ℕ, (Real.exp (-((z.1 : ℝ) + z.2)) +
          (if z.1 = 0 then 1 else 0)) + (if z.2 = 0 then 1 else 0)
            ∂(poissonMeasure mu0).prod (poissonMeasure mu1)) =
          (∫ z : ℕ × ℕ, Real.exp (-((z.1 : ℝ) + z.2)) +
            (if z.1 = 0 then 1 else 0)
              ∂(poissonMeasure mu0).prod (poissonMeasure mu1)) +
          ∫ z : ℕ × ℕ, (if z.2 = 0 then 1 else 0)
            ∂(poissonMeasure mu0).prod (poissonMeasure mu1) := by
        simpa only [Pi.add_apply] using integral_add (hExp.add hZero0) hZero1
      rw [hAddAll, hAdd01, hPair, hFirst, hSecond]

/-- Integrating the light envelope retains the exact `(1,1)` atom of the two
independent Poisson counts. -/
theorem poissonUsableCellLaplace_le_one_sub_atom (mu0 mu1 : NNReal) :
    poissonUsableCellLaplace mu0 mu1 ≤
      1 - (1 - Real.exp (-2)) *
        (Real.exp (-((mu0 : ℝ) + mu1)) * (mu0 : ℝ) * (mu1 : ℝ)) := by
  let μ := (poissonMeasure mu0).prod (poissonMeasure mu1)
  let c : ℝ := 1 - Real.exp (-2)
  let ind : ℕ × ℕ → ℝ := fun z ↦ if z = (1, 1) then 1 else 0
  have hInd := integrable_pairOneIndicator mu0 mu1
  have hEnvelope : Integrable (fun z : ℕ × ℕ ↦ 1 - c * ind z) μ := by
    exact (integrable_const (1 : ℝ)).sub (hInd.const_mul c)
  have hmono := integral_mono_ae
    (integrable_exp_neg_poissonUsableCellCount mu0 mu1) hEnvelope
    (Filter.Eventually.of_forall exp_neg_poissonUsableCellCount_le_lightEnvelope)
  have hAtom : (∫ z : ℕ × ℕ, ind z ∂μ) =
      Real.exp (-((mu0 : ℝ) + mu1)) * (mu0 : ℝ) * (mu1 : ℝ) := by
    calc
      (∫ z : ℕ × ℕ, ind z ∂μ) =
          (∫ z : ℕ × ℕ, (if z.1 = 1 then (1 : ℝ) else 0) *
            (if z.2 = 1 then (1 : ℝ) else 0) ∂μ) := by
              congr with z
              simp only [ind]
              rcases z with ⟨m, j⟩
              simp only [Prod.mk.injEq]
              by_cases hm : m = 1 <;> by_cases hj : j = 1 <;> simp [hm, hj]
      _ = (∫ m : ℕ, (if m = 1 then (1 : ℝ) else 0) ∂poissonMeasure mu0) *
          ∫ j : ℕ, (if j = 1 then (1 : ℝ) else 0) ∂poissonMeasure mu1 := by
            simpa only [μ] using (integral_prod_mul
              (μ := poissonMeasure mu0) (ν := poissonMeasure mu1) (L := ℝ)
              (fun m : ℕ ↦ if m = 1 then (1 : ℝ) else 0)
              (fun j : ℕ ↦ if j = 1 then (1 : ℝ) else 0))
      _ = _ := by
        rw [integral_poissonOneIndicator, integral_poissonOneIndicator]
        calc
          Real.exp (-(mu0 : ℝ)) * (mu0 : ℝ) *
              (Real.exp (-(mu1 : ℝ)) * (mu1 : ℝ)) =
              (Real.exp (-(mu0 : ℝ)) * Real.exp (-(mu1 : ℝ))) *
                (mu0 : ℝ) * (mu1 : ℝ) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring
  unfold poissonUsableCellLaplace
  calc
    _ ≤ ∫ z : ℕ × ℕ, 1 - c * ind z ∂μ := hmono
    _ = 1 - c * ∫ z : ℕ × ℕ, ind z ∂μ := by
      have hmul : (∫ z : ℕ × ℕ, c * ind z ∂μ) =
          c * ∫ z : ℕ × ℕ, ind z ∂μ := by
        exact integral_const_mul c ind
      rw [integral_sub (integrable_const (1 : ℝ)) (hInd.const_mul c), hmul]
      simp
    _ = _ := by rw [hAtom]

/-- The threshold separating light and heavy Poisson cells. -/
noncomputable def poissonUsableHeavyThreshold (epsilon : ℝ) : ℝ := 4 / epsilon

/-- The linear Laplace exponent used for heavy Poisson cells. -/
noncomputable def poissonUsableHeavyConstant (epsilon : ℝ) : ℝ := epsilon / 2

/-- Under overlap, a heavy cell pays the explicit linear exponent `epsilon/2`.
The threshold `4/epsilon` makes the factor three in the PGF envelope harmless. -/
theorem poissonUsableCellLaplace_le_heavy
    {epsilon x : ℝ} (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2)
    (mu0 mu1 : NNReal) (hx : (mu0 : ℝ) + mu1 = x)
    (hmu0 : epsilon * x ≤ mu0) (hmu1 : epsilon * x ≤ mu1)
    (hheavy : poissonUsableHeavyThreshold epsilon < x) :
    poissonUsableCellLaplace mu0 mu1 ≤
      Real.exp (-poissonUsableHeavyConstant epsilon * x) := by
  have hx0 : 0 ≤ x := by
    rw [← hx]
    positivity
  have ha : epsilon ≤ 1 - Real.exp (-1) := by
    nlinarith [Real.exp_neg_one_lt_half]
  have hfirst : Real.exp (-(1 - Real.exp (-1)) * x) ≤ Real.exp (-epsilon * x) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right ha hx0
    linarith
  have hzero0 : Real.exp (-(mu0 : ℝ)) ≤ Real.exp (-epsilon * x) :=
    Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hmu0)
  have hzero1 : Real.exp (-(mu1 : ℝ)) ≤ Real.exp (-epsilon * x) :=
    Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hmu1)
  have hthree : (3 : ℝ) ≤ Real.exp (epsilon * x / 2) := by
    have hepsx : 4 < epsilon * x := by
      have := (div_lt_iff₀ hepsilon).mp hheavy
      simpa only [poissonUsableHeavyThreshold, mul_comm] using this
    have htwo : (3 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_two, Real.exp_pos (1 : ℝ)]
    exact htwo.le.trans (Real.exp_le_exp.mpr (by linarith))
  calc
    poissonUsableCellLaplace mu0 mu1 ≤
        Real.exp (-(1 - Real.exp (-1)) * ((mu0 : ℝ) + mu1)) +
          Real.exp (-(mu0 : ℝ)) + Real.exp (-(mu1 : ℝ)) :=
      poissonUsableCellLaplace_le_threeExp mu0 mu1
    _ = Real.exp (-(1 - Real.exp (-1)) * x) +
          Real.exp (-(mu0 : ℝ)) + Real.exp (-(mu1 : ℝ)) := by rw [hx]
    _ ≤ 3 * Real.exp (-epsilon * x) := by linarith
    _ ≤ Real.exp (epsilon * x / 2) * Real.exp (-epsilon * x) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = Real.exp (-poissonUsableHeavyConstant epsilon * x) := by
      rw [← Real.exp_add]
      unfold poissonUsableHeavyConstant
      congr 1
      ring

/-- The quadratic Laplace exponent obtained from the event with exactly one
treated and one untreated observation in a light Poisson cell. -/
noncomputable def poissonUsableLightConstant (epsilon : ℝ) : ℝ :=
  epsilon ^ 2 * (1 - Real.exp (-2)) *
    Real.exp (-poissonUsableHeavyThreshold epsilon)

/-- The conservative exponent constant after the light/heavy mass split. -/
noncomputable def poissonUsableLaplaceConstant (epsilon : ℝ) : ℝ :=
  min (poissonUsableLightConstant epsilon / 4)
    (poissonUsableHeavyConstant epsilon / 2)

/-- The explicit light-cell constant is positive under strict overlap. -/
theorem poissonUsableLightConstant_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (_hepsilon' : epsilon < 1) :
    0 < poissonUsableLightConstant epsilon := by
  unfold poissonUsableLightConstant
  have h_exp_two : Real.exp (-2 : ℝ) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  positivity

/-- The explicit heavy-cell constant is positive under strict overlap. -/
theorem poissonUsableHeavyConstant_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < poissonUsableHeavyConstant epsilon := by
  unfold poissonUsableHeavyConstant
  positivity

/-- The final explicit Laplace exponent is positive under strict overlap. -/
theorem poissonUsableLaplaceConstant_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (_hepsilon' : epsilon < 1) :
    0 < poissonUsableLaplaceConstant epsilon := by
  unfold poissonUsableLaplaceConstant
  exact lt_min
    (div_pos (poissonUsableLightConstant_pos hepsilon _hepsilon') (by norm_num))
    (div_pos (poissonUsableHeavyConstant_pos hepsilon) (by norm_num))

/-- Under overlap, a light cell pays an explicit quadratic exponent.  The
proof retains the exact `(1,1)` Poisson atom and uses `1-y ≤ exp(-y)`. -/
theorem poissonUsableCellLaplace_le_light
    {epsilon x : ℝ} (hepsilon : 0 < epsilon)
    (mu0 mu1 : NNReal) (hx : (mu0 : ℝ) + mu1 = x)
    (hmu0 : epsilon * x ≤ mu0) (hmu1 : epsilon * x ≤ mu1)
    (hlight : x ≤ poissonUsableHeavyThreshold epsilon) :
    poissonUsableCellLaplace mu0 mu1 ≤
      Real.exp (-poissonUsableLightConstant epsilon * x ^ 2) := by
  have hx0 : 0 ≤ x := by
    rw [← hx]
    positivity
  have hprod : epsilon ^ 2 * x ^ 2 ≤ (mu0 : ℝ) * (mu1 : ℝ) := by
    have h := mul_le_mul hmu0 hmu1 (mul_nonneg hepsilon.le hx0) (by positivity)
    nlinarith
  have hexp : Real.exp (-poissonUsableHeavyThreshold epsilon) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (neg_le_neg hlight)
  have hc : 0 ≤ 1 - Real.exp (-2 : ℝ) := by
    have : Real.exp (-2 : ℝ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    linarith
  have hcore : poissonUsableLightConstant epsilon * x ^ 2 ≤
      (1 - Real.exp (-2)) *
        (Real.exp (-x) * (mu0 : ℝ) * (mu1 : ℝ)) := by
    unfold poissonUsableLightConstant
    have hExpProd : Real.exp (-poissonUsableHeavyThreshold epsilon) *
          (epsilon ^ 2 * x ^ 2) ≤
        Real.exp (-x) * ((mu0 : ℝ) * (mu1 : ℝ)) :=
      mul_le_mul hexp hprod (by positivity) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left hExpProd hc]
  calc
    poissonUsableCellLaplace mu0 mu1 ≤
        1 - (1 - Real.exp (-2)) *
          (Real.exp (-((mu0 : ℝ) + mu1)) * (mu0 : ℝ) * (mu1 : ℝ)) :=
      poissonUsableCellLaplace_le_one_sub_atom mu0 mu1
    _ = 1 - (1 - Real.exp (-2)) *
          (Real.exp (-x) * (mu0 : ℝ) * (mu1 : ℝ)) := by rw [hx]
    _ ≤ 1 - poissonUsableLightConstant epsilon * x ^ 2 := by linarith
    _ ≤ Real.exp (-poissonUsableLightConstant epsilon * x ^ 2) :=
      by convert Real.one_sub_le_exp_neg (poissonUsableLightConstant epsilon * x ^ 2) using 1 <;> ring

/-- A light/heavy split controls the total exponent at the birthday scale.
The quadratic and linear local constants are completely explicit; no
probabilistic assumptions remain in this aggregation lemma. -/
theorem lightHeavyExponent_ge_birthdayScale
    {d : ℕ} (hd : 0 < d) {n a b threshold : ℝ}
    (hn : 0 ≤ n) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (lambda : Fin d → ℝ) (hlambda : ∀ k, 0 ≤ lambda k)
    (hsum : ∑ k, lambda k = n) :
    min (a / 4) (b / 2) * n ^ 2 / max n (d : ℝ) ≤
      a * ∑ k ∈ Finset.univ.filter (fun k ↦ lambda k ≤ threshold), lambda k ^ 2 +
      b * ∑ k ∈ Finset.univ.filter (fun k ↦ threshold < lambda k), lambda k := by
  let light : Finset (Fin d) := Finset.univ.filter (fun k ↦ lambda k ≤ threshold)
  let heavy : Finset (Fin d) := Finset.univ.filter (fun k ↦ threshold < lambda k)
  have hpartition : (∑ k ∈ light, lambda k) + ∑ k ∈ heavy, lambda k = n := by
    rw [← hsum]
    classical
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k ↦ lambda k ≤ threshold) lambda]
    simp only [light, heavy, not_le]
  have hmax_pos : 0 < max n (d : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hd) (le_max_right _ _)
  have hn_rate : n ^ 2 / max n (d : ℝ) ≤ n := by
    apply (div_le_iff₀ hmax_pos).2
    nlinarith [le_max_left n (d : ℝ)]
  by_cases hheavy : n / 2 ≤ ∑ k ∈ heavy, lambda k
  · have hc_le : min (a / 4) (b / 2) ≤ b / 2 := min_le_right _ _
    have hleft : min (a / 4) (b / 2) * n ^ 2 / max n (d : ℝ) ≤ b * (n / 2) := by
      calc
        min (a / 4) (b / 2) * n ^ 2 / max n (d : ℝ) =
            min (a / 4) (b / 2) * (n ^ 2 / max n (d : ℝ)) := by ring
        _ ≤ min (a / 4) (b / 2) * n :=
          mul_le_mul_of_nonneg_left hn_rate (le_min (by positivity) (by positivity))
        _ ≤ (b / 2) * n := mul_le_mul_of_nonneg_right hc_le hn
        _ = b * (n / 2) := by ring
    have hlight_nonneg : 0 ≤ a * ∑ k ∈ light, lambda k ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hheavy hb
    change min (a / 4) (b / 2) * n ^ 2 / max n (d : ℝ) ≤
      a * ∑ k ∈ light, lambda k ^ 2 + b * ∑ k ∈ heavy, lambda k
    nlinarith
  · have hlight_mass : n / 2 < ∑ k ∈ light, lambda k := by
      linarith
    have hcauchy : (∑ k ∈ light, lambda k) ^ 2 ≤
        (light.card : ℝ) * ∑ k ∈ light, lambda k ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := light) (f := lambda)
    have hcard : (light.card : ℝ) ≤ d := by
      have hcardNat : light.card ≤ Fintype.card (Fin d) := light.card_le_univ
      rw [Fintype.card_fin] at hcardNat
      exact_mod_cast hcardNat
    have hsquares_nonneg : 0 ≤ ∑ k ∈ light, lambda k ^ 2 := by positivity
    have hcauchy_d : (∑ k ∈ light, lambda k) ^ 2 ≤
        (d : ℝ) * ∑ k ∈ light, lambda k ^ 2 :=
      hcauchy.trans (mul_le_mul_of_nonneg_right hcard hsquares_nonneg)
    have hhalf_sq : (n / 2) ^ 2 ≤ (∑ k ∈ light, lambda k) ^ 2 := by
      nlinarith [Finset.sum_nonneg (s := light) (fun k _ ↦ hlambda k)]
    have hsquares : n ^ 2 / (4 * d) ≤ ∑ k ∈ light, lambda k ^ 2 := by
      have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * d)).2
      nlinarith
    have hrate_d : n ^ 2 / max n (d : ℝ) ≤ n ^ 2 / d := by
      exact div_le_div_of_nonneg_left (sq_nonneg n) (by exact_mod_cast hd) (le_max_right _ _)
    have hc_le : min (a / 4) (b / 2) ≤ a / 4 := min_le_left _ _
    have hleft : min (a / 4) (b / 2) * n ^ 2 / max n (d : ℝ) ≤
        a * (n ^ 2 / (4 * d)) := by
      calc
        min (a / 4) (b / 2) * n ^ 2 / max n (d : ℝ) =
            min (a / 4) (b / 2) * (n ^ 2 / max n (d : ℝ)) := by ring
        _ ≤ min (a / 4) (b / 2) * (n ^ 2 / d) :=
          mul_le_mul_of_nonneg_left hrate_d (le_min (by positivity) (by positivity))
        _ ≤ (a / 4) * (n ^ 2 / d) :=
          mul_le_mul_of_nonneg_right hc_le (by positivity)
        _ = a * (n ^ 2 / (4 * d)) := by ring
    have hheavy_nonneg : 0 ≤ b * ∑ k ∈ heavy, lambda k := by
      exact mul_nonneg hb (Finset.sum_nonneg fun k _ ↦ hlambda k)
    dsimp [light, heavy] at *
    nlinarith [mul_le_mul_of_nonneg_left hsquares ha]

/-- The Laplace transform of independent two-arm Poisson cells has a
birthday-scale exponent.  Intensities in each arm are at least an
`epsilon`-fraction of the cell's total intensity. -/
theorem independentPoissonUsableLaplace_le_birthdayScale
    {d : ℕ} (hd : 0 < d) {epsilon total : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2)
    (mu0 mu1 : Fin d → NNReal) (x : Fin d → ℝ)
    (hx : ∀ k, (mu0 k : ℝ) + mu1 k = x k)
    (hmu0 : ∀ k, epsilon * x k ≤ mu0 k)
    (hmu1 : ∀ k, epsilon * x k ≤ mu1 k)
    (hsum : ∑ k, x k = total) :
    (∫ z : Fin d → ℕ × ℕ,
        Real.exp (-(∑ k, (poissonUsableCellCount (z k) : ℝ)))
      ∂Measure.pi (fun k ↦ (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k)))) ≤
      Real.exp (-poissonUsableLaplaceConstant epsilon * total ^ 2 /
        max total (d : ℝ)) := by
  classical
  have hx_nonneg : ∀ k, 0 ≤ x k := by
    intro k
    rw [← hx k]
    positivity
  have htotal : 0 ≤ total := by
    rw [← hsum]
    exact Finset.sum_nonneg (fun k _ ↦ hx_nonneg k)
  let threshold := poissonUsableHeavyThreshold epsilon
  let a := poissonUsableLightConstant epsilon
  let b := poissonUsableHeavyConstant epsilon
  let exponent : Fin d → ℝ := fun k ↦
    if x k ≤ threshold then a * x k ^ 2 else b * x k
  have hlocal : ∀ k, poissonUsableCellLaplace (mu0 k) (mu1 k) ≤
      Real.exp (-exponent k) := by
    intro k
    by_cases hk : x k ≤ threshold
    · convert poissonUsableCellLaplace_le_light hepsilon (mu0 k) (mu1 k)
          (hx k) (hmu0 k) (hmu1 k) hk using 1 <;>
        simp only [exponent, if_pos hk, a] <;> ring
    · have hk' : poissonUsableHeavyThreshold epsilon < x k := by
        simpa only [threshold, not_le] using hk
      convert poissonUsableCellLaplace_le_heavy hepsilon hepsilon_half (mu0 k) (mu1 k)
          (hx k) (hmu0 k) (hmu1 k) hk' using 1 <;>
        simp only [exponent, if_neg hk, b] <;> ring
  have hfactor :
      (∫ z : Fin d → ℕ × ℕ,
          Real.exp (-(∑ k, (poissonUsableCellCount (z k) : ℝ)))
        ∂Measure.pi (fun k ↦ (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k)))) =
        ∏ k, poissonUsableCellLaplace (mu0 k) (mu1 k) := by
    calc
      _ = ∫ z : Fin d → ℕ × ℕ,
          ∏ k, Real.exp (-(poissonUsableCellCount (z k) : ℝ))
          ∂Measure.pi (fun k ↦ (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k))) := by
            congr with z
            rw [← Real.exp_sum]
            congr 1
            rw [Finset.sum_neg_distrib]
      _ = ∏ k, ∫ z : ℕ × ℕ,
          Real.exp (-(poissonUsableCellCount z : ℝ))
          ∂(poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k)) := by
            exact integral_fintype_prod_eq_prod (𝕜 := ℝ)
              (μ := fun k ↦ (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k)))
              (fun _k z ↦ Real.exp (-(poissonUsableCellCount z : ℝ)))
      _ = _ := by rfl
  have hprod : (∏ k, poissonUsableCellLaplace (mu0 k) (mu1 k)) ≤
      ∏ k, Real.exp (-exponent k) := by
    exact Finset.prod_le_prod (fun k _ ↦ (integral_nonneg
      (fun z ↦ (Real.exp_pos (-(poissonUsableCellCount z : ℝ))).le)))
      (fun k _ ↦ hlocal k)
  have ha0 : 0 ≤ a := (poissonUsableLightConstant_pos hepsilon (by linarith)).le
  have hb0 : 0 ≤ b := (poissonUsableHeavyConstant_pos hepsilon).le
  have hAgg := lightHeavyExponent_ge_birthdayScale hd htotal ha0 hb0 x hx_nonneg hsum
    (threshold := threshold)
  have hExponent : poissonUsableLaplaceConstant epsilon * total ^ 2 /
        max total (d : ℝ) ≤ ∑ k, exponent k := by
    have hc : poissonUsableLaplaceConstant epsilon = min (a / 4) (b / 2) := by
      rfl
    rw [hc]
    refine hAgg.trans_eq ?_
    simp only [exponent, Finset.mul_sum]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : x k ≤ threshold <;> simp [hk]
  calc
    _ = ∏ k, poissonUsableCellLaplace (mu0 k) (mu1 k) := hfactor
    _ ≤ ∏ k, Real.exp (-exponent k) := hprod
    _ = Real.exp (-∑ k, exponent k) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib]
    _ ≤ Real.exp (-poissonUsableLaplaceConstant epsilon * total ^ 2 /
        max total (d : ℝ)) := by
      apply Real.exp_le_exp.mpr
      calc
        -∑ k, exponent k ≤
            -(poissonUsableLaplaceConstant epsilon * total ^ 2 /
              max total (d : ℝ)) := neg_le_neg hExponent
        _ = -poissonUsableLaplaceConstant epsilon * total ^ 2 /
              max total (d : ℝ) := by
          simp only [neg_div, neg_mul]

end CausalSmith.Mathlib.Probability
