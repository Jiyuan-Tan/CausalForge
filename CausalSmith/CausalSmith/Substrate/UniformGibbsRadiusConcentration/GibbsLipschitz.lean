import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Finite-action Gibbs squared radii

The Gibbs radius is expressed in the transformed coordinates `(g, g-f)`.
For bounded predictions it is `[0,1]`-valued and is `(eta+2)`-Lipschitz in
the product supremum norm.
-/

noncomputable section

namespace CausalSmith.Substrate

open scoped BigOperators

variable {A : Type*} [Fintype A]

/-- The normalizing denominator of a finite exponential tilt. -/
def finiteGibbsDenominator (w u : A → ℝ) (eta : ℝ) : ℝ :=
  ∑ a, w a * Real.exp (eta * u a)

/-- The Gibbs-weighted squared second coordinate of `(u,v)`.  In the intended
application `u=g` and `v=g-f`. -/
def finiteGibbsSquaredRadius
    (w : A → ℝ) (eta : ℝ) (z : (A → ℝ) × (A → ℝ)) : ℝ :=
  (∑ a, w a * Real.exp (eta * z.1 a) * (z.2 a) ^ 2) /
    finiteGibbsDenominator w z.1 eta

/-- A finite exponential-tilt denominator is strictly positive even when
some base weights vanish, provided the weights are nonnegative and sum to one. -/
theorem finiteGibbsDenominator_pos
    (w u : A → ℝ) (eta : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) :
    0 < finiteGibbsDenominator w u eta := by
  have hsum_ne : ∑ a, w a ≠ 0 := by simp [hmass]
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) hsum_ne
  have hwa : 0 < w a := lt_of_le_of_ne (hw a) (Ne.symm ha)
  exact Finset.sum_pos'
    (fun b _ => mul_nonneg (hw b) (Real.exp_pos _).le)
    ⟨a, Finset.mem_univ _, mul_pos hwa (Real.exp_pos _)⟩

/-- The normalized finite Gibbs weights are nonnegative and sum to one. -/
theorem finiteGibbs_weights
    (w u : A → ℝ) (eta : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) :
    (∀ a, 0 ≤ w a * Real.exp (eta * u a) /
      finiteGibbsDenominator w u eta) ∧
    ∑ a, w a * Real.exp (eta * u a) /
      finiteGibbsDenominator w u eta = 1 := by
  have hden := finiteGibbsDenominator_pos w u eta hw hmass
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hw a) (Real.exp_pos _).le) hden.le
  · rw [← Finset.sum_div, finiteGibbsDenominator]
    exact div_self hden.ne'

/-- If the second transformed coordinate is in `[-1,1]`, the Gibbs squared
radius lies in `[0,1]`. -/
theorem finiteGibbsSquaredRadius_mem_Icc
    (w : A → ℝ) (eta : ℝ) (z : (A → ℝ) × (A → ℝ))
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hz : ∀ a, |z.2 a| ≤ 1) :
    finiteGibbsSquaredRadius w eta z ∈ Set.Icc (0 : ℝ) 1 := by
  have hden := finiteGibbsDenominator_pos w z.1 eta hw hmass
  constructor
  · exact div_nonneg
      (Finset.sum_nonneg fun a _ =>
        mul_nonneg (mul_nonneg (hw a) (Real.exp_pos _).le) (sq_nonneg _))
      hden.le
  · apply (div_le_iff₀ hden).2
    unfold finiteGibbsDenominator
    simp only [one_mul]
    apply Finset.sum_le_sum
    intro a _
    have hs : (z.2 a) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (z.2 a),
        mul_self_le_mul_self (abs_nonneg (z.2 a)) (hz a)]
    have hp : 0 ≤ w a * Real.exp (eta * z.1 a) :=
      mul_nonneg (hw a) (Real.exp_pos _).le
    nlinarith

private def gibbsPath
    (w : A → ℝ) (eta : ℝ)
    (z z' : (A → ℝ) × (A → ℝ)) (t : ℝ) : ℝ :=
  finiteGibbsSquaredRadius w eta
    (z + t • (z' - z))

private def gibbsPathDerivative
    (w : A → ℝ) (eta : ℝ)
    (z z' : (A → ℝ) × (A → ℝ)) (t : ℝ) : ℝ :=
  let y := z + t • (z' - z)
  let p : A → ℝ := fun a =>
    w a * Real.exp (eta * y.1 a) /
      finiteGibbsDenominator w y.1 eta
  ∑ a, p a *
    (eta * (z'.1 a - z.1 a) *
        ((y.2 a) ^ 2 - finiteGibbsSquaredRadius w eta y) +
      2 * y.2 a * (z'.2 a - z.2 a))

private theorem hasDerivAt_gibbsPath
    (w : A → ℝ) (eta : ℝ)
    (z z' : (A → ℝ) × (A → ℝ))
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (t : ℝ) :
    HasDerivAt (gibbsPath w eta z z')
      (gibbsPathDerivative w eta z z' t) t := by
  let y : ℝ → (A → ℝ) × (A → ℝ) := fun s => z + s • (z' - z)
  let D : ℝ → ℝ := fun s => finiteGibbsDenominator w (y s).1 eta
  let N : ℝ → ℝ := fun s =>
    ∑ a, w a * Real.exp (eta * (y s).1 a) * ((y s).2 a) ^ 2
  have hy1 (a : A) :
      HasDerivAt (fun s => (y s).1 a) (z'.1 a - z.1 a) t := by
    have hfun : (fun s : ℝ => (y s).1 a)
        = fun s : ℝ => z.1 a + s * (z'.1 a - z.1 a) := by
      funext s; simp [y]
    rw [hfun]
    exact (hasDerivAt_mul_const (z'.1 a - z.1 a)).const_add (z.1 a)
  have hy2 (a : A) :
      HasDerivAt (fun s => (y s).2 a) (z'.2 a - z.2 a) t := by
    have hfun : (fun s : ℝ => (y s).2 a)
        = fun s : ℝ => z.2 a + s * (z'.2 a - z.2 a) := by
      funext s; simp [y]
    rw [hfun]
    exact (hasDerivAt_mul_const (z'.2 a - z.2 a)).const_add (z.2 a)
  have hexpTerm (a : A) :
      HasDerivAt (Real.exp ∘ fun s => eta * (y s).1 a)
        (Real.exp (eta * (y t).1 a) * (eta * (z'.1 a - z.1 a))) t :=
    (Real.hasDerivAt_exp (eta * (y t).1 a)).comp t ((hy1 a).const_mul eta)
  have hD : HasDerivAt D
      (∑ a, w a * Real.exp (eta * (y t).1 a) *
        (eta * (z'.1 a - z.1 a))) t := by
    unfold D finiteGibbsDenominator
    exact HasDerivAt.fun_sum fun a _ =>
      ((hexpTerm a).const_mul (w a)).congr_deriv (by ring)
  have hN : HasDerivAt N
      (∑ a, w a * Real.exp (eta * (y t).1 a) *
        (eta * (z'.1 a - z.1 a) * ((y t).2 a) ^ 2 +
          2 * (y t).2 a * (z'.2 a - z.2 a))) t := by
    unfold N
    refine HasDerivAt.fun_sum fun a _ => ?_
    have hv := (hy2 a).pow 2
    exact (((hexpTerm a).const_mul (w a)).mul hv).congr_deriv (by
      simp only [Pi.pow_apply, Function.comp_apply]
      push_cast
      ring)
  have hDpos : 0 < D t := by
    exact finiteGibbsDenominator_pos w (y t).1 eta hw hmass
  have hquot := hN.div hD hDpos.ne'
  change HasDerivAt (gibbsPath w eta z z')
    (gibbsPathDerivative w eta z z' t) t
  refine hquot.congr_deriv ?_
  simp only [gibbsPathDerivative]
  let np : A → ℝ := fun a =>
    w a * Real.exp (eta * (y t).1 a) *
      (eta * (z'.1 a - z.1 a) * (y t).2 a ^ 2 +
        2 * (y t).2 a * (z'.2 a - z.2 a))
  let dp : A → ℝ := fun a =>
    w a * Real.exp (eta * (y t).1 a) *
      (eta * (z'.1 a - z.1 a))
  have hpoint (a : A) :
      (w a * Real.exp (eta * (y t).1 a) / D t) *
        (eta * (z'.1 a - z.1 a) * ((y t).2 a ^ 2 - N t / D t) +
          2 * (y t).2 a * (z'.2 a - z.2 a)) =
      np a / D t - N t * dp a / D t ^ 2 := by
    dsimp [np, dp]
    field_simp [hDpos.ne']
    ring
  change
    ((∑ a, w a * Real.exp (eta * (y t).1 a) *
        (eta * (z'.1 a - z.1 a) * (y t).2 a ^ 2 +
          2 * (y t).2 a * (z'.2 a - z.2 a))) * D t -
      N t * ∑ a, w a * Real.exp (eta * (y t).1 a) *
        (eta * (z'.1 a - z.1 a))) / D t ^ 2 =
    (∑ a, (w a * Real.exp (eta * (y t).1 a) / D t) *
      (eta * (z'.1 a - z.1 a) * ((y t).2 a ^ 2 - N t / D t) +
        2 * (y t).2 a * (z'.2 a - z.2 a)))
  symm
  calc
    (∑ a, (w a * Real.exp (eta * (y t).1 a) / D t) *
        (eta * (z'.1 a - z.1 a) * ((y t).2 a ^ 2 - N t / D t) +
          2 * (y t).2 a * (z'.2 a - z.2 a))) =
        ∑ a, (np a / D t - N t * dp a / D t ^ 2) :=
      Finset.sum_congr rfl fun a _ => hpoint a
    _ = (∑ a, np a) / D t - N t * (∑ a, dp a) / D t ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      congr 1
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.mul_sum]
    _ = _ := by
      dsimp [np, dp]
      field_simp [hDpos.ne']

private theorem gibbsPathDerivative_bound
    (w : A → ℝ) (eta : ℝ)
    (z z' : (A → ℝ) × (A → ℝ))
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (heta : 0 ≤ eta)
    (hz : ∀ a, z.1 a ∈ Set.Icc (0 : ℝ) 1 ∧ |z.2 a| ≤ 1)
    (hz' : ∀ a, z'.1 a ∈ Set.Icc (0 : ℝ) 1 ∧ |z'.2 a| ≤ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |gibbsPathDerivative w eta z z' t| ≤
      (eta + 2) * ‖z' - z‖ := by
  let y := z + t • (z' - z)
  let p : A → ℝ := fun a =>
    w a * Real.exp (eta * y.1 a) /
      finiteGibbsDenominator w y.1 eta
  have hp := finiteGibbs_weights w y.1 eta hw hmass
  rcases ht with ⟨ht0, ht1⟩
  have hy1 (a : A) : y.1 a ∈ Set.Icc (0 : ℝ) 1 := by
    change z.1 a + t * (z'.1 a - z.1 a) ∈ Set.Icc (0 : ℝ) 1
    constructor <;>
      nlinarith [(hz a).1.1, (hz a).1.2, (hz' a).1.1, (hz' a).1.2]
  have hy2 (a : A) : |y.2 a| ≤ 1 := by
    change |z.2 a + t * (z'.2 a - z.2 a)| ≤ 1
    apply abs_le.2
    constructor <;>
      have hzlo := neg_le_of_abs_le (hz a).2 <;>
      have hzhi := le_of_abs_le (hz a).2 <;>
      have hz'lo := neg_le_of_abs_le (hz' a).2 <;>
      have hz'hi := le_of_abs_le (hz' a).2 <;>
      nlinarith
  have hR := finiteGibbsSquaredRadius_mem_Icc w eta y hw hmass hy2
  have hdu (a : A) : |z'.1 a - z.1 a| ≤ ‖z' - z‖ := by
    calc
      |z'.1 a - z.1 a| = ‖(z' - z).1 a‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖(z' - z).1‖ := norm_le_pi_norm _ a
      _ ≤ ‖z' - z‖ := norm_fst_le _
  have hdv (a : A) : |z'.2 a - z.2 a| ≤ ‖z' - z‖ := by
    calc
      |z'.2 a - z.2 a| = ‖(z' - z).2 a‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖(z' - z).2‖ := norm_le_pi_norm _ a
      _ ≤ ‖z' - z‖ := norm_snd_le _
  have hterm (a : A) :
      |eta * (z'.1 a - z.1 a) *
          ((y.2 a) ^ 2 - finiteGibbsSquaredRadius w eta y) +
        2 * y.2 a * (z'.2 a - z.2 a)| ≤
        (eta + 2) * ‖z' - z‖ := by
    have hsq : (y.2 a) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · nlinarith [sq_abs (y.2 a),
          mul_self_le_mul_self (abs_nonneg (y.2 a)) (hy2 a)]
    calc
      |eta * (z'.1 a - z.1 a) *
          ((y.2 a) ^ 2 - finiteGibbsSquaredRadius w eta y) +
        2 * y.2 a * (z'.2 a - z.2 a)| ≤
          |eta * (z'.1 a - z.1 a) *
            ((y.2 a) ^ 2 - finiteGibbsSquaredRadius w eta y)| +
          |2 * y.2 a * (z'.2 a - z.2 a)| := abs_add_le _ _
      _ ≤ eta * ‖z' - z‖ + 2 * ‖z' - z‖ := by
        have hdiff : |(y.2 a) ^ 2 -
            finiteGibbsSquaredRadius w eta y| ≤ 1 :=
          abs_le.2 ⟨by linarith [hsq.1, hR.2],
            by linarith [hsq.2, hR.1]⟩
        have hyabs := hy2 a
        apply add_le_add
        · rw [abs_mul, abs_mul, abs_of_nonneg heta]
          calc
            eta * |z'.1 a - z.1 a| *
                |y.2 a ^ 2 - finiteGibbsSquaredRadius w eta y| ≤
                eta * ‖z' - z‖ *
                  |y.2 a ^ 2 - finiteGibbsSquaredRadius w eta y| := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (hdu a) heta)
                      (abs_nonneg _)
            _ ≤ eta * ‖z' - z‖ * 1 := by
                    exact mul_le_mul_of_nonneg_left hdiff
                      (mul_nonneg heta (norm_nonneg _))
            _ = eta * ‖z' - z‖ := by ring
        · rw [abs_mul, abs_mul]
          norm_num
          calc
            2 * |y.2 a| * |z'.2 a - z.2 a| ≤
                2 * 1 * |z'.2 a - z.2 a| := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hyabs (by norm_num))
                    (abs_nonneg _)
            _ ≤ 2 * 1 * ‖z' - z‖ := by
                  exact mul_le_mul_of_nonneg_left (hdv a) (by norm_num)
            _ = 2 * ‖z' - z‖ := by ring
      _ = (eta + 2) * ‖z' - z‖ := by ring
  simp only [gibbsPathDerivative]
  calc
    |∑ a, p a *
      (eta * (z'.1 a - z.1 a) *
          ((y.2 a) ^ 2 - finiteGibbsSquaredRadius w eta y) +
        2 * y.2 a * (z'.2 a - z.2 a))| ≤
        ∑ a, |p a *
          (eta * (z'.1 a - z.1 a) *
              ((y.2 a) ^ 2 - finiteGibbsSquaredRadius w eta y) +
            2 * y.2 a * (z'.2 a - z.2 a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, p a * ((eta + 2) * ‖z' - z‖) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (hp.1 a)]
      exact mul_le_mul_of_nonneg_left (hterm a) (hp.1 a)
    _ = (eta + 2) * ‖z' - z‖ := by
      rw [← Finset.sum_mul, hp.2, one_mul]

/-- On transformed pairs arising from `[0,1]`-valued predictions, the finite
Gibbs squared radius is `(eta+2)`-Lipschitz for the product supremum norm. -/
theorem finiteGibbsSquaredRadius_lipschitz
    (w : A → ℝ) (eta : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (heta : 0 < eta)
    (z z' : (A → ℝ) × (A → ℝ))
    (hz : ∀ a, z.1 a ∈ Set.Icc (0 : ℝ) 1 ∧ |z.2 a| ≤ 1)
    (hz' : ∀ a, z'.1 a ∈ Set.Icc (0 : ℝ) 1 ∧ |z'.2 a| ≤ 1) :
    |finiteGibbsSquaredRadius w eta z -
        finiteGibbsSquaredRadius w eta z'| ≤
      (eta + 2) * ‖z - z'‖ := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := gibbsPath w eta z z')
    (f' := gibbsPathDerivative w eta z z')
    (fun t _ => (hasDerivAt_gibbsPath w eta z z' hw hmass t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact gibbsPathDerivative_bound w eta z z' hw hmass heta.le hz hz' t ht)
    (convex_Icc (0 : ℝ) 1)
    (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
  simp only [gibbsPath, zero_smul, add_zero, one_smul, add_sub_cancel_left,
    Real.norm_eq_abs] at hmv
  rw [norm_sub_rev] at hmv
  simpa [abs_sub_comm] using hmv

end CausalSmith.Substrate
