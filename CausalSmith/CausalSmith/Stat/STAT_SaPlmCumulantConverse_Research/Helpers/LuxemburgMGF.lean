import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic

/-!
# A Luxemburg square-exponential bound implies a global MGF bound

This file supplies the real-variable estimate used by transform-zero localization.
A centered random variable whose square-exponential moment is at most two has
all real exponential moments, with an explicit quadratic MGF envelope.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- The exponential Taylor remainder is bounded globally by a square times an
absolute exponential. -/
private lemma exp_le_one_add_add_sq_mul_exp_abs (u : ℝ) :
    Real.exp u ≤ 1 + u + u ^ 2 * Real.exp |u| := by
  by_cases hu : |u| ≤ 1
  · have hrem := Real.abs_exp_sub_one_sub_id_le hu
    have hle : Real.exp u - 1 - u ≤ u ^ 2 :=
      (le_abs_self (Real.exp u - 1 - u)).trans hrem
    have hexp : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
    have hsq : u ^ 2 ≤ u ^ 2 * Real.exp |u| := by
      nlinarith [sq_nonneg u]
    linarith
  · have habs : 1 < |u| := lt_of_not_ge hu
    by_cases hnonneg : 0 ≤ u
    · have hu1 : 1 < u := by rwa [abs_of_nonneg hnonneg] at habs
      have hmul : Real.exp u ≤ u ^ 2 * Real.exp |u| := by
        rw [abs_of_nonneg hnonneg]
        exact le_mul_of_one_le_left (Real.exp_nonneg u) (by nlinarith)
      linarith
    · have hu1 : u ≤ -1 := by
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at habs
        linarith
      have hpoly : 1 ≤ 1 + u + u ^ 2 := by nlinarith [sq_nonneg (u + 1)]
      have hexp : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
      have hsq : u ^ 2 ≤ u ^ 2 * Real.exp |u| := by
        nlinarith [sq_nonneg u]
      have heu : Real.exp u ≤ 1 := (Real.exp_le_one_iff.mpr (le_trans hu1 (by norm_num)))
      linarith

/-- A nonnegative square is at most the exponential of half that square. -/
private lemma sq_le_exp_half_sq (y : ℝ) :
    y ^ 2 ≤ Real.exp (y ^ 2 / 2) := by
  have hlin := Real.add_one_le_exp (y ^ 2 / 4)
  have hnonneg : 0 ≤ 1 + y ^ 2 / 4 := by positivity
  have hexpnonneg : 0 ≤ Real.exp (y ^ 2 / 4) := Real.exp_nonneg _
  have hsqmono : (1 + y ^ 2 / 4) ^ 2 ≤ (Real.exp (y ^ 2 / 4)) ^ 2 := by
    nlinarith
  calc
    y ^ 2 ≤ (1 + y ^ 2 / 4) ^ 2 := by nlinarith [sq_nonneg (y ^ 2 - 4)]
    _ ≤ (Real.exp (y ^ 2 / 4)) ^ 2 := hsqmono
    _ = Real.exp (y ^ 2 / 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- The numerical estimate `exp(1/2) ≤ 2`. -/
private lemma exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  convert Real.exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    using 1 <;> norm_num

/-- A square-exponential envelope gives integrability of every real
exponential tilt. -/
lemma integrable_exp_mul_of_luxemburg_sq
    (hψ : 0 < ψ) (hXmeas : Measurable X)
    (hLuxInt : Integrable (fun ω ↦ Real.exp (X ω ^ 2 / ψ ^ 2)) μ)
    (t : ℝ) : Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
  apply (hLuxInt.mul_const (Real.exp (t ^ 2 * ψ ^ 2 / 4))).mono'
    ((Real.continuous_exp.measurable.comp (measurable_const.fun_mul hXmeas)).aestronglyMeasurable)
  filter_upwards [] with ω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsquare : 0 ≤ X ω ^ 2 / ψ ^ 2 + t ^ 2 * ψ ^ 2 / 4 - t * X ω := by
    have h := sq_nonneg (X ω / ψ - t * ψ / 2)
    field_simp [hψ.ne'] at h ⊢
    nlinarith
  linarith

/-- A centered Luxemburg square-exponential bound implies the global MGF
estimate `E exp(tX) ≤ exp(4 ψ²t²)`. -/
lemma integral_exp_mul_le_exp_four_mul_sq_of_luxemburg
    [IsProbabilityMeasure μ]
    (hψ : 0 < ψ) (hXmeas : Measurable X) (hXint : Integrable X μ)
    (hLuxInt : Integrable (fun ω ↦ Real.exp (X ω ^ 2 / ψ ^ 2)) μ)
    (hLux : ∫ ω, Real.exp (X ω ^ 2 / ψ ^ 2) ∂μ ≤ 2)
    (hcenter : ∫ ω, X ω ∂μ = 0) (t : ℝ) :
    ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (4 * ψ ^ 2 * t ^ 2) := by
  let s : ℝ := t * ψ
  by_cases hsmall : |s| ≤ 1
  · have hs_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
    have hs_le : s ^ 2 ≤ 1 := by
      have := mul_self_le_mul_self (abs_nonneg s) hsmall
      nlinarith [sq_abs s]
    have hremInt : Integrable
        (fun ω ↦ 2 * s ^ 2 * Real.exp (X ω ^ 2 / ψ ^ 2)) μ :=
      hLuxInt.const_mul (2 * s ^ 2)
    have hpoint : ∀ ω, Real.exp (t * X ω) ≤
        1 + t * X ω + 2 * s ^ 2 * Real.exp (X ω ^ 2 / ψ ^ 2) := by
      intro ω
      let y : ℝ := X ω / ψ
      have htx : t * X ω = s * y := by
        dsimp [s, y]
        field_simp [hψ.ne']
      have habs : |s * y| ≤ (1 + y ^ 2) / 2 := by
        calc
          |s * y| = |s| * |y| := abs_mul _ _
          _ ≤ (s ^ 2 + y ^ 2) / 2 := by
            rw [← sq_abs s, ← sq_abs y]
            nlinarith [sq_nonneg (|s| - |y|)]
          _ ≤ (1 + y ^ 2) / 2 := by linarith
      have hbase := exp_le_one_add_add_sq_mul_exp_abs (s * y)
      have hexp : Real.exp |s * y| ≤ Real.exp ((1 + y ^ 2) / 2) :=
        Real.exp_le_exp.mpr habs
      have hyexp : y ^ 2 * Real.exp ((1 + y ^ 2) / 2) ≤
          2 * Real.exp (y ^ 2) := by
        rw [show (1 + y ^ 2) / 2 = (1 / 2 : ℝ) + y ^ 2 / 2 by ring,
          Real.exp_add]
        have hy := sq_le_exp_half_sq y
        have hp0 : 0 ≤ Real.exp (1 / 2 : ℝ) := Real.exp_nonneg _
        have hp1 : 0 ≤ Real.exp (y ^ 2 / 2) := Real.exp_nonneg _
        calc
          y ^ 2 * (Real.exp (1 / 2 : ℝ) * Real.exp (y ^ 2 / 2))
              ≤ Real.exp (y ^ 2 / 2) *
                  (Real.exp (1 / 2 : ℝ) * Real.exp (y ^ 2 / 2)) := by gcongr
          _ = Real.exp (1 / 2 : ℝ) *
              (Real.exp (y ^ 2 / 2) * Real.exp (y ^ 2 / 2)) := by ring
          _ = Real.exp (1 / 2 : ℝ) * Real.exp (y ^ 2) := by
            rw [← Real.exp_add]
            congr 2
            ring
          _ ≤ 2 * Real.exp (y ^ 2) := by gcongr; exact exp_half_le_two
      have hrem : (s * y) ^ 2 * Real.exp |s * y| ≤
          2 * s ^ 2 * Real.exp (y ^ 2) := by
        calc
          (s * y) ^ 2 * Real.exp |s * y|
              ≤ (s * y) ^ 2 * Real.exp ((1 + y ^ 2) / 2) := by gcongr
          _ = s ^ 2 * (y ^ 2 * Real.exp ((1 + y ^ 2) / 2)) := by ring
          _ ≤ s ^ 2 * (2 * Real.exp (y ^ 2)) := by gcongr
          _ = 2 * s ^ 2 * Real.exp (y ^ 2) := by ring
      calc
        Real.exp (t * X ω) = Real.exp (s * y) := by rw [htx]
        _ ≤ 1 + s * y + (s * y) ^ 2 * Real.exp |s * y| := hbase
        _ ≤ 1 + s * y + 2 * s ^ 2 * Real.exp (y ^ 2) := by linarith
        _ = 1 + t * X ω + 2 * s ^ 2 * Real.exp (X ω ^ 2 / ψ ^ 2) := by
          rw [← htx]
          congr 2
          dsimp [y]
          field_simp [hψ.ne']
    have htilt := integrable_exp_mul_of_luxemburg_sq hψ hXmeas hLuxInt t
    have hrhs : Integrable
        (fun ω ↦ 1 + t * X ω + 2 * s ^ 2 * Real.exp (X ω ^ 2 / ψ ^ 2)) μ :=
      ((integrable_const (1 : ℝ)).add (hXint.const_mul t)).add hremInt
    calc
      ∫ ω, Real.exp (t * X ω) ∂μ
          ≤ ∫ ω, (1 + t * X ω +
              2 * s ^ 2 * Real.exp (X ω ^ 2 / ψ ^ 2)) ∂μ :=
            integral_mono htilt hrhs hpoint
      _ = 1 + 2 * s ^ 2 * (∫ ω, Real.exp (X ω ^ 2 / ψ ^ 2) ∂μ) := by
        have hA : Integrable (fun ω ↦ (1 : ℝ) + t * X ω) μ :=
          (integrable_const (1 : ℝ)).add (hXint.const_mul t)
        have hB : Integrable
            (fun ω ↦ 2 * s ^ 2 * Real.exp (X ω ^ 2 / ψ ^ 2)) μ := hremInt
        rw [integral_add hA hB,
          integral_add (integrable_const (1 : ℝ)) (hXint.const_mul t),
          integral_const, integral_const_mul, integral_const_mul, hcenter]
        simp
      _ ≤ 1 + 4 * s ^ 2 := by nlinarith
      _ ≤ Real.exp (4 * s ^ 2) := by simpa [add_comm] using Real.add_one_le_exp (4 * s ^ 2)
      _ = Real.exp (4 * ψ ^ 2 * t ^ 2) := by
        congr 1
        dsimp [s]
        ring
  · have hs_gt : 1 < s ^ 2 := by
      have : 1 < |s| := lt_of_not_ge hsmall
      nlinarith [sq_abs s]
    have htilt := integrable_exp_mul_of_luxemburg_sq hψ hXmeas hLuxInt t
    have hpoint : ∀ ω, Real.exp (t * X ω) ≤
        Real.exp (s ^ 2 / 4) * Real.exp (X ω ^ 2 / ψ ^ 2) := by
      intro ω
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsquare := sq_nonneg (X ω / ψ - s / 2)
      have htx : t * X ω = s * (X ω / ψ) := by
        dsimp [s]
        field_simp [hψ.ne']
      rw [htx]
      field_simp [hψ.ne'] at hsquare ⊢
      nlinarith
    have henv : Integrable
        (fun ω ↦ Real.exp (s ^ 2 / 4) * Real.exp (X ω ^ 2 / ψ ^ 2)) μ :=
      hLuxInt.const_mul _
    calc
      ∫ ω, Real.exp (t * X ω) ∂μ
          ≤ ∫ ω, Real.exp (s ^ 2 / 4) *
              Real.exp (X ω ^ 2 / ψ ^ 2) ∂μ := integral_mono htilt henv hpoint
      _ = Real.exp (s ^ 2 / 4) *
          (∫ ω, Real.exp (X ω ^ 2 / ψ ^ 2) ∂μ) := by rw [integral_const_mul]
      _ ≤ Real.exp (s ^ 2 / 4) * 2 := by
        exact mul_le_mul_of_nonneg_left hLux (Real.exp_nonneg _)
      _ ≤ Real.exp (4 * s ^ 2) := by
        have htwo : 2 ≤ Real.exp 1 := by
          nlinarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
        have harg : 1 + s ^ 2 / 4 ≤ 4 * s ^ 2 := by nlinarith
        calc
          Real.exp (s ^ 2 / 4) * 2 ≤ Real.exp (s ^ 2 / 4) * Real.exp 1 := by
            gcongr
          _ = Real.exp (1 + s ^ 2 / 4) := by rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp (4 * s ^ 2) := Real.exp_le_exp.mpr harg
      _ = Real.exp (4 * ψ ^ 2 * t ^ 2) := by
        congr 1
        dsimp [s]
        ring

end CausalSmith.Stat.SaPlmCumulantConverse
