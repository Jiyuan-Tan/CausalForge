/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Moment-coordinate algebra for residual quadratic moment problems

This is the measure-free algebra layer for the `MomentProblems` folder. It works only with raw
moments `m₁, m₂, m₃, m₄`, and proves the identities used by the measure-level L² projection and
bounded-outcome envelope files.

The central residual is the squared `L²(μ)`-distance of `y²` to `span{1, y}`, i.e. the residual
variance of regressing `y²` on `1` and `y`:

    r(μ) = min_{b₀, b₁} ∫ (y² − b₀ − b₁ y)² dμ.

For any law with moments `m₁, m₂, m₃, m₄` (and `m₀ = 1`) this residual has the closed form
`momentResidual m₁ m₂ m₃ m₄`, the ratio of the two leading Hankel determinants. This file proves,
purely at the level of moments (no measure theory):

* `residualQuad_ge_momentResidual` / `residualQuad_optimalCoeff` — `momentResidual` is exactly the
  minimum over `(b₀, b₁)` of the regression objective, whenever the design is nondegenerate
  (`m₁² < m₂`, i.e. positive variance). This is the reusable residual-variance formula.
* `extremalResidual_eq_envelope` — the extremal three-point law on `{0, xᵥ, 1}` with second moment
  `q`, encoded through its moments `M₁ = t`, `M₂ = q`, `M₃`, `M₄` (single fractions of the free
  support parameter `t` and `q`), has residual exactly the closed form
  `momentEnvelope t q = ((t − q)(q − t²)) / (4 t (1 − t))`, for every admissible `t`.
* `momentEnvelope_hasDerivAt` / `momentEnvelope_stationary_of_quartic` — as a function of the
  support parameter `t`, the family residual `momentEnvelope t q` has derivative
  `envelopeQuartic t q / (4 t² (t − 1)²)`, so its stationary points are exactly the roots of the
  quartic `t⁴ − 2t³ + 2q t² − 2q² t + q² = 0`. The maximizing root `t = μᵥ ∈ (q, √q)` therefore
  selects the value `ρ(v) = momentEnvelope μᵥ q` of the envelope.
* `momentResidual_le_momentEnvelope` / `momentEnvelope_le_root` / `momentResidual_le_envelope` — the
  **sharp upper bound** `r(μ) ≤ ρ(v)` for every admissible law `μ` on `[0,1]` with `∫ y² = q`,
  proved by an explicit dual (SOS) certificate rather than general moment-problem machinery: a
  pointwise polynomial identity whose right side `y(1−y)(y−xᵥ)²` is manifestly nonnegative on
  `[0,1]`, plus the quartic-root maximality of the envelope over admissible first moments.

The existence/uniqueness of the maximizing root (`u = μᵥ`, taken here as a hypothesis of the sharp
bound) is packaged at the measure/envelope layer in
`MomentProblems.BoundedOutcomeEnvelope.QuarticRoot`.
-/

namespace Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra

open scoped Real

/-- The regression objective, in moment coordinates: the second moment about the linear fit
`b₀ + b₁ y` of `y²`, i.e. `∫ (y² − b₀ − b₁ y)² dμ` expressed through the raw moments
`m₁ = ∫ y`, `m₂ = ∫ y²`, `m₃ = ∫ y³`, `m₄ = ∫ y⁴` (with `m₀ = 1`). -/
def residualQuad (m1 m2 m3 m4 b0 b1 : ℝ) : ℝ :=
  m4 - 2 * b1 * m3 - 2 * b0 * m2 + b1 ^ 2 * m2 + 2 * b0 * b1 * m1 + b0 ^ 2

/-- The closed-form residual variance of regressing `y²` on `{1, y}`: the value at the optimal
coefficients of `residualQuad`, equal to the ratio of the two leading Hankel determinants
`det [[1,m₁,m₂],[m₁,m₂,m₃],[m₂,m₃,m₄]] / det [[1,m₁],[m₁,m₂]]`. -/
noncomputable def momentResidual (m1 m2 m3 m4 : ℝ) : ℝ :=
  (m1 ^ 2 * m4 - 2 * m1 * m2 * m3 + m2 ^ 3 - m2 * m4 + m3 ^ 2) / (m1 ^ 2 - m2)

/-- The optimal intercept `b₀*` in the regression of `y²` on `{1, y}`. -/
noncomputable def optIntercept (m1 m2 m3 : ℝ) : ℝ := (m1 * m3 - m2 ^ 2) / (m1 ^ 2 - m2)

/-- The optimal slope `b₁*` in the regression of `y²` on `{1, y}`. -/
noncomputable def optSlope (m1 m2 m3 : ℝ) : ℝ := (m1 * m2 - m3) / (m1 ^ 2 - m2)

/-- At the optimal coefficients `(b₀*, b₁*)` the regression objective attains the closed-form
residual `momentResidual`. -/
theorem residualQuad_optimalCoeff (m1 m2 m3 m4 : ℝ) (h : m1 ^ 2 < m2) :
    residualQuad m1 m2 m3 m4 (optIntercept m1 m2 m3) (optSlope m1 m2 m3)
      = momentResidual m1 m2 m3 m4 := by
  have hd : m1 ^ 2 - m2 ≠ 0 := by nlinarith
  unfold residualQuad optIntercept optSlope momentResidual
  field_simp
  ring

/-- The closed-form residual `momentResidual` is a lower bound for the regression objective at every
choice of coefficients, when the design is nondegenerate (`m₁² < m₂`, positive variance). Together
with `residualQuad_optimalCoeff` this shows `momentResidual` is the minimum
`min_{b₀,b₁} ∫ (y² − b₀ − b₁ y)² dμ`.

Certificate (CAS-verified): with `D = m₂ − m₁² > 0`,
`residualQuad − momentResidual = (b₀ − b₀* + m₁ (b₁ − b₁*))² + D (b₁ − b₁*)² ≥ 0`. -/
theorem residualQuad_ge_momentResidual (m1 m2 m3 m4 b0 b1 : ℝ) (h : m1 ^ 2 < m2) :
    momentResidual m1 m2 m3 m4 ≤ residualQuad m1 m2 m3 m4 b0 b1 := by
  have hd : m1 ^ 2 - m2 ≠ 0 := by nlinarith
  have key : residualQuad m1 m2 m3 m4 b0 b1 - momentResidual m1 m2 m3 m4
      = (b0 - optIntercept m1 m2 m3 + m1 * (b1 - optSlope m1 m2 m3)) ^ 2
        + (m2 - m1 ^ 2) * (b1 - optSlope m1 m2 m3) ^ 2 := by
    unfold residualQuad momentResidual optIntercept optSlope
    field_simp
    ring
  nlinarith [sq_nonneg (b0 - optIntercept m1 m2 m3 + m1 * (b1 - optSlope m1 m2 m3)),
    sq_nonneg (b1 - optSlope m1 m2 m3), key, h]

/-! ### Extremal three-point law and the envelope value

The optimizer among laws on `[0,1]` with `∫ y² = q` is the three-point law on `{0, xᵥ, 1}` whose
moments, as functions of the support parameter `t = μᵥ`, reduce to the single fractions below
(`M₀ = 1`, `M₁ = t`, `M₂ = q`). -/

/-- The envelope value `ρ`, as a function of the support parameter `t = μᵥ` and `q = v²`:
`ρ = ((t − q)(q − t²)) / (4 t (1 − t))`. -/
noncomputable def momentEnvelope (t q : ℝ) : ℝ := ((t - q) * (q - t ^ 2)) / (4 * t * (1 - t))

/-- First moment `M₁ = ∫ y` of the extremal three-point law: the support parameter `t = μᵥ`. -/
def extremalM1 (t : ℝ) : ℝ := t

/-- Third moment `M₃ = ∫ y³` of the extremal three-point law. -/
noncomputable def extremalM3 (t q : ℝ) : ℝ :=
  (2 * q ^ 2 * t - q ^ 2 - q * t ^ 2 - q * t + t ^ 3) / (2 * t * (t - 1))

/-- Fourth moment `M₄ = ∫ y⁴` of the extremal three-point law. -/
noncomputable def extremalM4 (t q : ℝ) : ℝ :=
  (4 * q ^ 3 * t ^ 2 - 4 * q ^ 3 * t + q ^ 3 - 4 * q ^ 2 * t ^ 3 + q ^ 2 * t
      + 3 * q * t ^ 4 - 2 * q * t ^ 3 + 2 * q * t ^ 2 + t ^ 5 - 2 * t ^ 4)
    / (4 * t ^ 2 * (t - 1) ^ 2)

/-- The quartic whose stationary root in `(q, √q)` is the envelope maximizer `t = μᵥ`. -/
def envelopeQuartic (t q : ℝ) : ℝ := t ^ 4 - 2 * t ^ 3 + 2 * q * t ^ 2 - 2 * q ^ 2 * t + q ^ 2

/-- **Family residual identity.** For every nondegenerate support parameter `t` (with `t ≠ 0`,
`t ≠ 1`, and second moment `q ≠ t²`), the residual variance of regressing `y²` on `{1, y}` under the
three-point law with moments `(t, q, M₃, M₄)` equals the closed form `momentEnvelope t q`. In
particular `ρ(v)` is attained by an admissible law at second moment `q = v²`.

This is a pure rational-function identity in `(t, q)` — the quartic is *not* needed here; it enters
only through `momentEnvelope_hasDerivAt` as the stationarity condition selecting the maximizer. -/
theorem extremalResidual_eq_envelope (t q : ℝ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htq : t ^ 2 ≠ q) :
    momentResidual (extremalM1 t) q (extremalM3 t q) (extremalM4 t q) = momentEnvelope t q := by
  unfold momentResidual momentEnvelope extremalM1 extremalM3 extremalM4
  have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have h1' : (1 : ℝ) - t ≠ 0 := by
    intro h
    apply ht1
    linarith
  have h2 : (t : ℝ) ^ 2 - q ≠ 0 := sub_ne_zero.mpr htq
  have h2' : q - t ^ 2 ≠ 0 := by
    intro h
    apply h2
    linarith
  field_simp [ht0, h1, h1', h2, h2']
  ring

/-- **Stationarity / envelope FOC.** As a function of the support parameter `t`, the family residual
`momentEnvelope t q` has derivative `envelopeQuartic t q / (4 t² (t − 1)²)`. Hence the quartic is
exactly the numerator of `dρ/dt`, and the envelope's stationary points are its roots. -/
theorem momentEnvelope_hasDerivAt (t q : ℝ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    HasDerivAt (fun s => momentEnvelope s q)
      (envelopeQuartic t q / (4 * t ^ 2 * (t - 1) ^ 2)) t := by
  have hN : HasDerivAt (fun s : ℝ => (s - q) * (q - s ^ 2))
      (1 * (q - t ^ 2) + (t - q) * (-(2 * t))) t := by
    have h1 : HasDerivAt (fun s : ℝ => s - q) 1 t := (hasDerivAt_id t).sub_const q
    have h2 : HasDerivAt (fun s : ℝ => q - s ^ 2) (-(2 * t)) t := by
      have hc : HasDerivAt (fun _ : ℝ => q) 0 t := hasDerivAt_const t q
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      change HasDerivAtFilter (fun s : ℝ => q - s ^ 2) (-(2 * t)) (nhds t ×ˢ pure t)
      convert (hc.sub hp).hasDerivAtFilter using 1
      · norm_num
    simpa using h1.mul h2
  have hD : HasDerivAt (fun s : ℝ => 4 * s * (1 - s)) (4 * (1 - t) + 4 * t * (-1)) t := by
    have h3 : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have h4 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t (1 : ℝ)
      change HasDerivAtFilter (fun s : ℝ => 1 - s) (-1) (nhds t ×ˢ pure t)
      convert (hc.sub (hasDerivAt_id t)).hasDerivAtFilter using 1
      · norm_num
    simpa using h3.mul h4
  have hDne : 4 * t * (1 - t) ≠ 0 := by
    have ht1' : (1 : ℝ) - t ≠ 0 := by
      intro h
      apply ht1
      linarith
    exact mul_ne_zero (mul_ne_zero (by norm_num) ht0) ht1'
  have hderiv := hN.div hD hDne
  unfold momentEnvelope
  convert hderiv using 1
  · unfold envelopeQuartic
    field_simp [ht0, ht1]
    ring

/-- At a root `t` of the quartic, the family residual `momentEnvelope · q` is stationary. The
maximizing root `t = μᵥ ∈ (q, √q)` therefore realizes the envelope value `ρ(v)`. -/
theorem momentEnvelope_stationary_of_quartic (t q : ℝ) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hquar : envelopeQuartic t q = 0) :
    deriv (fun s => momentEnvelope s q) t = 0 := by
  rw [(momentEnvelope_hasDerivAt t q ht0 ht1).deriv, hquar, zero_div]

/-! ### Sharp upper bound `r(μ) ≤ ρ(v)` via an explicit dual certificate

For a law `μ` on `[0,1]` with first moment `m = ∫ y dμ` and second moment `q = ∫ y² dμ`, one has
`q ≤ m ≤ √q` (since `y² ≤ y` forces `q ≤ m`, and `Var ≥ 0` forces `m² ≤ q`). The dual certificate is
the pointwise polynomial identity (verified by `ring`), with `xᵥ = extremalMid m q`,

    momentEnvelope m q − (y² − b₀ − b₁ y)² − λ(y)  =  y (1 − y) (y − xᵥ)²    (∀ y),

where `b₀ = extremalCoeff0 m q`, `b₁ = extremalCoeff1 m q`, and the multiplier `λ(y)` integrates to
`0` against `μ` (its moment combination `λ₀ + λ₁ m + λ₂ q` vanishes). Integrating `dμ`, the
right side is `∫ y(1−y)(y−xᵥ)² dμ = crossMoment m q m₃ m₄ ≥ 0`, giving `r(μ) ≤ momentEnvelope m q`.
The envelope
`momentEnvelope · q` is then maximized at the quartic root, so `momentEnvelope m q ≤ ρ(v)`. -/

/-- The interior support point `xᵥ = (m² − 2 m q + q) / (2 m (1 − m))` of the extremal three-point
law realizing first moment `m` and second moment `q`. -/
noncomputable def extremalMid (m q : ℝ) : ℝ := (m ^ 2 - 2 * m * q + q) / (2 * m * (1 - m))

/-- The intercept `b₀` of the certificate's linear fit: the regression coefficient of `y²` on `1`
for the extremal three-point law at first moment `m`, second moment `q`. -/
noncomputable def extremalCoeff0 (m q : ℝ) : ℝ := (m * extremalM3 m q - q ^ 2) / (m ^ 2 - q)

/-- The slope `b₁` of the certificate's linear fit: the regression coefficient of `y²` on `y`
for the extremal three-point law at first moment `m`, second moment `q`. -/
noncomputable def extremalCoeff1 (m q : ℝ) : ℝ := (m * q - extremalM3 m q) / (m ^ 2 - q)

/-- The certificate cross moment `∫ y (1 − y) (y − xᵥ)² dμ` of a law with moments
`(1, m, q, m₃, m₄)`, expanded in the moments (`xᵥ = extremalMid m q`). It is nonnegative for every
law supported in `[0,1]` — the integral of a nonnegative polynomial — and equals the certificate
slack `momentEnvelope m q − residualQuad m q m₃ m₄ b₀ b₁`. -/
noncomputable def crossMoment (m q m3 m4 : ℝ) : ℝ :=
  -m4 + (1 + 2 * extremalMid m q) * m3
    - (2 * extremalMid m q + extremalMid m q ^ 2) * q + extremalMid m q ^ 2 * m

/-- **Dual-certificate identity (integrated).** For the certificate's linear-fit coefficients, the
regression objective equals the envelope value minus the cross moment:
`residualQuad m q m₃ m₄ b₀ b₁ = momentEnvelope m q − crossMoment m q m₃ m₄`. This is the
moment-level form of the pointwise SOS certificate, a pure algebraic identity (`ring`) valid for
`m ≠ 0`, `m ≠ 1`, `m² ≠ q`. -/
theorem residualQuad_extremalCoeff_eq (m q m3 m4 : ℝ)
    (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hmq : m ^ 2 ≠ q) :
    residualQuad m q m3 m4 (extremalCoeff0 m q) (extremalCoeff1 m q)
      = momentEnvelope m q - crossMoment m q m3 m4 := by
  have h1m : (1 : ℝ) - m ≠ 0 := by
    intro h
    apply hm1
    linarith
  have hm1' : m - 1 ≠ 0 := sub_ne_zero.mpr hm1
  have hmq' : m ^ 2 - q ≠ 0 := sub_ne_zero.mpr hmq
  unfold residualQuad momentEnvelope crossMoment extremalCoeff0 extremalCoeff1 extremalM3
    extremalMid
  field_simp [hm0, hm1', h1m, hmq']
  ring

/-- **Sharp per-instance bound.** For an admissible moment tuple `(1, m, q, m₃, m₄)` of a law on
`[0,1]` with positive variance (`m² < q`) and nonnegative cross moment
(`0 ≤ crossMoment m q m₃ m₄`, automatic for any law on `[0,1]`), the residual variance of regressing
`y²` on `{1, y}` is at most the envelope value at the law's own first moment:
`momentResidual m q m₃ m₄ ≤ momentEnvelope m q`. -/
theorem momentResidual_le_momentEnvelope (m q m3 m4 : ℝ)
    (hm0 : 0 < m) (hm1 : m < 1) (hmq : m ^ 2 < q)
    (hcross : 0 ≤ crossMoment m q m3 m4) :
    momentResidual m q m3 m4 ≤ momentEnvelope m q := by
  have hmq' : m ^ 2 ≠ q := ne_of_lt hmq
  have hlb := residualQuad_ge_momentResidual m q m3 m4 (extremalCoeff0 m q) (extremalCoeff1 m q) hmq
  have heq := residualQuad_extremalCoeff_eq m q m3 m4 (ne_of_gt hm0) (ne_of_lt hm1) hmq'
  rw [heq] at hlb
  linarith

/-- **Envelope maximality.** Among admissible first moments the envelope `momentEnvelope · q` is
maximized at a quartic root `u = μᵥ`: if `q < u`, `u² < q`, and `envelopeQuartic u q = 0`, then for
every admissible first moment `m` with `q ≤ m`, `m² < q`, one has
`momentEnvelope m q ≤ momentEnvelope u q`.

Certificate (CAS-verified): with `D = 4 m u (m − 1)(u − 1) > 0` and
`L = m u² − m u − q² + 2 q u + u³ − 2 u²`,
`momentEnvelope u q − momentEnvelope m q = (u − m)² (−L) / D + ((u − m)/D) · envelopeQuartic u q`,
where `L < 0` on the admissible region, so the right side is `≥ 0` once the quartic term
vanishes. -/
theorem momentEnvelope_le_root (m q u : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hqm : q ≤ m) (hmq : m ^ 2 < q)
    (hqu : q < u) (huq : u ^ 2 < q) (hroot : envelopeQuartic u q = 0) :
    momentEnvelope m q ≤ momentEnvelope u q := by
  have hm0 : 0 < m := lt_of_lt_of_le hq0 hqm
  have hu0 : 0 < u := lt_trans hq0 hqu
  have hm1 : m < 1 := by nlinarith
  have hu1 : u < 1 := by nlinarith
  have hDpos : 0 < 4 * m * u * (m - 1) * (u - 1) := by
    nlinarith [mul_pos hm0 hu0]
  have hLneg : m * u ^ 2 - m * u - q ^ 2 + 2 * q * u + u ^ 3 - 2 * u ^ 2 < 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqm) (le_of_lt (sub_pos.mpr hqu)),
      mul_nonneg (le_of_lt hu0) (le_of_lt (sub_pos.mpr hqu)),
      mul_nonneg (le_of_lt hm0) (le_of_lt (sub_pos.mpr huq)),
      mul_nonneg (le_of_lt hu0) (le_of_lt (sub_pos.mpr huq))]
  have hmne : m ≠ 0 := ne_of_gt hm0
  have hune : u ≠ 0 := ne_of_gt hu0
  have hm1ne : m - 1 ≠ 0 := by
    intro h
    nlinarith
  have hu1ne : u - 1 ≠ 0 := by
    intro h
    nlinarith
  have h1mne : (1 : ℝ) - m ≠ 0 := by
    intro h
    nlinarith
  have h1une : (1 : ℝ) - u ≠ 0 := by
    intro h
    nlinarith
  have key : momentEnvelope u q - momentEnvelope m q
      =
        (u - m) ^ 2
          * (-(m * u ^ 2 - m * u - q ^ 2 + 2 * q * u + u ^ 3 - 2 * u ^ 2))
          / (4 * m * u * (m - 1) * (u - 1))
        + (u - m) / (4 * m * u * (m - 1) * (u - 1)) * envelopeQuartic u q := by
    unfold momentEnvelope envelopeQuartic
    field_simp [hmne, hune, hm1ne, hu1ne, h1mne, h1une]
    ring
  rw [hroot, mul_zero, add_zero] at key
  have hpos :
      0 ≤ (u - m) ^ 2
        * (-(m * u ^ 2 - m * u - q ^ 2 + 2 * q * u + u ^ 3 - 2 * u ^ 2))
        / (4 * m * u * (m - 1) * (u - 1)) := by
    apply div_nonneg _ (le_of_lt hDpos)
    exact mul_nonneg (sq_nonneg _) (by linarith)
  linarith [key, hpos]

/-- **Conditional moment-level envelope bound.** If the supplied moments have positive variance, a
nonnegative cross moment, and a supplied quartic root `u` satisfying `q < u` and `u² < q`, then the
moment residual for regressing `y²` on `{1, y}` is at most `momentEnvelope u q`.

This theorem combines the per-instance moment bound with envelope maximality. It does not by itself
derive the cross-moment condition from a probability law on `[0,1]`, prove existence or uniqueness
of the root, or state an attainment result. -/
theorem momentResidual_le_envelope (m q m3 m4 u : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hqm : q ≤ m) (hmq : m ^ 2 < q)
    (hcross : 0 ≤ crossMoment m q m3 m4)
    (hqu : q < u) (huq : u ^ 2 < q) (hroot : envelopeQuartic u q = 0) :
    momentResidual m q m3 m4 ≤ momentEnvelope u q := by
  have hm0 : 0 < m := lt_of_lt_of_le hq0 hqm
  have hm1 : m < 1 := by nlinarith
  exact le_trans (momentResidual_le_momentEnvelope m q m3 m4 hm0 hm1 hmq hcross)
    (momentEnvelope_le_root m q u hq0 hq1 hqm hmq hqu huq hroot)

end Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra
