/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Directional derivative of `phi_eta` in the nuisance argument

This file proves the closed-form directional derivative of the
DR pseudo-outcome `phi_eta z η` (defined in
`Estimation/CATE/Core/PseudoOutcome.lean`) in the nuisance argument `η`,
evaluated at an anchor `g₀ : NuisanceVec γ` along a direction
`v : NuisanceVec γ`.

`phi_eta` is reciprocal in `η.e_fn` (it contains `1 / η.e_fn` and
`1 / (1 − η.e_fn)`), so the directional derivative is *not* the
value-difference `phi_eta z η − phi_eta z g₀`.  The pointwise derivative
in `t` of `phi_eta z (g₀ + t • v)` at `t = 0` admits the closed form

    D_g phi_eta(z, g₀)[v]
      =  (v.μ_fn true X − v.μ_fn false X)
       + indA(z) · ( −v.e_fn X / (g₀.e_fn X)² · (Y − g₀.μ_fn true X)
                       − 1 / g₀.e_fn X · v.μ_fn true X )
       − (1 − indA(z)) · ( v.e_fn X / (1 − g₀.e_fn X)² · (Y − g₀.μ_fn false X)
                              − 1 / (1 − g₀.e_fn X) · v.μ_fn false X )

(matching the docstring of `NuisanceDirDeriv` in
`Estimation/CATE/OrthogonalLearning/DRLearner/Analytic.lean`).

Under strict overlap (`g₀ ∈ H_ε`), the pointwise difference quotient

    (phi_eta z (g₀ + t • v) − phi_eta z g₀) / t

converges to this closed form as `t → 0` (a routine real-analysis
calculation: derivative of `t ↦ 1 / (a + t b)` at `t = 0`).

This file provides:
* `phi_eta_dir_deriv g₀ v z`           — the closed form above.
* `measurable_phi_eta_dir_deriv`       — measurability in `z`.
* `phi_eta_dir_deriv_tendsto`          — pointwise convergence of the
                                         difference quotient.

Used by `Estimation/CATE/OrthogonalLearning/DRLearner/Analytic.lean` to identify the opaque
`NuisanceDirDeriv.dPhi` field with the closed form via uniqueness of
limits, and downstream by `cond_exp_phi_eta_dir_deriv_at_truth_zero`
(in `Estimation/CATE/ConditionalBias.lean` or this file) to conclude
that the σ(X)-conditional of the closed form is zero a.e. at the truth.
-/

import Causalean.Estimation.CATE.Core.PseudoOutcome
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Computes directional derivatives for CATE doubly robust pseudo-outcome maps. The
definition `phi_eta_dir_deriv` gives the closed-form derivative in a nuisance
direction, `measurable_phi_eta_dir_deriv` proves measurability in the data
argument, and `phi_eta_dir_deriv_tendsto` proves convergence of the pointwise
difference quotient under strict overlap.

These derivative formulas are the analytic core of the CATE orthogonality and
second-order bias arguments, including the conditional mean-zero result for the
derivative at the truth in `ConditionalBias.lean`.
-/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE BackdoorEstimationSystem

variable {γ : Type*} [MeasurableSpace γ]

/-! ## Closed-form directional derivative -/

/-- Closed-form directional derivative of `phi_eta z η` in `η` at `g₀`
along the direction `v : NuisanceVec γ`.

See the file docstring for the formula.  At the truth (`g₀ = η₀`) and
under strict overlap, the σ(X)-conditional of this is zero a.e. — the
content of `cond_exp_phi_eta_dir_deriv_at_truth_zero`. -/
noncomputable def phi_eta_dir_deriv
    (g₀ v : NuisanceVec γ) (z : γ × Bool × ℝ) : ℝ :=
  (v.μ_fn true (projX z) - v.μ_fn false (projX z))
    + indA z * (- v.e_fn (projX z) / (g₀.e_fn (projX z))^2 *
                   (projY z - g₀.μ_fn true (projX z))
                 - 1 / g₀.e_fn (projX z) * v.μ_fn true (projX z))
    - (1 - indA z) * (v.e_fn (projX z) / (1 - g₀.e_fn (projX z))^2 *
                       (projY z - g₀.μ_fn false (projX z))
                     - 1 / (1 - g₀.e_fn (projX z)) * v.μ_fn false (projX z))

/-- `phi_eta_dir_deriv g₀ v` is measurable in `z`. -/
lemma measurable_phi_eta_dir_deriv (g₀ v : NuisanceVec γ) :
    Measurable (fun z : γ × Bool × ℝ => phi_eta_dir_deriv g₀ v z) := by
  unfold phi_eta_dir_deriv indA projX projA projY
  have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
  have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
  have hμvT : Measurable (fun z : γ × Bool × ℝ => v.μ_fn true z.1) :=
    (v.μ_meas true).comp hx
  have hμvF : Measurable (fun z : γ × Bool × ℝ => v.μ_fn false z.1) :=
    (v.μ_meas false).comp hx
  have hev : Measurable (fun z : γ × Bool × ℝ => v.e_fn z.1) :=
    v.e_meas.comp hx
  have hμgT : Measurable (fun z : γ × Bool × ℝ => g₀.μ_fn true z.1) :=
    (g₀.μ_meas true).comp hx
  have hμgF : Measurable (fun z : γ × Bool × ℝ => g₀.μ_fn false z.1) :=
    (g₀.μ_meas false).comp hx
  have heg : Measurable (fun z : γ × Bool × ℝ => g₀.e_fn z.1) :=
    g₀.e_meas.comp hx
  have hind : Measurable (fun z : γ × Bool × ℝ =>
      if z.2.1 = true then (1 : ℝ) else 0) := by
    have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
    exact (Measurable.of_discrete
      (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
  have hbase : Measurable (fun z : γ × Bool × ℝ =>
      v.μ_fn true z.1 - v.μ_fn false z.1) := hμvT.sub hμvF
  -- Inner bracket of the indA branch.
  have hbrA : Measurable (fun z : γ × Bool × ℝ =>
      -v.e_fn z.1 / (g₀.e_fn z.1)^2 * (z.2.2 - g₀.μ_fn true z.1)
        - 1 / g₀.e_fn z.1 * v.μ_fn true z.1) := by
    have h1 : Measurable (fun z : γ × Bool × ℝ =>
        -v.e_fn z.1 / (g₀.e_fn z.1)^2) :=
      hev.neg.div (heg.pow_const 2)
    have h2 : Measurable (fun z : γ × Bool × ℝ =>
        z.2.2 - g₀.μ_fn true z.1) := hy.sub hμgT
    have h3 : Measurable (fun z : γ × Bool × ℝ =>
        (1 : ℝ) / g₀.e_fn z.1) := measurable_const.div heg
    exact (h1.mul h2).sub (h3.mul hμvT)
  -- Inner bracket of the (1-indA) branch.
  have hbrB : Measurable (fun z : γ × Bool × ℝ =>
      v.e_fn z.1 / (1 - g₀.e_fn z.1)^2 * (z.2.2 - g₀.μ_fn false z.1)
        - 1 / (1 - g₀.e_fn z.1) * v.μ_fn false z.1) := by
    have h1m : Measurable (fun z : γ × Bool × ℝ => 1 - g₀.e_fn z.1) :=
      measurable_const.sub heg
    have h1 : Measurable (fun z : γ × Bool × ℝ =>
        v.e_fn z.1 / (1 - g₀.e_fn z.1)^2) :=
      hev.div (h1m.pow_const 2)
    have h2 : Measurable (fun z : γ × Bool × ℝ =>
        z.2.2 - g₀.μ_fn false z.1) := hy.sub hμgF
    have h3 : Measurable (fun z : γ × Bool × ℝ =>
        (1 : ℝ) / (1 - g₀.e_fn z.1)) := measurable_const.div h1m
    exact (h1.mul h2).sub (h3.mul hμvF)
  exact (hbase.add (hind.mul hbrA)).sub
    ((measurable_const.sub hind).mul hbrB)

/-! ## Pointwise tendsto under strict overlap -/

private lemma phi_eta_real_line_hasDerivAt
    (m1 m0 e y a dm1 dm0 de : ℝ) (he : e ≠ 0) (h1e : 1 - e ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        ((m1 + t * dm1) - (m0 + t * dm0))
          + (a / (e + t * de)) * (y - (m1 + t * dm1))
          - ((1 - a) / (1 - (e + t * de))) * (y - (m0 + t * dm0))
          - 0)
      (dm1 - dm0 - (a / e) * dm1 - (a / e ^ 2) * (y - m1) * de
        + ((1 - a) / (1 - e)) * dm0
        - ((1 - a) / (1 - e) ^ 2) * (y - m0) * de) 0 := by
  have h_m1 : HasDerivAt (fun t : ℝ => m1 + t * dm1) dm1 0 := by
    simpa only [Pi.add_apply, zero_add, one_mul] using
      (hasDerivAt_const (0 : ℝ) m1).add ((hasDerivAt_id (0 : ℝ)).mul_const dm1)
  have h_m0 : HasDerivAt (fun t : ℝ => m0 + t * dm0) dm0 0 := by
    simpa only [Pi.add_apply, zero_add, one_mul] using
      (hasDerivAt_const (0 : ℝ) m0).add ((hasDerivAt_id (0 : ℝ)).mul_const dm0)
  have h_e : HasDerivAt (fun t : ℝ => e + t * de) de 0 := by
    simpa only [Pi.add_apply, zero_add, one_mul] using
      (hasDerivAt_const (0 : ℝ) e).add ((hasDerivAt_id (0 : ℝ)).mul_const de)
  have h_one_sub_e : HasDerivAt (fun t : ℝ => 1 - (e + t * de)) (-de) 0 := by
    change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - fun t : ℝ => e + t * de) (-de) 0
    simpa only [Pi.sub_apply, zero_sub] using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub h_e
  have h_term1 :
      HasDerivAt (fun t : ℝ => (m1 + t * dm1) - (m0 + t * dm0))
        (dm1 - dm0) 0 :=
    h_m1.sub h_m0
  have h_term2 :
      HasDerivAt
        (fun t : ℝ => (a / (e + t * de)) * (y - (m1 + t * dm1)))
        (-(a / e) * dm1 - (a / e ^ 2) * (y - m1) * de) 0 := by
    change HasDerivAt (((fun _ : ℝ => a) / (fun t : ℝ => e + t * de)) *
      ((fun _ : ℝ => y) - (fun t : ℝ => m1 + t * dm1))) _ 0
    convert ((hasDerivAt_const (0 : ℝ) a).div h_e
        (by simpa only [zero_mul, add_zero] using he)).mul
        ((hasDerivAt_const (0 : ℝ) y).sub h_m1) using 1
    simp only [Pi.div_apply, Pi.sub_apply, zero_mul, add_zero]
    field_simp [he]
    ring
  have h_term3 :
      HasDerivAt
        (fun t : ℝ =>
          ((1 - a) / (1 - (e + t * de))) * (y - (m0 + t * dm0)))
        (((1 - a) / (1 - e) ^ 2) * (y - m0) * de
          - ((1 - a) / (1 - e)) * dm0) 0 := by
    change HasDerivAt
      (((fun _ : ℝ => 1 - a) / (fun t : ℝ => 1 - (e + t * de))) *
        ((fun _ : ℝ => y) - (fun t : ℝ => m0 + t * dm0))) _ 0
    convert ((hasDerivAt_const (0 : ℝ) (1 - a)).div h_one_sub_e
        (by simpa only [zero_mul, add_zero] using h1e)).mul
        ((hasDerivAt_const (0 : ℝ) y).sub h_m0) using 1
    simp only [Pi.div_apply, Pi.sub_apply, zero_mul, add_zero]
    field_simp [h1e]
    ring
  convert ((h_term1.add h_term2).sub h_term3).sub (hasDerivAt_const (0 : ℝ) (0 : ℝ)) using 1
  ring

/-- Pointwise convergence of the difference quotient of `phi_eta` in the
nuisance argument to the closed-form directional derivative, under strict
overlap on the anchor `g₀`.

Proof sketch: write
`phi_eta z (g₀ + t • v) - phi_eta z g₀` as the sum of three pieces

  * linear-in-`t` outcome part `t · (v.μ_fn true X − v.μ_fn false X)`,
  * indicator-`A` reciprocal part involving `1/(g₀.e_fn X + t·v.e_fn X)`,
  * indicator-`(1−A)` reciprocal part involving
    `1/(1 − g₀.e_fn X − t·v.e_fn X)`.

Divide by `t` and apply `Filter.Tendsto.add` / `.sub` plus
elementary `tendsto_div_*` lemmas; the denominators `g₀.e_fn X` and
`1 − g₀.e_fn X` are nonzero by strict overlap (`H_ε`), so the
limit is well-defined and equals the closed form.

This theorem records the analytic content needed by the downstream
orthogonality construction. -/
theorem phi_eta_dir_deriv_tendsto
    (g₀ v : NuisanceVec γ) {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_g₀ : g₀ ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (z : γ × Bool × ℝ) :
    Tendsto (fun t : ℝ => (phi_eta z (g₀ + t • v) - phi_eta z g₀) / t)
      (𝓝[≠] 0) (𝓝 (phi_eta_dir_deriv g₀ v z)) := by
  let x := projX z
  let a := indA z
  let y := projY z
  let m1 := g₀.μ_fn true x
  let m0 := g₀.μ_fn false x
  let e := g₀.e_fn x
  let dm1 := v.μ_fn true x
  let dm0 := v.μ_fn false x
  let de := v.e_fn x
  have he_pos : 0 < e := by
    exact lt_of_lt_of_le hε_pos (h_overlap_g₀ x).1
  have he : e ≠ 0 := ne_of_gt he_pos
  have h1e_pos : 0 < 1 - e := by
    have he_lt_one : e < 1 := by
      calc
        e ≤ 1 - ε := by simpa [e, x] using (h_overlap_g₀ x).2
        _ < 1 := sub_lt_self 1 hε_pos
    exact sub_pos.mpr he_lt_one
  have h1e : 1 - e ≠ 0 := ne_of_gt h1e_pos
  have hderiv :
      HasDerivAt
        (fun t : ℝ => phi_eta z (g₀ + t • v))
        (phi_eta_dir_deriv g₀ v z) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        ((m1 + t * dm1) - (m0 + t * dm0))
          + (a / (e + t * de)) * (y - (m1 + t * dm1))
          - ((1 - a) / (1 - (e + t * de))) * (y - (m0 + t * dm0))
          - 0)
      (phi_eta_dir_deriv g₀ v z) 0
    convert phi_eta_real_line_hasDerivAt m1 m0 e y a dm1 dm0 de he h1e using 1
    unfold phi_eta_dir_deriv
    dsimp [x, a, y, m1, m0, e, dm1, dm0, de]
    have he' : g₀.e_fn (projX z) ≠ 0 := by simpa [e, x] using he
    have h1e' : 1 - g₀.e_fn (projX z) ≠ 0 := by simpa [e, x] using h1e
    field_simp [he', h1e', pow_two]
    ring
  simpa [div_eq_inv_mul] using hderiv.tendsto_slope_zero

end CATE
end Estimation
end Causalean
