/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# CATE second-order product-bias bound against a test function

This file proves the genuinely *second-order* (double-robustness) bound on the
DR-Learner nuisance bias.  The object is the population integral of the
pseudo-outcome bias `phi_eta(z, η) − phi₀(z)` weighted by an arbitrary bounded
σ(X)-test function `w : γ → ℝ`:

    ∫ z, (phi_eta z η − phi₀ S z) · w z.1 ∂P_Z.

Two results:

* `integral_phiDiff_mul_eq_condBias` — the *conditioning identity*
  `∫ z, (phi_eta z η − phi₀ S z) · w z.1 ∂P_Z = ∫ x, condBias η η₀ x · w x ∂P_X`,
  obtained by pulling the σ(X)-measurable factor `w(X)` through the conditional
  expectation `E[phi_eta − phi₀ | σX] = condBias ∘ X`
  (`phi_eta_minus_phi₀_cond_exp`).  This is the test-function generalisation of
  the `w ≡ 1` identity `aipw_remainder_identity`.

* `abs_integral_phiDiff_mul_le_product` — the **second-order product bound**

    |∫ z, (phi_eta z η − phi₀ S z) · w z.1 ∂P_Z|
        ≤ (B / ε) · Σ_{a} ‖η.μ_fn a − μ_val a‖_{L²(P_X)} · ‖η.e_fn − e_val‖_{L²(P_X)},

  where `B` bounds `|w|`.  Because `condBias η η₀ x` is *manifestly* the bilinear
  product `Σ_a (e − e₀)(μ_a − μ₀_a)/denom_a`, this exhibits the bias as a genuine
  product of the two nuisance errors — the heart of why double machine learning
  works.  This is the concrete quantitative form of the orthogonal statistical-learning second-order bias
  (`def:est-osl-second-order-bias`).

The Cauchy–Schwarz step reuses `integral_abs_mul_le_eLpNorm_mul_eLpNorm`, exactly
as in `aipw_remainder_bound`.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-second-order-bias`.
-/

import Causalean.Estimation.CATE.Core.ConditionalBias
import Causalean.Estimation.ATE.Remainder.Identity
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Second-Order CATE Bias

This file proves that the weighted population bias of the doubly robust CATE
pseudo-outcome is governed by a second-order product of nuisance errors. It
first converts the weighted pseudo-outcome bias into a conditional-bias
integral over covariates with `integral_phiDiff_mul_eq_condBias` and then
bounds that integral in `abs_integral_phiDiff_mul_le_product` by a product of
outcome-regression and propensity-score error norms. -/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
  Causalean.Estimation.ATE

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Conditioning identity for the weighted pseudo-outcome bias.**

For any measurable test function `w : γ → ℝ`, the population integral of the
pseudo-outcome bias `phi_eta(z, η) − phi₀(z)` weighted by `w(z.1)` against `P_Z`
equals the integral of the *conditional* bias `condBias η η₀` weighted by `w`
against `P_X`.  Obtained by pulling the σ(X)-measurable factor `w(X)` through the
conditional expectation `E[phi_eta − phi₀ | σX] = condBias ∘ X`. -/
theorem integral_phiDiff_mul_eq_condBias
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (η : NuisanceVec γ) {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η : η ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_μ_η_int : ∀ a : Bool,
      Integrable (fun ω => η.μ_fn a (S.toBackdoorEstimationSystem.factualX ω)) P.μ)
    (w : γ → ℝ) (hw_meas : Measurable w)
    (h_phi_int :
      Integrable (fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) P.μ)
    (h_phiw_int :
      Integrable (fun ω => (phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) *
        w (S.toBackdoorEstimationSystem.factualX ω)) P.μ) :
    ∫ z, (phi_eta z η - phi₀ S z) * w z.1
        ∂S.toBackdoorEstimationSystem.P_Z
      = ∫ x, condBias η S.toBackdoorEstimationSystem.η₀ x * w x
          ∂S.toBackdoorEstimationSystem.P_X := by
  set X := S.toPOBackdoorSystem.factualX with hX
  set Z := S.toBackdoorEstimationSystem.factualZ with hZ
  -- The conditional-bias identity (σ(X)-form).
  have hcond := phi_eta_minus_phi₀_cond_exp S hA η h_overlap_η h_overlap_η₀
    hε_pos h_μ_η_int
  -- σ(X)-strong measurability of `w ∘ X`.
  have hw_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => w (X ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => w (S.toPOBackdoorSystem.factualX ω))
    exact (hw_meas.comp (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  -- Pull `w ∘ X` out of the conditional expectation of `(phi_eta − phi₀) ∘ Z`.
  have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
    (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hw_sm h_phiw_int h_phi_int
  -- Hence `E[(phi_eta − phi₀)·(w∘X) | σX] =ᵐ (w∘X)·(condBias ∘ X)`.
  have hcond_mul :
      P.μ[fun ω => (phi_eta (Z ω) η - phi₀ S (Z ω)) * w (X ω) |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => w (X ω) *
            condBias η S.toBackdoorEstimationSystem.η₀ (X ω)) := by
    refine hpull.trans ?_
    filter_upwards [hcond] with ω hω
    rw [Pi.mul_apply, hω]; simp only [hX]; ring
  calc
    ∫ z, (phi_eta z η - phi₀ S z) * w z.1
        ∂S.toBackdoorEstimationSystem.P_Z
        = ∫ ω, (phi_eta (Z ω) η - phi₀ S (Z ω)) * w (X ω) ∂P.μ := by
          rw [BackdoorEstimationSystem.P_Z,
            MeasureTheory.integral_map
              S.toBackdoorEstimationSystem.measurable_factualZ.aemeasurable
              (by
                refine ((measurable_phi_eta η).sub (measurable_phi₀ S)).mul
                  (hw_meas.comp measurable_fst) |>.aestronglyMeasurable)]
          rfl
    _ = ∫ ω, P.μ[fun ω => (phi_eta (Z ω) η - phi₀ S (Z ω)) * w (X ω) |
            S.toPOBackdoorSystem.sigmaX] ω ∂P.μ := by
          rw [MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le]
    _ = ∫ ω, w (X ω) *
            condBias η S.toBackdoorEstimationSystem.η₀ (X ω) ∂P.μ :=
          MeasureTheory.integral_congr_ae hcond_mul
    _ = ∫ x, condBias η S.toBackdoorEstimationSystem.η₀ x * w x
            ∂S.toBackdoorEstimationSystem.P_X := by
          rw [BackdoorEstimationSystem.P_X,
            MeasureTheory.integral_map
              S.toPOBackdoorSystem.measurable_factualX.aemeasurable
              (by
                refine (((measurable_condBias η S.toBackdoorEstimationSystem.η₀).mul
                  hw_meas)).aestronglyMeasurable)]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp only [hX]; ring

/-- **Second-order product bias bound for the DR-Learner.**

The population integral of the pseudo-outcome bias weighted by any test function
`w` with `|w| ≤ B` is bounded by the *product* of the two nuisance L²-errors:

    |∫ z, (phi_eta z η − phi₀ S z) · w z.1 ∂P_Z|
        ≤ (B / ε) · Σ_a ‖η.μ_fn a − μ_val a‖_{L²(P_X)} · ‖η.e_fn − e_val‖_{L²(P_X)}.

This is the genuine *second-order* (double-robustness) content: the bias vanishes
to first order in each nuisance separately and is controlled by their product.
It is the concrete quantitative form of the orthogonal statistical-learning second-order bias
(`def:est-osl-second-order-bias`).  Proof: rewrite via
`integral_phiDiff_mul_eq_condBias`, bound `|condBias η η₀ x · w x|` pointwise by
`(B/ε)(|Δμ_T·Δe| + |Δμ_F·Δe|)` using strict overlap, and apply
`integral_abs_mul_le_eLpNorm_mul_eLpNorm` to each summand — exactly the
Cauchy–Schwarz route of `aipw_remainder_bound`. -/
theorem abs_integral_phiDiff_mul_le_product
    (S : CATEEstimationSystem P γ) {ε : ℝ} (hε_pos : 0 < ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (η : NuisanceVec γ)
    (h_overlap_η : η ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_μ_η_int : ∀ a : Bool,
      Integrable (fun ω => η.μ_fn a (S.toBackdoorEstimationSystem.factualX ω)) P.μ)
    (w : γ → ℝ) (hw_meas : Measurable w)
    {B : ℝ} (hB_nonneg : 0 ≤ B) (hw_bound : ∀ x, |w x| ≤ B)
    (h_phi_int :
      Integrable (fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) P.μ)
    (h_phiw_int :
      Integrable (fun ω => (phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) *
        w (S.toBackdoorEstimationSystem.factualX ω)) P.μ)
    (hΔμ_memLp : ∀ a, MemLp
      (fun x => η.μ_fn a x - S.μ_val a x) 2 S.toBackdoorEstimationSystem.P_X)
    (hΔe_memLp : MemLp
      (fun x => η.e_fn x - S.e_val x) 2 S.toBackdoorEstimationSystem.P_X) :
    |∫ z, (phi_eta z η - phi₀ S z) * w z.1
        ∂S.toBackdoorEstimationSystem.P_Z|
      ≤ (B / ε) *
          ∑ a : Bool,
            (eLpNorm (fun x => η.μ_fn a x - S.μ_val a x) 2
              S.toBackdoorEstimationSystem.P_X).toReal *
              (eLpNorm (fun x => η.e_fn x - S.e_val x) 2
                S.toBackdoorEstimationSystem.P_X).toReal := by
  set PX := S.toBackdoorEstimationSystem.P_X with hPX
  set η₀ := S.toBackdoorEstimationSystem.η₀ with hη₀
  haveI : IsFiniteMeasure PX := by rw [hPX]; unfold BackdoorEstimationSystem.P_X; infer_instance
  haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
    constructor; simpa using ENNReal.inv_two_add_inv_two
  have hBε_nonneg : 0 ≤ B / ε := div_nonneg hB_nonneg hε_pos.le
  have hη_lower : ∀ x, ε ≤ η.e_fn x := fun x => (h_overlap_η x).1
  have hη_upper : ∀ x, η.e_fn x ≤ 1 - ε := fun x => (h_overlap_η x).2
  have hη_pos : ∀ x, 0 < η.e_fn x := fun x => lt_of_lt_of_le hε_pos (hη_lower x)
  have hη_false_pos : ∀ x, 0 < 1 - η.e_fn x := by
    intro x; have hx : ε ≤ 1 - η.e_fn x := by linarith [hη_upper x]
    exact lt_of_lt_of_le hε_pos hx
  -- The bound integrand (explicit, so it matches the eLpNorm summands).
  set bnd : γ → ℝ := fun x =>
    (B / ε) * |(η.μ_fn true x - S.μ_val true x) * (η.e_fn x - S.e_val x)| +
      (B / ε) * |(η.μ_fn false x - S.μ_val false x) * (η.e_fn x - S.e_val x)| with hbnd
  -- Pointwise bound `|condBias η η₀ x * w x| ≤ bnd x`.
  have hpoint : ∀ x, |condBias η η₀ x * w x| ≤ bnd x := by
    intro x
    -- Reusable single-arm bound: `|a/c * w x| ≤ (B/ε)·|a|` for `0 < ε ≤ c`.
    have key : ∀ a c : ℝ, 0 < c → ε ≤ c → |a / c * w x| ≤ (B / ε) * |a| := by
      intro a c hc hεc
      have hwc : |w x| / c ≤ B / ε := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul (hw_bound x) ((inv_le_inv₀ hc hε_pos).2 hεc)
          (inv_nonneg.mpr hc.le) hB_nonneg
      calc |a / c * w x| = |a| * (|w x| / c) := by
            rw [abs_mul, abs_div, abs_of_pos hc]; ring
        _ ≤ |a| * (B / ε) := mul_le_mul_of_nonneg_left hwc (abs_nonneg _)
        _ = (B / ε) * |a| := by ring
    -- condBias expands to two arms `(Δμ_a · Δe) / denom_a`.
    have hexp : condBias η η₀ x =
        (η.μ_fn true x - S.μ_val true x) * (η.e_fn x - S.e_val x) / η.e_fn x +
          (η.μ_fn false x - S.μ_val false x) * (η.e_fn x - S.e_val x) /
            (1 - η.e_fn x) := by
      rw [hη₀]
      unfold condBias
      rw [Fintype.sum_bool, if_pos (rfl : (true : Bool) = true),
        if_neg (by decide : ¬((false : Bool) = true))]
      simp only [BackdoorEstimationSystem.η₀]
      ring
    rw [hexp, add_mul]
    refine (abs_add_le _ _).trans ?_
    simp only [hbnd]
    exact add_le_add
      (key _ _ (hη_pos x) (hη_lower x))
      (key _ _ (hη_false_pos x) (by linarith [hη_upper x]))
  -- Integrability of the product terms and of `bnd`.
  have hprod_int : ∀ a, Integrable
      (fun x => (η.μ_fn a x - S.μ_val a x) * (η.e_fn x - S.e_val x)) PX := by
    intro a
    have hmul : MemLp
        (fun x => (η.μ_fn a x - S.μ_val a x) * (η.e_fn x - S.e_val x)) 1 PX := by
      simpa [mul_comm] using (hΔμ_memLp a).mul hΔe_memLp
    exact hmul.integrable le_rfl
  have hbnd_int : Integrable bnd PX := by
    simp only [hbnd]
    exact ((hprod_int true).abs.const_mul (B / ε)).add
      ((hprod_int false).abs.const_mul (B / ε))
  have hcw_meas : Measurable (fun x => condBias η η₀ x * w x) :=
    (measurable_condBias η η₀).mul hw_meas
  have hcw_int : Integrable (fun x => condBias η η₀ x * w x) PX :=
    hbnd_int.mono' hcw_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hpoint x)
  -- Cauchy–Schwarz on each product term.
  have hCS : ∀ a, ∫ x, |(η.μ_fn a x - S.μ_val a x) * (η.e_fn x - S.e_val x)| ∂PX
      ≤ (eLpNorm (fun x => η.μ_fn a x - S.μ_val a x) 2 PX).toReal *
          (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 PX).toReal := by
    intro a
    exact integral_abs_mul_le_eLpNorm_mul_eLpNorm (ν := PX) (hΔμ_memLp a) hΔe_memLp
  -- Assemble.
  rw [integral_phiDiff_mul_eq_condBias S hA η hε_pos h_overlap_η h_overlap_η₀
    h_μ_η_int w hw_meas h_phi_int h_phiw_int]
  calc
    |∫ x, condBias η η₀ x * w x ∂PX|
        ≤ ∫ x, |condBias η η₀ x * w x| ∂PX :=
          MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x, bnd x ∂PX :=
          integral_mono_ae hcw_int.abs hbnd_int (Filter.Eventually.of_forall hpoint)
    _ = (B / ε) * (∫ x, |(η.μ_fn true x - S.μ_val true x) *
              (η.e_fn x - S.e_val x)| ∂PX) +
          (B / ε) * (∫ x, |(η.μ_fn false x - S.μ_val false x) *
              (η.e_fn x - S.e_val x)| ∂PX) := by
          simp only [hbnd]
          rw [integral_add ((hprod_int true).abs.const_mul (B / ε))
            ((hprod_int false).abs.const_mul (B / ε)),
            integral_const_mul, integral_const_mul]
    _ ≤ (B / ε) * ((eLpNorm (fun x => η.μ_fn true x - S.μ_val true x) 2 PX).toReal *
              (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 PX).toReal) +
          (B / ε) * ((eLpNorm (fun x => η.μ_fn false x - S.μ_val false x) 2 PX).toReal *
              (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 PX).toReal) :=
          add_le_add (mul_le_mul_of_nonneg_left (hCS true) hBε_nonneg)
            (mul_le_mul_of_nonneg_left (hCS false) hBε_nonneg)
    _ = (B / ε) *
          ∑ a : Bool,
            (eLpNorm (fun x => η.μ_fn a x - S.μ_val a x) 2 PX).toReal *
              (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 PX).toReal := by
          rw [Fintype.sum_bool]; ring

end CATE
end Estimation
end Causalean
