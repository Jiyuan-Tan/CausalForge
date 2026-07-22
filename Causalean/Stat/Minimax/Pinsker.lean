/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Pinsker's inequality: total variation controlled by KL divergence

This file bridges the elementary total-variation distance `tvDist`
(`Causalean/Stat/Minimax/TotalVariation.lean`) and Mathlib's Kullback–Leibler
divergence `InformationTheory.klDiv`.  The headline statement is **Pinsker's
inequality**

  `tvDist μ ν ≤ √((klDiv μ ν).toReal / 2)`,

which makes the Le Cam two-point lower bound (`half_one_sub_tvDist_le_max_error`)
usable for concrete two-point families where KL is computable (e.g. Gaussians).

The classical proof has two ingredients:

* a **Scheffé inequality** bounding `tvDist μ ν` by
  `(1/2) * ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν` when `μ ≪ ν`; and
* the scalar analytic bound `klFun x ≥ (3/2) * (x-1)^2 / (x+2)` for `x ≥ 0`,
  combined with Cauchy–Schwarz and `∫ (p+2) ∂ν = 3`.

## Main results

* `klFun_lower_bound` — the elementary scalar inequality
  `(3/2) * (x-1)^2 / (x+2) ≤ klFun x` for `0 ≤ x`. **Proven unconditionally.**
* `PinskerBound` — a `Prop` packaging the Pinsker inequality for a pair `(μ, ν)`.
* `pinskerBound_of_ac_of_ne_top` — **Pinsker's inequality, proven unconditionally**:
  for probability measures `μ ≪ ν` with `klDiv μ ν ≠ ⊤`, `PinskerBound μ ν` holds.
* `pinskerBound_pi_iid` — the i.i.d.-product corollary (product Pinsker from
  one-sample `μ ≪ ν` + `Integrable (llr μ ν) μ`).
* `klForm_two_point_lower_bound{,_of_pinsker}` — the KL-form minimax lower bound:
  given `2s`-separation, every estimator has worst-case error `≥ (1 - √(KL/2))/2`.
  The `_of_pinsker` form consumes a supplied `PinskerBound` term; the unconditional
  form derives it from `μ ≪ ν` + finite KL via `pinskerBound_of_ac_of_ne_top`.

Both halves of the bridge are discharged in this project: the scalar engine
`klFun_lower_bound`, the Scheffé `≤`-inequality
(`tvDist_le_half_integral_abs_rnDeriv`, `Causalean/Stat/Minimax/Scheffe.lean`), and
the weighted Cauchy-Schwarz assembly using the `√(p+2)` factor. `PinskerBound`
remains as reusable `Prop` packaging for downstream theorems, while
`pinskerBound_of_ac_of_ne_top` constructs it from absolute continuity and finite
KL divergence.
-/

import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.Scheffe
import Causalean.Mathlib.InformationTheory.ProductKLLeCam
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
Proves Pinsker's inequality and its KL-form Le Cam minimax lower-bound corollaries.

The file first proves the scalar inequality `klFun_lower_bound`, then packages
total-variation control as `PinskerBound`.  The main bridge
`pinskerBound_of_ac_of_ne_top` derives that package for probability measures
`μ ≪ ν` with finite KL divergence.  The product theorem
`pinskerBound_pi_iid` lifts the bridge to i.i.d. finite products, and the
`klForm_two_point_lower_bound` theorems turn the bridge into Le Cam lower bounds
whose right-hand divergence term is Kullback-Leibler rather than total variation.
-/

namespace Causalean.Stat

open MeasureTheory Real
open scoped ENNReal

open InformationTheory

/-! ### The scalar analytic inequality

The engine of Pinsker's inequality is the pointwise bound on `klFun x = x log x + 1 - x`:

  `(3/2) * (x - 1)^2 / (x + 2) ≤ klFun x`  for `x ≥ 0`.

Equivalently, writing `g x = klFun x - (3/2)(x-1)^2/(x+2)`, one has `g 1 = 0` and `g` is
decreasing on `[0,1]` and increasing on `[1,∞)`.  We prove it via the auxiliary function
`h x = (x + 2) * klFun x - (3/2) * (x - 1)^2` which is nonnegative on `[0,∞)`. -/

/-- The cleared-denominator Pinsker function `φ x = (x+2)·klFun x - (3/2)(x-1)²`. -/
private noncomputable def pinskerPhi (x : ℝ) : ℝ :=
  (x + 2) * klFun x - (3 / 2) * (x - 1) ^ 2

/-- First derivative of `pinskerPhi`: `φ' x = 2(x+1) log x - 4(x-1)`. -/
private theorem hasDerivAt_pinskerPhi {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerPhi (2 * (x + 1) * Real.log x - 4 * (x - 1)) x := by
  have hk : HasDerivAt klFun (Real.log x) x := hasDerivAt_klFun (ne_of_gt hx)
  have hxlog : HasDerivAt (fun y => (y + 2) * klFun y)
      (klFun x + (x + 2) * Real.log x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y + 2) 1 x := by
      simpa using (hasDerivAt_id x).add_const 2
    have := h1.mul hk
    simpa using this
  have hsq : HasDerivAt (fun y : ℝ => (3 / 2) * (y - 1) ^ 2) (3 * (x - 1)) x := by
    have h2 : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
      have := ((hasDerivAt_id x).sub_const 1).pow 2
      simpa [mul_comm] using this
    have := h2.const_mul (3 / 2 : ℝ)
    convert this using 1; ring
  have := hxlog.sub hsq
  convert this using 1
  rw [klFun]; ring

/-- Second derivative of `pinskerPhi`'s derivative: `φ'' x = 2(log x + 1/x - 1)`. -/
private theorem hasDerivAt_pinskerDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => 2 * (y + 1) * Real.log y - 4 * (y - 1))
      (2 * (Real.log x + 1 / x - 1)) x := by
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx)
  have h1 : HasDerivAt (fun y : ℝ => 2 * (y + 1)) 2 x := by
    have : HasDerivAt (fun y : ℝ => 2 * (y + 1)) (2 * 1) x :=
      (((hasDerivAt_id x).add_const 1).const_mul 2)
    simpa using this
  have hprod : HasDerivAt (fun y : ℝ => 2 * (y + 1) * Real.log y)
      (2 * Real.log x + 2 * (x + 1) * (1 / x)) x := by
    have := h1.mul hlog
    convert this using 1
  have hlin : HasDerivAt (fun y : ℝ => 4 * (y - 1)) 4 x := by
    have : HasDerivAt (fun y : ℝ => 4 * (y - 1)) (4 * 1) x :=
      (((hasDerivAt_id x).sub_const 1).const_mul 4)
    simpa using this
  have := hprod.sub hlin
  convert this using 1
  field_simp
  ring

/-- `φ'' x = 2(log x + 1/x - 1) ≥ 0` for `x > 0`, since `log(1/x) ≤ 1/x - 1`. -/
private theorem pinskerSecondDeriv_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ 2 * (Real.log x + 1 / x - 1) := by
  have hinv : Real.log (1 / x) ≤ 1 / x - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one] at hinv
  -- hinv : 0 - log x ≤ 1/x - 1
  nlinarith [hinv]

/-- `φ'` is monotone on `(0,∞)` (since `φ'' ≥ 0`). -/
private theorem pinskerDeriv_monotone :
    MonotoneOn (fun y => 2 * (y + 1) * Real.log y - 4 * (y - 1)) (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro y hy
    exact ((hasDerivAt_pinskerDeriv (hy : (0:ℝ) < y)).continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    exact (hasDerivAt_pinskerDeriv hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    rw [(hasDerivAt_pinskerDeriv hy).deriv]
    exact pinskerSecondDeriv_nonneg hy

/-- Abbreviation for `φ'`. -/
private noncomputable def pinskerDeriv (y : ℝ) : ℝ :=
  2 * (y + 1) * Real.log y - 4 * (y - 1)

private theorem pinskerDeriv_one : pinskerDeriv 1 = 0 := by simp [pinskerDeriv]

private theorem pinskerPhi_one : pinskerPhi 1 = 0 := by simp [pinskerPhi, klFun]

/-- `deriv pinskerPhi y = pinskerDeriv y` for `y > 0`. -/
private theorem deriv_pinskerPhi {y : ℝ} (hy : 0 < y) :
    deriv pinskerPhi y = pinskerDeriv y :=
  (hasDerivAt_pinskerPhi hy).deriv

/-- `φ' ≥ 0` on `[1,∞)` and `φ' ≤ 0` on `(0,1]`, from monotonicity of `φ'` and `φ'(1)=0`. -/
private theorem pinskerDeriv_sign {y : ℝ} (hy : 0 < y) :
    (1 ≤ y → 0 ≤ pinskerDeriv y) ∧ (y ≤ 1 → pinskerDeriv y ≤ 0) := by
  have hmono := pinskerDeriv_monotone
  constructor
  · intro h1
    have := hmono (Set.mem_Ioi.mpr (by norm_num : (0:ℝ) < 1)) (Set.mem_Ioi.mpr hy) h1
    simpa [pinskerDeriv, pinskerDeriv_one] using this
  · intro h1
    have := hmono (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr (by norm_num : (0:ℝ) < 1)) h1
    simpa [pinskerDeriv, pinskerDeriv_one] using this

/-- `pinskerPhi` is monotone on `[1,∞)`. -/
private theorem pinskerPhi_monotone_Ici :
    MonotoneOn pinskerPhi (Set.Ici 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
  · intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    exact ((hasDerivAt_pinskerPhi hy0).continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0:ℝ) < y := lt_trans one_pos hy
    exact (hasDerivAt_pinskerPhi hy0).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0:ℝ) < y := lt_trans one_pos hy
    rw [deriv_pinskerPhi hy0]
    exact (pinskerDeriv_sign hy0).1 (le_of_lt hy)

/-- `pinskerPhi` is antitone on `(0,1]`. -/
private theorem pinskerPhi_antitone_Ioc :
    AntitoneOn pinskerPhi (Set.Ioc 0 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) ?_ ?_ ?_
  · intro y hy
    exact ((hasDerivAt_pinskerPhi hy.1).continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    exact (hasDerivAt_pinskerPhi hy.1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    rw [deriv_pinskerPhi hy.1]
    exact (pinskerDeriv_sign hy.1).2 (le_of_lt hy.2)

/-- Auxiliary: `pinskerPhi x ≥ 0` for `x ≥ 0`, i.e.
`(x + 2) * klFun x - (3/2) * (x - 1)^2 ≥ 0`. -/
theorem klFun_mul_lower_aux {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x + 2) * klFun x - (3 / 2) * (x - 1) ^ 2 := by
  suffices h : 0 ≤ pinskerPhi x by simpa [pinskerPhi] using h
  rcases eq_or_lt_of_le hx with h0 | h0
  · -- x = 0
    rw [← h0]; norm_num [pinskerPhi, klFun]
  rcases le_total x 1 with hle | hge
  · -- 0 < x ≤ 1: φ antitone, so φ x ≥ φ 1 = 0
    have := pinskerPhi_antitone_Ioc (Set.mem_Ioc.mpr ⟨h0, hle⟩)
      (Set.mem_Ioc.mpr ⟨one_pos, le_refl 1⟩) hle
    rw [pinskerPhi_one] at this
    exact this
  · -- 1 ≤ x: φ monotone, so φ x ≥ φ 1 = 0
    have := pinskerPhi_monotone_Ici (Set.mem_Ici.mpr (le_refl 1))
      (Set.mem_Ici.mpr hge) hge
    rw [pinskerPhi_one] at this
    exact this

/-- **Pinsker scalar inequality.** For `x ≥ 0`,
`(3/2) * (x - 1)^2 / (x + 2) ≤ klFun x`.  This is the elementary bound that powers
Pinsker's inequality through Cauchy–Schwarz. -/
theorem klFun_lower_bound {x : ℝ} (hx : 0 ≤ x) :
    (3 / 2) * (x - 1) ^ 2 / (x + 2) ≤ klFun x := by
  have hpos : (0 : ℝ) < x + 2 := by linarith
  rw [div_le_iff₀ hpos]
  have h := klFun_mul_lower_aux hx
  nlinarith [h]

/-! ### Pinsker's inequality and the KL-form Le Cam bound -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Pinsker-type control of total variation by KL divergence:
`tvDist μ ν ≤ √((klDiv μ ν).toReal / 2)`.

A reusable `Prop` packaging of the bound for a pair `(μ, ν)`.  It is constructed
by `pinskerBound_of_ac_of_ne_top` whenever `μ ≪ ν` and `klDiv μ ν ≠ ⊤` (note:
under `.toReal`, `klDiv = ⊤` collapses to `0`, so those two hypotheses are
genuinely required; the bound is false without them). The `_of_pinsker` lemmas
below take a supplied term of this `Prop`. -/
def PinskerBound (μ ν : Measure Ω) : Prop :=
  tvDist μ ν ≤ Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2)

private theorem pinsker_weight_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x - 1) ^ 2 / (x + 2) := by
  exact div_nonneg (sq_nonneg _) (by linarith)

private theorem pinsker_weight_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    (x - 1) ^ 2 / (x + 2) ≤ (2 / 3) * klFun x := by
  have h := klFun_lower_bound hx
  have ha : (3 / 2) * ((x - 1) ^ 2 / (x + 2)) ≤ klFun x := by
    convert h using 1
    ring
  nlinarith

private theorem pinsker_abs_div_sqrt_sq {x : ℝ} (hx : 0 ≤ x) :
    (|x - 1| / Real.sqrt (x + 2)) ^ 2 = (x - 1) ^ 2 / (x + 2) := by
  have hpos : 0 < x + 2 := by linarith
  have hsqrt : Real.sqrt (x + 2) ^ 2 = x + 2 := Real.sq_sqrt (le_of_lt hpos)
  rw [div_pow, hsqrt, sq_abs]

private theorem pinsker_abs_div_sqrt_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (|x - 1| / Real.sqrt (x + 2)) * Real.sqrt (x + 2) = |x - 1| := by
  have hpos : 0 < x + 2 := by linarith
  exact div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos_of_pos hpos))

private theorem pinsker_half_sqrt_two_mul (K : ℝ) (hK : 0 ≤ K) :
    (1 / 2) * Real.sqrt (2 * K) = Real.sqrt (K / 2) := by
  have h2K : 0 ≤ 2 * K := by nlinarith
  have hleft : 0 ≤ (1 / 2) * Real.sqrt (2 * K) := by positivity
  symm
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) hleft]
  rw [mul_pow, Real.sq_sqrt h2K]
  ring

/-- **Pinsker's inequality (unconditional).** For probability measures `μ ≪ ν`
with finite KL divergence, `tvDist μ ν ≤ √((klDiv μ ν).toReal / 2)`. -/
theorem pinskerBound_of_ac_of_ne_top (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hfin : InformationTheory.klDiv μ ν ≠ ⊤) :
    PinskerBound μ ν := by
  set p : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal with hp_def
  set K : ℝ := (InformationTheory.klDiv μ ν).toReal with hK_def
  set g : Ω → ℝ := fun x => (p x - 1) ^ 2 / (p x + 2) with hg_def
  set f₁ : Ω → ℝ := fun x => |p x - 1| / Real.sqrt (p x + 2) with hf₁_def
  set f₂ : Ω → ℝ := fun x => Real.sqrt (p x + 2) with hf₂_def
  have hp_nonneg : ∀ x, 0 ≤ p x := by
    intro x
    rw [hp_def]
    exact ENNReal.toReal_nonneg
  have hK_nonneg : 0 ≤ K := by
    rw [hK_def]
    exact ENNReal.toReal_nonneg
  have hp_int : Integrable p ν := by
    rw [hp_def]
    exact Measure.integrable_toReal_rnDeriv
  have hp_meas : AEStronglyMeasurable p ν := by
    rw [hp_def]
    exact (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aestronglyMeasurable
  have hp_integral_one : ∫ x, p x ∂ν = 1 := by
    rw [hp_def, Measure.integral_toReal_rnDeriv hac]
    rw [measureReal_def, measure_univ]
    simp
  have hllr_int : Integrable (llr μ ν) μ :=
    (InformationTheory.klDiv_ne_top_iff.mp hfin).2
  have hkl_int : Integrable (fun x => klFun (p x)) ν := by
    rw [hp_def]
    exact (InformationTheory.integrable_klFun_rnDeriv_iff hac).2 hllr_int
  have hK_eq_integral : K = ∫ x, klFun (p x) ∂ν := by
    rw [hK_def, hp_def]
    exact InformationTheory.toReal_klDiv_eq_integral_klFun hac
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    rw [hg_def]
    exact pinsker_weight_nonneg (hp_nonneg x)
  have hg_le : ∀ x, g x ≤ (2 / 3) * klFun (p x) := by
    intro x
    rw [hg_def]
    exact pinsker_weight_le_klFun (hp_nonneg x)
  have hg_meas : AEStronglyMeasurable g ν := by
    rw [hg_def]
    exact (by fun_prop : AEMeasurable (fun x => (p x - 1) ^ 2 / (p x + 2)) ν)
      |>.aestronglyMeasurable
  have hf₂_meas : AEStronglyMeasurable f₂ ν := by
    rw [hf₂_def]
    fun_prop
  have hf₁_meas : AEStronglyMeasurable f₁ ν := by
    rw [hf₁_def]
    exact (by fun_prop : AEMeasurable (fun x => |p x - 1| / Real.sqrt (p x + 2)) ν)
      |>.aestronglyMeasurable
  have hg_int : Integrable g ν := by
    refine Integrable.mono' (hkl_int.const_mul (2 / 3)) hg_meas ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg x)]
      exact hg_le x
  have hg_integral_le : ∫ x, g x ∂ν ≤ (2 / 3) * K := by
    have hdom_int : Integrable (fun x => (2 / 3) * klFun (p x)) ν :=
      hkl_int.const_mul (2 / 3)
    have hle_int : ∫ x, g x ∂ν ≤ ∫ x, (2 / 3) * klFun (p x) ∂ν :=
      integral_mono_ae hg_int hdom_int (Filter.Eventually.of_forall hg_le)
    calc
      ∫ x, g x ∂ν ≤ ∫ x, (2 / 3) * klFun (p x) ∂ν := hle_int
      _ = (2 / 3) * K := by rw [integral_const_mul, ← hK_eq_integral]
  have hf₁_sq_int : Integrable (fun x => f₁ x ^ 2) ν := by
    refine hg_int.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hf₁_def, hg_def]
    exact (pinsker_abs_div_sqrt_sq (hp_nonneg x)).symm
  have hf₂_sq_int : Integrable (fun x => f₂ x ^ 2) ν := by
    refine (hp_int.add (integrable_const 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hf₂_def]
    exact (Real.sq_sqrt (by linarith [hp_nonneg x] : 0 ≤ p x + 2)).symm
  have hf₁L2 : MemLp f₁ (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hf₁_meas).2 hf₁_sq_int
  have hf₂L2 : MemLp f₂ (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hf₂_meas).2 hf₂_sq_int
  have hf₁_nonneg : 0 ≤ᵐ[ν] f₁ := Filter.Eventually.of_forall fun x => by
    rw [hf₁_def]
    exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hf₂_nonneg : 0 ≤ᵐ[ν] f₂ := Filter.Eventually.of_forall fun x => by
    rw [hf₂_def]
    exact Real.sqrt_nonneg _
  have hholder :
      ∫ x, f₁ x * f₂ x ∂ν
        ≤ (∫ x, f₁ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
          * (∫ x, f₂ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hf₁_nonneg hf₂_nonneg hf₁L2 hf₂L2
  have hLHS : ∫ x, f₁ x * f₂ x ∂ν = ∫ x, |p x - 1| ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [hf₁_def, hf₂_def]
      exact pinsker_abs_div_sqrt_mul_sqrt (hp_nonneg x)
  have hf₁_rpow : ∫ x, f₁ x ^ (2 : ℝ) ∂ν = ∫ x, g x ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [hf₁_def, hg_def]
      change (|p x - 1| / √(p x + 2)) ^ (2 : ℝ) = (p x - 1) ^ 2 / (p x + 2)
      rw [Real.rpow_two]
      exact pinsker_abs_div_sqrt_sq (hp_nonneg x)
  have hf₂_rpow : ∫ x, f₂ x ^ (2 : ℝ) ∂ν = 3 := by
    have hsqrt_sq : ∫ x, f₂ x ^ (2 : ℝ) ∂ν = ∫ x, p x + 2 ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        rw [hf₂_def]
        change √(p x + 2) ^ (2 : ℝ) = p x + 2
        rw [Real.rpow_two]
        exact Real.sq_sqrt (by linarith [hp_nonneg x] : 0 ≤ p x + 2)
    rw [hsqrt_sq]
    calc
      ∫ x, p x + 2 ∂ν = (∫ x, p x ∂ν) + ∫ _ : Ω, (2 : ℝ) ∂ν :=
        integral_add hp_int (integrable_const 2)
      _ = 3 := by rw [hp_integral_one]; norm_num
  have h_int_abs : ∫ x, |p x - 1| ∂ν ≤ Real.sqrt (2 * K) := by
    rw [hLHS, hf₁_rpow, hf₂_rpow] at hholder
    have hrpow_g : (∫ x, g x ∂ν) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ x, g x ∂ν) :=
      (Real.sqrt_eq_rpow (∫ x, g x ∂ν)).symm
    have hrpow_three : (3 : ℝ) ^ (1 / (2 : ℝ)) = Real.sqrt 3 :=
      (Real.sqrt_eq_rpow 3).symm
    rw [hrpow_g, hrpow_three] at hholder
    have hg_int_nonneg : 0 ≤ ∫ x, g x ∂ν :=
      integral_nonneg fun x => hg_nonneg x
    have hsqrt_g_le : Real.sqrt (∫ x, g x ∂ν) ≤ Real.sqrt ((2 / 3) * K) :=
      Real.sqrt_le_sqrt hg_integral_le
    have hprod_le :
        Real.sqrt (∫ x, g x ∂ν) * Real.sqrt 3
          ≤ Real.sqrt ((2 / 3) * K) * Real.sqrt 3 := by
      exact mul_le_mul_of_nonneg_right hsqrt_g_le (Real.sqrt_nonneg 3)
    calc
      ∫ x, |p x - 1| ∂ν
          ≤ Real.sqrt (∫ x, g x ∂ν) * Real.sqrt 3 := hholder
      _ ≤ Real.sqrt ((2 / 3) * K) * Real.sqrt 3 := hprod_le
      _ = Real.sqrt (2 * K) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ (2 / 3) * K) (3 : ℝ)]
        congr 1
        ring
  have hscheffe := tvDist_le_half_integral_abs_rnDeriv μ ν hac
  unfold PinskerBound
  have hscheffe_p : tvDist μ ν ≤ (1 / 2) * ∫ x, |p x - 1| ∂ν := by
    simpa [hp_def] using hscheffe
  calc
    tvDist μ ν ≤ (1 / 2) * ∫ x, |p x - 1| ∂ν := hscheffe_p
    _ ≤ (1 / 2) * Real.sqrt (2 * K) := by
      exact mul_le_mul_of_nonneg_left h_int_abs (by norm_num)
    _ = Real.sqrt (K / 2) := pinsker_half_sqrt_two_mul K hK_nonneg
    _ = Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2) := by rw [hK_def]

/-- **Pinsker's inequality for i.i.d. finite products (unconditional).**  From the
one-sample hypotheses `μ ≪ ν` and `Integrable (llr μ ν) μ`, the `n`-fold product
pair `(μ^{⊗n}, ν^{⊗n})` satisfies `PinskerBound`.  The product absolute
continuity and `klDiv ≠ ⊤` are discharged from the marginals via
`Causalean.Mathlib.InformationTheory.pi_iid_*`. -/
theorem pinskerBound_pi_iid {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ) (n : ℕ) :
    PinskerBound (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν)) := by
  have hac_pi :=
    Causalean.Mathlib.InformationTheory.pi_iid_absolutelyContinuous μ ν hac n
  have hint_pi :=
    Causalean.Mathlib.InformationTheory.pi_iid_llr_integrable μ ν hac hint n
  exact pinskerBound_of_ac_of_ne_top _ _ hac_pi
    (InformationTheory.klDiv_ne_top hac_pi hint_pi)

variable {P₀ P₁ : Measure Ω} [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
  {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]

/-- **KL-form Le Cam two-point lower bound.**  Given Pinsker control of `tvDist P₀ P₁`
by `klDiv P₀ P₁` and `2s`-separation of the parameter values, every estimator has
worst-case error probability at least `(1 - √((klDiv P₀ P₁).toReal / 2)) / 2`.

This is the directly usable minimax lower bound: bounding the (computable) KL
divergence above yields a lower bound on the error of *every* estimator.

The `_of_pinsker` suffix marks that this form consumes a supplied
`PinskerBound P₀ P₁` term.  For the unconditional version (deriving the bridge
from `P₀ ≪ P₁` + finite KL) use `klForm_two_point_lower_bound`. -/
theorem klForm_two_point_lower_bound_of_pinsker (h : PinskerBound P₀ P₁)
    {est : Ω → Θ} (hest : Measurable est) {θ₀ θ₁ : Θ} {s : ℝ}
    (hsep : 2 * s ≤ dist θ₀ θ₁) :
    (1 - Real.sqrt ((InformationTheory.klDiv P₀ P₁).toReal / 2)) / 2
      ≤ max (P₀.real {ω | s ≤ dist (est ω) θ₀}) (P₁.real {ω | s ≤ dist (est ω) θ₁}) := by
  have hmax := half_one_sub_tvDist_le_max_error (P₀ := P₀) (P₁ := P₁) hest hsep
  have htv : (1 - Real.sqrt ((InformationTheory.klDiv P₀ P₁).toReal / 2)) / 2
      ≤ (1 - tvDist P₀ P₁) / 2 := by
    have := h
    unfold PinskerBound at this
    linarith
  exact htv.trans hmax

/-- **KL-form Le Cam two-point lower bound (unconditional).**  Same conclusion as
`klForm_two_point_lower_bound_of_pinsker`, but with the Pinsker bridge discharged
from `P₀ ≪ P₁` and finite KL (`klDiv P₀ P₁ ≠ ⊤`) via `pinskerBound_of_ac_of_ne_top`
— no `PinskerBound` hypothesis. -/
theorem klForm_two_point_lower_bound (hac : P₀ ≪ P₁)
    (hfin : InformationTheory.klDiv P₀ P₁ ≠ ⊤)
    {est : Ω → Θ} (hest : Measurable est) {θ₀ θ₁ : Θ} {s : ℝ}
    (hsep : 2 * s ≤ dist θ₀ θ₁) :
    (1 - Real.sqrt ((InformationTheory.klDiv P₀ P₁).toReal / 2)) / 2
      ≤ max (P₀.real {ω | s ≤ dist (est ω) θ₀}) (P₁.real {ω | s ≤ dist (est ω) θ₁}) :=
  klForm_two_point_lower_bound_of_pinsker
    (pinskerBound_of_ac_of_ne_top P₀ P₁ hac hfin) hest hsep

end Causalean.Stat
