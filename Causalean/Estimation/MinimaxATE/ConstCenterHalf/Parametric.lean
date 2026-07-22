/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE estimation: the parametric `Ω(1/n)` lower bound

The Jin–Syrgkanis 2024 minimax rate for structure-agnostic ATE estimation is
`Ω(εg εm + 1/n)`.  The sibling files (`ExplicitWitness.lean`/`ChiSquaredCore.lean`,
`LowerBoundGen.lean`) deliver the **structure-agnostic** product term `εg εm` via the
Rademacher-bump / Ingster-χ² construction.  This file delivers the additive,
**parametric** `1/n` term — the irreducible statistical noise that survives even when
the nuisances are known up to a one-dimensional constant shift.

The construction is a single two-point (Le Cam) testing problem on a general finite
covariate `C`, with **constant** nuisances:

* a center `(m₀, g₀, g₁)` with all coordinates in `(0,1)`;
* the null DGP `(mC, gNull)` with `mC ≡ m₀`, `gNull d ≡ if d then g₁ else g₀`;
* the perturbed DGP `(mC, gPert)` with the treated arm shifted by `δ ≥ 0`,
  `gPert d ≡ if d then g₁ + δ else g₀` (control arm and propensity unchanged).

The ATE gap is exactly `δ` (`ate gPert − ate gNull = δ`), both DGPs lie in the class
`ℱ(εg, εm)` around `(mC, gNull)` once `δ² ≤ εg`, and the single-observation
χ²-divergence is the closed form

  `χ²(obsLaw pert ‖ obsLaw null) = m₀ δ² / (g₁ (1 − g₁))`.

Tensorizing over `n` i.i.d. draws (`one_add_chiSqDiv_pi_iid`) and using
`(1 + x)^n ≤ exp(n x) ≤ 2` in the regime `n · m₀ δ²/(g₁(1−g₁)) ≤ log 2` gives
`χ²(product pert ‖ product null) ≤ 1`, hence `tvDist ≤ ½√χ² ≤ ½`.  Le Cam's two-point
bound (`twoPointWitness_quarter`) then forces every measurable estimator to miss the
true ATE by `s = δ/2` with probability `≥ 1/4` somewhere in the class.

Solving the regime constraint for the largest admissible gap gives
`δ² ≍ g₁(1−g₁) log 2 /(m₀ n)`, i.e. `s = δ/2 ≍ 1/√n`, the parametric rate.

Main result:

* `parametric_lower_bound` — the headline `1/4 ≤ minimaxMiss … (δ/2)`.
-/

import Causalean.Estimation.MinimaxATE.Reduction.Witness
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSqOverlap
import Causalean.Estimation.MinimaxATE.Reduction.Bump
import Causalean.Stat.Minimax.ChiSquaredFinite

/-! # Parametric Lower Bound

This file proves the parametric component of the structure-agnostic ATE minimax lower bound.  It
uses a two-point constant-nuisance experiment to show that ordinary sampling noise imposes a
one-over-sample-size squared-risk floor even apart from the product-bias obstruction.

The construction fixes a constant propensity `mC`, a null outcome regression `gNull`, and a
treated-arm shift `gPert`.  The supporting lemmas prove validity (`validDGP_null`,
`validDGP_pert`), the exact ATEs (`ate_gNull`, `ate_gPert`), class membership
(`inClass_null`, `inClass_pert`), and the single-observation and product chi-squared bounds
(`one_add_chiSqDiv_obsPert_obsNull`, `chiSqDiv_productLaw_le_one`).  The public capstone
`parametric_lower_bound` applies the two-point reduction to show that every measurable estimator
misses by `δ / 2` with probability at least `1 / 4` somewhere in the class under the stated
budget and indistinguishability conditions. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

namespace Parametric

variable {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- The constant propensity center `m ≡ m₀`. -/
def mC (m₀ : ℝ) : C → ℝ := fun _ => m₀

/-- The null outcome regression: `g₁` on the treated arm, `g₀` on the control arm. -/
def gNull (g₀ g₁ : ℝ) : Bool → C → ℝ := fun d _ => if d then g₁ else g₀

/-- The perturbed outcome regression: the treated arm is shifted to `g₁ + δ`. -/
def gPert (g₀ g₁ δ : ℝ) : Bool → C → ℝ := fun d _ => if d then g₁ + δ else g₀

variable {m₀ g₀ g₁ δ : ℝ}

/-- Validity of the null DGP. -/
theorem validDGP_null (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1)
    (hg1 : 0 < g₁) (hg1' : g₁ < 1) :
    ValidDGP (C := C) (mC m₀) (gNull g₀ g₁) where
  m_mem _ := ⟨hm0.le, hm1.le⟩
  g_mem d _ := by cases d <;> simp [gNull] <;> constructor <;> linarith

/-- Validity of the perturbed DGP (using `0 ≤ δ` and `g₁ + δ ≤ 1`). -/
theorem validDGP_pert (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1)
    (hg1 : 0 < g₁) (hδ : 0 ≤ δ) (hδU : g₁ + δ ≤ 1) :
    ValidDGP (C := C) (mC m₀) (gPert g₀ g₁ δ) where
  m_mem _ := ⟨hm0.le, hm1.le⟩
  g_mem d _ := by cases d <;> simp [gPert] <;> constructor <;> linarith

/-- The ATE of the null DGP is `g₁ − g₀`. -/
theorem ate_gNull : ate (C := C) (gNull g₀ g₁) = g₁ - g₀ := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [ate, gNull, if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The ATE of the perturbed DGP is `(g₁ + δ) − g₀`. -/
theorem ate_gPert : ate (C := C) (gPert g₀ g₁ δ) = (g₁ + δ) - g₀ := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [ate, gPert, if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The squared `L²` distance between the perturbed and null treated arms is `δ²`;
control arms agree.  Hence each arm's error from `gNull` is `≤ εg` once `δ² ≤ εg`. -/
theorem l2sq_gPert_gNull (d : Bool) :
    l2sq (C := C) (gPert g₀ g₁ δ d) (gNull g₀ g₁ d) = if d then δ ^ 2 else 0 := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  cases d
  · simp [l2sq, gPert, gNull]
  · simp only [l2sq, gPert, gNull, if_true]
    have : ∀ _x : C, (g₁ + δ - g₁) ^ 2 = δ ^ 2 := by intro _; ring
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp

/-- The null DGP lies in the class around `(mC, gNull)` (zero nuisance error). -/
theorem inClass_null {εg εm : ℝ} (hv : ValidDGP (C := C) (mC m₀) (gNull g₀ g₁))
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm) :
    InClass (mC m₀) (gNull g₀ g₁) εg εm (mC m₀) (gNull (C := C) g₀ g₁) where
  valid := hv
  err_g d := by rw [l2sq_self]; exact hεg
  err_m := by rw [l2sq_self]; exact hεm

/-- The perturbed DGP lies in the class around `(mC, gNull)` when `δ² ≤ εg`. -/
theorem inClass_pert {εg εm : ℝ} (hv : ValidDGP (C := C) (mC m₀) (gPert g₀ g₁ δ))
    (hbudget : δ ^ 2 ≤ εg) (hεm : 0 ≤ εm) :
    InClass (mC m₀) (gNull g₀ g₁) εg εm (mC m₀) (gPert (C := C) g₀ g₁ δ) where
  valid := hv
  err_g d := by
    rw [l2sq_gPert_gNull]
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact le_trans (sq_nonneg δ) hbudget
    · simpa using hbudget
  err_m := by rw [l2sq_self]; exact hεm

/-- **Absolute continuity from full support.** If `ν` charges every singleton, every
measure is absolutely continuous w.r.t. `ν`. -/
theorem absolutelyContinuous_of_singleton_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (hν : ∀ x, ν {x} ≠ 0) : μ ≪ ν := by
  intro s hs
  have hempty : s = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact hν x (le_antisymm (hs ▸ measure_mono (Set.singleton_subset_iff.mpr hx)) (zero_le _))
  rw [hempty]; exact measure_empty

/-- The null single-observation law charges every point (its mass is positive). -/
theorem obsLaw_null_singleton_ne_zero (hv : ValidDGP (C := C) (mC m₀) (gNull g₀ g₁))
    (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1)
    (hg1 : 0 < g₁) (hg1' : g₁ < 1) (z : Obs C) : obsLaw hv {z} ≠ 0 := by
  have hpos : 0 < (obsLaw hv).real {z} := by
    rw [obsLaw_real_singleton hv z]
    have hC : (0 : ℝ) < (Fintype.card C : ℝ) := by
      have := Fintype.card_pos (α := C); exact_mod_cast this
    simp only [obsReal, mC, gNull]
    rcases z.2.1 with _ | _ <;> rcases z.2.2 with _ | _ <;>
      · simp only [Bool.false_eq_true, if_false, if_true]
        have h1 : (0:ℝ) < 1 - m₀ := by linarith
        have h2 : (0:ℝ) < 1 - g₀ := by linarith
        have h3 : (0:ℝ) < 1 - g₁ := by linarith
        positivity
  intro h
  rw [Measure.real, h, ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

/-- **Single-observation χ² (closed form).**  With `μ = obsLaw pert`, `ν = obsLaw null`,
the (shifted) χ²-divergence is `1 + m₀ δ²/(g₁(1−g₁))`. -/
theorem one_add_chiSqDiv_obsPert_obsNull
    (hvN : ValidDGP (C := C) (mC m₀) (gNull g₀ g₁))
    (hvP : ValidDGP (C := C) (mC m₀) (gPert g₀ g₁ δ))
    (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1)
    (hg1 : 0 < g₁) (hg1' : g₁ < 1) :
    1 + chiSqDiv (obsLaw hvP) (obsLaw hvN) = 1 + m₀ * δ ^ 2 / (g₁ * (1 - g₁)) := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hCpos : (0 : ℝ) < (Fintype.card C : ℝ) := by
    have := Fintype.card_pos (α := C); exact_mod_cast this
  have hg1ne : g₁ ≠ 0 := hg1.ne'
  have h1g1ne : (1 - g₁) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have hg0ne : g₀ ≠ 0 := hg0.ne'
  have h1g0ne : (1 - g₀) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have hm0ne : m₀ ≠ 0 := hm0.ne'
  have h1m0ne : (1 - m₀) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have hac : obsLaw hvP ≪ obsLaw hvN :=
    absolutelyContinuous_of_singleton_pos _ _
      (obsLaw_null_singleton_ne_zero hvN hm0 hm1 hg0 hg0' hg1 hg1')
  rw [finite_one_add_chiSqDiv (obsLaw hvP) (obsLaw hvN) hac]
  -- rewrite each singleton mass to its real form
  have hrw : ∀ z : Obs C,
      ((obsLaw hvP).real {z}) ^ 2 / ((obsLaw hvN).real {z})
        = (obsReal (mC m₀) (gPert g₀ g₁ δ) z) ^ 2 / (obsReal (mC m₀) (gNull g₀ g₁) z) := by
    intro z; rw [obsLaw_real_singleton hvP z, obsLaw_real_singleton hvN z]
  rw [Finset.sum_congr rfl (fun z _ => hrw z)]
  -- split the sum over `C × (Bool × Bool)`
  rw [Fintype.sum_prod_type]
  have hcell : ∀ x : C,
      ∑ p : Bool × Bool,
          (obsReal (mC m₀) (gPert g₀ g₁ δ) (x, p)) ^ 2 / (obsReal (mC m₀) (gNull g₀ g₁) (x, p))
        = (Fintype.card C : ℝ)⁻¹ * (1 - m₀)
          + (Fintype.card C : ℝ)⁻¹ * m₀ * (1 + δ ^ 2 / (g₁ * (1 - g₁))) := by
    intro x
    rw [Fintype.sum_prod_type]
    simp only [obsReal, mC, gNull, gPert, Fintype.sum_bool, Bool.false_eq_true, if_false,
      if_true]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun x _ => hcell x), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp
  ring

/-- The single-observation χ² is nonnegative and equals `m₀ δ²/(g₁(1−g₁))`. -/
theorem chiSqDiv_obsPert_obsNull_eq
    (hvN : ValidDGP (C := C) (mC m₀) (gNull g₀ g₁))
    (hvP : ValidDGP (C := C) (mC m₀) (gPert g₀ g₁ δ))
    (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1)
    (hg1 : 0 < g₁) (hg1' : g₁ < 1) :
    chiSqDiv (obsLaw hvP) (obsLaw hvN) = m₀ * δ ^ 2 / (g₁ * (1 - g₁)) := by
  have h := one_add_chiSqDiv_obsPert_obsNull hvN hvP hm0 hm1 hg0 hg0' hg1 hg1'
  linarith

/-- **χ² indistinguishability of the `n`-sample laws.**  In the regime
`n · m₀ δ²/(g₁(1−g₁)) ≤ log 2`, the χ²-divergence of the `n`-sample perturbed law
from the null is at most `1`.  Proved by tensorization (`one_add_chiSqDiv_pi_iid`) and
`(1 + x)^n ≤ exp(n x) ≤ 2`. -/
theorem chiSqDiv_productLaw_le_one {n : ℕ}
    (hvN : ValidDGP (C := C) (mC m₀) (gNull g₀ g₁))
    (hvP : ValidDGP (C := C) (mC m₀) (gPert g₀ g₁ δ))
    (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1)
    (hg1 : 0 < g₁) (hg1' : g₁ < 1)
    (hreg : (n : ℝ) * (m₀ * δ ^ 2 / (g₁ * (1 - g₁))) ≤ Real.log 2) :
    chiSqDiv (productLaw hvP n) (productLaw hvN n) ≤ 1 := by
  haveI : IsProbabilityMeasure (obsLaw hvP) := obsLaw_isProb hvP
  haveI : IsProbabilityMeasure (obsLaw hvN) := obsLaw_isProb hvN
  have hac : obsLaw hvP ≪ obsLaw hvN :=
    absolutelyContinuous_of_singleton_pos _ _
      (obsLaw_null_singleton_ne_zero hvN hm0 hm1 hg0 hg0' hg1 hg1')
  -- the single-observation χ² value `χ²₁ = m₀ δ²/(g₁(1−g₁))`
  set χ₁ := m₀ * δ ^ 2 / (g₁ * (1 - g₁)) with hχ₁
  have hχ₁0 : 0 ≤ χ₁ := by
    rw [hχ₁]; apply div_nonneg (by positivity)
    have : (0:ℝ) < 1 - g₁ := by linarith
    positivity
  have hsingle : 1 + chiSqDiv (obsLaw hvP) (obsLaw hvN) = 1 + χ₁ := by
    rw [hχ₁]; exact one_add_chiSqDiv_obsPert_obsNull hvN hvP hm0 hm1 hg0 hg0' hg1 hg1'
  -- tensorize
  have htensor : 1 + chiSqDiv (productLaw hvP n) (productLaw hvN n) = (1 + χ₁) ^ n := by
    rw [productLaw, productLaw, one_add_chiSqDiv_pi_iid (obsLaw hvP) (obsLaw hvN) hac n,
      hsingle]
  -- `(1 + χ₁)^n ≤ exp(n χ₁) ≤ 2`
  have hpow : (1 + χ₁) ^ n ≤ Real.exp ((n : ℝ) * χ₁) := by
    calc (1 + χ₁) ^ n ≤ (Real.exp χ₁) ^ n := by
            exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp χ₁]) n
      _ = Real.exp ((n : ℝ) * χ₁) := by rw [← Real.exp_nat_mul]
  have hexp2 : Real.exp ((n : ℝ) * χ₁) ≤ 2 := by
    have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    calc Real.exp ((n : ℝ) * χ₁) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.2 (by rw [hχ₁] at hreg ⊢; exact hreg)
      _ = 2 := h2
  linarith [htensor, hpow, hexp2]

/-- **Total-variation indistinguishability of the `n`-sample laws.** -/
theorem tvDist_productLaw_le_half {n : ℕ}
    (hvN : ValidDGP (C := C) (mC m₀) (gNull g₀ g₁))
    (hvP : ValidDGP (C := C) (mC m₀) (gPert g₀ g₁ δ))
    (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1)
    (hg1 : 0 < g₁) (hg1' : g₁ < 1)
    (hreg : (n : ℝ) * (m₀ * δ ^ 2 / (g₁ * (1 - g₁))) ≤ Real.log 2) :
    tvDist (productLaw hvN n) (productLaw hvP n) ≤ 1 / 2 := by
  haveI : IsProbabilityMeasure (productLaw hvP n) := productLaw_isProb hvP n
  haveI : IsProbabilityMeasure (productLaw hvN n) := productLaw_isProb hvN n
  have hac : obsLaw hvP ≪ obsLaw hvN :=
    absolutelyContinuous_of_singleton_pos _ _
      (obsLaw_null_singleton_ne_zero hvN hm0 hm1 hg0 hg0' hg1 hg1')
  have hacP : productLaw hvP n ≪ productLaw hvN n := by
    rw [productLaw, productLaw]; exact pi_iid_absolutelyContinuous _ _ hac n
  have hchi := chiSqDiv_productLaw_le_one hvN hvP hm0 hm1 hg0 hg0' hg1 hg1' hreg
  rw [tvDist_symm]
  calc tvDist (productLaw hvP n) (productLaw hvN n)
      ≤ (1 / 2) * Real.sqrt (chiSqDiv (productLaw hvP n) (productLaw hvN n)) :=
        tvDist_le_half_sqrt_chiSqDiv _ _ hacP Integrable.of_finite
    _ ≤ (1 / 2) * Real.sqrt 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); exact Real.sqrt_le_sqrt hchi
    _ = 1 / 2 := by rw [Real.sqrt_one]; ring

end Parametric

open Parametric in
/-- **Parametric `Ω(1/n)` minimax lower bound for structure-agnostic ATE estimation.**
Around any constant nuisance center `(m₀, g₀, g₁) ∈ (0,1)³`, with a treated-arm shift
`δ ≥ 0` (`g₁ + δ ≤ 1`) inside the outcome-error budget (`δ² ≤ εg`) and in the
sample-size regime `n · m₀ δ²/(g₁(1−g₁)) ≤ log 2`, **every** measurable estimator misses
the true ATE by `s = δ/2` with probability at least `1/4` somewhere in the class.

Taking `δ ≍ √(g₁(1−g₁) log 2 /(m₀ n))` (the largest admissible shift) gives `s = δ/2 ≍
1/√n`, the irreducible parametric noise that adds to the structure-agnostic product
term `εg εm` in the Jin–Syrgkanis 2024 rate `Ω(εg εm + 1/n)`. -/
theorem parametric_lower_bound {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C]
    [MeasurableSingletonClass C]
    {n : ℕ} {m₀ g₀ g₁ δ εg εm : ℝ}
    (hm0 : 0 < m₀) (hm1 : m₀ < 1) (hg0 : 0 < g₀) (hg0' : g₀ < 1) (hg1 : 0 < g₁) (hg1' : g₁ < 1)
    (hδ : 0 ≤ δ) (hδU : g₁ + δ ≤ 1)
    (hbudget : δ ^ 2 ≤ εg) (hεm : 0 ≤ εm)
    (hreg : (n : ℝ) * (m₀ * δ ^ 2 / (g₁ * (1 - g₁))) ≤ Real.log 2)
    {est : (Fin n → Obs C) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMiss (fun _ => m₀) (fun d _ => if d then g₁ else g₀) εg εm n est (δ / 2) := by
  have hvN : ValidDGP (C := C) (mC m₀) (gNull g₀ g₁) :=
    validDGP_null hm0 hm1 hg0 hg0' hg1 hg1'
  have hvP : ValidDGP (C := C) (mC m₀) (gPert g₀ g₁ δ) :=
    validDGP_pert hm0 hm1 hg0 hg0' hg1 hδ hδU
  have hεg : 0 ≤ εg := le_trans (sq_nonneg δ) hbudget
  -- the two-point witness: null vs perturbed
  let W : TwoPointWitness C n (mC m₀) (gNull g₀ g₁) εg εm :=
    { s := δ / 2
      c := 1 / 2
      Q := fun j => cond j (productLaw hvP n) (productLaw hvN n)
      prob := by
        intro j; cases j
        · exact productLaw_isProb hvN n
        · exact productLaw_isProb hvP n
      θ := fun j => cond j ((g₁ + δ) - g₀) (g₁ - g₀)
      sep := by
        change 2 * (δ / 2) ≤ |((g₁ + δ) - g₀) - (g₁ - g₀)|
        have : ((g₁ + δ) - g₀) - (g₁ - g₀) = δ := by ring
        rw [this, abs_of_nonneg hδ]; linarith
      tvBound := by
        simpa using
          tvDist_productLaw_le_half hvN hvP hm0 hm1 hg0 hg0' hg1 hg1' hreg
      dominated := by
        intro est' j
        cases j
        · -- null branch
          change (productLaw hvN n).real {x | (δ / 2) ≤ |est' x - (g₁ - g₀)|}
              ≤ minimaxMiss (mC m₀) (gNull g₀ g₁) εg εm n est' (δ / 2)
          have hb :=
            nMiss_le_minimaxMiss (mhat := mC m₀) (ghat := gNull g₀ g₁) (εg := εg) (εm := εm)
              (⟨(mC m₀, gNull g₀ g₁), inClass_null hvN hεg hεm⟩) (est := est') (s := δ / 2)
          simp only [nMiss, ate_gNull] at hb
          exact hb
        · -- perturbed branch
          change (productLaw hvP n).real {x | (δ / 2) ≤ |est' x - ((g₁ + δ) - g₀)|}
              ≤ minimaxMiss (mC m₀) (gNull g₀ g₁) εg εm n est' (δ / 2)
          have hb :=
            nMiss_le_minimaxMiss (mhat := mC m₀) (ghat := gNull g₀ g₁) (εg := εg) (εm := εm)
              (⟨(mC m₀, gPert g₀ g₁ δ), inClass_pert hvP hbudget hεm⟩) (est := est') (s := δ / 2)
          simp only [nMiss, ate_gPert] at hb
          exact hb }
  exact twoPointWitness_quarter W (le_refl _) hest

end Causalean.Estimation.MinimaxATE
