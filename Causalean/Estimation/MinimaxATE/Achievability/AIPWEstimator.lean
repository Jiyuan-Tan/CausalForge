/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE: finite AIPW score, bias, and variance ingredients

The converse half of the structure-agnostic optimality story lives in
`LowerBound*.lean` (`minimax_lower_bound{,_gen,_var}`): around a fixed nuisance
center `(mhat, ghat)`, no estimator beats the doubly-robust product rate `√(εg·εm)`.

This file supplies the finite AIPW ingredients used by the achievability result:
the fixed-center score and sample-average estimator, the finite doubly-robust bias
identity and product-error bound, the center-overlap and score-bound lemmas, and the
variance bound for the sample average.  Because the structure-agnostic class is
centered at *fixed* nuisances `(mhat, ghat)` — not data-estimated ones — the estimator is
the **fixed-center AIPW sample average**

  `θ̂(sample) = (1/n) Σ_i ψ_AIPW(Z_i; mhat, ghat)`,
  `ψ_AIPW(z; m̂, ĝ) = (ĝ₁ x − ĝ₀ x) + D·(Y − ĝ₁ x)/m̂ x − (1−D)·(Y − ĝ₀ x)/(1 − m̂ x)`.

Its plug-in bias is the doubly-robust remainder `≤ (1/ε)·2√εg·√εm` (finite Cauchy–Schwarz),
and its variance is `≤ B²/n` (the score is bounded because the *center* `m̂` is bounded
off `{0,1}`).  `Optimality.lean` turns these ingredients into the Chebyshev
`aipw_nMiss_le` bound, the uniform `aipw_minimaxMiss_le` bound, and the capstone
constant-factor optimality statement.

This is the finite specialization of the general AIPW DML asymptotic-normality theorem
`Estimation/ATE/DML.lean` (`dml_ATE_tendstoNormal`); the finite form is what pairs cleanly with
the finite converse.
-/

import Causalean.Estimation.MinimaxATE.Model
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Fixed-Center AIPW Achievability

This file defines the fixed-center augmented inverse probability weighted estimator
for the finite structure-agnostic average treatment effect problem.  The estimator
`estAIPW` is the sample average of `aipwScoreFin mhat ghat`, with the nuisance
center `(mhat, ghat)` held fixed rather than estimated from the sample.

The main facts are `aipw_pop_mean`, the finite population mean formula;
`aipw_bias_identity` and `aipw_bias_bound`, the doubly robust product-remainder
calculation; `exists_center_overlap`, which extracts a finite positive overlap
constant for the fixed center; and `aipwScore_bound`/`aipw_var_bound`, the score
and sample-average variance bounds used by `Optimality.lean` to prove the
miss-probability achievability theorem. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- The outcome `Y : Bool` read as a real number `{0,1}`. -/
def yReal (y : Bool) : ℝ := if y then 1 else 0

/-- The fixed-center augmented inverse-propensity score combines the fitted
treated-versus-control outcome-regression contrast with the residual from the
observed treatment arm, weighted by the fitted propensity at the covariate value.

Treated observations add the treated residual divided by the fitted propensity,
while control observations subtract the control residual divided by one minus
the fitted propensity. -/
noncomputable def aipwScoreFin (mhat : C → ℝ) (ghat : Bool → C → ℝ) (z : Obs C) : ℝ :=
  (ghat true z.1 - ghat false z.1)
    + cond z.2.1
        ((yReal z.2.2 - ghat true z.1) / mhat z.1)
        (-(yReal z.2.2 - ghat false z.1) / (1 - mhat z.1))

/-- The **fixed-center AIPW estimator**: the sample average of the AIPW score. -/
noncomputable def estAIPW (mhat : C → ℝ) (ghat : Bool → C → ℝ) (n : ℕ)
    (sample : Fin n → Obs C) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, aipwScoreFin mhat ghat (sample i)

/-- **Population mean of the AIPW score** under the DGP `(m, g)` is the finite sum
`Σ_z obsReal m g z · ψ_AIPW(z; m̂, ĝ)`. -/
theorem aipw_pop_mean [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ} (hv : ValidDGP m g)
    (mhat : C → ℝ) (ghat : Bool → C → ℝ) :
    ∫ z, aipwScoreFin mhat ghat z ∂(obsLaw hv)
      = ∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z := by
  unfold obsLaw
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [smul_eq_mul]
  congr 1
  unfold obsPMF
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (obsReal_nonneg hv z)]

/-- **Doubly-robust bias identity.**  The population AIPW mean minus the true ATE equals the
finite doubly-robust remainder: a sum of products of nuisance errors. -/
theorem aipw_bias_identity [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (mhat : C → ℝ) (ghat : Bool → C → ℝ)
    (hmhat : ∀ x, 0 < mhat x) (hmhat1 : ∀ x, mhat x < 1) :
    (∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z) - ate g
      = (Fintype.card C : ℝ)⁻¹ * ∑ x : C,
          ((1 - m x / mhat x) * (ghat true x - g true x)
            - (1 - (1 - m x) / (1 - mhat x)) * (ghat false x - g false x)) := by
  have hm0 : ∀ x, mhat x ≠ 0 := fun x => (hmhat x).ne'
  have hm1 : ∀ x, (1 : ℝ) - mhat x ≠ 0 := fun x => sub_ne_zero.mpr (hmhat1 x).ne'
  -- collapse the sum over `(x, d, y)` to a per-cell expression
  have hsum : (∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z)
      = (Fintype.card C : ℝ)⁻¹ * ∑ x : C,
          ((ghat true x - ghat false x)
            + m x / mhat x * (g true x - ghat true x)
            - (1 - m x) / (1 - mhat x) * (g false x - ghat false x)) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, obsReal, aipwScoreFin, yReal,
      cond_true, cond_false, if_true, if_false, Bool.false_eq_true]
    have h0 := hm0 x; have h1 := hm1 x
    field_simp
    ring
  rw [hsum]
  unfold ate
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have h0 := hm0 x; have h1 := hm1 x
  field_simp
  ring

/-- **Uniform lower bound on the center weights.**  With `mhat` strictly inside `(0,1)` on the
finite type `C`, there is `ε > 0` with `ε ≤ mhat x` and `ε ≤ 1 − mhat x` for all `x`. -/
theorem exists_center_overlap [Nonempty C] (mhat : C → ℝ)
    (hmhat : ∀ x, 0 < mhat x) (hmhat1 : ∀ x, mhat x < 1) :
    ∃ ε > 0, ∀ x, ε ≤ mhat x ∧ ε ≤ 1 - mhat x := by
  classical
  refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun x => min (mhat x) (1 - mhat x)), ?_, ?_⟩
  · rw [gt_iff_lt, Finset.lt_inf'_iff]
    intro x _
    exact lt_min (hmhat x) (by linarith [hmhat1 x])
  · intro x
    have h := Finset.inf'_le (s := (Finset.univ : Finset C))
      (fun x => min (mhat x) (1 - mhat x)) (Finset.mem_univ x)
    exact ⟨le_trans h (min_le_left _ _), le_trans h (min_le_right _ _)⟩

/-- **Doubly-robust bias bound.**  The plug-in bias is bounded by the product of the
`L²(P_X)` nuisance errors, with constant `1/ε` set by the center overlap. -/
theorem aipw_bias_bound [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (mhat : C → ℝ) (ghat : Bool → C → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hco : ∀ x, ε ≤ mhat x ∧ ε ≤ 1 - mhat x) :
    |(∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z) - ate g|
      ≤ ε⁻¹ * ((Real.sqrt (l2sq (g true) (ghat true)) + Real.sqrt (l2sq (g false) (ghat false)))
          * Real.sqrt (l2sq m mhat)) := by
  have hmhat : ∀ x, 0 < mhat x := fun x => lt_of_lt_of_le hε (hco x).1
  have hmhat1 : ∀ x, mhat x < 1 := fun x => by linarith [(hco x).2]
  rw [aipw_bias_identity mhat ghat hmhat hmhat1]
  have hCinv : (0 : ℝ) ≤ (Fintype.card C : ℝ)⁻¹ := by positivity
  -- general discrete Cauchy–Schwarz over the `L²(P_X)` inner product
  have hCS : ∀ (a b : C → ℝ),
      (Fintype.card C : ℝ)⁻¹ * ∑ x, |a x| * |b x|
        ≤ Real.sqrt ((Fintype.card C : ℝ)⁻¹ * ∑ x, a x ^ 2)
            * Real.sqrt ((Fintype.card C : ℝ)⁻¹ * ∑ x, b x ^ 2) := by
    intro a b
    have hcs : (∑ x, |a x| * |b x|) ^ 2 ≤ (∑ x, |a x| ^ 2) * ∑ x, |b x| ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    have hsq : ∀ (f : C → ℝ), ∑ x, |f x| ^ 2 = ∑ x, f x ^ 2 := by
      intro f; refine Finset.sum_congr rfl fun x _ => ?_; rw [sq_abs]
    rw [hsq, hsq] at hcs
    have hsum_nonneg : (0 : ℝ) ≤ ∑ x, |a x| * |b x| :=
      Finset.sum_nonneg fun x _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have ha2 : (0 : ℝ) ≤ ∑ x, a x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
    have hb2 : (0 : ℝ) ≤ ∑ x, b x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
    -- `∑ |a||b| ≤ √(∑a²)·√(∑b²)`
    have hstep : (∑ x, |a x| * |b x|) ≤ Real.sqrt (∑ x, a x ^ 2) * Real.sqrt (∑ x, b x ^ 2) := by
      rw [← Real.sqrt_mul ha2]
      exact (Real.le_sqrt hsum_nonneg (mul_nonneg ha2 hb2)).mpr hcs
    -- multiply through by `(card C)⁻¹` and absorb into the two square roots
    rw [Real.sqrt_mul hCinv, Real.sqrt_mul hCinv, mul_mul_mul_comm,
      Real.mul_self_sqrt hCinv]
    exact mul_le_mul_of_nonneg_left hstep hCinv
  -- per-cell doubly-robust bound: `|bracket x| ≤ |Δm x|·(|Δg₁ x| + |Δg₀ x|)/ε`
  have hcell : ∀ x : C,
      |(1 - m x / mhat x) * (ghat true x - g true x)
        - (1 - (1 - m x) / (1 - mhat x)) * (ghat false x - g false x)|
        ≤ |m x - mhat x| * (|ghat true x - g true x| + |ghat false x - g false x|) * ε⁻¹ := by
    intro x
    obtain ⟨hco1, hco2⟩ := hco x
    have hp : 0 < mhat x := hmhat x
    have hq : (0:ℝ) < 1 - mhat x := by linarith [hmhat1 x]
    have e1 : 1 - m x / mhat x = (mhat x - m x) / mhat x := by field_simp
    have e2 : 1 - (1 - m x) / (1 - mhat x) = (m x - mhat x) / (1 - mhat x) := by
      field_simp; ring
    rw [e1, e2]
    have hpε : (mhat x)⁻¹ ≤ ε⁻¹ := by
      rw [inv_le_inv₀ hp hε]; exact hco1
    have hqε : (1 - mhat x)⁻¹ ≤ ε⁻¹ := by
      rw [inv_le_inv₀ hq hε]; exact hco2
    calc |(mhat x - m x) / mhat x * (ghat true x - g true x)
            - (m x - mhat x) / (1 - mhat x) * (ghat false x - g false x)|
        ≤ |(mhat x - m x) / mhat x * (ghat true x - g true x)|
            + |(m x - mhat x) / (1 - mhat x) * (ghat false x - g false x)| := abs_sub _ _
      _ = |m x - mhat x| * (mhat x)⁻¹ * |ghat true x - g true x|
            + |m x - mhat x| * (1 - mhat x)⁻¹ * |ghat false x - g false x| := by
          rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hp, abs_of_pos hq,
            abs_sub_comm (mhat x), div_eq_mul_inv, div_eq_mul_inv]
      _ ≤ |m x - mhat x| * ε⁻¹ * |ghat true x - g true x|
            + |m x - mhat x| * ε⁻¹ * |ghat false x - g false x| := by
          gcongr
      _ = |m x - mhat x| * (|ghat true x - g true x| + |ghat false x - g false x|) * ε⁻¹ := by ring
  -- each Cauchy–Schwarz half, with the outcome arm aligned to `l2sq`
  have hhalf : ∀ d : Bool,
      (Fintype.card C : ℝ)⁻¹ * ∑ x, |m x - mhat x| * |ghat d x - g d x|
        ≤ Real.sqrt (l2sq m mhat) * Real.sqrt (l2sq (g d) (ghat d)) := by
    intro d
    have h := hCS (fun x => m x - mhat x) (fun x => ghat d x - g d x)
    refine h.trans (le_of_eq ?_)
    have hl2m : (Fintype.card C : ℝ)⁻¹ * ∑ x, (m x - mhat x) ^ 2 = l2sq m mhat := rfl
    have hl2g : (Fintype.card C : ℝ)⁻¹ * ∑ x, (ghat d x - g d x) ^ 2 = l2sq (g d) (ghat d) := by
      unfold l2sq
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← neg_sub (g d x) (ghat d x), neg_sq]
    rw [hl2m, hl2g]
  -- assemble: triangle inequality + per-cell bound + split + Cauchy–Schwarz
  rw [abs_mul, abs_of_nonneg hCinv]
  calc (Fintype.card C : ℝ)⁻¹
        * |∑ x, ((1 - m x / mhat x) * (ghat true x - g true x)
            - (1 - (1 - m x) / (1 - mhat x)) * (ghat false x - g false x))|
      ≤ (Fintype.card C : ℝ)⁻¹
          * ∑ x, |m x - mhat x|
              * (|ghat true x - g true x| + |ghat false x - g false x|) * ε⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hCinv
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => hcell x)
    _ = ε⁻¹ * (((Fintype.card C : ℝ)⁻¹ * ∑ x, |m x - mhat x| * |ghat true x - g true x|)
          + ((Fintype.card C : ℝ)⁻¹ * ∑ x, |m x - mhat x| * |ghat false x - g false x|)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ ε⁻¹ * ((Real.sqrt (l2sq m mhat) * Real.sqrt (l2sq (g true) (ghat true)))
          + (Real.sqrt (l2sq m mhat) * Real.sqrt (l2sq (g false) (ghat false)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (hhalf true) (hhalf false)
    _ = ε⁻¹ * ((Real.sqrt (l2sq (g true) (ghat true)) + Real.sqrt (l2sq (g false) (ghat false)))
          * Real.sqrt (l2sq m mhat)) := by ring

/-- **Score bound.**  The AIPW score is bounded by `B = 1 + 2/ε` whenever the center
nuisances are valid and `mhat` is `ε`-bounded off `{0,1}`. -/
theorem aipwScore_bound [Nonempty C]
    (mhat : C → ℝ) (ghat : Bool → C → ℝ) (hghat : ValidDGP mhat ghat) {ε : ℝ} (hε : 0 < ε)
    (hco : ∀ x, ε ≤ mhat x ∧ ε ≤ 1 - mhat x) (z : Obs C) :
    |aipwScoreFin mhat ghat z| ≤ 1 + 2 / ε := by
  obtain ⟨x, d, y⟩ := z
  obtain ⟨hco1, hco2⟩ := hco x
  obtain ⟨hg1a, hg1b⟩ := hghat.g_mem true x
  obtain ⟨hg0a, hg0b⟩ := hghat.g_mem false x
  have hya : (0:ℝ) ≤ yReal y := by unfold yReal; cases y <;> simp
  have hyb : yReal y ≤ 1 := by unfold yReal; cases y <;> simp
  -- bounded-ratio helper: `|(u−v)/w| ≤ 1/ε` for `u,v ∈ [0,1]`, `w ≥ ε > 0`.
  have hratio : ∀ (u v w : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → ε ≤ w →
      |(u - v) / w| ≤ 1 / ε := by
    intro u v w hu hu1 hv hv1 hw
    have hw0 : 0 < w := lt_of_lt_of_le hε hw
    rw [abs_div, abs_of_pos hw0, div_le_div_iff₀ hw0 hε]
    have huv : |u - v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [mul_le_mul_of_nonneg_right huv hε.le, hw]
  have hA : |ghat true x - ghat false x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hB : |cond d ((yReal y - ghat true x) / mhat x)
      (-(yReal y - ghat false x) / (1 - mhat x))| ≤ 1 / ε := by
    cases d
    · change |(-(yReal y - ghat false x)) / (1 - mhat x)| ≤ 1 / ε
      rw [neg_div, abs_neg]
      exact hratio (yReal y) (ghat false x) (1 - mhat x) hya hyb hg0a hg0b hco2
    · change |(yReal y - ghat true x) / mhat x| ≤ 1 / ε
      exact hratio (yReal y) (ghat true x) (mhat x) hya hyb hg1a hg1b hco1
  unfold aipwScoreFin
  calc |(ghat true x - ghat false x) + cond d _ _|
      ≤ |ghat true x - ghat false x| + |cond d _ _| := abs_add_le _ _
    _ ≤ 1 + 1 / ε := add_le_add hA hB
    _ ≤ 1 + 2 / ε := by gcongr; norm_num

/-- **Variance bound.**  The estimator's variance is `≤ B²/n` (iid sample average of a score
bounded by `B`). -/
theorem aipw_var_bound [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ} (hv : ValidDGP m g)
    (mhat : C → ℝ) (ghat : Bool → C → ℝ) (hghat : ValidDGP mhat ghat) {ε : ℝ} (hε : 0 < ε)
    (hco : ∀ x, ε ≤ mhat x ∧ ε ≤ 1 - mhat x) (n : ℕ) :
    variance (estAIPW mhat ghat n) (productLaw hv n) ≤ (1 + 2 / ε) ^ 2 / n := by
  set B : ℝ := 1 + 2 / ε with hBdef
  have hB0 : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  -- the single-observation score and its bound
  set score : Obs C → ℝ := aipwScoreFin mhat ghat with hscore
  have hbound : ∀ z, |score z| ≤ B := fun z =>
    aipwScore_bound mhat ghat hghat hε hco z
  have hmeas : Measurable score := measurable_of_finite score
  have haes : AEStronglyMeasurable score (obsLaw hv) := hmeas.aestronglyMeasurable
  have hmem : MemLp score 2 (obsLaw hv) :=
    MemLp.of_bound haes B (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hbound z)
  -- `Var[score] ≤ B²`
  have hvar_score : variance score (obsLaw hv) ≤ B ^ 2 := by
    refine (variance_le_expectation_sq haes).trans ?_
    have hsq : ∀ z, (score ^ 2) z ≤ B ^ 2 := by
      intro z
      have := hbound z
      have h2 : score z ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg (score z), sq_abs (score z)]
      simpa using h2
    calc ∫ z, (score ^ 2) z ∂(obsLaw hv)
        ≤ ∫ _z, B ^ 2 ∂(obsLaw hv) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hsq)
      _ = B ^ 2 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hconst : estAIPW mhat ghat 0 = (0 : (Fin 0 → Obs C) → ℝ) := by
      funext s; simp [estAIPW]
    rw [hconst, variance_zero]
    simp
  · have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    -- express the estimator as a scalar multiple of the sample sum of the score
    have hsmul : estAIPW mhat ghat n
        = (n : ℝ)⁻¹ • (∑ i, fun ω : Fin n → Obs C => score (ω i)) := by
      funext sample
      simp only [estAIPW, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hscore]
    -- the variance of the sample sum splits over the iid coordinates
    have hsum_var : variance (∑ i, fun ω : Fin n → Obs C => score (ω i)) (productLaw hv n)
        = (n : ℝ) * variance score (obsLaw hv) := by
      rw [productLaw, variance_sum_pi (fun _ => hmem), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hsmul, variance_smul, hsum_var]
    -- `n⁻¹² · (n · Var) ≤ n⁻¹² · (n · B²) = B²/n`
    have hkey : (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * variance score (obsLaw hv))
        ≤ (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * B ^ 2) := by
      gcongr
    refine hkey.trans (le_of_eq ?_)
    field_simp

end Causalean.Estimation.MinimaxATE
