/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rademacher modulus for the DR-Learner

Apply the generic bounded-loss Rademacher bridge
`OrthogonalLearning/LocalEmpProcess/Rademacher.lean` to the DR-Learner `LearningSystem`
from `OrthogonalLearning/DRLearner.lean`.  Hypotheses:

* bounded target class — there is `M_Θ` with `|eval θ x| ≤ M_Θ` for all
  `θ ∈ Θ_set` and all `x : γ`;
* strict overlap on the propensity component of the realised nuisance
  `h n ω`, giving a uniform bound on the AIPW pseudo-outcome
  `φ_h z = φ z h n ω`;
* bounded outcomes `|Y| ≤ M_Y` (the CATE setup already imposes
  measurability; bounded outcomes is added here);
* a Rademacher-complexity bound `R n` for the centred DR loss class on
  the estimation fold.

Conclusion: `LocalEmpProcessModulus` holds for `(τ̂_n, ĥ_n)` with
`ρ n := √(2 R n + 2b · √(2 log(1/δ) / |B(n)|))` on nonempty estimation
folds, and boundary branch `ρ n := √(2b)`, for an explicit constant `b`
depending on `M_Θ`, `M_Y`, and the overlap floor.

Combined with `OrthogonalLearning/OracleInequality.lean`, this gives:
`‖τ̂_n − τ₀‖² = O(R_n² + nuisance_remainder²)` with high probability.
-/

import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Rademacher
import Causalean.Estimation.CATE.OrthogonalLearning.DRLearner

/-! # DR-Learner Empirical Modulus

This file proves that bounded outcomes, bounded target evaluations, strict
propensity overlap, bounded nuisance regressions, and a Rademacher-complexity
bound imply the local empirical-process modulus for the doubly robust learner
for conditional treatment effects. It connects the generic orthogonal
statistical-learning modulus to the causal conditional-effect system through
the assumption predicates `DREvalBounded`, `DROutcomeBounded`,
`DRNuisanceOverlap`, and `DRNuisanceMuBounded`, the bounded-loss bridge
`dr_loss_uniformly_bounded`, and the modulus theorem
`localEmpProcessModulus_drLearner`. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.CATE
  Causalean.Stat Causalean.Stat.Concentration

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]

/-- Boundedness of the target candidate evaluation map: `|eval θ x| ≤ M_Θ`
uniformly over `θ ∈ Θ_set` and `x : γ`. -/
def DREvalBounded
    {Θ : Type*} (Θ_set : Set Θ) (eval : Θ → γ → ℝ) (M_Θ : ℝ) : Prop :=
  0 ≤ M_Θ ∧ ∀ θ ∈ Θ_set, ∀ x : γ, |eval θ x| ≤ M_Θ

/-- Bounded outcome assumption: the outcome coordinate is bounded by `M_Y`
under the observed-data law `P_Z`, almost everywhere.

This is the standard `P_Z`-a.e. bounded-outcome assumption used by the
DR-Learner bounded-loss bridge. -/
def DROutcomeBounded
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ) (M_Y : ℝ) : Prop :=
  0 ≤ M_Y ∧ ∀ᵐ z ∂(S.toBackdoorEstimationSystem.P_Z), |z.2.2| ≤ M_Y

/-- Strict overlap floor on the realised nuisance `h`: the propensity
component `h.e_fn` is bounded inside `[ε, 1 − ε]` uniformly in `x`. -/
def DRNuisanceOverlap
    {Θ : Type*}
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (_S : CATEEstimationSystem P γ)
    (_Θ_set : Set Θ) (h : NuisanceVec γ) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧ ∀ x : γ, ε ≤ h.e_fn x ∧ h.e_fn x ≤ 1 - ε

/-- Uniform L∞-bound on the outcome-regression component of the realised
nuisance `h`: `|h.μ_fn b x| ≤ M_μ` for both treatment arms. -/
def DRNuisanceMuBounded (h : NuisanceVec γ) (M_μ : ℝ) : Prop :=
  0 ≤ M_μ ∧ ∀ b : Bool, ∀ x : γ, |h.μ_fn b x| ≤ M_μ

/-- **Bridge: DR-Learner squared loss is bounded under (M_Θ, M_Y, M_μ, ε).**

The DR-Learner loss is `(φ_h(z) − eval θ z.1)²` where the AIPW
pseudo-outcome `phi_eta` is

    φ_h(z) = h.μ_fn(true, x) − h.μ_fn(false, x)
              + (a / h.e_fn x) · (y − h.μ_fn(true, x))
              − ((1−a) / (1 − h.e_fn x)) · (y − h.μ_fn(false, x)).

Under

* `|eval θ x| ≤ M_Θ` uniformly over `θ ∈ Θ_set, x : γ`,
* `|y| ≤ M_Y` for the realised outcome,
* `|h.μ_fn b x| ≤ M_μ` for both arms (`DRNuisanceMuBounded`),
* `ε ≤ h.e_fn x ≤ 1 − ε` (`DRNuisanceOverlap`),

the AIPW pseudo-outcome is uniformly bounded by

    M_φ := 2 · M_μ + 2 · (M_Y + M_μ) / ε,

so the loss is bounded by `b := (M_Θ + M_φ)^2`.  The
`indA z = if z.2.1 then 1 else 0` indicator is in `[0, 1]`, and the two
fractional weights `(indA z) / h.e_fn x` and
`(1 − indA z) / (1 − h.e_fn x)` are each `≤ 1/ε` by the overlap bound. -/
theorem dr_loss_uniformly_bounded
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    {M_Θ M_Y M_μ ε : ℝ}
    (hM_Θ : DREvalBounded Θ_set eval M_Θ)
    (hM_Y : DROutcomeBounded S M_Y)
    (h : NuisanceVec γ)
    (hM_μ : DRNuisanceMuBounded h M_μ)
    (hOverlap : DRNuisanceOverlap S Θ_set h ε) :
    UniformlyBoundedLossAE
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      h ((M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2) := by
  let Mφ : ℝ := 2 * M_μ + 2 * (M_Y + M_μ) / ε
  have hMφ_eq : M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε = M_Θ + Mφ := by
    change M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε = M_Θ + (2 * M_μ + 2 * (M_Y + M_μ) / ε)
    ring
  rw [hMφ_eq]
  rcases hM_Θ with ⟨hMΘ_nonneg, hEval⟩
  rcases hM_Y with ⟨hMY_nonneg, hY_ae⟩
  rcases hM_μ with ⟨hMμ_nonneg, hMu⟩
  rcases hOverlap with ⟨hε_pos, _hε_half, hOverlap'⟩
  filter_upwards [hY_ae] with z hz
  intro θ hθ
  let x : γ := z.1
  let I : ℝ := BackdoorEstimationSystem.indA z
  have hI_nonneg : 0 ≤ I := by
    by_cases hz : z.2.1 = true
    · simp [I, BackdoorEstimationSystem.indA, BackdoorEstimationSystem.projA, hz]
    · simp [I, BackdoorEstimationSystem.indA, BackdoorEstimationSystem.projA, hz]
  have hI_le_one : I ≤ 1 := by
    by_cases hz : z.2.1 = true
    · simp [I, BackdoorEstimationSystem.indA, BackdoorEstimationSystem.projA, hz]
    · simp [I, BackdoorEstimationSystem.indA, BackdoorEstimationSystem.projA, hz]
  have hOneSubI_nonneg : 0 ≤ 1 - I := by linarith
  have hOneSubI_le_one : 1 - I ≤ 1 := by linarith
  have he_lower : ε ≤ h.e_fn x := (hOverlap' x).1
  have he_upper : h.e_fn x ≤ 1 - ε := (hOverlap' x).2
  have he_pos : 0 < h.e_fn x := lt_of_lt_of_le hε_pos he_lower
  have hden_lower : ε ≤ 1 - h.e_fn x := by linarith
  have hden_pos : 0 < 1 - h.e_fn x := lt_of_lt_of_le hε_pos hden_lower
  have hsum_nonneg : 0 ≤ M_Y + M_μ := by linarith
  have hdiff_mu : |h.μ_fn true x - h.μ_fn false x| ≤ 2 * M_μ := by
    have htri := abs_sub (h.μ_fn true x) (h.μ_fn false x)
    have ht := hMu true x
    have hf := hMu false x
    nlinarith
  have hres_true : |z.2.2 - h.μ_fn true x| ≤ M_Y + M_μ := by
    have htri := abs_sub z.2.2 (h.μ_fn true x)
    have hy := hz
    have hm := hMu true x
    nlinarith
  have hres_false : |z.2.2 - h.μ_fn false x| ≤ M_Y + M_μ := by
    have htri := abs_sub z.2.2 (h.μ_fn false x)
    have hy := hz
    have hm := hMu false x
    nlinarith
  have hratio_true : |I / h.e_fn x| ≤ 1 / ε := by
    have hinv_le : (h.e_fn x)⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ he_pos hε_pos).2 he_lower
    have hmul₁ : I * (h.e_fn x)⁻¹ ≤ 1 * (h.e_fn x)⁻¹ :=
      mul_le_mul_of_nonneg_right hI_le_one (inv_nonneg.mpr he_pos.le)
    have hmul₂ : 1 * (h.e_fn x)⁻¹ ≤ 1 * ε⁻¹ :=
      mul_le_mul_of_nonneg_left hinv_le zero_le_one
    have hmul : I * (h.e_fn x)⁻¹ ≤ 1 * ε⁻¹ := le_trans hmul₁ hmul₂
    simpa [div_eq_mul_inv, one_div, abs_of_nonneg hI_nonneg, abs_of_pos he_pos] using hmul
  have hratio_false : |(1 - I) / (1 - h.e_fn x)| ≤ 1 / ε := by
    have hinv_le : (1 - h.e_fn x)⁻¹ ≤ ε⁻¹ :=
      (inv_le_inv₀ hden_pos hε_pos).2 hden_lower
    have hmul₁ : (1 - I) * (1 - h.e_fn x)⁻¹ ≤ 1 * (1 - h.e_fn x)⁻¹ :=
      mul_le_mul_of_nonneg_right hOneSubI_le_one (inv_nonneg.mpr hden_pos.le)
    have hmul₂ : 1 * (1 - h.e_fn x)⁻¹ ≤ 1 * ε⁻¹ :=
      mul_le_mul_of_nonneg_left hinv_le zero_le_one
    have hmul : (1 - I) * (1 - h.e_fn x)⁻¹ ≤ 1 * ε⁻¹ := le_trans hmul₁ hmul₂
    simpa [div_eq_mul_inv, one_div, abs_of_nonneg hOneSubI_nonneg, abs_of_pos hden_pos] using hmul
  have hterm_true :
      |(I / h.e_fn x) * (z.2.2 - h.μ_fn true x)| ≤ (M_Y + M_μ) / ε := by
    rw [abs_mul]
    have hmul := mul_le_mul hratio_true hres_true (abs_nonneg _) (one_div_nonneg.mpr hε_pos.le)
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hterm_false :
      |((1 - I) / (1 - h.e_fn x)) * (z.2.2 - h.μ_fn false x)|
        ≤ (M_Y + M_μ) / ε := by
    rw [abs_mul]
    have hmul := mul_le_mul hratio_false hres_false (abs_nonneg _) (one_div_nonneg.mpr hε_pos.le)
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hphi : |phi_eta z h| ≤ Mφ := by
    have htri₁ := abs_sub
      ((h.μ_fn true x - h.μ_fn false x)
        + (I / h.e_fn x) * (z.2.2 - h.μ_fn true x))
      (((1 - I) / (1 - h.e_fn x)) * (z.2.2 - h.μ_fn false x))
    have htri₂ := abs_add_le (h.μ_fn true x - h.μ_fn false x)
      ((I / h.e_fn x) * (z.2.2 - h.μ_fn true x))
    have hraw :
        |(h.μ_fn true x - h.μ_fn false x)
          + (I / h.e_fn x) * (z.2.2 - h.μ_fn true x)
          - ((1 - I) / (1 - h.e_fn x)) * (z.2.2 - h.μ_fn false x)|
          ≤ 2 * M_μ + (M_Y + M_μ) / ε + (M_Y + M_μ) / ε := by
      nlinarith
    have hraw' :
        |(h.μ_fn true x - h.μ_fn false x)
          + (I / h.e_fn x) * (z.2.2 - h.μ_fn true x)
          - ((1 - I) / (1 - h.e_fn x)) * (z.2.2 - h.μ_fn false x)
          - 0| ≤ Mφ := by
      have hraw₀ :
          |(h.μ_fn true x - h.μ_fn false x)
            + (I / h.e_fn x) * (z.2.2 - h.μ_fn true x)
            - ((1 - I) / (1 - h.e_fn x)) * (z.2.2 - h.μ_fn false x)
            - 0|
            ≤ 2 * M_μ + (M_Y + M_μ) / ε + (M_Y + M_μ) / ε := by
        simpa using hraw
      calc
        |(h.μ_fn true x - h.μ_fn false x)
          + (I / h.e_fn x) * (z.2.2 - h.μ_fn true x)
          - ((1 - I) / (1 - h.e_fn x)) * (z.2.2 - h.μ_fn false x)
          - 0|
            ≤ 2 * M_μ + (M_Y + M_μ) / ε + (M_Y + M_μ) / ε := hraw₀
        _ = Mφ := by
          dsimp [Mφ]
          ring
    simpa [phi_eta, BackdoorEstimationSystem.aipwMoment, BackdoorEstimationSystem.projX,
      BackdoorEstimationSystem.projY, x, I] using hraw'
  have hdiff_loss : |phi_eta z h - eval θ z.1| ≤ Mφ + M_Θ := by
    have htri := abs_sub (phi_eta z h) (eval θ z.1)
    have heval := hEval θ hθ z.1
    nlinarith
  have hsq : (phi_eta z h - eval θ z.1) ^ 2 ≤ (M_Θ + Mφ) ^ 2 := by
    have hbound : |phi_eta z h - eval θ z.1| ≤ M_Θ + Mφ := by linarith
    have hneg : -(M_Θ + Mφ) ≤ |phi_eta z h - eval θ z.1| := by
      have hnonneg := abs_nonneg (phi_eta z h - eval θ z.1)
      nlinarith
    simpa [sq_abs] using sq_le_sq' hneg hbound
  have hloss_nonneg : 0 ≤ (phi_eta z h - eval θ z.1) ^ 2 := sq_nonneg _
  simpa [UniformlyBoundedLossAE, drLearningSystem, abs_of_nonneg hloss_nonneg]
    using hsq

/-- **DR-Learner bounded-loss Rademacher modulus.**  The DR-Learner orthogonal-learning system,
under bounded eval / outcomes / nuisance L∞ / overlap and a Rademacher
bound on the centred loss class on fold B, satisfies the
`LocalEmpProcessModulus` predicate with the explicit rate
`ρ n = √(2 R n + 2b · √(2 log(1/δ) / |B(n)|))` from the generic
Rademacher bridge.
The empty-fold boundary branch uses `ρ n = √(2b)`. -/
theorem localEmpProcessModulus_drLearner
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [IsProbabilityMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (S_iid : IIDSample P.Ω (γ × Bool × ℝ) P.μ
      S.toBackdoorEstimationSystem.P_Z)
    (split : OneShotSplit S_iid)
    {M_Θ M_Y M_μ ε : ℝ}
    (hM_Θ : DREvalBounded Θ_set eval M_Θ)
    (hM_Y : DROutcomeBounded S M_Y)
    (h : NuisanceVec γ)
    (hM_μ : DRNuisanceMuBounded h M_μ)
    (hOverlap : DRNuisanceOverlap S Θ_set h ε)
    (hLoss_cont : LossContinuousOnΘset
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes) h)
    (idx : ℕ →
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
    (idx_dense : DenseRange idx)
    (R : ℕ → ℝ)
    (hR : RademacherBound
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      S_iid split h idx R)
    (hclamp_minimizes : DRClampedThetaMinimizes S Θ_set θ₀ eval
      ((M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∃ b : ℝ, 0 ≤ b ∧
      LocalEmpProcessModulus
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
        S_iid split
        (fun n => Real.sqrt
          (if (split.foldB n).card = 0 then 2 * b
           else 2 * R n + 2 * b *
            Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ h := by
  have hb_loss := dr_loss_uniformly_bounded
      S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀
      θ₀_minimizes hM_Θ hM_Y h hM_μ hOverlap
  set b : ℝ := (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2 with hb_def
  have hb_nonneg : 0 ≤ b := sq_nonneg _
  refine ⟨b, hb_nonneg, ?_⟩
  exact localEmpProcessModulus_of_bounded_rademacher_ae
    (S := drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
    (S_iid := S_iid) (split := split) (hb := hb_nonneg) (g := h)
    (hg_bdd_ae := hb_loss) (hg_cont := hLoss_cont) (idx := idx)
    (idx_dense := idx_dense) (R := R) hR (by
      simpa [DRClampedThetaMinimizes, hb_def, drLearningSystem] using hclamp_minimizes) hδ hδ'

end OrthogonalLearning
end Estimation
end Causalean
