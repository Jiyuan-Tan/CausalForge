/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW score L²(P_Z) continuity

Used by `DML.lean` for the `R₂` empirical-process step: conditioning on the
fold-A σ-algebra, the centered fold-B sum of
`m_AIPW(η̂(n), Z_i, θ₀) − m_AIPW(η₀, Z_i, θ₀)` has conditional second moment
bounded by

    ‖m_AIPW(η̂(n), ·, θ₀) − m_AIPW(η₀, ·, θ₀)‖²_{L²(P_Z)},

so we need that this L²-norm is `o_p(1)` under `μ`.

Pointwise the AIPW score is Lipschitz in `η` on the overlap-bounded set `H_ε`:

    |m_AIPW(η, z, θ₀) − m_AIPW(η₀, z, θ₀)|
      ≤ K₁(ε) · (|Δμ(1, x)| + |Δμ(0, x)|)
        + K₂(ε) · (|y − μ_val(1, x)| + |y − μ_val(0, x)|) · |Δe(x)|

with `K₁(ε), K₂(ε)` depending only on `ε` (the overlap constant).  Squaring,
applying `(a+b)² ≤ 2a²+2b²`, and integrating against `P_Z` gives a
quantitative bound on `‖Δ_AIPW‖²_{L²(P_Z)}` in terms of:

* `‖Δμ(a, ·)‖²_{L²(P_X)}` for `a ∈ {0,1}` — controlled by individual rates;
* `‖(Y − μ_val(d, X)) · Δe(X)‖²_{L²(P_Z)}` — needs `(Y − μ_val(d, X))² ∈
  L¹(P_Z)` (from `h_yd2` + finite var of `μ_val(d, ·)` on `P_X`) plus
  `‖Δe‖_{L²(P_X)} = o_p(1)` and the truncation argument
  (split `{|Y − μ_val| ≤ K} ∪ {|Y − μ_val| > K}`; `|Δe| ≤ 1` on the first set
  controls everything by `K · ‖Δe‖_1`, the second is small for large `K` by
  integrability).

The headline corollary `aipw_score_diff_isLittleOp_one` packages the L²
continuity with the individual rates into the `o_p(1)` form consumed by the
`R₂` argument in `DML.lean`.
-/

import Causalean.Estimation.ATE.Score.AIPWMoment
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
Proves L² continuity of the AIPW score on the a.e. overlap-bounded nuisance
space, supplying the empirical-process input used by double machine learning
for the average treatment effect.

The file defines the overlap-dependent Lipschitz constant `K_AIPW`, proves the
a.e. pointwise score bound `aipw_score_diff_pointwise_bound`, shows
integrability of the residual-weighted cross term via
`yMuVal_residual_sq_integrable`, and packages the final
`o_p(1)` L²-score continuity theorem as `aipw_score_diff_isLittleOp_one`.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Pointwise Lipschitz bound on `m_AIPW(·, z, θ₀)` on `H_ε` -/

/-- Pointwise Lipschitz constant for the AIPW moment in `η` on `H_ε`:
`K_AIPW ε := 1 + 2/ε + 2/ε²`.  Tracks the quadratic blow-up of the inverse
weights `1/ê`, `1/(1−ê)` and the cross terms `(ê − e)/(ê·e)`. -/
noncomputable def K_AIPW (ε : ℝ) : ℝ := 1 + 2 / ε + 2 / ε ^ 2

private lemma K_AIPW_one_le {ε : ℝ} (hε : 0 < ε) :
    1 ≤ K_AIPW ε := by
  unfold K_AIPW
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

private lemma K_AIPW_mu_le {ε : ℝ} (hε : 0 < ε) :
    1 + 1 / ε ≤ K_AIPW ε := by
  unfold K_AIPW
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

private lemma K_AIPW_inv_sq_le {ε : ℝ} (hε : 0 < ε) :
    1 / ε ^ 2 ≤ K_AIPW ε := by
  unfold K_AIPW
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

private lemma abs_div_sub_div_le
    {ε e ê y μ μhat : ℝ} (hε : 0 < ε) (he : ε ≤ e) (hê : ε ≤ ê) :
    |(y - μhat) / ê - (y - μ) / e| ≤
      |μhat - μ| / ε + |y - μ| * |ê - e| / ε ^ 2 := by
  have he_pos : 0 < e := lt_of_lt_of_le hε he
  have hê_pos : 0 < ê := lt_of_lt_of_le hε hê
  have he_ne : e ≠ 0 := he_pos.ne'
  have hê_ne : ê ≠ 0 := hê_pos.ne'
  have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hprod_pos : 0 < ê * e := mul_pos hê_pos he_pos
  have hmul : ε ^ 2 ≤ ê * e := by
    nlinarith [mul_le_mul hê he hε.le hê_pos.le]
  have hid : (y - μhat) / ê - (y - μ) / e =
      - (μhat - μ) / ê - (y - μ) * (ê - e) / (ê * e) := by
    field_simp [hê_ne, he_ne]
    ring
  rw [hid]
  have htermA : |-(μhat - μ) / ê| = |μhat - μ| / ê := by
    rw [abs_div, abs_neg, abs_of_pos hê_pos]
  have htermB : |(y - μ) * (ê - e) / (ê * e)| =
      |y - μ| * |ê - e| / (ê * e) := by
    rw [abs_div, abs_mul, abs_of_pos hprod_pos]
  calc
    |- (μhat - μ) / ê - (y - μ) * (ê - e) / (ê * e)|
        ≤ |-(μhat - μ) / ê| + |(y - μ) * (ê - e) / (ê * e)| := abs_sub _ _
    _ = |μhat - μ| / ê + |y - μ| * |ê - e| / (ê * e) := by
      rw [htermA, htermB]
    _ ≤ |μhat - μ| / ε + |y - μ| * |ê - e| / ε ^ 2 := by
      have hterm1 : |μhat - μ| / ê ≤ |μhat - μ| / ε := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hê_pos hε).2 hê) (abs_nonneg _)
      have hterm2 : |y - μ| * |ê - e| / (ê * e) ≤
          |y - μ| * |ê - e| / ε ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hprod_pos hεsq_pos).2 hmul)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact add_le_add hterm1 hterm2

private lemma aipw_real_bound
    {ε e ê μT μF μhT μhF y θ : ℝ} {a : Bool}
    (hε : 0 < ε) (he : ε ≤ e ∧ e ≤ 1 - ε) (hê : ε ≤ ê ∧ ê ≤ 1 - ε) :
    |((μhT - μhF) + ((if a = true then 1 else 0) / ê) * (y - μhT)
        - ((1 - (if a = true then 1 else 0)) / (1 - ê)) * (y - μhF) - θ)
      - ((μT - μF) + ((if a = true then 1 else 0) / e) * (y - μT)
        - ((1 - (if a = true then 1 else 0)) / (1 - e)) * (y - μF) - θ)|
      ≤ K_AIPW ε *
          (|μhT - μT| + |μhF - μF| + (|y - μT| + |y - μF|) * |ê - e|) := by
  have hK1 : 1 ≤ K_AIPW ε := K_AIPW_one_le hε
  have hKμ : 1 + 1 / ε ≤ K_AIPW ε := K_AIPW_mu_le hε
  have hKe : 1 / ε ^ 2 ≤ K_AIPW ε := K_AIPW_inv_sq_le hε
  have hKnonneg : 0 ≤ K_AIPW ε := le_trans zero_le_one hK1
  set dT : ℝ := |μhT - μT|
  set dF : ℝ := |μhF - μF|
  set rT : ℝ := |y - μT|
  set rF : ℝ := |y - μF|
  set de : ℝ := |ê - e|
  have hdT : 0 ≤ dT := by simp [dT]
  have hdF : 0 ≤ dF := by simp [dF]
  have hrT : 0 ≤ rT := by simp [rT]
  have hrF : 0 ≤ rF := by simp [rF]
  have hde : 0 ≤ de := by simp [de]
  have hcrossT : rT * de ≤ (rT + rF) * de := by nlinarith
  have hcrossF : rF * de ≤ (rT + rF) * de := by nlinarith
  have hTcoef : (1 + 1 / ε) * dT ≤ K_AIPW ε * dT :=
    mul_le_mul_of_nonneg_right hKμ hdT
  have hFcoef : (1 + 1 / ε) * dF ≤ K_AIPW ε * dF :=
    mul_le_mul_of_nonneg_right hKμ hdF
  have hTone : dT ≤ K_AIPW ε * dT := by
    simpa using mul_le_mul_of_nonneg_right hK1 hdT
  have hFone : dF ≤ K_AIPW ε * dF := by
    simpa using mul_le_mul_of_nonneg_right hK1 hdF
  have hCrossT : rT * de / ε ^ 2 ≤ K_AIPW ε * ((rT + rF) * de) := by
    calc
      rT * de / ε ^ 2 = (1 / ε ^ 2) * (rT * de) := by ring
      _ ≤ K_AIPW ε * (rT * de) :=
        mul_le_mul_of_nonneg_right hKe (mul_nonneg hrT hde)
      _ ≤ K_AIPW ε * ((rT + rF) * de) :=
        mul_le_mul_of_nonneg_left hcrossT hKnonneg
  have hCrossF : rF * de / ε ^ 2 ≤ K_AIPW ε * ((rT + rF) * de) := by
    calc
      rF * de / ε ^ 2 = (1 / ε ^ 2) * (rF * de) := by ring
      _ ≤ K_AIPW ε * (rF * de) :=
        mul_le_mul_of_nonneg_right hKe (mul_nonneg hrF hde)
      _ ≤ K_AIPW ε * ((rT + rF) * de) :=
        mul_le_mul_of_nonneg_left hcrossF hKnonneg
  cases a
  · have hden_e : ε ≤ 1 - e := by linarith [he.2]
    have hden_ê : ε ≤ 1 - ê := by linarith [hê.2]
    have hrat := abs_div_sub_div_le (e := 1 - e) (ê := 1 - ê)
      (y := y) (μ := μF) (μhat := μhF) hε hden_e hden_ê
    have hrat' : |(y - μhF) / (1 - ê) - (y - μF) / (1 - e)| ≤
        dF / ε + rF * de / ε ^ 2 := by
      have hde' : |e - ê| = de := by
        simpa [de] using abs_sub_comm e ê
      simpa [dF, rF, de, hde'] using hrat
    have hpre :
        |((μhT - μhF) + (0 / ê) * (y - μhT)
            - ((1 - 0) / (1 - ê)) * (y - μhF) - θ)
          - ((μT - μF) + (0 / e) * (y - μT)
            - ((1 - 0) / (1 - e)) * (y - μF) - θ)|
          ≤ dT + dF + (dF / ε + rF * de / ε ^ 2) := by
      have hsplit :
          (((μhT - μhF) + (0 / ê) * (y - μhT)
              - ((1 - 0) / (1 - ê)) * (y - μhF) - θ)
            - ((μT - μF) + (0 / e) * (y - μT)
              - ((1 - 0) / (1 - e)) * (y - μF) - θ)) =
            (μhT - μT) - (μhF - μF)
              - ((y - μhF) / (1 - ê) - (y - μF) / (1 - e)) := by
        ring
      rw [hsplit]
      calc
        |(μhT - μT) - (μhF - μF)
            - ((y - μhF) / (1 - ê) - (y - μF) / (1 - e))|
            ≤ |(μhT - μT) - (μhF - μF)|
                + |(y - μhF) / (1 - ê) - (y - μF) / (1 - e)| := abs_sub _ _
        _ ≤ dT + dF + (dF / ε + rF * de / ε ^ 2) := by
          have hbase : |(μhT - μT) - (μhF - μF)| ≤ dT + dF := by
            simpa [dT, dF] using abs_sub (μhT - μT) (μhF - μF)
          nlinarith
    have htarget : dT + dF + (dF / ε + rF * de / ε ^ 2) ≤
        K_AIPW ε * (dT + dF + (rT + rF) * de) := by
      have hdFdiv : dF / ε = (1 / ε) * dF := by ring
      calc
        dT + dF + (dF / ε + rF * de / ε ^ 2)
            = dT + (1 + 1 / ε) * dF + rF * de / ε ^ 2 := by
              rw [hdFdiv]
              ring
        _ ≤ K_AIPW ε * dT + K_AIPW ε * dF +
              K_AIPW ε * ((rT + rF) * de) := by
              nlinarith
        _ = K_AIPW ε * (dT + dF + (rT + rF) * de) := by ring
    simpa [dT, dF, rT, rF, de] using le_trans hpre htarget
  · have hrat := abs_div_sub_div_le (e := e) (ê := ê)
      (y := y) (μ := μT) (μhat := μhT) hε he.1 hê.1
    have hrat' : |(y - μhT) / ê - (y - μT) / e| ≤
        dT / ε + rT * de / ε ^ 2 := by
      simpa [dT, rT, de] using hrat
    have hpre :
        |((μhT - μhF) + (1 / ê) * (y - μhT)
            - ((1 - 1) / (1 - ê)) * (y - μhF) - θ)
          - ((μT - μF) + (1 / e) * (y - μT)
            - ((1 - 1) / (1 - e)) * (y - μF) - θ)|
          ≤ dT + dF + (dT / ε + rT * de / ε ^ 2) := by
      have hsplit :
          (((μhT - μhF) + (1 / ê) * (y - μhT)
              - ((1 - 1) / (1 - ê)) * (y - μhF) - θ)
            - ((μT - μF) + (1 / e) * (y - μT)
              - ((1 - 1) / (1 - e)) * (y - μF) - θ)) =
            (μhT - μT) - (μhF - μF)
              + ((y - μhT) / ê - (y - μT) / e) := by
        ring
      rw [hsplit]
      calc
        |(μhT - μT) - (μhF - μF)
            + ((y - μhT) / ê - (y - μT) / e)|
            ≤ |(μhT - μT) - (μhF - μF)|
                + |(y - μhT) / ê - (y - μT) / e| := abs_add_le _ _
        _ ≤ dT + dF + (dT / ε + rT * de / ε ^ 2) := by
          have hbase : |(μhT - μT) - (μhF - μF)| ≤ dT + dF := by
            simpa [dT, dF] using abs_sub (μhT - μT) (μhF - μF)
          nlinarith
    have htarget : dT + dF + (dT / ε + rT * de / ε ^ 2) ≤
        K_AIPW ε * (dT + dF + (rT + rF) * de) := by
      have hdTdiv : dT / ε = (1 / ε) * dT := by ring
      calc
        dT + dF + (dT / ε + rT * de / ε ^ 2)
            = (1 + 1 / ε) * dT + dF + rT * de / ε ^ 2 := by
              rw [hdTdiv]
              ring
        _ ≤ K_AIPW ε * dT + K_AIPW ε * dF +
              K_AIPW ε * ((rT + rF) * de) := by
              nlinarith
        _ = K_AIPW ε * (dT + dF + (rT + rF) * de) := by ring
    simpa [dT, dF, rT, rF, de] using le_trans hpre htarget

/-- **AIPW score Lipschitz bound on `H_ε`, `P_Z`-a.e.**

For any `η ∈ H_ε`, the AIPW moment difference satisfies, for `P_Z`-a.e. `z`,

    |m_AIPW(η, z, θ₀) − m_AIPW(η₀, z, θ₀)|
      ≤ K_AIPW(ε) · (|Δμ(1, x)| + |Δμ(0, x)|
        + (|y − μ_val(1, x)| + |y − μ_val(0, x)|) · |Δe(x)|).

The "a.e." quantifier is needed because `S.StrictOverlap ε` only asserts
`ε ≤ propScore true ≤ 1 − ε` `P.μ`-a.s.; transferring it through
`S.e_compat` and pushforward gives `ε ≤ S.e_val ∘ projX ≤ 1 − ε` `P_Z`-a.s.,
which combined with the pointwise bound `ε ≤ η.e_fn ≤ 1 − ε` from
`H_ε ε` is enough for the algebraic Lipschitz step.

Proof: expand `m_AIPW`, apply triangle inequality, and use the standard
algebraic identity
    `a/u − a/v = a · (v − u) / (u · v)`
together with `1/u, 1/v ≤ 1/ε` and `1/(u · v) ≤ 1/ε²`. -/
theorem aipw_score_diff_pointwise_bound
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (η : NuisanceVec γ) (hη : η ∈ H_ε_aeL2 S ε) :
    ∀ᵐ z ∂S.P_Z,
      |aipwMomentFunctional η z S.θ₀ - aipwMomentFunctional S.η₀ z S.θ₀|
        ≤ K_AIPW ε *
            (|η.μ_fn true (projX z) - S.μ_val true (projX z)|
              + |η.μ_fn false (projX z) - S.μ_val false (projX z)|
              + (|projY z - S.μ_val true (projX z)|
                  + |projY z - S.μ_val false (projX z)|)
                * |η.e_fn (projX z) - S.e_val (projX z)|) := by
  rcases h_overlap with ⟨hε_pos, _hε_half, hprop⟩
  have h_e_ω : ∀ᵐ ω ∂P.μ,
      ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) ∧
        S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
    filter_upwards [hprop, S.e_compat] with ω hω hcompat
    rw [hcompat] at hω
    exact hω
  have h_e_z : ∀ᵐ z ∂S.P_Z,
      ε ≤ S.e_val (projX z) ∧ S.e_val (projX z) ≤ 1 - ε := by
    have hset : MeasurableSet
        {z : γ × Bool × ℝ | ε ≤ S.e_val (projX z) ∧
          S.e_val (projX z) ≤ 1 - ε} := by
      have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
        simpa [projX] using
          (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
      exact measurableSet_Icc.preimage (S.e_meas.comp hx)
    unfold BackdoorEstimationSystem.P_Z
    rw [MeasureTheory.ae_map_iff S.measurable_factualZ.aemeasurable hset]
    filter_upwards [h_e_ω] with ω hω
    simpa [BackdoorEstimationSystem.factualZ, projX] using hω
  have hη_z : ∀ᵐ z ∂S.P_Z,
      ε ≤ η.e_fn (projX z) ∧ η.e_fn (projX z) ≤ 1 - ε :=
    H_ε_aeL2_overlap_P_Z S hη
  filter_upwards [h_e_z, hη_z] with z hz hηz
  simpa [aipwMomentFunctional, aipwMoment, η₀, indA] using
    (aipw_real_bound (a := projA z) (ε := ε)
      (e := S.e_val (projX z)) (ê := η.e_fn (projX z))
      (μT := S.μ_val true (projX z)) (μF := S.μ_val false (projX z))
      (μhT := η.μ_fn true (projX z)) (μhF := η.μ_fn false (projX z))
      (y := projY z) (θ := S.θ₀) hε_pos hz hηz)

/-! ## L²(P_Z) continuity of the AIPW score on `H_ε`

Squaring the pointwise bound and integrating against `P_Z`, with
`(a+b+c)² ≤ 3(a²+b²+c²)`, yields:

    ‖m_AIPW(η, ·, θ₀) − m_AIPW(η₀, ·, θ₀)‖²_{L²(P_Z)}
      ≤ 3 · K_AIPW(ε)² · (
          ‖Δμ(1, ·)‖²_{L²(P_X)}
          + ‖Δμ(0, ·)‖²_{L²(P_X)}
          + ∫ (|y−μ_val(1,x)| + |y−μ_val(0,x)|)² · |Δe(x)|² dP_Z).

The first two summands are direct L²(P_X) norms.  The last summand is bounded
above using `|Δe| ≤ 1` (since `ε ≤ ê, e ≤ 1−ε` ⇒ `|Δe| ≤ 1−2ε ≤ 1`):

    ∫ (|y−μ_val(1,x)| + |y−μ_val(0,x)|)² · |Δe|² dP_Z
      ≤ ∫ (|y−μ_val(1,x)| + |y−μ_val(0,x)|)² · |Δe| dP_Z.

We package this as a non-asymptotic bound; the asymptotic `o_p(1)` form is
the headline corollary below. -/

/-- The "tilted" cross-term integrand `(|y − μ_val(1, x)| + |y − μ_val(0, x)|)²`,
viewed as a fixed L¹(P_Z) function (witness via `h_y2 + h_yd2 + Cauchy–Schwarz`). -/
noncomputable def YMuVal_residual_sq
    (S : BackdoorEstimationSystem P γ) : (γ × Bool × ℝ) → ℝ :=
  fun z => (|projY z - S.μ_val true (projX z)|
            + |projY z - S.μ_val false (projX z)|) ^ 2

private lemma yMuVal_residual_meas
    (S : BackdoorEstimationSystem P γ) :
    Measurable (fun z : γ × Bool × ℝ =>
      |projY z - S.μ_val true (projX z)|
        + |projY z - S.μ_val false (projX z)|) := by
  have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
    simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
  have hy : Measurable (fun z : γ × Bool × ℝ => projY z) := by
    simpa [projY] using
      (measurable_snd.snd : Measurable (fun z : γ × Bool × ℝ => z.2.2))
  have hμt : Measurable (fun z : γ × Bool × ℝ => S.μ_val true (projX z)) :=
    (S.μ_meas true).comp hx
  have hμf : Measurable (fun z : γ × Bool × ℝ => S.μ_val false (projX z)) :=
    (S.μ_meas false).comp hx
  exact (continuous_abs.measurable.comp (hy.sub hμt)).add
    (continuous_abs.measurable.comp (hy.sub hμf))

/-- The cross-term integrand is `P_Z`-integrable, with the bound coming from
`(a+b)² ≤ 2(a² + b²)` and `Y² ∈ L¹(P_Z)`, `μ_val(d, X)² ∈ L¹(P_Z)`. -/
theorem yMuVal_residual_sq_integrable
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    Integrable (S.YMuVal_residual_sq) S.P_Z := by
  have _ := hA
  have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ := by
    exact (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ_L2 :
      ∀ d : Bool, MemLp
        (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
    intro d
    have hYd_L2 : MemLp (S.toPOBackdoorSystem.YofD d) 2 P.μ := by
      exact (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD d).aestronglyMeasurable).2 (h_yd2 d)
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD d |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hYd_L2.condExp
    exact hcond_L2.ae_eq (S.μ_compat hA d)
  let g : γ × Bool × ℝ → ℝ :=
    fun z => |projY z - S.μ_val true (projX z)|
      + |projY z - S.μ_val false (projX z)|
  have hg_meas : Measurable g := by
    have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
      simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
    have hy : Measurable (fun z : γ × Bool × ℝ => projY z) := by
      simpa [projY] using
        (measurable_snd.snd : Measurable (fun z : γ × Bool × ℝ => z.2.2))
    have hμt : Measurable (fun z : γ × Bool × ℝ => S.μ_val true (projX z)) :=
      (S.μ_meas true).comp hx
    have hμf : Measurable (fun z : γ × Bool × ℝ => S.μ_val false (projX z)) :=
      (S.μ_meas false).comp hx
    exact (continuous_abs.measurable.comp (hy.sub hμt)).add
      (continuous_abs.measurable.comp (hy.sub hμf))
  have hg_comp_L2 : MemLp (fun ω => g (S.factualZ ω)) 2 P.μ := by
    have ht : MemLp
        (fun ω => S.toPOBackdoorSystem.factualY ω -
          S.μ_val true (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hY_L2.sub (hμ_L2 true)
    have hf : MemLp
        (fun ω => S.toPOBackdoorSystem.factualY ω -
          S.μ_val false (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hY_L2.sub (hμ_L2 false)
    simpa [g, BackdoorEstimationSystem.factualZ, projX, projY, Real.norm_eq_abs]
      using ht.norm.add hf.norm
  have hg_L2 : MemLp g 2 S.P_Z := by
    rw [BackdoorEstimationSystem.P_Z]
    exact (memLp_map_measure_iff hg_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 hg_comp_L2
  simpa [BackdoorEstimationSystem.YMuVal_residual_sq, g] using hg_L2.integrable_sq

private lemma yMuVal_residual_memLp
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    MemLp (fun z : γ × Bool × ℝ =>
      |projY z - S.μ_val true (projX z)|
        + |projY z - S.μ_val false (projX z)|) 2 S.P_Z := by
  exact (memLp_two_iff_integrable_sq (yMuVal_residual_meas S).aestronglyMeasurable).2
    (by
      simpa [BackdoorEstimationSystem.YMuVal_residual_sq] using
        yMuVal_residual_sq_integrable S hA h_y2 h_yd2)

private lemma eLpNorm_comp_projX_eq
    (S : BackdoorEstimationSystem P γ) {f : γ → ℝ}
    (hf : AEStronglyMeasurable f S.P_X) :
    eLpNorm (fun z : γ × Bool × ℝ => f (projX z)) 2 S.P_Z =
      eLpNorm f 2 S.P_X := by
  have hfmap :
      AEStronglyMeasurable f (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
    simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using hf
  rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S]
  simpa [projX, Function.comp_def] using
    (MeasureTheory.eLpNorm_map_measure
      (μ := S.P_Z) (f := fun z : γ × Bool × ℝ => z.1) (g := f)
      (p := 2) hfmap measurable_fst.aemeasurable).symm

set_option maxHeartbeats 800000 in
-- The projection-norm rewrite otherwise times out while unfolding the `P_Z.map projX = P_X` bridge.
private lemma e_error_eLpNorm_projX_toReal_eq
    (S : BackdoorEstimationSystem P γ) (η : NuisanceVec γ)
    (hηe : MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X) :
    (eLpNorm (fun z : γ × Bool × ℝ => η.e_fn (projX z) - S.e_val (projX z))
        2 S.P_Z).toReal =
      (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
  exact congrArg ENNReal.toReal
    (eLpNorm_comp_projX_eq (S := S)
      (f := fun x => η.e_fn x - S.e_val x) hηe.aestronglyMeasurable)

set_option maxHeartbeats 800000 in
-- The truncation proof combines several `MemLp` and `lpNorm` coercion steps;
-- the default budget is too small.
private theorem residual_mul_e_error_isLittleOp_one
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_e_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z : γ × Bool × ℝ =>
          (|projY z - S.μ_val true (projX z)|
            + |projY z - S.μ_val false (projX z)|) *
            |(η_hat n ω).e_fn (projX z) - S.e_val (projX z)|) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  rcases h_overlap with ⟨hε_pos, _hε_half, _hprop⟩
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold BackdoorEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  let R : (γ × Bool × ℝ) → ℝ := fun z =>
    |projY z - S.μ_val true (projX z)|
      + |projY z - S.μ_val false (projX z)|
  let deZ : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    (η_hat n ω).e_fn (projX z) - S.e_val (projX z)
  have hR_meas : Measurable R := by
    simpa [R] using yMuVal_residual_meas S
  have hR_nonneg : ∀ z, 0 ≤ R z := by
    intro z
    dsimp [R]
    positivity
  have hR_memLp : MemLp R 2 S.P_Z := by
    simpa [R] using yMuVal_residual_memLp S hA h_y2 h_yd2
  have hdeZ_memLp : ∀ n ω, MemLp (deZ n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using h_e_memLp n ω
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    simpa [deZ, projX] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_meas : ∀ n ω, Measurable (deZ n ω) := by
    intro n ω
    have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
      simpa [projX] using
        (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
    exact ((η_hat n ω).e_meas.comp hx).sub (S.e_meas.comp hx)
  have hdeZ_bdd : ∀ n ω, ∀ᵐ z ∂S.P_Z, |deZ n ω z| ≤ 1 := by
    intro n ω
    filter_upwards [H_ε_aeL2_overlap_P_Z S (h_in_H n ω)] with z hη
    have hη_nonneg : 0 ≤ (η_hat n ω).e_fn (projX z) :=
      le_trans hε_pos.le hη.1
    have hη_le_one : (η_hat n ω).e_fn (projX z) ≤ 1 := by
      linarith [hη.2, hε_pos.le]
    have hS_nonneg : 0 ≤ S.e_val (projX z) := le_of_lt (S.e_pos (projX z))
    have hS_le_one : S.e_val (projX z) ≤ 1 := le_of_lt (S.e_lt_one (projX z))
    dsimp [deZ]
    rw [abs_le]
    constructor <;> linarith
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  by_cases hκtop : κ = ⊤
  · filter_upwards with n
    simp [hκtop]
  have hκpos : 0 < κ.toReal := ENNReal.toReal_pos (ne_of_gt hκ) hκtop
  let τ : ℝ := δ / 4
  have hτpos : 0 < τ := by
    dsimp [τ]
    linarith
  obtain ⟨M, hMpos, hMtail⟩ :=
    hR_memLp.eLpNorm_indicator_norm_ge_pos_le hR_meas.stronglyMeasurable hτpos
  let tail : (γ × Bool × ℝ) → ℝ := {z | M ≤ R z}.indicator R
  have htail_set : MeasurableSet {z : γ × Bool × ℝ | M ≤ R z} := by
    exact measurableSet_le measurable_const hR_meas
  have htail_memLp : MemLp tail 2 S.P_Z := by
    exact hR_memLp.indicator htail_set
  have htail_norm_le : (eLpNorm tail 2 S.P_Z).toReal ≤ τ := by
    have hle : eLpNorm tail 2 S.P_Z ≤ ENNReal.ofReal τ := by
      have htail_eq :
          tail = ({z : γ × Bool × ℝ | M ≤ ‖R z‖₊}.indicator R) := by
        funext z
        by_cases hz : M ≤ R z
        · simp [tail, hz, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg z)]
        · simp [tail, hz, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg z)]
      simpa [htail_eq] using hMtail
    calc
      (eLpNorm tail 2 S.P_Z).toReal ≤ (ENNReal.ofReal τ).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = τ := ENNReal.toReal_ofReal hτpos.le
  have hcross_bound : ∀ n ω,
      (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal
        ≤ M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal + τ := by
    intro n ω
    let bulk : (γ × Bool × ℝ) → ℝ := fun z => M * |deZ n ω z|
    let upper : (γ × Bool × ℝ) → ℝ := fun z => bulk z + tail z
    have hbulk_memLp : MemLp bulk 2 S.P_Z := by
      have h_abs : MemLp (fun z => |deZ n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdeZ_memLp n ω).norm
      simpa [bulk, Pi.smul_apply, smul_eq_mul] using h_abs.const_smul M
    have hupper_memLp : MemLp upper 2 S.P_Z := by
      simpa [upper] using hbulk_memLp.add htail_memLp
    have hpoint : ∀ᵐ z ∂S.P_Z, ‖R z * |deZ n ω z|‖ ≤ upper z := by
      filter_upwards [hdeZ_bdd n ω] with z hdez_le
      have hRz : 0 ≤ R z := hR_nonneg z
      have hdez_nonneg : 0 ≤ |deZ n ω z| := abs_nonneg _
      by_cases hz : M ≤ R z
      · have htail_eq : tail z = R z := by simp [tail, hz]
        have hmain : ‖R z * |deZ n ω z|‖ ≤ R z := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRz, abs_of_nonneg hdez_nonneg]
          exact mul_le_of_le_one_right hRz hdez_le
        dsimp [upper, bulk]
        rw [htail_eq]
        have hbulk_nonneg : 0 ≤ M * |deZ n ω z| :=
          mul_nonneg hMpos.le hdez_nonneg
        exact hmain.trans (by nlinarith)
      · have htail_eq : tail z = 0 := by simp [tail, hz]
        have hR_lt_M : R z ≤ M := by
          exact le_of_not_ge hz
        have hmain : ‖R z * |deZ n ω z|‖ ≤ M * |deZ n ω z| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRz, abs_of_nonneg hdez_nonneg]
          exact mul_le_mul_of_nonneg_right hR_lt_M hdez_nonneg
        dsimp [upper, bulk]
        rw [htail_eq]
        simpa using hmain
    have hmono :
        (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal
          ≤ (eLpNorm upper 2 S.P_Z).toReal := by
      exact ENNReal.toReal_mono hupper_memLp.eLpNorm_ne_top
        (eLpNorm_mono_ae_real hpoint)
    have htri :
        lpNorm upper 2 S.P_Z ≤ lpNorm bulk 2 S.P_Z + lpNorm tail 2 S.P_Z := by
      simpa [upper] using lpNorm_add_le (f := bulk) (g := tail)
        (μ := S.P_Z) hbulk_memLp
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hbulk_norm :
        lpNorm bulk 2 S.P_Z =
          M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal := by
      change lpNorm (M • (fun z : γ × Bool × ℝ => |deZ n ω z|)) 2 S.P_Z =
        M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal
      rw [lpNorm_const_smul]
      rw [lpNorm_fun_abs (hdeZ_memLp n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdeZ_memLp n ω).aestronglyMeasurable]
      have hcoef : (↑‖M‖₊ : ℝ) = M := by
        simp [Real.norm_eq_abs, abs_of_pos hMpos]
      rw [hcoef]
    have htail_lp :
        lpNorm tail 2 S.P_Z = (eLpNorm tail 2 S.P_Z).toReal := by
      rw [toReal_eLpNorm htail_memLp.aestronglyMeasurable]
    calc
      (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal
          ≤ (eLpNorm upper 2 S.P_Z).toReal := hmono
      _ = lpNorm upper 2 S.P_Z := by
            rw [toReal_eLpNorm hupper_memLp.aestronglyMeasurable]
      _ ≤ lpNorm bulk 2 S.P_Z + lpNorm tail 2 S.P_Z := htri
      _ = M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal +
          (eLpNorm tail 2 S.P_Z).toReal := by rw [hbulk_norm, htail_lp]
      _ ≤ M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal + τ :=
        add_le_add_right htail_norm_le (M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal)
  have hsmall := (ENNReal.tendsto_nhds_zero.mp
    (h_e_rate (δ / (2 * M)) (by positivity))) κ hκ
  filter_upwards [hsmall] with n hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  have hnorm_nonneg :
      0 ≤ (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal :=
    ENNReal.toReal_nonneg
  have hlt_norm :
      δ < (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal := by
    simpa [R, deZ, abs_of_nonneg hnorm_nonneg] using hω
  have hde_large : δ / (2 * M) < (eLpNorm (deZ n ω) 2 S.P_Z).toReal := by
    have hb := hcross_bound n ω
    by_contra hnot
    have hle : (eLpNorm (deZ n ω) 2 S.P_Z).toReal ≤ δ / (2 * M) :=
      le_of_not_gt hnot
    have hprod_le :
        M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal ≤ δ / 2 := by
      calc
        M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal
            ≤ M * (δ / (2 * M)) := mul_le_mul_of_nonneg_left hle hMpos.le
        _ = δ / 2 := by field_simp [hMpos.ne']
    have hcross_le : (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|)
        2 S.P_Z).toReal ≤ δ / 2 + τ := by
      exact hb.trans (add_le_add hprod_le le_rfl)
    dsimp [τ] at hcross_le
    nlinarith
  have heq_norm :
      (eLpNorm (deZ n ω) 2 S.P_Z).toReal =
        (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal := by
    simpa [deZ] using e_error_eLpNorm_projX_toReal_eq S (η_hat n ω) (h_e_memLp n ω)
  have hde_large_X :
      δ / (2 * M) <
        (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal := by
    simpa [heq_norm] using hde_large
  have hde_nonneg :
      0 ≤ (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal :=
    ENNReal.toReal_nonneg
  simpa [abs_of_nonneg hde_nonneg] using hde_large_X

/-- **Headline L²(P_Z) `o_p(1)` continuity bound for the AIPW score.**

Given:
* strict overlap `ε` for `(μ_val, e_val)`;
* `Y² ∈ L¹(P.μ)`, `(Y(d))² ∈ L¹(P.μ)` for `d ∈ {0,1}`;
* a random nuisance `η̂(n, ω) ∈ H_ε(ε)` for all `n, ω`;
* individual rates `‖Δμ_a(n,ω,·)‖_{L²(P_X)} = o_p(1)` and
  `‖Δe(n,ω,·)‖_{L²(P_X)} = o_p(1)`.

Then `‖m_AIPW(η̂(n,ω), ·, θ₀) − m_AIPW(η₀, ·, θ₀)‖_{L²(P_Z)} = o_p(1)`
under `μ`.

**Proof outline.**  Apply `aipw_score_diff_pointwise_bound`; square and
integrate against `P_Z`; for the cross term use `|Δe| ≤ 1` and a truncation
argument on `(|y − μ_val(d,x)| + ...)²` (for any `δ > 0` choose `K` such that
the tail `∫ ... · 𝟙{... > K²} dP_Z < δ`, then dominate the bulk by `K² ·
‖Δe‖_{L¹(P_X)} ≤ K² · ‖Δe‖_{L²(P_X)}` which is `o_p(1)`). -/
private theorem aipw_score_diff_isLittleOp_one_truncation_core
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_mu_memLp :
      ∀ n ω a, MemLp
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z =>
            aipwMomentFunctional (η_hat n ω) z S.θ₀ -
              aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  rcases h_overlap with ⟨hε_pos, hε_half, hprop⟩
  let R : (γ × Bool × ℝ) → ℝ := fun z =>
    |projY z - S.μ_val true (projX z)|
      + |projY z - S.μ_val false (projX z)|
  let dμZ : Bool → ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun a n ω z =>
    (η_hat n ω).μ_fn a (projX z) - S.μ_val a (projX z)
  let deZ : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    (η_hat n ω).e_fn (projX z) - S.e_val (projX z)
  let cross : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    R z * |deZ n ω z|
  let score : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    aipwMomentFunctional (η_hat n ω) z S.θ₀ -
      aipwMomentFunctional S.η₀ z S.θ₀
  have hR_meas : Measurable R := by
    simpa [R] using yMuVal_residual_meas S
  have hR_nonneg : ∀ z, 0 ≤ R z := by
    intro z
    dsimp [R]
    positivity
  have hR_memLp : MemLp R 2 S.P_Z := by
    simpa [R] using yMuVal_residual_memLp S hA h_y2 h_yd2
  have hdμZ_memLp : ∀ a n ω, MemLp (dμZ a n ω) 2 S.P_Z := by
    intro a n ω
    have hmap : MemLp (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using h_mu_memLp n ω a
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    simpa [dμZ, projX] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_memLp : ∀ n ω, MemLp (deZ n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using h_e_memLp n ω
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    simpa [deZ, projX] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_bdd : ∀ n ω, ∀ᵐ z ∂S.P_Z, |deZ n ω z| ≤ 1 := by
    intro n ω
    filter_upwards [H_ε_aeL2_overlap_P_Z S (h_in_H n ω)] with z hη
    have hη_nonneg : 0 ≤ (η_hat n ω).e_fn (projX z) :=
      le_trans hε_pos.le hη.1
    have hη_le_one : (η_hat n ω).e_fn (projX z) ≤ 1 := by
      linarith [hη.2, hε_pos.le]
    have hS_nonneg : 0 ≤ S.e_val (projX z) := le_of_lt (S.e_pos (projX z))
    have hS_le_one : S.e_val (projX z) ≤ 1 := le_of_lt (S.e_lt_one (projX z))
    dsimp [deZ]
    rw [abs_le]
    constructor <;> linarith
  have hcross_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (cross n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [cross, R, deZ] using
      residual_mul_e_error_isLittleOp_one S ⟨hε_pos, hε_half, hprop⟩
        hA h_y2 h_yd2 η_hat h_in_H h_e_memLp h_e_rate
  have hμZ_rate : ∀ a : Bool,
      IsLittleOp
        (fun n ω => (eLpNorm (dμZ a n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    intro a
    have heq :
        (fun n ω => (eLpNorm (dμZ a n ω) 2 S.P_Z).toReal) =
          (fun n ω =>
            (eLpNorm (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal) := by
      funext n
      funext ω
      dsimp [dμZ]
      exact congrArg ENNReal.toReal
        (eLpNorm_comp_projX_eq (S := S)
          (f := fun x => (η_hat n ω).μ_fn a x - S.μ_val a x)
          (h_mu_memLp n ω a).aestronglyMeasurable)
    rw [heq]
    exact h_mu_rate a
  have hsum_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
            (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    exact IsLittleOp.add_one (IsLittleOp.add_one (hμZ_rate true) (hμZ_rate false))
      hcross_rate
  have hK_pos : 0 < K_AIPW ε := lt_of_lt_of_le zero_lt_one (K_AIPW_one_le hε_pos)
  refine IsLittleOp.of_abs_le_const_mul_one (C := K_AIPW ε) hK_pos hsum_rate ?_
  intro n ω
  have hpointwise :
      ∀ᵐ z ∂S.P_Z, |score n ω z| ≤
        K_AIPW ε * (|dμZ true n ω z| + |dμZ false n ω z| + cross n ω z) := by
    simpa [score, dμZ, cross, R, deZ] using
      aipw_score_diff_pointwise_bound S ⟨hε_pos, hε_half, hprop⟩
        (η_hat n ω) (h_in_H n ω)
  let upper : (γ × Bool × ℝ) → ℝ := fun z =>
    K_AIPW ε * (|dμZ true n ω z| + |dμZ false n ω z| + cross n ω z)
  have hcross_memLp : MemLp (cross n ω) 2 S.P_Z := by
    have hcross_meas : Measurable (cross n ω) := by
      have hde_meas : Measurable (deZ n ω) := by
        have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
          simpa [projX] using
            (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
        exact ((η_hat n ω).e_meas.comp hx).sub (S.e_meas.comp hx)
      simpa [cross] using hR_meas.mul (continuous_abs.measurable.comp hde_meas)
    refine hR_memLp.mono' hcross_meas.aestronglyMeasurable ?_
    filter_upwards [hdeZ_bdd n ω] with z hdez_le
    have hRz : 0 ≤ R z := hR_nonneg z
    dsimp [cross]
    rw [abs_mul, abs_of_nonneg hRz, abs_of_nonneg (abs_nonneg _)]
    exact mul_le_of_le_one_right hRz hdez_le
  have hupper_memLp : MemLp upper 2 S.P_Z := by
    have hsum : MemLp
        (fun z => |dμZ true n ω z| + |dμZ false n ω z| + cross n ω z)
        2 S.P_Z := by
      have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
      have hf : MemLp (fun z => |dμZ false n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp false n ω).norm
      exact (ht.add hf).add hcross_memLp
    simpa [upper, Pi.smul_apply, smul_eq_mul] using hsum.const_smul (K_AIPW ε)
  have hmono :
      (eLpNorm (score n ω) 2 S.P_Z).toReal ≤
        (eLpNorm upper 2 S.P_Z).toReal := by
    have hle_enn : eLpNorm (score n ω) 2 S.P_Z ≤ eLpNorm upper 2 S.P_Z :=
      eLpNorm_mono_ae_real (by
        filter_upwards [hpointwise] with z hz
        simpa [Real.norm_eq_abs, upper] using hz)
    exact ENNReal.toReal_mono hupper_memLp.eLpNorm_ne_top hle_enn
  have hupper_bound :
      (eLpNorm upper 2 S.P_Z).toReal ≤
        K_AIPW ε *
          ((eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
            (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross n ω) 2 S.P_Z).toReal) := by
    let total : (γ × Bool × ℝ) → ℝ := fun z =>
      |dμZ true n ω z| + |dμZ false n ω z| + cross n ω z
    have htotal_memLp : MemLp total 2 S.P_Z := by
      have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
      have hf : MemLp (fun z => |dμZ false n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp false n ω).norm
      simpa [total] using (ht.add hf).add hcross_memLp
    have hupper_eq : upper = K_AIPW ε • total := by
      funext z
      simp [upper, total, smul_eq_mul]
    rw [hupper_eq]
    rw [toReal_eLpNorm (htotal_memLp.const_smul (K_AIPW ε)).aestronglyMeasurable]
    rw [lpNorm_const_smul]
    have hcoef : (↑‖K_AIPW ε‖₊ : ℝ) = K_AIPW ε := by
      simp [Real.norm_eq_abs, abs_of_pos hK_pos]
    rw [hcoef]
    gcongr
    have htri1 :
        lpNorm total 2 S.P_Z ≤
          lpNorm (fun z => |dμZ true n ω z| + |dμZ false n ω z|) 2 S.P_Z +
            lpNorm (cross n ω) 2 S.P_Z := by
      have htotal_eq :
          total =
            (fun z => |dμZ true n ω z| + |dμZ false n ω z|) + cross n ω := by
        funext z
        simp [total, Pi.add_apply, add_assoc]
      rw [htotal_eq]
      exact
          lpNorm_add_le (f := fun z => |dμZ true n ω z| + |dμZ false n ω z|)
            (g := cross n ω) (μ := S.P_Z)
            ((by
              have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
                simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
              have hf : MemLp (fun z => |dμZ false n ω z|) 2 S.P_Z := by
                simpa [Real.norm_eq_abs] using (hdμZ_memLp false n ω).norm
              exact ht.add hf))
            (by norm_num : (1 : ENNReal) ≤ 2)
    have htri2 :
        lpNorm (fun z => |dμZ true n ω z| + |dμZ false n ω z|) 2 S.P_Z ≤
          lpNorm (fun z => |dμZ true n ω z|) 2 S.P_Z +
            lpNorm (fun z => |dμZ false n ω z|) 2 S.P_Z := by
      have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
      simpa using lpNorm_add_le (f := fun z => |dμZ true n ω z|)
        (g := fun z => |dμZ false n ω z|) (μ := S.P_Z) ht
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hnormT :
        lpNorm (fun z => |dμZ true n ω z|) 2 S.P_Z =
          (eLpNorm (dμZ true n ω) 2 S.P_Z).toReal := by
      rw [lpNorm_fun_abs (hdμZ_memLp true n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdμZ_memLp true n ω).aestronglyMeasurable]
    have hnormF :
        lpNorm (fun z => |dμZ false n ω z|) 2 S.P_Z =
          (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal := by
      rw [lpNorm_fun_abs (hdμZ_memLp false n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdμZ_memLp false n ω).aestronglyMeasurable]
    have hnormC :
        lpNorm (cross n ω) 2 S.P_Z =
          (eLpNorm (cross n ω) 2 S.P_Z).toReal := by
      rw [← toReal_eLpNorm hcross_memLp.aestronglyMeasurable]
    linarith
  calc
    |(eLpNorm (score n ω) 2 S.P_Z).toReal|
        = (eLpNorm (score n ω) 2 S.P_Z).toReal := by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ (eLpNorm upper 2 S.P_Z).toReal := hmono
    _ ≤ K_AIPW ε *
        ((eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
          (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross n ω) 2 S.P_Z).toReal) := hupper_bound
    _ = K_AIPW ε *
        |(eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
          (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross n ω) 2 S.P_Z).toReal| := by
          rw [abs_of_nonneg]
          positivity

/-- The AIPW score difference has L² norm converging to zero in probability
when the nuisance errors converge in L².

This headline continuity result uses the almost-sure Lipschitz bound, the
covariate pushforward identity, and a truncation argument for the
residual-weighted propensity error. -/
theorem aipw_score_diff_isLittleOp_one
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_mu_memLp :
      ∀ n ω a, MemLp
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z =>
            aipwMomentFunctional (η_hat n ω) z S.θ₀ -
              aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  exact aipw_score_diff_isLittleOp_one_truncation_core
    S h_overlap hA h_y2 h_yd2 η_hat h_in_H h_mu_memLp h_e_memLp h_mu_rate h_e_rate

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
