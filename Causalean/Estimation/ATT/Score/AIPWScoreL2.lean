/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW score L²(P_Z) continuity (ATT)

Used by the ATT analogue of `DML.lean` for the `R₂` empirical-process step:
conditioning on the fold-A σ-algebra, the centered fold-B sum of
`m_AIPW^ATT(η̂(n), Z_i, θ₀) − m_AIPW^ATT(η₀, Z_i, θ₀)` has conditional second
moment bounded by

    ‖m_AIPW^ATT(η̂(n), ·, θ₀) − m_AIPW^ATT(η₀, ·, θ₀)‖²_{L²(P_Z)},

so we need that this L²-norm is `o_p(1)` under `μ`.

For `P_Z`-almost every observation, the ATT AIPW score is Lipschitz in `η` on
the a.e. one-sided-overlap nuisance set `H_ε`:

    |m_AIPW^ATT(η, z, θ₀) − m_AIPW^ATT(η₀, z, θ₀)|
      ≤ K_AIPW_ATT(ε) · |Δμ₀(x)|
        + K_AIPW_ATT(ε) · |y − μ₀_val(x)| · |Δe(x)|,

with `K_AIPW_ATT(ε)` depending only on `ε` (the overlap constant).  Compared to
the ATE counterpart, ATT only carries one μ-residual (`μ₀`, not `μ₁`), so the
score-difference decomposition has two terms (Δμ₀, residual · Δe) instead of
three.

Squaring, applying `(a+b)² ≤ 2(a²+b²)`, and integrating against `P_Z` gives a
quantitative bound on `‖Δ_AIPW^ATT‖²_{L²(P_Z)}` in terms of:

* `‖Δμ₀‖²_{L²(P_X)}` — controlled by an individual rate;
* `‖(Y − μ₀_val(X)) · Δe(X)‖²_{L²(P_Z)}` — needs `(Y − μ₀_val(X))² ∈ L¹(P_Z)`
  (from `h_y2`, `h_y0_2`, finite var of `μ₀_val` on `P_X`) plus
  `‖Δe‖_{L²(P_X)} = o_p(1)` and the truncation argument.

The headline corollary `aipw_score_diff_isLittleOp_one_ATT` packages the L²
continuity with the individual rates into the `o_p(1)` form consumed by the
`R₂` argument in the ATT DML pipeline.
-/

import Causalean.Estimation.ATT.Score.AIPWMoment
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
Proves `L²(P_Z)` continuity bounds for the ATT AIPW score as the nuisance
functions vary. The pointwise constant `K_AIPW_ATT` controls the Lipschitz bound
`aipw_score_lipschitz_ATT` on the a.e. one-sided-overlap class `H_ε`.

The file also defines the residual square `YMuVal_residual_sq_ATT` and proves
the headline stochastic-continuity theorem
`aipw_score_diff_isLittleOp_one_ATT`: if the control-regression and propensity
errors are individually `o_p(1)` in `L²(P_X)`, then the AIPW score difference is
`o_p(1)` in `L²(P_Z)`. This is the empirical-process input for ATT double
machine learning.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open Causalean.Estimation.ATE.BackdoorEstimationSystem (projX projA projY indA)

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## A.e. Lipschitz bound on `m_AIPW^ATT(·, z, θ₀)` on `H_ε` -/

/-- Pointwise Lipschitz constant for the ATT AIPW moment in `η` on `H_ε`:
`K_AIPW_ATT ε := 1 + 2/ε + 2/ε²`.  Tracks the quadratic blow-up of the inverse
weight `1/(1−ê)` and the cross term `(ê − e)/((1−ê)·(1−e))` arising from the
single IPW factor `e/(1−e)` in the ATT AIPW form.  Same shape as the ATE
constant `K_AIPW`, which is fine — both are dominated by the worst-case
`1/ε²` term. -/
noncomputable def K_AIPW_ATT (ε : ℝ) : ℝ := 1 + 2 / ε + 2 / ε ^ 2

/-- Trivial monotonicity: `1 ≤ K_AIPW_ATT ε`. -/
private lemma K_AIPW_ATT_one_le {ε : ℝ} (hε : 0 < ε) :
    1 ≤ K_AIPW_ATT ε := by
  unfold K_AIPW_ATT
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

/-- `1 + 1/ε ≤ K_AIPW_ATT ε`. Used to dominate the μ-residual term. -/
private lemma K_AIPW_ATT_mu_le {ε : ℝ} (hε : 0 < ε) :
    1 + 1 / ε ≤ K_AIPW_ATT ε := by
  unfold K_AIPW_ATT
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

/-- `1/ε² ≤ K_AIPW_ATT ε`. Used to dominate the cross-term `|y−μ₀|·|Δe|/ε²`. -/
private lemma K_AIPW_ATT_inv_sq_le {ε : ℝ} (hε : 0 < ε) :
    1 / ε ^ 2 ≤ K_AIPW_ATT ε := by
  unfold K_AIPW_ATT
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

private lemma abs_div_sub_div_le_ATT
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

private lemma aipw_att_real_bound
    {ε e ê μ μhat y θ : ℝ} {a : Bool}
    (hε : 0 < ε) (he : e ≤ 1 - ε) (hê : ê ≤ 1 - ε) :
    |((if a = true then 1 else 0) * (y - μhat)
        - (1 - (if a = true then 1 else 0)) * (ê / (1 - ê)) * (y - μhat)
        - (if a = true then 1 else 0) * θ)
      - ((if a = true then 1 else 0) * (y - μ)
        - (1 - (if a = true then 1 else 0)) * (e / (1 - e)) * (y - μ)
        - (if a = true then 1 else 0) * θ)|
      ≤ K_AIPW_ATT ε * |μhat - μ| + K_AIPW_ATT ε * |y - μ| * |ê - e| := by
  have hK1 : 1 ≤ K_AIPW_ATT ε := K_AIPW_ATT_one_le hε
  have hKμ : 1 + 1 / ε ≤ K_AIPW_ATT ε := K_AIPW_ATT_mu_le hε
  have hKe : 1 / ε ^ 2 ≤ K_AIPW_ATT ε := K_AIPW_ATT_inv_sq_le hε
  have hKnonneg : 0 ≤ K_AIPW_ATT ε := le_trans zero_le_one hK1
  have hden_e : ε ≤ 1 - e := by linarith
  have hden_ê : ε ≤ 1 - ê := by linarith
  have hden_e_pos : 0 < 1 - e := lt_of_lt_of_le hε hden_e
  have hden_ê_pos : 0 < 1 - ê := lt_of_lt_of_le hε hden_ê
  have hden_e_ne : 1 - e ≠ 0 := hden_e_pos.ne'
  have hden_ê_ne : 1 - ê ≠ 0 := hden_ê_pos.ne'
  set dμ : ℝ := |μhat - μ|
  set r : ℝ := |y - μ|
  set de : ℝ := |ê - e|
  have hdμ : 0 ≤ dμ := by simp [dμ]
  have hr : 0 ≤ r := by simp [r]
  have hde : 0 ≤ de := by simp [de]
  have hμcoef : (1 + 1 / ε) * dμ ≤ K_AIPW_ATT ε * dμ :=
    mul_le_mul_of_nonneg_right hKμ hdμ
  have hcross : r * de / ε ^ 2 ≤ K_AIPW_ATT ε * r * de := by
    calc
      r * de / ε ^ 2 = (1 / ε ^ 2) * r * de := by ring
      _ ≤ K_AIPW_ATT ε * r * de := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKe hr) hde
  cases a
  · have hfrac := abs_div_sub_div_le_ATT (e := 1 - e) (ê := 1 - ê)
      (y := y) (μ := μ) (μhat := μhat) hε hden_e hden_ê
    have hfrac' :
        |(y - μhat) / (1 - ê) - (y - μ) / (1 - e)| ≤
          dμ / ε + r * de / ε ^ 2 := by
      have hde' : |(1 - ê) - (1 - e)| = de := by
        calc
          |(1 - ê) - (1 - e)| = |-(ê - e)| := by congr 1; ring
          _ = de := by simpa [de] using abs_sub_comm e ê
      simpa [dμ, r, de, hde', abs_sub_comm e ê] using hfrac
    have hsplit :
        ((0 : ℝ) * (y - μhat)
            - (1 - (0 : ℝ)) * (ê / (1 - ê)) * (y - μhat)
            - (0 : ℝ) * θ)
          - ((0 : ℝ) * (y - μ)
            - (1 - (0 : ℝ)) * (e / (1 - e)) * (y - μ)
            - (0 : ℝ) * θ)
        = -(μhat - μ) - ((y - μhat) / (1 - ê) - (y - μ) / (1 - e)) := by
      simp only [zero_mul, one_mul, sub_zero, zero_sub]
      field_simp [hden_ê_ne, hden_e_ne]
      ring
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hsplit]
    calc
      |-(μhat - μ) - ((y - μhat) / (1 - ê) - (y - μ) / (1 - e))|
          ≤ dμ + (dμ / ε + r * de / ε ^ 2) := by
            calc
              |-(μhat - μ) - ((y - μhat) / (1 - ê) - (y - μ) / (1 - e))|
                  ≤ |-(μhat - μ)| +
                      |(y - μhat) / (1 - ê) - (y - μ) / (1 - e)| := abs_sub _ _
              _ = |μhat - μ| +
                      |(y - μhat) / (1 - ê) - (y - μ) / (1 - e)| := by
                rw [abs_neg]
              _ ≤ dμ + (dμ / ε + r * de / ε ^ 2) := by
                nlinarith [hfrac']
      _ = (1 + 1 / ε) * dμ + r * de / ε ^ 2 := by ring
      _ ≤ K_AIPW_ATT ε * dμ + K_AIPW_ATT ε * r * de := by
        exact add_le_add hμcoef hcross
      _ = K_AIPW_ATT ε * |μhat - μ| + K_AIPW_ATT ε * |y - μ| * |ê - e| := by
        simp [dμ, r, de]
  · have hpre :
        |((1 : ℝ) * (y - μhat)
            - (1 - (1 : ℝ)) * (ê / (1 - ê)) * (y - μhat)
            - (1 : ℝ) * θ)
          - ((1 : ℝ) * (y - μ)
            - (1 - (1 : ℝ)) * (e / (1 - e)) * (y - μ)
            - (1 : ℝ) * θ)| = dμ := by
      simp [dμ, abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simp only [↓reduceIte]
    rw [hpre]
    calc
      dμ ≤ K_AIPW_ATT ε * dμ := by
        simpa using mul_le_mul_of_nonneg_right hK1 hdμ
      _ ≤ K_AIPW_ATT ε * dμ + K_AIPW_ATT ε * r * de := by
        have hnonneg : 0 ≤ K_AIPW_ATT ε * r * de := by positivity
        linarith
      _ = K_AIPW_ATT ε * |μhat - μ| + K_AIPW_ATT ε * |y - μ| * |ê - e| := by
        simp [dμ, r, de]

/-- **ATT AIPW score Lipschitz bound on the a.e. one-sided-overlap set `H_ε`.**

For any `η ∈ H_ε`, the ATT AIPW moment difference satisfies the usual Lipschitz
bound for `P_Z`-almost every observation.  The nuisance-side one-sided overlap
is only a `P_X`-a.e. restriction; pushing it forward along `X` gives the needed
`P_Z`-a.e. denominator bound.

    |m_AIPW^ATT(η, z, θ₀) − m_AIPW^ATT(η₀, z, θ₀)|
      ≤ K_AIPW_ATT(ε) · |Δμ₀(x)|
        + K_AIPW_ATT(ε) · |y − μ₀_val(x)| · |Δe(x)|.

Proof outline: expand the ATT moment

    A · (Y − μ₀_fn(X)) − (1−A) · (e_fn/(1−e_fn)) · (Y − μ₀_fn(X)) − A · θ₀,

apply triangle inequality, and use the algebraic identity
`a/u − a/v = a · (v − u)/(u · v)` together with the one-sided overlap bounds
`1/(1−ê), 1/(1−e) ≤ 1/ε` and `1/((1−ê)(1−e)) ≤ 1/ε²`.  Note the simpler
structure compared to the ATE score-difference bound: only the
control-arm `μ₀` residual appears, so we get two summands instead of three. -/
theorem aipw_score_lipschitz_ATT
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (η : TreatedNuisanceVec γ) (hη : η ∈ H_ε S ε) :
    ∀ᵐ z ∂S.P_Z,
    |aipwMomentATTFunctional η z S.θ₀ - aipwMomentATTFunctional S.η₀ z S.θ₀|
      ≤ K_AIPW_ATT ε * |η.μ₀_fn (projX z) - S.μ₀_val (projX z)|
        + K_AIPW_ATT ε *
            |projY z - S.μ₀_val (projX z)| *
            |η.e_fn (projX z) - S.e_val (projX z)| := by
  rcases h_overlap with ⟨hε_pos, _hε_half, _hprop⟩
  filter_upwards [H_ε_overlap_P_Z S hη, H_ε_overlap_P_Z S hη₀_mem] with z hηz hSz_raw
  have hSz : S.e_val (projX z) ≤ 1 - ε := by
    simpa [TreatedEstimationSystem.η₀] using hSz_raw
  have hbound := aipw_att_real_bound (a := projA z) (ε := ε)
    (e := S.e_val (projX z)) (ê := η.e_fn (projX z))
    (μ := S.μ₀_val (projX z)) (μhat := η.μ₀_fn (projX z))
    (y := projY z) (θ := S.θ₀) hε_pos hSz hηz
  simpa [aipwMomentATTFunctional, aipwMomentATT, η₀, indA, abs_sub_comm,
    mul_assoc] using hbound

/-! ## L²(P_Z) `o_p(1)` continuity of the ATT AIPW score on `H_ε` -/

/-- The single ATT residual integrand `|Y − μ₀(X)|`, viewed on the data space. -/
noncomputable def YMuVal_residual_sq_ATT
    (S : TreatedEstimationSystem P γ) : (γ × Bool × ℝ) → ℝ :=
  fun z => (projY z - S.μ₀_val (projX z)) ^ 2

private lemma yMuVal_residual_meas_ATT
    (S : TreatedEstimationSystem P γ) :
    Measurable (fun z : γ × Bool × ℝ =>
      |projY z - S.μ₀_val (projX z)|) := by
  have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
    simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
  have hy : Measurable (fun z : γ × Bool × ℝ => projY z) := by
    simpa [projY] using
      (measurable_snd.snd : Measurable (fun z : γ × Bool × ℝ => z.2.2))
  have hμ : Measurable (fun z : γ × Bool × ℝ => S.μ₀_val (projX z)) :=
    S.μ₀_meas.comp hx
  simpa [Real.norm_eq_abs] using (hy.sub hμ).norm

private theorem yMuVal_residual_sq_integrable_ATT
    (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ) :
    Integrable (S.YMuVal_residual_sq_ATT) S.P_Z := by
  have _ := hA
  have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ := by
    exact (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ_L2 :
      MemLp (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
    have hY0_L2 : MemLp (S.toPOBackdoorSystem.YofD false) 2 P.μ := by
      exact (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD false).aestronglyMeasurable).2 h_y0_2
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD false |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hY0_L2.condExp
    exact hcond_L2.ae_eq (S.μ₀_compat hA)
  let g : γ × Bool × ℝ → ℝ :=
    fun z => |projY z - S.μ₀_val (projX z)|
  have hg_meas : Measurable g := by
    simpa [g] using yMuVal_residual_meas_ATT S
  have hg_comp_L2 : MemLp (fun ω => g (S.factualZ ω)) 2 P.μ := by
    have hdiff : MemLp
        (fun ω => S.toPOBackdoorSystem.factualY ω -
          S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hY_L2.sub hμ_L2
    simpa [g, TreatedEstimationSystem.factualZ, projX, projY, Real.norm_eq_abs]
      using hdiff.norm
  have hg_L2 : MemLp g 2 S.P_Z := by
    rw [TreatedEstimationSystem.P_Z]
    exact (memLp_map_measure_iff hg_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 hg_comp_L2
  simpa [TreatedEstimationSystem.YMuVal_residual_sq_ATT, g] using hg_L2.integrable_sq

private lemma yMuVal_residual_memLp_ATT
    (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ) :
    MemLp (fun z : γ × Bool × ℝ =>
      |projY z - S.μ₀_val (projX z)|) 2 S.P_Z := by
  exact (memLp_two_iff_integrable_sq (yMuVal_residual_meas_ATT S).aestronglyMeasurable).2
    (by
      simpa [TreatedEstimationSystem.YMuVal_residual_sq_ATT] using
        yMuVal_residual_sq_integrable_ATT S hA h_y2 h_y0_2)

private lemma eLpNorm_comp_projX_eq_ATT
    (S : TreatedEstimationSystem P γ) {f : γ → ℝ}
    (hf : AEStronglyMeasurable f S.P_X) :
    eLpNorm (fun z : γ × Bool × ℝ => f (projX z)) 2 S.P_Z =
      eLpNorm f 2 S.P_X := by
  have hfmap :
      AEStronglyMeasurable f (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
    simpa [TreatedEstimationSystem.P_Z_map_projX_eq_P_X S] using hf
  rw [← TreatedEstimationSystem.P_Z_map_projX_eq_P_X S]
  simpa [projX, Function.comp_def] using
    (MeasureTheory.eLpNorm_map_measure
      (μ := S.P_Z) (f := fun z : γ × Bool × ℝ => z.1) (g := f)
      (p := 2) hfmap measurable_fst.aemeasurable).symm

set_option maxHeartbeats 800000 in
-- The projection-norm rewrite unfolds the `P_Z.map projX = P_X` bridge.
private lemma e_error_eLpNorm_projX_toReal_eq_ATT
    (S : TreatedEstimationSystem P γ) (η : TreatedNuisanceVec γ)
    (hηe : MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X) :
    (eLpNorm (fun z : γ × Bool × ℝ => η.e_fn (projX z) - S.e_val (projX z))
        2 S.P_Z).toReal =
      (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
  exact congrArg ENNReal.toReal
    (eLpNorm_comp_projX_eq_ATT (S := S)
      (f := fun x => η.e_fn x - S.e_val x) hηe.aestronglyMeasurable)

set_option maxHeartbeats 800000 in
-- The truncation proof combines several `MemLp` and `lpNorm` coercion steps.
private theorem residual_mul_e_error_isLittleOp_one_ATT
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (h_e_lb : ∀ x, 0 ≤ S.e_val x)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ)
    (h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε S ε)
    (h_e_lb_hat : ∀ n ω x, 0 ≤ (η_hat n ω).e_fn x)
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
          |projY z - S.μ₀_val (projX z)| *
            |(η_hat n ω).e_fn (projX z) - S.e_val (projX z)|) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  rcases h_overlap with ⟨hε_pos, _hε_half, _hprop⟩
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  let R : (γ × Bool × ℝ) → ℝ := fun z =>
    |projY z - S.μ₀_val (projX z)|
  let deZ : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    (η_hat n ω).e_fn (projX z) - S.e_val (projX z)
  have hR_meas : Measurable R := by
    simpa [R] using yMuVal_residual_meas_ATT S
  have hR_nonneg : ∀ z, 0 ≤ R z := by
    intro z
    dsimp [R]
    positivity
  have hR_memLp : MemLp R 2 S.P_Z := by
    simpa [R] using yMuVal_residual_memLp_ATT S hA h_y2 h_y0_2
  have hdeZ_memLp : ∀ n ω, MemLp (deZ n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [TreatedEstimationSystem.P_Z_map_projX_eq_P_X S] using h_e_memLp n ω
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
    filter_upwards [H_ε_overlap_P_Z S (h_in_Hε n ω),
      H_ε_overlap_P_Z S hη₀_mem] with z hη_le_M hS_le_M_raw
    have hη_nonneg : 0 ≤ (η_hat n ω).e_fn (projX z) :=
      h_e_lb_hat n ω (projX z)
    have hS_nonneg : 0 ≤ S.e_val (projX z) := h_e_lb (projX z)
    have hS_le_M : S.e_val (projX z) ≤ 1 - ε := by
      simpa [TreatedEstimationSystem.η₀] using hS_le_M_raw
    have hM_le_one : 1 - ε ≤ 1 := by linarith
    dsimp [deZ]
    rw [abs_le]
    constructor
    · linarith
    · linarith
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
    simpa [deZ] using e_error_eLpNorm_projX_toReal_eq_ATT S (η_hat n ω) (h_e_memLp n ω)
  have hde_large_X :
      δ / (2 * M) <
        (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal := by
    simpa [heq_norm] using hde_large
  have hde_nonneg :
      0 ≤ (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal :=
    ENNReal.toReal_nonneg
  simpa [abs_of_nonneg hde_nonneg] using hde_large_X

/-- **Headline L²(P_Z) `o_p(1)` continuity bound for the ATT AIPW score.**

Given:
* one-sided overlap `ε` for `(μ₀_val, e_val)`, with the truth nuisance
  `S.η₀` in the a.e. nuisance class `H_ε S ε`;
* the universal probability-bound `0 ≤ e_val x` for the truth and
  `0 ≤ (η̂ n ω).e_fn x` for every realization (these encode the standard
  "propensity is a probability" normalization; combined with the upper bound
  `≤ 1 − ε` they yield `|Δe(x)| ≤ 1 − ε ≤ 1`);
* one-sided ATT back-door assumptions, used to put `Y − μ₀_val(X)` in `L²(P_Z)`;
* `Y² ∈ L¹(P.μ)` and `Y(0)² ∈ L¹(P.μ)`;
* a random nuisance `η̂(n, ω) ∈ H_ε S ε` for all `n, ω`;
* per-realization `L²(P_X)` witnesses for `Δμ₀` and `Δe`;
* individual rates `‖Δμ₀(n,ω,·)‖_{L²(P_X)} = o_p(1)` and
  `‖Δe(n,ω,·)‖_{L²(P_X)} = o_p(1)`.

Then `‖m_AIPW^ATT(η̂(n,ω), ·, θ₀) − m_AIPW^ATT(η₀, ·, θ₀)‖_{L²(P_Z)} = o_p(1)`
under `μ`.

**Proof outline.**  Apply `aipw_score_lipschitz_ATT`; square and integrate
against `P_Z`; for the cross term use `|Δe| ≤ 1` (from `0 ≤ ê, e ≤ 1 − ε`)
and a truncation argument on `(y − μ₀_val(x))²`.  The ATT version is simpler
than the ATE one because there is only one μ-residual: the L²(P_X) sum has
two terms (`‖Δμ₀‖²` and the truncation cross term) rather than three. -/
theorem aipw_score_diff_isLittleOp_one_ATT
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (h_e_lb : ∀ x, 0 ≤ S.e_val x)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ)
    (h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε S ε)
    (h_e_lb_hat : ∀ n ω x, 0 ≤ (η_hat n ω).e_fn x)
    (h_mu_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_mu_diff : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_e_diff : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z =>
            aipwMomentATTFunctional (η_hat n ω) z S.θ₀
              - aipwMomentATTFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  rcases h_overlap with ⟨hε_pos, hε_half, hprop⟩
  let R : (γ × Bool × ℝ) → ℝ := fun z =>
    |projY z - S.μ₀_val (projX z)|
  let dμZ : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    (η_hat n ω).μ₀_fn (projX z) - S.μ₀_val (projX z)
  let deZ : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    (η_hat n ω).e_fn (projX z) - S.e_val (projX z)
  let cross : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    R z * |deZ n ω z|
  let score : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    aipwMomentATTFunctional (η_hat n ω) z S.θ₀ -
      aipwMomentATTFunctional S.η₀ z S.θ₀
  have hR_meas : Measurable R := by
    simpa [R] using yMuVal_residual_meas_ATT S
  have hR_nonneg : ∀ z, 0 ≤ R z := by
    intro z
    dsimp [R]
    positivity
  have hR_memLp : MemLp R 2 S.P_Z := by
    simpa [R] using yMuVal_residual_memLp_ATT S hA h_y2 h_y0_2
  have hdμZ_memLp : ∀ n ω, MemLp (dμZ n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [TreatedEstimationSystem.P_Z_map_projX_eq_P_X S] using h_mu_memLp n ω
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    simpa [dμZ, projX] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_memLp : ∀ n ω, MemLp (deZ n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [TreatedEstimationSystem.P_Z_map_projX_eq_P_X S] using h_e_memLp n ω
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    simpa [deZ, projX] using
      (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_bdd : ∀ n ω, ∀ᵐ z ∂S.P_Z, |deZ n ω z| ≤ 1 := by
    intro n ω
    filter_upwards [H_ε_overlap_P_Z S (h_in_Hε n ω),
      H_ε_overlap_P_Z S hη₀_mem] with z hη_le_M hS_le_M_raw
    have hη_nonneg : 0 ≤ (η_hat n ω).e_fn (projX z) :=
      h_e_lb_hat n ω (projX z)
    have hS_nonneg : 0 ≤ S.e_val (projX z) := h_e_lb (projX z)
    have hS_le_M : S.e_val (projX z) ≤ 1 - ε := by
      simpa [TreatedEstimationSystem.η₀] using hS_le_M_raw
    have hM_le_one : 1 - ε ≤ 1 := by linarith
    dsimp [deZ]
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hcross_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (cross n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [cross, R, deZ] using
      residual_mul_e_error_isLittleOp_one_ATT S ⟨hε_pos, hε_half, hprop⟩
        hη₀_mem h_e_lb hA h_y2 h_y0_2 η_hat h_in_Hε h_e_lb_hat
        h_e_memLp h_e_diff
  have hμZ_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (dμZ n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    have heq :
        (fun n ω => (eLpNorm (dμZ n ω) 2 S.P_Z).toReal) =
          (fun n ω =>
            (eLpNorm (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal) := by
      funext n
      funext ω
      dsimp [dμZ]
      exact congrArg ENNReal.toReal
        (eLpNorm_comp_projX_eq_ATT (S := S)
          (f := fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x)
          (h_mu_memLp n ω).aestronglyMeasurable)
    rw [heq]
    exact h_mu_diff
  have hsum_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (dμZ n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    exact IsLittleOp.add_one hμZ_rate hcross_rate
  have hK_pos : 0 < K_AIPW_ATT ε := lt_of_lt_of_le zero_lt_one (K_AIPW_ATT_one_le hε_pos)
  refine IsLittleOp.of_abs_le_const_mul_one (C := K_AIPW_ATT ε) hK_pos hsum_rate ?_
  intro n ω
  have hpointwise :
      ∀ᵐ z ∂S.P_Z, |score n ω z| ≤
        K_AIPW_ATT ε * (|dμZ n ω z| + cross n ω z) := by
    simpa [score, dμZ, cross, R, deZ, mul_add, mul_assoc, add_comm, add_left_comm,
      add_assoc]
      using aipw_score_lipschitz_ATT S ⟨hε_pos, hε_half, hprop⟩
        hη₀_mem (η_hat n ω) (h_in_Hε n ω)
  let upper : (γ × Bool × ℝ) → ℝ := fun z =>
    K_AIPW_ATT ε * (|dμZ n ω z| + cross n ω z)
  have hcross_memLp : MemLp (cross n ω) 2 S.P_Z := by
    have hcross_meas : Measurable (cross n ω) := by
      have hde_meas : Measurable (deZ n ω) := by
        have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
          simpa [projX] using
            (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
        exact ((η_hat n ω).e_meas.comp hx).sub (S.e_meas.comp hx)
      simpa [cross, Real.norm_eq_abs] using hR_meas.mul hde_meas.norm
    refine hR_memLp.mono' hcross_meas.aestronglyMeasurable ?_
    filter_upwards [hdeZ_bdd n ω] with z hdez_le
    have hRz : 0 ≤ R z := hR_nonneg z
    dsimp [cross]
    rw [abs_mul, abs_of_nonneg hRz, abs_of_nonneg (abs_nonneg _)]
    exact mul_le_of_le_one_right hRz hdez_le
  have hupper_memLp : MemLp upper 2 S.P_Z := by
    have hsum : MemLp
        (fun z => |dμZ n ω z| + cross n ω z) 2 S.P_Z := by
      have hμ : MemLp (fun z => |dμZ n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp n ω).norm
      exact hμ.add hcross_memLp
    simpa [upper, Pi.smul_apply, smul_eq_mul] using hsum.const_smul (K_AIPW_ATT ε)
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
        K_AIPW_ATT ε *
          ((eLpNorm (dμZ n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross n ω) 2 S.P_Z).toReal) := by
    let total : (γ × Bool × ℝ) → ℝ := fun z =>
      |dμZ n ω z| + cross n ω z
    have htotal_memLp : MemLp total 2 S.P_Z := by
      have hμ : MemLp (fun z => |dμZ n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp n ω).norm
      simpa [total] using hμ.add hcross_memLp
    have hupper_eq : upper = K_AIPW_ATT ε • total := by
      funext z
      simp [upper, total, smul_eq_mul]
    rw [hupper_eq]
    rw [toReal_eLpNorm (htotal_memLp.const_smul (K_AIPW_ATT ε)).aestronglyMeasurable]
    rw [lpNorm_const_smul]
    have hcoef : (↑‖K_AIPW_ATT ε‖₊ : ℝ) = K_AIPW_ATT ε := by
      simp [Real.norm_eq_abs, abs_of_pos hK_pos]
    rw [hcoef]
    gcongr
    have htri :
        lpNorm total 2 S.P_Z ≤
          lpNorm (fun z => |dμZ n ω z|) 2 S.P_Z +
            lpNorm (cross n ω) 2 S.P_Z := by
      have htotal_eq :
          total = (fun z => |dμZ n ω z|) + cross n ω := by
        funext z
        simp [total, Pi.add_apply]
      rw [htotal_eq]
      have hμ : MemLp (fun z => |dμZ n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp n ω).norm
      exact lpNorm_add_le (f := fun z => |dμZ n ω z|)
        (g := cross n ω) (μ := S.P_Z) hμ
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hnormμ :
        lpNorm (fun z => |dμZ n ω z|) 2 S.P_Z =
          (eLpNorm (dμZ n ω) 2 S.P_Z).toReal := by
      rw [lpNorm_fun_abs (hdμZ_memLp n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdμZ_memLp n ω).aestronglyMeasurable]
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
    _ ≤ K_AIPW_ATT ε *
        ((eLpNorm (dμZ n ω) 2 S.P_Z).toReal +
          (eLpNorm (cross n ω) 2 S.P_Z).toReal) := hupper_bound
    _ = K_AIPW_ATT ε *
        |(eLpNorm (dμZ n ω) 2 S.P_Z).toReal +
          (eLpNorm (cross n ω) 2 S.P_Z).toReal| := by
          rw [abs_of_nonneg]
          positivity

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
