/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bounds for the inverse second moment `I`

`I P U λ = ∫ U/(max U λ)²` is sandwiched by `J` from above (`I ≤ J`, pointwise) and
by an elementary *shell* argument from below.  The shell `(ρλ, λ]` with
`ρ = (cm/(2cp))^{1/κ}` carries mass `≥ (cm/2)λᵏ` (upper tail at `ρλ`, lower tail at
`λ`) on which the integrand `U/λ² ≥ ρ/λ`, giving

    I P U λ  ≥  (ρ·cm/2) · λ^{κ-1}.

Combined with `I ≤ J ≤ A·λ^{κ-1}` (regime `κ < 1`) this yields the two-sided
bound `a·λ^{κ-1} ≤ I ≤ A·λ^{κ-1}`.  The shell lower bound crucially uses **both**
tail bounds (the gap `cm < cp` makes a one-sided argument fail).
-/

import Causalean.Stat.PolynomialTail.MomentJBounds

/-!
# Bounds for the inverse second moment

This module proves the corresponding regime bounds for
`I P U lam = invMomentI P U lam = int U / (max U lam)^2`.  The upper side comes from the pointwise
comparison `invMomentI_le_invMomentJ`, so the `J` bounds from `MomentJBounds` immediately control
`I`.

The lower side is specific to `I`: `invMomentI_ge_shell` uses the annulus
`rho * lam < U <= lam`, with `rho = (cm / (2 * cp))^(1 / kappa)`, to extract a positive mass
shell from the two-sided polynomial-tail assumption.  The module then proves
`invMomentI_bounds_lt`, `invMomentI_bounds_eq`, and `invMomentI_bounds_gt` for the three regimes,
plus `IsTheta` corollaries `invMomentJ_isTheta_lt`, `invMomentI_isTheta_lt`,
`invMomentJ_isTheta_gt`, and `invMomentI_isTheta_gt` as `lam -> 0+`.
-/

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set Topology Filter Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
  {κ t₀ cm cp lam : ℝ}

/-- **`I ≤ J`.**  Pointwise `U/(max U λ)² ≤ (max U λ)⁻¹` (since `U ≤ max U λ`). -/
theorem invMomentI_le_invMomentJ [IsProbabilityMeasure P] (hsetup : TailSetup P U)
    (hlam_pos : 0 < lam) : invMomentI P U lam ≤ invMomentJ P U lam := by
  rw [invMomentI, invMomentJ]
  refine integral_mono_ae (integrable_invMomentI_integrand hsetup hlam_pos)
    (integrable_invMomentJ_integrand hsetup hlam_pos) ?_
  filter_upwards [hsetup.pos] with ω hUpos
  have hm : 0 < max (U ω) lam := lt_of_lt_of_le hlam_pos (le_max_right _ _)
  have hUm : U ω / max (U ω) lam ≤ 1 := by rw [div_le_one hm]; exact le_max_left _ _
  calc U ω / (max (U ω) lam) ^ 2
      = (U ω / max (U ω) lam) * (max (U ω) lam)⁻¹ := by
        rw [sq, ← div_div, div_eq_mul_inv]
    _ ≤ 1 * (max (U ω) lam)⁻¹ :=
        mul_le_mul_of_nonneg_right hUm (inv_nonneg.mpr hm.le)
    _ = (max (U ω) lam)⁻¹ := one_mul _

/-- **`J − I` is controlled by the tail mass.**  `J P U λ − I P U λ ≤ cp·λ^{κ-1}`.
Pointwise the gap equals `wλ/(max U λ) ≤ λ⁻¹·wλ`, and `∫ wλ ≤ P{U<λ} ≤ cp·λᵏ`. -/
theorem invMomentJ_sub_invMomentI_le [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    invMomentJ P U lam - invMomentI P U lam ≤ cp * lam ^ (κ - 1) := by
  have hJint := integrable_invMomentJ_integrand hsetup hlam_pos
  have hIint := integrable_invMomentI_integrand hsetup hlam_pos
  have hWint := integrable_trimWeight hsetup hlam_pos
  have hsmeas : MeasurableSet {ω | U ω < lam} := hsetup.measurable measurableSet_Iio
  have hptbound : ∀ᵐ ω ∂P, (max (U ω) lam)⁻¹ - U ω / (max (U ω) lam) ^ 2
      ≤ lam⁻¹ * trimWeight U lam ω := by
    filter_upwards [hsetup.pos] with ω hUpos
    have hm : 0 < max (U ω) lam := lt_of_lt_of_le hlam_pos (le_max_right _ _)
    have heq : (max (U ω) lam)⁻¹ - U ω / (max (U ω) lam) ^ 2
        = trimWeight U lam ω / max (U ω) lam := by simp only [trimWeight]; field_simp
    rw [heq, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hlam_pos (le_max_right _ _))
      (trimWeight_mem hlam_pos hUpos).1
  have hWmass : ∫ ω, trimWeight U lam ω ∂P ≤ P.real {ω | U ω < lam} := by
    have hind : P.real {ω | U ω < lam}
        = ∫ ω, Set.indicator {ω | U ω < lam} (fun _ => (1 : ℝ)) ω ∂P := by
      rw [integral_indicator hsmeas, setIntegral_const, smul_eq_mul, mul_one]
    rw [hind]
    refine integral_mono_ae hWint ((integrable_const (1 : ℝ)).indicator hsmeas) ?_
    filter_upwards [hsetup.pos] with ω hUpos
    by_cases hω : U ω < lam
    · rw [Set.indicator_of_mem (show ω ∈ {ω | U ω < lam} from hω)]
      exact (trimWeight_mem hlam_pos hUpos).2
    · have hw0 : trimWeight U lam ω = 0 := by
        simp only [trimWeight, max_eq_left (not_lt.mp hω), div_self (ne_of_gt hUpos), sub_self]
      rw [hw0, Set.indicator_of_notMem (show ω ∉ {ω | U ω < lam} from hω)]
  rw [invMomentJ, invMomentI, ← integral_sub hJint hIint]
  calc ∫ ω, ((max (U ω) lam)⁻¹ - U ω / (max (U ω) lam) ^ 2) ∂P
      ≤ ∫ ω, lam⁻¹ * trimWeight U lam ω ∂P :=
        integral_mono_ae (hJint.sub hIint) (hWint.const_mul _) hptbound
    _ = lam⁻¹ * ∫ ω, trimWeight U lam ω ∂P := integral_const_mul _ _
    _ ≤ lam⁻¹ * (cp * lam ^ κ) := by
        have h1 : (0 : ℝ) ≤ lam⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left
          (le_trans hWmass (measureReal_lt_le h hlam_pos hlam_le)) h1
    _ = cp * lam ^ (κ - 1) := by rw [Real.rpow_sub hlam_pos, Real.rpow_one]; field_simp

/-- **`I` is antitone in `λ`.**  As `λ` decreases, `max U λ` decreases, so the
integrand `U/(max U λ)²` increases.  Hence `I P U λ₂ ≤ I P U λ₁` when `λ₁ ≤ λ₂`. -/
theorem invMomentI_antitone [IsProbabilityMeasure P] (hsetup : TailSetup P U)
    {l1 l2 : ℝ} (hl1 : 0 < l1) (hl12 : l1 ≤ l2) :
    invMomentI P U l2 ≤ invMomentI P U l1 := by
  rw [invMomentI, invMomentI]
  refine integral_mono_ae (integrable_invMomentI_integrand hsetup (lt_of_lt_of_le hl1 hl12))
    (integrable_invMomentI_integrand hsetup hl1) ?_
  filter_upwards [hsetup.pos] with ω hUpos
  have hm1 : 0 < max (U ω) l1 := lt_of_lt_of_le hl1 (le_max_right _ _)
  have hmono : max (U ω) l1 ≤ max (U ω) l2 := max_le_max le_rfl hl12
  gcongr

/-! ## The shell lower bound -/

/-- **Shell lower bound on `I`.**  `(ρ·cm/2)·λ^{κ-1} ≤ I P U λ`, with
`ρ = (cm/(2cp))^{1/κ}`.  Valid for every `λ ∈ (0, t₀]`. -/
theorem invMomentI_ge_shell [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    (cm / 2) * (cm / (2 * cp)) ^ (1 / κ) * lam ^ (κ - 1) ≤ invMomentI P U lam := by
  have hcp_pos := h.cp_pos
  have hκ := h.kappa_pos
  set ρ : ℝ := (cm / (2 * cp)) ^ (1 / κ) with hρ
  have hbase_pos : 0 < cm / (2 * cp) := div_pos h.cm_pos (by linarith)
  have hbase_lt_one : cm / (2 * cp) < 1 := by
    rw [div_lt_one (by linarith)]; nlinarith [h.cm_lt_cp, h.cm_pos]
  have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos hbase_pos _
  have hρκ : ρ ^ κ = cm / (2 * cp) := by
    rw [hρ, ← Real.rpow_mul hbase_pos.le, one_div, inv_mul_cancel₀ (ne_of_gt hκ),
      Real.rpow_one]
  have hρ_lt_one : ρ < 1 := by
    by_contra hc
    push_neg at hc
    have := Real.one_le_rpow hc hκ.le
    rw [hρκ] at this; linarith
  have hrL_pos : 0 < ρ * lam := mul_pos hρ_pos hlam_pos
  have hrL_lt : ρ * lam < lam := by nlinarith [hlam_pos]
  have hrL_le_t0 : ρ * lam ≤ t₀ := le_of_lt (lt_of_lt_of_le hrL_lt hlam_le)
  -- shell set and its mass
  set S : Set Ω := {ω | ρ * lam < U ω ∧ U ω ≤ lam} with hS
  have hSmeas : MeasurableSet S :=
    (hsetup.measurable measurableSet_Ioi).inter (hsetup.measurable measurableSet_Iic)
  have hSsub : S = {ω | U ω ≤ lam} \ {ω | U ω ≤ ρ * lam} := by
    ext ω; simp only [hS, mem_setOf_eq, mem_diff, not_le]; tauto
  have hmass : (cm / 2) * lam ^ κ ≤ P.real S := by
    have hsub : {ω | U ω ≤ ρ * lam} ⊆ {ω | U ω ≤ lam} :=
      fun ω (hω : U ω ≤ ρ * lam) => le_trans hω hrL_lt.le
    rw [hSsub, measureReal_diff hsub (hsetup.measurable measurableSet_Iic)
      (measure_ne_top P _)]
    have hlo := h.tail_lower lam hlam_pos hlam_le
    have hhi := h.tail_upper (ρ * lam) hrL_pos hrL_le_t0
    have hrLk : (ρ * lam) ^ κ = (cm / (2 * cp)) * lam ^ κ := by
      rw [Real.mul_rpow hρ_pos.le hlam_pos.le, hρκ]
    rw [hrLk] at hhi
    have hsimp : cp * (cm / (2 * cp) * lam ^ κ) = (cm / 2) * lam ^ κ := by
      field_simp
    rw [hsimp] at hhi
    linarith
  -- pointwise: `(ρ/λ)·𝟙_S ≤ integrand`
  have hsmeas_int : Integrable
      (fun ω => (ρ / lam) * Set.indicator S (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hSmeas).const_mul _
  have hpt : ∀ᵐ ω ∂P,
      (ρ / lam) * Set.indicator S (fun _ => (1 : ℝ)) ω ≤ U ω / (max (U ω) lam) ^ 2 := by
    filter_upwards [hsetup.pos] with ω hUpos
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, mul_one, max_eq_right hω.2,
        show ρ / lam = ρ * lam / lam ^ 2 from by
          rw [sq]; exact (mul_div_mul_right ρ lam hlam_pos.ne').symm]
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr hω.1.le
    · rw [Set.indicator_of_notMem hω, mul_zero]
      positivity
  -- assemble
  have hint := integrable_invMomentI_integrand hsetup hlam_pos
  calc (cm / 2) * ρ * lam ^ (κ - 1)
      = (ρ / lam) * ((cm / 2) * lam ^ κ) := by
        rw [Real.rpow_sub hlam_pos, Real.rpow_one]; field_simp
    _ ≤ (ρ / lam) * P.real S :=
        mul_le_mul_of_nonneg_left hmass (div_nonneg hρ_pos.le hlam_pos.le)
    _ = ∫ ω, (ρ / lam) * Set.indicator S (fun _ => (1 : ℝ)) ω ∂P := by
        rw [integral_const_mul, integral_indicator hSmeas, setIntegral_const,
          smul_eq_mul, mul_one]
    _ ≤ invMomentI P U lam := by
        rw [invMomentI]; exact integral_mono_ae hsmeas_int hint hpt

/-! ## Two-sided bound for `I` in the regime `κ < 1` -/

/-- **Regime `0 < κ < 1`.** Under [the polynomial lower-tail hypothesis `PolyTail P U κ t₀ cm
cp`](hyp:h) with [`U` measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent
strictly between `0` and `1`](hyp:hκ1), [there exist constants `0 < a ≤ A` such that the
truncated inverse second moment `I P U λ` is squeezed between `a·λ^{κ-1}` and `A·λ^{κ-1}`,
uniformly for every `λ ∈ (0, t₀]`](goal). Lower: shell; upper: `I ≤ J`. -/
theorem invMomentI_bounds_lt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : κ < 1) :
    ∃ a A : ℝ, 0 < a ∧ a ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ t₀ →
      a * lam ^ (κ - 1) ≤ invMomentI P U lam ∧ invMomentI P U lam ≤ A * lam ^ (κ - 1) := by
  obtain ⟨aJ, AJ, haJ, haAJ, hJ⟩ := invMomentJ_bounds_lt h hsetup hκ1
  set aS : ℝ := (cm / 2) * (cm / (2 * cp)) ^ (1 / κ) with haS
  have haS_pos : 0 < aS :=
    mul_pos (by linarith [h.cm_pos])
      (Real.rpow_pos_of_pos (div_pos h.cm_pos (by linarith [h.cp_pos])) _)
  refine ⟨min aS AJ, AJ, lt_min haS_pos (lt_of_lt_of_le haJ haAJ), min_le_right _ _,
    fun lam hlp hll => ?_⟩
  have hpow_nonneg : 0 ≤ lam ^ (κ - 1) := Real.rpow_nonneg hlp.le _
  refine ⟨?_, le_trans (invMomentI_le_invMomentJ hsetup hlp) (hJ lam hlp hll).2⟩
  calc min aS AJ * lam ^ (κ - 1) ≤ aS * lam ^ (κ - 1) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hpow_nonneg
    _ ≤ invMomentI P U lam := invMomentI_ge_shell h hsetup hlp hll

/-! ## Two-sided bound for `I` in the regime `κ = 1` -/

/-- **Regime `κ = 1`.** Under [the polynomial lower-tail hypothesis `PolyTail P U κ t₀ cm
cp`](hyp:h) with [`U` measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent
exactly `1`](hyp:hκ), [there exist constants `0 < a ≤ A` such that the truncated inverse second
moment `I P U λ` is squeezed between `a·log(1/λ)` and `A·log(1/λ) + A`, uniformly for every
`λ ∈ (0, t₀]`](goal). Upper: `I ≤ J`; lower: `I = J − (J−I) ≥ J − cp`, uniformized with the
constant shell floor. -/
theorem invMomentI_bounds_eq [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ : κ = 1) :
    ∃ a A : ℝ, 0 < a ∧ a ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ t₀ →
      a * Real.log (1 / lam) ≤ invMomentI P U lam ∧
        invMomentI P U lam ≤ A * Real.log (1 / lam) + A := by
  subst hκ
  obtain ⟨aJ, AJ, haJ, haAJ, hJ⟩ := invMomentJ_bounds_eq h hsetup rfl
  have hcp_pos := h.cp_pos
  have hpow0 : ∀ x : ℝ, x ^ ((1 : ℝ) - 1) = 1 := fun x => by
    rw [show (1 : ℝ) - 1 = 0 from by norm_num, Real.rpow_zero]
  set L0 : ℝ := Real.log (1 / t₀) with hL0
  have hL0_pos : 0 < L0 := by
    rw [hL0]; apply Real.log_pos; rw [one_div]; exact (one_lt_inv₀ h.t0_pos).mpr h.t0_lt_one
  set cS : ℝ := (cm / 2) * (cm / (2 * cp)) ^ (1 / (1 : ℝ)) with hcS
  have hcS_pos : 0 < cS :=
    mul_pos (by linarith [h.cm_pos])
      (Real.rpow_pos_of_pos (div_pos h.cm_pos (by linarith)) _)
  set Lstar : ℝ := 2 * cp / aJ + L0 with hLstar
  have hLstar_pos : 0 < Lstar := by
    have : 0 < 2 * cp / aJ := div_pos (by linarith) haJ
    linarith
  refine ⟨min (aJ / 2) (cS / Lstar), AJ, lt_min (by linarith) (div_pos hcS_pos hLstar_pos),
    le_trans (min_le_left _ _) (by linarith), fun lam hlp hll => ?_⟩
  obtain ⟨hJlo, hJhi⟩ := hJ lam hlp hll
  have hrel := invMomentJ_sub_invMomentI_le h hsetup hlp hll
  rw [hpow0] at hrel
  have hsh := invMomentI_ge_shell h hsetup hlp hll
  rw [hpow0, mul_one] at hsh
  have hIle_J := invMomentI_le_invMomentJ hsetup hlp
  have hL : L0 ≤ Real.log (1 / lam) := by
    rw [hL0]
    exact Real.log_le_log (one_div_pos.mpr h.t0_pos) (one_div_le_one_div_of_le hlp hll)
  set L := Real.log (1 / lam) with hLdef
  have hL_pos : 0 < L := lt_of_lt_of_le hL0_pos hL
  refine ⟨?_, by linarith [hIle_J, hJhi]⟩
  -- lower: min(aJ/2, cS/Lstar) · L ≤ I
  by_cases hLcase : L ≤ Lstar
  · have hstep : (cS / Lstar) * L ≤ cS := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hLstar_pos]; nlinarith [hcS_pos, hLcase]
    have : min (aJ / 2) (cS / Lstar) * L ≤ (cS / Lstar) * L :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hL_pos.le
    linarith [hsh]
  · push_neg at hLcase
    have haJL : 2 * cp < aJ * L := by
      have h' : 2 * cp / aJ < L := by linarith [hL0_pos]
      rw [div_lt_iff₀ haJ] at h'; nlinarith [h']
    have : min (aJ / 2) (cS / Lstar) * L ≤ (aJ / 2) * L :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hL_pos.le
    nlinarith [hJlo, hrel, haJL, this]

/-! ## Bounded `I` in the regime `κ > 1` -/

/-- **Regime `κ > 1`.** Under [the polynomial lower-tail hypothesis `PolyTail P U κ t₀ cm
cp`](hyp:h) with [`U` measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent
strictly above `1`](hyp:hκ1), [there exist constants `0 < a ≤ A` such that the truncated inverse
second moment `I P U λ` is bounded between `a` and `A`, uniformly for every `λ ∈ (0,
t₀]`](goal): the inverse second moment does not blow up. Lower: `I` is antitone, so
`I(λ) ≥ I(t₀) ≥` (shell at `t₀`), a positive constant; upper: `I ≤ J`. -/
theorem invMomentI_bounds_gt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : 1 < κ) :
    ∃ a A : ℝ, 0 < a ∧ a ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ t₀ →
      a ≤ invMomentI P U lam ∧ invMomentI P U lam ≤ A := by
  obtain ⟨aJ, AJ, haJ, haAJ, hJ⟩ := invMomentJ_bounds_gt h hsetup hκ1
  set aI : ℝ := (cm / 2) * (cm / (2 * cp)) ^ (1 / κ) * t₀ ^ (κ - 1) with haI
  have haI_pos : 0 < aI :=
    mul_pos (mul_pos (by linarith [h.cm_pos])
      (Real.rpow_pos_of_pos (div_pos h.cm_pos (by linarith [h.cp_pos])) _))
      (Real.rpow_pos_of_pos h.t0_pos _)
  have haI_le : aI ≤ invMomentI P U t₀ := invMomentI_ge_shell h hsetup h.t0_pos le_rfl
  have haI_le_AJ : aI ≤ AJ :=
    le_trans haI_le (le_trans (invMomentI_le_invMomentJ hsetup h.t0_pos)
      (hJ t₀ h.t0_pos le_rfl).2)
  refine ⟨aI, AJ, haI_pos, haI_le_AJ, fun lam hlp hll => ?_⟩
  exact ⟨le_trans haI_le (invMomentI_antitone hsetup hlp hll),
    le_trans (invMomentI_le_invMomentJ hsetup hlp) (hJ lam hlp hll).2⟩

/-! ## IsTheta corollaries as `λ → 0⁺` -/

/-- Generic two-sided-bound ⟹ `IsTheta` packager on `𝓝[>] 0`. -/
theorem isTheta_of_two_sided {f g : ℝ → ℝ} {t₀ a A : ℝ} (ht0 : 0 < t₀) (ha : 0 < a)
    (hgpos : ∀ lam : ℝ, 0 < lam → lam ≤ t₀ → 0 < g lam)
    (hfnn : ∀ lam : ℝ, 0 < lam → lam ≤ t₀ → 0 ≤ f lam)
    (hbd : ∀ lam : ℝ, 0 < lam → lam ≤ t₀ → a * g lam ≤ f lam ∧ f lam ≤ A * g lam) :
    f =Θ[𝓝[>] (0 : ℝ)] g := by
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), 0 < lam ∧ lam ≤ t₀ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ht0)]
      with lam h1 h2 using ⟨h1, le_of_lt h2⟩
  refine ⟨?_, ?_⟩
  · rw [Asymptotics.isBigO_iff]
    refine ⟨A, hev.mono fun lam ⟨hlp, hll⟩ => ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hfnn lam hlp hll),
      abs_of_nonneg (hgpos lam hlp hll).le]
    exact (hbd lam hlp hll).2
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1 / a, hev.mono fun lam ⟨hlp, hll⟩ => ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hgpos lam hlp hll).le,
      abs_of_nonneg (hfnn lam hlp hll), one_div, inv_mul_eq_div, le_div_iff₀ ha, mul_comm]
    exact (hbd lam hlp hll).1

/-- **IsTheta for `J` (κ < 1).** Under [the polynomial lower-tail hypothesis](hyp:h) with [`U`
measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent strictly between `0` and
`1`](hyp:hκ1), [the truncated inverse first moment `J P U λ` is `Θ(λ^{κ-1})` as `λ →
0⁺`](goal). -/
theorem invMomentJ_isTheta_lt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : κ < 1) :
    (fun lam => invMomentJ P U lam) =Θ[𝓝[>] (0 : ℝ)] fun lam => lam ^ (κ - 1) := by
  obtain ⟨a, A, ha, _, hbd⟩ := invMomentJ_bounds_lt h hsetup hκ1
  exact isTheta_of_two_sided h.t0_pos ha (fun lam hlp _ => Real.rpow_pos_of_pos hlp _)
    (fun lam hlp hll => le_trans (mul_nonneg ha.le (Real.rpow_nonneg hlp.le _))
      (hbd lam hlp hll).1) hbd

/-- **IsTheta for `I` (κ < 1).** Under [the polynomial lower-tail hypothesis](hyp:h) with [`U`
measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent strictly between `0` and
`1`](hyp:hκ1), [the truncated inverse second moment `I P U λ` is `Θ(λ^{κ-1})` as `λ →
0⁺`](goal). -/
theorem invMomentI_isTheta_lt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : κ < 1) :
    (fun lam => invMomentI P U lam) =Θ[𝓝[>] (0 : ℝ)] fun lam => lam ^ (κ - 1) := by
  obtain ⟨a, A, ha, _, hbd⟩ := invMomentI_bounds_lt h hsetup hκ1
  exact isTheta_of_two_sided h.t0_pos ha (fun lam hlp _ => Real.rpow_pos_of_pos hlp _)
    (fun lam hlp hll => le_trans (mul_nonneg ha.le (Real.rpow_nonneg hlp.le _))
      (hbd lam hlp hll).1) hbd

/-- **IsTheta for `J` (κ > 1).** Under [the polynomial lower-tail hypothesis](hyp:h) with [`U`
measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent strictly above
`1`](hyp:hκ1), [the truncated inverse first moment `J P U λ` is `Θ(1)` — bounded — as `λ →
0⁺`](goal). -/
theorem invMomentJ_isTheta_gt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : 1 < κ) :
    (fun lam => invMomentJ P U lam) =Θ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  obtain ⟨a, A, ha, _, hbd⟩ := invMomentJ_bounds_gt h hsetup hκ1
  exact isTheta_of_two_sided h.t0_pos ha (fun _ _ _ => one_pos)
    (fun lam hlp hll => le_trans ha.le (hbd lam hlp hll).1)
    (fun lam hlp hll => by simpa using hbd lam hlp hll)

/-- **IsTheta for `I` (κ > 1).** Under [the polynomial lower-tail hypothesis](hyp:h) with [`U`
measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent strictly above
`1`](hyp:hκ1), [the truncated inverse second moment `I P U λ` is `Θ(1)` — bounded — as `λ →
0⁺`](goal). -/
theorem invMomentI_isTheta_gt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : 1 < κ) :
    (fun lam => invMomentI P U lam) =Θ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  obtain ⟨a, A, ha, _, hbd⟩ := invMomentI_bounds_gt h hsetup hκ1
  exact isTheta_of_two_sided h.t0_pos ha (fun _ _ _ => one_pos)
    (fun lam hlp hll => le_trans ha.le (hbd lam hlp hll).1)
    (fun lam hlp hll => by simpa using hbd lam hlp hll)

end Causalean.Stat.PolynomialTail
