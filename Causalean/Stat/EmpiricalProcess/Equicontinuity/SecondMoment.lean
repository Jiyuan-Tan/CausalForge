/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Second-moment / Chebyshev control of the vector empirical process

The uniform-in-`n` workhorse behind asymptotic equicontinuity.  For an `E`-valued
function `f` (with `E` a finite-dimensional real inner-product space) the centered
empirical process `Gₙ(f) = empProcVec f n` satisfies the **variance identity at
the empirical-process scale**

    E_μ ‖Gₙ(f)‖² ≤ ∫ ‖f‖² dP                 (uniformly in `n ≥ 1`),

because `Var(√n (Pₙ − P) f) = Var_P f` for i.i.d. data — no central limit theorem
and no chaining are needed.  Chebyshev then gives

    μ {‖Gₙ(f)‖ > ε} ≤ (∫ ‖f‖² dP) / ε².

The proof reduces the `E`-valued second moment to the scalar one coordinate-wise
through an orthonormal basis (Parseval, `OrthonormalBasis.sum_sq_inner_right`) and
the scalar variance bound `Causalean.Mathlib.iid_centered_sum_sq_lintegral_le`.

This is the quantitative input to the deterministic-curve equicontinuity corollary
(`Equicontinuity/Modulus.lean`) and to any concrete discharge of
`AsymptoticEquicont`.
-/

import Causalean.Stat.EmpiricalProcess.Equicontinuity.Process
import Causalean.Mathlib.IIDCenteredSum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Empirical-Process Second Moments

This file bounds the second moment of the vector-valued centered empirical
process by the population second moment of the indexed function.  The lemma
`IIDSample.measurable_empProcVec` records measurability of the process,
`empProcVec_sq_lintegral_le` proves the uniform-in-sample-size second-moment
bound, and `empProcVec_chebyshev` converts it into the tail estimate used by
stochastic-equicontinuity and empirical-process remainder bounds. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- The i.i.d. product law of the first `n` coordinates: copied pattern from the
sample-quantile oscillation file. -/
private lemma iid_pi_law (S : IIDSample Ω X μ P) (n : ℕ) :
    μ.map (fun ω (i : Finset.range n) => S.Z i ω)
      = Measure.pi (fun _ : Finset.range n => P) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hindep : iIndepFun (fun i : Finset.range n => S.Z i) μ :=
    S.indep.precomp (Subtype.val_injective (p := fun i => i ∈ Finset.range n))
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Finset.range n => (S.meas i).aemeasurable)).mp hindep
  calc μ.map (fun ω (i : Finset.range n) => S.Z i ω)
      = Measure.pi (fun i : Finset.range n => μ.map (S.Z i)) := hmap
    _ = Measure.pi (fun _ : Finset.range n => P) := by
        congr with i; rw [← (S.identDist i).map_eq, S.law]

/-- Coordinate decomposition of the vector empirical process: for any fixed
`c : E` and `n ≥ 1`, `⟪c, Gₙ(f)(ω)⟫` is the scalar centered i.i.d. sum of
`gᵢ ↦ ⟪c, f (Zᵢ ω)⟫`.  This is the bridge to the scalar variance bound. -/
private lemma inner_empProcVec (S : IIDSample Ω X μ P) (f : X → E)
    (hf_int : Integrable f P) (c : E) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    inner ℝ c (S.empProcVec f n ω)
      = (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
          (inner ℝ c (f (S.Z i ω)) - ∫ x, inner ℝ c (f x) ∂P) := by
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr this
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hinner_int : inner ℝ c (∫ x, f x ∂P) = ∫ x, inner ℝ c (f x) ∂P :=
    (integral_inner hf_int c).symm
  have key : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
    field_simp
    linarith [hsq]
  have hLHS : inner ℝ c (S.empProcVec f n ω)
      = (Real.sqrt (n : ℝ))⁻¹ * (∑ i ∈ Finset.range n, inner ℝ c (f (S.Z i ω)))
        - Real.sqrt (n : ℝ) * ∫ x, inner ℝ c (f x) ∂P := by
    simp only [IIDSample.empProcVec, inner_sub_right, real_inner_smul_right,
      inner_sum, hinner_int]
  rw [hLHS, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_sub, ← mul_assoc, key]

/-- The vector empirical process is measurable in `ω`. -/
lemma measurable_empProcVec [MeasurableSpace E] [BorelSpace E]
    (S : IIDSample Ω X μ P) (f : X → E) (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω => S.empProcVec f n ω) := by
  refine Measurable.sub ?_ measurable_const
  exact (Finset.measurable_sum _ fun i _ => hf.comp (S.meas i)).const_smul _

end IIDSample

/-- **Second-moment bound for the vector empirical process** (variance identity at
the empirical scale).  For `f ∈ L²(P)`,

    ∫⁻ ‖Gₙ(f)‖² dμ ≤ ENNReal.ofReal (∫ ‖f‖² dP),

uniformly in `n`.  No CLT, no chaining: the `√n` scaling exactly cancels the i.i.d.
variance growth.  Proved coordinate-wise via Parseval + the scalar bound. -/
theorem empProcVec_sq_lintegral_le [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    [MeasurableSpace E] [BorelSpace E]
    (S : IIDSample Ω X μ P) (f : X → E) (hf_meas : Measurable f)
    (hf_L2 : MemLp f 2 P) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖S.empProcVec f n ω‖ ^ 2) ∂μ
      ≤ ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂P) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: the process is `0`.
    subst hn
    have h0 : ∀ ω, S.empProcVec f 0 ω = 0 := fun ω => by simp [IIDSample.empProcVec]
    simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      ENNReal.ofReal_zero, lintegral_zero]
    exact zero_le _
  -- `n ≥ 1`.
  have hf_int : Integrable f P := hf_L2.integrable (by norm_num)
  set b := stdOrthonormalBasis ℝ E with hb
  -- coordinate functions `g j x = ⟪b j, f x⟫`
  set g : _ → X → ℝ := fun j x => inner ℝ (b j) (f x) with hg
  have hg_meas : ∀ j, Measurable (g j) := fun j =>
    ((innerSL ℝ (b j)).continuous.measurable).comp hf_meas
  have hbnorm : ∀ j, ‖b j‖ = 1 := fun j => b.orthonormal.norm_eq_one j
  -- each coordinate function is in `L²(P)`
  have hg_L2 : ∀ j, MemLp (g j) 2 P := by
    intro j
    refine hf_L2.mono (hg_meas j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    calc ‖g j x‖ ≤ ‖b j‖ * ‖f x‖ := norm_inner_le_norm _ _
      _ = ‖f x‖ := by rw [hbnorm j, one_mul]
  -- `(eLpNorm (g j) 2 P)² = ∫ (g j)² dP`
  have hsq_eLpNorm : ∀ j, (eLpNorm (g j) 2 P).toReal ^ 2 = ∫ x, (g j x) ^ 2 ∂P := by
    intro j
    have hpow := (hg_L2 j).eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    rw [hpow]
    simp only [ENNReal.toReal_ofNat]
    have hroot_nonneg : 0 ≤ (∫ a, ‖g j a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ :=
      Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
    rw [ENNReal.toReal_ofReal hroot_nonneg]
    have hint_eq : (∫ a, ‖g j a‖ ^ (2 : ℝ) ∂P) = ∫ x, (g j x) ^ 2 ∂P := by
      congr with x; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [hint_eq, ← Real.rpow_natCast ((∫ x, (g j x) ^ 2 ∂P) ^ (2 : ℝ)⁻¹) 2,
      ← Real.rpow_mul (integral_nonneg fun z => sq_nonneg _),
      show ((2 : ℝ)⁻¹ * (2 : ℕ)) = 1 by norm_num, Real.rpow_one]
  -- coordinate second-moment bound from the scalar variance primitive
  have hcomp : ∀ j,
      ∫⁻ ω, ENNReal.ofReal (inner ℝ (b j) (S.empProcVec f n ω) ^ 2) ∂μ
        ≤ ENNReal.ofReal ((eLpNorm (g j) 2 P).toReal ^ 2) := by
    intro j
    have hrw : (fun ω => ENNReal.ofReal (inner ℝ (b j) (S.empProcVec f n ω) ^ 2))
        = (fun ω => ENNReal.ofReal (((Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
            ∑ i ∈ Finset.range n, (g j (S.Z i ω) - ∫ x, g j x ∂P)) ^ 2)) := by
      funext ω
      rw [IIDSample.inner_empProcVec S f hf_int (b j) hn ω]
      simp only [Finset.card_range]
      rfl
    rw [hrw]
    have hbound := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
      (μ := μ) (P := P) (s := Finset.range n)
      (by simpa [Finset.card_range] using hn) (W := S.Z) (fun i _ => S.meas i)
      (m_A := ⊥) (hm_A_le := bot_le)
      (hW_indep_A := ProbabilityTheory.indep_bot_left _)
      (hW_iid_pi := S.iid_pi_law n)
      (g := fun _ x => g j x)
      (hg_uncurry_meas := (hg_meas j).comp measurable_snd)
      (hg_memLp := fun _ => hg_L2 j)
    refine hbound.trans ?_
    rw [lintegral_const]
    simp
  -- measurability of each coordinate integrand in `ω`
  have hmeas_int : ∀ j,
      Measurable (fun ω => ENNReal.ofReal (inner ℝ (b j) (S.empProcVec f n ω) ^ 2)) := by
    intro j
    have hproc : Measurable (fun ω => S.empProcVec f n ω) :=
      S.measurable_empProcVec f hf_meas n
    exact (((innerSL ℝ (b j)).continuous.measurable.comp hproc).pow_const 2).ennreal_ofReal
  -- assembly: Parseval coordinate-wise, then sum the bounds
  calc ∫⁻ ω, ENNReal.ofReal (‖S.empProcVec f n ω‖ ^ 2) ∂μ
      = ∫⁻ ω, ∑ j, ENNReal.ofReal (inner ℝ (b j) (S.empProcVec f n ω) ^ 2) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [← b.sum_sq_inner_right (S.empProcVec f n ω),
          ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
    _ = ∑ j, ∫⁻ ω, ENNReal.ofReal (inner ℝ (b j) (S.empProcVec f n ω) ^ 2) ∂μ :=
        lintegral_finset_sum _ fun j _ => hmeas_int j
    _ ≤ ∑ j, ENNReal.ofReal ((eLpNorm (g j) 2 P).toReal ^ 2) :=
        Finset.sum_le_sum fun j _ => hcomp j
    _ = ENNReal.ofReal (∑ j, (eLpNorm (g j) 2 P).toReal ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _).symm
    _ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂P) := by
        congr 1
        simp_rw [hsq_eLpNorm]
        rw [← integral_finset_sum]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact b.sum_sq_inner_right (f x)
        · intro j _
          have : (fun x => (g j x) ^ 2) = (fun x => ‖g j x‖ ^ 2) := by
            funext x; rw [Real.norm_eq_abs, sq_abs]
          rw [this]
          exact (hg_L2 j).integrable_norm_rpow (by norm_num) (by norm_num) |>.congr
            (Filter.Eventually.of_forall fun x => by simp)

/-- **Chebyshev bound for the vector empirical process.**  Combining the
second-moment bound with Markov's inequality:

    μ {‖Gₙ(f)‖ > ε} ≤ (∫ ‖f‖² dP) / ε²,

uniformly in `n`.  This is the uniform-in-`n` modulus that drives asymptotic
equicontinuity: as the `L²(P)` size of `f` shrinks, the tail probability shrinks
at a rate independent of the sample size. -/
theorem empProcVec_chebyshev [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    [MeasurableSpace E] [BorelSpace E]
    (S : IIDSample Ω X μ P) (f : X → E) (hf_meas : Measurable f)
    (hf_L2 : MemLp f 2 P) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε < ‖S.empProcVec f n ω‖}
      ≤ ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂P) / ENNReal.ofReal (ε ^ 2) := by
  have hεsq : (0 : ℝ) < ε ^ 2 := by positivity
  have hne0 : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith
  have hnetop : ENNReal.ofReal (ε ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have haemeas : AEMeasurable
      (fun ω => ENNReal.ofReal (‖S.empProcVec f n ω‖ ^ 2)) μ :=
    (((S.measurable_empProcVec f hf_meas n).norm.pow_const 2).ennreal_ofReal).aemeasurable
  have hsub : {ω | ε < ‖S.empProcVec f n ω‖}
      ⊆ {ω | ENNReal.ofReal (ε ^ 2)
          ≤ ENNReal.ofReal (‖S.empProcVec f n ω‖ ^ 2)} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    have hω' : ε < ‖S.empProcVec f n ω‖ := hω
    exact pow_le_pow_left₀ hε.le hω'.le 2
  calc μ {ω | ε < ‖S.empProcVec f n ω‖}
      ≤ μ {ω | ENNReal.ofReal (ε ^ 2)
          ≤ ENNReal.ofReal (‖S.empProcVec f n ω‖ ^ 2)} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (‖S.empProcVec f n ω‖ ^ 2) ∂μ) / ENNReal.ofReal (ε ^ 2) :=
        meas_ge_le_lintegral_div haemeas hne0 hnetop
    _ ≤ ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂P) / ENNReal.ofReal (ε ^ 2) := by
        gcongr
        exact empProcVec_sq_lintegral_le S f hf_meas hf_L2 n

end Causalean.Stat
