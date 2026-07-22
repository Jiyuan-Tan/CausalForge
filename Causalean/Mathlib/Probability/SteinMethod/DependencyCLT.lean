/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The local-dependence Stein bound (Chen–Goldstein–Shao / Ross)

For a finite family `X : ι → Ω → ℝ` of mean-zero random variables with `Var(∑ Xᵢ) = 1` and
*dependency neighborhoods* `N i` (each `Xᵢ` independent of `∑_{j∉Nᵢ} Xⱼ`), the standardized sum
`W = ∑ Xᵢ` satisfies, for a `C²`-ish test function `h` with `‖h'‖ ≤ L`,

    |E[h(W)] − E[h(Z)]| ≤ 2L·√(Var(∑ᵢ Xᵢ·Tᵢ)) + L·∑ᵢ E[|Xᵢ|·Tᵢ²],   Tᵢ = ∑_{j∈Nᵢ} Xⱼ,

via the Stein equation `E[h(W)] − E[h(Z)] = E[f'(W) − W·f(W)]` (`f = steinSol h`), the
independence (which kills `E[Xᵢ·f(W−Tᵢ)] = 0`), a covariance/Cauchy–Schwarz bound for the
first term (using `‖f'‖ ≤ 2L` and `E[∑ᵢXᵢTᵢ] = Var W = 1`), and a second-order Taylor bound for
the second term (using that `f'` is `2L`-Lipschitz).
-/

import Causalean.Mathlib.Probability.SteinMethod.Bounds
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local-dependence Stein bound

This file defines the standardized sum `depSum`, the neighborhood sum
`nbhdSum`, and proves the Chen-Goldstein-Shao/Ross style
`stein_local_dependence_bound` for a finite family of mean-zero random
variables with dependency neighborhoods. The bound controls the difference
between expectations under the standardized sum and the standard normal by two
local-dependence error terms.
-/

open MeasureTheory ProbabilityTheory
open scoped Real ENNReal

namespace Causalean
namespace SteinMethod

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standardized sum `W = ∑ᵢ Xᵢ`. -/
noncomputable def depSum (X : ι → Ω → ℝ) : Ω → ℝ := fun ω => ∑ i, X i ω

/-- The neighborhood sum `Tᵢ = ∑_{j∈Nᵢ} Xⱼ`. -/
noncomputable def nbhdSum (X : ι → Ω → ℝ) (N : ι → Finset ι) (i : ι) : Ω → ℝ :=
  fun ω => ∑ j ∈ N i, X j ω

/-- **Cauchy–Schwarz for real integrals.**  For `L²` functions `f, g`,
`|∫ f·g| ≤ √(∫ f²)·√(∫ g²)`. -/
private theorem abs_integral_mul_le_sqrt {μ : Measure Ω} (f g : Ω → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ| ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have hf2 : MemLp f (ENNReal.ofReal 2) μ := by rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  have hg2 : MemLp g (ENNReal.ofReal 2) μ := by rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  have hkey := integral_mul_norm_le_Lp_mul_Lq (μ := μ) hpq hf2 hg2
  -- Translate norms/powers to abs/squares, and the `rpow (1/2)` to `sqrt`.
  have heq1 : ∀ ω, ‖f ω‖ * ‖g ω‖ = |f ω * g ω| := by
    intro ω; rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  have hsqrt : ∀ (c : ℝ), c ^ (1 / (2:ℝ)) = Real.sqrt c := by
    intro c; rw [Real.sqrt_eq_rpow]
  have hnormsq : ∀ ω, ‖f ω‖ ^ (2:ℝ) = f ω ^ 2 := by
    intro ω; rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hnormsqg : ∀ ω, ‖g ω‖ ^ (2:ℝ) = g ω ^ 2 := by
    intro ω; rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  calc |∫ ω, f ω * g ω ∂μ|
      ≤ ∫ ω, |f ω * g ω| ∂μ := abs_integral_le_integral_abs
    _ = ∫ ω, ‖f ω‖ * ‖g ω‖ ∂μ := by simp_rw [heq1]
    _ ≤ (∫ ω, ‖f ω‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) * (∫ ω, ‖g ω‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := hkey
    _ = Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
        rw [hsqrt, hsqrt]; simp_rw [hnormsq, hnormsqg]

/-- The derivative of the Stein solution is continuous (it is `2L`-Lipschitz). -/
private theorem steinSol_deriv_continuous (h : ℝ → ℝ) (hh : Continuous h) {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L)
    (hdiff : Differentiable ℝ h) : Continuous (deriv (steinSol h)) := by
  have hlip : LipschitzWith (2 * L).toNNReal (deriv (steinSol h)) := by
    refine LipschitzWith.of_dist_le_mul (fun u v => ?_)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact steinSol_deriv_lipschitz h hh hC hL hb hd hdiff u v
  exact hlip.continuous

/-- **Second-order Taylor bound for the Stein solution.**  Because `deriv (steinSol h)` is
`2L`-Lipschitz (`steinSol_deriv_lipschitz`), the first-order remainder of `steinSol h` at the
*right* endpoint is controlled quadratically:
`|f(a+t) − f(a) − t·f'(a+t)| ≤ L·t²`. -/
private theorem steinSol_taylor_right (h : ℝ → ℝ) (hh : Continuous h) {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L)
    (hdiff : Differentiable ℝ h) (a t : ℝ) :
    |steinSol h (a + t) - steinSol h a - t * deriv (steinSol h) (a + t)| ≤ L * t ^ 2 := by
  set f := steinSol h with hf
  set f' := deriv (steinSol h) with hf'
  have hf'cont : Continuous f' := steinSol_deriv_continuous h hh hC hL hb hd hdiff
  -- `s ↦ f (a + s * t)` has derivative `f' (a + s * t) * t`.
  have hg : ∀ s : ℝ, HasDerivAt (fun s => f (a + s * t)) (f' (a + s * t) * t) s := by
    intro s
    have hfderiv : HasDerivAt f (f' (a + s * t)) (a + s * t) := by
      rw [hf, hf']; exact steinSol_hasDerivAt h hh hb (a + s * t) |>.congr_deriv
        (by rw [(steinSol_hasDerivAt h hh hb (a + s * t)).deriv])
    have hinner : HasDerivAt (fun s : ℝ => a + s * t) t s := by
      simpa using ((hasDerivAt_id s).mul_const t).const_add a
    exact hfderiv.comp s hinner
  -- FTC over `[0,1]`: `f (a + t) − f a = ∫₀¹ f' (a + s t) * t ds`.
  have hcont : Continuous (fun s : ℝ => f' (a + s * t) * t) :=
    (hf'cont.comp (by fun_prop)).mul continuous_const
  have hFTC : (∫ s in (0:ℝ)..1, f' (a + s * t) * t) = f (a + t) - f a := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => f (a + s * t)) (f' := fun s => f' (a + s * t) * t)
      (fun s _ => hg s) (hcont.intervalIntegrable 0 1)
    simpa using this
  -- The remainder as an integral: `r = ∫₀¹ t·(f' (a + s t) − f' (a + t)) ds`.
  have hconst : (∫ _s in (0:ℝ)..1, t * deriv (steinSol h) (a + t)) = t * f' (a + t) := by
    rw [intervalIntegral.integral_const]; simp [hf']
  have hrem : steinSol h (a + t) - steinSol h a - t * deriv (steinSol h) (a + t)
      = ∫ s in (0:ℝ)..1, (f' (a + s * t) * t - t * f' (a + t)) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1)]
    rw [hFTC, hconst]
  rw [hrem]
  -- Bound the integrand pointwise by `2L·t²·(1 − s)` on `[0,1]`.
  have hbound_int : |∫ s in (0:ℝ)..1, (f' (a + s * t) * t - t * f' (a + t))|
      ≤ ∫ s in (0:ℝ)..1, 2 * L * t ^ 2 * (1 - s) := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((hcont.sub continuous_const).abs.intervalIntegrable 0 1)
      ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 1)
      (fun s hs => ?_)
    have hs1 : s ≤ 1 := hs.2
    have hlip := steinSol_deriv_lipschitz h hh hC hL hb hd hdiff (a + s * t) (a + t)
    calc |f' (a + s * t) * t - t * f' (a + t)|
        = |t| * |f' (a + s * t) - f' (a + t)| := by rw [← abs_mul]; ring_nf
      _ ≤ |t| * (2 * L * |(a + s * t) - (a + t)|) := by
          apply mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
      _ = 2 * L * t ^ 2 * (1 - s) := by
          have hst : (a + s * t) - (a + t) = (s - 1) * t := by ring
          rw [hst, abs_mul, abs_of_nonpos (by linarith : s - 1 ≤ 0)]
          rw [show |t| * (2 * L * (-(s - 1) * |t|)) = 2 * L * (|t| * |t|) * (1 - s) by ring]
          rw [← abs_mul, abs_mul_self, sq]
  calc |∫ s in (0:ℝ)..1, (f' (a + s * t) * t - t * f' (a + t))|
      ≤ ∫ s in (0:ℝ)..1, 2 * L * t ^ 2 * (1 - s) := hbound_int
    _ = L * t ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
        rw [show (fun s => 1 - s) = (fun s => (1:ℝ) - s) from rfl]
        rw [intervalIntegral.integral_sub (intervalIntegrable_const)
          (intervalIntegral.intervalIntegrable_id)]
        simp; ring

/-- **The local-dependence Stein bound.** -/
theorem stein_local_dependence_bound
    (X : ι → Ω → ℝ) (N : ι → Finset ι)
    (hmeas : ∀ i, Measurable (X i))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |X i ω| ≤ B)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hself : ∀ i, i ∈ N i)
    (hindep : ∀ i, IndepFun (X i) (fun ω => ∑ j ∈ Finset.univ \ N i, X j ω) μ)
    (hvar : ∫ ω, (depSum X ω) ^ 2 ∂μ = 1)
    (h : ℝ → ℝ) (hh : Continuous h) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h) :
    |(∫ ω, h (depSum X ω) ∂μ) - gExpect h|
      ≤ 2 * L * Real.sqrt (variance (fun ω => ∑ i, X i ω * nbhdSum X N i ω) μ)
        + L * ∑ i, ∫ ω, |X i ω| * (nbhdSum X N i ω) ^ 2 ∂μ := by
  classical
  -- Abbreviations.
  set W : Ω → ℝ := depSum X with hW
  set T : ι → Ω → ℝ := fun i => nbhdSum X N i with hT
  set S : ι → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ \ N i, X j ω with hS
  set f : ℝ → ℝ := steinSol h with hf
  set f' : ℝ → ℝ := deriv (steinSol h) with hf'
  set Y : Ω → ℝ := fun ω => ∑ i, X i ω * T i ω with hY
  -- Continuity / measurability of the Stein solution and its derivative.
  have hfdiff : Differentiable ℝ f := fun w => (steinSol_hasDerivAt h hh hb w).differentiableAt
  have hfcont : Continuous f := hfdiff.continuous
  have hf'cont : Continuous f' := steinSol_deriv_continuous h hh hC hL hb hd hdiff
  have hfbd : ∀ w, |f w| ≤ 2 * L := fun w => steinSol_abs_le h hh hC hL hb hd hdiff w
  have hf'bd : ∀ w, |f' w| ≤ 2 * L := fun w => steinSol_deriv_abs_le h hh hC hL hb hd hdiff w
  -- Measurability of the random variables.
  have hWmeas : Measurable W := by
    simp only [hW]; exact Finset.measurable_sum _ (fun i _ => hmeas i)
  have hTmeas : ∀ i, Measurable (T i) := by
    intro i; simp only [hT]; exact Finset.measurable_sum _ (fun j _ => hmeas j)
  have hSmeas : ∀ i, Measurable (S i) := by
    intro i; rw [hS]; exact Finset.measurable_sum _ (fun j _ => hmeas j)
  have hYmeas : Measurable Y := by
    rw [hY]; exact Finset.measurable_sum _ (fun i _ => (hmeas i).mul (hTmeas i))
  -- Boundedness of the sums (by `card · B`).
  have hWbd : ∀ ω, |W ω| ≤ (Fintype.card ι : ℝ) * B := by
    intro ω; simp only [hW, depSum]
    calc |∑ i, X i ω| ≤ ∑ _i : ι, B := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            exact Finset.sum_le_sum (fun i _ => hbound i ω)
      _ = (Fintype.card ι : ℝ) * B := by rw [Finset.sum_const]; simp [mul_comm]
  have hTbd : ∀ i ω, |T i ω| ≤ (Fintype.card ι : ℝ) * B := by
    intro i ω; simp only [hT, nbhdSum]
    calc |∑ j ∈ N i, X j ω| ≤ ∑ _j ∈ N i, B := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            exact Finset.sum_le_sum (fun j _ => hbound j ω)
      _ = ((N i).card : ℝ) * B := by rw [Finset.sum_const]; simp [mul_comm]
      _ ≤ (Fintype.card ι : ℝ) * B := by
            apply mul_le_mul_of_nonneg_right _ hB
            exact_mod_cast Finset.card_le_univ (N i)
  have hSbd : ∀ i ω, |S i ω| ≤ (Fintype.card ι : ℝ) * B := by
    intro i ω; rw [hS]
    calc |∑ j ∈ Finset.univ \ N i, X j ω| ≤ ∑ _j ∈ Finset.univ \ N i, B := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            exact Finset.sum_le_sum (fun j _ => hbound j ω)
      _ = ((Finset.univ \ N i).card : ℝ) * B := by rw [Finset.sum_const]; simp [mul_comm]
      _ ≤ (Fintype.card ι : ℝ) * B := by
            apply mul_le_mul_of_nonneg_right _ hB
            exact_mod_cast Finset.card_le_univ (Finset.univ \ N i)
  -- A helper: a bounded measurable real function is integrable on the probability measure.
  have hInt_of_bd : ∀ (g : Ω → ℝ) (_ : Measurable g) (c : ℝ) (_ : ∀ ω, |g ω| ≤ c),
      Integrable g μ := by
    intro g hg c hgc
    have hmemlp : MemLp g 1 μ :=
      MemLp.of_bound hg.aestronglyMeasurable c
        (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgc ω))
    exact hmemlp.integrable le_rfl
  -- Integrability facts used throughout.
  have hXint : ∀ i, Integrable (X i) μ := fun i => hInt_of_bd _ (hmeas i) B (fun ω => hbound i ω)
  have hfWmeas : Measurable (fun ω => f (W ω)) := hfcont.measurable.comp hWmeas
  have hf'Wmeas : Measurable (fun ω => f' (W ω)) := hf'cont.measurable.comp hWmeas
  have hf'Wint : Integrable (fun ω => f' (W ω)) μ :=
    hInt_of_bd _ hf'Wmeas (2 * L) (fun ω => hf'bd (W ω))
  have hWfWint : Integrable (fun ω => W ω * f (W ω)) μ :=
    hInt_of_bd _ (hWmeas.mul hfWmeas) ((Fintype.card ι : ℝ) * B * (2 * L)) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hWbd ω) (hfbd (W ω)) (abs_nonneg _)
        (by positivity))
  have hhWint : Integrable (fun ω => h (W ω)) μ :=
    hInt_of_bd _ (hh.measurable.comp hWmeas) C (fun ω => hb (W ω))
  -- **Step 1.** Stein equation, integrated.
  have hstein_pt : ∀ ω, f' (W ω) - W ω * f (W ω) = h (W ω) - gExpect h := by
    intro ω; rw [hf', hf]; exact steinSol_stein_eq h hh hb (W ω)
  have hStep1 : (∫ ω, h (W ω) ∂μ) - gExpect h
      = (∫ ω, f' (W ω) ∂μ) - ∫ ω, W ω * f (W ω) ∂μ := by
    have hpt : (fun ω => h (W ω) - gExpect h) = (fun ω => f' (W ω) - W ω * f (W ω)) := by
      funext ω; rw [hstein_pt ω]
    have hlhs : (∫ ω, (h (W ω) - gExpect h) ∂μ) = (∫ ω, h (W ω) ∂μ) - gExpect h := by
      rw [integral_sub hhWint (integrable_const _), integral_const]
      simp
    rw [← hlhs, hpt, integral_sub hf'Wint hWfWint]
  -- **Step 2.** `W = T i + S i` (split `univ = N i ⊔ (univ \ N i)`).
  have hWsplit : ∀ i ω, W ω = T i ω + S i ω := by
    intro i ω
    simp only [hW, depSum, hT, nbhdSum, hS]
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ (N i))]
  -- Measurability / boundedness / integrability of `f ∘ S i` and the products.
  have hfSmeas : ∀ i, Measurable (fun ω => f (S i ω)) := fun i => hfcont.measurable.comp (hSmeas i)
  have hfSint : ∀ i, Integrable (fun ω => f (S i ω)) μ := fun i =>
    hInt_of_bd _ (hfSmeas i) (2 * L) (fun ω => hfbd (S i ω))
  have hcardB_nonneg : (0:ℝ) ≤ (Fintype.card ι : ℝ) * B := by positivity
  have hXfWint : ∀ i, Integrable (fun ω => X i ω * f (W ω)) μ := fun i =>
    hInt_of_bd _ ((hmeas i).mul hfWmeas) (B * (2 * L)) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hbound i ω) (hfbd (W ω)) (abs_nonneg _) hB)
  have hXfSint : ∀ i, Integrable (fun ω => X i ω * f (S i ω)) μ := fun i =>
    hInt_of_bd _ ((hmeas i).mul (hfSmeas i)) (B * (2 * L)) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hbound i ω) (hfbd (S i ω)) (abs_nonneg _) hB)
  -- **Step 3.** Independence kills `∫ Xᵢ·f(Sᵢ) = 0`.
  have hXfS_zero : ∀ i, ∫ ω, X i ω * f (S i ω) ∂μ = 0 := by
    intro i
    have hindep_comp : IndepFun (X i) (fun ω => f (S i ω)) μ :=
      (hindep i).comp (φ := id) (ψ := f) measurable_id hfcont.measurable
    rw [hindep_comp.integral_fun_mul_eq_mul_integral
        (hmeas i).aestronglyMeasurable (hfSmeas i).aestronglyMeasurable]
    rw [hmean i, zero_mul]
  -- **Step 4 (a).** `∫ W·f(W) = ∑ᵢ ∫ Xᵢ·f(W)`.
  have hIWf_sum : (∫ ω, W ω * f (W ω) ∂μ) = ∑ i, ∫ ω, X i ω * f (W ω) ∂μ := by
    have hpt : (fun ω => W ω * f (W ω)) = (fun ω => ∑ i, X i ω * f (W ω)) := by
      funext ω; rw [← Finset.sum_mul]
      simp only [hW, depSum]
    rw [hpt, integral_finset_sum _ (fun i _ => hXfWint i)]
  -- Each `∫ Xᵢ·f(W) = ∫ Xᵢ·(f(W) − f(Sᵢ))`.
  have hXfW_sub : ∀ i, (∫ ω, X i ω * f (W ω) ∂μ)
      = ∫ ω, X i ω * (f (W ω) - f (S i ω)) ∂μ := by
    intro i
    have hsplit : (fun ω => X i ω * (f (W ω) - f (S i ω)))
        = (fun ω => X i ω * f (W ω) - X i ω * f (S i ω)) := by funext ω; ring
    rw [hsplit, integral_sub (hXfWint i) (hXfSint i), hXfS_zero i, sub_zero]
  -- The Taylor remainder `R i ω = Tᵢ·f'(W) − (f(W) − f(Sᵢ))`.
  set R : ι → Ω → ℝ := fun i ω => T i ω * f' (W ω) - (f (W ω) - f (S i ω)) with hR
  -- Taylor bound: `|R i ω| ≤ L·(Tᵢ ω)²`.
  have hRbound : ∀ i ω, |R i ω| ≤ L * (T i ω) ^ 2 := by
    intro i ω
    have htaylor := steinSol_taylor_right h hh hC hL hb hd hdiff (S i ω) (T i ω)
    have hWeq : S i ω + T i ω = W ω := by rw [hWsplit i ω]; ring
    rw [hWeq] at htaylor
    change |T i ω * f' (W ω) - (f (W ω) - f (S i ω))| ≤ L * (T i ω) ^ 2
    have heq : T i ω * f' (W ω) - (f (W ω) - f (S i ω))
        = -(f (W ω) - f (S i ω) - T i ω * deriv (steinSol h) (W ω)) := by rw [hf']; ring
    rw [heq, abs_neg]; exact htaylor
  -- Measurability / integrability of `R i`, `Xᵢ·Tᵢ·f'(W)`, `Xᵢ·Rᵢ`.
  have hf'Wcont_meas : Measurable (fun ω => f' (W ω)) := hf'Wmeas
  have hRmeas : ∀ i, Measurable (R i) := by
    intro i; rw [hR]
    exact ((hTmeas i).mul hf'Wmeas).sub (hfWmeas.sub (hfSmeas i))
  have hXTf'int : ∀ i, Integrable (fun ω => X i ω * T i ω * f' (W ω)) μ := by
    intro i
    refine hInt_of_bd _ (((hmeas i).mul (hTmeas i)).mul hf'Wmeas)
      (B * ((Fintype.card ι : ℝ) * B) * (2 * L)) (fun ω => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul (hbound i ω) (hTbd i ω) (abs_nonneg _) hB)
      (hf'bd (W ω)) (abs_nonneg _) (by positivity)
  have hXRint : ∀ i, Integrable (fun ω => X i ω * R i ω) μ := by
    intro i
    refine hInt_of_bd _ ((hmeas i).mul (hRmeas i)) (B * (L * ((Fintype.card ι : ℝ) * B) ^ 2))
      (fun ω => ?_)
    rw [abs_mul]
    refine mul_le_mul (hbound i ω) ((hRbound i ω).trans ?_) (abs_nonneg _) hB
    apply mul_le_mul_of_nonneg_left _ hL
    calc (T i ω) ^ 2 = |T i ω| ^ 2 := (sq_abs _).symm
      _ ≤ ((Fintype.card ι : ℝ) * B) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _) (hTbd i ω)
  -- Decomposition of each summand.
  have hXfW_decomp : ∀ i, (∫ ω, X i ω * f (W ω) ∂μ)
      = (∫ ω, X i ω * T i ω * f' (W ω) ∂μ) - ∫ ω, X i ω * R i ω ∂μ := by
    intro i
    rw [hXfW_sub i]
    have hpt : (fun ω => X i ω * (f (W ω) - f (S i ω)))
        = (fun ω => X i ω * T i ω * f' (W ω) - X i ω * R i ω) := by
      funext ω; rw [hR]; ring
    rw [hpt, integral_sub (hXTf'int i) (hXRint i)]
  -- **Step 4 (c).** `∑ᵢ ∫ Xᵢ·Tᵢ·f'(W) = ∫ f'(W)·Y`.
  have hf'WYint : Integrable (fun ω => f' (W ω) * Y ω) μ := by
    refine hInt_of_bd _ (hf'Wmeas.mul hYmeas)
      (2 * L * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * B * B))) (fun ω => ?_)
    rw [abs_mul]
    refine mul_le_mul (hf'bd (W ω)) ?_ (abs_nonneg _) (by positivity)
    rw [hY]
    calc |∑ i, X i ω * T i ω| ≤ ∑ _i : ι, (Fintype.card ι : ℝ) * B * B := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
          rw [abs_mul, mul_comm ((Fintype.card ι : ℝ) * B) B]
          exact mul_le_mul (hbound i ω) (hTbd i ω) (abs_nonneg _) hB
      _ = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * B * B) := by
          rw [Finset.sum_const]; simp [mul_comm]
  have hsum_XTf' : (∑ i, ∫ ω, X i ω * T i ω * f' (W ω) ∂μ) = ∫ ω, f' (W ω) * Y ω ∂μ := by
    rw [← integral_finset_sum _ (fun i _ => hXTf'int i)]
    congr 1; funext ω
    rw [hY, Finset.mul_sum]
    congr 1; funext i; ring
  -- **Master identity.** `(∫h(W)) − gExpect h = ∫ f'(W)·(1 − Y) + ∑ᵢ ∫ Xᵢ·Rᵢ`.
  have hYint : Integrable Y μ := by
    refine hInt_of_bd _ hYmeas ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * B * B)) (fun ω => ?_)
    rw [hY]
    calc |∑ i, X i ω * T i ω| ≤ ∑ _i : ι, (Fintype.card ι : ℝ) * B * B := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
          rw [abs_mul, mul_comm ((Fintype.card ι : ℝ) * B) B]
          exact mul_le_mul (hbound i ω) (hTbd i ω) (abs_nonneg _) hB
      _ = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * B * B) := by
          rw [Finset.sum_const]; simp [mul_comm]
  have hmaster : (∫ ω, h (W ω) ∂μ) - gExpect h
      = (∫ ω, f' (W ω) * (1 - Y ω) ∂μ) + ∑ i, ∫ ω, X i ω * R i ω ∂μ := by
    rw [hStep1, hIWf_sum]
    have hsumdecomp : (∑ i, ∫ ω, X i ω * f (W ω) ∂μ)
        = (∑ i, ∫ ω, X i ω * T i ω * f' (W ω) ∂μ) - ∑ i, ∫ ω, X i ω * R i ω ∂μ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hXfW_decomp i)
    rw [hsumdecomp, hsum_XTf']
    have h1mY : (∫ ω, f' (W ω) * (1 - Y ω) ∂μ)
        = (∫ ω, f' (W ω) ∂μ) - ∫ ω, f' (W ω) * Y ω ∂μ := by
      have hpt : (fun ω => f' (W ω) * (1 - Y ω)) = (fun ω => f' (W ω) - f' (W ω) * Y ω) := by
        funext ω; ring
      rw [hpt, integral_sub hf'Wint hf'WYint]
    rw [h1mY]; ring
  -- **Step 5 (a).** `∫ Y = ∫ W² = 1`.
  have hXSint : ∀ i, Integrable (fun ω => X i ω * S i ω) μ := fun i =>
    hInt_of_bd _ ((hmeas i).mul (hSmeas i)) (B * ((Fintype.card ι : ℝ) * B)) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hbound i ω) (hSbd i ω) (abs_nonneg _) hB)
  have hXTint : ∀ i, Integrable (fun ω => X i ω * T i ω) μ := fun i =>
    hInt_of_bd _ ((hmeas i).mul (hTmeas i)) (B * ((Fintype.card ι : ℝ) * B)) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hbound i ω) (hTbd i ω) (abs_nonneg _) hB)
  have hXWint : ∀ i, Integrable (fun ω => X i ω * W ω) μ := fun i =>
    hInt_of_bd _ ((hmeas i).mul hWmeas) (B * ((Fintype.card ι : ℝ) * B)) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hbound i ω) (hWbd ω) (abs_nonneg _) hB)
  have hXS_zero : ∀ i, ∫ ω, X i ω * S i ω ∂μ = 0 := by
    intro i
    have hindep_i : IndepFun (X i) (S i) μ := hindep i
    rw [hindep_i.integral_fun_mul_eq_mul_integral (hmeas i).aestronglyMeasurable
        (hSmeas i).aestronglyMeasurable, hmean i, zero_mul]
  have hintY : (∫ ω, Y ω ∂μ) = 1 := by
    have hYeq : (∫ ω, Y ω ∂μ) = ∑ i, ∫ ω, X i ω * T i ω ∂μ := by
      rw [hY, integral_finset_sum _ (fun i _ => hXTint i)]
    have hW2eq : (∫ ω, W ω ^ 2 ∂μ) = ∑ i, ∫ ω, X i ω * W ω ∂μ := by
      have hpt : (fun ω => W ω ^ 2) = (fun ω => ∑ i, X i ω * W ω) := by
        funext ω; rw [← Finset.sum_mul, sq]
        simp only [hW, depSum]
      rw [hpt, integral_finset_sum _ (fun i _ => hXWint i)]
    have hXW_eq : ∀ i, (∫ ω, X i ω * W ω ∂μ) = ∫ ω, X i ω * T i ω ∂μ := by
      intro i
      have hpt : (fun ω => X i ω * W ω) = (fun ω => X i ω * T i ω + X i ω * S i ω) := by
        funext ω; rw [hWsplit i ω]; ring
      rw [hpt, integral_add (hXTint i) (hXSint i), hXS_zero i, add_zero]
    rw [hYeq, ← hvar, hW2eq]
    exact (Finset.sum_congr rfl (fun i _ => (hXW_eq i).symm))
  -- **Step 5 (b).** First term bounded by `2L·√(Var Y)` via Cauchy–Schwarz.
  -- MemLp 2 of the relevant bounded functions.
  have hmemlp_of_bd : ∀ (g : Ω → ℝ) (_ : Measurable g) (c : ℝ) (_ : ∀ ω, |g ω| ≤ c),
      MemLp g 2 μ := by
    intro g hg c hgc
    exact MemLp.of_bound hg.aestronglyMeasurable c
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgc ω))
  have hf'W_memlp : MemLp (fun ω => f' (W ω)) 2 μ :=
    hmemlp_of_bd _ hf'Wmeas (2 * L) (fun ω => hf'bd (W ω))
  have hYc_memlp : MemLp (fun ω => Y ω - ∫ ω, Y ω ∂μ) 2 μ := by
    refine hmemlp_of_bd _ (hYmeas.sub measurable_const)
      ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * B * B) + |∫ ω, Y ω ∂μ|) (fun ω => ?_)
    refine (abs_sub _ _).trans ?_
    gcongr
    rw [hY]
    calc |∑ i, X i ω * T i ω| ≤ ∑ _i : ι, (Fintype.card ι : ℝ) * B * B := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
          rw [abs_mul, mul_comm ((Fintype.card ι : ℝ) * B) B]
          exact mul_le_mul (hbound i ω) (hTbd i ω) (abs_nonneg _) hB
      _ = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * B * B) := by
          rw [Finset.sum_const]; simp [mul_comm]
  -- `∫ (f'(W))² ≤ (2L)²`.
  have hf'Wsq_le : (∫ ω, (f' (W ω)) ^ 2 ∂μ) ≤ (2 * L) ^ 2 := by
    have hbd2 : ∀ ω, (f' (W ω)) ^ 2 ≤ (2 * L) ^ 2 := by
      intro ω
      calc (f' (W ω)) ^ 2 = |f' (W ω)| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * L) ^ 2 := by apply pow_le_pow_left₀ (abs_nonneg _) (hf'bd (W ω))
    calc (∫ ω, (f' (W ω)) ^ 2 ∂μ) ≤ ∫ _ω, (2 * L) ^ 2 ∂μ := by
          refine integral_mono ?_ (integrable_const _) hbd2
          exact hInt_of_bd _ (hf'Wmeas.pow_const 2) ((2 * L) ^ 2) (fun ω => by
            rw [abs_of_nonneg (sq_nonneg _)]; exact hbd2 ω)
      _ = (2 * L) ^ 2 := by rw [integral_const]; simp
  -- Variance of Y.
  have hvarY : variance Y μ = ∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ :=
    variance_eq_integral hYmeas.aemeasurable
  have hvarY_nonneg : 0 ≤ variance Y μ := variance_nonneg Y μ
  -- The Cauchy–Schwarz bound.
  have hfirst : |∫ ω, f' (W ω) * (1 - Y ω) ∂μ| ≤ 2 * L * Real.sqrt (variance Y μ) := by
    have h1mY : (fun ω => f' (W ω) * (1 - Y ω))
        = (fun ω => f' (W ω) * (Y ω - ∫ ω, Y ω ∂μ)) * (-1 : Ω → ℝ) := by
      funext ω; simp only [Pi.mul_apply, Pi.neg_apply, Pi.one_apply]; rw [hintY]; ring
    have hrw : (∫ ω, f' (W ω) * (1 - Y ω) ∂μ)
        = -∫ ω, f' (W ω) * (Y ω - ∫ ω, Y ω ∂μ) ∂μ := by
      rw [← integral_neg]; congr 1; funext ω; rw [hintY]; ring
    rw [hrw, abs_neg]
    calc |∫ ω, f' (W ω) * (Y ω - ∫ ω, Y ω ∂μ) ∂μ|
        ≤ Real.sqrt (∫ ω, (f' (W ω)) ^ 2 ∂μ)
            * Real.sqrt (∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ) :=
          abs_integral_mul_le_sqrt _ _ hf'W_memlp hYc_memlp
      _ ≤ (2 * L) * Real.sqrt (variance Y μ) := by
          rw [hvarY]
          apply mul_le_mul _ le_rfl (Real.sqrt_nonneg _) (by positivity)
          rw [show (2:ℝ) * L = Real.sqrt ((2 * L) ^ 2) by
            rw [Real.sqrt_sq (by positivity)]]
          exact Real.sqrt_le_sqrt hf'Wsq_le
  -- **Step 6.** Second term bounded by `L·∑ᵢ ∫ |Xᵢ|·Tᵢ²` (Taylor remainder).
  have hXTsq_int : ∀ i, Integrable (fun ω => |X i ω| * (T i ω) ^ 2) μ := by
    intro i
    refine hInt_of_bd _ ((hmeas i).abs.mul ((hTmeas i).pow_const 2))
      (B * ((Fintype.card ι : ℝ) * B) ^ 2) (fun ω => ?_)
    rw [abs_mul, abs_abs]
    refine mul_le_mul (hbound i ω) ?_ (abs_nonneg _) hB
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (T i ω) ^ 2 = |T i ω| ^ 2 := (sq_abs _).symm
      _ ≤ ((Fintype.card ι : ℝ) * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hTbd i ω) 2
  have hXR_le : ∀ i, |∫ ω, X i ω * R i ω ∂μ| ≤ L * ∫ ω, |X i ω| * (T i ω) ^ 2 ∂μ := by
    intro i
    calc |∫ ω, X i ω * R i ω ∂μ|
        ≤ ∫ ω, |X i ω * R i ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |X i ω| * (L * (T i ω) ^ 2) ∂μ := by
          refine integral_mono (hXRint i).abs ?_ (fun ω => ?_)
          · exact (hXTsq_int i).const_mul L |>.congr
              (Filter.Eventually.of_forall (fun ω => by ring))
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hRbound i ω) (abs_nonneg _)
      _ = L * ∫ ω, |X i ω| * (T i ω) ^ 2 ∂μ := by
          rw [← integral_const_mul]; congr 1; funext ω; ring
  have hsecond : |∑ i, ∫ ω, X i ω * R i ω ∂μ| ≤ L * ∑ i, ∫ ω, |X i ω| * (T i ω) ^ 2 ∂μ := by
    calc |∑ i, ∫ ω, X i ω * R i ω ∂μ|
        ≤ ∑ i, |∫ ω, X i ω * R i ω ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, L * ∫ ω, |X i ω| * (T i ω) ^ 2 ∂μ := Finset.sum_le_sum (fun i _ => hXR_le i)
      _ = L * ∑ i, ∫ ω, |X i ω| * (T i ω) ^ 2 ∂μ := by rw [Finset.mul_sum]
  -- **Step 7.** Combine via the triangle inequality.
  calc |(∫ ω, h (depSum X ω) ∂μ) - gExpect h|
      = |(∫ ω, f' (W ω) * (1 - Y ω) ∂μ) + ∑ i, ∫ ω, X i ω * R i ω ∂μ| := by
        rw [← hW, hmaster]
    _ ≤ |∫ ω, f' (W ω) * (1 - Y ω) ∂μ| + |∑ i, ∫ ω, X i ω * R i ω ∂μ| := abs_add_le _ _
    _ ≤ 2 * L * Real.sqrt (variance Y μ) + L * ∑ i, ∫ ω, |X i ω| * (T i ω) ^ 2 ∂μ :=
        add_le_add hfirst hsecond

end SteinMethod
end Causalean
