/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The bounded local-dependence central limit theorem

Assembling the Stein machinery: for a sequence of triangular arrays `Xₙ : ιₙ → Ωₙ → ℝ` that are
mean-zero with `Var(∑ Xₙ) = 1`, equipped with dependency neighborhoods, and whose two Stein
error terms vanish (`Var(∑ XᵢTᵢ) → 0` and `∑ E[|Xᵢ|Tᵢ²] → 0`), the standardized sum
`Wₙ = ∑ Xₙ` converges in distribution to a standard normal — concretely, the CDF converges,
`P[Wₙ ≤ s] → Φ(s)` for every `s`.

Route: the local-dependence Stein bound (`stein_local_dependence_bound`) applied to the test
functions `cos(t·)`, `sin(t·)` (so `L = |t|`) gives characteristic-function convergence
`charFun(law Wₙ)(t) → e^{−t²/2}`; the `clt` package's Lévy continuity theorem upgrades this to
weak convergence of the laws to the standard Gaussian; and the portmanteau theorem (the Gaussian
CDF has no atoms) yields pointwise CDF convergence.
-/

import Causalean.Mathlib.Probability.SteinMethod.DependencyCLT
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Clt.CLT

/-!
# Local-dependence central limit theorem via Stein bounds

This file converts the local-dependence Stein estimate into CDF convergence to
the standard normal law. It proves the reusable implication
`cdf_tendsto_of_charFun_tendsto` from pointwise characteristic-function
convergence to pointwise Gaussian CDF convergence, then applies the Stein bound
to cosine and sine test functions in the bounded local-dependence central limit
theorem `stein_cdf_clt`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

namespace Causalean
namespace SteinMethod

/-- **CDF convergence from characteristic-function convergence (to the standard Gaussian).**
A reusable corollary of Lévy continuity (`clt` package) + the portmanteau theorem: if the
characteristic functions of a sequence of probability measures converge pointwise to that of the
standard normal, then their CDFs converge pointwise (the Gaussian law is atomless). -/
theorem cdf_tendsto_of_charFun_tendsto (lawn : ℕ → ProbabilityMeasure ℝ)
    (hchar : ∀ t : ℝ, Tendsto (fun n => charFun (lawn n : Measure ℝ) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)))
    (s : ℝ) :
    Tendsto (fun n => (lawn n : Measure ℝ).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  -- Package the standard Gaussian as a `ProbabilityMeasure`.
  set ν₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩ with hν₀
  -- Lévy continuity (`clt` package): char-function convergence ⇒ weak convergence.
  have hweak : Tendsto lawn atTop (𝓝 ν₀) := by
    rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have : (ν₀ : Measure ℝ) = gaussianReal 0 1 := rfl
    simpa [this] using hchar t
  -- The Gaussian is atomless, so the frontier of `Iic s` is null.
  haveI hatoms : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  have hnull : (ν₀ : Measure ℝ) (frontier (Set.Iic s)) = 0 := by
    have hcoe : (ν₀ : Measure ℝ) = gaussianReal 0 1 := rfl
    rw [hcoe, frontier_Iic]
    exact measure_singleton s
  -- Portmanteau: weak convergence ⇒ measure convergence on null-frontier sets.
  have hmeas := MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μ := ν₀) (μs := lawn) hweak (E := Set.Iic s) hnull
  -- Pass to real-valued measures.
  have hfin : ∀ n, (lawn n : Measure ℝ) (Set.Iic s) ≠ ⊤ := fun n => measure_ne_top _ _
  refine (ENNReal.tendsto_toReal ?_).comp hmeas
  exact measure_ne_top _ _

/-- A bounded real function of a measurable map is integrable on a probability measure. -/
private theorem integrable_bdd_real {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (g : Ω → ℝ) (hg : Measurable g) {c : ℝ} (hc : ∀ ω, |g ω| ≤ c) :
    Integrable g ν :=
  (MemLp.of_bound hg.aestronglyMeasurable c
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hc ω))).integrable le_rfl

/-- **Characteristic function of a pushforward law in cos/sin form.**  For a measurable real
`W` on a probability space, `charFun (ν.map W) t` decomposes into its real and imaginary parts
`∫ cos(t·W) ∂ν` and `∫ sin(t·W) ∂ν`. -/
private theorem charFun_map_eq_cos_sin {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (W : Ω → ℝ) (hW : Measurable W) (t : ℝ) :
    charFun (ν.map W) t
      = (↑(∫ ω, Real.cos (t * W ω) ∂ν) : ℂ) + (↑(∫ ω, Real.sin (t * W ω) ∂ν) : ℂ) * Complex.I := by
  -- Move the integral back to `ν` via `integral_map`.
  have hg : AEStronglyMeasurable (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)) (ν.map W) :=
    (Complex.measurable_exp.comp
      ((measurable_const.mul Complex.measurable_ofReal).mul measurable_const)).aestronglyMeasurable
  rw [charFun_apply_real, integral_map hW.aemeasurable hg]
  -- Integrability of the real/imaginary integrands.
  have hcosint : Integrable (fun ω => (↑(Real.cos (t * W ω)) : ℂ)) ν :=
    (integrable_bdd_real (fun ω => Real.cos (t * W ω))
      (Real.measurable_cos.comp (measurable_const.mul hW))
      (fun ω => Real.abs_cos_le_one _)).ofReal
  have hsinint : Integrable (fun ω => (↑(Real.sin (t * W ω)) : ℂ) * Complex.I) ν :=
    ((integrable_bdd_real (fun ω => Real.sin (t * W ω))
      (Real.measurable_sin.comp (measurable_const.mul hW))
      (fun ω => Real.abs_sin_le_one _)).ofReal).mul_const Complex.I
  -- Rewrite the complex exponential pointwise and split.
  have hpt : ∀ ω, Complex.exp (↑t * ↑(W ω) * Complex.I)
      = ↑(Real.cos (t * W ω)) + ↑(Real.sin (t * W ω)) * Complex.I := by
    intro ω
    rw [show (↑t * ↑(W ω) : ℂ) = ↑(t * W ω) by push_cast; ring, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  simp_rw [hpt]
  rw [integral_add hcosint hsinint]
  congr 1
  · exact integral_complex_ofReal
  · have hmc := integral_mul_const (μ := ν) Complex.I (fun ω => (↑(Real.sin (t * W ω)) : ℂ))
    refine hmc.trans ?_
    congr 1
    exact integral_complex_ofReal

/-- **Expectation convergence for a fixed Stein test function.**  Under the local-dependence CLT
hypotheses, for any bounded `C¹` test function `h` (`|h| ≤ C`, `|h'| ≤ L`) the expectations
`E[h(Wₙ)]` converge to the Gaussian expectation `E[h(Z)]`, because both Stein error terms vanish. -/
private theorem stein_expect_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (N : ∀ n, ι n → Finset (ι n))
    (hmeas : ∀ n i, Measurable (X n i))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hbound : ∀ n i ω, |X n i ω| ≤ B n)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (hself : ∀ n i, i ∈ N n i)
    (hindep : ∀ n i, IndepFun (X n i) (fun ω => ∑ j ∈ Finset.univ \ N n i, X n j ω) (μ n))
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (herr1 : Tendsto
      (fun n => variance (fun ω => ∑ i, X n i ω * nbhdSum (X n) (N n) i ω) (μ n)) atTop (𝓝 0))
    (herr2 : Tendsto
      (fun n => ∑ i, ∫ ω, |X n i ω| * (nbhdSum (X n) (N n) i ω) ^ 2 ∂(μ n)) atTop (𝓝 0))
    (h : ℝ → ℝ) (hh : Continuous h) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h) :
    Tendsto (fun n => ∫ ω, h (depSum (X n) ω) ∂(μ n)) atTop (𝓝 (gExpect h)) := by
  -- The Stein bound: `|E[h(Wₙ)] − E[h(Z)]| ≤ err₁(n) + err₂(n)` with both errors → 0.
  set lhs : ℕ → ℝ := fun n => ∫ ω, h (depSum (X n) ω) ∂(μ n) with hlhs
  set rhs : ℕ → ℝ := fun n => 2 * L *
      Real.sqrt (variance (fun ω => ∑ i, X n i ω * nbhdSum (X n) (N n) i ω) (μ n))
      + L * ∑ i, ∫ ω, |X n i ω| * (nbhdSum (X n) (N n) i ω) ^ 2 ∂(μ n) with hrhs
  have hbound_n : ∀ n, |lhs n - gExpect h| ≤ rhs n := fun n =>
    stein_local_dependence_bound (X n) (N n) (hmeas n) (hB n) (hbound n) (hmean n)
      (hself n) (hindep n) (hvar n) h hh hC hL hb hd hdiff
  -- The error sequence converges to `0`.
  have hrhs0 : Tendsto rhs atTop (𝓝 0) := by
    have ht1 : Tendsto (fun n => 2 * L *
        Real.sqrt (variance (fun ω => ∑ i, X n i ω * nbhdSum (X n) (N n) i ω) (μ n)))
        atTop (𝓝 0) := by
      have hsqrt : Tendsto
          (fun n => Real.sqrt (variance (fun ω => ∑ i, X n i ω * nbhdSum (X n) (N n) i ω) (μ n)))
          atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp herr1
        simpa [Real.sqrt_zero] using this
      simpa using hsqrt.const_mul (2 * L)
    have ht2 : Tendsto (fun n => L * ∑ i, ∫ ω, |X n i ω| * (nbhdSum (X n) (N n) i ω) ^ 2 ∂(μ n))
        atTop (𝓝 0) := by simpa using herr2.const_mul L
    simpa [hrhs] using ht1.add ht2
  -- Squeeze: `|lhs n − gExpect h| ≤ rhs n → 0` forces `lhs n → gExpect h`.
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun n => ?_) hrhs0
  rw [Real.norm_eq_abs]; exact hbound_n n

/-- **The bounded local-dependence CLT (CDF form).** -/
theorem stein_cdf_clt
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (N : ∀ n, ι n → Finset (ι n))
    (hmeas : ∀ n i, Measurable (X n i))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hbound : ∀ n i ω, |X n i ω| ≤ B n)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (hself : ∀ n i, i ∈ N n i)
    (hindep : ∀ n i, IndepFun (X n i) (fun ω => ∑ j ∈ Finset.univ \ N n i, X n j ω) (μ n))
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (herr1 : Tendsto
      (fun n => variance (fun ω => ∑ i, X n i ω * nbhdSum (X n) (N n) i ω) (μ n)) atTop (𝓝 0))
    (herr2 : Tendsto
      (fun n => ∑ i, ∫ ω, |X n i ω| * (nbhdSum (X n) (N n) i ω) ^ 2 ∂(μ n)) atTop (𝓝 0))
    (s : ℝ) :
    Tendsto (fun n => ((μ n).map (depSum (X n))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  -- `W n` is the standardized sum; it is measurable (finite sum of measurable maps).
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n => by
    unfold depSum; exact Finset.measurable_sum _ (fun i _ => hmeas n i)
  -- The law of `W n` is a probability measure.
  haveI : ∀ n, IsProbabilityMeasure ((μ n).map (depSum (X n))) := fun n =>
    Measure.isProbabilityMeasure_map (hWmeas n).aemeasurable
  -- Package the laws.
  set lawn : ℕ → ProbabilityMeasure ℝ :=
    fun n => ⟨(μ n).map (depSum (X n)), inferInstance⟩ with hlawn
  -- Reduce to characteristic-function convergence via Theorem 1.
  have hcoe : ∀ n, (lawn n : Measure ℝ) = (μ n).map (depSum (X n)) := fun n => rfl
  refine cdf_tendsto_of_charFun_tendsto lawn ?_ s
  intro t
  -- Test functions `cos(t·)` and `sin(t·)`: both bounded by `1` with derivative bounded by `|t|`.
  have hcos_cont : Continuous (fun x => Real.cos (t * x)) := by fun_prop
  have hcos_diff : Differentiable ℝ (fun x => Real.cos (t * x)) := by fun_prop
  have hcos_b : ∀ x, |Real.cos (t * x)| ≤ 1 := fun x => Real.abs_cos_le_one _
  have hcos_d : ∀ x, |deriv (fun x => Real.cos (t * x)) x| ≤ |t| := by
    intro x
    have hderiv : deriv (fun x => Real.cos (t * x)) x = -(t * Real.sin (t * x)) := by
      have h := (Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t)
      simpa [mul_comm] using h.deriv
    rw [hderiv, abs_neg, abs_mul]
    calc |t| * |Real.sin (t * x)| ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |t| := mul_one _
  have hsin_cont : Continuous (fun x => Real.sin (t * x)) := by fun_prop
  have hsin_diff : Differentiable ℝ (fun x => Real.sin (t * x)) := by fun_prop
  have hsin_b : ∀ x, |Real.sin (t * x)| ≤ 1 := fun x => Real.abs_sin_le_one _
  have hsin_d : ∀ x, |deriv (fun x => Real.sin (t * x)) x| ≤ |t| := by
    intro x
    have hderiv : deriv (fun x => Real.sin (t * x)) x = t * Real.cos (t * x) := by
      have h := (Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t)
      simpa [mul_comm] using h.deriv
    rw [hderiv, abs_mul]
    calc |t| * |Real.cos (t * x)| ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |t| := mul_one _
  -- Stein convergence of the cos- and sin-expectations to the Gaussian expectations.
  have hcos_tendsto :
      Tendsto (fun n => ∫ ω, Real.cos (t * depSum (X n) ω) ∂(μ n)) atTop
        (𝓝 (gExpect (fun x => Real.cos (t * x)))) :=
    stein_expect_tendsto μ X N hmeas B hB hbound hmean hself hindep hvar herr1 herr2
      (fun x => Real.cos (t * x)) hcos_cont zero_le_one (abs_nonneg t) hcos_b hcos_d hcos_diff
  have hsin_tendsto :
      Tendsto (fun n => ∫ ω, Real.sin (t * depSum (X n) ω) ∂(μ n)) atTop
        (𝓝 (gExpect (fun x => Real.sin (t * x)))) :=
    stein_expect_tendsto μ X N hmeas B hB hbound hmean hself hindep hvar herr1 herr2
      (fun x => Real.sin (t * x)) hsin_cont zero_le_one (abs_nonneg t) hsin_b hsin_d hsin_diff
  -- Decompose `charFun` of the limit Gaussian into the cos/sin Gaussian expectations.
  have hgauss : charFun (gaussianReal 0 1) t
      = (↑(gExpect (fun x => Real.cos (t * x))) : ℂ)
        + (↑(gExpect (fun x => Real.sin (t * x))) : ℂ) * Complex.I := by
    have hmap : (gaussianReal 0 1).map id = gaussianReal 0 1 := Measure.map_id
    have := charFun_map_eq_cos_sin (gaussianReal 0 1) id measurable_id t
    rw [hmap] at this
    simpa [gExpect, Function.comp] using this
  -- Decompose `charFun` of each law `lawn n` into the cos/sin sample expectations.
  have hlaw : ∀ n, charFun (lawn n : Measure ℝ) t
      = (↑(∫ ω, Real.cos (t * depSum (X n) ω) ∂(μ n)) : ℂ)
        + (↑(∫ ω, Real.sin (t * depSum (X n) ω) ∂(μ n)) : ℂ) * Complex.I := by
    intro n
    rw [hcoe n]
    exact charFun_map_eq_cos_sin (μ n) (depSum (X n)) (hWmeas n) t
  -- Combine: real and imaginary parts converge, hence the complex char-functions converge.
  rw [hgauss]
  simp_rw [hlaw]
  refine Tendsto.add ?_ (Tendsto.mul_const Complex.I ?_)
  · exact (Complex.continuous_ofReal.tendsto _).comp hcos_tendsto
  · exact (Complex.continuous_ofReal.tendsto _).comp hsin_tendsto

end SteinMethod
end Causalean
