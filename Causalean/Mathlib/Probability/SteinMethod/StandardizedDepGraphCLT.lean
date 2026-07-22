/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Probability.SteinMethod.DepGraphCLT
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- The per-stage `DecidableEq (ι n)` is used in the proof terms (via `depGraph_div_const`) but not
-- in the statement types; the `DepGraph` structure carries its own decidability field.
set_option linter.unusedDecidableInType false

/-!
# Standardized bounded-degree dependency-graph CLT

A standardization wrapper around the abstract Stein dependency-graph CLT
`Causalean.SteinMethod.stein_cdf_clt_of_depGraph`. The engine consumes an array that has *already*
been standardized to unit variance with a summand bound tending to `0` and a Lyapunov limit
`card · Bₙ³ → 0`. Real applications instead arrive with fixed bounded summands `|X| ≤ M`, a raw
second moment `∫ (∑ᵢ Xᵢ)² = vₙ`, and a linear variance floor `c · card ιₙ ≤ vₙ` — so this file
supplies the missing layer: it divides through by `√vₙ`, re-derives unit variance, converts the
summand bound into `Bₙ = (M/√c)/√(card ιₙ)`, discharges `card · Bₙ³ → 0` internally, and adds the
prefix-shift plumbing for the eventual-hypothesis variants. Downstream a user can invoke it on raw
mean-zero bounded summands and get CDF convergence of `(∑ᵢ Xᵢ)/√vₙ` to `N(0,1)` in one step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

namespace Causalean
namespace SteinMethod

/-- Dividing every summand in a dependency graph by the same deterministic constant preserves the
graph and transfers the independence field by measurable post-composition. -/
noncomputable def depGraph_div_const
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ} (D : DepGraph X μ) (s : ℝ) :
    DepGraph (fun i ω => X i ω / s) μ where
  G := D.G
  decG := D.decG
  refl := D.refl
  symm := D.symm
  meas i := (D.meas i).div_const s
  indep A B hAB := by
    have h := D.indep A B hAB
    let φ : (A → ℝ) → (A → ℝ) := fun v k => v k / s
    let ψ : (B → ℝ) → (B → ℝ) := fun v k => v k / s
    have hφ : Measurable φ := by
      exact measurable_pi_lambda φ fun k => by
        have hk : Measurable (fun v : A → ℝ => v k) := measurable_pi_apply k
        simpa [φ] using hk.div_const s
    have hψ : Measurable ψ := by
      exact measurable_pi_lambda ψ fun k => by
        have hk : Measurable (fun v : B → ℝ => v k) := measurable_pi_apply k
        simpa [ψ] using hk.div_const s
    simpa only [φ, ψ, Function.comp] using h.comp hφ hψ

/-- Dependency-graph CLT wrapper when the linear variance floor holds at every index.
The public theorem below removes this all-index convenience by shifting to a tail. -/
theorem bounded_degree_dependency_clt_of_variance_floor_all
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (Dep : ∀ n, DepGraph (X n) (μ n))
    (Dmax : ℕ) (hdeg : ∀ n i, ((Dep n).nbhd i).card ≤ Dmax)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ n i ω, |X n i ω| ≤ M)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = v n)
    (c : ℝ) (hc : 0 < c)
    (hvc : ∀ n, c * (Fintype.card (ι n) : ℝ) ≤ v n)
    (hcard_pos : ∀ n, 0 < Fintype.card (ι n))
    (hcard : Tendsto (fun n => Fintype.card (ι n)) atTop atTop)
    (s : ℝ) :
    Tendsto (fun n =>
        ((μ n).map (fun ω => depSum (X n) ω / Real.sqrt (v n))).real (Set.Iic s))
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  set Xs : ∀ n, ι n → Ω n → ℝ := fun n i ω => X n i ω / Real.sqrt (v n) with hXs
  set Ds : ∀ n, DepGraph (Xs n) (μ n) :=
    fun n => depGraph_div_const (Dep n) (Real.sqrt (v n)) with hDs
  set cardR : ℕ → ℝ := fun n => (Fintype.card (ι n) : ℝ) with hcardR
  set K : ℝ := M / Real.sqrt c with hK
  set B : ℕ → ℝ := fun n => K / Real.sqrt (cardR n) with hBdef
  have hcardR_pos : ∀ n, 0 < cardR n := by
    intro n
    have hpos : (0 : ℝ) < (Fintype.card (ι n) : ℝ) := by
      exact_mod_cast hcard_pos n
    simpa [cardR] using hpos
  have hv_pos : ∀ n, 0 < v n := by
    intro n
    have hfloor : 0 < c * cardR n := mul_pos hc (hcardR_pos n)
    exact lt_of_lt_of_le hfloor (by simpa [cardR] using hvc n)
  have hmeas : ∀ n i, Measurable (Xs n i) := fun n i => (Ds n).meas i
  have hdeg' : ∀ n i, ((Ds n).nbhd i).card ≤ Dmax := by
    intro n i
    simpa [Ds, depGraph_div_const, DepGraph.nbhd] using hdeg n i
  have hB_nonneg : ∀ n, 0 ≤ B n := by
    intro n
    have hc_sqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hK_nonneg : 0 ≤ K := by
      rw [hK]
      exact div_nonneg hM hc_sqrt.le
    exact div_nonneg hK_nonneg (Real.sqrt_nonneg _)
  have hbound' : ∀ n i ω, |Xs n i ω| ≤ B n := by
    intro n i ω
    have hsv : 0 < Real.sqrt (v n) := Real.sqrt_pos.mpr (hv_pos n)
    have hsf : 0 < Real.sqrt (c * cardR n) :=
      Real.sqrt_pos.mpr (mul_pos hc (hcardR_pos n))
    have hs_le : Real.sqrt (c * cardR n) ≤ Real.sqrt (v n) :=
      Real.sqrt_le_sqrt (by simpa [cardR] using hvc n)
    calc |Xs n i ω| = |X n i ω| / Real.sqrt (v n) := by
          simp [hXs, abs_div, abs_of_pos hsv]
      _ ≤ M / Real.sqrt (v n) :=
          div_le_div_of_nonneg_right (hbound n i ω) hsv.le
      _ ≤ M / Real.sqrt (c * cardR n) :=
          div_le_div_of_nonneg_left hM hsf hs_le
      _ = B n := by
          rw [hBdef, hK, Real.sqrt_mul hc.le (cardR n)]
          field_simp [(Real.sqrt_pos.mpr hc).ne', (Real.sqrt_pos.mpr (hcardR_pos n)).ne']
  have hmean' : ∀ n i, ∫ ω, Xs n i ω ∂(μ n) = 0 := by
    intro n i
    have hsv_ne : Real.sqrt (v n) ≠ 0 := (Real.sqrt_pos.mpr (hv_pos n)).ne'
    have hfun : (fun ω => Xs n i ω) =
        fun ω => (Real.sqrt (v n))⁻¹ * X n i ω := by
      funext ω
      simp [hXs, div_eq_inv_mul]
    rw [hfun, integral_const_mul, hmean n i, mul_zero]
  have hdep : ∀ n, depSum (Xs n) = fun ω => depSum (X n) ω / Real.sqrt (v n) := by
    intro n
    funext ω
    simp [depSum, hXs, Finset.sum_div]
  have hvar' : ∀ n, ∫ ω, (depSum (Xs n) ω) ^ 2 ∂(μ n) = 1 := by
    intro n
    have hvn_pos : 0 < v n := hv_pos n
    have hsv_ne : Real.sqrt (v n) ≠ 0 := (Real.sqrt_pos.mpr hvn_pos).ne'
    rw [hdep n]
    have hfun : (fun ω => (depSum (X n) ω / Real.sqrt (v n)) ^ 2)
        = fun ω => ((Real.sqrt (v n)) ^ 2)⁻¹ * (depSum (X n) ω) ^ 2 := by
      funext ω
      field_simp [hsv_ne]
    rw [hfun, integral_const_mul, hv n, Real.sq_sqrt hvn_pos.le]
    field_simp [hvn_pos.ne']
  have hcardR_tendsto : Tendsto cardR atTop atTop := by
    simpa [cardR] using tendsto_natCast_atTop_atTop.comp hcard
  have hsqrtcard : Tendsto (fun n => Real.sqrt (cardR n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcardR_tendsto
  have hB0 : Tendsto B atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => K / Real.sqrt (cardR n)) atTop (𝓝 0) :=
      hsqrtcard.const_div_atTop K
    simpa [B] using hlim
  have hNB3eq : (fun n => cardR n * (B n) ^ 3)
      = fun n => K ^ 3 / Real.sqrt (cardR n) := by
    funext n
    have hcpos : 0 < cardR n := hcardR_pos n
    have hs_ne : Real.sqrt (cardR n) ≠ 0 := (Real.sqrt_pos.mpr hcpos).ne'
    rw [hBdef]
    calc cardR n * (K / Real.sqrt (cardR n)) ^ 3
        = K ^ 3 * (cardR n / (Real.sqrt (cardR n)) ^ 3) := by ring
      _ = K ^ 3 / Real.sqrt (cardR n) := by
        rw [show (Real.sqrt (cardR n)) ^ 3
              = Real.sqrt (cardR n) * (Real.sqrt (cardR n)) ^ 2 by ring,
            Real.sq_sqrt hcpos.le]
        field_simp [hs_ne]
  have hNB3 : Tendsto (fun n => (Fintype.card (ι n) : ℝ) * (B n) ^ 3)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => K ^ 3 / Real.sqrt (cardR n)) atTop (𝓝 0) :=
      hsqrtcard.const_div_atTop (K ^ 3)
    simpa [cardR, hNB3eq] using hlim
  have hclt := stein_cdf_clt_of_depGraph μ Xs Ds hmeas Dmax hdeg' B hB_nonneg hbound'
    hB0 hNB3 hmean' hvar' s
  exact hclt.congr (fun n => by rw [hdep n])

/-- **Bounded-degree dependency-graph CLT (raw, variance-floor form).** A standardized
triangular-array CLT for mean-zero, uniformly bounded summands with a bounded-degree dependency
graph and a linearly growing variance, delivering CDF convergence of the standardized sum
`(∑ᵢ Xᵢ)/√vₙ` to the standard normal. The index size must diverge (`card ιₙ → ∞`); together with the
variance floor `vₙ ≥ c · card ιₙ` this forces the Lyapunov ratio `card ιₙ · (M/√vₙ)³ → 0` that
drives the Stein bound. -/
theorem bounded_degree_dependency_clt
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (Dep : ∀ n, DepGraph (X n) (μ n))
    (Dmax : ℕ) (hdeg : ∀ n i, ((Dep n).nbhd i).card ≤ Dmax)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ n i ω, |X n i ω| ≤ M)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = v n)
    (c : ℝ) (hc : 0 < c)
    (hvc : ∀ᶠ n in atTop, c * (Fintype.card (ι n) : ℝ) ≤ v n)
    (hcard : Tendsto (fun n => Fintype.card (ι n)) atTop atTop)
    (s : ℝ) :
    Tendsto (fun n =>
        ((μ n).map (fun ω => depSum (X n) ω / Real.sqrt (v n))).real (Set.Iic s))
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  rcases eventually_atTop.1 hvc with ⟨Nv, hNv⟩
  rcases eventually_atTop.1 (hcard.eventually_ge_atTop 1) with ⟨Nc, hNc⟩
  let N := max Nv Nc
  have hvc_tail : ∀ n, c * (Fintype.card (ι (n + N)) : ℝ) ≤ v (n + N) := by
    intro n
    apply hNv
    omega
  have hcard_pos_tail : ∀ n, 0 < Fintype.card (ι (n + N)) := by
    intro n
    have hge : 1 ≤ Fintype.card (ι (n + N)) := hNc (n + N) (by omega)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one hge
  have hcard_tail : Tendsto (fun n => Fintype.card (ι (n + N))) atTop atTop :=
    hcard.comp (tendsto_add_atTop_nat N)
  have htail :=
    bounded_degree_dependency_clt_of_variance_floor_all
      (μ := fun n => μ (n + N))
      (X := fun n => X (n + N))
      (Dep := fun n => Dep (n + N))
      Dmax
      (fun n i => hdeg (n + N) i)
      M hM
      (fun n i ω => hbound (n + N) i ω)
      (fun n i => hmean (n + N) i)
      (fun n => v (n + N))
      (fun n => hv (n + N))
      c hc hvc_tail hcard_pos_tail hcard_tail s
  exact (tendsto_add_atTop_iff_nat N).1 htail

/-- Eventual-bound variant of `bounded_degree_dependency_clt`: only the tail of a triangular array
affects the limiting CDF, so the uniform summand bound need only hold after a finite prefix. -/
theorem bounded_degree_dependency_clt_eventually_bounded
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (Dep : ∀ n, DepGraph (X n) (μ n))
    (Dmax : ℕ) (hdeg : ∀ n i, ((Dep n).nbhd i).card ≤ Dmax)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᶠ n in atTop, ∀ i ω, |X n i ω| ≤ M)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = v n)
    (c : ℝ) (hc : 0 < c)
    (hvc : ∀ᶠ n in atTop, c * (Fintype.card (ι n) : ℝ) ≤ v n)
    (hcard : Tendsto (fun n => Fintype.card (ι n)) atTop atTop)
    (s : ℝ) :
    Tendsto (fun n =>
        ((μ n).map (fun ω => depSum (X n) ω / Real.sqrt (v n))).real (Set.Iic s))
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  rcases eventually_atTop.1 hbound with ⟨Nb, hNb⟩
  have hbound_tail : ∀ n i ω, |X (n + Nb) i ω| ≤ M := by
    intro n i ω
    exact hNb (n + Nb) (by omega) i ω
  have hvc_tail : ∀ᶠ n in atTop,
      c * (Fintype.card (ι (n + Nb)) : ℝ) ≤ v (n + Nb) := by
    rcases eventually_atTop.1 hvc with ⟨Nv, hNv⟩
    exact eventually_atTop.2 ⟨Nv, fun n hn => hNv (n + Nb) (by omega)⟩
  have hcard_tail : Tendsto (fun n => Fintype.card (ι (n + Nb))) atTop atTop :=
    hcard.comp (tendsto_add_atTop_nat Nb)
  have htail :=
    bounded_degree_dependency_clt
      (μ := fun n => μ (n + Nb))
      (X := fun n => X (n + Nb))
      (Dep := fun n => Dep (n + Nb))
      Dmax
      (fun n i => hdeg (n + Nb) i)
      M hM hbound_tail
      (fun n i => hmean (n + Nb) i)
      (fun n => v (n + Nb))
      (fun n => hv (n + Nb))
      c hc hvc_tail hcard_tail s
  exact (tendsto_add_atTop_iff_nat Nb).1 htail

end SteinMethod
end Causalean
