/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Independent-summands central limit theorem over product designs

A normalized sum of independent, uniformly bounded, mean-zero per-coordinate summands over a
product design converges in distribution to the standard normal — the independent-summands case
of the Stein dependency-graph CLT, with cross-coordinate independence supplied by the
product-measure bridge.

Concretely, for each `n` we have a finite family of independent coordinate designs `D n i` and
real summands `g n i : α n i → ℝ`, each bounded by `B n` (with `B n → 0` and `card·B³ → 0`) and
mean-zero, whose total sum `∑ᵢ g n i (w i)` has unit design variance.  The product design makes
the coordinate summands genuinely measure-theoretically independent, so the trivial **diagonal**
dependency graph `G a b := a = b` (every node depends only on itself, degree one) satisfies the
`DepGraph` independence field via `indepFun_prodDesign_apply_blocks`.  Feeding this into
`stein_cdf_clt_of_depGraph` yields `P[∑ᵢ g n i (w i) ≤ s] → Φ(s)`.  This is the
zero-dependence specialization of `localDependenceCLT_of_conditions`.
-/

import Causalean.Mathlib.Probability.SteinMethod.DepGraphCLT
import Causalean.Experimentation.DesignBased.ProductMeasure
import Causalean.Experimentation.DesignBased.GaussianCDF

/-! # Independent-summands CLT for product designs

Product-design sums of independent bounded mean-zero summands satisfy a standard-normal limit.

The construction `diagDepGraph` supplies the dependency graph whose only edges are self-edges, with
independence coming from finite product designs. The theorem `prodDesign_clt` then specializes the
dependency-graph Stein CLT: uniformly bounded, mean-zero coordinate summands with vanishing
third-moment envelope and unit total design variance have standard-normal distributional limits
under the product design.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

open Causalean.SteinMethod

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {α : ∀ n, ι n → Type*} [∀ n i, Fintype (α n i)]
variable [∀ n i, MeasurableSpace (α n i)] [∀ n i, MeasurableSingletonClass (α n i)]

/-- The **diagonal dependency graph** for the per-coordinate summands `X n i = fun w => g n i (w i)`
under the product-design measure: each coordinate depends only on itself (`G a b := a = b`).  The
independence field is the product-measure block independence `indepFun_prodDesign_apply_blocks`,
since distinct coordinate-index sets are disjoint. -/
noncomputable def diagDepGraph (D : ∀ n, ∀ i, FiniteDesign (α n i)) (g : ∀ n, ∀ i, α n i → ℝ)
    (n : ℕ) :
    DepGraph (fun (i : ι n) (w : ∀ j, α n j) => g n i (w i)) (prodDesign (D n)).toMeasure where
  G a b := a = b
  decG := inferInstance
  refl _ := rfl
  symm _ _ h := h.symm
  meas i := (Measurable.of_discrete).comp (measurable_pi_apply i)
  indep A B hAB := by
    -- Distinct index sets are disjoint, so the coordinate-block evaluations are independent.
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a haA haB
      exact hAB a haA a haB rfl
    exact indepFun_prodDesign_apply_blocks (D n)
      (fun i => Measurable.of_discrete) hdisj

/-- **Independent-summands CLT over product designs.** A normalized sum of independent, uniformly
bounded (`|g n i a| ≤ B n` with `B n → 0`, `card(ιₙ)·Bₙ³ → 0`), mean-zero per-coordinate summands
over the product design `prodDesign (D n)`, with unit total design variance, converges in
distribution to the standard normal: `P[∑ᵢ g n i (w i) ≤ s] → Φ(s)`. -/
theorem prodDesign_clt
    (D : ∀ n, ∀ i, FiniteDesign (α n i)) (g : ∀ n, ∀ i, α n i → ℝ)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hB0 : Tendsto B atTop (𝓝 0))
    (hbound : ∀ n i a, |g n i a| ≤ B n)
    (hNB3 : Tendsto (fun n => (Fintype.card (ι n) : ℝ) * (B n) ^ 3) atTop (𝓝 0))
    (hmean : ∀ n i, (D n i).E (g n i) = 0)
    (hvar : ∀ n, (prodDesign (D n)).Var (fun w => ∑ i, g n i (w i)) = 1)
    (s : ℝ) :
    Tendsto (fun n => (prodDesign (D n)).Pr (fun w => (∑ i, g n i (w i)) ≤ s))
      atTop (𝓝 (stdNormalCdf s)) := by
  classical
  -- Probability measures and per-coordinate summands.
  set μ : ∀ n, Measure (∀ j, α n j) := fun n => (prodDesign (D n)).toMeasure with hμ
  set X : ∀ n, ι n → (∀ j, α n j) → ℝ :=
    fun n i w => g n i (w i) with hX
  -- Diagonal dependency graph (independence from the product-measure bridge).
  set Dg : ∀ n, DepGraph (X n) (μ n) := fun n => diagDepGraph D g n with hDg
  -- Each summand is measurable.
  have hmeas : ∀ n i, Measurable (X n i) := fun n i => (Dg n).meas i
  -- Degree one: the neighborhood of `i` in the diagonal graph is `{i}`.
  have hdeg : ∀ n i, ((Dg n).nbhd i).card ≤ 1 := by
    intro n i
    have hsub : (Dg n).nbhd i ⊆ {i} := by
      intro j hj
      rw [Finset.mem_singleton]
      exact ((Dg n).mem_nbhd_iff.mp hj).symm
    calc ((Dg n).nbhd i).card ≤ ({i} : Finset (ι n)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton i
  -- Mean-zero: `∫ Xₙᵢ dμₙ = (prodDesign Dₙ).E (Xₙᵢ) = (Dₙᵢ).E (gₙᵢ) = 0`.
  have hmean' : ∀ n i, ∫ w, X n i w ∂(μ n) = 0 := by
    intro n i
    rw [hμ, hX, FiniteDesign.integral_toMeasure, FiniteDesign.E_prod_apply, hmean]
  -- `depSum (Xₙ) w = ∑ i, g n i (w i)` definitionally.
  have hdepSum : ∀ n, depSum (X n) = (fun w => ∑ i, g n i (w i)) := fun n => rfl
  -- The total sum is mean-zero under the product design.
  have hEsum : ∀ n, (prodDesign (D n)).E (fun w => ∑ i, g n i (w i)) = 0 := by
    intro n
    rw [show (fun w : ∀ j, α n j => ∑ i, g n i (w i))
          = (fun w => ∑ i, (fun i (w : ∀ j, α n j) => g n i (w i)) i w) from rfl,
      FiniteDesign.E_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [FiniteDesign.E_prod_apply, hmean]
  -- Unit total variance: `∫ (depSum Xₙ)² dμₙ = 1` (mean-zero so `E[S²] = Var S = 1`).
  have hvar' : ∀ n, ∫ w, (depSum (X n) w) ^ 2 ∂(μ n) = 1 := by
    intro n
    rw [hdepSum n, hμ, FiniteDesign.integral_toMeasure]
    have hve := FiniteDesign.Var_eq (prodDesign (D n)) (fun w => ∑ i, g n i (w i))
    rw [hEsum n, (by ring : (0 : ℝ) ^ 2 = 0), sub_zero] at hve
    rw [← hve, hvar n]
  -- Apply the dependency-graph Stein CLT (degree bound `m := 1`).
  have hbound' : ∀ n i (ω : ∀ j, α n j), |X n i ω| ≤ B n :=
    fun n i ω => hbound n i (ω i)
  have hclt := stein_cdf_clt_of_depGraph μ X Dg hmeas 1 hdeg B hB hbound' hB0 hNB3
    hmean' hvar' s
  -- Rewrite the limit point: `Φ(s) = (gaussianReal 0 1).real (Iic s)` by definition.
  rw [show stdNormalCdf s = (gaussianReal 0 1).real (Set.Iic s) from rfl]
  -- Match the prelimit sequences pointwise.
  refine hclt.congr (fun n => ?_)
  have hWmeas : Measurable (depSum (X n)) := by
    rw [hdepSum n]; exact Finset.measurable_sum _ (fun i _ => hmeas n i)
  have hset : {w | (∑ i, g n i (w i)) ≤ s} = (depSum (X n)) ⁻¹' Set.Iic s := by
    rw [hdepSum n]; rfl
  rw [hμ] at *
  rw [← FiniteDesign.toMeasure_real_setOf, hset,
    MeasureTheory.map_measureReal_apply hWmeas measurableSet_Iic]

end DesignBased
end Experimentation
end Causalean
