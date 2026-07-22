/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The dependency-graph CLT from primitive conditions

`stein_cdf_clt` needs the two Stein negligibility limits (`Var(∑XᵢTᵢ)→0`, `∑E[|Xᵢ|Tᵢ²]→0`) and
the leave-out independence as hypotheses.  Here we *derive* them from a genuine **dependency
graph** (the Chen–Shao / Aronow–Samii Condition 3): a reflexive symmetric relation `G` on the
index set whose non-adjacent index sets carry independent variable tuples, with bounded degree
`m`, together with bounded summands `|Xᵢ| ≤ Bₙ` such that `Bₙ → 0` and `N·Bₙ³ → 0`.

The covariance `Cov(XᵢTᵢ, XⱼTⱼ)` vanishes unless `i,j` are at graph distance at most three
(so the closed neighborhoods `Nᵢ, Nⱼ` are not separated); there are `≤ N·m³` such pairs, each
bounded by `2(m·Bₙ²)²`, giving `Var(∑XᵢTᵢ) ≤ 2m⁵·N·Bₙ⁴ → 0`; and
`∑E[|Xᵢ|Tᵢ²] ≤ m²·N·Bₙ³ → 0`.  The
leave-out independence is the dependency-graph property applied to `{i}` and `Nᵢᶜ`.  See
`doc/stein_clt_plan.md`.
-/

import Causalean.Mathlib.Probability.SteinMethod.CLT
import Mathlib.Probability.Independence.Basic

/-!
# Dependency-graph central limit theorem from primitive graph conditions

This file derives the local-dependence Stein hypotheses from a dependency graph
with bounded degree and uniformly small summands. It defines `DepGraph` and
`DepGraph.nbhd`, proves leave-out independence, separated-neighborhood
covariance cancellation, the bounds `DepGraph.var_nbhd_prod_le` and
`DepGraph.sum_E_nbhd_sq_le`, and concludes with the CDF central limit theorem
`stein_cdf_clt_of_depGraph`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators

namespace Causalean
namespace SteinMethod

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A **dependency graph** for the family `X`: `G` is a reflexive symmetric relation, the closed
neighborhood is `N i = {j | G i j}`, and any two index sets with no edges between them carry
independent variable tuples. -/
structure DepGraph (X : ι → Ω → ℝ) (μ : Measure Ω) where
  /-- The dependency relation. -/
  G : ι → ι → Prop
  /-- Decidability of adjacency (for the neighborhood `Finset`). -/
  decG : DecidableRel G
  /-- Each index depends on itself. -/
  refl : ∀ i, G i i
  /-- Symmetry of the dependency relation. -/
  symm : ∀ i j, G i j → G j i
  /-- Each variable in the family is measurable. -/
  meas : ∀ i, Measurable (X i)
  /-- Non-adjacent index sets carry independent variable tuples. -/
  indep : ∀ A B : Finset ι, (∀ a ∈ A, ∀ b ∈ B, ¬ G a b) →
    IndepFun (fun ω => fun k : A => X k ω) (fun ω => fun k : B => X k ω) μ

namespace DepGraph

variable {X : ι → Ω → ℝ} (D : DepGraph X μ)

/-- The closed dependency neighborhood `N i = {j | G i j}`. -/
noncomputable def nbhd (i : ι) : Finset ι := by
  letI := D.decG; exact Finset.univ.filter (fun j => D.G i j)

/-- Membership in the neighborhood is exactly adjacency. -/
theorem mem_nbhd_iff {i j : ι} : j ∈ D.nbhd i ↔ D.G i j := by
  letI := D.decG
  simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Each index is in its own neighborhood. -/
theorem self_mem_nbhd (i : ι) : i ∈ D.nbhd i := D.mem_nbhd_iff.mpr (D.refl i)

/-- The neighborhood sum is measurable. -/
private theorem measurable_nbhdSum (i : ι) :
    Measurable (fun ω => ∑ k ∈ D.nbhd i, X k ω) :=
  Finset.measurable_sum _ (fun k _ => D.meas k)

/-- The localized product `gᵢ = Xᵢ · Tᵢ` is measurable. -/
private theorem measurable_locProd (i : ι) :
    Measurable (fun ω => X i ω * ∑ k ∈ D.nbhd i, X k ω) :=
  (D.meas i).mul (D.measurable_nbhdSum i)

/-- Pointwise bound on the neighborhood sum: `|Tᵢ| ≤ (card Nᵢ)·B ≤ m·B`. -/
private theorem abs_nbhdSum_le {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (D.nbhd i).card ≤ m) (i : ι) (ω : Ω) :
    |∑ k ∈ D.nbhd i, X k ω| ≤ (m : ℝ) * B := by
  calc |∑ k ∈ D.nbhd i, X k ω| ≤ ∑ k ∈ D.nbhd i, |X k ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ D.nbhd i, B := Finset.sum_le_sum (fun k _ => hbound k ω)
    _ = (D.nbhd i).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast hdeg i

/-- Pointwise bound on the localized product `|gᵢ| ≤ m·B²`. -/
private theorem abs_locProd_le {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (D.nbhd i).card ≤ m) (i : ι) (ω : Ω) :
    |X i ω * ∑ k ∈ D.nbhd i, X k ω| ≤ (m : ℝ) * B ^ 2 := by
  rw [abs_mul]
  calc |X i ω| * |∑ k ∈ D.nbhd i, X k ω|
      ≤ B * ((m : ℝ) * B) :=
        mul_le_mul (hbound i ω) (D.abs_nbhdSum_le hB hbound hdeg i ω) (abs_nonneg _) hB
    _ = (m : ℝ) * B ^ 2 := by ring

/-- **Leave-out independence** (the `stein_cdf_clt` hypothesis `hindep`). -/
theorem indepFun_leaveOut (i : ι) :
    IndepFun (X i) (fun ω => ∑ j ∈ Finset.univ \ D.nbhd i, X j ω) μ := by
  classical
  -- The two index sets `{i}` and `univ \ N i` have no edges between them.
  have hsep : ∀ a ∈ ({i} : Finset ι), ∀ b ∈ Finset.univ \ D.nbhd i, ¬ D.G a b := by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha; subst ha
    rw [Finset.mem_sdiff] at hb
    exact fun hab => hb.2 (D.mem_nbhd_iff.mpr hab)
  have hind := D.indep ({i} : Finset ι) (Finset.univ \ D.nbhd i) hsep
  -- Eval at `i` on the `{i}`-tuple, and the total sum on the `(univ \ N i)`-tuple.
  -- The two composing maps are measurable (Pi-evaluation / finite sum of evaluations).
  have hφ : Measurable fun t : (({i} : Finset ι) → ℝ) => t ⟨i, Finset.mem_singleton.mpr rfl⟩ :=
    measurable_pi_apply _
  have hψ : Measurable fun t : ((Finset.univ \ D.nbhd i : Finset ι) → ℝ) => ∑ k, t k :=
    Finset.measurable_sum _ (fun k _ => measurable_pi_apply _)
  have hcomp := hind.comp hφ hψ
  -- Identify the two sides with `X i` and the leave-out sum.
  have h1 : (fun t : (({i} : Finset ι) → ℝ) => t ⟨i, Finset.mem_singleton.mpr rfl⟩)
        ∘ (fun ω => fun k : ({i} : Finset ι) => X k ω) = X i := rfl
  have h2 : (fun t : ((Finset.univ \ D.nbhd i : Finset ι) → ℝ) => ∑ k, t k)
        ∘ (fun ω => fun k : (Finset.univ \ D.nbhd i : Finset ι) => X k ω)
        = (fun ω => ∑ j ∈ Finset.univ \ D.nbhd i, X j ω) := by
    funext ω
    simp only [Function.comp]
    rw [Finset.sum_coe_sort (Finset.univ \ D.nbhd i) (fun j => X j ω)]
  rw [h1, h2] at hcomp
  exact hcomp

/-- **Covariance vanishing for separated indices.** If `Nᵢ` and `Nⱼ` have no edges between them,
the localized products `Xᵢ·Tᵢ` and `Xⱼ·Tⱼ` are uncorrelated. -/
theorem cov_mul_nbhd_eq_zero {i j : ι}
    (hsep : ∀ a ∈ D.nbhd i, ∀ b ∈ D.nbhd j, ¬ D.G a b) :
    μ[fun ω => (X i ω * ∑ k ∈ D.nbhd i, X k ω) * (X j ω * ∑ k ∈ D.nbhd j, X k ω)]
      = μ[fun ω => X i ω * ∑ k ∈ D.nbhd i, X k ω]
        * μ[fun ω => X j ω * ∑ k ∈ D.nbhd j, X k ω] := by
  classical
  -- Tuples over the two neighborhoods are independent.
  have hind := D.indep (D.nbhd i) (D.nbhd j) hsep
  -- `φ` reads off `Xᵢ` (via `i ∈ Nᵢ`) and forms `Xᵢ · ∑_{k∈Nᵢ} Xₖ` from the `Nᵢ`-tuple.
  let φ : (↥(D.nbhd i) → ℝ) → ℝ :=
    fun t => t ⟨i, D.self_mem_nbhd i⟩ * ∑ k, t k
  let ψ : (↥(D.nbhd j) → ℝ) → ℝ :=
    fun t => t ⟨j, D.self_mem_nbhd j⟩ * ∑ k, t k
  have hφ : Measurable φ :=
    (measurable_pi_apply _).mul (Finset.measurable_sum _ (fun k _ => measurable_pi_apply _))
  have hψ : Measurable ψ :=
    (measurable_pi_apply _).mul (Finset.measurable_sum _ (fun k _ => measurable_pi_apply _))
  -- Both tuples are AEMeasurable (each coordinate `X k` is measurable).
  have hXi : AEMeasurable (fun ω => fun k : ↥(D.nbhd i) => X k ω) μ :=
    (measurable_pi_lambda _ (fun k : ↥(D.nbhd i) => D.meas (↑k))).aemeasurable
  have hXj : AEMeasurable (fun ω => fun k : ↥(D.nbhd j) => X k ω) μ :=
    (measurable_pi_lambda _ (fun k : ↥(D.nbhd j) => D.meas (↑k))).aemeasurable
  have key := hind.integral_fun_comp_mul_comp hXi hXj
    hφ.aestronglyMeasurable hψ.aestronglyMeasurable
  -- Identify `φ ∘ tupleᵢ = gᵢ` pointwise.
  have eφ : ∀ ω, φ (fun k : ↥(D.nbhd i) => X k ω)
      = X i ω * ∑ k ∈ D.nbhd i, X k ω := by
    intro ω
    simp only [φ]
    rw [Finset.sum_coe_sort (D.nbhd i) (fun k => X k ω)]
  have eψ : ∀ ω, ψ (fun k : ↥(D.nbhd j) => X k ω)
      = X j ω * ∑ k ∈ D.nbhd j, X k ω := by
    intro ω
    simp only [ψ]
    rw [Finset.sum_coe_sort (D.nbhd j) (fun k => X k ω)]
  simp only [eφ, eψ] at key
  exact key

/-- The localized product `gᵢ` lies in `L²`. -/
private theorem memLp_locProd {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (D.nbhd i).card ≤ m) (i : ι) :
    MemLp (fun ω => X i ω * ∑ k ∈ D.nbhd i, X k ω) 2 μ :=
  MemLp.of_bound (D.measurable_locProd i).aestronglyMeasurable ((m : ℝ) * B ^ 2)
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact D.abs_locProd_le hB hbound hdeg i ω))

/-- The covariance of two localized products is bounded by `2(mB²)²` in absolute value. -/
private theorem abs_cov_locProd_le {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (D.nbhd i).card ≤ m) (i j : ι) :
    |covariance (fun ω => X i ω * ∑ k ∈ D.nbhd i, X k ω)
        (fun ω => X j ω * ∑ k ∈ D.nbhd j, X k ω) μ|
      ≤ 2 * ((m : ℝ) * B ^ 2) ^ 2 := by
  set gi := fun ω => X i ω * ∑ k ∈ D.nbhd i, X k ω with hgi
  set gj := fun ω => X j ω * ∑ k ∈ D.nbhd j, X k ω with hgj
  have hMi := D.memLp_locProd hB hbound hdeg i
  have hMj := D.memLp_locProd hB hbound hdeg j
  rw [covariance_eq_sub hMi hMj]
  -- `|gᵢ| ≤ mB²` and `|gⱼ| ≤ mB²` pointwise.
  have hbi : ∀ ω, |gi ω| ≤ (m : ℝ) * B ^ 2 := fun ω => D.abs_locProd_le hB hbound hdeg i ω
  have hbj : ∀ ω, |gj ω| ≤ (m : ℝ) * B ^ 2 := fun ω => D.abs_locProd_le hB hbound hdeg j ω
  have hC : (0 : ℝ) ≤ (m : ℝ) * B ^ 2 := by positivity
  -- Bound `|μ[gᵢ·gⱼ]| ≤ (mB²)²`.
  have hMi_int : Integrable gi μ := hMi.integrable one_le_two
  have hMj_int : Integrable gj μ := hMj.integrable one_le_two
  have hprod : |μ[fun ω => gi ω * gj ω]| ≤ ((m : ℝ) * B ^ 2) ^ 2 := by
    have hint : Integrable (fun ω => gi ω * gj ω) μ := hMi.integrable_mul hMj
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |gi ω * gj ω| ∂μ ≤ ∫ _ω, ((m : ℝ) * B ^ 2) ^ 2 ∂μ := by
            refine integral_mono hint.abs (integrable_const _) (fun ω => ?_)
            rw [abs_mul, sq]
            exact mul_le_mul (hbi ω) (hbj ω) (abs_nonneg _) hC
      _ = ((m : ℝ) * B ^ 2) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  -- Bound `|μ[gᵢ]·μ[gⱼ]| ≤ (mB²)²`.
  have hEi : |μ[gi]| ≤ (m : ℝ) * B ^ 2 := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |gi ω| ∂μ ≤ ∫ _ω, (m : ℝ) * B ^ 2 ∂μ :=
            integral_mono hMi_int.abs (integrable_const _) hbi
      _ = (m : ℝ) * B ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  have hEj : |μ[gj]| ≤ (m : ℝ) * B ^ 2 := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |gj ω| ∂μ ≤ ∫ _ω, (m : ℝ) * B ^ 2 ∂μ :=
            integral_mono hMj_int.abs (integrable_const _) hbj
      _ = (m : ℝ) * B ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  have hmean_prod : |μ[gi] * μ[gj]| ≤ ((m : ℝ) * B ^ 2) ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hEi hEj (abs_nonneg _) hC
  -- Combine via the triangle inequality.
  calc |μ[fun ω => gi ω * gj ω] - μ[gi] * μ[gj]|
      ≤ |μ[fun ω => gi ω * gj ω]| + |μ[gi] * μ[gj]| := abs_sub _ _
    _ ≤ ((m : ℝ) * B ^ 2) ^ 2 + ((m : ℝ) * B ^ 2) ^ 2 := add_le_add hprod hmean_prod
    _ = 2 * ((m : ℝ) * B ^ 2) ^ 2 := by ring

/-- **Pair-counting variance bound (`herr1`).** With bounded summands `|Xᵢ| ≤ B` and degree
`≤ m`, the covariance double sum collapses to the `≤ N·m³` pairs at graph distance at most
three, each
bounded by `2(mB²)²`, giving `Var(∑ᵢ Xᵢ·Tᵢ) ≤ 2·m⁵·N·B⁴`. -/
theorem var_nbhd_prod_le {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (D.nbhd i).card ≤ m) :
    variance (fun ω => ∑ i, X i ω * ∑ k ∈ D.nbhd i, X k ω) μ
      ≤ 2 * (m : ℝ) ^ 5 * (Fintype.card ι : ℝ) * B ^ 4 := by
  classical
  set g : ι → Ω → ℝ := fun i ω => X i ω * ∑ k ∈ D.nbhd i, X k ω with hg
  have hM : ∀ i, MemLp (g i) 2 μ := fun i => D.memLp_locProd hB hbound hdeg i
  -- Expand the variance into a covariance double sum.
  have hvar_eq : variance (fun ω => ∑ i, g i ω) μ = ∑ i, ∑ j, covariance (g i) (g j) μ :=
    variance_fun_sum hM
  rw [show (fun ω => ∑ i, X i ω * ∑ k ∈ D.nbhd i, X k ω) = (fun ω => ∑ i, g i ω) from rfl,
    hvar_eq]
  -- For each `i`, restrict the inner sum to the "non-separated" `j`s; separated ones vanish.
  -- The non-separated set sits inside a double neighborhood expansion of `Nᵢ`.
  set S : ι → Finset ι := fun i => (D.nbhd i).biUnion (fun a => D.nbhd a) with hS
  set T : ι → Finset ι := fun i => (S i).biUnion (fun b => D.nbhd b) with hT
  -- `cov[gᵢ, gⱼ] = 0` when `j ∉ T i` (the indices are separated).
  have hsep_zero : ∀ i j, j ∉ T i → covariance (g i) (g j) μ = 0 := by
    intro i j hj
    -- Show `Nᵢ` and `Nⱼ` are separated.
    have hsep : ∀ a ∈ D.nbhd i, ∀ b ∈ D.nbhd j, ¬ D.G a b := by
      intro a ha b hb hab
      -- `b ∈ N a ⊆ S i`, and `j ∈ N b` (by symm), so `j ∈ T i` — contradiction.
      apply hj
      rw [hT, Finset.mem_biUnion]
      refine ⟨b, ?_, ?_⟩
      · rw [hS, Finset.mem_biUnion]
        exact ⟨a, ha, D.mem_nbhd_iff.mpr hab⟩
      · -- `b ∈ Nⱼ` means `G j b`; by symm `G b j`, i.e. `j ∈ N b`.
        exact D.mem_nbhd_iff.mpr (D.symm j b (D.mem_nbhd_iff.mp hb))
    have hcov := D.cov_mul_nbhd_eq_zero hsep
    rw [covariance_eq_sub (hM i) (hM j)]
    rw [show (g i * g j) = (fun ω => g i ω * g j ω) from rfl] at *
    rw [hcov]; ring
  -- Drop the separated `j`s from the inner sum.
  have hinner : ∀ i, ∑ j, covariance (g i) (g j) μ
      = ∑ j ∈ T i, covariance (g i) (g j) μ := by
    intro i
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact hsep_zero i j hj
  -- Bound: each retained covariance ≤ 2(mB²)², and `#(T i) ≤ m³`.
  have hcard_S : ∀ i, (S i).card ≤ m * m := by
    intro i
    calc (S i).card ≤ ∑ a ∈ D.nbhd i, (D.nbhd a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ D.nbhd i, m := Finset.sum_le_sum (fun a _ => hdeg a)
      _ = (D.nbhd i).card * m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m * m := Nat.mul_le_mul_right m (hdeg i)
  have hcard_T : ∀ i, (T i).card ≤ m ^ 3 := by
    intro i
    calc (T i).card ≤ ∑ b ∈ S i, (D.nbhd b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ S i, m := Finset.sum_le_sum (fun b _ => hdeg b)
      _ = (S i).card * m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (m * m) * m := Nat.mul_le_mul_right m (hcard_S i)
      _ = m ^ 3 := by ring
  -- Now bound the full double sum.
  have hCnn : (0 : ℝ) ≤ 2 * ((m : ℝ) * B ^ 2) ^ 2 := by positivity
  calc ∑ i, ∑ j, covariance (g i) (g j) μ
      = ∑ i, ∑ j ∈ T i, covariance (g i) (g j) μ := by
        exact Finset.sum_congr rfl (fun i _ => hinner i)
    _ ≤ ∑ i, ∑ j ∈ T i, |covariance (g i) (g j) μ| :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => le_abs_self _))
    _ ≤ ∑ i, ∑ _j ∈ T i, 2 * ((m : ℝ) * B ^ 2) ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
          (fun j _ => D.abs_cov_locProd_le hB hbound hdeg i j))
    _ = ∑ i, (T i).card * (2 * ((m : ℝ) * B ^ 2) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _i : ι, (m ^ 3 : ℝ) * (2 * ((m : ℝ) * B ^ 2) ^ 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        apply mul_le_mul_of_nonneg_right _ hCnn
        exact_mod_cast hcard_T i
    _ = (Fintype.card ι : ℝ) * ((m ^ 3 : ℝ) * (2 * ((m : ℝ) * B ^ 2) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 2 * (m : ℝ) ^ 5 * (Fintype.card ι : ℝ) * B ^ 4 := by ring

/-- **Negligibility bound (`herr2`).** `∑ᵢ E[|Xᵢ|·Tᵢ²] ≤ m²·N·B³`. -/
theorem sum_E_nbhd_sq_le {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (D.nbhd i).card ≤ m) :
    ∑ i, ∫ ω, |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2 ∂μ
      ≤ (m : ℝ) ^ 2 * (Fintype.card ι : ℝ) * B ^ 3 := by
  classical
  -- Per `i`, the integrand is bounded by the constant `m²·B³`.
  have hpt : ∀ i ω, |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2 ≤ (m : ℝ) ^ 2 * B ^ 3 := by
    intro i ω
    have h1 : |X i ω| ≤ B := hbound i ω
    have h2 : (∑ k ∈ D.nbhd i, X k ω) ^ 2 ≤ ((m : ℝ) * B) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (D.abs_nbhdSum_le hB hbound hdeg i ω) 2
    calc |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2
        ≤ B * ((m : ℝ) * B) ^ 2 :=
          mul_le_mul h1 h2 (sq_nonneg _) hB
      _ = (m : ℝ) ^ 2 * B ^ 3 := by ring
  -- Hence each integral is `≤ m²·B³`.
  have hint : ∀ i, ∫ ω, |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2 ∂μ ≤ (m : ℝ) ^ 2 * B ^ 3 := by
    intro i
    have hmeas_i : Measurable (fun ω => |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2) :=
      ((D.meas i).abs).mul ((D.measurable_nbhdSum i).pow_const 2)
    have hbdd : ∀ ω, |(|X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2)| ≤ (m : ℝ) ^ 2 * B ^ 3 := by
      intro ω
      rw [abs_of_nonneg (by positivity)]
      exact hpt i ω
    have hintegrable : Integrable (fun ω => |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2) μ :=
      (MemLp.of_bound hmeas_i.aestronglyMeasurable ((m : ℝ) ^ 2 * B ^ 3)
        (Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs]; exact hbdd ω))).integrable le_rfl
    calc ∫ ω, |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2 ∂μ
        ≤ ∫ _ω, (m : ℝ) ^ 2 * B ^ 3 ∂μ :=
          integral_mono hintegrable (integrable_const _) (fun ω => hpt i ω)
      _ = (m : ℝ) ^ 2 * B ^ 3 := by
          rw [integral_const, probReal_univ, one_smul]
  -- Sum over `i` (there are `N = card ι` of them).
  calc ∑ i, ∫ ω, |X i ω| * (∑ k ∈ D.nbhd i, X k ω) ^ 2 ∂μ
      ≤ ∑ _i : ι, (m : ℝ) ^ 2 * B ^ 3 := Finset.sum_le_sum (fun i _ => hint i)
    _ = (Fintype.card ι : ℝ) * ((m : ℝ) ^ 2 * B ^ 3) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (m : ℝ) ^ 2 * (Fintype.card ι : ℝ) * B ^ 3 := by ring

end DepGraph

/-- **The bounded dependency-graph CLT.** From a dependency graph with bounded degree `m`,
bounded summands `|Xₙᵢ| ≤ Bₙ` with `Bₙ → 0` and `N·Bₙ³ → 0`, mean-zero summands, and unit total
variance, the standardized sum converges in distribution to a standard normal (CDF form). The two
Stein negligibility limits are derived internally. -/
theorem stein_cdf_clt_of_depGraph
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (hmeas : ∀ n i, Measurable (X n i))
    (m : ℕ) (hdeg : ∀ n i, ((D n).nbhd i).card ≤ m)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hbound : ∀ n i ω, |X n i ω| ≤ B n)
    (hB0 : Tendsto B atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (ι n) : ℝ) * (B n) ^ 3) atTop (𝓝 0))
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (s : ℝ) :
    Tendsto (fun n => ((μ n).map (depSum (X n))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  -- `nbhdSum (X n) (Nₙ) i ω = ∑_{k∈Nₙ i} X n k ω` definitionally.
  -- Leave-out independence and the self-membership hypothesis come from the dependency graph.
  have hself : ∀ n i, i ∈ (D n).nbhd i := fun n i => (D n).self_mem_nbhd i
  have hindep : ∀ n i, IndepFun (X n i)
      (fun ω => ∑ j ∈ Finset.univ \ (D n).nbhd i, X n j ω) (μ n) :=
    fun n i => (D n).indepFun_leaveOut i
  -- Error term 1: variance of the localized double sum, squeezed via `var_nbhd_prod_le`.
  have herr1 : Tendsto (fun n => variance
      (fun ω => ∑ i, X n i ω * nbhdSum (X n) (fun i => (D n).nbhd i) i ω) (μ n))
      atTop (𝓝 0) := by
    -- Upper bound `2 m⁵ · N · B⁴ → 0`.
    have hub : Tendsto (fun n => 2 * (m : ℝ) ^ 5 * (Fintype.card (ι n) : ℝ) * (B n) ^ 4)
        atTop (𝓝 0) := by
      have hfac : (fun n => 2 * (m : ℝ) ^ 5 * (Fintype.card (ι n) : ℝ) * (B n) ^ 4)
          = (fun n => (2 * (m : ℝ) ^ 5) *
              (((Fintype.card (ι n) : ℝ) * (B n) ^ 3) * B n)) := by
        funext n; ring
      rw [hfac]
      have h := (hNB3.mul hB0)
      simpa using (h.const_mul (2 * (m : ℝ) ^ 5)).congr (fun n => by ring)
    refine squeeze_zero (fun n => variance_nonneg _ _) (fun n => ?_) hub
    have := (D n).var_nbhd_prod_le (hB n) (hbound n) (hdeg n)
    simpa only [nbhdSum] using this
  -- Error term 2: `∑ᵢ E[|Xᵢ|·Tᵢ²]`, squeezed via `sum_E_nbhd_sq_le`.
  have herr2 : Tendsto (fun n => ∑ i,
      ∫ ω, |X n i ω| * (nbhdSum (X n) (fun i => (D n).nbhd i) i ω) ^ 2 ∂(μ n))
      atTop (𝓝 0) := by
    have hub : Tendsto (fun n => (m : ℝ) ^ 2 * (Fintype.card (ι n) : ℝ) * (B n) ^ 3)
        atTop (𝓝 0) := by
      have hfac : (fun n => (m : ℝ) ^ 2 * (Fintype.card (ι n) : ℝ) * (B n) ^ 3)
          = (fun n => (m : ℝ) ^ 2 * ((Fintype.card (ι n) : ℝ) * (B n) ^ 3)) := by
        funext n; ring
      rw [hfac]
      simpa using hNB3.const_mul ((m : ℝ) ^ 2)
    have hnonneg : ∀ n, 0 ≤ ∑ i,
        ∫ ω, |X n i ω| * (nbhdSum (X n) (fun i => (D n).nbhd i) i ω) ^ 2 ∂(μ n) := by
      intro n
      apply Finset.sum_nonneg
      intro i _
      apply integral_nonneg
      intro ω
      positivity
    refine squeeze_zero hnonneg (fun n => ?_) hub
    have := (D n).sum_E_nbhd_sq_le (hB n) (hbound n) (hdeg n)
    simpa only [nbhdSum] using this
  exact stein_cdf_clt μ X (fun n => (D n).nbhd) hmeas B hB hbound hmean hself hindep hvar
    herr1 herr2 s

end SteinMethod
end Causalean
