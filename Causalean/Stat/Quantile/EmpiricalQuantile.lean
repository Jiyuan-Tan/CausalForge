/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sample quantile (generalized inverse of the empirical cdf)

Causal-agnostic statistical primitive: the `τ`-**sample quantile** of an i.i.d.
real sample, defined as the (lower) generalized inverse of the empirical cdf

    q̂ₙ(τ) := quantile (νₙ) τ,     νₙ := (1/n) Σ_{i<n} δ_{Zᵢ},

where `νₙ` is the **empirical measure** and `quantile` is the cdf-inverse of
`Stat/Quantile.lean`.  Because `cdf νₙ = F̂ₙ` (the `empiricalCDF` of
`Stat/EmpiricalCDF.lean`), the sample quantile inherits the Galois connection

    q̂ₙ(τ) ≤ x  ↔  τ ≤ F̂ₙ(x)        (switching relation, `0 < τ < 1`).

This file supplies the empirical measure, the cdf bridge, the switching
relation, monotonicity of `F̂ₙ` in `y`, and the **atom bound**

    |F̂ₙ(q̂ₙ) − τ| ≤ 1/n        a.s. (under an atomless population),

which are the deterministic / structural facts feeding the Bahadur
derivation in `Stat/Quantile/SampleQuantileBahadur.lean`.

Project-agnostic; upstream-candidate.
-/

import Causalean.Stat.Quantile.EmpiricalCDF
import Causalean.Stat.Quantile.Quantile

/-! # Empirical Measures and Sample Quantiles

This file builds the sample quantile from the empirical measure of an i.i.d.
real sample. The central definitions are `IIDSample.empiricalMeasure`, the
finite empirical probability measure, and `IIDSample.sampleQuantile`, the
generalized inverse of that measure's cdf.

The main structural results are the cdf bridge
`IIDSample.empiricalMeasure_cdf`, the switching relation
`IIDSample.sampleQuantile_le_iff`, monotonicity of `IIDSample.empiricalCDF` in
its real argument, and the atom bound `IIDSample.sampleQuantile_atom_bound`.
Together these deterministic facts feed the derived Bahadur representation for
the ordinary empirical sample quantile.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-! ## Empirical measure -/

/-- The **empirical measure** `νₙ = (1/n) Σ_{i<n} δ_{Zᵢ}` of an i.i.d. sample. -/
noncomputable def IIDSample.empiricalMeasure (S : IIDSample Ω ℝ μ P) (n : ℕ) (ω : Ω) :
    Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (S.Z i ω)

/-- For `0 < n` the empirical measure is a probability measure. -/
lemma IIDSample.empiricalMeasure_isProbabilityMeasure (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (hn : 0 < n) (ω : Ω) :
    IsProbabilityMeasure (S.empiricalMeasure n ω) := by
  constructor
  unfold IIDSample.empiricalMeasure
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  simp only [MeasureTheory.measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  rw [ENNReal.inv_mul_cancel]
  · exact_mod_cast hn.ne'
  · exact ENNReal.natCast_ne_top n

/-- The empirical measure of the lower ray `Iic y` is `F̂ₙ(y)` (as `ℝ`). -/
lemma IIDSample.empiricalMeasure_real_Iic (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (_hn : 0 < n) (ω : Ω) (y : ℝ) :
    (S.empiricalMeasure n ω).real (Set.Iic y) = S.empiricalCDF y n ω := by
  unfold IIDSample.empiricalMeasure IIDSample.empiricalCDF IIDSample.sampleMean
  rw [Measure.real, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  simp only [Measure.dirac_apply' _ measurableSet_Iic]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  rw [ENNReal.toReal_sum (fun i _ => by
    by_cases h : S.Z i ω ∈ Set.Iic y <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h])]
  apply Finset.sum_congr rfl
  intro i _
  unfold cdfStat
  by_cases h : S.Z i ω ∈ Set.Iic y
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, ENNReal.toReal_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.toReal_zero]

/-- **cdf bridge.**  The cdf of the empirical measure is the empirical cdf:
`cdf νₙ = F̂ₙ`. -/
lemma IIDSample.empiricalMeasure_cdf (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (hn : 0 < n) (ω : Ω) (y : ℝ) :
    cdf (S.empiricalMeasure n ω) y = S.empiricalCDF y n ω := by
  haveI := S.empiricalMeasure_isProbabilityMeasure hn ω
  rw [cdf_eq_real, S.empiricalMeasure_real_Iic hn ω y]

/-! ## Sample quantile -/

/-- The **sample `τ`-quantile** `q̂ₙ(τ) = quantile νₙ τ`, the generalized inverse
of the empirical cdf. -/
noncomputable def IIDSample.sampleQuantile (S : IIDSample Ω ℝ μ P) (τ : ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => quantile (S.empiricalMeasure n ω) τ

/-- **Switching relation.**  For interior `τ ∈ (0,1)` and `0 < n`,
`q̂ₙ(τ) ≤ x ↔ τ ≤ F̂ₙ(x)`. -/
lemma IIDSample.sampleQuantile_le_iff (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (hn : 0 < n) (ω : Ω) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (x : ℝ) :
    S.sampleQuantile τ n ω ≤ x ↔ τ ≤ S.empiricalCDF x n ω := by
  haveI := S.empiricalMeasure_isProbabilityMeasure hn ω
  rw [IIDSample.sampleQuantile, quantile_le_iff hτ0 hτ1, S.empiricalMeasure_cdf hn ω]

/-! ## Monotonicity of the empirical cdf in the argument -/

/-- The empirical cdf is monotone in its real argument `y` (a sum of monotone
lower-ray indicators). -/
lemma IIDSample.empiricalCDF_monotone (S : IIDSample Ω ℝ μ P) (n : ℕ) (ω : Ω) :
    Monotone (fun y => S.empiricalCDF y n ω) := by
  intro y y' hyy'
  unfold IIDSample.empiricalCDF IIDSample.sampleMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  unfold cdfStat
  by_cases h : S.Z i ω ≤ y
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h),
      Set.indicator_of_mem (Set.mem_Iic.mpr (h.trans hyy'))]
  · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic]; exact h)]
    exact cdfStat_nonneg y' _

/-! ## Atom bound (tie-free under an atomless population) -/

/-- **Atom bound.**  Under an atomless population (`Continuous (cdf P)`, i.e. `P`
has no atoms), the sample is a.s. tie-free, so the empirical cdf jumps by exactly
`1/n` at the sample quantile and `τ ≤ F̂ₙ(q̂ₙ) ≤ τ + 1/n`.  Consequently

    |F̂ₙ(q̂ₙ(τ)) − τ| ≤ 1/n        a.s.

This is the only place an atomless-population hypothesis enters the
sample-quantile asymptotics. -/
lemma IIDSample.sampleQuantile_atom_bound [IsProbabilityMeasure μ] (S : IIDSample Ω ℝ μ P)
    (hcont : Continuous (fun y => cdf P y))
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∀ᵐ ω ∂μ, |S.empiricalCDF (S.sampleQuantile τ n ω) n ω - τ| ≤ (n : ℝ)⁻¹ := by
  -- `P` is atomless: `Continuous (cdf P)` ⇒ no jumps ⇒ every singleton is null.
  haveI hP : IsProbabilityMeasure P := by
    rw [← S.law]
    exact MeasureTheory.Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  haveI hPna : NoAtoms P := by
    refine ⟨fun x => ?_⟩
    have heq : P = (cdf P).measure := (measure_cdf P).symm
    rw [heq, StieltjesFunction.measure_singleton,
      ContinuousWithinAt.leftLim_eq (hcont.continuousWithinAt), sub_self, ENNReal.ofReal_zero]
  -- Each coordinate has law `P`.
  have hlaw : ∀ i : ℕ, μ.map (S.Z i) = P := fun i => (S.identDist i).map_eq.symm.trans S.law
  -- Pairwise a.s. distinctness: `μ{Zᵢ = Zⱼ} = 0` for `i ≠ j` (independence + atomless law).
  have hpair : ∀ i j : ℕ, i ≠ j → μ {ω | S.Z i ω = S.Z j ω} = 0 := by
    intro i j hij
    have hind : IndepFun (S.Z i) (S.Z j) μ := S.indep.indepFun hij
    have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
      measurableSet_eq_fun measurable_fst measurable_snd
    have hpre : {ω | S.Z i ω = S.Z j ω}
        = (fun ω => (S.Z i ω, S.Z j ω)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := rfl
    rw [hpre, ← Measure.map_apply ((S.meas i).prodMk (S.meas j)) hmeas,
      (indepFun_iff_map_prod_eq_prod_map_map
        (S.meas i).aemeasurable (S.meas j).aemeasurable).mp hind,
      hlaw i, hlaw j, Measure.measure_prod_null hmeas]
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hsing : (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = {x} := by ext y; simp [eq_comm]
    simp [hsing, measure_singleton]
  -- Assemble into one a.s. tie-free event on `range n`.
  have hae : ∀ᵐ ω ∂μ, ∀ i ∈ (Finset.range n : Set ℕ),
      ∀ j ∈ (Finset.range n : Set ℕ), i ≠ j → S.Z i ω ≠ S.Z j ω := by
    rw [ae_ball_iff (Set.to_countable _)]
    intro i _
    rw [ae_ball_iff (Set.to_countable _)]
    intro j _
    by_cases hij : i = j
    · exact ae_of_all _ (fun ω hne => absurd hij hne)
    · rw [ae_iff]
      have heqset : {ω | ¬ (i ≠ j → S.Z i ω ≠ S.Z j ω)} = {ω | S.Z i ω = S.Z j ω} := by
        ext ω; simp [hij]
      rw [heqset, hpair i j hij]
  -- The empirical-cdf sum counts the sample points below the threshold.
  have hcard : ∀ (x : ℝ) (ω : Ω), ∑ i ∈ Finset.range n, cdfStat x (S.Z i ω)
      = (((Finset.range n).filter (fun i => S.Z i ω ≤ x)).card : ℝ) := by
    intro x ω
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold cdfStat
    by_cases h : S.Z i ω ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h)]; simp [h]
    · rw [Set.indicator_of_notMem (by simpa using h)]; simp [h]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  filter_upwards [hae] with ω haeω
  set q := S.sampleQuantile τ n ω with hq
  -- LOWER bound `τ ≤ F̂ₙ(q)` is deterministic (switching at `x = q`, reflexivity).
  have hlower : τ ≤ S.empiricalCDF q n ω :=
    (S.sampleQuantile_le_iff hn ω hτ0 hτ1 q).mp (le_refl q)
  -- Strict switching: any `x < q` has `F̂ₙ(x) < τ`.
  have hstrict : ∀ x : ℝ, x < q → S.empiricalCDF x n ω < τ := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    exact absurd ((S.sampleQuantile_le_iff hn ω hτ0 hτ1 x).mpr hcon) (not_le.mpr hx)
  -- Abbreviations for the three counts.
  set Cle : ℝ → Finset ℕ :=
    fun x => (Finset.range n).filter (fun i => S.Z i ω ≤ x) with hCle
  set Clt : Finset ℕ := (Finset.range n).filter (fun i => S.Z i ω < q) with hClt
  set Ceq : Finset ℕ := (Finset.range n).filter (fun i => S.Z i ω = q) with hCeq
  -- `F̂ₙ(x) = (Cle x).card / n`.
  have hFcard : ∀ x : ℝ, S.empiricalCDF x n ω = (n : ℝ)⁻¹ * ((Cle x).card : ℝ) := by
    intro x
    rw [IIDSample.empiricalCDF, IIDSample.sampleMean, hcard x ω]
  -- `Cle q = Clt ∪ Ceq`, disjointly: `Zᵢ ≤ q ↔ Zᵢ < q ∨ Zᵢ = q`.
  have hdisj : Disjoint Clt Ceq := by
    rw [hClt, hCeq, Finset.disjoint_filter]
    intro i _ hlt heq; exact absurd heq (ne_of_lt hlt)
  have hunion : Cle q = Clt ∪ Ceq := by
    rw [hCle, hClt, hCeq, ← Finset.filter_or]
    refine Finset.filter_congr (fun i _ => ?_)
    exact ⟨fun h => h.lt_or_eq, fun h => h.elim le_of_lt le_of_eq⟩
  have hcountsplit : (Cle q).card = Clt.card + Ceq.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  -- Tie-free ⇒ at most one index equals `q`.
  have hCeq_le : Ceq.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hCeq, Finset.mem_filter] at ha hb
    by_contra hab
    exact haeω a (by simpa using ha.1) b (by simpa using hb.1) hab (ha.2.trans hb.2.symm)
  -- Strict part: `(Clt.card : ℝ) ≤ n·τ`, via a threshold `x < q` with `Cle x = Clt`.
  have hClt_le : (Clt.card : ℝ) ≤ (n : ℝ) * τ := by
    rcases Finset.eq_empty_or_nonempty Clt with hempty | hne
    · rw [hempty, Finset.card_empty, Nat.cast_zero]; positivity
    · -- `m = max{Zᵢ : Zᵢ < q}`; choose threshold `x = m < q`, then `Cle m = Clt`.
      set T : Finset ℝ := Clt.image (fun i => S.Z i ω) with hT
      have hTne : T.Nonempty := hne.image _
      set m : ℝ := T.max' hTne with hm
      have hmlt : m < q := by
        obtain ⟨a, haT, ham⟩ := Finset.mem_image.mp (T.max'_mem hTne)
        rw [hClt, Finset.mem_filter] at haT
        rw [hm, ← ham]; exact haT.2
      have hCleq : Cle m = Clt := by
        rw [hCle, hClt]
        refine Finset.filter_congr (fun i hi => ?_)
        constructor
        · intro hle; exact lt_of_le_of_lt hle hmlt
        · intro hlt
          refine Finset.le_max' T _ ?_
          rw [hT]
          exact Finset.mem_image.mpr
            ⟨i, by rw [hClt, Finset.mem_filter]; exact ⟨hi, hlt⟩, rfl⟩
      have hlt2 : S.empiricalCDF m n ω < τ := hstrict m hmlt
      rw [hFcard m, hCleq] at hlt2
      -- `(n)⁻¹ * card < τ`  ⟹  `card < n·τ`.
      have hkey := (inv_mul_lt_iff₀ hnR).mp hlt2
      linarith [hkey]
  -- Combine: `n·F̂ₙ(q) = (Cle q).card ≤ n·τ + 1`, so `F̂ₙ(q) ≤ τ + 1/n`.
  have hupper : S.empiricalCDF q n ω ≤ τ + (n : ℝ)⁻¹ := by
    rw [hFcard q, hcountsplit]
    push_cast
    rw [mul_add]
    have h1 : (n : ℝ)⁻¹ * (Clt.card : ℝ) ≤ τ := by
      rw [inv_mul_le_iff₀ hnR]; linarith [hClt_le]
    have h2 : (n : ℝ)⁻¹ * (Ceq.card : ℝ) ≤ (n : ℝ)⁻¹ := by
      have : (Ceq.card : ℝ) ≤ 1 := by exact_mod_cast hCeq_le
      nlinarith [inv_nonneg.mpr hnR.le, this]
    linarith
  rw [abs_le]
  exact ⟨by linarith [inv_nonneg.mpr hnR.le], by linarith⟩

end Causalean.Stat
