/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Glivenko–Cantelli: uniform laws of large numbers

Two sufficient conditions for the (weak) Glivenko–Cantelli property
`GlivenkoCantelli S f` of a function class `f : ι → X → ℝ` under an
`Causalean.Stat.IIDSample`:

* `glivenkoCantelli_of_fintype` — a **finite** class of integrable functions is
  Glivenko–Cantelli.  Immediate from the pointwise weak law of large numbers
  (`IIDSample.sampleMean_tendsto_inProb`) and a union bound.

* `glivenkoCantelli_of_hasL1Bracketing` — a class with finite `L¹(P)` brackets
  of arbitrarily small width is Glivenko-Cantelli.  The bracketing argument:
  each member is sandwiched on a common full-measure support in a bracket whose
  absolute endpoint gap has integral `≤ ε/2`, so outside the null event that a
  sample point leaves the support, its empirical deviation is controlled by the
  deviations of the finitely many bracket endpoints plus `ε/2`; the endpoint
  deviations vanish by the finite case.

This is the uniform-convergence engine consumed by `MEstimatorConsistency.lean`
(Newey–McFadden consistency of extremum estimators).
-/

import Causalean.Stat.EmpiricalProcess.Basic
import Causalean.Stat.Limit.WLLN

/-!
This file proves two Glivenko-Cantelli uniform laws for the predicate defined in
`EmpiricalProcess/Basic.lean`.  The theorem `glivenkoCantelli_of_fintype`
handles finite integrable classes by a union bound and the weak law of large
numbers, while `glivenkoCantelli_of_hasL1Bracketing` upgrades finite
`L¹(P)`-bracketing numbers into a uniform law over an arbitrary indexed class.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## Shared helpers -/

/-- Squeeze a sequence of measures to `0` by a dominating sequence that tends to
`0`. -/
private theorem tendsto_measure_zero_of_le {E : ℕ → Set Ω} {g : ℕ → ℝ≥0∞}
    (hle : ∀ n, μ (E n) ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => μ (E n)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun _ => zero_le _) (Eventually.of_forall hle)

/-- Transfer `P`-integrability of a measurable statistic to `μ`-integrability of
its pullback along the first sample point. -/
private theorem integrable_pullback (S : IIDSample Ω X μ P) {g : X → ℝ}
    (hgi : Integrable g P) :
    Integrable (fun ω => g (S.Z 0 ω)) μ := by
  have h : Integrable g (μ.map (S.Z 0)) := by rw [S.law]; exact hgi
  simpa [Function.comp_def] using h.comp_measurable (S.meas 0)

/-- Single-statistic empirical deviation tends to `0` in probability (the
pointwise weak law of large numbers, rephrased with `|·|` instead of `dist`). -/
private theorem dev_tendsto_zero (S : IIDSample Ω X μ P) [IsProbabilityMeasure P]
    {g : X → ℝ} (hg : Measurable g)
    (hgi : Integrable (fun ω => g (S.Z 0 ω)) μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε ≤ |S.sampleMean g n ω - ∫ x, g x ∂P|})
      atTop (𝓝 0) := by
  have h : Tendsto_inProb (S.sampleMean g) (fun _ => ∫ x, g x ∂P) μ :=
    S.sampleMean_tendsto_inProb hg hgi
  -- `Tendsto_inProb` is `edist`/`ℝ≥0∞`-valued; bridge to the real `|·|` event.
  have h2 := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  have hset : ∀ n,
      {ω | ENNReal.ofReal ε ≤ edist (S.sampleMean g n ω) ((fun _ => ∫ x, g x ∂P) ω)}
        = {ω | ε ≤ |S.sampleMean g n ω - ∫ x, g x ∂P|} := by
    intro n; ext ω
    simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  simp_rw [hset] at h2
  exact h2

/-- Monotonicity of the sample mean in the statistic on sample paths that stay
inside the set where the pointwise comparison is known. -/
private theorem sampleMean_mono_on (S : IIDSample Ω X μ P) {g h : X → ℝ}
    {support : Set X} (hgh : ∀ x ∈ support, g x ≤ h x)
    {n : ℕ} {ω : Ω} (hω : ∀ k ∈ Finset.range n, S.Z k ω ∈ support) :
    S.sampleMean g n ω ≤ S.sampleMean h n ω := by
  unfold IIDSample.sampleMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun i hi => hgh (S.Z i ω) (hω i hi))

/-! ## Finite-class Glivenko–Cantelli -/

/-- **A finite class of integrable functions is Glivenko–Cantelli.**

For a finite index type `ι` with each `f i` measurable and `P`-integrable, the
worst-case empirical-mean deviation over the class converges to `0` in
probability.  Proof: union bound over the finitely many coordinates, each
vanishing by the weak law of large numbers. -/
theorem glivenkoCantelli_of_fintype [Finite ι] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (f : ι → X → ℝ)
    (hmeas : ∀ i, Measurable (f i))
    (hint : ∀ i, Integrable (f i) P) :
    GlivenkoCantelli S f := by
  letI := Fintype.ofFinite ι
  intro ε hε
  have hcoord : ∀ i, Tendsto
      (fun n => μ {ω | ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|})
      atTop (𝓝 0) :=
    fun i => dev_tendsto_zero S (hmeas i)
      (integrable_pullback S (hint i)) hε
  have hsum : Tendsto
      (fun n => ∑ i, μ {ω | ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|})
      atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset ι) (fun i _ => hcoord i)
    simpa using this
  refine tendsto_measure_zero_of_le (fun n => ?_) hsum
  calc μ {ω | ∃ i, ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|}
      = μ (⋃ i, {ω | ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|}) := by
        rw [Set.iUnion_setOf]
    _ ≤ ∑' i, μ {ω | ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|} :=
        measure_iUnion_le _
    _ = ∑ i, μ {ω | ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|} :=
        tsum_fintype _

/-! ## Bracketing Glivenko–Cantelli -/

/-- **A class with finite `L¹(P)` brackets of arbitrarily small width is
Glivenko-Cantelli.**

Given `ε > 0`, take a finite `ε/2` bracketing in the sense of `HasL1Bracketing`.
Each class member `f i` lies in a bracket `[lo j, hi j]` on a common full-measure
support, and each bracket has absolute `L¹(P)` width `∫ |hi_j − lo_j| dP ≤ ε/2`.
On sample paths whose observations stay inside the support, the sandwiching gives

    Pₙ lo_j ≤ Pₙ f_i ≤ Pₙ hi_j,    ∫ lo_j ≤ ∫ f_i ≤ ∫ hi_j,

so `|Pₙ f_i − P f_i| ≤ max(|Pₙ hi_j − P hi_j|, |Pₙ lo_j − P lo_j|) + ε/2`.
The exceptional event where some sampled observation leaves the support has
probability zero, and the remaining bad event is contained in the union of the
`2m` endpoint-deviation events, each of which vanishes by the finite case. -/
theorem glivenkoCantelli_of_hasL1Bracketing [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (f : ι → X → ℝ)
    (hmeas : ∀ i, Measurable (f i))
    (hbr : HasL1Bracketing f P) :
    GlivenkoCantelli S f := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨B⟩ := hbr (ε / 2) hε2
  -- endpoint deviations vanish in probability
  have hhi : ∀ j, Tendsto
      (fun n => μ {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
      atTop (𝓝 0) :=
    fun j => dev_tendsto_zero S (B.hi_meas j)
      (integrable_pullback S (B.hi_int j)) hε2
  have hlo : ∀ j, Tendsto
      (fun n => μ {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|})
      atTop (𝓝 0) :=
    fun j => dev_tendsto_zero S (B.lo_meas j)
      (integrable_pullback S (B.lo_int j)) hε2
  -- each class member is integrable (sandwiched between integrable endpoints)
  have hf_int : ∀ i, Integrable (f i) P := by
    intro i
    refine Integrable.mono'
      (g := fun x => |B.lo (B.assign i) x| + |B.hi (B.assign i) x|)
      ((B.lo_int _).abs.add (B.hi_int _).abs) (hmeas i).aestronglyMeasurable
      (B.support_ae.mono fun x hx => ?_)
    rw [Real.norm_eq_abs]
    have h1 := B.lo_le i x hx
    have h2 := B.le_hi i x hx
    rcases le_total 0 (f i x) with hpos | hneg
    · rw [abs_of_nonneg hpos]
      calc f i x ≤ |B.hi (B.assign i) x| := le_trans h2 (le_abs_self _)
        _ ≤ _ := le_add_of_nonneg_left (abs_nonneg _)
    · rw [abs_of_nonpos hneg]
      calc -f i x ≤ |B.lo (B.assign i) x| :=
            le_trans (neg_le_neg h1) (neg_le_abs _)
        _ ≤ _ := le_add_of_nonneg_right (abs_nonneg _)
  -- dominating sequence: the total endpoint-deviation probability
  have hgtendsto : Tendsto
      (fun n =>
        (∑ j, μ {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
        + (∑ j, μ {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|}))
      atTop (𝓝 0) := by
    have h1 := tendsto_finset_sum (Finset.univ : Finset (Fin B.m))
      (fun j _ => hhi j)
    have h2 := tendsto_finset_sum (Finset.univ : Finset (Fin B.m))
      (fun j _ => hlo j)
    have h12 := h1.add h2
    simpa using h12
  refine tendsto_measure_zero_of_le (fun n => ?_) hgtendsto
  -- the bad event is covered by the endpoint events
  have hsupport_fail_zero :
      μ {ω | ∃ k : Fin n, S.Z k.1 ω ∉ B.support} = 0 := by
    apply le_antisymm ?_ (zero_le _)
    calc μ {ω | ∃ k : Fin n, S.Z k.1 ω ∉ B.support}
        = μ (⋃ k : Fin n, {ω | S.Z k.1 ω ∉ B.support}) := by
          rw [Set.iUnion_setOf]
      _ ≤ ∑' k : Fin n, μ {ω | S.Z k.1 ω ∉ B.support} :=
          measure_iUnion_le _
      _ = 0 := by
          have hzero : ∀ k : Fin n, μ {ω | S.Z k.1 ω ∉ B.support} = 0 := by
            intro k
            have hmap_zero : (μ.map (S.Z k.1)) B.supportᶜ = 0 := by
              simpa [S.map_eq k.1] using MeasureTheory.ae_iff.mp B.support_ae
            rw [← hmap_zero]
            rw [Measure.map_apply_of_aemeasurable (S.meas k.1).aemeasurable
              B.support_meas.compl]
            rfl
          simp [hzero]
  have hsub : {ω | ∃ i, ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|}
      ⊆ {ω | ∃ k : Fin n, S.Z k.1 ω ∉ B.support}
        ∪ ((⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
          ∪ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|})) := by
    intro ω hω
    obtain ⟨i, hi⟩ := hω
    set j := B.assign i with hj
    by_cases hbad : ∃ k : Fin n, S.Z k.1 ω ∉ B.support
    · exact Or.inl hbad
    refine Or.inr ?_
    have hω_support : ∀ k ∈ Finset.range n, S.Z k ω ∈ B.support := by
      intro k hk
      by_contra hnot
      exact hbad ⟨⟨k, Finset.mem_range.mp hk⟩, hnot⟩
    have hsm_lo : S.sampleMean (B.lo j) n ω ≤ S.sampleMean (f i) n ω :=
      sampleMean_mono_on S (support := B.support)
        (fun x hx => by simpa [j, hj] using B.lo_le i x hx) hω_support
    have hsm_hi : S.sampleMean (f i) n ω ≤ S.sampleMean (B.hi j) n ω :=
      sampleMean_mono_on S (support := B.support)
        (fun x hx => by simpa [j, hj] using B.le_hi i x hx) hω_support
    have hint_lo : ∫ x, B.lo j x ∂P ≤ ∫ x, f i x ∂P :=
      integral_mono_ae (B.lo_int j) (hf_int i)
        (B.support_ae.mono fun x hx => by simpa [j, hj] using B.lo_le i x hx)
    have hint_hi : ∫ x, f i x ∂P ≤ ∫ x, B.hi j x ∂P :=
      integral_mono_ae (hf_int i) (B.hi_int j)
        (B.support_ae.mono fun x hx => by simpa [j, hj] using B.le_hi i x hx)
    have hmesh : ∫ x, B.hi j x ∂P - ∫ x, B.lo j x ∂P ≤ ε / 2 := by
      rw [← integral_sub (B.hi_int j) (B.lo_int j)]
      refine le_trans ?_ (B.mesh j)
      exact integral_mono_ae ((B.hi_int j).sub (B.lo_int j))
        (((B.hi_int j).sub (B.lo_int j)).abs)
        (Eventually.of_forall fun x => le_abs_self _)
    rcases le_abs.mp hi with hA | hB
    · -- upper deviation: hits the `hi` bracket endpoint
      refine Or.inl (Set.mem_iUnion.mpr ⟨j, ?_⟩)
      simp only [Set.mem_setOf_eq]
      refine le_abs.mpr (Or.inl ?_)
      linarith
    · -- lower deviation: hits the `lo` bracket endpoint
      refine Or.inr (Set.mem_iUnion.mpr ⟨j, ?_⟩)
      simp only [Set.mem_setOf_eq]
      refine le_abs.mpr (Or.inr ?_)
      linarith
  calc μ {ω | ∃ i, ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|}
      ≤ μ ({ω | ∃ k : Fin n, S.Z k.1 ω ∉ B.support}
          ∪ ((⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
            ∪ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|}))) :=
        measure_mono hsub
    _ ≤ μ {ω | ∃ k : Fin n, S.Z k.1 ω ∉ B.support}
          + (μ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
            + μ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|})) := by
        refine le_trans (measure_union_le _ _) ?_
        gcongr
        exact measure_union_le _ _
    _ = μ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
          + μ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|}) := by
        rw [hsupport_fail_zero]
        simp
    _ ≤ (∑ j, μ {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
          + (∑ j, μ {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|}) := by
        gcongr
        · calc μ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|})
              ≤ ∑' j, μ {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|} :=
                measure_iUnion_le _
            _ = ∑ j, μ {ω | ε / 2 ≤ |S.sampleMean (B.hi j) n ω - ∫ x, B.hi j x ∂P|} :=
                tsum_fintype _
        · calc μ (⋃ j, {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|})
              ≤ ∑' j, μ {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|} :=
                measure_iUnion_le _
            _ = ∑ j, μ {ω | ε / 2 ≤ |S.sampleMean (B.lo j) n ω - ∫ x, B.lo j x ∂P|} :=
                tsum_fintype _

end Causalean.Stat
