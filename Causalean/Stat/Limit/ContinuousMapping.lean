/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Continuous-mapping primitives for convergence in probability

Reusable building blocks for Slutsky / continuous-mapping arguments at the
estimation layer.  All statements are phrased over the project's
`Tendsto_inProb` and `IsLittleOp` wrappers (`Causalean/Stat/Limit/Convergence.lean`).

The headline lemma is `Tendsto_inProb.comp_continuousAt`: if `Yn →_p c` and
`g` is continuous at `c`, then `g ∘ Yn →_p g c`.  The remaining lemmas are
specializations and bookkeeping helpers (`inv`, `sub_const`, `isLittleOp_one`).
-/

import Causalean.Stat.Limit.Convergence
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Matrix

/-! # Continuous Mapping

This file provides continuous-mapping and Slutsky-style primitives for
convergence in probability. The lemmas cover composition with a function
continuous at the probability limit, reciprocals at nonzero limits, centering by
a constant, and small-order bookkeeping.

The main scalar tools are `Tendsto_inProb.comp_continuousAt`,
`Tendsto_inProb.inv`, `Tendsto_inProb.sub_const`, `Tendsto_inProb.sub`,
`Tendsto_inProb.isLittleOp_one`, and `Tendsto_inProb.isBigOp_one`.  The file
also provides finite-dimensional continuous mapping principles
`Tendsto_inProb.pi_comp_continuousAt` and
`Tendsto_inProb.matrix_comp_continuousAt`, which lift entrywise convergence in
probability to continuous functionals of vectors and square matrices. -/

namespace Causalean.Stat

open MeasureTheory Filter Topology

/-- **Continuous mapping for convergence in probability at a point.**
If `Yn →_p c` under `μ` and `g` is continuous at `c`, then
`g ∘ Yn →_p g c`.  Generalizes `Tendsto_inProb.inv` (the case
`g = fun x => 1/x` at a nonzero `c`). -/
theorem Tendsto_inProb.comp_continuousAt
    {Ω : Type*} [MeasurableSpace Ω] {Yn : ℕ → Ω → ℝ} {c : ℝ} {μ : Measure Ω}
    {g : ℝ → ℝ} (hg : ContinuousAt g c)
    (h : Tendsto_inProb Yn (fun _ => c) μ) :
    Tendsto_inProb (fun n ω => g (Yn n ω)) (fun _ => g c) μ := by
  unfold Tendsto_inProb at h ⊢
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  have hev : ∀ᶠ y in 𝓝 c, dist (g y) (g c) < ε :=
    (Metric.tendsto_nhds.mp hg) ε hε
  rcases Metric.eventually_nhds_iff.mp hev with ⟨η, hηpos, hη⟩
  have ht := h η hηpos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  -- `ε ≤ dist (g (Yn n ω)) (g c)` forces `Yn n ω` outside the η-ball at `c`.
  exact le_of_not_gt fun hd => not_le_of_gt (hη hd) hω

/-- Reciprocal continuity for convergence in probability at a nonzero
constant: if `Yn →_p Y₀` with `Y₀ ≠ 0`, then `1 / Yn →_p 1 / Y₀`. -/
theorem Tendsto_inProb.inv
    {Ω : Type*} [MeasurableSpace Ω] {Yn : ℕ → Ω → ℝ} {Y₀ : ℝ} {μ : Measure Ω}
    (h : Tendsto_inProb Yn (fun _ => Y₀) μ) (hY₀ : Y₀ ≠ 0) :
    Tendsto_inProb (fun n ω => 1 / Yn n ω) (fun _ => 1 / Y₀) μ := by
  unfold Tendsto_inProb at h ⊢
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  have hcont : ContinuousAt (fun x : ℝ => x⁻¹) Y₀ := continuousAt_inv₀ hY₀
  have hev : ∀ᶠ y in 𝓝 Y₀, dist (y⁻¹) (Y₀⁻¹) < ε :=
    (Metric.tendsto_nhds.mp hcont) ε hε
  rcases Metric.eventually_nhds_iff.mp hev with ⟨η, hηpos, hη⟩
  have ht := h η hηpos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hω' : ε ≤ dist (Yn n ω)⁻¹ Y₀⁻¹ := by
    simpa [one_div] using hω
  exact le_of_not_gt fun hd => not_le_of_gt (hη hd) hω'

/-- Center a convergence-in-probability statement around a constant limit:
if `Yn →_p Y₀`, then `Yn - Y₀ →_p 0`. -/
theorem Tendsto_inProb.sub_const
    {Ω : Type*} [MeasurableSpace Ω] {Yn : ℕ → Ω → ℝ} {Y₀ : ℝ} {μ : Measure Ω}
    (h : Tendsto_inProb Yn (fun _ => Y₀) μ) :
    Tendsto_inProb (fun n ω => Yn n ω - Y₀) (fun _ => 0) μ := by
  unfold Tendsto_inProb at h ⊢
  rw [tendstoInMeasure_iff_norm] at h ⊢
  intro ε hε
  simpa [Pi.sub_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h ε hε

/-- **Difference of convergent-in-probability sequences.**  If `Xn →_p a` and
`Yn →_p b` (both to constant limits), then `Xn − Yn →_p a − b`.  Standard
ε/2-union-bound argument; the analogue of `TendstoInMeasure.sub`, which Mathlib
does not currently provide for the constant-limit case. -/
theorem Tendsto_inProb.sub
    {Ω : Type*} [MeasurableSpace Ω] {Xn Yn : ℕ → Ω → ℝ} {a b : ℝ}
    {μ : Measure Ω}
    (hX : Tendsto_inProb Xn (fun _ => a) μ)
    (hY : Tendsto_inProb Yn (fun _ => b) μ) :
    Tendsto_inProb (fun n ω => Xn n ω - Yn n ω) (fun _ => a - b) μ := by
  unfold Tendsto_inProb at hX hY ⊢
  rw [tendstoInMeasure_iff_norm] at hX hY ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hupper :
      Tendsto
        (fun n => μ {ω | ε / 2 ≤ ‖Xn n ω - a‖} + μ {ω | ε / 2 ≤ ‖Yn n ω - b‖})
        atTop (𝓝 0) := by
    simpa using (hX (ε / 2) hhalf).add (hY (ε / 2) hhalf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le _) ?_
  intro n
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hω
  have heq : Xn n ω - Yn n ω - (a - b) = (Xn n ω - a) - (Yn n ω - b) := by ring
  rw [heq] at hω
  rcases le_or_gt (ε / 2) |Xn n ω - a| with h1 | h1
  · exact Or.inl (by simpa [Set.mem_setOf_eq, Real.norm_eq_abs] using h1)
  · refine Or.inr ?_
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
    by_contra h2
    push_neg at h2
    have htri : |(Xn n ω - a) - (Yn n ω - b)| < ε := by
      calc |(Xn n ω - a) - (Yn n ω - b)|
            ≤ |Xn n ω - a| + |Yn n ω - b| := abs_sub _ _
        _ < ε / 2 + ε / 2 := add_lt_add h1 h2
        _ = ε := by ring
    linarith

/-- Convergence in probability to zero implies `o_p(1)`: if `Yn →_p 0`,
then `Yn` is `IsLittleOp` of the constant-one rate. -/
theorem Tendsto_inProb.isLittleOp_one
    {Ω : Type*} [MeasurableSpace Ω] {Yn : ℕ → Ω → ℝ} {μ : Measure Ω}
    (h : Tendsto_inProb Yn (fun _ => 0) μ) :
    IsLittleOp Yn (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  unfold Tendsto_inProb at h
  rw [tendstoInMeasure_iff_norm] at h
  have ht := h ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hle : ε ≤ |Yn n ω| := le_of_lt (by simpa using hω)
  simpa [Real.norm_eq_abs] using hle

/-- **In-probability tightness.**  A sequence converging in probability to a
constant is bounded in probability: `Xₙ →ₚ c ⟹ Xₙ = O_p(1)`. -/
theorem Tendsto_inProb.isBigOp_one
    {Ω : Type*} [MeasurableSpace Ω] {Xn : ℕ → Ω → ℝ} {c : ℝ} {μ : Measure Ω}
    (h : Tendsto_inProb Xn (fun _ => c) μ) :
    IsBigOp Xn (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  refine ⟨|c| + 1, ?_⟩
  unfold Tendsto_inProb at h
  rw [tendstoInMeasure_iff_norm] at h
  have ht := h 1 one_pos
  have hlim :
      Filter.limsup (fun n => μ {ω | (1 : ℝ) ≤ ‖Xn n ω - c‖}) Filter.atTop = 0 :=
    ht.limsup_eq
  calc
    Filter.limsup (fun n => μ {ω | (|c| + 1) * (fun _ => (1 : ℝ)) n < |Xn n ω|})
        Filter.atTop
        ≤ Filter.limsup (fun n => μ {ω | (1 : ℝ) ≤ ‖Xn n ω - c‖}) Filter.atTop := by
          refine Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_)
          intro n
          apply measure_mono
          intro ω hω
          simp only [Set.mem_setOf_eq, mul_one] at hω ⊢
          rw [Real.norm_eq_abs]
          have htri := abs_sub_abs_le_abs_sub (Xn n ω) c
          linarith
    _ = 0 := hlim
    _ ≤ ENNReal.ofReal ε := zero_le _

set_option linter.unusedFintypeInType false

/-- **Finite-Pi continuous mapping in probability.**  If every coordinate of a
finite-dimensional random vector converges in probability to the corresponding
constant coordinate, and `g` is continuous at the limiting vector, then
`g(Yₙ) →ₚ g(c)`. -/
theorem Tendsto_inProb.pi_comp_continuousAt
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {Yn : ℕ → Ω → (ι → ℝ)} {c : ι → ℝ} {g : (ι → ℝ) → ℝ}
    (hg : ContinuousAt g c)
    (h : ∀ i, Tendsto_inProb (fun n ω => Yn n ω i) (fun _ => c i) μ) :
    Tendsto_inProb (fun n ω => g (Yn n ω)) (fun _ => g c) μ := by
  classical
  unfold Tendsto_inProb
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hg) ε hε
  rcases Metric.eventually_nhds_iff.mp hev with ⟨η, hηpos, hη⟩
  let δ : ℝ := η / 2
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδpos
  have hδ_lt_eta : δ < η := by dsimp [δ]; linarith
  let Bad : ℕ → ι → Set Ω := fun n i => {ω | δ ≤ |Yn n ω i - c i|}
  have hentry : ∀ i, Filter.Tendsto (fun n => μ (Bad n i)) Filter.atTop (nhds 0) := by
    intro i
    have hi := h i
    unfold Tendsto_inProb at hi
    rw [tendstoInMeasure_iff_norm] at hi
    have ht := hi δ hδpos
    simpa [Bad, Real.norm_eq_abs] using ht
  have hupper : Filter.Tendsto (fun n => ∑ i, μ (Bad n i)) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_finset_sum (M := ENNReal) (s := (Finset.univ : Finset ι))
        (f := fun i n => μ (Bad n i)) (x := Filter.atTop)
        (a := fun _ => (0 : ENNReal)) (fun i _ => hentry i))
  have hsubset : ∀ n,
      {ω | ε ≤ dist (g (Yn n ω)) (g c)} ⊆ ⋃ i, Bad n i := by
    intro n ω hω
    by_contra hωU
    have hcoord : ∀ i, |Yn n ω i - c i| < δ := by
      intro i
      have hnot : ¬ δ ≤ |Yn n ω i - c i| := by
        intro hb
        exact hωU (Set.mem_iUnion.2 ⟨i, hb⟩)
      exact not_le.mp hnot
    have hdist_le : dist (Yn n ω) c ≤ δ := by
      refine (dist_pi_le_iff hδ_nonneg).2 ?_
      intro i
      simpa [Real.dist_eq] using le_of_lt (hcoord i)
    have hdist : dist (Yn n ω) c < η := lt_of_le_of_lt hdist_le hδ_lt_eta
    exact not_le_of_gt (hη hdist) hω
  have hmeasure_union : ∀ n,
      μ (⋃ i, Bad n i) ≤ ∑ i, μ (Bad n i) := by
    intro n
    exact MeasureTheory.measure_iUnion_fintype_le μ (fun i => Bad n i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le _) ?_
  intro n
  calc
    μ {ω | ε ≤ dist (g (Yn n ω)) (g c)} ≤ μ (⋃ i, Bad n i) :=
      measure_mono (hsubset n)
    _ ≤ ∑ i, μ (Bad n i) := hmeasure_union n

/-- **Matrix continuous mapping in probability.**  If every entry of the random
matrix `Mₙ` converges in probability to the corresponding entry of `M₀`, and
`g` is continuous at `M₀`, then `g(Mₙ) →ₚ g(M₀)`. -/
theorem Tendsto_inProb.matrix_comp_continuousAt
    {Ω K : Type*} [MeasurableSpace Ω] [Fintype K] {μ : Measure Ω}
    {Mn : ℕ → Ω → Matrix K K ℝ} {M₀ : Matrix K K ℝ} {g : Matrix K K ℝ → ℝ}
    (hg : ContinuousAt g M₀)
    (h : ∀ i j, Tendsto_inProb (fun n ω => Mn n ω i j) (fun _ => M₀ i j) μ) :
    Tendsto_inProb (fun n ω => g (Mn n ω)) (fun _ => g M₀) μ := by
  classical
  let reindex : ((K × K) → ℝ) → Matrix K K ℝ :=
    fun y => Matrix.of fun i j => y (i, j)
  have hreindex_cont : Continuous reindex := by
    dsimp [reindex]
    exact continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  have hpoint : reindex (fun p : K × K => M₀ p.1 p.2) = M₀ := by
    ext i j
    simp [reindex]
  have hg' : ContinuousAt (fun y : (K × K) → ℝ => g (reindex y))
      (fun p : K × K => M₀ p.1 p.2) := by
    have hg_at : ContinuousAt g (reindex (fun p : K × K => M₀ p.1 p.2)) := by
      simpa [hpoint] using hg
    exact hg_at.comp' hreindex_cont.continuousAt
  have hpi := Tendsto_inProb.pi_comp_continuousAt
    (Ω := Ω) (ι := K × K) (μ := μ)
    (Yn := fun n ω p => Mn n ω p.1 p.2)
    (c := fun p => M₀ p.1 p.2)
    (g := fun y : (K × K) → ℝ => g (reindex y)) hg'
    (fun p => h p.1 p.2)
  simpa [reindex, Matrix.of_apply] using hpi

end Causalean.Stat
