/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.Moments.Variance
import Causalean.Mathlib.Probability.ConvergingTogether.CharFunBound

/-!
# Moments and deviation bounds for i.i.d. empirical means

This module gives the exact mean and variance of an i.i.d. empirical average,
as well as scalar and finite-dimensional `L²` and `L¹` deviation bounds under
the corresponding moment assumptions.

The sample index is an arbitrary nonempty finite type; the sample size is then
its cardinality.  Each result also has a `Fin n` specialisation under the
unprimed classical name, so that callers indexing a sample by a `Finset`
subtype or by a fold of a cross-fitting partition can use the same lemmas.

The file also records the integrability / `L²`-membership side conditions of the
Euclidean deviation bound as public lemmas, since they are needed whenever the
bound is combined with another integral estimate.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The Euclidean length of a finite real-valued vector is no greater than the sum of the
absolute values of its components. -/
lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Real.sqrt (∑ i, (v i) ^ 2) ≤ ∑ i, |v i| := by
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => |v i|) (fun _ _ => abs_nonneg _)

/-! ### Generic Euclidean-norm side conditions -/

/-- The Euclidean length of a finite family of integrable real functions is itself integrable.

This is the explicit `√(Σ vᵢ²)` counterpart of Mathlib's `integrable_pi_iff`, which instead
governs the supremum norm on a finite product of normed spaces. -/
theorem integrable_euclidean_of_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    (v : Ω → ι → ℝ) (hv : ∀ i, Integrable (fun ω => v ω i) μ) :
    Integrable (fun ω => Real.sqrt (∑ i, (v ω i) ^ 2)) μ := by
  have hsum : Integrable (fun ω => ∑ i, |v ω i|) μ :=
    integrable_finset_sum _ fun i _ => (hv i).abs
  have hmeas : AEStronglyMeasurable (fun ω => Real.sqrt (∑ i, (v ω i) ^ 2)) μ := by
    fun_prop
  refine hsum.mono' hmeas (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_sum_sq_le_sum_abs (v ω)

/-- The Euclidean length of a finite family of square-integrable real functions is itself
square-integrable. -/
theorem memLp_two_sqrt_sum_sq
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {Y : ι → Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 μ) :
    MemLp (fun ω => Real.sqrt (∑ k, (Y k ω) ^ 2)) 2 μ := by
  have hsum_int : Integrable (fun ω => ∑ k, (Y k ω) ^ 2) μ :=
    integrable_finset_sum _ fun k _ => (hY k).integrable_sq
  have hR_ae : AEStronglyMeasurable (fun ω => Real.sqrt (∑ k, (Y k ω) ^ 2)) μ :=
    hsum_int.aemeasurable.sqrt.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hR_ae).2
  convert hsum_int using 1
  funext ω
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-! ### Deviation bounds indexed by an arbitrary finite sample index -/

/-- The mean squared error of a square-integrable scalar sample average from independent,
identically distributed observations is at most the population second moment divided by the
sample size.

The sample is indexed by an arbitrary finite type, whose cardinality plays the role of
the sample size. -/
theorem iid_mean_sq_le_fintype {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 μ) :
    ∫ s, ((Fintype.card ι : ℝ)⁻¹ * (∑ i : ι, ξ (s i)) - ∫ ω, ξ ω ∂μ) ^ 2
        ∂(Measure.pi fun _ : ι => μ) ≤
      (∫ ω, (ξ ω) ^ 2 ∂μ) / (Fintype.card ι : ℝ) := by
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  let P : Measure (ι → Ω) := Measure.pi fun _ : ι => μ
  let X : (ι → Ω) → ℝ := fun s => ∑ i : ι, ξ (s i)
  have hXLp : MemLp X 2 P := by
    simpa [X, P] using memLp_finset_sum Finset.univ fun i _ =>
      hξ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)
  have hmean : ∫ s, (Fintype.card ι : ℝ)⁻¹ * X s ∂P = ∫ ω, ξ ω ∂μ := by
    rw [integral_const_mul]
    change (Fintype.card ι : ℝ)⁻¹ * ∫ s, ∑ i : ι, ξ (s i) ∂(Measure.pi fun _ : ι => μ) = _
    have hsum_integral := integral_finset_sum Finset.univ fun i _ =>
      (measurePreserving_eval (fun _ : ι => μ) i).integrable_comp_of_integrable
        (hξ.integrable (by norm_num))
    rw [show (∫ s, ∑ i : ι, ξ (s i) ∂(Measure.pi fun _ : ι => μ)) =
        ∑ i : ι, ∫ s, ξ (s i) ∂(Measure.pi fun _ : ι => μ) by
      simpa using hsum_integral]
    have hcoord (i : ι) :
        ∫ s, ξ (s i) ∂(Measure.pi fun _ : ι => μ) = ∫ ω, ξ ω ∂μ :=
      integral_comp_eval (μ := fun _ : ι => μ) (i := i) hξ.aestronglyMeasurable
    simp_rw [hcoord]
    simp [hcard]
  calc
    ∫ s, ((Fintype.card ι : ℝ)⁻¹ * (∑ i : ι, ξ (s i)) - ∫ ω, ξ ω ∂μ) ^ 2 ∂P =
        ProbabilityTheory.variance (fun s => (Fintype.card ι : ℝ)⁻¹ * X s) P := by
          rw [ProbabilityTheory.variance_eq_integral]
          · simp only [hmean]
            rfl
          · exact hXLp.const_mul (Fintype.card ι : ℝ)⁻¹ |>.aemeasurable
    _ = ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ProbabilityTheory.variance X P := by
      exact ProbabilityTheory.variance_const_mul _ _ _
    _ = ((Fintype.card ι : ℝ)⁻¹) ^ 2 *
        (∑ _i : ι, ProbabilityTheory.variance ξ μ) := by
      congr 1
      change ProbabilityTheory.variance (fun s => ∑ i : ι, ξ (s i))
          (Measure.pi fun _ : ι => μ) = _
      calc
        ProbabilityTheory.variance (fun s => ∑ i : ι, ξ (s i))
            (Measure.pi fun _ : ι => μ) =
            ProbabilityTheory.variance (∑ i : ι, fun s => ξ (s i))
              (Measure.pi fun _ : ι => μ) := by
                congr 1
                funext s
                simp
        _ = _ := ProbabilityTheory.variance_sum_pi (fun _ : ι => hξ)
    _ ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 *
        (∑ _i : ι, ∫ ω, (ξ ω) ^ 2 ∂μ) := by
      gcongr
      exact ProbabilityTheory.variance_le_expectation_sq hξ.aestronglyMeasurable
    _ = (∫ ω, (ξ ω) ^ 2 ∂μ) / (Fintype.card ι : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

/-- The mean absolute error of a square-integrable scalar sample average from independent,
identically distributed observations is at most the square root of the population second moment
divided by the sample size.

The sample is indexed by an arbitrary nonempty finite type, whose cardinality plays the role of
the sample size. -/
theorem iid_mean_abs_le_fintype {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 μ) :
    ∫ s, |(Fintype.card ι : ℝ)⁻¹ * (∑ i : ι, ξ (s i)) - ∫ ω, ξ ω ∂μ|
        ∂(Measure.pi fun _ : ι => μ) ≤
      Real.sqrt ((∫ ω, (ξ ω) ^ 2 ∂μ) / (Fintype.card ι : ℝ)) := by
  let P : Measure (ι → Ω) := Measure.pi fun _ : ι => μ
  let Y : (ι → Ω) → ℝ := fun s =>
    (Fintype.card ι : ℝ)⁻¹ * (∑ i : ι, ξ (s i)) - ∫ ω, ξ ω ∂μ
  have hYLp : MemLp Y 2 P := by
    apply MemLp.sub (MemLp.const_mul (by
      simpa [P] using memLp_finset_sum Finset.univ fun i _ =>
        hξ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)) _)
    exact memLp_const _
  exact (ConvergingTogether.integral_abs_le_sqrt_integral_sq P Y hYLp).trans
    (by simpa [P, Y] using
      (Real.sqrt_le_sqrt (iid_mean_sq_le_fintype (ι := ι) μ ξ hξ)))

/-- The centred coordinatewise sample averages of finitely many square-integrable statistics form a
square-integrable Euclidean length on the product sample space.

This is the `L²` side condition of the Euclidean deviation bound; it is stated separately so it
can be reused whenever that bound is combined with another integral estimate. -/
theorem memLp_two_iid_mean_euclidean_fintype
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : κ → Ω → ℝ) (hξ : ∀ k, MemLp (ξ k) 2 μ) :
    MemLp (fun s => Real.sqrt (∑ k : κ,
        ((Fintype.card ι : ℝ)⁻¹ * (∑ i : ι, ξ k (s i)) - ∫ ω, ξ k ω ∂μ) ^ 2)) 2
      (Measure.pi fun _ : ι => μ) := by
  refine memLp_two_sqrt_sum_sq (fun k => ?_)
  apply MemLp.sub (MemLp.const_mul (by
    simpa using memLp_finset_sum Finset.univ fun i _ =>
      (hξ k).comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)) _)
  exact memLp_const _

/-- The expected Euclidean error of finitely many square-integrable sample averages from the same
independent, identically distributed sample is controlled by their summed population second
moments and the sample size.

The sample is indexed by an arbitrary nonempty finite type, whose cardinality plays the role of
the sample size. -/
theorem iid_mean_euclidean_abs_le_fintype
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [Fintype κ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : κ → Ω → ℝ) (hξ : ∀ k, MemLp (ξ k) 2 μ) :
    ∫ s, Real.sqrt (∑ k : κ,
        ((Fintype.card ι : ℝ)⁻¹ * (∑ i : ι, ξ k (s i)) - ∫ ω, ξ k ω ∂μ) ^ 2)
        ∂(Measure.pi fun _ : ι => μ) ≤
      Real.sqrt ((∑ k : κ, ∫ ω, (ξ k ω) ^ 2 ∂μ) / (Fintype.card ι : ℝ)) := by
  let P : Measure (ι → Ω) := Measure.pi fun _ : ι => μ
  let Y : κ → (ι → Ω) → ℝ := fun k s =>
    (Fintype.card ι : ℝ)⁻¹ * (∑ i : ι, ξ k (s i)) - ∫ ω, ξ k ω ∂μ
  let R : (ι → Ω) → ℝ := fun s => Real.sqrt (∑ k : κ, (Y k s) ^ 2)
  have hYLp (k : κ) : MemLp (Y k) 2 P := by
    apply MemLp.sub (MemLp.const_mul (by
      simpa [P] using memLp_finset_sum Finset.univ fun i _ =>
        (hξ k).comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)) _)
    exact memLp_const _
  have hRLp : MemLp R 2 P := memLp_two_sqrt_sum_sq hYLp
  calc
    ∫ s, Real.sqrt (∑ k : κ, (Y k s) ^ 2) ∂P ≤
        Real.sqrt (∫ s, (R s) ^ 2 ∂P) :=
      by
        simpa [R, abs_of_nonneg (Real.sqrt_nonneg _)] using
          ConvergingTogether.integral_abs_le_sqrt_integral_sq P R hRLp
    _ = Real.sqrt (∑ k : κ, ∫ s, (Y k s) ^ 2 ∂P) := by
      congr 1
      rw [show (fun s => (R s) ^ 2) = fun s => ∑ k : κ, (Y k s) ^ 2 by
        funext s
        exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact integral_finset_sum _ fun k _ => (hYLp k).integrable_sq
    _ ≤ Real.sqrt ((∑ k : κ, ∫ ω, (ξ k ω) ^ 2 ∂μ) / (Fintype.card ι : ℝ)) := by
      apply Real.sqrt_le_sqrt
      calc
        (∑ k : κ, ∫ s, (Y k s) ^ 2 ∂P) ≤
            ∑ k : κ, (∫ ω, (ξ k ω) ^ 2 ∂μ) / (Fintype.card ι : ℝ) := by
          exact Finset.sum_le_sum fun k _ =>
            iid_mean_sq_le_fintype μ (ξ k) (hξ k)
        _ = _ := by rw [Finset.sum_div]

/-- An average of independent, identically distributed observations has the same expectation as
the population statistic being averaged.

The sample is indexed by an arbitrary nonempty finite type, whose cardinality plays the role of
the sample size. -/
lemma iid_average_integral_fintype
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Integrable F μ) :
    (∫ sample : ι → Ω,
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, F (sample i)
        ∂Measure.pi (fun _ : ι => μ)) =
      ∫ o, F o ∂μ := by
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  rw [integral_const_mul]
  rw [integral_finset_sum]
  · simp_rw [integral_comp_eval
      (μ := fun _ : ι => μ) hF.aestronglyMeasurable]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · intro i _
    exact integrable_comp_eval hF

/-- The variance of an average of independent, identically distributed observations is the
population variance divided by the sample size.

The sample is indexed by an arbitrary nonempty finite type, whose cardinality plays the role of
the sample size. -/
lemma iid_average_variance_fintype
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    ProbabilityTheory.variance
        (fun sample : ι → Ω =>
          (Fintype.card ι : ℝ)⁻¹ * ∑ i, F (sample i))
      (Measure.pi (fun _ : ι => μ)) =
      (Fintype.card ι : ℝ)⁻¹ * ProbabilityTheory.variance F μ := by
  by_cases hι : Nonempty ι
  · letI := hι
    have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    rw [ProbabilityTheory.variance_const_mul]
    have hfun :
        (fun sample : ι → Ω => ∑ i, F (sample i)) =
          ∑ i, fun sample : ι → Ω => F (sample i) := by
      funext sample
      simp
    rw [hfun]
    rw [ProbabilityTheory.variance_sum_pi (fun _ => hF)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have hfun :
        (fun sample : ι → Ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, F (sample i)) = 0 := by
      funext sample
      simp
    rw [hfun, ProbabilityTheory.variance_zero]
    simp

/-! ### `Fin n`-indexed specialisations

These are the classical statements with the sample size given as a natural number.  They are
immediate consequences of the versions above via `Fintype.card_fin`. -/

/-- The mean squared error of a square-integrable scalar sample average of `n` independent,
identically distributed observations is at most the population second moment divided by `n`. -/
theorem iid_mean_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 μ) :
    ∫ s, ((n : ℝ)⁻¹ * (∑ i : Fin n, ξ (s i)) - ∫ ω, ξ ω ∂μ) ^ 2
        ∂(Measure.pi fun _ : Fin n => μ) ≤
      (∫ ω, (ξ ω) ^ 2 ∂μ) / (n : ℝ) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  simpa using iid_mean_sq_le_fintype (ι := Fin n) μ ξ hξ

/-- The mean absolute error of a square-integrable scalar sample average of `n` independent,
identically distributed observations is at most the square root of the population second moment
divided by `n`. -/
theorem iid_mean_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 μ) :
    ∫ s, |(n : ℝ)⁻¹ * (∑ i : Fin n, ξ (s i)) - ∫ ω, ξ ω ∂μ|
        ∂(Measure.pi fun _ : Fin n => μ) ≤
      Real.sqrt ((∫ ω, (ξ ω) ^ 2 ∂μ) / (n : ℝ)) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  simpa using iid_mean_abs_le_fintype (ι := Fin n) μ ξ hξ

/-- For [a strictly positive sample size `n`](hyp:hn) and [finitely many square-integrable
real-valued statistics indexed by `k`](hyp:hξ), each observed on the same `n`-point independent,
identically distributed sample, [the expected Euclidean norm of the vector of centered sample
averages — one coordinate per statistic — is at most the square root of the sum of the population
second moments divided by `n`](goal). -/
theorem iid_mean_euclidean_abs_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (ξ : ι → Ω → ℝ) (hξ : ∀ k, MemLp (ξ k) 2 μ) :
    ∫ s, Real.sqrt (∑ k : ι,
        ((n : ℝ)⁻¹ * (∑ i : Fin n, ξ k (s i)) - ∫ ω, ξ k ω ∂μ) ^ 2)
        ∂(Measure.pi fun _ : Fin n => μ) ≤
      Real.sqrt ((∑ k : ι, ∫ ω, (ξ k ω) ^ 2 ∂μ) / (n : ℝ)) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  simpa using
    iid_mean_euclidean_abs_le_fintype (ι := Fin n) (κ := ι) μ ξ hξ

/-- The centred coordinatewise sample averages of finitely many square-integrable statistics over an
`n`-point independent, identically distributed sample form a square-integrable Euclidean
length. -/
theorem memLp_two_iid_mean_euclidean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (ξ : ι → Ω → ℝ) (hξ : ∀ k, MemLp (ξ k) 2 μ) :
    MemLp (fun s => Real.sqrt (∑ k : ι,
        ((n : ℝ)⁻¹ * (∑ i : Fin n, ξ k (s i)) - ∫ ω, ξ k ω ∂μ) ^ 2)) 2
      (Measure.pi fun _ : Fin n => μ) := by
  simpa using
    memLp_two_iid_mean_euclidean_fintype (ι := Fin n) (κ := ι) μ ξ hξ

set_option maxHeartbeats 800000 in
-- Elaborating the nested product-space integrability proof requires a larger deterministic budget.
/-- The centred coordinatewise sample averages of finitely many integrable statistics over an
`n`-point independent, identically distributed sample have integrable Euclidean length. -/
theorem integrable_iid_mean_euclidean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (ξ : ι → Ω → ℝ) (hξ : ∀ k, Integrable (ξ k) μ) :
    Integrable (fun s => Real.sqrt (∑ k : ι,
        ((n : ℝ)⁻¹ * (∑ i : Fin n, ξ k (s i)) - ∫ ω, ξ k ω ∂μ) ^ 2))
      (Measure.pi fun _ : Fin n => μ) := by
  let v : (Fin n → Ω) → ι → ℝ := fun s k =>
    (n : ℝ)⁻¹ * (∑ i : Fin n, ξ k (s i)) - ∫ ω, ξ k ω ∂μ
  have hv (k : ι) : Integrable (fun s => v s k) (Measure.pi fun _ : Fin n => μ) := by
    dsimp only [v]
    apply Integrable.sub
    · apply Integrable.const_mul
      exact integrable_finset_sum Finset.univ fun i _ =>
        (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable (hξ k)
    · exact integrable_const _
  simpa only [v] using integrable_euclidean_of_integrable v hv

/-- An average of `n` independent, identically distributed observations has the same expectation
as the population statistic being averaged. -/
lemma iid_average_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (F : Ω → ℝ) (hF : Integrable F μ) :
    (∫ sample : Fin m → Ω,
        (m : ℝ)⁻¹ * ∑ i, F (sample i)
        ∂Measure.pi (fun _ : Fin m => μ)) =
      ∫ o, F o ∂μ := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  simpa using iid_average_integral_fintype (ι := Fin m) μ F hF

/-- The variance of an average of independent, identically distributed observations is the
population variance divided by the sample size (including the zero-length case). -/
lemma iid_average_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ)
    (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    ProbabilityTheory.variance
        (fun sample : Fin m → Ω =>
          (m : ℝ)⁻¹ * ∑ i, F (sample i))
      (Measure.pi (fun _ : Fin m => μ)) =
      (m : ℝ)⁻¹ * ProbabilityTheory.variance F μ := by
  cases m with
  | zero =>
    have hfun :
        (fun sample : Fin 0 → Ω => ((0 : ℕ) : ℝ)⁻¹ * ∑ i, F (sample i)) = 0 := by
      funext sample
      simp
    rw [hfun, ProbabilityTheory.variance_zero]
    simp
  | succ m =>
    simpa using iid_average_variance_fintype (ι := Fin (m + 1)) μ F hF

end

end Causalean.Mathlib.Probability
