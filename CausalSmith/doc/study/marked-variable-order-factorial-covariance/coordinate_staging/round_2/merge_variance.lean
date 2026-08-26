
namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## Unbiasedness for normalized finite-coordinate statistics -/

/-- For [an i.i.d. sample](hyp:S), [a finite coordinate family](hyp:ι),
[a kernel](hyp:k), and [sample size `n`](hyp:n), if [the number of coordinates
does not exceed the sample size](hyp:hcard), [the kernel is measurable](hyp:hkmeas),
and [the kernel is integrable under the product law](hyp:hkint), [the expected
normalized statistic equals the kernel's product-law mean](goal). -/
theorem integral_normalizedFiniteKernelStatistic
    (S : Causalean.Stat.IIDSample Ω X μ P) {ι : Type*} [Fintype ι]
    {k : (ι → X) → ℝ} {n : ℕ}
    (hcard : Fintype.card ι ≤ n) (hkmeas : Measurable k)
    (hkint : Integrable k (Measure.pi fun _ : ι => P)) :
    ∫ ω, normalizedFiniteKernelStatistic S k n ω ∂μ =
      ∫ z, k z ∂(Measure.pi fun _ : ι => P) := by
  /- Expand the finite sum, transport each injective assignment with
  `IIDSample.map_fintype_tuple_eq`, and cancel the positive tuple count. -/
  classical
  have hdesc_ne : (n.descFactorial (Fintype.card ι) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hcard).ne'
  have hterm_int : ∀ t ∈ finiteInjectiveTuples ι n,
      Integrable (fun ω => k (fun i => S.Z (t i : ℕ) ω)) μ := by
    intro t ht
    have htinj : Function.Injective t := (Finset.mem_filter.mp ht).2
    have hmap : Integrable k
        (μ.map (fun ω : Ω => fun i : ι => S.Z (t i : ℕ) ω)) := by
      rw [S.map_fintype_tuple_eq htinj]
      exact hkint
    exact (integrable_map_measure hkmeas.aestronglyMeasurable
      (measurable_pi_lambda _ (fun i : ι => S.meas (t i : ℕ))).aemeasurable).mp hmap
  simp only [normalizedFiniteKernelStatistic]
  rw [integral_const_mul,
    integral_finsetSum _ (fun t ht => hterm_int t ht)]
  have hsum_eval :
      (∑ t ∈ finiteInjectiveTuples ι n,
        ∫ ω, k (fun i => S.Z (t i : ℕ) ω) ∂μ) =
      ∑ _t ∈ finiteInjectiveTuples ι n,
        ∫ z, k z ∂(Measure.pi fun _ : ι => P) := by
    apply Finset.sum_congr rfl
    intro t ht
    have htinj : Function.Injective t := (Finset.mem_filter.mp ht).2
    rw [← S.map_fintype_tuple_eq htinj]
    rw [integral_map
      (measurable_pi_lambda _ (fun i : ι => S.meas (t i : ℕ))).aemeasurable
      hkmeas.aestronglyMeasurable]
  rw [hsum_eval, Finset.sum_const, nsmul_eq_mul]
  rw [finiteInjectiveTuples_card]
  field_simp [hdesc_ne]


end Causalean.Stat
