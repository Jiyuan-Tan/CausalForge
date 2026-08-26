
namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## Normalized finite-coordinate statistics -/

/-- The injective assignments send each coordinate in a finite family to a
distinct observation among the first `n` sample positions. -/
noncomputable def finiteInjectiveTuples (ι : Type*) [Fintype ι] (n : ℕ) :
    Finset (ι → Fin n) := by
  classical
  exact Finset.univ.filter Function.Injective

/-- For [a finite coordinate family](hyp:ι) and [sample size `n`](hyp:n), [the
number of injective sample assignments is the falling factorial of `n` with
length equal to the number of coordinates](goal). -/
theorem finiteInjectiveTuples_card (ι : Type*) [Fintype ι] (n : ℕ) :
    (finiteInjectiveTuples ι n).card = n.descFactorial (Fintype.card ι) := by
  classical
  have hsub : Fintype.card {t : ι → Fin n // Function.Injective t} =
      (finiteInjectiveTuples ι n).card := by
    unfold finiteInjectiveTuples
    exact Fintype.card_of_subtype _ (by intro t; simp)
  let e : {t : ι → Fin n // Function.Injective t} ≃ (ι ↪ Fin n) :=
    { toFun := fun t => ⟨t.1, t.2⟩
      invFun := fun f => ⟨f, f.2⟩
      left_inv := fun t => by cases t; rfl
      right_inv := fun f => by cases f; rfl }
  rw [← hsub, Fintype.card_congr e]
  simp [Fintype.card_embedding_eq]

/-- The normalized finite-kernel statistic averages a kernel over every
injective assignment of its finite coordinate family to sample positions. -/
noncomputable def normalizedFiniteKernelStatistic (S : Causalean.Stat.IIDSample Ω X μ P)
    {ι : Type*} [Fintype ι] (k : (ι → X) → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ((n.descFactorial (Fintype.card ι) : ℝ)⁻¹) *
    ∑ t ∈ finiteInjectiveTuples ι n, k (fun i => S.Z (t i : ℕ) ω)

/-- The ordered-product kernel multiplies one real-valued coordinate function
for every position in an ordered tuple. -/
def orderedProductKernel {r : ℕ} (f : Fin r → X → ℝ) : (Fin r → X) → ℝ :=
  fun z => ∏ i, f i (z i)

/-- The normalized ordered-product statistic averages coordinatewise products
over injective ordered tuples and divides by the corresponding falling factorial. -/
noncomputable def normalizedOrderedProductStatistic
    (S : Causalean.Stat.IIDSample Ω X μ P) {r : ℕ}
    (f : Fin r → X → ℝ) (n : ℕ) : Ω → ℝ :=
  normalizedFiniteKernelStatistic S (orderedProductKernel f) n

/-- For [an i.i.d. sample](hyp:S), [an order-`r` kernel](hyp:k), and [sample size
`n`](hyp:n), [the normalized finite-kernel statistic agrees with the existing
fixed-order U-statistic](goal). -/
theorem normalizedFiniteKernelStatistic_fin_eq_uStatisticOrder
    (S : Causalean.Stat.IIDSample Ω X μ P) {r : ℕ}
    (k : (Fin r → X) → ℝ) (n : ℕ) :
    normalizedFiniteKernelStatistic S k n =
      Causalean.Stat.uStatisticOrder S k n := by
  classical
  have htuples : finiteInjectiveTuples (Fin r) n =
      Causalean.Stat.injectiveTuples r n := by
    ext t
    simp [finiteInjectiveTuples, Causalean.Stat.injectiveTuples]
  unfold normalizedFiniteKernelStatistic Causalean.Stat.uStatisticOrder
  rw [Causalean.Stat.injectiveTupleCount_eq_descFactorial]
  rw [htuples]
  simp

/-- For [an i.i.d. sample](hyp:S), [a family of order-`r` coordinate functions](hyp:f),
and [sample size `n`](hyp:n), [the normalized ordered-product statistic is the
existing fixed-order U-statistic applied to their product kernel](goal). -/
theorem normalizedOrderedProductStatistic_eq_uStatisticOrder
    (S : Causalean.Stat.IIDSample Ω X μ P) {r : ℕ}
    (f : Fin r → X → ℝ) (n : ℕ) :
    normalizedOrderedProductStatistic S f n =
      Causalean.Stat.uStatisticOrder S (orderedProductKernel f) n := by
  exact normalizedFiniteKernelStatistic_fin_eq_uStatisticOrder S
    (orderedProductKernel f) n

end Causalean.Stat
