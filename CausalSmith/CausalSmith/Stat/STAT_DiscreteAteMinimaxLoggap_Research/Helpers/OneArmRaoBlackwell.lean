import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmCountSufficiency
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmDepoissonization
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite permutation Rao--Blackwellization

An arbitrary ordered-sample estimator can be averaged over coordinate
permutations.  Convexity decreases squared risk, while every iid product law
is invariant under those permutations.  This is the finite symmetrization
step used by the count-level D.2 reduction.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

def permuteFiniteSample {n : ℕ} {X : Type*}
    (σ : Equiv.Perm (Fin n)) (x : Fin n → X) : Fin n → X :=
  fun i => x (σ i)

noncomputable def finitePermutationAverage {n : ℕ} {X : Type*}
    (est : (Fin n → X) → ℝ) (x : Fin n → X) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), est (permuteFiniteSample σ x)) /
    Fintype.card (Equiv.Perm (Fin n))

def finiteSampleHistogram {n : ℕ} {X : Type*} [DecidableEq X]
    (x : Fin n → X) (a : X) : ℕ :=
  Fintype.card {i : Fin n // x i = a}

def finiteSampleFiberEquiv {n : ℕ} {X : Type*} (x : Fin n → X) :
    Fin n ≃ Σ a : X, {i : Fin n // x i = a} where
  toFun i := ⟨x i, i, rfl⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨a, i, hi⟩
    dsimp
    subst a
    rfl

/-- Equal finite histograms differ only by a permutation of sample
coordinates. -/
lemma exists_perm_of_finiteSampleHistogram_eq
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {x y : Fin n → X} (h : finiteSampleHistogram x = finiteSampleHistogram y) :
    ∃ σ : Equiv.Perm (Fin n), permuteFiniteSample σ x = y := by
  classical
  have hcard (a : X) :
      Fintype.card {i : Fin n // y i = a} =
        Fintype.card {i : Fin n // x i = a} := by
    simpa [finiteSampleHistogram] using (congrFun h a).symm
  let ef (a : X) : {i : Fin n // y i = a} ≃ {i : Fin n // x i = a} :=
    Fintype.equivOfCardEq (hcard a)
  let σ : Equiv.Perm (Fin n) :=
    (finiteSampleFiberEquiv y).trans
      ((Equiv.sigmaCongrRight ef).trans (finiteSampleFiberEquiv x).symm)
  refine ⟨σ, ?_⟩
  funext i
  change x (σ i) = y i
  have hi : x ((ef (y i)) ⟨i, rfl⟩).1 = y i :=
    ((ef (y i)) ⟨i, rfl⟩).2
  simpa [σ, finiteSampleFiberEquiv] using hi

lemma finitePermutationAverage_permute
    {n : ℕ} {X : Type*} (est : (Fin n → X) → ℝ)
    (τ : Equiv.Perm (Fin n)) (x : Fin n → X) :
    finitePermutationAverage est (permuteFiniteSample τ x) =
      finitePermutationAverage est x := by
  let R : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) := {
    toFun σ := σ.trans τ.symm
    invFun ρ := ρ.trans τ
    left_inv σ := by ext i; simp
    right_inv ρ := by ext i; simp }
  unfold finitePermutationAverage
  congr 1
  rw [← R.sum_comp]
  apply Fintype.sum_congr
  intro σ
  apply congrArg est
  funext i
  simp [R, permuteFiniteSample]

lemma finitePermutationAverage_eq_of_histogram_eq
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) {x y : Fin n → X}
    (h : finiteSampleHistogram x = finiteSampleHistogram y) :
    finitePermutationAverage est x = finitePermutationAverage est y := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_finiteSampleHistogram_eq h
  rw [← hσ, finitePermutationAverage_permute]

def FiniteSampleHistogramSpace (n : ℕ) (X : Type*) [DecidableEq X] :=
  Set.range (@finiteSampleHistogram n X _)

noncomputable def finiteSampleOfHistogram
    {n : ℕ} {X : Type*} [DecidableEq X]
    (h : FiniteSampleHistogramSpace n X) : Fin n → X :=
  Classical.choose h.2

lemma finiteSampleOfHistogram_spec
    {n : ℕ} {X : Type*} [DecidableEq X]
    (h : FiniteSampleHistogramSpace n X) :
    finiteSampleHistogram (finiteSampleOfHistogram h) = h.1 :=
  Classical.choose_spec h.2

/-- The permutation-averaged estimator factored through the finite histogram
space. -/
noncomputable def finiteHistogramEstimator
    {n : ℕ} {X : Type*} [DecidableEq X]
    (est : (Fin n → X) → ℝ) (h : FiniteSampleHistogramSpace n X) : ℝ :=
  finitePermutationAverage est (finiteSampleOfHistogram h)

lemma finiteHistogramEstimator_apply
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) (x : Fin n → X) :
    finiteHistogramEstimator est ⟨finiteSampleHistogram x, ⟨x, rfl⟩⟩ =
      finitePermutationAverage est x := by
  apply finitePermutationAverage_eq_of_histogram_eq
  exact finiteSampleOfHistogram_spec _

def histogramTotal {X : Type*} [Fintype X] (c : X → ℕ) : ℕ :=
  ∑ a, c a

lemma histogramTotal_finiteSampleHistogram
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (x : Fin n → X) :
    histogramTotal (finiteSampleHistogram x) = n := by
  classical
  unfold histogramTotal finiteSampleHistogram
  simp_rw [Fintype.card_subtype]
  rw [← Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := x) (by simp)]
  simp

def HistogramFiber {X : Type*} [Fintype X] [DecidableEq X]
    (c : X → ℕ) :=
  {x : Fin (histogramTotal c) → X // finiteSampleHistogram x = c}

noncomputable instance histogramFiberFintype
    {X : Type*} [Fintype X] [DecidableEq X] (c : X → ℕ) :
    Fintype (HistogramFiber c) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

def retainedHistogramPrefix {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {c : X → ℕ} (h : n ≤ histogramTotal c)
    (x : HistogramFiber c) : Fin n → X :=
  fun i => x.1 (Fin.castLE h i)

/-- Uniform conditional-fibre estimator used after a Poisson count table is
observed.  The `n ≤ total` proof is explicit because the complementary event
is paid by the D.2 lower-tail term. -/
noncomputable def retainedHistogramAverage
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) (c : X → ℕ)
    (h : n ≤ histogramTotal c) : ℝ := by
  classical
  exact (∑ x : HistogramFiber c, est (retainedHistogramPrefix h x)) /
    Fintype.card (HistogramFiber c)

/-- Finite Jensen/Cauchy on a nonempty histogram fibre. -/
lemma retainedHistogramAverage_sq_sub_le
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) (theta : ℝ) (c : X → ℕ)
    (h : n ≤ histogramTotal c) [Nonempty (HistogramFiber c)] :
    (retainedHistogramAverage est c h - theta) ^ 2 ≤
      (∑ x : HistogramFiber c,
          (est (retainedHistogramPrefix h x) - theta) ^ 2) /
        Fintype.card (HistogramFiber c) := by
  classical
  have hcard : (Fintype.card (HistogramFiber c) : ℝ) ≠ 0 := by positivity
  rw [retainedHistogramAverage]
  have hrewrite :
      (∑ x : HistogramFiber c, est (retainedHistogramPrefix h x)) /
            Fintype.card (HistogramFiber c) - theta =
        (∑ x : HistogramFiber c,
            (est (retainedHistogramPrefix h x) - theta)) /
              Fintype.card (HistogramFiber c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp [hcard]
  rw [hrewrite]
  simpa using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ)
      (f := fun x : HistogramFiber c =>
        est (retainedHistogramPrefix h x) - theta))

def finiteProductWeight {n : ℕ} {X : Type*}
    (p : X → ℝ) (x : Fin n → X) : ℝ :=
  ∏ i, p (x i)

/-- Iid product mass is constant on each finite histogram fibre. -/
lemma finiteProductWeight_eq_of_histogram_eq
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) {x y : Fin n → X}
    (h : finiteSampleHistogram x = finiteSampleHistogram y) :
    finiteProductWeight p x = finiteProductWeight p y := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_finiteSampleHistogram_eq h
  rw [← hσ]
  unfold finiteProductWeight permuteFiniteSample
  simpa using
    (σ.prod_comp Finset.univ (fun i => p (x i)) (by simp)).symm

lemma finiteProductWeight_histogramFiber_constant
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (c : X → ℕ) (x y : HistogramFiber c) :
    finiteProductWeight p x.1 = finiteProductWeight p y.1 :=
  finiteProductWeight_eq_of_histogram_eq p (x.2.trans y.2.symm)

def FixedHistogramFiber (N : ℕ) {X : Type*} [DecidableEq X]
    (c : X → ℕ) :=
  {x : Fin N → X // finiteSampleHistogram x = c}

noncomputable instance fixedHistogramFiberFintype
    (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (c : X → ℕ) :
    Fintype (FixedHistogramFiber N c) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def fixedHistogramAverage
    {n N : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) (h : n ≤ N) (c : X → ℕ) : ℝ := by
  classical
  exact (∑ x : FixedHistogramFiber N c,
      est (fun i => x.1 (Fin.castLE h i))) /
    Fintype.card (FixedHistogramFiber N c)

/-- Finite Jensen/Cauchy on a fixed-total histogram fibre. -/
lemma fixedHistogramAverage_sq_sub_le
    {n N : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) (theta : ℝ) (h : n ≤ N) (c : X → ℕ)
    [Nonempty (FixedHistogramFiber N c)] :
    (fixedHistogramAverage est h c - theta) ^ 2 ≤
      (∑ x : FixedHistogramFiber N c,
          (est (fun i => x.1 (Fin.castLE h i)) - theta) ^ 2) /
        Fintype.card (FixedHistogramFiber N c) := by
  classical
  have hcard : (Fintype.card (FixedHistogramFiber N c) : ℝ) ≠ 0 := by
    positivity
  rw [fixedHistogramAverage]
  have hrewrite :
      (∑ x : FixedHistogramFiber N c,
          est (fun i => x.1 (Fin.castLE h i))) /
            Fintype.card (FixedHistogramFiber N c) - theta =
        (∑ x : FixedHistogramFiber N c,
            (est (fun i => x.1 (Fin.castLE h i)) - theta)) /
              Fintype.card (FixedHistogramFiber N c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp [hcard]
  rw [hrewrite]
  simpa using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ)
      (f := fun x : FixedHistogramFiber N c =>
        est (fun i => x.1 (Fin.castLE h i)) - theta))

/-- On one nonempty fixed-total histogram fibre, uniform prefix averaging
decreases product-mass-weighted squared loss. -/
lemma fixedHistogramFiber_weighted_average_sq_le
    {n N : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : ∀ a, 0 ≤ p a)
    (est : (Fin n → X) → ℝ) (theta : ℝ) (h : n ≤ N) (c : X → ℕ)
    [Nonempty (FixedHistogramFiber N c)] :
    (∑ x : FixedHistogramFiber N c,
        finiteProductWeight p x.1 *
          (fixedHistogramAverage est h c - theta) ^ 2) ≤
      ∑ x : FixedHistogramFiber N c,
        finiteProductWeight p x.1 *
          (est (fun i => x.1 (Fin.castLE h i)) - theta) ^ 2 := by
  classical
  let x0 : FixedHistogramFiber N c := Classical.arbitrary _
  let w : ℝ := finiteProductWeight p x0.1
  have hw (x : FixedHistogramFiber N c) : finiteProductWeight p x.1 = w :=
    finiteProductWeight_eq_of_histogram_eq p (x.2.trans x0.2.symm)
  have hw0 : 0 ≤ w := by
    dsimp [w, finiteProductWeight]
    exact Finset.prod_nonneg fun i _ => hp (x0.1 i)
  have hc : (0 : ℝ) < Fintype.card (FixedHistogramFiber N c) := by
    positivity
  have hJ := fixedHistogramAverage_sq_sub_le est theta h c
  have hscaled :
      (Fintype.card (FixedHistogramFiber N c) : ℝ) *
          (fixedHistogramAverage est h c - theta) ^ 2 ≤
        ∑ x : FixedHistogramFiber N c,
          (est (fun i => x.1 (Fin.castLE h i)) - theta) ^ 2 := by
    exact (by simpa [mul_comm] using (le_div_iff₀ hc).mp hJ)
  have hmul := mul_le_mul_of_nonneg_left hscaled hw0
  simp_rw [hw]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  nlinarith

/-- Summing the fibrewise Jensen inequality gives fixed-total iid risk
contraction for the histogram estimator. -/
lemma fixedHistogramAverage_weighted_risk_le
    {n N : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : ∀ a, 0 ≤ p a)
    (est : (Fin n → X) → ℝ) (theta : ℝ) (h : n ≤ N) :
    (∑ z : Fin N → X,
        finiteProductWeight p z *
          (fixedHistogramAverage est h (finiteSampleHistogram z) - theta) ^ 2) ≤
      ∑ z : Fin N → X,
        finiteProductWeight p z *
          (est (fun i => z (Fin.castLE h i)) - theta) ^ 2 := by
  classical
  let H : Finset (X → ℕ) :=
    Finset.univ.image (fun z : Fin N → X => finiteSampleHistogram z)
  have hleft := Finset.sum_fiberwise_eq_sum_filter Finset.univ H
    (fun z : Fin N → X => finiteSampleHistogram z) (fun z : Fin N → X =>
      finiteProductWeight p z *
        (fixedHistogramAverage est h (finiteSampleHistogram z) - theta) ^ 2)
  have hright := Finset.sum_fiberwise_eq_sum_filter Finset.univ H
    (fun z : Fin N → X => finiteSampleHistogram z) (fun z : Fin N → X =>
      finiteProductWeight p z *
        (est (fun i => z (Fin.castLE h i)) - theta) ^ 2)
  have hleft' :
      (∑ c ∈ H, ∑ z ∈ (Finset.univ : Finset (Fin N → X)) with finiteSampleHistogram z = c,
        finiteProductWeight p z *
          (fixedHistogramAverage est h (finiteSampleHistogram z) - theta) ^ 2) =
        ∑ z : Fin N → X, finiteProductWeight p z *
          (fixedHistogramAverage est h (finiteSampleHistogram z) - theta) ^ 2 := by
    simpa [H] using hleft
  have hright' :
      (∑ c ∈ H, ∑ z ∈ (Finset.univ : Finset (Fin N → X)) with finiteSampleHistogram z = c,
        finiteProductWeight p z *
          (est (fun i => z (Fin.castLE h i)) - theta) ^ 2) =
        ∑ z : Fin N → X, finiteProductWeight p z *
          (est (fun i => z (Fin.castLE h i)) - theta) ^ 2 := by
    simpa [H] using hright
  rw [← hleft', ← hright']
  simp only [H, Finset.mem_image, Finset.mem_univ, true_and,
    exists_eq_right]
  apply Finset.sum_le_sum
  intro c _
  by_cases hf : (Finset.univ.filter fun z : Fin N → X =>
      finiteSampleHistogram z = c).Nonempty
  · let z0 : Fin N → X := Classical.choose hf
    have hz0 : finiteSampleHistogram z0 = c := by
      exact (Finset.mem_filter.mp (Classical.choose_spec hf)).2
    letI : Nonempty (FixedHistogramFiber N c) := ⟨⟨z0, hz0⟩⟩
    have hle := fixedHistogramFiber_weighted_average_sq_le
      p hp est theta h c
    calc
      (∑ z ∈ Finset.univ with finiteSampleHistogram z = c,
          finiteProductWeight p z *
            (fixedHistogramAverage est h (finiteSampleHistogram z) - theta) ^ 2) =
          ∑ z ∈ Finset.univ with finiteSampleHistogram z = c,
            finiteProductWeight p z *
              (fixedHistogramAverage est h c - theta) ^ 2 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
      _ = ∑ x : FixedHistogramFiber N c,
            finiteProductWeight p x.1 *
              (fixedHistogramAverage est h c - theta) ^ 2 := by
        exact Finset.sum_subtype
          (p := fun z : Fin N → X => finiteSampleHistogram z = c)
          (Finset.univ.filter fun z : Fin N → X => finiteSampleHistogram z = c)
          (by simp) (fun z : Fin N → X => finiteProductWeight p z *
            (fixedHistogramAverage est h c - theta) ^ 2)
      _ ≤ ∑ x : FixedHistogramFiber N c,
            finiteProductWeight p x.1 *
              (est (fun i => x.1 (Fin.castLE h i)) - theta) ^ 2 := hle
      _ = ∑ z ∈ Finset.univ with finiteSampleHistogram z = c,
            finiteProductWeight p z *
              (est (fun i => z (Fin.castLE h i)) - theta) ^ 2 := by
        exact (Finset.sum_subtype
          (p := fun z : Fin N → X => finiteSampleHistogram z = c)
          (Finset.univ.filter fun z : Fin N → X => finiteSampleHistogram z = c)
          (by simp) (fun z : Fin N → X => finiteProductWeight p z *
            (est (fun i => z (Fin.castLE h i)) - theta) ^ 2)).symm
  · simp only [Finset.not_nonempty_iff_eq_empty] at hf
    rw [hf]
    simp

/-- Measure-theoretic fixed-total form of the histogram Rao--Blackwell
contraction under an iid product law. -/
lemma fixedHistogramAverage_productRisk_le
    {n N : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P]
    (est : (Fin n → X) → ℝ) (theta : ℝ) (h : n ≤ N) :
    (∫ z : Fin N → X,
        (fixedHistogramAverage est h (finiteSampleHistogram z) - theta) ^ 2
          ∂Measure.pi (fun _ : Fin N => P)) ≤
      ∫ z : Fin N → X,
        (est (fun i => z (Fin.castLE h i)) - theta) ^ 2
          ∂Measure.pi (fun _ : Fin N => P) := by
  rw [integral_fintype Integrable.of_finite,
    integral_fintype Integrable.of_finite]
  simp_rw [Causalean.Stat.pi_real_singleton]
  simpa [finiteProductWeight, mul_comm] using
    (fixedHistogramAverage_weighted_risk_le
      (p := fun a : X => P.real {a})
      (fun a => measureReal_nonneg) est theta h)

/-- Extending an iid tuple and then retaining its first `n` coordinates does
not change the risk of an `n`-sample estimator. -/
lemma productRisk_retainedPrefix_eq
    {n N : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (P : Measure X) [IsProbabilityMeasure P]
    (est : (Fin n → X) → ℝ) (theta : ℝ) (h : n ≤ N) :
    (∫ z : Fin N → X,
        (est (fun i => z (Fin.castLE h i)) - theta) ^ 2
          ∂Measure.pi (fun _ : Fin N => P)) =
      ∫ z : Fin n → X, (est z - theta) ^ 2
        ∂Measure.pi (fun _ : Fin n => P) := by
  have hprefixN : Measurable (fun z : ℕ → X => fun i : Fin N => z i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  have hprefixn : Measurable (fun z : ℕ → X => fun i : Fin n => z i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  rw [← Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw_map_finPrefix
      P N,
    integral_map hprefixN.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable,
    ← Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw_map_finPrefix
      P n,
    integral_map hprefixn.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  rfl

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Count-table estimator obtained by averaging the original estimator over
the full histogram fibre when the random sample contains at least `n` points. -/
noncomputable def finiteSampleHistogramEstimator
    {n : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) (s : FiniteSample X) : ℝ :=
  if h : n ≤ s.count then
    fixedHistogramAverage est h (finiteSampleHistogram s.points)
  else 0

noncomputable instance finiteSampleMeasurableSingletonClass
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] :
    MeasurableSingletonClass (FiniteSample X) where
  measurableSet_singleton s := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro N
    change MeasurableSet ((Sigma.mk N) ⁻¹' {s})
    rcases s with ⟨M, x⟩
    by_cases hNM : N = M
    · subst M
      convert MeasurableSet.singleton x using 1
      ext y
      simp
    · convert MeasurableSet.empty using 1
      ext y
      simp [hNM]

lemma measurable_finiteSampleHistogramEstimator
    {n : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) :
    Measurable (finiteSampleHistogramEstimator est : FiniteSample X → ℝ) := by
  exact measurable_of_countable _

/-- Conditional on any successful Poisson total, histogram averaging has no
larger squared risk than the original fixed-size estimator. -/
lemma finitePoissonCountReconstruction_histogramRisk_le
    {n N : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P]
    (est : (Fin n → X) → ℝ) (theta : ℝ) (h : n ≤ N) :
    (∫ s, (finiteSampleHistogramEstimator est s - theta) ^ 2
        ∂finitePoissonCountReconstruction P N) ≤
      ∫ z : Fin n → X, (est z - theta) ^ 2
        ∂Measure.pi (fun _ : Fin n => P) := by
  unfold finitePoissonCountReconstruction
  have hmap : Measurable
      (fun z : ℕ → X => streamToFiniteSample (N, z)) :=
    measurable_streamToFiniteSample.comp
      (measurable_const.prodMk measurable_id)
  have hloss : Measurable (fun s : FiniteSample X =>
      (finiteSampleHistogramEstimator est s - theta) ^ 2) :=
    ((measurable_finiteSampleHistogramEstimator est).sub measurable_const).pow_const 2
  rw [integral_map hmap.aemeasurable hloss.aestronglyMeasurable]
  have hest (z : ℕ → X) :
      finiteSampleHistogramEstimator est (streamToFiniteSample (N, z)) =
        fixedHistogramAverage est h
          (finiteSampleHistogram (fun i : Fin N => z i)) := by
    simp [finiteSampleHistogramEstimator, streamToFiniteSample,
      FiniteSample.count, FiniteSample.points, h]
  simp_rw [hest]
  have hprefixN : Measurable (fun z : ℕ → X => fun i : Fin N => z i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  change (∫ z : ℕ → X,
      (fixedHistogramAverage est h
          (finiteSampleHistogram (fun i : Fin N => z i)) - theta) ^ 2
        ∂iidStreamLaw P) ≤ _
  calc
    (∫ z : ℕ → X,
        (fixedHistogramAverage est h
            (finiteSampleHistogram (fun i : Fin N => z i)) - theta) ^ 2
          ∂iidStreamLaw P) =
        ∫ z : Fin N → X,
          (fixedHistogramAverage est h (finiteSampleHistogram z) - theta) ^ 2
            ∂Measure.pi (fun _ : Fin N => P) := by
      rw [← iidStreamLaw_map_finPrefix P N,
        integral_map hprefixN.aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]
    _ ≤ ∫ z : Fin N → X,
          (est (fun i => z (Fin.castLE h i)) - theta) ^ 2
            ∂Measure.pi (fun _ : Fin N => P) :=
      fixedHistogramAverage_productRisk_le P est theta h
    _ = _ := productRisk_retainedPrefix_eq P est theta h

/-- The histogram estimator viewed directly as a function of the count table.
On a failed Poisson total it is set to zero. -/
noncomputable def poissonHistogramEstimator
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (est : (Fin n → X) → ℝ) (c : X → ℕ) : ℝ :=
  if h : n ≤ histogramTotal c then fixedHistogramAverage est h c else 0

/-- Poissonizing a finite-alphabet experiment and retaining only its histogram
costs only the explicit lower-tail penalty.  This is the count-risk bridge used
with the `Fin d × Fin 3` one-arm predictive table. -/
lemma poissonHistogramRisk_le_fixedRisk_add_tail
    {n : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (est : (Fin n → X) → ℝ) (theta : ℝ) :
    (∫⁻ c : X → ℕ,
        ENNReal.ofReal ((poissonHistogramEstimator est c - theta) ^ 2)
      ∂Measure.map (fun s : FiniteSample X =>
          finiteSampleHistogram s.points) (finitePoissonSampleLaw P lam)) ≤
      ENNReal.ofReal
          (∫ z : Fin n → X, (est z - theta) ^ 2
            ∂Measure.pi (fun _ : Fin n => P)) +
        ENNReal.ofReal (theta ^ 2) * (poissonMeasure lam) {k | k < n} := by
  let countMap : FiniteSample X → X → ℕ :=
    fun s => finiteSampleHistogram s.points
  have hcountMap : Measurable countMap := measurable_of_countable _
  let loss : FiniteSample X → ℝ≥0∞ := fun s =>
    ENNReal.ofReal ((finiteSampleHistogramEstimator est s - theta) ^ 2)
  have hloss : Measurable loss :=
    (((measurable_finiteSampleHistogramEstimator est).sub measurable_const).pow_const 2).ennreal_ofReal
  rw [lintegral_map (measurable_of_countable _) hcountMap]
  have hest (s : FiniteSample X) :
      poissonHistogramEstimator est (countMap s) =
        finiteSampleHistogramEstimator est s := by
    have htotal : histogramTotal (countMap s) = s.count := by
      exact histogramTotal_finiteSampleHistogram s.points
    unfold poissonHistogramEstimator finiteSampleHistogramEstimator
    by_cases h : n ≤ s.count <;> simp [htotal, h, countMap]
  simp_rw [hest]
  change (∫⁻ s, loss s ∂finitePoissonSampleLaw P lam) ≤ _
  rw [finitePoissonSampleLaw_eq_count_bind_reconstruction]
  apply poissonBindLintegral_le_core_add_tail
    (K := finitePoissonCountReconstruction P) (loss := loss)
    (core := ENNReal.ofReal
      (∫ z : Fin n → X, (est z - theta) ^ 2
        ∂Measure.pi (fun _ : Fin n => P)))
    (fail := ENNReal.ofReal (theta ^ 2))
    (measurable_finitePoissonCountReconstruction P) lam n hloss
  · intro N hN
    have hrisk := finitePoissonCountReconstruction_histogramRisk_le
      P est theta hN
    have hstream (z : ℕ → X) :
        finiteSampleHistogramEstimator est (streamToFiniteSample (N, z)) =
          fixedHistogramAverage est hN
            (finiteSampleHistogram (fun i : Fin N => z i)) := by
      simp [finiteSampleHistogramEstimator, streamToFiniteSample,
        FiniteSample.count, FiniteSample.points, hN]
    have hprefixN : Measurable (fun z : ℕ → X => fun i : Fin N => z i) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
    have hstreamMap : Measurable
        (fun z : ℕ → X => streamToFiniteSample (N, z)) :=
      measurable_streamToFiniteSample.comp
        (measurable_const.prodMk measurable_id)
    have hlossStream (z : ℕ → X) :
        loss (streamToFiniteSample (N, z)) =
          ENNReal.ofReal
            ((fixedHistogramAverage est hN
              (finiteSampleHistogram (fun i : Fin N => z i)) - theta) ^ 2) := by
      simp [loss, hstream]
    have hfinite : Integrable (fun z : Fin N → X =>
        (fixedHistogramAverage est hN (finiteSampleHistogram z) - theta) ^ 2)
        (Measure.pi (fun _ : Fin N => P)) := Integrable.of_finite
    have hprefixRiskLintegral :
        (∫⁻ z : ℕ → X,
          ENNReal.ofReal
            ((fixedHistogramAverage est hN
                (finiteSampleHistogram (fun i : Fin N => z i)) - theta) ^ 2)
            ∂iidStreamLaw P) =
          ∫⁻ z : Fin N → X,
            ENNReal.ofReal
              ((fixedHistogramAverage est hN (finiteSampleHistogram z) - theta) ^ 2)
            ∂Measure.pi (fun _ : Fin N => P) := by
      rw [← iidStreamLaw_map_finPrefix P N,
        lintegral_map (measurable_of_countable _) hprefixN]
    have hreconstruction :
        (∫⁻ s, loss s ∂finitePoissonCountReconstruction P N) =
          ENNReal.ofReal
            (∫ s, (finiteSampleHistogramEstimator est s - theta) ^ 2
              ∂finitePoissonCountReconstruction P N) := by
      unfold finitePoissonCountReconstruction
      rw [lintegral_map hloss hstreamMap]
      simp_rw [hlossStream]
      change (∫⁻ z : ℕ → X,
          ENNReal.ofReal
            ((fixedHistogramAverage est hN
                (finiteSampleHistogram (fun i : Fin N => z i)) - theta) ^ 2)
            ∂iidStreamLaw P) = _
      rw [hprefixRiskLintegral]
      rw [← ofReal_integral_eq_lintegral_ofReal hfinite]
      · congr 1
        rw [integral_map]
        · simp_rw [hstream]
          rw [← iidStreamLaw_map_finPrefix P N,
            integral_map hprefixN.aemeasurable
              (measurable_of_countable _).aestronglyMeasurable]
        · exact
            (measurable_streamToFiniteSample.comp
              (measurable_const.prodMk measurable_id)).aemeasurable
        · exact
            (((measurable_finiteSampleHistogramEstimator est).sub
              measurable_const).pow_const 2).aestronglyMeasurable
      · exact ae_of_all _ fun _ => sq_nonneg _
    rw [hreconstruction]
    exact ENNReal.ofReal_le_ofReal hrisk
  · intro N hN
    unfold finitePoissonCountReconstruction
    have hstreamMap : Measurable
        (fun z : ℕ → X => streamToFiniteSample (N, z)) :=
      measurable_streamToFiniteSample.comp
        (measurable_const.prodMk measurable_id)
    rw [lintegral_map hloss hstreamMap]
    have hnot : ¬ n ≤ N := Nat.not_le_of_lt hN
    simp [loss, finiteSampleHistogramEstimator, streamToFiniteSample,
      FiniteSample.count, hnot, sq_nonneg]

/-- Real-valued form of the Poisson histogram risk bound.  In particular it
supplies the integrability hypotheses needed by the count-space Le Cam bound. -/
lemma integral_poissonHistogramRisk_le_fixedRisk_add_tail
    {n : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (est : (Fin n → X) → ℝ) (theta : ℝ) :
    Integrable
        (fun c : X → ℕ => (poissonHistogramEstimator est c - theta) ^ 2)
        (Measure.map (fun s : FiniteSample X =>
          finiteSampleHistogram s.points) (finitePoissonSampleLaw P lam)) ∧
      (∫ c : X → ℕ, (poissonHistogramEstimator est c - theta) ^ 2
          ∂Measure.map (fun s : FiniteSample X =>
            finiteSampleHistogram s.points) (finitePoissonSampleLaw P lam)) ≤
        (∫ z : Fin n → X, (est z - theta) ^ 2
          ∂Measure.pi (fun _ : Fin n => P)) +
          theta ^ 2 * (poissonMeasure lam).real {k | k < n} := by
  let Q := Measure.map (fun s : FiniteSample X =>
    finiteSampleHistogram s.points) (finitePoissonSampleLaw P lam)
  let loss : (X → ℕ) → ℝ :=
    fun c => (poissonHistogramEstimator est c - theta) ^ 2
  have hbound := poissonHistogramRisk_le_fixedRisk_add_tail P lam est theta
  have hfixed0 : 0 ≤
      ∫ z : Fin n → X, (est z - theta) ^ 2
        ∂Measure.pi (fun _ : Fin n => P) :=
    integral_nonneg fun _ => sq_nonneg _
  have hloss : Measurable loss := measurable_of_countable _
  have htailTop :
      ENNReal.ofReal (theta ^ 2) * (poissonMeasure lam) {k | k < n} < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hrhsLtTop :
      ENNReal.ofReal
          (∫ z : Fin n → X, (est z - theta) ^ 2
            ∂Measure.pi (fun _ : Fin n => P)) +
        ENNReal.ofReal (theta ^ 2) * (poissonMeasure lam) {k | k < n} < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, htailTop⟩
  have hint : Integrable loss Q := by
    refine ⟨hloss.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact hbound.trans_lt hrhsLtTop
  refine ⟨hint, ?_⟩
  have heq : ENNReal.ofReal (∫ c, loss c ∂Q) =
      ∫⁻ c, ENNReal.ofReal (loss c) ∂Q := by
    exact ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hrhsTop :
      ENNReal.ofReal
          (∫ z : Fin n → X, (est z - theta) ^ 2
            ∂Measure.pi (fun _ : Fin n => P)) +
        ENNReal.ofReal (theta ^ 2) * (poissonMeasure lam) {k | k < n} ≠ ⊤ :=
    hrhsLtTop.ne
  have hlhsTop : ENNReal.ofReal (∫ c, loss c ∂Q) ≠ ⊤ := by simp
  have hreal :=
    (ENNReal.toReal_le_toReal hlhsTop hrhsTop).2 (heq.trans_le hbound)
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _),
    ENNReal.toReal_add ENNReal.ofReal_ne_top (ne_of_lt htailTop),
    ENNReal.toReal_ofReal hfixed0, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg theta)] at hreal
  simpa only [Q, loss, measureReal_def] using hreal

/-- On one nonempty iid histogram fibre, uniform retained-prefix averaging
decreases the product-mass-weighted squared loss. -/
lemma histogramFiber_weighted_retainedAverage_sq_le
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : ∀ a, 0 ≤ p a)
    (est : (Fin n → X) → ℝ) (theta : ℝ) (c : X → ℕ)
    (h : n ≤ histogramTotal c) [Nonempty (HistogramFiber c)] :
    (∑ x : HistogramFiber c,
        finiteProductWeight p x.1 *
          (retainedHistogramAverage est c h - theta) ^ 2) ≤
      ∑ x : HistogramFiber c,
        finiteProductWeight p x.1 *
          (est (retainedHistogramPrefix h x) - theta) ^ 2 := by
  classical
  let x0 : HistogramFiber c := Classical.arbitrary _
  let w : ℝ := finiteProductWeight p x0.1
  have hw (x : HistogramFiber c) : finiteProductWeight p x.1 = w :=
    finiteProductWeight_histogramFiber_constant p c x x0
  have hw0 : 0 ≤ w := by
    dsimp [w, finiteProductWeight]
    exact Finset.prod_nonneg fun i _ => hp (x0.1 i)
  have hc : (0 : ℝ) < Fintype.card (HistogramFiber c) := by positivity
  have hJ := retainedHistogramAverage_sq_sub_le est theta c h
  have hscaled :
      (Fintype.card (HistogramFiber c) : ℝ) *
          (retainedHistogramAverage est c h - theta) ^ 2 ≤
        ∑ x : HistogramFiber c,
          (est (retainedHistogramPrefix h x) - theta) ^ 2 := by
    exact (by simpa [mul_comm] using (le_div_iff₀ hc).mp hJ)
  have hmul := mul_le_mul_of_nonneg_left hscaled hw0
  simp_rw [hw]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  nlinarith

lemma finitePermutationAverage_sq_sub_le
    {n : ℕ} {X : Type*} (est : (Fin n → X) → ℝ)
    (theta : ℝ) (x : Fin n → X) :
    (finitePermutationAverage est x - theta) ^ 2 ≤
      (∑ σ : Equiv.Perm (Fin n),
        (est (permuteFiniteSample σ x) - theta) ^ 2) /
          Fintype.card (Equiv.Perm (Fin n)) := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by positivity
  rw [finitePermutationAverage]
  have hrewrite :
      (∑ σ : Equiv.Perm (Fin n), est (permuteFiniteSample σ x)) /
            Fintype.card (Equiv.Perm (Fin n)) - theta =
        (∑ σ : Equiv.Perm (Fin n),
            (est (permuteFiniteSample σ x) - theta)) /
              Fintype.card (Equiv.Perm (Fin n)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp [hcard]
  rw [hrewrite]
  simpa using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ)
      (f := fun σ : Equiv.Perm (Fin n) =>
        est (permuteFiniteSample σ x) - theta))

/-- Permutation averaging cannot increase squared risk under an iid finite
product law. -/
lemma mse_finitePermutationAverage_le
    {n d : ℕ} (P : DiscreteLaw d)
    (est : (Fin n → Obs d) → ℝ) (theta : ℝ) :
    mse (productLaw P n) (finitePermutationAverage est) theta ≤
      mse (productLaw P n) est theta := by
  let μ : Measure (Fin n → Obs d) := productLaw P n
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by positivity
  have hpoint (x : Fin n → Obs d) :=
    finitePermutationAverage_sq_sub_le est theta x
  unfold mse
  calc
    ∫ x, (finitePermutationAverage est x - theta) ^ 2 ∂μ ≤
        ∫ x, (∑ σ : Equiv.Perm (Fin n),
          (est (permuteFiniteSample σ x) - theta) ^ 2) /
            Fintype.card (Equiv.Perm (Fin n)) ∂μ := by
      apply integral_mono_ae
      · exact Integrable.of_finite
      · exact Integrable.of_finite
      · exact ae_of_all _ hpoint
    _ = (∑ σ : Equiv.Perm (Fin n),
          ∫ x, (est (permuteFiniteSample σ x) - theta) ^ 2 ∂μ) /
            Fintype.card (Equiv.Perm (Fin n)) := by
      rw [integral_div]
      congr 1
      rw [integral_finset_sum]
      intro σ _
      exact MemLp.of_discrete.integrable_sq
    _ = (∑ _σ : Equiv.Perm (Fin n),
          ∫ x, (est x - theta) ^ 2 ∂μ) /
            Fintype.card (Equiv.Perm (Fin n)) := by
      congr 2
      funext σ
      let e := MeasurableEquiv.piCongrLeft
        (fun _ : Fin n => Obs d) σ.symm
      have hmp : MeasurePreserving e μ μ := by
        simpa [μ, productLaw] using
          (measurePreserving_piCongrLeft
            (fun _ : Fin n => obsLaw P) σ.symm)
      have he : (fun x => (est (permuteFiniteSample σ x) - theta) ^ 2) =
          (fun x => (est x - theta) ^ 2) ∘ e := by
        funext x
        congr 2
        apply congrArg est
        funext i
        change x (σ i) =
          (MeasurableEquiv.piCongrLeft
            (fun _ : Fin n => Obs d) σ.symm) x i
        simpa using
          (MeasurableEquiv.piCongrLeft_apply_apply
            (β := fun _ : Fin n => Obs d) σ.symm x (σ i)).symm
      rw [he]
      exact hmp.integral_comp' (fun x => (est x - theta) ^ 2)
    _ = ∫ x, (est x - theta) ^ 2 ∂μ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [ne_of_gt hcard]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
