/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variance infrastructure for fixed-order U-statistics

This file develops the reusable finite-product and `L²` transport lemmas needed
for variance calculations of fixed-order U-statistics.  The results here are
honest order-`m` analogues of the per-term law, integrability, and diagonal
second-moment facts used in the order-2 variance proof.
-/

import Causalean.Stat.UStatistic.OrderM.Hajek

/-!
Provides the product-law and `L²` infrastructure for fixed-order U-statistics.

For injectively indexed sample tuples, `map_fintype_tuple_eq` and
`map_tuple_eq` identify the joint law with the product measure.  The remaining
public lemmas transfer integrability, unbiasedness, mean-zero, and diagonal
second-moment facts from an order-`m` kernel under `P^m` to the corresponding
sample terms and U-statistics.  The declaration `zetaOrder` names the kernel
second moment used by the exact and upper-bound variance arguments.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- The joint law of any finite collection of distinct sample coordinates is
the corresponding product law.

The index map `r : ι → Fin n` is assumed injective, so the coordinates
`S.Z (r i)` are independent and each has law `P`.  This is the reusable
transport lemma behind fixed-order U-statistic expectations and moments. -/
theorem map_fintype_tuple_eq (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {n : ℕ} {r : ι → Fin n}
    (hr : Function.Injective r) :
    μ.map (fun ω : Ω => fun i : ι => S.Z (r i : ℕ) ω)
      = Measure.pi (fun _ : ι => P) := by
  have hrNat : Function.Injective (fun i : ι => (r i : ℕ)) := by
    intro a b hab
    exact hr (Fin.ext hab)
  have hindep : iIndepFun (fun i : ι => S.Z (r i : ℕ)) μ :=
    S.indep.precomp hrNat
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : ι => (S.meas (r i : ℕ)).aemeasurable)).mp hindep
  calc
    μ.map (fun ω : Ω => fun i : ι => S.Z (r i : ℕ) ω)
        = Measure.pi (fun i : ι => μ.map (S.Z (r i : ℕ))) := hmap
    _ = Measure.pi (fun _ : ι => P) := by
        congr with i
        rw [S.map_eq (r i : ℕ)]

/-- The joint law of an injectively indexed order-`m` sample tuple is `P^m`.

This is the `Fin m` specialization of `map_fintype_tuple_eq`, used throughout
the fixed-order U-statistic variance and negligibility proofs. -/
theorem map_tuple_eq (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ]
    {m n : ℕ} {t : Fin m → Fin n} (ht : Function.Injective t) :
    μ.map (fun ω : Ω => fun j : Fin m => S.Z (t j : ℕ) ω)
      = Measure.pi (fun _ : Fin m => P) := by
  exact S.map_fintype_tuple_eq ht

end IIDSample

namespace OrderDegenKernel

variable [IsProbabilityMeasure P] {m : ℕ} [NeZero m]
  {g : (Fin m → X) → ℝ}

/-- A square-integrable order-`m` degenerate kernel is integrable under the
product law. -/
theorem integrable (hg : OrderDegenKernel P g) :
    Integrable g (Measure.pi fun _ : Fin m => P) :=
  ((memLp_two_iff_integrable_sq hg.meas.aestronglyMeasurable).mpr hg.sq).integrable
    (by norm_num)

/-- A fully degenerate order-`m` kernel has zero product-law mean. -/
theorem integral_eq_zero (hg : OrderDegenKernel P g) :
    uMeanOrder g P = 0 := by
  classical
  let j : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩
  let p : Fin m → Prop := fun k => k = j
  let π : Measure (Fin m → X) := Measure.pi fun _ : Fin m => P
  let πhead : Measure ({k : Fin m // p k} → X) :=
    @Measure.pi {k : Fin m // p k} (fun _ => X) (Subtype.fintype p)
      (fun _ => inferInstance) (fun _ => P)
  let πtail : Measure ({k : Fin m // ¬ p k} → X) :=
    @Measure.pi {k : Fin m // ¬ p k} (fun _ => X) (Subtype.fintype fun k => ¬ p k)
      (fun _ => inferInstance) (fun _ => P)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => X) p
  let F : (({k : Fin m // p k} → X) × ({k : Fin m // ¬ p k} → X)) → ℝ :=
    fun q => g (e.symm q)
  have hmp : MeasurePreserving e π (πhead.prod πtail) := by
    simpa [π, πhead, πtail, e] using
      (measurePreserving_piEquivPiSubtypeProd (μ := fun _ : Fin m => P)
        (α := fun _ : Fin m => X) p)
  have hπhead_eval : πhead =
      @Measure.pi {k : Fin m // p k} (fun _ => X) (Fintype.subtypeEq j)
        (fun _ => inferInstance) (fun _ => P) := by
    dsimp [πhead]
    letI : Fintype {k : Fin m // p k} := Subtype.fintype p
    refine Measure.pi_eq (μ := fun _ : {k : Fin m // p k} => P)
      (μ' := @Measure.pi {k : Fin m // p k} (fun _ => X) (Fintype.subtypeEq j)
        (fun _ => inferInstance) (fun _ => P)) ?_
    intro s hs
    letI : Fintype {k : Fin m // p k} := Fintype.subtypeEq j
    rw [Measure.pi_pi]
    simp
  have hFsm : AEStronglyMeasurable F (πhead.prod πtail) := by
    exact (hg.meas.comp e.symm.measurable).aestronglyMeasurable
  have hFint : Integrable F (πhead.prod πtail) := by
    have hcomp : Integrable (fun z : Fin m → X => F (e z)) π := by
      simpa [F, e, π] using hg.integrable
    exact (hmp.integrable_comp hFsm).mp hcomp
  have hsplit : ∫ z, g z ∂π = ∫ q, F q ∂(πhead.prod πtail) := by
    have h := hmp.integral_comp' F
    simpa [F, e, π] using h
  rw [uMeanOrder]
  change ∫ z, g z ∂π = 0
  rw [hsplit, integral_prod_symm F hFint]
  have hinner : ∀ tail : {k : Fin m // ¬ p k} → X,
      (∫ head : {k : Fin m // p k} → X, F (head, tail) ∂πhead) = 0 := by
    intro tail
    let a0 : {k : Fin m // p k} := ⟨j, rfl⟩
    have hmpu : MeasurePreserving (Function.eval a0) πhead P := by
      rw [hπhead_eval]
      simpa [p, a0] using
        (measurePreserving_eval (fun _ : {k : Fin m // p k} => P) a0)
    have hpoint :
        (fun head : {k : Fin m // p k} → X => F (head, tail))
          = fun head => F ((fun _ : {k : Fin m // p k} => head a0), tail) := by
      funext head
      congr 2
      ext a
      have ha : a = a0 := by
        cases a with
        | mk val property =>
          simp only [p] at property
          subst val
          rfl
      rw [ha]
    have hchange : (∫ head : {k : Fin m // p k} → X, F (head, tail) ∂πhead)
        = ∫ x : X, F ((fun _ : {k : Fin m // p k} => x), tail) ∂P := by
      rw [hpoint]
      have hsm : AEStronglyMeasurable
          (fun x : X => F ((fun _ : {k : Fin m // p k} => x), tail))
          (Measure.map (Function.eval a0) πhead) := by
        rw [hmpu.map_eq]
        exact (hg.meas.comp (by
          change Measurable (fun x : X => e.symm ((fun _ : {k : Fin m // p k} => x), tail))
          measurability)).aestronglyMeasurable
      have hmap := integral_map hmpu.measurable.aemeasurable hsm
      rw [hmpu.map_eq] at hmap
      exact hmap.symm
    rw [hchange]
    have hfun : (fun x : X => F ((fun _ : {k : Fin m // p k} => x), tail)) =
        fun x : X => g (insertCoord j x tail) := by
      funext x
      change g (fun k : Fin m => if h : k = j then x else tail ⟨k, h⟩)
        = g (insertCoord j x tail)
      rfl
    rw [hfun]
    exact hg.deg j tail
  rw [show (fun tail : {k : Fin m // ¬ p k} → X =>
      ∫ head : {k : Fin m // p k} → X, F (head, tail) ∂πhead)
        = fun _ => 0 by
      funext tail
      exact hinner tail]
  simp

end OrderDegenKernel

namespace IIDSample

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {m n : ℕ} {g : (Fin m → X) → ℝ} (S : IIDSample Ω X μ P)

/-! ## Unbiasedness and product-law transport -/

omit [IsProbabilityMeasure P] in
/-- An order-`m` kernel term along an injective tuple is integrable whenever the
kernel is integrable under the product law. -/
theorem integrable_orderKernelTerm {h : (Fin m → X) → ℝ}
    (hmeas : Measurable h)
    (hint : Integrable h (Measure.pi fun _ : Fin m => P))
    {t : Fin m → Fin n} (ht : Function.Injective t) :
    Integrable (fun ω => h (fun j => S.Z (t j : ℕ) ω)) μ := by
  have hmap : Integrable h
      (μ.map (fun ω : Ω => fun j : Fin m => S.Z (t j : ℕ) ω)) := by
    rw [S.map_tuple_eq ht]
    exact hint
  exact (integrable_map_measure hmeas.aestronglyMeasurable
    (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ))).aemeasurable).mp hmap

omit [IsProbabilityMeasure P] in
/-- The expectation of an injectively indexed order-`m` kernel term equals the
kernel's product-law mean. -/
theorem integral_orderKernelTerm_eq {h : (Fin m → X) → ℝ}
    (hmeas : Measurable h) {t : Fin m → Fin n} (ht : Function.Injective t) :
    ∫ ω, h (fun j => S.Z (t j : ℕ) ω) ∂μ =
      ∫ z, h z ∂(Measure.pi fun _ : Fin m => P) := by
  rw [← S.map_tuple_eq ht]
  rw [integral_map
    (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ))).aemeasurable
    hmeas.aestronglyMeasurable]

omit [IsProbabilityMeasure P] in
/-- An injectively indexed order-`m` kernel term has mean zero whenever the
kernel has zero product-law mean. -/
theorem integral_orderKernelTerm_eq_zero_of_uMean_zero {h : (Fin m → X) → ℝ}
    (hmeas : Measurable h) {t : Fin m → Fin n} (ht : Function.Injective t)
    (hmean_zero : uMeanOrder h P = 0) :
    ∫ ω, h (fun j => S.Z (t j : ℕ) ω) ∂μ = 0 := by
  rw [S.integral_orderKernelTerm_eq hmeas ht, ← uMeanOrder, hmean_zero]

omit [IsProbabilityMeasure P] in
/-- The fixed-order U-statistic is unbiased: its expectation is the product-law
kernel mean. -/
theorem integral_uStatisticOrder_eq_uMean {m n : ℕ} {h : (Fin m → X) → ℝ}
    (hmeas : Measurable h)
    (hint : Integrable h (Measure.pi fun _ : Fin m => P))
    (hmn : m ≤ n) :
    ∫ ω, uStatisticOrder S h n ω ∂μ = uMeanOrder h P := by
  classical
  have hcount_ne : injectiveTupleCount m n ≠ 0 := injectiveTupleCount_ne_zero hmn
  have hcard_ne : ((injectiveTuples m n).card : ℝ) ≠ 0 := by
    simpa [injectiveTupleCount] using hcount_ne
  have hterm_int : ∀ t ∈ injectiveTuples m n,
      Integrable (fun ω => h (fun j => S.Z (t j : ℕ) ω)) μ := by
    intro t ht
    exact S.integrable_orderKernelTerm hmeas hint ((Finset.mem_filter.mp ht).2)
  simp only [uStatisticOrder]
  rw [integral_const_mul,
    integral_finset_sum _ (fun t ht => hterm_int t ht)]
  have hsum_eval :
      (∑ t ∈ injectiveTuples m n,
        ∫ ω, h (fun j => S.Z (t j : ℕ) ω) ∂μ)
        =
      ∑ _t ∈ injectiveTuples m n,
        ∫ z, h z ∂(Measure.pi fun _ : Fin m => P) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact S.integral_orderKernelTerm_eq hmeas ((Finset.mem_filter.mp ht).2)
  rw [hsum_eval]
  rw [Finset.sum_const, nsmul_eq_mul, uMeanOrder]
  rw [injectiveTupleCount]
  field_simp [hcard_ne]

omit [IsProbabilityMeasure P] in
/-- A fixed-order U-statistic with product-law mean zero has expectation zero. -/
theorem integral_uStatisticOrder_eq_zero_of_uMean_zero {m n : ℕ}
    {h : (Fin m → X) → ℝ}
    (hmeas : Measurable h)
    (hint : Integrable h (Measure.pi fun _ : Fin m => P))
    (hmn : m ≤ n)
    (hmean_zero : uMeanOrder h P = 0) :
    ∫ ω, uStatisticOrder S h n ω ∂μ = 0 := by
  rw [S.integral_uStatisticOrder_eq_uMean hmeas hint hmn, hmean_zero]

omit [IsProbabilityMeasure P] in
/-- The rescaled fixed-order U-statistic has mean equal to the same rescaling of
the product-law kernel mean. -/
theorem integral_rescaled_uStatisticOrder_eq_sqrt_mul_uMean {m n : ℕ}
    {h : (Fin m → X) → ℝ}
    (hmeas : Measurable h)
    (hint : Integrable h (Measure.pi fun _ : Fin m => P))
    (hmn : m ≤ n) :
    ∫ ω, Real.sqrt (n : ℝ) * uStatisticOrder S h n ω ∂μ =
      Real.sqrt (n : ℝ) * uMeanOrder h P := by
  rw [integral_const_mul, S.integral_uStatisticOrder_eq_uMean hmeas hint hmn]

omit [IsProbabilityMeasure P] in
/-- If an order-`m` kernel has product-law mean zero, then the rescaled
fixed-order U-statistic has mean zero. -/
theorem integral_rescaled_uStatisticOrder_eq_zero_of_uMean_zero {m n : ℕ}
    {h : (Fin m → X) → ℝ}
    (hmeas : Measurable h)
    (hint : Integrable h (Measure.pi fun _ : Fin m => P))
    (hmn : m ≤ n)
    (hmean_zero : uMeanOrder h P = 0) :
    ∫ ω, Real.sqrt (n : ℝ) * uStatisticOrder S h n ω ∂μ = 0 := by
  rw [S.integral_rescaled_uStatisticOrder_eq_sqrt_mul_uMean hmeas hint hmn,
    hmean_zero, mul_zero]

/-- A fully degenerate order-`m` kernel whose product-law mean is zero gives a
mean-zero fixed-order U-statistic.  The product-law mean-zero assumption is kept
explicit here rather than inferred from coordinatewise degeneracy. -/
theorem integral_uStatisticOrder_eq_zero_of_degenKernel_uMean_zero [NeZero m]
    (hg : OrderDegenKernel P g) (hmn : m ≤ n)
    (hmean_zero : uMeanOrder g P = 0) :
    ∫ ω, uStatisticOrder S g n ω ∂μ = 0 :=
  S.integral_uStatisticOrder_eq_zero_of_uMean_zero hg.meas hg.integrable hmn hmean_zero

/-- A fully degenerate order-`m` kernel gives a mean-zero fixed-order
U-statistic in the nonempty sampling regime `m ≤ n`. -/
theorem integral_uStatisticOrder_eq_zero_of_degenKernel [NeZero m]
    (hg : OrderDegenKernel P g) (hmn : m ≤ n) :
    ∫ ω, uStatisticOrder S g n ω ∂μ = 0 :=
  S.integral_uStatisticOrder_eq_zero_of_degenKernel_uMean_zero hg hmn hg.integral_eq_zero

omit [IsProbabilityMeasure P] in
/-- An injectively indexed fully degenerate order-`m` kernel term has mean zero
when its product-law mean is zero. -/
theorem integral_orderTerm_eq_zero_of_degenKernel_uMean_zero [NeZero m]
    (hg : OrderDegenKernel P g) {t : Fin m → Fin n} (ht : Function.Injective t)
    (hmean_zero : uMeanOrder g P = 0) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) ∂μ = 0 :=
  S.integral_orderKernelTerm_eq_zero_of_uMean_zero hg.meas ht hmean_zero

/-- An injectively indexed fully degenerate order-`m` kernel term has mean
zero. -/
theorem integral_orderTerm_eq_zero [NeZero m]
    (hg : OrderDegenKernel P g) {t : Fin m → Fin n} (ht : Function.Injective t) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) ∂μ = 0 :=
  S.integral_orderTerm_eq_zero_of_degenKernel_uMean_zero hg ht hg.integral_eq_zero

/-- A fully degenerate order-`m` kernel whose product-law mean is zero gives a
mean-zero rescaled fixed-order U-statistic.  This is a mean statement only; it
does not assert the variance bound or negligibility. -/
theorem integral_rescaled_uStatisticOrder_eq_zero_of_degenKernel_uMean_zero [NeZero m]
    (hg : OrderDegenKernel P g) (hmn : m ≤ n)
    (hmean_zero : uMeanOrder g P = 0) :
    ∫ ω, Real.sqrt (n : ℝ) * uStatisticOrder S g n ω ∂μ = 0 :=
  S.integral_rescaled_uStatisticOrder_eq_zero_of_uMean_zero hg.meas hg.integrable
    hmn hmean_zero

/-- A fully degenerate order-`m` kernel gives a mean-zero rescaled fixed-order
U-statistic in the nonempty sampling regime `m ≤ n`.  This is a mean statement
only; it does not assert the variance bound or negligibility. -/
theorem integral_rescaled_uStatisticOrder_eq_zero_of_degenKernel [NeZero m]
    (hg : OrderDegenKernel P g) (hmn : m ≤ n) :
    ∫ ω, Real.sqrt (n : ℝ) * uStatisticOrder S g n ω ∂μ = 0 :=
  S.integral_rescaled_uStatisticOrder_eq_zero_of_degenKernel_uMean_zero hg hmn
    hg.integral_eq_zero

/-- `ζ_m = E[g(Z₁,…,Z_m)^2]`, the second moment of an order-`m` kernel under the
product law `P^m`.

This scalar is the diagonal second moment of an injectively indexed kernel term
and is the variance scale used in the exact variance and second-moment-bound
modules. -/
noncomputable def zetaOrder (P : Measure X) {m : ℕ}
    (g : (Fin m → X) → ℝ) : ℝ :=
  ∫ z, (g z) ^ 2 ∂(Measure.pi fun _ : Fin m => P)

/-- An order-`m` kernel term along an injective tuple is integrable. -/
theorem integrable_orderTerm [NeZero m] (hg : OrderDegenKernel P g)
    {t : Fin m → Fin n} (ht : Function.Injective t) :
    Integrable (fun ω => g (fun j => S.Z (t j : ℕ) ω)) μ := by
  have hmap : Integrable g
      (μ.map (fun ω : Ω => fun j : Fin m => S.Z (t j : ℕ) ω)) := by
    rw [S.map_tuple_eq ht]
    exact hg.integrable
  exact (integrable_map_measure hg.meas.aestronglyMeasurable
    (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ))).aemeasurable).mp hmap

omit [IsProbabilityMeasure P] in
/-- The square of an order-`m` kernel term along an injective tuple is
integrable. -/
theorem integrable_orderTerm_sq [NeZero m] (hg : OrderDegenKernel P g)
    {t : Fin m → Fin n} (ht : Function.Injective t) :
    Integrable (fun ω => (g (fun j => S.Z (t j : ℕ) ω)) ^ 2) μ := by
  have hmap : Integrable (fun z => (g z) ^ 2)
      (μ.map (fun ω : Ω => fun j : Fin m => S.Z (t j : ℕ) ω)) := by
    rw [S.map_tuple_eq ht]
    exact hg.sq
  exact (integrable_map_measure (hg.meas.pow_const 2).aestronglyMeasurable
    (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ))).aemeasurable).mp hmap

omit [IsProbabilityMeasure P] in
/-- Diagonal second moment of a single injective order-`m` kernel term. -/
theorem orderTerm_diag [NeZero m] (hg : OrderDegenKernel P g)
    {t : Fin m → Fin n} (ht : Function.Injective t) :
    ∫ ω, (g (fun j => S.Z (t j : ℕ) ω)) ^ 2 ∂μ = zetaOrder P g := by
  rw [zetaOrder]
  rw [← S.map_tuple_eq ht]
  rw [integral_map
    (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ))).aemeasurable
    (hg.meas.pow_const 2).aestronglyMeasurable]

omit [IsProbabilityMeasure P] in
/-- Each injective order-`m` kernel term is in `L²`. -/
theorem memLp_orderTerm [NeZero m] (hg : OrderDegenKernel P g)
    {t : Fin m → Fin n} (ht : Function.Injective t) :
    MemLp (fun ω => g (fun j => S.Z (t j : ℕ) ω)) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω => g (fun j => S.Z (t j : ℕ) ω)) μ :=
    (hg.meas.comp
      (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ)))).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).mpr (S.integrable_orderTerm_sq hg ht)

omit [IsProbabilityMeasure P] in
/-- The product of two injective order-`m` kernel terms is integrable. -/
theorem integrable_orderTerm_mul [NeZero m] (hg : OrderDegenKernel P g)
    {t q : Fin m → Fin n} (ht : Function.Injective t) (hq : Function.Injective q) :
    Integrable
      (fun ω => g (fun j => S.Z (t j : ℕ) ω) *
        g (fun j => S.Z (q j : ℕ) ω)) μ :=
  (S.memLp_orderTerm hg ht).integrable_mul (S.memLp_orderTerm hg hq)

/-- The injective-tuple sum of an order-`m` degenerate kernel is integrable. -/
theorem integrable_injectiveTuples_sum [NeZero m] (hg : OrderDegenKernel P g)
    (n : ℕ) :
    Integrable (fun ω => ∑ t ∈ injectiveTuples m n,
      g (fun j => S.Z (t j : ℕ) ω)) μ := by
  apply integrable_finset_sum
  intro t ht
  exact S.integrable_orderTerm hg ((Finset.mem_filter.mp ht).2)

omit [IsProbabilityMeasure P] in
/-- The injective-tuple sum of an order-`m` degenerate kernel is in `L²`. -/
theorem memLp_injectiveTuples_sum [NeZero m] (hg : OrderDegenKernel P g)
    (n : ℕ) :
    MemLp (fun ω => ∑ t ∈ injectiveTuples m n,
      g (fun j => S.Z (t j : ℕ) ω)) 2 μ := by
  have hsum := memLp_finset_sum (μ := μ) (p := 2) (injectiveTuples m n)
    (f := fun t ω => g (fun j => S.Z (t j : ℕ) ω))
    (fun t ht => S.memLp_orderTerm hg ((Finset.mem_filter.mp ht).2))
  simpa using hsum

omit [IsProbabilityMeasure P] in
/-- The rescaled order-`m` degenerate U-statistic is in `L²`. -/
theorem memLp_rescaled_order [NeZero m] (hg : OrderDegenKernel P g) (n : ℕ) :
    MemLp (fun ω => Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) 2 μ := by
  have hsum : MemLp (fun ω => ∑ t ∈ injectiveTuples m n,
      g (fun j => S.Z (t j : ℕ) ω)) 2 μ :=
    S.memLp_injectiveTuples_sum hg n
  have : (fun ω => Real.sqrt (n : ℝ) * uStatisticOrder S g n ω)
      = (fun ω => (Real.sqrt (n : ℝ) * (injectiveTupleCount m n)⁻¹)
          * ∑ t ∈ injectiveTuples m n, g (fun j => S.Z (t j : ℕ) ω)) := by
    funext ω
    simp only [uStatisticOrder]
    ring
  rw [this]
  exact hsum.const_mul _

omit [IsProbabilityMeasure P] in
/-- `ζ_m` is nonnegative. -/
theorem zetaOrder_nonneg {m : ℕ} {g : (Fin m → X) → ℝ} :
    0 ≤ zetaOrder P g :=
  integral_nonneg (fun _ => sq_nonneg _)

end IIDSample

end Causalean.Stat
