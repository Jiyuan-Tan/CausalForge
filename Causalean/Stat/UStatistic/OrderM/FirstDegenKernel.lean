/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# First-order degenerate order-`m` kernels and their `L²` transport

This file introduces `OrderFirstDegenKernel`, the correct hypothesis for the
higher-order U-statistic remainder: a measurable, square-integrable order-`m`
kernel whose conditional mean given any single coordinate is zero (equivalently,
whose mean and every first Hoeffding projection vanish).  This is *strictly
weaker* than the complete degeneracy of `OrderDegenKernel` (`OrderM/Hajek`) and
is exactly what the residual `uDegenOrder h P` satisfies for every order `m`; the
two notions coincide only at `m = 2`.

It also collects the `L²`/product-law transport lemmas that depend only on
measurability and square-integrability (no degeneracy), so they apply to
`OrderFirstDegenKernel`.  These mirror the `OrderDegenKernel` transport lemmas of
`OrderM/Variance`; keeping them here makes the first-order-degenerate remainder
path usable without requiring complete degeneracy.
-/

import Causalean.Stat.UStatistic.OrderM.Variance

/-!
# First-order degenerate fixed-order kernels

This module introduces `OrderFirstDegenKernel`, a measurable square-integrable
order-`m` kernel whose conditional mean is zero after integrating out all
coordinates except any chosen one.  This is the degeneracy notion satisfied by
the first-order Hoeffding residual in the fixed-order U-statistic CLT.

The namespace results show that such kernels are integrable and have product-law
mean zero (`OrderFirstDegenKernel.integrable` and
`OrderFirstDegenKernel.integral_eq_zero`).  The `IIDSample` lemmas transport
measurability and square-integrability along injective sample tuples, giving
`integrable_sqKernelTerm_sq`, `memLp_sqKernelTerm`,
`integrable_sqKernelTerm_mul`, and `memLp_rescaled_sqKernel` for downstream
remainder bounds.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- A first-order degenerate order-`m` kernel: measurable, square-integrable, and
mean-zero in each coordinate after integrating out the other `m − 1`
coordinates. -/
structure OrderFirstDegenKernel (P : Measure X) {m : ℕ} [NeZero m]
    (g : (Fin m → X) → ℝ) : Prop where
  meas : Measurable g
  /-- The first Hoeffding projection in every coordinate vanishes: integrating
  out the `m − 1` tail coordinates leaves `0`. -/
  firstDeg : ∀ (j : Fin m) (x : X),
    ∫ tail : ({k : Fin m // k ≠ j}) → X,
        g (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P) = 0
  sq : Integrable (fun z => (g z) ^ 2) (Measure.pi fun _ : Fin m => P)

namespace OrderFirstDegenKernel

variable [IsProbabilityMeasure P] {m : ℕ} [NeZero m] {g : (Fin m → X) → ℝ}

/-- A first-order degenerate square-integrable kernel is integrable under the
product law. -/
theorem integrable (hg : OrderFirstDegenKernel P g) :
    Integrable g (Measure.pi fun _ : Fin m => P) :=
  ((memLp_two_iff_integrable_sq hg.meas.aestronglyMeasurable).mpr hg.sq).integrable
    (by norm_num)

/-- The product-law mean of a first-order degenerate kernel is zero: split off the
first coordinate with `measurePreserving_piEquivPiSubtypeProd` (as in
`OrderDegenKernel.integral_eq_zero`) and apply the coordinate-`0` first-projection
identity `firstDeg`. -/
theorem integral_eq_zero (hg : OrderFirstDegenKernel P g) :
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
  rw [hsplit, integral_prod F hFint]
  have hinner : ∀ head : {k : Fin m // p k} → X,
      (∫ tail : {k : Fin m // ¬ p k} → X, F (head, tail) ∂πtail) = 0 := by
    intro head
    let a0 : {k : Fin m // p k} := ⟨j, rfl⟩
    have hhead :
        (fun tail : {k : Fin m // ¬ p k} → X => F (head, tail))
          = fun tail => F ((fun _ : {k : Fin m // p k} => head a0), tail) := by
      funext tail
      congr 2
      ext a
      have ha : a = a0 := by
        cases a with
        | mk val property =>
          simp only [p] at property
          subst val
          rfl
      rw [ha]
    rw [hhead]
    have hfun : (fun tail : {k : Fin m // ¬ p k} → X =>
          F ((fun _ : {k : Fin m // p k} => head a0), tail))
        = fun tail : ({k : Fin m // k ≠ j}) → X => g (insertCoord j (head a0) tail) := by
      funext tail
      change g (fun k : Fin m => if h : k = j then head a0 else tail ⟨k, h⟩)
        = g (insertCoord j (head a0) tail)
      rfl
    rw [hfun]
    exact hg.firstDeg j (head a0)
  rw [show (fun head : {k : Fin m // p k} → X =>
      ∫ tail : {k : Fin m // ¬ p k} → X, F (head, tail) ∂πtail)
        = fun _ => 0 by
      funext head
      exact hinner head]
  simp

end OrderFirstDegenKernel

/-! ## `L²` transport for measurable square-integrable kernels

All of these use only `hmeas` and `hsq` (no degeneracy).  They mirror the
`OrderDegenKernel`-bundled versions in `OrderM/Variance`; the proofs there go
through `S.map_tuple_eq` + `integrable_map_measure` / `memLp_two_iff_integrable_sq`
and transcribe verbatim with `hmeas`, `hsq`, and the derived `hint`. -/

namespace IIDSample

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {m n : ℕ} {g : (Fin m → X) → ℝ} (S : IIDSample Ω X μ P)

omit [IsProbabilityMeasure P] in
/-- The square of an order-`m` kernel term along an injective tuple is
integrable. -/
theorem integrable_sqKernelTerm_sq (hmeas : Measurable g)
    (hsq : Integrable (fun z => (g z) ^ 2) (Measure.pi fun _ : Fin m => P))
    {t : Fin m → Fin n} (ht : Function.Injective t) :
    Integrable (fun ω => (g (fun j => S.Z (t j : ℕ) ω)) ^ 2) μ := by
  have hmap : Integrable (fun z => (g z) ^ 2)
      (μ.map (fun ω : Ω => fun j : Fin m => S.Z (t j : ℕ) ω)) := by
    rw [S.map_tuple_eq ht]
    exact hsq
  exact (integrable_map_measure (hmeas.pow_const 2).aestronglyMeasurable
    (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ))).aemeasurable).mp hmap

omit [IsProbabilityMeasure P] in
/-- Each injective order-`m` kernel term is in `L²`. -/
theorem memLp_sqKernelTerm (hmeas : Measurable g)
    (hsq : Integrable (fun z => (g z) ^ 2) (Measure.pi fun _ : Fin m => P))
    {t : Fin m → Fin n} (ht : Function.Injective t) :
    MemLp (fun ω => g (fun j => S.Z (t j : ℕ) ω)) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω => g (fun j => S.Z (t j : ℕ) ω)) μ :=
    (hmeas.comp
      (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ)))).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).mpr (S.integrable_sqKernelTerm_sq hmeas hsq ht)

omit [IsProbabilityMeasure P] in
/-- The product of two injective order-`m` kernel terms is integrable. -/
theorem integrable_sqKernelTerm_mul (hmeas : Measurable g)
    (hsq : Integrable (fun z => (g z) ^ 2) (Measure.pi fun _ : Fin m => P))
    {t q : Fin m → Fin n} (ht : Function.Injective t) (hq : Function.Injective q) :
    Integrable
      (fun ω => g (fun j => S.Z (t j : ℕ) ω) *
        g (fun j => S.Z (q j : ℕ) ω)) μ :=
  (S.memLp_sqKernelTerm hmeas hsq ht).integrable_mul (S.memLp_sqKernelTerm hmeas hsq hq)

omit [IsProbabilityMeasure P] in
/-- The rescaled injective-tuple sum `√n · Uₙ` is in `L²`. -/
theorem memLp_rescaled_sqKernel (hmeas : Measurable g)
    (hsq : Integrable (fun z => (g z) ^ 2) (Measure.pi fun _ : Fin m => P)) (n : ℕ) :
    MemLp (fun ω => Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) 2 μ := by
  have hsum : MemLp (fun ω => ∑ t ∈ injectiveTuples m n,
      g (fun j => S.Z (t j : ℕ) ω)) 2 μ := by
    have hsum := memLp_finset_sum (μ := μ) (p := 2) (injectiveTuples m n)
      (f := fun t ω => g (fun j => S.Z (t j : ℕ) ω))
      (fun t ht => S.memLp_sqKernelTerm hmeas hsq ((Finset.mem_filter.mp ht).2))
    simpa using hsum
  have : (fun ω => Real.sqrt (n : ℝ) * uStatisticOrder S g n ω)
      = (fun ω => (Real.sqrt (n : ℝ) * (injectiveTupleCount m n)⁻¹)
          * ∑ t ∈ injectiveTuples m n, g (fun j => S.Z (t j : ℕ) ω)) := by
    funext ω
    simp only [uStatisticOrder]
    ring
  rw [this]
  exact hsum.const_mul _

end IIDSample

end Causalean.Stat
