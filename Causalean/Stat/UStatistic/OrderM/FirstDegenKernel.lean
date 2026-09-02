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

The generic `L²`/product-law transport lemmas from `OrderM/Variance` apply
directly because they require only measurability and square-integrability, not
complete degeneracy.
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
`OrderFirstDegenKernel.integral_eq_zero`). Generic `IIDSample` transport lemmas
from `OrderM.Variance` supply the downstream `L²` bounds.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- **First-order degenerate order-`m` kernel.** A kernel `g` on `m`-tuples over `X`, together
with the population measure `P`, is first-order degenerate when [`g` is
measurable](hyp:meas), [its first Hoeffding projection vanishes in every coordinate —
integrating `g` over the other $m-1$ coordinates against the product measure leaves zero,
whichever coordinate and value are held fixed](hyp:firstDeg), and [`g` is square-integrable
under the product measure $P^{\otimes m}$](hyp:sq). -/
structure OrderFirstDegenKernel (P : Measure X) {m : ℕ} [NeZero m]
    (g : (Fin m → X) → ℝ) : Prop where
  meas : Measurable g
  /-- The first Hoeffding projection in every coordinate vanishes: integrating
  out the `m − 1` tail coordinates leaves `0`. -/
  firstDeg : ∀ (j : Fin m) (x : X),
    ∫ tail : ({k : Fin m // k ≠ j}) → X,
        g (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P) = 0
  sq : Integrable (fun z => (g z) ^ 2) (Measure.pi fun _ : Fin m => P)

-- Measurability and square-integrability of a first-order degenerate order-`m` kernel are
-- exposed to the function-property tactics, so a proof holding an `OrderFirstDegenKernel`
-- hypothesis need not name these fields.
attribute [fun_prop] OrderFirstDegenKernel.meas OrderFirstDegenKernel.sq

namespace OrderFirstDegenKernel

variable [IsProbabilityMeasure P] {m : ℕ} [NeZero m] {g : (Fin m → X) → ℝ}

omit [IsProbabilityMeasure P] in
/-- A first-order degenerate square-integrable kernel is integrable under the
product law. -/
@[fun_prop]
theorem integrable [IsFiniteMeasure P] (hg : OrderFirstDegenKernel P g) :
    Integrable g (Measure.pi fun _ : Fin m => P) :=
  ((memLp_two_iff_integrable_sq hg.meas.aestronglyMeasurable).mpr hg.sq).integrable
    (by norm_num)

omit [IsProbabilityMeasure P] in
/-- **Population mean of a first-order degenerate kernel is zero.** If the order-`m`
kernel `g` is [first-order degenerate: measurable, square-integrable under the `m`-fold
product law, and with zero mean after integrating out all but any single
coordinate](hyp:hg), then [the population mean of `g` under the `m`-fold product law is
zero](goal).

Proof: split off the first coordinate with `measurePreserving_piEquivPiSubtypeProd` (as
in `OrderDegenKernel.integral_eq_zero`) and apply the coordinate-`0` first-projection
identity `firstDeg`. -/
theorem integral_eq_zero [IsFiniteMeasure P] (hg : OrderFirstDegenKernel P g) :
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

end Causalean.Stat
