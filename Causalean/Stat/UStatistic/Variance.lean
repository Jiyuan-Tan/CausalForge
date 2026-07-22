/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exact variance of the degenerate order-2 U-statistic (thin `m = 2` shell)

For a symmetric, square-integrable, doubly-degenerate kernel `g` the rescaled
degenerate U-statistic `√n · Gₙ` has the exact second moment `2ζ / (n−1)`,
`ζ = ∬ g² dP dP`.  This is the `m = 2` case of the general fixed-order exact
variance `Causalean.Stat.UStatistic.OrderM.ExactVariance`
(`integral_injectiveTuples_sum_sq_degen`, `integral_rescaled_order_sq_degen`):
the unscaled formula gives `2ζ / (n(n−1))`, while the rescaled formula
`n · m! · ζ_m / n^{(m)}` gives `2ζ / (n−1)`.

The bespoke order-2 second-moment computation has been **retired** in favour of
that general result: the `DegenKernel` hypothesis and the second-moment lemmas
below are kept (they are the interface consumed by the higher-order
influence-function estimators, `Causalean.Stat.Nonparametric.HOIF`), but their
proofs now route through the order-`m` theory via the paired kernel `pairKernel g`
and the bridges `DegenKernel.toOrderDegenKernel`, `zeta_eq_zetaOrder`.
-/

import Causalean.Stat.UStatistic.OrderM.ExactVariance

/-!
Defines the degenerate order-2 kernel interface and proves its variance facts
through the fixed-order theory.

The structure `DegenKernel` records the measurable, symmetric,
square-integrable, doubly degenerate kernels used by higher-order
influence-function arguments.  Its bridge `DegenKernel.toOrderDegenKernel`
turns such a kernel into a completely degenerate `Fin 2` kernel, while
`zeta_eq_zetaOrder` identifies the order-2 second moment with the fixed-order
quantity.  The public theorems `integral_offDiag_sum_sq`,
`integral_rescaled_sq`, `memLp_rescaled`, and `integral_rescaled_eq_zero`
provide the exact order-2 second-moment, `L²`, and mean-zero facts.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

private theorem injectiveTupleCount_two_eq_offDiag_card (n : ℕ) :
    injectiveTupleCount 2 n = ((Finset.range n).offDiag.card : ℝ) := by
  have hdesc : ((n.descFactorial 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    by_cases hn0 : n = 0
    · subst n
      norm_num [Nat.descFactorial]
    · have hle : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
      simp [Nat.descFactorial, Nat.cast_sub hle]
      ring
  have hoff : ((Finset.range n).offDiag.card : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Finset.offDiag_card, Finset.card_range]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hle : n ≤ n * n := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hn0)
      rw [Nat.cast_sub hle, Nat.cast_mul]
      ring
  rw [injectiveTupleCount_eq_descFactorial, hdesc, hoff]

private theorem injectiveTupleCount_two_eq_mul_sub_one {n : ℕ} (hn : 2 ≤ n) :
    injectiveTupleCount 2 n = (n : ℝ) * ((n : ℝ) - 1) := by
  rw [injectiveTupleCount_eq_descFactorial]
  have hle1 : 1 ≤ n := by omega
  simp [Nat.descFactorial, Nat.cast_sub hle1]
  ring

private theorem rescaled_order_two_arith {n : ℕ} (hn : 2 ≤ n) (ζ : ℝ) :
    (n : ℝ) * (Nat.factorial 2 : ℝ) * ζ / injectiveTupleCount 2 n
      = 2 * ζ / ((n : ℝ) - 1) := by
  have hcount := injectiveTupleCount_two_eq_mul_sub_one hn
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn) : n ≠ 0)
  have hn1_ne : (n : ℝ) - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  rw [hcount]
  norm_num
  field_simp [hn_ne, hn1_ne]

/-! ## The degenerate order-2 kernel hypothesis -/

/-- Bundled hypotheses on a degenerate order-2 kernel `g`.

The kernel is measurable on `X × X`, symmetric, square-integrable under
`P × P`, and has zero conditional mean in each coordinate.  The field `deg`
states one coordinate condition; the other is derived as `DegenKernel.deg'`
using symmetry. -/
structure DegenKernel (P : Measure X) (g : X → X → ℝ) : Prop where
  meas : Measurable (fun p : X × X => g p.1 p.2)
  symm : ∀ x y, g x y = g y x
  deg  : ∀ x, ∫ y, g x y ∂P = 0
  sq   : Integrable (fun p : X × X => (g p.1 p.2) ^ 2) (P.prod P)

namespace DegenKernel

variable [IsProbabilityMeasure P] {g : X → X → ℝ}

/-- `g` is L¹ on the product law (probability space, from L²). -/
theorem integrable (hg : DegenKernel P g) :
    Integrable (fun p : X × X => g p.1 p.2) (P.prod P) :=
  ((memLp_two_iff_integrable_sq hg.meas.aestronglyMeasurable).mpr hg.sq).integrable
    (by norm_num)

omit [IsProbabilityMeasure P] in
/-- Left degeneracy, from symmetry and right degeneracy. -/
theorem deg' (hg : DegenKernel P g) (y : X) : ∫ x, g x y ∂P = 0 := by
  simp_rw [hg.symm _ y]; exact hg.deg y

/-- **Bridge to the order-`m` theory (`m = 2`).**  A degenerate order-2 kernel `g`
gives a completely-degenerate order-`2` kernel `pairKernel g` (`z ↦ g (z 0) (z 1)`):
symmetry of `pairKernel g` under `Equiv.Perm (Fin 2)` is `hg.symm`; the
single-coordinate integrals are `hg.deg` / `hg.deg'`; square-integrability
transports across the `Fin 2 → X` ≃ `X × X` product-law equivalence. -/
theorem toOrderDegenKernel (hg : DegenKernel P g) :
    OrderDegenKernel P (pairKernel g) := by
  refine
    { meas := ?_
      symm := ?_
      deg := ?_
      sq := ?_ }
  · change Measurable (fun z : Fin 2 → X => g (z 0) (z 1))
    have hcoord : Measurable (fun z : Fin 2 → X => (z 0, z 1)) :=
      (measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2))
    simpa using hg.meas.comp hcoord
  · intro σ z
    have hneq : σ (1 : Fin 2) ≠ σ (0 : Fin 2) := by
      intro h
      have : (1 : Fin 2) = 0 := σ.injective h
      norm_num at this
    by_cases hσ0 : σ (0 : Fin 2) = 0
    · have hσ1 : σ (1 : Fin 2) = 1 := by
        apply Fin.ext
        have hvlt : (σ (1 : Fin 2)).val < 2 := (σ (1 : Fin 2)).isLt
        have hvne : (σ (1 : Fin 2)).val ≠ 0 := by
          intro hv
          exact hneq (by rw [hσ0]; exact Fin.ext hv)
        omega
      unfold pairKernel
      simp [hσ0, hσ1]
    · have hσ0' : σ (0 : Fin 2) = 1 := by
        apply Fin.ext
        have hvlt : (σ (0 : Fin 2)).val < 2 := (σ (0 : Fin 2)).isLt
        have hvne : (σ (0 : Fin 2)).val ≠ 0 := by
          intro hv
          exact hσ0 (Fin.ext hv)
        omega
      have hσ1 : σ (1 : Fin 2) = 0 := by
        apply Fin.ext
        have hvlt : (σ (1 : Fin 2)).val < 2 := (σ (1 : Fin 2)).isLt
        by_contra hvne
        have hv1 : (σ (1 : Fin 2)).val = 1 := by omega
        exact hneq (by rw [hσ0']; exact Fin.ext hv1)
      unfold pairKernel
      simp [hσ0', hσ1, hg.symm]
  · intro j tail
    fin_cases j
    · let a : {k : Fin 2 // k ≠ (0 : Fin 2)} := ⟨1, by norm_num⟩
      change ∫ x, pairKernel g (insertCoord (0 : Fin 2) x tail) ∂P = 0
      have hfun :
          (fun x => pairKernel g (insertCoord (0 : Fin 2) x tail))
            = fun x => g x (tail a) := by
        funext x
        simp [pairKernel, insertCoord, a]
      rw [hfun]
      exact hg.deg' (tail a)
    · let a : {k : Fin 2 // k ≠ (1 : Fin 2)} := ⟨0, by norm_num⟩
      change ∫ x, pairKernel g (insertCoord (1 : Fin 2) x tail) ∂P = 0
      have hfun :
          (fun x => pairKernel g (insertCoord (1 : Fin 2) x tail))
            = fun x => g (tail a) x := by
        funext x
        simp [pairKernel, insertCoord, a]
      rw [hfun]
      exact hg.deg (tail a)
  · let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => X)
    have hmp : MeasurePreserving e
        (Measure.pi fun _ : Fin 2 => P) (P.prod P) := by
      simpa [e] using (measurePreserving_piFinTwo (fun _ : Fin 2 => P))
    simpa [pairKernel, e] using hmp.integrable_comp_of_integrable hg.sq

end DegenKernel

namespace IIDSample

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {g : X → X → ℝ} (S : IIDSample Ω X μ P)

/-- `ζ = ∬ g² dP dP`, the second moment of the kernel. -/
noncomputable def zeta (P : Measure X) (g : X → X → ℝ) : ℝ :=
  ∫ p, (g p.1 p.2) ^ 2 ∂(P.prod P)

omit [IsProbabilityMeasure μ] in
/-- The order-2 second moment `ζ` equals the order-`m` second moment `ζ_m` of the
paired kernel: `∬ g² dP dP = ∫ (pairKernel g)² dP²`.  A change of variables along
the `Fin 2 → X` ≃ `X × X` measure equivalence. -/
theorem zeta_eq_zetaOrder : zeta P g = zetaOrder P (pairKernel g) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => X)
  have hmp : MeasurePreserving e
      (Measure.pi fun _ : Fin 2 => P) (P.prod P) := by
    simpa [e] using (measurePreserving_piFinTwo (fun _ : Fin 2 => P))
  have hsplit :
      ∫ z : Fin 2 → X, (g (z 0) (z 1)) ^ 2 ∂(Measure.pi fun _ : Fin 2 => P)
        = ∫ p : X × X, (g p.1 p.2) ^ 2 ∂(P.prod P) := by
    simpa [e] using hmp.integral_comp' (fun p : X × X => (g p.1 p.2) ^ 2)
  unfold zeta zetaOrder pairKernel
  exact hsplit.symm

omit [IsProbabilityMeasure P] in
/-- `ζ ≥ 0`. -/
theorem zeta_nonneg : 0 ≤ zeta P g :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- **Second moment of the off-diagonal sum.**
`E[(Σ_{p ∈ offDiag} g(Z_{p.1},Z_{p.2}))²] = 2 · |offDiag| · ζ`.  The `m = 2` case of
`integral_injectiveTuples_sum_sq_degen`, using
`sum_injectiveTuples_two_eq_offDiag`, `toOrderDegenKernel`, and `zeta_eq_zetaOrder`
(`2! = 2`, `injectiveTupleCount 2 n = |offDiag| = n(n−1)`). -/
theorem integral_offDiag_sum_sq (hg : DegenKernel P g) (n : ℕ) :
    ∫ ω, (∑ p ∈ (Finset.range n).offDiag, g (S.Z p.1 ω) (S.Z p.2 ω)) ^ 2 ∂μ
      = 2 * ((Finset.range n).offDiag.card : ℝ) * zeta P g := by
  have hpoint :
      (fun ω =>
          (∑ p ∈ (Finset.range n).offDiag, g (S.Z p.1 ω) (S.Z p.2 ω)) ^ 2)
        =
      (fun ω =>
          (∑ t ∈ injectiveTuples 2 n,
            pairKernel g (fun j => S.Z (t j : ℕ) ω)) ^ 2) := by
    funext ω
    rw [sum_injectiveTuples_two_eq_offDiag S g n ω]
  rw [hpoint, S.integral_injectiveTuples_sum_sq_degen hg.toOrderDegenKernel n,
    ← zeta_eq_zetaOrder, injectiveTupleCount_two_eq_offDiag_card n]
  norm_num

/-- **L² bound on the rescaled degenerate U-statistic.** For `n ≥ 2`,
`E[(√n · Gₙ)²] = 2ζ / (n−1)`.  The `m = 2` case of
`integral_rescaled_order_sq_degen` (`n · 2! · ζ / n^{(2)} = 2ζ/(n−1)`), via
`uStatisticOrder_two_eq_uStatistic` and `zeta_eq_zetaOrder`. -/
theorem integral_rescaled_sq (hg : DegenKernel P g) {n : ℕ} (hn : 2 ≤ n) :
    ∫ ω, (Real.sqrt (n : ℝ) * uStatistic S g n ω) ^ 2 ∂μ
      = 2 * zeta P g / ((n : ℝ) - 1) := by
  have h := S.integral_rescaled_order_sq_degen hg.toOrderDegenKernel hn
  rw [uStatisticOrder_two_eq_uStatistic S g n, ← zeta_eq_zetaOrder] at h
  rw [h]
  exact rescaled_order_two_arith hn (zeta P g)

/-- The rescaled degenerate U-statistic is in `L²`. -/
theorem memLp_rescaled (hg : DegenKernel P g) (n : ℕ) :
    MemLp (fun ω => Real.sqrt (n : ℝ) * uStatistic S g n ω) 2 μ := by
  simpa [uStatisticOrder_two_eq_uStatistic S g n] using
    S.memLp_rescaled_order hg.toOrderDegenKernel n

/-- The rescaled degenerate U-statistic has mean zero. -/
theorem integral_rescaled_eq_zero (hg : DegenKernel P g) (n : ℕ) :
    ∫ ω, Real.sqrt (n : ℝ) * uStatistic S g n ω ∂μ = 0 := by
  by_cases hn : 2 ≤ n
  · have h := S.integral_rescaled_uStatisticOrder_eq_zero_of_degenKernel
      hg.toOrderDegenKernel hn
    simpa [uStatisticOrder_two_eq_uStatistic S g n] using h
  · have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · simp [uStatistic]
    · simp [uStatistic]

end IIDSample

end Causalean.Stat
