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

The module also gives a nonasymptotic variance bound for a bounded
off-diagonal kernel average without any degeneracy assumption.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- The number of ordered injective pairs from a sample of size `n` equals the number of
off-diagonal ordered pairs drawn from that sample. -/
theorem injectiveTupleCount_two_eq_offDiag_card (n : ℕ) :
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

/-- For a sample of size at least two, the number of ordered injective pairs is the sample size
times one less than the sample size. -/
theorem injectiveTupleCount_two_eq_mul_sub_one {n : ℕ} (hn : 2 ≤ n) :
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

/-- **Degenerate order-2 kernel.** A kernel `g : X → X → ℝ` is doubly degenerate under the
measure `P` when [`g` is measurable as a function on $X \times X$](hyp:meas), [`g` is
symmetric, $g(x,y) = g(y,x)$](hyp:symm), [integrating `g` over its second argument against
`P` gives zero for every fixed first argument](hyp:deg), and [`g` is square-integrable under
the product measure $P \times P$](hyp:sq).

The kernel is measurable on `X × X`, symmetric, square-integrable under
`P × P`, and has zero conditional mean in each coordinate.  The field `deg`
states one coordinate condition; the other is derived as `DegenKernel.deg'`
using symmetry. -/
structure DegenKernel (P : Measure X) (g : X → X → ℝ) : Prop where
  meas : Measurable (fun p : X × X => g p.1 p.2)
  symm : ∀ x y, g x y = g y x
  deg  : ∀ x, ∫ y, g x y ∂P = 0
  sq   : Integrable (fun p : X × X => (g p.1 p.2) ^ 2) (P.prod P)

-- Square-integrability of a doubly degenerate order-2 kernel is exposed to the
-- function-property tactics.  The companion `meas` field is deliberately NOT tagged: its
-- statement is measurability of `fun p => g p.1 p.2`, a shape `fun_prop` rejects outright,
-- so measurability of an order-2 kernel stays name-called.
attribute [fun_prop] DegenKernel.sq

namespace DegenKernel

variable [IsProbabilityMeasure P] {g : X → X → ℝ}

omit [IsProbabilityMeasure P] in
/-- `g` is L¹ on a finite product measure, from L². -/
theorem integrable [IsFiniteMeasure P] (hg : DegenKernel P g) :
    Integrable (fun p : X × X => g p.1 p.2) (P.prod P) :=
  ((memLp_two_iff_integrable_sq hg.meas.aestronglyMeasurable).mpr hg.sq).integrable
    (by norm_num)

omit [IsProbabilityMeasure P] in
/-- Left degeneracy, from symmetry and right degeneracy. -/
theorem deg' (hg : DegenKernel P g) (y : X) : ∫ x, g x y ∂P = 0 := by
  simp_rw [hg.symm _ y]; exact hg.deg y

omit [IsProbabilityMeasure P] in
/-- **Bridge to the order-`m` theory (`m = 2`).** If the two-argument kernel
`g : X → X → ℝ` is [degenerate: measurable, symmetric, square-integrable under
`P × P`, and with zero conditional mean in each coordinate](hyp:hg), then [the paired
order-2 kernel `pairKernel g`, defined by `z ↦ g(z 0, z 1)`, is completely degenerate
in the order-`m` sense](goal).

Symmetry of `pairKernel g` under `Equiv.Perm (Fin 2)` is `hg.symm`; the
single-coordinate integrals are `hg.deg` / `hg.deg'`; square-integrability
transports across the `Fin 2 → X` ≃ `X × X` product-law equivalence. -/
theorem toOrderDegenKernel [SigmaFinite P] (hg : DegenKernel P g) :
    OrderDegenKernel P (pairKernel g) := by
  refine
    { meas := ?_
      symm := ?_
      deg := ?_
      sq := ?_ }
  · change Measurable (fun z : Fin 2 → X => g (z 0) (z 1))
    have hcoord : Measurable (fun z : Fin 2 → X => (z 0, z 1)) :=
      (measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2))
    exact hg.meas.comp hcoord
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
    simpa [pairKernel, e, Function.comp_def] using hmp.integrable_comp_of_integrable hg.sq

end DegenKernel

namespace IIDSample

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {g : X → X → ℝ} (S : IIDSample Ω X μ P)

/-- `ζ = ∬ g² dP dP`, the second moment of the kernel. -/
noncomputable def zeta (P : Measure X) (g : X → X → ℝ) : ℝ :=
  ∫ p, (g p.1 p.2) ^ 2 ∂(P.prod P)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The order-2 second moment `ζ` equals the order-`m` second moment `ζ_m` of the
paired kernel: `∬ g² dP dP = ∫ (pairKernel g)² dP²`.  A change of variables along
the `Fin 2 → X` ≃ `X × X` measure equivalence. -/
theorem zeta_eq_zetaOrder [SigmaFinite P] : zeta P g = zetaOrder P (pairKernel g) := by
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

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- **Second moment of the off-diagonal sum.** For an i.i.d. sample `S` and sample size
`n`, if the two-argument kernel `g` is [degenerate](hyp:hg), then [the second moment of
the sum of `g(Z_i, Z_j)` over all ordered off-diagonal index pairs `i ≠ j` below `n`
equals `2 · |offDiag| · ζ`, where `ζ` is the kernel's second moment under
`P × P`](goal). The `m = 2` case of `integral_injectiveTuples_sum_sq_degen`, using
`sum_injectiveTuples_two_eq_offDiag`, `toOrderDegenKernel`, and `zeta_eq_zetaOrder`
(`2! = 2`, `injectiveTupleCount 2 n = |offDiag| = n(n−1)`). -/
theorem integral_offDiag_sum_sq (hg : DegenKernel P g) (n : ℕ) :
    ∫ ω, (∑ p ∈ (Finset.range n).offDiag, g (S.Z p.1 ω) (S.Z p.2 ω)) ^ 2 ∂μ
      = 2 * ((Finset.range n).offDiag.card : ℝ) * zeta P g := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
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

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- **L² bound on the rescaled degenerate U-statistic.** For an i.i.d. sample `S`, if
the two-argument kernel `g` is [degenerate](hyp:hg) and the sample size [is at least
two](hyp:hn), then [the second moment of the `√n`-rescaled degenerate U-statistic of
`g` equals `2ζ/(n−1)`, where `ζ` is the kernel's second moment under `P × P`](goal). The
`m = 2` case of `integral_rescaled_order_sq_degen`
(`n · 2! · ζ / n^{(2)} = 2ζ/(n−1)`), via `uStatisticOrder_two_eq_uStatistic` and
`zeta_eq_zetaOrder`. -/
theorem integral_rescaled_sq (hg : DegenKernel P g) {n : ℕ} (hn : 2 ≤ n) :
    ∫ ω, (Real.sqrt (n : ℝ) * uStatistic S g n ω) ^ 2 ∂μ
      = 2 * zeta P g / ((n : ℝ) - 1) := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have h := S.integral_rescaled_order_sq_degen hg.toOrderDegenKernel hn
  rw [uStatisticOrder_two_eq_uStatistic S g n, ← zeta_eq_zetaOrder] at h
  rw [h]
  exact rescaled_order_two_arith hn (zeta P g)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The rescaled degenerate U-statistic is in `L²`. -/
theorem memLp_rescaled (hg : DegenKernel P g) (n : ℕ) :
    MemLp (fun ω => Real.sqrt (n : ℝ) * uStatistic S g n ω) 2 μ := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  simpa [uStatisticOrder_two_eq_uStatistic S g n] using
    S.memLp_rescaled_order hg.toOrderDegenKernel.meas hg.toOrderDegenKernel.sq n

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The rescaled degenerate U-statistic has mean zero. -/
theorem integral_rescaled_eq_zero (hg : DegenKernel P g) (n : ℕ) :
    ∫ ω, Real.sqrt (n : ℝ) * uStatistic S g n ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  by_cases hn : 2 ≤ n
  · have h := S.integral_rescaled_uStatisticOrder_eq_zero_of_degenKernel
      hg.toOrderDegenKernel hn
    simpa [uStatisticOrder_two_eq_uStatistic S g n] using h
  · have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · simp [uStatistic]
    · simp [uStatistic]

end IIDSample

set_option maxHeartbeats 800000 in
-- Expanding variance into all covariance pairs and counting overlaps needs a larger budget.
/-- A bounded kernel's off-diagonal average over an independent sample
has variance at most thirty-two times the squared kernel bound divided by the sample size.

Unlike the exact `DegenKernel` second-moment results above, this bound requires no
degeneracy assumption and therefore complements rather than competes with them. -/
lemma variance_offDiag_kernel_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (N : ℕ)
    (kernel : X → X → ℝ) (hkernel : Measurable (Function.uncurry kernel))
    (M : ℝ) (hbound : ∀ x y, |kernel x y| ≤ M) :
    variance
        (fun target : Fin N → X =>
          ((N : ℝ) * (N - 1 : ℕ))⁻¹ *
            ∑ i, ∑ j, if i ≠ j then kernel (target i) (target j) else 0)
        (Measure.pi (fun _ : Fin N => μ)) ≤
      32 * M ^ 2 / (N : ℝ) := by
  classical
  have hM : 0 ≤ M := by
    let x : X := (nonempty_of_isProbabilityMeasure μ).some
    exact (abs_nonneg (kernel x x)).trans (hbound x x)
  rcases Nat.lt_or_ge N 2 with hNsmall | hNtwo
  · have hcases : N = 0 ∨ N = 1 := by omega
    rcases hcases with rfl | rfl
    · simp [show (fun _ : (Fin 0 → X) => (0 : ℝ)) = 0 by rfl, variance_zero]
    · simp [show (fun _ : (Fin 1 → X) => (0 : ℝ)) = 0 by rfl, variance_zero,
        sq_nonneg M]
  let μN := Measure.pi (fun _ : Fin N => μ)
  let b : Fin N → Fin N → (Fin N → X) → ℝ := fun i j target =>
    if i ≠ j then kernel (target i) (target j) else 0
  have hbmeas (i j : Fin N) : Measurable (b i j) := by
    dsimp only [b]
    split_ifs
    · have hp : Measurable (fun target : Fin N → X =>
          (target i, target j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact (show Measurable (fun target : Fin N → X =>
        Function.uncurry kernel (target i, target j)) from hkernel.comp hp)
    · exact measurable_const
  have hbbound (i j : Fin N) (target : Fin N → X) :
      |b i j target| ≤ M := by
    dsimp only [b]
    split_ifs
    · exact hbound _ _
    · simpa using hM
  have hbmem (i j : Fin N) : MemLp (b i j) 2 μN :=
    MemLp.of_bound (hbmeas i j).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun target => by
        simpa [Real.norm_eq_abs] using hbbound i j target)
  have habsCov (i j k l : Fin N) :
      |cov[b i j, b k l; μN]| ≤ 2 * M ^ 2 := by
    rw [covariance_eq_sub (hbmem i j) (hbmem k l)]
    have hEX : |∫ target, b i j target ∂μN| ≤ M := by
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_of_norm_le_const
          (μ := μN) (f := b i j) (C := M)
          (Filter.Eventually.of_forall fun target => by
            simpa [Real.norm_eq_abs] using hbbound i j target))
    have hEY : |∫ target, b k l target ∂μN| ≤ M := by
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_of_norm_le_const
          (μ := μN) (f := b k l) (C := M)
          (Filter.Eventually.of_forall fun target => by
            simpa [Real.norm_eq_abs] using hbbound k l target))
    have hprod : |(∫ target, b i j target ∂μN) *
        (∫ target, b k l target ∂μN)| ≤ M ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul hEX hEY (abs_nonneg _) hM
    have hEXY : |∫ target, b i j target * b k l target ∂μN| ≤ M ^ 2 := by
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_of_norm_le_const
          (μ := μN) (f := fun target => b i j target * b k l target)
          (C := M ^ 2) (Filter.Eventually.of_forall fun target => by
            rw [Real.norm_eq_abs, abs_mul]
            calc
              |b i j target| * |b k l target| ≤ M * M :=
                mul_le_mul (hbbound i j target)
                  (hbbound k l target) (abs_nonneg _) hM
              _ = M ^ 2 := by ring
            ))
    calc
      |(∫ target, b i j target * b k l target ∂μN) -
          (∫ target, b i j target ∂μN) *
            ∫ target, b k l target ∂μN| ≤
          |∫ target, b i j target * b k l target ∂μN| +
            |(∫ target, b i j target ∂μN) *
              ∫ target, b k l target ∂μN| := abs_sub _ _
      _ ≤ M ^ 2 + M ^ 2 := add_le_add hEXY hprod
      _ = 2 * M ^ 2 := by ring
  have hcoordIndep :
      iIndepFun (fun i : Fin N => fun target : Fin N → X => target i) μN :=
    iIndepFun_pi (fun _ => Measurable.aemeasurable measurable_id)
  have hcov0 (i j k l : Fin N)
      (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
      cov[b i j, b k l; μN] = 0 := by
    by_cases hij : i = j
    · subst j
      simp [b, covariance]
    by_cases hkl : k = l
    · subst l
      simp [b, covariance]
    have hpairs :=
      hcoordIndep.indepFun_prodMk_prodMk
        (fun r => measurable_pi_apply r) i j k l hik hil hjk hjl
    have hindep : b i j ⟂ᵢ[μN] b k l := by
      have hc := hpairs.comp hkernel hkernel
      simpa only [Function.comp_def, Function.uncurry_apply_pair, b, if_pos hij,
        if_pos hkl] using hc
    exact hindep.covariance_eq_zero (hbmem i j) (hbmem k l)
  let χ : Prop → ℝ := fun p => if p then 1 else 0
  let bracket : Fin N → Fin N → Fin N → Fin N → ℝ := fun i j k l =>
    χ (i = k) + χ (i = l) + χ (j = k) + χ (j = l)
  have hbracket_nonneg (i j k l : Fin N) :
      0 ≤ bracket i j k l := by
    dsimp only [bracket, χ]
    positivity
  have hterm (i j k l : Fin N) :
      cov[b i j, b k l; μN] ≤
        (2 * M ^ 2) * bracket i j k l := by
    by_cases hij : i = j
    · subst j
      have hz : b i i = fun _ => 0 := by
        funext target
        simp [b]
      rw [hz]
      simp only [covariance_const_left, ge_iff_le]
      exact mul_nonneg (by positivity) (hbracket_nonneg i i k l)
    by_cases hkl : k = l
    · subst l
      have hz : b k k = fun _ => 0 := by
        funext target
        simp [b]
      rw [hz]
      simp only [covariance_const_right, ge_iff_le]
      exact mul_nonneg (by positivity) (hbracket_nonneg i j k k)
    by_cases hconn : i = k ∨ i = l ∨ j = k ∨ j = l
    · have hone : 1 ≤ bracket i j k l := by
        rcases hconn with h | h | h | h
        · subst k
          dsimp only [bracket, χ]
          split_ifs <;> simp_all
        · subst l
          dsimp only [bracket, χ]
          split_ifs <;> simp_all
        · subst k
          dsimp only [bracket, χ]
          split_ifs <;> simp_all
        · subst l
          dsimp only [bracket, χ]
          split_ifs <;> simp_all
      calc
        cov[b i j, b k l; μN] ≤ |cov[b i j, b k l; μN]| :=
          le_abs_self _
        _ ≤ 2 * M ^ 2 := habsCov i j k l
        _ = (2 * M ^ 2) * 1 := by ring
        _ ≤ (2 * M ^ 2) * bracket i j k l := by
          gcongr
    · push_neg at hconn
      rw [hcov0 i j k l hconn.1 hconn.2.1 hconn.2.2.1 hconn.2.2.2]
      exact mul_nonneg (by positivity) (hbracket_nonneg i j k l)
  have hvarsum :
      variance (fun target : Fin N → X => ∑ i, ∑ j, b i j target) μN ≤
        8 * M ^ 2 * (N : ℝ) ^ 3 := by
    have hexpand :
        variance (fun target : Fin N → X => ∑ i, ∑ j, b i j target) μN =
          ∑ i, ∑ j, ∑ k, ∑ l, cov[b i j, b k l; μN] := by
      have h :=
        variance_fun_sum
          (μ := μN) (X := fun p : Fin N × Fin N => b p.1 p.2)
          (fun p => hbmem p.1 p.2)
      simpa only [Fintype.sum_prod_type] using h
    rw [hexpand]
    calc
      (∑ i, ∑ j, ∑ k, ∑ l, cov[b i j, b k l; μN]) ≤
          ∑ i, ∑ j, ∑ k, ∑ l,
            (2 * M ^ 2) * bracket i j k l := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro l hl
        exact hterm i j k l
      _ = (2 * M ^ 2) *
          (∑ i, ∑ j, ∑ k, ∑ l, bracket i j k l) := by
        simp_rw [Finset.mul_sum]
      _ = (2 * M ^ 2) * (4 * (N : ℝ) ^ 3) := by
        congr 1
        have hchi (i : Fin N) : ∑ k : Fin N, χ (i = k) = 1 := by
          rw [Finset.sum_eq_single i]
          · simp [χ]
          · intro k hk hki
            simp [χ, hki.symm]
          · simp
        have hchi' (k : Fin N) : ∑ i : Fin N, χ (i = k) = 1 := by
          rw [Finset.sum_eq_single k]
          · simp [χ]
          · intro i hi hik
            simp [χ, hik]
          · simp
        have hdouble :
            (∑ i : Fin N, ∑ k : Fin N, χ (i = k)) = (N : ℝ) := by
          calc
            _ = ∑ _i : Fin N, (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hchi i
            _ = (N : ℝ) := by simp
        dsimp only [bracket]
        simp_rw [Finset.sum_add_distrib]
        simp only [hchi, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Fintype.card_fin]
        simp_rw [← Finset.mul_sum]
        rw [hdouble]
        ring
      _ = 8 * M ^ 2 * (N : ℝ) ^ 3 := by ring
  have hNreal : 0 < (N : ℝ) := by positivity
  have hNm1real : 0 < ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hNtwo
  rw [variance_const_mul]
  change
    (((N : ℝ) * (N - 1 : ℕ))⁻¹) ^ 2 *
        variance (fun target : Fin N → X => ∑ i, ∑ j, b i j target) μN ≤
      32 * M ^ 2 / (N : ℝ)
  calc
    _ ≤ (((N : ℝ) * (N - 1 : ℕ))⁻¹) ^ 2 *
        (8 * M ^ 2 * (N : ℝ) ^ 3) := by gcongr
    _ ≤ 32 * M ^ 2 / (N : ℝ) := by
      have hNm1 : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show N ≤ 2 * (N - 1) by omega)
      have hsquare : (N : ℝ) ^ 2 ≤ 4 * ((N - 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith
      field_simp [hNreal.ne', hNm1real.ne']
      nlinarith [sq_nonneg M]

end Causalean.Stat
