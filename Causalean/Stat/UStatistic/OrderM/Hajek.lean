/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hájek projection for fixed-order U-statistics

This file gives the first-order Hájek expansion and central-limit contact point
for fixed-order U-statistics.  For an ordered kernel the influence function is
the sum of the coordinatewise first Hoeffding projections; for symmetric kernels
this is the standard `m` times the first projection.  The remainder is the
U-statistic formed from the higher-order residual kernel.
-/

import Causalean.Stat.UStatistic.Hajek
import Causalean.Stat.UStatistic.OrderM.Basic
import Causalean.Stat.CLT.AsymptoticLinearity

/-!
Develops the fixed-order Hájek decomposition for U-statistics indexed by
injective ordered `m`-tuples.

The main objects are `uInfluenceOrder`, the sum of the coordinatewise first
Hoeffding projections; `uRemainderOrder`, the U-statistic formed from the
higher-order residual kernel; and `OrderDegenerateNegligible`, the `√n`-scale
negligibility hypothesis consumed by the fixed-order CLT.  The theorem
`uStatisticOrder_sub_uMean_eq` proves the exact finite-sample decomposition, and
`uStatisticOrder_isAsymLinear` packages it as asymptotic linearity once the
residual term is negligible.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## Coordinate projections and degenerate kernels -/

/-- The first-order influence function of an ordered fixed-order kernel: the sum
of its coordinatewise first Hoeffding projections.  For a symmetric kernel this
is `m` times the usual first projection. -/
noncomputable def uInfluenceOrder {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (P : Measure X) : X → ℝ :=
  fun x => ∑ j : Fin m, uProjOrderAt j h P x

/-- If all coordinatewise first projections agree with a common projection, then
the order-`m` influence function is `m` times that projection. -/
theorem uInfluenceOrder_eq_card_mul_of_common_projection {m : ℕ} [NeZero m]
    {h : (Fin m → X) → ℝ} {φ : X → ℝ}
    (hproj : ∀ j : Fin m, ∀ x, uProjOrderAt j h P x = φ x) :
    uInfluenceOrder h P = fun x => (m : ℝ) * φ x := by
  funext x
  simp [uInfluenceOrder, hproj, Finset.sum_const, nsmul_eq_mul]

/-- The higher-order remainder statistic for an order-`m` U-statistic. -/
noncomputable def uRemainderOrder (S : IIDSample Ω X μ P) {m : ℕ} [NeZero m]
    (h : (Fin m → X) → ℝ) (n : ℕ) : Ω → ℝ :=
  uStatisticOrder S (uDegenOrder h P) n

/-- A fully degenerate order-`m` kernel under product measure `P^m`.

The kernel is measurable, invariant under coordinate permutations,
square-integrable, and has zero integral in every coordinate after the remaining
coordinates are fixed.  This is the complete-degeneracy interface used for exact
variance calculations; the weaker first-order degeneracy interface for the
Hájek remainder is `OrderFirstDegenKernel`. -/
structure OrderDegenKernel (P : Measure X) {m : ℕ} [NeZero m]
    (g : (Fin m → X) → ℝ) : Prop where
  meas : Measurable g
  symm : ∀ σ : Equiv.Perm (Fin m), ∀ z, g (z ∘ σ) = g z
  deg : ∀ j (tail : ({k : Fin m // k ≠ j}) → X),
    ∫ x, g (insertCoord j x tail) ∂P = 0
  sq : Integrable (fun z => (g z) ^ 2) (Measure.pi fun _ : Fin m => P)

/-! ## Hájek decomposition -/

/-- The higher-order order-`m` Hájek remainder is negligible at the `√n` scale.

For a kernel `h`, this states that
`√n * uRemainderOrder S h n = o_p(1)`.  It is kept as a separate hypothesis in
the decomposition layer and discharged in `OrderM.RemainderNegligible` from
first-order degeneracy and a second-moment bound. -/
def OrderDegenerateNegligible (S : IIDSample Ω X μ P) {m : ℕ} [NeZero m]
    (h : (Fin m → X) → ℝ) : Prop :=
  IsLittleOp
    (fun n ω => Real.sqrt (n : ℝ) * uRemainderOrder S h n ω)
    (fun _ => (1 : ℝ)) μ

/-! ### Ordered-tuple counting -/

/-- If `m ≤ n`, there is at least one ordered injective `m`-tuple in `Fin n`. -/
theorem injectiveTupleCount_ne_zero {m n : ℕ} (hmn : m ≤ n) :
    injectiveTupleCount m n ≠ 0 := by
  classical
  have hmem :
      (fun j : Fin m => (⟨j.1, lt_of_lt_of_le j.2 hmn⟩ : Fin n))
        ∈ injectiveTuples m n := by
    rw [injectiveTuples, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hab)
  have hpos : 0 < (injectiveTuples m n).card := Finset.card_pos.mpr ⟨_, hmem⟩
  rw [injectiveTupleCount]
  exact_mod_cast (Nat.ne_of_gt hpos)

/-- Fibres of a fixed coordinate map on ordered injective tuples have the same
cardinality.  The bijection composes tuples with the codomain transposition
swapping the two fibre values. -/
theorem injectiveTuples_fiber_card_eq {m n : ℕ} [NeZero m] (j : Fin m)
    (y y' : Fin n) :
    ((injectiveTuples m n).filter (fun t => t j = y)).card =
      ((injectiveTuples m n).filter (fun t => t j = y')).card := by
  classical
  refine Finset.card_bij
    (fun t _ => (Equiv.swap y y') ∘ t)
    ?hmem ?hinj ?hsurj
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    rcases ht with ⟨htuple, hj⟩
    have htinj : Function.Injective t := by
      simpa [injectiveTuples] using htuple
    refine ⟨?_, ?_⟩
    · simp [injectiveTuples, (Equiv.swap y y').injective.comp htinj]
    · simp [Function.comp, hj, Equiv.swap_apply_left]
  · intro t₁ _ t₂ _ h
    funext k
    exact (Equiv.swap y y').injective (congrFun h k)
  · intro t ht
    refine ⟨(Equiv.swap y y') ∘ t, ?_, ?_⟩
    · rw [Finset.mem_filter] at ht ⊢
      rcases ht with ⟨htuple, hj⟩
      have htinj : Function.Injective t := by
        simpa [injectiveTuples] using htuple
      refine ⟨?_, ?_⟩
      · simp [injectiveTuples, (Equiv.swap y y').injective.comp htinj]
      · simp [Function.comp, hj, Equiv.swap_apply_right]
    · funext k
      simp [Function.comp]

/-- For each coordinate of an ordered injective tuple, every sample index appears
equally often. -/
theorem sum_injectiveTuples_apply_eq_range {m n : ℕ} [NeZero m] (hmn : m ≤ n)
    (j : Fin m) (f : ℕ → ℝ) :
    ∑ t ∈ injectiveTuples m n, f (t j : ℕ)
      = (injectiveTupleCount m n / (n : ℝ)) * ∑ i ∈ Finset.range n, f i := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hnpos_nat : 0 < n := lt_of_lt_of_le hmpos hmn
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
  let y0 : Fin n := ⟨0, hnpos_nat⟩
  let c : ℕ := ((injectiveTuples m n).filter (fun t => t j = y0)).card
  have hfiber_card : ∀ y : Fin n,
      ((injectiveTuples m n).filter (fun t => t j = y)).card = c := by
    intro y
    exact injectiveTuples_fiber_card_eq j y y0
  have hcard : (injectiveTuples m n).card = n * c := by
    have hmaps : Set.MapsTo (fun t : Fin m → Fin n => t j)
        (↑(injectiveTuples m n)) (↑(Finset.univ : Finset (Fin n))) := by
      intro t ht
      simp
    rw [Finset.card_eq_sum_card_fiberwise (f := fun t : Fin m → Fin n => t j)
      (s := injectiveTuples m n) (t := (Finset.univ : Finset (Fin n))) hmaps]
    simp [hfiber_card, c]
  have hcoeff : injectiveTupleCount m n / (n : ℝ) = (c : ℝ) := by
    rw [injectiveTupleCount, hcard, Nat.cast_mul]
    field_simp [hnne]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := injectiveTuples m n) (t := (Finset.univ : Finset (Fin n)))
    (g := fun t : Fin m → Fin n => t j)
    (f := fun t : Fin m → Fin n => f (t j : ℕ))]
  · have hinner : ∀ y : Fin n,
        (∑ t ∈ injectiveTuples m n with t j = y, f (t j : ℕ))
          = (c : ℝ) * f (y : ℕ) := by
      intro y
      calc
        ∑ t ∈ injectiveTuples m n with t j = y, f (t j : ℕ)
            = ∑ t ∈ injectiveTuples m n with t j = y, f (y : ℕ) := by
              apply Finset.sum_congr rfl
              intro t ht
              have htj : t j = y := (Finset.mem_filter.mp ht).2
              simp [htj]
        _ = (c : ℝ) * f (y : ℕ) := by
              rw [Finset.sum_const, nsmul_eq_mul, hfiber_card y]
    simp_rw [hinner]
    rw [← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range]
    rw [hcoeff]
  · intro t ht
    simp

/-- **Hájek decomposition for a fixed-order U-statistic.**  For positive order
`m` and sample size `n ≥ m`, the centered statistic equals its linear Hájek
projection plus the higher-order residual U-statistic. -/
theorem uStatisticOrder_sub_uMean_eq (S : IIDSample Ω X μ P)
    {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    {n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    uStatisticOrder S h n ω - uMeanOrder h P
      = (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, uInfluenceOrder h P (S.Z i ω))
          + uRemainderOrder S h n ω := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hnpos_nat : 0 < n := lt_of_lt_of_le hmpos hmn
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
  have hcount_ne : injectiveTupleCount m n ≠ 0 := injectiveTupleCount_ne_zero hmn
  have hterm : ∀ t ∈ injectiveTuples m n,
      h (fun j => S.Z (t j : ℕ) ω)
        = uMeanOrder h P
          + (∑ j : Fin m, uProjOrderAt j h P (S.Z (t j : ℕ) ω))
          + uDegenOrder h P (fun j => S.Z (t j : ℕ) ω) :=
    fun t _ => hoeffding_decomp_order h P _
  have hproj :
      (∑ t ∈ injectiveTuples m n,
        ∑ j : Fin m, uProjOrderAt j h P (S.Z (t j : ℕ) ω))
        = (injectiveTupleCount m n / (n : ℝ))
          * (∑ i ∈ Finset.range n, uInfluenceOrder h P (S.Z i ω)) := by
    rw [Finset.sum_comm]
    rw [show (∑ j : Fin m, ∑ t ∈ injectiveTuples m n,
          uProjOrderAt j h P (S.Z (t j : ℕ) ω))
        = ∑ j : Fin m, (injectiveTupleCount m n / (n : ℝ))
          * ∑ i ∈ Finset.range n, uProjOrderAt j h P (S.Z i ω) from by
        apply Finset.sum_congr rfl
        intro j _
        exact sum_injectiveTuples_apply_eq_range hmn j
          (fun i => uProjOrderAt j h P (S.Z i ω))]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp [uInfluenceOrder]
  have hsum : (∑ t ∈ injectiveTuples m n, h (fun j => S.Z (t j : ℕ) ω))
      = injectiveTupleCount m n * uMeanOrder h P
        + (injectiveTupleCount m n / (n : ℝ))
          * (∑ i ∈ Finset.range n, uInfluenceOrder h P (S.Z i ω))
        + ∑ t ∈ injectiveTuples m n,
            uDegenOrder h P (fun j => S.Z (t j : ℕ) ω) := by
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [hproj]
    simp only [injectiveTupleCount]
  simp only [uStatisticOrder, uRemainderOrder, hsum]
  field_simp [hcount_ne, hnne]
  ring

/-- The Hájek remainder in `IsAsymLinear` form is the rescaled higher-order
residual U-statistic. -/
theorem uStatisticOrder_remainder_eq [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    {n : ℕ} (hmn : m ≤ n) :
    (fun ω =>
        Real.sqrt ((Finset.range n).card : ℝ)
            * (uStatisticOrder S h n ω - uMeanOrder h P)
          - (Real.sqrt ((Finset.range n).card : ℝ))⁻¹
            * ∑ i ∈ Finset.range n, uInfluenceOrder h P (S.Z i ω))
      = fun ω => Real.sqrt (n : ℝ) * uRemainderOrder S h n ω := by
  funext ω
  rw [Finset.card_range]
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hnpos_nat : 0 < n := lt_of_lt_of_le hmpos hmn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos_nat
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hsne : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
  have hs2 : s * s = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hnpos)
  rw [uStatisticOrder_sub_uMean_eq S h hmn ω]
  set B : ℝ := ∑ i ∈ Finset.range n, uInfluenceOrder h P (S.Z i ω) with hBdef
  set G : ℝ := uRemainderOrder S h n ω with hGdef
  rw [show (n : ℝ) = s * s from hs2.symm]
  field_simp
  ring

/-! ## Asymptotic linearity

The central-limit contact point: negligibility of the higher-order remainder makes
the U-statistic asymptotically linear.  The CLT itself (`uStatisticOrder_clt` and
the end-to-end `uStatisticOrder_clt_of_regular`) is assembled in `OrderM.CLT`. -/

variable [IsProbabilityMeasure μ]

/-- **Fixed-order U-statistic asymptotic linearity.**  If the summed first
projection is centered and square-integrable, and the higher-order residual is
negligible at the `√n` scale, then the fixed-order U-statistic is asymptotically
linear with influence function equal to the sum of coordinatewise first
projections. -/
theorem uStatisticOrder_isAsymLinear (S : IIDSample Ω X μ P)
    {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (hψ_mean : ∫ x, uInfluenceOrder h P x ∂P = 0)
    (hψ_sq : Integrable (fun x => (uInfluenceOrder h P x) ^ 2) P)
    (hneg : OrderDegenerateNegligible S h) :
    IsAsymLinear (uStatisticOrder S h) (uMeanOrder h P)
      (uInfluenceOrder h P) S (fun r => Finset.range r) := by
  refine ⟨hψ_mean, hψ_sq, ?_⟩
  refine isLittleOp_of_eventuallyEq hneg ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  exact uStatisticOrder_remainder_eq S h hn

end Causalean.Stat
