/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mogstad-Torgovitsky-Walters finite index algebra

Pure finite-support algebra for the ordered first-stage index in the saturated
multiple-IV characterization of Mogstad, Torgovitsky, and Walters (2021).

Source labels:

* `def:po-estimand-mtw-tail-coefficients`
* `thm:po-estimand-mtw-signed-decomposition`
* `rem:po-estimand-mtw-lean-implementation`
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Invertible
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Causalean.Panel.Weighted.NormalizedWeights
/-! # Multiple-Instrument IV Finite Index Algebra

This file develops the finite ordered-index algebra used in the
Mogstad-Torgovitsky-Walters multiple-instrument characterization. It defines
support masses, ordered first-stage indices, centered instruments, tail
coefficients, and the finite matrix identities that underlie the signed
decomposition. -/

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset
open MeasureTheory

/-- Adjacent threshold for the ordered support.  The value `j : Adj K`
represents the source-paper threshold between support positions `j-1` and `j`
in zero-based Lean indexing, i.e. source notation `2, ..., K`. -/
abbrev Adj (K : ℕ) := {j : Fin K // 0 < j.val}

namespace Adj

/-- Lower endpoint `j-1` of an adjacent threshold. -/
def lower {K : ℕ} (j : Adj K) : Fin K :=
  ⟨j.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.1.isLt⟩

/-- Upper endpoint `j` of an adjacent threshold. -/
def upper {K : ℕ} (j : Adj K) : Fin K :=
  j.1

end Adj

/-- Finite ordered first-stage index.  The support masses `rho` sum to one,
and `dhat` is ordered weakly increasingly in the displayed support order. -/
structure FiniteIndex (K : ℕ) where
  /-- Instrument support mass `ρ_k`. -/
  rho : Fin K → ℝ
  /-- Ordered saturated first-stage index `dhat_k`. -/
  dhat : Fin K → ℝ
  /-- Support masses are nonnegative. -/
  rho_nonneg : ∀ k, 0 ≤ rho k
  /-- Support masses sum to one. -/
  rho_sum_one : ∑ k, rho k = 1
  /-- The displayed support order is weakly increasing in the first-stage index. -/
  dhat_mono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l

/-- Measure-backed finite support mass `P(Z = k)` for a `Fin K`-valued
instrument. -/
noncomputable def supportMass {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (Z : Ω → Fin K) (k : Fin K) : ℝ :=
  (μ {ω | Z ω = k}).toReal

/-- Support masses obtained from a measure are nonnegative. -/
theorem supportMass_nonneg {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (Z : Ω → Fin K) (k : Fin K) :
    0 ≤ supportMass μ Z k := by
  exact ENNReal.toReal_nonneg

/-- For a probability measure, the finite support masses induced by `Z` sum to
one. -/
theorem supportMass_sum_eq_one {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Fin K) (hZ : Measurable Z) :
    ∑ k : Fin K, supportMass μ Z k = 1 := by
  have hsum :
      (Finset.univ).sum
          (fun k : Fin K => (μ (Z ⁻¹' ({k} : Set (Fin K)))).toReal) =
        (μ (Z ⁻¹' (Set.univ : Set (Fin K)))).toReal := by
    simpa [Measure.real] using
      (MeasureTheory.sum_measureReal_preimage_singleton
        (μ := μ) (s := (Finset.univ : Finset (Fin K))) (f := Z)
        (hf := by
          intro k _hk
          exact hZ (measurableSet_singleton k))
        (h := by
          intro k _hk
          exact ne_of_lt <| lt_of_le_of_lt (measure_mono (Set.subset_univ _))
            (by simp [IsProbabilityMeasure.measure_univ])))
  simpa [supportMass, Set.preimage_univ] using hsum

/-- Construct the ordered finite first-stage index from a probability-space
instrument `Z : Ω → Fin K` and a finite support score `dhat`.  The support
masses are the actual measure masses `P(Z = k)`; the only remaining
first-stage input is the displayed-order monotonicity of the score. -/
noncomputable def FiniteIndex.fromMeasureScore {Ω : Type*} [MeasurableSpace Ω]
    {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Fin K) (hZ : Measurable Z)
    (dhat : Fin K → ℝ)
    (hdhat_mono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l) :
    FiniteIndex K where
  rho := supportMass μ Z
  dhat := dhat
  rho_nonneg := supportMass_nonneg μ Z
  rho_sum_one := supportMass_sum_eq_one μ Z hZ
  dhat_mono := hdhat_mono

namespace FiniteIndex

variable {K : ℕ} (I : FiniteIndex K)

/-- Mean first-stage index `dbar = Σ_k ρ_k dhat_k`. -/
noncomputable def meanIndex : ℝ :=
  ∑ k, I.rho k * I.dhat k

/-- Centered first-stage index `a_k = dhat_k - dbar`. -/
noncomputable def centeredIndex (k : Fin K) : ℝ :=
  I.dhat k - I.meanIndex

/-- Ordered upper tail `T_j = {j, ..., K}` for an adjacent threshold. -/
noncomputable def upperTail (j : Adj K) : Finset (Fin K) :=
  Finset.univ.filter fun k => j.1.val ≤ k.val

/-- MTW tail coefficient `B_j = Σ_{k ≥ j} ρ_k a_k`. -/
noncomputable def tailCoeff (j : Adj K) : ℝ :=
  ∑ k ∈ upperTail j, I.rho k * I.centeredIndex k

/-- Centering identity `Σ_k ρ_k (dhat_k - dbar) = 0`.

This is the finite algebra behind subtracting the baseline term in
`thm:po-estimand-mtw-signed-decomposition`. -/
theorem centered_weight_sum_zero :
    ∑ k, I.rho k * I.centeredIndex k = 0 := by
  calc
    ∑ k, I.rho k * I.centeredIndex k =
        ∑ k, (I.rho k * I.dhat k - I.rho k * I.meanIndex) := by
      simp [centeredIndex, sub_eq_add_neg, mul_add]
    _ = ∑ k, I.rho k * I.dhat k - ∑ k, I.rho k * I.meanIndex := by
      rw [Finset.sum_sub_distrib]
    _ = I.meanIndex - I.meanIndex * ∑ k, I.rho k := by
      simp [meanIndex, Finset.sum_mul, mul_comm]
    _ = 0 := by
      simp [I.rho_sum_one]

/-- MTW tail coefficients are nonnegative when the support is ordered by the
first-stage index (`def:po-estimand-mtw-tail-coefficients`). -/
theorem tailCoeff_nonneg (j : Adj K) :
    0 ≤ I.tailCoeff j := by
  classical
  let T := upperTail j
  let L : Finset (Fin K) := Finset.univ.filter fun l => l.val < j.1.val
  let A : ℝ := ∑ k ∈ T, I.rho k
  let B : ℝ := ∑ l ∈ L, I.rho l
  let ST : ℝ := ∑ k ∈ T, I.rho k * I.dhat k
  let SL : ℝ := ∑ l ∈ L, I.rho l * I.dhat l
  have hmass : B + A = 1 := by
    have h :=
      Finset.sum_filter_not_add_sum_filter
        (s := Finset.univ) (p := fun k : Fin K => j.1.val ≤ k.val) (f := I.rho)
    simpa [A, B, T, L, upperTail, Nat.not_le] using h.trans I.rho_sum_one
  have hmean : I.meanIndex = SL + ST := by
    have h :=
      Finset.sum_filter_not_add_sum_filter
        (s := Finset.univ) (p := fun k : Fin K => j.1.val ≤ k.val)
        (f := fun k => I.rho k * I.dhat k)
    simpa [ST, SL, T, L, upperTail, meanIndex, Nat.not_le] using h.symm
  have htail_basic : I.tailCoeff j = ST - A * I.meanIndex := by
    calc
      I.tailCoeff j =
          ∑ k ∈ T, (I.rho k * I.dhat k - I.rho k * I.meanIndex) := by
        simp [tailCoeff, centeredIndex, T, upperTail, mul_sub]
      _ = ST - ∑ k ∈ T, I.rho k * I.meanIndex := by
        rw [Finset.sum_sub_distrib]
      _ = ST - I.meanIndex * A := by
        simp [A, ST, Finset.mul_sum, mul_comm]
      _ = ST - A * I.meanIndex := by
        rw [mul_comm I.meanIndex A]
  have htail : I.tailCoeff j = B * ST - A * SL := by
    rw [htail_basic, hmean]
    have hB : B = 1 - A := by linarith
    rw [hB]
    ring
  have hfirst :
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat k) = B * ST := by
    simp [B, ST, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  have hsecond :
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat l) = A * SL := by
    rw [Finset.sum_comm]
    simp [A, SL, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
  have hdouble :
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * (I.dhat k - I.dhat l)) =
        B * ST - A * SL := by
    calc
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * (I.dhat k - I.dhat l)) =
          (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat k) -
            (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat l) := by
        simp [mul_sub, Finset.sum_sub_distrib]
      _ = B * ST - A * SL := by
        rw [hfirst, hsecond]
  rw [htail, ← hdouble]
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro l hl
  have hkT : j.1.val ≤ k.val := by
    simpa [T, upperTail] using hk
  have hlL : l.val < j.1.val := by
    simpa [L] using hl
  have hle : l.val ≤ k.val := by omega
  have hdhat : 0 ≤ I.dhat k - I.dhat l := sub_nonneg.mpr (I.dhat_mono hle)
  exact mul_nonneg (mul_nonneg (I.rho_nonneg k) (I.rho_nonneg l)) hdhat

/-- Finite upper-tail interchange identity used by the signed decomposition.
It is the algebraic form of moving from
`Σ_k ρ_k a_k Σ_{j≤k} x_j` to `Σ_j B_j x_j`. -/
theorem tail_sum_interchange (x : Adj K → ℝ) :
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ j : Adj K, if j.1.val ≤ k.val then x j else 0)) =
      ∑ j : Adj K, I.tailCoeff j * x j := by
  simp only [tailCoeff, upperTail]
  calc
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ j : Adj K, if j.1.val ≤ k.val then x j else 0)) =
        ∑ k : Fin K, ∑ j : Adj K,
          if j.1.val ≤ k.val then (I.rho k * I.centeredIndex k) * x j else 0 := by
      simp [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]
    _ = ∑ j : Adj K, ∑ k : Fin K,
          if j.1.val ≤ k.val then (I.rho k * I.centeredIndex k) * x j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Adj K, x j * ∑ k : Fin K,
          if j.1.val ≤ k.val then I.rho k * I.centeredIndex k else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases h : j.1.val ≤ k.val
      · simp [h, mul_comm]
      · simp [h]
    _ = ∑ j : Adj K,
        (∑ k ∈ Finset.univ.filter fun k => j.1.val ≤ k.val,
          I.rho k * I.centeredIndex k) * x j := by
      simp [Finset.sum_filter, mul_comm]

/-- Covariance identity: the MTW tail coefficient `B_j` equals the
finite-support covariance between the first-stage index `dhat(Z)` and the
upper-tail indicator `1_{Z ∈ T_j}` under the instrument distribution `ρ`.

Formally, with `ind_k := if k ∈ upperTail j then (1 : ℝ) else 0` and
`mean_ind := Σ_l ρ_l * ind_l`,

    B_j = Σ_k ρ_k * (dhat_k − dbar) * (ind_k − mean_ind)
         = Cov_ρ(dhat, 1_{T_j}).

The centering of the indicator drops out because `Σ_k ρ_k * centeredIndex_k = 0`
(`centered_weight_sum_zero`).  This identity bridges the tail-coefficient
algebra to the observable first-stage moments.

Source location: `def:po-estimand-mtw-tail-coefficients` (TeX:135–138). -/
theorem tailCoeff_eq_cov (j : Adj K) :
    I.tailCoeff j =
      ∑ k : Fin K,
        I.rho k * (I.dhat k - I.meanIndex) *
          ((if k ∈ upperTail j then (1 : ℝ) else 0) -
            ∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) := by
  -- The subtracted cross-term is (Σ_k ρ_k centeredIndex_k) * (Σ_l ρ_l ind_l) = 0.
  have hcross :
      ∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) = 0 := by
    have : (∑ k : Fin K, I.rho k * I.centeredIndex k) *
        (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) = 0 := by
      rw [I.centered_weight_sum_zero]; ring
    calc ∑ k : Fin K,
          I.rho k * I.centeredIndex k *
            (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0))
        = (∑ k : Fin K, I.rho k * I.centeredIndex k) *
            (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) := by
          rw [Finset.sum_mul]
      _ = 0 := this
  -- Rewrite the whole RHS directly and cancel cross-term.
  -- Let C := Σ_l ρ_l * ind_l (a constant w.r.t. k).
  -- RHS = Σ_k ρ_k*(dhat_k - mean)*(ind_k - C)
  --     = Σ_k ρ_k*centeredIndex_k*ind_k  -  C * Σ_k ρ_k*centeredIndex_k
  --     = Σ_k ρ_k*centeredIndex_k*ind_k  -  C * 0
  --     = Σ_{k∈T_j} ρ_k*centeredIndex_k  = tailCoeff j.
  have key : ∑ k : Fin K,
        I.rho k * (I.dhat k - I.meanIndex) *
          ((if k ∈ upperTail j then (1 : ℝ) else 0) -
            ∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) =
      ∑ k : Fin K,
          I.rho k * I.centeredIndex k * (if k ∈ upperTail j then (1 : ℝ) else 0) := by
    -- unfold centeredIndex so ring can see everything
    simp only [centeredIndex]
    have hcross2 :
        (∑ k : Fin K, I.rho k * (I.dhat k - I.meanIndex)) *
          (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) = 0 := by
      have : ∑ k : Fin K, I.rho k * (I.dhat k - I.meanIndex) = 0 := by
        have := I.centered_weight_sum_zero
        simp only [centeredIndex] at this; exact this
      rw [this]; ring
    calc ∑ k : Fin K,
          I.rho k * (I.dhat k - I.meanIndex) *
            ((if k ∈ upperTail j then (1 : ℝ) else 0) -
              ∑ l, I.rho l * (if l ∈ upperTail j then 1 else 0))
        = (∑ k : Fin K,
            I.rho k * (I.dhat k - I.meanIndex) * (if k ∈ upperTail j then (1 : ℝ) else 0)) -
          (∑ k : Fin K, I.rho k * (I.dhat k - I.meanIndex)) *
            (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          congr 1; ext k; ring
      _ = ∑ k : Fin K,
            I.rho k * (I.dhat k - I.meanIndex) * (if k ∈ upperTail j then (1 : ℝ) else 0) := by
          rw [hcross2, sub_zero]
  rw [key]
  -- Now: Σ_k ρ_k*centeredIndex_k*indicator(k∈T_j) = Σ_{k∈T_j} ρ_k*centeredIndex_k = tailCoeff j
  simp only [tailCoeff, upperTail, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> ring

end FiniteIndex

/-! ### Matrix first-stage construction -/

/-- Finite second-moment matrix `E[q(Z)q(Z)ᵀ]` for a score vector on finite
instrument support. -/
noncomputable def firstStageGram {K L : ℕ}
    (rho : Fin K → ℝ) (score : Fin K → Fin L → ℝ) :
    Matrix (Fin L) (Fin L) ℝ :=
  fun a b => ∑ k : Fin K, rho k * score k a * score k b

/-- Finite-support matrix first stage for the source population-2SLS
definition.  The score vector `q`, support masses `rho`, reduced-form
first-stage moments `firstStageMoment`, and invertible Gram matrix determine
the projection coefficient by the displayed matrix inverse.  The resulting
fitted values are required to be in the displayed weakly increasing order so
they can feed the MTW tail-coefficient algebra. -/
structure MatrixFirstStage (K L : ℕ) where
  /-- Instrument support mass `ρ_k`. -/
  rho : Fin K → ℝ
  /-- Score vector `q(zᵏ)`. -/
  score : Fin K → Fin L → ℝ
  /-- Moment vector `E[q(Z)D]` in finite-support form. -/
  firstStageMoment : Fin L → ℝ
  /-- Support masses are nonnegative. -/
  rho_nonneg : ∀ k, 0 ≤ rho k
  /-- Support masses sum to one. -/
  rho_sum_one : ∑ k, rho k = 1
  /-- The finite second-moment matrix is invertible. -/
  gram_invertible : Invertible (firstStageGram rho score)
  /-- The matrix-inverse fitted first stage is weakly increasing in the
  displayed support order. -/
  fitted_mono :
    ∀ {k l : Fin K}, k.val ≤ l.val →
      (∑ a : Fin L,
          (∑ b : Fin L,
            (⅟(firstStageGram rho score)) a b *
              firstStageMoment b) *
            score k a) ≤
        (∑ a : Fin L,
          (∑ b : Fin L,
            (⅟(firstStageGram rho score)) a b *
              firstStageMoment b) *
            score l a)

namespace MatrixFirstStage

variable {K L : ℕ} (S : MatrixFirstStage K L)

/-- Finite second-moment matrix `E[q(Z)q(Z)ᵀ]`. -/
noncomputable def gram : Matrix (Fin L) (Fin L) ℝ :=
  firstStageGram S.rho S.score

/-- The finite second-moment matrix is invertible by the matrix first-stage
assumption. -/
noncomputable instance instInvertibleGram : Invertible S.gram := by
  change Invertible (firstStageGram S.rho S.score)
  exact S.gram_invertible

/-- Population first-stage projection coefficient
`(E[q(Z)q(Z)ᵀ])⁻¹ E[q(Z)D]`. -/
noncomputable def projectionCoeff (a : Fin L) : ℝ :=
  ∑ b : Fin L, (⅟S.gram) a b * S.firstStageMoment b

/-- Fitted saturated first-stage value `dhat_k = q(zᵏ)'Π`. -/
noncomputable def fittedValue (k : Fin K) : ℝ :=
  ∑ a : Fin L, S.projectionCoeff a * S.score k a

/-- The matrix first stage induces the ordered finite index consumed by the
MTW tail-coefficient and response-type algebra. -/
noncomputable def toFiniteIndex : FiniteIndex K where
  rho := S.rho
  dhat := S.fittedValue
  rho_nonneg := S.rho_nonneg
  rho_sum_one := S.rho_sum_one
  dhat_mono := by
    intro k l hkl
    simpa [fittedValue, projectionCoeff, gram] using S.fitted_mono hkl

end MatrixFirstStage

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
