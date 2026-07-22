/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sävje–Aronow–Hudgens (2021): the Hájek estimator is consistent for EATE under Bernoulli

The Hájek (ratio / inverse-probability-weighted) estimator normalizes the Horvitz–Thompson
numerators by the realized inverse-probability weight sums instead of by `n`:

    ĤA = (∑ᵢ ZᵢYᵢ/pᵢ) / (∑ᵢ Zᵢ/pᵢ) − (∑ᵢ (1−Zᵢ)Yᵢ/(1−pᵢ)) / (∑ᵢ (1−Zᵢ)/(1−pᵢ)).

Writing `Âₜ = n⁻¹∑(treated/control HT summand)` and `B̂ₜ = n⁻¹∑(weight summand)`, the ratio is
`Âₜ/B̂ₜ` (the `n` cancels). Under a Bernoulli design with restricted interference:

* `Â₁ →ₚ ȳ(1)`, `Â₀ →ₚ ȳ(0)` — vanishing variance (the same disjoint-block argument as the HT
  estimator), so each treatment/control numerator concentrates at its mean;
* `B̂₁ →ₚ 1`, `B̂₀ →ₚ 1` — the realized weight sums have mean exactly `1` (since `E[Zᵢ/pᵢ] = 1`) and
  vanishing variance (single-coordinate independence);
* the **Slutsky ratio step** `tendstoInProb_div_one` then gives `Âₜ/B̂ₜ →ₚ ȳ(t)`, and the difference
  `ĤA →ₚ ȳ(1) − ȳ(0) = EATE` (the last equality is HT unbiasedness).

The Slutsky step needs the limits `ȳ(t)` *uniformly* bounded, so this result additionally assumes
(faithfully to the paper's uniform regularity constant `k` and its Assumption C on potential-outcome
moments): a uniform bound `(Exp m).k ≤ M` and the absolute potential-outcome moment bounds
`hpo1`/`hpo0`. The interference condition is the same `k⁴·d̄/n → 0` as for the HT estimator.
-/

import Causalean.Experimentation.UnknownInterference.Consistency
import Causalean.Experimentation.DesignBased.InProb
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance

/-!
# Hájek estimation under unknown interference

The Hájek estimator normalizes treated and control inverse-probability-weighted outcome sums by
their realized weight sums. This file defines those numerator and denominator components, proves
their mean and variance controls under Bernoulli assignment, and combines them with the
finite-design Slutsky tools to prove consistency for the Sävje-Aronow-Hudgens EATE estimand.
-/

open scoped BigOperators Topology Classical
open Finset Filter

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-! ### Components of the Hájek estimator -/

/-- Treated Horvitz–Thompson summand `Zᵢ Yᵢ / pᵢ`. -/
noncomputable def htTreatSummand (p : U → ℝ) (y : U → (U → Bool) → ℝ) (i : U) (z : U → Bool) : ℝ :=
  (if z i then (1 : ℝ) else 0) * y i z / p i

/-- Control Horvitz–Thompson summand `(1 − Zᵢ) Yᵢ / (1 − pᵢ)`. -/
noncomputable def htCtrlSummand (p : U → ℝ) (y : U → (U → Bool) → ℝ) (i : U) (z : U → Bool) : ℝ :=
  (if z i then (0 : ℝ) else 1) * y i z / (1 - p i)

/-- Treated weight summand `Zᵢ / pᵢ`. -/
noncomputable def weightTreatSummand (p : U → ℝ) (i : U) (z : U → Bool) : ℝ :=
  (if z i then (1 : ℝ) else 0) / p i

/-- Control weight summand `(1 − Zᵢ) / (1 − pᵢ)`. -/
noncomputable def weightCtrlSummand (p : U → ℝ) (i : U) (z : U → Bool) : ℝ :=
  (if z i then (0 : ℝ) else 1) / (1 - p i)

/-- The treated numerator average `Â₁ = n⁻¹ ∑ᵢ Zᵢ Yᵢ / pᵢ`. -/
noncomputable def AhatTreat (p : U → ℝ) (y : U → (U → Bool) → ℝ) (z : U → Bool) : ℝ :=
  (∑ i, htTreatSummand p y i z) / (Fintype.card U : ℝ)

/-- The control numerator average `Â₀ = n⁻¹ ∑ᵢ (1−Zᵢ) Yᵢ / (1−pᵢ)`. -/
noncomputable def AhatCtrl (p : U → ℝ) (y : U → (U → Bool) → ℝ) (z : U → Bool) : ℝ :=
  (∑ i, htCtrlSummand p y i z) / (Fintype.card U : ℝ)

/-- The treated weight average `B̂₁ = n⁻¹ ∑ᵢ Zᵢ / pᵢ`. -/
noncomputable def BhatTreat (p : U → ℝ) (z : U → Bool) : ℝ :=
  (∑ i, weightTreatSummand p i z) / (Fintype.card U : ℝ)

/-- The control weight average `B̂₀ = n⁻¹ ∑ᵢ (1−Zᵢ) / (1−pᵢ)`. -/
noncomputable def BhatCtrl (p : U → ℝ) (z : U → Bool) : ℝ :=
  (∑ i, weightCtrlSummand p i z) / (Fintype.card U : ℝ)

/-- **The Hájek estimator** `ĤA = Â₁/B̂₁ − Â₀/B̂₀`, the realized-weight-normalized
inverse-probability-weighted estimator. -/
noncomputable def hajekEst (p : U → ℝ) (y : U → (U → Bool) → ℝ) (z : U → Bool) : ℝ :=
  AhatTreat p y z / BhatTreat p z - AhatCtrl p y z / BhatCtrl p z

/-! ### Mean and variance of the components -/

/-- With nonzero treatment propensities and a nonempty population, the treated weight average has
mean exactly one: `E[B̂₁] = 1`. -/
theorem E_BhatTreat (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hcard : 1 ≤ Fintype.card U) :
    (bernoulliDesign p hp0 hp1).E (BhatTreat p) = 1 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn]; exact_mod_cast Nat.one_le_iff_ne_zero.mp hcard
  have h1 : D.E (BhatTreat p) = (1 / n) * ∑ i : U, D.E (weightTreatSummand p i) := by
    have hcongr : ∀ z, BhatTreat p z = (1 / n) * ∑ i : U, weightTreatSummand p i z := by
      intro z; rw [BhatTreat, hn]; ring
    rw [D.E_congr hcongr, D.E_const_mul, D.E_sum]
  have h2 : ∀ i : U, D.E (weightTreatSummand p i) = 1 := by
    intro i
    have hc : ∀ z, weightTreatSummand p i z = (1 / p i) * (if z i then (1 : ℝ) else 0) := by
      intro z; rw [weightTreatSummand]; ring
    rw [D.E_congr hc, D.E_const_mul]
    have : D.E (fun z => if z i then (1 : ℝ) else 0) = p i := by
      rw [hD]; exact bernoulliDesign_E_treat p hp0 hp1 i
    rw [this]; field_simp [hp0' i]
  rw [h1]
  simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← hn]; field_simp

/-- With nonzero control propensities and a nonempty population, the control weight average has mean
exactly one: `E[B̂₀] = 1`. -/
theorem E_BhatCtrl (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0) (hcard : 1 ≤ Fintype.card U) :
    (bernoulliDesign p hp0 hp1).E (BhatCtrl p) = 1 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn]; exact_mod_cast Nat.one_le_iff_ne_zero.mp hcard
  have h1 : D.E (BhatCtrl p) = (1 / n) * ∑ i : U, D.E (weightCtrlSummand p i) := by
    have hcongr : ∀ z, BhatCtrl p z = (1 / n) * ∑ i : U, weightCtrlSummand p i z := by
      intro z; rw [BhatCtrl, hn]; ring
    rw [D.E_congr hcongr, D.E_const_mul, D.E_sum]
  have h2 : ∀ i : U, D.E (weightCtrlSummand p i) = 1 := by
    intro i
    have hc : ∀ z, weightCtrlSummand p i z = (1 / (1 - p i)) * (if z i then (0 : ℝ) else 1) := by
      intro z; rw [weightCtrlSummand]; ring
    rw [D.E_congr hc, D.E_const_mul]
    have : D.E (fun z => if z i then (0 : ℝ) else 1) = 1 - p i := by
      rw [hD]; exact bernoulliDesign_E_ctrl p hp0 hp1 i
    rw [this]; field_simp [hp1' i]
  rw [h1]
  simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← hn]; field_simp

/-- Monotonicity of expectation: pointwise `≤` lifts to `E` (re-stated `private` here). -/
private lemma E_mono {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) {X Y : Ω → ℝ}
    (h : ∀ z, X z ≤ Y z) : D.E X ≤ D.E Y :=
  Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z) (D.p_nonneg z))

/-- Variance is nonnegative (re-stated `private` here). -/
private lemma Var_nonneg {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) (X : Ω → ℝ) :
    0 ≤ D.Var X :=
  D.E_nonneg (fun _ => sq_nonneg _)

/-- Helper: `|D.E X| ≤ D.E |X|` (Jensen for the absolute value under a finite design). -/
private lemma abs_E_le_E_abs {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) (X : Ω → ℝ) :
    |D.E X| ≤ D.E (fun z => |X z|) := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hptw : ∀ z, 0 ≤ |X z| + X z := fun z => by
      have := neg_abs_le (X z); linarith
    have hpos : 0 ≤ D.E (fun z => |X z| + X z) := D.E_nonneg hptw
    rw [D.E_add] at hpos; linarith
  · have hptw : ∀ z, 0 ≤ |X z| - X z := fun z => by
      have := le_abs_self (X z); linarith
    have hpos : 0 ≤ D.E (fun z => |X z| - X z) := D.E_nonneg hptw
    rw [D.E_sub] at hpos; linarith

/-- Helper: the treated HT summand's expectation is the expectation of the treated potential
outcome `E[Z_i Y_i / p_i] = E[y_i(1; Z_{-i})]` (block factorization, as in `E_htSummand`). -/
private lemma E_htTreatSummand (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (y : U → (U → Bool) → ℝ) (i : U) :
    (bernoulliDesign p hp0 hp1).E (htTreatSummand p y i)
      = (bernoulliDesign p hp0 hp1).E (fun z => y i (Function.update z i true)) := by
  classical
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  set D := bernoulliDesign p hp0 hp1 with hD
  set hT : (U → Bool) → ℝ := fun z => y i (Function.update z i true) with hhT
  show D.E (htTreatSummand p y i) = D.E hT
  have hpt : ∀ z, htTreatSummand p y i z
      = (1 / p i) * ((if z i then (1 : ℝ) else 0) * hT z) := by
    intro z
    by_cases hz : z i
    · have : Function.update z i true = z := by
        funext x; by_cases hx : x = i
        · subst hx; rw [Function.update_self]; exact hz.symm
        · rw [Function.update_of_ne hx]
      simp only [htTreatSummand, hz, if_pos, hhT, this]
      field_simp
    · simp only [htTreatSummand, hz, hhT]
      simp
  rw [D.E_congr hpt, D.E_const_mul]
  have hblock : D.E (fun z => (if z i then (1 : ℝ) else 0) * hT z)
      = D.E (fun z => if z i then (1 : ℝ) else 0) * D.E hT := by
    rw [hD]
    unfold bernoulliDesign
    refine FiniteDesign.E_prod_block_mul _ {i} (fun z => if z i then (1 : ℝ) else 0) hT ?_ ?_
    · intro w w' hww
      have hwi : w i = w' i := hww i (Finset.mem_singleton_self i)
      change (if w i then (1 : ℝ) else 0) = (if w' i then (1 : ℝ) else 0)
      rw [hwi]
    · intro w w' hww
      change y i (Function.update w i true) = y i (Function.update w' i true)
      congr 1
      funext x
      by_cases hx : x = i
      · subst hx; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
        exact hww x (by simp [Finset.mem_singleton, hx])
  rw [hblock]
  have hEtreat : D.E (fun z => if z i then (1 : ℝ) else 0) = p i := by
    rw [hD]; exact bernoulliDesign_E_treat p hp0 hp1 i
  rw [hEtreat]
  field_simp [hp0' i]

/-- Helper: the control HT summand's expectation is `E[y_i(0; Z_{-i})]`. -/
private lemma E_htCtrlSummand (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0) (y : U → (U → Bool) → ℝ) (i : U) :
    (bernoulliDesign p hp0 hp1).E (htCtrlSummand p y i)
      = (bernoulliDesign p hp0 hp1).E (fun z => y i (Function.update z i false)) := by
  classical
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  set D := bernoulliDesign p hp0 hp1 with hD
  set hC : (U → Bool) → ℝ := fun z => y i (Function.update z i false) with hhC
  show D.E (htCtrlSummand p y i) = D.E hC
  have hpt : ∀ z, htCtrlSummand p y i z
      = (1 / (1 - p i)) * ((if z i then (0 : ℝ) else 1) * hC z) := by
    intro z
    by_cases hz : z i
    · simp only [htCtrlSummand, hz, if_pos, hhC]
      simp
    · have : Function.update z i false = z := by
        funext x; by_cases hx : x = i
        · subst hx; rw [Function.update_self]; simpa using hz
        · rw [Function.update_of_ne hx]
      simp only [htCtrlSummand, hz, hhC, this]
      field_simp
  rw [D.E_congr hpt, D.E_const_mul]
  have hblock : D.E (fun z => (if z i then (0 : ℝ) else 1) * hC z)
      = D.E (fun z => if z i then (0 : ℝ) else 1) * D.E hC := by
    rw [hD]
    unfold bernoulliDesign
    refine FiniteDesign.E_prod_block_mul _ {i} (fun z => if z i then (0 : ℝ) else 1) hC ?_ ?_
    · intro w w' hww
      have hwi : w i = w' i := hww i (Finset.mem_singleton_self i)
      change (if w i then (0 : ℝ) else 1) = (if w' i then (0 : ℝ) else 1)
      rw [hwi]
    · intro w w' hww
      change y i (Function.update w i false) = y i (Function.update w' i false)
      congr 1
      funext x
      by_cases hx : x = i
      · subst hx; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
        exact hww x (by simp [Finset.mem_singleton, hx])
  rw [hblock]
  have hEctrl : D.E (fun z => if z i then (0 : ℝ) else 1) = 1 - p i := by
    rw [hD]; exact bernoulliDesign_E_ctrl p hp0 hp1 i
  rw [hEctrl]
  field_simp [hp1' i]

/-! ### Disjoint-block helpers for the treated/control numerator summands -/

/-- The treated HT summand `Zᵢ Yᵢ / pᵢ` depends only on the treatments of `i`'s interferers. -/
private theorem htTreatSummand_depends_on_interferers (p : U → ℝ) (y : U → (U → Bool) → ℝ) (i : U)
    (z z' : U → Bool) (h : ∀ ℓ ∈ interferers y i, z ℓ = z' ℓ) :
    htTreatSummand p y i z = htTreatSummand p y i z' := by
  have hmem : ∀ ℓ : U, Interferes y ℓ i → ℓ ∈ interferers y i := by
    intro ℓ hℓ; exact Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, hℓ⟩
  have hzi : z i = z' i := h i (hmem i (Or.inl rfl))
  have hyi : y i z = y i z' :=
    y_eq_of_agree_on_interferers y i z z' (fun ℓ hℓ => h ℓ (hmem ℓ hℓ))
  unfold htTreatSummand; rw [hzi, hyi]

/-- The control HT summand `(1−Zᵢ) Yᵢ / (1−pᵢ)` depends only on the treatments of
`i`'s interferers. -/
private theorem htCtrlSummand_depends_on_interferers (p : U → ℝ) (y : U → (U → Bool) → ℝ) (i : U)
    (z z' : U → Bool) (h : ∀ ℓ ∈ interferers y i, z ℓ = z' ℓ) :
    htCtrlSummand p y i z = htCtrlSummand p y i z' := by
  have hmem : ∀ ℓ : U, Interferes y ℓ i → ℓ ∈ interferers y i := by
    intro ℓ hℓ; exact Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, hℓ⟩
  have hzi : z i = z' i := h i (hmem i (Or.inl rfl))
  have hyi : y i z = y i z' :=
    y_eq_of_agree_on_interferers y i z z' (fun ℓ hℓ => h ℓ (hmem ℓ hℓ))
  unfold htCtrlSummand; rw [hzi, hyi]

/-- Treated summands are uncorrelated off the interference-dependence graph. -/
private theorem cov_htTreatSummand_zero (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) {i j : U} (h : ¬ InterfDep y i j) :
    (bernoulliDesign p hp0 hp1).Cov (htTreatSummand p y i) (htTreatSummand p y j) = 0 := by
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  unfold bernoulliDesign
  exact FiniteDesign.Cov_prod_disjoint_zero (fun i => coinDesign (p i) (hp0 i) (hp1 i))
    (interferers y i) (interferers y j) (disjoint_interferers_of_not_interfDep y h)
    (htTreatSummand p y i) (htTreatSummand p y j)
    (fun z z' hzz => htTreatSummand_depends_on_interferers p y i z z' hzz)
    (fun z z' hzz => htTreatSummand_depends_on_interferers p y j z z' hzz)

/-- Control summands are uncorrelated off the interference-dependence graph. -/
private theorem cov_htCtrlSummand_zero (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) {i j : U} (h : ¬ InterfDep y i j) :
    (bernoulliDesign p hp0 hp1).Cov (htCtrlSummand p y i) (htCtrlSummand p y j) = 0 := by
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  unfold bernoulliDesign
  exact FiniteDesign.Cov_prod_disjoint_zero (fun i => coinDesign (p i) (hp0 i) (hp1 i))
    (interferers y i) (interferers y j) (disjoint_interferers_of_not_interfDep y h)
    (htCtrlSummand p y i) (htCtrlSummand p y j)
    (fun z z' hzz => htCtrlSummand_depends_on_interferers p y i z z' hzz)
    (fun z z' hzz => htCtrlSummand_depends_on_interferers p y j z z' hzz)

/-- Per-summand variance bound for the treated summand: `Var(Zᵢ Yᵢ/pᵢ) ≤ k⁴`. -/
private theorem var_htTreatSummand_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k)
    (hplo : ∀ i, k⁻¹ ≤ p i) (hphi : ∀ i, p i ≤ 1 - k⁻¹)
    (hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2) (i : U) :
    (bernoulliDesign p hp0 hp1).Var (htTreatSummand p y i) ≤ k ^ 4 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkinv0 : (0 : ℝ) < k⁻¹ := inv_pos.mpr hk0
  have hpi0 : (0 : ℝ) < p i := lt_of_lt_of_le hkinv0 (hplo i)
  have hrecp : 1 / p i ≤ k := by
    rw [div_le_iff₀ hpi0]
    nlinarith [mul_le_mul_of_nonneg_right (hplo i) (le_of_lt hk0), inv_mul_cancel₀ (ne_of_gt hk0)]
  -- Pointwise `(htTreatSummand)² ≤ k² (y i)²`.
  have hpt : ∀ z, (htTreatSummand p y i z) ^ 2 ≤ k ^ 2 * (y i z) ^ 2 := by
    intro z
    have habs : |htTreatSummand p y i z| ≤ k * |y i z| := by
      unfold htTreatSummand
      by_cases hz : z i = true
      · rw [if_pos hz]
        rw [show (1 : ℝ) * y i z / p i = y i z / p i by ring]
        rw [abs_div, abs_of_pos hpi0]
        calc |y i z| / p i = |y i z| * (1 / p i) := by ring
          _ ≤ |y i z| * k := mul_le_mul_of_nonneg_left hrecp (abs_nonneg _)
          _ = k * |y i z| := by ring
      · rw [if_neg hz]
        rw [show (0 : ℝ) * y i z / p i = 0 by ring, abs_zero]
        have : (0 : ℝ) ≤ k * |y i z| := mul_nonneg (le_of_lt hk0) (abs_nonneg _)
        linarith
    have h1 : (htTreatSummand p y i z) ^ 2 = |htTreatSummand p y i z| ^ 2 := (sq_abs _).symm
    have h2 : (k * |y i z|) ^ 2 = k ^ 2 * (y i z) ^ 2 := by rw [mul_pow, sq_abs]
    rw [h1, ← h2]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc D.Var (htTreatSummand p y i)
      ≤ D.E (fun z => (htTreatSummand p y i z) ^ 2) := by
        rw [D.Var_eq]; linarith [sq_nonneg (D.E (htTreatSummand p y i))]
    _ ≤ D.E (fun z => k ^ 2 * (y i z) ^ 2) := E_mono D hpt
    _ = k ^ 2 * D.E (fun z => (y i z) ^ 2) := D.E_const_mul _ _
    _ ≤ k ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_left (hmom i) (sq_nonneg k)
    _ = k ^ 4 := by ring

/-- Per-summand variance bound for the control summand: `Var((1−Zᵢ) Yᵢ/(1−pᵢ)) ≤ k⁴`. -/
private theorem var_htCtrlSummand_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k)
    (hplo : ∀ i, k⁻¹ ≤ p i) (hphi : ∀ i, p i ≤ 1 - k⁻¹)
    (hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2) (i : U) :
    (bernoulliDesign p hp0 hp1).Var (htCtrlSummand p y i) ≤ k ^ 4 := by
  set D := bernoulliDesign p hp0 hp1 with hD
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkinv0 : (0 : ℝ) < k⁻¹ := inv_pos.mpr hk0
  have hpi1 : (0 : ℝ) < 1 - p i := lt_of_lt_of_le hkinv0 (by linarith [hphi i])
  have hrecq : 1 / (1 - p i) ≤ k := by
    rw [div_le_iff₀ hpi1]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith [hphi i] : k⁻¹ ≤ 1 - p i) (le_of_lt hk0),
      inv_mul_cancel₀ (ne_of_gt hk0)]
  have hpt : ∀ z, (htCtrlSummand p y i z) ^ 2 ≤ k ^ 2 * (y i z) ^ 2 := by
    intro z
    have habs : |htCtrlSummand p y i z| ≤ k * |y i z| := by
      unfold htCtrlSummand
      by_cases hz : z i = true
      · rw [if_pos hz]
        rw [show (0 : ℝ) * y i z / (1 - p i) = 0 by ring, abs_zero]
        have : (0 : ℝ) ≤ k * |y i z| := mul_nonneg (le_of_lt hk0) (abs_nonneg _)
        linarith
      · rw [if_neg hz]
        rw [show (1 : ℝ) * y i z / (1 - p i) = y i z / (1 - p i) by ring]
        rw [abs_div, abs_of_pos hpi1]
        calc |y i z| / (1 - p i) = |y i z| * (1 / (1 - p i)) := by ring
          _ ≤ |y i z| * k := mul_le_mul_of_nonneg_left hrecq (abs_nonneg _)
          _ = k * |y i z| := by ring
    have h1 : (htCtrlSummand p y i z) ^ 2 = |htCtrlSummand p y i z| ^ 2 := (sq_abs _).symm
    have h2 : (k * |y i z|) ^ 2 = k ^ 2 * (y i z) ^ 2 := by rw [mul_pow, sq_abs]
    rw [h1, ← h2]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc D.Var (htCtrlSummand p y i)
      ≤ D.E (fun z => (htCtrlSummand p y i z) ^ 2) := by
        rw [D.Var_eq]; linarith [sq_nonneg (D.E (htCtrlSummand p y i))]
    _ ≤ D.E (fun z => k ^ 2 * (y i z) ^ 2) := E_mono D hpt
    _ = k ^ 2 * D.E (fun z => (y i z) ^ 2) := D.E_const_mul _ _
    _ ≤ k ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_left (hmom i) (sq_nonneg k)
    _ = k ^ 4 := by ring

/-- Variance bound for the treated numerator average: `Var(Â₁) ≤ k⁴·d̄/n` (same disjoint-block
argument as the HT estimator). -/
theorem var_AhatTreat_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U)
    (hplo : ∀ i, k⁻¹ ≤ p i) (hphi : ∀ i, p i ≤ 1 - k⁻¹)
    (hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2) :
    (bernoulliDesign p hp0 hp1).Var (AhatTreat p y) ≤ k ^ 4 * dbar y / (Fintype.card U : ℝ) := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by rw [hn]; exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  have hcov : ∀ i j, D.Cov (htTreatSummand p y i) (htTreatSummand p y j)
      ≤ (if InterfDep y i j then (k ^ 4 : ℝ) else 0) := by
    intro i j
    by_cases hdep : InterfDep y i j
    · rw [if_pos hdep]
      have hVsub : 0 ≤ D.Var (fun z => htTreatSummand p y i z - htTreatSummand p y j z) :=
        Var_nonneg D _
      rw [D.Var_sub] at hVsub
      have hVi : D.Var (htTreatSummand p y i) ≤ k ^ 4 :=
        var_htTreatSummand_le p hp0 hp1 y k hk hplo hphi hmom i
      have hVj : D.Var (htTreatSummand p y j) ≤ k ^ 4 :=
        var_htTreatSummand_le p hp0 hp1 y k hk hplo hphi hmom j
      linarith
    · rw [if_neg hdep]
      exact le_of_eq (cov_htTreatSummand_zero p hp0 hp1 y hdep)
  have hEstEq : AhatTreat p y
      = fun z => n⁻¹ * ∑ i : U, (1 : ℝ) * htTreatSummand p y i z := by
    funext z; unfold AhatTreat; rw [hn, div_eq_inv_mul]; congr 1
    exact Finset.sum_congr rfl (fun i _ => (one_mul _).symm)
  have hVarEst : D.Var (AhatTreat p y)
      = (n⁻¹) ^ 2 * ∑ i : U, ∑ j : U, D.Cov (htTreatSummand p y i) (htTreatSummand p y j) := by
    rw [hEstEq, D.Var_const_mul, D.Var_linear_comb Finset.univ (fun _ => (1:ℝ)) (htTreatSummand p y)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [one_mul, one_mul]
  have hsumle : (∑ i : U, ∑ j : U, D.Cov (htTreatSummand p y i) (htTreatSummand p y j))
      ≤ k ^ 4 * dbarCount y := by
    have hstep : (∑ i : U, ∑ j : U, D.Cov (htTreatSummand p y i) (htTreatSummand p y j))
        ≤ ∑ i : U, ∑ j : U, (if InterfDep y i j then (k ^ 4 : ℝ) else 0) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    refine le_trans hstep ?_
    rw [dbarCount, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hdep : InterfDep y i j <;> simp [hdep]
  rw [hVarEst]
  have hninv2 : (0 : ℝ) ≤ (n⁻¹) ^ 2 := sq_nonneg _
  calc (n⁻¹) ^ 2 * ∑ i : U, ∑ j : U, D.Cov (htTreatSummand p y i) (htTreatSummand p y j)
      ≤ (n⁻¹) ^ 2 * (k ^ 4 * dbarCount y) := mul_le_mul_of_nonneg_left hsumle hninv2
    _ = k ^ 4 * dbar y / n := by rw [dbar, hn]; ring

/-- Variance bound for the control numerator average: `Var(Â₀) ≤ k⁴·d̄/n`. -/
theorem var_AhatCtrl_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U)
    (hplo : ∀ i, k⁻¹ ≤ p i) (hphi : ∀ i, p i ≤ 1 - k⁻¹)
    (hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2) :
    (bernoulliDesign p hp0 hp1).Var (AhatCtrl p y) ≤ k ^ 4 * dbar y / (Fintype.card U : ℝ) := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by rw [hn]; exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  have hcov : ∀ i j, D.Cov (htCtrlSummand p y i) (htCtrlSummand p y j)
      ≤ (if InterfDep y i j then (k ^ 4 : ℝ) else 0) := by
    intro i j
    by_cases hdep : InterfDep y i j
    · rw [if_pos hdep]
      have hVsub : 0 ≤ D.Var (fun z => htCtrlSummand p y i z - htCtrlSummand p y j z) :=
        Var_nonneg D _
      rw [D.Var_sub] at hVsub
      have hVi : D.Var (htCtrlSummand p y i) ≤ k ^ 4 :=
        var_htCtrlSummand_le p hp0 hp1 y k hk hplo hphi hmom i
      have hVj : D.Var (htCtrlSummand p y j) ≤ k ^ 4 :=
        var_htCtrlSummand_le p hp0 hp1 y k hk hplo hphi hmom j
      linarith
    · rw [if_neg hdep]
      exact le_of_eq (cov_htCtrlSummand_zero p hp0 hp1 y hdep)
  have hEstEq : AhatCtrl p y
      = fun z => n⁻¹ * ∑ i : U, (1 : ℝ) * htCtrlSummand p y i z := by
    funext z; unfold AhatCtrl; rw [hn, div_eq_inv_mul]; congr 1
    exact Finset.sum_congr rfl (fun i _ => (one_mul _).symm)
  have hVarEst : D.Var (AhatCtrl p y)
      = (n⁻¹) ^ 2 * ∑ i : U, ∑ j : U, D.Cov (htCtrlSummand p y i) (htCtrlSummand p y j) := by
    rw [hEstEq, D.Var_const_mul, D.Var_linear_comb Finset.univ (fun _ => (1:ℝ)) (htCtrlSummand p y)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [one_mul, one_mul]
  have hsumle : (∑ i : U, ∑ j : U, D.Cov (htCtrlSummand p y i) (htCtrlSummand p y j))
      ≤ k ^ 4 * dbarCount y := by
    have hstep : (∑ i : U, ∑ j : U, D.Cov (htCtrlSummand p y i) (htCtrlSummand p y j))
        ≤ ∑ i : U, ∑ j : U, (if InterfDep y i j then (k ^ 4 : ℝ) else 0) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    refine le_trans hstep ?_
    rw [dbarCount, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hdep : InterfDep y i j <;> simp [hdep]
  rw [hVarEst]
  have hninv2 : (0 : ℝ) ≤ (n⁻¹) ^ 2 := sq_nonneg _
  calc (n⁻¹) ^ 2 * ∑ i : U, ∑ j : U, D.Cov (htCtrlSummand p y i) (htCtrlSummand p y j)
      ≤ (n⁻¹) ^ 2 * (k ^ 4 * dbarCount y) := mul_le_mul_of_nonneg_left hsumle hninv2
    _ = k ^ 4 * dbar y / n := by rw [dbar, hn]; ring

/-- Variance bound for the treated weight average: `Var(B̂₁) ≤ k²/n` (single-coordinate
independence — the weight summands `Zᵢ/pᵢ` depend on disjoint singletons). -/
theorem var_BhatTreat_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U) (hplo : ∀ i, k⁻¹ ≤ p i) :
    (bernoulliDesign p hp0 hp1).Var (BhatTreat p) ≤ k ^ 2 / (Fintype.card U : ℝ) := by
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by rw [hn]; exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkinv0 : (0 : ℝ) < k⁻¹ := inv_pos.mpr hk0
  -- single-coordinate function `g_i b = (if b then 1 else 0)/p i`
  set g : U → Bool → ℝ := fun i b => (if b then (1 : ℝ) else 0) / p i with hg
  -- `BhatTreat = fun z => ∑ i, (n⁻¹) * g i (z i)`
  have hBeq : BhatTreat p
      = fun z => ∑ i : U, n⁻¹ * g i (z i) := by
    funext z; unfold BhatTreat weightTreatSummand
    rw [hn, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hg]; ring
  -- per-coordinate variance bound `Var(g i) ≤ k²`
  have hVcoord : ∀ i, (coinDesign (p i) (hp0 i) (hp1 i)).Var (g i) ≤ k ^ 2 := by
    intro i
    have hpi0 : (0 : ℝ) < p i := lt_of_lt_of_le hkinv0 (hplo i)
    have hrecp : 1 / p i ≤ k := by
      rw [div_le_iff₀ hpi0]
      nlinarith [mul_le_mul_of_nonneg_right (hplo i) (le_of_lt hk0), inv_mul_cancel₀ (ne_of_gt hk0)]
    have hEsq : (coinDesign (p i) (hp0 i) (hp1 i)).E (fun b => (g i b) ^ 2) = 1 / p i := by
      have h0 : p i ≠ 0 := ne_of_gt hpi0
      rw [coinDesign_E]; simp only [hg]; norm_num; field_simp
    have hVle : (coinDesign (p i) (hp0 i) (hp1 i)).Var (g i)
        ≤ (coinDesign (p i) (hp0 i) (hp1 i)).E (fun b => (g i b) ^ 2) := by
      rw [(coinDesign (p i) (hp0 i) (hp1 i)).Var_eq]
      linarith [sq_nonneg ((coinDesign (p i) (hp0 i) (hp1 i)).E (g i))]
    have hk2 : (1 : ℝ) / p i ≤ k ^ 2 := by nlinarith [hrecp, hk]
    linarith [le_trans hVle (le_of_eq hEsq)]
  -- apply the product-design linear-combination variance identity
  rw [hBeq]
  unfold bernoulliDesign
  rw [FiniteDesign.Var_prod_linear_comb (fun i => coinDesign (p i) (hp0 i) (hp1 i))
        (fun _ => n⁻¹) g]
  -- `∑ i, (n⁻¹)² · Var(g i) ≤ ∑ i, (n⁻¹)² · k² = n · (n⁻¹)² · k² = k²/n`
  have hninv2 : (0 : ℝ) ≤ (n⁻¹) ^ 2 := sq_nonneg _
  have hstep : (∑ i : U, (n⁻¹) ^ 2 * (coinDesign (p i) (hp0 i) (hp1 i)).Var (g i))
      ≤ ∑ _i : U, (n⁻¹) ^ 2 * k ^ 2 :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hVcoord i) hninv2)
  refine le_trans hstep ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
  rw [show (n : ℝ) * ((n⁻¹) ^ 2 * k ^ 2) = (n * n⁻¹) * (n⁻¹ * k ^ 2) by ring]
  rw [mul_inv_cancel₀ (ne_of_gt hn0), one_mul, inv_mul_eq_div]

/-- Variance bound for the control weight average: `Var(B̂₀) ≤ k²/n`. -/
theorem var_BhatCtrl_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U) (hphi : ∀ i, p i ≤ 1 - k⁻¹) :
    (bernoulliDesign p hp0 hp1).Var (BhatCtrl p) ≤ k ^ 2 / (Fintype.card U : ℝ) := by
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by rw [hn]; exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkinv0 : (0 : ℝ) < k⁻¹ := inv_pos.mpr hk0
  -- single-coordinate function `g_i b = (if b then 0 else 1)/(1 - p i)`
  set g : U → Bool → ℝ := fun i b => (if b then (0 : ℝ) else 1) / (1 - p i) with hg
  have hBeq : BhatCtrl p
      = fun z => ∑ i : U, n⁻¹ * g i (z i) := by
    funext z; unfold BhatCtrl weightCtrlSummand
    rw [hn, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hg]; ring
  have hVcoord : ∀ i, (coinDesign (p i) (hp0 i) (hp1 i)).Var (g i) ≤ k ^ 2 := by
    intro i
    have hpi1 : (0 : ℝ) < 1 - p i := lt_of_lt_of_le hkinv0 (by linarith [hphi i])
    have hrecq : 1 / (1 - p i) ≤ k := by
      rw [div_le_iff₀ hpi1]
      nlinarith [mul_le_mul_of_nonneg_right (by linarith [hphi i] : k⁻¹ ≤ 1 - p i) (le_of_lt hk0),
        inv_mul_cancel₀ (ne_of_gt hk0)]
    have hEsq : (coinDesign (p i) (hp0 i) (hp1 i)).E (fun b => (g i b) ^ 2) = 1 / (1 - p i) := by
      have h1 : (1 : ℝ) - p i ≠ 0 := ne_of_gt hpi1
      rw [coinDesign_E]; simp only [hg]; norm_num; field_simp
    have hVle : (coinDesign (p i) (hp0 i) (hp1 i)).Var (g i)
        ≤ (coinDesign (p i) (hp0 i) (hp1 i)).E (fun b => (g i b) ^ 2) := by
      rw [(coinDesign (p i) (hp0 i) (hp1 i)).Var_eq]
      linarith [sq_nonneg ((coinDesign (p i) (hp0 i) (hp1 i)).E (g i))]
    have hk2 : (1 : ℝ) / (1 - p i) ≤ k ^ 2 := by nlinarith [hrecq, hk]
    linarith [le_trans hVle (le_of_eq hEsq)]
  rw [hBeq]
  unfold bernoulliDesign
  rw [FiniteDesign.Var_prod_linear_comb (fun i => coinDesign (p i) (hp0 i) (hp1 i))
        (fun _ => n⁻¹) g]
  have hninv2 : (0 : ℝ) ≤ (n⁻¹) ^ 2 := sq_nonneg _
  have hstep : (∑ i : U, (n⁻¹) ^ 2 * (coinDesign (p i) (hp0 i) (hp1 i)).Var (g i))
      ≤ ∑ _i : U, (n⁻¹) ^ 2 * k ^ 2 :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hVcoord i) hninv2)
  refine le_trans hstep ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
  rw [show (n : ℝ) * ((n⁻¹) ^ 2 * k ^ 2) = (n * n⁻¹) * (n⁻¹ * k ^ 2) by ring]
  rw [mul_inv_cancel₀ (ne_of_gt hn0), one_mul, inv_mul_eq_div]

/-- The treated numerator mean is the average treated potential outcome, uniformly bounded by `k`
via the potential-outcome moment bound (Assumption C). -/
theorem abs_E_AhatTreat_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U)
    (hpo : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => |y i (Function.update z i true)|) ≤ k) :
    |(bernoulliDesign p hp0 hp1).E (AhatTreat p y)| ≤ k := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by
    rw [hn]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hcard
  -- `E[Â₁] = (1/n) * ∑ i E[htTreatSummand i]`.
  have h1 : D.E (AhatTreat p y) = (1 / n) * ∑ i : U, D.E (htTreatSummand p y i) := by
    have hcongr : ∀ z, AhatTreat p y z = (1 / n) * ∑ i : U, htTreatSummand p y i z := by
      intro z; rw [AhatTreat, hn]; ring
    rw [D.E_congr hcongr, D.E_const_mul, D.E_sum]
  -- Each summand's expectation is bounded by `k`.
  have hbound : ∀ i : U, |D.E (htTreatSummand p y i)| ≤ k := by
    intro i
    rw [E_htTreatSummand p hp0 hp1 hp0' y i]
    exact le_trans (abs_E_le_E_abs D _) (hpo i)
  rw [h1, abs_mul]
  have hpos : |1 / n| = 1 / n := abs_of_pos (by positivity)
  rw [hpos]
  calc (1 / n) * |∑ i : U, D.E (htTreatSummand p y i)|
      ≤ (1 / n) * ∑ i : U, |D.E (htTreatSummand p y i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / n) * ∑ i : U, k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hbound i)) (by positivity)
    _ = k := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
        field_simp

/-- The control numerator mean is the average control potential outcome, uniformly bounded
by `k`. -/
theorem abs_E_AhatCtrl_le (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0)
    (y : U → (U → Bool) → ℝ) (k : ℝ) (hk : 1 ≤ k) (hcard : 1 ≤ Fintype.card U)
    (hpo : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => |y i (Function.update z i false)|) ≤ k) :
    |(bernoulliDesign p hp0 hp1).E (AhatCtrl p y)| ≤ k := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by
    rw [hn]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hcard
  have h1 : D.E (AhatCtrl p y) = (1 / n) * ∑ i : U, D.E (htCtrlSummand p y i) := by
    have hcongr : ∀ z, AhatCtrl p y z = (1 / n) * ∑ i : U, htCtrlSummand p y i z := by
      intro z; rw [AhatCtrl, hn]; ring
    rw [D.E_congr hcongr, D.E_const_mul, D.E_sum]
  have hbound : ∀ i : U, |D.E (htCtrlSummand p y i)| ≤ k := by
    intro i
    rw [E_htCtrlSummand p hp0 hp1 hp1' y i]
    exact le_trans (abs_E_le_E_abs D _) (hpo i)
  rw [h1, abs_mul]
  have hpos : |1 / n| = 1 / n := abs_of_pos (by positivity)
  rw [hpos]
  calc (1 / n) * |∑ i : U, D.E (htCtrlSummand p y i)|
      ≤ (1 / n) * ∑ i : U, |D.E (htCtrlSummand p y i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / n) * ∑ i : U, k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hbound i)) (by positivity)
    _ = k := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
        field_simp

/-- The difference of the numerator means is EATE: `E[Â₁] − E[Â₀] = EATE` (the HT estimator is
`Â₁ − Â₀`, and it is unbiased). -/
theorem E_AhatTreat_sub_E_AhatCtrl (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0) (y : U → (U → Bool) → ℝ) :
    (bernoulliDesign p hp0 hp1).E (AhatTreat p y) - (bernoulliDesign p hp0 hp1).E (AhatCtrl p y)
      = EATE (bernoulliDesign p hp0 hp1) y := by
  set D := bernoulliDesign p hp0 hp1 with hD
  rw [← D.E_sub]
  -- Pointwise `AhatTreat - AhatCtrl = htEst`.
  have hpt : ∀ z, AhatTreat p y z - AhatCtrl p y z = htEst p y z := by
    intro z
    rw [AhatTreat, AhatCtrl, htEst, ← sub_div]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [htSummand, htTreatSummand, htCtrlSummand]
  rw [D.E_congr hpt]
  rw [hD]
  exact htEst_unbiased p hp0 hp1 hp0' hp1' y

/-- Helper: `1 ≤ d̄` whenever the population is nonempty. The diagonal terms `InterfDep y i i`
always hold (witness `ℓ = i`), so `dbarCount y ≥ n`, hence `dbar y = dbarCount/n ≥ 1`. -/
private lemma one_le_dbar (y : U → (U → Bool) → ℝ) (hcard : 1 ≤ Fintype.card U) :
    (1 : ℝ) ≤ dbar y := by
  have hn0 : (0 : ℝ) < (Fintype.card U : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hcard
  have hdiag : ∀ i : U, InterfDep y i i := fun i => ⟨i, Or.inl rfl, Or.inl rfl⟩
  have hcount : (Fintype.card U : ℝ) ≤ dbarCount y := by
    rw [dbarCount]
    calc (Fintype.card U : ℝ)
        = ∑ _i : U, (1 : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ = ∑ i : U, (if InterfDep y i i then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [if_pos (hdiag i)]
      _ ≤ ∑ i : U, ∑ j : U, (if InterfDep y i j then (1 : ℝ) else 0) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            refine Finset.single_le_sum (f := fun j => if InterfDep y i j then (1 : ℝ) else 0)
              (fun j _ => ?_) (Finset.mem_univ i)
            by_cases h : InterfDep y i j <;> simp [h]
  rw [dbar, le_div_iff₀ hn0, one_mul]
  exact hcount

/-! ### Consistency -/

/-- **Consistency of the Hájek estimator for EATE (Sävje–Aronow–Hudgens 2021).** Along a sequence
of Bernoulli experiments with restricted interference (`k⁴·d̄/n → 0`), uniformly bounded regularity
constant (`(Exp m).k ≤ M`), and bounded potential-outcome moments (`hpo1`/`hpo0`, the paper's
Assumption C), the Hájek estimator converges in probability to EATE. -/
theorem hajek_consistent_eate (Exp : ℕ → SAHExperiment) (M : ℝ)
    (hM : ∀ m, (Exp m).k ≤ M)
    (hrate : Tendsto (fun m => (Exp m).k ^ 4 * dbar (Exp m).y / (Fintype.card (Exp m).U : ℝ))
      atTop (𝓝 0))
    (hpo1 : ∀ m i, (Exp m).D.E (fun z => |(Exp m).y i (Function.update z i true)|) ≤ (Exp m).k)
    (hpo0 : ∀ m i, (Exp m).D.E (fun z => |(Exp m).y i (Function.update z i false)|) ≤ (Exp m).k) :
    FiniteDesign.TendstoInProb (fun m => (Exp m).D)
      (fun m => hajekEst (Exp m).p (Exp m).y) (fun m => (Exp m).eate) := by
  set D : ∀ m, FiniteDesign ((Exp m).U → Bool) := fun m => (Exp m).D with hDdef
  -- The numerator means (limit sequences for `Â₁`, `Â₀`).
  set ybar1 : ℕ → ℝ := fun m => (D m).E (AhatTreat (Exp m).p (Exp m).y) with hybar1
  set ybar0 : ℕ → ℝ := fun m => (D m).E (AhatCtrl (Exp m).p (Exp m).y) with hybar0
  -- Unfold `D m` to the underlying Bernoulli design.
  have hDm : ∀ m, D m = bernoulliDesign (Exp m).p (Exp m).hp0 (Exp m).hp1 := by
    intro m; simp only [hDdef, SAHExperiment.D]
  -- (A) Variance → 0 facts.
  have hvarA1 : Tendsto (fun m => (D m).Var (AhatTreat (Exp m).p (Exp m).y)) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => Var_nonneg (D m) _) (fun m => ?_) hrate
    rw [hDm m]
    exact var_AhatTreat_le (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).y (Exp m).k (Exp m).hk
      (Exp m).hcard (Exp m).hplo (Exp m).hphi (Exp m).hmom
  have hvarA0 : Tendsto (fun m => (D m).Var (AhatCtrl (Exp m).p (Exp m).y)) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => Var_nonneg (D m) _) (fun m => ?_) hrate
    rw [hDm m]
    exact var_AhatCtrl_le (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).y (Exp m).k (Exp m).hk
      (Exp m).hcard (Exp m).hplo (Exp m).hphi (Exp m).hmom
  -- The `k²/n ≤ k⁴·d̄/n` squeeze for the weight variances.
  have hweightle : ∀ m, (Exp m).k ^ 2 / (Fintype.card (Exp m).U : ℝ)
      ≤ (Exp m).k ^ 4 * dbar (Exp m).y / (Fintype.card (Exp m).U : ℝ) := by
    intro m
    have hn0 : (0 : ℝ) < (Fintype.card (Exp m).U : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one (Exp m).hcard
    apply div_le_div_of_nonneg_right _ hn0.le
    have hk1 : (1 : ℝ) ≤ (Exp m).k := (Exp m).hk
    have hd1 : (1 : ℝ) ≤ dbar (Exp m).y := one_le_dbar (Exp m).y (Exp m).hcard
    have hk2 : (1 : ℝ) ≤ (Exp m).k ^ 2 := by nlinarith [hk1]
    have hk4 : (Exp m).k ^ 2 ≤ (Exp m).k ^ 4 := by nlinarith [hk1, hk2]
    have hstep : (Exp m).k ^ 4 ≤ (Exp m).k ^ 4 * dbar (Exp m).y := by
      nlinarith [hd1, pow_nonneg (le_trans zero_le_one hk1) 4]
    linarith
  have hvarB1 : Tendsto (fun m => (D m).Var (BhatTreat (Exp m).p)) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => Var_nonneg (D m) _) (fun m => ?_) hrate
    refine le_trans ?_ (hweightle m)
    rw [hDm m]
    exact var_BhatTreat_le (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).k (Exp m).hk
      (Exp m).hcard (Exp m).hplo
  have hvarB0 : Tendsto (fun m => (D m).Var (BhatCtrl (Exp m).p)) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => Var_nonneg (D m) _) (fun m => ?_) hrate
    refine le_trans ?_ (hweightle m)
    rw [hDm m]
    exact var_BhatCtrl_le (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).k (Exp m).hk
      (Exp m).hcard (Exp m).hphi
  -- (B) Component convergences.
  have hA1 : FiniteDesign.TendstoInProb D (fun m => AhatTreat (Exp m).p (Exp m).y) ybar1 :=
    FiniteDesign.tendstoInProb_of_var D _ hvarA1
  have hA0 : FiniteDesign.TendstoInProb D (fun m => AhatCtrl (Exp m).p (Exp m).y) ybar0 :=
    FiniteDesign.tendstoInProb_of_var D _ hvarA0
  have hB1 : FiniteDesign.TendstoInProb D (fun m => BhatTreat (Exp m).p) (fun _ => 1) := by
    have hraw := FiniteDesign.tendstoInProb_of_var D (fun m => BhatTreat (Exp m).p) hvarB1
    have heq : (fun m => (D m).E (BhatTreat (Exp m).p)) = (fun _ => (1 : ℝ)) := by
      funext m; rw [hDm m]
      exact E_BhatTreat (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).p_ne_zero (Exp m).hcard
    rw [heq] at hraw; exact hraw
  have hB0 : FiniteDesign.TendstoInProb D (fun m => BhatCtrl (Exp m).p) (fun _ => 1) := by
    have hraw := FiniteDesign.tendstoInProb_of_var D (fun m => BhatCtrl (Exp m).p) hvarB0
    have heq : (fun m => (D m).E (BhatCtrl (Exp m).p)) = (fun _ => (1 : ℝ)) := by
      funext m; rw [hDm m]
      exact E_BhatCtrl (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).one_sub_p_ne_zero (Exp m).hcard
    rw [heq] at hraw; exact hraw
  -- (C) Ratios via Slutsky.
  have hbound1 : ∀ m, |ybar1 m| ≤ M := by
    intro m
    refine le_trans ?_ (hM m)
    change |(D m).E (AhatTreat (Exp m).p (Exp m).y)| ≤ (Exp m).k
    rw [hDm m]
    exact abs_E_AhatTreat_le (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).p_ne_zero
      (Exp m).one_sub_p_ne_zero (Exp m).y (Exp m).k (Exp m).hk (Exp m).hcard
      (by intro i; have := hpo1 m i; unfold SAHExperiment.D at this; exact this)
  have hbound0 : ∀ m, |ybar0 m| ≤ M := by
    intro m
    refine le_trans ?_ (hM m)
    change |(D m).E (AhatCtrl (Exp m).p (Exp m).y)| ≤ (Exp m).k
    rw [hDm m]
    exact abs_E_AhatCtrl_le (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).p_ne_zero
      (Exp m).one_sub_p_ne_zero (Exp m).y (Exp m).k (Exp m).hk (Exp m).hcard
      (by intro i; have := hpo0 m i; unfold SAHExperiment.D at this; exact this)
  have hR1 : FiniteDesign.TendstoInProb D
      (fun m z => AhatTreat (Exp m).p (Exp m).y z / BhatTreat (Exp m).p z) ybar1 :=
    FiniteDesign.tendstoInProb_div_one D _ _ ybar1 M hbound1 hA1 hB1
  have hR0 : FiniteDesign.TendstoInProb D
      (fun m z => AhatCtrl (Exp m).p (Exp m).y z / BhatCtrl (Exp m).p z) ybar0 :=
    FiniteDesign.tendstoInProb_div_one D _ _ ybar0 M hbound0 hA0 hB0
  -- (D) Difference.
  have hdiff := hR1.sub hR0
  -- The statistic is exactly `hajekEst`.
  have hstat : (fun m z => AhatTreat (Exp m).p (Exp m).y z / BhatTreat (Exp m).p z
      - AhatCtrl (Exp m).p (Exp m).y z / BhatCtrl (Exp m).p z)
      = (fun m => hajekEst (Exp m).p (Exp m).y) := by
    funext m z; rw [hajekEst]
  -- The limit sequence is `eate`.
  have hlim : (fun m => ybar1 m - ybar0 m) = (fun m => (Exp m).eate) := by
    funext m
    change (D m).E (AhatTreat (Exp m).p (Exp m).y) - (D m).E (AhatCtrl (Exp m).p (Exp m).y)
      = (Exp m).eate
    rw [SAHExperiment.eate, EATE, hDm m]
    have hsub := E_AhatTreat_sub_E_AhatCtrl (Exp m).p (Exp m).hp0 (Exp m).hp1 (Exp m).p_ne_zero
      (Exp m).one_sub_p_ne_zero (Exp m).y
    rw [EATE] at hsub
    rw [show SAHExperiment.D (Exp m) = bernoulliDesign (Exp m).p (Exp m).hp0 (Exp m).hp1
      from hDm m]
    exact hsub
  rw [hstat, hlim] at hdiff
  exact hdiff

end UnknownInterference
end Experimentation
end Causalean
