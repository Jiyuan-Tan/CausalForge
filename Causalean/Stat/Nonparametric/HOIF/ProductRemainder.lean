/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Order-`m` HOIF estimation bias: the product remainder

The order-`m` higher-order influence function (HOIF) estimator removes the leading
nuisance-estimation bias up to a remainder that is a *finite sum of products of `m+1`
nuisance `L²`-errors*.  Writing `δ` for the largest of those errors, every term of the
remainder is a product of `m+1` factors each `≤ δ`, so the whole remainder is bounded by
`|T|·δ^{m+1}` (with `|T|` the fixed number of terms), and its squared contribution by

  `R² ≤ |T|²·δ^{2(m+1)}`.

This is the order-`m` analogue of the second-order doubly-robust remainder
`(product of two nuisance errors)`: pushing to order `m` buys the higher power `δ^{m+1}`.
Choosing the order `m` so that `2(m+1)λ_* >` the target risk exponent makes this squared
contribution `o(ρ_n)` — the rate-selection lemma `hoif_order_choice_negligible`.

This file is purely elementary (finite products of bounded reals + a power-law limit);
it carries no measure theory and is the leaf of the HOIF substrate.
-/

namespace Causalean.Stat.Nonparametric.HOIF

open scoped BigOperators
open Filter Topology

/-- **A product of `m+1` factors each in `[0, δ]` is at most `δ^{m+1}`.**
Each nuisance-error factor of a single HOIF remainder term is nonnegative and bounded by
the largest error `δ`; multiplying `m+1` of them keeps the product below `δ^{m+1}`. -/
theorem prod_le_pow_of_factors_le {ι : Type*} (e : ι → ℝ) (m : ℕ) (δ : ℝ)
    (s : Finset ℕ) (idx : ℕ → ι)
    (hcard : s.card = m + 1)
    (hnn : ∀ k ∈ s, 0 ≤ e (idx k)) (hle : ∀ k ∈ s, e (idx k) ≤ δ) :
    ∏ k ∈ s, e (idx k) ≤ δ ^ (m + 1) := by
  calc ∏ k ∈ s, e (idx k) ≤ ∏ _k ∈ s, δ :=
        Finset.prod_le_prod (fun k hk => hnn k hk) (fun k hk => hle k hk)
    _ = δ ^ (m + 1) := by rw [Finset.prod_const, hcard]

/-- **Squared HOIF product-remainder bound.**
The order-`m` HOIF estimation-bias remainder `R` is dominated by a sum, over a finite index
set `T` of terms, of products of `m+1` nuisance-error factors `e t k`; every factor lies in
`[0, δ]`, where `δ` is the largest nuisance `L²`-error.  Then the remainder's squared
contribution obeys `R² ≤ |T|²·δ^{2(m+1)}`.  This is the order-`m` doubly-robust bound: the
higher the order, the higher the power of `δ`. -/
theorem hoif_remainder_sq_le {ι : Type*} (T : Finset ι) (e : ι → ℕ → ℝ)
    (m : ℕ) (δ : ℝ) (R : ℝ)
    (hnn : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), 0 ≤ e t k)
    (hle : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), e t k ≤ δ)
    (hbound : |R| ≤ ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k) :
    R ^ 2 ≤ (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) := by
  -- Each term ≤ δ^{m+1}.
  have hterm : ∀ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k ≤ δ ^ (m + 1) := by
    intro t ht
    calc ∏ k ∈ Finset.range (m + 1), e t k ≤ ∏ _k ∈ Finset.range (m + 1), δ :=
          Finset.prod_le_prod (fun k hk => hnn t ht k hk) (fun k hk => hle t ht k hk)
      _ = δ ^ (m + 1) := by rw [Finset.prod_const, Finset.card_range]
  -- Sum ≤ |T|·δ^{m+1}.
  have hsum_le : ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k
      ≤ (T.card : ℝ) * δ ^ (m + 1) := by
    calc ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k
          ≤ ∑ _t ∈ T, δ ^ (m + 1) := Finset.sum_le_sum hterm
      _ = (T.card : ℝ) * δ ^ (m + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- The sum is nonnegative (sum of products of nonnegatives).
  have hsum_nn : 0 ≤ ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k :=
    Finset.sum_nonneg (fun t ht =>
      Finset.prod_nonneg (fun k hk => hnn t ht k hk))
  -- Square the chain |R| ≤ sum ≤ |T|·δ^{m+1}.
  have hRabs : |R| ≤ (T.card : ℝ) * δ ^ (m + 1) := le_trans hbound hsum_le
  have hR2 : R ^ 2 ≤ ((T.card : ℝ) * δ ^ (m + 1)) ^ 2 := by
    rw [← sq_abs R]
    exact pow_le_pow_left₀ (abs_nonneg R) hRabs 2
  calc R ^ 2 ≤ ((T.card : ℝ) * δ ^ (m + 1)) ^ 2 := hR2
    _ = (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (m + 1) 2]

/-- **Rate selection: a high-enough HOIF order makes the squared remainder `o(ρ_n)`.**
If the squared product-remainder bound has the power-law form `K·n^{-a}` with
`a = 2(m+1)λ_*` and the target risk rate is `ρ_n = n^{-κ}`, then whenever the chosen order
makes `a > κ` the ratio `(K·n^{-a}) / n^{-κ} = K·n^{κ-a}` tends to `0`: the HOIF estimation
bias is asymptotically negligible relative to the target rate. -/
theorem hoif_order_choice_negligible {K a κ : ℝ} (haκ : κ < a) :
    Tendsto (fun n : ℕ => K * (n : ℝ) ^ (κ - a)) atTop (𝓝 0) := by
  have hpos : 0 < a - κ := by linarith
  have hbase : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun x : ℝ => x ^ (-(a - κ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hpos
  have hcomp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(a - κ))) atTop (𝓝 0) :=
    hpow.comp hbase
  have := hcomp.const_mul K
  simpa [neg_sub] using this

end Causalean.Stat.Nonparametric.HOIF
