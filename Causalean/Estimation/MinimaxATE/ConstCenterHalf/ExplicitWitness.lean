/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: assembling the explicit two-point witness

This file assembles the explicit Case-1 construction (`Construction.lean`,
`Membership.lean`, `Gap.lean`) into a `TwoPointWitness` and the resulting minimax
lower bound, with the two i.i.d. data laws

* `Qfalse = P̂^⊗n` — the `n`-sample law of the null estimate `(m̂, ĝ) = (1/2, 1/2)`;
* `Qtrue  = (1/2^K) Σ_λ Qλ^⊗n` — the **uniform mixture** over Rademacher signs
  `λ : Fin K → Bool` of the perturbed laws (`mixture` from `Stat/Minimax`).

The `dominated` (realizability) obligation is discharged by `mixtureReal_le`: every
perturbed DGP lies in the class (`inClass_perturbed`) and shares the **same** ATE
`θ_true = 2β(α+β)/(1−4β²)` (`ate_gPerturbed`, independent of `λ`), so an average of
in-class miss probabilities is at most their supremum `minimaxMiss`; the null law is
itself in-class with ATE `0`.

The only remaining input is the **statistical indistinguishability** of the two
laws, `tvDist Qfalse Qtrue ≤ 1/2` (the Ingster χ² / Hellinger second-moment bound of
the paper, valid in the regime `n · εg · εm ≲ 1`).  Here it is carried as an explicit
hypothesis `htv`; the sibling χ²-core file discharges it.  Given it,
`explicit_minimax_lower_bound` concludes that **no** estimator can be within
`s = β(α+β)/(1−4β²) ≍ √(εg·εm)` of the true ATE with probability `> 3/4` uniformly
over the class — the doubly-robust product rate is unbeatable.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Membership
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Gap
import Causalean.Estimation.MinimaxATE.Reduction.Witness
import Causalean.Stat.Minimax.Mixture

/-! # Explicit Two-Point Witness

This file builds the baseline finite two-point witness for the structure-agnostic ATE lower
bound. It defines the centered null law `Qfalse`, the uniform sign weights `signWeight`, the
sign-indexed perturbed laws `Qpert`, and the mixed alternative `Qtrue`, together with their
probability-measure lemmas.

The helper `real_le_minimaxMiss` relates any in-class DGP's miss probability to the minimax
miss functional. The construction `explicitWitness` packages the null and mixed alternative
into a `TwoPointWitness` under a supplied total-variation bound, and
`explicit_minimax_lower_bound` turns that witness into the conditional finite-cell minimax lower
bound used by the chi-squared core. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

variable {K n : ℕ} {α β εg εm : ℝ}

/-- The centered null nuisance functions are in the nuisance class whenever the budgets are
nonnegative. -/
theorem inClass_null (hεg : 0 ≤ εg) (hεm : 0 ≤ εm) :
    InClass (C := Fin K × Bool) mhat ghat εg εm mhat ghat where
  valid := validDGP_hat
  err_g d := by rw [l2sq_self]; exact hεg
  err_m := by rw [l2sq_self]; exact hεm

/-- The `n`-sample law of the centered null data-generating process. -/
noncomputable def Qfalse (K n : ℕ) [NeZero K] : Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (validDGP_hat (K := K)) n

/-- Equal mixture weight on every Rademacher sign vector. -/
noncomputable def signWeight (K : ℕ) : (Fin K → Bool) → ℝ≥0∞ :=
  fun _ => (Fintype.card (Fin K → Bool) : ℝ≥0∞)⁻¹

/-- The `n`-sample law for one perturbed data-generating process indexed by a sign vector. -/
noncomputable def Qpert [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (n : ℕ) (lam : Fin K → Bool) : Measure (Fin n → Obs (Fin K × Bool)) :=
  productLaw (validDGP_perturbed hα hβ hαβ lam) n

/-- Alternative `n`-sample law formed by uniformly mixing over all perturbation signs. -/
noncomputable def Qtrue [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2) (n : ℕ) :
    Measure (Fin n → Obs (Fin K × Bool)) :=
  mixture (signWeight K) (fun lam => Qpert hα hβ hαβ n lam)

/-- The uniform weights over sign vectors have total mass one. -/
theorem signWeight_sum (K : ℕ) : ∑ lam : Fin K → Bool, signWeight K lam = 1 := by
  have hpos : (Fintype.card (Fin K → Bool)) ≠ 0 := Fintype.card_ne_zero
  simp only [signWeight]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by exact_mod_cast hpos) (ENNReal.natCast_ne_top _)]

/-- The centered null n-sample law is a probability measure. -/
theorem Qfalse_isProb (K n : ℕ) [NeZero K] : IsProbabilityMeasure (Qfalse K n) := by
  unfold Qfalse; infer_instance

/-- Each perturbed n-sample law is a probability measure in the valid parameter regime. -/
theorem Qpert_isProb [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (n : ℕ) (lam : Fin K → Bool) : IsProbabilityMeasure (Qpert hα hβ hαβ n lam) := by
  unfold Qpert; infer_instance

/-- The uniformly mixed alternative n-sample law is a probability measure in the valid parameter
regime. -/
theorem Qtrue_isProb [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + 2 * β ≤ 1 / 2) (n : ℕ) :
    IsProbabilityMeasure (Qtrue (K := K) hα hβ hαβ n) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert hα hβ hαβ n lam) :=
    fun lam => Qpert_isProb hα hβ hαβ n lam
  unfold Qtrue
  exact mixture_isProbabilityMeasure _ (signWeight_sum K) _

/-- The miss probability of any in-class data-generating process is bounded by the minimax miss
probability.

This real-valued form keeps the nuisance functions explicit so the ATE center can be rewritten. -/
theorem real_le_minimaxMiss [NeZero K] {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
    (hin : InClass mhat ghat εg εm m g) (est : (Fin n → Obs (Fin K × Bool)) → ℝ) (s : ℝ) :
    (productLaw hin.valid n).real {x | s ≤ |est x - ate g|}
      ≤ minimaxMiss mhat ghat εg εm n est s := by
  simpa [nMiss] using
    nMiss_le_minimaxMiss (⟨(m, g), hin⟩ : InClassDGP mhat ghat εg εm) (est := est) (s := s)

/-- Assemble the explicit Le Cam witness from the centered null and the uniform perturbation
mixture.

The witness uses the supplied total-variation indistinguishability bound, the null ATE,
and the common perturbed ATE shared by all sign vectors. -/
noncomputable def explicitWitness [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hm : β ^ 2 ≤ εm) (hg : (α + β) ^ 2 / (1 - 2 * β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (htv : tvDist (Qfalse K n) (Qtrue hα hβ hαβ n) ≤ 1 / 2) :
    TwoPointWitness (Fin K × Bool) n mhat ghat εg εm where
  s := β * (α + β) / (1 - 4 * β ^ 2)
  c := 1 / 2
  Q := fun j => cond j (Qtrue hα hβ hαβ n) (Qfalse K n)
  prob := by
    intro j; cases j
    · exact Qfalse_isProb K n
    · exact Qtrue_isProb hα hβ hαβ n
  θ := fun j => cond j (2 * β * (α + β) / (1 - 4 * β ^ 2)) 0
  sep := by
    have hβ4 : β ≤ 1 / 4 := by linarith
    have hden : (0:ℝ) < 1 - 4 * β ^ 2 := by nlinarith
    have hnum : (0:ℝ) ≤ 2 * β * (α + β) := by
      have : (0:ℝ) ≤ α + β := by linarith
      positivity
    change 2 * (β * (α + β) / (1 - 4 * β ^ 2))
        ≤ |2 * β * (α + β) / (1 - 4 * β ^ 2) - 0|
    rw [sub_zero, abs_of_nonneg (div_nonneg hnum hden.le)]
    apply le_of_eq; ring
  tvBound := by simpa using htv
  dominated := by
    intro est j
    cases j
    · -- `Q false = Qfalse`, `θ false = 0 = ate ĝ`
      have hb := real_le_minimaxMiss (n := n) (inClass_null hεg hεm) est
        (β * (α + β) / (1 - 4 * β ^ 2))
      rw [ate_ghat] at hb
      exact hb
    · -- `Q true = Qtrue` is the mixture; bound each part then `mixtureReal_le`
      haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert hα hβ hαβ n lam) :=
        fun lam => Qpert_isProb hα hβ hαβ n lam
      change (Qtrue hα hβ hαβ n).real
          {x | β * (α + β) / (1 - 4 * β ^ 2) ≤ |est x - 2 * β * (α + β) / (1 - 4 * β ^ 2)|}
          ≤ minimaxMiss mhat ghat εg εm n est (β * (α + β) / (1 - 4 * β ^ 2))
      unfold Qtrue
      refine mixtureReal_le (signWeight K) (signWeight_sum K)
        (fun lam => Qpert hα hβ hαβ n lam) _ _ ?_
      intro lam
      have hb := real_le_minimaxMiss (n := n) (inClass_perturbed hα hβ hαβ hm hg lam) est
        (β * (α + β) / (1 - 4 * β ^ 2))
      rw [ate_gPerturbed hα hβ hαβ lam] at hb
      exact hb

/-- Every measurable estimator misses the true ATE by the explicit product-rate scale somewhere
in the class.

This conditional lower bound assumes the centered budgets, the Rademacher perturbation budgets,
and the total-variation indistinguishability of the null and mixed alternative laws. -/
theorem explicit_minimax_lower_bound [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hm : β ^ 2 ≤ εm) (hg : (α + β) ^ 2 / (1 - 2 * β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (htv : tvDist (Qfalse K n) (Qtrue hα hβ hαβ n) ≤ 1 / 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMiss mhat ghat εg εm n est (β * (α + β) / (1 - 4 * β ^ 2)) :=
  twoPointWitness_quarter (explicitWitness hα hβ hαβ hm hg hεg hεm htv) (le_refl _) hest

end Causalean.Estimation.MinimaxATE
