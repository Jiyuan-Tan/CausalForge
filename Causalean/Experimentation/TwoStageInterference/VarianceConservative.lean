/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008): conservative within-group variance estimator

The natural design-based estimator of the difference-in-means variance from a single realized
within-group assignment.  Among the units observed treated it forms the sample variance of their
outcomes, among the units observed in control it forms the sample variance of theirs, and it
combines them as `Ŝ₁/K + Ŝ₀/(n−K)` — the empirical analogue of the first two terms of the Neyman
variance `S₁/K + S₀/(n−K) − Sτ/n`.  Because it excludes the unestimable unit-effect term `Sτ/n`
(nonnegative), the estimator is conservative in expectation.  This file defines the estimator,
proves that it is pointwise nonnegative, and proves the conservativeness statement
`Var(τ̂) ≤ E[v̂ar]` (Hudgens–Halloran Eq. 9): in expectation `E[v̂ar] = S₁/K + S₀/(n−K)`, which
overstates the Neyman variance by exactly the nonnegative unit-effect term `Sτ/n`.

The conservativeness theorem instantiates the generic expected-sample-variance moment lemma
`E_Shat` (in `VarianceMoments`) for the treated indicators (count `K`) and the control indicators
`1 − T` (count `n − K`), so `E[Ŝ₁] = S₁` and `E[Ŝ₀] = S₀`.  Beyond the hypotheses of the variance
identity `Var_tauHat` it needs two faithful features of the completely-randomized design: a
deterministic treated count `∑ⱼ Tⱼ = K` on the design's support (`hsupp`, needed to expand the
sample variance without third moments), and the non-degeneracy bounds `2 ≤ K` and `K + 2 ≤ n`
(needed so both sample variances exist, i.e. `K−1`, `n−K−1`, `n−1` are all nonzero).
-/

import Causalean.Experimentation.TwoStageInterference.VarianceMoments

/-! # Conservative two-stage variance estimators

Within-group sample-variance estimators conservatively estimate direct-effect
randomization variance.

The definitions `obsMeanTreated`, `obsMeanControl`, `ShatTreated`, `ShatControl`, and `varHat`
describe the single-assignment sample-variance estimator.  The theorem `varHat_nonneg` proves
pointwise nonnegativity, `E_ShatTreated` and `E_ShatControl` identify the expected treated and
control sample variances with `S1` and `S0`, and `E_varHat_conservative` proves
`Var(tauHat) ≤ E[varHat]`.  `E_varHat_conservative_CRD` specializes that inequality to the
completely randomized within-group design, where the moment and support hypotheses are proved by
`crd_mean`, `crd_pair`, and `crd_supp`.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

section Group

variable {n : ℕ} (K : ℕ) (a b : Fin n → ℝ)

/-- Empirical mean of the treated-state outcomes among the units observed treated under the
realized assignment `w`: `(1/K)∑_{j: wⱼ=1} a j`, written with the treatment indicators. -/
noncomputable def obsMeanTreated (w : Fin n → Bool) : ℝ :=
  (∑ j, T j w * a j) / K

/-- Empirical mean of the untreated-state outcomes among the units observed in control under the
realized assignment `w`: `(1/(n−K))∑_{j: wⱼ=0} b j`. -/
noncomputable def obsMeanControl (w : Fin n → Bool) : ℝ :=
  (∑ j, (1 - T j w) * b j) / (n - K : ℝ)

/-- Observed sample variance among the `K` treated units, `Ŝ₁`, with `K−1` denominator:
`(1/(K−1))∑_{j: wⱼ=1}(a j − ā_obs)²`. -/
noncomputable def ShatTreated (w : Fin n → Bool) : ℝ :=
  (∑ j, T j w * (a j - obsMeanTreated K a w) ^ 2) / (K - 1 : ℝ)

/-- Observed sample variance among the `n−K` control units, `Ŝ₀`, with `n−K−1` denominator:
`(1/(n−K−1))∑_{j: wⱼ=0}(b j − b̄_obs)²`. -/
noncomputable def ShatControl (w : Fin n → Bool) : ℝ :=
  (∑ j, (1 - T j w) * (b j - obsMeanControl K b w) ^ 2) / (n - K - 1 : ℝ)

/-- **Conservative variance estimator** `v̂ar = Ŝ₁/K + Ŝ₀/(n−K)`, the empirical analogue of the
first two terms of the Neyman variance.  Computable from a single realized assignment. -/
noncomputable def varHat (w : Fin n → Bool) : ℝ :=
  ShatTreated K a w / K + ShatControl K b w / (n - K : ℝ)

/-- The treatment indicator is nonnegative. -/
lemma T_nonneg (j : Fin n) (w : Fin n → Bool) : 0 ≤ T j w :=
  FiniteDesign.ind_nonneg _ w

/-- `1 − Tⱼ` (the control indicator) is nonnegative. -/
lemma one_sub_T_nonneg (j : Fin n) (w : Fin n → Bool) : 0 ≤ 1 - T j w :=
  sub_nonneg.mpr (FiniteDesign.ind_le_one _ w)

/-- The observed treated sample variance is nonnegative, provided `1 ≤ K` (so the denominator
`K−1 ≥ 0`): it is a nonnegative-weighted sum of squares divided by a nonnegative number. -/
lemma ShatTreated_nonneg (hK : 1 ≤ K) (w : Fin n → Bool) : 0 ≤ ShatTreated K a w := by
  unfold ShatTreated
  apply div_nonneg
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (T_nonneg j w) (sq_nonneg _))
  · have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith

/-- The observed control sample variance is nonnegative, provided `K + 1 ≤ n` (so the denominator
`n−K−1 ≥ 0`). -/
lemma ShatControl_nonneg (hKn : K + 1 ≤ n) (w : Fin n → Bool) : 0 ≤ ShatControl K b w := by
  unfold ShatControl
  apply div_nonneg
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (one_sub_T_nonneg j w) (sq_nonneg _))
  · have : (K : ℝ) + 1 ≤ n := by exact_mod_cast hKn
    linarith

/-- **Pointwise nonnegativity of the conservative variance estimator.** For a group of `n` units
with potential outcomes `a` and `b`, provided [at least one unit is treated](hyp:hK) and [at least
one unit remains in control (`K + 1 ≤ n`)](hyp:hKn) — so both within-group sample-variance
denominators `K` and `n − K` are positive — then for [every realized assignment `w`](hyp:w), [the
conservative variance estimator `v̂ar` is nonnegative, being the sum of two nonnegative sample
variances each divided by a positive count](goal). -/
theorem varHat_nonneg (hK : 1 ≤ K) (hKn : K + 1 ≤ n) (w : Fin n → Bool) :
    0 ≤ varHat K a b w := by
  unfold varHat
  have hKpos : (0 : ℝ) < K := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hnKpos : (0 : ℝ) < n - K := by
    have h1 : (K : ℝ) + 1 ≤ n := by exact_mod_cast hKn
    linarith
  apply add_nonneg
  · exact div_nonneg (ShatTreated_nonneg K a hK w) hKpos.le
  · exact div_nonneg (ShatControl_nonneg K b hKn w) hnKpos.le

section Conservative

variable (ρ : FiniteDesign (Fin n → Bool))
variable (hK2 : 2 ≤ K) (hKn2 : K + 2 ≤ n)
variable (hmean : ∀ j, ρ.E (T j) = (K : ℝ) / n)
variable (hpair : ∀ j k, j ≠ k →
  ρ.E (fun w => T j w * T k w) = (K * (K - 1) : ℝ) / (n * (n - 1)))
variable (hsupp : ∀ w, ρ.p w ≠ 0 → (∑ j, T j w) = (K : ℝ))

include hK2 hKn2 in
/-- The real denominators arising in the conservative-variance moment calculation are nonzero:
`n`, `n−1`, `K`, `K−1`, `n−K`, `n−K−1`, from the non-degeneracy bounds `2 ≤ K` and `K + 2 ≤ n`. -/
private lemma denom_facts :
    (n : ℝ) ≠ 0 ∧ (n - 1 : ℝ) ≠ 0 ∧ (K : ℝ) ≠ 0 ∧ (K - 1 : ℝ) ≠ 0
      ∧ (n - K : ℝ) ≠ 0 ∧ (n - K - 1 : ℝ) ≠ 0 := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hKnr : (K : ℝ) + 2 ≤ n := by exact_mod_cast hKn2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> nlinarith

include hK2 hKn2 hmean hpair hsupp in
/-- **Expected observed treated sample variance.**  For any within-group design whose treatment
indicators satisfy the completely-randomized moment hypotheses — first moment `K/n` (`hmean`),
pairwise second moment `K(K−1)/(n(n−1))` (`hpair`), and a deterministic treated count `K` on the
support (`hsupp`) — [the expectation of the realized treated-state sample variance equals the
population treated-state sample variance `S₁`](goal): `E[Ŝ₁] = S₁`.

These moments hold for the completely randomized design of Assumption 1
(`crd_mean`/`crd_pair`/`crd_supp`).  Instantiates the generic `E_Shat` moment lemma with the
treatment-indicator family `T` and count `K`. -/
lemma E_ShatTreated : ρ.E (ShatTreated K a) = S1 a := by
  obtain ⟨hnr, hn1r, hKr, hK1r, _, _⟩ := denom_facts K hK2 hKn2
  have hidem : ∀ (j : Fin n) (w : Fin n → Bool), T j w * T j w = T j w := by
    intro j w
    have := congrFun (FiniteDesign.ind_sq (fun w => w j = true)) w
    simpa [sq, T] using this
  -- ShatTreated K a unfolds to the `E_Shat` integrand with U = T, M = K.
  have hval := E_Shat ρ (K : ℝ) a T hnr hn1r hKr hK1r hidem hmean hpair hsupp
  unfold ShatTreated obsMeanTreated
  unfold S1 popMeanV
  exact hval

include hK2 hKn2 hmean hpair hsupp in
/-- **Expected observed control sample variance.**  The control analogue: for any design
satisfying the same completely-randomized moment hypotheses, [the expectation of the realized
untreated-state sample variance among the `n−K` control units equals the population
untreated-state sample variance `S₀`](goal): `E[Ŝ₀] = S₀`.

Instantiates `E_Shat` with the control-indicator family `1 − T` and count `n − K`, deriving the
control moments (`E[1−Tⱼ] = (n−K)/n`, `E[(1−Tⱼ)(1−Tₖ)] = (n−K)(n−K−1)/(n(n−1))`, idempotence, and
the support total `n−K`) from `hmean`/`hpair`/`hsupp`. -/
lemma E_ShatControl : ρ.E (ShatControl K b) = S0 b := by
  obtain ⟨hnr, hn1r, _, _, hnKr, hnK1r⟩ := denom_facts K hK2 hKn2
  set U : Fin n → (Fin n → Bool) → ℝ := fun j w => 1 - T j w with hU
  -- idempotence of the control indicator
  have hidemT : ∀ (j : Fin n) (w : Fin n → Bool), T j w * T j w = T j w := by
    intro j w
    have := congrFun (FiniteDesign.ind_sq (fun w => w j = true)) w
    simpa [sq, T] using this
  have hidem : ∀ (j : Fin n) (w : Fin n → Bool), U j w * U j w = U j w := by
    intro j w; simp only [hU]
    rw [show (1 - T j w) * (1 - T j w) = 1 - 2 * T j w + T j w * T j w from by ring,
      hidemT j w]; ring
  -- first moment: E[1 − Tⱼ] = (n−K)/n
  have hmeanU : ∀ j, ρ.E (U j) = ((n - K : ℝ)) / n := by
    intro j
    have : U j = (fun w => 1 - T j w) := rfl
    rw [this]
    rw [show (fun w => (1 : ℝ) - T j w) = (fun w => (1 : ℝ) - T j w) from rfl]
    rw [FiniteDesign.E_sub, FiniteDesign.E_const, hmean j]
    field_simp
  -- pairwise second moment: E[(1−Tⱼ)(1−Tₖ)] = (n−K)(n−K−1)/(n(n−1))
  have hpairU : ∀ j k, j ≠ k →
      ρ.E (fun w => U j w * U k w)
        = ((n - K : ℝ) * ((n - K : ℝ) - 1)) / (n * (n - 1)) := by
    intro j k hjk
    have hexp : (fun w => U j w * U k w)
        = (fun w => 1 - T j w - T k w + T j w * T k w) := by
      funext w; simp only [hU]; ring
    rw [hexp]
    rw [show (fun w => 1 - T j w - T k w + T j w * T k w)
          = (fun w => (1 - T j w - T k w) + (T j w * T k w)) from by funext w; ring]
    rw [FiniteDesign.E_add]
    rw [show (fun w => 1 - T j w - T k w) = (fun w => (1 - T j w) - T k w) from by funext w; ring]
    rw [FiniteDesign.E_sub,
      show (fun w => (1 : ℝ) - T j w) = (fun w => (1 : ℝ) - T j w) from rfl,
      FiniteDesign.E_sub, FiniteDesign.E_const, hmean j, hmean k, hpair j k hjk]
    field_simp
    ring
  -- support total: ∑ⱼ (1 − Tⱼ) = n − K on the support
  have hsuppU : ∀ w, ρ.p w ≠ 0 → (∑ j, U j w) = ((n - K : ℝ)) := by
    intro w hw
    simp only [hU]
    rw [Finset.sum_sub_distrib]
    rw [hsupp w hw]
    simp [Finset.card_univ]
  have hval := E_Shat ρ ((n : ℝ) - K) b U hnr hn1r hnKr hnK1r hidem hmeanU hpairU hsuppU
  -- bridge: M − 1 = (n−K) − 1, M = n−K
  unfold ShatControl obsMeanControl
  unfold S0 popMeanV
  simpa only [hU, sub_sub] using hval

include hK2 hKn2 hmean hpair hsupp in
/-- **Conservativeness of the within-group variance estimator (Hudgens–Halloran 2008, Eq. 9).**
For any design satisfying the completely-randomized moment hypotheses (`hmean`/`hpair`/`hsupp`) and
treating exactly `K` of `n` units (with `2 ≤ K` and `K + 2 ≤ n`, so both sample variances are well
defined), [the conservative estimator overstates the randomization variance,
`Var(τ̂) ≤ E[v̂ar]`](goal).

In expectation `E[v̂ar] = S₁/K + S₀/(n−K)`, which exceeds the Neyman variance
`S₁/K + S₀/(n−K) − Sτ/n` by exactly the nonnegative unit-effect term `Sτ/n`.  The added hypotheses
over `Var_tauHat` are the deterministic treated-count on the support (`hsupp`) and non-degeneracy
(`hK2`, `hKn2`).  (`E_varHat_conservative_CRD` specializes this to the completely randomized
design.) -/
theorem E_varHat_conservative : ρ.Var (tauHat K a b) ≤ ρ.E (varHat K a b) := by
  obtain ⟨hnr, hn1r, _, _, hnKr, _⟩ := denom_facts K hK2 hKn2
  have hK : 0 < K := by omega
  have hKn : K < n := by omega
  -- E[v̂ar] = S₁/K + S₀/(n−K)
  have hEvar : ρ.E (varHat K a b) = S1 a / K + S0 b / (n - K) := by
    unfold varHat
    rw [show (fun w => ShatTreated K a w / K + ShatControl K b w / (n - K : ℝ))
          = (fun w => ShatTreated K a w / K + ShatControl K b w / (n - K : ℝ)) from rfl,
      FiniteDesign.E_add]
    rw [show (fun w => ShatTreated K a w / (K : ℝ)) = (fun w => (K : ℝ)⁻¹ * ShatTreated K a w)
        from by funext w; rw [div_eq_mul_inv]; ring,
      show (fun w => ShatControl K b w / (n - K : ℝ)) = (fun w => (n - K : ℝ)⁻¹ * ShatControl K b w)
        from by funext w; rw [div_eq_mul_inv]; ring]
    rw [FiniteDesign.E_const_mul, FiniteDesign.E_const_mul,
      E_ShatTreated K a ρ hK2 hKn2 hmean hpair hsupp,
      E_ShatControl K b ρ hK2 hKn2 hmean hpair hsupp]
    rw [div_eq_mul_inv (S1 a), div_eq_mul_inv (S0 b)]; ring
  rw [hEvar, Var_tauHat K a b ρ hK hKn hmean hpair]
  -- Stau a b / n ≥ 0 (sum of squares over n−1 > 0, divided by n > 0)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
  have hStau_nonneg : 0 ≤ Stau a b / n := by
    apply div_nonneg
    · unfold Stau
      apply div_nonneg
      · exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
      · linarith
    · linarith
  linarith

end Conservative

/-- **Conservativeness of the within-group variance estimator, for the completely randomized
design (Hudgens–Halloran 2008, Eq. 9).** For a group of `n` units with potential outcomes `a`
(treated state) and `b` (untreated state), consider the completely randomized within-group design
that treats exactly `K` units uniformly at random, where [at least two units are
treated](hyp:hK2) and [at least two units remain in control (`K + 2 ≤ n`)](hyp:hKn2) — so both
within-group sample variances are well defined. Then [the randomization variance of the
control-minus-treatment difference-in-means estimator under this design is at most the
expectation, under the same design, of the conservative variance estimator `v̂ar`](goal).

Its first- and second-order treatment moments and deterministic treated count are the derived
facts `crd_mean`/`crd_pair`/`crd_supp`, so — unlike `E_varHat_conservative` — no moment hypotheses
are assumed; this is Eq. 9 as Hudgens & Halloran state it under their mixed-strategy Assumption
1. -/
theorem E_varHat_conservative_CRD (hK2 : 2 ≤ K) (hKn2 : K + 2 ≤ n) :
    (crd K (le_trans (Nat.le_add_right K 2) hKn2)).Var (tauHat K a b)
      ≤ (crd K (le_trans (Nat.le_add_right K 2) hKn2)).E (varHat K a b) :=
  E_varHat_conservative K a b (crd K (le_trans (Nat.le_add_right K 2) hKn2)) hK2 hKn2
    (fun j => crd_mean K _ j)
    (fun j k hjk => crd_pair K _ j k hjk)
    (fun w hw => crd_supp K _ w hw)

end Group

end TwoStageInterference
end Experimentation
end Causalean
