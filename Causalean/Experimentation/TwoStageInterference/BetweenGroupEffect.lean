/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008), Theorem 6: two-stage variance of the direct-effect contrast

Theorem 6: the two-stage randomization variance of the treatment-minus-control direct-effect
contrast estimator decomposes into a between-group simple-random-sampling term over the group-level
treatment-minus-control contrasts plus a within-group term averaging the per-group contrast
estimator variances.

The key observation is that `Ŷ(1;ψ) − Ŷ(0;ψ) = (∑ᵢ 1(Sᵢ=ψ)·dᵢ(wᵢ))/C`, where
`dᵢ(w) = Ŷ_i(1)(w) − Ŷ_i(0)(w)` is the per-group contrast estimator.  So the contrast
variance is the abstract two-stage decomposition `Var_groupAgg` instantiated with the per-group
statistic `g i = dᵢ`.  The between-term conditional mean `(ψ i).E (dᵢ)` collapses to
`ȳ_i(1;ψ) − ȳ_i(0;ψ)` by `E_groupEst` (twice, via linearity of expectation), giving the
finite-population-corrected SRS variance `(1 − C/N)/C · Sμ²(ȳ_·(1;ψ) − ȳ_·(0;ψ))`; the within-term
`(1/(C·N)) · ∑ᵢ (ψ i).Var (dᵢ)` is already in the target shape.
-/

import Causalean.Experimentation.TwoStageInterference.BetweenGroup
import Causalean.Experimentation.TwoStageInterference.Effects

/-! # Direct-contrast variance under two-stage interference

The treatment-minus-control direct-effect contrast estimator has a two-stage between/within
variance decomposition.

The theorem `Var_estDirect` instantiates `Var_groupAgg` with the per-group
treatment-minus-control statistic, yielding Hudgens-Halloran Theorem 6 under explicit stage-one
and within-group moment hypotheses.  `Var_estDirect_CRD` specializes the same identity to the
completely randomized mixed two-stage design, where `crdOn_mean`, `crdOn_pair`, and the
within-group `crd_prop_*` facts discharge those hypotheses.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

set_option linter.unusedDecidableInType false in
/-- **Hudgens–Halloran (2008), Theorem 6 (two-stage variance of the direct-effect contrast
estimator).** Consider the two-stage design that first allocates each group to
[strategy ψ or strategy φ](hyp:ψ,φ) and then randomizes the group's units accordingly, with
outcomes recorded by [the potential-outcome function Y](hyp:Y). Assume [the target sample size C
of selected groups is nonzero](hyp:hC), [the number N of groups is nonzero](hyp:hN), [N minus one
is nonzero](hyp:hN1), [every group's control-arm unit count m0 is nonzero](hyp:hm0), [every
group's treatment-arm unit count m1 is nonzero](hyp:hm1), and [every group's size n is
nonzero](hyp:hn). Suppose the stage-1 design draws a simple random sample of C of the N groups, so
that [each group is selected with probability C/N](hyp:hstage1) and [each pair of distinct groups
is jointly selected with probability C(C−1)/(N(N−1))](hyp:hstage1pair), and that within a selected
ψ-group [each unit's control propensity is m0/n](hyp:hprop0) and [each unit's treatment propensity
is m1/n](hyp:hprop1). Then [the randomization variance of the treatment-minus-control estimator
decomposes into a between-group term — the finite-population-corrected sample variance of the
group-level treatment-minus-control contrasts, scaled by (1 − C/N)/C — plus a within-group term
averaging, over the N groups and scaled by 1/(C·N), the conditional variance of each group's
within-group contrast estimator](goal).

`Var_estDirect_CRD` specializes this identity to the actual mixed (completely randomized) design
of Assumption 1, discharging all the moment hypotheses above as proven facts. -/
theorem Var_estDirect (D₁ : FiniteDesign (StratAssign ι)) (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (m0 m1 : ι → ℝ) (C : ℝ)
    (hC : C ≠ 0) (hN : (Fintype.card ι : ℝ) ≠ 0) (hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0)
    (hm0 : ∀ i, m0 i ≠ 0) (hm1 : ∀ i, m1 i ≠ 0) (hn : ∀ i, (n i : ℝ) ≠ 0)
    (hprop0 : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = false) = m0 i / (n i))
    (hprop1 : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = true) = m1 i / (n i))
    (hstage1 : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ))
    (hstage1pair : ∀ i j, i ≠ j → D₁.E (fun s => FiniteDesign.ind (fun s => s i = true) s
                      * FiniteDesign.ind (fun s => s j = true) s)
        = (C * (C - 1)) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))) :
    (jointDesign D₁ ψ φ).Var (estDirect Y m0 m1 C)
      = (1 - C / (Fintype.card ι : ℝ)) / C
          * SmuVar (fun i => groupMean ψ Y i true - groupMean ψ Y i false)
        + (1 / (C * (Fintype.card ι : ℝ)))
          * ∑ i, (ψ i).Var (fun w => groupEst Y i true (m1 i) w - groupEst Y i false (m0 i) w) := by
  -- (a) The contrast estimator is the aggregate of the per-group contrast statistic.
  have hagg : (estDirect Y m0 m1 C)
      = (fun sw => (∑ i, if sw.1 i = true then
            (fun w => groupEst Y i true (m1 i) w - groupEst Y i false (m0 i) w) (sw.2 i)
          else 0) / C) := by
    funext sw
    unfold estDirect popEst
    rw [← sub_div]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : sw.1 i = true
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, sub_zero]
  -- (b) Apply the abstract two-stage decomposition with `g i = dᵢ`.
  rw [hagg, Var_groupAgg D₁ ψ φ
      (fun i w => groupEst Y i true (m1 i) w - groupEst Y i false (m0 i) w) C
      hC hN hN1 hstage1 hstage1pair]
  -- (c) Collapse the between-term conditional means to the group-level contrasts.
  have hmean : (fun i => (ψ i).E
        (fun w => groupEst Y i true (m1 i) w - groupEst Y i false (m0 i) w))
      = (fun i => groupMean ψ Y i true - groupMean ψ Y i false) := by
    funext i
    rw [FiniteDesign.E_sub (ψ i) (groupEst Y i true (m1 i)) (groupEst Y i false (m0 i))]
    rw [E_groupEst ψ Y i true (m1 i) (hm1 i) (hn i) (hprop1 i)]
    rw [E_groupEst ψ Y i false (m0 i) (hm0 i) (hn i) (hprop0 i)]
  rw [hmean]

set_option linter.unusedDecidableInType false in
/-- **Hudgens–Halloran (2008), Theorem 6, for the mixed two-stage design.** Consider the
completely randomized two-stage design in which stage 1 draws a simple random sample of C groups
out of the population of N groups, and each drawn group is completely randomized by treating K of
its n units, with outcomes recorded by [the potential-outcome function Y](hyp:Y). Assume [the
sample size C is strictly positive](hyp:hC0), [C is strictly less than the number N of
groups](hyp:hCN), [every group's treated-unit count K is strictly positive](hyp:hK0), and [every
group's treated count K is strictly less than its size n](hyp:hKn). Then [the randomization
variance of the treatment-minus-control estimator on this design equals the same
between-group/within-group decomposition as `Var_estDirect`, with control count n−K and treatment
count K in each group](goal).

This specializes `Var_estDirect`, discharging its stage-1 and within-group moment hypotheses via
the derived facts `crdOn_mean`, `crdOn_pair`, and `crd_prop_true`/`crd_prop_false`, so only the
mixed-strategy validity conditions above are assumed. The estimator uses the Hudgens-Halloran
treatment-minus-control orientation. -/
theorem Var_estDirect_CRD (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (K : ι → ℕ) (C : ℕ)
    (hC0 : 0 < C) (hCN : C < Fintype.card ι)
    (hK0 : ∀ i, 0 < K i) (hKn : ∀ i, K i < n i) :
    (jointDesign (crdOn C hCN.le) (fun i => crd (K i) (hKn i).le)
        (fun i => crd (K i) (hKn i).le)).Var
        (estDirect Y (fun i => (n i : ℝ) - K i) (fun i => (K i : ℝ)) (C : ℝ))
      = (1 - (C : ℝ) / (Fintype.card ι : ℝ)) / C
          * SmuVar (fun i => groupMean (fun i => crd (K i) (hKn i).le) Y i true
              - groupMean (fun i => crd (K i) (hKn i).le) Y i false)
        + (1 / ((C : ℝ) * (Fintype.card ι : ℝ)))
          * ∑ i, (crd (K i) (hKn i).le).Var
              (fun w => groupEst Y i true (K i : ℝ) w
                - groupEst Y i false ((n i : ℝ) - K i) w) := by
  have hCN' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le C) hCN
  have hNr : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hCN'
  have hN1r : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have h2 : 2 ≤ Fintype.card ι := by omega
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h2
    linarith
  have hCr : (C : ℝ) ≠ 0 := by exact_mod_cast hC0.ne'
  have hnr : ∀ i, (n i : ℝ) ≠ 0 := fun i => by
    have h := hKn i; have : 0 < n i := by omega
    exact_mod_cast this.ne'
  have hm0 : ∀ i, ((n i : ℝ) - K i) ≠ 0 := fun i =>
    sub_ne_zero.mpr (ne_of_gt (show (K i : ℝ) < n i by exact_mod_cast hKn i))
  have hm1 : ∀ i, (K i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hK0 i).ne'
  have hprop0 : ∀ i (j : Fin (n i)),
      (crd (K i) (hKn i).le).Pr (fun w => w j = false) = ((n i : ℝ) - K i) / n i :=
    fun i j => crd_prop_false (K i) (hKn i).le j
  have hprop1 : ∀ i (j : Fin (n i)),
      (crd (K i) (hKn i).le).Pr (fun w => w j = true) = (K i : ℝ) / n i :=
    fun i j => crd_prop_true (K i) (hKn i).le j
  exact Var_estDirect (crdOn C hCN.le) (fun i => crd (K i) (hKn i).le)
    (fun i => crd (K i) (hKn i).le) Y (fun i => (n i : ℝ) - K i) (fun i => (K i : ℝ)) (C : ℝ)
    hCr hNr hN1r hm0 hm1 hnr hprop0 hprop1
    (fun i => crdOn_mean C hCN.le i)
    (fun i j hij => crdOn_pair C hCN.le i j hij)

end TwoStageInterference
end Experimentation
end Causalean
