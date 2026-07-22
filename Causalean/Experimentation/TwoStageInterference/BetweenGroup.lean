/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008), Theorem 4: two-stage variance decomposition of `Ŷ(z;ψ)`

The randomization variance of the population mean estimator under two-stage sampling splits into
a between-group simple-random-sampling term with finite-population correction `(1−C/N)/C` and a
within-group term averaging the per-group conditional variances — Hudgens–Halloran Theorem 4.

Concretely, the joint two-stage design `jointDesign D₁ ψ φ` selects which of the `N := card ι`
groups receive allocation strategy ψ (a simple random sample of `C` groups), then randomizes each
selected group by its within-group design `ψ i`.  Writing the population estimator `Ŷ(z;ψ)` as the
sample mean of the per-group estimators over the selected groups and applying the design-based law
of total variance (`Var_compound_eq_tower`), the variance decomposes as
`(1 − C/N)/C · Sμ²(ȳ·(z;ψ)) + (1/(C·N)) · ∑ᵢ Var_{ψ i}(Ŷ_i(z))`: the between-group term is the
finite-population-corrected SRS variance of the group-level potential outcomes `ȳ_i(z;ψ)`
(`Var_srs_mean`), and the within-group term is the average over groups of the per-group
conditional variances of the within-group estimator.  The first- and second-order stage-1
selection moments and the within-group `z`-propensity `m i / n i` are taken as hypotheses.

The core is the design-agnostic `Var_groupAgg`: for an arbitrary per-group within-group statistic
`g i`, the two-stage variance of `(∑ᵢ 1(Sᵢ=ψ)·g i(wᵢ))/C` decomposes into the same between/within
shape, with the between term over the conditional means `(ψ i).E (g i)` and the within term over
the conditional variances `(ψ i).Var (g i)`.  `Var_popEst` is the special case `g i = Ŷ_i(z)`.
-/

import Causalean.Experimentation.TwoStageInterference.StageOne
import Causalean.Experimentation.TwoStageInterference.Unbiased
import Causalean.Experimentation.TwoStageInterference.CompleteRandomization
import Causalean.Experimentation.DesignBased.CompoundVariance
import Causalean.Experimentation.DesignBased.ProductVariance

/-! # Two-stage between-group variance

Two-stage population-mean variance decomposes into between-group and within-group terms.

The abstract theorem `Var_groupAgg` proves the decomposition for any per-group statistic: an SRS
between-group term over conditional means plus an averaged within-group conditional-variance term.
`Var_popEst` instantiates it for the population estimator `popEst`, and `Var_popEst_CRD`
specializes the result to the completely randomized mixed two-stage design, using the CRD
inclusion and propensity lemmas rather than leaving those moments as assumptions.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/-- The stage-1 selection indicator of group `i`: `1` if group `i` is flagged ψ (`s i = true`),
else `0`. -/
private noncomputable def Usel (i : ι) : StratAssign ι → ℝ :=
  FiniteDesign.ind (fun s : StratAssign ι => s i = true)

/-- Key pointwise rewrite: for a fixed stage-1 assignment `s`, the aggregate estimator on the
ψ-groups built from the per-group statistic `g`, as a function of the within-group assignment `w`,
is the `Usel`-weighted linear combination `∑ i, (Usel i s / C) · g i (w i)`. -/
private lemma agg_as_linear_comb (g : ∀ i, WAssign n i → ℝ) (C : ℝ)
    (s : StratAssign ι) (w : ∀ i, WAssign n i) :
    (∑ i, if s i = true then g i (w i) else 0) / C
      = ∑ i, (Usel i s / C) * g i (w i) := by
  unfold Usel FiniteDesign.ind
  simp only
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : s i = true <;> simp [h, div_eq_inv_mul]

section

variable (D₁ : FiniteDesign (StratAssign ι)) (ψ φ : ∀ i, FiniteDesign (WAssign n i))
variable (g : ∀ i, WAssign n i → ℝ) (C : ℝ)

/-- WITHIN term (abstract). The expected stage-2 conditional variance of the aggregate equals
`(1/(C·N))` times the average of the per-group conditional variances `(ψ i).Var (g i)`. -/
private lemma within_term_agg (hC : C ≠ 0) (hN : (Fintype.card ι : ℝ) ≠ 0)
    (hstage1 : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ)) :
    D₁.E (fun s => (prodDesign (fun i => if s i then ψ i else φ i)).Var
        (fun w => (∑ i, if s i = true then g i (w i) else 0) / C))
      = (1 / (C * (Fintype.card ι : ℝ)))
        * ∑ i, (ψ i).Var (g i) := by
  have hinner : ∀ s : StratAssign ι,
      (prodDesign (fun i => if s i then ψ i else φ i)).Var
          (fun w => (∑ i, if s i = true then g i (w i) else 0) / C)
        = ∑ i, (Usel i s / C ^ 2) * (ψ i).Var (g i) := by
    intro s
    rw [(prodDesign (fun i => if s i then ψ i else φ i)).Var_congr
        (agg_as_linear_comb g C s)]
    rw [FiniteDesign.Var_prod_linear_comb (fun i => if s i then ψ i else φ i)
        (fun i => Usel i s / C) g]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `(Usel i s / C)^2 · (D₂ s i).Var(g i) = (Usel i s / C^2) · (ψ i).Var(g i)` pointwise in `s`.
    unfold Usel FiniteDesign.ind
    by_cases h : s i = true
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [D₁.E_congr hinner]
  rw [show (fun s : StratAssign ι => ∑ i, (Usel i s / C ^ 2) * (ψ i).Var (g i))
        = (fun s => ∑ i, (fun i => (1 / C ^ 2) * (ψ i).Var (g i) * Usel i s) i)
        from funext fun s => Finset.sum_congr rfl (fun i _ => by ring)]
  rw [FiniteDesign.E_sum]
  rw [show (∑ i, D₁.E (fun s => (1 / C ^ 2) * (ψ i).Var (g i) * Usel i s))
        = ∑ i, (1 / C ^ 2) * (ψ i).Var (g i) * (C / (Fintype.card ι : ℝ))
        from Finset.sum_congr rfl (fun i _ => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
  · rw [FiniteDesign.E_const_mul]
    unfold Usel
    rw [FiniteDesign.E_ind, hstage1 i]

/-- BETWEEN term (abstract). The stage-2 conditional mean of the aggregate equals
`(∑ i, Usel i s · (ψ i).E (g i))/C`, the SRS sample mean of the group-level conditional means. -/
private lemma between_cond_mean_agg (s : StratAssign ι) :
    (prodDesign (fun i => if s i then ψ i else φ i)).E
        (fun w => (∑ i, if s i = true then g i (w i) else 0) / C)
      = (∑ i, Usel i s * (ψ i).E (g i)) / C := by
  rw [(prodDesign (fun i => if s i then ψ i else φ i)).E_congr
      (agg_as_linear_comb g C s)]
  rw [FiniteDesign.E_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [FiniteDesign.E_const_mul, FiniteDesign.E_prod_apply]
  -- on `s i = true`: `(if s i then ψ i else φ i).E (g i) = (ψ i).E (g i)`; on `false` both sides 0.
  unfold Usel FiniteDesign.ind
  by_cases h : s i = true
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

end

set_option linter.unusedDecidableInType false in
/-- **Two-stage variance decomposition, abstract per-group statistic.**  For an arbitrary
within-group statistic `g i` per group, and any two-stage design `jointDesign D₁ ψ φ` whose stage-1
selection satisfies the SRS inclusion moments `C/N` (`hstage1`) and `C(C−1)/(N(N−1))`
(`hstage1pair`) — the moments of the mixed group-assignment strategy of Assumption 1, a simple
random sample of `C` of the `N := card ι` groups flagged ψ — the randomization variance of the
aggregate
`(∑ᵢ 1(Sᵢ=ψ)·g i(wᵢ))/C` splits into a between-group SRS term with finite-population correction
`(1 − C/N)/C` applied to the population sample variance of the conditional means `(ψ i).E (g i)`,
plus a within-group term `(1/(C·N))` times the sum of the conditional variances `(ψ i).Var (g i)`.
This is `Var_popEst` (Theorem 4) and `Var_estDirect` (Theorem 6) with `g` instantiated. -/
theorem Var_groupAgg (D₁ : FiniteDesign (StratAssign ι)) (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (g : ∀ i, WAssign n i → ℝ) (C : ℝ)
    (hC : C ≠ 0) (hN : (Fintype.card ι : ℝ) ≠ 0) (hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0)
    (hstage1 : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ))
    (hstage1pair : ∀ i j, i ≠ j → D₁.E (fun s => FiniteDesign.ind (fun s => s i = true) s
                      * FiniteDesign.ind (fun s => s j = true) s)
        = (C * (C - 1)) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))) :
    (jointDesign D₁ ψ φ).Var (fun sw => (∑ i, if sw.1 i = true then g i (sw.2 i) else 0) / C)
      = (1 - C / (Fintype.card ι : ℝ)) / C * SmuVar (fun i => (ψ i).E (g i))
        + (1 / (C * (Fintype.card ι : ℝ))) * ∑ i, (ψ i).Var (g i) := by
  -- Step 0: law of total variance for the compound design.
  unfold jointDesign
  rw [FiniteDesign.Var_compound_eq_tower D₁ (fun s i => if s i then ψ i else φ i)
      (fun sw => (∑ i, if sw.1 i = true then g i (sw.2 i) else 0) / C)]
  rw [add_comm]
  congr 1
  · -- BETWEEN term: collapse the conditional mean, then `Var_srs_mean`.
    rw [D₁.Var_congr (between_cond_mean_agg ψ φ g C)]
    rw [Var_srs_mean D₁ Usel (fun i => (ψ i).E (g i)) C ?_ ?_ ?_ hC hN1 hN]
    · -- hmean
      intro i; unfold Usel; rw [FiniteDesign.E_ind, hstage1 i]
    · -- hpair
      intro i j hij; unfold Usel; exact hstage1pair i j hij
    · -- hvar
      intro i; unfold Usel; rw [FiniteDesign.Var_ind, hstage1 i]
  · -- WITHIN term.
    exact within_term_agg D₁ ψ φ g C hC hN hstage1

set_option linter.unusedDecidableInType false in
/-- **Hudgens–Halloran (2008), Theorem 4 (two-stage variance decomposition of `Ŷ(z;ψ)`).**
For a two-stage design `jointDesign D₁ ψ φ` whose stage-1 selection has the SRS inclusion moments
`C/N` and `C(C−1)/(N(N−1))` (`hstage1`/`hstage1pair`) and whose within-group designs have
`z`-propensity `m i / n i` (`hprop`) — the moments of the mixed strategy of Assumption 1, a simple
random sample of `C` of the `N := card ι` groups flagged ψ, each selected group randomized by its
within-group mixed design (`Var_popEst_CRD` specializes to that design, discharging all three moment
hypotheses) — the randomization variance of the population estimator `Ŷ(z;ψ)`
splits into a between-group SRS term with finite-population correction `(1 − C/N)/C` applied to the
population sample variance of the group-level potential outcomes `ȳ_i(z;ψ)`, plus a within-group
term `(1/(C·N))` times the sum of the per-group conditional variances of the within-group
estimator. -/
theorem Var_popEst (D₁ : FiniteDesign (StratAssign ι)) (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (z : Bool) (m : ι → ℝ) (C : ℝ)
    (hC : C ≠ 0) (hm : ∀ i, m i ≠ 0) (hn : ∀ i, (n i : ℝ) ≠ 0)
    (hN : (Fintype.card ι : ℝ) ≠ 0) (hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0)
    (hprop : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = z) = m i / (n i))
    (hstage1 : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ))
    (hstage1pair : ∀ i j, i ≠ j →
      D₁.E (fun s => FiniteDesign.ind (fun s => s i = true) s
                      * FiniteDesign.ind (fun s => s j = true) s)
        = (C * (C - 1)) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))) :
    (jointDesign D₁ ψ φ).Var (popEst Y z true m C)
      = (1 - C / (Fintype.card ι : ℝ)) / C * SmuVar (fun i => groupMean ψ Y i z)
        + (1 / (C * (Fintype.card ι : ℝ))) * ∑ i, (ψ i).Var (groupEst Y i z (m i)) := by
  -- `popEst` is the aggregate with `g i = groupEst Y i z (m i)`.
  have hpop : (popEst Y z true m C)
      = (fun sw => (∑ i, if sw.1 i = true then groupEst Y i z (m i) (sw.2 i) else 0) / C) := by
    funext sw; rfl
  rw [hpop, Var_groupAgg D₁ ψ φ (fun i => groupEst Y i z (m i)) C hC hN hN1 hstage1 hstage1pair]
  -- Collapse the between-term conditional means `(ψ i).E (groupEst…) = groupMean ψ Y i z`.
  have hmean : (fun i => (ψ i).E (groupEst Y i z (m i))) = (fun i => groupMean ψ Y i z) := by
    funext i; exact E_groupEst ψ Y i z (m i) (hm i) (hn i) (hprop i)
  rw [hmean]

set_option linter.unusedDecidableInType false in
/-- **Hudgens–Halloran (2008), Theorem 4, for the mixed two-stage design.**  `Var_popEst`
specialized to the actual mixed (completely randomized) two-stage design of Assumption 1: stage-1 is
a simple random sample of `C` of the `N = card ι` groups (`crdOn C`), and each ψ-group `i` is
completely randomized treating `K i` of its `n i` units (`crd (K i)`).  The stage-1 SRS inclusion
moments and within-group `z`-propensities are the derived facts `crdOn_mean`/`crdOn_pair`/
`crd_prop_*`, so — unlike `Var_popEst` — no design-moment hypotheses are assumed, only the
mixed-strategy validity conditions `0 < C < N` and `0 < K i < n i`. -/
theorem Var_popEst_CRD (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (z : Bool) (K : ι → ℕ) (C : ℕ)
    (hC0 : 0 < C) (hCN : C < Fintype.card ι)
    (hK0 : ∀ i, 0 < K i) (hKn : ∀ i, K i < n i) :
    (jointDesign (crdOn C hCN.le) (fun i => crd (K i) (hKn i).le)
        (fun i => crd (K i) (hKn i).le)).Var
        (popEst Y z true (fun i => bif z then (K i : ℝ) else ((n i : ℝ) - K i)) (C : ℝ))
      = (1 - (C : ℝ) / (Fintype.card ι : ℝ)) / C
          * SmuVar (fun i => groupMean (fun i => crd (K i) (hKn i).le) Y i z)
        + (1 / ((C : ℝ) * (Fintype.card ι : ℝ)))
          * ∑ i, (crd (K i) (hKn i).le).Var
              (groupEst Y i z (bif z then (K i : ℝ) else ((n i : ℝ) - K i))) := by
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
  have hmr : ∀ i, (bif z then (K i : ℝ) else ((n i : ℝ) - K i)) ≠ 0 := fun i => by
    cases z with
    | true => simpa using (by exact_mod_cast (hK0 i).ne' : (K i : ℝ) ≠ 0)
    | false =>
        simp only [cond_false]
        exact sub_ne_zero.mpr (ne_of_gt (show (K i : ℝ) < n i by exact_mod_cast hKn i))
  have hprop : ∀ i (j : Fin (n i)),
      (crd (K i) (hKn i).le).Pr (fun w => w j = z)
        = (bif z then (K i : ℝ) else ((n i : ℝ) - K i)) / n i := fun i j => by
    cases z with
    | true => simpa using crd_prop_true (K i) (hKn i).le j
    | false => simpa using crd_prop_false (K i) (hKn i).le j
  exact Var_popEst (crdOn C hCN.le) (fun i => crd (K i) (hKn i).le)
    (fun i => crd (K i) (hKn i).le) Y z
    (fun i => bif z then (K i : ℝ) else ((n i : ℝ) - K i)) (C : ℝ)
    hCr hmr hnr hNr hN1r hprop
    (fun i => crdOn_mean C hCN.le i)
    (fun i j hij => crdOn_pair C hCN.le i j hij)

end TwoStageInterference
end Experimentation
end Causalean
