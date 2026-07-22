/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014), Proposition 5.1 under literally identical groups

This file discharges the analytic homogeneity hypothesis `hhom` of the treatment-minus-control
direct-effect CLT bundle `Homogeneous` from a *concrete, checkable* condition: that the groups are
literally identical.  In the identical-groups regime every group has the same size `K`, the same
allocation strategies ψ/φ, the same potential outcomes, and the same unit counts, so the
within-group assignment space is the common, non-dependent space `W := Fin K → Bool` and the
conditional design is a genuine product over `ι → W`.

The mathematical content is selection symmetry.  The conditional studentized CDF given a stage-1
selection `s` depends on `s` only through the number of selected groups (fixed at `C`), because a
coordinate permutation `σ : ι ≃ ι` carrying one selection pattern to another simultaneously relabels
the conditional product design (via `prodDesign_Pr_reindex`) and carries the studentized statistic,
since identical groups make the per-group summand the same for every coordinate.  Hence any two
supported selections give the same conditional CDF, which is exactly `hhom`.

It provides: the identical-groups bundle `IdenticalRef` (reference data per `n` plus the common
propensity hypotheses, assembling a constant `LHExperiment`); the selection-symmetry permutation
existence lemma `exists_equiv_selection`; the derived hypothesis `hhom_of_identical`; the assembled
`Homogeneous` bundle `homogeneous_of_identical`; and the headline `directEffect_clt_identical`, which
rests on identical groups, bounded outcomes, and the many-groups rate — no `hhom` assumption.
-/

import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLTDischargeMain
import Causalean.Experimentation.DesignBased.ProductReindex

/-!
# Identical-groups discharge for the direct-effect CLT

This file turns literal group-level symmetry into the homogeneity hypothesis used by the
Liu-Hudgens direct-effect CLT.

The reference bundle `IdenticalRef` stores one identical-groups experiment: a common group size,
common within-group strategies, common potential outcomes, common treated/control counts, the
stage-1 design, and the propensities/nondegeneracy hypotheses needed to build `toExp :
LHExperiment`. It also defines the common per-group contrast `groupDiff₀`, the concrete
studentized statistic `studId`, the common group effect `refDelta`, and the common within-group
variance `refVar`.

The theorem `hhom_of_identical` proves the selection-symmetry hypothesis by relabeling equal-size
selected sets with `exists_equiv_selection` and `prodDesign_Pr_reindex`. The definition
`homogeneous_of_identical` assembles the resulting `Homogeneous` bundle, and
`directEffect_clt_identical` derives asymptotic normality without assuming analytic homogeneity as a
separate premise.
-/

open scoped BigOperators Topology
open Finset Filter

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-! ### Selection-symmetry permutation -/

/-- **Selection-symmetry permutation.** Given two Boolean selections `s, s'` on a finite type `ι`
that flag the same number of indices (`card {i | s i} = card {i | s' i}`), there is a permutation
`σ : ι ≃ ι` aligning their patterns: `s' i = s (σ i)` for every `i`.  Built by gluing a bijection of
the selected sets (equal cardinality) with a bijection of their complements (equal cardinality,
since the total is fixed) through `Equiv.sumCompl`. -/
lemma exists_equiv_selection {ι : Type*} [Fintype ι] (s s' : ι → Bool)
    (hcard : (Finset.univ.filter (fun i => s i = true)).card
      = (Finset.univ.filter (fun i => s' i = true)).card) :
    ∃ σ : ι ≃ ι, ∀ i, s' i = s (σ i) := by
  classical
  -- Predicates with the carried `Fintype`/`DecidablePred` instances.
  -- True-sets have equal cardinality (`hcard`); complements then also (total `card ι` fixed).
  have hcardT : Fintype.card {i // s' i = true} = Fintype.card {i // s i = true} := by
    simp only [Fintype.card_subtype]
    exact hcard.symm
  have hcardF : Fintype.card {i // ¬ s' i = true} = Fintype.card {i // ¬ s i = true} := by
    have h1 := Fintype.card_subtype_compl (fun i => s' i = true)
    have h2 := Fintype.card_subtype_compl (fun i => s i = true)
    rw [h1, h2, hcardT]
  -- Bijections of selected sets and of complements.
  let eT : {i // s' i = true} ≃ {i // s i = true} := Fintype.equivOfCardEq hcardT
  let eF : {i // ¬ s' i = true} ≃ {i // ¬ s i = true} := Fintype.equivOfCardEq hcardF
  -- Glue via `sumCompl` on both sides.
  let σ : ι ≃ ι :=
    (Equiv.sumCompl (fun i => s' i = true)).symm.trans
      ((eT.sumCongr eF).trans (Equiv.sumCompl (fun i => s i = true)))
  refine ⟨σ, fun i => ?_⟩
  -- Compute `σ i` explicitly: it is the underlying element of the image of `i` under the glued
  -- bijection, which by construction lies in the matching set of `s`.
  have hσ : ∀ i, σ i = (Equiv.sumCompl (fun i => s i = true))
      ((eT.sumCongr eF) ((Equiv.sumCompl (fun i => s' i = true)).symm i)) := fun i => rfl
  rw [hσ]
  -- Case on `s' i`; in each branch `σ i` lands in the matching set of `s`.
  by_cases hi : s' i = true
  · rw [Equiv.sumCompl_symm_apply_of_pos (p := fun i => s' i = true) hi]
    rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact hi.trans ((eT ⟨i, hi⟩).2).symm
  · rw [Equiv.sumCompl_symm_apply_of_neg (p := fun i => s' i = true) hi]
    rw [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    have hF : s (↑(eF ⟨i, hi⟩)) = false := Bool.not_eq_true _ ▸ (eF ⟨i, hi⟩).2
    rw [hF]; simpa using hi

/-! ### Identical-groups reference data and the constant experiment -/

/-- **Reference data for one identical-groups experiment.** All groups share a common size `K`,
a common pair of allocation strategies `ψ₀`/`φ₀` over the within-group space `Fin K → Bool`,
common potential outcomes `Y₀`, and common control/treatment unit counts `m0₀`/`m1₀`. The stage-1
design `D₁` over the population of groups `ι`, the ψ-selection count `C`, and the regularity
hypotheses complete the data needed to assemble the constant `LHExperiment` `toExp`. -/
structure IdenticalRef where
  /-- Finite population of groups. -/
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  /-- The common group size. -/
  K : ℕ
  /-- The common allocation strategy ψ. -/
  ψ₀ : FiniteDesign (Fin K → Bool)
  /-- The common comparison strategy φ. -/
  φ₀ : FiniteDesign (Fin K → Bool)
  /-- The common partial-interference potential outcomes. -/
  Y₀ : Fin K → (Fin K → Bool) → ℝ
  /-- The common control-unit count. -/
  m0₀ : ℝ
  /-- The common treated-unit count. -/
  m1₀ : ℝ
  /-- Stage-1 strategy-assignment design. -/
  D₁ : FiniteDesign (StratAssign ι)
  /-- Number of groups selected for ψ at stage 1. -/
  C : ℝ
  /-- The ψ-selection count is nonzero. -/
  hC : C ≠ 0
  /-- The common control count is nonzero. -/
  hm0 : m0₀ ≠ 0
  /-- The common treated count is nonzero. -/
  hm1 : m1₀ ≠ 0
  /-- The common group size is nonzero. -/
  hn  : (K : ℝ) ≠ 0
  /-- There is at least one group. -/
  hN  : (Fintype.card ι : ℝ) ≠ 0
  /-- There are at least two groups, needed for the pair propensity. -/
  hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0
  /-- Within-group control propensity of every unit is `m0₀ / K`. -/
  hprop0 : ∀ j : Fin K, ψ₀.Pr (fun w => w j = false) = m0₀ / (K : ℝ)
  /-- Within-group treatment propensity of every unit is `m1₀ / K`. -/
  hprop1 : ∀ j : Fin K, ψ₀.Pr (fun w => w j = true) = m1₀ / (K : ℝ)
  /-- Stage-1 first-order selection propensity of every group is `C/N`. -/
  hstage1 : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ)
  /-- Stage-1 second-order (pair) selection propensity is `C(C−1)/(N(N−1))`. -/
  hstage1pair : ∀ i j, i ≠ j →
    D₁.E (fun s => FiniteDesign.ind (fun s => s i = true) s
        * FiniteDesign.ind (fun s => s j = true) s)
      = (C * (C - 1)) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))

attribute [instance] IdenticalRef.fι IdenticalRef.dι

namespace IdenticalRef

variable (R : IdenticalRef)

/-- The constant `LHExperiment` assembled from identical-groups reference data: every group has
`gsize := K`, strategies `ψ₀`/`φ₀`, outcomes `Y₀`, and counts `m0₀`/`m1₀`.  Because `gsize` is the
literal constant `fun _ => K`, the within-group assignment space is the non-dependent space
`Fin K → Bool` and the conditional design is a genuine product over `ι → (Fin K → Bool)`. -/
noncomputable def toExp : LHExperiment where
  ι := R.ι
  gsize := fun _ => R.K
  D₁ := R.D₁
  ψ := fun _ => R.ψ₀
  φ := fun _ => R.φ₀
  Y := fun _ => R.Y₀
  m0 := fun _ => R.m0₀
  m1 := fun _ => R.m1₀
  C := R.C
  hC := R.hC
  hm0 := fun _ => R.hm0
  hm1 := fun _ => R.hm1
  hn := fun _ => R.hn
  hN := R.hN
  hN1 := R.hN1
  hprop0 := fun _ => R.hprop0
  hprop1 := fun _ => R.hprop1
  hstage1 := R.hstage1
  hstage1pair := R.hstage1pair

/-- The common per-group treatment-minus-control contrast estimator of the identical groups; it
does not depend on the group index. -/
noncomputable def groupDiff₀ (w : Fin R.K → Bool) : ℝ :=
  (∑ j, if w j = true then R.Y₀ j w else 0) / R.m1₀
    - (∑ j, if w j = false then R.Y₀ j w else 0) / R.m0₀

/-- In the constant experiment, every group's contrast estimator equals the common `groupDiff₀`. -/
lemma groupDiff_toExp (i : R.ι) : groupDiff R.toExp i = R.groupDiff₀ := by
  rfl

/-- The conditional design of the constant experiment is the genuine product, over the
non-dependent space `R.ι → (Fin K → Bool)`, of the per-group strategy designs. -/
lemma condDesign_toExp (s : StratAssign R.ι) :
    condDesign R.toExp s = prodDesign (fun i => if s i then R.ψ₀ else R.φ₀) := rfl

/-- The concrete studentized treatment-minus-control contrast statistic of the constant
experiment. -/
noncomputable def studId (sw : StratAssign R.ι × (R.ι → (Fin R.K → Bool))) : ℝ :=
  (R.toExp.estD sw - R.toExp.DEbar) / Real.sqrt (R.toExp.directVar)

/-- **Estimator equivariance.** Because all groups are identical, the aggregate contrast estimator
sees a selection only through its pattern: if `σ` aligns the patterns of `s'` and `s`
(`s' i = s (σ i)`), then evaluating at `s'` and the relabeled assignment `w ∘ σ` equals the value
at `s` and `w`. -/
lemma estD_equivariant (s s' : StratAssign R.ι) (σ : R.ι ≃ R.ι) (hσ : ∀ i, s' i = s (σ i))
    (w : R.ι → (Fin R.K → Bool)) :
    R.toExp.estD (s', fun i => w (σ i)) = R.toExp.estD (s, w) := by
  rw [estD_eq_agg, estD_eq_agg]
  congr 1
  refine Fintype.sum_equiv σ
    (fun i => (if s' i then (1 : ℝ) else 0) * groupDiff R.toExp i (w (σ i)))
    (fun i => (if s i then (1 : ℝ) else 0) * groupDiff R.toExp i (w i)) (fun i => ?_)
  simp only [groupDiff_toExp, hσ i]

/-- **Studentized equivariance.** The studentized statistic is likewise selection-pattern
equivariant, since `DEbar` and `directVar` are scalars and the estimator is equivariant. -/
lemma studId_equivariant (s s' : StratAssign R.ι) (σ : R.ι ≃ R.ι) (hσ : ∀ i, s' i = s (σ i))
    (w : R.ι → (Fin R.K → Bool)) :
    R.studId (s', fun i => w (σ i)) = R.studId (s, w) := by
  unfold studId
  congr 2
  exact estD_equivariant R s s' σ hσ w

open Classical in
/-- **Derived homogeneity hypothesis under identical groups.** For two stage-1 selections each
flagging exactly `C` groups, the conditional studentized CDF is the same.  This is exactly the
analytic homogeneity hypothesis `hhom`, now a theorem: the selection-symmetry permutation `σ`
(`exists_equiv_selection`) relabels the conditional product design (`prodDesign_Pr_reindex`) while
carrying the studentized statistic (`studId_equivariant`), so the two CDFs coincide. -/
lemma hhom_of_identical (t : ℝ) (s s' : StratAssign R.ι)
    (hs : (∑ i, if s i then (1 : ℝ) else 0) = R.C)
    (hs' : (∑ i, if s' i then (1 : ℝ) else 0) = R.C) :
    (condDesign R.toExp s).Pr (fun w => R.studId (s, w) ≤ t)
      = (condDesign R.toExp s').Pr (fun w => R.studId (s', w) ≤ t) := by
  -- The two selections flag the same number of groups, so their selected sets have equal card.
  have hsum : (∑ i, if s i then (1 : ℝ) else 0) = (∑ i, if s' i then (1 : ℝ) else 0) := by
    rw [hs, hs']
  have hcardℝ : ((Finset.univ.filter (fun i => s i = true)).card : ℝ)
      = ((Finset.univ.filter (fun i => s' i = true)).card : ℝ) := by
    have e : ∀ u : StratAssign R.ι, (∑ i, if u i then (1 : ℝ) else 0)
        = ((Finset.univ.filter (fun i => u i = true)).card : ℝ) := by
      intro u
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        mul_one]
    rw [← e s, ← e s', hsum]
  have hcard : (Finset.univ.filter (fun i => s i = true)).card
      = (Finset.univ.filter (fun i => s' i = true)).card := by exact_mod_cast hcardℝ
  -- The selection-symmetry permutation aligning `s'` to `s`.
  obtain ⟨σ, hσ⟩ := exists_equiv_selection s s' hcard
  -- Relabel `condDesign s'` to `condDesign s` via `prodDesign_Pr_reindex`, carrying the statistic.
  rw [condDesign_toExp, condDesign_toExp]
  -- The permuted product `D ∘ σ` equals the conditional design at `s'` (since `s' i = s (σ i)`).
  have hdesign : (fun i => if s (σ i) then R.ψ₀ else R.φ₀)
      = (fun i => if s' i then R.ψ₀ else R.φ₀) := by
    funext i; rw [hσ i]
  calc (prodDesign (fun i => if s i then R.ψ₀ else R.φ₀)).Pr (fun w => R.studId (s, w) ≤ t)
      = (prodDesign (fun i => if s i then R.ψ₀ else R.φ₀)).Pr
          (fun w => R.studId (s', fun i => w (σ i)) ≤ t) :=
        FiniteDesign.Pr_congr _ _ _ (fun w => by rw [studId_equivariant R s s' σ hσ w])
    _ = (prodDesign (fun i => (fun i => if s i then R.ψ₀ else R.φ₀) (σ i))).Pr
          (fun w => R.studId (s', w) ≤ t) :=
        FiniteDesign.prodDesign_Pr_reindex σ (fun i => if s i then R.ψ₀ else R.φ₀)
          (fun w => R.studId (s', w) ≤ t)
    _ = (prodDesign (fun i => if s' i then R.ψ₀ else R.φ₀)).Pr (fun w => R.studId (s', w) ≤ t) := by
        rw [hdesign]

/-! ### Reference group effect and variance -/

/-- The common group-average potential outcome `ȳ(z)` of the identical groups under treatment
status `z`, computed from the reference allocation strategy and outcomes — index-free. -/
noncomputable def refGroupMean (z : Bool) : ℝ :=
  (∑ j : Fin R.K,
    R.ψ₀.E (fun w => if w j = z then R.Y₀ j w else 0) / R.ψ₀.Pr (fun w => w j = z)) / (R.K : ℝ)

/-- The common group-level treatment-minus-control direct-effect contrast `δ` of the identical
groups; it does not depend on any group index. -/
noncomputable def refDelta : ℝ := R.refGroupMean true - R.refGroupMean false

/-- The common within-group contrast-estimator variance `v` of the identical groups. -/
noncomputable def refVar : ℝ := R.ψ₀.Var R.groupDiff₀

/-- In the constant experiment every group's level contrast equals the common `refDelta`. -/
lemma hδ_toExp (i : R.ι) :
    groupMean R.toExp.ψ R.toExp.Y i true - groupMean R.toExp.ψ R.toExp.Y i false = R.refDelta := by
  rfl

/-- In the constant experiment every group's within-group variance equals the common `refVar`. -/
lemma hv_toExp (i : R.ι) :
    (R.toExp.ψ i).Var (groupDiff R.toExp i) = R.refVar := by
  rfl

end IdenticalRef

open DesignBased in
open scoped Classical in
/-- **Homogeneity bundle from identical groups.** From a sequence of identical-groups experiments
sharing one group-level treatment-minus-control direct-effect contrast `δ`, with a uniform bound
`M` on the centered per-group estimator, the many-groups rate, and the exact-`C` selection support,
the full `Homogeneous` bundle is assembled — with its `hhom` field discharged by
`hhom_of_identical`.  The within-group variances `v n := refVar (R n)` may vary across `n`. -/
noncomputable def homogeneous_of_identical (R : ℕ → IdenticalRef) (t δ M : ℝ)
    (hδ : ∀ n, (R n).refDelta = δ)
    (hvpos : ∀ n, 0 < (R n).refVar)
    (hMbound : ∀ n i w, |groupDiff (R n).toExp i w - δ| ≤ M)
    (hcount : ∀ n s, (R n).toExp.D₁.p s ≠ 0 →
      (∑ i, if s i then (1 : ℝ) else 0) = (R n).toExp.C)
    (hB0 : Tendsto (fun n => M / Real.sqrt ((R n).toExp.C * (R n).refVar)) atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (R n).toExp.ι : ℝ)
        * (M / Real.sqrt ((R n).toExp.C * (R n).refVar)) ^ 3) atTop (𝓝 0)) :
    Homogeneous (fun n => (R n).toExp) t (fun n => (R n).studId) δ M (fun n => (R n).refVar) where
  hstud := fun n sw => rfl
  hδ := fun n i => by rw [(R n).hδ_toExp i, hδ n]
  hv := fun n i => (R n).hv_toExp i
  hvpos := hvpos
  hMbound := hMbound
  hcount := hcount
  hB0 := hB0
  hNB3 := hNB3
  hhom := fun n s s' hs hs' =>
    (R n).hhom_of_identical t s s' (hcount n s hs) (hcount n s' hs')

open DesignBased in
/-- **Proposition 5.1 under literally identical groups.** When the groups are identical across the
sequence — common size, allocation strategies, potential outcomes, and unit counts, all sharing one
group-level treatment-minus-control direct-effect contrast `δ` — with a uniform bound `M` on the
centered per-group contrast estimator, the exact-`C` selection support, and the many-groups rate,
the studentized contrast statistic is asymptotically standard normal.  No analytic homogeneity
hypothesis is assumed: it is derived from the concrete identical-groups structure via
`hhom_of_identical`. -/
theorem directEffect_clt_identical (R : ℕ → IdenticalRef) (t δ M : ℝ)
    (hδ : ∀ n, (R n).refDelta = δ)
    (hvpos : ∀ n, 0 < (R n).refVar)
    (hMbound : ∀ n i w, |groupDiff (R n).toExp i w - δ| ≤ M)
    (hcount : ∀ n s, (R n).toExp.D₁.p s ≠ 0 →
      (∑ i, if s i then (1 : ℝ) else 0) = (R n).toExp.C)
    (hB0 : Tendsto (fun n => M / Real.sqrt ((R n).toExp.C * (R n).refVar)) atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (R n).toExp.ι : ℝ)
        * (M / Real.sqrt ((R n).toExp.C * (R n).refVar)) ^ 3) atTop (𝓝 0)) :
    Tendsto (fun n => (R n).toExp.jointD.Pr (fun sw => (R n).studId sw ≤ t)) atTop
      (𝓝 (stdNormalCdf t)) :=
  directEffect_clt_homogeneous
    (homogeneous_of_identical R t δ M hδ hvpos hMbound hcount hB0 hNB3)

end TwoStageInterference
end Experimentation
end Causalean
