/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014), Proposition 5.1: discharging the conditional-CLT regularity

This file makes Proposition 5.1 **primitive**: under homogeneity (all group-level
treatment-minus-control direct-effect contrasts equal a common `δ`, all within-group contrast
estimator variances equal a common `v n`), bounded per-group contrast estimators, and the
many-groups rate, the studentized contrast statistic is asymptotically standard normal, with the
*conditional* central limit theorem supplied directly by the independent-summands CLT
`prodDesign_clt` of the design-based substrate and the selection-mixture lifted by homogeneity.
No CLT is taken as a black box.

The mathematical content is that, under homogeneity, the conditional studentized statistic given a
stage-1 selection `s` is a normalized sum of independent, uniformly bounded, mean-zero
per-coordinate summands over the conditional product design `cond s = prodDesign (if sᵢ then ψᵢ
else φᵢ)`:

    stud(s,w) = ∑ᵢ (1(sᵢ=ψ)·(dᵢ(wᵢ) − δ)) / √(C·v),    dᵢ(w) = Ŷ_i(1)(w) − Ŷ_i(0)(w),

because homogeneity collapses the population average contrast to `DEbar = δ`, kills the
between-group term of `directVar` (the population variance of a constant is zero) leaving
`directVar = v/C`, and the selection has exactly `C` ψ-flagged groups.  Each summand is mean-zero
on the selected coordinates and the total design variance is one, so `prodDesign_clt` delivers the
conditional CDF → `Φ` for a fixed reference selection; the hypothesis `hhom` (the conditional CDF is
selection-independent — the faithful encoding of the paper's homogeneity) lifts this uniform bound
over the stage-1 support, and the (support-restricted) mixture-lifting lemma
`tendsto_E_of_uniformBound_ae` averages it to the unconditional `Φ`.

We add a support-restricted ("a.e.") variant `tendsto_E_of_uniformBound_ae` of the mixture-lifting
lemma, because the homogeneity hypothesis `hhom` only relates conditional CDFs across the stage-1
*support*, while the stage-1 average only weights support points; the bound off-support is never
needed.

This file provides the substrate lemmas (`Var_sub_const`, `tendsto_E_of_uniformBound_ae`), the
homogeneity + regularity bundle `Homogeneous`, the estimand/variance reductions
(`DEbar_eq_of_homogeneous`, `directVar_eq_of_homogeneous`), the studentized-as-independent-sum
identity `stud_eq_sum_of_homogeneous`, and the reference-selection machinery (`refSel`,
`nonempty_of_refSel`).  The conditional CLT `condCLT_ref` and the headline
`directEffect_clt_homogeneous` are assembled in `CLTDischargeMain`.
-/

import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLT
import Causalean.Experimentation.DesignBased.IndepSummandsCLT
import Causalean.Experimentation.DesignBased.ProductVariance

/-! # Primitive ingredients for the Liu-Hudgens homogeneous CLT discharge

This file provides the primitive ingredients that remove the conditional-CLT premise from the
Liu-Hudgens Proposition 5.1 argument under homogeneity.

It defines the per-group contrast estimator `groupDiff`, the conditional product design
`condDesign`, and the homogeneity/regularity bundle `Homogeneous`. The main reductions show that
homogeneity collapses the estimand to the common contrast (`DEbar_eq_of_homogeneous`), collapses
the two-stage variance to `v / C` (`directVar_eq_of_homogeneous`), and rewrites the studentized
statistic as a normalized sum of independent per-coordinate summands (`stud_eq_sum_of_homogeneous`).

The support-restricted averaging lemma `FiniteDesign.tendsto_E_of_uniformBound_ae` and the
reference-selection lemmas `refSel`, `refSel_mem`, and `nonempty_of_refSel` are used by
`CLTDischargeMain.lean` to prove `directEffect_clt_homogeneous` without taking a conditional CLT as
a black box. -/

open scoped BigOperators Topology
open Finset Filter

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)

/-- Shifting a random variable by a constant leaves its variance unchanged. -/
lemma Var_sub_const (X : Ω → ℝ) (c : ℝ) :
    D.Var (fun z => X z - c) = D.Var X := by
  rw [Var_eq, Var_eq, E_sub, E_const]
  have h : (fun z => (X z - c) ^ 2)
      = (fun z => (X z) ^ 2 + ((-(2 * c)) * X z + c ^ 2)) := by funext z; ring
  rw [h, E_add, E_add, E_const_mul, E_const]; ring

/-- Design expectations converge to a constant when the random variables converge uniformly on the
support of each design.

Off-support points carry zero design weight, so the uniform bound is required only where the design
assigns positive probability. -/
theorem tendsto_E_of_uniformBound_ae {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (D : ∀ n, FiniteDesign (Ω n)) (F : ∀ n, Ω n → ℝ) (L : ℝ) (B : ℕ → ℝ)
    (hbound : ∀ n s, (D n).p s ≠ 0 → |F n s - L| ≤ B n) (hB : Tendsto B atTop (𝓝 0)) :
    Tendsto (fun n => (D n).E (F n)) atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hB
  have hrecenter : (D n).E (F n) - L = (D n).E (fun s => F n s - L) := by
    rw [(D n).E_sub (F n) (fun _ => L), (D n).E_const]
  rw [Real.norm_eq_abs, hrecenter]
  -- `|∑ p s (F s − L)| ≤ ∑ p s |F s − L| ≤ ∑ p s · B n = B n` on the support.
  unfold FiniteDesign.E
  calc |∑ s, (D n).p s * (F n s - L)|
      ≤ ∑ s, |(D n).p s * (F n s - L)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s, (D n).p _s * B n := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        rw [abs_mul, abs_of_nonneg ((D n).p_nonneg s)]
        by_cases hps : (D n).p s = 0
        · simp [hps]
        · exact mul_le_mul_of_nonneg_left (hbound n s hps) ((D n).p_nonneg s)
    _ = B n := by rw [← Finset.sum_mul, (D n).p_sum, one_mul]

end FiniteDesign

end DesignBased

namespace TwoStageInterference

open DesignBased

/-- This is the per-group estimator for the treatment-minus-control direct-effect contrast in one
group of a Liu-Hudgens experiment.

It subtracts the control-strategy group estimator from the treated-strategy group estimator for the
same within-group assignment. -/
noncomputable def groupDiff (E : LHExperiment) (i : E.ι)
    (w : Fin (E.gsize i) → Bool) : ℝ :=
  groupEst E.Y i true (E.m1 i) w - groupEst E.Y i false (E.m0 i) w

/-- This is the stage-two product design conditional on a stage-one strategy assignment. -/
noncomputable def condDesign (E : LHExperiment) (s : StratAssign E.ι) :
    FiniteDesign (∀ i, Fin (E.gsize i) → Bool) :=
  prodDesign (fun i => if s i then E.ψ i else E.φ i)

/-- The experiment-level contrast estimator is the mean of the selected groups' per-group
treatment-minus-control contrast estimators.

This is a pure unfolding of the Horvitz-Thompson estimator under the two-stage design. -/
lemma estD_eq_agg (E : LHExperiment)
    (s : StratAssign E.ι) (w : ∀ i, Fin (E.gsize i) → Bool) :
    E.estD (s, w) = (∑ i, (if s i then (1 : ℝ) else 0) * groupDiff E i (w i)) / E.C := by
  simp only [LHExperiment.estD, estDirect, popEst, groupDiff]
  rw [← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : s i = true
  · simp only [h, if_pos, one_mul]
  · simp [h]

/-- **Homogeneity + regularity bundle for a sequence of Liu–Hudgens experiments.** Faithfully
encodes the hypotheses of Proposition 5.1 for the Hudgens-Halloran orientation: all
group-level direct-effect contrasts equal a common `δ` (homogeneity); all within-group contrast
estimator variances equal a common positive `v n`; the centered per-group contrast estimator is
bounded by `M`; every supported stage-1 selection flags exactly `C` groups; the bound sequence
`B n := M / √(C n · v n)` and `card · B³` vanish (the many-groups rate); and the conditional
studentized CDF is selection-independent over the stage-1 support (`hhom`, the analytic form of
homogeneity that lifts the conditional CLT to the average). -/
structure Homogeneous (Exp : ℕ → LHExperiment) (t : ℝ)
    (stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (δ M : ℝ) (v : ℕ → ℝ) where
  /-- The studentized statistic is `(estD − DEbar)/√directVar`. -/
  hstud : ∀ n sw,
    stud n sw = ((Exp n).estD sw - (Exp n).DEbar) / Real.sqrt ((Exp n).directVar)
  /-- All group-level treatment-minus-control direct-effect contrasts equal the common value `δ`
  (homogeneity). -/
  hδ : ∀ n i, groupMean (Exp n).ψ (Exp n).Y i true
              - groupMean (Exp n).ψ (Exp n).Y i false = δ
  /-- All within-group contrast-estimator variances equal the common value `v n`. -/
  hv : ∀ n i, ((Exp n).ψ i).Var (groupDiff (Exp n) i) = v n
  /-- The common within-group variance is positive. -/
  hvpos : ∀ n, 0 < v n
  /-- The centered per-group contrast estimator is bounded by `M`. -/
  hMbound : ∀ n i w, |groupDiff (Exp n) i w - δ| ≤ M
  /-- Every supported stage-1 selection flags exactly `C` groups. -/
  hcount : ∀ n s, (Exp n).D₁.p s ≠ 0 →
    (∑ i, if s i then (1 : ℝ) else 0) = (Exp n).C
  /-- The many-groups rate: `B n := M / √(C n · v n) → 0`. -/
  hB0 : Tendsto (fun n => M / Real.sqrt ((Exp n).C * v n)) atTop (𝓝 0)
  /-- The Lyapunov rate: `card · B³ → 0`. -/
  hNB3 : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ)
      * (M / Real.sqrt ((Exp n).C * v n)) ^ 3) atTop (𝓝 0)
  /-- The conditional studentized CDF is selection-independent over the stage-1 support. -/
  hhom : ∀ n s s', (Exp n).D₁.p s ≠ 0 → (Exp n).D₁.p s' ≠ 0 →
    (condDesign (Exp n) s).Pr (fun w => stud n (s, w) ≤ t)
      = (condDesign (Exp n) s').Pr (fun w => stud n (s', w) ≤ t)

variable {Exp : ℕ → LHExperiment} {t δ M : ℝ} {v : ℕ → ℝ}
  {stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ}

/-- **Estimand reduction.** Under homogeneity the population average treatment-minus-control
direct-effect contrast collapses to the common group-level contrast: `DEbar = δ`. -/
lemma DEbar_eq_of_homogeneous (h : Homogeneous Exp t stud δ M v) (n : ℕ) :
    (Exp n).DEbar = δ := by
  simp only [LHExperiment.DEbar, CE_direct, popMean, ← sub_div, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => h.hδ n i), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [mul_comm, mul_div_assoc, div_self (Exp n).hN, mul_one]

/-- **Variance reduction.** Under homogeneity the between-group term of `directVar` vanishes (the
population variance of a constant is zero) and the within-group term averages to `v n / C`, so
`directVar = v n / C`. -/
lemma directVar_eq_of_homogeneous (h : Homogeneous Exp t stud δ M v) (n : ℕ) :
    (Exp n).directVar = v n / (Exp n).C := by
  have hSmu : SmuVar (fun i => groupMean (Exp n).ψ (Exp n).Y i true
      - groupMean (Exp n).ψ (Exp n).Y i false) = 0 := by
    simp only [SmuVar]
    have hmubar : (∑ i, (groupMean (Exp n).ψ (Exp n).Y i true
          - groupMean (Exp n).ψ (Exp n).Y i false)) / (Fintype.card (Exp n).ι : ℝ) = δ := by
      rw [Finset.sum_congr rfl (fun i _ => h.hδ n i), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_comm, mul_div_assoc, div_self (Exp n).hN, mul_one]
    rw [hmubar]
    rw [Finset.sum_congr rfl (fun i _ => by rw [h.hδ n i, sub_self]; ring : ∀ i ∈ Finset.univ,
      (groupMean (Exp n).ψ (Exp n).Y i true - groupMean (Exp n).ψ (Exp n).Y i false - δ) ^ 2
        = 0)]
    simp
  have hwithin : ∑ i, ((Exp n).ψ i).Var (fun w => groupEst (Exp n).Y i true ((Exp n).m1 i) w
        - groupEst (Exp n).Y i false ((Exp n).m0 i) w)
      = (Fintype.card (Exp n).ι : ℝ) * v n := by
    rw [show (∑ i, ((Exp n).ψ i).Var (fun w => groupEst (Exp n).Y i true ((Exp n).m1 i) w
            - groupEst (Exp n).Y i false ((Exp n).m0 i) w))
          = ∑ i, ((Exp n).ψ i).Var (groupDiff (Exp n) i) from rfl,
      Finset.sum_congr rfl (fun i _ => h.hv n i), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  simp only [LHExperiment.directVar]
  rw [hSmu, hwithin]
  have hC := (Exp n).hC
  have hN := (Exp n).hN
  field_simp
  ring

/-- This is the mean-zero scaled per-coordinate summand of the conditional studentized statistic
under homogeneity. -/
noncomputable def cltSummand (n : ℕ) (δ : ℝ) (v : ℕ → ℝ) (s : StratAssign (Exp n).ι)
    (i : (Exp n).ι) (a : Fin ((Exp n).gsize i) → Bool) : ℝ :=
  (if s i then (1 : ℝ) else 0) * (groupDiff (Exp n) i a - δ)
    / Real.sqrt ((Exp n).C * v n)

/-- **Studentized = independent sum.** For a supported stage-1 selection `s`, under homogeneity the
conditional studentized statistic is the normalized independent sum
`stud(s,w) = ∑ᵢ gₛ,ᵢ(wᵢ)`. -/
lemma stud_eq_sum_of_homogeneous (h : Homogeneous Exp t stud δ M v) (n : ℕ)
    (s : StratAssign (Exp n).ι) (hs : (Exp n).D₁.p s ≠ 0)
    (w : ∀ i, Fin ((Exp n).gsize i) → Bool) :
    stud n (s, w) = ∑ i, cltSummand n δ v s i (w i) := by
  have hCpos : 0 < (Exp n).C := by
    rcases lt_or_gt_of_ne (Exp n).hC with h0 | h0
    · -- if C < 0, contradiction with hcount (sum of indicators ≥ 0)
      exfalso
      have hnn : (0 : ℝ) ≤ ∑ i, if s i then (1 : ℝ) else 0 :=
        Finset.sum_nonneg (fun i _ => by positivity)
      rw [h.hcount n s hs] at hnn
      linarith
    · exact h0
  have hvpos := h.hvpos n
  have hcount := h.hcount n s hs
  -- `√(C·v) > 0` and `C·√(v/C) = √(C·v)`.
  have hCv : (0 : ℝ) < (Exp n).C * v n := mul_pos hCpos hvpos
  have hsqrtCv : 0 < Real.sqrt ((Exp n).C * v n) := Real.sqrt_pos.mpr hCv
  have hsqrtvC : 0 < Real.sqrt (v n / (Exp n).C) := Real.sqrt_pos.mpr (div_pos hvpos hCpos)
  have hkey : (Exp n).C * Real.sqrt (v n / (Exp n).C) = Real.sqrt ((Exp n).C * v n) := by
    rw [show (Exp n).C * v n = (Exp n).C ^ 2 * (v n / (Exp n).C) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hCpos.le]
  rw [h.hstud, estD_eq_agg, DEbar_eq_of_homogeneous h, directVar_eq_of_homogeneous h]
  -- Recenter: `(∑ 1(sᵢ)·dᵢ)/C − δ = (∑ 1(sᵢ)·(dᵢ−δ))/C` using `∑ 1(sᵢ) = C`.
  have hrecenter : (∑ i, (if s i then (1 : ℝ) else 0) * groupDiff (Exp n) i (w i)) / (Exp n).C - δ
      = (∑ i, (if s i then (1 : ℝ) else 0) * (groupDiff (Exp n) i (w i) - δ)) / (Exp n).C := by
    rw [Finset.sum_congr rfl (fun i _ => mul_sub _ _ _ : ∀ i ∈ Finset.univ,
        (if s i then (1:ℝ) else 0) * (groupDiff (Exp n) i (w i) - δ)
          = (if s i then (1:ℝ) else 0) * groupDiff (Exp n) i (w i)
            - (if s i then (1:ℝ) else 0) * δ),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hcount, sub_div,
      mul_div_cancel_left₀ _ (ne_of_gt hCpos)]
  rw [hrecenter]
  -- Distribute the scalar `1/(C·√(v/C)) = 1/√(C·v)` into the sum.
  simp only [cltSummand]
  rw [div_div, hkey, Finset.sum_div]

/-- The conditional mean of the per-group contrast estimator under the ψ-design is the common
group-level contrast: `(ψ i).E (dᵢ) = δ`.  Immediate from `E_groupEst` (twice) and homogeneity. -/
lemma E_groupDiff_eq_of_homogeneous (h : Homogeneous Exp t stud δ M v) (n : ℕ) (i : (Exp n).ι) :
    ((Exp n).ψ i).E (groupDiff (Exp n) i) = δ := by
  unfold groupDiff
  rw [FiniteDesign.E_sub,
    E_groupEst (Exp n).ψ (Exp n).Y i true ((Exp n).m1 i) ((Exp n).hm1 i) ((Exp n).hn i)
      ((Exp n).hprop1 i),
    E_groupEst (Exp n).ψ (Exp n).Y i false ((Exp n).m0 i) ((Exp n).hm0 i) ((Exp n).hn i)
      ((Exp n).hprop0 i),
    h.hδ n i]

/-- Nonnegativity of the bound constant `M`, available whenever the experiment has at least one
group. -/
lemma M_nonneg_of_homogeneous (h : Homogeneous Exp t stud δ M v) (n : ℕ) [Nonempty (Exp n).ι] :
    0 ≤ M := by
  obtain ⟨i⟩ := (inferInstance : Nonempty (Exp n).ι)
  exact le_trans (abs_nonneg _) (h.hMbound n i (fun _ => false))

/-- Some stage-1 selection lies in the support of `D₁` (its probabilities sum to one). -/
lemma exists_support_selection (E : LHExperiment) : ∃ s, E.D₁.p s ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have : ∑ s, E.D₁.p s = 0 := Finset.sum_eq_zero (fun s _ => hcon s)
  rw [E.D₁.p_sum] at this
  exact one_ne_zero this

open Classical in
/-- A fixed reference selection in the support of stage 1. -/
noncomputable def refSel (Exp : ℕ → LHExperiment) (n : ℕ) : StratAssign (Exp n).ι :=
  (exists_support_selection (Exp n)).choose

/-- The fixed reference selection has positive stage-one design probability. -/
lemma refSel_mem (Exp : ℕ → LHExperiment) (n : ℕ) :
    (Exp n).D₁.p (refSel Exp n) ≠ 0 :=
  (exists_support_selection (Exp n)).choose_spec

/-- The reference selection flags at least one group, so the group index type is nonempty. -/
lemma nonempty_of_refSel (h : Homogeneous Exp t stud δ M v) (n : ℕ) : Nonempty (Exp n).ι := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  have h0 : (∑ i, if refSel Exp n i then (1 : ℝ) else 0) = 0 := by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rw [h.hcount n (refSel Exp n) (refSel_mem Exp n)] at h0
  exact (Exp n).hC h0

end TwoStageInterference
end Experimentation
end Causalean
