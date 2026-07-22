/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: convexity and the observable KKT certificate

`thm:convex-design`. The feasible set is nonempty, compact and convex; the
graph-only envelope is convex on it; a minimizer exists; and every minimizer
admits an observable global KKT optimality certificate through the envelope
gradient, a budget multiplier, and complementary box multipliers.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Envelope
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact
import Optlib.Optimality.Constrained_Problem
import Causalean.Mathlib.Analysis.SmoothReciprocal
import Causalean.Mathlib.Analysis.GradientCoord
import Causalean.Mathlib.Analysis.Convex.ReciprocalProduct

set_option linter.style.longLine false

open scoped BigOperators
open Finset Filter Topology InnerProductSpace Set
open Causalean.Mathlib

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

private lemma feasibleSet_nonempty
    (ε B : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hBlo : (Fintype.card I : ℝ) * ε ≤ B) (hBhi : B ≤ (Fintype.card I : ℝ) * (1 - ε)) :
    (feasibleSet (I := I) ε B).Nonempty := by
  classical
  let p : I → ℝ := fun _ => B / (Fintype.card I : ℝ)
  refine ⟨p, ?_⟩
  refine ⟨?_, ⟨hε, hε2⟩, ?_, ?_⟩
  · intro k
    have hcard_nat : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨k⟩
    have hcard : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hcard_nat
    constructor
    · have hε_le : ε ≤ B / (Fintype.card I : ℝ) := by
        rw [le_div_iff₀ hcard]
        simpa [mul_comm] using hBlo
      exact le_trans hε.le hε_le
    · have hp_le : B / (Fintype.card I : ℝ) ≤ 1 - ε := by
        rw [div_le_iff₀ hcard]
        simpa [mul_comm] using hBhi
      exact le_trans hp_le (by linarith [hε])
  · intro k
    have hcard_nat : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨k⟩
    have hcard : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hcard_nat
    constructor
    · rw [le_div_iff₀ hcard]
      simpa [mul_comm] using hBlo
    · rw [div_le_iff₀ hcard]
      simpa [mul_comm] using hBhi
  · dsimp [BudgetBalance, p]
    by_cases hI : Nonempty I
    · have hcard_nat : 0 < Fintype.card I := Fintype.card_pos_iff.mpr hI
      have hcard_ne : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_nat)
      calc
        ∑ _k : I, B / (Fintype.card I : ℝ)
            = (Fintype.card I : ℝ) * (B / (Fintype.card I : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = B := by field_simp [hcard_ne]
    · have hcard_zero : Fintype.card I = 0 :=
        Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hI)
      have hB0 : B = 0 := by
        have hlo : 0 ≤ B := by simpa [hcard_zero] using hBlo
        have hhi : B ≤ 0 := by simpa [hcard_zero] using hBhi
        exact le_antisymm hhi hlo
      simp [hcard_zero, hB0]

private lemma feasibleSet_convex (ε B : ℝ) :
    Convex ℝ (feasibleSet (I := I) ε B) := by
  classical
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxprob, hxadm, hxfloor, hxbudget⟩
  rcases hy with ⟨hyprob, _hyadm, hyfloor, hybudget⟩
  refine ⟨?_, hxadm, ?_, ?_⟩
  · intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · exact add_nonneg (mul_nonneg ha.le (hxprob k).1) (mul_nonneg hb.le (hyprob k).1)
    · calc
        a * x k + b * y k ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hxprob k).2 ha.le)
            (mul_le_mul_of_nonneg_left (hyprob k).2 hb.le)
        _ = 1 := by linarith
  · intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · calc
        ε = (a + b) * ε := by rw [hab, one_mul]
        _ = a * ε + b * ε := by ring
        _ ≤ a * x k + b * y k :=
          add_le_add (mul_le_mul_of_nonneg_left (hxfloor k).1 ha.le)
            (mul_le_mul_of_nonneg_left (hyfloor k).1 hb.le)
    · calc
        a * x k + b * y k ≤ a * (1 - ε) + b * (1 - ε) :=
          add_le_add (mul_le_mul_of_nonneg_left (hxfloor k).2 ha.le)
            (mul_le_mul_of_nonneg_left (hyfloor k).2 hb.le)
        _ = (a + b) * (1 - ε) := by ring
        _ = 1 - ε := by rw [hab, one_mul]
  · dsimp [BudgetBalance] at hxbudget hybudget ⊢
    change ∑ k, (a * x k + b * y k) = B
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hxbudget, hybudget]
    calc
      a * B + b * B = (a + b) * B := by ring
      _ = B := by rw [hab, one_mul]

private lemma feasibleSet_isClosed (ε B : ℝ) :
    IsClosed (feasibleSet (I := I) ε B) := by
  classical
  have hprob : IsClosed {p : I → ℝ | ProbVector p} := by
    simpa [ProbVector, Set.setOf_forall] using
      (isClosed_iInter (fun k : I =>
        (isClosed_le continuous_const (continuous_apply k)).inter
          (isClosed_le (continuous_apply k) continuous_const)))
  have hfloor : IsClosed {p : I → ℝ | PositivityFloor ε p} := by
    simpa [PositivityFloor, Set.setOf_forall] using
      (isClosed_iInter (fun k : I =>
        (isClosed_le continuous_const (continuous_apply k)).inter
          (isClosed_le (continuous_apply k) continuous_const)))
  have hbudget : IsClosed {p : I → ℝ | BudgetBalance B p} := by
    dsimp [BudgetBalance]
    exact isClosed_eq (continuous_finset_sum _ (fun k _ => continuous_apply k)) continuous_const
  have hclosed : IsClosed {p : I → ℝ | ProbVector p ∧ PositivityFloor ε p ∧ BudgetBalance B p} :=
    hprob.inter (hfloor.inter hbudget)
  by_cases hadm : EpsilonAdmissible ε
  · have heq :
        feasibleSet (I := I) ε B =
          {p : I → ℝ | ProbVector p ∧ PositivityFloor ε p ∧ BudgetBalance B p} := by
      ext p
      constructor
      · intro hp
        exact ⟨hp.prob, hp.floor, hp.budget⟩
      · intro hp
        exact ⟨hp.1, hadm, hp.2.1, hp.2.2⟩
    simpa [heq] using hclosed
  · have heq : feasibleSet (I := I) ε B = (∅ : Set (I → ℝ)) := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      exact hadm hp.admissible
    rw [heq]
    exact isClosed_empty

private lemma feasibleSet_compact (ε B : ℝ) :
    IsCompact (feasibleSet (I := I) ε B) := by
  classical
  exact (isCompact_univ_pi (fun _ : I => isCompact_Icc)).of_isClosed_subset
    (feasibleSet_isClosed (I := I) ε B) (by
      intro p hp k _hk
      exact hp.prob k)

private lemma varEnvelope_continuousOn_feasible
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε : 0 < ε) :
    ContinuousOn E.varEnvelope (feasibleSet (I := I) ε B) := by
  classical
  let s : Set (I → ℝ) := feasibleSet (I := I) ε B
  unfold BipartiteExperiment.varEnvelope
  refine continuousOn_const.mul ?_
  refine continuousOn_finset_sum Finset.univ ?_
  intro i _
  refine continuousOn_finset_sum Finset.univ ?_
  intro j _
  unfold BipartiteExperiment.r1 BipartiteExperiment.r0 BipartiteExperiment.r10
  by_cases hij : 0 < (E.shared i j).card
  · simp [hij]
    have hprod1 : ContinuousOn (fun p : I → ℝ => ∏ k ∈ E.shared i j, p k) s := by
      refine continuousOn_finset_prod (E.shared i j) ?_
      intro k _
      exact (continuous_apply k).continuousOn
    have hprod1_ne : ∀ p ∈ s, (∏ k ∈ E.shared i j, p k) ≠ 0 := by
      intro p hp
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k _hk
      have hpk : ContinuousOn (fun p : I → ℝ => p k) s := (continuous_apply k).continuousOn
      exact ne_of_gt (lt_of_lt_of_le hε ((show FeasibleDesign ε B p from hp).floor k).1)
    have hr1 : ContinuousOn (fun p : I → ℝ => (∏ k ∈ E.shared i j, p k)⁻¹ - 1) s :=
      (hprod1.inv₀ hprod1_ne).sub continuousOn_const
    have hprod0 : ContinuousOn (fun p : I → ℝ => ∏ k ∈ E.shared i j, (1 - p k)) s := by
      refine continuousOn_finset_prod (E.shared i j) ?_
      intro k _
      fun_prop
    have hprod0_ne : ∀ p ∈ s, (∏ k ∈ E.shared i j, (1 - p k)) ≠ 0 := by
      intro p hp
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k _hk
      have h1mp_ne : 1 - p k ≠ 0 := by
        have hlt : p k < 1 := by
          linarith [((show FeasibleDesign ε B p from hp).floor k).2, hε]
        linarith
      exact h1mp_ne
    have hr0 : ContinuousOn (fun p : I → ℝ => (∏ k ∈ E.shared i j, (1 - p k))⁻¹ - 1) s :=
      (hprod0.inv₀ hprod0_ne).sub continuousOn_const
    exact (hr1.add hr0).add continuousOn_const
  · simpa [hij] using (continuousOn_const : ContinuousOn (fun _ : I → ℝ => (0 : ℝ)) s)

-- Convexity of the reciprocal exposure products was promoted to
-- `Causalean.Mathlib.Analysis.Convex.ReciprocalProduct` (`prod_inv_convexOn`,
-- `prod_one_sub_inv_convexOn`, and the `-log`-convexity helpers); these thin wrappers specialise
-- the general convex-set lemmas to the feasible box.
private lemma prod_inv_convexOn_feasible
    (ε B : ℝ) (hε : 0 < ε) (S : Finset I) :
    ConvexOn ℝ (feasibleSet (I := I) ε B)
      (fun p : I → ℝ => (∏ k ∈ S, p k)⁻¹) :=
  Causalean.Mathlib.prod_inv_convexOn (feasibleSet_convex (I := I) ε B) S
    (fun p hp k _ => lt_of_lt_of_le hε ((show FeasibleDesign ε B p from hp).floor k).1)

private lemma prod_one_sub_inv_convexOn_feasible
    (ε B : ℝ) (hε : 0 < ε) (S : Finset I) :
    ConvexOn ℝ (feasibleSet (I := I) ε B)
      (fun p : I → ℝ => (∏ k ∈ S, (1 - p k))⁻¹) :=
  Causalean.Mathlib.prod_one_sub_inv_convexOn (feasibleSet_convex (I := I) ε B) S
    (fun p hp k _ => by linarith [((show FeasibleDesign ε B p from hp).floor k).2, hε])

private lemma convexOn_finset_sum'
    {α : Type*} [DecidableEq α] (s : Set (I → ℝ)) (hs : Convex ℝ s)
    (t : Finset α) (f : α → (I → ℝ) → ℝ)
    (hf : ∀ a ∈ t, ConvexOn ℝ s (f a)) :
    ConvexOn ℝ s (fun p => ∑ a ∈ t, f a p) := by
  classical
  revert hf
  refine Finset.induction_on t ?_ ?_
  · intro hf
    simpa using
      (convexOn_const (0 : ℝ) hs :
        ConvexOn ℝ s (fun _ : I → ℝ => (0 : ℝ)))
  · intro a t hat ht hf
    have ha : ConvexOn ℝ s (f a) := hf a (Finset.mem_insert_self a t)
    have ht' : ConvexOn ℝ s (fun p => ∑ b ∈ t, f b p) := by
      exact ht (by intro b hb; exact hf b (Finset.mem_insert_of_mem hb))
    simpa [Finset.sum_insert, hat] using ha.add ht'

/-! ### Smooth envelope extension

The original envelope is singular at the coordinate hyperplanes `p_k = 0` and `p_k = 1`. The cutoff
reciprocal `recipC` (agrees with `x⁻¹` on the feasible box, globally `C¹`) was promoted to
`Causalean.Mathlib.Analysis.SmoothReciprocal` (`recipC`, `recipC_eq_inv`, `recipC_contDiff`, opened
via `Causalean.Mathlib`).
-/

namespace BipartiteExperiment

variable (E : BipartiteExperiment I O)

/-- Extends the treated-overlap kernel to all propensity vectors by replacing reciprocal probabilities with a smooth cutoff reciprocal; it agrees with the original kernel away from zero. -/
noncomputable def r1Ext (ε : ℝ) (p : I → ℝ) (i j : O) : ℝ :=
  if 0 < (E.shared i j).card then (∏ k ∈ E.shared i j, recipC ε (p k)) - 1 else 0

/-- Extends the control-overlap kernel to all propensity vectors by smoothly regularizing reciprocal control probabilities; it agrees with the original kernel away from one. -/
noncomputable def r0Ext (ε : ℝ) (p : I → ℝ) (i j : O) : ℝ :=
  if 0 < (E.shared i j).card then (∏ k ∈ E.shared i j, recipC ε (1 - p k)) - 1 else 0

/-- Defines a globally smooth extension of the variance envelope by combining the regularized treated and control overlap kernels. -/
noncomputable def varEnvelopeExt (ε : ℝ) (p : I → ℝ) : ℝ :=
  4 * (Fintype.card O : ℝ)⁻¹ *
    ∑ i, ∑ j, (E.r1Ext ε p i j + E.r0Ext ε p i j + 2 * E.r10 i j)

/-- When every treatment probability is at least half the cutoff, the regularized treated-overlap kernel equals the original treated kernel. -/
lemma r1Ext_eq_r1_of_box {ε : ℝ} (hε : 0 < ε) {p : I → ℝ}
    (hp : ∀ k, ε / 2 ≤ p k) (i j : O) :
    E.r1Ext ε p i j = E.r1 p i j := by
  unfold r1Ext BipartiteExperiment.r1
  by_cases hij : 0 < (E.shared i j).card
  · simp [hij]
    calc
      ∏ k ∈ E.shared i j, recipC ε (p k) = ∏ k ∈ E.shared i j, (p k)⁻¹ := by
        exact Finset.prod_congr rfl (by intro k _hk; exact recipC_eq_inv hε (hp k))
      _ = (∏ k ∈ E.shared i j, p k)⁻¹ := by
        rw [Finset.prod_inv_distrib]
  · simp [hij]

/-- When every control probability is at least half the cutoff, the regularized control-overlap kernel equals the original control kernel. -/
lemma r0Ext_eq_r0_of_box {ε : ℝ} (hε : 0 < ε) {p : I → ℝ}
    (hp : ∀ k, ε / 2 ≤ 1 - p k) (i j : O) :
    E.r0Ext ε p i j = E.r0 p i j := by
  unfold r0Ext BipartiteExperiment.r0
  by_cases hij : 0 < (E.shared i j).card
  · simp [hij]
    calc
      ∏ k ∈ E.shared i j, recipC ε (1 - p k) =
          ∏ k ∈ E.shared i j, (1 - p k)⁻¹ := by
        exact Finset.prod_congr rfl (by intro k _hk; exact recipC_eq_inv hε (hp k))
      _ = (∏ k ∈ E.shared i j, (1 - p k))⁻¹ := by
        rw [Finset.prod_inv_distrib]
  · simp [hij]

/-- On the interior propensity box, the smooth extended variance envelope equals the original variance envelope. -/
lemma varEnvelopeExt_eq_varEnvelope_of_box {ε : ℝ} (hε : 0 < ε) {p : I → ℝ}
    (hplo : ∀ k, ε / 2 ≤ p k) (hphi : ∀ k, ε / 2 ≤ 1 - p k) :
    E.varEnvelopeExt ε p = E.varEnvelope p := by
  unfold varEnvelopeExt BipartiteExperiment.varEnvelope
  apply congrArg (fun z : ℝ => 4 * (Fintype.card O : ℝ)⁻¹ * z)
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [E.r1Ext_eq_r1_of_box hε hplo i j, E.r0Ext_eq_r0_of_box hε hphi i j]

/-- For a positive cutoff, the regularized treated-overlap kernel is continuously differentiable in all propensity coordinates. -/
@[fun_prop]
lemma r1Ext_contDiff (ε : ℝ) (hε : 0 < ε) (i j : O) :
    ContDiff ℝ 1 (fun p : I → ℝ => E.r1Ext ε p i j) := by
  unfold r1Ext
  by_cases hij : 0 < (E.shared i j).card
  · simp [hij]
    fun_prop (disch := assumption)
  · simp [hij]
    fun_prop

/-- For a positive cutoff, the regularized control-overlap kernel is continuously differentiable in all propensity coordinates. -/
@[fun_prop]
lemma r0Ext_contDiff (ε : ℝ) (hε : 0 < ε) (i j : O) :
    ContDiff ℝ 1 (fun p : I → ℝ => E.r0Ext ε p i j) := by
  unfold r0Ext
  by_cases hij : 0 < (E.shared i j).card
  · simp [hij]
    fun_prop (disch := assumption)
  · simp [hij]
    fun_prop

/-- For a positive cutoff, the smooth extended variance envelope is continuously differentiable in the propensity vector. -/
lemma varEnvelopeExt_contDiff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 1 (E.varEnvelopeExt ε) := by
  unfold varEnvelopeExt
  fun_prop (disch := assumption)

/-- For a positive cutoff, the smooth extended variance envelope is differentiable in the propensity vector. -/
lemma varEnvelopeExt_differentiable (ε : ℝ) (hε : 0 < ε) :
    Differentiable ℝ (E.varEnvelopeExt ε) :=
  (E.varEnvelopeExt_contDiff ε hε).differentiable (by norm_num)

end BipartiteExperiment

/-! ### Euclidean transport for the optlib finite-dimensional KKT theorem -/

/-- Re-expresses a propensity vector indexed by interventions as a vector in finite-dimensional Euclidean space. -/
noncomputable def designToEuclidean (p : I → ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card I)) :=
  (EuclideanSpace.equiv (Fin (Fintype.card I)) ℝ).symm
    (fun a => p ((Fintype.equivFin I).symm a))

/-- Re-expresses a finite-dimensional Euclidean vector as a propensity vector indexed by interventions. -/
noncomputable def euclideanToDesign (x : EuclideanSpace ℝ (Fin (Fintype.card I))) :
    I → ℝ :=
  fun k => x ((Fintype.equivFin I) k)

/-- Converting a propensity vector to Euclidean coordinates and back recovers every original propensity. -/
@[simp]
lemma euclideanToDesign_designToEuclidean (p : I → ℝ) (k : I) :
    euclideanToDesign (I := I) (designToEuclidean p) k = p k := by
  simp [euclideanToDesign, designToEuclidean]

/-- Converting a Euclidean vector to a propensity vector and back recovers the original Euclidean vector. -/
@[simp]
lemma designToEuclidean_euclideanToDesign
    (x : EuclideanSpace ℝ (Fin (Fintype.card I))) :
    designToEuclidean (euclideanToDesign (I := I) x) = x := by
  ext a
  simp [euclideanToDesign, designToEuclidean]

/-- Expresses one quarter of the smooth extended variance envelope as a function on Euclidean coordinates. -/
noncomputable def transportedEnvelopeExt
    (E : BipartiteExperiment I O) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (Fintype.card I))) : ℝ :=
  E.varEnvelopeExt ε (euclideanToDesign (I := I) x) / 4

/-- For a positive cutoff, the Euclidean-coordinate version of the smooth extended envelope is differentiable. -/
lemma transportedEnvelopeExt_differentiable
    (E : BipartiteExperiment I O) (ε : ℝ) (hε : 0 < ε) :
    Differentiable ℝ (transportedEnvelopeExt (I := I) E ε) := by
  unfold transportedEnvelopeExt
  have hobj : Differentiable ℝ (E.varEnvelopeExt ε) :=
    E.varEnvelopeExt_differentiable ε hε
  have hcoord :
      Differentiable ℝ
        (fun x : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
          euclideanToDesign (I := I) x) := by
    unfold euclideanToDesign
    fun_prop
  have hcomp :
      Differentiable ℝ
        (fun x : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
          E.varEnvelopeExt ε (euclideanToDesign (I := I) x)) := by
    simpa [Function.comp_def] using hobj.comp hcoord
  simpa [div_eq_mul_inv] using hcomp.mul_const ((4 : ℝ)⁻¹)

private lemma deriv_prod_inv_coord_line
    (S : Finset I) (p : I → ℝ) (k : I) (hpk : p k ≠ 0) :
    deriv (fun t : ℝ => ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹) 0 =
      if k ∈ S then - (∏ l ∈ S, (p l)⁻¹) * (p k)⁻¹ else 0 := by
  classical
  by_cases hk : k ∈ S
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹)
          = fun t : ℝ => (p k + t)⁻¹ * ∏ l ∈ S \ {k}, (p l)⁻¹ := by
      funext t
      calc
        ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹
            = (p k + t)⁻¹ * ∏ l ∈ S \ {k},
                (p l + (if l = k then t else 0))⁻¹ := by
              rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
              simp
        _ = (p k + t)⁻¹ * ∏ l ∈ S \ {k}, (p l)⁻¹ := by
              congr 1
              apply Finset.prod_congr rfl
              intro l hl
              have hlk : l ≠ k := by
                intro h
                subst h
                simp at hl
              simp [hlk]
    rw [hfun]
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => (p k + t)⁻¹) 0 := by
      have hlin : DifferentiableAt ℝ (fun t : ℝ => p k + t) 0 := by fun_prop
      exact hlin.inv (by simpa using hpk)
    have hderiv_inv : deriv (fun t : ℝ => (p k + t)⁻¹) 0 = -1 / (p k) ^ 2 := by
      have hlin : HasDerivAt (fun t : ℝ => p k + t) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (p k)
      have h := hlin.inv (by simpa using hpk)
      simpa using h.deriv
    rw [deriv_mul_const hdiff, hderiv_inv, if_pos hk]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
    field_simp [hpk]
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹)
          = fun _t : ℝ => ∏ l ∈ S, (p l)⁻¹ := by
      funext t
      apply Finset.prod_congr rfl
      intro l hl
      have hlk : l ≠ k := by intro h; subst h; exact hk hl
      simp [hlk]
    rw [hfun, deriv_const, if_neg hk]

private lemma differentiableAt_prod_inv_coord_line
    (S : Finset I) (p : I → ℝ) (k : I) (hpk : p k ≠ 0) :
    DifferentiableAt ℝ (fun t : ℝ => ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹) 0 := by
  classical
  by_cases hk : k ∈ S
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹)
          = fun t : ℝ => (p k + t)⁻¹ * ∏ l ∈ S \ {k}, (p l)⁻¹ := by
      funext t
      calc
        ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹
            = (p k + t)⁻¹ * ∏ l ∈ S \ {k},
                (p l + (if l = k then t else 0))⁻¹ := by
              rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
              simp
        _ = (p k + t)⁻¹ * ∏ l ∈ S \ {k}, (p l)⁻¹ := by
              congr 1
              apply Finset.prod_congr rfl
              intro l hl
              have hlk : l ≠ k := by
                intro h
                subst h
                simp at hl
              simp [hlk]
    rw [hfun]
    have hlin : DifferentiableAt ℝ (fun t : ℝ => p k + t) 0 := by fun_prop
    exact (hlin.inv (by simpa using hpk)).mul (differentiableAt_const _)
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (p l + (if l = k then t else 0))⁻¹)
          = fun _t : ℝ => ∏ l ∈ S, (p l)⁻¹ := by
      funext t
      apply Finset.prod_congr rfl
      intro l hl
      have hlk : l ≠ k := by intro h; subst h; exact hk hl
      simp [hlk]
    rw [hfun]
    exact differentiableAt_const _

private lemma deriv_prod_one_sub_inv_coord_line
    (S : Finset I) (p : I → ℝ) (k : I) (hpk : 1 - p k ≠ 0) :
    deriv (fun t : ℝ => ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹) 0 =
      if k ∈ S then (∏ l ∈ S, (1 - p l)⁻¹) * (1 - p k)⁻¹ else 0 := by
  classical
  by_cases hk : k ∈ S
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹)
          = fun t : ℝ => (1 - p k - t)⁻¹ * ∏ l ∈ S \ {k}, (1 - p l)⁻¹ := by
      funext t
      calc
        ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹
            = (1 - (p k + t))⁻¹ * ∏ l ∈ S \ {k},
                (1 - (p l + (if l = k then t else 0)))⁻¹ := by
              rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
              simp
        _ = (1 - p k - t)⁻¹ * ∏ l ∈ S \ {k}, (1 - p l)⁻¹ := by
              congr 1
              · ring
              · apply Finset.prod_congr rfl
                intro l hl
                have hlk : l ≠ k := by
                  intro h
                  subst h
                  simp at hl
                simp [hlk]
    rw [hfun]
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => (1 - p k - t)⁻¹) 0 := by
      have hlin : DifferentiableAt ℝ (fun t : ℝ => 1 - p k - t) 0 := by fun_prop
      exact hlin.inv (by simpa using hpk)
    have hderiv_inv :
        deriv (fun t : ℝ => (1 - p k - t)⁻¹) 0 = 1 / (1 - p k) ^ 2 := by
      have hlin : HasDerivAt (fun t : ℝ => 1 - p k - t) (-1) 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (1 - p k)).sub (hasDerivAt_id (0 : ℝ))
      have h := hlin.inv (by simpa using hpk)
      simpa [div_eq_mul_inv] using h.deriv
    rw [deriv_mul_const hdiff, hderiv_inv, if_pos hk]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
    field_simp [hpk]
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹)
          = fun _t : ℝ => ∏ l ∈ S, (1 - p l)⁻¹ := by
      funext t
      apply Finset.prod_congr rfl
      intro l hl
      have hlk : l ≠ k := by intro h; subst h; exact hk hl
      simp [hlk]
    rw [hfun, deriv_const, if_neg hk]

private lemma differentiableAt_prod_one_sub_inv_coord_line
    (S : Finset I) (p : I → ℝ) (k : I) (hpk : 1 - p k ≠ 0) :
    DifferentiableAt ℝ
      (fun t : ℝ => ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹) 0 := by
  classical
  by_cases hk : k ∈ S
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹)
          = fun t : ℝ => (1 - p k - t)⁻¹ * ∏ l ∈ S \ {k}, (1 - p l)⁻¹ := by
      funext t
      calc
        ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹
            = (1 - (p k + t))⁻¹ * ∏ l ∈ S \ {k},
                (1 - (p l + (if l = k then t else 0)))⁻¹ := by
              rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
              simp
        _ = (1 - p k - t)⁻¹ * ∏ l ∈ S \ {k}, (1 - p l)⁻¹ := by
              congr 1
              · ring
              · apply Finset.prod_congr rfl
                intro l hl
                have hlk : l ≠ k := by
                  intro h
                  subst h
                  simp at hl
                simp [hlk]
    rw [hfun]
    have hlin : DifferentiableAt ℝ (fun t : ℝ => 1 - p k - t) 0 := by fun_prop
    exact (hlin.inv (by simpa using hpk)).mul (differentiableAt_const _)
  · have hfun :
        (fun t : ℝ => ∏ l ∈ S, (1 - (p l + (if l = k then t else 0)))⁻¹)
          = fun _t : ℝ => ∏ l ∈ S, (1 - p l)⁻¹ := by
      funext t
      apply Finset.prod_congr rfl
      intro l hl
      have hlk : l ≠ k := by intro h; subst h; exact hk hl
      simp [hlk]
    rw [hfun]
    exact differentiableAt_const _

private lemma deriv_r1_coord_line
    (E : BipartiteExperiment I O) (p : I → ℝ) (k : I) (hpk : p k ≠ 0) (i j : O) :
    deriv (fun t : ℝ => E.r1 (fun l => p l + (if l = k then t else 0)) i j) 0 =
      if k ∈ E.shared i j then - (∏ l ∈ E.shared i j, (p l)⁻¹) * (p k)⁻¹ else 0 := by
  classical
  unfold BipartiteExperiment.r1
  by_cases hcard : 0 < (E.shared i j).card
  · simp only [hcard, ↓reduceIte, Finset.prod_inv_distrib, neg_mul]
    rw [deriv_sub_const]
    have hfun :
        (fun t : ℝ => (∏ x ∈ E.shared i j, (p x + (if x = k then t else 0)))⁻¹)
          = fun t : ℝ => ∏ x ∈ E.shared i j,
              (p x + (if x = k then t else 0))⁻¹ := by
      funext t
      rw [Finset.prod_inv_distrib]
    rw [hfun, deriv_prod_inv_coord_line (E.shared i j) p k hpk]
    by_cases hk : k ∈ E.shared i j <;> simp [hk, Finset.prod_inv_distrib]
  · have hknot : k ∉ E.shared i j := by
      intro hk
      exact hcard (Finset.card_pos.mpr ⟨k, hk⟩)
    simp [hcard, hknot]

private lemma differentiableAt_r1_coord_line
    (E : BipartiteExperiment I O) (p : I → ℝ) (k : I) (hpk : p k ≠ 0) (i j : O) :
    DifferentiableAt ℝ
      (fun t : ℝ => E.r1 (fun l => p l + (if l = k then t else 0)) i j) 0 := by
  classical
  unfold BipartiteExperiment.r1
  by_cases hcard : 0 < (E.shared i j).card
  · simp only [hcard, ↓reduceIte, Finset.prod_inv_distrib]
    have hfun :
        (fun t : ℝ => (∏ x ∈ E.shared i j, (p x + (if x = k then t else 0)))⁻¹ - 1)
          = fun t : ℝ =>
              (∏ x ∈ E.shared i j, (p x + (if x = k then t else 0))⁻¹) - 1 := by
      funext t
      rw [Finset.prod_inv_distrib]
    rw [hfun]
    exact (differentiableAt_prod_inv_coord_line (E.shared i j) p k hpk).sub
      (differentiableAt_const 1)
  · simp [hcard]

private lemma deriv_r0_coord_line
    (E : BipartiteExperiment I O) (p : I → ℝ) (k : I) (hpk : 1 - p k ≠ 0) (i j : O) :
    deriv (fun t : ℝ => E.r0 (fun l => p l + (if l = k then t else 0)) i j) 0 =
      if k ∈ E.shared i j then
        (∏ l ∈ E.shared i j, (1 - p l)⁻¹) * (1 - p k)⁻¹
      else 0 := by
  classical
  unfold BipartiteExperiment.r0
  by_cases hcard : 0 < (E.shared i j).card
  · simp only [hcard, ↓reduceIte, Finset.prod_inv_distrib, neg_mul]
    rw [deriv_sub_const]
    have hfun :
        (fun t : ℝ =>
            (∏ x ∈ E.shared i j, (1 - (p x + (if x = k then t else 0))))⁻¹)
          = fun t : ℝ => ∏ x ∈ E.shared i j,
              (1 - (p x + (if x = k then t else 0)))⁻¹ := by
      funext t
      rw [Finset.prod_inv_distrib]
    rw [hfun, deriv_prod_one_sub_inv_coord_line (E.shared i j) p k hpk]
    by_cases hk : k ∈ E.shared i j <;> simp [hk, Finset.prod_inv_distrib]
  · have hknot : k ∉ E.shared i j := by
      intro hk
      exact hcard (Finset.card_pos.mpr ⟨k, hk⟩)
    simp [hcard, hknot]

private lemma differentiableAt_r0_coord_line
    (E : BipartiteExperiment I O) (p : I → ℝ) (k : I) (hpk : 1 - p k ≠ 0) (i j : O) :
    DifferentiableAt ℝ
      (fun t : ℝ => E.r0 (fun l => p l + (if l = k then t else 0)) i j) 0 := by
  classical
  unfold BipartiteExperiment.r0
  by_cases hcard : 0 < (E.shared i j).card
  · simp only [hcard, ↓reduceIte, Finset.prod_inv_distrib]
    have hfun :
        (fun t : ℝ =>
            (∏ x ∈ E.shared i j, (1 - (p x + (if x = k then t else 0))))⁻¹ - 1)
          = fun t : ℝ =>
              (∏ x ∈ E.shared i j, (1 - (p x + (if x = k then t else 0)))⁻¹) - 1 := by
      funext t
      rw [Finset.prod_inv_distrib]
    rw [hfun]
    exact (differentiableAt_prod_one_sub_inv_coord_line (E.shared i j) p k hpk).sub
      (differentiableAt_const 1)
  · simp [hcard]

/-- Coordinate-line derivative of the normalized envelope: the partial derivative of
`V_env/4` in coordinate `k` at a feasible `p` is exactly the gradient score `envelopeGrad p k`.
Made public (was `private`) so the `EnvelopeLineC2Data` discharge in `Helpers/EnvelopeCalculus`
can assemble the directional derivative along `e_b - e_a` from the two coordinate partials. -/
lemma deriv_varEnvelope_div_four_coord_line
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε : 0 < ε) {p : I → ℝ}
    (hp : p ∈ feasibleSet (I := I) ε B) (k : I) :
    deriv
        (fun t : ℝ =>
          E.varEnvelope (fun l => p l + (if l = k then t else 0)) / 4)
        0 =
      E.envelopeGrad p k := by
  classical
  have hpk : p k ≠ 0 := by
    have hfloor := (show FeasibleDesign ε B p from hp).floor k
    exact ne_of_gt (lt_of_lt_of_le hε hfloor.1)
  have h1pk : 1 - p k ≠ 0 := by
    have hfloor := (show FeasibleDesign ε B p from hp).floor k
    exact ne_of_gt (by linarith [hfloor.2, hε])
  unfold BipartiteExperiment.varEnvelope BipartiteExperiment.envelopeGrad
  have hsum :
      deriv
          (fun t : ℝ =>
            ∑ i, ∑ j,
              (E.r1 (fun l => p l + (if l = k then t else 0)) i j +
                E.r0 (fun l => p l + (if l = k then t else 0)) i j +
                2 * E.r10 i j))
          0 =
        ∑ i, ∑ j,
          (if k ∈ E.shared i j then
            - (∏ l ∈ E.shared i j, (p l)⁻¹) * (p k)⁻¹ +
              (∏ l ∈ E.shared i j, (1 - p l)⁻¹) * (1 - p k)⁻¹
          else 0) := by
    rw [deriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [deriv_fun_sum]
      · apply Finset.sum_congr rfl
        intro j _hj
        have hterm :
            (fun t : ℝ =>
              E.r1 (fun l => p l + (if l = k then t else 0)) i j +
                E.r0 (fun l => p l + (if l = k then t else 0)) i j +
                2 * E.r10 i j)
              =
            (fun t : ℝ => E.r1 (fun l => p l + (if l = k then t else 0)) i j) +
              (fun t : ℝ => E.r0 (fun l => p l + (if l = k then t else 0)) i j) +
              (fun _t : ℝ => 2 * E.r10 i j) := by
          rfl
        rw [hterm]
        rw [deriv_add]
        · rw [deriv_add]
          · rw [deriv_const]
            rw [deriv_r1_coord_line E p k hpk i j,
              deriv_r0_coord_line E p k h1pk i j]
            by_cases hk : k ∈ E.shared i j <;> simp [hk]
          · exact differentiableAt_r1_coord_line E p k hpk i j
          · exact differentiableAt_r0_coord_line E p k h1pk i j
        · exact (differentiableAt_r1_coord_line E p k hpk i j).add
            (differentiableAt_r0_coord_line E p k h1pk i j)
        · exact differentiableAt_const (2 * E.r10 i j)
      · intro j _hj
        exact ((differentiableAt_r1_coord_line E p k hpk i j).add
          (differentiableAt_r0_coord_line E p k h1pk i j)).add
          (differentiableAt_const (2 * E.r10 i j))
    · intro i _hi
      exact DifferentiableAt.fun_sum fun j _hj =>
        ((differentiableAt_r1_coord_line E p k hpk i j).add
          (differentiableAt_r0_coord_line E p k h1pk i j)).add
          (differentiableAt_const (2 * E.r10 i j))
  rw [deriv_div_const]
  rw [deriv_const_mul]
  · rw [hsum]
    ring
  · exact DifferentiableAt.fun_sum fun i _hi =>
      DifferentiableAt.fun_sum fun j _hj =>
        ((differentiableAt_r1_coord_line E p k hpk i j).add
          (differentiableAt_r0_coord_line E p k h1pk i j)).add
          (differentiableAt_const (2 * E.r10 i j))

-- @node: lemma:envelopeGrad-eq-gradient-varEnvelopeExt
/-- At every feasible design, the Euclidean gradient of the transported smooth envelope equals the stated envelope gradient in each intervention coordinate. -/
lemma envelopeGrad_eq_gradient_varEnvelopeExt
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε : 0 < ε) {p : I → ℝ}
    (hp : p ∈ feasibleSet (I := I) ε B) (k : I) :
    (gradient (transportedEnvelopeExt (I := I) E ε) (designToEuclidean p))
        ((Fintype.equivFin I) k) =
      E.envelopeGrad p k := by
  classical
  have hcoord :=
    gradient_coord_eq_deriv
      (transportedEnvelopeExt (I := I) E ε)
      (designToEuclidean p) ((Fintype.equivFin I) k)
      ((transportedEnvelopeExt_differentiable (I := I) E ε hε).differentiableAt)
  rw [hcoord]
  have hline :
      (fun t : ℝ =>
          transportedEnvelopeExt (I := I) E ε
            (designToEuclidean p +
              t • EuclideanSpace.single ((Fintype.equivFin I) k) (1 : ℝ)))
        =ᶠ[𝓝 (0 : ℝ)]
        fun t : ℝ =>
          E.varEnvelope (fun l => p l + (if l = k then t else 0)) / 4 := by
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-(ε / 2)) (ε / 2) :=
      Ioo_mem_nhds (by linarith [hε]) (by linarith [hε])
    filter_upwards [hsmall] with t ht
    unfold transportedEnvelopeExt
    have hdesign :
        euclideanToDesign (I := I)
          (designToEuclidean p +
            t • EuclideanSpace.single ((Fintype.equivFin I) k) (1 : ℝ))
          =
        fun l => p l + (if l = k then t else 0) := by
      funext l
      simp [euclideanToDesign, designToEuclidean]
    rw [hdesign]
    congr 1
    apply E.varEnvelopeExt_eq_varEnvelope_of_box hε
    · intro l
      by_cases h : l = k
      · have hfloor := (show FeasibleDesign ε B p from hp).floor l
        have hfloor_k : ε ≤ p k ∧ p k ≤ 1 - ε := by simpa [h] using hfloor
        simp [h]
        linarith [hfloor_k.1, ht.1]
      · have hfloor := (show FeasibleDesign ε B p from hp).floor l
        simp [h]
        linarith [hfloor.1, hε]
    · intro l
      by_cases h : l = k
      · have hfloor := (show FeasibleDesign ε B p from hp).floor l
        have hfloor_k : ε ≤ p k ∧ p k ≤ 1 - ε := by simpa [h] using hfloor
        simp [h]
        linarith [hfloor_k.2, ht.2]
      · have hfloor := (show FeasibleDesign ε B p from hp).floor l
        simp [h]
        linarith [hfloor.2, hε]
  rw [hline.deriv_eq]
  exact deriv_varEnvelope_div_four_coord_line E ε B hε hp k

/-! ### Optlib constrained problem for the transported design program -/

private noncomputable def optBudgetIndex (n : ℕ) : ℕ := 2 * n

private noncomputable def optEqIndexSet (n : ℕ) : Finset ℕ := {optBudgetIndex n}

private noncomputable def optBoxIndexSet (n : ℕ) : Finset ℕ := Finset.range (2 * n)

private noncomputable def optBudgetConstraint {n : ℕ} (B : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ a : Fin n, x a) - B

private noncomputable def optBoxConstraint {n : ℕ} (ε : ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if h : j < n then x ⟨j, h⟩ - ε
  else if h' : j - n < n then 1 - ε - x ⟨j - n, h'⟩
  else 1

private noncomputable def optDesignProblem
    (E : BipartiteExperiment I O) (ε B : ℝ) :
    Constrained_OptimizationProblem
      (EuclideanSpace ℝ (Fin (Fintype.card I)))
      (optEqIndexSet (Fintype.card I)) (optBoxIndexSet (Fintype.card I)) :=
  { domain := univ
    equality_constraints := fun _ x => optBudgetConstraint B x
    inequality_constraints := fun j x => optBoxConstraint ε j x
    eq_ine_not_intersect := by
      classical
      simp [optEqIndexSet, optBoxIndexSet, optBudgetIndex]
    objective := transportedEnvelopeExt (I := I) E ε }

private lemma optBoxConstraint_lower {n : ℕ} (ε : ℝ)
    (a : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    optBoxConstraint ε a.val x = x a - ε := by
  simp [optBoxConstraint, a.2]

private lemma optBoxConstraint_upper {n : ℕ} (ε : ℝ)
    (a : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    optBoxConstraint ε (n + a.val) x = 1 - ε - x a := by
  have hnot : ¬ n + a.val < n := by omega
  have hlt : n + a.val - n < n := by omega
  have hfin : (⟨n + a.val - n, hlt⟩ : Fin n) = a := by
    ext
    simp
  simp [optBoxConstraint, hnot, hlt, hfin]

private lemma optBoxConstraint_mem_range_upper_lt {n j : ℕ}
    (hj : j ∈ optBoxIndexSet n) (hjn : ¬ j < n) : j - n < n := by
  simp [optBoxIndexSet] at hj
  omega

private lemma sum_fin_eq_sum_design
    (x : EuclideanSpace ℝ (Fin (Fintype.card I))) :
    (∑ a : Fin (Fintype.card I), x a) =
      ∑ k : I, euclideanToDesign (I := I) x k := by
  classical
  simpa [euclideanToDesign] using
    (Finset.sum_equiv (Fintype.equivFin I).symm
      (s := Finset.univ) (t := Finset.univ)
      (f := fun a : Fin (Fintype.card I) => x a)
      (g := fun k : I => x ((Fintype.equivFin I) k))
      (by simp) (by intro a _; simp))

private lemma optLower_mem_boxIndexSet (k : I) :
    ((Fintype.equivFin I) k).val ∈ optBoxIndexSet (Fintype.card I) := by
  simp [optBoxIndexSet]
  omega

private lemma optUpper_mem_boxIndexSet (k : I) :
    Fintype.card I + ((Fintype.equivFin I) k).val ∈
      optBoxIndexSet (Fintype.card I) := by
  simp [optBoxIndexSet]
  omega

private lemma feasible_of_optFeasPoint
    {ε B : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (x : EuclideanSpace ℝ (Fin (Fintype.card I)))
    (hx : (optDesignProblem (I := I) (O := O) E ε B).FeasPoint x) :
    euclideanToDesign (I := I) x ∈ feasibleSet (I := I) ε B := by
  classical
  rcases hx with ⟨_hdom, heq, hineq⟩
  refine ⟨?_, ⟨hε, hε2⟩, ?_, ?_⟩
  · intro k
    have hlo := hineq ((Fintype.equivFin I) k).val (optLower_mem_boxIndexSet (I := I) k)
    have hhi := hineq (Fintype.card I + ((Fintype.equivFin I) k).val)
      (optUpper_mem_boxIndexSet (I := I) k)
    simp [optDesignProblem, optBoxConstraint_lower, optBoxConstraint_upper,
      euclideanToDesign] at hlo hhi
    constructor
    · simp [euclideanToDesign]
      linarith [hε]
    · simp [euclideanToDesign]
      linarith [hε]
  · intro k
    have hlo := hineq ((Fintype.equivFin I) k).val (optLower_mem_boxIndexSet (I := I) k)
    have hhi := hineq (Fintype.card I + ((Fintype.equivFin I) k).val)
      (optUpper_mem_boxIndexSet (I := I) k)
    simp [optDesignProblem, optBoxConstraint_lower, optBoxConstraint_upper,
      euclideanToDesign] at hlo hhi
    constructor
    · simp [euclideanToDesign]
      linarith
    · simp [euclideanToDesign]
      linarith
  · dsimp [BudgetBalance]
    have hbudget := heq (optBudgetIndex (Fintype.card I)) (by simp [optEqIndexSet])
    simp [optDesignProblem, optBudgetConstraint] at hbudget
    rw [← sum_fin_eq_sum_design (I := I) x]
    linarith

private lemma optFeasPoint_of_feasible
    {ε B : ℝ} {p : I → ℝ} (hp : p ∈ feasibleSet (I := I) ε B) :
    (optDesignProblem (I := I) (O := O) E ε B).FeasPoint (designToEuclidean p) := by
  classical
  refine ⟨by simp [optDesignProblem], ?_, ?_⟩
  · intro i hi
    simp [optDesignProblem, optEqIndexSet, optBudgetConstraint] at hi ⊢
    rw [sum_fin_eq_sum_design (I := I) (designToEuclidean p)]
    simp [euclideanToDesign_designToEuclidean]
    rw [(show FeasibleDesign ε B p from hp).budget]
    ring
  · intro j hj
    by_cases hjlo : j < Fintype.card I
    · have hfloor := (show FeasibleDesign ε B p from hp).floor
        ((Fintype.equivFin I).symm ⟨j, hjlo⟩)
      simp [optDesignProblem, optBoxConstraint, hjlo, euclideanToDesign, designToEuclidean]
      linarith [hfloor.1]
    · have hjhi : j - Fintype.card I < Fintype.card I :=
        optBoxConstraint_mem_range_upper_lt (n := Fintype.card I) hj hjlo
      have hfloor := (show FeasibleDesign ε B p from hp).floor
        ((Fintype.equivFin I).symm ⟨j - Fintype.card I, hjhi⟩)
      simp [optDesignProblem, optBoxConstraint, hjlo, hjhi, euclideanToDesign, designToEuclidean]
      linarith [hfloor.2]

private lemma optBoxConstraint_contDiffAt {n : ℕ} (ε : ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ 1 (optBoxConstraint ε j) x := by
  unfold optBoxConstraint
  by_cases hjlo : j < n
  · simp [hjlo]
    fun_prop
  · simp [hjlo]
    by_cases hjhi : j - n < n
    · simp [hjhi]
      fun_prop
    · simp [hjhi]
      fun_prop

private lemma optBudgetConstraint_contDiffAt {n : ℕ} (B : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ 1 (optBudgetConstraint B) x := by
  unfold optBudgetConstraint
  fun_prop

private lemma optDesignProblem_LinearCQ
    (E : BipartiteExperiment I O) (ε B : ℝ)
    (x : EuclideanSpace ℝ (Fin (Fintype.card I))) :
    (optDesignProblem (I := I) E ε B).LinearCQ x := by
  classical
  constructor
  · intro i hi
    rw [Constrained_OptimizationProblem.IsLinear_iff']
    refine ⟨∑ a : Fin (Fintype.card I), EuclideanSpace.single a (1 : ℝ), -B, ?_⟩
    ext y
    simp [optDesignProblem, optBudgetConstraint]
    have hinner :
        ⟪∑ a : Fin (Fintype.card I), EuclideanSpace.single a (1 : ℝ), y⟫_ℝ =
          ∑ a : Fin (Fintype.card I), y a := by
      rw [real_inner_comm, inner_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      simpa using EuclideanSpace.inner_single_right a (1 : ℝ) y
    rw [hinner]
    ring
  · intro j hj
    rw [Constrained_OptimizationProblem.IsLinear_iff']
    by_cases hjlo : j < Fintype.card I
    · refine ⟨EuclideanSpace.single ⟨j, hjlo⟩ (1 : ℝ), -ε, ?_⟩
      ext y
      rw [show ⟪EuclideanSpace.single ⟨j, hjlo⟩ (1 : ℝ), y⟫_ℝ = y ⟨j, hjlo⟩ by
        simpa using EuclideanSpace.inner_single_left ⟨j, hjlo⟩ (1 : ℝ) y]
      have hfin : (⟨j, by exact hjlo⟩ : Fin (Fintype.card I)) = ⟨j, hjlo⟩ := by
        ext
        rfl
      simp [optDesignProblem, optBoxConstraint, hjlo, hfin]
      ring
    · by_cases hjhi : j - Fintype.card I < Fintype.card I
      · refine ⟨-EuclideanSpace.single ⟨j - Fintype.card I, hjhi⟩ (1 : ℝ), 1 - ε, ?_⟩
        ext y
        rw [show ⟪-EuclideanSpace.single ⟨j - Fintype.card I, hjhi⟩ (1 : ℝ), y⟫_ℝ =
            -y ⟨j - Fintype.card I, hjhi⟩ by
          rw [inner_neg_left]
          simpa using congrArg Neg.neg
            (EuclideanSpace.inner_single_left ⟨j - Fintype.card I, hjhi⟩ (1 : ℝ) y)]
        simp [optDesignProblem, optBoxConstraint, hjlo, hjhi, sub_eq_add_neg]
        ring
      · refine ⟨0, 1, ?_⟩
        ext y
        simp [optDesignProblem, optBoxConstraint, hjlo, hjhi]

private lemma gradient_optBudgetConstraint {n : ℕ} (B : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (optBudgetConstraint B) x =
      ∑ a : Fin n, EuclideanSpace.single a (1 : ℝ) := by
  let A : EuclideanSpace ℝ (Fin n) := ∑ a : Fin n, EuclideanSpace.single a (1 : ℝ)
  have hfun : optBudgetConstraint B = fun y : EuclideanSpace ℝ (Fin n) => ⟪A, y⟫_ℝ + (-B) := by
    ext y
    simp [optBudgetConstraint, A]
    have hinner : ⟪∑ a : Fin n, EuclideanSpace.single a (1 : ℝ), y⟫_ℝ = ∑ a : Fin n, y a := by
      rw [real_inner_comm, inner_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      simpa using EuclideanSpace.inner_single_right a (1 : ℝ) y
    rw [hinner]
    ring
  rw [hfun, gradient_add_const]
  exact (gradient_of_inner_const x A).gradient

set_option maxHeartbeats 1000000 in
private lemma gradient_optBoxConstraint {n : ℕ} (ε : ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (optBoxConstraint ε j) x =
      if h : j < n then EuclideanSpace.single ⟨j, h⟩ (1 : ℝ)
      else if h' : j - n < n then -EuclideanSpace.single ⟨j - n, h'⟩ (1 : ℝ)
      else 0 := by
  by_cases hjlo : j < n
  · have hfun : optBoxConstraint ε j =
        fun y : EuclideanSpace ℝ (Fin n) =>
          ⟪EuclideanSpace.single ⟨j, hjlo⟩ (1 : ℝ), y⟫_ℝ + (-ε) := by
      ext y
      rw [show ⟪EuclideanSpace.single ⟨j, hjlo⟩ (1 : ℝ), y⟫_ℝ = y ⟨j, hjlo⟩ by
        simpa using EuclideanSpace.inner_single_left ⟨j, hjlo⟩ (1 : ℝ) y]
      have hfin : (⟨j, by exact hjlo⟩ : Fin n) = ⟨j, hjlo⟩ := by
        ext
        rfl
      simp [optBoxConstraint, hjlo, hfin]
      ring
    rw [hfun, gradient_add_const]
    simp [hjlo]
    exact (gradient_of_inner_const x (EuclideanSpace.single ⟨j, hjlo⟩ (1 : ℝ))).gradient
  · by_cases hjhi : j - n < n
    · have hfun : optBoxConstraint ε j =
          fun y : EuclideanSpace ℝ (Fin n) =>
            -⟪EuclideanSpace.single ⟨j - n, hjhi⟩ (1 : ℝ), y⟫_ℝ + (1 - ε) := by
        ext y
        rw [show ⟪EuclideanSpace.single ⟨j - n, hjhi⟩ (1 : ℝ), y⟫_ℝ =
            y ⟨j - n, hjhi⟩ by
          simpa using EuclideanSpace.inner_single_left ⟨j - n, hjhi⟩ (1 : ℝ) y]
        simp [optBoxConstraint, hjlo, hjhi, sub_eq_add_neg]
        ring
      rw [hfun, gradient_add_const]
      rw [gradient_neg]
      rw [(gradient_of_inner_const x
        (EuclideanSpace.single ⟨j - n, hjhi⟩ (1 : ℝ))).gradient]
      simp [hjlo, hjhi]
    · have hfun : optBoxConstraint ε j = fun _y : EuclideanSpace ℝ (Fin n) => (1 : ℝ) := by
        ext y
        simp [optBoxConstraint, hjlo, hjhi]
      rw [hfun]
      simp [hjlo, hjhi]

@[simp]
private lemma gradient_const_mul_optBudgetConstraint {n : ℕ} (B c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun m : EuclideanSpace ℝ (Fin n) => c * optBudgetConstraint B m) x =
      c • ∑ a : Fin n, EuclideanSpace.single a (1 : ℝ) := by
  rw [gradient_const_mul' c ((optBudgetConstraint_contDiffAt (n := n) B x).differentiableAt
    (by norm_num))]
  rw [gradient_optBudgetConstraint]

@[simp]
private lemma gradient_const_mul_optBoxConstraint {n : ℕ} (ε c : ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun m : EuclideanSpace ℝ (Fin n) => c * optBoxConstraint ε j m) x =
      c • (if h : j < n then EuclideanSpace.single ⟨j, h⟩ (1 : ℝ)
        else if h' : j - n < n then -EuclideanSpace.single ⟨j - n, h'⟩ (1 : ℝ)
        else 0) := by
  rw [gradient_const_mul' c ((optBoxConstraint_contDiffAt (n := n) ε j x).differentiableAt
    (by norm_num))]
  rw [gradient_optBoxConstraint]

private lemma optBoxGradientCoord_sum {n : ℕ}
    (lambda2 : optBoxIndexSet n → ℝ) (a : Fin n) :
    (∑ j : optBoxIndexSet n,
      ((if h : (j : ℕ) < n then
          lambda2 j • EuclideanSpace.single ⟨(j : ℕ), h⟩ (1 : ℝ)
        else if h' : (j : ℕ) - n < n then
          -(lambda2 j • EuclideanSpace.single ⟨(j : ℕ) - n, h'⟩ (1 : ℝ))
        else 0) : EuclideanSpace ℝ (Fin n)) a) =
      lambda2 ⟨a.val, by simp [optBoxIndexSet]; omega⟩ -
        lambda2 ⟨n + a.val, by simp [optBoxIndexSet]; omega⟩ := by
  classical
  let lo : optBoxIndexSet n := ⟨a.val, by simp [optBoxIndexSet]; omega⟩
  let hi : optBoxIndexSet n := ⟨n + a.val, by simp [optBoxIndexSet]; omega⟩
  let f : optBoxIndexSet n → ℝ := fun j =>
    ((if h : (j : ℕ) < n then
        lambda2 j • EuclideanSpace.single ⟨(j : ℕ), h⟩ (1 : ℝ)
      else if h' : (j : ℕ) - n < n then
        -(lambda2 j • EuclideanSpace.single ⟨(j : ℕ) - n, h'⟩ (1 : ℝ))
      else 0) : EuclideanSpace ℝ (Fin n)) a
  have hf_lo : f lo = lambda2 lo := by
    have hfin : (⟨(lo : ℕ), by simp [lo]⟩ : Fin n) = a := by
      ext
      simp [lo]
    simp [f, lo, hfin, EuclideanSpace.single_apply]
  have hf_hi : f hi = -lambda2 hi := by
    have hnot : ¬ (hi : ℕ) < n := by
      simp [hi]
    have hlt : (hi : ℕ) - n < n := by
      simp [hi]
    have hfin : (⟨(hi : ℕ) - n, hlt⟩ : Fin n) = a := by
      ext
      simp [hi]
    simp [f, hi, hnot, hlt, hfin, EuclideanSpace.single_apply]
  have hf_zero : ∀ j : optBoxIndexSet n, j ≠ lo → j ≠ hi → f j = 0 := by
    intro j hjlo hjhi
    by_cases hj_low : (j : ℕ) < n
    · have hfin_ne : (⟨(j : ℕ), hj_low⟩ : Fin n) ≠ a := by
        intro hfin
        apply hjlo
        ext
        exact congrArg Fin.val hfin
      simp [f, hj_low, hfin_ne.symm, EuclideanSpace.single_apply]
    · by_cases hj_high : (j : ℕ) - n < n
      · have hfin_ne : (⟨(j : ℕ) - n, hj_high⟩ : Fin n) ≠ a := by
          intro hfin
          apply hjhi
          ext
          have hval : (j : ℕ) - n = a.val := congrArg Fin.val hfin
          have hjmem : (j : ℕ) < 2 * n := by
            have hjmem0 : (j : ℕ) ∈ Finset.range (2 * n) := by
              change (j : ℕ) ∈ Finset.range (2 * n)
              exact j.property
            exact Finset.mem_range.mp hjmem0
          have hnle : n ≤ (j : ℕ) := Nat.le_of_not_gt hj_low
          simp [hi]
          omega
        simp [f, hj_low, hj_high, hfin_ne.symm, EuclideanSpace.single_apply]
      · simp [f, hj_low, hj_high]
  have hhi_ne_lo : hi ≠ lo := by
    intro h
    have hval : (hi : ℕ) = (lo : ℕ) := congrArg (fun j : optBoxIndexSet n => (j : ℕ)) h
    have hnat : n + a.val = a.val := by
      simpa [hi, lo] using hval
    omega
  have hsum_ne :
      (∑ j : {j : optBoxIndexSet n // j ≠ lo}, f j) = f hi := by
    refine Fintype.sum_eq_single (⟨hi, hhi_ne_lo⟩ : {j : optBoxIndexSet n // j ≠ lo}) ?_
    intro j hj
    exact hf_zero j.1 j.2 (by
      intro h
      apply hj
      ext
      exact congrArg (fun j : optBoxIndexSet n => (j : ℕ)) h)
  have hsum_two : (∑ j : optBoxIndexSet n, f j) = f lo + f hi := by
    rw [Fintype.sum_eq_add_sum_subtype_ne f lo, hsum_ne]
  simpa [f, lo, hi, hf_lo, hf_hi, sub_eq_add_neg] using hsum_two

private lemma optBudgetGradientCoord_sum_gradient {n : ℕ} (B : ℝ)
    (lambda1 : optEqIndexSet n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (a : Fin n) :
    (∑ i : optEqIndexSet n,
      gradient (fun m : EuclideanSpace ℝ (Fin n) => lambda1 i * optBudgetConstraint B m) x) a =
      lambda1 ⟨optBudgetIndex n, by simp [optEqIndexSet]⟩ := by
  classical
  let budget : optEqIndexSet n := ⟨optBudgetIndex n, by simp [optEqIndexSet]⟩
  rw [Fintype.sum_eq_single budget]
  · have hcoord :
        (((∑ b : Fin n, EuclideanSpace.single b (1 : ℝ)) : EuclideanSpace ℝ (Fin n)) a) = 1 := by
      norm_num [EuclideanSpace.single_apply]
    simp [budget, gradient_const_mul_optBudgetConstraint, hcoord]
  · intro i hi
    exfalso
    apply hi
    ext
    have himem : (i : ℕ) = optBudgetIndex n := by
      have himem0 : (i : ℕ) ∈ optEqIndexSet n := i.property
      change (i : ℕ) ∈ ({optBudgetIndex n} : Finset ℕ) at himem0
      exact Finset.mem_singleton.mp himem0
    exact himem

private lemma optBoxGradientCoord_sum_gradient {n : ℕ} (ε : ℝ)
    (lambda2 : optBoxIndexSet n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (a : Fin n) :
    (∑ j : optBoxIndexSet n,
      gradient (fun m : EuclideanSpace ℝ (Fin n) => lambda2 j * optBoxConstraint ε (↑j) m) x) a =
      lambda2 ⟨a.val, by simp [optBoxIndexSet]; omega⟩ -
        lambda2 ⟨n + a.val, by simp [optBoxIndexSet]; omega⟩ := by
  simpa [gradient_const_mul_optBoxConstraint] using
    optBoxGradientCoord_sum (n := n) (lambda2 := lambda2) (a := a)

private lemma optLagrange_gradient_coord
    (E : BipartiteExperiment I O) (ε B : ℝ)
    (x : EuclideanSpace ℝ (Fin (Fintype.card I)))
    (hobj : DifferentiableAt ℝ (transportedEnvelopeExt (I := I) E ε) x)
    (lambda1 : optEqIndexSet (Fintype.card I) → ℝ)
    (lambda2 : optBoxIndexSet (Fintype.card I) → ℝ)
    (a : Fin (Fintype.card I)) :
    (gradient
        (fun m => (optDesignProblem (I := I) E ε B).Lagrange_function m lambda1 lambda2)
        x) a =
      (gradient (transportedEnvelopeExt (I := I) E ε) x) a
        - lambda1 ⟨optBudgetIndex (Fintype.card I), by simp [optEqIndexSet]⟩
        - lambda2 ⟨a.val, by simp [optBoxIndexSet]; omega⟩
        + lambda2 ⟨Fintype.card I + a.val, by simp [optBoxIndexSet]; omega⟩ := by
  classical
  unfold Constrained_OptimizationProblem.Lagrange_function
  simp only [optDesignProblem]
  have hbudgetDiff :
      DifferentiableAt ℝ (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
        ∑ i, lambda1 i * optBudgetConstraint B m) x := by
    apply DifferentiableAt.fun_sum
    intro i _hi
    exact ((optBudgetConstraint_contDiffAt (n := Fintype.card I) B x).differentiableAt
      (by norm_num)).const_mul (lambda1 i)
  have hboxDiff :
      DifferentiableAt ℝ (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
        ∑ j, lambda2 j * optBoxConstraint ε (↑j) m) x := by
    apply DifferentiableAt.fun_sum
    intro j _hj
    exact ((optBoxConstraint_contDiffAt (n := Fintype.card I) ε (↑j) x).differentiableAt
      (by norm_num)).const_mul (lambda2 j)
  have hsub1 :
      gradient
          (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
            (transportedEnvelopeExt (I := I) E ε m -
                (∑ i, lambda1 i * optBudgetConstraint B m)) -
              (∑ j, lambda2 j * optBoxConstraint ε (↑j) m)) x =
        gradient
            (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
              transportedEnvelopeExt (I := I) E ε m -
                (∑ i, lambda1 i * optBudgetConstraint B m)) x -
          gradient
            (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
              ∑ j, lambda2 j * optBoxConstraint ε (↑j) m) x := by
    exact gradient_sub (hobj.sub hbudgetDiff) hboxDiff
  rw [hsub1]
  have hsub2 :
      gradient
          (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
            transportedEnvelopeExt (I := I) E ε m -
              (∑ i, lambda1 i * optBudgetConstraint B m)) x =
        gradient (transportedEnvelopeExt (I := I) E ε) x -
          gradient
            (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
              ∑ i, lambda1 i * optBudgetConstraint B m) x := by
    exact gradient_sub hobj hbudgetDiff
  rw [hsub2]
  rw [gradient_sum, gradient_sum]
  · change
      (gradient (transportedEnvelopeExt (I := I) E ε) x).ofLp a -
          (∑ i : optEqIndexSet (Fintype.card I),
            gradient (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
              lambda1 i * optBudgetConstraint B m) x).ofLp a -
          (∑ j : optBoxIndexSet (Fintype.card I),
            gradient (fun m : EuclideanSpace ℝ (Fin (Fintype.card I)) =>
              lambda2 j * optBoxConstraint ε (↑j) m) x).ofLp a =
        (gradient (transportedEnvelopeExt (I := I) E ε) x).ofLp a -
          lambda1 ⟨optBudgetIndex (Fintype.card I), by simp [optEqIndexSet]⟩ -
          lambda2 ⟨a.val, by simp [optBoxIndexSet]; omega⟩ +
          lambda2 ⟨Fintype.card I + a.val, by simp [optBoxIndexSet]; omega⟩
    rw [optBudgetGradientCoord_sum_gradient (n := Fintype.card I) (B := B)
      (lambda1 := lambda1) (x := x) (a := a)]
    rw [optBoxGradientCoord_sum_gradient (n := Fintype.card I) (ε := ε)
      (lambda2 := lambda2) (x := x) (a := a)]
    ring
  · intro j _hj
    exact ((optBoxConstraint_contDiffAt (n := Fintype.card I) ε (↑j) x).differentiableAt
      (by norm_num)).const_mul (lambda2 j)
  · intro i _hi
    exact ((optBudgetConstraint_contDiffAt (n := Fintype.card I) B x).differentiableAt
      (by norm_num)).const_mul (lambda1 i)

-- @node: thm:convex-design
/-- **Convex design.** For a feasible budget `B ∈ [mε, m(1−ε)]`,
the feasible set `P_{n,B,ε}` is nonempty, compact and convex, the envelope
`V_env` is convex on it, and a minimizer exists. The multiplier/KKT certificate is
kept separate because it needs a general finite-dimensional normal-cone KKT
substrate theorem that is not currently available in Mathlib/Causalean. -/
theorem convex_design
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hBlo : (Fintype.card I : ℝ) * ε ≤ B) (hBhi : B ≤ (Fintype.card I : ℝ) * (1 - ε)) :
    (feasibleSet (I := I) ε B).Nonempty ∧
    IsCompact (feasibleSet (I := I) ε B) ∧
    Convex ℝ (feasibleSet (I := I) ε B) ∧
    ConvexOn ℝ (feasibleSet (I := I) ε B) E.varEnvelope ∧
    (∃ pstar ∈ feasibleSet (I := I) ε B,
        ∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope pstar ≤ E.varEnvelope q) ∧
    (∀ pstar ∈ feasibleSet (I := I) ε B,
        (∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope pstar ≤ E.varEnvelope q) →
        ∃ (lam : ℝ) (νp νm : I → ℝ),
          -- @realizes lambda_n(carrier `lam : ℝ`, the budget multiplier introduced by this existential)
          -- @realizes nu_{k,n}^+(carrier `νp : I → ℝ`, the upper-box multiplier introduced here)
          -- @realizes nu_{k,n}^-(carrier `νm : I → ℝ`, the lower-box multiplier introduced here)
          (∀ k, 0 ≤ νp k) ∧   -- @realizes nu_{k,n}^+(range clause pinning the space [0,∞) of ν_k^+)
          (∀ k, 0 ≤ νm k) ∧   -- @realizes nu_{k,n}^-(range clause pinning the space [0,∞) of ν_k^-)
          (∀ k, E.envelopeGrad pstar k = lam - νp k + νm k) ∧
          (∀ k, νp k * (pstar k - (1 - ε)) = 0) ∧
          (∀ k, νm k * (ε - pstar k) = 0)) := by
  classical
  have hne : (feasibleSet (I := I) ε B).Nonempty :=
    feasibleSet_nonempty (I := I) ε B hε hε2 hBlo hBhi
  have hcompact : IsCompact (feasibleSet (I := I) ε B) :=
    feasibleSet_compact (I := I) ε B
  have hconv : Convex ℝ (feasibleSet (I := I) ε B) :=
    feasibleSet_convex (I := I) ε B
  have hconvEnv : ConvexOn ℝ (feasibleSet (I := I) ε B) E.varEnvelope := by
    let P : Set (I → ℝ) := feasibleSet (I := I) ε B
    have hterm : ∀ i j : O,
        ConvexOn ℝ P (fun p : I → ℝ => E.r1 p i j + E.r0 p i j + 2 * E.r10 i j) := by
      intro i j
      have hr1 : ConvexOn ℝ P (fun p : I → ℝ => E.r1 p i j) := by
        unfold BipartiteExperiment.r1
        by_cases hij : 0 < (E.shared i j).card
        · have hraw := prod_inv_convexOn_feasible (I := I) ε B hε (E.shared i j)
          simpa [P, hij, sub_eq_add_neg] using hraw.add_const (-1)
        · simpa [P, hij] using
            (convexOn_const (0 : ℝ) hconv :
              ConvexOn ℝ (feasibleSet (I := I) ε B) (fun _ : I → ℝ => (0 : ℝ)))
      have hr0 : ConvexOn ℝ P (fun p : I → ℝ => E.r0 p i j) := by
        unfold BipartiteExperiment.r0
        by_cases hij : 0 < (E.shared i j).card
        · have hraw := prod_one_sub_inv_convexOn_feasible (I := I) ε B hε (E.shared i j)
          simpa [P, hij, sub_eq_add_neg] using hraw.add_const (-1)
        · simpa [P, hij] using
            (convexOn_const (0 : ℝ) hconv :
              ConvexOn ℝ (feasibleSet (I := I) ε B) (fun _ : I → ℝ => (0 : ℝ)))
      exact (hr1.add hr0).add (convexOn_const (2 * E.r10 i j) hconv)
    have hsum_j : ∀ i : O,
        ConvexOn ℝ P (fun p : I → ℝ =>
          ∑ j ∈ (Finset.univ : Finset O), (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j)) := by
      intro i
      exact convexOn_finset_sum' (I := I) P hconv (Finset.univ : Finset O)
        (fun j p => E.r1 p i j + E.r0 p i j + 2 * E.r10 i j)
        (by intro j _; exact hterm i j)
    have hsum : ConvexOn ℝ P (fun p : I → ℝ =>
        ∑ i ∈ (Finset.univ : Finset O),
          ∑ j ∈ (Finset.univ : Finset O), (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j)) := by
      exact convexOn_finset_sum' (I := I) P hconv (Finset.univ : Finset O)
        (fun i p => ∑ j ∈ (Finset.univ : Finset O), (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j))
        (by intro i _; exact hsum_j i)
    have hscale_nonneg : 0 ≤ 4 * (Fintype.card O : ℝ)⁻¹ := by positivity
    have hscaled := hsum.smul hscale_nonneg
    convert hscaled using 2
  have hmin :
      ∃ pstar ∈ feasibleSet (I := I) ε B,
        ∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope pstar ≤ E.varEnvelope q :=
    hcompact.exists_isMinOn hne (varEnvelope_continuousOn_feasible E ε B hε)
  have hcert :
      ∀ pstar ∈ feasibleSet (I := I) ε B,
        (∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope pstar ≤ E.varEnvelope q) →
        ∃ (lam : ℝ) (νp νm : I → ℝ),
          (∀ k, 0 ≤ νp k) ∧ (∀ k, 0 ≤ νm k) ∧
          (∀ k, E.envelopeGrad pstar k = lam - νp k + νm k) ∧
          (∀ k, νp k * (pstar k - (1 - ε)) = 0) ∧
          (∀ k, νm k * (ε - pstar k) = 0) := by
    intro pstar hpstar hpmin
    let P := optDesignProblem (I := I) E ε B
    let loc := designToEuclidean pstar
    have hfeasLoc : P.FeasPoint loc := by
      simpa [P, loc] using
        (optFeasPoint_of_feasible (I := I) (O := O) (E := E) (ε := ε) (B := B) hpstar)
    have hloc : P.Local_Minimum loc := by
      refine ⟨hfeasLoc, ?_⟩
      apply IsMinOn.localize
      rw [isMinOn_iff]
      intro y hy
      have hyfeas : euclideanToDesign (I := I) y ∈ feasibleSet (I := I) ε B := by
        simpa [P] using
          (feasible_of_optFeasPoint (I := I) (O := O) (E := E) (ε := ε) (B := B)
            hε hε2 y hy)
      have hobj_loc :
          P.objective loc = E.varEnvelope pstar / 4 := by
        have hlocdesign : euclideanToDesign (I := I) loc = pstar := by
          funext k
          simp [loc]
        simp [P, loc, optDesignProblem, transportedEnvelopeExt, hlocdesign]
        rw [E.varEnvelopeExt_eq_varEnvelope_of_box hε]
        · intro k
          have hk := (show FeasibleDesign ε B pstar from hpstar).floor k
          linarith [hk.1, hε]
        · intro k
          have hk := (show FeasibleDesign ε B pstar from hpstar).floor k
          linarith [hk.2, hε]
      have hobj_y :
          P.objective y = E.varEnvelope (euclideanToDesign (I := I) y) / 4 := by
        simp [P, optDesignProblem, transportedEnvelopeExt]
        rw [E.varEnvelopeExt_eq_varEnvelope_of_box hε]
        · intro k
          have hk := (show FeasibleDesign ε B (euclideanToDesign (I := I) y) from hyfeas).floor k
          linarith [hk.1, hε]
        · intro k
          have hk := (show FeasibleDesign ε B (euclideanToDesign (I := I) y) from hyfeas).floor k
          linarith [hk.2, hε]
      rw [hobj_loc, hobj_y]
      nlinarith [hpmin (euclideanToDesign (I := I) y) hyfeas]
    have hobjdiff : Differentiable ℝ P.objective := by
      simpa [P, optDesignProblem] using transportedEnvelopeExt_differentiable (I := I) E ε hε
    have hconte :
        ∀ i ∈ optEqIndexSet (Fintype.card I),
          ContDiffAt ℝ (1 : ℕ) (P.equality_constraints i) loc := by
      intro i hi
      simpa [P, optDesignProblem] using
        optBudgetConstraint_contDiffAt (n := Fintype.card I) B loc
    have hconti :
        ∀ j ∈ optBoxIndexSet (Fintype.card I),
          ContDiffAt ℝ (1 : ℕ) (P.inequality_constraints j) loc := by
      intro j hj
      simpa [P, optDesignProblem] using
        optBoxConstraint_contDiffAt (n := Fintype.card I) ε j loc
    have hLinearCQ : P.LinearCQ loc := by
      simpa [P] using optDesignProblem_LinearCQ (I := I) (O := O) E ε B loc
    have hdomain : P.domain = univ := by
      rfl
    obtain ⟨_hkfeas, lambda1, lambda2, hstat, hnonneg, hcomp⟩ :=
      first_order_neccessary_LinearCQ P loc hloc hobjdiff hconte hconti hLinearCQ hdomain
    let lam : ℝ := lambda1 ⟨optBudgetIndex (Fintype.card I), by simp [optEqIndexSet]⟩
    let νm : I → ℝ :=
      fun k => lambda2 ⟨((Fintype.equivFin I) k).val, optLower_mem_boxIndexSet (I := I) k⟩
    let νp : I → ℝ :=
      fun k => lambda2 ⟨Fintype.card I + ((Fintype.equivFin I) k).val,
        optUpper_mem_boxIndexSet (I := I) k⟩
    refine ⟨lam, νp, νm, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact hnonneg ⟨Fintype.card I + ((Fintype.equivFin I) k).val,
        optUpper_mem_boxIndexSet (I := I) k⟩
    · intro k
      exact hnonneg ⟨((Fintype.equivFin I) k).val, optLower_mem_boxIndexSet (I := I) k⟩
    · intro k
      have hcoord :
          (gradient (fun m => P.Lagrange_function m lambda1 lambda2) loc)
              ((Fintype.equivFin I) k) = 0 := by
        simpa using congrArg
          (fun v : EuclideanSpace ℝ (Fin (Fintype.card I)) => v ((Fintype.equivFin I) k))
          hstat
      have hobjAt : DifferentiableAt ℝ (transportedEnvelopeExt (I := I) E ε) loc :=
        (transportedEnvelopeExt_differentiable (I := I) E ε hε).differentiableAt
      rw [optLagrange_gradient_coord (I := I) (O := O) E ε B loc hobjAt lambda1 lambda2
        ((Fintype.equivFin I) k)] at hcoord
      have hgrad :=
        envelopeGrad_eq_gradient_varEnvelopeExt (I := I) (O := O) E ε B hε hpstar k
      simp [loc, lam, νp, νm] at hcoord
      rw [hgrad] at hcoord
      linarith
    · intro k
      have hc := hcomp ⟨Fintype.card I + ((Fintype.equivFin I) k).val,
        optUpper_mem_boxIndexSet (I := I) k⟩
      simp [P, loc, optDesignProblem, optBoxConstraint_upper, designToEuclidean, νp] at hc ⊢
      rcases hc with hc | hc
      · left
        exact hc
      · right
        linarith [hc]
    · intro k
      have hc := hcomp ⟨((Fintype.equivFin I) k).val, optLower_mem_boxIndexSet (I := I) k⟩
      simp [P, loc, optDesignProblem, optBoxConstraint_lower, designToEuclidean, νm] at hc ⊢
      rcases hc with hc | hc
      · left
        exact hc
      · right
        linarith [hc]
  exact ⟨hne, hcompact, hconv, hconvEnv, hmin, hcert⟩

end CausalSmith.Experimentation.BipartiteMinimaxDesign
