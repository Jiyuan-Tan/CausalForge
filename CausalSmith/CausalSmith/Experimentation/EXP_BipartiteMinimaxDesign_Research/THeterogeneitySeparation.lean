/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: heterogeneity strictly helps

`thm:heterogeneity-separation`. Whenever the homogeneous-point envelope-gradient
scores are not all equal, the homogeneous design fails first-order optimality, so
every envelope-optimal design is non-homogeneous and strictly better; in the
singleton-exposure case the trigger reduces to an observable degree summary.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.TConvexDesign
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.EnvelopeCalculus
import Causalean.Mathlib.Analysis.SecondOrderDescent

set_option linter.style.longLine false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: shared_card_eq_one_of_singleton
/-- A nonempty shared neighborhood of singleton exposure neighborhoods has
cardinality one. -/
lemma shared_card_eq_one_of_singleton
    (E : BipartiteExperiment I O) (hsingle : ∀ i, (E.N i).card = 1)
    {i j : O} {k : I} (hk : k ∈ E.shared i j) :
    (E.shared i j).card = 1 := by
  have hsub : E.shared i j ⊆ E.N i := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hpos : 0 < (E.shared i j).card := by
    exact Finset.card_pos.mpr ⟨k, hk⟩
  have hle : (E.shared i j).card ≤ 1 := by
    simpa [hsingle i] using Finset.card_le_card hsub
  exact Nat.le_antisymm hle hpos

-- @node: sum_indicator_shared_eq_sdeg_sq_mul
/-- Counting ordered outcome pairs whose shared neighborhood contains `k` gives
`s_k^2`. -/
lemma sum_indicator_shared_eq_sdeg_sq_mul
    (E : BipartiteExperiment I O) (k : I) (C : ℝ) :
    (∑ i : O, ∑ j : O, if k ∈ E.shared i j then C else 0) =
      (E.sdeg k : ℝ) ^ 2 * C := by
  classical
  simp only [BipartiteExperiment.shared, Finset.mem_inter]
  have hindicator : ∀ (P : O → Prop) [DecidablePred P] (A : ℝ),
      (∑ x : O, if P x then A else 0) = (((Finset.univ.filter P).card : ℝ) * A) := by
    intro P hP A
    rw [← Finset.sum_filter]
    simp
  have hinner : ∀ i : O,
      (∑ j : O, if k ∈ E.N i ∧ k ∈ E.N j then C else 0) =
        if k ∈ E.N i then ((E.M k).card : ℝ) * C else 0 := by
    intro i
    by_cases hi : k ∈ E.N i
    · simp [hi, hindicator, BipartiteExperiment.M]
    · simp [hi]
  simp_rw [hinner]
  rw [hindicator]
  simp [BipartiteExperiment.sdeg, BipartiteExperiment.M]
  ring

-- @node: singleton_envelopeGrad_eq_sdeg_sq
/-- In singleton-exposure graphs, the homogeneous-point envelope gradient reduces
to the observable squared intervention-side degree summary. -/
lemma singleton_envelopeGrad_eq_sdeg_sq
    (E : BipartiteExperiment I O) (rho : ℝ) (phom : I → ℝ)
    (hphom : phom = fun _ => rho) (hsingle : ∀ i, (E.N i).card = 1) (k : I) :
    E.envelopeGrad phom k =
      (Fintype.card O : ℝ)⁻¹ * ((E.sdeg k : ℝ) ^ 2) *
        (((1 - rho) ^ 2)⁻¹ - (rho ^ 2)⁻¹) := by
  classical
  subst phom
  let C : ℝ := (((1 - rho) ^ 2)⁻¹ - (rho ^ 2)⁻¹)
  have hsummand : ∀ i j : O,
      (if k ∈ E.shared i j then
          -((rho ^ (E.shared i j).card)⁻¹ * rho⁻¹)
            + ((1 - rho) ^ (E.shared i j).card)⁻¹ * (1 - rho)⁻¹
        else 0) = if k ∈ E.shared i j then C else 0 := by
    intro i j
    by_cases hk : k ∈ E.shared i j
    · have hcard := shared_card_eq_one_of_singleton E hsingle hk
      rw [if_pos hk, if_pos hk, hcard]
      simp only [pow_one]
      change -(rho⁻¹ * rho⁻¹) + (1 - rho)⁻¹ * (1 - rho)⁻¹ =
        (((1 - rho) ^ 2)⁻¹ - (rho ^ 2)⁻¹)
      rw [← inv_pow, ← inv_pow]
      ring
    · rw [if_neg hk, if_neg hk]
  simp only [BipartiteExperiment.envelopeGrad, prod_inv_distrib, prod_const, neg_mul]
  simp_rw [hsummand]
  rw [sum_indicator_shared_eq_sdeg_sq_mul]
  ring

/-- The shared non-homogeneity + strict-improvement + explicit-gap conclusion of
`thm:heterogeneity-separation`, factored so that BOTH the general gradient-spread
trigger and the standalone singleton-degree trigger deliver the *same* conclusion.
Here `a`/`b` attain the max/min gradient score at `p^hom`; `Δg = g_a − g_b > 0` is the
gradient-score spread, `η_box = min{ρ−ε, 1−ε−ρ}`, and `L_ab = dirModulus … (e_b−e_a)`
is the observable directional second-order modulus. The gap admits the explicit lower
bound `2 Δg min{η_box, Δg/L_ab}` (read as `2 Δg η_box` when `L_ab = 0`). -/
def SeparationConclusion (E : BipartiteExperiment I O) (ε B rho : ℝ) (phom : I → ℝ) : Prop :=
  (¬ ∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope phom ≤ E.varEnvelope q) ∧
  (∃ a b : I,
      (∀ k, E.envelopeGrad phom k ≤ E.envelopeGrad phom a) ∧
      (∀ k, E.envelopeGrad phom b ≤ E.envelopeGrad phom k) ∧
      0 < E.envelopeGrad phom a - E.envelopeGrad phom b ∧
      ∀ pstar ∈ feasibleSet (I := I) ε B,
        (∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope pstar ≤ E.varEnvelope q) →
        pstar ≠ phom ∧ E.varEnvelope pstar < E.varEnvelope phom ∧
        E.varEnvelope phom - E.varEnvelope pstar ≥
          2 * (E.envelopeGrad phom a - E.envelopeGrad phom b) *
            (let L := dirModulus E ε B
                (fun k => (if k = b then (1 : ℝ) else 0) - (if k = a then 1 else 0));
              if L = 0 then min (rho - ε) (1 - ε - rho)
              else min (min (rho - ε) (1 - ε - rho))
                ((E.envelopeGrad phom a - E.envelopeGrad phom b) / L)))

-- @node: envelope_segment_descent_gate
/-- The one-dimensional calculus of the reciprocal-product envelope line
`g(s)=V_env(p^hom+s d)/4`: `C²` regularity on the box segment, differentiability at the
origin, the first derivative identity `g'(0)=-(g_a-g_b)`, nonnegativity of the directional
modulus, and the `le_ciSup` curvature bound by `dirModulus`.

FORMERLY SUBSTRATE-DEBT, now DISCHARGED (2026-07-09) by `envelopeLineC2Data_holds`: no
theorem in this file assumes it. It survives as a named bundle because the descent-gap
estimate reads more clearly against it. The two missing pieces were the reciprocal-product
second derivative — supplied by generalizing `recipC` to every smoothness order and lifting
`varEnvelopeExt` to `C²` — and the `BddAbove`/`le_ciSup` argument for `dirModulus`, supplied
by continuity of the curvature `envCurv` on the compact `feasibleSet`
(`Helpers/EnvelopeCalculus`, on the reusable `Causalean.Mathlib.Analysis.LineSecondDeriv`
primitive). The descent gap itself was never assumed; it is derived below from
`second_order_descent_gap_half`. -/
def EnvelopeLineC2Data
    (E : BipartiteExperiment I O) (ε B rho : ℝ) (phom : I → ℝ) (a b : I) : Prop :=
  let d := fun k => (if k = b then (1 : ℝ) else 0) - (if k = a then 1 else 0)
  let g := fun s : ℝ => E.varEnvelope (fun k => phom k + s * d k) / 4
  let T := min (rho - ε) (1 - ε - rho)
  0 ≤ dirModulus E ε B d
    ∧ ContDiffOn ℝ 2 g (Set.Icc 0 T)
    ∧ DifferentiableAt ℝ g 0
    ∧ deriv g 0 = -(E.envelopeGrad phom a - E.envelopeGrad phom b)
    ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, deriv (deriv g) t ≤ dirModulus E ε B d)

private lemma homogeneous_pair_segment_feasible
    (ε B rho : ℝ) (hε : EpsilonAdmissible ε) (hrbox : ε < rho ∧ rho < 1 - ε)
    {phom : I → ℝ} (hphom : phom = fun _ => rho)
    (hfeas : phom ∈ feasibleSet (I := I) ε B) (a b : I) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (min (rho - ε) (1 - ε - rho))) :
    (fun k => phom k + s *
      ((if k = b then (1 : ℝ) else 0) - (if k = a then 1 else 0))) ∈
      feasibleSet (I := I) ε B := by
  classical
  let d : I → ℝ := fun k => (if k = b then (1 : ℝ) else 0) - (if k = a then 1 else 0)
  let q : I → ℝ := fun k => phom k + s * d k
  have hs0 : 0 ≤ s := hs.1
  have hsT : s ≤ min (rho - ε) (1 - ε - rho) := hs.2
  have hs_rho : s ≤ rho - ε := le_trans hsT (min_le_left _ _)
  have hs_one : s ≤ 1 - ε - rho := le_trans hsT (min_le_right _ _)
  have hfloor : PositivityFloor ε q := by
    intro k
    by_cases hab : a = b
    · subst b
      simpa [q, d] using (show FeasibleDesign ε B phom from hfeas).floor k
    · subst phom
      by_cases hb : k = b
      · have ha : k ≠ a := by
          intro hka
          exact hab (hka.symm.trans hb)
        have hba : b ≠ a := by
          intro hba
          exact hab hba.symm
        simp [q, d, hb, hba]
        constructor <;> linarith
      · by_cases ha : k = a
        · simp [q, d, ha, hab]
          constructor <;> linarith
        · have hqk : q k = rho := by
            simp [q, d, hb, ha]
          rw [hqk]
          exact ⟨hrbox.1.le, hrbox.2.le⟩
  have hprob : ProbVector q := by
    intro k
    have hk := hfloor k
    constructor
    · exact le_trans hε.1.le hk.1
    · linarith [hk.2, hε.1]
  have hsumd : ∑ k, d k = 0 := by
    simp [d, Finset.sum_sub_distrib]
  have hbudget : BudgetBalance B q := by
    have hbase := (show FeasibleDesign ε B phom from hfeas).budget
    dsimp [BudgetBalance, q] at hbase ⊢
    calc
      ∑ k, (phom k + s * d k) = (∑ k, phom k) + ∑ k, s * d k := by
        rw [Finset.sum_add_distrib]
      _ = B + s * ∑ k, d k := by
        rw [hbase, Finset.mul_sum]
      _ = B := by
        rw [hsumd]
        ring
  exact ⟨hprob, hε, hfloor, hbudget⟩

-- @node: homogeneous_feasible
omit [DecidableEq I] in
/-- The homogeneous design is feasible when `rho = B / card I` and it lies strictly
inside the positivity box. -/
lemma homogeneous_feasible
    (ε B rho : ℝ) (hε : EpsilonAdmissible ε) (hm : 0 < Fintype.card I)
    (hrho : rho = B / (Fintype.card I : ℝ))
    (hrbox : ε < rho ∧ rho < 1 - ε)
    (phom : I → ℝ) (hphom : phom = fun _ => rho) :
    phom ∈ feasibleSet (I := I) ε B := by
  classical
  subst phom
  refine ⟨?_, hε, ?_, ?_⟩
  · intro k
    constructor <;> linarith [hε.1, hε.2, hrbox.1, hrbox.2]
  · intro k
    constructor <;> linarith [hrbox.1, hrbox.2]
  · unfold BudgetBalance
    have hm_ne : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [hrho]
    field_simp [hm_ne]
    change (Fintype.card I : ℝ) * B = B * (Fintype.card I : ℝ)
    ring

-- @node: homogeneous_not_minimizer_of_gradient_spread
/-- At an interior homogeneous point, KKT stationarity would force all envelope
gradient coordinates to agree. Hence any gradient spread rules out optimality. -/
lemma homogeneous_not_minimizer_of_gradient_spread
    (E : BipartiteExperiment I O) (ε B rho : ℝ) (hε : EpsilonAdmissible ε)
    (hB : BudgetAdmissible (I := I) ε B)
    (hm : 0 < Fintype.card I)
    (hrho : rho = B / (Fintype.card I : ℝ))
    (hrbox : ε < rho ∧ rho < 1 - ε)
    (phom : I → ℝ) (hphom : phom = fun _ => rho)
    (hspread : ∃ a b : I, E.envelopeGrad phom a ≠ E.envelopeGrad phom b) :
    ¬ ∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope phom ≤ E.varEnvelope q := by
  classical
  intro hmin
  have hfeas : phom ∈ feasibleSet (I := I) ε B :=
    homogeneous_feasible (I := I) ε B rho hε hm hrho hrbox phom hphom
  obtain ⟨_hne, _hcompact, _hconv, _hconvEnv, _hexists, hcert⟩ :=
    convex_design E ε B hε.1 hε.2 hB.1 hB.2
  obtain ⟨lam, νp, νm, _hνp_nonneg, _hνm_nonneg, hgrad, hcomp_upper, hcomp_lower⟩ :=
    hcert phom hfeas hmin
  have hνp_zero : ∀ k, νp k = 0 := by
    intro k
    have hfactor : phom k - (1 - ε) ≠ 0 := by
      subst phom
      linarith [hrbox.2]
    rcases mul_eq_zero.mp (hcomp_upper k) with hν | hfac
    · exact hν
    · exact False.elim (hfactor hfac)
  have hνm_zero : ∀ k, νm k = 0 := by
    intro k
    have hfactor : ε - phom k ≠ 0 := by
      subst phom
      linarith [hrbox.1]
    rcases mul_eq_zero.mp (hcomp_lower k) with hν | hfac
    · exact hν
    · exact False.elim (hfactor hfac)
  rcases hspread with ⟨a, b, hab⟩
  have ha : E.envelopeGrad phom a = lam := by
    rw [hgrad a, hνp_zero a, hνm_zero a]
    ring
  have hb : E.envelopeGrad phom b = lam := by
    rw [hgrad b, hνp_zero b, hνm_zero b]
    ring
  exact hab (ha.trans hb.symm)

-- @node: singleton_degree_spread_to_gradient_spread
/-- In the singleton-exposure case, unequal squared intervention-side degrees
produce unequal homogeneous envelope-gradient coordinates when `rho ≠ 1 / 2`. -/
lemma singleton_degree_spread_to_gradient_spread
    (E : BipartiteExperiment I O) (rho : ℝ) (hrhalf : rho ≠ 1 / 2)
    (phom : I → ℝ) (hphom : phom = fun _ => rho)
    (hsingle : ∀ i, (E.N i).card = 1)
    (hsdeg : ∃ a b : I, (E.sdeg a : ℝ) ^ 2 ≠ (E.sdeg b : ℝ) ^ 2) :
    ∃ a b : I, E.envelopeGrad phom a ≠ E.envelopeGrad phom b := by
  classical
  let C : ℝ := (((1 - rho) ^ 2)⁻¹ - (rho ^ 2)⁻¹)
  have hC : C ≠ 0 := by
    intro hzero
    have hinv : ((1 - rho) ^ 2)⁻¹ = (rho ^ 2)⁻¹ := by
      exact sub_eq_zero.mp hzero
    have hsquares : (1 - rho) ^ 2 = rho ^ 2 := inv_injective hinv
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hlin | hlin
    · apply hrhalf
      linarith
    · linarith
  have hO_ne : (Fintype.card O : ℝ) ≠ 0 := by
    intro hOzero
    have hOcard : Fintype.card O = 0 := by exact_mod_cast hOzero
    rcases hsdeg with ⟨a, b, hab⟩
    have ha0 : (E.sdeg a : ℝ) = 0 := by
      have hle : (E.M a).card ≤ 0 := by
        simpa [BipartiteExperiment.M, hOcard] using Finset.card_le_univ (E.M a)
      have hcard : (E.M a).card = 0 := Nat.eq_zero_of_le_zero hle
      simp [BipartiteExperiment.sdeg, hcard]
    have hb0 : (E.sdeg b : ℝ) = 0 := by
      have hle : (E.M b).card ≤ 0 := by
        simpa [BipartiteExperiment.M, hOcard] using Finset.card_le_univ (E.M b)
      have hcard : (E.M b).card = 0 := Nat.eq_zero_of_le_zero hle
      simp [BipartiteExperiment.sdeg, hcard]
    apply hab
    rw [ha0, hb0]
  let scale : ℝ := (Fintype.card O : ℝ)⁻¹ * C
  have hscale : scale ≠ 0 := by
    exact mul_ne_zero (inv_ne_zero hO_ne) hC
  rcases hsdeg with ⟨a, b, hab⟩
  refine ⟨a, b, ?_⟩
  have hgrad : ∀ k, E.envelopeGrad phom k = scale * ((E.sdeg k : ℝ) ^ 2) := by
    intro k
    rw [singleton_envelopeGrad_eq_sdeg_sq E rho phom hphom hsingle k]
    ring
  intro hgab
  apply hab
  rw [hgrad a, hgrad b] at hgab
  exact mul_left_cancel₀ hscale hgab

omit [Fintype I] in
/-- The direction `e_b - e_a` is bounded by `1` in every coordinate. -/
private lemma pair_direction_abs_le_one (a b : I) (k : I) :
    |(if k = b then (1 : ℝ) else 0) - (if k = a then 1 else 0)| ≤ 1 := by
  have hb : (if k = b then (1 : ℝ) else 0) = 1 ∨ (if k = b then (1 : ℝ) else 0) = 0 := by
    split <;> simp
  have ha : (if k = a then (1 : ℝ) else 0) = 1 ∨ (if k = a then (1 : ℝ) else 0) = 0 := by
    split <;> simp
  rcases hb with hb | hb <;> rcases ha with ha | ha <;> rw [hb, ha] <;> norm_num

/-- **The `EnvelopeLineC2Data` gate is discharged.** Every conjunct is now derived, so
`thm:heterogeneity-separation` no longer assumes any one-dimensional calculus input.

The five conjuncts come from `Helpers/EnvelopeCalculus`:
`0 ≤ dirModulus` from convexity of `V_env` (via `convexOn_deriv2_nonneg`), `ContDiffOn ℝ 2`
from `contDiffOn_envelope_line`, differentiability at `0` from `differentiableAt_envelope_line_zero`,
the first-derivative identity from `deriv_envelope_line_zero`, and the curvature bound from
`deriv_deriv_envelope_line_eq_envCurv` + `envCurv_le_dirModulus`. -/
lemma envelopeLineC2Data_holds
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε : EpsilonAdmissible ε)
    (hm : 0 < Fintype.card I)
    (hB : BudgetAdmissible (I := I) ε B)
    (rho : ℝ) (hrho : rho = B / (Fintype.card I : ℝ))
    (hrbox : ε < rho ∧ rho < 1 - ε)
    (phom : I → ℝ) (hphom : phom = fun _ => rho)
    (a b : I) :
    EnvelopeLineC2Data E ε B rho phom a b := by
  classical
  let d : I → ℝ := fun k =>
    (if k = b then (1 : ℝ) else 0) - (if k = a then 1 else 0)
  let g : ℝ → ℝ := fun s => E.varEnvelope (fun k => phom k + s * d k) / 4
  let T : ℝ := min (rho - ε) (1 - ε - rho)
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min (by linarith [hrbox.1]) (by linarith [hrbox.2])
  have hd : ∀ k, |d k| ≤ 1 := by
    intro k
    exact pair_direction_abs_le_one a b k
  have hfeas : phom ∈ feasibleSet (I := I) ε B :=
    homogeneous_feasible (I := I) ε B rho hε hm hrho hrbox phom hphom
  have hseg : ∀ s ∈ Set.Icc (-T) T,
      (fun k => phom k + s * d k) ∈ feasibleSet (I := I) ε B := by
    intro s hs
    by_cases hs0 : 0 ≤ s
    · exact homogeneous_pair_segment_feasible (I := I) ε B rho hε hrbox hphom hfeas a b
        ⟨hs0, hs.2⟩
    · have hneg : 0 ≤ -s := by linarith
      have hupper : -s ≤ T := by linarith [hs.1]
      have hswap := homogeneous_pair_segment_feasible (I := I) ε B rho hε hrbox hphom
        hfeas b a (s := -s) ⟨hneg, hupper⟩
      convert hswap using 1
      funext k
      simp only [d]
      ring
  have hbox : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ k,
      ε / 2 ≤ phom k + s * d k ∧ ε / 2 ≤ 1 - (phom k + s * d k) := by
    intro s hs k
    have hsL : s ≤ rho - ε := le_trans hs.2 (min_le_left _ _)
    have hsR : s ≤ 1 - ε - rho := le_trans hs.2 (min_le_right _ _)
    have hsd : |s * d k| ≤ s := by
      calc
        |s * d k| = |s| * |d k| := abs_mul _ _
        _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left (hd k) (abs_nonneg s)
        _ = s := by simp [abs_of_nonneg hs.1]
    have hlow : -s ≤ s * d k := by
      linarith [neg_le_abs (s * d k)]
    have hupp : s * d k ≤ s := by
      linarith [le_abs_self (s * d k)]
    rw [hphom]
    constructor <;> linarith [hε.1]
  unfold EnvelopeLineC2Data
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply le_trans ?_ (E.envCurv_le_dirModulus ε B hε.1 hε.2 hB.1 hB.2 hd hfeas)
    rw [← E.deriv_deriv_envelope_line_zero ε B hε.1 hfeas hd]
    apply Causalean.Mathlib.Analysis.convexOn_deriv2_nonneg
    · let A : ℝ →ᵃ[ℝ] (I → ℝ) := AffineMap.lineMap phom (phom + d)
      have hline : ∀ s : ℝ, A s = fun k => phom k + s * d k := by
        intro s
        ext k
        simp [A, AffineMap.lineMap_apply_module']
        ring
      have hpre : ConvexOn ℝ (A ⁻¹' feasibleSet (I := I) ε B)
          (E.varEnvelope ∘ A) :=
        (convex_design E ε B hε.1 hε.2 hB.1 hB.2).2.2.2.1.comp_affineMap A
      have hrestr : ConvexOn ℝ (Set.Icc (-T) T) (E.varEnvelope ∘ A) :=
        hpre.subset (by
          intro s hs
          change A s ∈ feasibleSet (I := I) ε B
          rw [hline s]
          exact hseg s hs) (convex_Icc _ _)
      convert hrestr.smul (show 0 ≤ (4 : ℝ)⁻¹ by norm_num) using 1
      funext s
      rw [← hline s]
      simp [Function.comp_apply, div_eq_inv_mul]
    · intro y hy
      exact E.differentiableAt_envelope_line ε B hε.1 hd y (hseg y hy)
    · rw [interior_Icc]
      exact ⟨by linarith, by linarith⟩
    · exact E.differentiableAt_deriv_envelope_line_zero ε B hε.1 hfeas hd
  · exact E.contDiffOn_envelope_line ε hε.1 hbox
  · exact E.differentiableAt_envelope_line_zero ε B hε.1 hfeas hd
  · rw [E.deriv_envelope_line_zero ε B hε.1 hfeas hd]
    simp only [d]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro t ht
    rw [E.deriv_deriv_envelope_line_eq_envCurv ε B hε.1 hd t
      (hseg t ⟨le_trans (neg_nonpos.mpr hT.le) ht.1, ht.2⟩)]
    exact E.envCurv_le_dirModulus ε B hε.1 hε.2 hB.1 hB.2 hd
      (hseg t ⟨le_trans (neg_nonpos.mpr hT.le) ht.1, ht.2⟩)

-- @node: envelope_segment_descent_gap
/-- General gradient-spread separation, with the one-dimensional Taylor/`dirModulus` gap
estimate now DERIVED: the former `EnvelopeLineC2Data` hypothesis is supplied internally by
`envelopeLineC2Data_holds`. -/
lemma envelope_segment_descent_gap
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε : EpsilonAdmissible ε)
    (hm : 0 < Fintype.card I)
    (hB : BudgetAdmissible (I := I) ε B)
    (rho : ℝ) (hrho : rho = B / (Fintype.card I : ℝ))
    (hrbox : ε < rho ∧ rho < 1 - ε)
    (phom : I → ℝ) (hphom : phom = fun _ => rho)
    (hspread : ∃ a b : I, E.envelopeGrad phom a ≠ E.envelopeGrad phom b) :
    SeparationConclusion E ε B rho phom := by
  classical
  have hdata : ∀ a b : I, EnvelopeLineC2Data E ε B rho phom a b := fun a b =>
    envelopeLineC2Data_holds E ε B hε hm hB rho hrho hrbox phom hphom a b
  have hnot :
      ¬ ∀ q ∈ feasibleSet (I := I) ε B, E.varEnvelope phom ≤ E.varEnvelope q :=
    homogeneous_not_minimizer_of_gradient_spread E ε B rho hε hB hm hrho hrbox phom hphom
      hspread
  have hI : Nonempty I := Fintype.card_pos_iff.mp hm
  obtain ⟨a, hmax⟩ :=
    Finite.exists_max (fun k : I => E.envelopeGrad phom k)
  obtain ⟨b, hmin⟩ :=
    Finite.exists_min (fun k : I => E.envelopeGrad phom k)
  have hne_ba : E.envelopeGrad phom b ≠ E.envelopeGrad phom a := by
    intro hba
    rcases hspread with ⟨x, y, hxy⟩
    apply hxy
    have hx : E.envelopeGrad phom x = E.envelopeGrad phom a := by
      exact le_antisymm (hmax x) (by simpa [hba] using hmin x)
    have hy : E.envelopeGrad phom y = E.envelopeGrad phom a := by
      exact le_antisymm (hmax y) (by simpa [hba] using hmin y)
    exact hx.trans hy.symm
  have hdelta : 0 < E.envelopeGrad phom a - E.envelopeGrad phom b := by
    have hlt : E.envelopeGrad phom b < E.envelopeGrad phom a :=
      lt_of_le_of_ne (hmin a) hne_ba
    linarith
  refine ⟨hnot, a, b, hmax, hmin, hdelta, ?_⟩
  intro pstar hpstar hpmin
  have hfeas : phom ∈ feasibleSet (I := I) ε B :=
    homogeneous_feasible (I := I) ε B rho hε hm hrho hrbox phom hphom
  have hpstar_ne : pstar ≠ phom := by
    intro hp_eq
    apply hnot
    intro q hq
    simpa [hp_eq] using hpmin q hq
  have hstrict : E.varEnvelope pstar < E.varEnvelope phom := by
    have hle : E.varEnvelope pstar ≤ E.varEnvelope phom := hpmin phom hfeas
    have hne_val : E.varEnvelope pstar ≠ E.varEnvelope phom := by
      intro heq
      apply hnot
      intro q hq
      calc
        E.varEnvelope phom = E.varEnvelope pstar := heq.symm
        _ ≤ E.varEnvelope q := hpmin q hq
    exact lt_of_le_of_ne hle hne_val
  refine ⟨hpstar_ne, hstrict, ?_⟩
  let d : I → ℝ := fun k => (if k = b then (1 : ℝ) else 0) - (if k = a then 1 else 0)
  let g : ℝ → ℝ := fun s => E.varEnvelope (fun k => phom k + s * d k) / 4
  let T : ℝ := min (rho - ε) (1 - ε - rho)
  let L : ℝ := dirModulus E ε B d
  let Δ : ℝ := E.envelopeGrad phom a - E.envelopeGrad phom b
  let s : ℝ := Causalean.Mathlib.Analysis.descentStep L Δ T
  have hT : 0 ≤ T := by
    dsimp [T]
    exact le_min (by linarith [hrbox.1]) (by linarith [hrbox.2])
  have hdata_ab : EnvelopeLineC2Data E ε B rho phom a b := hdata a b
  have hdata_unfold :
      0 ≤ L
        ∧ ContDiffOn ℝ 2 g (Set.Icc 0 T)
        ∧ DifferentiableAt ℝ g 0
        ∧ deriv g 0 = -Δ
        ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, deriv (deriv g) t ≤ L) := by
    simpa [EnvelopeLineC2Data, d, g, T, L, Δ] using hdata_ab
  rcases hdata_unfold with ⟨hLnn, hgC2, hgdiff, hgderiv0, hgcurv⟩
  have hslope : deriv g 0 ≤ -Δ := by
    rw [hgderiv0]
  have hdesc :
      s ∈ Set.Icc (0 : ℝ) T ∧ g 0 - g s ≥ (Δ / 2) * s := by
    simpa [s] using
      (Causalean.Mathlib.Analysis.second_order_descent_gap_half
        (f := g) (M := L) (c := Δ) (T := T) hT hdelta hLnn hgC2 hgdiff hgcurv hslope)
  have hq_feas :
      (fun k => phom k + s * d k) ∈ feasibleSet (I := I) ε B := by
    exact homogeneous_pair_segment_feasible (I := I) ε B rho hε hrbox hphom hfeas a b
      (by simpa [T] using hdesc.1)
  have hpstar_le_q : E.varEnvelope pstar ≤ E.varEnvelope (fun k => phom k + s * d k) :=
    hpmin (fun k => phom k + s * d k) hq_feas
  have hg0_eval : g 0 = E.varEnvelope phom / 4 := by
    simp [g]
  have hgs_eval : g s = E.varEnvelope (fun k => phom k + s * d k) / 4 := by
    rfl
  have henv_gap_to_step :
      E.varEnvelope phom - E.varEnvelope (fun k => phom k + s * d k) ≥ 2 * Δ * s := by
    nlinarith [hdesc.2, hg0_eval, hgs_eval]
  have henv_gap_to_q :
      E.varEnvelope phom - E.varEnvelope pstar ≥
        E.varEnvelope phom - E.varEnvelope (fun k => phom k + s * d k) := by
    linarith
  have hgap_step : E.varEnvelope phom - E.varEnvelope pstar ≥ 2 * Δ * s := by
    exact le_trans henv_gap_to_step henv_gap_to_q
  simpa [d, T, L, Δ, s, Causalean.Mathlib.Analysis.descentStep] using hgap_step

-- @node: thm:heterogeneity-separation
/-- **Heterogeneity separation.** Set `ρ = B/m` and let `p^hom ≡ ρ` be the
homogeneous feasible design (with `ρ ∈ (ε,1−ε)`, `ρ ≠ 1/2`).
(1) **General trigger:** if the gradient scores `g_k(p^hom)` are not all equal, then
`p^hom` is not an envelope minimizer, every minimizer is non-homogeneous and strictly
better, with the explicit `2 Δg min{η_box, Δg/L_ab}` gap bound (`SeparationConclusion`).
(2) **Singleton reduction:** for singleton-exposure graphs the gradient reduces to the
observable degree summary `g_k(p^hom) = n^{-1} s_k² ((1−ρ)^{-2} − ρ^{-2})`.
(3) **Standalone singleton trigger:** for a singleton-exposure graph whose observable
degree summaries `s_k²` are not all equal, the SAME conclusion holds — WITHOUT assuming
the gradient-spread hypothesis, which is instead derived from (2) together with
`ρ ≠ 1/2` (so `(1−ρ)^{-2} − ρ^{-2} ≠ 0` scales unequal `s_k²` into unequal `g_k`). -/
theorem heterogeneity_separation
    (E : BipartiteExperiment I O) (ε B : ℝ) (hε : EpsilonAdmissible ε)
    (hm : 0 < Fintype.card I)
    (hB : BudgetAdmissible (I := I) ε B)
    (rho : ℝ) (hrho : rho = B / (Fintype.card I : ℝ))
    (hrbox : ε < rho ∧ rho < 1 - ε) (hrhalf : rho ≠ 1 / 2)
    (phom : I → ℝ) (hphom : phom = fun _ => rho) :
    ((∃ a b : I, E.envelopeGrad phom a ≠ E.envelopeGrad phom b) →
        SeparationConclusion E ε B rho phom) ∧
    ((∀ i, (E.N i).card = 1) →
        ∀ k, E.envelopeGrad phom k
          = (Fintype.card O : ℝ)⁻¹ * ((E.sdeg k : ℝ) ^ 2) * (((1 - rho) ^ 2)⁻¹ - (rho ^ 2)⁻¹)) ∧
    ((∀ i, (E.N i).card = 1) →
        (∃ a b : I, (E.sdeg a : ℝ) ^ 2 ≠ (E.sdeg b : ℝ) ^ 2) →
        SeparationConclusion E ε B rho phom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hspread
    exact envelope_segment_descent_gap E ε B hε hm hB rho hrho hrbox phom hphom hspread
  · intro hsingle k
    exact singleton_envelopeGrad_eq_sdeg_sq E rho phom hphom hsingle k
  · intro hsingle hsdeg
    exact envelope_segment_descent_gap E ε B hε hm hB rho hrho hrbox phom hphom
      (singleton_degree_spread_to_gradient_spread E rho hrhalf phom hphom hsingle hsdeg)

end CausalSmith.Experimentation.BipartiteMinimaxDesign
