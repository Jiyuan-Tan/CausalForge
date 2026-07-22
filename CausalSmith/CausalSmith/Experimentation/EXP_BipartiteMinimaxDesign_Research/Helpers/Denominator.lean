/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: Hájek-denominator positivity

`lem:denominator-positivity`. The note's sequence-level asymptotic claim
`sup_{q ∈ P} P_q(D_1 = 0 ∨ D_0 = 0) = O(n^{-1})`, rendered as the eventual Big-O
bound along a sequence of bipartite experiments: `∃ C ≥ 0, ∀ᶠ n, sup_q P_q(…) ≤
C / card (Ox n)`. The bound comes from a Chebyshev inequality on the exposure-count
denominators built from the bounded-degree covariance count.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DenominatorControl

set_option linter.style.longLine false

open scoped BigOperators Topology
open Finset Filter
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: treatDenominator_zero_prob_le
/-- The probability that the treated Hájek denominator is zero is bounded by the overlap-dependency and denominator-kernel bound divided by the number of outcomes. -/
lemma treatDenominator_zero_prob_le (E : BipartiteExperiment I O)
    (ε B dbar Dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hcardO : 0 < Fintype.card O)
    (hdeg : BoundedOutcomeDegree E dbar) (hdep : BoundedOverlapDependency E Dbar)
    (q : I → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hq : FeasibleDesign ε B q) :
    (bernoulliDesign q hq0 hq1).Pr (fun z => (E.hajekDenominators q z).1 = 0)
      ≤ Dbar * denominatorKernelBound ε dbar / (Fintype.card O : ℝ) := by
  classical
  let D := bernoulliDesign q hq0 hq1
  let X : (I → Bool) → ℝ := fun z => ∑ i, E.expT z i / E.piT q i
  let nR : ℝ := Fintype.card O
  have hnRpos : 0 < nR := by
    unfold nR
    exact_mod_cast hcardO
  have hpos : ∀ k, 0 < q k := fun k => lt_of_lt_of_le hε0 (hq.floor k).1
  have hmean : D.E X = nR := by
    unfold D X nR
    exact treatDenominator_mean E q hq0 hq1 hpos
  have hmono :
      D.Pr (fun z => (E.hajekDenominators q z).1 = 0)
        ≤ D.Pr (fun z => nR ≤ |X z - D.E X|) := by
    apply D.Pr_mono
    intro z hz
    have hzX : X z = 0 := by
      simpa [X, BipartiteExperiment.hajekDenominators] using hz
    have habs : |X z - D.E X| = nR := by
      rw [hmean, hzX]
      simp [abs_of_nonneg hnRpos.le]
    exact le_of_eq habs.symm
  have hcheb : D.Pr (fun z => nR ≤ |X z - D.E X|) ≤ D.Var X / nR ^ 2 :=
    D.chebyshev X hnRpos
  have hvar : D.Var X ≤ nR * (Dbar * denominatorKernelBound ε dbar) := by
    unfold D X nR
    exact treatDenominator_var_le E ε B dbar Dbar hε0 hε2 hdeg hdep q hq0 hq1 hq
  have hupper :
      D.Var X / nR ^ 2 ≤ Dbar * denominatorKernelBound ε dbar / nR := by
    calc
      D.Var X / nR ^ 2
          ≤ (nR * (Dbar * denominatorKernelBound ε dbar)) / nR ^ 2 :=
            div_le_div_of_nonneg_right hvar (sq_nonneg nR)
      _ = Dbar * denominatorKernelBound ε dbar / nR := by
            field_simp [ne_of_gt hnRpos]
  exact hmono.trans (hcheb.trans hupper)

-- @node: ctrlDenominator_zero_prob_le
/-- The probability that the control Hájek denominator is zero is bounded by the overlap-dependency and denominator-kernel bound divided by the number of outcomes. -/
lemma ctrlDenominator_zero_prob_le (E : BipartiteExperiment I O)
    (ε B dbar Dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hcardO : 0 < Fintype.card O)
    (hdeg : BoundedOutcomeDegree E dbar) (hdep : BoundedOverlapDependency E Dbar)
    (q : I → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hq : FeasibleDesign ε B q) :
    (bernoulliDesign q hq0 hq1).Pr (fun z => (E.hajekDenominators q z).2 = 0)
      ≤ Dbar * denominatorKernelBound ε dbar / (Fintype.card O : ℝ) := by
  classical
  let D := bernoulliDesign q hq0 hq1
  let X : (I → Bool) → ℝ := fun z => ∑ i, E.expC z i / E.piC q i
  let nR : ℝ := Fintype.card O
  have hnRpos : 0 < nR := by
    unfold nR
    exact_mod_cast hcardO
  have hlt : ∀ k, q k < 1 := fun k => by linarith [(hq.floor k).2, hε0]
  have hmean : D.E X = nR := by
    unfold D X nR
    exact ctrlDenominator_mean E q hq0 hq1 hlt
  have hmono :
      D.Pr (fun z => (E.hajekDenominators q z).2 = 0)
        ≤ D.Pr (fun z => nR ≤ |X z - D.E X|) := by
    apply D.Pr_mono
    intro z hz
    have hzX : X z = 0 := by
      simpa [X, BipartiteExperiment.hajekDenominators] using hz
    have habs : |X z - D.E X| = nR := by
      rw [hmean, hzX]
      simp [abs_of_nonneg hnRpos.le]
    exact le_of_eq habs.symm
  have hcheb : D.Pr (fun z => nR ≤ |X z - D.E X|) ≤ D.Var X / nR ^ 2 :=
    D.chebyshev X hnRpos
  have hvar : D.Var X ≤ nR * (Dbar * denominatorKernelBound ε dbar) := by
    unfold D X nR
    exact ctrlDenominator_var_le E ε B dbar Dbar hε0 hε2 hdeg hdep q hq0 hq1 hq
  have hupper :
      D.Var X / nR ^ 2 ≤ Dbar * denominatorKernelBound ε dbar / nR := by
    calc
      D.Var X / nR ^ 2
          ≤ (nR * (Dbar * denominatorKernelBound ε dbar)) / nR ^ 2 :=
            div_le_div_of_nonneg_right hvar (sq_nonneg nR)
      _ = Dbar * denominatorKernelBound ε dbar / nR := by
            field_simp [ne_of_gt hnRpos]
  exact hmono.trans (hcheb.trans hupper)

open Classical in
-- @node: lem:denominator-positivity
/-- **Denominator positivity (eventual sequence-level `O(n⁻¹)` bound).** This is the
note's asymptotic claim
`sup_{q ∈ P_{n,B_n,ε}} P_q(D_1(q,Z) = 0 ∨ D_0(q,Z) = 0) = O(n^{-1})`,
rendered verbatim as a Big-O statement along the paper's *sequence* of bipartite
experiments `E n`: the budget **sequence** `B n` (admissible at every stage) is
fixed *before* the constant, exactly as the note fixes `B_n` inside the design
class `P_{n,B_n,ε}`; there is then a constant `C ≥ 0` such that, for all
sufficiently large `n`, **every** feasible design `q` at stage `n` (i.e. the
supremum over the design class `P_{n,B_n,ε}`) satisfies
`P_q(D_1 = 0 ∨ D_0 = 0) ≤ C / n`.

The core fixes the outcome population as `O_n = {1,…,n}`, so the stage index IS the
outcome-unit count: the hypothesis `hcard : ∀ n, Fintype.card (Ox n) = n` pins that
identification, and the rate is stated in the paper's own stage-size variable `n`.
Without it, `card (Ox n)` could diverge along a sequence unrelated to `n` (e.g.
`card (Ox n) = 2 ^ n`), and neither `C / card (Ox n)` nor `C / n` would be the
paper's `O(n^{-1})` claim.

The `∃ C` is quantified after the budget sequence but before `n` and `q` (`C`
depends only on the regularity constants `ε, d̄, D̄`, never on `n` or on `q`), which
is exactly the content of a `O(n^{-1})` bound uniform in the design; a `C` placed
before `∀ B` would instead assert one rate uniformly over *all* admissible budget
choices, which the note does not state. The `∀ᶠ n in atTop` qualifier
is the note's asymptotic (`n → ∞`) scope. A per-stage universally-quantified bound
over *all* finite experiments and *all* cardinalities — the earlier rendering — is
strictly stronger than, and does not follow back from, the stated `O` claim; and at
the empty-`O` stage it is outright false (there `D_1 = D_0 = 0` a.s. so the
zero-denominator event has probability `1`, yet `C / card O = C / 0 = 0` in `ℝ`).
Working on the eventual tail supplied by `hcardO` discharges both defects.

The budget `B` is constrained to its declared admissible interval by
`BudgetAdmissible ε B` (the `B_n` space), not merely pinned to the hyperplane
`∑_k q_k = B` inside `FeasibleDesign`. -/
lemma denominator_positivity
    {Ix Ox : ℕ → Type*} [∀ n, Fintype (Ix n)] [∀ n, Fintype (Ox n)]
    [∀ n, DecidableEq (Ix n)]
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (ε dbar Dbar : ℝ) (hε : EpsilonAdmissible ε)
    -- @realizes B_n(carrier: the budget SEQUENCE, one budget per stage n, fixed before the rate constant exactly as the note fixes B_n inside P_{n,B_n,ε})
    (B : ℕ → ℝ)
    -- @realizes B_n(cluster member: the authoritative admissible-interval predicate B_n ∈ [card I_n·ε, card I_n·(1−ε)] of `BudgetAdmissible`, pinning the B_n space at every stage independently of the FeasibleDesign hyperplane ∑ q_k = B_n)
    (_hB : ∀ n, BudgetAdmissible (I := Ix n) ε (B n))
    -- @realizes O_n(carrier: the outcome-index set O_n = {1,…,n} of stage n, realized by the type `Ox n`)
    -- @realizes n(the core fixes O_n = {1,…,n}, so the stage index IS the outcome-population size: card (Ox n) = n)
    (hcard : ∀ n, Fintype.card (Ox n) = n)
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (q : Ix n → ℝ)
        (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1),
        FeasibleDesign ε (B n) q →   -- @realizes P_{n,B_n,epsilon}(cluster member: the feasible-design predicate whose `prob` field pins q ∈ [0,1]^{m_n}, the ambient box of the design class P_{n,B_n,ε}, alongside the floor and budget clauses at the FIXED budget B n; the ∀-over-q IS the note's supremum over the class)
        (bernoulliDesign q hq0 hq1).Pr
            -- @realizes D_1(p,Z)(cluster member: `(hajekDenominators q z).1`, the [0,∞)-valued treated
            -- denominator, whose degenerate boundary value 0 this bound makes O(1/n)-rare)
            -- @realizes D_0(p,Z)(cluster member: `(hajekDenominators q z).2`, the [0,∞)-valued control
            -- denominator, whose degenerate boundary value 0 this bound makes O(1/n)-rare)
            (fun z => ((E n).hajekDenominators q z).1 = 0 ∨ ((E n).hajekDenominators q z).2 = 0)
          ≤ C / (n : ℝ) := by
  classical
  rcases hε with ⟨hε0, hε2⟩
  refine ⟨2 * max 0 Dbar * denominatorKernelBound ε dbar, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by positivity) (le_max_left _ _))
      (denominatorKernelBound_nonneg hε0)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    intro q hq0 hq1 hq
    have hcardO' : 0 < Fintype.card (Ox n) := by
      rw [hcard n]; exact Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    let D := bernoulliDesign q hq0 hq1
    let nR : ℝ := Fintype.card (Ox n)
    have hnR : nR = (n : ℝ) := by
      unfold nR; exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (hcard n)
    have hDbar : max 0 Dbar = Dbar := max_eq_right (hdep n).1.le
    have htreat := treatDenominator_zero_prob_le (E n) ε (B n) dbar Dbar hε0 hε2
      hcardO' (hdeg n) (hdep n) q hq0 hq1 hq
    have hctrl := ctrlDenominator_zero_prob_le (E n) ε (B n) dbar Dbar hε0 hε2
      hcardO' (hdeg n) (hdep n) q hq0 hq1 hq
    calc
      (bernoulliDesign q hq0 hq1).Pr
          (fun z => ((E n).hajekDenominators q z).1 = 0 ∨ ((E n).hajekDenominators q z).2 = 0)
          ≤ D.Pr (fun z => ((E n).hajekDenominators q z).1 = 0)
              + D.Pr (fun z => ((E n).hajekDenominators q z).2 = 0) := by
            exact FiniteDesign.Pr_or_le D _ _
      _ ≤ Dbar * denominatorKernelBound ε dbar / nR
            + Dbar * denominatorKernelBound ε dbar / nR := by
            exact add_le_add htreat hctrl
      _ = (2 * max 0 Dbar * denominatorKernelBound ε dbar) / nR := by
            rw [hDbar]
            ring
      _ = (2 * max 0 Dbar * denominatorKernelBound ε dbar) / (n : ℝ) := by
            rw [hnR]

end CausalSmith.Experimentation.BipartiteMinimaxDesign
