/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: the post-design conservative Wald interval

`thm:postdesign-wald`. The graph-only conservative estimator is conservative for
the variance scale, and the induced Wald interval has asymptotic coverage at
least `1 − α_cov` along nondegenerate sequences.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.THeteroClt
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.THeteroEnvelope
import Causalean.Experimentation.DesignBased.GaussianCDF
import Causalean.Experimentation.DesignBased.WaldCoverage
import Mathlib.Order.LiminfLimsup

set_option linter.style.longLine false

open scoped BigOperators Topology
open Finset Filter
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {Ix Ox : ℕ → Type*} [∀ n, Fintype (Ix n)] [∀ n, Fintype (Ox n)]
  [∀ n, DecidableEq (Ix n)] [∀ n, DecidableEq (Ox n)]


open Classical in
-- @node: thm:postdesign-wald
/-- **Post-design conservative Wald coverage.** Under the assumptions of the
heterogeneous Hájek CLT, the conservative estimator `V̂_cons = V_env` dominates the
variance scale, and the conservative Wald interval has asymptotic coverage
`≥ 1 − α`, where `z` is the upper `1 − α/2` standard-normal quantile.

The note states coverage holds "under the assumptions of `thm:hetero-clt`", so this
theorem carries the CLT's outcome-cardinality hypothesis `hcardEq`
(`card (Ox n) = n` eventually) verbatim — the paper's `n` is the outcome-population
size, and without that identification the `√n` normalization and the applied CLT
(`hetero_clt`) do not fire. -/
theorem postdesign_wald
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool))
    (p : ∀ n, Ix n → ℝ) (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hcardEq : ∀ᶠ n in atTop, Fintype.card (Ox n) = n)   -- @realizes n(the paper's stage index IS the outcome-population size: n = |O_n| = card (Ox n) on the eventual tail)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hBI : ∀ n, BipartiteInterference (E n))
    (hbdd : ∀ n, BoundedOutcomes (E n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hstar : ∀ n, p n = optimalDesign (E n) (ε n) (B n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n)
    (hnd : VarianceNondegenerate (fun n => (E n).varScale (D n) (p n)))
    (α : ℝ) (_hα0 : 0 < α) (_hα1 : α < 1) -- @realizes alpha_cov(nominal miscoverage level; carrier ℝ, range (0,1) pinned by _hα0/_hα1)
    (z : ℝ) (hz0 : 0 ≤ z)
    (hz : stdNormalCdf z = 1 - α / 2) :
    (∀ n, (E n).varScale (D n) (p n) ≤ (E n).varEstCons (p n)) ∧
    (1 - α) ≤ liminf (fun n =>
        (D n).Pr (fun zz =>
          |(E n).tau - (E n).hajekEstimator (p n) zz| ≤
            z * Real.sqrt ((E n).varEstCons (p n) / (Fintype.card (Ox n)))))
        atTop := by
  classical
  have hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop :=
    tendsto_id.congr' (hcardEq.mono fun n hn => hn.symm)
  have hvar_le : ∀ n, (E n).varScale (D n) (p n) ≤ (E n).varEstCons (p n) := by
    intro n
    have hpos : ∀ k, 0 < p n k := by
      intro k
      exact lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
    have hlt : ∀ k, p n k < 1 := by
      intro k
      linarith [((hfeas n).floor k).2, (hε n).1]
    have henv := hetero_envelope (E n) (D n) (p n) (hp0 n) (hp1 n) hpos hlt (hBern n) (hbdd n)
    simpa [BipartiteExperiment.varEstCons] using henv.2
  refine ⟨hvar_le, ?_⟩
  have hvarpos : ∀ᶠ n in atTop, 0 < (E n).varScale (D n) (p n) := by
    rcases hnd with ⟨c, hc, hc_ev⟩
    exact hc_ev.mono fun n hn => lt_of_lt_of_le hc hn
  have hclt := hetero_clt E D p hp0 hp1 ε B dbar Dbar hcardEq hBern hBI hbdd hdeg hdep
    hfeas hε hstar hεfloor hnd
  -- `conservative_wald_liminf_of_studentized_cdf` promoted to
  -- `Causalean.Experimentation.DesignBased.WaldCoverage` as a paper-agnostic lemma over abstract
  -- sequences; instantiate it with the bipartite estimator / target / variance projections.
  have hmpos : ∀ᶠ n in atTop, 0 < (Fintype.card (Ox n) : ℝ) :=
    (hcardO.eventually_ge_atTop 1).mono fun n hn => by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  exact conservative_wald_liminf_of_studentized_cdf D
    (fun n => (E n).hajekEstimator (p n)) (fun n => (E n).tau)
    (fun n => (E n).varScale (D n) (p n)) (fun n => (E n).varEstCons (p n))
    (fun n => (Fintype.card (Ox n) : ℝ))
    hmpos hvarpos hvar_le hclt.2 α z hz0 hz

end CausalSmith.Experimentation.BipartiteMinimaxDesign
