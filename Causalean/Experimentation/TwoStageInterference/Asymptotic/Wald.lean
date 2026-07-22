/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): asymptotic (oracle) Wald confidence-interval coverage

The oracle Wald interval `D̂E ± z·√Var` for the Liu–Hudgens treatment-minus-control direct-effect
contrast has asymptotic coverage at least `1 − γ`, derived from the direct-contrast CLT and
standard-normal CDF symmetry.  Concretely,
along a sequence of two-stage Hudgens–Halloran experiments the studentized statistic
`stud = (D̂E − DE̅)/√directVar` is asymptotically standard normal (the CLT), so the covering event
`|D̂E − DE̅| ≤ z·√directVar` is — after dividing through by `√directVar > 0` — exactly
`|stud| ≤ z`, whose probability is bounded below by `Pr[stud ≤ z] − Pr[stud ≤ −z]`.  This lower
bound converges to `Φ(z) − Φ(−z) = (1 − γ/2) − (γ/2) = 1 − γ` by the two CLT limits together with
the CDF symmetry `Φ(−z) = 1 − Φ(z)`, and a `liminf` comparison delivers the result.

This is the transplant of the Aronow–Samii oracle Wald-coverage proof
(`ExposureMappingInterference.wald_coverage`) to the Liu–Hudgens bundle.  Following that template,
the two CLT limits at `z` and `−z` are supplied as hypotheses (`hcltPos`, `hcltNeg`) — they are
exactly the conclusion of `directEffect_clt` — so this coverage statement is decoupled from the
conditional-CLT regularity plumbing.

The interval here is the **oracle** one: it uses the TRUE design variance `directVar` (which
`var_estD` proves equals `Var(estD)`), not an estimated `V̂`.  The FEASIBLE (estimated-variance)
interval — the analogue of `ExposureMappingInterference.wald_coverage_feasible` — is `wald_coverage_feasible` in
`WaldFeasible.lean`.
-/

import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup
import Causalean.Experimentation.DesignBased.GaussianCDF
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Oracle Wald coverage

Oracle Wald intervals for Liu-Hudgens treatment-minus-control direct-effect contrasts have
asymptotic coverage from the CLT.

The public theorem `wald_coverage_oracle` proves the lower-coverage result for intervals using
the true design variance.  It takes the two one-sided studentized CLT limits at the normal
quantile and its negative as inputs, then converts the event `|stud| ≤ zq` into coverage of
`DEbar` by multiplying through the positive square-root design variance.
-/

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-- **Asymptotic oracle Wald coverage (Liu–Hudgens 2014).** Along a sequence of two-stage
Hudgens–Halloran experiments `Exp`, write `stud n` for the studentized statistic for the
treatment-minus-control direct-effect contrast
`(D̂E − DE̅)/√directVar` (pinned by `hstud`).  Assume the variance is everywhere positive (`hVar`),
that `zq = z_{1−γ/2} ≥ 0` is the standard-normal upper quantile (`hzq : Φ(zq) = 1 − γ/2`), and the
two direct-contrast CLT limits at `zq` and `−zq` (`hcltPos`, `hcltNeg`, exactly
`directEffect_clt`'s conclusion).  Then the oracle Wald interval `D̂E ± zq·√directVar` attains
asymptotic coverage of `DE̅` at least `1 − γ`. -/
theorem wald_coverage_oracle (Exp : ℕ → LHExperiment)
    (stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (hstud : ∀ n sw, stud n sw = ((Exp n).estD sw - (Exp n).DEbar) / Real.sqrt ((Exp n).directVar))
    (hVar : ∀ n, 0 < (Exp n).directVar)
    {γ : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - γ / 2)
    (hcltPos : Tendsto (fun n => (Exp n).jointD.Pr (fun sw => stud n sw ≤ zq))
      atTop (𝓝 (stdNormalCdf zq)))
    (hcltNeg : Tendsto (fun n => (Exp n).jointD.Pr (fun sw => stud n sw ≤ -zq))
      atTop (𝓝 (stdNormalCdf (-zq)))) :
    1 - γ ≤ Filter.liminf
      (fun n => (Exp n).jointD.Pr (fun sw =>
        |(Exp n).estD sw - (Exp n).DEbar| ≤ zq * Real.sqrt ((Exp n).directVar)))
      Filter.atTop := by
  -- The studentized lower-CDF probabilities at `zq` and `-zq`.
  set S : ℕ → ℝ := fun n =>
    (Exp n).jointD.Pr (fun sw => stud n sw ≤ zq) with hSdef
  set Lo : ℕ → ℝ := fun n =>
    (Exp n).jointD.Pr (fun sw => stud n sw ≤ -zq) with hLodef
  set I : ℕ → ℝ := fun n => (Exp n).jointD.Pr (fun sw =>
    |(Exp n).estD sw - (Exp n).DEbar| ≤ zq * Real.sqrt ((Exp n).directVar)) with hIdef
  -- (1) Limit of `S - Lo`.
  have hlim : Tendsto (fun n => S n - Lo n) atTop (𝓝 (1 - γ)) := by
    have h := hcltPos.sub hcltNeg
    rw [stdNormalCdf_neg zq, hzq] at h
    have he : (1 - γ / 2) - (1 - (1 - γ / 2)) = 1 - γ := by ring
    rwa [he] at h
  -- (2) Pointwise lower bound `S - Lo ≤ I`.
  have hbound : ∀ n, S n - Lo n ≤ I n := by
    intro n
    -- Abbreviate the studentized statistic and the square-root denominator.
    set W : (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ :=
      fun sw => stud n sw with hWdef
    -- Split `S` by the event `W ≤ -zq`.
    have hsplit := (Exp n).jointD.Pr_split (fun sw => W sw ≤ zq) (fun sw => W sw ≤ -zq)
    -- The first piece equals `Lo`.
    have hfirst : (Exp n).jointD.Pr (fun sw => W sw ≤ zq ∧ W sw ≤ -zq) = Lo n := by
      apply (Exp n).jointD.Pr_congr
      intro sw
      constructor
      · exact fun h => h.2
      · intro h2
        exact ⟨le_trans h2 (by linarith [hzq0]), h2⟩
    -- So `S - Lo` is the probability of the second piece.
    have hSLo : S n - Lo n =
        (Exp n).jointD.Pr (fun sw => W sw ≤ zq ∧ ¬ W sw ≤ -zq) := by
      have : S n = (Exp n).jointD.Pr (fun sw => W sw ≤ zq ∧ W sw ≤ -zq)
          + (Exp n).jointD.Pr (fun sw => W sw ≤ zq ∧ ¬ W sw ≤ -zq) := hsplit
      rw [this, hfirst]; ring
    rw [hSLo]
    -- That second piece is contained in `I`'s event.
    apply (Exp n).jointD.Pr_mono
    intro sw hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [not_le] at hz2
    -- `|W sw| ≤ zq`.
    have habs : |W sw| ≤ zq := abs_le.mpr ⟨le_of_lt hz2, hz1⟩
    -- Unfold the studentized statistic.
    set s : ℝ := Real.sqrt ((Exp n).directVar) with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr (hVar n)
    rw [hWdef] at habs
    simp only at habs
    rw [hstud n sw, ← hsdef] at habs
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs] at habs
    exact habs
  -- (3) Conclude with liminf.
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => S n - Lo n) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop I :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
      (fun n => (Exp n).jointD.Pr_le_one _)
  calc 1 - γ = Filter.liminf (fun n => S n - Lo n) atTop := hlim.liminf_eq.symm
    _ ≤ Filter.liminf I atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound) hbdd hcobdd

end TwoStageInterference
end Experimentation
end Causalean
