/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): asymptotic (feasible) Wald confidence-interval coverage

The **feasible** Wald interval `D̂E ± z·√(V̂)` for the Liu–Hudgens treatment-minus-control
direct-effect contrast — using an *estimated* variance `V̂` instead of the unknown true design
variance `directVar` — attains asymptotic coverage at least `1 − γ`, provided the variance
estimator is *conservative-consistent*: it undershoots the true variance only with vanishing
probability (`hVhat`).

This is the adaptation of the Aronow–Samii feasible Wald-coverage proof
(`ExposureMappingInterference.wald_coverage_feasible`) to the Liu–Hudgens bundle, and the feasible
analogue of the oracle interval `wald_coverage_oracle` in `Wald.lean`.  The argument is:

* for each slack `ε ∈ (0,1)`, on the good-variance event `V̂ ≥ (1−ε)·directVar` the covering event
  `|D̂E − DE̅| ≤ z·√V̂` contains the studentized band `{−c ≤ W ≤ c}` with `c = z·√(1−ε)` and
  `W = (D̂E − DE̅)/√directVar`;
* the band probability has `liminf ≥ Φ(c) − Φ(−c)` by the direct-contrast CLT (lower-CDF machinery,
  `clt_interval_liminf_lb`), and the bad-variance event has probability `→ 0` (`hVhat`), so
  `liminf coverage ≥ 2·Φ(z·√(1−ε)) − 1`;
* letting `ε → 0⁺` and using Gaussian-CDF continuity gives `2·Φ(z) − 1 = 1 − γ`.

**Scope / faithfulness.** As in Aronow–Samii's headline `wald_coverage_feasible`, the estimator
`Vh` is taken abstractly and its conservative-consistency `hVhat` is a *hypothesis* — this is the
genuine input to the feasible interval.  Constructing a concrete Liu–Hudgens `V̂` (the between-group
sample variance of the ψ-selected group estimates plus the within-group Neyman estimators
`varHat`) and discharging `hVhat` from primitive conditions is the analogue of Aronow–Samii's
separate `wald_coverage_feasible_of_conditions`.  The in-expectation
conservativeness already proven (`E_varHat_conservative`, `Var ≤ E[V̂]`) is a necessary ingredient
toward `hVhat` but is *not* the same statement (it lacks the concentration half), so it is not
invoked here.  The direct-contrast CLT is supplied per threshold as `hclt` (exactly
`directEffect_clt`'s conclusion, quantified over `t`), decoupling this coverage statement from the
conditional-CLT plumbing — mirroring how `wald_coverage_oracle` takes its two CLT limits as
hypotheses.
-/

import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup
import Causalean.Experimentation.DesignBased.GaussianCDF
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Feasible Wald coverage

Feasible Wald intervals retain asymptotic coverage when the estimated variance does not undershoot.

The helper lemma `clt_interval_liminf_lb` turns per-threshold CLT limits into a lower bound for
two-sided studentized bands.  The public theorem `wald_coverage_feasible` then combines that band
bound with a conservative-consistency hypothesis on the variance estimator `Vh`, proving
asymptotic lower coverage for intervals of the form `estD ± zq * sqrt (Vh)`.
-/

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-- **STEP 1 — general CLT interval lower bound (Liu–Hudgens).** For any nonnegative threshold `c`,
the symmetric two-sided band probability `Pr[−c ≤ W ≤ c]` has `liminf` at least `Φ(c) − Φ(−c)`,
where `W = stud n` is the studentized statistic for the treatment-minus-control direct-effect
contrast.  Mirrors the `wald_coverage_oracle` lower-CDF machinery; the only input is the
per-threshold direct-contrast CLT `hclt`. -/
private lemma clt_interval_liminf_lb (Exp : ℕ → LHExperiment)
    (stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (hclt : ∀ t, Tendsto (fun n => (Exp n).jointD.Pr (fun sw => stud n sw ≤ t))
      atTop (𝓝 (stdNormalCdf t)))
    (c : ℝ) (hc : 0 ≤ c) :
    stdNormalCdf c - stdNormalCdf (-c) ≤
      Filter.liminf (fun n => (Exp n).jointD.Pr (fun sw =>
        -c ≤ stud n sw ∧ stud n sw ≤ c)) atTop := by
  set S : ℕ → ℝ := fun n =>
    (Exp n).jointD.Pr (fun sw => stud n sw ≤ c) with hSdef
  set Lo : ℕ → ℝ := fun n =>
    (Exp n).jointD.Pr (fun sw => stud n sw ≤ -c) with hLodef
  set J : ℕ → ℝ := fun n => (Exp n).jointD.Pr (fun sw =>
    -c ≤ stud n sw ∧ stud n sw ≤ c) with hJdef
  -- Limit of `S - Lo` is `Φ(c) - Φ(-c)`.
  have hS : Tendsto S atTop (𝓝 (stdNormalCdf c)) := hclt c
  have hLo : Tendsto Lo atTop (𝓝 (stdNormalCdf (-c))) := hclt (-c)
  have hlim : Tendsto (fun n => S n - Lo n) atTop (𝓝 (stdNormalCdf c - stdNormalCdf (-c))) :=
    hS.sub hLo
  -- Pointwise lower bound `S - Lo ≤ J`.
  have hbound : ∀ n, S n - Lo n ≤ J n := by
    intro n
    set W : (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ :=
      fun sw => stud n sw with hWdef
    have hsplit := (Exp n).jointD.Pr_split (fun sw => W sw ≤ c) (fun sw => W sw ≤ -c)
    have hfirst : (Exp n).jointD.Pr (fun sw => W sw ≤ c ∧ W sw ≤ -c) = Lo n := by
      apply (Exp n).jointD.Pr_congr
      intro sw
      constructor
      · exact fun h => h.2
      · intro h2
        exact ⟨le_trans h2 (by linarith), h2⟩
    have hSLo : S n - Lo n =
        (Exp n).jointD.Pr (fun sw => W sw ≤ c ∧ ¬ W sw ≤ -c) := by
      have : S n = (Exp n).jointD.Pr (fun sw => W sw ≤ c ∧ W sw ≤ -c)
          + (Exp n).jointD.Pr (fun sw => W sw ≤ c ∧ ¬ W sw ≤ -c) := hsplit
      rw [this, hfirst]; ring
    rw [hSLo]
    apply (Exp n).jointD.Pr_mono
    intro sw hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [not_le] at hz2
    exact ⟨le_of_lt hz2, hz1⟩
  -- Conclude with liminf.
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => S n - Lo n) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop J :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
      (fun n => (Exp n).jointD.Pr_le_one _)
  calc stdNormalCdf c - stdNormalCdf (-c)
      = Filter.liminf (fun n => S n - Lo n) atTop := hlim.liminf_eq.symm
    _ ≤ Filter.liminf J atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound) hbdd hcobdd

/-- **Asymptotic feasible Wald coverage (Liu–Hudgens 2014).** Along a sequence of two-stage
Hudgens–Halloran experiments `Exp`, write `stud n` for the studentized statistic for the
treatment-minus-control direct-effect contrast (pinned by `hstud`), and let `Vh n` be an arbitrary
variance estimator. Assume the per-threshold direct-contrast CLT (`hclt`, exactly
`directEffect_clt`'s conclusion ∀ `t`),
an everywhere-positive true variance (`hVar`), and that `Vh` is *conservative-consistent* — for
every slack `ε > 0` the bad event `V̂ < (1−ε)·directVar` has probability `→ 0` (`hVhat`).  With
`zq = z_{1−γ/2} ≥ 0` the standard-normal upper quantile (`hzq`), the **feasible** Wald interval
`D̂E ± zq·√(Vh)` attains asymptotic coverage of `DE̅` at least `1 − γ`. -/
theorem wald_coverage_feasible (Exp : ℕ → LHExperiment)
    (stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (hstud : ∀ n sw, stud n sw = ((Exp n).estD sw - (Exp n).DEbar) / Real.sqrt ((Exp n).directVar))
    (Vh : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (hclt : ∀ t, Tendsto (fun n => (Exp n).jointD.Pr (fun sw => stud n sw ≤ t))
      atTop (𝓝 (stdNormalCdf t)))
    (hVar : ∀ n, 0 < (Exp n).directVar)
    (hVhat : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (Exp n).jointD.Pr (fun sw =>
        Vh n sw < (1 - ε) * (Exp n).directVar)) atTop (𝓝 0))
    {γ : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - γ / 2) :
    1 - γ ≤ Filter.liminf
      (fun n => (Exp n).jointD.Pr (fun sw =>
        |(Exp n).estD sw - (Exp n).DEbar| ≤ zq * Real.sqrt (Vh n sw)))
      Filter.atTop := by
  -- The coverage probability sequence.
  set I : ℕ → ℝ := fun n => (Exp n).jointD.Pr (fun sw =>
    |(Exp n).estD sw - (Exp n).DEbar| ≤ zq * Real.sqrt (Vh n sw)) with hIdef
  -- `I` is coboundedly below (always ≤ 1).
  have hIcobdd : IsCoboundedUnder (· ≥ ·) atTop I :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ)) (fun n => (Exp n).jointD.Pr_le_one _)
  -- For each `ε ∈ (0,1)`, `liminf I ≥ 2·Φ(zq·√(1-ε)) - 1`.
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      2 * stdNormalCdf (zq * Real.sqrt (1 - ε)) - 1 ≤ Filter.liminf I atTop := by
    intro ε hε0 hε1
    set c : ℝ := zq * Real.sqrt (1 - ε) with hcdef
    have h1mε : (0 : ℝ) < 1 - ε := by linarith
    have hc0 : 0 ≤ c := mul_nonneg hzq0 (Real.sqrt_nonneg _)
    -- The CLT band probability and the "bad variance" probability.
    set B : ℕ → ℝ := fun n => (Exp n).jointD.Pr (fun sw =>
      -c ≤ stud n sw ∧ stud n sw ≤ c) with hBdef
    set A : ℕ → ℝ := fun n => (Exp n).jointD.Pr (fun sw =>
      Vh n sw < (1 - ε) * (Exp n).directVar) with hAdef
    have hA0 : Tendsto A atTop (𝓝 0) := hVhat ε hε0
    -- STEP 2: pointwise `B n - A n ≤ I n`.
    have hstep2 : ∀ n, B n - A n ≤ I n := by
      intro n
      set Vr : ℝ := (Exp n).directVar with hVrdef
      set σ : ℝ := Real.sqrt Vr with hσdef
      have hσpos : 0 < σ := Real.sqrt_pos.mpr (hVar n)
      set W : (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ :=
        fun sw => stud n sw with hWdef
      -- Split `B` by the bad-variance event.
      set Abad : (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → Prop :=
        fun sw => Vh n sw < (1 - ε) * Vr with hAbaddef
      set Bev : (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → Prop :=
        fun sw => -c ≤ W sw ∧ W sw ≤ c with hBevdef
      have hsplit := (Exp n).jointD.Pr_split Bev Abad
      -- `Pr(Bev ∧ Abad) ≤ A n`.
      have hBA : (Exp n).jointD.Pr (fun sw => Bev sw ∧ Abad sw) ≤ A n := by
        apply (Exp n).jointD.Pr_mono; intro sw hz; exact hz.2
      -- So `B n - A n ≤ Pr(Bev ∧ ¬Abad)`.
      have hBmA : B n - A n ≤ (Exp n).jointD.Pr (fun sw => Bev sw ∧ ¬ Abad sw) := by
        have hBeq : B n = (Exp n).jointD.Pr (fun sw => Bev sw ∧ Abad sw)
            + (Exp n).jointD.Pr (fun sw => Bev sw ∧ ¬ Abad sw) := hsplit
        linarith [hBeq, hBA]
      refine le_trans hBmA ?_
      -- `Pr(Bev ∧ ¬Abad) ≤ I n` by event inclusion.
      apply (Exp n).jointD.Pr_mono
      intro sw hz
      obtain ⟨⟨hzlo, hzhi⟩, hznotbad⟩ := hz
      rw [hAbaddef, not_lt] at hznotbad
      -- `|W sw| ≤ c`.
      have habsW : |W sw| ≤ c := abs_le.mpr ⟨hzlo, hzhi⟩
      -- `estD - DEbar = W sw * σ`.
      have hWσ : (Exp n).estD sw - (Exp n).DEbar = W sw * σ := by
        change (Exp n).estD sw - (Exp n).DEbar = stud n sw * σ
        rw [hstud n sw, ← hVrdef, ← hσdef]
        field_simp
      rw [hWσ, abs_mul, abs_of_pos hσpos]
      -- `|W sw| * σ ≤ c * σ = zq * √((1-ε)*Vr) ≤ zq * √(V̂)`.
      calc |W sw| * σ ≤ c * σ := by
              apply mul_le_mul_of_nonneg_right habsW hσpos.le
        _ = zq * Real.sqrt ((1 - ε) * Vr) := by
              rw [hcdef, hσdef, mul_assoc, ← Real.sqrt_mul h1mε.le]
        _ ≤ zq * Real.sqrt (Vh n sw) := by
              apply mul_le_mul_of_nonneg_left _ hzq0
              exact Real.sqrt_le_sqrt hznotbad
    -- STEP 3: liminf chain.
    -- `liminf B ≤ liminf (B - A)` since `A → 0`.
    have hBAliminf : Filter.liminf B atTop ≤ Filter.liminf (fun n => B n - A n) atTop := by
      have hnegA : Tendsto (fun n => -A n) atTop (𝓝 0) := by
        simpa using hA0.neg
      have hBbdd_ge : IsBoundedUnder (· ≥ ·) atTop B :=
        isBoundedUnder_of ⟨0, fun n => (Exp n).jointD.Pr_nonneg _⟩
      have hBbdd_le : IsBoundedUnder (· ≤ ·) atTop B :=
        isBoundedUnder_of ⟨1, fun n => (Exp n).jointD.Pr_le_one _⟩
      have hnegAbdd_ge : IsBoundedUnder (· ≥ ·) atTop (fun n => -A n) :=
        hnegA.isBoundedUnder_ge
      have hnegAcobdd : IsCoboundedUnder (· ≥ ·) atTop (fun n => -A n) :=
        hnegA.isBoundedUnder_le.isCoboundedUnder_ge
      have h := le_liminf_add (u := B) (v := fun n => -A n)
        hBbdd_ge hBbdd_le hnegAbdd_ge hnegAcobdd
      rw [hnegA.liminf_eq] at h
      simp only [add_zero] at h
      have hsub : (B + fun n => -A n) = fun n => B n - A n := by
        funext n; simp [sub_eq_add_neg]
      rwa [hsub] at h
    -- `liminf (B - A) ≤ liminf I` by pointwise bound.
    have hABI : Filter.liminf (fun n => B n - A n) atTop ≤ Filter.liminf I atTop := by
      have hBAbelow : IsBoundedUnder (· ≥ ·) atTop (fun n => B n - A n) := by
        refine isBoundedUnder_of ⟨-1, fun n => ?_⟩
        have hBn : 0 ≤ B n := by rw [hBdef]; exact (Exp n).jointD.Pr_nonneg _
        have hAn : A n ≤ 1 := by rw [hAdef]; exact (Exp n).jointD.Pr_le_one _
        change (-1 : ℝ) ≤ B n - A n
        linarith
      exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hstep2) hBAbelow hIcobdd
    -- STEP 1 gives `Φ(c) - Φ(-c) ≤ liminf B`.
    have hstep1 := clt_interval_liminf_lb Exp stud hclt c hc0
    -- Chain and rewrite `Φ(c) - Φ(-c) = 2·Φ(c) - 1`.
    have hΦ : stdNormalCdf c - stdNormalCdf (-c) = 2 * stdNormalCdf c - 1 := by
      rw [stdNormalCdf_neg c]; ring
    calc 2 * stdNormalCdf (zq * Real.sqrt (1 - ε)) - 1
        = stdNormalCdf c - stdNormalCdf (-c) := by rw [hcdef, hΦ]
      _ ≤ Filter.liminf B atTop := hstep1
      _ ≤ Filter.liminf (fun n => B n - A n) atTop := hBAliminf
      _ ≤ Filter.liminf I atTop := hABI
  -- STEP 4: let `ε → 0⁺` along `ε = 1/(k+1)`.  The RHS bound tends to `1 - γ`.
  set g : ℝ → ℝ := fun ε => 2 * stdNormalCdf (zq * Real.sqrt (1 - ε)) - 1 with hgdef
  have hgcont : Tendsto g (𝓝 0) (𝓝 (1 - γ)) := by
    have hsqrt : Tendsto (fun ε : ℝ => Real.sqrt (1 - ε)) (𝓝 0) (𝓝 1) := by
      have : Tendsto (fun ε : ℝ => (1 - ε)) (𝓝 0) (𝓝 (1 - 0)) :=
        (tendsto_const_nhds.sub tendsto_id)
      rw [sub_zero] at this
      have hc := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp this
      rw [Real.sqrt_one] at hc
      exact hc
    have hzqsqrt : Tendsto (fun ε : ℝ => zq * Real.sqrt (1 - ε)) (𝓝 0) (𝓝 zq) := by
      have := tendsto_const_nhds (x := zq) |>.mul hsqrt
      simpa using this
    have hΦc : Tendsto (fun ε : ℝ => stdNormalCdf (zq * Real.sqrt (1 - ε))) (𝓝 0)
        (𝓝 (stdNormalCdf zq)) :=
      (continuous_stdNormalCdf.tendsto zq).comp hzqsqrt
    have : Tendsto g (𝓝 0) (𝓝 (2 * stdNormalCdf zq - 1)) := by
      rw [hgdef]
      exact (tendsto_const_nhds.mul hΦc).sub tendsto_const_nhds
    have heq : 2 * stdNormalCdf zq - 1 = 1 - γ := by rw [hzq]; ring
    rwa [heq] at this
  -- Evaluate along `ε_k = 1/(k+1) → 0`, eventually in `(0,1)`.
  have hseq : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hgseq : Tendsto (fun k : ℕ => g (1 / (k + 1))) atTop (𝓝 (1 - γ)) :=
    hgcont.comp hseq
  -- `g (1/(k+1)) ≤ liminf I` eventually (for `k ≥ 1`, so `1/(k+1) ≤ 1/2 < 1`).
  have hev : ∀ᶠ k : ℕ in atTop, g (1 / (k + 1)) ≤ Filter.liminf I atTop := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun k hk => ?_⟩
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hden : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have hlt1 : (1 : ℝ) / (k + 1) < 1 := by
      rw [div_lt_one hden]; linarith
    exact key _ hpos hlt1
  exact le_of_tendsto hgseq hev

end TwoStageInterference
end Experimentation
end Causalean
