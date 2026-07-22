/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.SteinCLT
import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Asymptotic confidence intervals (Aronow–Samii 2017, Prop 6.5)

Given the local-dependence CLT interface and a nonzero limiting variance (Condition 4), the
Wald interval `τ̂ ± z_{1−α/2}·√Var[τ̂]` attains asymptotic coverage **at least** `1 − α`
(the paper's claim), formalized as `1 − α ≤ liminf` of the coverage probabilities.

The proof uses only the *lower* half of the CLT: the event `|τ̂ − τ| ≤ z·√Var` contains
`{−z < W ≤ z}` (with `W` the studentized statistic), whose probability is
`Pr[W ≤ z] − Pr[W ≤ −z] → Φ(z) − Φ(−z) = 1 − α` by the interface plus CDF symmetry
`Φ(−z) = 1 − Φ(z)`. (The matching upper bound — exact convergence to `1 − α` — would need
Gaussian-CDF continuity; the paper only claims "at least", so it is not pursued here.)
-/


open scoped BigOperators Topology Classical
open Filter

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

/-- **Proposition 6.5 (asymptotic coverage, true standard error).** Under the
local-dependence CLT (`hclt`) and an everywhere-positive variance (`hVar`, the operative form
of Condition 4 — nonzero limiting variance), with `zq = z_{1−α/2} ≥ 0` the standard-normal
upper quantile, the Wald interval centered at `τ̂` with the true standard error attains
asymptotic coverage at least `1 − α`. -/
theorem wald_coverage (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (hclt : LocalDependenceCLT Exp dk dl)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt ((Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))))
      Filter.atTop := by
  -- The studentized lower-CDF probabilities at `zq` and `-zq`.
  set S : ℕ → ℝ := fun n =>
    (Exp n).D.Pr (fun z => (Exp n).studentizedEffect (dk n) (dl n) z ≤ zq) with hSdef
  set Lo : ℕ → ℝ := fun n =>
    (Exp n).D.Pr (fun z => (Exp n).studentizedEffect (dk n) (dl n) z ≤ -zq) with hLodef
  set I : ℕ → ℝ := fun n => (Exp n).D.Pr (fun z =>
    |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
        - tauTrue (Exp n).y (dk n) (dl n)|
      ≤ zq * Real.sqrt ((Exp n).D.Var
          (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))) with hIdef
  -- (1) Limit of `S - Lo`.
  have hS : Tendsto S atTop (𝓝 (stdNormalCdf zq)) := hclt.tendsto_cdf zq
  have hLo : Tendsto Lo atTop (𝓝 (stdNormalCdf (-zq))) := hclt.tendsto_cdf (-zq)
  have hlim : Tendsto (fun n => S n - Lo n) atTop (𝓝 (1 - α)) := by
    have h := hS.sub hLo
    rw [stdNormalCdf_neg zq, hzq] at h
    have he : (1 - α / 2) - (1 - (1 - α / 2)) = 1 - α := by ring
    rwa [he] at h
  -- (2) Pointwise lower bound `S - Lo ≤ I`.
  have hbound : ∀ n, S n - Lo n ≤ I n := by
    intro n
    -- Abbreviate the studentized statistic.
    set W : (Exp n).Ω → ℝ := fun z => (Exp n).studentizedEffect (dk n) (dl n) z with hWdef
    -- Split `S` by the event `W ≤ -zq`.
    have hsplit := (Exp n).D.Pr_split (fun z => W z ≤ zq) (fun z => W z ≤ -zq)
    -- The first piece equals `Lo`.
    have hfirst : (Exp n).D.Pr (fun z => W z ≤ zq ∧ W z ≤ -zq) = Lo n := by
      apply (Exp n).D.Pr_congr
      intro z
      constructor
      · exact fun h => h.2
      · intro h2
        exact ⟨le_trans h2 (by linarith [hzq0]), h2⟩
    -- So `S - Lo` is the probability of the second piece.
    have hSLo : S n - Lo n =
        (Exp n).D.Pr (fun z => W z ≤ zq ∧ ¬ W z ≤ -zq) := by
      have : S n = (Exp n).D.Pr (fun z => W z ≤ zq ∧ W z ≤ -zq)
          + (Exp n).D.Pr (fun z => W z ≤ zq ∧ ¬ W z ≤ -zq) := hsplit
      rw [this, hfirst]; ring
    rw [hSLo]
    -- That second piece is contained in `I`'s event.
    apply (Exp n).D.Pr_mono
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [not_le] at hz2
    -- `|W z| ≤ zq`.
    have habs : |W z| ≤ zq := abs_le.mpr ⟨le_of_lt hz2, hz1⟩
    -- Unfold the studentized statistic.
    set s : ℝ := Real.sqrt ((Exp n).D.Var
        (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))) with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr (hVar n)
    rw [hWdef] at habs
    simp only [Experiment.studentizedEffect] at habs
    rw [← hsdef] at habs
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs] at habs
    exact habs
  -- (3) Conclude with liminf.
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => S n - Lo n) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop I :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
      (fun n => (Exp n).D.Pr_le_one _)
  calc 1 - α = Filter.liminf (fun n => S n - Lo n) atTop := hlim.liminf_eq.symm
    _ ≤ Filter.liminf I atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound) hbdd hcobdd

/-- **STEP 1 — general CLT interval lower bound.** For any nonnegative threshold `c`, the
symmetric two-sided interval probability `Pr[-c ≤ W ≤ c]` has `liminf` at least `Φ(c) - Φ(-c)`,
where `W` is the studentized statistic. Mirrors the `wald_coverage` lower-CDF machinery. -/
private lemma clt_interval_liminf_lb (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (hclt : LocalDependenceCLT Exp dk dl) (c : ℝ) (hc : 0 ≤ c) :
    stdNormalCdf c - stdNormalCdf (-c) ≤
      Filter.liminf (fun n => (Exp n).D.Pr (fun z =>
        -c ≤ (Exp n).studentizedEffect (dk n) (dl n) z ∧
          (Exp n).studentizedEffect (dk n) (dl n) z ≤ c)) atTop := by
  set S : ℕ → ℝ := fun n =>
    (Exp n).D.Pr (fun z => (Exp n).studentizedEffect (dk n) (dl n) z ≤ c) with hSdef
  set Lo : ℕ → ℝ := fun n =>
    (Exp n).D.Pr (fun z => (Exp n).studentizedEffect (dk n) (dl n) z ≤ -c) with hLodef
  set J : ℕ → ℝ := fun n => (Exp n).D.Pr (fun z =>
    -c ≤ (Exp n).studentizedEffect (dk n) (dl n) z ∧
      (Exp n).studentizedEffect (dk n) (dl n) z ≤ c) with hJdef
  -- Limit of `S - Lo` is `Φ(c) - Φ(-c)`.
  have hS : Tendsto S atTop (𝓝 (stdNormalCdf c)) := hclt.tendsto_cdf c
  have hLo : Tendsto Lo atTop (𝓝 (stdNormalCdf (-c))) := hclt.tendsto_cdf (-c)
  have hlim : Tendsto (fun n => S n - Lo n) atTop (𝓝 (stdNormalCdf c - stdNormalCdf (-c))) :=
    hS.sub hLo
  -- Pointwise lower bound `S - Lo ≤ J`.
  have hbound : ∀ n, S n - Lo n ≤ J n := by
    intro n
    set W : (Exp n).Ω → ℝ := fun z => (Exp n).studentizedEffect (dk n) (dl n) z with hWdef
    have hsplit := (Exp n).D.Pr_split (fun z => W z ≤ c) (fun z => W z ≤ -c)
    have hfirst : (Exp n).D.Pr (fun z => W z ≤ c ∧ W z ≤ -c) = Lo n := by
      apply (Exp n).D.Pr_congr
      intro z
      constructor
      · exact fun h => h.2
      · intro h2
        exact ⟨le_trans h2 (by linarith), h2⟩
    have hSLo : S n - Lo n =
        (Exp n).D.Pr (fun z => W z ≤ c ∧ ¬ W z ≤ -c) := by
      have : S n = (Exp n).D.Pr (fun z => W z ≤ c ∧ W z ≤ -c)
          + (Exp n).D.Pr (fun z => W z ≤ c ∧ ¬ W z ≤ -c) := hsplit
      rw [this, hfirst]; ring
    rw [hSLo]
    apply (Exp n).D.Pr_mono
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [not_le] at hz2
    exact ⟨le_of_lt hz2, hz1⟩
  -- Conclude with liminf.
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => S n - Lo n) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop J :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
      (fun n => (Exp n).D.Pr_le_one _)
  calc stdNormalCdf c - stdNormalCdf (-c)
      = Filter.liminf (fun n => S n - Lo n) atTop := hlim.liminf_eq.symm
    _ ≤ Filter.liminf J atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound) hbdd hcobdd

/-- **Proposition 6.5 (asymptotic coverage, feasible/estimated standard error — the paper's actual
interval).** Under the local-dependence CLT (`hclt`), positive variance (`hVar`), and
variance-estimator consistency (`hVhat`: the conservative estimate `V̂` undershoots the true
variance with vanishing probability), the Wald interval `τ̂ ± z_{1−α/2}·√(V̂[τ̂])` — using the
**estimated** variance `htEffectVarEst`, exactly as in Aronow–Samii Prop 6.5 — attains asymptotic
coverage at least `1 − α`. -/
theorem wald_coverage_feasible (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (hclt : LocalDependenceCLT Exp dk dl)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hVhat : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (Exp n).D.Pr (fun z =>
        htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
          < (1 - ε) * (Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))))
      atTop (𝓝 0))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt
              (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z)))
      Filter.atTop := by
  -- The coverage probability sequence.
  set I : ℕ → ℝ := fun n => (Exp n).D.Pr (fun z =>
    |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
        - tauTrue (Exp n).y (dk n) (dl n)|
      ≤ zq * Real.sqrt
          (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z)) with hIdef
  -- `I` is coboundedly below (always ≤ 1).
  have hIcobdd : IsCoboundedUnder (· ≥ ·) atTop I :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ)) (fun n => (Exp n).D.Pr_le_one _)
  have hIbdd : IsBoundedUnder (· ≤ ·) atTop I :=
    isBoundedUnder_of ⟨1, fun n => (Exp n).D.Pr_le_one _⟩
  -- For each `ε ∈ (0,1)`, `liminf I ≥ 2·Φ(zq·√(1-ε)) - 1`.
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      2 * stdNormalCdf (zq * Real.sqrt (1 - ε)) - 1 ≤ Filter.liminf I atTop := by
    intro ε hε0 hε1
    set c : ℝ := zq * Real.sqrt (1 - ε) with hcdef
    have h1mε : (0 : ℝ) < 1 - ε := by linarith
    have hc0 : 0 ≤ c := mul_nonneg hzq0 (Real.sqrt_nonneg _)
    -- The CLT interval probability and the "bad variance" probability.
    set B : ℕ → ℝ := fun n => (Exp n).D.Pr (fun z =>
      -c ≤ (Exp n).studentizedEffect (dk n) (dl n) z ∧
        (Exp n).studentizedEffect (dk n) (dl n) z ≤ c) with hBdef
    set A : ℕ → ℝ := fun n => (Exp n).D.Pr (fun z =>
      htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
        < (1 - ε) * (Exp n).D.Var
            (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))) with hAdef
    have hA0 : Tendsto A atTop (𝓝 0) := hVhat ε hε0
    -- STEP 2: pointwise `B n - A n ≤ I n`.
    have hstep2 : ∀ n, B n - A n ≤ I n := by
      intro n
      set Vr : ℝ := (Exp n).D.Var
        (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)) with hVrdef
      set σ : ℝ := Real.sqrt Vr with hσdef
      have hσpos : 0 < σ := Real.sqrt_pos.mpr (hVar n)
      have hσ2 : σ ^ 2 = Vr := Real.sq_sqrt (hVar n).le
      set W : (Exp n).Ω → ℝ := fun z => (Exp n).studentizedEffect (dk n) (dl n) z with hWdef
      -- Split `B` by the bad-variance event.
      set Abad : (Exp n).Ω → Prop := fun z =>
        htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z < (1 - ε) * Vr
        with hAbaddef
      set Bev : (Exp n).Ω → Prop := fun z => -c ≤ W z ∧ W z ≤ c with hBevdef
      have hsplit := (Exp n).D.Pr_split Bev Abad
      -- `Pr(Bev ∧ Abad) ≤ A n`.
      have hBA : (Exp n).D.Pr (fun z => Bev z ∧ Abad z) ≤ A n := by
        apply (Exp n).D.Pr_mono; intro z hz; exact hz.2
      -- So `B n - A n ≤ Pr(Bev ∧ ¬Abad)`.
      have hBmA : B n - A n ≤ (Exp n).D.Pr (fun z => Bev z ∧ ¬ Abad z) := by
        have hBeq : B n = (Exp n).D.Pr (fun z => Bev z ∧ Abad z)
            + (Exp n).D.Pr (fun z => Bev z ∧ ¬ Abad z) := hsplit
        linarith [hBeq, hBA]
      refine le_trans hBmA ?_
      -- `Pr(Bev ∧ ¬Abad) ≤ I n` by event inclusion.
      apply (Exp n).D.Pr_mono
      intro z hz
      obtain ⟨⟨hzlo, hzhi⟩, hznotbad⟩ := hz
      rw [hAbaddef, not_lt] at hznotbad
      -- `|W z| ≤ c`.
      have habsW : |W z| ≤ c := abs_le.mpr ⟨hzlo, hzhi⟩
      -- `htEffect - tauTrue = W z * σ`.
      have hWσ : htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
          - tauTrue (Exp n).y (dk n) (dl n) = W z * σ := by
        rw [hWdef]
        simp only [Experiment.studentizedEffect]
        rw [← hVrdef, ← hσdef]
        field_simp
      rw [hWσ, abs_mul, abs_of_pos hσpos]
      -- `|W z| * σ ≤ c * σ = zq * √((1-ε)*Vr) ≤ zq * √(V̂)`.
      calc |W z| * σ ≤ c * σ := by
              apply mul_le_mul_of_nonneg_right habsW hσpos.le
        _ = zq * Real.sqrt ((1 - ε) * Vr) := by
              rw [hcdef, hσdef, mul_assoc, ← Real.sqrt_mul h1mε.le]
        _ ≤ zq * Real.sqrt
              (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z) := by
              apply mul_le_mul_of_nonneg_left _ hzq0
              exact Real.sqrt_le_sqrt hznotbad
    -- STEP 3: liminf chain.
    -- `liminf B ≤ liminf (B - A)` since `A → 0`.
    have hBAliminf : Filter.liminf B atTop ≤ Filter.liminf (fun n => B n - A n) atTop := by
      have hnegA : Tendsto (fun n => -A n) atTop (𝓝 0) := by
        simpa using hA0.neg
      have hBbdd_ge : IsBoundedUnder (· ≥ ·) atTop B :=
        isBoundedUnder_of ⟨0, fun n => (Exp n).D.Pr_nonneg _⟩
      have hBbdd_le : IsBoundedUnder (· ≤ ·) atTop B :=
        isBoundedUnder_of ⟨1, fun n => (Exp n).D.Pr_le_one _⟩
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
        have hBn : 0 ≤ B n := by rw [hBdef]; exact (Exp n).D.Pr_nonneg _
        have hAn : A n ≤ 1 := by rw [hAdef]; exact (Exp n).D.Pr_le_one _
        change (-1 : ℝ) ≤ B n - A n
        linarith
      exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hstep2) hBAbelow hIcobdd
    -- STEP 1 gives `Φ(c) - Φ(-c) ≤ liminf B`.
    have hstep1 := clt_interval_liminf_lb Exp dk dl hclt c hc0
    -- Chain and rewrite `Φ(c) - Φ(-c) = 2·Φ(c) - 1`.
    have hΦ : stdNormalCdf c - stdNormalCdf (-c) = 2 * stdNormalCdf c - 1 := by
      rw [stdNormalCdf_neg c]; ring
    calc 2 * stdNormalCdf (zq * Real.sqrt (1 - ε)) - 1
        = stdNormalCdf c - stdNormalCdf (-c) := by rw [hcdef, hΦ]
      _ ≤ Filter.liminf B atTop := hstep1
      _ ≤ Filter.liminf (fun n => B n - A n) atTop := hBAliminf
      _ ≤ Filter.liminf I atTop := hABI
  -- STEP 4: let `ε → 0⁺` along `ε = 1/(k+1)`.
  -- The RHS bound tends to `1 - α`.
  set g : ℝ → ℝ := fun ε => 2 * stdNormalCdf (zq * Real.sqrt (1 - ε)) - 1 with hgdef
  have hgcont : Tendsto g (𝓝 0) (𝓝 (1 - α)) := by
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
    have heq : 2 * stdNormalCdf zq - 1 = 1 - α := by rw [hzq]; ring
    rwa [heq] at this
  -- Evaluate along `ε_k = 1/(k+1) → 0`, eventually in `(0,1)`.
  have hseq : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hgseq : Tendsto (fun k : ℕ => g (1 / (k + 1))) atTop (𝓝 (1 - α)) :=
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

end ExposureMappingInterference
end Experimentation
end Causalean
