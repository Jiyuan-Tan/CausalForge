/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative
import Causalean.Experimentation.DesignBased.Chebyshev
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.Consistency
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.Intervals

/-!
# Consistency of the conservative variance estimator (Aronow–Samii 2017)

The feasible Wald interval of Aronow–Samii (Prop 6.5) uses the *estimated* variance `Vh`
(`htEffectVarEst`).  Its asymptotic coverage (`wald_coverage_feasible`) consumes a single
analytic input: the conservative estimate undershoots the true variance only with vanishing
probability,

  `∀ ε > 0, Pr[ Vh < (1−ε)·Var[τ̂] ] → 0`.

This file **reduces that input to one clean L²-relative-consistency limit**

  `Var[Vh] / Var[τ̂]² → 0`

via the finite Chebyshev inequality and the already-proven conservativeness
`Var[τ̂] ≤ E[Vh]` (`E_htEffectVarEst_ge`, Prop 5.x):

  `{ Vh < (1−ε)·Var } ⊆ { ε·Var ≤ |Vh − E Vh| }`  (using `E Vh ≥ Var`),
  `Pr[ ε·Var ≤ |Vh − E Vh| ] ≤ Var[Vh]/(ε·Var)² = (1/ε²)·(Var[Vh]/Var²)`,

and the right side tends to `0`.  The hypothesis `Var[Vh]/Var² → 0` is the precise,
isolated remaining input — the quantitative content of the paper's appendix
variance-estimator-consistency bound under Conditions 1/3/4.  Note that under Condition 4
(`N·Var → c > 0`, so `Var ∼ c/N`) this relative limit is equivalent to `Var[N·Vh] → 0`.
-/


open scoped BigOperators Topology Classical
open Filter

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

/-- **Reduction of feasible-interval variance consistency to L²-relative consistency.**
Given the standing overlap/no-degeneracy conditions (so the conservativeness
`Var[τ̂] ≤ E[Vh]` holds), positive true variance, and the L²-relative-consistency limit
`Var[Vh]/Var[τ̂]² → 0`, the conservative variance estimator undershoots the true variance
only with vanishing probability: for every `ε > 0`,
`Pr[ Vh < (1−ε)·Var[τ̂] ] → 0`.  This is exactly the hypothesis `hVhat` consumed by
`wald_coverage_feasible`. -/
theorem htEffectVarEst_undershoot_tendsto_zero
    (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (hne : ∀ n, dk n ≠ dl n)
    (hk : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≠ 0)
    (hl : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≠ 0)
    (hjk : ∀ n i j, i ≠ j →
      propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n) ≠ 0)
    (hjl : ∀ n i j, i ≠ j →
      propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n) ≠ 0)
    (hjc : ∀ n i j, i ≠ j →
      propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n) ≠ 0)
    (hVarpos : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hrel : Tendsto (fun n =>
        (Exp n).D.Var
            (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))
          / ((Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))) ^ 2)
        atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (Exp n).D.Pr (fun z =>
        htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
          < (1 - ε) * (Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))))
      atTop (𝓝 0) := by
  intro ε hε0
  have hεne : ε ≠ 0 := hε0.ne'
  -- Squeeze the coverage-defect probability between `0` and `(1/ε²)·(Var[Vh]/Var²)`.
  refine squeeze_zero (g := fun n => (1 / ε ^ 2) *
      ((Exp n).D.Var
          (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))
        / ((Exp n).D.Var
            (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))) ^ 2))
      (fun n => (Exp n).D.Pr_nonneg _) (fun n => ?_) ?_
  · -- Per-`n` upper bound via event inclusion + Chebyshev.
    set Vh : (Exp n).Ω → ℝ :=
      htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) with hVh
    set Vr : ℝ := (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)) with hVr
    have hVrpos : 0 < Vr := hVarpos n
    have hVrne : Vr ≠ 0 := hVrpos.ne'
    -- Conservativeness: `E[Vh] ≥ Var[τ̂]`.
    have hEge : Vr ≤ (Exp n).D.E Vh :=
      E_htEffectVarEst_ge (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)
        (hne n) (hk n) (hl n) (hjk n) (hjl n) (hjc n)
    have haε : 0 < ε * Vr := mul_pos hε0 hVrpos
    -- `{ Vh < (1−ε)Vr } ⊆ { ε·Vr ≤ |Vh − E Vh| }`.
    have hsub : ∀ z, Vh z < (1 - ε) * Vr → ε * Vr ≤ |Vh z - (Exp n).D.E Vh| := by
      intro z hz
      have hexpand : (1 - ε) * Vr = Vr - ε * Vr := by ring
      have hz' : Vh z < Vr - ε * Vr := by rw [hexpand] at hz; exact hz
      have h1 : Vh z - (Exp n).D.E Vh < -(ε * Vr) := by linarith [hz', hEge]
      have h2 : -(Vh z - (Exp n).D.E Vh) ≤ |Vh z - (Exp n).D.E Vh| :=
        neg_le_abs _
      linarith
    have hmono := (Exp n).D.Pr_mono
      (fun z => Vh z < (1 - ε) * Vr)
      (fun z => ε * Vr ≤ |Vh z - (Exp n).D.E Vh|) hsub
    have hcheb := (Exp n).D.chebyshev Vh haε
    calc (Exp n).D.Pr (fun z => Vh z < (1 - ε) * Vr)
        ≤ (Exp n).D.Pr (fun z => ε * Vr ≤ |Vh z - (Exp n).D.E Vh|) := hmono
      _ ≤ (Exp n).D.Var Vh / (ε * Vr) ^ 2 := hcheb
      _ = (1 / ε ^ 2) * ((Exp n).D.Var Vh / Vr ^ 2) := by
            rw [mul_pow]; field_simp
  · -- `(1/ε²)·(Var[Vh]/Var²) → (1/ε²)·0 = 0`.
    have h := hrel.const_mul (1 / ε ^ 2)
    simpa using h

/-- **Feasible Wald coverage from L²-relative variance consistency (capstone).**
Combining the variance-consistency reduction (`htEffectVarEst_undershoot_tendsto_zero`) with
the feasible-interval coverage theorem (`wald_coverage_feasible`), the paper's actual interval
`τ̂ ± z_{1−α/2}·√V̂` attains asymptotic coverage `≥ 1 − α` once the single analytic input
`Var[V̂]/Var[τ̂]² → 0` is supplied (in addition to the local-dependence CLT, positive variance,
and the standing overlap/no-degeneracy conditions).  This is the feasible counterpart of
`wald_coverage_of_conditions` with the variance-estimator-consistency premise reduced to its
quantitative core. -/
theorem wald_coverage_feasible_of_relVar
    (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (hclt : LocalDependenceCLT Exp dk dl)
    (hne : ∀ n, dk n ≠ dl n)
    (hk : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≠ 0)
    (hl : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≠ 0)
    (hjk : ∀ n i j, i ≠ j →
      propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n) ≠ 0)
    (hjl : ∀ n i j, i ≠ j →
      propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n) ≠ 0)
    (hjc : ∀ n i j, i ≠ j →
      propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n) ≠ 0)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hrel : Tendsto (fun n =>
        (Exp n).D.Var
            (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))
          / ((Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))) ^ 2)
        atTop (𝓝 0))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt
              (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z)))
      Filter.atTop :=
  wald_coverage_feasible Exp dk dl hclt hVar
    (htEffectVarEst_undershoot_tendsto_zero Exp dk dl hne hk hl hjk hjl hjc hVar hrel)
    zq hzq0 hzq

/-- **Bridge from `Var[N·V̂] → 0` to L²-relative consistency.**  The paper's appendix establishes
`Var[N·V̂_n] → 0` (here as `N²·Var[V̂_n] → 0`); together with Condition 4
(`N·Var[τ̂_n] → c > 0`) this yields the relative limit `Var[V̂_n]/Var[τ̂_n]² → 0`, via the
identity `Var[V̂]/Var² = (N²·Var[V̂])/(N·Var)²` and `Tendsto.div` (numerator `→ 0`, denominator
`→ c² > 0`). -/
theorem relVar_of_NsqVar_tendsto
    (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    {c : ℝ} (hc : 0 < c)
    (hCond4 : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ) *
        (Exp n).D.Var (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
      atTop (𝓝 c))
    (hVN : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ) ^ 2 *
        (Exp n).D.Var
          (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
      atTop (𝓝 0)) :
    Tendsto (fun n =>
        (Exp n).D.Var
            (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))
          / ((Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))) ^ 2)
      atTop (𝓝 0) := by
  set card : ℕ → ℝ := fun n => (Fintype.card (Exp n).ι : ℝ) with hcard
  set Vr : ℕ → ℝ := fun n =>
    (Exp n).D.Var (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)) with hVrdef
  set Vh : ℕ → ℝ := fun n =>
    (Exp n).D.Var (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))
    with hVhdef
  -- `(N·Vr)² → c² ≠ 0`, and `N²·Vh → 0`, so the quotient tends to `0/c² = 0`.
  have hf : Tendsto (fun n => card n ^ 2 * Vh n / (card n * Vr n) ^ 2) atTop (𝓝 0) := by
    have := hVN.div (hCond4.pow 2) (pow_ne_zero 2 hc.ne')
    simpa using this
  -- Eventually `N·Vr > 0`, hence `N ≠ 0` and `Vr ≠ 0`, giving the algebraic identity.
  have hpos : ∀ᶠ n in atTop, 0 < card n * Vr n :=
    hCond4.eventually (eventually_gt_nhds hc)
  have hev : (fun n => card n ^ 2 * Vh n / (card n * Vr n) ^ 2)
      =ᶠ[atTop] (fun n => Vh n / Vr n ^ 2) := by
    filter_upwards [hpos] with n hn
    have hne : card n * Vr n ≠ 0 := hn.ne'
    have hcardn : card n ≠ 0 := fun h => hne (by rw [h, zero_mul])
    rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 hcardn)]
  exact hf.congr' hev

end ExposureMappingInterference
end Experimentation
end Causalean
