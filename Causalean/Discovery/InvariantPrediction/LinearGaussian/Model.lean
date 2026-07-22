/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DAG
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

/-!
# Invariant Causal Prediction — linear-Gaussian model layer

Setup of the **linear-Gaussian** identifiability theorem of Peters, Bühlmann &
Meinshausen, *Causal inference using invariant prediction* (JRSS-B 2016,
`arXiv:1501.01332`), Theorem `prop:1`(i) (the **do-intervention** version).

This is a *self-contained* linear-Gaussian framework, deliberately separate from
the nonparametric SWIG/kernel `EnvFamily` development in the sibling files.  It
uses the **random-variable** encoding of `Discovery/LiNGAM/Kurtosis.lean`:
variables are real functions on a probability space, with `∫`/`E[·]` for moments
and `IdentDistrib` for equality in distribution.

## Encoding choices

* **Index convention.**  The paper uses variables `X₁,…,X_{p+1}` with target
  `Y = X₁` and predictors `X₂,…,X_{p+1}`.  We index nodes by `Fin (p+1)` and put
  the **target at index `0`**, predictors at `1,…,p`.  So `target = 0` and the
  predictor index set is `{1,…,p} = {k : k ≠ 0}` (`Finset.univ.erase 0`).  This
  is a pure 0-based relabelling of the paper's `1,…,p+1`; `PA(Y)` is then a
  subset of `{k : k ≠ 0}`.

* **One coefficient matrix, one DAG.**  The observational SEM `e = 1`
  (`eq:semmmmm`) carries the coefficients `β : Matrix (Fin (p+1)) (Fin (p+1)) ℝ`
  with `Xⱼ = Σ_{k≠j} βⱼₖ Xₖ + εⱼ`.  Acyclicity is witnessed by a `DAG` whose
  edge `k → j` holds exactly when `βⱼₖ ≠ 0` (`hEdge`); reusing `Causalean.DAG`
  gives parents / descendants / topological order / the "youngest node" notion
  for free.  `PA(Y) = {k : β 0 k ≠ 0}` is then literally `dag.parents 0`.

* **Gaussian noise, random-variable form.**  The observational SEM has its own
  probability space with observed coordinates, and do-intervention environments
  live on that same probability space with the same structural noises.
  Independence of the noises and their Gaussian marginals are stated on the
  *observational* environment only (that is where the graph/`β`/Gaussianity live).

* **Do-interventions (`sec:idfirst`).**  In environment `e` an intervention set
  `A e ⊆ {1,…,p}` and values `a e : Fin (p+1) → ℝ` replace the structural
  equation of each `j ∈ A e` by the constant `a e j` (zeroing its row of `β` and
  replacing `εⱼ` by `a e j`).  Per the paper, `0 ∉ A e` (never intervene on the
  target) and `A 1 = ∅` (observational).

The do-version's proof (later) is a **mean-shift** argument
(`R^{e₀} = α_{k₀} a_{k₀} + …` vs. `R^1 = α_{k₀} X_{k₀}^1 + …`, eq:help1/help2),
so the model exposes residual means / laws cleanly via `IdentDistrib` and `∫`.
-/

namespace Causalean.Discovery.InvariantPrediction.LinearGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {p : ℕ}

/-- The target node `Y = X₁`, encoded at index `0` of `Fin (p+1)`. -/
abbrev target (p : ℕ) : Fin (p + 1) := 0

/-- The predictor index set `{X₂,…,X_{p+1}}`, encoded as `{k : k ≠ 0}`. -/
def predictors (p : ℕ) : Finset (Fin (p + 1)) := Finset.univ.erase 0

/-- A node is a predictor exactly when it is not the target node. -/
@[simp] theorem mem_predictors {k : Fin (p + 1)} : k ∈ predictors p ↔ k ≠ 0 := by
  simp [predictors]

/-- The **observational linear-Gaussian SEM** (`eq:semmmmm`), the `e = 1` block.

It fixes the structural coefficients `β` (with `Xⱼ = Σ_{k≠j} βⱼₖ Xₖ + εⱼ`), the
acyclic graph whose edge `k → j` is `βⱼₖ ≠ 0`, the noise variances `σ²`, and the
joint law on its own probability space `Ω`: the coordinates solve the structural
equations a.e., the noises `ε` are jointly independent `N(0, σⱼ²)`, and they are
the structural residuals `εⱼ = Xⱼ − Σ_{k≠j} βⱼₖ Xₖ`.  This is the only block that
carries the graph, the coefficients and the Gaussianity. -/
structure ObsSEM (p : ℕ) where
  /-- Sample space of the observational environment. -/
  Ω : Type*
  /-- Measurable structure on `Ω`. -/
  mΩ : MeasurableSpace Ω
  /-- The observational probability measure `P¹`. -/
  P : Measure Ω
  /-- `P¹` is a probability measure. -/
  hP : IsProbabilityMeasure P
  /-- The structural coefficients `βⱼₖ` (row `j`, column `k`). -/
  β : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ
  /-- The noise standard deviations `σⱼ` (`εⱼ ~ N(0, σⱼ²)`). -/
  σ : Fin (p + 1) → ℝ
  /-- The noises are nondegenerate (`σⱼ > 0`), as in a genuine Gaussian SEM. -/
  hσpos : ∀ j, 0 < σ j
  /-- The acyclic graph of the SEM; its edges are the nonzero coefficients. -/
  dag : Causalean.DAG (Fin (p + 1))
  /-- The graph edge `k → j` holds exactly when the coefficient `βⱼₖ` is nonzero. -/
  hEdge : ∀ j k, dag.edge k j ↔ β j k ≠ 0
  /-- No self-loops: a variable does not enter its own structural equation. -/
  hNoSelf : ∀ j, β j j = 0
  /-- The observed coordinates `X : Ω → (Fin (p+1) → ℝ)`. -/
  X : Ω → Fin (p + 1) → ℝ
  /-- Each coordinate is measurable. -/
  hXmeas : ∀ j, Measurable fun ω => X ω j
  /-- The structural noises `εⱼ = Xⱼ − Σ_{k≠j} βⱼₖ Xₖ`. -/
  ε : Ω → Fin (p + 1) → ℝ
  /-- The noises are the structural residuals (definitional, stated a.e.). -/
  hε : ∀ᵐ ω ∂P, ∀ j, ε ω j = X ω j - ∑ k ∈ Finset.univ.erase j, β j k * X ω k
  /-- The noises are jointly independent. -/
  hindep : iIndepFun (fun j ω => ε ω j) P
  /-- Each noise is centered Gaussian with variance `σⱼ²`:
  the law of `εⱼ` under `P` is `N(0, σⱼ²)`. -/
  hGauss : ∀ j, P.map (fun ω => ε ω j) = gaussianReal 0 ⟨(σ j) ^ 2, by positivity⟩
  /-- **Target exogeneity (the paper's Assumption 1, `ε ⊥ X_{S*}`).**  The target
  noise `ε₀` is independent of each *parent* coordinate `Xₖ` (`k ∈ PA(Y)`, i.e.
  `dag.edge k 0`).  In a recursive SEM this is a *consequence* of the joint noise
  independence (`hindep`) plus acyclicity — the parents of `Y` are non-descendants
  of `Y`, so they are functions of noises other than `ε₀` — but the random-variable
  encoding here does not expose the `ε → X` solve `X = (I−B)⁻¹ε`, so we carry it as
  a field.  It is stated **only for parents** of the target: it is *false* for
  descendants of `Y`. -/
  hYexo : ∀ k, dag.edge k (target p) → IndepFun (fun ω => ε ω (target p)) (fun ω => X ω k) P

attribute [instance] ObsSEM.mΩ ObsSEM.hP

namespace ObsSEM

variable (M : ObsSEM p)

/-- The parents of the target `Y` in the observational graph:
`PA(Y) = {k : β 0 k ≠ 0}`.  This is the set the completeness theorem recovers. -/
def paY : Finset (Fin (p + 1)) := M.dag.parents (target p)

/-- `PA(Y)` consists of predictors only (`0 ∉ PA(Y)`): the target is acyclic, so
it is not its own parent. -/
theorem paY_subset_predictors : M.paY ⊆ predictors p := by
  intro k hk
  rw [mem_predictors]
  rintro rfl
  exact M.dag.irrefl (target p) (M.dag.mem_parents.mp hk)

/-- Membership in `PA(Y)` is exactly a nonzero target coefficient. -/
theorem mem_paY {k : Fin (p + 1)} : k ∈ M.paY ↔ M.β (target p) k ≠ 0 := by
  rw [paY, M.dag.mem_parents, M.hEdge]

end ObsSEM

/-- A single **do-intervention environment** for the observational SEM `M`
(`sec:idfirst`).

Faithful do-semantics (modularity / autonomy): the environment is the
observational SEM with the structural equations of the intervened nodes `A`
replaced by the assigned constants `a`, **on the same probability space `M.Ω`
and driven by the same noises `M.ε`** as `M`.  The post-intervention coordinates
`X : M.Ω → Fin (p+1) → ℝ` therefore satisfy: `Xⱼ = aⱼ` for `j ∈ A`, and the
unchanged structural equation `Xⱼ = εⱼ + Σ_{k≠j} βⱼₖ Xₖ` for `j ∉ A` (same `β`,
same `ε`).

With this encoding the target's invariance (`assum:invariant`: since `0 ∉ A`, the
target keeps its equation, its noise `ε₀`'s law, and `ε₀`'s independence of the
predictors — all inherited from `M`) and the fact that **non-descendants of `A`
keep their observational values** are *consequences* of the structure, exactly as
in `propos:sem`, rather than separately-imposed axioms. -/
structure Env (M : ObsSEM p) where
  /-- The do-intervention target set `Aᵉ` (never the target `0`). -/
  A : Finset (Fin (p + 1))
  /-- The intervention never acts on the target. -/
  hAtarget : target p ∉ A
  /-- The assigned values `aᵉⱼ` for `j ∈ Aᵉ`. -/
  a : Fin (p + 1) → ℝ
  /-- The post-intervention coordinates, on `M`'s probability space. -/
  X : M.Ω → Fin (p + 1) → ℝ
  /-- Each coordinate is measurable. -/
  hXmeas : ∀ j, Measurable fun ω => X ω j
  /-- do-pin: each intervened coordinate equals its assigned constant a.e. -/
  hDoPin : ∀ j ∈ A, ∀ᵐ ω ∂M.P, X ω j = a j
  /-- Modularity: each un-intervened coordinate keeps the observational
  structural equation, with the **same** coefficients `β` and noises `ε` as `M`. -/
  hDoStruct : ∀ j, j ∉ A → ∀ᵐ ω ∂M.P,
    X ω j = M.ε ω j + ∑ k ∈ Finset.univ.erase j, M.β j k * X ω k
  /-- **Target exogeneity in this environment (the paper's Assumption 1).**  The
  target keeps its structural equation (`0 ∉ A`), so its noise `M.ε₀` is still
  independent of each *parent* coordinate `Xₖ` (`k ∈ PA(Y)`) — now of the
  post-intervention `X`.  As with `ObsSEM.hYexo` this is a consequence of recursive
  noise-independence + acyclicity that the random-variable encoding does not expose,
  so it is carried as a field; stated **only for parents** of the target. -/
  hExo : ∀ k, M.dag.edge k (target p) → IndepFun (fun ω => M.ε ω (target p)) (fun ω => X ω k) M.P

/-- An **environment family** for the linear-Gaussian ICP problem is an
observational SEM together with finitely many do-intervention environments.

By convention one environment (index irrelevant here) is the observational SEM
itself; the indexed `env i` are the interventional blocks.  The do-intervention
identifiability hypotheses (`prop:1`(i)) are stated as separate predicates over
this family in `Regression.lean`. -/
structure EnvFamily (p : ℕ) where
  /-- The observational linear-Gaussian SEM (`e = 1`). -/
  obs : ObsSEM p
  /-- Index type of the interventional environments. -/
  ι : Type*
  /-- Finitely many environments. -/
  hι : Fintype ι
  /-- The interventional environments. -/
  env : ι → Env obs

attribute [instance] EnvFamily.hι

namespace EnvFamily

variable (F : EnvFamily p)

/-- The observational parent set `PA(Y)` of the family. -/
abbrev paY : Finset (Fin (p + 1)) := F.obs.paY

end EnvFamily

end Causalean.Discovery.InvariantPrediction.LinearGaussian
