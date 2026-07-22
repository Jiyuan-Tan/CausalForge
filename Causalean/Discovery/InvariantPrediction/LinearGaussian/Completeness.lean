/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.LinearGaussian.Regression
import Causalean.Discovery.InvariantPrediction.LinearGaussian.Helpers.Moments
import Causalean.Discovery.InvariantPrediction.LinearGaussian.Helpers.Residual
import Causalean.Discovery.InvariantPrediction.LinearGaussian.Helpers.Invariance

/-!
# Invariant Causal Prediction — completeness for do-interventions (`prop:1`(i))

The **statement** of Peters–Bühlmann–Meinshausen 2016, Theorem `prop:1`(i): for a
linear-Gaussian SEM whose interventions are *do-interventions* with shifted
values (`a^e_j ≠ E[X¹_j]`) and at least one single-node intervention on every
predictor, the identified set equals the parents of the target:
`S(E) = PA(Y)`.

The intermediate lemmas mirror the paper's appendix proof (`app:proofs`, "Proof
of Theorem prop:1 (i)"):

1. **Soundness** `icp_sound_linearGaussian` (`S(E) ⊆ PA(Y)`) — `H_{0,PA(Y)}`
   holds with `γ = γ* = β₀,·` and residual `ε₁`, so `PA(Y)` is one of the
   intersected sets (`propos:sem`).
2. **Youngest-node selection** `exists_youngest_nonzero` — among the indices `k`
   with `α_k ≠ 0` (`α = γ* − β^{pred}(S)`) there is one, `k₀`, with no directed
   path to any other such index (a sink in the induced subgraph).
3. **Mean-shift** `residual_mean_shift_of_doIntervention` — under the single
   `do(X_{k₀} = a)` intervention with `a ≠ E[X¹_{k₀}]` and `α_{k₀} ≠ 0`, the
   residual law in that environment differs from the observational one (their
   means differ by `α_{k₀}·(a − E[X¹_{k₀}]) ≠ 0`), contradicting invariance.
4. **Completeness** `icp_complete_linearGaussian` — combines 1–3: any
   null-satisfying `S` must contain `PA(Y)`, so `S(E) ⊇ PA(Y)`, and with
   soundness `S(E) = PA(Y)`.

## Encoding choices (fidelity notes)

* **Single-intervention hypothesis (`prop:1`(i)).**  `HasShiftedSingleInterventions`:
  for each predictor `j`, some environment `i` has `A i = {j}` (single
  intervention on `j`) and `a i j ≠ E[X¹_j]` (the shift condition, with the mean
  taken under the *observational* law).  This is exactly the paper's "`a^e_j ≠
  E(X¹_j)` and for each `j ∈ {2,…,p+1}` there is `e` with `A^e = {j}`".

* **`E[X¹_j]` is the observational mean** `∫ ω, M.X ω j ∂P`.  Finiteness /
  integrability of the observational coordinates is bundled as `hIntegrable`
  (the Gaussian SEM has all moments; the theorem keeps this fact as an explicit
  integrability hypothesis rather than rebuilding Gaussian moment theory here).

* **`α` and `β^{pred}`.**  The proof works with `α k = γ*_k − γ_k` for the null's
  coefficient `γ` (which, being orthogonal to `X_S`, *is* `β^{pred}(S)`).  We do
  not introduce a separate `β^{pred}` object; `α` is defined inline in the
  lemmas.

* **Exogeneity (the paper's Assumption 1).**  Soundness needs `ε₀ ⊥ X_k` for each
  parent `k ∈ PA(Y)`.  In a recursive Gaussian SEM this follows from joint noise
  independence + acyclicity, but the random-variable encoding here does not expose
  the `ε → X` solve, so it is carried as the structure fields `ObsSEM.hYexo` and
  `Env.hExo` (stated only for parents — it is *false* for descendants of `Y`).

* **`hyoung` at the call site.**  `residual_mean_shift_of_doIntervention` takes a
  `hyoung` hypothesis — every *other* support index `k ≠ k₀` with `α_k ≠ 0` is not
  a descendant of `k₀`.  In the completeness proof this is supplied exactly by the
  youngest-node selection (`exists_youngest_nonzero` over the support of `α`).
-/

namespace Causalean.Discovery.InvariantPrediction.LinearGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {p : ℕ}

namespace EnvFamily

variable (F : EnvFamily p)

/-- The observational mean of coordinate `j`: `E[X¹_j] = ∫ X_j dP¹`. -/
noncomputable def obsMean (j : Fin (p + 1)) : ℝ := ∫ ω, F.obs.X ω j ∂F.obs.P

/-- **Do-intervention single-intervention hypothesis** of `prop:1`(i): for every
predictor `j`, some environment performs a single shifted do-intervention on `j`,
i.e. `A i = {j}` and the assigned value differs from the observational mean
`a i j ≠ E[X¹_j]`. -/
def HasShiftedSingleInterventions : Prop :=
  ∀ j ∈ predictors p, ∃ i : F.ι,
    (F.env i).A = {j} ∧ (F.env i).a j ≠ F.obsMean j

/-- Integrability of the observational coordinates (all Gaussian moments exist);
carried as an explicit hypothesis so the observational means `E[X¹_j]` used by
the shifted-intervention condition are available. -/
def ObsIntegrable : Prop := ∀ j, Integrable (fun ω => F.obs.X ω j) F.obs.P

/-- **Soundness** (`propos:sem`): the identified set is contained in the target's
parents, `S(E) ⊆ PA(Y)`.  The null `H_{0,PA(Y)}` is correct with the causal
coefficient `γ* = β₀,·` and residual `ε₁`, so `PA(Y) ∈ invariantSets` and hence
is one of the intersected sets. -/
theorem icp_sound_linearGaussian (hInt : F.ObsIntegrable) :
    F.identifiedSet ⊆ F.paY := by
  -- It suffices that `PA(Y)` itself satisfies the invariance null, since the
  -- identified set is contained in every invariant set.
  intro k hk
  rw [mem_identifiedSet] at hk
  refine hk F.paY ?_
  rw [mem_invariantSets]
  refine ⟨F.obs.paY_subset_predictors, ?_⟩
  -- Witness: causal coefficient `γ* = β₀,·` and residual law `N(0, σ₀²)`.
  refine ⟨causalCoeff F.obs,
    gaussianReal 0 ⟨(F.obs.σ (target p)) ^ 2, by positivity⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- `SupportedOn γ* PA(Y)`: `β₀ₖ ≠ 0 ↔ k ∈ PA(Y)`.
    intro k hk0
    exact F.obs.mem_paY.mpr hk0
  · -- Observational independence clause: residual `=ᵐ ε₀`, then `hYexo`.
    intro k hkPaY
    have hedge : F.obs.dag.edge k (target p) := F.obs.dag.mem_parents.mp hkPaY
    exact (F.obs.hYexo k hedge).congr (Filter.EventuallyEq.symm (obsResidual_eq_eps F.obs))
      (Filter.EventuallyEq.refl _ _)
  · -- Observational law clause: `P.map residual = P.map ε₀ = N(0, σ₀²)`.
    rw [Measure.map_congr (obsResidual_eq_eps F.obs), F.obs.hGauss (target p)]
  · -- Interventional independence clause: residual `=ᵐ ε₀`, then `(env i).hExo`.
    intro i k hkPaY
    have hedge : F.obs.dag.edge k (target p) := F.obs.dag.mem_parents.mp hkPaY
    exact ((F.env i).hExo k hedge).congr
      (Filter.EventuallyEq.symm (envResidual_eq_eps F.obs (F.env i)))
      (Filter.EventuallyEq.refl _ _)
  · -- Interventional law clause: same as observational via `=ᵐ ε₀`.
    intro i
    rw [Measure.map_congr (envResidual_eq_eps F.obs (F.env i)), F.obs.hGauss (target p)]

/-- **Youngest-node selection** (the "youngest node `X_{k₀}`" step).  Given a
nonempty set of indices `T` (the support of `α = γ* − γ`), there is an index
`k₀ ∈ T` that is a *sink* of the induced subgraph: no directed path in the
observational DAG goes from `k₀` to any *other* element of `T`.  This is the
"youngest" node with non-zero `α` of the paper's proof. -/
theorem exists_youngest_nonzero (T : Finset (Fin (p + 1))) (hT : T.Nonempty) :
    ∃ k₀ ∈ T, ∀ k ∈ T, k ≠ k₀ → ¬ F.obs.dag.isAncestor k₀ k := by
  -- Pick the index of `T` with the largest topological order: it cannot be a
  -- proper ancestor of any other element, since ancestors strictly increase the
  -- topological order.
  obtain ⟨k₀, hk₀T, hmax⟩ :=
    Finset.exists_max_image T (fun k => F.obs.dag.topoOrder k) hT
  refine ⟨k₀, hk₀T, ?_⟩
  intro k hkT _ hanc
  have hlt : F.obs.dag.topoOrder k₀ < F.obs.dag.topoOrder k :=
    F.obs.dag.isAncestor_topoOrder_lt hanc
  exact absurd (hmax k hkT) (Nat.not_le.mpr hlt)

/-- **Residual mean-shift** (`eq:help1`/`eq:help2`).  Fix a coefficient vector
`γ` and let `α = γ* − γ` (`γ*` the causal coefficient `β₀,·`).  Suppose `k₀` is a
youngest index with `α_{k₀} ≠ 0`, and `i` is an environment with a single shifted
do-intervention on `k₀` (`A i = {k₀}`, `a i k₀ ≠ E[X¹_{k₀}]`).  Then the residual
`R^i = Y^i − Σ γ_k X_k^i` and the observational residual `R¹` have **different
means**, hence different laws — the two cannot be `IdentDistrib`.

The mean gap is `α_{k₀} · (a i k₀ − E[X¹_{k₀}]) ≠ 0` (the do-intervention pins
`X_{k₀}` to the constant `a`, all other contributions matching the observational
mean by invariance of the un-intervened equations).

The `hyoung` hypothesis encodes the **youngest-node** property supplied at the call
site (from `exists_youngest_nonzero`): every *other* index `k ≠ k₀` with a nonzero
`α_k = β₀ₖ − γ_k` is not a descendant of `k₀`.  Hence those coordinates are
non-descendants of the intervention and keep their observational mean, so the only
surviving mean contribution is the pinned coordinate `k₀`. -/
theorem residual_mean_shift_of_doIntervention
    (hInt : F.ObsIntegrable) (γ : Fin (p + 1) → ℝ)
    (k₀ : Fin (p + 1)) (hk₀ : (F.obs.β (target p) k₀ - γ k₀) ≠ 0)
    (hyoung : ∀ k, k ≠ k₀ → (F.obs.β (target p) k - γ k) ≠ 0 →
      ¬ F.obs.dag.isAncestor k₀ k)
    (i : F.ι) (hAi : (F.env i).A = {k₀}) (hai : (F.env i).a k₀ ≠ F.obsMean k₀) :
    ¬ IdentDistrib (envResidual (F.env i) γ) (obsResidual F.obs γ)
        F.obs.P F.obs.P := by
  classical
  set M := F.obs with hM
  set e := F.env i with he
  -- `α k = β₀ₖ − γ k`.
  set α : Fin (p + 1) → ℝ := fun k => M.β (target p) k - γ k with hα
  -- `k₀ ≠ 0`: the intervention never targets `Y`, and `A = {k₀}`.
  have hk₀ne : k₀ ≠ target p := by
    intro h; subst h; exact e.hAtarget (by rw [hAi]; exact Finset.mem_singleton_self _)
  -- ---- Residual rewrites: `R = ε₀ + Σ_k α_k X_k` (both worlds). ----
  -- `Σ α_k x_k = Σ β₀ₖ x_k − Σ γ_k x_k`.
  have hαsum : ∀ x : Fin (p + 1) → ℝ,
      ∑ k, α k * x k = (∑ k, M.β (target p) k * x k) - ∑ k, γ k * x k := by
    intro x
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; simp only [hα]; ring
  have hobsR : ∀ᵐ ω ∂M.P,
      obsResidual M γ ω = M.ε ω (target p) + ∑ k, α k * M.X ω k := by
    filter_upwards [M.hε] with ω hω
    have hX0 : M.X ω (target p)
        = M.ε ω (target p) + ∑ k, M.β (target p) k * M.X ω k := by
      rw [sum_causalCoeff_eq M (M.X ω)]; rw [hω (target p)]; ring
    simp only [obsResidual, hX0, hαsum (M.X ω)]; ring
  have henvR : ∀ᵐ ω ∂M.P,
      envResidual e γ ω = M.ε ω (target p) + ∑ k, α k * e.X ω k := by
    filter_upwards [e.hDoStruct (target p) e.hAtarget] with ω hω
    have hX0 : e.X ω (target p)
        = M.ε ω (target p) + ∑ k, M.β (target p) k * e.X ω k := by
      rw [sum_causalCoeff_eq M (e.X ω), hω]
    simp only [envResidual, hX0, hαsum (e.X ω)]; ring
  -- ---- Integrability of each summand. ----
  -- obs: `α k * X_k` is integrable.
  have hobsTermInt : ∀ k, Integrable (fun ω => α k * M.X ω k) M.P :=
    fun k => (hInt k).const_mul _
  -- env: `α k * X_kᵉ` is integrable: either `α k = 0` (zero function) or `X_kᵉ`
  -- agrees a.e. with an integrable function (`a` const if `k = k₀`, `X_k` else).
  have hAk₀ : ∀ᵐ ω ∂M.P, e.X ω k₀ = e.a k₀ :=
    e.hDoPin k₀ (by rw [hAi]; exact Finset.mem_singleton_self _)
  have henvEqObs : ∀ k, k ≠ k₀ → ¬ M.dag.isAncestor k₀ k →
      ∀ᵐ ω ∂M.P, e.X ω k = M.X ω k := by
    intro k hk hanc
    filter_upwards [nonDescendant_invariance M e k₀ hAi] with ω hω using hω k hk hanc
  have henvTermInt : ∀ k, Integrable (fun ω => α k * e.X ω k) M.P := by
    intro k
    by_cases hαk : α k = 0
    · simp [hαk]
    · by_cases hkk₀ : k = k₀
      · -- `k = k₀`: `e.X · k =ᵐ e.a k₀` (do-pin), so `α k * e.X · k =ᵐ α k * e.a k₀`.
        subst hkk₀
        refine (integrable_const (α k * e.a k)).congr ?_
        filter_upwards [hAk₀] with ω hω using by rw [hω]
      · -- `k ≠ k₀` and `α k ≠ 0`, so `k` is a non-descendant of `k₀`.
        have hanc : ¬ M.dag.isAncestor k₀ k := hyoung k hkk₀ hαk
        refine ((hInt k).const_mul (α k)).congr ?_
        filter_upwards [henvEqObs k hkk₀ hanc] with ω hω using by rw [hω]
  -- ---- Compute the two means. ----
  have hεInt : Integrable (fun ω => M.ε ω (target p)) M.P := eps_integrable M (target p)
  have hobsMean : ∫ ω, obsResidual M γ ω ∂M.P
      = ∑ k, α k * (∫ ω, M.X ω k ∂M.P) := by
    rw [integral_congr_ae hobsR]
    rw [integral_add hεInt (integrable_finset_sum _ (fun k _ => hobsTermInt k))]
    rw [eps_integral_zero M (target p), zero_add, integral_finset_sum _
      (fun k _ => hobsTermInt k)]
    apply Finset.sum_congr rfl; intro k _; rw [integral_const_mul]
  have henvMean : ∫ ω, envResidual e γ ω ∂M.P
      = ∑ k, α k * (∫ ω, e.X ω k ∂M.P) := by
    rw [integral_congr_ae henvR]
    rw [integral_add hεInt (integrable_finset_sum _ (fun k _ => henvTermInt k))]
    rw [eps_integral_zero M (target p), zero_add, integral_finset_sum _
      (fun k _ => henvTermInt k)]
    apply Finset.sum_congr rfl; intro k _; rw [integral_const_mul]
  -- ---- The mean gap is the single `k₀` term. ----
  have hgap : ∫ ω, envResidual e γ ω ∂M.P - ∫ ω, obsResidual M γ ω ∂M.P
      = α k₀ * (e.a k₀ - F.obsMean k₀) := by
    rw [henvMean, hobsMean, ← Finset.sum_sub_distrib]
    -- Each term: `α k * (E[X_kᵉ] − E[X_k])`.  Only `k = k₀` survives.
    have hterm : ∀ k ∈ Finset.univ, k ≠ k₀ →
        α k * (∫ ω, e.X ω k ∂M.P) - α k * (∫ ω, M.X ω k ∂M.P) = 0 := by
      intro k _ hkk₀
      by_cases hαk : α k = 0
      · simp [hαk]
      · have hanc : ¬ M.dag.isAncestor k₀ k := hyoung k hkk₀ hαk
        have : (∫ ω, e.X ω k ∂M.P) = (∫ ω, M.X ω k ∂M.P) :=
          integral_congr_ae (henvEqObs k hkk₀ hanc)
        rw [this]; ring
    rw [Finset.sum_eq_single k₀ hterm (by simp)]
    -- `E[X_{k₀}ᵉ] = a k₀` (do-pin); `E[X_{k₀}] = obsMean k₀`.
    have hEnvk₀ : (∫ ω, e.X ω k₀ ∂M.P) = e.a k₀ := by
      rw [integral_congr_ae hAk₀, integral_const]; simp
    rw [hEnvk₀]
    simp only [EnvFamily.obsMean]; ring
  -- ---- Different means ⟹ not IdentDistrib. ----
  intro hid
  have heq : ∫ ω, envResidual e γ ω ∂M.P = ∫ ω, obsResidual M γ ω ∂M.P :=
    hid.integral_eq
  rw [heq, sub_self] at hgap
  exact (mul_ne_zero hk₀ (sub_ne_zero.mpr hai)) hgap.symm

/-- **Completeness for do-interventions — Theorem `prop:1`(i).**

For a linear-Gaussian SEM with do-interventions such that every predictor `j`
receives at least one single intervention `A^e = {j}` with shifted value
`a^e_j ≠ E[X¹_j]`, the identified set equals the parents of the target:

`S(E) = PA(Y)`.

This is the main result of this sub-development. -/
theorem icp_complete_linearGaussian
    (hInt : F.ObsIntegrable) (hInterv : F.HasShiftedSingleInterventions) :
    F.identifiedSet = F.paY := by
  classical
  apply le_antisymm (icp_sound_linearGaussian F hInt)
  -- `PA(Y) ⊆ S(E)`: every parent lies in every invariant set.
  intro pp hpp
  rw [mem_identifiedSet]
  intro S hS
  rw [mem_invariantSets] at hS
  obtain ⟨hSpred, γ, Fε, hSupp, _, hObsLaw, _, hEnvLaw⟩ := hS
  -- It suffices to show `PA(Y) ⊆ S`.
  by_contra hppS
  -- `α k = β₀ₖ − γ k`.  Its support `T` is nonempty (contains `pp`).
  set α : Fin (p + 1) → ℝ := fun k => F.obs.β (target p) k - γ k with hα
  -- `α pp ≠ 0`: `pp ∈ paY` gives `β₀,pp ≠ 0`, and `pp ∉ S` gives `γ pp = 0`.
  have hγpp : γ pp = 0 := by
    by_contra h; exact hppS (hSupp pp h)
  have hαpp : α pp ≠ 0 := by
    simp only [hα, hγpp, sub_zero]
    exact F.obs.mem_paY.mp hpp
  set T : Finset (Fin (p + 1)) := Finset.univ.filter (fun k => α k ≠ 0) with hT
  have hppT : pp ∈ T := by rw [hT]; simp [hαpp]
  have hTne : T.Nonempty := ⟨pp, hppT⟩
  -- Youngest index of the support.
  obtain ⟨k₀, hk₀T, hk₀young⟩ := F.exists_youngest_nonzero T hTne
  have hαk₀ : α k₀ ≠ 0 := by rw [hT] at hk₀T; simpa using hk₀T
  -- `hyoung` for the mean-shift lemma: every other support index is a non-ancestor.
  have hyoung : ∀ k, k ≠ k₀ → (F.obs.β (target p) k - γ k) ≠ 0 →
      ¬ F.obs.dag.isAncestor k₀ k := by
    intro k hk hαk
    exact hk₀young k (by rw [hT]; simp [α, hαk]) hk
  -- `k₀` is a predictor (`k₀ ≠ 0`): either `γ k₀ ≠ 0` (so `k₀ ∈ S ⊆ predictors`) or
  -- `β₀,k₀ ≠ 0` (so `k₀ ∈ paY ⊆ predictors`).
  have hk₀pred : k₀ ∈ predictors p := by
    by_cases hγk₀ : γ k₀ = 0
    · -- `β₀,k₀ = α k₀ ≠ 0`, so `k₀ ∈ paY`.
      have : F.obs.β (target p) k₀ ≠ 0 := by
        have : α k₀ = F.obs.β (target p) k₀ := by simp [hα, hγk₀]
        rwa [this] at hαk₀
      exact F.obs.paY_subset_predictors (F.obs.mem_paY.mpr this)
    · exact hSpred (hSupp k₀ hγk₀)
  -- A single shifted do-intervention on `k₀`.
  obtain ⟨i, hAi, hai⟩ := hInterv k₀ hk₀pred
  -- The mean-shift lemma: residuals are NOT identically distributed.
  have hni := F.residual_mean_shift_of_doIntervention hInt γ k₀ hαk₀ hyoung i hAi hai
  -- But the invariance null says they share the law `Fε`, hence ARE identically
  -- distributed — contradiction.
  apply hni
  have hmeasObs : Measurable (obsResidual F.obs γ) :=
    (F.obs.hXmeas (target p)).sub
      (Finset.measurable_sum _ (fun k _ => (F.obs.hXmeas k).const_mul _))
  have hmeasEnv : Measurable (envResidual (F.env i) γ) :=
    ((F.env i).hXmeas (target p)).sub
      (Finset.measurable_sum _ (fun k _ => ((F.env i).hXmeas k).const_mul _))
  refine ⟨hmeasEnv.aemeasurable, hmeasObs.aemeasurable, ?_⟩
  rw [hEnvLaw i, hObsLaw]

end EnvFamily

end Causalean.Discovery.InvariantPrediction.LinearGaussian
