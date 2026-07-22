/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Back-door estimation system: structure, data law, value-space ATE estimand

The `BackdoorEstimationSystem` extends `POBackdoorSystem` with the value-space
factorization of the σ(X)-measurable representatives (Doob–Dynkin lift).  This
file collects:

* the structure itself with the observable compatibility fields `μ_reg_compat`,
  `e_compat`, plus the derived counterfactual lemma `μ_compat`;
* the strict-overlap predicate;
* the covariate marginal `P_X`, factual data triple `factualZ`, joint law `P_Z`;
* the value-space estimand `θ₀` and its agreement with the PO-level ATE;
* `POBackdoorSystem.toBackdoorEstimationSystem`, showing that the estimation
  layer's value-space representatives can be constructed from observable
  regression and propensity lifts under overlap and integrability.
-/

import Causalean.PO.ID.Exact.ATE
import Causalean.Stat.Orthogonality.Orthogonality
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Defines the estimation-layer structure used by back-door ATE estimators.

The file introduces `BackdoorEstimationSystem`, its strict-overlap predicate
`StrictOverlap`, the covariate and observed-data laws `P_X` and `P_Z`, and the
value-space estimand `θ₀`.  It proves that `θ₀` agrees with the PO-level ATE
under the back-door assumptions, derives counterfactual compatibility as
`μ_compat`, and provides `POBackdoorSystem.toBackdoorEstimationSystem` to show
that the added value-space compatibility and positivity fields are obtainable
from observable lifts rather than extra causal assumptions.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

/-! ## Back-door estimation system

A `BackdoorEstimationSystem` extends `POBackdoorSystem` with the value-space
factorization of the σ(X)-measurable representatives.  The compatibility
fields encode the Doob–Dynkin lift; existence of such fields is the
estimation-layer assumption added on top of identification. -/

/-- Wrapper around `POBackdoorSystem` carrying value-space representatives
of the outcome regression and propensity score, plus their compatibility
with the σ(X)-measurable representatives `S.adjustedCE` / `S.propScore` on
`Ω`.

Field summary:
* `μ_val a x`     — value-space outcome regression  `μ(a, x)`.
* `e_val x`       — value-space propensity           `e(x) ∈ (0, 1)`.
* `μ_reg_compat`  — `μ_val d ∘ factualX =ᵐ adjustedCE d` (observable; ML target).
* `e_compat`      — `propScore true =ᵐ e_val ∘ factualX`. -/
structure BackdoorEstimationSystem (P : POSystem) (γ : Type*)
    [MeasurableSpace γ] [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    extends POBackdoorSystem P γ where
  /-- Value-space outcome regression `μ(a, x)`. -/
  μ_val : Bool → γ → ℝ
  μ_meas : ∀ b, Measurable (μ_val b)
  /-- Value-space propensity `e(x) ∈ (0, 1)`. -/
  e_val : γ → ℝ
  e_meas : Measurable e_val
  e_pos : ∀ x, 0 < e_val x
  e_lt_one : ∀ x, e_val x < 1
  /-- The value-space outcome regression `μ_val` represents the **observable**
  adjustment functional `adjustedCE d = E[Y·1_{D=d}|σX] / P[D=d|σX]`, with NO
  identification assumptions: `μ_val d (factualX ·) =ᵐ adjustedCE d`. This is the
  ML/regression target (`adjustedCE` is the regression `E[Y|D=d,X]`, see
  `regression_adjustment`). The counterfactual reading
  `μ[Y(d)|σX] =ᵐ μ_val d ∘ factualX` is NOT assumed here — it is the *derived*
  lemma `μ_compat` below, which additionally requires `Assumptions` via
  back-door identification (`cate_backdoor`). -/
  μ_reg_compat : ∀ d : Bool,
    (fun ω => μ_val d (toPOBackdoorSystem.factualX ω))
      =ᵐ[P.μ] toPOBackdoorSystem.adjustedCE d
  /-- Propensity factors through `factualX`:
  `propScore true =ᵐ e_val (factualX ·)`. -/
  e_compat :
    toPOBackdoorSystem.propScore true
      =ᵐ[P.μ] (fun ω => e_val (toPOBackdoorSystem.factualX ω))

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Counterfactual compatibility (derived, under identification).** Recovers the
former `μ_compat` field — the *counterfactual* reading
`μ[Y(d) | σ(X)] =ᵐ μ_val d ∘ factualX` — now as a theorem rather than an
assumption. It is the observable `μ_reg_compat` (`μ_val d ∘ factualX =ᵐ adjustedCE d`)
composed with back-door identification (`cate_backdoor : μ[Y(d)|σX] =ᵐ adjustedCE d`),
so the counterfactual binding is NOT part of the estimation system's data: it holds
only under `Assumptions`. Every downstream proof that used the old field calls this
with the ambient `hA`. -/
lemma μ_compat (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool) :
    P.μ[S.toPOBackdoorSystem.YofD d | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) :=
  (S.toPOBackdoorSystem.cate_backdoor hA d).trans (S.μ_reg_compat d).symm

/-- Strict-overlap predicate `ε ≤ propScore true ω ≤ 1 − ε` a.s., with
`ε ∈ (0, 1/2]`.  Restated to the value-space propensity via `e_compat`. -/
def StrictOverlap (S : BackdoorEstimationSystem P γ) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧
    (∀ᵐ ω ∂P.μ, ε ≤ S.toPOBackdoorSystem.propScore true ω ∧
      S.toPOBackdoorSystem.propScore true ω ≤ 1 - ε)

/-! ## Marginal of the covariate and joint data law -/

/-- Covariate marginal: `P_X := μ.map factualX`. -/
noncomputable def P_X (S : BackdoorEstimationSystem P γ) : Measure γ :=
  P.μ.map S.toPOBackdoorSystem.factualX

/-- Data triple `(X, A, Y) : Ω → γ × Bool × ℝ`. -/
noncomputable def factualZ (S : BackdoorEstimationSystem P γ) :
    P.Ω → γ × Bool × ℝ :=
  fun ω => (S.toPOBackdoorSystem.factualX ω,
            S.toPOBackdoorSystem.factualD ω,
            S.toPOBackdoorSystem.factualY ω)

/-- The observed covariate, treatment, and outcome triple is measurable. -/
lemma measurable_factualZ (S : BackdoorEstimationSystem P γ) :
    Measurable S.factualZ :=
  (S.toPOBackdoorSystem.measurable_factualX).prodMk
    ((S.toPOBackdoorSystem.measurable_factualD).prodMk
      S.toPOBackdoorSystem.measurable_factualY)

/-- Joint data law `P_Z := μ.map (X, A, Y)`. -/
noncomputable def P_Z (S : BackdoorEstimationSystem P γ) :
    Measure (γ × Bool × ℝ) :=
  P.μ.map S.factualZ

/-- The covariate marginal `P_X` is the pushforward of `P_Z` along the
projection `(x, a, y) ↦ x`.  Used to bridge integrals/`eLpNorm` between
`P_X` (covariates only) and `P_Z` (full data triple). -/
lemma P_Z_map_projX_eq_P_X (S : BackdoorEstimationSystem P γ) :
    S.P_Z.map (fun z : γ × Bool × ℝ => z.1) = S.P_X := by
  unfold BackdoorEstimationSystem.P_Z BackdoorEstimationSystem.P_X
  rw [Measure.map_map (by fun_prop : Measurable (fun z : γ × Bool × ℝ => z.1))
    S.measurable_factualZ]
  rfl

/-! ## ATE estimand on the value space -/

/-- Value-space ATE: `θ₀ = ∫ (μ(1, x) - μ(0, x)) dP_X`. -/
noncomputable def θ₀ (S : BackdoorEstimationSystem P γ) : ℝ :=
  ∫ x, S.μ_val true x - S.μ_val false x ∂(S.P_X)

/-- The value-space estimand agrees with the PO-level ATE under the
back-door assumptions.  Restates `def:est-ate-nuisance` (last sentence)
combined with `prop:po-backdoor-ate`. -/
theorem θ₀_eq_ATE (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) :
    S.θ₀ = S.toPOBackdoorSystem.ATE := by
  unfold BackdoorEstimationSystem.θ₀ BackdoorEstimationSystem.P_X PO.POBackdoorSystem.ATE
  have hmeas_diff : Measurable (fun x => S.μ_val true x - S.μ_val false x) :=
    (S.μ_meas true).sub (S.μ_meas false)
  rw [MeasureTheory.integral_map S.toPOBackdoorSystem.measurable_factualX.aemeasurable
    hmeas_diff.aestronglyMeasurable]
  have hcompat :
      (fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
        S.μ_val false (S.toPOBackdoorSystem.factualX ω))
        =ᵐ[P.μ]
      (fun ω => P.μ[S.toPOBackdoorSystem.YofD true | S.toPOBackdoorSystem.sigmaX] ω -
        P.μ[S.toPOBackdoorSystem.YofD false | S.toPOBackdoorSystem.sigmaX] ω) :=
    (S.μ_compat hA true).symm.sub (S.μ_compat hA false).symm
  rw [MeasureTheory.integral_congr_ae hcompat]
  have hsub :
      P.μ[S.toPOBackdoorSystem.YofD true - S.toPOBackdoorSystem.YofD false |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
      (fun ω => P.μ[S.toPOBackdoorSystem.YofD true | S.toPOBackdoorSystem.sigmaX] ω -
        P.μ[S.toPOBackdoorSystem.YofD false | S.toPOBackdoorSystem.sigmaX] ω) :=
    MeasureTheory.condExp_sub hA.integrable_Y1 hA.integrable_Y0 S.toPOBackdoorSystem.sigmaX
  rw [MeasureTheory.integral_congr_ae hsub.symm]
  rw [MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le]
  rfl

end BackdoorEstimationSystem

/-! ## Derivability: the estimation system adds no assumptions beyond overlap -/

open Classical in
/-- **The compatibility/positivity fields are free.** From a `POBackdoorSystem` with
a.e. two-sided overlap and an integrable observed outcome — and *no* unconfoundedness
— one constructs a `BackdoorEstimationSystem`: `μ_val` is the value-space outcome
regression `regFn` and `e_val` is the propensity lift `eLift` clamped into `(0,1)`
off-support. Every added field is discharged (`μ_reg_compat` from
`regression_adjustment`; `e_pos`/`e_lt_one` from the clamp; `e_compat` from overlap).
So `BackdoorEstimationSystem` carries no assumption beyond `POBackdoorSystem` + overlap
+ integrability — in particular the value-space lifts (`μ_compat`, `e_compat`) were
never genuine assumptions. -/
noncomputable def _root_.Causalean.PO.POBackdoorSystem.toBackdoorEstimationSystem
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    (S : PO.POBackdoorSystem P γ) [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hov : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hY : Integrable S.factualY P.μ) :
    BackdoorEstimationSystem P γ where
  toPOBackdoorSystem := S
  μ_val := fun b x => S.regFn (b, x)
  μ_meas := fun _ => S.measurable_regFn.comp (measurable_const.prodMk measurable_id)
  e_val := Set.piecewise {x : γ | 0 < S.eLift x ∧ S.eLift x < 1} S.eLift (fun _ => 1 / 2)
  e_meas := by
    refine Measurable.piecewise ?_ S.measurable_eLift measurable_const
    exact (measurableSet_lt measurable_const S.measurable_eLift).inter
      (measurableSet_lt S.measurable_eLift measurable_const)
  e_pos := by
    intro x
    by_cases hx : x ∈ {x : γ | 0 < S.eLift x ∧ S.eLift x < 1}
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx.1
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; norm_num
  e_lt_one := by
    intro x
    by_cases hx : x ∈ {x : γ | 0 < S.eLift x ∧ S.eLift x < 1}
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx.2
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; norm_num
  μ_reg_compat := fun d =>
    (S.regression_adjustment d hY (S.propScore_ne_of_overlap hov d)).symm
  e_compat := by
    filter_upwards [hov] with ω hω
    have heq : S.propScore true ω = S.eLift (S.factualX ω) :=
      congrFun S.propScore_true_eq_eLift ω
    have hmem : S.factualX ω ∈ {x : γ | 0 < S.eLift x ∧ S.eLift x < 1} := by
      rw [Set.mem_setOf_eq, ← heq]; exact hω
    rw [heq, Set.piecewise_eq_of_mem _ _ _ hmem]

end ATE
end Estimation
end Causalean
