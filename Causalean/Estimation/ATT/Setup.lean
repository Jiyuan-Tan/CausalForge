/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Treated estimation system: structure, data law, value-space ATT estimand

The `TreatedEstimationSystem` extends `POBackdoorSystem` with value-space
representatives of the control-arm outcome regression and the propensity score
needed by the ATT AIPW formulas. Parallel to `Estimation/ATE/Setup.lean`, it
stores only the `μ₀` outcome-regression arm and a value-space upper-overlap
field for the propensity score; downstream identification and variance results
use the one-sided `POBackdoorSystem.ATTAssumptions` bundle, because ATT only
needs the control-arm backdoor identity and control overlap.

This file collects:

* the structure itself with the observable compatibility fields `μ₀_reg_compat`,
  `e_compat`, plus the derived one-sided counterfactual lemma `μ₀_compat`;
* the one-sided overlap predicate;
* the covariate marginal `P_X`, factual data triple `factualZ`, joint law `P_Z`;
* the value-space estimand `θ₀` and its agreement with the PO-level `ATT`.
-/

import Causalean.PO.ID.Exact.ATT
import Causalean.Stat.Orthogonality.Orthogonality
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Defines the treated-estimation system for ATT estimation under back-door
assumptions. The structure bundles value-space representatives for the control
outcome regression, propensity score, treatment probability, and compatibility
fields needed by ATT AIPW moments.

The file introduces `TreatedEstimationSystem`, derives the control-arm
counterfactual compatibility lemma `μ₀_compat`, defines the one-sided overlap
predicate `OneSidedOverlap`, the covariate and data laws `P_X` and `P_Z`, the
value-space target `θ₀`, and proves `θ₀_eq_ATT`. It also constructs a
`TreatedEstimationSystem` from a `POBackdoorSystem` with overlap and an
integrable observed outcome via `POBackdoorSystem.toTreatedEstimationSystem`.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

/-! ## Treated estimation system

A `TreatedEstimationSystem` extends `POBackdoorSystem` with the value-space
factorization of the σ(X)-measurable representatives needed for ATT.  The
compatibility fields encode the Doob–Dynkin lift; existence of such fields is
the estimation-layer assumption added on top of identification. -/

/-- Wrapper around `POBackdoorSystem` carrying value-space representatives of
the control-arm outcome regression and propensity score, plus their
compatibility with the σ(X)-measurable representatives `S.adjustedCE false` /
`S.propScore true` on `Ω`.

Field summary:
* `μ₀_val x`     — value-space control-arm outcome regression `μ₀(x)`.
* `e_val x`      — value-space propensity `e(x) ∈ (0, 1)`.
* `μ₀_reg_compat` — `μ₀_val ∘ factualX =ᵐ adjustedCE false` (observable; ML target).
* `e_compat`     — `propScore true =ᵐ e_val ∘ factualX`.

Only `μ₀` is needed (the AIPW form for ATT does not involve `μ₁`).  Likewise
only the `< 1` half of overlap is enforced via `e_lt_one`; positivity of the
treated arm is handled at the PO level via `propTreated_pos` in
`ATTAssumptions`. -/
structure TreatedEstimationSystem (P : POSystem) (γ : Type*)
    [MeasurableSpace γ] [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    extends POBackdoorSystem P γ where
  /-- Value-space control-arm outcome regression `μ₀(x)`. -/
  μ₀_val : γ → ℝ
  μ₀_meas : Measurable μ₀_val
  /-- Value-space propensity `e(x)`. -/
  e_val : γ → ℝ
  e_meas : Measurable e_val
  /-- One-sided overlap on the value-space propensity. -/
  e_lt_one : ∀ x, e_val x < 1
  /-- The control-arm regression `μ₀_val` represents the **observable** adjustment
  functional `adjustedCE false = E[Y·1_{D=0}|σX] / P[D=0|σX]`, with NO identification
  assumptions: `μ₀_val (factualX ·) =ᵐ adjustedCE false`. This is the ML/regression
  target (`adjustedCE false` is the control regression `E[Y|D=0,X]`, see
  `regression_adjustment`). The counterfactual reading
  `μ[Y(0)|σX] =ᵐ μ₀_val ∘ factualX` is NOT assumed here — it is the *derived* lemma
  `μ₀_compat` below, which requires the one-sided ATT backdoor assumptions. -/
  μ₀_reg_compat :
    (fun ω => μ₀_val (toPOBackdoorSystem.factualX ω))
      =ᵐ[P.μ] toPOBackdoorSystem.adjustedCE false
  /-- Propensity factors through `factualX`:
  `propScore true =ᵐ e_val (factualX ·)`. -/
  e_compat :
    toPOBackdoorSystem.propScore true
      =ᵐ[P.μ] (fun ω => e_val (toPOBackdoorSystem.factualX ω))

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Control-arm backdoor CATE under ATT assumptions.** The conditional mean of
the untreated potential outcome given the covariates equals the observable
control regression when consistency, conditional ignorability, integrability,
and one-sided control overlap hold. No treated-arm overlap is used. -/
lemma control_cate_backdoor (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) :
    S.toPOBackdoorSystem.CATE false
      =ᵐ[P.μ] S.toPOBackdoorSystem.adjustedCE false :=
  S.toPOBackdoorSystem.cate_backdoor_of_propScore_ne hA.consistency
    hA.unconfoundedness hA.integrable_Y1 hA.integrable_Y0 false
    hA.propScore_false_ne

/-- **Treated propensity nonnegativity.** The conditional treatment probability
`P[D=1 | X]` is nonnegative almost surely because it is the conditional
expectation of a nonnegative treatment indicator. -/
lemma propScore_true_nonneg_ae (S : TreatedEstimationSystem P γ) :
    ∀ᵐ ω ∂P.μ, 0 ≤ S.toPOBackdoorSystem.propScore true ω :=
  MeasureTheory.condExp_nonneg (Filter.Eventually.of_forall
    (fun ω => by
      rcases S.toPOBackdoorSystem.dVar.indicator_eq_one_or_zero true ω with h | h <;>
        simp [h]))

/-- **Counterfactual compatibility (derived, under ATT identification).** The
control-arm outcome-regression representative equals the conditional mean of
the untreated potential outcome given the covariates, almost surely.

The observable regression compatibility `μ₀_reg_compat` is composed with the
one-sided control-arm backdoor identity. Thus the counterfactual binding is not
part of the estimation system's data; it holds under `ATTAssumptions`, without
the treated-arm overlap required for ATE. -/
lemma μ₀_compat (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) :
    P.μ[S.toPOBackdoorSystem.YofD false | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) :=
  (S.control_cate_backdoor hA).trans S.μ₀_reg_compat.symm

/-- One-sided overlap predicate `propScore true ω ≤ 1 − ε` a.s., with
`ε ∈ (0, 1/2]`.  The `0 < propScore true` half is implied at the PO level by
`Assumptions.overlap`; for ATT only the upper bound matters because the IPW
correction divides by `1 − e(X)`. -/
def OneSidedOverlap (S : TreatedEstimationSystem P γ) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧
    (∀ᵐ ω ∂P.μ, S.toPOBackdoorSystem.propScore true ω ≤ 1 - ε)

/-! ## Marginal of the covariate and joint data law -/

/-- Covariate marginal: `P_X := μ.map factualX`. -/
noncomputable def P_X (S : TreatedEstimationSystem P γ) : Measure γ :=
  P.μ.map S.toPOBackdoorSystem.factualX

/-- Data triple `(X, A, Y) : Ω → γ × Bool × ℝ`. -/
noncomputable def factualZ (S : TreatedEstimationSystem P γ) :
    P.Ω → γ × Bool × ℝ :=
  fun ω => (S.toPOBackdoorSystem.factualX ω,
            S.toPOBackdoorSystem.factualD ω,
            S.toPOBackdoorSystem.factualY ω)

/-- Measurability of the data triple. -/
lemma measurable_factualZ (S : TreatedEstimationSystem P γ) :
    Measurable S.factualZ :=
  (S.toPOBackdoorSystem.measurable_factualX).prodMk
    ((S.toPOBackdoorSystem.measurable_factualD).prodMk
      S.toPOBackdoorSystem.measurable_factualY)

/-- Joint data law `P_Z := μ.map (X, A, Y)`. -/
noncomputable def P_Z (S : TreatedEstimationSystem P γ) :
    Measure (γ × Bool × ℝ) :=
  P.μ.map S.factualZ

/-- The covariate marginal `P_X` is the pushforward of `P_Z` along the
projection `(x, a, y) ↦ x`.  Used to bridge integrals/`eLpNorm` between
`P_X` (covariates only) and `P_Z` (full data triple). -/
lemma P_Z_map_projX_eq_P_X (S : TreatedEstimationSystem P γ) :
    S.P_Z.map (fun z : γ × Bool × ℝ => z.1) = S.P_X := by
  unfold TreatedEstimationSystem.P_Z TreatedEstimationSystem.P_X
  rw [Measure.map_map (by fun_prop : Measurable (fun z : γ × Bool × ℝ => z.1))
    S.measurable_factualZ]
  rfl

/-! ## ATT estimand on the value space -/

/-- Marginal treatment probability `π = P[A = 1]`, viewed at the value-space
layer.  Delegates to the PO-level definition `POBackdoorSystem.propTreated`. -/
noncomputable def π_val (S : TreatedEstimationSystem P γ) : ℝ :=
  S.toPOBackdoorSystem.propTreated

/-- Value-space ATT estimand: delegates to the PO-level adjusted form
`POBackdoorSystem.adjustedATT`. -/
noncomputable def θ₀ (S : TreatedEstimationSystem P γ) : ℝ :=
  S.toPOBackdoorSystem.adjustedATT

/-- The value-space estimand agrees with the PO-level ATT under the back-door
ATT assumptions.  Direct restatement of `POBackdoorSystem.ATT_eq_adjustedATT`. -/
theorem θ₀_eq_ATT (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) :
    S.θ₀ = S.toPOBackdoorSystem.ATT := by
  unfold θ₀
  exact (S.toPOBackdoorSystem.ATT_eq_adjustedATT hA).symm

end TreatedEstimationSystem

/-! ## Derivability: the estimation system adds no assumptions beyond overlap -/

open Classical in
/-- **The compatibility/positivity fields are free.** From a `POBackdoorSystem` with
two-sided overlap and an integrable observed outcome — and *no* unconfoundedness — one
constructs a `TreatedEstimationSystem`: `μ₀_val` is the control-arm regression
`regFn false` and `e_val` is the propensity lift `eLift` clamped below `1`. Every added
field is discharged (`μ₀_reg_compat` from `regression_adjustment false`; `e_lt_one` from
the clamp; `e_compat` from overlap). So the control regression and propensity lifts were
never genuine assumptions. -/
noncomputable def _root_.Causalean.PO.POBackdoorSystem.toTreatedEstimationSystem
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    (S : PO.POBackdoorSystem P γ) [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hov : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hY : Integrable S.factualY P.μ) :
    TreatedEstimationSystem P γ where
  toPOBackdoorSystem := S
  μ₀_val := fun x => S.regFn (false, x)
  μ₀_meas := S.measurable_regFn.comp (measurable_const.prodMk measurable_id)
  e_val := Set.piecewise {x : γ | S.eLift x < 1} S.eLift (fun _ => 1 / 2)
  e_meas :=
    Measurable.piecewise (measurableSet_lt S.measurable_eLift measurable_const)
      S.measurable_eLift measurable_const
  e_lt_one := by
    intro x
    by_cases hx : x ∈ {x : γ | S.eLift x < 1}
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; norm_num
  μ₀_reg_compat :=
    (S.regression_adjustment false hY (S.propScore_ne_of_overlap hov false)).symm
  e_compat := by
    filter_upwards [hov] with ω hω
    have heq : S.propScore true ω = S.eLift (S.factualX ω) :=
      congrFun S.propScore_true_eq_eLift ω
    have hmem : S.factualX ω ∈ {x : γ | S.eLift x < 1} := by
      rw [Set.mem_setOf_eq, ← heq]; exact hω.2
    rw [heq, Set.piecewise_eq_of_mem _ _ _ hmem]

end ATT
end Estimation
end Causalean
