/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Exact.Proximal.Setup
import Mathlib.Probability.Independence.Conditional

/-! # Proximal Assumptions

This file states the proximal proxy assumptions for average treatment effect
identification. `POProximalSystem.Assumptions` bundles consistency, latent
exchangeability, outcome-side and treatment-side proxy restrictions, an outcome
bridge equation, arm positivity, treatment-arm completeness, and the
integrability conditions needed for the bridge representation.

The assumptions follow the Miao, Geng, and Tchetgen Tchetgen proximal
identification setup. The only exported lemma, `Assumptions.integrable_Y`, is a
compatibility projection showing that factual outcome integrability follows
from consistency and integrability of the two potential-outcome cells. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POProximalSystem

variable {P : POSystem}
  {γ_X γ_Z γ_W γ_U : Type*}
  [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
  [MeasurableSpace γ_W] [MeasurableSpace γ_U]

/-- Proximal ATE assumption bundle (def:po-proximal-assumptions).

Fields:
- `consistency`     : the ambient PO system satisfies POSystem.Consistency.
- `latent_exch`     : Y(a) ⟂ A | (U,X) for each a ∈ {0,1}.
- `proxy_YZ`        : Y ⟂ Z | (A,U,X).
- `proxy_WAZ`       : W ⟂ (A,Z) | (U,X).
- `h`               : bridge function h : Bool × γ_W × γ_X → ℝ.
- `measurable_h`    : h is measurable.
- `integrable_hAWX` : h(A,W,X) is integrable.
- `bridge`          : E[Y - h(A,W,X) | σ(A,Z,X)] = 0 a.s.
- `positivity_arm`  : every σ_UX-measurable positive-μ set has positive
                      intersection with each arm `{A=a}` (Miao 2018 Asm. 7).
- `completeness`    : for each a, Z|{A=a} is complete for (U,X)-functionals,
                      with stratum-wise conclusion (Miao 2018 Asm. 8).
- `integrable_YofA0`: Y(0) is integrable.
- `integrable_YofA1`: Y(1) is integrable.
- `integrable_h0WX` : h(0,W,X) is integrable.
- `integrable_h1WX` : h(1,W,X) is integrable.
-/
structure Assumptions
    (S : POProximalSystem P γ_X γ_Z γ_W γ_U)
    (μ : Measure P.Ω := P.μ) [IsFiniteMeasure μ]
    [StandardBorelSpace P.Ω] where
  /-- Consistency axiom for the ambient PO system. -/
  consistency : POSystem.Consistency P
  /-- Latent exchangeability: Y(a) ⟂ A | (U,X) for each treatment level. -/
  latent_exch : ∀ a : Bool,
    CondIndepFun S.σ_UX S.σ_UX_le (S.YofA a) S.A μ
  /-- Proxy restriction (outcome side): Y ⟂ Z | (A,U,X). -/
  proxy_YZ : CondIndepFun S.σ_AUX S.σ_AUX_le S.Y S.Z μ
  /-- Proxy restriction (treatment side): W ⟂ (A,Z) | (U,X). -/
  proxy_WAZ : CondIndepFun S.σ_UX S.σ_UX_le S.W (fun ω => (S.A ω, S.Z ω)) μ
  /-- Bridge function h : Bool × γ_W × γ_X → ℝ. -/
  h : Bool × γ_W × γ_X → ℝ
  /-- h is measurable. -/
  measurable_h : Measurable h
  /-- h(A,W,X) is integrable under μ. -/
  integrable_hAWX : Integrable (fun ω => h (S.A ω, S.W ω, S.X ω)) μ
  /-- Outcome bridge: E[Y - h(A,W,X) | σ(A,Z,X)] = 0 a.s. -/
  bridge : (μ[fun ω => S.Y ω - h (S.A ω, S.W ω, S.X ω) | S.σ_AZX]) =ᵐ[μ] 0
  /-- Positivity (Miao-Geng-Tchetgen Tchetgen 2018, Assumption 7).

  Every σ_UX-measurable set of positive μ-measure intersects each arm
  `{A=a}` in a positive-measure subset. Equivalently (contrapositive):
  if a σ_UX-measurable set `B` has μ-null intersection with the arm, then
  `B` itself is μ-null.

  This is the measure-zero form of `0 < P(A=a | U, X)` a.s., chosen because
  it is consumed directly by the stratum-to-global lift in `Helpers.lean`
  (see `eq_zero_globally_of_eq_zero_on_arm`). -/
  positivity_arm :
    ∀ (a : Bool) (B : Set P.Ω),
      MeasurableSet[S.σ_UX] B →
      μ (B ∩ {ω | S.A ω = a}) = 0 → μ B = 0
  /-- Completeness within treatment level
  (Miao-Geng-Tchetgen Tchetgen 2018, Assumption 8).

  For each `a ∈ {0,1}` and every measurable `g : γ_U × γ_X → ℝ` integrable
  on `μ.restrict {A=a}`,
    if  μ[g(U,X) | σ(A,Z,X)] = 0 a.s. on {A=a},
    then  g(U,X) = 0 a.s. on {A=a}.

  Conclusion is **stratum-wise** (`=ᵐ[μ.restrict {A=a}]`), not global,
  matching the classical pointwise-in-(a,x) statement under disintegration.
  The global conclusion is recovered downstream (step 7 of `Main.lean`)
  by combining this with `positivity_arm`. -/
  completeness :
    ∀ (a : Bool) (g : γ_U × γ_X → ℝ),
      Measurable g →
      Integrable (fun ω => g (S.UX ω)) (μ.restrict {ω | S.A ω = a}) →
      (μ[fun ω => g (S.UX ω) | S.σ_AZX]) =ᵐ[μ.restrict {ω | S.A ω = a}] 0 →
      (fun ω => g (S.UX ω)) =ᵐ[μ.restrict {ω | S.A ω = a}] 0
  /-- Integrability of Y(0). -/
  integrable_YofA0 : Integrable (S.YofA false) μ
  /-- Integrability of Y(1). -/
  integrable_YofA1 : Integrable (S.YofA true) μ
  /-- Integrability of h(0,W,X). -/
  integrable_h0WX : Integrable (fun ω => h (false, S.W ω, S.X ω)) μ
  /-- Integrability of h(1,W,X). -/
  integrable_h1WX : Integrable (fun ω => h (true, S.W ω, S.X ω)) μ

namespace Assumptions

variable {S : POProximalSystem P γ_X γ_Z γ_W γ_U}
  {μ : Measure P.Ω} [IsFiniteMeasure μ] [StandardBorelSpace P.Ω]

omit [IsFiniteMeasure μ] [StandardBorelSpace P.Ω] in
private lemma integrable_mul_indicator {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : POVar P α) (x : α)
    {f : P.Ω → ℝ} (hf : Integrable f μ) (hf_meas : Measurable f) :
    Integrable (fun ω => f ω * a.indicator x ω) μ := by
  refine hf.mono (hf_meas.mul (a.measurable_indicator x)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rcases a.indicator_eq_one_or_zero x ω with h | h <;> simp [h]

/-- Compatibility projection: factual outcome integrability follows from
consistency and integrability of the two potential-outcome cells. -/
lemma integrable_Y (HA : Assumptions S μ) (hAY : S.Avar.v ≠ S.Yvar.v) :
    Integrable S.Y μ := by
  have htrue_int : Integrable (fun ω => S.YofA true ω * S.Avar.indicator true ω) μ :=
    integrable_mul_indicator S.Avar true HA.integrable_YofA1 (S.measurable_YofA true)
  have hfalse_int : Integrable (fun ω => S.YofA false ω * S.Avar.indicator false ω) μ :=
    integrable_mul_indicator S.Avar false HA.integrable_YofA0 (S.measurable_YofA false)
  have hsum_int : Integrable
      ((fun ω => S.YofA true ω * S.Avar.indicator true ω) +
        fun ω => S.YofA false ω * S.Avar.indicator false ω) μ :=
    htrue_int.add hfalse_int
  refine hsum_int.congr (Filter.Eventually.of_forall ?_)
  intro ω
  by_cases hω : S.A ω = true
  · have hcf : S.YofA true ω = S.Y ω := by
      simpa [YofA, Y, A] using
        POVar.cf_eq_factual_on_event HA.consistency S.Yvar S.Avar true hAY.symm hω
    have hind_true : S.Avar.indicator true ω = 1 :=
      S.Avar.indicator_apply_eq_one hω
    have hfalse : S.A ω ≠ false := by
      rw [hω]
      decide
    have hind_false : S.Avar.indicator false ω = 0 :=
      S.Avar.indicator_apply_eq_zero hfalse
    simp [Pi.add_apply, hcf, hind_true, hind_false]
  · have hω_false : S.A ω = false := by
      cases hA : S.A ω <;> simp_all
    have hcf : S.YofA false ω = S.Y ω := by
      simpa [YofA, Y, A] using
        POVar.cf_eq_factual_on_event HA.consistency S.Yvar S.Avar false hAY.symm hω_false
    have hind_true : S.Avar.indicator true ω = 0 :=
      S.Avar.indicator_apply_eq_zero hω
    have hind_false : S.Avar.indicator false ω = 1 :=
      S.Avar.indicator_apply_eq_one hω_false
    simp [Pi.add_apply, hcf, hind_true, hind_false]

end Assumptions

end POProximalSystem

end PO
end Causalean
