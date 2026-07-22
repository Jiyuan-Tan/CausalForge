/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sequential DR (AIPW) moment, influence function, and overlap-bounded
# nuisance space for `n = 2` DTR estimation

* `seqDRMoment dbar z η θ`            — sequential AIPW moment for `n = 2`
                                        DTR (`m_seqDR` from the plan).
* `ψ_seqDR S z`                       — influence function at the truth.
* `DTRNuisanceVec₂ γ`                 — quadruple `(μ₀_fn, e₀_fn, μ₁_fn, e₁_fn)`
                                        with measurability witnesses, equipped
                                        with componentwise `AddCommGroup` and
                                        `Module ℝ` instances so it can be fed
                                        to `NeymanOrthogonal`.
* `H_ε ε`                             — overlap-bounded realization set.
* `seqDRMomentFunctional`             — `m_seqDR` viewed as
                                        `DTRNuisanceVec₂ γ → … → ℝ`.

Bundle ordering convention: cons-order `(s₁, d₀, s₀)` matches
`historyBundle 1 = cons S₁ (cons D₀ (cons S₀ nil))` from `Setup.lean`.
The data tuple is `(s₀, d₀, s₁, d₁, y) : γ 0 × δ × γ 1 × δ × ℝ`.

Mirrors the structure of `Estimation/ATE/AIPWMoment.lean`.
-/

import Causalean.Estimation.DTR.Setup

/-!
# Sequential DR Moment for Two-Stage Regimes

This file defines the explicit two-stage sequential AIPW moment for dynamic
treatment regimes, its truth-level influence function, and the overlap-bounded
nuisance space used by the abstract DML layer.  The target is the fixed-regime
mean for a two-period regime, and the score uses stagewise inverse-propensity
weights centered by the target estimand.

The development is intentionally specialized to horizon two; the treatment space
is discrete enough to support equality indicators.  The stage-1 history is stored
in cons order as the current state, previous treatment, and previous state.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

/-! ## Projections out of the data tuple -/

variable {δ : Type} [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable {γ : Fin 2 → Type} [∀ k, MeasurableSpace (γ k)]

/-- This projection returns the initial state from the observed two-stage data tuple. -/
def projS₀ : γ 0 × δ × γ 1 × δ × ℝ → γ 0 := fun z => z.1

/-- This projection returns the first treatment from the observed two-stage data tuple. -/
def projD₀ : γ 0 × δ × γ 1 × δ × ℝ → δ := fun z => z.2.1

/-- This projection returns the second state from the observed two-stage data tuple. -/
def projS₁ : γ 0 × δ × γ 1 × δ × ℝ → γ 1 := fun z => z.2.2.1

/-- This projection returns the second treatment from the observed two-stage data tuple. -/
def projD₁ : γ 0 × δ × γ 1 × δ × ℝ → δ := fun z => z.2.2.2.1

/-- This projection returns the outcome from the observed two-stage data tuple. -/
def projY : γ 0 × δ × γ 1 × δ × ℝ → ℝ := fun z => z.2.2.2.2

/-- This projection returns the stage-1 history in the order used by the DTR history bundle.

It records the current state, the previous treatment, and the previous state. -/
def histH₁ (z : γ 0 × δ × γ 1 × δ × ℝ) : γ 1 × δ × γ 0 :=
  (projS₁ z, projD₀ z, projS₀ z)

/-- This function is the real-valued indicator that two discrete treatments are equal. -/
noncomputable def indEq (d d' : δ) : ℝ :=
  haveI : Decidable (d = d') := Classical.dec _
  if d = d' then 1 else 0

/-! ## Nuisance vector for sequential DR (n = 2) -/

end DTR
end Estimation
end Causalean

namespace Causalean
namespace Estimation
namespace DTR

/-- Stagewise nuisance vector for two-period dynamic-treatment-regime estimation.

The fields are the value-space nuisance functions used by the sequential
doubly-robust moment. `μ₀_fn` and `e₀_fn` are the baseline outcome regression
and treatment propensity as functions of first-period covariates. `μ₁_fn` and
`e₁_fn` are the second-stage outcome regression and treatment propensity as
functions of second-period covariates, the first-period treatment/action, and
first-period covariates. The remaining fields certify measurability of these
four nuisance functions. -/
structure DTRNuisanceVec₂ (δ : Type) (γ : Fin 2 → Type)
    [MeasurableSpace δ] [MeasurableSingletonClass δ]
    [∀ k, MeasurableSpace (γ k)] where
  μ₀_fn : γ 0 → ℝ
  e₀_fn : γ 0 → ℝ
  μ₁_fn : γ 1 × δ × γ 0 → ℝ
  e₁_fn : γ 1 × δ × γ 0 → ℝ
  μ₀_meas : Measurable μ₀_fn
  e₀_meas : Measurable e₀_fn
  μ₁_meas : Measurable μ₁_fn
  e₁_meas : Measurable e₁_fn

namespace DTRNuisanceVec₂

variable {δ : Type} [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable {γ : Fin 2 → Type} [∀ k, MeasurableSpace (γ k)]

/-- The zero nuisance vector sets every stagewise regression and propensity component to zero. -/
instance : Zero (DTRNuisanceVec₂ δ γ) where
  zero :=
    ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
     measurable_const, measurable_const, measurable_const, measurable_const⟩

/-- Addition of nuisance vectors is performed component by component. -/
instance : Add (DTRNuisanceVec₂ δ γ) where
  add η η' :=
    ⟨fun s => η.μ₀_fn s + η'.μ₀_fn s,
     fun s => η.e₀_fn s + η'.e₀_fn s,
     fun h => η.μ₁_fn h + η'.μ₁_fn h,
     fun h => η.e₁_fn h + η'.e₁_fn h,
     η.μ₀_meas.add η'.μ₀_meas,
     η.e₀_meas.add η'.e₀_meas,
     η.μ₁_meas.add η'.μ₁_meas,
     η.e₁_meas.add η'.e₁_meas⟩

/-- Negation of a nuisance vector is performed component by component. -/
instance : Neg (DTRNuisanceVec₂ δ γ) where
  neg η :=
    ⟨fun s => -η.μ₀_fn s, fun s => -η.e₀_fn s,
     fun h => -η.μ₁_fn h, fun h => -η.e₁_fn h,
     η.μ₀_meas.neg, η.e₀_meas.neg, η.μ₁_meas.neg, η.e₁_meas.neg⟩

/-- Subtraction of nuisance vectors is performed component by component. -/
instance : Sub (DTRNuisanceVec₂ δ γ) where
  sub η η' :=
    ⟨fun s => η.μ₀_fn s - η'.μ₀_fn s,
     fun s => η.e₀_fn s - η'.e₀_fn s,
     fun h => η.μ₁_fn h - η'.μ₁_fn h,
     fun h => η.e₁_fn h - η'.e₁_fn h,
     η.μ₀_meas.sub η'.μ₀_meas,
     η.e₀_meas.sub η'.e₀_meas,
     η.μ₁_meas.sub η'.μ₁_meas,
     η.e₁_meas.sub η'.e₁_meas⟩

/-- Real scalar multiplication of a nuisance vector is performed component by component. -/
instance : SMul ℝ (DTRNuisanceVec₂ δ γ) where
  smul t η :=
    ⟨fun s => t * η.μ₀_fn s, fun s => t * η.e₀_fn s,
     fun h => t * η.μ₁_fn h, fun h => t * η.e₁_fn h,
     measurable_const.mul η.μ₀_meas,
     measurable_const.mul η.e₀_meas,
     measurable_const.mul η.μ₁_meas,
     measurable_const.mul η.e₁_meas⟩

/-- Two nuisance vectors are equal when all four stagewise components agree pointwise. -/
@[ext]
theorem ext {η η' : DTRNuisanceVec₂ δ γ}
    (h0μ : ∀ s, η.μ₀_fn s = η'.μ₀_fn s)
    (h0e : ∀ s, η.e₀_fn s = η'.e₀_fn s)
    (h1μ : ∀ h, η.μ₁_fn h = η'.μ₁_fn h)
    (h1e : ∀ h, η.e₁_fn h = η'.e₁_fn h) : η = η' := by
  cases η
  cases η'
  simp only at h0μ h0e h1μ h1e
  congr
  · funext s; exact h0μ s
  · funext s; exact h0e s
  · funext h; exact h1μ h
  · funext h; exact h1e h

/-- The nuisance vectors form an additive commutative group under componentwise operations. -/
instance : AddCommGroup (DTRNuisanceVec₂ δ γ) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  nsmul := nsmulRec
  zsmul := zsmulRec
  nsmul_zero η := by rfl
  nsmul_succ n η := by rfl
  zsmul_zero' η := by rfl
  zsmul_succ' n η := by rfl
  zsmul_neg' n η := by rfl
  sub_eq_add_neg η η' := by
    apply ext
    · intro s; exact sub_eq_add_neg (η.μ₀_fn s) (η'.μ₀_fn s)
    · intro s; exact sub_eq_add_neg (η.e₀_fn s) (η'.e₀_fn s)
    · intro h; exact sub_eq_add_neg (η.μ₁_fn h) (η'.μ₁_fn h)
    · intro h; exact sub_eq_add_neg (η.e₁_fn h) (η'.e₁_fn h)
  add_assoc η η' η'' := by
    apply ext
    · intro s; exact add_assoc (η.μ₀_fn s) (η'.μ₀_fn s) (η''.μ₀_fn s)
    · intro s; exact add_assoc (η.e₀_fn s) (η'.e₀_fn s) (η''.e₀_fn s)
    · intro h; exact add_assoc (η.μ₁_fn h) (η'.μ₁_fn h) (η''.μ₁_fn h)
    · intro h; exact add_assoc (η.e₁_fn h) (η'.e₁_fn h) (η''.e₁_fn h)
  zero_add η := by
    apply ext
    · intro s; exact zero_add (η.μ₀_fn s)
    · intro s; exact zero_add (η.e₀_fn s)
    · intro h; exact zero_add (η.μ₁_fn h)
    · intro h; exact zero_add (η.e₁_fn h)
  add_zero η := by
    apply ext
    · intro s; exact add_zero (η.μ₀_fn s)
    · intro s; exact add_zero (η.e₀_fn s)
    · intro h; exact add_zero (η.μ₁_fn h)
    · intro h; exact add_zero (η.e₁_fn h)
  neg_add_cancel η := by
    apply ext
    · intro s; exact neg_add_cancel (η.μ₀_fn s)
    · intro s; exact neg_add_cancel (η.e₀_fn s)
    · intro h; exact neg_add_cancel (η.μ₁_fn h)
    · intro h; exact neg_add_cancel (η.e₁_fn h)
  add_comm η η' := by
    apply ext
    · intro s; exact add_comm (η.μ₀_fn s) (η'.μ₀_fn s)
    · intro s; exact add_comm (η.e₀_fn s) (η'.e₀_fn s)
    · intro h; exact add_comm (η.μ₁_fn h) (η'.μ₁_fn h)
    · intro h; exact add_comm (η.e₁_fn h) (η'.e₁_fn h)

/-- The nuisance vectors form a real module under componentwise scalar multiplication. -/
instance : Module ℝ (DTRNuisanceVec₂ δ γ) where
  smul := (· • ·)
  one_smul η := by
    apply ext
    · intro s; change (1 : ℝ) * η.μ₀_fn s = η.μ₀_fn s; exact one_mul _
    · intro s; change (1 : ℝ) * η.e₀_fn s = η.e₀_fn s; exact one_mul _
    · intro h; change (1 : ℝ) * η.μ₁_fn h = η.μ₁_fn h; exact one_mul _
    · intro h; change (1 : ℝ) * η.e₁_fn h = η.e₁_fn h; exact one_mul _
  mul_smul t u η := by
    apply ext
    · intro s; change (t * u) * η.μ₀_fn s = t * (u * η.μ₀_fn s); ring
    · intro s; change (t * u) * η.e₀_fn s = t * (u * η.e₀_fn s); ring
    · intro h; change (t * u) * η.μ₁_fn h = t * (u * η.μ₁_fn h); ring
    · intro h; change (t * u) * η.e₁_fn h = t * (u * η.e₁_fn h); ring
  smul_zero t := by
    apply ext
    · intro s; change t * (0 : ℝ) = 0; exact mul_zero t
    · intro s; change t * (0 : ℝ) = 0; exact mul_zero t
    · intro h; change t * (0 : ℝ) = 0; exact mul_zero t
    · intro h; change t * (0 : ℝ) = 0; exact mul_zero t
  smul_add t η η' := by
    apply ext
    · intro s
      change t * (η.μ₀_fn s + η'.μ₀_fn s) = t * η.μ₀_fn s + t * η'.μ₀_fn s
      ring
    · intro s
      change t * (η.e₀_fn s + η'.e₀_fn s) = t * η.e₀_fn s + t * η'.e₀_fn s
      ring
    · intro h
      change t * (η.μ₁_fn h + η'.μ₁_fn h) = t * η.μ₁_fn h + t * η'.μ₁_fn h
      ring
    · intro h
      change t * (η.e₁_fn h + η'.e₁_fn h) = t * η.e₁_fn h + t * η'.e₁_fn h
      ring
  add_smul t u η := by
    apply ext
    · intro s
      change (t + u) * η.μ₀_fn s = t * η.μ₀_fn s + u * η.μ₀_fn s
      ring
    · intro s
      change (t + u) * η.e₀_fn s = t * η.e₀_fn s + u * η.e₀_fn s
      ring
    · intro h
      change (t + u) * η.μ₁_fn h = t * η.μ₁_fn h + u * η.μ₁_fn h
      ring
    · intro h
      change (t + u) * η.e₁_fn h = t * η.e₁_fn h + u * η.e₁_fn h
      ring
  zero_smul η := by
    apply ext
    · intro s; change (0 : ℝ) * η.μ₀_fn s = 0; exact zero_mul _
    · intro s; change (0 : ℝ) * η.e₀_fn s = 0; exact zero_mul _
    · intro h; change (0 : ℝ) * η.μ₁_fn h = 0; exact zero_mul _
    · intro h; change (0 : ℝ) * η.e₁_fn h = 0; exact zero_mul _

end DTRNuisanceVec₂

end DTR
end Estimation
end Causalean

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

/-! ## Sequential DR moment and influence function -/

variable {δ : Type} [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable {γ : Fin 2 → Type} [∀ k, MeasurableSpace (γ k)]

/-- This is the explicit two-stage sequential doubly robust moment for a fixed treatment regime.

It combines the stage-0 regression, the stage-1 regression correction, and the final outcome
residual correction with stagewise inverse-propensity weights, then centers by the candidate
target value.

    seqDRMoment dbar z η θ
      = η.μ₀_fn s₀
        + (1{d₀ = dbar 0} / η.e₀_fn s₀)
            * (η.μ₁_fn (s₁, d₀, s₀) - η.μ₀_fn s₀)
        + (1{d₀ = dbar 0} · 1{d₁ = dbar 1} /
            (η.e₀_fn s₀ · η.e₁_fn (s₁, d₀, s₀)))
            * (y - η.μ₁_fn (s₁, d₀, s₀))
        - θ.

The target regime `dbar` is supplied as an argument since it lives at the
system level (`DTREstimationSystem.dbar`).  Use `S.seqDRMoment` (the wrapped
form) to feed it `S.dbar` directly. -/
noncomputable def seqDRMoment
    (dbar : Fin 2 → δ) (z : γ 0 × δ × γ 1 × δ × ℝ)
    (η : DTRNuisanceVec₂ δ γ) (θ : ℝ) : ℝ :=
  η.μ₀_fn (projS₀ z)
    + (indEq (projD₀ z) (dbar 0) / η.e₀_fn (projS₀ z))
        * (η.μ₁_fn (histH₁ z) - η.μ₀_fn (projS₀ z))
    + (indEq (projD₀ z) (dbar 0) * indEq (projD₁ z) (dbar 1) /
        (η.e₀_fn (projS₀ z) * η.e₁_fn (histH₁ z)))
        * (projY z - η.μ₁_fn (histH₁ z))
    - θ

namespace DTREstimationSystem

variable {P : POSystem}
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- This is the true nuisance vector extracted from a two-stage DTR estimation system. -/
noncomputable def η₀ (S : DTREstimationSystem P δ γ) :
    DTRNuisanceVec₂ δ γ :=
  ⟨S.μ₀_val, S.e₀_val, S.μ₁_val, S.e₁_val,
   S.μ₀_meas, S.e₀_meas, S.μ₁_meas, S.e₁_meas⟩

/-- This is the sequential doubly robust moment specialized to the system's target regime. -/
noncomputable def seqDRMoment (S : DTREstimationSystem P δ γ)
    (z : γ 0 × δ × γ 1 × δ × ℝ) (η : DTRNuisanceVec₂ δ γ) (θ : ℝ) : ℝ :=
  Causalean.Estimation.DTR.seqDRMoment S.dbar z η θ

/-- This is the sequential doubly robust influence function evaluated at the true nuisances and target. -/
noncomputable def ψ_seqDR (S : DTREstimationSystem P δ γ)
    (z : γ 0 × δ × γ 1 × δ × ℝ) : ℝ :=
  S.seqDRMoment z S.η₀ S.θ₀

/-- This set contains nuisance candidates whose two propensity components are uniformly overlap-bounded.

The bounds are pointwise on the stage-0 and stage-1 history spaces. -/
def H_ε (ε : ℝ) : Set (DTRNuisanceVec₂ δ γ) :=
  { η | (∀ s, ε ≤ η.e₀_fn s ∧ η.e₀_fn s ≤ 1 - ε)
        ∧ (∀ h, ε ≤ η.e₁_fn h ∧ η.e₁_fn h ≤ 1 - ε) }

/-- This is the sequential doubly robust moment packaged as a functional of nuisance, data, and target value. -/
noncomputable def seqDRMomentFunctional (S : DTREstimationSystem P δ γ) :
    DTRNuisanceVec₂ δ γ → (γ 0 × δ × γ 1 × δ × ℝ) → ℝ → ℝ :=
  fun η z θ => Causalean.Estimation.DTR.seqDRMoment S.dbar z η θ

/-- The sequential doubly robust moment functional is measurable as a function of the observed data tuple.

This measurability result lets the abstract DML layer consume the moment. -/
lemma measurable_seqDRMomentFunctional (S : DTREstimationSystem P δ γ)
    (η : DTRNuisanceVec₂ δ γ) (θ : ℝ) :
    Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
      S.seqDRMomentFunctional η z θ) := by
  unfold DTREstimationSystem.seqDRMomentFunctional
  unfold Causalean.Estimation.DTR.seqDRMoment
  have hs0 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z) := by
    unfold projS₀
    exact measurable_fst
  have hd0 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => projD₀ z) := by
    unfold projD₀
    measurability
  have hd1 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => projD₁ z) := by
    unfold projD₁
    measurability
  have hy : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => projY z) := by
    unfold projY
    measurability
  have hh1 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z) := by
    unfold histH₁ projS₁ projD₀ projS₀
    measurability
  have hμ0 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
      η.μ₀_fn (projS₀ z)) := η.μ₀_meas.comp hs0
  have he0 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
      η.e₀_fn (projS₀ z)) := η.e₀_meas.comp hs0
  have hμ1 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
      η.μ₁_fn (histH₁ z)) := η.μ₁_meas.comp hh1
  have he1 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
      η.e₁_fn (histH₁ z)) := η.e₁_meas.comp hh1
  have hind0 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
      indEq (projD₀ z) (S.dbar 0)) := by
    have hset : MeasurableSet
        {z : γ 0 × δ × γ 1 × δ × ℝ | projD₀ z = S.dbar 0} :=
      (MeasurableSet.singleton (S.dbar 0)).preimage hd0
    convert (measurable_const.indicator hset : Measurable
      (Set.indicator {z : γ 0 × δ × γ 1 × δ × ℝ | projD₀ z = S.dbar 0}
        (fun _ => (1 : ℝ)))) using 1
  have hind1 : Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
      indEq (projD₁ z) (S.dbar 1)) := by
    have hset : MeasurableSet
        {z : γ 0 × δ × γ 1 × δ × ℝ | projD₁ z = S.dbar 1} :=
      (MeasurableSet.singleton (S.dbar 1)).preimage hd1
    convert (measurable_const.indicator hset : Measurable
      (Set.indicator {z : γ 0 × δ × γ 1 × δ × ℝ | projD₁ z = S.dbar 1}
        (fun _ => (1 : ℝ)))) using 1
  exact ((hμ0.add ((hind0.div he0).mul (hμ1.sub hμ0))).add
    (((hind0.mul hind1).div (he0.mul he1)).mul (hy.sub hμ1))).sub measurable_const

omit [MeasurableSingletonClass δ] in
/-- The initial-state projection is measurable. -/
lemma measurable_projS₀ :
    Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z) := by
  unfold projS₀; exact measurable_fst

omit [MeasurableSingletonClass δ] in
/-- The cons-ordered stage-1 history projection is measurable. -/
lemma measurable_histH₁ :
    Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z) := by
  unfold histH₁ projS₁ projD₀ projS₀; measurability

/-- Pushing the full observed data law through the initial-state projection gives the stage-0 history marginal. -/
lemma P_Z_map_projS₀_eq_P_H₀ (S : DTREstimationSystem P δ γ) :
    S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z) = S.P_H₀ := by
  unfold DTREstimationSystem.P_Z DTREstimationSystem.P_H₀
  rw [Measure.map_map measurable_projS₀ S.measurable_factualZ]; rfl

/-- Pushing the full observed data law through the stage-1 history projection gives the stage-1 history marginal. -/
lemma P_Z_map_histH₁_eq_P_H₁ (S : DTREstimationSystem P δ γ) :
    S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z) = S.P_H₁ := by
  unfold DTREstimationSystem.P_Z DTREstimationSystem.P_H₁
  rw [Measure.map_map measurable_histH₁ S.measurable_factualZ]; rfl

end DTREstimationSystem

end DTR
end Estimation
end Causalean
