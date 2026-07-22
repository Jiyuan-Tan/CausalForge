/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW moment, influence function, and overlap-bounded nuisance space (ATT)

Parallels `Estimation/ATE/Score/AIPWMoment.lean` for the ATT version.

* `aipwMomentATT z μ₀_fn e_fn θ`     — ATT AIPW moment (Hahn 1998, post-rescale).
* `ψ_ATT S z`                         — influence function at the truth.
* `TreatedNuisanceVec γ`              — pair `(μ₀_fn, e_fn)` with measurability,
                                        equipped with componentwise `AddCommGroup`
                                        and `Module ℝ` instances.
* `H_ε ε`                             — one-sided overlap-bounded realization set.
* `aipwMomentATTFunctional`           — moment as `TreatedNuisanceVec γ → … → ℝ`.

Re-uses the data-projection helpers `projX`, `projA`, `projY`, `indA` from the
ATE version to avoid duplication.
-/

import Causalean.Estimation.ATT.Setup
import Causalean.Estimation.ATE.Score.AIPWMoment

/-!
Defines the value-space ingredients for ATT augmented inverse-probability
weighting. The file introduces the un-normalized moment `aipwMomentATT`, the
truth influence function `ψ_ATT`, the nuisance vector `TreatedNuisanceVec` with
componentwise vector-space structure, the true nuisance `η₀`, and the one-sided
overlap class `H_ε`.

It also provides measurability and law-transport helpers, including
`H_ε_overlap_factualX`, `H_ε_overlap_P_Z`, `aipwMomentATTFunctional`, and
`measurable_aipwMomentATTFunctional`, used by the mean-zero, finite-variance,
remainder, and score-continuity modules.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO
open Causalean.Estimation.ATE.BackdoorEstimationSystem (projX projA projY indA)

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## AIPW moment and influence function for ATT -/

/-- The ATT AIPW moment

    A · (Y − μ₀(X))
      − (1 − A) · (e(X) / (1 − e(X))) · (Y − μ₀(X))
      − A · θ

(Hahn 1998 form).  The factor `1/π` enters in `ψ_ATT` as the IF rescale; here
the moment is presented in its un-normalized form so that
`E[m_AIPW(η₀, Z, θ_ATT)] = 0`. -/
noncomputable def aipwMomentATT
    (z : γ × Bool × ℝ) (μ₀_fn : γ → ℝ) (e_fn : γ → ℝ) (θ : ℝ) : ℝ :=
  indA z * (projY z - μ₀_fn (projX z))
    - (1 - indA z) * (e_fn (projX z) / (1 - e_fn (projX z)))
        * (projY z - μ₀_fn (projX z))
    - indA z * θ

/-- The ATT AIPW influence function at the truth for the population-`π_T`
one-shot estimator:
`ψ_ATT(z) := (1/π) · m_AIPW(η₀, z, 0) − θ₀`.

The explicit centering matches `Stat.IsAsymLinear`, whose influence function
field has mean zero.  The empirical-`π_T` ratio version instead centers through
the `−A·θ₀` term inside `m_AIPW(η₀, z, θ₀)`. -/
noncomputable def ψ_ATT (S : TreatedEstimationSystem P γ)
    (z : γ × Bool × ℝ) : ℝ :=
  (1 / S.π_val) * aipwMomentATT z S.μ₀_val S.e_val 0 - S.θ₀

end TreatedEstimationSystem

/-! ## Overlap-bounded nuisance space `H_ε`

We package nuisance pairs `(μ₀_fn, e_fn)` together with their measurability as
`TreatedNuisanceVec`, with vector-space operations defined componentwise. -/

/-- Pair of value-space nuisance functions `(μ₀_fn, e_fn)` together with
measurability witnesses.  Used as the abstract nuisance space `H` for the
ATT AIPW moment functional. -/
structure TreatedNuisanceVec (γ : Type*) [MeasurableSpace γ] where
  μ₀_fn : γ → ℝ
  e_fn  : γ → ℝ
  μ₀_meas : Measurable μ₀_fn
  e_meas  : Measurable e_fn

namespace TreatedNuisanceVec

variable {γ : Type*} [MeasurableSpace γ]

/-- The zero treated-nuisance vector sets the control regression and propensity function to zero. -/
instance : Zero (TreatedNuisanceVec γ) where
  zero := ⟨fun _ => 0, fun _ => 0, measurable_const, measurable_const⟩

/-- Addition of treated-nuisance vectors is componentwise addition of the control regression and propensity function. -/
instance : Add (TreatedNuisanceVec γ) where
  add η η' :=
    ⟨fun x => η.μ₀_fn x + η'.μ₀_fn x,
     fun x => η.e_fn x + η'.e_fn x,
     η.μ₀_meas.add η'.μ₀_meas,
     η.e_meas.add η'.e_meas⟩

/-- Negation of a treated-nuisance vector negates the control regression and propensity function. -/
instance : Neg (TreatedNuisanceVec γ) where
  neg η :=
    ⟨fun x => -η.μ₀_fn x, fun x => -η.e_fn x,
     η.μ₀_meas.neg, η.e_meas.neg⟩

/-- Subtraction of treated-nuisance vectors is componentwise subtraction of the control regression and propensity function. -/
instance : Sub (TreatedNuisanceVec γ) where
  sub η η' :=
    ⟨fun x => η.μ₀_fn x - η'.μ₀_fn x,
     fun x => η.e_fn x - η'.e_fn x,
     η.μ₀_meas.sub η'.μ₀_meas,
     η.e_meas.sub η'.e_meas⟩

/-- Scalar multiplication of a treated-nuisance vector scales the control regression and propensity function. -/
instance : SMul ℝ (TreatedNuisanceVec γ) where
  smul t η :=
    ⟨fun x => t * η.μ₀_fn x, fun x => t * η.e_fn x,
     measurable_const.mul η.μ₀_meas,
     measurable_const.mul η.e_meas⟩

/-- Two treated-nuisance vectors are equal when their control regressions and propensity functions agree everywhere. -/
@[ext]
theorem ext {η η' : TreatedNuisanceVec γ}
    (hμ : ∀ x, η.μ₀_fn x = η'.μ₀_fn x)
    (he : ∀ x, η.e_fn x = η'.e_fn x) : η = η' := by
  cases η
  cases η'
  simp only at hμ he
  congr
  · funext x
    exact hμ x
  · funext x
    exact he x

/-- Treated-nuisance vectors form an additive commutative group under componentwise operations. -/
instance : AddCommGroup (TreatedNuisanceVec γ) where
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
    · intro x; exact sub_eq_add_neg (η.μ₀_fn x) (η'.μ₀_fn x)
    · intro x; exact sub_eq_add_neg (η.e_fn x) (η'.e_fn x)
  add_assoc η η' η'' := by
    apply ext
    · intro x; exact add_assoc (η.μ₀_fn x) (η'.μ₀_fn x) (η''.μ₀_fn x)
    · intro x; exact add_assoc (η.e_fn x) (η'.e_fn x) (η''.e_fn x)
  zero_add η := by
    apply ext
    · intro x; exact zero_add (η.μ₀_fn x)
    · intro x; exact zero_add (η.e_fn x)
  add_zero η := by
    apply ext
    · intro x; exact add_zero (η.μ₀_fn x)
    · intro x; exact add_zero (η.e_fn x)
  neg_add_cancel η := by
    apply ext
    · intro x; exact neg_add_cancel (η.μ₀_fn x)
    · intro x; exact neg_add_cancel (η.e_fn x)
  add_comm η η' := by
    apply ext
    · intro x; exact add_comm (η.μ₀_fn x) (η'.μ₀_fn x)
    · intro x; exact add_comm (η.e_fn x) (η'.e_fn x)

/-- Treated-nuisance vectors form a real vector space under componentwise scalar multiplication. -/
instance : Module ℝ (TreatedNuisanceVec γ) where
  smul := (· • ·)
  one_smul η := by
    apply ext
    · intro x
      change (1 : ℝ) * η.μ₀_fn x = η.μ₀_fn x
      exact one_mul _
    · intro x
      change (1 : ℝ) * η.e_fn x = η.e_fn x
      exact one_mul _
  mul_smul t u η := by
    apply ext
    · intro x
      change (t * u) * η.μ₀_fn x = t * (u * η.μ₀_fn x)
      ring
    · intro x
      change (t * u) * η.e_fn x = t * (u * η.e_fn x)
      ring
  smul_zero t := by
    apply ext
    · intro x
      change t * (0 : ℝ) = 0
      exact mul_zero t
    · intro x
      change t * (0 : ℝ) = 0
      exact mul_zero t
  smul_add t η η' := by
    apply ext
    · intro x
      change t * (η.μ₀_fn x + η'.μ₀_fn x) = t * η.μ₀_fn x + t * η'.μ₀_fn x
      ring
    · intro x
      change t * (η.e_fn x + η'.e_fn x) = t * η.e_fn x + t * η'.e_fn x
      ring
  add_smul t u η := by
    apply ext
    · intro x
      change (t + u) * η.μ₀_fn x = t * η.μ₀_fn x + u * η.μ₀_fn x
      ring
    · intro x
      change (t + u) * η.e_fn x = t * η.e_fn x + u * η.e_fn x
      ring
  zero_smul η := by
    apply ext
    · intro x
      change (0 : ℝ) * η.μ₀_fn x = 0
      exact zero_mul _
    · intro x
      change (0 : ℝ) * η.e_fn x = 0
      exact zero_mul _

end TreatedNuisanceVec

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- The truth `η₀ : TreatedNuisanceVec γ`. -/
noncomputable def η₀ (S : TreatedEstimationSystem P γ) : TreatedNuisanceVec γ :=
  ⟨S.μ₀_val, S.e_val, S.μ₀_meas, S.e_meas⟩

/-- The ATT nuisance class carries one-sided upper overlap `P_X`-a.e., an
`L²(P_X)` outcome-regression component, and an `L∞(P_X)` propensity component.

For ATT only the upper overlap bound matters because the IPW correction divides
by `1 − e(X)`. Nonnegativity of the truth and learners is kept as a separate
hypothesis in the score-continuity theorem, matching the existing ATT setup. -/
def H_ε (S : TreatedEstimationSystem P γ) (ε : ℝ) :
    Set (TreatedNuisanceVec γ) :=
  { η | (∀ᵐ x ∂S.P_X, η.e_fn x ≤ 1 - ε) ∧
      MemLp η.μ₀_fn 2 S.P_X ∧
      MemLp η.e_fn ⊤ S.P_X }

/-- Membership in the ATT `H_ε` transports the one-sided a.e. overlap bound to
the original probability space along the observed covariate. -/
lemma H_ε_overlap_factualX
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    {η : TreatedNuisanceVec γ} (hη : η ∈ H_ε S ε) :
    ∀ᵐ ω ∂P.μ, η.e_fn (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
  have hset : MeasurableSet {x : γ | η.e_fn x ≤ 1 - ε} := by
    exact measurableSet_Iic.preimage η.e_meas
  have hx : ∀ᵐ x ∂S.P_X, η.e_fn x ≤ 1 - ε := hη.1
  unfold TreatedEstimationSystem.P_X at hx
  exact (MeasureTheory.ae_map_iff
    S.toPOBackdoorSystem.measurable_factualX.aemeasurable hset).mp hx

/-- Membership in the ATT `H_ε` transports the one-sided a.e. overlap bound to
the observed-data law along the covariate projection. -/
lemma H_ε_overlap_P_Z
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    {η : TreatedNuisanceVec γ} (hη : η ∈ H_ε S ε) :
    ∀ᵐ z ∂S.P_Z, η.e_fn (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)
      ≤ 1 - ε := by
  open Causalean.Estimation.ATE.BackdoorEstimationSystem in
  have hset : MeasurableSet {x : γ | η.e_fn x ≤ 1 - ε} := by
    exact measurableSet_Iic.preimage η.e_meas
  have hx : ∀ᵐ x ∂S.P_X, η.e_fn x ≤ 1 - ε := hη.1
  rw [← TreatedEstimationSystem.P_Z_map_projX_eq_P_X S] at hx
  have hproj : Measurable (fun z : γ × Bool × ℝ => projX z) := by
    simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
  exact (MeasureTheory.ae_map_iff hproj.aemeasurable hset).mp hx

/-- The ATT AIPW moment as a moment functional `TreatedNuisanceVec γ → X → ℝ → ℝ`,
suitable for feeding `NeymanOrthogonal`. -/
noncomputable def aipwMomentATTFunctional :
    TreatedNuisanceVec γ → (γ × Bool × ℝ) → ℝ → ℝ :=
  fun η z θ => aipwMomentATT z η.μ₀_fn η.e_fn θ

/-- Measurability of the ATT AIPW moment functional in the data variable `z`. -/
lemma measurable_aipwMomentATTFunctional
    (η : TreatedNuisanceVec γ) (θ : ℝ) :
    Measurable (fun z => aipwMomentATTFunctional η z θ) := by
  unfold aipwMomentATTFunctional aipwMomentATT
  have hX : Measurable (projX : γ × Bool × ℝ → γ) := by
    unfold projX; fun_prop
  have hA : Measurable (projA : γ × Bool × ℝ → Bool) := by
    unfold projA; fun_prop
  have hY : Measurable (projY : γ × Bool × ℝ → ℝ) := by
    unfold projY; fun_prop
  have hindA : Measurable (indA : γ × Bool × ℝ → ℝ) := by
    unfold indA
    refine Measurable.ite ?_ measurable_const measurable_const
    exact hA (MeasurableSet.singleton true)
  have hμ₀X : Measurable (fun z : γ × Bool × ℝ => η.μ₀_fn (projX z)) :=
    η.μ₀_meas.comp hX
  have heX : Measurable (fun z : γ × Bool × ℝ => η.e_fn (projX z)) :=
    η.e_meas.comp hX
  refine Measurable.sub ?_ (hindA.mul measurable_const)
  refine Measurable.sub ?_ ?_
  · exact hindA.mul (hY.sub hμ₀X)
  · refine Measurable.mul (Measurable.mul ?_ ?_) (hY.sub hμ₀X)
    · exact (measurable_const.sub hindA)
    · exact heX.div (measurable_const.sub heX)

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
