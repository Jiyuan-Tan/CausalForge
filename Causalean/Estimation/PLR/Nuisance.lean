/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bundled nuisance space for the partially linear model

* `PLRNuisance γ`  — pair `(lFn, mFn)` of measurable real-valued covariate
                     functions (outcome regression and treatment regression),
                     equipped with componentwise `AddCommGroup` and `Module ℝ`
                     instances so it can serve as the nuisance space `H` of the
                     DML `GeneralMoment` framework, which requires
                     `[AddCommGroup H] [Module ℝ H]`.

Direct (but simpler) mirror of `NuisanceVec` in
`Causalean/Estimation/ATE/AIPWMoment.lean`: two real-valued function fields
instead of a `Bool`-indexed regression and a propensity score.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Bundled nuisance space for the partially linear model

This file packages the two partially-linear-model nuisance functions — the
outcome regression `lFn` and the treatment regression `mFn` — together with
their measurability witnesses into a single type `PLRNuisance`, and equips it
with componentwise real-vector-space structure. This bundled nuisance space is
the nuisance space used by the partially linear double-machine-learning moment
instance. -/

namespace Causalean
namespace Estimation
namespace PLR

/-- A partially linear nuisance bundles the outcome regression and treatment
regression as measurable functions of the covariates.

This type is used as the abstract nuisance space for the partially linear
double-machine-learning moment functional. -/
structure PLRNuisance (γ : Type*) [MeasurableSpace γ] where
  lFn : γ → ℝ
  mFn : γ → ℝ
  lMeas : Measurable lFn
  mMeas : Measurable mFn

namespace PLRNuisance

variable {γ : Type*} [MeasurableSpace γ]

/-- The zero nuisance pair: both the outcome regression and the treatment
regression are the constant function zero. -/
instance : Zero (PLRNuisance γ) where
  zero := ⟨fun _ => 0, fun _ => 0, measurable_const, measurable_const⟩

/-- Addition of two nuisance pairs, performed separately on the outcome
regression and on the treatment regression. -/
instance : Add (PLRNuisance γ) where
  add η η' :=
    ⟨fun x => η.lFn x + η'.lFn x,
     fun x => η.mFn x + η'.mFn x,
     η.lMeas.add η'.lMeas,
     η.mMeas.add η'.mMeas⟩

/-- Negation of a nuisance pair, negating both the outcome regression and the
treatment regression. -/
instance : Neg (PLRNuisance γ) where
  neg η :=
    ⟨fun x => -η.lFn x, fun x => -η.mFn x,
     η.lMeas.neg, η.mMeas.neg⟩

/-- Subtraction of two nuisance pairs, performed separately on the outcome
regression and on the treatment regression. -/
instance : Sub (PLRNuisance γ) where
  sub η η' :=
    ⟨fun x => η.lFn x - η'.lFn x,
     fun x => η.mFn x - η'.mFn x,
     η.lMeas.sub η'.lMeas,
     η.mMeas.sub η'.mMeas⟩

/-- Scaling a nuisance pair by a real number, multiplying both the outcome
regression and the treatment regression pointwise by that scalar. -/
instance : SMul ℝ (PLRNuisance γ) where
  smul t η :=
    ⟨fun x => t * η.lFn x, fun x => t * η.mFn x,
     measurable_const.mul η.lMeas,
     measurable_const.mul η.mMeas⟩

/-- Two nuisance pairs are equal whenever their outcome regressions agree at
every covariate value and their treatment regressions agree at every covariate
value. -/
@[ext]
theorem ext {η η' : PLRNuisance γ}
    (hl : ∀ x, η.lFn x = η'.lFn x)
    (hm : ∀ x, η.mFn x = η'.mFn x) : η = η' := by
  cases η
  cases η'
  simp only at hl hm
  congr
  · funext x
    exact hl x
  · funext x
    exact hm x

/-- The nuisance pairs form an additive commutative group under componentwise
operations, inheriting all the group laws from the reals applied at each
covariate value. -/
instance : AddCommGroup (PLRNuisance γ) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  nsmul := nsmulRec
  zsmul := zsmulRec
  nsmul_zero η := by
    rfl
  nsmul_succ n η := by
    rfl
  zsmul_zero' η := by
    rfl
  zsmul_succ' n η := by
    rfl
  zsmul_neg' n η := by
    rfl
  sub_eq_add_neg η η' := by
    apply ext <;> intro x
    · exact sub_eq_add_neg (η.lFn x) (η'.lFn x)
    · exact sub_eq_add_neg (η.mFn x) (η'.mFn x)
  add_assoc η η' η'' := by
    apply ext <;> intro x
    · exact add_assoc (η.lFn x) (η'.lFn x) (η''.lFn x)
    · exact add_assoc (η.mFn x) (η'.mFn x) (η''.mFn x)
  zero_add η := by
    apply ext <;> intro x
    · exact zero_add (η.lFn x)
    · exact zero_add (η.mFn x)
  add_zero η := by
    apply ext <;> intro x
    · exact add_zero (η.lFn x)
    · exact add_zero (η.mFn x)
  neg_add_cancel η := by
    apply ext <;> intro x
    · exact neg_add_cancel (η.lFn x)
    · exact neg_add_cancel (η.mFn x)
  add_comm η η' := by
    apply ext <;> intro x
    · exact add_comm (η.lFn x) (η'.lFn x)
    · exact add_comm (η.mFn x) (η'.mFn x)

/-- The nuisance pairs form a real vector space, with scalar multiplication
acting pointwise on both the outcome regression and the treatment regression. -/
instance : Module ℝ (PLRNuisance γ) where
  smul := (· • ·)
  one_smul η := by
    apply ext <;> intro x
    · change (1 : ℝ) * η.lFn x = η.lFn x
      exact one_mul _
    · change (1 : ℝ) * η.mFn x = η.mFn x
      exact one_mul _
  mul_smul t u η := by
    apply ext <;> intro x
    · change (t * u) * η.lFn x = t * (u * η.lFn x)
      ring
    · change (t * u) * η.mFn x = t * (u * η.mFn x)
      ring
  smul_zero t := by
    apply ext <;> intro x
    · change t * (0 : ℝ) = 0
      exact mul_zero t
    · change t * (0 : ℝ) = 0
      exact mul_zero t
  smul_add t η η' := by
    apply ext <;> intro x
    · change t * (η.lFn x + η'.lFn x) = t * η.lFn x + t * η'.lFn x
      ring
    · change t * (η.mFn x + η'.mFn x) = t * η.mFn x + t * η'.mFn x
      ring
  add_smul t u η := by
    apply ext <;> intro x
    · change (t + u) * η.lFn x = t * η.lFn x + u * η.lFn x
      ring
    · change (t + u) * η.mFn x = t * η.mFn x + u * η.mFn x
      ring
  zero_smul η := by
    apply ext <;> intro x
    · change (0 : ℝ) * η.lFn x = 0
      exact zero_mul _
    · change (0 : ℝ) * η.mFn x = 0
      exact zero_mul _

end PLRNuisance

end PLR
end Estimation
end Causalean
