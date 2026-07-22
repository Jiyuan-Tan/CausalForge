/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bochner integral against a `Measure.bind`

Mathlib provides `MeasureTheory.Measure.lintegral_bind` for the lower Lebesgue
integral, but no analogue for the Bochner integral.  This file supplies the
missing bridge: integrating a Bochner-integrable function against the Giry-monad
bind `m.bind κ` equals the iterated integral `∫ a, ∫ x, f x ∂κ a ∂m`.

This is a purely measure-theoretic statement over generic types and a generic
normed space, with the standard measurability and integrability side-conditions.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Invariance

/-! # Bochner Integrals Against Measure Binds

This file proves Bochner-integral identities for Giry-monad binds and for binds whose
fibres are pushforwards. These identities convert an integral against a bound measure
into the corresponding iterated integral, supporting nested-kernel calculations in the
causal and statistical parts of the library.

The main public results are `integral_bind`, `integral_bind_map`,
`integral_bind_bind_map`, `integral_bind_of_ae_eq_const`, `map_bind_bind_map_proj`, and
`integral_bind_bind_map_proj`. Together they cover one-level binds, bind-then-map
integrals, doubly nested bind-then-map integrals, fibrewise constant collapses, and
projection back to a reattached base coordinate. -/

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.MeasureTheory

/-- Bochner integral against a Giry-monad `bind`.

The Bochner analogue of `MeasureTheory.Measure.lintegral_bind`: for a measurable
kernel `κ` and a function `f` that is Bochner-integrable against `m.bind κ`, the
integral against the bind collapses to the iterated integral. -/
theorem integral_bind {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure α} {κ : α → Measure β} {f : β → E}
    (hκ : Measurable κ)
    (hf : Integrable f (m.bind κ)) :
    ∫ x, f x ∂m.bind κ = ∫ a, ∫ x, f x ∂κ a ∂m := by
  let K : Kernel α β := ⟨κ, hκ⟩
  have hcomp : (K ∘ₘ m) = m.bind κ := by
    rw [Measure.comp_eq_comp_const_apply]
    rfl
  rw [← hcomp]
  simpa [K, Kernel.comp_apply, Measure.comp_eq_comp_const_apply] using
    (ProbabilityTheory.Kernel.integral_comp
      (κ := Kernel.const Unit m) (η := K) (a := ()) (f := f)
      (by simpa [K, Kernel.comp_apply, Measure.comp_eq_comp_const_apply] using hf))

/-- Bochner integral against a Giry-monad `bind` whose kernel is a pushforward.

When each fibre of the kernel is itself a `Measure.map (g a)`, integrating against
`m.bind (fun a => (κ a).map (g a))` collapses to the iterated integral of the
pulled-back integrand `a ↦ ∫ x, f (g a x) ∂κ a`. This packages a single
application of `integral_bind` with the fibrewise `MeasureTheory.integral_map`,
supplying the bridge needed to expand a nested bind-then-map Bochner integral. -/
theorem integral_bind_map {α β γ E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure α} {κ : α → Measure β} {g : α → β → γ} {f : γ → E}
    (hκ : Measurable κ) (hg : ∀ a, Measurable (g a))
    (hgm : Measurable (fun a => (κ a).map (g a)))
    (hf : Integrable f (m.bind (fun a => (κ a).map (g a)))) :
    ∫ z, f z ∂m.bind (fun a => (κ a).map (g a)) = ∫ a, ∫ x, f (g a x) ∂κ a ∂m := by
  have _ : Measurable κ := hκ
  let K : Kernel α γ := ⟨fun a => (κ a).map (g a), hgm⟩
  have hcomp : (K ∘ₘ m) = m.bind fun a => (κ a).map (g a) := by
    rw [Measure.comp_eq_comp_const_apply]
    rfl
  have hfK : Integrable f ((K ∘ₘ m)) := by simpa [hcomp] using hf
  have hfiber_int_ae : ∀ᵐ a ∂m, Integrable f ((κ a).map (g a)) := by
    simpa [K, Kernel.const_apply] using
      (MeasureTheory.Integrable.ae_of_comp
        (κ := Kernel.const Unit m) (η := K) (a := ()) (f := f) hfK)
  have hfiber : (fun a => ∫ z, f z ∂(κ a).map (g a)) =ᶠ[ae m]
      (fun a => ∫ x, f (g a x) ∂κ a) := by
    filter_upwards [hfiber_int_ae] with a ha
    exact integral_map (hg a).aemeasurable ha.aestronglyMeasurable
  calc
    ∫ z, f z ∂m.bind (fun a => (κ a).map (g a))
        = ∫ z, f z ∂(K ∘ₘ m) := by rw [hcomp]
    _ = ∫ a, ∫ z, f z ∂K a ∂m := by
      simpa [K, Kernel.comp_apply, Measure.comp_eq_comp_const_apply] using
        (ProbabilityTheory.Kernel.integral_comp
          (κ := Kernel.const Unit m) (η := K) (a := ()) (f := f) hfK)
    _ = ∫ a, ∫ x, f (g a x) ∂κ a ∂m := integral_congr_ae hfiber

/-- Bochner integral against a doubly-nested Giry-monad `bind` whose innermost
kernel is a pushforward.

The triple-collapse companion to `integral_bind` and `integral_bind_map`: when
the outer kernel of an `m.bind` is itself a `bind` of a `Measure.map (g a b)`,
the Bochner integral collapses to the threefold iterated integral of the
pulled-back integrand `(a, b, c) ↦ f (g a b c)`.  This is the single bridge for
a `bind`-then-`bind`-then-`map` integrand, which neither `integral_bind` nor
`integral_bind_map` covers in one step. -/
theorem integral_bind_bind_map {α β γ δ E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure α} {κ₁ : α → Measure β} {κ₂ : α → β → Measure γ}
    {g : α → β → γ → δ} {f : δ → E}
    (_hκ₁ : Measurable κ₁)
    (hκ₂ : Measurable fun p : α × β => κ₂ p.1 p.2)
    (hg : ∀ a b, Measurable (g a b))
    (hmap : ∀ a, Measurable fun b => (κ₂ a b).map (g a b))
    (hker : Measurable fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b))
    (hf : Integrable f (m.bind fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b)))
    (hf₂ : ∀ᵐ a ∂m, Integrable (fun b => ∫ c, f (g a b c) ∂(κ₂ a b)) (κ₁ a))
    (hf' : Integrable (fun a => ∫ b, ∫ c, f (g a b c) ∂(κ₂ a b) ∂(κ₁ a)) m) :
    ∫ z, f z ∂(m.bind fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b))
      = ∫ a, ∫ b, ∫ c, f (g a b c) ∂(κ₂ a b) ∂(κ₁ a) ∂m := by
  classical
  have _ : Integrable (fun a => ∫ b, ∫ c, f (g a b c) ∂(κ₂ a b) ∂(κ₁ a)) m := hf'
  let K : Kernel α δ := ⟨fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b), hker⟩
  have hcomp : (K ∘ₘ m) = m.bind fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b) := by
    rw [Measure.comp_eq_comp_const_apply]; rfl
  have hfK : Integrable f (K ∘ₘ m) := by simpa [hcomp] using hf
  have hfiber_int_ae : ∀ᵐ a ∂m,
      Integrable f ((κ₁ a).bind fun b => (κ₂ a b).map (g a b)) := by
    simpa [K, Kernel.const_apply] using
      (MeasureTheory.Integrable.ae_of_comp
        (κ := Kernel.const Unit m) (η := K) (a := ()) (f := f) hfK)
  have hcollapse :
      (fun a => ∫ z, f z ∂((κ₁ a).bind fun b => (κ₂ a b).map (g a b)))
        =ᶠ[ae m] (fun a => ∫ b, ∫ c, f (g a b c) ∂(κ₂ a b) ∂(κ₁ a)) := by
    filter_upwards [hfiber_int_ae, hf₂] with a hfa hf₂a
    exact integral_bind_map (hκ₂.comp measurable_prodMk_left) (hg a) (hmap a) hfa
  rw [integral_bind hker hf]
  exact integral_congr_ae hcollapse

/-- Marginal collapse of a Bochner integral against a Giry-monad `bind` of
probability measures.

If each fibre `κ a` is a probability measure and the integrand `f` agrees
`κ a`-almost-everywhere with a constant `f' a` on that fibre, then the integral
against `m.bind κ` collapses to the integral of the fibrewise constant against
the base measure `m`.  This is the bridge for the situation where the integrand
only depends on a coordinate that is constant within each inner kernel, so the
inner integral evaluates to that constant and the `bind` reduces to `∫ a, f' a ∂m`. -/
theorem integral_bind_of_ae_eq_const {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure α} {κ : α → Measure β} {f : β → E} {f' : α → E}
    (hκ : Measurable κ) (hp : ∀ a, IsProbabilityMeasure (κ a))
    (hconst : ∀ a, ∀ᵐ y ∂κ a, f y = f' a)
    (hf : Integrable f (m.bind κ))
    (hf' : Integrable f' m) :
    ∫ y, f y ∂m.bind κ = ∫ a, f' a ∂m := by
  have _ : Integrable f' m := hf'
  rw [integral_bind hκ hf]
  by_cases hE : CompleteSpace E
  · have hfiber : (fun a => ∫ y, f y ∂κ a) =ᶠ[ae m] (fun a => f' a) := by
      exact Filter.Eventually.of_forall fun a => by
        calc
          ∫ y, f y ∂κ a = ∫ y, f' a ∂κ a := integral_congr_ae (hconst a)
          _ = f' a := by
            rw [integral_const, measureReal_def, isProbabilityMeasure_iff.mp (hp a)]
            simp
    exact integral_congr_ae hfiber
  · simp [integral, hE]

/-- Base-coordinate marginal of a doubly-nested `bind`-`bind`-`map`.

If every inner fibre `κ₁ a` and `κ₂ a b` is a probability measure and the
innermost map `g a b` reattaches the base point `a` so that the projection `π`
recovers it (`π (g a b c) = a`), then the `π`-pushforward of the nested
construction is exactly the base measure `m`.  This is the underlying measure
identity behind `integral_bind_bind_map_proj`, stated without any integrability
or integrand hypotheses: the two inner probability fibres each contribute total
mass one over a fixed base point, so transporting back along `π` returns `m`
unchanged (no hypothesis on `m` is needed).  It is the bridge for marginalising
a nested Giry-monad construction onto its reattached coordinate when only
measurability of the eventual integrand is available. -/
theorem map_bind_bind_map_proj {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ]
    {m : Measure α} {κ₁ : α → Measure β} {κ₂ : α → β → Measure γ}
    {g : α → β → γ → δ} {π : δ → α}
    (_hκ₁ : Measurable κ₁) (hp₁ : ∀ a, IsProbabilityMeasure (κ₁ a))
    (_hκ₂ : Measurable fun p : α × β => κ₂ p.1 p.2)
    (hp₂ : ∀ a b, IsProbabilityMeasure (κ₂ a b))
    (hg : ∀ a b, Measurable (g a b))
    (hmap : ∀ a, Measurable fun b => (κ₂ a b).map (g a b))
    (hker : Measurable fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b))
    (hπ : Measurable π) (hπg : ∀ a b c, π (g a b c) = a) :
    (m.bind fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b)).map π = m := by
  have hdπ : Measurable (fun z => Measure.dirac (π z)) := Measure.measurable_dirac.comp hπ
  have key : ∀ a, ((κ₁ a).bind fun b => (κ₂ a b).map (g a b)).map π = Measure.dirac a := by
    intro a
    have hinner : (fun b => ((κ₂ a b).map (g a b)).map π) = fun _ => Measure.dirac a := by
      funext b; rw [Measure.map_map hπ (hg a b)]
      have hc : (π ∘ g a b) = fun _ => a := funext (hπg a b)
      rw [hc, Measure.map_const, (hp₂ a b).measure_univ, one_smul]
    rw [← Measure.bind_dirac_eq_map _ hπ, Measure.bind_bind (hmap a).aemeasurable hdπ.aemeasurable]
    have hstep : (fun b => ((κ₂ a b).map (g a b)).bind fun z => Measure.dirac (π z))
        = fun _ => Measure.dirac a := by
      funext b; rw [Measure.bind_dirac_eq_map _ hπ]; exact congrFun hinner b
    rw [hstep, Measure.bind_const, (hp₁ a).measure_univ, one_smul]
  rw [← Measure.bind_dirac_eq_map _ hπ, Measure.bind_bind hker.aemeasurable hdπ.aemeasurable]
  have hstep2 : (fun a => ((κ₁ a).bind fun b => (κ₂ a b).map (g a b)).bind
        fun z => Measure.dirac (π z)) = fun a => Measure.dirac a := by
    funext a; rw [Measure.bind_dirac_eq_map _ hπ]; exact key a
  rw [hstep2, Measure.bind_dirac]

/-- Marginal collapse of a Bochner integral against a doubly-nested bind-then-map
onto the reattached base coordinate.

If every fibre `κ₁ a` and `κ₂ a b` is a probability measure and the innermost
map `g a b` reattaches the base point `a` so that a projection `π` recovers it
(`π (g a b c) = a`), then integrating a function `f ∘ π` of the reattached
coordinate alone collapses the entire `bind`-`bind`-`map` to `∫ a, f a ∂m`.
This is the one-step bridge for marginalising a nested Giry-monad construction
back onto the coordinate that the innermost pushforward carries through; the
fibrewise probability-mass-one hypotheses are what make the two inner integrals
of the constant `f a` evaluate to `f a` (no assumption on `m` is needed). -/
theorem integral_bind_bind_map_proj {α β γ δ E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure α} {κ₁ : α → Measure β} {κ₂ : α → β → Measure γ}
    {g : α → β → γ → δ} {π : δ → α} {f : α → E}
    (hκ₁ : Measurable κ₁) (hp₁ : ∀ a, IsProbabilityMeasure (κ₁ a))
    (hκ₂ : Measurable fun p : α × β => κ₂ p.1 p.2)
    (hp₂ : ∀ a b, IsProbabilityMeasure (κ₂ a b))
    (hg : ∀ a b, Measurable (g a b))
    (hmap : ∀ a, Measurable fun b => (κ₂ a b).map (g a b))
    (hker : Measurable fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b))
    (hπ : Measurable π) (hπg : ∀ a b c, π (g a b c) = a)
    (hf' : Integrable f m) :
    ∫ z, f (π z) ∂(m.bind fun a => (κ₁ a).bind fun b => (κ₂ a b).map (g a b))
      = ∫ a, f a ∂m := by
  have hmeq := map_bind_bind_map_proj (m := m)
    hκ₁ hp₁ hκ₂ hp₂ hg hmap hker hπ hπg
  conv_rhs => rw [← hmeq]
  exact (integral_map hπ.aemeasurable (hmeq.symm ▸ hf'.aestronglyMeasurable)).symm

end Causalean.Mathlib.MeasureTheory
