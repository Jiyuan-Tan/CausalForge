/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Missing Mathlib-style lemmas about `ProbabilityTheory.condDistrib`

Collects general-purpose conditional-distribution lemmas that are not
specific to this project and should plausibly be upstreamed to Mathlib.
All statements here are independent of `Causalean`'s SCM / SWIG
infrastructure.

## Current contents

* `map_compProd_prodMap_left_eq_compProd_comap` — pushforward identity:
  pushing a `compProd μ κ` forward through `(e × id)` (where `e` is a
  measurable equivalence on the first coordinate) gives
  `(μ.map e).compProd (κ.comap e.symm)`.  General-purpose helper.
* `condDistrib_comp_right_measurableEquiv` — if `e : α ≃ᵐ β` is a
  measurable equivalence, then `condDistrib Y (e ∘ X) μ` evaluated at
  `e x` equals `condDistrib Y X μ` evaluated at `x`, almost surely in
  `x` under `μ.map X`.  Follows from uniqueness of disintegration
  (`condDistrib_ae_eq_of_measure_eq_compProd`).
* `measure_eq_bind_marginal_condDistrib` — classical bind-form
  disintegration of a finite product measure.
* `condDistrib_map_comp` — reparameterization of `condDistrib` through a
  pushforward measure.

## Removed (April 2026)

* `exists_condDistrib_kernel_family` — see the note at the bottom of this
  file.  The statement is provable but does not close the
  `backdoorAdjustment` measurability obligation due to an absolute-
  continuity gap; the intended fix is a `Kernel.condKernel`-based
  restructure of `obsCondDistrib` itself, not a Mathlib lemma.
-/

import Mathlib.Probability.Kernel.CondDistrib

/-! # Conditional-Distribution Transport Lemmas

This file proves general-purpose lemmas for conditional distributions under
measurable equivalences and disintegration through bind form. The statements are
independent of the causal-model infrastructure and serve as Mathlib-adjacent
measure-theoretic support for identification proofs.

The exported results are `map_compProd_prodMap_left_eq_compProd_comap`,
`condDistrib_comp_right_measurableEquiv`,
`measure_eq_bind_marginal_condDistrib`, and `condDistrib_map_comp`. Together
they move regular conditional distributions across measurable equivalences,
package finite-measure disintegration as a bind identity, and compare
conditional distributions before and after pushing the source measure forward. -/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

/-- **Pushforward of `compProd` through a measurable equivalence on the
    first coordinate.**

    If `e : β ≃ᵐ β'` is a measurable equivalence and `κ` is an s-finite
    kernel `β → γ`, then pushing `ν.compProd κ` forward through
    `Prod.map e id` produces `(ν.map e).compProd (κ.comap e.symm _)`.

    Proved by computing both sides on measurable rectangles via
    `Measure.compProd_apply` and the change-of-variables formula
    `lintegral_map`. -/
theorem map_compProd_prodMap_left_eq_compProd_comap
    {β β' γ : Type*} [MeasurableSpace β] [MeasurableSpace β']
    [MeasurableSpace γ]
    (ν : MeasureTheory.Measure β) [MeasureTheory.SFinite ν]
    (e : β ≃ᵐ β')
    (κ : ProbabilityTheory.Kernel β γ)
    [ProbabilityTheory.IsSFiniteKernel κ] :
    MeasureTheory.Measure.map (Prod.map e (id : γ → γ)) (ν.compProd κ)
      = (MeasureTheory.Measure.map e ν).compProd
          (κ.comap e.symm e.symm.measurable) := by
  ext s hs
  rw [MeasureTheory.Measure.map_apply
        (e.measurable.prodMap measurable_id) hs]
  rw [MeasureTheory.Measure.compProd_apply
        (e.measurable.prodMap measurable_id hs)]
  rw [MeasureTheory.Measure.compProd_apply hs]
  rw [MeasureTheory.lintegral_map
        (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs)
        e.measurable]
  apply MeasureTheory.lintegral_congr
  intro b
  rw [ProbabilityTheory.Kernel.comap_apply, e.symm_apply_apply]
  rfl

/-- Push-forward invariance of `condDistrib` under a measurable
    equivalence of the conditioning variable.

    If `e : α ≃ᵐ β` is measurable with measurable inverse, the
    conditional distribution of `Y` given `e ∘ X` agrees (a.e. on the
    source distribution of `X`) with the conditional distribution of
    `Y` given `X`, modulo reparameterization by `e`.

    **Proof.** By uniqueness of disintegration (Mathlib's
    `condDistrib_ae_eq_of_measure_eq_compProd`), the kernel
    `(condDistrib Y X μ).comap e.symm` is `μ.map (e ∘ X)`-a.e. equal
    to `condDistrib Y (e ∘ X) μ`.  The compProd identity needed,
    `μ.map ((e ∘ X), Y) = (μ.map (e ∘ X)).compProd (κ.comap e.symm)`,
    follows from `compProd_map_condDistrib` and
    `map_compProd_prodMap_left_eq_compProd_comap` above.  We then
    transport the resulting `(μ.map (e ∘ X))`-a.e. equality back to
    `μ.map X`-a.e. via `ae_of_ae_map` applied to `e`, evaluating both
    sides at points of the form `e x`. -/
theorem condDistrib_comp_right_measurableEquiv
    {α β Ω γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
    {mγ : MeasurableSpace γ} (μ : MeasureTheory.Measure γ)
    [MeasureTheory.IsFiniteMeasure μ]
    {Y : γ → Ω} {X : γ → α} (e : α ≃ᵐ β)
    (hY : Measurable Y) (hX : Measurable X) :
    ∀ᵐ x ∂(μ.map X),
      ProbabilityTheory.condDistrib Y (e ∘ X) μ (e x)
        = ProbabilityTheory.condDistrib Y X μ x := by
  classical
  set κ : ProbabilityTheory.Kernel α Ω := ProbabilityTheory.condDistrib Y X μ
    with hκ_def
  set κ' : ProbabilityTheory.Kernel β Ω := κ.comap e.symm e.symm.measurable
    with hκ'_def
  -- (1) Pushforward of the joint `(X, Y)` map under `(e × id)`.
  have hpush :
      MeasureTheory.Measure.map (fun a => ((e ∘ X) a, Y a)) μ
        = MeasureTheory.Measure.map (Prod.map e (id : Ω → Ω))
            (MeasureTheory.Measure.map (fun a => (X a, Y a)) μ) := by
    rw [MeasureTheory.Measure.map_map
          (e.measurable.prodMap measurable_id) (hX.prodMk hY)]
    rfl
  -- (2) Compose with `compProd_map_condDistrib` and the pushforward lemma
  -- `map_compProd_prodMap_left_eq_compProd_comap` to express the
  -- `(e ∘ X, Y)`-pushforward as a compProd against `κ'`.
  have hcompProd_eX :
      MeasureTheory.Measure.map (fun a => ((e ∘ X) a, Y a)) μ
        = (MeasureTheory.Measure.map (e ∘ X) μ).compProd κ' := by
    rw [hpush,
        ← ProbabilityTheory.compProd_map_condDistrib (X := X) hY.aemeasurable,
        map_compProd_prodMap_left_eq_compProd_comap
          (MeasureTheory.Measure.map X μ) e κ]
    congr 1
    exact MeasureTheory.Measure.map_map e.measurable hX
  -- (3) Uniqueness of disintegration gives ae-equality of `κ'` with
  -- `condDistrib Y (e ∘ X) μ` under `μ.map (e ∘ X)`.
  have hae :
      (fun b => ProbabilityTheory.condDistrib Y (e ∘ X) μ b)
        =ᵐ[MeasureTheory.Measure.map (e ∘ X) μ] κ' :=
    ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
      (e ∘ X) hY.aemeasurable hcompProd_eX
  -- (4) Transport the ae-equality through `e`.  Since
  -- `μ.map (e ∘ X) = (μ.map X).map e`, an a.e. statement on the former
  -- becomes an a.e. statement on `μ.map X` after precomposing with `e`.
  have hmap : MeasureTheory.Measure.map (e ∘ X) μ
      = MeasureTheory.Measure.map e (MeasureTheory.Measure.map X μ) :=
    (MeasureTheory.Measure.map_map e.measurable hX).symm
  rw [hmap] at hae
  have hae' :
      ∀ᵐ x ∂(MeasureTheory.Measure.map X μ),
        ProbabilityTheory.condDistrib Y (e ∘ X) μ (e x) = κ' (e x) :=
    MeasureTheory.ae_of_ae_map (μ := MeasureTheory.Measure.map X μ)
      (f := e) e.measurable.aemeasurable hae
  -- (5) Finally, `κ' (e x) = κ (e.symm (e x)) = κ x`.
  filter_upwards [hae'] with x hx
  rw [hx, hκ'_def, ProbabilityTheory.Kernel.comap_apply, e.symm_apply_apply]

/-- **Measure-theoretic chain rule / disintegration (Mathlib gap).**

    A finite measure on a product space `β × γ` equals the `bind` of its
    `γ`-marginal against the regular conditional distribution of the
    `β`-coordinate given the `γ`-coordinate.

    This is a classical disintegration identity; upstream Mathlib has
    `ProbabilityTheory.condDistrib` and `Measure.compProd_of_condDistrib`
    fragments but no single-lemma packaging in this `bind`-form.

    Used by the backdoor completeness chain-rule step to decompose
    `(M.fixSet X).obsKernel s` (projected to `ValuesOn (Y ∪ Z)`) into its
    `Z`-marginal bound against its `Y | Z` conditional. -/
theorem measure_eq_bind_marginal_condDistrib
    {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    [StandardBorelSpace β] [Nonempty β]
    (μ : MeasureTheory.Measure (β × γ))
    [MeasureTheory.IsFiniteMeasure μ] :
    μ = (μ.map Prod.snd).bind
          (fun c : γ =>
            (ProbabilityTheory.condDistrib Prod.fst Prod.snd μ c).map
              (fun b : β => (b, c))) := by
  classical
  let κ : ProbabilityTheory.Kernel γ β :=
    ProbabilityTheory.condDistrib Prod.fst Prod.snd μ
  have hcomp :
      MeasureTheory.Measure.map Prod.snd μ ⊗ₘ κ
        = MeasureTheory.Measure.map (fun p : β × γ => (p.2, p.1)) μ := by
    simpa [κ] using
      (ProbabilityTheory.compProd_map_condDistrib
        (μ := μ) (X := Prod.snd) (Y := Prod.fst) (by fun_prop))
  have hswap :
      μ = MeasureTheory.Measure.map Prod.swap
        (MeasureTheory.Measure.map (fun p : β × γ => (p.2, p.1)) μ) := by
    rw [MeasureTheory.Measure.map_map measurable_swap]
    · simp [Function.comp_def]
    · fun_prop
  have hprod_swap :
      ((ProbabilityTheory.Kernel.id ×ₖ κ).map Prod.swap)
        = (κ ×ₖ ProbabilityTheory.Kernel.id) := by
    ext c
    rw [ProbabilityTheory.Kernel.map_apply _ measurable_swap,
      ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.prod_apply,
      MeasureTheory.Measure.prod_swap]
  have hkernel :
      (fun c : γ => MeasureTheory.Measure.map (fun b : β => (b, c)) (κ c))
        =ᵐ[MeasureTheory.Measure.map Prod.snd μ]
          ((κ ×ₖ ProbabilityTheory.Kernel.id)) := by
    filter_upwards with c
    rw [ProbabilityTheory.Kernel.prod_apply]
    exact (MeasureTheory.Measure.prod_dirac (μ := κ c) c).symm
  simpa [κ] using (calc
    μ = MeasureTheory.Measure.map Prod.swap
        (MeasureTheory.Measure.map (fun p : β × γ => (p.2, p.1)) μ) := hswap
    _ = MeasureTheory.Measure.map Prod.swap
        (MeasureTheory.Measure.map Prod.snd μ ⊗ₘ κ) := by
          rw [hcomp]
    _ = (κ ×ₖ ProbabilityTheory.Kernel.id) ∘ₘ
        MeasureTheory.Measure.map Prod.snd μ := by
          rw [MeasureTheory.Measure.compProd_eq_comp_prod]
          rw [MeasureTheory.Measure.map_comp _ _ measurable_swap]
          rw [hprod_swap]
    _ = (fun c : γ =>
          MeasureTheory.Measure.map (fun b : β => (b, c)) (κ c)) ∘ₘ
        MeasureTheory.Measure.map Prod.snd μ := by
          exact MeasureTheory.Measure.bind_congr_right hkernel.symm)

-- **Note (April 2026).**  A previous stub `exists_condDistrib_kernel_family`
-- in this file tried to package "there exists a kernel agreeing a.e. with
-- `condDistrib Y X (κ a)` at each `a`" as a Mathlib-style existence lemma.
-- That statement is provable (via `ProbabilityTheory.Kernel.condKernel`
-- applied to the joint push-forward `κ.map ⟨X, Y⟩`, which disintegrates the
-- same joint and hence agrees a.e. by uniqueness of disintegration), but it
-- does **not** close the `backdoorAdjustment` measurability obligation in
-- `SCM/ID/Adjustment.lean`:
--
--   `condDistrib` makes per-measure Radon–Nikodym choices that are not
--   functorial in the source measure, so `s ↦ condDistrib Y X (κ s) b` is
--   not measurable.  A `Kernel.condKernel`-based replacement *is* jointly
--   measurable, but it only agrees with `condDistrib` a.e. under
--   `(κ a).map X`.  The `backdoorAdjustment` body evaluates the conditional
--   at `fillZrW s_post z` with `z` drawn from `(κ s_orig).map Z`; the
--   push-forward through `fillZrW` concentrates the `X`-slot on a fixed
--   value determined by `s_post`, which is generally **not** absolutely
--   continuous w.r.t. `(κ s_orig).map X` (continuous-X SCMs fail this).  So
--   the a.e.-equality cannot be transported to bridge the two definitions.
--
-- The proper fix (queued: `doc/plan.md` under "Technical debt — condDistrib
-- → Kernel.condKernel migration") is to redefine `obsCondDistrib` as a
-- slice of a `Kernel.condKernel` at the definition layer in
-- `Causal/Model/Kernel.lean`, then update Rule 2's statement and proof to
-- work at the `Kernel.condKernel` level directly.

/-- **Reparameterization of `condDistrib` through a pushforward.**

    For a measurable map `φ` from `Ω` to `Ω'`, the conditional distribution of `g`
    given `f` computed under the pushforward measure `μ.map φ` agrees, almost
    everywhere on the `f`-marginal, with the conditional distribution of the
    pullbacks `g ∘ φ` given `f ∘ φ` computed under `μ`.

    This lets a conditional distribution stated on an image space (e.g. observed
    values, under an observational kernel) be transported to the source space
    (e.g. latent values, under the latent product), where additional structure is
    available.  Proved by uniqueness of disintegration
    (`condDistrib_ae_eq_of_measure_eq_compProd_of_measurable`): the required
    `compProd` identity is `compProd_map_condDistrib` for `g ∘ φ`, `f ∘ φ`,
    transported across `φ` by `Measure.map_map`. -/
theorem condDistrib_map_comp
    {Ω Ω' 𝒳 𝒴 : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace 𝒳]
    [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    {φ : Ω → Ω'} {g : Ω' → 𝒴} {f : Ω' → 𝒳}
    (hφ : Measurable φ) (hg : Measurable g) (hf : Measurable f) :
    ProbabilityTheory.condDistrib g f (μ.map φ)
      =ᵐ[(μ.map φ).map f] ProbabilityTheory.condDistrib (g ∘ φ) (f ∘ φ) μ := by
  haveI : MeasureTheory.IsFiniteMeasure (μ.map φ) := μ.isFiniteMeasure_map φ
  refine ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hf hg ?_
  have h1 : (μ.map φ).map (fun x => (f x, g x))
      = μ.map (fun ω => ((f ∘ φ) ω, (g ∘ φ) ω)) := by
    rw [MeasureTheory.Measure.map_map (hf.prodMk hg) hφ]; rfl
  have h2 : (μ.map φ).map f = μ.map (f ∘ φ) :=
    MeasureTheory.Measure.map_map hf hφ
  rw [h1, h2]
  exact (ProbabilityTheory.compProd_map_condDistrib (hg.comp hφ).aemeasurable).symm

end Causalean
