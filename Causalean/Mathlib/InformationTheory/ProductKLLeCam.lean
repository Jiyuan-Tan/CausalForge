/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Product-KL tensorisation for Le Cam arguments

Mathlib currently exposes `InformationTheory.klDiv`, but the finite-product
tensorisation theorem needed by the Le Cam bridge is not part of the imported
API. This file proves the finite-product identity on the finite-KL branch and
packages it as the bounded interface used downstream.
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Product KL Bounds for Le Cam Arguments

This file proves and packages tensorisation tools for Kullback--Leibler divergence over
finite product laws.  The central proposition `ProductKLTensorizationBound` records the
finite product KL, the finite one-observation KL, and the real-valued inequality
`KL(μ^n, ν^n) ≤ n * KL(μ,ν)` so downstream Le Cam arguments cannot accidentally hide an
infinite KL term behind `ENNReal.toReal`.

The main public results are:
* `productKL_tensorization_of_finite`, the finite-branch equality for finite products;
* `productKL_tensorization`, the packaged `ProductKLTensorizationBound`;
* `productKL_tensorization_iid`, the i.i.d. specialization from one-sample absolute
  continuity and log-likelihood-ratio integrability;
* `pi_iid_absolutelyContinuous` and `pi_iid_llr_integrable`, reusable finite-product
  side conditions.

It is a Mathlib-adjacent information-theory layer rather than a causal model
construction. -/

namespace Causalean.Mathlib.InformationTheory

open MeasureTheory
open scoped ENNReal

namespace ProductKLPrivate

open _root_.InformationTheory

private lemma klDiv_toReal_map_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    (klDiv (Measure.map e μ) (Measure.map e ν)).toReal = (klDiv μ ν).toReal := by
  rw [toReal_klDiv_eq_integral_klFun (hμν.map e.measurable),
    toReal_klDiv_eq_integral_klFun hμν]
  rw [e.measurableEmbedding.integral_map]
  exact integral_congr_ae <|
    (e.measurableEmbedding.rnDeriv_map μ ν).mono fun x hx => by
      simp [hx]

private lemma rnDeriv_prod_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [SigmaFinite μ₁] [SigmaFinite ν₁] [SigmaFinite μ₂] [SigmaFinite ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) :
    (fun z : α × β => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2)
      =ᵐ[ν₁.prod ν₂] (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) := by
  refine Measure.eq_rnDeriv₀ (ν := ν₁.prod ν₂) (μ := μ₁.prod μ₂) ?_
    Measure.MutuallySingular.zero_left ?_
  · fun_prop
  · rw [zero_add]
    calc
      μ₁.prod μ₂
          = (ν₁.withDensity (μ₁.rnDeriv ν₁)).prod
              (ν₂.withDensity (μ₂.rnDeriv ν₂)) := by
              rw [Measure.withDensity_rnDeriv_eq _ _ h₁,
                Measure.withDensity_rnDeriv_eq _ _ h₂]
      _ = (ν₁.prod ν₂).withDensity
            (fun z : α × β => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2) := by
              exact prod_withDensity₀
                (Measure.measurable_rnDeriv μ₁ ν₁).aemeasurable
                (Measure.measurable_rnDeriv μ₂ ν₂).aemeasurable

private lemma ae_prod_fst_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν] {p : α → Prop}
    (hp_meas : MeasurableSet {x | p x}) (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ z ∂μ.prod ν, p z.1 := by
  have hmap : ∀ᵐ x ∂Measure.map Prod.fst (μ.prod ν), p x := by
    simpa [MeasurePreserving.map_eq (measurePreserving_fst (μ := μ) (ν := ν))] using hp
  exact (ae_map_iff (measurePreserving_fst (μ := μ) (ν := ν)).aemeasurable hp_meas).mp hmap

private lemma ae_prod_snd_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [SFinite ν] {p : β → Prop}
    (hp_meas : MeasurableSet {y | p y}) (hp : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ z ∂μ.prod ν, p z.2 := by
  have hmap : ∀ᵐ y ∂Measure.map Prod.snd (μ.prod ν), p y := by
    simpa [MeasurePreserving.map_eq (measurePreserving_snd (μ := μ) (ν := ν))] using hp
  exact (ae_map_iff (measurePreserving_snd (μ := μ) (ν := ν)).aemeasurable hp_meas).mp hmap

private lemma llr_prod_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) :
    llr (μ₁.prod μ₂) (ν₁.prod ν₂)
      =ᵐ[μ₁.prod μ₂] fun z : α × β => llr μ₁ ν₁ z.1 + llr μ₂ ν₂ z.2 := by
  have hprod : μ₁.prod μ₂ ≪ ν₁.prod ν₂ := h₁.prod h₂
  have hrn := hprod.ae_eq (rnDeriv_prod_ae μ₁ ν₁ μ₂ ν₂ h₁ h₂)
  have hpos₁ : ∀ᵐ x ∂μ₁, 0 < μ₁.rnDeriv ν₁ x := Measure.rnDeriv_pos h₁
  have hpos₂ : ∀ᵐ y ∂μ₂, 0 < μ₂.rnDeriv ν₂ y := Measure.rnDeriv_pos h₂
  have hfin₁ : ∀ᵐ x ∂μ₁, μ₁.rnDeriv ν₁ x ≠ ∞ :=
    Filter.Eventually.filter_mono h₁.ae_le (Measure.rnDeriv_ne_top μ₁ ν₁)
  have hfin₂ : ∀ᵐ y ∂μ₂, μ₂.rnDeriv ν₂ y ≠ ∞ :=
    Filter.Eventually.filter_mono h₂.ae_le (Measure.rnDeriv_ne_top μ₂ ν₂)
  have hpos₁p : ∀ᵐ z ∂μ₁.prod μ₂, 0 < μ₁.rnDeriv ν₁ z.1 :=
    ae_prod_fst_of_ae
      (measurableSet_lt measurable_const (Measure.measurable_rnDeriv μ₁ ν₁)) hpos₁
  have hpos₂p : ∀ᵐ z ∂μ₁.prod μ₂, 0 < μ₂.rnDeriv ν₂ z.2 :=
    ae_prod_snd_of_ae
      (measurableSet_lt measurable_const (Measure.measurable_rnDeriv μ₂ ν₂)) hpos₂
  have hfin₁p : ∀ᵐ z ∂μ₁.prod μ₂, μ₁.rnDeriv ν₁ z.1 ≠ ∞ :=
    ae_prod_fst_of_ae (p := fun x => μ₁.rnDeriv ν₁ x ≠ ∞)
      (by
        change MeasurableSet ((fun x => μ₁.rnDeriv ν₁ x) ⁻¹' ({∞} : Set ℝ≥0∞))ᶜ
        exact (Measure.measurable_rnDeriv μ₁ ν₁ (MeasurableSet.singleton (∞ : ℝ≥0∞))).compl)
      hfin₁
  have hfin₂p : ∀ᵐ z ∂μ₁.prod μ₂, μ₂.rnDeriv ν₂ z.2 ≠ ∞ :=
    ae_prod_snd_of_ae (p := fun y => μ₂.rnDeriv ν₂ y ≠ ∞)
      (by
        change MeasurableSet ((fun y => μ₂.rnDeriv ν₂ y) ⁻¹' ({∞} : Set ℝ≥0∞))ᶜ
        exact (Measure.measurable_rnDeriv μ₂ ν₂ (MeasurableSet.singleton (∞ : ℝ≥0∞))).compl)
      hfin₂
  filter_upwards [hrn, hpos₁p, hpos₂p, hfin₁p, hfin₂p] with z hz hposz₁ hposz₂ hfinz₁ hfinz₂
  rw [llr_def, llr_def, llr_def]
  change Real.log (((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) z).toReal) =
    Real.log (μ₁.rnDeriv ν₁ z.1).toReal + Real.log (μ₂.rnDeriv ν₂ z.2).toReal
  rw [← hz]
  rw [ENNReal.toReal_mul, Real.log_mul]
  · exact (ENNReal.toReal_pos hposz₁.ne' hfinz₁).ne'
  · exact (ENNReal.toReal_pos hposz₂.ne' hfinz₂).ne'

private lemma llr_prod_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂)
    (hint₁ : Integrable (llr μ₁ ν₁) μ₁)
    (hint₂ : Integrable (llr μ₂ ν₂) μ₂) :
    Integrable (llr (μ₁.prod μ₂) (ν₁.prod ν₂)) (μ₁.prod μ₂) := by
  have hllr := llr_prod_ae μ₁ ν₁ μ₂ ν₂ h₁ h₂
  have hcomp₁ : Integrable (fun z : α × β => llr μ₁ ν₁ z.1) (μ₁.prod μ₂) := by
    simpa [Function.comp_def] using
      ((measurePreserving_fst (μ := μ₁) (ν := μ₂)).integrable_comp
        (stronglyMeasurable_llr μ₁ ν₁).aestronglyMeasurable).2 hint₁
  have hcomp₂ : Integrable (fun z : α × β => llr μ₂ ν₂ z.2) (μ₁.prod μ₂) := by
    simpa [Function.comp_def] using
      ((measurePreserving_snd (μ := μ₁) (ν := μ₂)).integrable_comp
        (stronglyMeasurable_llr μ₂ ν₂).aestronglyMeasurable).2 hint₂
  exact (integrable_congr hllr).2 (hcomp₁.add hcomp₂)

private lemma llr_integrable_of_map_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (hint : Integrable (llr (Measure.map e μ) (Measure.map e ν)) (Measure.map e μ)) :
    Integrable (llr μ ν) μ := by
  have hcomp :
      Integrable (fun x : α => llr (Measure.map e μ) (Measure.map e ν) (e x)) μ :=
    (integrable_map_equiv e (llr (Measure.map e μ) (Measure.map e ν))).1 hint
  have hllr :
      (fun x : α => llr (Measure.map e μ) (Measure.map e ν) (e x))
        =ᵐ[μ] llr μ ν := by
    have hrn := hμν.ae_eq (e.measurableEmbedding.rnDeriv_map μ ν)
    filter_upwards [hrn] with x hx
    rw [llr_def, llr_def]
    simp [hx]
  exact (integrable_congr hllr).1 hcomp

private lemma pi_absolutelyContinuous_iid {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    ∀ k : ℕ, Measure.pi (fun _ : Fin k => μ) ≪ Measure.pi (fun _ : Fin k => ν) := by
  intro k
  induction k with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ k ih =>
      let e : ((i : Fin (k + 1)) → α) ≃ᵐ α × ((j : Fin k) → α) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) 0
      have hmapμ :
          Measure.map e (Measure.pi (fun _ : Fin (k + 1) => μ))
            = μ.prod (Measure.pi (fun _ : Fin k => μ)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (k + 1) => μ) (0 : Fin (k + 1))).map_eq
      have hmapν :
          Measure.map e (Measure.pi (fun _ : Fin (k + 1) => ν))
            = ν.prod (Measure.pi (fun _ : Fin k => ν)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (k + 1) => ν) (0 : Fin (k + 1))).map_eq
      have hmapac :
          Measure.map e (Measure.pi (fun _ : Fin (k + 1) => μ))
            ≪ Measure.map e (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        rw [hmapμ, hmapν]
        exact hμν.prod ih
      have hback := hmapac.map e.symm.measurable
      simpa [Measure.map_map, Function.comp_def] using hback

private lemma pi_llr_integrable_iid {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hint : Integrable (llr μ ν) μ) :
    ∀ k : ℕ,
      Integrable
        (llr (Measure.pi (fun _ : Fin k => μ)) (Measure.pi (fun _ : Fin k => ν)))
        (Measure.pi (fun _ : Fin k => μ)) := by
  intro k
  induction k with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      exact integrable_dirac' (stronglyMeasurable_llr _ _) (by simp)
  | succ k ih =>
      let e : ((i : Fin (k + 1)) → α) ≃ᵐ α × ((j : Fin k) → α) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) 0
      have hmapμ :
          Measure.map e (Measure.pi (fun _ : Fin (k + 1) => μ))
            = μ.prod (Measure.pi (fun _ : Fin k => μ)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (k + 1) => μ) (0 : Fin (k + 1))).map_eq
      have hmapν :
          Measure.map e (Measure.pi (fun _ : Fin (k + 1) => ν))
            = ν.prod (Measure.pi (fun _ : Fin k => ν)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (k + 1) => ν) (0 : Fin (k + 1))).map_eq
      have hπac := pi_absolutelyContinuous_iid μ ν hμν k
      have hprod_int :
          Integrable
            (llr
              ((Measure.map e (Measure.pi (fun _ : Fin (k + 1) => μ))))
              ((Measure.map e (Measure.pi (fun _ : Fin (k + 1) => ν)))))
            (Measure.map e (Measure.pi (fun _ : Fin (k + 1) => μ))) := by
        rw [hmapμ, hmapν]
        exact llr_prod_integrable μ ν
          (Measure.pi (fun _ : Fin k => μ))
          (Measure.pi (fun _ : Fin k => ν))
          hμν hπac hint ih
      exact llr_integrable_of_map_measurableEquiv e
        (Measure.pi (fun _ : Fin (k + 1) => μ))
        (Measure.pi (fun _ : Fin (k + 1) => ν))
        (pi_absolutelyContinuous_iid μ ν hμν (k + 1)) hprod_int

private lemma klDiv_prod_toReal_add {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂)
    (_h₁' : ν₁ ≪ μ₁) (_h₂' : ν₂ ≪ μ₂)
    (hint₁ : Integrable (llr μ₁ ν₁) μ₁)
    (hint₂ : Integrable (llr μ₂ ν₂) μ₂) :
    (klDiv (μ₁.prod μ₂) (ν₁.prod ν₂)).toReal =
      (klDiv μ₁ ν₁).toReal + (klDiv μ₂ ν₂).toReal := by
  have hllr := llr_prod_ae μ₁ ν₁ μ₂ ν₂ h₁ h₂
  have hcomp₁ : Integrable (fun z : α × β => llr μ₁ ν₁ z.1) (μ₁.prod μ₂) := by
    simpa [Function.comp_def] using
      ((measurePreserving_fst (μ := μ₁) (ν := μ₂)).integrable_comp
        (stronglyMeasurable_llr μ₁ ν₁).aestronglyMeasurable).2 hint₁
  have hcomp₂ : Integrable (fun z : α × β => llr μ₂ ν₂ z.2) (μ₁.prod μ₂) := by
    simpa [Function.comp_def] using
      ((measurePreserving_snd (μ := μ₁) (ν := μ₂)).integrable_comp
        (stronglyMeasurable_llr μ₂ ν₂).aestronglyMeasurable).2 hint₂
  have hprod_int : Integrable (llr (μ₁.prod μ₂) (ν₁.prod ν₂)) (μ₁.prod μ₂) := by
    exact (integrable_congr hllr).2 (hcomp₁.add hcomp₂)
  rw [toReal_klDiv_of_measure_eq (h₁.prod h₂), toReal_klDiv_of_measure_eq h₁,
    toReal_klDiv_of_measure_eq h₂]
  · rw [integral_congr_ae hllr]
    rw [integral_add hcomp₁ hcomp₂]
    have hfst :
        ∫ z : α × β, llr μ₁ ν₁ z.1 ∂μ₁.prod μ₂ = ∫ x, llr μ₁ ν₁ x ∂μ₁ := by
      have hmap := integral_map
        (μ := μ₁.prod μ₂) (φ := Prod.fst) (f := llr μ₁ ν₁)
        (measurePreserving_fst (μ := μ₁) (ν := μ₂)).aemeasurable
        (stronglyMeasurable_llr μ₁ ν₁).aestronglyMeasurable
      rw [(measurePreserving_fst (μ := μ₁) (ν := μ₂)).map_eq] at hmap
      exact hmap.symm
    have hsnd :
        ∫ z : α × β, llr μ₂ ν₂ z.2 ∂μ₁.prod μ₂ = ∫ y, llr μ₂ ν₂ y ∂μ₂ := by
      have hmap := integral_map
        (μ := μ₁.prod μ₂) (φ := Prod.snd) (f := llr μ₂ ν₂)
        (measurePreserving_snd (μ := μ₁) (ν := μ₂)).aemeasurable
        (stronglyMeasurable_llr μ₂ ν₂).aestronglyMeasurable
      rw [(measurePreserving_snd (μ := μ₁) (ν := μ₂)).map_eq] at hmap
      exact hmap.symm
    rw [hfst, hsnd]
  · simp
  · simp
  · simp

private lemma productKL_tensorization_toReal_eq {α : Type*} [MeasurableSpace α]
    (n : ℕ) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hac' : ν ≪ μ) (hint : Integrable (llr μ ν) μ)
    (hπac : ∀ k : ℕ,
      Measure.pi (fun _ : Fin k => μ) ≪ Measure.pi (fun _ : Fin k => ν))
    (hπac' : ∀ k : ℕ,
      Measure.pi (fun _ : Fin k => ν) ≪ Measure.pi (fun _ : Fin k => μ))
    (hπint : ∀ k : ℕ,
      Integrable
        (llr (Measure.pi (fun _ : Fin k => μ)) (Measure.pi (fun _ : Fin k => ν)))
        (Measure.pi (fun _ : Fin k => μ))) :
    (_root_.InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν))).toReal
      = (n : ℝ) * (_root_.InformationTheory.klDiv μ ν).toReal := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp
  | succ n ih =>
      let e : ((i : Fin (n + 1)) → α) ≃ᵐ α × ((j : Fin n) → α) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      have hmapμ :
          Measure.map e (Measure.pi (fun _ : Fin (n + 1) => μ))
            = μ.prod (Measure.pi (fun _ : Fin n => μ)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).map_eq
      have hmapν :
          Measure.map e (Measure.pi (fun _ : Fin (n + 1) => ν))
            = ν.prod (Measure.pi (fun _ : Fin n => ν)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (n + 1) => ν) (0 : Fin (n + 1))).map_eq
      have hrelab :=
        klDiv_toReal_map_measurableEquiv e
          (Measure.pi (fun _ : Fin (n + 1) => μ))
          (Measure.pi (fun _ : Fin (n + 1) => ν)) (hπac (n + 1))
      rw [Nat.cast_add_one]
      change
        (_root_.InformationTheory.klDiv
            (Measure.pi (fun _ : Fin (n + 1) => μ))
            (Measure.pi (fun _ : Fin (n + 1) => ν))).toReal
          = ((n : ℝ) + 1) * (_root_.InformationTheory.klDiv μ ν).toReal
      calc
        (_root_.InformationTheory.klDiv
            (Measure.pi (fun _ : Fin (n + 1) => μ))
            (Measure.pi (fun _ : Fin (n + 1) => ν))).toReal
            = (_root_.InformationTheory.klDiv
                (Measure.map e (Measure.pi (fun _ : Fin (n + 1) => μ)))
                (Measure.map e (Measure.pi (fun _ : Fin (n + 1) => ν)))).toReal := hrelab.symm
        _ = (_root_.InformationTheory.klDiv
                (μ.prod (Measure.pi (fun _ : Fin n => μ)))
                (ν.prod (Measure.pi (fun _ : Fin n => ν)))).toReal := by
              rw [hmapμ, hmapν]
        _ = (_root_.InformationTheory.klDiv μ ν).toReal
              + (_root_.InformationTheory.klDiv
                  (Measure.pi (fun _ : Fin n => μ))
                  (Measure.pi (fun _ : Fin n => ν))).toReal := by
              exact klDiv_prod_toReal_add μ ν
                (Measure.pi (fun _ : Fin n => μ))
                (Measure.pi (fun _ : Fin n => ν))
                hac (hπac n) hac' (hπac' n) hint (hπint n)
        _ = ((n : ℝ) + 1) * (_root_.InformationTheory.klDiv μ ν).toReal := by
              rw [ih]
              ring

end ProductKLPrivate

/-- Product-KL tensorisation bound for an `n`-fold i.i.d. product pair.

The product and one-observation KL divergences are both finite, and after this
finite-KL guard the real-valued product KL is at most `n` times the real-valued
one-observation KL. The finiteness conjuncts prevent the Le Cam interface from
silently turning an infinite KL divergence into zero via `ENNReal.toReal`. -/
def ProductKLTensorizationBound {α : Type*} [MeasurableSpace α]
    (n : ℕ) (μ ν : Measure α) : Prop :=
  _root_.InformationTheory.klDiv
      (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) ≠ ∞ ∧
    _root_.InformationTheory.klDiv μ ν ≠ ∞ ∧
    (_root_.InformationTheory.klDiv
          (Measure.pi (fun _ : Fin n => μ))
          (Measure.pi (fun _ : Fin n => ν))).toReal
      ≤ (n : ℝ) * (_root_.InformationTheory.klDiv μ ν).toReal

/-- Finite-branch product-KL tensorisation for i.i.d. finite products.

The one-sample laws are mutually absolutely continuous and have integrable
log-likelihood ratio.  The same finite-branch facts are assumed for each
finite product prefix; these are the hypotheses needed to avoid the
`klDiv = ∞` / `ENNReal.toReal ∞ = 0` branch. -/
theorem productKL_tensorization_of_finite {α : Type*} [MeasurableSpace α]
    (n : ℕ) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hac' : ν ≪ μ) (hint : Integrable (llr μ ν) μ)
    (hπac : ∀ k : ℕ,
      Measure.pi (fun _ : Fin k => μ) ≪ Measure.pi (fun _ : Fin k => ν))
    (hπac' : ∀ k : ℕ,
      Measure.pi (fun _ : Fin k => ν) ≪ Measure.pi (fun _ : Fin k => μ))
    (hπint : ∀ k : ℕ,
      Integrable
        (llr (Measure.pi (fun _ : Fin k => μ)) (Measure.pi (fun _ : Fin k => ν)))
        (Measure.pi (fun _ : Fin k => μ))) :
    (_root_.InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν))).toReal
      = (n : ℝ) * (_root_.InformationTheory.klDiv μ ν).toReal :=
  ProductKLPrivate.productKL_tensorization_toReal_eq
    n μ ν hac hac' hint hπac hπac' hπint

/-- Product-KL tensorisation packaged in the existing Le Cam interface. -/
theorem productKL_tensorization {α : Type*} [MeasurableSpace α]
    (n : ℕ) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hac' : ν ≪ μ) (hint : Integrable (llr μ ν) μ)
    (hπac : ∀ k : ℕ,
      Measure.pi (fun _ : Fin k => μ) ≪ Measure.pi (fun _ : Fin k => ν))
    (hπac' : ∀ k : ℕ,
      Measure.pi (fun _ : Fin k => ν) ≪ Measure.pi (fun _ : Fin k => μ))
    (hπint : ∀ k : ℕ,
      Integrable
        (llr (Measure.pi (fun _ : Fin k => μ)) (Measure.pi (fun _ : Fin k => ν)))
        (Measure.pi (fun _ : Fin k => μ))) :
    ProductKLTensorizationBound n μ ν := by
  have hleft_ne_top :
      _root_.InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν)) ≠ ∞ :=
    _root_.InformationTheory.klDiv_ne_top (hπac n) (hπint n)
  have hright_kl_ne_top : _root_.InformationTheory.klDiv μ ν ≠ ∞ :=
    _root_.InformationTheory.klDiv_ne_top hac hint
  exact ⟨hleft_ne_top, hright_kl_ne_top, le_of_eq <|
    productKL_tensorization_of_finite n μ ν hac hac' hint hπac hπac' hπint⟩

/-- Product-KL tensorisation for i.i.d. finite products from one-sample hypotheses. -/
theorem productKL_tensorization_iid {α : Type*} [MeasurableSpace α]
    (n : ℕ) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hac' : ν ≪ μ) (hint : Integrable (llr μ ν) μ) :
    ProductKLTensorizationBound n μ ν := by
  exact productKL_tensorization n μ ν hac hac' hint
    (ProductKLPrivate.pi_absolutelyContinuous_iid μ ν hac)
    (ProductKLPrivate.pi_absolutelyContinuous_iid ν μ hac')
    (ProductKLPrivate.pi_llr_integrable_iid μ ν hac hint)

/-- Unpack a supplied product-KL tensorisation bound. -/
theorem ProductKLTensorizationBound.apply {α : Type*} [MeasurableSpace α]
    {n : ℕ} {μ ν : Measure α}
    (h : ProductKLTensorizationBound n μ ν) :
    (_root_.InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν))).toReal
      ≤ (n : ℝ) * (_root_.InformationTheory.klDiv μ ν).toReal :=
  h.2.2

/-- The product KL divergence in a supplied tensorisation bound is finite. -/
theorem ProductKLTensorizationBound.product_ne_top {α : Type*} [MeasurableSpace α]
    {n : ℕ} {μ ν : Measure α}
    (h : ProductKLTensorizationBound n μ ν) :
    _root_.InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν)) ≠ ∞ :=
  h.1

/-- The one-observation KL divergence in a supplied tensorisation bound is finite. -/
theorem ProductKLTensorizationBound.one_ne_top {α : Type*} [MeasurableSpace α]
    {n : ℕ} {μ ν : Measure α}
    (h : ProductKLTensorizationBound n μ ν) :
    _root_.InformationTheory.klDiv μ ν ≠ ∞ :=
  h.2.1

/-- Public: absolute continuity of i.i.d. finite products from the one-sample
hypothesis `μ ≪ ν`. (Thin wrapper over the private induction.) -/
theorem pi_iid_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) ≪ Measure.pi (fun _ : Fin n => ν) :=
  ProductKLPrivate.pi_absolutelyContinuous_iid μ ν hμν n

/-- Public: log-likelihood-ratio integrability for i.i.d. finite products from
the one-sample hypotheses `μ ≪ ν` and `Integrable (llr μ ν) μ`.  Combined with
`pi_iid_absolutelyContinuous` this certifies `klDiv (pi μ) (pi ν) ≠ ⊤`
(via `InformationTheory.klDiv_ne_top`). -/
theorem pi_iid_llr_integrable {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hint : Integrable (llr μ ν) μ) (n : ℕ) :
    Integrable
      (llr (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν)))
      (Measure.pi (fun _ : Fin n => μ)) :=
  ProductKLPrivate.pi_llr_integrable_iid μ ν hμν hint n

end Causalean.Mathlib.InformationTheory
