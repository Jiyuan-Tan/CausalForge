/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Analysis.Regression
import Mathlib.Topology.Order.Basic

/-! # RDD One-Sided Limits

This file provides the one-sided limit engine used by sharp and fuzzy
regression-discontinuity identification. If two real-valued functions agree
almost everywhere on the relevant side of a cutoff and the reference function
is continuous at the cutoff, then any corresponding one-sided limit of the
other function equals the reference value at the cutoff, provided the running
variable law has positive mass arbitrarily close to that side.

Theorems `oneSidedLimit_eq_right` and `oneSidedLimit_eq_left` identify
right- and left-hand limits from one-sided a.e. agreement. The pointwise
versions `value_eq_of_aeEq_right` and `value_eq_of_aeEq_left` identify the
cutoff values of two continuous representatives. These results isolate the
topological and measure-theoretic argument from the causal RDD files. -/

namespace Causalean
namespace PO
namespace RDDLimits

open Filter MeasureTheory
open scoped Topology

variable {π : Measure ℝ} {f g : ℝ → ℝ} {c : ℝ}

/-- For every right-neighborhood of `c`, an a.e. agreement of `f` and `g` on
`Ici c` plus positive `π`-mass on the open interval yields a point in
`(c, c + ε)` at which `f = g`. -/
private lemma exists_eq_in_Ioo_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.Ioo c (c + ε), f x = g x := by
  have hsubset : Set.Ioo c (c + ε) ⊆ Set.Ici c := fun x hx => le_of_lt hx.1
  have h_le : π.restrict (Set.Ioo c (c + ε)) ≤ π.restrict (Set.Ici c) :=
    Measure.restrict_mono hsubset le_rfl
  have h_ae_Ioo : f =ᵐ[π.restrict (Set.Ioo c (c + ε))] g :=
    h_aeEq.filter_mono (ae_mono h_le)
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (h_support ε hε) h_ae_Ioo

private lemma exists_eq_in_Ioo_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.Ioo (c - ε) c, f x = g x := by
  have hsubset : Set.Ioo (c - ε) c ⊆ Set.Iio c := fun x hx => hx.2
  have h_le : π.restrict (Set.Ioo (c - ε) c) ≤ π.restrict (Set.Iio c) :=
    Measure.restrict_mono hsubset le_rfl
  have h_ae_Ioo : f =ᵐ[π.restrict (Set.Ioo (c - ε) c)] g :=
    h_aeEq.filter_mono (ae_mono h_le)
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (h_support ε hε) h_ae_Ioo

private lemma neBot_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0) :
    (𝓝[>] c ⊓ Filter.principal {x | f x = g x}).NeBot := by
  rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot]
  intro hbot
  rcases mem_nhdsGT_iff_exists_Ioo_subset.1 hbot with ⟨b, hcb, hsub⟩
  set ε : ℝ := b - c
  have hε : 0 < ε := sub_pos.mpr hcb
  have hbeq : c + ε = b := by simp [ε]
  rcases exists_eq_in_Ioo_right h_aeEq h_support hε with ⟨x, hx_mem, hx_eq⟩
  rw [hbeq] at hx_mem
  exact hsub hx_mem hx_eq

private lemma neBot_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0) :
    (𝓝[<] c ⊓ Filter.principal {x | f x = g x}).NeBot := by
  rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot]
  intro hbot
  rcases mem_nhdsLT_iff_exists_Ioo_subset.1 hbot with ⟨a, hac, hsub⟩
  set ε : ℝ := c - a
  have hε : 0 < ε := sub_pos.mpr hac
  have haeq : c - ε = a := by simp [ε]
  rcases exists_eq_in_Ioo_left h_aeEq h_support hε with ⟨x, hx_mem, hx_eq⟩
  rw [haeq] at hx_mem
  exact hsub hx_mem hx_eq

/-- **Right-side limit identification.**  If `f =ᵐ[π.restrict (Ici c)] g`,
`g` is continuous at `c`, every right-open neighborhood of `c` has positive
`π`-mass, and `f` has any right-side limit `L` at `c`, then `L = g c`. -/
theorem oneSidedLimit_eq_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0)
    {L : ℝ} (hL : Tendsto f (𝓝[>] c) (𝓝 L)) :
    L = g c := by
  haveI : (𝓝[>] c ⊓ Filter.principal {x | f x = g x}).NeBot :=
    neBot_right h_aeEq h_support
  have h_f :
      Tendsto f
        (𝓝[>] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := hL.mono_left inf_le_left
  have h_g_full :
      Tendsto g (𝓝[>] c) (𝓝 (g c)) :=
    hg_cont.tendsto.mono_left inf_le_left
  have h_g :
      Tendsto g
        (𝓝[>] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 (g c)) := h_g_full.mono_left inf_le_left
  have h_eq :
      f =ᶠ[𝓝[>] c ⊓ Filter.principal {x | f x = g x}] g := by
    refine Filter.eventually_iff_exists_mem.mpr ?_
    refine ⟨{x | f x = g x}, ?_, fun x hx => hx⟩
    exact mem_inf_of_right (mem_principal_self _)
  have h_f' :
      Tendsto g
        (𝓝[>] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := h_f.congr' h_eq
  exact tendsto_nhds_unique h_f' h_g

/-- **Left-side limit identification.**  Symmetric form of
`oneSidedLimit_eq_right`. -/
theorem oneSidedLimit_eq_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0)
    {L : ℝ} (hL : Tendsto f (𝓝[<] c) (𝓝 L)) :
    L = g c := by
  haveI : (𝓝[<] c ⊓ Filter.principal {x | f x = g x}).NeBot :=
    neBot_left h_aeEq h_support
  have h_f :
      Tendsto f
        (𝓝[<] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := hL.mono_left inf_le_left
  have h_g_full :
      Tendsto g (𝓝[<] c) (𝓝 (g c)) :=
    hg_cont.tendsto.mono_left inf_le_left
  have h_g :
      Tendsto g
        (𝓝[<] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 (g c)) := h_g_full.mono_left inf_le_left
  have h_eq :
      f =ᶠ[𝓝[<] c ⊓ Filter.principal {x | f x = g x}] g := by
    refine Filter.eventually_iff_exists_mem.mpr ?_
    refine ⟨{x | f x = g x}, ?_, fun x hx => hx⟩
    exact mem_inf_of_right (mem_principal_self _)
  have h_f' :
      Tendsto g
        (𝓝[<] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := h_f.congr' h_eq
  exact tendsto_nhds_unique h_f' h_g

/-- **Pointwise equality from a.e. agreement plus continuity.**  If `f` and
`g` agree `π.restrict (Ici c)`-a.e., both are continuous at `c`, and every
right-open neighborhood of `c` has positive `π`-mass, then `f c = g c`. -/
theorem value_eq_of_aeEq_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (hf_cont : ContinuousAt f c) (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0) :
    f c = g c := by
  have hL : Tendsto f (𝓝[>] c) (𝓝 (f c)) :=
    hf_cont.tendsto.mono_left nhdsWithin_le_nhds
  exact oneSidedLimit_eq_right h_aeEq hg_cont h_support hL

/-- Symmetric pointwise version of `value_eq_of_aeEq_right`. -/
theorem value_eq_of_aeEq_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (hf_cont : ContinuousAt f c) (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0) :
    f c = g c := by
  have hL : Tendsto f (𝓝[<] c) (𝓝 (f c)) :=
    hf_cont.tendsto.mono_left nhdsWithin_le_nhds
  exact oneSidedLimit_eq_left h_aeEq hg_cont h_support hL

end RDDLimits
end PO
end Causalean
