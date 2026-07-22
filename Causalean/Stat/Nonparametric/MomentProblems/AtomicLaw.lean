/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.MeasureTheory.MomentSliceSupport
import Causalean.Stat.Nonparametric.MomentProblems.Cumulant
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Finite atomic laws on the real line

This module builds the finitely supported probability laws used as explicit witnesses in
truncated moment problems: a finite list of distinct real atom locations carrying a matching list
of weights.  It records how such a law integrates an arbitrary function (a weighted sum over the
atoms), when it is a probability measure, how much mass it puts on each atom, that all of its
moments are finite (the support is bounded), and that it is never Gaussian as soon as two atoms
carry strictly positive mass.

The last fact is what makes finite atomic laws usable as non-Gaussian witnesses: a nondegenerate
normal law has no atoms at all, and a degenerate one is a single point mass, so two distinct atoms
of positive mass rule out both cases.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-- The total weight that an indexed list of atoms places on a given point of the real line: the
sum of the weights of all indices whose location is that point. -/
noncomputable def atomicWeight (n : ℕ) (x : Fin n → ℝ) (p : Fin n → ℝ) : ℝ → ℝ :=
  fun t ↦ ∑ i : Fin n, if x i = t then p i else 0

/-- The **finite atomic law** determined by a list of real locations and a matching list of
weights: the measure that puts each weight as a point mass at its own location. -/
noncomputable def atomicLaw (n : ℕ) (x : Fin n → ℝ) (p : Fin n → ℝ) : Measure ℝ :=
  Causalean.Mathlib.MeasureTheory.discreteMeasure (Finset.image x Finset.univ)
    (atomicWeight n x p)

/-- When the atom locations are pairwise distinct, the total weight sitting at one of them is
exactly that atom's own weight — no two indices collide. -/
theorem atomicWeight_apply {n : ℕ} {x : Fin n → ℝ} {p : Fin n → ℝ}
    (hx : Function.Injective x) (j : Fin n) :
    atomicWeight n x p (x j) = p j := by
  classical
  simp [atomicWeight, hx.eq_iff]

/-- Integrating a function against a finite atomic law with distinct locations and nonnegative
weights gives the weighted sum of the function's values at the atoms. -/
theorem integral_atomicLaw {n : ℕ} {x : Fin n → ℝ} {p : Fin n → ℝ}
    (hx : Function.Injective x) (hp : ∀ i, 0 ≤ p i) (f : ℝ → ℝ) :
    ∫ t, f t ∂(atomicLaw n x p) = ∑ i : Fin n, p i * f (x i) := by
  classical
  rw [atomicLaw, Causalean.Mathlib.MeasureTheory.integral_discreteMeasure]
  · rw [Finset.sum_image hx.injOn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [atomicWeight_apply hx]
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    rw [atomicWeight_apply hx]
    exact hp i

/-- A finite atomic law with distinct locations, nonnegative weights, and weights summing to one
is a probability measure. -/
theorem isProbabilityMeasure_atomicLaw {n : ℕ} {x : Fin n → ℝ} {p : Fin n → ℝ}
    (hx : Function.Injective x) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsProbabilityMeasure (atomicLaw n x p) := by
  classical
  apply Causalean.Mathlib.MeasureTheory.isProbabilityMeasure_discreteMeasure
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    rw [atomicWeight_apply hx]
    exact hp i
  · rw [Finset.sum_image hx.injOn]
    simpa only [atomicWeight_apply hx] using hsum

/-- A finite atomic law with distinct locations and nonnegative weights puts exactly its own
weight of mass on each single atom. -/
theorem atomicLaw_singleton {n : ℕ} {x : Fin n → ℝ} {p : Fin n → ℝ}
    (hx : Function.Injective x) (hp : ∀ i, 0 ≤ p i) (j : Fin n) :
    atomicLaw n x p {x j} = ENNReal.ofReal (p j) := by
  classical
  have hpj := hp j
  rw [atomicLaw, Causalean.Mathlib.MeasureTheory.discreteMeasure_singleton]
  · rw [atomicWeight_apply hx]
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- A finite atomic probability law has finite moments of every order: its support is a bounded
finite set, so the identity function is bounded almost everywhere and hence in every `Lᵖ`. -/
theorem memLp_id_atomicLaw {n : ℕ} {x : Fin n → ℝ} {p : Fin n → ℝ}
    (hx : Function.Injective x) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (q : ℝ≥0∞) : MemLp (id : ℝ → ℝ) q (atomicLaw n x p) := by
  classical
  let C : ℝ := ∑ i : Fin n, |x i|
  letI : IsProbabilityMeasure (atomicLaw n x p) :=
    isProbabilityMeasure_atomicLaw hx hp hsum
  apply memLp_of_bounded
  · rw [ae_iff]
    change atomicLaw n x p (Set.Icc (-C) C)ᶜ = 0
    apply Causalean.Mathlib.MeasureTheory.discreteMeasure_apply_compl_Icc
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hxi : |x i| ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum (fun j hj ↦ abs_nonneg (x j)) (Finset.mem_univ i)
    exact (abs_le.mp hxi)
  · exact continuous_id.aestronglyMeasurable

/-- A finite atomic probability law supported on at least two distinct locations, each carrying
strictly positive mass, is **not** a Gaussian law: a normal law with positive variance has no
point masses at all, and one with zero variance is a single point mass. -/
theorem not_isGaussianLaw_atomicLaw {n : ℕ} {x : Fin n → ℝ} {p : Fin n → ℝ}
    (hx : Function.Injective x) (hp : ∀ i, 0 < p i)
    (hn : 2 ≤ n) : ¬ IsGaussianLaw (atomicLaw n x p) := by
  classical
  intro hgauss
  obtain ⟨mean, v, hv⟩ := hgauss
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi₀₁ : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have hx₀₁ : x i₀ ≠ x i₁ := fun h ↦ hi₀₁ (hx h)
  have hpnonneg : ∀ i, 0 ≤ p i := fun i ↦ (hp i).le
  by_cases hvzero : v = 0
  · have hdirac : atomicLaw n x p = Measure.dirac mean := by
      rw [hv, hvzero, gaussianReal_zero_var]
    have hmass₀ := atomicLaw_singleton hx hpnonneg i₀
    have hmass₁ := atomicLaw_singleton hx hpnonneg i₁
    rw [hdirac] at hmass₀ hmass₁
    have hmean₀ : mean = x i₀ := by
      by_contra hne
      have hzero : Measure.dirac mean {x i₀} = 0 := by
        simp [Measure.dirac_apply' mean (MeasurableSet.singleton (x i₀)), hne]
      exact ENNReal.ofReal_ne_zero_iff.mpr (hp i₀) (hmass₀.symm.trans hzero)
    have hmean₁ : mean = x i₁ := by
      by_contra hne
      have hzero : Measure.dirac mean {x i₁} = 0 := by
        simp [Measure.dirac_apply' mean (MeasurableSet.singleton (x i₁)), hne]
      exact ENNReal.ofReal_ne_zero_iff.mpr (hp i₁) (hmass₁.symm.trans hzero)
    exact hx₀₁ (hmean₀.symm.trans hmean₁)
  · have hnoatoms : NoAtoms (atomicLaw n x p) := by
      rw [hv]
      exact noAtoms_gaussianReal hvzero
    have hzero : atomicLaw n x p {x i₀} = 0 := hnoatoms.measure_singleton (x i₀)
    rw [atomicLaw_singleton hx hpnonneg i₀] at hzero
    exact ENNReal.ofReal_ne_zero_iff.mpr (hp i₀) hzero

end Causalean.Stat.MomentProblems
