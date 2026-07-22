/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The Bernoulli randomization design

The **Bernoulli design** assigns each unit `i` to treatment by an independent coin flip with
unit-specific probability `p i`.  It is the product `prodDesign` of the per-unit coin designs, so
two distinct units' treatments are independent.  This file records the design and its
**inclusion probabilities** — the design facts an estimator's bias and variance are built from:
the first-order inclusion probability of a unit is `p i`, the treatment indicator has variance
`p i (1 − p i)`, and two distinct units' treatment indicators have joint expectation `p i · p j`
and zero covariance.

This is the paper-agnostic canonical Bernoulli design in the design zoo; the Sävje–Aronow–Hudgens
folder carries its own copy used by that paper's development.
-/

import Causalean.Experimentation.DesignBased.ProductVariance

/-! # Bernoulli randomization designs

Bernoulli designs assign each unit independently with unit-specific treatment probabilities.

This file defines the single-unit coin design and its product design, then records the
first- and second-order inclusion facts used by estimator bias and variance calculations.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The single-unit **coin design** on `Bool`: treatment (`true`) with probability `p`, control
(`false`) with probability `1 − p`. -/
def coinDesign (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDesign Bool where
  p := fun b => cond b p (1 - p)
  p_nonneg := by
    intro b; cases b
    · exact sub_nonneg.mpr hp1
    · exact hp0
  p_sum := by rw [Fintype.sum_bool]; show p + (1 - p) = 1; ring

/-- The expectation of a function of a single coin: `E[g] = p·g(true) + (1−p)·g(false)`. -/
lemma coinDesign_E (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Bool → ℝ) :
    (coinDesign p hp0 hp1).E g = p * g true + (1 - p) * g false := by
  simp only [FiniteDesign.E, coinDesign, Fintype.sum_bool, cond_true, cond_false]

/-- The treatment indicator of a single coin, `1(true)`, has expectation `p`. -/
lemma coinDesign_E_treat (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coinDesign p hp0 hp1).E (fun b => if b then (1 : ℝ) else 0) = p := by
  rw [coinDesign_E]; simp

/-- The treatment indicator of a single coin has variance `p(1 − p)`. -/
lemma coinDesign_Var_treat (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coinDesign p hp0 hp1).Var (fun b => if b then (1 : ℝ) else 0) = p * (1 - p) := by
  rw [FiniteDesign.Var_eq, coinDesign_E_treat]
  have hsq :
      (fun b : Bool => ((if b then (1 : ℝ) else 0) : ℝ) ^ 2) =
        (fun b : Bool => if b then (1 : ℝ) else 0) := by
    funext b
    cases b <;> simp
  rw [hsq, coinDesign_E_treat]
  ring

/-- The **Bernoulli randomization design**: each unit `i` is independently assigned treatment with
probability `p i`.  Built as the product of the per-unit coin designs. -/
noncomputable def bernoulliDesign (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteDesign (U → Bool) :=
  prodDesign (fun i => coinDesign (p i) (hp0 i) (hp1 i))

/-- The treatment indicator of unit `i` under an assignment `z`: `1` if `i` is treated, else `0`. -/
def treatInd (i : U) (z : U → Bool) : ℝ := if z i then 1 else 0

/-- **First-order inclusion probability.** Unit `i`'s treatment indicator has expectation `p i`. -/
lemma bernoulliDesign_E_treatInd (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).E (treatInd i) = p i := by
  change (prodDesign (fun k => coinDesign (p k) (hp0 k) (hp1 k))).E
      (fun z => (fun b => if b then (1 : ℝ) else 0) (z i)) = p i
  rw [FiniteDesign.E_prod_apply (fun k => coinDesign (p k) (hp0 k) (hp1 k)) i
        (fun b => if b then (1 : ℝ) else 0), coinDesign_E_treat]

/-- The treatment indicator of unit `i` has variance `p i (1 − p i)` under the Bernoulli design. -/
lemma bernoulliDesign_Var_treatInd (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).Var (treatInd i) = p i * (1 - p i) := by
  change (prodDesign (fun k => coinDesign (p k) (hp0 k) (hp1 k))).Var
      (fun z => (fun b => if b then (1 : ℝ) else 0) (z i)) = p i * (1 - p i)
  rw [FiniteDesign.Var_prod_apply (fun k => coinDesign (p k) (hp0 k) (hp1 k)) i
        (fun b => if b then (1 : ℝ) else 0), coinDesign_Var_treat]

/-- **Second-order inclusion probability.** For distinct units `i ≠ j`, the joint expectation of
the two treatment indicators factors as `p i · p j` — the units are independently assigned. -/
lemma bernoulliDesign_E_treatInd_pair (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {i j : U} (h : i ≠ j) :
    (bernoulliDesign p hp0 hp1).E (fun z => treatInd i z * treatInd j z) = p i * p j := by
  change (prodDesign (fun k => coinDesign (p k) (hp0 k) (hp1 k))).E
      (fun z =>
        (fun b => if b then (1 : ℝ) else 0) (z i) *
          (fun b => if b then (1 : ℝ) else 0) (z j)) = p i * p j
  rw [FiniteDesign.E_prod_apply₂ (fun k => coinDesign (p k) (hp0 k) (hp1 k)) h
        (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (1 : ℝ) else 0),
      coinDesign_E_treat, coinDesign_E_treat]

/-- For distinct units `i ≠ j`, the two treatment indicators are uncorrelated under the Bernoulli
design. -/
lemma bernoulliDesign_Cov_treatInd (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {i j : U} (h : i ≠ j) :
    (bernoulliDesign p hp0 hp1).Cov (treatInd i) (treatInd j) = 0 := by
  change (prodDesign (fun k => coinDesign (p k) (hp0 k) (hp1 k))).Cov
      (fun z => (fun b => if b then (1 : ℝ) else 0) (z i))
      (fun z => (fun b => if b then (1 : ℝ) else 0) (z j)) = 0
  rw [FiniteDesign.Cov_prod_apply_of_ne (fun k => coinDesign (p k) (hp0 k) (hp1 k)) h
        (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (1 : ℝ) else 0)]

end DesignBased
end Experimentation
end Causalean
