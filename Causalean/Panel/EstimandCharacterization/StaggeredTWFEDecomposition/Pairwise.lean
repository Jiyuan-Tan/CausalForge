/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon pairwise algebra layer

**Role in the folder.** *Finite-algebra support (not a headline).* Reduction
machinery feeding the algebraic headline `AlgebraicDecomposition.lean`. See
`StaggeredTWFEDecomposition.lean` for the folder layer-map.

This file sits between the paper-agnostic finite weighted identities in
`Panel/EstimandCharacterization/Causalean.Panel.Weighted.NormalizedWeights.lean` and the headline
Goodman-Bacon decomposition in `AlgebraicDecomposition.lean`.

It exposes the pairwise centered-treatment contributions that the denominator
and numerator identities should first reduce to before the adoption-window
case split into TN / EL / LE comparisons.
-/

import Causalean.Panel.Weighted.NormalizedWeights
import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.FinitePanel
import Mathlib.Tactic.Ring

/-! # Goodman-Bacon Pairwise Algebra

This file reduces Goodman-Bacon denominator and numerator terms to ordered-pair
centered-treatment contributions. It is the algebraic bridge between generic
finite weighted covariance identities and the adoption-window case analysis that
produces the three comparison types in the decomposition. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

private lemma weighted_center_cov_uncentered_right {ι : Type*} [Fintype ι]
    (p x y : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * (x i - ∑ j, p j * x j) * y i =
      (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j) * (y i - y j) := by
  classical
  let mx := ∑ j, p j * x j
  let my := ∑ j, p j * y j
  have hzero : ∑ i, p i * (x i - mx) = 0 := by
    calc
      ∑ i, p i * (x i - mx) = (∑ i, p i * x i) - ∑ i, p i * mx := by
        simp [mul_sub, Finset.sum_sub_distrib]
      _ = mx - (∑ i, p i) * mx := by
        simp [Finset.sum_mul, mx]
      _ = 0 := by
        rw [hp]
        ring
  have hmy : ∑ i, p i * (x i - mx) * my = 0 := by
    calc
      ∑ i, p i * (x i - mx) * my = (∑ i, p i * (x i - mx)) * my := by
        rw [Finset.sum_mul]
      _ = 0 := by
        rw [hzero]
        ring
  have hcenter : ∑ i, p i * (x i - mx) * y i =
      ∑ i, p i * (x i - mx) * (y i - my) := by
    calc
      ∑ i, p i * (x i - mx) * y i =
          ∑ i, (p i * (x i - mx) * (y i - my) + p i * (x i - mx) * my) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ = ∑ i, p i * (x i - mx) * (y i - my) + ∑ i, p i * (x i - mx) * my := by
            rw [Finset.sum_add_distrib]
      _ = ∑ i, p i * (x i - mx) * (y i - my) := by
            rw [hmy]
            ring
  calc
    ∑ i, p i * (x i - ∑ j, p j * x j) * y i =
        ∑ i, p i * (x i - mx) * y i := by rfl
    _ = ∑ i, p i * (x i - mx) * (y i - my) := hcenter
    _ = ∑ i, p i * (x i - ∑ j, p j * x j) * (y i - ∑ j, p j * y j) := by rfl
    _ = (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j) * (y i - y j) :=
      Causalean.Panel.Weighted.NormalizedWeights.weighted_center_cov p x y hp

private lemma sum_weight_over_T_commute
    (P : CohortPanel 𝒢 T) (f : 𝒢 → Fin T → ℝ) :
    (∑ g, ∑ t, (P.p g / (T : ℝ)) * f g t) =
      (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g * f g t := by
  rw [Finset.sum_comm]
  simp [div_eq_mul_inv, Finset.mul_sum, mul_left_comm, mul_comm]

private lemma pairwise_sum_normalize
    (P : CohortPanel 𝒢 T) (f : 𝒢 → 𝒢 → Fin T → ℝ) :
    (T : ℝ)⁻¹ * ∑ t, ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u * f g u t) =
      ∑ g, ∑ u, (P.p g * P.p u / (2 * (T : ℝ))) * ∑ t, f g u t := by
  calc
    (T : ℝ)⁻¹ * ∑ t, ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u * f g u t)
        = (T : ℝ)⁻¹ * ∑ t, ∑ g, ∑ u, (1 / 2) * (P.p g * P.p u * f g u t) := by
          simp [Finset.mul_sum]
    _ = (T : ℝ)⁻¹ * ∑ g, ∑ u, ∑ t, (1 / 2) * (P.p g * P.p u * f g u t) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [Finset.sum_comm]
    _ = ∑ g, ∑ u, (P.p g * P.p u / (2 * (T : ℝ))) * ∑ t, f g u t := by
          simp [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Cohort-demeaned treatment path `D_{gt} − \overline D_g`. -/
noncomputable def centeredD (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) : ℝ :=
  D P g t - barD P g

/-- Ordered-pair contribution in the pairwise representation of `V_D`.

The factor `1/2` is deliberate: the generic finite weighted variance identity
sums over ordered pairs. The Goodman-Bacon denominator later combines the two
orders `(g,u)` and `(u,g)` into one unordered comparison weight.
-/
noncomputable def vdPairContribution (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  (P.p g * P.p u / (2 * (T : ℝ))) *
    ∑ t, (centeredD P g t - centeredD P u t)^2

/-- Ordered-pair contribution in the pairwise representation of the TWFE
numerator. As for `vdPairContribution`, the two orders of each cohort pair are
combined by the Goodman-Bacon-specific window lemmas below. -/
noncomputable def numPairContribution (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  (P.p g * P.p u / (2 * (T : ℝ))) *
    ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t)

private lemma D_eq_zero_of_isInf (P : CohortPanel 𝒢 T) {u : 𝒢}
    (hu : AdoptionDate.isInf (P.A u)) (t : Fin T) :
    D P u t = 0 := by
  unfold D
  rw [show P.A u = ⊤ from hu]
  simp [AdoptionDate.le]

private lemma barD_eq_zero_of_isInf (P : CohortPanel 𝒢 T) {u : 𝒢}
    (hu : AdoptionDate.isInf (P.A u)) :
    barD P u = 0 := by
  unfold barD
  simp [D_eq_zero_of_isInf P hu]

private lemma D_sq_eq_D (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) :
    D P g t ^ 2 = D P g t := by
  unfold D
  by_cases h : AdoptionDate.le (P.A g) t <;> simp [h]

private lemma binary_time_variance (P : CohortPanel 𝒢 T)
    (x : Fin T → ℝ) (hx : ∀ t, x t ^ 2 = x t) :
    (T : ℝ)⁻¹ * ∑ t, (x t - ((T : ℝ)⁻¹ * ∑ t, x t)) ^ 2 =
      ((T : ℝ)⁻¹ * ∑ t, x t) * (1 - ((T : ℝ)⁻¹ * ∑ t, x t)) := by
  classical
  let m : ℝ := (T : ℝ)⁻¹ * ∑ t, x t
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hsum_sq : ∑ t, x t ^ 2 = ∑ t, x t := by
    exact Finset.sum_congr rfl (by intro t _ht; exact hx t)
  have hsum_expand :
      ∑ t, (x t ^ 2 - 2 * m * x t + m ^ 2) =
        ∑ t, x t - 2 * m * ∑ t, x t + (T : ℝ) * m ^ 2 := by
    calc
      ∑ t, (x t ^ 2 - 2 * m * x t + m ^ 2) =
          ∑ t, x t ^ 2 - ∑ t, 2 * m * x t + ∑ _t : Fin T, m ^ 2 := by
        simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = ∑ t, x t - 2 * m * ∑ t, x t + (T : ℝ) * m ^ 2 := by
        rw [hsum_sq]
        simp [Finset.mul_sum, Fintype.card_fin]
  calc
    (T : ℝ)⁻¹ * ∑ t, (x t - ((T : ℝ)⁻¹ * ∑ t, x t)) ^ 2 =
        (T : ℝ)⁻¹ * ∑ t, (x t ^ 2 - 2 * m * x t + m ^ 2) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      simp [m]
      ring
    _ = ((T : ℝ)⁻¹ * ∑ t, x t) * (1 - ((T : ℝ)⁻¹ * ∑ t, x t)) := by
      rw [hsum_expand]
      simp [m]
      field_simp [hTne]
      ring

set_option linter.flexible false in
private lemma binary_time_cov_filter_mean
    (P : CohortPanel 𝒢 T) (p : Fin T → Prop) [DecidablePred p] (z : Fin T → ℝ)
    (hcard1 : ((Finset.univ.filter p).card : ℝ) ≠ 0) :
    (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
        ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t =
      ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) *
        (1 - ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) *
          (((Finset.univ.filter p).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter p), z t) -
            ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) := by
  classical
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  let A : ℝ := ((Finset.univ.filter p).card : ℝ)
  let B : ℝ := ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)
  let Z1 : ℝ := ∑ t ∈ (Finset.univ.filter p), z t
  let Z0 : ℝ := ∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t
  have hA : A ≠ 0 := by
    simpa [A] using hcard1
  have hsum_if : (∑ t, (if p t then (1 : ℝ) else 0)) = A := by
    simp [A]
  have hsum_if_z : (∑ t, (if p t then (1 : ℝ) else 0) * z t) = Z1 := by
    simp [Z1, Finset.sum_filter]
  have hsum_z : (∑ t, z t) = Z1 + Z0 := by
    simp [Z1, Z0, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro t _
    by_cases ht : p t <;> simp [ht]
  have hcard_total : A + B = (T : ℝ) := by
    have hnat :
        (Finset.univ.filter p).card +
            (Finset.univ.filter (fun t => ¬ p t)).card = T := by
      calc
        (Finset.univ.filter p).card +
            (Finset.univ.filter (fun t => ¬ p t)).card =
            ((Finset.univ.filter p) ∪
              (Finset.univ.filter (fun t => ¬ p t))).card := by
          rw [Finset.card_union_of_disjoint]
          simp [Finset.disjoint_left]
        _ = T := by
          have hunion :
              (Finset.univ.filter p) ∪ (Finset.univ.filter (fun t => ¬ p t)) =
                (Finset.univ : Finset (Fin T)) := by
            ext t
            simp [em]
          simp [hunion]
    simpa [A, B] using
      (show (((Finset.univ.filter p).card : ℝ) +
              ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ) = (T : ℝ)) by
        exact_mod_cast hnat)
  have hmain :
      (T : ℝ)⁻¹ * (Z1 - ((T : ℝ)⁻¹ * A) * (Z1 + Z0)) =
        ((T : ℝ)⁻¹ * A) * (1 - ((T : ℝ)⁻¹ * A)) *
          (A⁻¹ * Z1 - B⁻¹ * Z0) := by
    by_cases hB : B = 0
    · have hZT0 : Z0 = 0 := by
        have hempty : Finset.univ.filter (fun t => ¬ p t) = ∅ := by
          apply Finset.card_eq_zero.mp
          have hB' : ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ) = 0 := by
            simpa [B] using hB
          exact_mod_cast hB'
        simp [Z0, hempty]
      have hAeq : A = (T : ℝ) := by
        linarith
      rw [hZT0, hAeq]
      field_simp [hTne]
      ring
    · have hABne : A + B ≠ 0 := by
        rw [hcard_total]
        exact hTne
      rw [← hcard_total]
      field_simp [hA, hB, hABne]
      ring
  calc
    (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
        ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t =
        (T : ℝ)⁻¹ * (Z1 - ((T : ℝ)⁻¹ * A) * (Z1 + Z0)) := by
      rw [hsum_if]
      calc
        (T : ℝ)⁻¹ *
            ∑ t, ((if p t then (1 : ℝ) else 0) - (T : ℝ)⁻¹ * A) * z t =
            (T : ℝ)⁻¹ * (∑ t, (if p t then (1 : ℝ) else 0) * z t -
              ∑ t, ((T : ℝ)⁻¹ * A) * z t) := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro t _
          ring
        _ = (T : ℝ)⁻¹ * (Z1 - ((T : ℝ)⁻¹ * A) * (Z1 + Z0)) := by
          rw [hsum_if_z, ← Finset.mul_sum, hsum_z]
    _ = ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) *
        (1 - ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) *
          (((Finset.univ.filter p).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter p), z t) -
            ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) := by
      rw [hmain, hsum_if]

open Classical in
private lemma TN_treated_window_card_ne_zero
    (P : CohortPanel 𝒢 T) {g : 𝒢} (hg : AdoptionDate.isFin (P.A g)) :
    ((Finset.univ.filter (fun t => AdoptionDate.le (P.A g) t)).card : ℝ) ≠ 0 := by
  cases hA : P.A g with
  | top =>
      exact False.elim (hg hA)
  | coe a =>
      have hmem : a ∈ Finset.univ.filter (fun t => AdoptionDate.le (P.A g) t) := by
        simp [AdoptionDate.le, hA]
      have hpos : 0 < (Finset.univ.filter
          (fun t => AdoptionDate.le (P.A g) t)).card :=
        Finset.card_pos.mpr ⟨a, hmem⟩
      have hne :
          ((Finset.univ.filter (fun t => AdoptionDate.le (P.A g) t)).card : ℝ) ≠
            0 := by
        exact_mod_cast (ne_of_gt hpos)
      simpa [hA] using hne

open Classical in
private lemma TT_middle_window_card_ne_zero
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (_hℓ : AdoptionDate.isFin (P.A ℓ)) :
    ((Finset.univ.filter
        (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t)).card :
      ℝ) ≠ 0 := by
  cases he : P.A e with
  | top =>
      have hbad := hord
      simp [he] at hbad
  | coe a =>
      cases hℓA : P.A ℓ with
      | top =>
          exact False.elim (_hℓ hℓA)
      | coe b =>
          have hab : (a : WithTop (Fin T)) < (b : WithTop (Fin T)) := by
            simpa [he, hℓA] using hord
          have habFin : a < b := by
            exact (WithTop.coe_lt_coe (a := b) (b := a)).mp hab
          have hmem : a ∈ Finset.univ.filter
              (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t) := by
            simp [AdoptionDate.le, AdoptionDate.lt, he, hℓA, habFin]
          have hpos : 0 < (Finset.univ.filter
              (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t)).card :=
            Finset.card_pos.mpr ⟨a, hmem⟩
          have hne :
              ((Finset.univ.filter
                (fun t => AdoptionDate.le (P.A e) t ∧
                  AdoptionDate.lt (P.A ℓ) t)).card : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hpos)
          simpa [he, hℓA] using hne

private lemma weighted_centeredD_mean (P : CohortPanel 𝒢 T) (t : Fin T) :
    (∑ h, P.p h * centeredD P h t) = (∑ h, P.p h * D P h t) - pCohort P := by
  unfold centeredD pCohort
  calc
    (∑ h, P.p h * (D P h t - barD P h)) =
        ∑ h, (P.p h * D P h t - P.p h * barD P h) := by
          refine Finset.sum_congr rfl ?_
          intro h _hh
          ring
    _ = (∑ h, P.p h * D P h t) - ∑ h, P.p h * barD P h := by
          simp only [Finset.sum_sub_distrib]

/-- The explicit double-demeaning formula for `Dtilde` is the weighted
centering, across cohorts, of the cohort-demeaned treatment path. -/
lemma Dtilde_eq_centeredD_sub_weighted_mean
    (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) :
    Dtilde P g t = centeredD P g t - ∑ h, P.p h * centeredD P h t := by
  rw [weighted_centeredD_mean P t]
  rw [Dtilde_eq]
  unfold centeredD
  ring

/-- Pairwise representation of the residualized-treatment variance.

Proof route: rewrite `Dtilde` using
`Dtilde_eq_centeredD_sub_weighted_mean`, swap the `g`/`t` finite sums, and
apply `Causalean.Panel.Weighted.NormalizedWeights.weighted_center_var` at each period `t`. -/
lemma VD_eq_pairwise_centeredD (P : CohortPanel 𝒢 T) :
    VD P = ∑ g, ∑ u, vdPairContribution P g u := by
  classical
  calc
    VD P = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g * (Dtilde P g t)^2 := by
      unfold VD
      exact sum_weight_over_T_commute P (fun g t => (Dtilde P g t)^2)
    _ = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g *
        (centeredD P g t - ∑ h, P.p h * centeredD P h t)^2 := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      refine Finset.sum_congr rfl ?_
      intro g _hg
      rw [Dtilde_eq_centeredD_sub_weighted_mean]
    _ = (T : ℝ)⁻¹ * ∑ t,
        ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u *
          (centeredD P g t - centeredD P u t)^2) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      exact Causalean.Panel.Weighted.NormalizedWeights.weighted_center_var (fun g => P.p g)
        (fun g => centeredD P g t) P.p_sum_one
    _ = ∑ g, ∑ u, vdPairContribution P g u := by
      unfold vdPairContribution
      exact pairwise_sum_normalize P
        (fun g u t => (centeredD P g t - centeredD P u t)^2)

/-- Pairwise representation of the TWFE numerator.

Proof route: rewrite `Dtilde` using
`Dtilde_eq_centeredD_sub_weighted_mean`, use that the weighted centered
`D` term has zero cohort mean at each period, and apply
`Causalean.Panel.Weighted.NormalizedWeights.weighted_center_cov` to the cohort dimension. -/
lemma twfe_numerator_eq_pairwise_centeredD_Y (P : CohortPanel 𝒢 T) :
    (∑ g, ∑ t, (P.p g / (T : ℝ)) * Dtilde P g t * P.Y g t) =
      ∑ g, ∑ u, numPairContribution P g u := by
  classical
  calc
    (∑ g, ∑ t, (P.p g / (T : ℝ)) * Dtilde P g t * P.Y g t) =
        ∑ g, ∑ t, (P.p g / (T : ℝ)) * (Dtilde P g t * P.Y g t) := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      refine Finset.sum_congr rfl ?_
      intro t _ht
      ring
    _ = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g * (Dtilde P g t * P.Y g t) := by
      exact sum_weight_over_T_commute P (fun g t => Dtilde P g t * P.Y g t)
    _ = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g *
        (centeredD P g t - ∑ h, P.p h * centeredD P h t) * P.Y g t := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      refine Finset.sum_congr rfl ?_
      intro g _hg
      rw [Dtilde_eq_centeredD_sub_weighted_mean]
      ring
    _ = (T : ℝ)⁻¹ * ∑ t,
        ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u *
          (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      exact weighted_center_cov_uncentered_right (fun g => P.p g)
        (fun g => centeredD P g t) (fun g => P.Y g t) P.p_sum_one
    _ = ∑ g, ∑ u, numPairContribution P g u := by
      unfold numPairContribution
      simpa [mul_assoc] using pairwise_sum_normalize P
        (fun g u t => (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t))

/-! ### Pairwise Goodman-Bacon helper layer -/

/-- Symmetric denominator helper for `TN_pair_vd_contribution_eq_gap` and
`TT_pair_vd_contribution_eq_gap`: after adding the two ordered pair
contributions, only the raw time variance of the centered treatment gap
remains. -/
private lemma vdPairContribution_add_swap
    (P : CohortPanel 𝒢 T) (g u : 𝒢) :
    vdPairContribution P g u + vdPairContribution P u g =
      (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t)^2 := by
  classical
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hsum :
      (∑ t, (centeredD P u t - centeredD P g t)^2) =
        ∑ t, (centeredD P g t - centeredD P u t)^2 := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    ring
  unfold vdPairContribution
  rw [hsum]
  field_simp [hTne]
  ring

/-- Symmetric numerator helper for `TN_pair_contribution_eq_lambda_delta` and
`TT_pair_contribution_eq_lambda_delta_sum`: after adding the two ordered pair
contributions, the two sign reversals in the swapped covariance term cancel. -/
private lemma numPairContribution_add_swap
    (P : CohortPanel 𝒢 T) (g u : 𝒢) :
    numPairContribution P g u + numPairContribution P u g =
      (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) := by
  classical
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hsum :
      (∑ t, (centeredD P u t - centeredD P g t) * (P.Y u t - P.Y g t)) =
        ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    ring
  unfold numPairContribution
  rw [hsum]
  field_simp [hTne]
  ring

/-- TN denominator/numerator bridge used by the TN pair lemmas: the
never-treated cohort contributes zero to both `D` and `barD`, so the centered
gap is exactly the finite cohort's demeaned treatment path. -/
private lemma TN_centeredD_gap_eq
    (P : CohortPanel 𝒢 T) {g u : 𝒢} (hu : AdoptionDate.isInf (P.A u)) (t : Fin T) :
    centeredD P g t - centeredD P u t = D P g t - barD P g := by
  unfold centeredD
  rw [D_eq_zero_of_isInf P hu t, barD_eq_zero_of_isInf P hu]
  ring

open Classical in
private lemma TN_filter_not_treated_eq_S0
    (P : CohortPanel 𝒢 T) (g : 𝒢) :
    Finset.univ.filter (fun t => ¬ AdoptionDate.le (P.A g) t) = S0_TN P g := by
  rw [S0_TN]
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, AdoptionDate.le,
    AdoptionDate.lt]
  exact not_le

open Classical in
private lemma TT_D_gap_eq_middle_indicator
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (t : Fin T) :
    D P e t - D P ℓ t =
      if AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t then 1 else 0 := by
  unfold D
  by_cases hℓt : AdoptionDate.le (P.A ℓ) t
  · have het : AdoptionDate.le (P.A e) t := le_trans (le_of_lt hord) hℓt
    have hnlt : ¬ AdoptionDate.lt (P.A ℓ) t := by
      exact fun h => not_lt_of_ge hℓt h
    simp [hℓt, het, hnlt]
  · have hlt : AdoptionDate.lt (P.A ℓ) t := by
      exact not_le.mp hℓt
    by_cases het : AdoptionDate.le (P.A e) t <;> simp [hℓt, hlt, het]

/-- TN denominator bridge for `TN_pair_vd_contribution_eq_gap`: rewrites the
time variance of the centered treated-vs-never gap as the Bernoulli variance of
the finite cohort's treatment path. -/
private lemma TN_time_variance_eq_gap
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hg : AdoptionDate.isFin (P.A g)) (hu : AdoptionDate.isInf (P.A u)) :
    (T : ℝ)⁻¹ * ∑ t, (centeredD P g t - centeredD P u t)^2 =
      q P g u * (1 - q P g u) := by
  have : AdoptionDate.isFin (P.A g) := hg
  calc
    (T : ℝ)⁻¹ * ∑ t, (centeredD P g t - centeredD P u t)^2 =
        (T : ℝ)⁻¹ * ∑ t, (D P g t - barD P g)^2 := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      rw [TN_centeredD_gap_eq P hu t]
    _ = barD P g * (1 - barD P g) := by
      simpa [barD] using binary_time_variance P (fun t => D P g t) (D_sq_eq_D P g)
    _ = q P g u * (1 - q P g u) := by
      rw [q, barD_eq_zero_of_isInf P hu]
      ring

/-- TT denominator bridge for `TT_pair_vd_contribution_eq_gap`: under
`A_e < A_ℓ < ⊤`, the centered early-late gap has variance
`q P e ℓ * (1 - q P e ℓ)`. -/
private lemma TT_time_variance_eq_gap
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (_hℓ : AdoptionDate.isFin (P.A ℓ)) :
    (T : ℝ)⁻¹ * ∑ t, (centeredD P e t - centeredD P ℓ t)^2 =
      q P e ℓ * (1 - q P e ℓ) := by
  let x : Fin T → ℝ := fun t => D P e t - D P ℓ t
  have hx : ∀ t, x t ^ 2 = x t := by
    intro t
    unfold x D
    by_cases hℓt : AdoptionDate.le (P.A ℓ) t
    · by_cases het : AdoptionDate.le (P.A e) t
      · simp [hℓt, het]
      · have : AdoptionDate.le (P.A e) t := le_trans (le_of_lt hord) hℓt
        exact False.elim (het this)
    · by_cases het : AdoptionDate.le (P.A e) t <;> simp [hℓt, het]
  have hmean : (T : ℝ)⁻¹ * ∑ t, x t = q P e ℓ := by
    unfold x q barD
    rw [Finset.sum_sub_distrib]
    ring
  calc
    (T : ℝ)⁻¹ * ∑ t, (centeredD P e t - centeredD P ℓ t)^2 =
        (T : ℝ)⁻¹ * ∑ t, (x t - ((T : ℝ)⁻¹ * ∑ t, x t))^2 := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      unfold x centeredD
      rw [hmean]
      unfold q
      ring
    _ = q P e ℓ * (1 - q P e ℓ) := by
      rw [binary_time_variance P x hx, hmean]

private lemma disjoint_union_mean_eq_card_weighted_mean {α : Type*} [DecidableEq α]
    (A B : Finset α) (z : α → ℝ) (hdisj : Disjoint A B)
    (hB : ((B.card : ℝ) ≠ 0)) :
    (((A ∪ B).card : ℝ)⁻¹ * ∑ t ∈ A ∪ B, z t) =
      ((A.card : ℝ) / ((A ∪ B).card : ℝ)) *
          ((A.card : ℝ)⁻¹ * ∑ t ∈ A, z t) +
        (1 - ((A.card : ℝ) / ((A ∪ B).card : ℝ))) *
          ((B.card : ℝ)⁻¹ * ∑ t ∈ B, z t) := by
  classical
  let a : ℝ := A.card
  let b : ℝ := B.card
  let ZA : ℝ := ∑ t ∈ A, z t
  let ZB : ℝ := ∑ t ∈ B, z t
  have hsum : ∑ t ∈ A ∪ B, z t = ZA + ZB := by
    simp [ZA, ZB, Finset.sum_union hdisj]
  have hcard : ((A ∪ B).card : ℝ) = a + b := by
    have hnat : (A ∪ B).card = A.card + B.card :=
      Finset.card_union_of_disjoint hdisj
    simp [a, b, hnat]
  have hb : b ≠ 0 := by simpa [b] using hB
  have hbpos : 0 < b := by
    have hBnat : B.card ≠ 0 := by
      exact_mod_cast hB
    dsimp [b]
    exact_mod_cast (Nat.pos_of_ne_zero hBnat)
  have hab : a + b ≠ 0 := by
    intro h
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact_mod_cast (Nat.zero_le A.card)
    linarith
  by_cases ha : a = 0
  · have hAempty : A = ∅ := by
      apply Finset.card_eq_zero.mp
      have : (A.card : ℝ) = 0 := by simpa [a] using ha
      exact Nat.cast_eq_zero.mp this
    have hZA : ZA = 0 := by simp [ZA, hAempty]
    rw [hsum, hcard, hZA, ha]
    simp [hAempty]
    field_simp [hb]
    ring
  · have haA : ((A.card : ℝ) ≠ 0) := by
      simpa [a] using ha
    have hAB : ((A.card : ℝ) + (B.card : ℝ)) ≠ 0 := by
      simpa [a, b] using hab
    rw [hsum, hcard]
    field_simp [haA, hB, hAB]
    simp [a, b, ZA, ZB]
    ring_nf

open Classical in
private lemma TT_middle_filter_eq_S1_EL
    (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) :
    Finset.univ.filter
        (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t) =
      S1_EL P e ℓ := by
  ext t
  simp [S1_EL]

open Classical in
private lemma TT_middle_filter_eq_S0_LE
    (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) :
    Finset.univ.filter
        (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t) =
      S0_LE P e ℓ := by
  ext t
  simp [S0_LE]

set_option linter.flexible false in
open Classical in
private lemma TT_middle_complement_eq_pre_union_post
    (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) :
    Finset.univ.filter
        (fun t => ¬ (AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t)) =
      S0_EL P e ℓ ∪ S1_LE P e ℓ := by
  ext t
  simp [S0_EL, S1_LE, AdoptionDate.le, AdoptionDate.lt]
  constructor
  · intro h
    by_cases hpre : (t : WithTop (Fin T)) < P.A e
    · exact Or.inl hpre
    · have he : P.A e ≤ (t : WithTop (Fin T)) := le_of_not_gt hpre
      exact Or.inr (h he)
  · intro h hmid
    rcases h with hpre | hpost
    · exact False.elim ((not_lt_of_ge hmid) hpre)
    · exact hpost

set_option linter.flexible false in
private lemma TT_disjoint_pre_mid
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} :
    Disjoint (S0_EL P e ℓ) (S1_EL P e ℓ) := by
  rw [Finset.disjoint_left]
  intro t ht0 ht1
  simp [S0_EL, S1_EL, AdoptionDate.le, AdoptionDate.lt] at ht0 ht1
  exact not_lt_of_ge ht1.1 ht0

set_option linter.flexible false in
private lemma TT_disjoint_mid_post
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} :
    Disjoint (S1_EL P e ℓ) (S1_LE P e ℓ) := by
  rw [Finset.disjoint_left]
  intro t htm htp
  simp [S1_EL, S1_LE, AdoptionDate.le, AdoptionDate.lt] at htm htp
  exact not_lt_of_ge htp htm.2

set_option linter.flexible false in
private lemma TT_disjoint_pre_post
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} (hord : P.A e < P.A ℓ) :
    Disjoint (S0_EL P e ℓ) (S1_LE P e ℓ) := by
  rw [Finset.disjoint_left]
  intro t ht0 ht1
  simp [S0_EL, S1_LE, AdoptionDate.le, AdoptionDate.lt] at ht0 ht1
  exact not_lt_of_ge ht1 (lt_trans ht0 hord)

private lemma TT_pre_mid_post_union
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} (_hord : P.A e < P.A ℓ) :
    S0_EL P e ℓ ∪ S1_EL P e ℓ ∪ S1_LE P e ℓ =
      (Finset.univ : Finset (Fin T)) := by
  ext t
  simp [S0_EL, S1_EL, S1_LE, AdoptionDate.le, AdoptionDate.lt]
  by_cases hpre : (t : WithTop (Fin T)) < P.A e
  · simp [hpre]
  · have he : P.A e ≤ (t : WithTop (Fin T)) := le_of_not_gt hpre
    by_cases hmid : (t : WithTop (Fin T)) < P.A ℓ
    · simp [hpre, he, hmid]
    · have hpost : P.A ℓ ≤ (t : WithTop (Fin T)) := le_of_not_gt hmid
      simp [hpre, he, hmid, hpost]

open Classical in
private lemma TT_post_window_card_ne_zero
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} (hℓ : AdoptionDate.isFin (P.A ℓ)) :
    (((S1_LE P e ℓ).card : ℝ) ≠ 0) := by
  cases hA : P.A ℓ with
  | top =>
      exact False.elim (hℓ hA)
  | coe a =>
      have hmem : a ∈ S1_LE P e ℓ := by
        simp [S1_LE, AdoptionDate.le, hA]
      have hpos : 0 < (S1_LE P e ℓ).card :=
        Finset.card_pos.mpr ⟨a, hmem⟩
      exact_mod_cast (ne_of_gt hpos)

set_option linter.flexible false in
private lemma TT_mu_eq_pre_complement_share
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (hℓ : AdoptionDate.isFin (P.A ℓ)) :
    mu P e ℓ =
      ((S0_EL P e ℓ).card : ℝ) /
        (((S0_EL P e ℓ ∪ S1_LE P e ℓ).card : ℝ)) := by
  classical
  let A := S0_EL P e ℓ
  let M := S1_EL P e ℓ
  let B := S1_LE P e ℓ
  have hpre_mid : Disjoint A M := by
    simpa [A, M] using TT_disjoint_pre_mid P (e := e) (ℓ := ℓ)
  have hmid_post : Disjoint M B := by
    simpa [M, B] using TT_disjoint_mid_post P (e := e) (ℓ := ℓ)
  have hpre_post : Disjoint A B := by
    simpa [A, B] using TT_disjoint_pre_post P hord
  have huniv : A ∪ M ∪ B = (Finset.univ : Finset (Fin T)) := by
    simpa [A, M, B] using TT_pre_mid_post_union P hord
  have hAM_B : Disjoint (A ∪ M) B := by
    rw [Finset.disjoint_left]
    intro t ht hb
    rw [Finset.mem_union] at ht
    rcases ht with ht | ht
    · exact (Finset.disjoint_left.mp hpre_post) ht hb
    · exact (Finset.disjoint_left.mp hmid_post) ht hb
  have htreated_e :
      Finset.univ.filter (fun t => AdoptionDate.le (P.A e) t) = M ∪ B := by
    ext t
    simp [M, B, S1_EL, S1_LE, AdoptionDate.le, AdoptionDate.lt]
    constructor
    · intro he
      by_cases hlt : (t : WithTop (Fin T)) < P.A ℓ
      · exact Or.inl ⟨he, hlt⟩
      · exact Or.inr (le_of_not_gt hlt)
    · intro h
      rcases h with h | h
      · exact h.1
      · exact le_trans (le_of_lt hord) h
  have hbar_e : barD P e = (T : ℝ)⁻¹ * ((M ∪ B).card : ℝ) := by
    unfold barD D
    rw [← htreated_e]
    simp
  have hbar_l : barD P ℓ = (T : ℝ)⁻¹ * (B.card : ℝ) := by
    unfold barD D
    simp [B, S1_LE]
  have hMBcard : ((M ∪ B).card : ℝ) = (M.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_union_of_disjoint hmid_post)
  have hABcard : ((A ∪ B).card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_union_of_disjoint hpre_post)
  have hTcard : (T : ℝ) = (A.card : ℝ) + (M.card : ℝ) + (B.card : ℝ) := by
    have hnat : A.card + M.card + B.card = T := by
      calc
        A.card + M.card + B.card = (A ∪ M).card + B.card := by
          rw [Finset.card_union_of_disjoint hpre_mid]
        _ = ((A ∪ M) ∪ B).card := by
          rw [Finset.card_union_of_disjoint hAM_B]
        _ = T := by
          rw [huniv]
          simp
    exact_mod_cast hnat.symm
  have hqM : q P e ℓ = (T : ℝ)⁻¹ * (M.card : ℝ) := by
    unfold q
    rw [hbar_e, hbar_l, hMBcard]
    ring
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hBne : ((B.card : ℝ) ≠ 0) := by
    simpa [B] using TT_post_window_card_ne_zero P (e := e) hℓ
  have hABne : ((A.card : ℝ) + (B.card : ℝ)) ≠ 0 := by
    intro h
    have hb0 : (B.card : ℝ) = 0 := by
      nlinarith [show (0 : ℝ) ≤ (A.card : ℝ) by exact_mod_cast (Nat.zero_le A.card)]
    exact hBne hb0
  unfold mu
  rw [hbar_e, hqM, hMBcard, hABcard, hTcard]
  field_simp [hTne, hABne]
  ring_nf
  simp [A]
  field_simp [hABne]
  ring

/-- TN numerator bridge for `TN_pair_contribution_eq_lambda_delta`: rewrites
the centered treated-vs-never time covariance as the raw TN weight factor times
the two-window DID contrast. -/
private lemma TN_time_cov_eq_lambda_delta_core
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hg : AdoptionDate.isFin (P.A g)) (hu : AdoptionDate.isInf (P.A u)) :
    (T : ℝ)⁻¹ * ∑ t,
      (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) =
      barD P g * (1 - barD P g) * Δ_TN P g u := by
  classical
  let p : Fin T → Prop := fun t => AdoptionDate.le (P.A g) t
  let z : Fin T → ℝ := fun t => P.Y g t - P.Y u t
  have hcov := binary_time_cov_filter_mean P p z
    (by simpa [p] using TN_treated_window_card_ne_zero P hg)
  have hbar :
      ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) = barD P g := by
    unfold p barD D
    rfl
  have hS1 : Finset.univ.filter p = S1_TN P g := by
    ext t
    simp [p, S1_TN]
  have hS0 : Finset.univ.filter (fun t => ¬ p t) = S0_TN P g := by
    simpa [p] using TN_filter_not_treated_eq_S0 P g
  have hdelta :
      (((Finset.univ.filter p).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter p), z t) -
          ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) =
        Δ_TN P g u := by
    rw [hS1, hS0]
    unfold z Δ_TN Ybar
    simp only [Finset.sum_sub_distrib]
    ring
  calc
    (T : ℝ)⁻¹ * ∑ t,
        (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) =
        (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
          ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      rw [TN_centeredD_gap_eq P hu t]
      unfold p z barD D
      ring
    _ = barD P g * (1 - barD P g) * Δ_TN P g u := by
      rw [hcov, hbar, hdelta]

/-- TT numerator bridge for `TT_pair_contribution_eq_lambda_delta_sum`: rewrites
the centered early-late time covariance as the `mu`-weighted EL and LE DID
contrast combination. -/
private lemma TT_time_cov_eq_lambda_delta_core
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (hℓ : AdoptionDate.isFin (P.A ℓ)) :
    (T : ℝ)⁻¹ * ∑ t,
      (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
      q P e ℓ * (1 - q P e ℓ) *
        (mu P e ℓ * Δ_EL P e ℓ + (1 - mu P e ℓ) * Δ_LE P e ℓ) := by
  classical
  let p : Fin T → Prop := fun t =>
    AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t
  let z : Fin T → ℝ := fun t => P.Y e t - P.Y ℓ t
  have hcov := binary_time_cov_filter_mean P p z
    (by simpa [p] using TT_middle_window_card_ne_zero P hord hℓ)
  have hq :
      ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) = q P e ℓ := by
    calc
      (T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0) =
          (T : ℝ)⁻¹ * ∑ t, (D P e t - D P ℓ t) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro t _ht
        rw [TT_D_gap_eq_middle_indicator P hord t]
      _ = q P e ℓ := by
        unfold q barD
        rw [Finset.sum_sub_distrib]
        ring
  have hqbar :
      barD P e - barD P ℓ =
        ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) := by
    rw [hq]
    rfl
  have hdid :
      (((Finset.univ.filter p).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter p), z t) -
          ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) =
        mu P e ℓ * Δ_EL P e ℓ + (1 - mu P e ℓ) * Δ_LE P e ℓ := by
    have hmid1 : Finset.univ.filter p = S1_EL P e ℓ := by
      simpa [p] using TT_middle_filter_eq_S1_EL P e ℓ
    have hmid0 : Finset.univ.filter p = S0_LE P e ℓ := by
      simpa [p] using TT_middle_filter_eq_S0_LE P e ℓ
    have hcomp :
        Finset.univ.filter (fun t => ¬ p t) = S0_EL P e ℓ ∪ S1_LE P e ℓ := by
      simpa [p] using TT_middle_complement_eq_pre_union_post P e ℓ
    have hcomp_mean :=
      disjoint_union_mean_eq_card_weighted_mean (S0_EL P e ℓ) (S1_LE P e ℓ) z
        (TT_disjoint_pre_post P hord) (TT_post_window_card_ne_zero P (e := e) hℓ)
    have hmu := TT_mu_eq_pre_complement_share P hord hℓ
    rw [hmid1, hcomp, hcomp_mean, hmu]
    unfold z Δ_EL Δ_LE Ybar
    rw [← hmid1, ← hmid0]
    simp only [Finset.sum_sub_distrib]
    ring
  calc
    (T : ℝ)⁻¹ * ∑ t,
        (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
        (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
          ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      have hdgap : D P e t - D P ℓ t = if p t then (1 : ℝ) else 0 := by
        rw [TT_D_gap_eq_middle_indicator P hord t]
      calc
        (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
            ((D P e t - D P ℓ t) - (barD P e - barD P ℓ)) *
              (P.Y e t - P.Y ℓ t) := by
          unfold centeredD
          ring
        _ = ((if p t then (1 : ℝ) else 0) -
            ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t := by
          rw [hdgap, hqbar]
    _ = q P e ℓ * (1 - q P e ℓ) *
        (mu P e ℓ * Δ_EL P e ℓ + (1 - mu P e ℓ) * Δ_LE P e ℓ) := by
      rw [hcov, hq, hdid]

/-- TN denominator pair: combining the two ordered pairwise-variance
contributions gives the treated-vs-never raw denominator factor. -/
lemma TN_pair_vd_contribution_eq_gap
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hg : AdoptionDate.isFin (P.A g)) (hu : AdoptionDate.isInf (P.A u)) :
    vdPairContribution P g u + vdPairContribution P u g =
      P.p g * P.p u * q P g u * (1 - q P g u) := by
  rw [vdPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hvar := TN_time_variance_eq_gap P hg hu
  calc
    (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t)^2 =
        P.p g * P.p u *
          ((T : ℝ)⁻¹ * ∑ t, (centeredD P g t - centeredD P u t)^2) := by
      field_simp [hTne]
    _ = P.p g * P.p u * q P g u * (1 - q P g u) := by
      rw [hvar]
      ring

/-- Treated-treated denominator pair: combining the two ordered
pairwise-variance contributions gives the timing-pair raw denominator factor. -/
lemma TT_pair_vd_contribution_eq_gap
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (hℓ : AdoptionDate.isFin (P.A ℓ)) :
    vdPairContribution P e ℓ + vdPairContribution P ℓ e =
      P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) := by
  rw [vdPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hvar := TT_time_variance_eq_gap P hord hℓ
  calc
    (P.p e * P.p ℓ / (T : ℝ)) *
        ∑ t, (centeredD P e t - centeredD P ℓ t)^2 =
        P.p e * P.p ℓ *
          ((T : ℝ)⁻¹ * ∑ t, (centeredD P e t - centeredD P ℓ t)^2) := by
      field_simp [hTne]
    _ = P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) := by
      rw [hvar]
      ring

/-- TN numerator pair: combining the two ordered pairwise-covariance
contributions gives `λ_TN · Δ_TN`. -/
lemma TN_pair_contribution_eq_lambda_delta
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hg : AdoptionDate.isFin (P.A g)) (hu : AdoptionDate.isInf (P.A u)) :
    numPairContribution P g u + numPairContribution P u g =
      lambdaTN P g u * Δ_TN P g u := by
  rw [numPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hcov := TN_time_cov_eq_lambda_delta_core P hg hu
  calc
    (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) =
        P.p g * P.p u *
          ((T : ℝ)⁻¹ * ∑ t,
            (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t)) := by
      field_simp [hTne]
    _ = lambdaTN P g u * Δ_TN P g u := by
      rw [hcov]
      unfold lambdaTN
      ring

/-- Treated-treated numerator pair: combining the two ordered
pairwise-covariance contributions splits into the EL and LE comparison
windows. -/
lemma TT_pair_contribution_eq_lambda_delta_sum
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (hℓ : AdoptionDate.isFin (P.A ℓ)) :
    numPairContribution P e ℓ + numPairContribution P ℓ e =
      lambdaEL P e ℓ * Δ_EL P e ℓ + lambdaLE P e ℓ * Δ_LE P e ℓ := by
  rw [numPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hcov := TT_time_cov_eq_lambda_delta_core P hord hℓ
  calc
    (P.p e * P.p ℓ / (T : ℝ)) *
        ∑ t, (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
        P.p e * P.p ℓ *
          ((T : ℝ)⁻¹ * ∑ t,
            (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t)) := by
      field_simp [hTne]
    _ = lambdaEL P e ℓ * Δ_EL P e ℓ + lambdaLE P e ℓ * Δ_LE P e ℓ := by
      rw [hcov]
      unfold lambdaEL lambdaLE
      ring

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
