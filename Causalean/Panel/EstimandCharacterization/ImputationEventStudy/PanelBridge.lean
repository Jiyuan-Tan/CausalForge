/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Borusyak-Jaravel-Spiess ↔ panel linear-algebra substrate bridge

This file connects the bespoke finite design-matrix algebra of the BJS
imputation setup (`Imputation.lean`) to the shared panel inner-product /
subspace substrate (`Causalean/Panel/Weighted/`).

The OLS imputation estimator is the **uniform-weight** special case of the
panel WLS substrate.  Concretely, the untreated cells carry the uniform
`WeightedSupport` `ω_u ≡ 1/|U|`; with that inner product the BJS "left-null-space
of `Q_U`" condition `∀ r, ∑_u v_u q_{ur} = 0` is exactly `ip`-orthogonality of
`v` to the regressor **column span** `span {u ↦ q_{ur} | r}`.  The keystone
lemma `columnSpan_ip_orthogonal_iff` exposes that equivalence, so the
left-null-space adjustment in `linear_unbiased_of_prediction_identified` can be
phrased through the panel `Subspace` orthogonality vocabulary.
-/

import Causalean.Panel.Weighted.InnerProduct
import Causalean.Panel.Weighted.Subspace
import Causalean.Panel.EstimandCharacterization.ImputationEventStudy.Imputation

/-! # BJS panel-substrate bridge

Provides the uniform untreated-cell `WeightedSupport`, the regressor column maps
into `Untreated → ℝ`, their span, and the bridge identifying the BJS
left-null-space condition with `ip`-orthogonality to that span.  The main public
bridge is `columnSpan_ip_orthogonal_iff`; `exists_imputationWeights_of_gap_orthogonal`
uses it to absorb a left-null-space gap into one target-relevant imputation row.
The file then proves `linear_unbiased_of_prediction_identified` and
`bjs_linear_unbiased_iff_imputation_form`, the linear-unbiased characterization
theorems kept separate from the base finite imputation algebra. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace ImputationEventStudy

open Finset Causalean.Panel.Weighted

noncomputable section

variable {Treated Untreated Regressor : Type*}
  [Fintype Treated] [Fintype Untreated] [Fintype Regressor]

section Bridge

variable [DecidableEq Untreated]

/-- The untreated cells equipped with the **uniform** weighted support
`ω_u ≡ 1/|U|`.  The OLS imputation estimator is the uniform-weight instance of
the panel WLS substrate, so this is the `WeightedSupport` through which BJS
consumes the `ip` / `Subspace` API. -/
def untreatedSupport (Untreated : Type*) [Fintype Untreated] [DecidableEq Untreated]
    [Nonempty Untreated] : WeightedSupport Untreated where
  observed := Finset.univ
  observed_nonempty := Finset.univ_nonempty
  weight := fun _ => (Fintype.card Untreated : ℝ)⁻¹
  weight_pos := by
    intro u _
    positivity
  weight_zero_off := by
    intro u hu
    exact absurd (Finset.mem_univ u) hu
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

namespace BJSPanel

variable (P : BJSPanel Treated Untreated Regressor)

/-- The `r`-th regressor **column** as an array over the untreated cells:
`u ↦ q_{ur}`. -/
def regressorColumn (r : Regressor) : Untreated → ℝ := fun u => P.qU u r

/-- The regressor column span inside `Untreated → ℝ`: the span of all columns
`u ↦ q_{ur}`.  Membership of a treated row's representation in (the analogous
span over `Regressor`) is the BJS row-span condition; orthogonality to *this*
span is the left-null-space condition. -/
def columnSpan : Submodule ℝ (Untreated → ℝ) :=
  Submodule.span ℝ (Set.range P.regressorColumn)

variable [Nonempty Untreated]

/-- The panel inner product of an untreated-cell vector `v` with a regressor
column is the BJS left-null-space sum, rescaled by the uniform weight. -/
lemma ip_untreatedSupport_regressorColumn (v : Untreated → ℝ) (r : Regressor) :
    (untreatedSupport Untreated).ip v (P.regressorColumn r)
      = (Fintype.card Untreated : ℝ)⁻¹ * ∑ u : Untreated, v u * P.qU u r := by
  rw [WeightedSupport.ip_def, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  simp only [untreatedSupport, regressorColumn]
  ring

/-- `ip`-orthogonality to a single regressor column ⟺ that column's BJS
left-null-space coordinate vanishes. -/
lemma ip_regressorColumn_eq_zero_iff (v : Untreated → ℝ) (r : Regressor) :
    (untreatedSupport Untreated).ip v (P.regressorColumn r) = 0
      ↔ ∑ u : Untreated, v u * P.qU u r = 0 := by
  rw [ip_untreatedSupport_regressorColumn]
  rw [mul_eq_zero]
  have hne : (Fintype.card Untreated : ℝ)⁻¹ ≠ 0 := by
    simp [Fintype.card_ne_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hne
    · exact h
  · intro h; exact Or.inr h

/-- **Keystone bridge.**  A vector over the untreated cells is `ip`-orthogonal
to the whole regressor column span iff it satisfies the BJS left-null-space
condition `∀ r, ∑_u v_u q_{ur} = 0`.  This is the panel-substrate restatement of
"`v` lies in the left null space of `Q_U`". -/
lemma columnSpan_ip_orthogonal_iff (v : Untreated → ℝ) :
    (∀ h ∈ P.columnSpan, (untreatedSupport Untreated).ip v h = 0)
      ↔ ∀ r : Regressor, ∑ u : Untreated, v u * P.qU u r = 0 := by
  constructor
  · intro h r
    rw [← ip_regressorColumn_eq_zero_iff]
    exact h (P.regressorColumn r) (Submodule.subset_span ⟨r, rfl⟩)
  · intro h
    have hcol : ∀ r : Regressor,
        (untreatedSupport Untreated).ip v (P.regressorColumn r) = 0 := by
      intro r; rw [ip_regressorColumn_eq_zero_iff]; exact h r
    -- The set of `w` with `ip v w = 0` is a submodule containing every column,
    -- hence contains the whole span.
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro x ⟨r, rfl⟩; exact hcol r
    · simp [WeightedSupport.ip]
    · intro x y _ _ hx hy
      rw [WeightedSupport.ip_add_right, hx, hy, add_zero]
    · intro s x _ hx
      rw [WeightedSupport.ip_smul_right, hx, mul_zero]

/-- **Left-null-space row adjustment (audit M3), phrased through the panel
substrate.**  Given base imputation weights `H0`, a nonzero target weight at
`c0`, and a target untreated-coefficient vector `vU` whose gap
`gap u = vU u + ∑_c a_c · H0.weight c u` is `ip`-orthogonal to the regressor
column span (equivalently: `gap` lies in the left null space of `Q_U`), one
nonzero target row of `H0` can absorb the gap without disturbing any
target-relevant row identity.  The resulting imputation weights `H` represent
the untreated coefficients: `∑_c a_c · H.weight c u = - vU u` for every `u`.

This is the substrate-citizen form of the finite left-null-space construction
formerly inlined in `linear_unbiased_of_prediction_identified`. -/
theorem exists_imputationWeights_of_gap_orthogonal
    (vU : Untreated → ℝ) {c0 : Treated} (hc0 : P.a c0 ≠ 0)
    (H0 : P.ImputationWeights)
    (hgap : ∀ h ∈ P.columnSpan,
      (untreatedSupport Untreated).ip
        (fun u => vU u + ∑ c : Treated, P.a c * H0.weight c u) h = 0) :
    ∃ H : P.ImputationWeights,
      ∀ u : Untreated, (∑ c : Treated, P.a c * H.weight c u) = - vU u := by
  classical
  let weightedUntreated : Untreated → ℝ :=
    fun u => ∑ c : Treated, P.a c * H0.weight c u
  let correction : Untreated → ℝ :=
    fun u => (P.a c0)⁻¹ * (-vU u - weightedUntreated u)
  -- The panel-substrate orthogonality hypothesis unpacks (via the keystone
  -- bridge) to the BJS left-null-space coordinate condition on the gap.
  have hWeightedCombined :
      ∀ r : Regressor,
        ∑ u : Untreated, (vU u + weightedUntreated u) * P.qU u r = 0 :=
    (P.columnSpan_ip_orthogonal_iff _).mp hgap
  have hCorrectionNull :
      ∀ r : Regressor, ∑ u : Untreated, correction u * P.qU u r = 0 := by
    intro r
    have hNeg :
        ∑ u : Untreated, (-vU u - weightedUntreated u) * P.qU u r = 0 := by
      calc
        (∑ u : Untreated, (-vU u - weightedUntreated u) * P.qU u r)
            = -∑ u : Untreated, (vU u + weightedUntreated u) * P.qU u r := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro u _
              ring
        _ = 0 := by rw [hWeightedCombined r, neg_zero]
    calc
      (∑ u : Untreated, correction u * P.qU u r)
          = (P.a c0)⁻¹ *
              ∑ u : Untreated, (-vU u - weightedUntreated u) * P.qU u r := by
            simp only [correction]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            rw [mul_assoc]
      _ = 0 := by rw [hNeg, mul_zero]
  let HWeight : Treated → Untreated → ℝ :=
    fun c u => if c = c0 then H0.weight c u + correction u else H0.weight c u
  have hHWeightSum :
      ∀ u : Untreated, (∑ c : Treated, P.a c * HWeight c u) = -vU u := by
    intro u
    have hUpdate :
        (∑ c : Treated, P.a c * HWeight c u) =
          (∑ c : Treated, P.a c * H0.weight c u) + P.a c0 * correction u := by
      calc
        (∑ c : Treated, P.a c * HWeight c u)
            = ∑ c : Treated,
                (P.a c * H0.weight c u +
                  if c = c0 then P.a c * correction u else 0) := by
              apply Finset.sum_congr rfl
              intro c _
              by_cases hC : c = c0
              · subst c; simp [HWeight]; ring
              · simp [HWeight, hC]
        _ = (∑ c : Treated, P.a c * H0.weight c u) +
              ∑ c : Treated, (if c = c0 then P.a c * correction u else 0) := by
              rw [Finset.sum_add_distrib]
        _ = (∑ c : Treated, P.a c * H0.weight c u) + P.a c0 * correction u := by
              simp
    calc
      (∑ c : Treated, P.a c * HWeight c u)
          = weightedUntreated u + P.a c0 * correction u := by rw [hUpdate]
      _ = weightedUntreated u +
            P.a c0 * ((P.a c0)⁻¹ * (-vU u - weightedUntreated u)) := rfl
      _ = -vU u := by
            rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; ring
  refine ⟨{ weight := HWeight, row_identity := ?_ }, hHWeightSum⟩
  intro c hA r
  by_cases hC : c = c0
  · subst c
    calc
      (∑ u : Untreated, HWeight c0 u * P.qU u r)
          = ∑ u : Untreated, (H0.weight c0 u + correction u) * P.qU u r := by
            simp [HWeight]
      _ = (∑ u : Untreated, H0.weight c0 u * P.qU u r) +
            ∑ u : Untreated, correction u * P.qU u r := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro u _; rw [add_mul]
      _ = P.qT c0 r := by
            rw [H0.row_identity c0 hc0 r, hCorrectionNull r, add_zero]
  · simpa [HWeight, hC] using H0.row_identity c hA r

end BJSPanel

end Bridge

/-! ## BJS linear-unbiased characterization, consuming the panel substrate

The two characterization theorems formerly inlined in `Imputation.lean`.  They
live here so the source-strength direction
`linear_unbiased_of_prediction_identified` can consume the substrate-based
left-null-space lemma `exists_imputationWeights_of_gap_orthogonal`.  Their
statements are byte-for-byte the originals — `DecidableEq Untreated` is obtained
internally via `Classical.decEq`, so the public signatures are unchanged. -/

namespace BJSPanel

variable (P : BJSPanel Treated Untreated Regressor)

/-- BJS linear-unbiased representation from the primitive prediction-span
condition.

This is the finite left-null-space adjustment step from the source proof.  It
starts with any valid row-span imputation matrix `H0`; nuisance unbiasedness
implies the untreated-coefficient gap lies in the left null space of the
untreated regressor rows.  The adjustment that absorbs that gap into one nonzero
target-weight row is `exists_imputationWeights_of_gap_orthogonal`, which phrases
the left-null-space condition as `ip`-orthogonality to the regressor column span
in the panel `WeightedSupport`/`Subspace` substrate. -/
theorem linear_unbiased_of_prediction_identified
    (L : P.LinearEstimator)
    (hUnbiasedForAllTau : L.unbiasedForAllTau)
    (hPredictionSpan : P.PredictionIdentified)
    (hNonzeroTargetWeight : ∃ c : Treated, P.a c ≠ 0) :
    ∃ H : P.ImputationWeights,
      (∀ c : Treated, L.vT c = P.a c) ∧
        (∀ u : Untreated, L.vU u = - ∑ c : Treated, P.a c * H.weight c u) ∧
          (∀ (YT : Treated → ℝ) (YU : Untreated → ℝ),
            L.value YT YU =
              ∑ c : Treated, P.a c *
                (YT c - ∑ u : Untreated, H.weight c u * YU u)) ∧
            L.observedValue = P.psiImp H.weight := by
  classical
  haveI : DecidableEq Untreated := Classical.decEq Untreated
  let H0 : P.ImputationWeights := Classical.choice hPredictionSpan
  rcases hNonzeroTargetWeight with ⟨c0, hc0⟩
  have hVT : ∀ c : Treated, L.vT c = P.a c := by
    intro c
    have h := hUnbiasedForAllTau (fun _ : Regressor => 0)
      (fun d : Treated => if d = c then (1 : ℝ) else 0)
    simpa [LinearEstimator.modelValue, LinearEstimator.value, targetForTau, dot] using h
  let weightedUntreated : Untreated → ℝ :=
    fun u => ∑ c : Treated, P.a c * H0.weight c u
  have hNuisanceCoord :
      ∀ r : Regressor,
        (∑ c : Treated, P.a c * P.qT c r) +
          ∑ u : Untreated, L.vU u * P.qU u r = 0 := by
    intro r
    let beta : Regressor → ℝ := fun r' => if r' = r then (1 : ℝ) else 0
    have h := hUnbiasedForAllTau beta (fun _ : Treated => 0)
    simpa [LinearEstimator.modelValue, LinearEstimator.value, targetForTau,
      dot, beta, hVT] using h
  have hH0Aggregate :
      ∀ r : Regressor,
        (∑ c : Treated, P.a c * P.qT c r) =
          ∑ u : Untreated, weightedUntreated u * P.qU u r := by
    intro r
    calc
      (∑ c : Treated, P.a c * P.qT c r)
          = ∑ c : Treated,
              P.a c * ∑ u : Untreated, H0.weight c u * P.qU u r := by
              apply Finset.sum_congr rfl
              intro c hc
              by_cases hA : P.a c = 0
              · simp [hA]
              · rw [H0.row_identity c hA r]
      _ = ∑ c : Treated, ∑ u : Untreated,
              P.a c * (H0.weight c u * P.qU u r) := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [Finset.mul_sum]
      _ = ∑ u : Untreated, ∑ c : Treated,
              P.a c * (H0.weight c u * P.qU u r) := by
              rw [Finset.sum_comm]
      _ = ∑ u : Untreated, weightedUntreated u * P.qU u r := by
              apply Finset.sum_congr rfl
              intro u hu
              unfold weightedUntreated
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro c hc
              rw [mul_assoc]
  have hWeightedCombined :
      ∀ r : Regressor,
        ∑ u : Untreated, (L.vU u + weightedUntreated u) * P.qU u r = 0 := by
    intro r
    have hN := hNuisanceCoord r
    rw [hH0Aggregate r] at hN
    calc
      (∑ u : Untreated, (L.vU u + weightedUntreated u) * P.qU u r)
          = (∑ u : Untreated, L.vU u * P.qU u r) +
              ∑ u : Untreated, weightedUntreated u * P.qU u r := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro u hu
              rw [add_mul]
      _ = (∑ u : Untreated, weightedUntreated u * P.qU u r) +
            ∑ u : Untreated, L.vU u * P.qU u r := by
            rw [add_comm]
      _ = 0 := hN
  -- With no untreated cells the imputation representation is vacuous on the
  -- untreated coordinates; otherwise route the gap through the panel substrate.
  rcases isEmpty_or_nonempty Untreated with hEmpty | hNE
  · have hWitness : L.HasImputationRepresentation :=
      { weights := H0
        untreated_weight_representation := by
          intro u; exact (hEmpty.false u).elim }
    exact linear_unbiased_of_imputation_representation P L hUnbiasedForAllTau hWitness
  · have hgap : ∀ h ∈ P.columnSpan,
        (untreatedSupport Untreated).ip
          (fun u => L.vU u + ∑ c : Treated, P.a c * H0.weight c u) h = 0 := by
      rw [P.columnSpan_ip_orthogonal_iff]
      intro r
      exact hWeightedCombined r
    obtain ⟨H, hHsum⟩ :=
      P.exists_imputationWeights_of_gap_orthogonal L.vU hc0 H0 hgap
    have hWitness : L.HasImputationRepresentation :=
      { weights := H
        untreated_weight_representation := by
          intro u; rw [hHsum u]; ring }
    exact linear_unbiased_of_imputation_representation P L hUnbiasedForAllTau hWitness

/-- Combined iff characterization of the BJS linear-unbiased imputation class.

This assembles the two directions of
`prop:po-estimand-bjs-linear-unbiased-imputation` (identification half only;
see the efficiency note in `Imputation.lean`):

- (⟹) Every linear unbiased estimator has the BJS imputation form
  (`linear_unbiased_of_prediction_identified`).
- (⟸) Every estimator that has the imputation form is unbiased for `theta`
  (`bjs_imputation_identification`).

Together they state: under `PredictionIdentified` and a nonzero target weight,
a linear estimator `L` is unbiased for every `tau` if and only if it is
representable as a BJS imputation estimator. -/
theorem bjs_linear_unbiased_iff_imputation_form
    (L : P.LinearEstimator)
    (hPredictionSpan : P.PredictionIdentified)
    (hNonzeroTargetWeight : ∃ c : Treated, P.a c ≠ 0) :
    L.unbiasedForAllTau ↔
      ∃ H : P.ImputationWeights,
        (∀ c : Treated, L.vT c = P.a c) ∧
          (∀ u : Untreated, L.vU u = - ∑ c : Treated, P.a c * H.weight c u) ∧
            (∀ (YT : Treated → ℝ) (YU : Untreated → ℝ),
              L.value YT YU =
                ∑ c : Treated, P.a c *
                  (YT c - ∑ u : Untreated, H.weight c u * YU u)) ∧
              L.observedValue = P.psiImp H.weight := by
  constructor
  · -- (⟹) linear unbiasedness ⟹ imputation form
    intro hUnbiased
    exact linear_unbiased_of_prediction_identified P L hUnbiased hPredictionSpan
      hNonzeroTargetWeight
  · -- (⟸) imputation form ⟹ linear unbiasedness for every (beta, tau')
    intro ⟨H, hVT, hVU, hValue, _⟩ beta tau'
    simp only [LinearEstimator.modelValue]
    rw [hValue]
    unfold targetForTau
    apply Finset.sum_congr rfl
    intro c _
    by_cases hA : P.a c = 0
    · simp [hA]
    · have hRowId : ∀ r : Regressor,
          ∑ u : Untreated, H.weight c u * P.qU u r = P.qT c r :=
        H.row_identity c hA
      have hImpute :
          (∑ u : Untreated, H.weight c u * dot (P.qU u) beta) =
            dot (P.qT c) beta := by
        unfold dot
        calc
          (∑ u : Untreated, H.weight c u * ∑ r : Regressor, P.qU u r * beta r)
              = ∑ u : Untreated, ∑ r : Regressor,
                  (H.weight c u * P.qU u r) * beta r := by
                  apply Finset.sum_congr rfl
                  intro u _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro r _
                  rw [mul_assoc]
          _ = ∑ r : Regressor, ∑ u : Untreated,
                (H.weight c u * P.qU u r) * beta r := by
                rw [Finset.sum_comm]
          _ = ∑ r : Regressor,
                (∑ u : Untreated, H.weight c u * P.qU u r) * beta r := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.sum_mul]
          _ = ∑ r : Regressor, P.qT c r * beta r := by
                apply Finset.sum_congr rfl
                intro r _
                rw [hRowId r]
      rw [hImpute]
      ring

end BJSPanel

end

end ImputationEventStudy
end Panel.EstimandCharacterization
end Causalean
