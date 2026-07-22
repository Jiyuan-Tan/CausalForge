/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bridge: localized regime ⇒ `LocalEmpProcessModulus`

This bridge discharges the `LocalEmpProcessModulus` hypothesis used by
`OrthogonalLearning/OracleInequality.lean` from a **localized regime**, i.e. from
data-generating assumptions that admit a sub-root upper envelope on the local
Rademacher complexity of the centred loss class.

Sibling: `Causalean/Estimation/OrthogonalLearning/LocalEmpProcess/Rademacher.lean` realises the same predicate
under a global Rademacher bound. Downstream callers pick
whichever bridge fits the problem at hand; the localized version
includes a countable-class critical-radius bridge for settings where the
`‖θ−θ₀‖` slot of the modulus inequality matters.

References:
* Foster, Syrgkanis, *Orthogonal statistical learning*, Ann. Statist.
  51 (2023) 879–908, Lemma 14 / Lemma 29 (the localized rate `O(δ_n)`
  with critical radius `δ_n`).
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Theorem 3.3.

## Output

The file provides three bridge families.

* `localEmpProcessModulus_of_localized_bounded` and its a.e. analogue give a
  low-hypothesis fallback with the conservative deterministic envelope
  `ρ n := √(2 · b)`.
* `localEmpProcessModulus_of_localized_sharp` gives the countable-class
  Foster-Syrgkanis critical-radius envelope
  `ρ n := (8 · L + 3) · criticalRadius (ψ |B(n)|)` on nonempty fold-B samples.
* `localEmpProcessModulus_of_localized_sharp_ae` obtains the same sharp envelope
  from an a.e. centred-loss bound by clamping the centred loss on a conull set
  and transferring the event back to the original system.

## Headline schema

```
theorem localEmpProcessModulus_of_localized
    (S : LearningSystem Ω μ Z P_Z Θ G) (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid) (g : G)
    {ψ : ℕ → ℝ → ℝ} {b : ℝ}
    (hreg : LocalizedRademacherRegime S S_iid split g idx norm ψ b)
    (hpop_center : ∀ θ ∈ S.Θ_set, |S.L θ g - S.L S.θ₀ g| ≤ b)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun _n => Real.sqrt (2 * b)) δ g
```
-/

import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Local
import Causalean.Stat.Concentration.UniformDeviation.UniformDeviationLocalized
import Causalean.Stat.Concentration.UniformDeviation.CriticalRadius
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # Localized Rademacher Modulus

This file derives `LocalEmpProcessModulus` from localized Rademacher regimes for
orthogonal statistical learning. `LocalizedRademacherRegime` and
`LocalizedRademacherRegimeAE` package pointwise and a.e. centred-loss envelopes,
sub-root complexity envelopes, and population Rademacher bounds.
`localEmpProcessModulus_of_localized_bounded` provides a constant-rate fallback,
`localEmpProcessModulus_of_localized_sharp` provides the countable-class
critical-radius bridge, `localEmpProcessModulus_of_localized_sharp_ae` transfers
that bridge through an a.e. clamping argument, and
`localEmpProcessModulus_of_localized_singleton` covers the degenerate singleton
target class.
-/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
  Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

private lemma foldB_pi_law_localized [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid) (n : ℕ) :
    μ.map (fun ω (i : split.foldB n) => S_iid.Z i ω) =
      Measure.pi (fun _ : split.foldB n => P_Z) :=
  Causalean.Stat.oneShot_iid S_iid split n

/-- **Localized regime predicate for a `LearningSystem`.**

For a fixed nuisance `g`, viewed as a centred loss class on `Z` indexed
by a countable dense sequence `idx : ℕ → S.Θ_set`:

* `0 ≤ b` and `|ℓ z θ g − ℓ z θ₀ g| ≤ b` uniformly over `Θ_set` —
  the boundedness needed by McDiarmid.
* `SubRoot ψ` — the sub-root condition on the population complexity
  envelope.
* `RademacherUpperBound` — `ψ` upper-bounds the population Rademacher
  complexity of the centred loss class (zero-out `starHull` form) on a
  fold-B-sized sample drawn from `P_Z`, uniformly in `n`.

The Lipschitz control `norm F_θ ≤ L · ‖θ − θ₀‖` of the centred loss class
is **NOT** part of the regime; it is consumed only by the sharp bridge
`localEmpProcessModulus_of_localized_sharp` as a separate explicit
`(L : ℝ) (hL_nonneg) (hF_lip)` triple. The bounded fallback bridge does
not need it.

The `idx` parameter mirrors the global-Rademacher bridge
(`localEmpProcessModulus_of_bounded_rademacher`): FoML's symmetrization and
McDiarmid headlines need a countable index, while `S.Θ_set` is typically
uncountable. The bridge theorem lifts from the `ℕ`-indexed sup back to a
`↥S.Θ_set` sup via `separableSpaceSup_eq_real`.

The `norm` parameter is the choice of function-space norm (e.g. the
sup-norm or the population L²-norm) that the localization in
`RademacherUpperBound` is taken in. Downstream callers pick whichever
matches their critical-radius envelope `ψ`. -/
def LocalizedRademacherRegime
    (S : LearningSystem Ω μ Z P_Z Θ G) (_S_iid : IIDSample Ω Z μ P_Z)
    (_split : OneShotSplit _S_iid) (g : G)
    (idx : ℕ → S.Θ_set)
    (norm : (Z → ℝ) → ℝ)
    (ψ : ℕ → ℝ → ℝ) (b : ℝ) : Prop :=
  0 ≤ b ∧
    (∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b) ∧
    (∀ n, SubRoot (ψ n)) ∧
    ∀ n : ℕ,
      RademacherUpperBound
        (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) (_split.foldB n).card (ψ (_split.foldB n).card)

/-- **Almost-everywhere localized regime predicate for a `LearningSystem`.**

This is the satisfiable analogue of `LocalizedRademacherRegime`: the centred-loss
envelope is required only under the population law. The sub-root and
Rademacher-envelope fields are unchanged. -/
def LocalizedRademacherRegimeAE
    (S : LearningSystem Ω μ Z P_Z Θ G) (_S_iid : IIDSample Ω Z μ P_Z)
    (_split : OneShotSplit _S_iid) (g : G)
    (idx : ℕ → S.Θ_set)
    (norm : (Z → ℝ) → ℝ)
    (ψ : ℕ → ℝ → ℝ) (b : ℝ) : Prop :=
  0 ≤ b ∧
    (∀ᵐ z ∂P_Z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b) ∧
    (∀ n, SubRoot (ψ n)) ∧
    ∀ n : ℕ,
      RademacherUpperBound
        (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) (_split.foldB n).card (ψ (_split.foldB n).card)

private lemma empRiskFoldB_centered_abs_le
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (hbound : ∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b)
    (n : ℕ) (ω : Ω) {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |empRiskFoldB S S_iid split n ω θ g
        - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b := by
  classical
  by_cases hm0 : (split.foldB n).card = 0
  · have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
    simp [empRiskFoldB, hfold_empty, hb]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    have hm_pos : 0 < ((split.foldB n).card : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    have hcenter :
        empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g =
          ((split.foldB n).card : ℝ)⁻¹ *
            ∑ i ∈ split.foldB n,
              (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
      simp [empRiskFoldB]
      ring
    rw [hcenter]
    calc
      |((split.foldB n).card : ℝ)⁻¹ *
          ∑ i ∈ split.foldB n,
            (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)|
          = ((split.foldB n).card : ℝ)⁻¹ *
              |∑ i ∈ split.foldB n,
                (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)| := by
            rw [abs_mul, abs_of_nonneg]
            exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ ((split.foldB n).card : ℝ)⁻¹ * (∑ _i ∈ split.foldB n, b) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                (Finset.sum_le_sum fun i _hi => hbound (S_iid.Z i ω) θ hθ)
            · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ = b := by
            simp
            field_simp [ne_of_gt hm_pos]

private lemma empRiskFoldB_centered_abs_le_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (n : ℕ) (ω : Ω)
    (hω : ∀ i ∈ split.foldB n, ∀ θ ∈ S.Θ_set,
      |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |empRiskFoldB S S_iid split n ω θ g
        - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b := by
  classical
  by_cases hm0 : (split.foldB n).card = 0
  · have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
    simp [empRiskFoldB, hfold_empty, hb]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    have hm_pos : 0 < ((split.foldB n).card : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    have hcenter :
        empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g =
          ((split.foldB n).card : ℝ)⁻¹ *
            ∑ i ∈ split.foldB n,
              (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
      simp [empRiskFoldB]
      ring
    rw [hcenter]
    calc
      |((split.foldB n).card : ℝ)⁻¹ *
          ∑ i ∈ split.foldB n,
            (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)|
          = ((split.foldB n).card : ℝ)⁻¹ *
              |∑ i ∈ split.foldB n,
                (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)| := by
            rw [abs_mul, abs_of_nonneg]
            exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ ((split.foldB n).card : ℝ)⁻¹ * (∑ _i ∈ split.foldB n, b) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                (Finset.sum_le_sum fun i hi => hω i hi θ hθ)
            · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ = b := by
            simp
            field_simp [ne_of_gt hm_pos]

/-- **Uniform-bound fallback bridge.**

Under an `LocalizedRademacherRegime` and an explicit centred population-risk
bound, the `LocalEmpProcessModulus` predicate holds with the
conservative envelope `ρ n := √(2 · b)`.

This bridge is a **legitimate low-hypothesis option**: it does NOT use
the sub-root envelope `ψ`, the critical radius, the Lipschitz field, or
any concentration step. It only consumes the uniform centred bound
`b` from the regime plus the population-side bound `hpop_center`.
Useful when the caller has not (yet) supplied the critical-radius /
Rademacher integrability machinery required by
`localEmpProcessModulus_of_localized_sharp`, but already knows that the
centred loss is uniformly bounded.

The rate `ρ n := √(2 · b)` is a *constant* in `n`, so this version does
NOT recover the Foster–Syrgkanis Lemma 29 rate. Use the sharp variant
when the problem at hand admits a critical radius.

**Hypotheses.** `[IsProbabilityMeasure μ]` is needed for the
`μ E ≥ 1 - ENNReal.ofReal δ` event-mass bound. The additional
`hpop_center` hypothesis records the population counterpart of the
pointwise centred-loss bound in `hreg`; it is necessary here because the
raw losses need not be integrable from the centred pointwise bound
alone. -/
theorem localEmpProcessModulus_of_localized_bounded
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set]
    (g : G)
    (idx : ℕ → S.Θ_set)
    {norm : (Z → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ} {b : ℝ}
    (hreg : LocalizedRademacherRegime S S_iid split g idx norm ψ b)
    (hpop_center : ∀ θ ∈ S.Θ_set, |S.L θ g - S.L S.θ₀ g| ≤ b)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun _n => Real.sqrt (2 * b)) δ g := by
  intro n
  classical
  obtain ⟨hb, hbound, _hsub, _hub⟩ := hreg
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · rw [measure_univ]
    exact tsub_le_self
  · intro ω _ θ hθ
    have hpop_abs : |S.L θ g - S.L S.θ₀ g| ≤ b := hpop_center θ hθ
    have hemp_abs :
        |empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b :=
      empRiskFoldB_centered_abs_le S S_iid split hb hbound n ω hθ
    have hmain :
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g) ≤ 2 * b := by
      have hpop_le : S.L θ g - S.L S.θ₀ g ≤ b :=
        (le_abs_self _).trans hpop_abs
      have hemp_ge :
          -b ≤ empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g :=
        (abs_le.mp hemp_abs).1
      linarith
    have hρsq :
        (Real.sqrt (2 * b)) ^ 2 = 2 * b := by
      rw [Real.sq_sqrt]
      nlinarith
    have hρ_nonneg : 0 ≤ Real.sqrt (2 * b) := Real.sqrt_nonneg _
    have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
    calc
      (S.L θ g - S.L S.θ₀ g)
          - (empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g)
          ≤ 2 * b := hmain
      _ = (Real.sqrt (2 * b)) ^ 2 := hρsq.symm
      _ ≤ Real.sqrt (2 * b) * ‖θ - S.θ₀‖ + (Real.sqrt (2 * b)) ^ 2 := by
        nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]

/-- **Almost-everywhere uniform-bound fallback bridge.**

This is the a.e. analogue of
`localEmpProcessModulus_of_localized_bounded`. The event is the conull fold-B
sample event on which the centred-loss envelope holds at every estimation-fold
sample point. -/
theorem localEmpProcessModulus_of_localized_bounded_ae
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set]
    (g : G)
    (idx : ℕ → S.Θ_set)
    {norm : (Z → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ} {b : ℝ}
    (hreg : LocalizedRademacherRegimeAE S S_iid split g idx norm ψ b)
    (hpop_center : ∀ θ ∈ S.Θ_set, |S.L θ g - S.L S.θ₀ g| ≤ b)
    {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun _n => Real.sqrt (2 * b)) δ g := by
  intro n
  classical
  obtain ⟨hb, hbound_ae, _hsub, _hub⟩ := hreg
  let Gn : Set Ω :=
    {ω | ∀ i ∈ split.foldB n, ∀ θ ∈ S.Θ_set,
      |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b}
  have hsample_all_ae : ∀ i : ℕ, ∀ᵐ ω ∂μ,
      ∀ θ ∈ S.Θ_set,
        |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b := by
    intro i
    have hlaw_i : μ.map (S_iid.Z i) = P_Z := by
      rw [← (S_iid.identDist i).map_eq, S_iid.law]
    have hmap : ∀ᵐ z ∂μ.map (S_iid.Z i),
        ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b := by
      simpa [hlaw_i] using hbound_ae
    exact ae_of_ae_map (S_iid.meas i).aemeasurable hmap
  have hGn_ae : ∀ᵐ ω ∂μ, ω ∈ Gn := by
    have hfin : ∀ᵐ ω ∂μ, ∀ i ∈ split.foldB n,
        ∀ θ ∈ S.Θ_set,
          |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b := by
      simpa using (Finset.eventually_all (split.foldB n)).2
        (fun i _hi => hsample_all_ae i)
    simpa [Gn] using hfin
  have hGn_null : μ Gnᶜ = 0 := ae_iff.mp hGn_ae
  rcases exists_measurable_superset_of_null hGn_null with
    ⟨N, hGn_compl_subset_N, hN_meas, hN_null⟩
  refine ⟨Set.univ \ N, MeasurableSet.univ.diff hN_meas, ?_, ?_⟩
  · rw [measure_diff_null hN_null, measure_univ]
    exact tsub_le_self
  · intro ω hω θ hθ
    have hωG : ω ∈ Gn := by
      by_contra hnot
      exact hω.2 (hGn_compl_subset_N hnot)
    have hpop_abs : |S.L θ g - S.L S.θ₀ g| ≤ b := hpop_center θ hθ
    have hemp_abs :
        |empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b :=
      empRiskFoldB_centered_abs_le_ae S S_iid split hb n ω
        (by simpa [Gn] using hωG) hθ
    have hmain :
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g) ≤ 2 * b := by
      have hpop_le : S.L θ g - S.L S.θ₀ g ≤ b :=
        (le_abs_self _).trans hpop_abs
      have hemp_ge :
          -b ≤ empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g :=
        (abs_le.mp hemp_abs).1
      linarith
    have hρsq :
        (Real.sqrt (2 * b)) ^ 2 = 2 * b := by
      rw [Real.sq_sqrt]
      nlinarith
    have hρ_nonneg : 0 ≤ Real.sqrt (2 * b) := Real.sqrt_nonneg _
    have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
    calc
      (S.L θ g - S.L S.θ₀ g)
          - (empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g)
          ≤ 2 * b := hmain
      _ = (Real.sqrt (2 * b)) ^ 2 := hρsq.symm
      _ ≤ Real.sqrt (2 * b) * ‖θ - S.θ₀‖ + (Real.sqrt (2 * b)) ^ 2 := by
        nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]

/-- The target minimizes the auxiliary population risk whose centered excess
loss has been clamped to radius `b`.

This is the minimizer condition needed when an a.e.-bounded empirical-process
proof replaces the original centered loss by
`ℓ(θ₀, g₀) + clamp(ℓ(θ, g₀) − ℓ(θ₀, g₀))`. -/
def CenteredClampedThetaMinimizes
    (S : LearningSystem Ω μ Z P_Z Θ G) (b : ℝ) : Prop :=
  ∀ θ ∈ S.Θ_set,
    ∫ z, S.ℓ z S.θ₀ S.g₀
        + max (-b) (min b (S.ℓ z S.θ₀ S.g₀ - S.ℓ z S.θ₀ S.g₀)) ∂P_Z
      ≤
    ∫ z, S.ℓ z S.θ₀ S.g₀
        + max (-b) (min b (S.ℓ z θ S.g₀ - S.ℓ z S.θ₀ S.g₀)) ∂P_Z

/-- **Localized critical-radius modulus, countable-class Foster–Syrgkanis form.**

Under an `LocalizedRademacherRegime` carrying

* a uniform centred-loss bound `b`,
* a countable target class with a dense indexing sequence,
* a Lipschitz constant `L` for the centred loss class in the chosen
  function-space norm (`norm F_θ ≤ L · ‖θ − θ₀‖`),
* a sub-root upper envelope `ψ` on the population Rademacher complexity
  of the centred loss class on a fold-B-sized sample,

`LocalEmpProcessModulus` holds with the localized empirical-process envelope

    ρ n := (8 · L + 3) · criticalRadius (ψ |B(n)|)

(falling back to the deterministic bound `√(2 · b)` when the fold-B
sample is empty, an artefact of the formalization). This countable-class
formalization has the critical-radius envelope that gives the
Foster-Syrgkanis-style localized rate, in contrast to the bounded fallback
`localEmpProcessModulus_of_localized_bounded` which is constant in `n`.

The hypothesis `hδ_dom` (the FS Lemma 29 lower-bound condition on the
critical radius) absorbs the McDiarmid concentration slack
`b · √(2 log(1/δ) / m)` into the `(criticalRadius ψ_m)²` term, which
matches FS Lemma 29's stipulation
`δ_n = Ω(√((d log log n + log(1/ζ)) / n))`.

Proof outline (peeling + bridge + concentration):

1. **Fold-B re-indexing** transports `localized_uniform_deviation`'s
   `(Fin m → Z)`-event to a `μ`-event on `Ω` via `oneShot_iid`.

2. **Dyadic peeling** over `‖θ − θ₀‖`-shells lifts the per-radius bound
   `4 r δ_n + b · √(2 log(1/δ_k)/m)` from `localized_uniform_deviation`
   to a uniform-over-θ statement of shape
   `8 L δ_n · ‖θ − θ₀‖ + 4 δ_n² + b · √(2 log(K/δ)/m)`,
   where `K` is the number of dyadic shells (controlled by the diameter
   `Rmax`). The Lipschitz field `L` of `LocalizedRademacherRegime` provides
   `norm F_θ ≤ L · ‖θ − θ₀‖`, so each `θ` falls in a level whose
   localization radius is at most `2 L · ‖θ − θ₀‖`.

3. **Critical-radius absorption.** Hypothesis `hδ_dom` rewrites the
   McDiarmid slack as a sub-`δ_n²` term, yielding the clean
   `8 L δ_n · ‖θ − θ₀‖ + 5 δ_n²` envelope.

4. **Modulus packaging** chooses `ρ n := (8 L + 3) · δ_n` so that
   `ρ ‖θ − θ₀‖ + ρ² ≥ 8 L δ_n · ‖θ − θ₀‖ + δ_n²`, dominating the
   peeled bound.

The bounded fallback `localEmpProcessModulus_of_localized_bounded`
(above) is kept as a low-hypothesis option for callers that lack the
critical-radius / Rademacher-integrability machinery. -/
theorem localEmpProcessModulus_of_localized_sharp
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set] [Countable S.Θ_set]
    (g : G)
    (_hg_cont : ∀ z, Continuous fun (θ : S.Θ_set) => S.ℓ z θ.val g)
    (idx : ℕ → S.Θ_set)
    (_idx_dense : DenseRange idx)
    {norm : (Z → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ} {b L Rmax : ℝ}
    (hreg : LocalizedRademacherRegime S S_iid split g idx norm ψ b)
    (hL_nonneg : 0 ≤ L)
    (hF_lip : ∀ θ ∈ S.Θ_set,
      norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) ≤ L * ‖θ - S.θ₀‖)
    (hℓ_meas : ∀ θ ∈ S.Θ_set, Measurable (fun z => S.ℓ z θ g))
    (hℓ_int : ∀ θ ∈ S.Θ_set, Integrable (fun z => S.ℓ z θ g) P_Z)
    (hF_diam : ∀ θ ∈ S.Θ_set,
      norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) ≤ Rmax)
    -- n-dependent critical-radius hypotheses (ψ m is the envelope at sample size m).
    (hRmax_lb : ∀ m : ℕ, criticalRadius (ψ m) ≤ Rmax)
    (hcrit_pos : ∀ m : ℕ, 0 < criticalRadius (ψ m))
    (hcrit_fp : ∀ m : ℕ, ψ m (criticalRadius (ψ m)) ≤ (criticalRadius (ψ m)) ^ 2)
    (hψ_ub : ∀ m : ℕ,
      RademacherUpperBound
        (fun (θ : S.Θ_set) (z : Z) => S.ℓ z θ.val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) m (ψ m))
    -- BddAbove hypothesis needed by the bridge lemma inside `localized_uniform_deviation`.
    (hrad_bdd : ∀ m r, ∀ S_fin : Fin m → Z, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam S.Θ_set =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut
            (fun (θ : S.Θ_set) (z : Z) => S.ℓ z θ.val g - S.ℓ z S.θ₀ g)
            norm r p (S_fin k)|))
    -- Integrability of the upper empirical Rademacher process; consumed by the
    -- bridge lemma inside `localized_uniform_deviation`.
    (hrad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              (fun (θ : S.Θ_set) (z : Z) => S.ℓ z θ.val g - S.ℓ z S.θ₀ g)
              norm r) ((id : Z → Z) ∘ ω))
        (Measure.pi (fun _ => P_Z)))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    -- Foster–Syrgkanis Lemma 29 critical-radius lower bound (peeling-aware):
    -- for any dyadic shell count `K` covering `Rmax`, the McDiarmid slack at
    -- the union-bound-adjusted confidence `δ / (2 (K + 1))` is dominated by
    -- the squared critical radius. The `K + 1` accounts for the union over
    -- `K + 1` dyadic shells in the peeling argument; the factor `2` keeps the
    -- intersection event mass `≥ 1 − δ` strictly. This absorbs every
    -- `b · √(log(·)/m)` term into the `δ_n²` part of the modulus inequality.
    (hδ_dom : ∀ n K : ℕ, 0 < (split.foldB n).card →
      Rmax ≤ (criticalRadius (ψ (split.foldB n).card)) * (2 : ℝ) ^ K →
      b * Real.sqrt
          (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / (split.foldB n).card)
        ≤ (criticalRadius (ψ (split.foldB n).card)) ^ 2) :
    LocalEmpProcessModulus S S_iid split
      (fun n =>
        if (split.foldB n).card = 0 then Real.sqrt (2 * b)
        else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) δ g := by
  intro n
  classical
  obtain ⟨hb, hbound, hsub, _hub_idx⟩ := hreg
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  by_cases hm0 : (split.foldB n).card = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ θ hθ
      have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
      have hcenter_int :
          Integrable (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) P_Z :=
        (hℓ_int θ hθ).sub (hℓ_int S.θ₀ S.θ₀_mem)
      have hmean_eq :
          (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
            S.L θ g - S.L S.θ₀ g := by
        change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
          (∫ z, S.ℓ z θ g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
        exact integral_sub (hℓ_int θ hθ) (hℓ_int S.θ₀ S.θ₀_mem)
      have hpop_abs : |S.L θ g - S.L S.θ₀ g| ≤ b := by
        rw [← hmean_eq]
        calc
          |∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z|
              ≤ ∫ z, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ∂P_Z :=
                abs_integral_le_integral_abs
          _ ≤ ∫ _z, b ∂P_Z := by
                apply integral_mono
                · exact hcenter_int.abs
                · exact integrable_const b
                · intro z
                  exact hbound z θ hθ
          _ = b := by simp
      have hρsq :
          (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
           else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 =
            2 * b := by
        rw [if_pos hm0, Real.sq_sqrt]
        nlinarith
      have hρ_nonneg :
          0 ≤
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) := by
        rw [if_pos hm0]
        exact Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
      calc
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
            = S.L θ g - S.L S.θ₀ g := by
                simp [empRiskFoldB, hfold_empty]
        _ ≤ b := (le_abs_self _).trans hpop_abs
        _ ≤ 2 * b := by nlinarith
        _ =
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 :=
              hρsq.symm
        _ ≤
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) *
              ‖θ - S.θ₀‖
              +
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 := by
              nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    let m : ℕ := (split.foldB n).card
    let δn : ℝ := criticalRadius (ψ m)
    haveI : Nonempty Z := nonempty_of_isProbabilityMeasure P_Z
    let F : S.Θ_set → Z → ℝ :=
      fun θ z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g
    have hF_meas_full : ∀ θ : S.Θ_set, Measurable (F θ) := by
      intro θ
      exact (hℓ_meas θ.val θ.property).sub (hℓ_meas S.θ₀ S.θ₀_mem)
    let Rloc : LocalizedRegime Z S.Θ_set Z F norm P_Z (id : Z → Z) :=
      { b := b
        b_nonneg := hb
        bound := by
          intro θ z
          exact hbound z θ.val θ.property
        ψ := ψ
        ψ_subRoot := hsub
        ψ_ub := by
          intro m'
          simpa [F] using hψ_ub m' }
    have hdev_Rmax :
        ∃ E : Set (Fin m → Z), MeasurableSet E ∧
          Measure.pi (fun _ => P_Z) E ≥ 1 - ENNReal.ofReal δ ∧
          ∀ ω ∈ E, ∀ θ : S.Θ_set, norm (F θ) ≤ Rmax →
            |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => F θ ((id : Z → Z) (ω k)))
                - P_Z[fun z => F θ ((id : Z → Z) z)]|
              ≤ 4 * Rmax * criticalRadius (Rloc.ψ m)
                + Rloc.b * Real.sqrt (2 * Real.log (1 / δ) / m) := by
      exact localized_uniform_deviation F norm P_Z (id : Z → Z)
        measurable_id hF_meas_full Rloc hδ hδ' m
        (by simpa [m] using hm_pos_nat) (r := Rmax) (by simpa [Rloc] using hRmax_lb m)
        (by simpa [Rloc] using hcrit_pos m) (by simpa [Rloc] using hcrit_fp m)
        (by simpa [F] using hrad_bdd m Rmax)
        (by simpa [F, Function.comp_def] using hrad_int m Rmax)
    have hnonempty_modulus :
        ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
          ∀ ω ∈ E, ∀ θ ∈ S.Θ_set,
            (S.L θ g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
              ≤ ((8 * L + 3) * δn) * ‖θ - S.θ₀‖
                  + ((8 * L + 3) * δn) ^ 2 := by
      have hpeelingK : ∃ K : ℕ, Rmax ≤ δn * (2 : ℝ) ^ K := by
        have hδn_pos : 0 < δn := hcrit_pos m
        -- 2^K → ∞, so for K large enough, δn · 2^K ≥ Rmax.
        rcases pow_unbounded_of_one_lt (Rmax / δn) (by norm_num : (1 : ℝ) < 2) with ⟨K, hK⟩
        refine ⟨K, ?_⟩
        rw [div_lt_iff₀ hδn_pos] at hK
        linarith [hK]
      rcases hpeelingK with ⟨K, hK⟩
      have hfoldB_peeling_bridge :
          ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
            ∀ ω ∈ E, ∀ θ ∈ S.Θ_set,
              (S.L θ g - S.L S.θ₀ g)
                - (empRiskFoldB S S_iid split n ω θ g
                    - empRiskFoldB S S_iid split n ω S.θ₀ g)
                ≤ 8 * L * δn * ‖θ - S.θ₀‖
                    + 4 * δn ^ 2
                    + b * Real.sqrt
                        (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / m) := by
        let η : ℝ := δ / (2 * ((K : ℝ) + 1))
        let slack : ℝ :=
          b * Real.sqrt (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / m)
        have hη_pos : 0 < η := by
          have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
          exact div_pos hδ hden
        have hη_le_one : η ≤ 1 := by
          have hden_pos : 0 < 2 * ((K : ℝ) + 1) := by positivity
          have hden_ge_one : 1 ≤ 2 * ((K : ℝ) + 1) := by
            have hK_nonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg K
            nlinarith
          dsimp [η]
          rw [div_le_iff₀ hden_pos]
          nlinarith [hδ']
        have hEk_per_shell :
            ∀ k : Fin (K + 1),
              ∃ E_k : Set (Fin m → Z), MeasurableSet E_k ∧
                Measure.pi (fun _ : Fin m => P_Z) E_k ≥ 1 - ENNReal.ofReal η ∧
                ∀ ω ∈ E_k, ∀ θ : S.Θ_set,
                  norm (F θ) ≤ δn * (2 : ℝ) ^ (k : ℕ) →
                    |(m : ℝ)⁻¹ *
                        (Finset.univ.sum fun j : Fin m => F θ ((id : Z → Z) (ω j)))
                        - P_Z[fun z => F θ ((id : Z → Z) z)]|
                      ≤ 4 * (δn * (2 : ℝ) ^ (k : ℕ)) * δn + slack := by
          intro k
          have hr_lb : criticalRadius (Rloc.ψ m) ≤ δn * (2 : ℝ) ^ (k : ℕ) := by
            have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
              exact one_le_pow₀ (a := (2 : ℝ)) (n := (k : ℕ))
                (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
            have hδn_nonneg : 0 ≤ δn := le_of_lt (hcrit_pos m)
            simpa [Rloc, δn] using
              (mul_le_mul_of_nonneg_left hpow_one hδn_nonneg)
          rcases localized_uniform_deviation F norm P_Z (id : Z → Z)
              measurable_id hF_meas_full Rloc hη_pos hη_le_one m
              (by simpa [m] using hm_pos_nat)
              (r := δn * (2 : ℝ) ^ (k : ℕ))
              hr_lb
              (by simpa [Rloc, δn] using hcrit_pos m)
              (by simpa [Rloc, δn] using hcrit_fp m)
              (by simpa [F] using hrad_bdd m (δn * (2 : ℝ) ^ (k : ℕ)))
              (by simpa [F, Function.comp_def] using
                hrad_int m (δn * (2 : ℝ) ^ (k : ℕ))) with
            ⟨E_k, hE_k_meas, hE_k_prob, hE_k_bound⟩
          refine ⟨E_k, hE_k_meas, hE_k_prob, ?_⟩
          intro ω hω θ hθr
          have h := hE_k_bound ω hω θ hθr
          simpa [Rloc, δn, η, slack, one_div, div_eq_mul_inv, mul_comm, mul_left_comm,
            mul_assoc] using h
        have hEtot_intersection :
            ∃ Etot : Set (Fin m → Z), MeasurableSet Etot ∧
              Measure.pi (fun _ : Fin m => P_Z) Etot ≥ 1 - ENNReal.ofReal δ ∧
              ∀ k : Fin (K + 1), Etot ⊆ (hEk_per_shell k).choose := by
          let μπ : Measure (Fin m → Z) := Measure.pi (fun _ : Fin m => P_Z)
          let Ek : Fin (K + 1) → Set (Fin m → Z) :=
            fun k => (hEk_per_shell k).choose
          let Etot : Set (Fin m → Z) := ⋂ k, Ek k
          have hEk_meas : ∀ k, MeasurableSet (Ek k) := by
            intro k
            exact (hEk_per_shell k).choose_spec.1
          have hEk_compl_le : ∀ k, μπ ((Ek k)ᶜ) ≤ ENNReal.ofReal η := by
            intro k
            have hprob : μπ (Ek k) ≥ 1 - ENNReal.ofReal η :=
              (hEk_per_shell k).choose_spec.2.1
            have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal η + μπ (Ek k) := by
              simpa [add_comm] using (tsub_le_iff_right.mp hprob)
            rw [measure_compl (hEk_meas k) (measure_ne_top _ _), measure_univ]
            exact tsub_le_iff_right.mpr hone_le
          have hEtot_meas : MeasurableSet Etot := by
            exact MeasurableSet.iInter hEk_meas
          have hbad_subset : Etotᶜ ⊆ ⋃ k, (Ek k)ᶜ := by
            simp [Etot]
          have hbad_le : μπ (Etotᶜ) ≤ ENNReal.ofReal δ := by
            calc
              μπ (Etotᶜ) ≤ μπ (⋃ k, (Ek k)ᶜ) := measure_mono hbad_subset
              _ ≤ ∑ k : Fin (K + 1), μπ ((Ek k)ᶜ) :=
                measure_iUnion_fintype_le μπ fun k => (Ek k)ᶜ
              _ ≤ ∑ _k : Fin (K + 1), ENNReal.ofReal η := by
                exact Finset.sum_le_sum fun k _hk => hEk_compl_le k
              _ = (K + 1 : ℕ) * ENNReal.ofReal η := by simp
              _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ)) * ENNReal.ofReal η := by
                have hcoe :
                    ((K : ENNReal) + 1) = ENNReal.ofReal ((K : ℝ) + 1) := by
                  calc
                    ((K : ENNReal) + 1)
                        = ENNReal.ofReal (K : ℝ) + ENNReal.ofReal (1 : ℝ) := by
                          simp
                    _ = ENNReal.ofReal ((K : ℝ) + 1) :=
                          (ENNReal.ofReal_add (Nat.cast_nonneg K) (by norm_num)).symm
                simpa [Nat.cast_add, Nat.cast_one] using congrArg
                  (fun x => x * ENNReal.ofReal η) hcoe
              _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * η) := by
                rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (((K + 1 : ℕ) : ℝ)))]
              _ = ENNReal.ofReal (δ / 2) := by
                congr 1
                dsimp [η]
                have hcast : (((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1) := by norm_num
                rw [hcast]
                field_simp
              _ ≤ ENNReal.ofReal δ := by
                exact ENNReal.ofReal_le_ofReal (by linarith [hδ])
          refine ⟨Etot, hEtot_meas, ?_, ?_⟩
          · rw [measure_compl hEtot_meas (measure_ne_top _ _), measure_univ] at hbad_le
            have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal δ + μπ Etot :=
              tsub_le_iff_right.mp hbad_le
            exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
          · intro k
            exact Set.iInter_subset (fun k => Ek k) k
        rcases hEtot_intersection with ⟨Etot, hEtot_meas, hEtot_prob, hEtot_subset⟩
        let e : Fin m ≃o split.foldB n := (split.foldB n).orderIsoOfFin rfl
        let Y : Ω → Fin m → Z := fun ω j => S_iid.Z (e j).val ω
        have hY_meas : Measurable Y := by
          apply measurable_pi_lambda
          intro j
          exact S_iid.meas (e j).val
        have hY_law : μ.map Y = Measure.pi (fun _ : Fin m => P_Z) := by
          let YB : Ω → split.foldB n → Z := fun ω i => S_iid.Z i.val ω
          let T : (split.foldB n → Z) ≃ᵐ (Fin m → Z) :=
            MeasurableEquiv.piCongrLeft (fun _ : Fin m => Z) e.symm.toEquiv
          have hY_eq : Y = T ∘ YB := by
            funext ω j
            simpa [Y, YB, T] using
              (MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm.toEquiv)
                (β := fun _ : Fin m => Z)
                (x := fun i : split.foldB n => S_iid.Z i.val ω) (i := e j)).symm
          rw [hY_eq, ← Measure.map_map T.measurable
            (measurable_pi_lambda YB fun i => S_iid.meas i.val)]
          · rw [foldB_pi_law_localized S_iid split n]
            simpa [T] using Measure.pi_map_piCongrLeft (e := e.symm.toEquiv)
              (β := fun _ : Fin m => Z) (μ := fun _ : Fin m => P_Z)
        refine ⟨Y ⁻¹' Etot, hEtot_meas.preimage hY_meas, ?_, ?_⟩
        · rw [← Measure.map_apply hY_meas hEtot_meas, hY_law]
          exact hEtot_prob
        · intro ω hω θ hθ
          let θs : S.Θ_set := ⟨θ, hθ⟩
          have hShell_select :
              ∃ k₀ : Fin (K + 1),
                norm (F θs) ≤ δn * (2 : ℝ) ^ (k₀ : ℕ) ∧
                4 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn
                  ≤ 8 * L * δn * ‖θ - S.θ₀‖ + 4 * δn ^ 2 := by
            have hδn_pos : 0 < δn := hcrit_pos m
            have hδn_nonneg : 0 ≤ δn := le_of_lt hδn_pos
            have hnormF_le_L :
                norm (F θs) ≤ L * ‖θ - S.θ₀‖ := by
              simpa [F, θs] using hF_lip θ hθ
            have htop : norm (F θs) ≤ δn * (2 : ℝ) ^ K := by
              exact (hF_diam θ hθ).trans hK
            by_cases hsmall : norm (F θs) ≤ δn
            · let kzero : Fin (K + 1) := ⟨0, Nat.succ_pos K⟩
              refine ⟨kzero, ?_, ?_⟩
              · change norm (F θs) ≤ δn * (2 : ℝ) ^ (0 : ℕ)
                rw [pow_zero, mul_one]
                exact hsmall
              · have hLdist_nonneg : 0 ≤ L * ‖θ - S.θ₀‖ :=
                  mul_nonneg hL_nonneg (norm_nonneg _)
                have hnonneg : 0 ≤ 8 * δn * (L * ‖θ - S.θ₀‖) := by
                  nlinarith [hδn_nonneg, hLdist_nonneg]
                change 4 * (δn * (2 : ℝ) ^ (0 : ℕ)) * δn
                    ≤ 8 * L * δn * ‖θ - S.θ₀‖ + 4 * δn ^ 2
                rw [pow_zero, mul_one]
                nlinarith [hnonneg, sq_nonneg δn]
            · let p : ℕ → Prop := fun j => norm (F θs) ≤ δn * (2 : ℝ) ^ j
              have hex : ∃ j, p j := ⟨K, htop⟩
              let j0 : ℕ := Nat.find hex
              have hj0_spec : p j0 := Nat.find_spec hex
              have hj0_pos : 0 < j0 := by
                by_contra hj0_not
                have hj0_zero : j0 = 0 := Nat.eq_zero_of_not_pos hj0_not
                have : norm (F θs) ≤ δn := by
                  change norm (F θs) ≤ δn * (2 : ℝ) ^ j0 at hj0_spec
                  rw [hj0_zero, pow_zero, mul_one] at hj0_spec
                  exact hj0_spec
                exact hsmall this
              have hj0_le_K : j0 ≤ K := Nat.find_min' hex htop
              refine ⟨⟨j0, Nat.lt_succ_of_le hj0_le_K⟩, hj0_spec, ?_⟩
              have hprev_not : ¬ p (j0 - 1) := by
                have hlt : j0 - 1 < j0 := Nat.sub_one_lt (Nat.ne_of_gt hj0_pos)
                exact Nat.find_min hex hlt
              have hprev_lt : δn * (2 : ℝ) ^ (j0 - 1) < norm (F θs) := by
                exact not_le.mp hprev_not
              have hr_le_normF : δn * (2 : ℝ) ^ j0 ≤ 2 * norm (F θs) := by
                have hj0_eq : j0 = (j0 - 1) + 1 := by omega
                have hpow :
                    (2 : ℝ) ^ j0 = (2 : ℝ) ^ (j0 - 1) * 2 := by
                  conv_lhs => rw [hj0_eq, pow_succ]
                rw [hpow]
                nlinarith
              have hr_le_L : δn * (2 : ℝ) ^ j0 ≤ 2 * L * ‖θ - S.θ₀‖ := by
                nlinarith [hr_le_normF, hnormF_le_L]
              nlinarith [mul_le_mul_of_nonneg_right hr_le_L (by nlinarith : 0 ≤ 4 * δn),
                hδn_nonneg, sq_nonneg δn]
          rcases hShell_select with ⟨k₀, hk₀_radius, hk₀_rate⟩
          have hEk_bound := (hEk_per_shell k₀).choose_spec.2.2
          have hY_in_Ek : Y ω ∈ (hEk_per_shell k₀).choose :=
            hEtot_subset k₀ hω
          have hdev := hEk_bound (Y ω) hY_in_Ek θs hk₀_radius
          have hsum_reindex :
              (Finset.univ.sum fun j : Fin m => F θs (Y ω j)) =
                ∑ i ∈ split.foldB n,
                  (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
            have hsum_subtype :
                (Finset.univ.sum fun j : Fin m => F θs (Y ω j)) =
                  ∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g) :=
              Fintype.sum_equiv e.toEquiv (fun j => F θs (Y ω j))
                (fun i : split.foldB n =>
                  S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)
                (by intro j; rfl)
            have hsum_attach :
                (∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)) =
                  ∑ i ∈ split.foldB n,
                    (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
              simpa using Finset.sum_attach (s := split.foldB n)
                (f := fun i =>
                  S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)
            exact hsum_subtype.trans hsum_attach
          have hmean_eq :
              (∫ z, F θs z ∂P_Z) = S.L θ g - S.L S.θ₀ g := by
            change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
              S.L θ g - S.L S.θ₀ g
            change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
              (∫ z, S.ℓ z θ g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
            exact integral_sub (hℓ_int θ hθ) (hℓ_int S.θ₀ S.θ₀_mem)
          have hcenter_abs :
              |(empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
                - (S.L θ g - S.L S.θ₀ g)|
                ≤ 4 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn + slack := by
            have hdev' :
                |(m : ℝ)⁻¹ *
                    (∑ i ∈ split.foldB n,
                      (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g))
                    - (S.L θ g - S.L S.θ₀ g)|
                  ≤ 4 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn + slack := by
              simpa [hmean_eq, hsum_reindex] using hdev
            convert hdev' using 1
            simp [empRiskFoldB, m]
            ring_nf
          have hmain :
              (S.L θ g - S.L S.θ₀ g)
                - (empRiskFoldB S S_iid split n ω θ g
                    - empRiskFoldB S S_iid split n ω S.θ₀ g)
                ≤ 4 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn + slack := by
            have := neg_le_abs ((empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
                - (S.L θ g - S.L S.θ₀ g))
            linarith
          have hrate :
              4 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn + slack
                ≤ 8 * L * δn * ‖θ - S.θ₀‖ + 4 * δn ^ 2 + slack := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hk₀_rate slack
          simpa [slack, add_assoc] using hmain.trans hrate
      rcases hfoldB_peeling_bridge with ⟨E, hE_meas, hE_prob, hE_bound⟩
      refine ⟨E, hE_meas, hE_prob, ?_⟩
      intro ω hω θ hθ
      have hdev := hE_bound ω hω θ hθ
      have hslack :
          b * Real.sqrt
              (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / m) ≤ δn ^ 2 := by
        simpa [m, δn] using hδ_dom n K hm_pos_nat (by simpa [δn] using hK)
      have hpackaging :
          8 * L * δn * ‖θ - S.θ₀‖
              + 4 * δn ^ 2
              + b * Real.sqrt
                  (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / m)
            ≤ ((8 * L + 3) * δn) * ‖θ - S.θ₀‖
                + ((8 * L + 3) * δn) ^ 2 := by
        have hδn_pos : 0 < δn := hcrit_pos m
        have hδn_nn : 0 ≤ δn := le_of_lt hδn_pos
        have hL_nn : 0 ≤ L := hL_nonneg
        have hnorm_nn : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
        nlinarith [hslack, sq_nonneg ((8 * L + 3) * δn),
          mul_nonneg hL_nn hnorm_nn, mul_nonneg hδn_nn hnorm_nn,
          mul_nonneg (mul_nonneg hL_nn hδn_nn) hnorm_nn,
          sq_nonneg L, sq_nonneg δn, mul_self_nonneg δn]
      exact hdev.trans hpackaging
    rcases hnonempty_modulus with ⟨E, hE_meas, hE_prob, hE_bound⟩
    refine ⟨E, hE_meas, hE_prob, ?_⟩
    intro ω hω θ hθ
    have := hE_bound ω hω θ hθ
    simpa [hm0, m, δn] using this

/-- **Almost-everywhere countable-class localized bridge.**

This is the a.e. analogue of `localEmpProcessModulus_of_localized_sharp`.
The centred envelope is assumed only under `P_Z`, the target class is still
required to be countable with a dense indexing sequence, and the function-space
norm is assumed invariant under `P_Z`-a.e. equality. The proof applies the
pointwise theorem to the auxiliary system whose centred loss is clamped to
`[-b, b]`, then transfers the resulting fold-B event back to the original
system on the conull sample event where the clamp is inactive. -/
theorem localEmpProcessModulus_of_localized_sharp_ae
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set] [Countable S.Θ_set]
    (g : G)
    (_hg_cont : ∀ z, Continuous fun (θ : S.Θ_set) => S.ℓ z θ.val g)
    (idx : ℕ → S.Θ_set)
    (_idx_dense : DenseRange idx)
    {norm : (Z → ℝ) → ℝ}
    (hnorm_ae : ∀ F F' : Z → ℝ, F =ᵐ[P_Z] F' → norm F = norm F')
    {ψ : ℕ → ℝ → ℝ} {b L Rmax : ℝ}
    (hreg : LocalizedRademacherRegimeAE S S_iid split g idx norm ψ b)
    (hL_nonneg : 0 ≤ L)
    (hF_lip : ∀ θ ∈ S.Θ_set,
      norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) ≤ L * ‖θ - S.θ₀‖)
    (hℓ_meas : ∀ θ ∈ S.Θ_set, Measurable (fun z => S.ℓ z θ g))
    (hℓ_int : ∀ θ ∈ S.Θ_set, Integrable (fun z => S.ℓ z θ g) P_Z)
    (hF_diam : ∀ θ ∈ S.Θ_set,
      norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) ≤ Rmax)
    (hRmax_lb : ∀ m : ℕ, criticalRadius (ψ m) ≤ Rmax)
    (hcrit_pos : ∀ m : ℕ, 0 < criticalRadius (ψ m))
    (hcrit_fp : ∀ m : ℕ, ψ m (criticalRadius (ψ m)) ≤ (criticalRadius (ψ m)) ^ 2)
    (hψ_ub : ∀ m : ℕ,
      RademacherUpperBound
        (fun (θ : S.Θ_set) (z : Z) => S.ℓ z θ.val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) m (ψ m))
    (hrad_bdd : ∀ m r, ∀ S_fin : Fin m → Z, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam S.Θ_set =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut
            (fun (θ : S.Θ_set) (z : Z) => S.ℓ z θ.val g - S.ℓ z S.θ₀ g)
            norm r p (S_fin k)|))
    (hrad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              (fun (θ : S.Θ_set) (z : Z) => S.ℓ z θ.val g - S.ℓ z S.θ₀ g)
              norm r) ((id : Z → Z) ∘ ω))
        (Measure.pi (fun _ => P_Z)))
    (hclamp_minimizes : CenteredClampedThetaMinimizes S b)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hδ_dom : ∀ n K : ℕ, 0 < (split.foldB n).card →
      Rmax ≤ (criticalRadius (ψ (split.foldB n).card)) * (2 : ℝ) ^ K →
      b * Real.sqrt
          (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / (split.foldB n).card)
        ≤ (criticalRadius (ψ (split.foldB n).card)) ^ 2) :
    LocalEmpProcessModulus S S_iid split
      (fun n =>
        if (split.foldB n).card = 0 then Real.sqrt (2 * b)
        else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) δ g := by
  classical
  obtain ⟨hb, hbound_ae, hsub, hub_idx⟩ := hreg
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  let clamp : ℝ → ℝ := fun t => max (-b) (min b t)
  let Sc : LearningSystem Ω μ Z P_Z Θ G :=
    { S with
      ℓ := fun z θ g' =>
        S.ℓ z S.θ₀ g' + clamp (S.ℓ z θ g' - S.ℓ z S.θ₀ g')
      ℓ_meas := fun θ g' => by
        dsimp [clamp]
        exact (S.ℓ_meas S.θ₀ g').add
          (measurable_const.max
            (measurable_const.min ((S.ℓ_meas θ g').sub (S.ℓ_meas S.θ₀ g'))))
      θ₀_minimizes := by
        intro θ hθ
        simpa [CenteredClampedThetaMinimizes, clamp] using hclamp_minimizes θ hθ }
  have hclamp_abs : ∀ t : ℝ, |clamp t| ≤ b := by
    intro t
    rw [abs_le]
    constructor
    · dsimp [clamp]
      exact le_max_left (-b) (min b t)
    · dsimp [clamp]
      exact max_le (by linarith) (min_le_left b t)
  have hclamp_zero : clamp 0 = 0 := by
    dsimp [clamp]
    rw [min_eq_right hb, max_eq_right]
    linarith
  have hclamp_eq_of_abs_le : ∀ {t : ℝ}, |t| ≤ b → clamp t = t := by
    intro t ht
    have ht_low : -b ≤ t := (abs_le.mp ht).1
    have ht_high : t ≤ b := (abs_le.mp ht).2
    dsimp [clamp]
    rw [min_eq_right ht_high, max_eq_right ht_low]
  have hSc_center :
      ∀ z θ, θ ∈ S.Θ_set →
        Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g =
          clamp (S.ℓ z θ g - S.ℓ z S.θ₀ g) := by
    intro z θ _hθ
    dsimp [Sc]
    have hzero_arg : S.ℓ z S.θ₀ g - S.ℓ z S.θ₀ g = 0 := by ring
    rw [hzero_arg]
    rw [hclamp_zero]
    ring
  have hSc_bound :
      ∀ z, ∀ θ ∈ Sc.Θ_set, |Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g| ≤ b := by
    intro z θ hθ
    rw [hSc_center z θ (by simpa [Sc] using hθ)]
    exact hclamp_abs _
  let Fs : S.Θ_set → Z → ℝ :=
    fun θ z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g
  let Fc : S.Θ_set → Z → ℝ :=
    fun θ z => Sc.ℓ z θ.val g - Sc.ℓ z Sc.θ₀ g
  have hcenter_all_ae :
      ∀ᵐ z ∂P_Z, ∀ θ : S.Θ_set, Fs θ z = Fc θ z := by
    filter_upwards [hbound_ae] with z hz θ
    have hc := hclamp_eq_of_abs_le (hz θ.val θ.property)
    calc
      Fs θ z = S.ℓ z θ.val g - S.ℓ z S.θ₀ g := rfl
      _ = clamp (S.ℓ z θ.val g - S.ℓ z S.θ₀ g) := hc.symm
      _ = Fc θ z := by
        dsimp [Fc]
        rw [hSc_center z θ.val θ.property]
  have hstar_all_ae :
      ∀ r : ℝ, ∀ᵐ z ∂P_Z, ∀ p : starHullParam S.Θ_set,
        starHullZeroOut Fs norm r p z = starHullZeroOut Fc norm r p z := by
    intro r
    filter_upwards [hcenter_all_ae] with z hz p
    have hstar_ae : starHullEval Fs p =ᵐ[P_Z] starHullEval Fc p := by
      filter_upwards [hcenter_all_ae] with z' hz'
      dsimp [starHullEval]
      rw [hz' p.2]
    have hnorm_eq : norm (starHullEval Fs p) = norm (starHullEval Fc p) :=
      hnorm_ae _ _ hstar_ae
    have hpval : starHullEval Fs p z = starHullEval Fc p z := by
      dsimp [starHullEval]
      rw [hz p.2]
    by_cases hp : norm (starHullEval Fs p) ≤ r
    · have hpc : norm (starHullEval Fc p) ≤ r := hnorm_eq ▸ hp
      change
        (if norm (starHullEval Fs p) ≤ r then starHullEval Fs p z else 0) =
          (if norm (starHullEval Fc p) ≤ r then starHullEval Fc p z else 0)
      rw [if_pos hp, if_pos hpc]
      exact hpval
    · have hpc : ¬ norm (starHullEval Fc p) ≤ r := by
        intro hc
        exact hp (hnorm_eq.symm ▸ hc)
      change
        (if norm (starHullEval Fs p) ≤ r then starHullEval Fs p z else 0) =
          (if norm (starHullEval Fc p) ≤ r then starHullEval Fc p z else 0)
      rw [if_neg hp, if_neg hpc]
  have hℓ_all_ae :
      ∀ᵐ z ∂P_Z, ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
    filter_upwards [hbound_ae] with z hz θ hθ
    have hc := hclamp_eq_of_abs_le (hz θ hθ)
    dsimp [Sc]
    rw [hc]
    ring
  have hL_eq : ∀ θ, θ ∈ S.Θ_set → S.L θ g = Sc.L θ g := by
    intro θ hθ
    dsimp [LearningSystem.L]
    apply integral_congr_ae
    filter_upwards [hℓ_all_ae] with z hz
    exact hz θ hθ
  have hSc_lip : ∀ θ ∈ Sc.Θ_set,
      norm (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) ≤ L * ‖θ - Sc.θ₀‖ := by
    intro θ hθ
    have hθS : θ ∈ S.Θ_set := by simpa [Sc] using hθ
    have hae : (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) =ᵐ[P_Z]
        fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g := by
      filter_upwards [hcenter_all_ae] with z hz
      exact (hz ⟨θ, hθS⟩).symm
    rw [hnorm_ae _ _ hae]
    simpa [Sc] using hF_lip θ hθS
  have hSc_diam : ∀ θ ∈ Sc.Θ_set,
      norm (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) ≤ Rmax := by
    intro θ hθ
    have hθS : θ ∈ S.Θ_set := by simpa [Sc] using hθ
    have hae : (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) =ᵐ[P_Z]
        fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g := by
      filter_upwards [hcenter_all_ae] with z hz
      exact (hz ⟨θ, hθS⟩).symm
    rw [hnorm_ae _ _ hae]
    simpa [Sc] using hF_diam θ hθS
  have hSc_ψ_ub : ∀ m : ℕ,
      RademacherUpperBound
        (fun (θ : Sc.Θ_set) (z : Z) => Sc.ℓ z θ.val g - Sc.ℓ z Sc.θ₀ g)
        norm P_Z (id : Z → Z) m (ψ m) := by
    intro m r hr
    have hcongr :
        rademacherComplexity m (starHullZeroOut Fs norm r) P_Z (id : Z → Z) =
          rademacherComplexity m (starHullZeroOut Fc norm r) P_Z (id : Z → Z) :=
      rademacherComplexity_congr_ae_all m
        (starHullZeroOut Fs norm r) (starHullZeroOut Fc norm r)
        P_Z (id : Z → Z) (by simpa using hstar_all_ae r)
    calc
      rademacherComplexity m
          (starHullZeroOut
            (fun (θ : Sc.Θ_set) (z : Z) => Sc.ℓ z θ.val g - Sc.ℓ z Sc.θ₀ g)
            norm r) P_Z (id : Z → Z)
          = rademacherComplexity m (starHullZeroOut Fc norm r) P_Z (id : Z → Z) := by
              rfl
      _ = rademacherComplexity m (starHullZeroOut Fs norm r) P_Z (id : Z → Z) :=
              hcongr.symm
      _ ≤ ψ m r := by
              simpa [Fs] using hψ_ub m r hr
  let idxc : ℕ → Sc.Θ_set := fun k => ⟨(idx k).val, by
    simp [Sc, (idx k).property]⟩
  have idxc_dense : DenseRange idxc := by
    simpa [idxc, Sc] using _idx_dense
  have hSc_reg : LocalizedRademacherRegime Sc S_iid split g idxc norm ψ b := by
    refine ⟨hb, hSc_bound, hsub, ?_⟩
    intro n r hr
    have hidx_all_ae :
        ∀ r : ℝ, ∀ᵐ z ∂P_Z, ∀ p : starHullParam ℕ,
          starHullZeroOut
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
              norm r p z =
            starHullZeroOut
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g)
              norm r p z := by
      intro r'
      filter_upwards [hcenter_all_ae] with z hz p
      have hstar_ae :
          starHullEval
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p
            =ᵐ[P_Z]
          starHullEval
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p := by
        filter_upwards [hcenter_all_ae] with z' hz'
        change (p.1 : ℝ) *
            (S.ℓ z' (idx p.2).val g - S.ℓ z' S.θ₀ g) =
          (p.1 : ℝ) *
            (Sc.ℓ z' (idx p.2).val g - Sc.ℓ z' Sc.θ₀ g)
        have hbase :
            S.ℓ z' (idx p.2).val g - S.ℓ z' S.θ₀ g =
              Sc.ℓ z' (idx p.2).val g - Sc.ℓ z' Sc.θ₀ g := by
          simpa [Fs, Fc] using hz' (idx p.2)
        rw [hbase]
      have hnorm_eq :
          norm (starHullEval
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p) =
            norm (starHullEval
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p) :=
        hnorm_ae _ _ hstar_ae
      have hpval :
          starHullEval
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p z =
            starHullEval
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p z := by
        change (p.1 : ℝ) *
            (S.ℓ z (idx p.2).val g - S.ℓ z S.θ₀ g) =
          (p.1 : ℝ) *
            (Sc.ℓ z (idx p.2).val g - Sc.ℓ z Sc.θ₀ g)
        have hbase :
            S.ℓ z (idx p.2).val g - S.ℓ z S.θ₀ g =
              Sc.ℓ z (idx p.2).val g - Sc.ℓ z Sc.θ₀ g := by
          simpa [Fs, Fc] using hz (idx p.2)
        rw [hbase]
      by_cases hp : norm (starHullEval
          (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p) ≤ r'
      · have hpc : norm (starHullEval
            (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p) ≤ r' :=
          hnorm_eq ▸ hp
        change
          (if norm (starHullEval
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p) ≤ r'
            then starHullEval
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p z
            else 0) =
          (if norm (starHullEval
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p) ≤ r'
            then starHullEval
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p z
            else 0)
        rw [if_pos hp, if_pos hpc]
        exact hpval
      · have hpc : ¬ norm (starHullEval
            (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p) ≤ r' := by
          intro hc
          exact hp (hnorm_eq.symm ▸ hc)
        change
          (if norm (starHullEval
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p) ≤ r'
            then starHullEval
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) p z
            else 0) =
          (if norm (starHullEval
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p) ≤ r'
            then starHullEval
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) p z
            else 0)
        rw [if_neg hp, if_neg hpc]
    have hcongr :
        rademacherComplexity (split.foldB n).card
            (starHullZeroOut
              (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
              norm r) P_Z (id : Z → Z) =
          rademacherComplexity (split.foldB n).card
            (starHullZeroOut
              (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g)
              norm r) P_Z (id : Z → Z) :=
      rademacherComplexity_congr_ae_all (split.foldB n).card
        (starHullZeroOut
          (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g) norm r)
        (starHullZeroOut
          (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g) norm r)
        P_Z (id : Z → Z) (by simpa using hidx_all_ae r)
    calc
      rademacherComplexity (split.foldB n).card
          (starHullZeroOut
            (fun (k : ℕ) (z : Z) => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g)
            norm r) P_Z (id : Z → Z)
          = rademacherComplexity (split.foldB n).card
              (starHullZeroOut
                (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
                norm r) P_Z (id : Z → Z) := hcongr.symm
      _ ≤ ψ (split.foldB n).card r := hub_idx n r hr
  have hSc_cont :
      ∀ z, Continuous fun (θ : Sc.Θ_set) => Sc.ℓ z θ.val g := by
    intro z
    dsimp [Sc, clamp]
    exact continuous_const.add
      (continuous_const.max
        (continuous_const.min ((_hg_cont z).sub continuous_const)))
  have hSc_ℓ_meas : ∀ θ ∈ Sc.Θ_set, Measurable (fun z => Sc.ℓ z θ g) := by
    intro θ _hθ
    exact Sc.ℓ_meas θ g
  have hSc_ℓ_int : ∀ θ ∈ Sc.Θ_set, Integrable (fun z => Sc.ℓ z θ g) P_Z := by
    intro θ hθ
    have hcenter_meas :
        Measurable fun z => clamp (S.ℓ z θ g - S.ℓ z S.θ₀ g) := by
      dsimp [clamp]
      exact measurable_const.max
        (measurable_const.min ((hℓ_meas θ hθ).sub (hℓ_meas S.θ₀ S.θ₀_mem)))
    have hcenter_int :
        Integrable (fun z => clamp (S.ℓ z θ g - S.ℓ z S.θ₀ g)) P_Z :=
      Integrable.of_bound hcenter_meas.aestronglyMeasurable b
        (by
          filter_upwards with z
          simpa [Real.norm_eq_abs] using hclamp_abs (S.ℓ z θ g - S.ℓ z S.θ₀ g))
    simpa [Sc] using (hℓ_int S.θ₀ S.θ₀_mem).add hcenter_int
  have hSc_rad_bdd : ∀ m r, ∀ S_fin : Fin m → Z, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam Sc.Θ_set =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut
            (fun (θ : Sc.Θ_set) (z : Z) => Sc.ℓ z θ.val g - Sc.ℓ z Sc.θ₀ g)
            norm r p (S_fin k)|) := by
    intro m r S_fin σ
    exact starHullZeroOut_bddAbove_of_bound
      (fun (θ : Sc.Θ_set) (z : Z) => Sc.ℓ z θ.val g - Sc.ℓ z Sc.θ₀ g)
      norm hb
      (fun θ z => hSc_bound z θ.val θ.property) m r S_fin σ
  have hSc_rad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              (fun (θ : Sc.Θ_set) (z : Z) => Sc.ℓ z θ.val g - Sc.ℓ z Sc.θ₀ g)
              norm r) ((id : Z → Z) ∘ ω))
        (Measure.pi (fun _ => P_Z)) := by
    intro m r
    have hprod : ∀ᵐ s : Fin m → Z ∂Measure.pi (fun _ : Fin m => P_Z),
        ∀ p : starHullParam S.Θ_set, ∀ k : Fin m,
          starHullZeroOut Fs norm r p ((id : Z → Z) (s k)) =
            starHullZeroOut Fc norm r p ((id : Z → Z) (s k)) := by
      filter_upwards [Filter.eventually_all.2 fun k : Fin m =>
        Measure.tendsto_eval_ae_ae.eventually (hstar_all_ae r)] with s hs p k
      exact hs k p
    have hemp :
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m (starHullZeroOut Fs norm r) ((id : Z → Z) ∘ ω))
          =ᵐ[Measure.pi (fun _ => P_Z)]
        fun ω : Fin m → Z =>
          empiricalRademacherComplexity m (starHullZeroOut Fc norm r) ((id : Z → Z) ∘ ω) := by
      filter_upwards [hprod] with s hs
      exact empiricalRademacherComplexity_congr_sample m
        (starHullZeroOut Fs norm r) (starHullZeroOut Fc norm r) ((id : Z → Z) ∘ s)
        (fun p k => hs p k)
    have hbase := hrad_int m r
    exact (by
      simpa [Fs, Fc] using hbase.congr hemp)
  have hmod_c := localEmpProcessModulus_of_localized_sharp
    (S := Sc) (S_iid := S_iid) (split := split)
    (g := g) (_hg_cont := hSc_cont) (idx := idxc) (_idx_dense := idxc_dense)
    (norm := norm) (ψ := ψ) (L := L)
    (b := b) (Rmax := Rmax)
    (hreg := hSc_reg) (hL_nonneg := hL_nonneg) (hF_lip := hSc_lip)
    (hℓ_meas := hSc_ℓ_meas) (hℓ_int := hSc_ℓ_int)
    (hF_diam := hSc_diam) (hRmax_lb := hRmax_lb)
    (hcrit_pos := hcrit_pos) (hcrit_fp := hcrit_fp)
    (hψ_ub := hSc_ψ_ub) (hrad_bdd := hSc_rad_bdd)
    (hrad_int := hSc_rad_int)
    (hδ := hδ) (hδ' := hδ') (hδ_dom := hδ_dom)
  intro n
  rcases hmod_c n with ⟨Ec, hEc_meas, hEc_prob, hEc_bound⟩
  let Gs : Set Ω :=
    {ω | ∀ i ∈ split.foldB n, ∀ θ ∈ S.Θ_set,
      S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g}
  have hsample_all_ae : ∀ i : ℕ, ∀ᵐ ω ∂μ,
      ∀ θ ∈ S.Θ_set,
        S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g := by
    intro i
    have hlaw_i : μ.map (S_iid.Z i) = P_Z := by
      rw [← (S_iid.identDist i).map_eq, S_iid.law]
    have hmap : ∀ᵐ z ∂μ.map (S_iid.Z i),
        ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
      simpa [hlaw_i] using hℓ_all_ae
    exact ae_of_ae_map (S_iid.meas i).aemeasurable hmap
  have hGs_ae : ∀ᵐ ω ∂μ, ω ∈ Gs := by
    have hfin : ∀ᵐ ω ∂μ, ∀ i ∈ split.foldB n,
        ∀ θ ∈ S.Θ_set,
          S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g := by
      simpa using (Finset.eventually_all (split.foldB n)).2
        (fun i _hi => hsample_all_ae i)
    simpa [Gs] using hfin
  have hGs_null : μ Gsᶜ = 0 := ae_iff.mp hGs_ae
  rcases exists_measurable_superset_of_null hGs_null with
    ⟨N, hGs_compl_subset_N, hN_meas, hN_null⟩
  refine ⟨Ec \ N, hEc_meas.diff hN_meas, ?_, ?_⟩
  · rw [measure_diff_null hN_null]
    exact hEc_prob
  · intro ω hω θ hθ
    have hωEc : ω ∈ Ec := hω.1
    have hωG : ω ∈ Gs := by
      by_contra hnot
      exact hω.2 (hGs_compl_subset_N hnot)
    have hLθ : S.L θ g = Sc.L θ g := hL_eq θ hθ
    have hL0 : S.L S.θ₀ g = Sc.L Sc.θ₀ g := by
      simpa [Sc] using hL_eq S.θ₀ S.θ₀_mem
    have hempθ :
        empRiskFoldB S S_iid split n ω θ g =
          empRiskFoldB Sc S_iid split n ω θ g := by
      dsimp [empRiskFoldB]
      congr 1
      exact Finset.sum_congr rfl fun i hi => hωG i hi θ hθ
    have hemp0 :
        empRiskFoldB S S_iid split n ω S.θ₀ g =
          empRiskFoldB Sc S_iid split n ω Sc.θ₀ g := by
      dsimp [empRiskFoldB]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by
        simpa [Sc] using hωG i hi S.θ₀ S.θ₀_mem
    calc
      (S.L θ g - S.L S.θ₀ g)
          - (empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g)
          = (Sc.L θ g - Sc.L Sc.θ₀ g)
              - (empRiskFoldB Sc S_iid split n ω θ g
                  - empRiskFoldB Sc S_iid split n ω Sc.θ₀ g) := by
            rw [hLθ, hL0, hempθ, hemp0]
      _ ≤
          (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
           else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) *
            ‖θ - S.θ₀‖
            +
          (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
           else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 := by
            simpa [Sc] using hEc_bound ω hωEc θ (by simpa [Sc] using hθ)

/-- **Trivial finite class.**  When `Θ_set = {θ₀}` the
modulus inequality holds with `ρ n := 0` (the centred excess risk is
identically zero). Mirrors `localEmpProcessModulus_singleton` in the
global-Rademacher bridge. -/
theorem localEmpProcessModulus_of_localized_singleton
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    [IsProbabilityMeasure μ]
    (g : G)
    (hsing : S.Θ_set = {S.θ₀})
    {δ : ℝ} (_hδ : 0 < δ) :
    LocalEmpProcessModulus S S_iid split (fun _ => 0) δ g := by
  intro n
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · rw [measure_univ]
    exact tsub_le_self
  · intro ω _ θ hθ
    have hθ' : θ ∈ ({S.θ₀} : Set Θ) := by
      simpa [hsing] using hθ
    rcases hθ' with rfl
    simp

end OrthogonalLearning
end Estimation
end Causalean
