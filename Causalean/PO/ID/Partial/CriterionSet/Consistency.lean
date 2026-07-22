/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hausdorff consistency of criterion-function set estimators (Chernozhukov–Hong–Tamer 2007)

Companion to `CriterionSet/Basic.lean`.  Given a population criterion `Q` with
identified set `Θ_I = {Q = 0}` and a sample criterion `Qn` close to `Q` in the
sup-norm (the uniform-convergence input supplied by a ULLN / Glivenko–Cantelli
argument), the level-set estimator `Θ̂ₙ = {Qn ≤ cₙ}` converges to `Θ_I` in
Hausdorff distance.

The mathematical core is the **deterministic rate bound**: under a *linear
minorant* `δ · d(θ, Θ_I) ≤ Q θ` (the CHT polynomial-minorant identifiability
condition, degree `γ = 1`), a sup-norm error `ε` and a cutoff `c ≥ ε`,

    H(Θ̂ₙ, Θ_I) ≤ (c + ε) / δ.

Both directions are elementary: points of `Θ̂ₙ` cannot be far from `Θ_I` (the
minorant forces `d(θ, Θ_I) ≤ (c+ε)/δ`), and `Θ_I ⊆ Θ̂ₙ` outright (`Q = 0 ⇒
Qn ≤ ε ≤ c`).  Consistency `H(Θ̂ₙ, Θ_I) → 0` is then a squeeze from `cₙ, εₙ → 0`.

This reuses the metric Hausdorff distance of `RandomSet/Hausdorff.lean` (the same
`directedHausdorff` / `hausdorffDist` that drives the Beresteanu–Molinari
support-function program), tying the two partial-ID inference pillars to one
geometry.

## Main definitions

* `LinearMinorant Q δ` — the linear identifiability minorant `δ · d(θ, Θ_I) ≤ Q θ`.

## Main results

* `directedHausdorff_eq_zero_of_subset`, `directedHausdorff_le_of_forall`,
  `directedHausdorff_nonneg`, `hausdorffDist_nonneg` — metric Hausdorff helpers.
* `hausdorffDist_levelSet_le` — the deterministic CHT rate bound.
* `tendsto_hausdorffDist_levelSet` — Hausdorff consistency `H(Θ̂ₙ, Θ_I) → 0`.
-/

import Causalean.PO.ID.Partial.CriterionSet.Basic
import Causalean.PO.ID.Partial.RandomSet.Hausdorff

/-! # Hausdorff consistency for criterion-set estimators

This file proves deterministic Hausdorff-distance bounds for level sets of
sample criterion functions, following the Chernozhukov-Hong-Tamer
criterion-set consistency argument. The population identified set is
`identifiedSet Q = {theta | Q theta = 0}`, the sample estimator is
`levelSet Qn c = {theta | Qn theta <= c}`, and the key identifiability
condition is `LinearMinorant Q delta`, a linear lower bound on criterion values
in terms of distance to the identified set.

The main theorem `hausdorffDist_levelSet_le` states that a uniform sup-norm
error bound `|Qn - Q| <= epsilon`, a cutoff `epsilon <= c`, and a positive
minorant modulus `delta` imply
`hausdorffDist (levelSet Qn c) (identifiedSet Q) <= (c + epsilon) / delta`.
The consistency theorem `tendsto_hausdorffDist_levelSet` turns this deterministic
bound into Hausdorff convergence when both the cutoff and the uniform error
vanish. The file also supplies reusable helpers for nonnegativity and subset
control of `directedHausdorff` and `hausdorffDist`.
-/

open Filter Topology

namespace Causalean.PartialID.CriterionSet

open Causalean.PartialID.RandomSet

variable {Θ : Type*} [PseudoMetricSpace Θ]

/-! ## Metric Hausdorff helpers -/

/-- The directed Hausdorff distance is nonnegative (a sup of nonnegative
point-to-set distances). -/
lemma directedHausdorff_nonneg (A B : Set Θ) : 0 ≤ directedHausdorff A B :=
  Real.sSup_nonneg (by rintro _ ⟨a, _, rfl⟩; exact Metric.infDist_nonneg)

/-- The symmetric Hausdorff distance is nonnegative. -/
lemma hausdorffDist_nonneg (A B : Set Θ) : 0 ≤ hausdorffDist A B :=
  le_max_of_le_left (directedHausdorff_nonneg A B)

/-- If every point of `A` is within `M` of `B` (and `M ≥ 0`), the directed
Hausdorff distance from `A` to `B` is at most `M`. -/
lemma directedHausdorff_le_of_forall {A B : Set Θ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a ∈ A, Metric.infDist a B ≤ M) : directedHausdorff A B ≤ M :=
  Real.sSup_le (by rintro _ ⟨a, ha, rfl⟩; exact h a ha) hM

/-- If `A ⊆ B` then the directed Hausdorff distance from `A` to `B` is `0`. -/
lemma directedHausdorff_eq_zero_of_subset {A B : Set Θ} (h : A ⊆ B) :
    directedHausdorff A B = 0 :=
  le_antisymm
    (directedHausdorff_le_of_forall le_rfl
      (fun _ ha => le_of_eq (Metric.infDist_zero_of_mem (h ha))))
    (directedHausdorff_nonneg A B)

/-! ## The CHT criterion-set consistency results -/

/-- A criterion `Q` satisfies a **linear minorant** with modulus `δ` relative to
its identified set: `δ · d(θ, Θ_I) ≤ Q θ` for all `θ`.  This is the
Chernozhukov–Hong–Tamer (2007) polynomial-minorant identifiability condition of
degree `γ = 1` — it forces `Q` to grow at least linearly away from `Θ_I`, so a
small criterion value pins `θ` near the identified set. -/
def LinearMinorant (Q : Θ → ℝ) (δ : ℝ) : Prop :=
  ∀ θ, δ * Metric.infDist θ (identifiedSet Q) ≤ Q θ

/-- **Deterministic CHT rate bound.**  Under a linear minorant of modulus `δ > 0`,
a sup-norm error `|Qn − Q| ≤ ε`, and a cutoff `c ≥ ε`, the level-set estimator is
within Hausdorff distance `(c + ε)/δ` of the identified set:

    H(levelSet Qn c, identifiedSet Q) ≤ (c + ε) / δ. -/
theorem hausdorffDist_levelSet_le
    {Q Qn : Θ → ℝ} {δ c ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hc : ε ≤ c)
    (hmin : LinearMinorant Q δ)
    (hunif : ∀ θ, |Qn θ - Q θ| ≤ ε) :
    hausdorffDist (levelSet Qn c) (identifiedSet Q) ≤ (c + ε) / δ := by
  have hbound : (0 : ℝ) ≤ (c + ε) / δ := div_nonneg (by linarith) hδ.le
  refine max_le ?_ ?_
  · -- points of the estimator are pinned near `Θ_I` by the minorant
    refine directedHausdorff_le_of_forall hbound (fun θ hθ => ?_)
    have hQc : Q θ ≤ c + ε := by
      have hcl := (abs_le.mp (hunif θ)).1
      have : Qn θ ≤ c := mem_levelSet.mp hθ
      linarith
    rw [le_div_iff₀ hδ]
    have hm := hmin θ
    nlinarith [hm, hQc]
  · -- the identified set sits inside the estimator, so its directed distance is 0
    have hsub : identifiedSet Q ⊆ levelSet Qn c := by
      intro θ hθ
      rw [mem_levelSet]
      have hQ0 : Q θ = 0 := mem_identifiedSet.mp hθ
      have hcu := (abs_le.mp (hunif θ)).2
      linarith
    rw [directedHausdorff_eq_zero_of_subset hsub]
    exact hbound

/-- **Hausdorff consistency of the criterion-set estimator.**  If the sample
criterion converges uniformly to the population criterion (`|Qnₙ − Q| ≤ εₙ` with
`εₙ → 0`) and the cutoff sequence satisfies `εₙ ≤ cₙ → 0`, then the level-set
estimator is Hausdorff-consistent for the identified set:
`H(levelSet Qnₙ cₙ, identifiedSet Q) → 0`. -/
theorem tendsto_hausdorffDist_levelSet
    {Q : Θ → ℝ} {Qn : ℕ → Θ → ℝ} {δ : ℝ} {c ε : ℕ → ℝ}
    (hδ : 0 < δ) (hmin : LinearMinorant Q δ)
    (hε : ∀ n, 0 ≤ ε n) (hc : ∀ n, ε n ≤ c n)
    (hunif : ∀ n θ, |Qn n θ - Q θ| ≤ ε n)
    (hc0 : Tendsto c atTop (𝓝 0)) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => hausdorffDist (levelSet (Qn n) (c n)) (identifiedSet Q))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun n => hausdorffDist_nonneg _ _)
    (fun n => hausdorffDist_levelSet_le hδ (hε n) (hc n) hmin (hunif n)) ?_
  have : Tendsto (fun n => (c n + ε n) / δ) atTop (𝓝 ((0 + 0) / δ)) :=
    ((hc0.add hε0).div_const δ)
  simpa using this

end Causalean.PartialID.CriterionSet
