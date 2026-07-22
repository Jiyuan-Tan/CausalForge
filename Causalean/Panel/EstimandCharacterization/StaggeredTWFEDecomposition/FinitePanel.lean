/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): TWFE decomposition under staggered timing — Layer A primitives

**Role in the folder.** *Finite base.* Every other file in the folder sits on
these definitions. Pure finite ℝ data — **no probability space, no potential
outcomes**. See `StaggeredTWFEDecomposition.lean` for the folder layer-map.

Layer A — pure finite-cell algebra. This file holds the cell-statistics record
`CohortPanel`, the adoption-date helpers, the residualized treatment `Dtilde`,
the residualized variance `VD`, the window mean `Ybar`, the three 2x2
comparison contrasts `Δ_TN, Δ_EL, Δ_LE`, the raw and normalized weights
(`λ_TN, λ_EL, λ_LE, w_TN, w_EL, w_LE`), and the comparison index set
`𝒦` together with the unified `weight, contrast, lambdaWeight`.

Implementation note (per NL doc A5.5 / orchestrator dispatch). The
admissible filter `𝒦 P` enforces only the type-of-comparison side conditions
(`isFin`, `isInf`, adoption-date order). Empty-window filtering is omitted:
when a comparison window is empty the corresponding raw weight already
contains a `0` factor (`barD g · (1 - barD g)` or `q · (1 - q)`), so the
contribution to the headline identity vanishes naturally.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`.
Source LaTeX:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.tex`.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Causalean.Panel.WeightedTwoWayPanel
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.WithBot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Goodman-Bacon Panel Algebra

This file provides the finite cohort-period primitives for the Goodman-Bacon
two-way fixed-effect decomposition. It defines staggered adoption panels,
absorbing treatment, residualized treatment, the TWFE coefficient, comparison
windows, pairwise comparison contrasts, and the raw and normalized weights for
treated-versus-never, early-versus-late, and late-versus-early comparisons. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

/-- Three-valued tag for the type of an admissible 2x2 comparison:
treated-versus-never, early-versus-late before late, and late-versus-early
after early. -/
inductive CompTag | TN | EL | LE deriving DecidableEq

/-- The three Goodman-Bacon comparison tags form a finite type. -/
instance : Fintype CompTag :=
  ⟨{CompTag.TN, CompTag.EL, CompTag.LE}, by intro c; cases c <;> decide⟩

/-- Staggered-adoption cohort panel (cell-statistics record).

Carries cohort population shares `p`, adoption dates `A : 𝒢 → WithTop (Fin T)`
(with `⊤` encoding the never-treated case `A_g = ∞`), and cohort-period
factual outcome means `Y`. Side conditions: shares are positive, sum to one,
and the period count is positive. -/
structure CohortPanel (𝒢 : Type*) (T : ℕ) [Fintype 𝒢] [DecidableEq 𝒢] where
  /-- Cohort population share `p_g`. -/
  p : 𝒢 → ℝ
  /-- Adoption date `A_g ∈ 𝒯 ∪ {∞}`, encoded with `⊤ = ∞`. -/
  A : 𝒢 → WithTop (Fin T)
  /-- Cohort-period factual outcome mean `Y_{gt}`. -/
  Y : 𝒢 → Fin T → ℝ
  /-- The number of periods is positive. -/
  T_pos : 0 < T
  /-- Cohort shares are strictly positive. -/
  p_pos : ∀ g, 0 < p g
  /-- Cohort shares sum to one. -/
  p_sum_one : ∑ g, p g = 1

namespace AdoptionDate

/-- Adoption-date predicate `A_g ≤ t`, i.e. cohort `g` has adopted by period
`t`. The lift `(t : WithTop (Fin T))` carries `⊤ = ∞` so that `∞ ≤ t` is
false, matching the LaTeX convention `1_{∞ ≤ t} = 0`. -/
def le {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop := a ≤ (t : WithTop (Fin T))

/-- Adoption-date predicate `t < A_g`, i.e. cohort `g` is untreated at
period `t`. -/
def lt {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop := (t : WithTop (Fin T)) < a

/-- `A_g` is finite, i.e. cohort `g` is eventually treated. -/
def isFin {T : ℕ} (a : WithTop (Fin T)) : Prop := a ≠ ⊤

/-- `A_g = ∞`, i.e. cohort `g` is never treated. -/
def isInf {T : ℕ} (a : WithTop (Fin T)) : Prop := a = ⊤

end AdoptionDate

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

open Classical in
/-- Treatment indicator `D_{gt} = 1_{A_g ≤ t}`, binary and absorbing.
Marked `noncomputable` because the `WithTop`-order predicate is taken via
classical decidability. -/
noncomputable def D (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) : ℝ :=
  if AdoptionDate.le (P.A g) t then 1 else 0

/-- Cohort treatment share `\overline{D}_g := T⁻¹ ∑_t D_{gt}`. -/
noncomputable def barD (P : CohortPanel 𝒢 T) (g : 𝒢) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t, D P g t

/-- Overall treatment share `E[D] = ∑_g p_g \overline{D}_g`. -/
noncomputable def pCohort (P : CohortPanel 𝒢 T) : ℝ :=
  ∑ g, P.p g * barD P g

/-- Cohort shares as unit weights for the shared weighted two-way panel module. -/
noncomputable def cohortWeights (P : CohortPanel 𝒢 T) :
    WeightedTwoWayPanel.UnitWeights 𝒢 :=
  ⟨P.p, P.p_pos, P.p_sum_one⟩

/-- Goodman-Bacon's cohort treatment share is the shared unit mean. -/
theorem barD_eq_unitMean (P : CohortPanel 𝒢 T) (g : 𝒢) :
    barD P g = WeightedTwoWayPanel.unitMean (D P) g := by
  simp [barD, WeightedTwoWayPanel.unitMean]

/-- Goodman-Bacon's overall treatment share is the shared weighted grand mean. -/
theorem pCohort_eq_grandMean (P : CohortPanel 𝒢 T) :
    pCohort P = WeightedTwoWayPanel.grandMean (cohortWeights P) (D P) := by
  simp [pCohort, WeightedTwoWayPanel.grandMean, cohortWeights, ← barD_eq_unitMean]

/-- Residualized treatment via the explicit double-demeaning formula
`\widetilde{D}_{gt} := D_{gt} − \overline{D}_g − E[D|T=t] + E[D]`. -/
noncomputable def Dtilde (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) : ℝ :=
  WeightedTwoWayPanel.ddot (cohortWeights P) (D P) g t

/-- Compatibility with the original Goodman-Bacon closed form for residualized
treatment. -/
theorem Dtilde_eq (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) :
    Dtilde P g t =
      D P g t - barD P g - (∑ g', P.p g' * D P g' t) + pCohort P := by
  unfold Dtilde WeightedTwoWayPanel.ddot
  rw [← barD_eq_unitMean P g, ← pCohort_eq_grandMean P]
  unfold WeightedTwoWayPanel.timeMean cohortWeights
  simp

/-- Residualized treatment variance `V_D := ∑_{g,t} (p_g/T) \widetilde{D}_{gt}^2`. -/
noncomputable def VD (P : CohortPanel 𝒢 T) : ℝ :=
  ∑ g, ∑ t, (P.p g / (T : ℝ)) * (Dtilde P g t)^2

/-- Population TWFE coefficient (finite-cell form) from
`def:po-estimand-goodman-bacon-twfe`. Defined unconditionally; positivity of
the denominator is supplied at theorem-use time via `hVD_pos`. -/
noncomputable def betaTWFE (P : CohortPanel 𝒢 T) : ℝ :=
  (∑ g, ∑ t, (P.p g / (T : ℝ)) * Dtilde P g t * P.Y g t) / VD P

/-- Window mean `\overline{Y}_{g,S} := |S|⁻¹ ∑_{t ∈ S} Y_{gt}`. Defined
unconditionally; nonemptiness `S.Nonempty` is supplied as a hypothesis when
used. -/
noncomputable def Ybar (P : CohortPanel 𝒢 T) (g : 𝒢) (S : Finset (Fin T)) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ t ∈ S, P.Y g t

/-! ### Comparison windows -/

open Classical in
/-- Treated-versus-never untreated window `\mathcal{T}_g^0 = {t : t < A_g}`. -/
noncomputable def S0_TN (P : CohortPanel 𝒢 T) (g : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.lt (P.A g) t)

open Classical in
/-- Treated-versus-never treated window `\mathcal{T}_g^1 = {t : A_g ≤ t}`. -/
noncomputable def S1_TN (P : CohortPanel 𝒢 T) (g : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.le (P.A g) t)

open Classical in
/-- Early-vs-late untreated window `\mathcal{T}_{e\ell}^0 = {t : t < A_e}`.
The late-cohort argument `_ℓ` is unused but preserved for symmetry with
`S1_EL`. -/
noncomputable def S0_EL (P : CohortPanel 𝒢 T) (e _ℓ : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.lt (P.A e) t)

open Classical in
/-- Early-vs-late treated window `\mathcal{T}_{e\ell}^1 = {t : A_e ≤ t < A_ℓ}`. -/
noncomputable def S1_EL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t)

open Classical in
/-- Late-vs-early early-treated window `\mathcal{T}_{\ell e}^0 = {t : A_e ≤ t < A_ℓ}`. -/
noncomputable def S0_LE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t)

open Classical in
/-- Late-vs-early both-treated window `\mathcal{T}_{\ell e}^1 = {t : A_ℓ ≤ t}`.
The early-cohort argument `_e` is unused but preserved for symmetry with
`S0_LE`. -/
noncomputable def S1_LE (P : CohortPanel 𝒢 T) (_e ℓ : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.le (P.A ℓ) t)

/-! ### 2x2 comparison contrasts -/

/-- Treated-vs-never 2x2 DID contrast `Δ^TN_{g,u}`. -/
noncomputable def Δ_TN (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  (Ybar P g (S1_TN P g) - Ybar P g (S0_TN P g))
    - (Ybar P u (S1_TN P g) - Ybar P u (S0_TN P g))

/-- Early-vs-late before late 2x2 DID contrast `Δ^EL_{e,ℓ}`. -/
noncomputable def Δ_EL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  (Ybar P e (S1_EL P e ℓ) - Ybar P e (S0_EL P e ℓ))
    - (Ybar P ℓ (S1_EL P e ℓ) - Ybar P ℓ (S0_EL P e ℓ))

/-- Late-vs-early after early 2x2 DID contrast `Δ^LE_{ℓ,e}`. -/
noncomputable def Δ_LE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  (Ybar P ℓ (S1_LE P e ℓ) - Ybar P ℓ (S0_LE P e ℓ))
    - (Ybar P e (S1_LE P e ℓ) - Ybar P e (S0_LE P e ℓ))

/-! ### Raw and normalized weights -/

/-- Treated-vs-never raw weight `λ^TN_{g,u} := p_g p_u \overline{D}_g (1−\overline{D}_g)`. -/
noncomputable def lambdaTN (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  P.p g * P.p u * (barD P g * (1 - barD P g))

/-- Treated-treated timing-pair gap `q_{eℓ} := \overline{D}_e − \overline{D}_ℓ`. -/
noncomputable def q (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  barD P e - barD P ℓ

/-- Splitting fraction `μ_{eℓ} := (1−\overline{D}_e)/(1−q_{eℓ})`. -/
noncomputable def mu (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  (1 - barD P e) / (1 - q P e ℓ)

/-- Early-vs-late raw weight `λ^EL_{e,ℓ} := p_e p_ℓ q (1−q) μ`. -/
noncomputable def lambdaEL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) * mu P e ℓ

/-- Late-vs-early raw weight `λ^LE_{ℓ,e} := p_e p_ℓ q (1−q) (1−μ)`. -/
noncomputable def lambdaLE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) * (1 - mu P e ℓ)

open Classical in
/-- Aggregate raw-weight denominator
`Λ := ∑_{TN admissible} λ^TN + ∑_{e<ℓ<∞} (λ^EL + λ^LE)`. -/
noncomputable def Lambda (P : CohortPanel 𝒢 T) : ℝ :=
  (∑ g, ∑ u, if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then
              lambdaTN P g u else 0)
  + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
                lambdaEL P e ℓ + lambdaLE P e ℓ else 0)

/-- Normalized treated-vs-never weight `w^TN_{g,u} := λ^TN_{g,u} / Λ`. -/
noncomputable def w_TN (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  lambdaTN P g u / Lambda P

/-- Normalized early-vs-late weight `w^EL_{e,ℓ} := λ^EL_{e,ℓ} / Λ`. -/
noncomputable def w_EL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  lambdaEL P e ℓ / Lambda P

/-- Normalized late-vs-early weight `w^LE_{ℓ,e} := λ^LE_{ℓ,e} / Λ`. -/
noncomputable def w_LE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  lambdaLE P e ℓ / Lambda P

/-! ### Comparison index set 𝒦 and unified weight/contrast/lambdaWeight -/

/-- Admissibility predicate for a tagged cohort pair `(tag, g₁, g₂)`. For
`TN`: `g₁` eventually treated and `g₂` never treated, both with positive
shares. For `EL`/`LE`: `A_{g₁} < A_{g₂} < ∞`, both with positive shares. -/
def admissible (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : Prop :=
  match k.1 with
  | CompTag.TN =>
      AdoptionDate.isFin (P.A k.2.1) ∧ AdoptionDate.isInf (P.A k.2.2)
        ∧ 0 < P.p k.2.1 ∧ 0 < P.p k.2.2
  | CompTag.EL =>
      P.A k.2.1 < P.A k.2.2 ∧ AdoptionDate.isFin (P.A k.2.2)
        ∧ 0 < P.p k.2.1 ∧ 0 < P.p k.2.2
  | CompTag.LE =>
      P.A k.2.1 < P.A k.2.2 ∧ AdoptionDate.isFin (P.A k.2.2)
        ∧ 0 < P.p k.2.1 ∧ 0 < P.p k.2.2

open Classical in
/-- Comparison index set `𝒦 P : Finset (CompTag × 𝒢 × 𝒢)`, the set of all
admissible 2x2 comparisons. -/
noncomputable def 𝒦 (P : CohortPanel 𝒢 T) : Finset (CompTag × 𝒢 × 𝒢) :=
  (Finset.univ : Finset (CompTag × 𝒢 × 𝒢)).filter (fun k => admissible P k)

open Classical in
/-- Unified normalized weight on the full index `CompTag × 𝒢 × 𝒢`: returns
the matching `w_TN/w_EL/w_LE` on admissible triples and `0` otherwise. -/
noncomputable def weight (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : ℝ :=
  if admissible P k then
    match k.1 with
    | CompTag.TN => w_TN P k.2.1 k.2.2
    | CompTag.EL => w_EL P k.2.1 k.2.2
    | CompTag.LE => w_LE P k.2.1 k.2.2
  else 0

open Classical in
/-- Unified 2x2 contrast on the full index `CompTag × 𝒢 × 𝒢`: returns the
matching `Δ_TN/Δ_EL/Δ_LE` on admissible triples and `0` otherwise. -/
noncomputable def contrast (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : ℝ :=
  if admissible P k then
    match k.1 with
    | CompTag.TN => Δ_TN P k.2.1 k.2.2
    | CompTag.EL => Δ_EL P k.2.1 k.2.2
    | CompTag.LE => Δ_LE P k.2.1 k.2.2
  else 0

open Classical in
/-- Unified raw weight on the full index `CompTag × 𝒢 × 𝒢`: returns the
matching `λ_TN/λ_EL/λ_LE` on admissible triples and `0` otherwise. -/
noncomputable def lambdaWeight (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : ℝ :=
  if admissible P k then
    match k.1 with
    | CompTag.TN => lambdaTN P k.2.1 k.2.2
    | CompTag.EL => lambdaEL P k.2.1 k.2.2
    | CompTag.LE => lambdaLE P k.2.1 k.2.2
  else 0

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
