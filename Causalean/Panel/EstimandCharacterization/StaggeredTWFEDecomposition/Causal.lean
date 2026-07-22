/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): TWFE decomposition under staggered timing — Layer C

**Role in the folder.** *Causal layer (support for the causal headline).*
Provides the potential-outcome corollaries consumed by the fused headline
`CausalDecomposition.lean`. See `StaggeredTWFEDecomposition.lean` for the folder
layer-map.

Layer C — causal characterization of the three 2x2 contrasts. Promotes the
algebraic objects `Δ_TN, Δ_EL, Δ_LE` from Layer A to causal statements about
window-specific ATTs under a two-state potential-outcome simplification.

**Two-state simplification (audit gap G2 / review item A6).**
The paper (Goodman-Bacon 2021, Assumption 1) uses a full adoption-date-indexed
potential-outcome family `Y_{gt}(a)` where `a` ranges over `𝒯 ∪ {∞}`.  Each
cohort `g` has its own path `Y_g(A_g)` for every possible adoption date `a`, and
consistency is stated as `Y_{gt} = Y_{gt}(A_g)`.

This Lean layer flattens that family to two maps:
- `Y0 : 𝒢 → Fin T → ℝ` representing `Y(∞)` (the never-treated path), and
- `Y1 : 𝒢 → Fin T → ℝ` representing `Y(A_g)` (each cohort's own adoption-date path).

This simplification is **sufficient** for the three corollaries proved here
(`Δ_TN_eq_ATT`, `Δ_EL_eq_ATT`, `Δ_LE_eq_bad_comparison`), because Cor 5 of the
paper only ever references `Y_{gt}(A_g)` (own adoption date) or `Y_{gt}(∞)` (the
never-treated state).  The full adoption-date-indexed family `Y_{gt}(a)` is needed
only for more general heterogeneous-treatment comparisons across cohorts with
different adoption dates, which are outside the scope of Cor 5.

In particular, the LE bad-comparison result — showing that `Δ_LE` is contaminated
by `ATT_e(S1_LE) − ATT_e(S0_LE)` when early-treated cohorts serve as controls — is
fully captured by the two-state simplification.  To lift this to the paper's general
`Y_{gt}(a)` family one would introduce a type
`Y_full : 𝒢 → Fin T → WithTop (Fin T) → ℝ` and derive `Y0 g t = Y_full g t ⊤`
and `Y1 g t = Y_full g t (P.A g)` as special slices; this is deferred to a future
`AdoptionPath` module (see audit SH-3).

`Y0` denotes the never-treated path `Y(∞)`, while `Y1` denotes each cohort's
own adoption-date path `Y(A_g)`. This is sufficient for the LE bad-comparison
corollary proved here; it is not the full adoption-date-indexed family
`Y_gt(a)`.

* consistency `Y_{gt} = Y_{gt}(A_g)`,
* no anticipation `t < A_g → Y_{gt}(A_g) = Y_{gt}(∞)`,
* pairwise untreated parallel trends.

The three corollaries (NL doc A6 / LaTeX
`cor:po-estimand-goodman-bacon-causal-characterization`):

* `Δ_TN_eq_ATT` — `Δ_TN P g u = ATT_window Y0 Y1 g (S1_TN P g)`.
* `Δ_EL_eq_ATT` — `Δ_EL P e ℓ = ATT_window Y0 Y1 e (S1_EL P e ℓ)`.
* `Δ_LE_eq_bad_comparison` —
  `Δ_LE P e ℓ = ATT_window Y0 Y1 ℓ (S1_LE P e ℓ)
                  − (ATT_window Y0 Y1 e (S1_LE P e ℓ)
                      − ATT_window Y0 Y1 e (S0_LE P e ℓ))`.

Pure cell-level algebra: window means commute with sums, parallel trends
cancels untreated trends, and consistency + no-anticipation reduce factual
window means to potential-outcome window means. **No** dependence on
`prop:po-did-att`; the proofs are stated directly in terms of the window
mean operator `Ybar0` (the never-treated potential-outcome window mean).

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`.
Source LaTeX:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.tex`.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.FinitePanel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Goodman-Bacon Causal Characterization

This file gives the causal layer of the Goodman-Bacon staggered-timing
decomposition. Under two-state potential-outcome assumptions, consistency, no
anticipation, and pairwise untreated parallel trends, it identifies the
treated-versus-never and early-versus-late contrasts with window-specific
average treatment effects and expresses the late-versus-early contrast with its
bad-comparison adjustment. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

/-- Window mean of a potential-outcome map `Y* : 𝒢 → Fin T → ℝ`,
`Ȳ_{g(*),S} := |S|⁻¹ ∑_{t ∈ S} Y*_{gt}`. Defined unconditionally; nonemptiness
of `S` is supplied at theorem-use time. -/
noncomputable def Ybar0 (Y0 : 𝒢 → Fin T → ℝ) (g : 𝒢) (S : Finset (Fin T)) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ t ∈ S, Y0 g t

/-- Window-specific ATT in the two-state Goodman-Bacon causal layer:
`ATT_{g,S} := |S|⁻¹ ∑_{t ∈ S} (Y_{gt}(A_g) − Y_{gt}(∞))`,
parameterized by potential-outcome maps `Y0 = Y(∞)` and `Y1 = Y(A_g)`. -/
noncomputable def ATT_window (Y0 Y1 : 𝒢 → Fin T → ℝ) (g : 𝒢)
    (S : Finset (Fin T)) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ t ∈ S, (Y1 g t - Y0 g t)

/-- Causal-side assumptions for the Goodman-Bacon decomposition
(LaTeX `ass:po-estimand-goodman-bacon-causal`).

**Two-state simplification (gap G2).** The paper uses a full adoption-date-indexed
family `Y_{gt}(a)`.  Here we use only two maps `Y0 = Y(∞)` and `Y1 = Y(A_g)`,
which suffices for Cor 5 (TN/EL ATT identification and the LE bad-comparison
corollary).  See the file header for a full discussion.

**Redundancy note.** `consistencyTreated` and `consistencyUntreated` together
with `noAnticipation` are slightly over-strong relative to the paper's single
consistency axiom `Y_{gt} = Y_{gt}(A_g)`: on pre-adoption cells, `consistencyUntreated`
gives `Y_{gt} = Y0 g t`, while `noAnticipation` gives `Y1 g t = Y0 g t`, so
together they imply `Y_{gt} = Y1 g t` on pre-adoption cells too.  The split is
kept because each field is used directly in downstream proofs.

* `consistencyTreated` — on treated cells (`A_g ≤ t`), the factual outcome
  equals the post-adoption potential outcome `Y1`.
* `consistencyUntreated` — on untreated cells (`t < A_g`), the factual
  outcome equals the never-treated potential outcome `Y0`. (When combined
  with `noAnticipation`, this is equivalent to consistency.)
* `noAnticipation` — `t < A_g → Y_{gt}(A_g) = Y_{gt}(∞)` (i.e. `Y1 g t = Y0 g t`).
* `parallelTrends_TN`/`parallelTrends_EL`/`parallelTrends_LE` — equal
  untreated trends across the three comparison types; the three-way split
  matches the LaTeX statement, which quantifies over admissible comparisons
  by comparison type. -/
structure CausalAssumptions (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ) :
    Prop where
  /-- Consistency on treated cells: when `A_g ≤ t`, the factual outcome
  equals the post-adoption potential outcome. -/
  consistencyTreated :
    ∀ g t, AdoptionDate.le (P.A g) t → P.Y g t = Y1 g t
  /-- Consistency on untreated cells: when `t < A_g`, the factual outcome
  equals the never-treated potential outcome. -/
  consistencyUntreated :
    ∀ g t, AdoptionDate.lt (P.A g) t → P.Y g t = Y0 g t
  /-- No anticipation: pre-adoption potential outcomes coincide. -/
  noAnticipation :
    ∀ g t, AdoptionDate.lt (P.A g) t → Y1 g t = Y0 g t
  /-- Pairwise untreated parallel trends for treated-vs-never (TN). -/
  parallelTrends_TN :
    ∀ g u, AdoptionDate.isFin (P.A g) → AdoptionDate.isInf (P.A u) →
      Ybar0 Y0 g (S1_TN P g) - Ybar0 Y0 g (S0_TN P g)
        = Ybar0 Y0 u (S1_TN P g) - Ybar0 Y0 u (S0_TN P g)
  /-- Pairwise untreated parallel trends for early-vs-late before late (EL). -/
  parallelTrends_EL :
    ∀ e ℓ, P.A e < P.A ℓ → AdoptionDate.isFin (P.A ℓ) →
      Ybar0 Y0 e (S1_EL P e ℓ) - Ybar0 Y0 e (S0_EL P e ℓ)
        = Ybar0 Y0 ℓ (S1_EL P e ℓ) - Ybar0 Y0 ℓ (S0_EL P e ℓ)
  /-- Pairwise untreated parallel trends for late-vs-early after early (LE). -/
  parallelTrends_LE :
    ∀ e ℓ, P.A e < P.A ℓ → AdoptionDate.isFin (P.A ℓ) →
      Ybar0 Y0 e (S1_LE P e ℓ) - Ybar0 Y0 e (S0_LE P e ℓ)
        = Ybar0 Y0 ℓ (S1_LE P e ℓ) - Ybar0 Y0 ℓ (S0_LE P e ℓ)

namespace CausalAssumptions

variable {P : CohortPanel 𝒢 T} {Y0 Y1 : 𝒢 → Fin T → ℝ}

/-- Helper: `AdoptionDate.lt (P.A g) t` rules out `AdoptionDate.le (P.A g) t`. -/
theorem AdoptionDate.not_le_of_lt {a : WithTop (Fin T)} {t : Fin T}
    (h : AdoptionDate.lt a t) : ¬ AdoptionDate.le a t := by
  intro hle
  exact lt_irrefl _ (lt_of_lt_of_le h hle)

/-- Helper: every period is strictly less than `⊤` in `WithTop (Fin T)`. -/
theorem AdoptionDate.lt_of_isInf {a : WithTop (Fin T)} {t : Fin T}
    (h : AdoptionDate.isInf a) : AdoptionDate.lt a t := by
  unfold AdoptionDate.lt AdoptionDate.isInf at *
  rw [h]
  exact (WithTop.coe_lt_top _ : (t : WithTop (Fin T)) < ⊤)

/-- On the untreated window `S0_TN P g = {t : t < A_g}`, the factual `Ybar`
of cohort `g` equals the never-treated `Ybar0`: by `consistencyUntreated`
on each cell. -/
theorem Ybar_eq_Ybar0_on_S0_TN (hA : CausalAssumptions P Y0 Y1) (g : 𝒢) :
    Ybar P g (S0_TN P g) = Ybar0 Y0 g (S0_TN P g) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htlt : AdoptionDate.lt (P.A g) t := by
    simpa [S0_TN, Finset.mem_filter] using ht
  exact hA.consistencyUntreated g t htlt

/-- On the never-treated cohort `u` (i.e. `A_u = ∞`), every period is
untreated, so on any window `S` the factual `Ybar` equals the
never-treated `Ybar0`. -/
theorem Ybar_eq_Ybar0_of_inf (hA : CausalAssumptions P Y0 Y1)
    {u : 𝒢} (hu : AdoptionDate.isInf (P.A u)) (S : Finset (Fin T)) :
    Ybar P u S = Ybar0 Y0 u S := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t _
  exact hA.consistencyUntreated u t (AdoptionDate.lt_of_isInf hu)

/-- On a window where every cell is treated for cohort `g`, the factual
`Ybar` decomposes as the never-treated mean plus the window ATT. -/
theorem Ybar_eq_Ybar0_add_ATT_of_treated (hA : CausalAssumptions P Y0 Y1)
    (g : 𝒢) (S : Finset (Fin T))
    (hS : ∀ t ∈ S, AdoptionDate.le (P.A g) t) :
    Ybar P g S = Ybar0 Y0 g S + ATT_window Y0 Y1 g S := by
  classical
  unfold Ybar Ybar0 ATT_window
  rw [← mul_add]
  congr 1
  calc
    ∑ t ∈ S, P.Y g t = ∑ t ∈ S, Y1 g t := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      exact hA.consistencyTreated g t (hS t ht)
    _ = ∑ t ∈ S, (Y0 g t + (Y1 g t - Y0 g t)) := by
      refine Finset.sum_congr rfl ?_
      intro t _
      ring
    _ = ∑ t ∈ S, Y0 g t + ∑ t ∈ S, (Y1 g t - Y0 g t) := by
      exact Finset.sum_add_distrib

/-- On the early-cohort untreated window `S0_EL P e ℓ = {t : t < A_e}`, the
factual `Ybar` of cohort `e` equals the never-treated `Ybar0`. -/
theorem Ybar_eq_Ybar0_on_S0_EL (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢) :
    Ybar P e (S0_EL P e ℓ) = Ybar0 Y0 e (S0_EL P e ℓ) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htlt : AdoptionDate.lt (P.A e) t := by
    simpa [S0_EL, Finset.mem_filter] using ht
  exact hA.consistencyUntreated e t htlt

/-- The late-cohort factual `Ybar` on `S1_EL P e ℓ = {A_e ≤ t < A_ℓ}` equals
the never-treated `Ybar0`: each cell satisfies `t < A_ℓ`. -/
theorem Ybar_eq_Ybar0_late_on_S1_EL (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢) :
    Ybar P ℓ (S1_EL P e ℓ) = Ybar0 Y0 ℓ (S1_EL P e ℓ) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htmem : AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t := by
    simpa [S1_EL, Finset.mem_filter] using ht
  exact hA.consistencyUntreated ℓ t htmem.2

/-- The late-cohort factual `Ybar` on `S0_EL P e ℓ = {t : t < A_e}` equals
the never-treated `Ybar0` when `A_e < A_ℓ`. -/
theorem Ybar_eq_Ybar0_late_on_S0_EL (hA : CausalAssumptions P Y0 Y1)
    (e ℓ : 𝒢) (h_lt : P.A e < P.A ℓ) :
    Ybar P ℓ (S0_EL P e ℓ) = Ybar0 Y0 ℓ (S0_EL P e ℓ) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htlt : (t : WithTop (Fin T)) < P.A e := by
    simpa [S0_EL, Finset.mem_filter, AdoptionDate.lt] using ht
  exact hA.consistencyUntreated ℓ t (by
    simpa [AdoptionDate.lt] using lt_trans htlt h_lt)

/-- The late-cohort factual `Ybar` on `S0_LE P e ℓ = {A_e ≤ t < A_ℓ}` equals
the never-treated `Ybar0`. -/
theorem Ybar_eq_Ybar0_late_on_S0_LE (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢) :
    Ybar P ℓ (S0_LE P e ℓ) = Ybar0 Y0 ℓ (S0_LE P e ℓ) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htmem : AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t := by
    simpa [S0_LE, Finset.mem_filter] using ht
  exact hA.consistencyUntreated ℓ t htmem.2

end CausalAssumptions

/-- **Layer C corollary 1 — TN identifies ATT.** Under
`CausalAssumptions P Y0 Y1`, for every admissible treated-versus-never pair
`(g, u)` with `A_g < ∞` and `A_u = ∞`,

    Δ_TN P g u = ATT_window Y0 Y1 g (S1_TN P g).

Proof outline:
1. Replace `Ybar P u (S1_TN P g)` and `Ybar P u (S0_TN P g)` by `Ybar0 Y0 u …`
   via `Ybar_eq_Ybar0_of_inf` (cohort `u` is never treated).
2. Replace `Ybar P g (S0_TN P g)` by `Ybar0 Y0 g (S0_TN P g)` via
   `Ybar_eq_Ybar0_on_S0_TN` (pre-adoption + no anticipation).
3. Apply `parallelTrends_TN` to cancel `(Ybar0 Y0 g S1) - (Ybar0 Y0 g S0)`
   against `(Ybar0 Y0 u S1) - (Ybar0 Y0 u S0)`.
4. The remainder reduces to `Ybar P g (S1_TN P g) - Ybar0 Y0 g (S1_TN P g)`,
   which by consistency on `S1_TN` (treated cells) and the `ATT_window`
   definition equals `ATT_window Y0 Y1 g (S1_TN P g)`. -/
theorem Δ_TN_eq_ATT (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (g u : 𝒢)
    (h_g_fin : AdoptionDate.isFin (P.A g))
    (h_u_inf : AdoptionDate.isInf (P.A u)) :
    Δ_TN P g u = ATT_window Y0 Y1 g (S1_TN P g) := by
  classical
  have h_treated :
      Ybar P g (S1_TN P g) =
        Ybar0 Y0 g (S1_TN P g) + ATT_window Y0 Y1 g (S1_TN P g) := by
    exact hA.Ybar_eq_Ybar0_add_ATT_of_treated g (S1_TN P g) (by
      intro t ht
      simpa [S1_TN, Finset.mem_filter] using ht)
  have h_g0 := hA.Ybar_eq_Ybar0_on_S0_TN g
  have h_u1 := hA.Ybar_eq_Ybar0_of_inf h_u_inf (S1_TN P g)
  have h_u0 := hA.Ybar_eq_Ybar0_of_inf h_u_inf (S0_TN P g)
  have hPT := hA.parallelTrends_TN g u h_g_fin h_u_inf
  unfold Δ_TN
  rw [h_treated, h_g0, h_u1, h_u0]
  linarith

/-- **Layer C corollary 2 — EL identifies the early cohort's ATT.** Under
`CausalAssumptions P Y0 Y1`, for every admissible early-versus-late pair
`(e, ℓ)` with `A_e < A_ℓ < ∞`,

    Δ_EL P e ℓ = ATT_window Y0 Y1 e (S1_EL P e ℓ).

Proof outline:
1. Replace `Ybar P ℓ (S1_EL P e ℓ)` and `Ybar P ℓ (S0_EL P e ℓ)` by
   `Ybar0 Y0 ℓ …` (late cohort is untreated on both EL windows since they
   sit before `A_ℓ`).
2. Replace `Ybar P e (S0_EL P e ℓ)` by `Ybar0 Y0 e …` via
   `Ybar_eq_Ybar0_on_S0_EL`.
3. Apply `parallelTrends_EL` to cancel the late-cohort contribution.
4. The remainder is `Ybar P e (S1_EL P e ℓ) - Ybar0 Y0 e (S1_EL P e ℓ) =
   ATT_window Y0 Y1 e (S1_EL P e ℓ)` by consistency on the treated window. -/
theorem Δ_EL_eq_ATT (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢)
    (h_lt : P.A e < P.A ℓ) (h_ℓ_fin : AdoptionDate.isFin (P.A ℓ)) :
    Δ_EL P e ℓ = ATT_window Y0 Y1 e (S1_EL P e ℓ) := by
  classical
  have h_e1 :
      Ybar P e (S1_EL P e ℓ) =
        Ybar0 Y0 e (S1_EL P e ℓ) + ATT_window Y0 Y1 e (S1_EL P e ℓ) := by
    exact hA.Ybar_eq_Ybar0_add_ATT_of_treated e (S1_EL P e ℓ) (by
      intro t ht
      have htmem :
          AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t := by
        simpa [S1_EL, Finset.mem_filter] using ht
      exact htmem.1)
  have h_e0 := hA.Ybar_eq_Ybar0_on_S0_EL e ℓ
  have h_l1 := hA.Ybar_eq_Ybar0_late_on_S1_EL e ℓ
  have h_l0 := hA.Ybar_eq_Ybar0_late_on_S0_EL e ℓ h_lt
  have hPT := hA.parallelTrends_EL e ℓ h_lt h_ℓ_fin
  unfold Δ_EL
  rw [h_e1, h_e0, h_l1, h_l0]
  linarith

/-- **Layer C corollary 3 — LE has a bad-comparison term.** Under
`CausalAssumptions P Y0 Y1`, for every admissible late-versus-early pair
`(e, ℓ)` with `A_e < A_ℓ < ∞`,

    Δ_LE P e ℓ
      = ATT_window Y0 Y1 ℓ (S1_LE P e ℓ)
        − (ATT_window Y0 Y1 e (S1_LE P e ℓ)
            − ATT_window Y0 Y1 e (S0_LE P e ℓ)).

Proof outline:
1. The late cohort `ℓ` is untreated on `S0_LE P e ℓ = {A_e ≤ t < A_ℓ}` so
   `Ybar P ℓ (S0_LE P e ℓ) = Ybar0 Y0 ℓ …`.
2. On `S1_LE P e ℓ = {A_ℓ ≤ t}`, `ℓ` is treated, so consistency gives
   `Ybar P ℓ (S1_LE P e ℓ) = Ybar0 Y0 ℓ … + ATT_window Y0 Y1 ℓ …`.
3. Cohort `e` is treated on both `S0_LE` and `S1_LE` (since `A_e < A_ℓ`
   means `A_e ≤ t` whenever `t ∈ S0_LE` or `t ∈ S1_LE`); decompose
   `Ybar P e S = Ybar0 Y0 e S + ATT_window Y0 Y1 e S` for each window.
4. Apply `parallelTrends_LE` to cancel `Ybar0 Y0 ℓ` differences against
   `Ybar0 Y0 e` differences; the residual ATT terms produce the
   bad-comparison expression. -/
theorem Δ_LE_eq_bad_comparison (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢)
    (h_lt : P.A e < P.A ℓ) (h_ℓ_fin : AdoptionDate.isFin (P.A ℓ)) :
    Δ_LE P e ℓ
      = ATT_window Y0 Y1 ℓ (S1_LE P e ℓ)
        - (ATT_window Y0 Y1 e (S1_LE P e ℓ)
            - ATT_window Y0 Y1 e (S0_LE P e ℓ)) := by
  classical
  have h_l1 :
      Ybar P ℓ (S1_LE P e ℓ) =
        Ybar0 Y0 ℓ (S1_LE P e ℓ) + ATT_window Y0 Y1 ℓ (S1_LE P e ℓ) := by
    exact hA.Ybar_eq_Ybar0_add_ATT_of_treated ℓ (S1_LE P e ℓ) (by
      intro t ht
      simpa [S1_LE, Finset.mem_filter] using ht)
  have h_l0 := hA.Ybar_eq_Ybar0_late_on_S0_LE e ℓ
  have h_e0 :
      Ybar P e (S0_LE P e ℓ) =
        Ybar0 Y0 e (S0_LE P e ℓ) + ATT_window Y0 Y1 e (S0_LE P e ℓ) := by
    exact hA.Ybar_eq_Ybar0_add_ATT_of_treated e (S0_LE P e ℓ) (by
      intro t ht
      have htmem :
          AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t := by
        simpa [S0_LE, Finset.mem_filter] using ht
      exact htmem.1)
  have h_e1 :
      Ybar P e (S1_LE P e ℓ) =
        Ybar0 Y0 e (S1_LE P e ℓ) + ATT_window Y0 Y1 e (S1_LE P e ℓ) := by
    exact hA.Ybar_eq_Ybar0_add_ATT_of_treated e (S1_LE P e ℓ) (by
      intro t ht
      have hle : AdoptionDate.le (P.A ℓ) t := by
        simpa [S1_LE, Finset.mem_filter] using ht
      exact le_of_lt (lt_of_lt_of_le h_lt hle))
  have hPT := hA.parallelTrends_LE e ℓ h_lt h_ℓ_fin
  unfold Δ_LE
  rw [h_l1, h_l0, h_e1, h_e0]
  linarith

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
