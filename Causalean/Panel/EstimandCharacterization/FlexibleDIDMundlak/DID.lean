/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Wooldridge flexible imputation / POLS / ETWFE DID characterization

Finite-cell first declarations for the staggered-adoption DID characterization:
primitive cohort shares, covariate weights, conditional means, explicit
support/full-rank assumptions, finite-cell normal equations, and cell/aggregate
ATT equality theorems.
-/

import Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.TWFE

/-! # Wooldridge Flexible DID Cells

This file provides finite-cell primitives for Wooldridge-style flexible
imputation, pooled least squares, and extended two-way fixed effects
difference-in-differences estimands. It defines staggered-adoption cell means,
support conditions, untreated-outcome regressions, normal-equation-based
POLS/ETWFE coefficients, and aggregate ATT quantities. The main public theorem
is `flexible_did_scaffold_characterization`, the finite-cell characterization, with cell and aggregate components
available as `flexible_did_cell_characterization` and
`flexible_did_aggregate_characterization`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open Finset

variable {Cohort Time Covar : Type*}
  [Fintype Cohort] [Fintype Time] [Fintype Covar]

/-- Finite staggered-adoption cell system. `treatedCell g t` is the target
cohort-time set `q ≤ g ≤ t ≤ T`; `untreatedCell g t` marks observations used
to fit the untreated-outcome regression. Conditional expectations are encoded
as primitive finite-cell means. -/
structure StaggeredATTCells (Cohort Time Covar : Type*)
    [Fintype Cohort] [Fintype Time] [Fintype Covar] where
  cohortShare : Cohort → ℝ
  covarWeight : Cohort → Covar → ℝ
  treatedCell : Cohort → Time → Prop
  untreatedCell : Cohort → Time → Prop
  Y0Mean : Cohort → Time → Covar → ℝ
  YgMean : Cohort → Time → Covar → ℝ
  observedMean : Cohort → Time → Covar → ℝ
  cohortShare_pos_on_treated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t → 0 < cohortShare g
  covarWeight_nonneg : ∀ g c, 0 ≤ covarWeight g c
  covarWeight_sum_one : ∀ g, ∑ c, covarWeight g c = 1
  consistency_treated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t →
      ∀ c, observedMean g t c = YgMean g t c
  consistency_untreated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, untreatedCell g t →
      ∀ c, observedMean g t c = Y0Mean g t c

namespace StaggeredATTCells

open Classical in
/-- Treated cohort-time support set `C_tr`. -/
noncomputable def treatedCells (P : StaggeredATTCells Cohort Time Covar) :
    Finset (Cohort × Time) :=
  (Finset.univ : Finset (Cohort × Time)).filter (fun gt => P.treatedCell gt.1 gt.2)

open Classical in
/-- Untreated cohort-time design set used to fit the untreated-outcome
regression (the support of the weighted projection that produces `m0`). -/
noncomputable def untreatedCells (P : StaggeredATTCells Cohort Time Covar) :
    Finset (Cohort × Time) :=
  (Finset.univ : Finset (Cohort × Time)).filter (fun gt => P.untreatedCell gt.1 gt.2)

/-- ATT cell `τ_gt`, averaged over baseline covariate cells within cohort. -/
noncomputable def tauCell (P : StaggeredATTCells Cohort Time Covar)
    (g : Cohort) (t : Time) : ℝ :=
  ∑ c, P.covarWeight g c * (P.YgMean g t c - P.Y0Mean g t c)

/-- Aggregate ATT for requested finite treated-cell weights. -/
noncomputable def tauAgg (P : StaggeredATTCells Cohort Time Covar)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * P.tauCell gt.1 gt.2

end StaggeredATTCells

/-- Nonnegative aggregate weights summing to one on the target treated cells. -/
structure AggregateWeights (P : StaggeredATTCells Cohort Time Covar) where
  weight : Cohort → Time → ℝ
  nonneg_on_treated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t → 0 ≤ weight g t
  sum_treated : ∑ gt ∈ P.treatedCells, weight gt.1 gt.2 = 1

/-- No anticipation: before adoption, the cohort-`g` potential outcome equals
the untreated potential outcome. Here `untreatedCell` marks the relevant
pre-treatment / not-yet-treated observations. -/
def NoAnticipation (P : StaggeredATTCells Cohort Time Covar) : Prop :=
  ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t →
    ∀ c, P.YgMean g t c = P.Y0Mean g t c

/-- Conditional parallel trends, represented by the equivalent additive
untreated mean form `m0(g,t,c) = α(g,c) + λ(t,c)`. -/
def ConditionalParallelTrendsAdditive
    (P : StaggeredATTCells Cohort Time Covar) : Prop :=
  ∃ α : Cohort → Covar → ℝ, ∃ lam : Time → Covar → ℝ,
    ∀ g t c, P.Y0Mean g t c = α g c + lam t c

/-- An additive function `d(g,t,c) = γ(g,c) + δ(t,c)` of the cohort/time/covariate
cell, the difference class used to compare two additive untreated-mean
representations. -/
def IsCellAdditive (d : Cohort → Time → Covar → ℝ) : Prop :=
  ∃ γ : Cohort → Covar → ℝ, ∃ δ : Time → Covar → ℝ,
    ∀ g t c, d g t c = γ g c + δ t c

/-- Connected untreated design and full-rank identification condition.

Saturating the untreated design with enough connected cells to pin down the
additive `α_{g,c} + λ_{t,c}` parameters is represented by the statement that an
additive cell function vanishing on every untreated cell must also vanish on
every treated cell. Equivalently, there is no nonzero additive function
supported only off the untreated design. -/
def UntreatedDesignIdentifies (P : StaggeredATTCells Cohort Time Covar) : Prop :=
  ∀ d : Cohort → Time → Covar → ℝ, IsCellAdditive (Cohort := Cohort) d →
    (∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t → ∀ c, d g t c = 0) →
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t → ∀ c, d g t c = 0

/-- Saturated untreated-outcome regression and its support/identification
conditions.

The fitted untreated mean `m0(g,t,c)` is additive in cohort/time conditional on
covariates. The field `untreatedNormalEq` states the weighted least-squares
normal equations for projecting the observed outcome onto this additive class
using untreated observations only: against every additive test function, the
covariate/cell-weighted residual `observedMean - m0` sums to zero on the
untreated design.

The exact-fit facts are proved below rather than stored as fields:
`untreatedFit` derives agreement on untreated cells from the normal equations,
no anticipation, and conditional parallel trends, while `recovers_target_Y0`
uses `UntreatedDesignIdentifies` to extend the untreated-outcome fit to target
treated cells. The companion population bridge relates these finite-cell means
to conditional expectations. -/
structure SaturatedUntreatedRegression
    (P : StaggeredATTCells Cohort Time Covar) where
  m0 : Cohort → Time → Covar → ℝ
  additive :
    ∃ α : Cohort → Covar → ℝ, ∃ lam : Time → Covar → ℝ,
      ∀ g t c, m0 g t c = α g c + lam t c
  /-- Nonnegative covariate/cell weights of the untreated-only projection. -/
  untreatedWeight : Cohort → Time → Covar → ℝ
  /-- The projection weights are strictly positive on the untreated design
  (positive probability of each untreated observation cell). -/
  untreatedWeight_pos :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t →
      ∀ c, 0 < untreatedWeight g t c
  /-- Finite-cell projection origin of `m0`: `m0` solves the weighted
  least-squares normal equations for the observed outcome on the additive class
  `H0`, using only untreated observations: against every additive test function
  the covariate/cell-weighted residual `observedMean − m0` over the untreated
  design vanishes. -/
  untreatedNormalEq :
    ∀ d : Cohort → Time → Covar → ℝ, IsCellAdditive (Cohort := Cohort) d →
      ∑ gt ∈ P.untreatedCells, ∑ c,
          untreatedWeight gt.1 gt.2 c *
            (P.observedMean gt.1 gt.2 c - m0 gt.1 gt.2 c) * d gt.1 gt.2 c = 0
  design_identifies : UntreatedDesignIdentifies P
  target_cell_support :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t → 0 < P.cohortShare g

namespace SaturatedUntreatedRegression

/-- The weighted projection `m0` reproduces the factual cohort-`g` outcome mean
on every untreated cell.

Proof: under no anticipation the untreated observed mean equals the cohort-`g`
mean, and under conditional parallel trends it is additive (lies in `H0`).  The
residual `m0 − Y0Mean` is then itself additive (`additive` + `hCPT`); plugging it
into the weighted untreated normal equations (`untreatedNormalEq`) shows the
positively-weighted sum of its squares over the untreated design vanishes, so the
residual is zero on every untreated cell — the projection is exact there. -/
theorem untreatedFit
    {P : StaggeredATTCells Cohort Time Covar}
    (S : SaturatedUntreatedRegression P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    ⦃g : Cohort⦄ ⦃t : Time⦄ (hgt : P.untreatedCell g t) (c : Covar) :
    S.m0 g t c = P.YgMean g t c := by
  classical
  obtain ⟨αy, lamy, hy⟩ := hCPT
  obtain ⟨αm, lamm, hm⟩ := S.additive
  set d : Cohort → Time → Covar → ℝ :=
    fun g t c => S.m0 g t c - P.Y0Mean g t c with hd
  have hd_add : IsCellAdditive (Cohort := Cohort) d := by
    refine ⟨fun g c => αm g c - αy g c, fun t c => lamm t c - lamy t c, ?_⟩
    intro g t c
    simp only [hd, hm, hy]; ring
  have hne := S.untreatedNormalEq d hd_add
  -- The positively-weighted squared residual over the untreated design vanishes.
  have hsq :
      (∑ gt ∈ P.untreatedCells, ∑ c,
          S.untreatedWeight gt.1 gt.2 c * (d gt.1 gt.2 c) ^ 2) = 0 := by
    have hQR :
        (∑ gt ∈ P.untreatedCells, ∑ c,
            S.untreatedWeight gt.1 gt.2 c * (d gt.1 gt.2 c) ^ 2)
          + (∑ gt ∈ P.untreatedCells, ∑ c,
              S.untreatedWeight gt.1 gt.2 c *
                (P.observedMean gt.1 gt.2 c - S.m0 gt.1 gt.2 c) * d gt.1 gt.2 c)
          = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero ?_
      intro gt hgt_mem
      have hut : P.untreatedCell gt.1 gt.2 := by
        simpa [StaggeredATTCells.untreatedCells] using hgt_mem
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero ?_
      intro c _
      have hobs : P.observedMean gt.1 gt.2 c = P.Y0Mean gt.1 gt.2 c :=
        P.consistency_untreated hut c
      simp only [hd]
      rw [hobs]; ring
    linarith [hQR, hne]
  -- Extract the single untreated cell `(g,t)` and covariate `c`.
  have hmem : (g, t) ∈ P.untreatedCells := by
    simp only [StaggeredATTCells.untreatedCells, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hgt
  have hrow_nonneg :
      ∀ gt ∈ P.untreatedCells,
        0 ≤ ∑ c, S.untreatedWeight gt.1 gt.2 c * (d gt.1 gt.2 c) ^ 2 := by
    intro gt hgt_mem
    have hut : P.untreatedCell gt.1 gt.2 := by
      simpa [StaggeredATTCells.untreatedCells] using hgt_mem
    exact Finset.sum_nonneg fun c _ =>
      mul_nonneg (le_of_lt (S.untreatedWeight_pos hut c)) (sq_nonneg _)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg hrow_nonneg).mp hsq (g, t) hmem
  have hcell_nonneg :
      ∀ c' ∈ (Finset.univ : Finset Covar),
        0 ≤ S.untreatedWeight g t c' * (d g t c') ^ 2 :=
    fun c' _ => mul_nonneg (le_of_lt (S.untreatedWeight_pos hgt c')) (sq_nonneg _)
  have hcell :=
    (Finset.sum_eq_zero_iff_of_nonneg hcell_nonneg).mp hrow c (Finset.mem_univ c)
  have hw := S.untreatedWeight_pos hgt c
  have hd0 : d g t c = 0 := by
    have hsq0 : (d g t c) ^ 2 = 0 :=
      (mul_eq_zero.mp hcell).resolve_left (ne_of_gt hw)
    exact pow_eq_zero_iff (by norm_num) |>.mp hsq0
  have hm0 : S.m0 g t c = P.Y0Mean g t c := by
    have hh := hd0; simp only [hd] at hh; linarith
  rw [hm0]; exact (hNA hgt c).symm

/-- Under no anticipation and conditional parallel trends, the saturated
untreated regression recovers the untreated
potential-outcome mean on every treated cell.

Proof: on the untreated design, `m0` reproduces the factual cohort-`g` mean
(`untreatedFit`), which no anticipation turns into the untreated-outcome mean
(`hNA`).  Both `m0` and `Y0Mean` are additive (`additive`, `hCPT`), so their
difference is an additive cell function vanishing on every untreated cell; the
connected/full-rank identifiability condition (`design_identifies`) extends that
vanishing to every treated cell, giving `m0 = Y0Mean` there. -/
theorem recovers_target_Y0
    {P : StaggeredATTCells Cohort Time Covar}
    (S : SaturatedUntreatedRegression P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    ⦃g : Cohort⦄ ⦃t : Time⦄ (hgt : P.treatedCell g t) (c : Covar) :
    S.m0 g t c = P.Y0Mean g t c := by
  classical
  obtain ⟨αm, lamm, hm⟩ := S.additive
  obtain ⟨αy, lamy, hy⟩ := id hCPT
  -- The difference of the two additive representations.
  set d : Cohort → Time → Covar → ℝ :=
    fun g t c => S.m0 g t c - P.Y0Mean g t c with hd
  have hd_add : IsCellAdditive (Cohort := Cohort) d := by
    refine ⟨fun g c => αm g c - αy g c, fun t c => lamm t c - lamy t c, ?_⟩
    intro g t c
    simp only [hd, hm, hy]; ring
  have hd_untreated :
      ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t → ∀ c, d g t c = 0 := by
    intro g t hut c
    have h1 : S.m0 g t c = P.Y0Mean g t c := by
      rw [S.untreatedFit hNA hCPT hut c, hNA hut c]
    simp [hd, h1]
  have hzero : d g t c = 0 := S.design_identifies d hd_add hd_untreated hgt c
  have := sub_eq_zero.mp (by simpa [hd] using hzero)
  exact this

end SaturatedUntreatedRegression

/-- Imputation residual mean for a treated cohort-time cell.

The companion file `FlexibleDIDMundlak/PopulationBridge.lean` connects this
finite covariate-weighted average of cell residuals to the corresponding
population conditional expectation when the cell weights are conditional
probabilities and the residuals are within-cell conditional means. -/
noncomputable def imputationTheta (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P) (g : Cohort) (t : Time) : ℝ :=
  ∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c)

/-- Finite-cell residual normal equation for a cell coefficient.  With
baseline-covariate weights summing to one inside cohort `g`, this pins down
the unique coefficient as the imputation residual mean. -/
def cellResidualNormalEq (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P) (theta : ℝ) (g : Cohort) (t : Time) :
    Prop :=
  ∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c - theta) = 0

/-- A finite-cell residual normal equation identifies the coefficient with
the imputation residual mean. -/
theorem cellResidualNormalEq_eq_imputationTheta
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    {theta : ℝ} {g : Cohort} {t : Time}
    (hθ : cellResidualNormalEq P S theta g t) :
    theta = imputationTheta P S g t := by
  unfold cellResidualNormalEq at hθ
  unfold imputationTheta
  have hsum :
      (∑ c, P.covarWeight g c *
          (P.observedMean g t c - S.m0 g t c - theta)) =
        (∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c)) -
          (∑ c, P.covarWeight g c) * theta := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  have hnormal :
      (∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c)) -
          theta = 0 := by
    calc
      (∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c)) - theta
          = (∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c)) -
              (∑ c, P.covarWeight g c) * theta := by
                rw [P.covarWeight_sum_one g]
                ring
      _ = ∑ c, P.covarWeight g c *
            (P.observedMean g t c - S.m0 g t c - theta) := by
              rw [hsum]
      _ = 0 := hθ
  exact (sub_eq_zero.mp hnormal).symm

/-- Saturated treated-cell indicator `1{(g',t') = (g,t)}` (the POLS/ETWFE
treated regressor for cell `(g,t)`). -/
noncomputable def cellIndicator [DecidableEq Cohort] [DecidableEq Time]
    (g : Cohort) (t : Time) : Cohort → Time → ℝ :=
  fun g' t' => if g' = g ∧ t' = t then 1 else 0

/-- Saturated block-diagonalization for treated-cell indicators.

Because the treated-cell indicators are saturated — one indicator per cell — the
*full* POLS/ETWFE
normal equation for the indicator of cell `(g,t)`, namely the covariate-weighted
residual summed against `cellIndicator g t` over the entire cohort×time design,
collapses to that single cell's residual sum.  Hence the per-cell residual
normal equation `cellResidualNormalEq` *is* the full saturated normal equation
for cell `(g,t)`, not an extra simplification: the cross-cell terms vanish by
orthogonality of the saturated indicators.  This is the concrete content behind
the `pols_cell_normalEq` / `etwfe_cell_normalEq` fields below. -/
theorem cellIndicator_normalEq_eq_cellResidual
    [DecidableEq Cohort] [DecidableEq Time]
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P) (theta : ℝ) (g : Cohort) (t : Time) :
    (∑ g', ∑ t', ∑ c, cellIndicator g t g' t' *
        P.covarWeight g' c * (P.observedMean g' t' c - S.m0 g' t' c
          - cellIndicator g t g' t' * theta) = 0)
      ↔ cellResidualNormalEq P S theta g t := by
  classical
  unfold cellResidualNormalEq cellIndicator
  -- The full saturated sum collapses to the single-cell residual sum, because
  -- the saturated indicator vanishes off cell `(g,t)`.
  have hcollapse :
      (∑ g', ∑ t', ∑ c, (if g' = g ∧ t' = t then (1 : ℝ) else 0) *
          P.covarWeight g' c * (P.observedMean g' t' c - S.m0 g' t' c
            - (if g' = g ∧ t' = t then (1 : ℝ) else 0) * theta))
        = ∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c - theta) := by
    rw [Finset.sum_eq_single g, Finset.sum_eq_single t]
    · refine Finset.sum_congr rfl ?_
      intro c _
      simp
    · intro t' _ ht'
      refine Finset.sum_eq_zero ?_
      intro c _
      simp [ht']
    · intro hg; simp at hg
    · intro g' _ hg'
      refine Finset.sum_eq_zero ?_
      intro t' _
      refine Finset.sum_eq_zero ?_
      intro c _
      simp [hg']
    · intro hg; simp at hg
  rw [hcollapse]

/-- Flexible imputation, POLS, and ETWFE cell estimands. POLS and ETWFE are
kept as coding-free cell coefficients. Their equality to imputation is derived
from finite-cell residual normal equations, not stored as direct equality
fields.

`pols_cell_normalEq` and `etwfe_cell_normalEq` carry the per-cell FWL output of
the saturated regression: the covariate-weighted residual normal equation for
each treated cell. By `cellIndicator_normalEq_eq_cellResidual`, this per-cell
equation is equivalent to the full saturated normal equation for that cell's
treated indicator. The ETWFE leg additionally uses the FWL/TWFE-Mundlak
residualization from `TWFE.lean` to identify its residualized treated regressor
with the POLS one; that identification is recorded by sharing the same
`cellResidualNormalEq` form. -/
structure FlexibleDIDEstimands (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P) where
  thetaImp : Cohort → Time → ℝ
  thetaPOLS : Cohort → Time → ℝ
  thetaETWFE : Cohort → Time → ℝ
  thetaImp_eq_imputation :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      thetaImp g t = imputationTheta P S g t
  pols_cell_normalEq :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      cellResidualNormalEq P S (thetaPOLS g t) g t
  etwfe_cell_normalEq :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      cellResidualNormalEq P S (thetaETWFE g t) g t

namespace FlexibleDIDEstimands

/-- POLS cell coefficients equal imputation because their finite-cell residual
normal equation identifies the same weighted residual mean. -/
theorem thetaPOLS_eq_imputationTheta
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaPOLS g t = imputationTheta P S g t :=
  cellResidualNormalEq_eq_imputationTheta P S (E.pols_cell_normalEq hgt)

/-- ETWFE cell coefficients equal imputation because the FWL/TWFE-Mundlak
bridge supplies the same finite-cell residualized normal equation. -/
theorem thetaETWFE_eq_imputationTheta
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaETWFE g t = imputationTheta P S g t :=
  cellResidualNormalEq_eq_imputationTheta P S (E.etwfe_cell_normalEq hgt)

/-- Compatibility alias: the POLS/imputation equality is now derived from the
POLS normal equation, rather than stored as a field. -/
theorem pols_cell_eq_imputation
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaPOLS g t = E.thetaImp g t := by
  rw [E.thetaPOLS_eq_imputationTheta P S hgt, E.thetaImp_eq_imputation hgt]

/-- Compatibility alias: ETWFE/POLS equality is now derived by solving both
finite-cell normal equations, rather than stored as a field. -/
theorem etwfe_cell_eq_pols
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaETWFE g t = E.thetaPOLS g t := by
  rw [E.thetaETWFE_eq_imputationTheta P S hgt,
    E.thetaPOLS_eq_imputationTheta P S hgt]

end FlexibleDIDEstimands

/-- Aggregate estimand for the imputation coefficients. -/
noncomputable def psiImp (P : StaggeredATTCells Cohort Time Covar)
    {S : SaturatedUntreatedRegression P} (E : FlexibleDIDEstimands P S)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * E.thetaImp gt.1 gt.2

/-- Aggregate estimand for the flexible POLS coefficients. -/
noncomputable def psiPOLS (P : StaggeredATTCells Cohort Time Covar)
    {S : SaturatedUntreatedRegression P} (E : FlexibleDIDEstimands P S)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * E.thetaPOLS gt.1 gt.2

/-- Aggregate estimand for the flexible ETWFE coefficients. -/
noncomputable def psiETWFE (P : StaggeredATTCells Cohort Time Covar)
    {S : SaturatedUntreatedRegression P} (E : FlexibleDIDEstimands P S)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * E.thetaETWFE gt.1 gt.2

/-- Imputation recovers the ATT cell once the saturated untreated prediction
equals the untreated potential-outcome mean in target cells. -/
theorem imputationTheta_eq_tauCell
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaImp g t = P.tauCell g t := by
  rw [E.thetaImp_eq_imputation hgt]
  unfold imputationTheta StaggeredATTCells.tauCell
  refine Finset.sum_congr rfl ?_
  intro c _hc
  rw [P.consistency_treated hgt c, S.recovers_target_Y0 hNA hCPT hgt c]

/-- Cell-level characterization: once the untreated-regression witness recovers
target untreated means and the POLS/ETWFE cell coefficients satisfy their
finite-cell residual normal equations, all three equal the ATT cell. -/
theorem flexible_did_cell_characterization
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaImp g t = P.tauCell g t ∧
      E.thetaPOLS g t = P.tauCell g t ∧
      E.thetaETWFE g t = P.tauCell g t := by
  have himp : E.thetaImp g t = P.tauCell g t :=
    imputationTheta_eq_tauCell P S E hNA hCPT hgt
  have hpols : E.thetaPOLS g t = P.tauCell g t := by
    rw [E.pols_cell_eq_imputation P S hgt, himp]
  have hetwfe : E.thetaETWFE g t = P.tauCell g t := by
    rw [E.etwfe_cell_eq_pols P S hgt, hpols]
  exact ⟨himp, hpols, hetwfe⟩

/-- Compatibility theorem for the cell characterization name used by earlier
clients. The proof uses normal-equation-derived equalities. -/
theorem flexible_did_cell_characterization_of_estimand_equalities
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaImp g t = P.tauCell g t ∧
      E.thetaPOLS g t = P.tauCell g t ∧
      E.thetaETWFE g t = P.tauCell g t :=
  flexible_did_cell_characterization P S E hNA hCPT hgt

/-- Aggregate characterization: every requested nonnegative treated-cell
weighting of the three bundled estimands equals the weighted ATT aggregate. -/
theorem flexible_did_aggregate_characterization
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    (a : AggregateWeights P) :
    psiImp P E a.weight = P.tauAgg a.weight ∧
      psiPOLS P E a.weight = P.tauAgg a.weight ∧
      psiETWFE P E a.weight = P.tauAgg a.weight := by
  classical
  have hcell :
      ∀ gt ∈ P.treatedCells,
        E.thetaImp gt.1 gt.2 = P.tauCell gt.1 gt.2 ∧
          E.thetaPOLS gt.1 gt.2 = P.tauCell gt.1 gt.2 ∧
          E.thetaETWFE gt.1 gt.2 = P.tauCell gt.1 gt.2 := by
    intro gt hgt_mem
    have hgt : P.treatedCell gt.1 gt.2 := by
      simpa [StaggeredATTCells.treatedCells] using hgt_mem
    exact flexible_did_cell_characterization P S E hNA hCPT hgt
  constructor
  · unfold psiImp StaggeredATTCells.tauAgg
    refine Finset.sum_congr rfl ?_
    intro gt hgt
    rw [(hcell gt hgt).1]
  constructor
  · unfold psiPOLS StaggeredATTCells.tauAgg
    refine Finset.sum_congr rfl ?_
    intro gt hgt
    rw [(hcell gt hgt).2.1]
  · unfold psiETWFE StaggeredATTCells.tauAgg
    refine Finset.sum_congr rfl ?_
    intro gt hgt
    rw [(hcell gt hgt).2.2]

/-- Compatibility theorem for the aggregate characterization name used by
earlier clients. The proof uses normal-equation-derived cell equalities. -/
theorem flexible_did_aggregate_characterization_of_estimand_equalities
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    (a : AggregateWeights P) :
    psiImp P E a.weight = P.tauAgg a.weight ∧
      psiPOLS P E a.weight = P.tauAgg a.weight ∧
      psiETWFE P E a.weight = P.tauAgg a.weight :=
  flexible_did_aggregate_characterization P S E hNA hCPT a

/-- **Headline finite-cell characterization** (Wooldridge, Theorem B).

Under **no anticipation** (`hNA`) and **conditional parallel trends**
(`hCPT`) — the two causal assumptions the source proof invokes — together with
the saturated untreated regression `S` and the POLS/ETWFE finite-cell residual
normal equations carried by `E`, the flexible imputation, POLS, and ETWFE cell
estimands all equal the ATT cell `τ_gt`, and hence every nonnegative weighted
aggregate equals `τ_agg(a)`.

The assumptions `hNA` and `hCPT` drive
`SaturatedUntreatedRegression.recovers_target_Y0`, which feeds
`imputationTheta_eq_tauCell`. The POLS/ETWFE legs are pinned to the imputation
residual through the cell residual normal equations carried by `E`; see
`FlexibleDIDEstimands` for the saturated-regression interface. -/
theorem flexible_did_scaffold_characterization
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P) :
    (∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      E.thetaImp g t = P.tauCell g t ∧
        E.thetaPOLS g t = P.tauCell g t ∧
        E.thetaETWFE g t = P.tauCell g t) ∧
      (∀ a : AggregateWeights P,
        psiImp P E a.weight = P.tauAgg a.weight ∧
          psiPOLS P E a.weight = P.tauAgg a.weight ∧
          psiETWFE P E a.weight = P.tauAgg a.weight) := by
  constructor
  · intro g t hgt
    exact flexible_did_cell_characterization P S E hNA hCPT hgt
  · intro a
    exact flexible_did_aggregate_characterization P S E hNA hCPT a

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
