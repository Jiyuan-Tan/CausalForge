import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Basic
import Mathlib.Tactic.NormNum

/-!
# Primitive sign-frontier constructions

This file defines the all-positive sign-reversal region, the concrete
four-cohort fixture, and the row/column-margin elimination polynomial `Phi`.
-/

open scoped BigOperators
open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

/-- Treated cells within the declared cohort support. -/
abbrev TreatedSupportedCell (T : ℕ) (C : Finset (Cohort T)) :=
  {z : SupportedCell T C // treatmentIndicator T z.1.1 z.2 = 1}

/-- Primitive tuples indexed only by the paper's declared cohort and cell domains. -/
abbrev SignReversalPrimitive (T : ℕ) (C : Finset (Cohort T)) :=
  (↑C → OpenUnit) ×
    ((SupportedCell T C → PosReal) × (TreatedSupportedCell T C → ℝ))

/-- The collapsed PPML objective written directly in the C-indexed primitive coordinates. -/
noncomputable def primitiveLimitingCriterion (T : ℕ) (C : Finset (Cohort T))
    (p : SignReversalPrimitive T C) (theta : CollapsedParameter T C) : ℝ :=
  ∑ z : SupportedCell T C,
    ((p.1 z.1 : ℝ) / T) *
      ((p.2.1 z : ℝ) *
          Real.exp (treatmentIndicator T z.1.1 z.2 *
            if h : treatmentIndicator T z.1.1 z.2 = 1
            then p.2.2 ⟨z, h⟩ else 0) *
          collapsedIndex T C (collapsedRegressor T C z.1.1 z.2) theta -
        Real.exp (collapsedIndex T C (collapsedRegressor T C z.1.1 z.2) theta))

/-- Treatment coordinate selected by the primitive collapsed objective. -/
noncomputable def primitiveBetaStar (T : ℕ) (C : Finset (Cohort T))
    (p : SignReversalPrimitive T C) : ℝ :=
  (maximizerOrZero (primitiveLimitingCriterion T C p)).2

/-- Restrict full-array primitives to exactly the coordinates declared in `R_T`. -/
noncomputable def restrictSignReversalPrimitive (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) : SignReversalPrimitive T C :=
  (fun g => pi g.1,
    (fun z => ⟨untreatedMean T barB gamma z.1.1 z.2,
      mul_pos (barB z.1.1).property (Real.exp_pos _)⟩,
    fun z => delta (z.1.1.1, z.1.2)))

-- @node: def:global-sign-reversal-region
/-- The all-positive-effect PPML sign-reversal region `R_T`. -/
noncomputable def signReversalRegion (T : ℕ) (C : Finset (Cohort T))
    (gamma : Fin T → ℝ) : Set (SignReversalPrimitive T C) :=
  {p | ValidPanelHorizon T ∧
    ValidCohortSupport T C ∧
    MulticohortFrontierScope T C ∧
    (∑ g : ↑C, (p.1 g : ℝ)) = 1 ∧
    (∃ barB : ↑C → PosReal, ∀ z : SupportedCell T C,
      (p.2.1 z : ℝ) = (barB z.1 : ℝ) * Real.exp (gamma z.2)) ∧
    (∀ z : TreatedSupportedCell T C, 0 < p.2.2 z) ∧
    (∀ a : CollapsedParameter T C, a ≠ 0 →
      0 < ∑ z : SupportedCell T C,
        ((p.1 z.1 : ℝ) / T) *
          (collapsedIndex T C (collapsedRegressor T C z.1.1 z.2) a) ^ 2) ∧
    primitiveBetaStar T C p < 0}
  -- @realizes R_T(set of primitive tuples satisfying scope, positivity, rank, and beta_star<0)
  -- @realizes Rcal_4(four-period specialization of the global sign-reversal region)
  -- @realizes pi_g(simplex shares indexed only by g in C)
  -- @realizes B_gt(positive baseline coordinates indexed only by supported cells)
  -- @realizes delta_gt(effect coordinates indexed only by treated supported cells)

/-- Four adoption cohorts: paper dates 2, 3, 4, and never treated. -/
def fourCohortSupport : Finset (Cohort 4) :=
  {((⟨1, by decide⟩ : Fin 4) : Cohort 4),
    ((⟨2, by decide⟩ : Fin 4) : Cohort 4),
    ((⟨3, by decide⟩ : Fin 4) : Cohort 4), ⊤}

/-- Equal cohort counts along the cofinal sequence `N = 4(m+1)`. -/
def fourCohortCount (m : ℕ) (g : Cohort 4) : ℕ :=
  if g ∈ fourCohortSupport then m + 1 else 0
  -- @realizes N(cofinal subsequence N=4(m+1))
  -- @realizes n_gN(equal count m+1 on each supported cohort)

/-- Every cohort in the declared four-cohort support has positive count. -/
lemma fourCohortCount_pos (m : ℕ) (g : Cohort 4) (hg : g ∈ fourCohortSupport) :
    0 < fourCohortCount m g := by
  simp [fourCohortCount, hg]
  -- @realizes n_gN(positive on the declared supported-cohort domain)

/-- Unit baselines are identically one in the fixture. -/
def fourCohortBaseline (m : ℕ) (_i : Fin (4 * (m + 1))) : PosReal := ⟨1, zero_lt_one⟩
  -- @realizes b_iN(unit baseline identically one in W4)

/-- Untreated time effects are identically zero in the fixture. -/
def fourCohortGamma (_t : Fin 4) : ℝ := 0
  -- @realizes gamma_t0(time component identically zero in W4)

/-- The W4 effect vector: log(4) at paper cell (2,4), and log(101/100) elsewhere treated. -/
noncomputable def fourCohortDelta (z : Cell 4) : ℝ :=
  if treatmentIndicator 4 z.1 z.2 = 1 then
    if z.1 = (⟨1, by decide⟩ : Fin 4) ∧ z.2 = ⟨3, by decide⟩ then
      Real.log 4
    else Real.log (101 / 100 : ℝ)
  else 0
  -- @realizes delta_gt(log(4) at (2,4), log(101/100) at other treated cells)

/-- Equal limiting cohort shares in W4. -/
noncomputable def fourCohortShare (_g : Cohort 4) : OpenUnit :=
  ⟨(1 : ℝ) / 4, by constructor <;> norm_num⟩
  -- @realizes pi_g(equal limiting share 1/4 in W4)

/-- Unit limiting cohort baselines in W4. -/
def fourCohortLimitBaseline (_g : Cohort 4) : PosReal := ⟨1, zero_lt_one⟩
  -- @realizes bar_b_g(limiting cohort baseline equal to one in W4)

abbrev FourCohortConfiguration :=
  Finset (Cohort 4) ×
    ((ℕ → Cohort 4 → ℕ) ×
      ((∀ m, Fin (4 * (m + 1)) → PosReal) × ((Fin 4 → ℝ) × (Cell 4 → ℝ))))

-- @node: def:four-cohort-witness
/-- The concrete four-cohort triangular-array configuration `W4`. -/
noncomputable def fourCohortWitness : FourCohortConfiguration :=
  (fourCohortSupport,
    (fourCohortCount,
      (fourCohortBaseline, (fourCohortGamma, fourCohortDelta))))
  -- @realizes W4(equal-share four-period configuration with the exceptional late effect)

/-- Primitive positive cell mass before division by the common time factor. -/
noncomputable def primitiveH (T : ℕ) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (t : Fin T) : ℝ :=
  (pi g : ℝ) * untreatedMean T barB gamma g t *
    Real.exp (treatmentIndicator T g t * delta (g, t))
  -- @realizes h_gt(pi_g * B_gt * exp(D_gt * delta_gt))

/-- Row margin `R_g`. -/
noncomputable def primitiveRow (T : ℕ) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
  (g : Cohort T) : ℝ :=
  ∑ t : Fin T, primitiveH T pi barB gamma delta g t
  -- @realizes R_g(row margin of h_gt)

/-- Column margin `C_t`. -/
noncomputable def primitiveColumn (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) (t : Fin T) : ℝ :=
  ∑ g ∈ C, primitiveH T pi barB gamma delta g t
  -- @realizes C_t(column margin of h_gt)

/-- Total primitive mass `M`. -/
noncomputable def primitiveTotal (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) : ℝ :=
  ∑ g ∈ C, primitiveRow T pi barB gamma delta g
  -- @realizes M(grand sum of h_gt)

/-- Treated primitive total `A`. -/
noncomputable def primitiveTreatedTotal (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) : ℝ :=
  ∑ g ∈ C, ∑ t : Fin T,
    treatmentIndicator T g t * primitiveH T pi barB gamma delta g t
  -- @realizes A(treated-cell sum of h_gt)

-- @node: def:frontier-elimination-handle
/-- The nuisance-free frontier polynomial `Phi = M*A - sum D_gt R_g C_t`. -/
noncomputable def frontierEliminationHandle (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) : ℝ :=
  primitiveTotal T C pi barB gamma delta *
      primitiveTreatedTotal T C pi barB gamma delta -
    ∑ g ∈ C, ∑ t : Fin T,
      treatmentIndicator T g t * primitiveRow T pi barB gamma delta g *
        primitiveColumn T C pi barB gamma delta t
  -- @realizes Phi(delta)(nuisance-free frontier polynomial)

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
