/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# de Chaisemartin-D'Haultfoeuille (2020): finite-cell TWFE algebra

Pure finite group-time algebra for the DCDH TWFE estimand with heterogeneous
effects. This file formalizes the finite weighted-cell identities only: no
`POSystem`, measure theory, sampling bridge, or residualization API is used.

Source labels from
`doc/basic_concepts/po/estimand_characterization/de_chaisemartin_dhaultfoeuille_twfe.md`:

* `def:po-estimand-dcdh-panel`
* `def:po-estimand-dcdh-residualized-treatment`
* `def:po-estimand-dcdh-twfe-coefficient`
* `ass:po-estimand-dcdh-untreated-parallel`
* `thm:po-estimand-dcdh-twfe-decomposition`
* `prop:po-estimand-dcdh-weights-sum-one`
* `prop:po-estimand-dcdh-sign-reversal`
* `rem:po-estimand-dcdh-negative-weight-warning`
* `rem:po-estimand-dcdh-lean-shape`

## Scope notes

**Two-way fixed-effect nuisance class.** `IsGTFE` is a local abbreviation for
`Causalean.Panel.Weighted.IsUnitTimeAdditive`, which itself unfolds to
`∃ a b, ∀ i t, h i t = a i + b t`.

**Residualized treatment.** The paper motivates D̃ as the FWL
residual of D projected on the two-way FE span H_GT.  Here it is taken as a
primitive witness satisfying `D_minus_resid_mem` and `Dtilde_orthogonal`.
The companion file `FWLBridge.lean` supplies `DCDHPanel.ofTwoWayPanel`, which
constructs this witness from the uniform two-way-panel double-demeaning operator.

**Treatment effects.** The
paper defines τ_gt = Y_gt(1) − Y_gt(0) from two potential-outcome functions.
Here `tau` is a raw field; the only connection to outcomes is the consistency
axiom `Y = Y0 + D * tau`.  The population origin of this field is supplied in the
companion file `Causalean/Panel/EstimandCharacterization/HeterogeneousTWFE/PopulationBridge.lean`:
`cellMean_consistency` shows that for cell-conditional means
(`eventCondExp` on a cell event with constant `D ≡ d`), pointwise PO consistency
`Y = Y0 + d·(Y1 − Y0)` yields the consistency identity `Ȳ = Ȳ(0) + d·τ̄` with
`τ̄ = E[Y(1)|A] − E[Y(0)|A]` a genuine potential-outcome contrast.  That file
also provides the full `DCDHPanel.ofPopulation` constructor, which builds a
genuine `DCDHPanel` from a probability model (`pi = μ(cell)`, `Y/Y0 = E[·|cell]`,
`tau = E[Y(1)|cell] − E[Y(0)|cell]`), deriving `consistency` from
`cellMean_consistency` and `pi_sum_one` from finite-partition measure additivity;
`D̃` is taken as a witness there (the general-weight FWL residual is separate;
the uniform case is `ofTwoWayPanel`).  This finite-algebra file itself stays
measure-free.
-/

import Causalean.Panel.Weighted.AdditiveSpan
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # DCDH Finite Panel Algebra

This file formalizes the finite group-time algebra behind the
de Chaisemartin-D'Haultfoeuille two-way fixed-effect estimand.  `DCDHPanel`
packages weighted cells, binary treatment, potential untreated means, treatment
effects, and a residualized-treatment witness.  The main results decompose
`DCDHPanel.betaTWFE` into untreated bias plus treated-cell weighted effects
(`twfe_eq_untreatedBias_add_treated_weighted_tau`), show that treated DCDH
weights sum to one and have the sign of `Dtilde`, and prove finite sign-reversal
constructions such as
`exists_panel_with_positive_treated_effects_twfe_negative_of_negative_component`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace HeterogeneousTWFE

open Finset

/-- Group-time fixed-effect span, represented as additive group and period
components.

Compatibility alias for the shared additive-span predicate. -/
abbrev IsGTFE {G T : Type*} [Fintype G] [Fintype T] (h : G → T → ℝ) : Prop :=
  Causalean.Panel.Weighted.IsUnitTimeAdditive h

/-- Finite DCDH group-time panel with a residualized-treatment witness. -/
structure DCDHPanel (G T : Type*) [Fintype G] [Fintype T] where
  pi : G → T → ℝ
  D : G → T → ℝ
  Y : G → T → ℝ
  Y0 : G → T → ℝ
  tau : G → T → ℝ
  Dtilde : G → T → ℝ
  pi_pos : ∀ g t, 0 < pi g t
  pi_sum_one : ∑ g, ∑ t, pi g t = 1
  D_binary : ∀ g t, D g t = 0 ∨ D g t = 1
  consistency : ∀ g t, Y g t = Y0 g t + D g t * tau g t
  D_minus_resid_mem : IsGTFE (fun g t => D g t - Dtilde g t)
  Dtilde_orthogonal :
    ∀ h : G → T → ℝ, IsGTFE h → ∑ g, ∑ t, pi g t * Dtilde g t * h g t = 0
  SD_pos : 0 < ∑ g, ∑ t, pi g t * (Dtilde g t)^2

namespace DCDHPanel

variable {G T : Type*} [Fintype G] [Fintype T]

/-- Residualized-treatment denominator `S_D`. -/
def SD (P : DCDHPanel G T) : ℝ :=
  ∑ g, ∑ t, P.pi g t * (P.Dtilde g t)^2

/-- Finite FWL/TWFE coefficient. -/
noncomputable def betaTWFE (P : DCDHPanel G T) : ℝ :=
  (∑ g, ∑ t, P.pi g t * P.Dtilde g t * P.Y g t) / P.SD

/-- Untreated residual contrast divided by the residualized-treatment
denominator. -/
noncomputable def untreatedBias (P : DCDHPanel G T) : ℝ :=
  (∑ g, ∑ t, P.pi g t * P.Dtilde g t * P.Y0 g t) / P.SD

/-- Normalized DCDH cell weight, interpreted on treated cells. -/
noncomputable def omega (P : DCDHPanel G T) (g : G) (t : T) : ℝ :=
  (P.pi g t * P.Dtilde g t) / P.SD

/-- Treated cells `{(g,t) | D_gt = 1}`. -/
noncomputable def treatedCells (P : DCDHPanel G T) : Finset (G × T) :=
  Finset.univ.filter (fun gt : G × T => P.D gt.1 gt.2 = 1)

/-- All-cell treatment-effect component using the binary treatment indicator. -/
noncomputable def DWeightedTau (P : DCDHPanel G T) : ℝ :=
  ∑ g, ∑ t, ((P.pi g t * P.Dtilde g t * P.D g t) / P.SD) * P.tau g t

/-- Treated-cell weighted treatment-effect component. -/
noncomputable def treatedWeightedTau (P : DCDHPanel G T) : ℝ :=
  ∑ gt ∈ P.treatedCells, P.omega gt.1 gt.2 * P.tau gt.1 gt.2

/-- Zero untreated residual contrast, the bias-free DCDH condition. -/
def zeroUntreatedResidualContrast (P : DCDHPanel G T) : Prop :=
  ∑ g, ∑ t, P.pi g t * P.Dtilde g t * P.Y0 g t = 0

/-- Orthogonality of the residualized treatment against `D - Dtilde` gives
the DCDH denominator identity. -/
theorem inner_Dtilde_D_eq_SD (P : DCDHPanel G T) :
  ∑ g, ∑ t, P.pi g t * P.Dtilde g t * P.D g t = P.SD := by
  have horth : ∑ g, ∑ t, P.pi g t * P.Dtilde g t *
      (P.D g t - P.Dtilde g t) = 0 :=
    P.Dtilde_orthogonal (fun g t => P.D g t - P.Dtilde g t)
      P.D_minus_resid_mem
  have hdiff :
      (∑ g, ∑ t, P.pi g t * P.Dtilde g t * P.D g t) -
        (∑ g, ∑ t, P.pi g t * (P.Dtilde g t)^2) = 0 := by
    rw [← horth]
    simp_rw [mul_sub, Finset.sum_sub_distrib, pow_two]
    ring_nf
  rw [SD]
  exact sub_eq_zero.mp hdiff

/-- Group-plus-period untreated means imply the zero untreated residual
contrast. -/
theorem zeroUntreatedResidualContrast_of_Y0_mem_gtfe
  (P : DCDHPanel G T) (hY0 : IsGTFE P.Y0) :
  P.zeroUntreatedResidualContrast := by
  simpa [zeroUntreatedResidualContrast] using P.Dtilde_orthogonal P.Y0 hY0

/-- DCDH finite TWFE decomposition into untreated bias and the all-cell
`D`-weighted treatment-effect component. -/
theorem twfe_eq_untreatedBias_add_DWeightedTau (P : DCDHPanel G T) :
  P.betaTWFE = P.untreatedBias + P.DWeightedTau := by
  rw [betaTWFE, untreatedBias, DWeightedTau]
  simp_rw [P.consistency]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [add_div]
  congr 1
  rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _hg
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- The all-cell `D`-weighted component is the same as the treated-cell sum. -/
theorem DWeightedTau_eq_treatedWeightedTau (P : DCDHPanel G T) :
  P.DWeightedTau = P.treatedWeightedTau := by
  unfold DWeightedTau treatedWeightedTau treatedCells omega
  rw [← Fintype.sum_prod_type'
    (fun g t => P.pi g t * P.Dtilde g t * P.D g t / P.SD * P.tau g t)]
  simp_rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun gt _hgt => by
    rcases gt with ⟨g, t⟩
    rcases P.D_binary g t with hD | hD
    · simp [hD]
    · simp [hD])

/-- DCDH finite TWFE decomposition with normalized treated-cell weights. -/
theorem twfe_eq_untreatedBias_add_treated_weighted_tau (P : DCDHPanel G T) :
  P.betaTWFE = P.untreatedBias + P.treatedWeightedTau := by
  rw [twfe_eq_untreatedBias_add_DWeightedTau, DWeightedTau_eq_treatedWeightedTau]

/-- Under the zero untreated residual contrast, TWFE equals the treated-cell
weighted treatment-effect sum. -/
theorem twfe_eq_treated_weighted_tau_of_zeroUntreatedContrast
  (P : DCDHPanel G T) (h0 : P.zeroUntreatedResidualContrast) :
  P.betaTWFE = P.treatedWeightedTau := by
  rw [twfe_eq_untreatedBias_add_treated_weighted_tau]
  rw [untreatedBias, h0]
  simp

/-- The treated-cell DCDH weights sum to one. -/
theorem treated_omega_sum_eq_one (P : DCDHPanel G T) :
  ∑ gt ∈ P.treatedCells, P.omega gt.1 gt.2 = 1 := by
  have hnum :
      ∑ gt ∈ P.treatedCells, P.pi gt.1 gt.2 * P.Dtilde gt.1 gt.2 = P.SD := by
    rw [← inner_Dtilde_D_eq_SD P]
    unfold treatedCells
    rw [← Fintype.sum_prod_type'
      (fun g t => P.pi g t * P.Dtilde g t * P.D g t)]
    simp_rw [Finset.sum_filter]
    exact (Finset.sum_congr rfl (fun gt _hgt => by
      rcases gt with ⟨g, t⟩
      rcases P.D_binary g t with hD | hD
      · simp [hD]
      · simp [hD])).symm
  calc
    ∑ gt ∈ P.treatedCells, P.omega gt.1 gt.2
        = (∑ gt ∈ P.treatedCells,
            P.pi gt.1 gt.2 * P.Dtilde gt.1 gt.2) / P.SD := by
          unfold omega
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = 1 := by
      rw [hnum]
      exact div_self (ne_of_gt P.SD_pos)

/-- The sign of the normalized DCDH weight is the sign of the residualized
treatment. The lemma is named for its treated-cell use in the DCDH weight
interpretation, but the equivalence only needs `π_gt > 0` and `S_D > 0`. -/
theorem treated_omega_neg_iff_Dtilde_neg
  (P : DCDHPanel G T) {g : G} {t : T} :
  P.omega g t < 0 ↔ P.Dtilde g t < 0 := by
  unfold omega
  constructor
  · intro h
    have hnum : P.pi g t * P.Dtilde g t < 0 :=
      ((div_neg_iff.mp h).resolve_left
        (fun hpos => not_lt_of_gt P.SD_pos hpos.2)).1
    nlinarith [P.pi_pos g t]
  · intro h
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (P.pi_pos g t) h)
      P.SD_pos

/-- Positive-weight direction of the sign characterization: ω_gt > 0 iff
D̃_gt > 0.  Together with `treated_omega_neg_iff_Dtilde_neg` and
`treated_omega_zero_iff_Dtilde_zero` this completes the paper's claim
sign(ω_gt) = sign(D̃_gt) (.tex Theorem 2 / .md prop:po-estimand-dcdh-weights-sum-one). -/
theorem treated_omega_pos_iff_Dtilde_pos
  (P : DCDHPanel G T) {g : G} {t : T} :
  0 < P.omega g t ↔ 0 < P.Dtilde g t := by
  unfold omega SD
  -- 0 < (pi * Dtilde) / SD ↔ 0 < pi * Dtilde  (since SD > 0)
  rw [div_pos_iff_of_pos_right P.SD_pos]
  constructor
  · intro h
    have hpi := P.pi_pos g t
    rcases lt_trichotomy (P.Dtilde g t) 0 with h' | h' | h'
    · exact absurd (mul_neg_of_pos_of_neg hpi h') (not_lt.mpr (le_of_lt h))
    · simp [h'] at h
    · exact h'
  · intro h
    exact mul_pos (P.pi_pos g t) h

/-- Zero-weight direction of the sign characterization: ω_gt = 0 iff D̃_gt = 0.
Together with the pos/neg sibling lemmas, this completes sign(ω_gt) = sign(D̃_gt)
for all three cases. -/
theorem treated_omega_zero_iff_Dtilde_zero
  (P : DCDHPanel G T) {g : G} {t : T} :
  P.omega g t = 0 ↔ P.Dtilde g t = 0 := by
  unfold omega
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with hnum | hSD
    · rcases mul_eq_zero.mp hnum with hpi | hDt
      · exact absurd hpi (ne_of_gt (P.pi_pos g t))
      · exact hDt
    · exact absurd hSD (ne_of_gt P.SD_pos)
  · intro h
    left
    rw [h, mul_zero]

end DCDHPanel

/-- Two-cell signed-weight calculation from the DCDH sign-reversal example. -/
theorem two_cell_signed_weights_positive_effects_negative_sum
  {c ε M : ℝ} (hc : 0 < c) (hε : 0 < ε)
  (hM : ((1 + c) * ε) / c < M) :
  0 < ε ∧ 0 < M ∧ (1 + c) * ε + (-c) * M < 0 := by
  constructor
  · exact hε
  constructor
  · have hnum_pos : 0 < (1 + c) * ε := by
      nlinarith
    have hfrac_pos : 0 < ((1 + c) * ε) / c := by
      positivity
    linarith
  · have hdom : (1 + c) * ε < c * M := by
      have hmul := mul_lt_mul_of_pos_left hM hc
      field_simp [hc.ne'] at hmul
      nlinarith
    nlinarith

/-- Finite signed-average construction: if normalized weights have a strictly
negative component, some strictly positive effects have a negative weighted
sum. -/
theorem exists_positive_effects_negative_weighted_sum_of_negative_component
  {ι : Type*} [Fintype ι] (w : ι → ℝ)
  (h_sum : ∑ i, w i = 1)
  (h_neg_component : ∑ i ∈ (Finset.univ.filter fun i => w i < 0), w i < 0) :
  ∃ tau : ι → ℝ, (∀ i, 0 < tau i) ∧ ∑ i, w i * tau i < 0 := by
  classical
  have _ : ∑ i, w i = 1 := h_sum
  let N : Finset ι := Finset.univ.filter fun i => w i < 0
  let B : ℝ := ∑ i ∈ (Finset.univ.filter fun i => ¬ w i < 0), w i
  have hAneg : (∑ i ∈ N, w i) < 0 := by
    simpa [N] using h_neg_component
  have hden_pos : 0 < -(∑ i ∈ N, w i) := by
    linarith
  obtain ⟨M, hM⟩ := exists_gt (max 0 (B / (-(∑ i ∈ N, w i))))
  have hMpos : 0 < M := lt_of_le_of_lt (le_max_left _ _) hM
  have hBlt : B < M * (-(∑ i ∈ N, w i)) := by
    have hratio : B / (-(∑ i ∈ N, w i)) < M :=
      lt_of_le_of_lt (le_max_right _ _) hM
    have hmul := mul_lt_mul_of_pos_right hratio hden_pos
    rw [div_mul_cancel₀ B (ne_of_gt hden_pos)] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  refine ⟨fun i => if w i < 0 then M else 1, ?_, ?_⟩
  · intro i
    by_cases hi : w i < 0
    · simp [hi, hMpos]
    · simp [hi]
  · have hsum_split :
        ∑ i, w i * (if w i < 0 then M else 1) =
          M * (∑ i ∈ N, w i) + B := by
      simp only [N, B, Finset.sum_filter]
      simp_rw [mul_ite, mul_one]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hneg : w i < 0
      · simp [hneg]
        ring
      · simp [hneg]
    rw [hsum_split]
    nlinarith

/-- If some treated cell has negative residualized treatment, then the total
weight over negatively weighted treated cells is strictly negative.

This bridge converts the economically natural hypothesis into the
negative-weight-sum precondition used by the sign-reversal theorem.

Proof: `treated_omega_neg_iff_Dtilde_neg` identifies the filter
`{gt ∈ treatedCells | omega < 0}` with `{gt ∈ treatedCells | Dtilde < 0}`;
the hypothesis provides at least one such cell, so the sum is a nonempty
sum of negative reals, hence strictly negative. -/
theorem neg_component_of_exists_Dtilde_neg
  {G T : Type*} [Fintype G] [Fintype T]
  (P : DCDHPanel G T)
  (h : ∃ (g : G) (t : T), P.D g t = 1 ∧ P.Dtilde g t < 0) :
  ∑ gt ∈ (P.treatedCells.filter fun gt => P.omega gt.1 gt.2 < 0),
    P.omega gt.1 gt.2 < 0 := by
  obtain ⟨g₀, t₀, hD, hDt⟩ := h
  let S := P.treatedCells.filter (fun gt => P.omega gt.1 gt.2 < 0)
  have hmem : (g₀, t₀) ∈ S := by
    simp only [S, Finset.mem_filter, DCDHPanel.treatedCells, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hD, (DCDHPanel.treated_omega_neg_iff_Dtilde_neg P).mpr hDt⟩
  have hle : ∀ gt ∈ S, P.omega gt.1 gt.2 ≤ 0 := fun gt hgt =>
    le_of_lt (Finset.mem_filter.mp hgt).2
  -- Finset.sum_lt_sum : (∀ i ∈ s, f i ≤ g i) → (∃ i ∈ s, f i < g i) → sum f < sum g
  have key : ∑ gt ∈ S, P.omega gt.1 gt.2 < ∑ _gt ∈ S, (0 : ℝ) :=
    Finset.sum_lt_sum hle ⟨(g₀, t₀), hmem, (Finset.mem_filter.mp hmem).2⟩
  simpa using key

/-- Panel-level DCDH sign reversal: if the treated-cell weights have a strictly
negative total component and untreated residual contrast is zero, then one can
choose strictly positive treated effects, keeping the treatment/residualization
geometry fixed, so that the resulting TWFE coefficient is negative. -/
theorem exists_panel_with_positive_treated_effects_twfe_negative_of_negative_component
  {G T : Type*} [Fintype G] [Fintype T]
  (P : DCDHPanel G T)
  (h0 : P.zeroUntreatedResidualContrast)
  (h_neg_component :
    ∑ gt ∈ (P.treatedCells.filter fun gt => P.omega gt.1 gt.2 < 0),
      P.omega gt.1 gt.2 < 0) :
  ∃ P' : DCDHPanel G T,
    (∀ g t, P'.pi g t = P.pi g t) ∧
    (∀ g t, P'.D g t = P.D g t) ∧
    (∀ g t, P'.Y0 g t = P.Y0 g t) ∧
    (∀ g t, P'.Dtilde g t = P.Dtilde g t) ∧
    (∀ g t, 0 < P'.tau g t) ∧
    P'.zeroUntreatedResidualContrast ∧
    P'.betaTWFE < 0 := by
  classical
  let w : G × T → ℝ :=
    fun gt => if gt ∈ P.treatedCells then P.omega gt.1 gt.2 else 0
  have hsum_w : ∑ gt, w gt = 1 := by
    calc
      ∑ gt, w gt
          = ∑ gt ∈ P.treatedCells, P.omega gt.1 gt.2 := by
            simp [w]
      _ = 1 := DCDHPanel.treated_omega_sum_eq_one P
  have hneg_w :
      ∑ gt ∈ (Finset.univ.filter fun gt => w gt < 0), w gt < 0 := by
    have hsum_eq :
        ∑ gt ∈ (Finset.univ.filter fun gt => w gt < 0), w gt =
          ∑ gt ∈ (P.treatedCells.filter fun gt => P.omega gt.1 gt.2 < 0),
            P.omega gt.1 gt.2 := by
      apply Finset.sum_congr
      · ext gt
        by_cases htreated : gt ∈ P.treatedCells
        · simp [w, htreated]
        · simp [w, htreated]
      · intro gt hgt
        have htreated : gt ∈ P.treatedCells := by
          exact (Finset.mem_filter.mp hgt).1
        simp [w, htreated]
    rw [hsum_eq]
    exact h_neg_component
  obtain ⟨tau, htau_pos, hweighted_neg⟩ :=
    exists_positive_effects_negative_weighted_sum_of_negative_component
      w hsum_w hneg_w
  let P' : DCDHPanel G T :=
    { pi := P.pi
      D := P.D
      Y := fun g t => P.Y0 g t + P.D g t * tau (g, t)
      Y0 := P.Y0
      tau := fun g t => tau (g, t)
      Dtilde := P.Dtilde
      pi_pos := P.pi_pos
      pi_sum_one := P.pi_sum_one
      D_binary := P.D_binary
      consistency := by
        intro g t
        rfl
      D_minus_resid_mem := P.D_minus_resid_mem
      Dtilde_orthogonal := P.Dtilde_orthogonal
      SD_pos := P.SD_pos }
  have hzero' : P'.zeroUntreatedResidualContrast := by
    simpa [P', DCDHPanel.zeroUntreatedResidualContrast] using h0
  have htreated_sum :
      P'.treatedWeightedTau = ∑ gt, w gt * tau gt := by
    calc
      P'.treatedWeightedTau
          = ∑ gt ∈ P.treatedCells, P.omega gt.1 gt.2 * tau gt := by
            simp [P', DCDHPanel.treatedWeightedTau, DCDHPanel.treatedCells,
              DCDHPanel.omega, DCDHPanel.SD]
      _ = ∑ gt, w gt * tau gt := by
            simp [w]
  refine ⟨P', ?_, ?_, ?_, ?_, ?_, hzero', ?_⟩
  · intro g t
    rfl
  · intro g t
    rfl
  · intro g t
    rfl
  · intro g t
    rfl
  · intro g t
    exact htau_pos (g, t)
  · rw [DCDHPanel.twfe_eq_treated_weighted_tau_of_zeroUntreatedContrast P' hzero']
    rw [htreated_sum]
    exact hweighted_neg

end HeterogeneousTWFE
end Panel.EstimandCharacterization
end Causalean
