/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Panel.Weighted.AdditiveSpan
import Causalean.Panel.Weighted.Subspace
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Weighted Finite Two-Way Panel Helpers

Paper-agnostic finite-sum infrastructure for two-way panels under a **general
unit weight** `p : Unit → ℝ` (a pmf: `∑ p = 1`, `0 < p i`) with a uniform period
measure. This is the share-weighted generalization of the uniform two-way panel
algebra used by the estimand-characterization modules:

* uniform balanced panels recover the old `UniformTwoWayPanel` by `p ≡ 1/|Unit|`;
* Goodman-Bacon cohort-share panels take `p = cohort shares`.

It provides the `p`-weighted unit/time/grand means, double demeaning (`ddot`), the
`p`-weighted inner product, the unit/time additive nuisance class, the
reconstruction identity, and the share-weighted orthogonality theorems
(`ddot` ⟂ unit / time / additive).

## Bridge to the generic `WeightedSupport` FWL tower

The closed forms above are connected to the abstract Frisch–Waugh–Lovell
substrate in `Causalean/Panel/Weighted/` by the `Bridge` section: the panel is the
cell support `R = Unit × Time` with weight `ω_{(i,t)} = p_i / |Time|`
(`cellSupport`), the `p`-weighted inner product is `|Time|` times
`WeightedSupport.ip` (`inner_eq_card_smul_ip`), and `ddot` is the generic residual
maker against the two-axis additive span (`ddot_eq_residualize`).  The abstract
FWL coefficient lemma `Weighted.WeightedSupport.scalar_fwl_of_normalEqs` is thus
reusable through the bridge.
-/

namespace Causalean
namespace Panel
namespace WeightedTwoWayPanel

open Finset

variable {Unit Time : Type*} [Fintype Unit] [Fintype Time]

/-- Unit weights forming a probability vector: strictly positive, summing to one.
Mirrors Goodman-Bacon cohort shares; `p ≡ 1/|Unit|` recovers the uniform panel. -/
structure UnitWeights (Unit : Type*) [Fintype Unit] where
  p : Unit → ℝ
  pos : ∀ i, 0 < p i
  sum_one : ∑ i, p i = 1

/-- Unit mean `\bar V_{i·}` under the uniform period measure (weight-free in time). -/
noncomputable def unitMean (V : Unit → Time → ℝ) (i : Unit) : ℝ :=
  (Fintype.card Time : ℝ)⁻¹ * ∑ t, V i t

/-- `p`-weighted time mean `\bar V_{·t} = ∑_i p_i V_{it}`. -/
noncomputable def timeMean (w : UnitWeights Unit) (V : Unit → Time → ℝ) (t : Time) : ℝ :=
  ∑ i, w.p i * V i t

/-- `p`-weighted grand mean `\bar V = ∑_i p_i \bar V_{i·}`. -/
noncomputable def grandMean (w : UnitWeights Unit) (V : Unit → Time → ℝ) : ℝ :=
  ∑ i, w.p i * unitMean V i

/-- Two-way residual / double-demeaned array under the `p`-weighted means. -/
noncomputable def ddot (w : UnitWeights Unit) (V : Unit → Time → ℝ) (i : Unit) (t : Time) : ℝ :=
  V i t - unitMean V i - timeMean w V t + grandMean w V

/-- `p`-weighted finite-panel inner product (uniform-time normalizer dropped as
harmless). -/
noncomputable def inner (w : UnitWeights Unit) (V W : Unit → Time → ℝ) : ℝ :=
  ∑ i, ∑ t, w.p i * (V i t * W i t)

/-- Unit-time additive nuisance class `h_it = a_i + b_t` (shared predicate). -/
abbrev IsUnitTimeAdditive (h : Unit → Time → ℝ) : Prop :=
  Causalean.Panel.Weighted.IsUnitTimeAdditive h

/-- The unit/time component removed by double demeaning. -/
noncomputable def unitTimeProjection (w : UnitWeights Unit) (V : Unit → Time → ℝ)
    (i : Unit) (t : Time) : ℝ :=
  unitMean V i + timeMean w V t - grandMean w V

/-- Reconstruction identity `V_it = ddot V_it + unitMean + timeMean - grandMean`. -/
theorem ddot_reconstruct (w : UnitWeights Unit) (V : Unit → Time → ℝ) (i : Unit) (t : Time) :
    ddot w V i t + unitMean V i + timeMean w V t - grandMean w V = V i t := by
  unfold ddot
  ring

/-- The removed component is itself unit/time additive. -/
theorem unitTimeProjection_additive (w : UnitWeights Unit) (V : Unit → Time → ℝ) :
    IsUnitTimeAdditive (unitTimeProjection w V) := by
  refine ⟨unitMean V, fun t => timeMean w V t - grandMean w V, ?_⟩
  intro i t
  unfold unitTimeProjection
  ring

/-- Pointwise residual decomposition `V - ddot V` into the unit/time projection. -/
theorem sub_ddot_eq_unitTimeProjection (w : UnitWeights Unit) (V : Unit → Time → ℝ)
    (i : Unit) (t : Time) :
    V i t - ddot w V i t = unitTimeProjection w V i t := by
  unfold ddot unitTimeProjection
  ring

/-- Double-demeaned arrays are orthogonal (in the `p`-weighted inner product) to
arbitrary unit-only functions: `∑_i ∑_t p_i · ddot V_{it} · a_i = 0`.
Per-unit the period sum of `ddot` vanishes (uniform time mean cancels), so the
`p_i a_i` factor drops out. -/
theorem ddot_orthogonal_unit (w : UnitWeights Unit)
    (hT : (0 : ℝ) < Fintype.card Time)
    (V : Unit → Time → ℝ) (a : Unit → ℝ) :
    ∑ i, ∑ t, w.p i * (ddot w V i t * a i) = 0 := by
  classical
  have hT_ne : (Fintype.card Time : ℝ) ≠ 0 := ne_of_gt hT
  have h_unitMean_count : ∀ i,
      (Fintype.card Time : ℝ) * unitMean V i = ∑ t, V i t := by
    intro i
    unfold unitMean
    rw [← mul_assoc, mul_inv_cancel₀ hT_ne, one_mul]
  have h_timeMean_sum :
      ∑ t, timeMean w V t = (Fintype.card Time : ℝ) * grandMean w V := by
    unfold timeMean grandMean
    calc
      ∑ t, ∑ i, w.p i * V i t = ∑ i, ∑ t, w.p i * V i t := by
        rw [Finset.sum_comm]
      _ = ∑ i, w.p i * ∑ t, V i t := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
      _ = ∑ i, w.p i * ((Fintype.card Time : ℝ) * unitMean V i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [h_unitMean_count i]
      _ = (Fintype.card Time : ℝ) * ∑ i, w.p i * unitMean V i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have hrow : ∀ i, ∑ t, ddot w V i t = 0 := by
    intro i
    calc
      ∑ t, ddot w V i t =
          ∑ t, V i t - (Fintype.card Time : ℝ) * unitMean V i -
            ∑ t, timeMean w V t + (Fintype.card Time : ℝ) * grandMean w V := by
          simp only [ddot, Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.sum_const, nsmul_eq_mul]
          rw [Finset.card_univ]
      _ = 0 := by
          rw [h_unitMean_count i, h_timeMean_sum]
          ring
  calc
    ∑ i, ∑ t, w.p i * (ddot w V i t * a i) =
        ∑ i, w.p i * ((∑ t, ddot w V i t) * a i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        ∑ t, w.p i * (ddot w V i t * a i)
            = ∑ t, (w.p i * a i) * ddot w V i t := by
          apply Finset.sum_congr rfl
          intro t _ht
          ring
        _ = (w.p i * a i) * ∑ t, ddot w V i t := by
          rw [Finset.mul_sum]
        _ = w.p i * ((∑ t, ddot w V i t) * a i) := by
          ring
    _ = 0 := by
      simp [hrow]

/-- Double-demeaned arrays are orthogonal (in the `p`-weighted inner product) to
arbitrary time-only functions: `∑_i ∑_t p_i · ddot V_{it} · b_t = 0`.
Per-period the `p`-weighted unit sum of `ddot` vanishes (`∑ p = 1` cancels the
time mean against the grand mean). -/
theorem ddot_orthogonal_time (w : UnitWeights Unit)
    (V : Unit → Time → ℝ) (b : Time → ℝ) :
    ∑ i, ∑ t, w.p i * (ddot w V i t * b t) = 0 := by
  classical
  have hcol : ∀ t, ∑ i, w.p i * ddot w V i t = 0 := by
    intro t
    calc
      ∑ i, w.p i * ddot w V i t =
          ∑ i, (w.p i * V i t - w.p i * unitMean V i -
            w.p i * timeMean w V t + w.p i * grandMean w V) := by
        apply Finset.sum_congr rfl
        intro i _hi
        unfold ddot
        ring
      _ = ∑ i, w.p i * V i t - ∑ i, w.p i * unitMean V i -
            (∑ i, w.p i) * timeMean w V t +
            (∑ i, w.p i) * grandMean w V := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
      _ = 0 := by
        rw [w.sum_one]
        unfold timeMean grandMean
        ring
  calc
    ∑ i, ∑ t, w.p i * (ddot w V i t * b t) =
        ∑ t, (∑ i, w.p i * ddot w V i t) * b t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _ht
      calc
        ∑ i, w.p i * (ddot w V i t * b t)
            = ∑ i, (w.p i * ddot w V i t) * b t := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = (∑ i, w.p i * ddot w V i t) * b t := by
          rw [Finset.sum_mul]
    _ = 0 := by
      simp [hcol]

/-- Double-demeaned arrays are orthogonal to every unit/time additive nuisance
function in the `p`-weighted inner product. -/
theorem ddot_orthogonal_unit_time (w : UnitWeights Unit)
    (hT : (0 : ℝ) < Fintype.card Time)
    (V h : Unit → Time → ℝ) (hh : IsUnitTimeAdditive h) :
    inner w (ddot w V) h = 0 := by
  rcases hh with ⟨a, b, hh⟩
  unfold inner
  calc
    ∑ i, ∑ t, w.p i * (ddot w V i t * h i t)
        = ∑ i, ∑ t, w.p i * (ddot w V i t * (a i + b t)) := by
          simp [hh]
    _ = (∑ i, ∑ t, w.p i * (ddot w V i t * a i)) +
          (∑ i, ∑ t, w.p i * (ddot w V i t * b t)) := by
          simp [mul_add, Finset.sum_add_distrib]
    _ = 0 := by
          rw [ddot_orthogonal_unit w hT V a, ddot_orthogonal_time w V b, zero_add]

/-! ### Bridge to the generic `WeightedSupport` FWL tower

The bespoke `p`-weighted inner product and double demeaning above are the
*concrete closed forms*; the generic Frisch–Waugh–Lovell substrate in
`Causalean/Panel/Weighted/` (`WeightedSupport.ip`, `residualize`,
`scalar_fwl_of_normalEqs`) is the *abstract orthogonal-projection* layer.  This
section connects the two: the panel is the cell support `R = Unit × Time` with
weight `ω_{(i,t)} = p_i / |Time|`, the `p`-weighted inner product is `|Time|`
times `WeightedSupport.ip`, and `ddot` is the generic residual maker against the
two-axis additive span.  Downstream code can therefore read the explicit
demeaning formula off the abstract projection and reuse `scalar_fwl_of_normalEqs`
on the panel. -/

section Bridge

open Causalean.Panel.Weighted

variable [DecidableEq Unit] [DecidableEq Time] [Nonempty Unit] [Nonempty Time]

/-- The panel viewed as a cell-indexed weighted support on `R = Unit × Time`
with the factorized weight `ω_{(i,t)} = p_i / |Time|` (every cell observed). -/
noncomputable def cellSupport (w : UnitWeights Unit) :
    WeightedSupport (Unit × Time) where
  observed := Finset.univ
  observed_nonempty := Finset.univ_nonempty
  weight r := w.p r.1 / (Fintype.card Time : ℝ)
  weight_pos := by
    intro r _
    have hT : (0 : ℝ) < (Fintype.card Time : ℝ) := by exact_mod_cast Fintype.card_pos
    exact div_pos (w.pos r.1) hT
  weight_zero_off := by
    intro r hr; exact (hr (Finset.mem_univ r)).elim
  weight_sum_one := by
    have hT : (Fintype.card Time : ℝ) ≠ 0 := by
      have h := Fintype.card_pos (α := Time)
      exact_mod_cast h.ne'
    rw [Fintype.sum_prod_type]
    have hrow : ∀ i : Unit,
        (∑ _t : Time, w.p i / (Fintype.card Time : ℝ)) = w.p i := by
      intro i
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    simp_rw [hrow]
    exact w.sum_one
    -- ∑_{(i,t)∈univ} p_i/|T| = ∑_i ∑_t p_i/|T| = ∑_i |T|·(p_i/|T|) = ∑_i p_i = 1.
    -- Hints: `Fintype.sum_prod_type`, `Finset.sum_const`, `Finset.card_univ`,
    -- `nsmul_eq_mul`, `mul_div_cancel₀`, `w.sum_one`; `|T| ≠ 0` from `Nonempty Time`.

/-- The cell-support bridge assigns each unit-period cell its unit weight divided
equally across periods. -/
@[simp] lemma cellSupport_weight (w : UnitWeights Unit) (r : Unit × Time) :
    (cellSupport w).weight r = w.p r.1 / (Fintype.card Time : ℝ) := rfl

/-- Every unit-period cell is observed in the cell-support bridge. -/
@[simp] lemma cellSupport_observed (w : UnitWeights Unit) :
    (cellSupport w).observed = (Finset.univ : Finset (Unit × Time)) := rfl

omit [Fintype Unit] [Fintype Time] [DecidableEq Unit] [DecidableEq Time]
  [Nonempty Unit] [Nonempty Time] in
/-- Membership in the two-axis additive span is exactly the panel's
`IsUnitTimeAdditive` predicate after uncurrying. -/
lemma mem_twoAxisAdditiveSpan_iff {h : Unit × Time → ℝ} :
    h ∈ twoAxisAdditiveSpan Unit Time ↔ IsUnitTimeAdditive (fun i t => h (i, t)) := by
  unfold twoAxisAdditiveSpan IsUnitTimeAdditive
  rw [AdditiveSpan.mem_iff]
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, fun i t => hab (i, t)⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, ?_⟩
    intro r
    simpa using hab r.1 r.2

/-- The `p`-weighted panel inner product is `|Time|` times the generic
weighted-support inner product on the cell support. -/
theorem inner_eq_card_smul_ip (w : UnitWeights Unit) (V W : Unit → Time → ℝ) :
    inner w V W =
      (Fintype.card Time : ℝ) *
        (cellSupport w).ip (fun r => V r.1 r.2) (fun r => W r.1 r.2) := by
  have hT : (Fintype.card Time : ℝ) ≠ 0 := by
    have h := Fintype.card_pos (α := Time)
    exact_mod_cast h.ne'
  simp only [inner, WeightedSupport.ip_def, cellSupport_observed, cellSupport_weight]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t _
  field_simp
  -- Unfold `inner` and `WeightedSupport.ip`; rewrite the cell sum over
  -- `Unit × Time` as `∑_i ∑_t` (`Fintype.sum_prod_type`).  Each cell summand is
  -- `(p_i/|T|) · V_it · W_it`; pull `|T|` out via `Finset.mul_sum` and use
  -- `w.p i * (V_it * W_it) = |T| * ((p_i/|T|) * V_it * W_it)` (needs `|T| ≠ 0`).

/-- **Concrete ↔ abstract bridge.** The closed-form two-way double demeaning
`ddot` is the generic `WeightedSupport` residual maker against the two-axis
additive span.  Every cell is observed, so the identity holds pointwise. -/
theorem ddot_eq_residualize (w : UnitWeights Unit) (V : Unit → Time → ℝ)
    (i : Unit) (t : Time) :
    (cellSupport w).residualize (twoAxisAdditiveSpan Unit Time)
        (fun r => V r.1 r.2) (i, t)
      = ddot w V i t := by
  classical
  set c : WeightedSupport (Unit × Time) := cellSupport w with hc
  set H := twoAxisAdditiveSpan Unit Time with hH
  set X : Unit × Time → ℝ := fun r => V r.1 r.2 with hX
  set Y : Unit × Time → ℝ := fun r => unitTimeProjection w V r.1 r.2 with hY
  have hYmem : Y ∈ H := by
    rw [hH, mem_twoAxisAdditiveSpan_iff]
    exact unitTimeProjection_additive w V
  have hT : (0 : ℝ) < (Fintype.card Time : ℝ) := by exact_mod_cast Fintype.card_pos
  have hTne : (Fintype.card Time : ℝ) ≠ 0 := ne_of_gt hT
  have hXY : ∀ r : Unit × Time, (X - Y) r = ddot w V r.1 r.2 := by
    intro r
    have h := sub_ddot_eq_unitTimeProjection w V r.1 r.2
    simp only [hX, hY, Pi.sub_apply]
    linarith [h]
  have horth : ∀ h ∈ H, c.ip (X - Y) h = 0 := by
    intro h hh
    have hadd : IsUnitTimeAdditive (fun i t => h (i, t)) :=
      (mem_twoAxisAdditiveSpan_iff).mp (hH ▸ hh)
    have hkey : inner w (ddot w V) (fun i t => h (i, t)) = 0 :=
      ddot_orthogonal_unit_time w hT V (fun i t => h (i, t)) hadd
    have hbridge :
        inner w (ddot w V) (fun i t => h (i, t))
          = (Fintype.card Time : ℝ)
              * c.ip (fun r => ddot w V r.1 r.2) (fun r => h (r.1, r.2)) := by
      rw [hc]
      exact inner_eq_card_smul_ip w (ddot w V) (fun i t => h (i, t))
    have hXYfun : (fun r : Unit × Time => ddot w V r.1 r.2) = X - Y := by
      funext r
      exact (hXY r).symm
    have hhfun : (fun r : Unit × Time => h (r.1, r.2)) = h := by
      funext r
      rfl
    rw [hXYfun, hhfun] at hbridge
    rw [hbridge] at hkey
    exact (mul_eq_zero.mp hkey).resolve_left hTne
  have hproj : c.proj H X (i, t) = Y (i, t) :=
    c.proj_apply_eq_of_mem_orthogonal H X hYmem horth (i, t) (by
      rw [hc]
      exact Finset.mem_univ _)
  simp only [WeightedSupport.residualize_apply, Pi.sub_apply, hproj]
  have h := hXY (i, t)
  simp only [hX, hY, Pi.sub_apply] at h
  linarith [h]
  -- Let `c := cellSupport w`, `H := twoAxisAdditiveSpan Unit Time`,
  -- `X := fun r => V r.1 r.2`, `Y := fun r => unitTimeProjection w V r.1 r.2`.
  -- (1) `Y ∈ H` via `mem_twoAxisAdditiveSpan_iff` + `unitTimeProjection_additive`.
  -- (2) `X - Y = fun r => ddot w V r.1 r.2` pointwise, by
  --     `sub_ddot_eq_unitTimeProjection`.
  -- (3) `∀ h ∈ H, c.ip (X - Y) h = 0`: rewrite via (2) and
  --     `inner_eq_card_smul_ip` to reduce to
  --     `inner w (ddot w V) (fun i t => h (i,t)) = 0`, which is
  --     `ddot_orthogonal_unit_time` (`hT : 0 < |Time|` from `Nonempty Time`,
  --     additivity from `mem_twoAxisAdditiveSpan_iff`); divide by `|T| ≠ 0`.
  -- (4) `c.proj H X (i,t) = Y (i,t)` by `proj_apply_eq_of_mem_orthogonal`
  --     (`observed = univ`).
  -- (5) `residualize_apply`: result `= V i t - unitTimeProjection w V i t
  --     = ddot w V i t` (last step `sub_ddot_eq_unitTimeProjection`).

end Bridge

end WeightedTwoWayPanel
end Panel
end Causalean
