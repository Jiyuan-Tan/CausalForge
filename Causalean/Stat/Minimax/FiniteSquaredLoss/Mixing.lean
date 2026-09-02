/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.FiniteSquaredLoss.Core
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Conditional mixing and convexified finite risk sets

This module proves the conditional Jensen step that turns mixtures of finite
procedures back into an ordinary randomized design with a bounded decision rule.
It then packages the compact convex risk set used by Sion's theorem.
-/

open scoped BigOperators
open Set

namespace Causalean.Stat.Minimax.FiniteSquaredLoss

open Causalean.Experimentation.DesignBased

variable {Theta R : Type*} [Fintype Theta] [Fintype R]
variable {X : R → Type*} [∀ r, Fintype (X r)]

/-- Conditional mixing combines two designs linearly and, at every design point
with positive mixed mass, averages their actions using the corresponding posterior
mixture weights; at zero mass it uses the lower endpoint. -/
noncomputable def mixProcedure {l u t : ℝ} (hlu : l ≤ u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (q₀ q₁ : Procedure X l u) : Procedure X l u := by
  let p : R → ℝ := fun r ↦ t * q₀.design.p r + (1 - t) * q₁.design.p r
  refine
    { design :=
        { p := p
          p_nonneg := ?_
          p_sum := ?_ }
      decision := ?_ }
  · intro r
    exact add_nonneg (mul_nonneg ht0 (q₀.design.p_nonneg r))
      (mul_nonneg (sub_nonneg.mpr ht1) (q₁.design.p_nonneg r))
  · simp only [p, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [q₀.design.p_sum, q₁.design.p_sum]
    ring
  · intro r x
    by_cases hp : p r = 0
    · exact ⟨l, le_rfl, hlu⟩
    · let a₀ := t * q₀.design.p r / p r
      let a₁ := (1 - t) * q₁.design.p r / p r
      refine ⟨a₀ * (q₀.decision r x : ℝ) + a₁ * (q₁.decision r x : ℝ), ?_, ?_⟩
      · -- Show `a₀,a₁ ≥ 0` and `a₀+a₁=1`, then combine the two lower bounds.
        have hp_nonneg : 0 ≤ p r := add_nonneg
          (mul_nonneg ht0 (q₀.design.p_nonneg r))
          (mul_nonneg (sub_nonneg.mpr ht1) (q₁.design.p_nonneg r))
        have ha₀ : 0 ≤ a₀ := div_nonneg
          (mul_nonneg ht0 (q₀.design.p_nonneg r)) hp_nonneg
        have ha₁ : 0 ≤ a₁ := div_nonneg
          (mul_nonneg (sub_nonneg.mpr ht1) (q₁.design.p_nonneg r)) hp_nonneg
        have ha_sum : a₀ + a₁ = 1 := by
          simp only [a₀, a₁, ← add_div]
          exact div_self hp
        calc
          l = a₀ * l + a₁ * l := by rw [← add_mul, ha_sum, one_mul]
          _ ≤ a₀ * (q₀.decision r x : ℝ) + a₁ * (q₁.decision r x : ℝ) :=
            add_le_add
              (mul_le_mul_of_nonneg_left (q₀.decision r x).property.1 ha₀)
              (mul_le_mul_of_nonneg_left (q₁.decision r x).property.1 ha₁)
      · -- The same convex-weight calculation combines the two upper bounds.
        have hp_nonneg : 0 ≤ p r := add_nonneg
          (mul_nonneg ht0 (q₀.design.p_nonneg r))
          (mul_nonneg (sub_nonneg.mpr ht1) (q₁.design.p_nonneg r))
        have ha₀ : 0 ≤ a₀ := div_nonneg
          (mul_nonneg ht0 (q₀.design.p_nonneg r)) hp_nonneg
        have ha₁ : 0 ≤ a₁ := div_nonneg
          (mul_nonneg (sub_nonneg.mpr ht1) (q₁.design.p_nonneg r)) hp_nonneg
        have ha_sum : a₀ + a₁ = 1 := by
          simp only [a₀, a₁, ← add_div]
          exact div_self hp
        calc
          a₀ * (q₀.decision r x : ℝ) + a₁ * (q₁.decision r x : ℝ)
              ≤ a₀ * u + a₁ * u :=
            add_le_add
              (mul_le_mul_of_nonneg_left (q₀.decision r x).property.2 ha₀)
              (mul_le_mul_of_nonneg_left (q₁.decision r x).property.2 ha₁)
          _ = u := by rw [← add_mul, ha_sum, one_mul]

/-- With [nonnegative](hyp:hP) [likelihood coefficients](hyp:P), [an ordered action interval](hyp:hlu),
and [a mixing weight between zero and one](hyp:ht0,ht1), conditional mixing produces a
procedure whose [statewise squared-loss risk is no greater than the corresponding mixture
of the two original risks](goal). No normalization of the coefficients is required. -/
theorem risk_mixProcedure_le
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (hP : ∀ theta r x, 0 ≤ P theta r x)
    {l u t : ℝ} (hlu : l ≤ u) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (q₀ q₁ : Procedure X l u) (theta : Theta) :
    risk P tau (mixProcedure hlu ht0 ht1 q₀ q₁) theta ≤
      t * risk P tau q₀ theta + (1 - t) * risk P tau q₁ theta := by
  /- Split on each mixed design mass. At positive mass, clear its denominator and
  use the two-point squared-loss identity/Jensen inequality. At zero mass,
  nonnegativity forces both weighted component masses to vanish. Multiply the
  pointwise inequality by `P ≥ 0` and sum first over observations, then designs. -/
  classical
  unfold risk
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  let m₀ : ℝ := t * q₀.design.p r
  let m₁ : ℝ := (1 - t) * q₁.design.p r
  let p : ℝ := m₀ + m₁
  have hm₀ : 0 ≤ m₀ := mul_nonneg ht0 (q₀.design.p_nonneg r)
  have hm₁ : 0 ≤ m₁ := mul_nonneg (sub_nonneg.mpr ht1) (q₁.design.p_nonneg r)
  have hp_nonneg : 0 ≤ p := add_nonneg hm₀ hm₁
  by_cases hp_zero : p = 0
  · have hm₀_zero : m₀ = 0 := by nlinarith
    have hm₁_zero : m₁ = 0 := by nlinarith
    change p * _ ≤
      t * (q₀.design.p r * _) + (1 - t) * (q₁.design.p r * _)
    rw [hp_zero, zero_mul, ← mul_assoc t, ← mul_assoc (1 - t),
      show t * q₀.design.p r = 0 from hm₀_zero,
      show (1 - t) * q₁.design.p r = 0 from hm₁_zero]
    simp
  · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_zero)
    have hdesign :
        (mixProcedure hlu ht0 ht1 q₀ q₁).design.p r = p := by
      rfl
    rw [hdesign, Finset.mul_sum]
    rw [← mul_assoc t, ← mul_assoc (1 - t), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have hdecision :
        ((mixProcedure hlu ht0 ht1 q₀ q₁).decision r x : ℝ) =
          m₀ / p * (q₀.decision r x : ℝ) +
            m₁ / p * (q₁.decision r x : ℝ) := by
      simp [mixProcedure, p, m₀, m₁, hp_zero]
    rw [hdecision]
    have hid :
        (m₀ / p * (q₀.decision r x : ℝ) +
            m₁ / p * (q₁.decision r x : ℝ)) - tau theta =
          (m₀ * ((q₀.decision r x : ℝ) - tau theta) +
            m₁ * ((q₁.decision r x : ℝ) - tau theta)) / p := by
      field_simp
      simp only [p]
      ring
    have hjensen :
        p * ((m₀ / p * (q₀.decision r x : ℝ) +
            m₁ / p * (q₁.decision r x : ℝ)) - tau theta) ^ 2 ≤
          m₀ * ((q₀.decision r x : ℝ) - tau theta) ^ 2 +
            m₁ * ((q₁.decision r x : ℝ) - tau theta) ^ 2 := by
      rw [hid, div_pow]
      field_simp
      simp only [p]
      have hvar : 0 ≤ m₀ * m₁ *
          (((q₀.decision r x : ℝ) - tau theta) -
            ((q₁.decision r x : ℝ) - tau theta)) ^ 2 :=
        mul_nonneg (mul_nonneg hm₀ hm₁) (sq_nonneg _)
      nlinarith [hvar]
    calc
      p * (P theta r x *
          ((m₀ / p * (q₀.decision r x : ℝ) +
            m₁ / p * (q₁.decision r x : ℝ)) - tau theta) ^ 2) =
          P theta r x * (p *
            ((m₀ / p * (q₀.decision r x : ℝ) +
              m₁ / p * (q₁.decision r x : ℝ)) - tau theta) ^ 2) := by ring
      _ ≤ P theta r x *
          (m₀ * ((q₀.decision r x : ℝ) - tau theta) ^ 2 +
            m₁ * ((q₁.decision r x : ℝ) - tau theta) ^ 2) :=
        mul_le_mul_of_nonneg_left hjensen (hP theta r x)
      _ = t * q₀.design.p r *
            (P theta r x * ((q₀.decision r x : ℝ) - tau theta) ^ 2) +
          (1 - t) * q₁.design.p r *
            (P theta r x * ((q₁.decision r x : ℝ) - tau theta) ^ 2) := by
        simp only [m₀, m₁]
        ring

/-- A risk vector is dominated when some ordinary finite procedure has no larger
risk in any state. -/
def dominatedRiskVectors
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ) (l u : ℝ) :
    Set (Theta → ℝ) :=
  {z | ∃ q : Procedure X l u, ∀ theta, risk P tau q theta ≤ z theta}

/-- With [nonnegative](hyp:hP) [likelihood coefficients](hyp:P) and [an ordered action interval](hyp:hlu),
the set of risk vectors dominated by an ordinary finite procedure [is convex](goal). -/
theorem convex_dominatedRiskVectors
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (hP : ∀ theta r x, 0 ≤ P theta r x) {l u : ℝ} (hlu : l ≤ u) :
    Convex ℝ (dominatedRiskVectors P tau l u) := by
  -- Unpack two witnessing procedures and use `mixProcedure` plus `risk_mixProcedure_le`.
  intro z hz w hw a b ha hb hab
  rcases hz with ⟨q₀, hq₀⟩
  rcases hw with ⟨q₁, hq₁⟩
  have ha1 : a ≤ 1 := by nlinarith
  refine ⟨mixProcedure hlu ha ha1 q₀ q₁, ?_⟩
  intro theta
  calc
    risk P tau (mixProcedure hlu ha ha1 q₀ q₁) theta ≤
        a * risk P tau q₀ theta + (1 - a) * risk P tau q₁ theta :=
      risk_mixProcedure_le P tau hP hlu ha ha1 q₀ q₁ theta
    _ ≤ a * z theta + (1 - a) * w theta :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hq₀ theta) ha)
        (mul_le_mul_of_nonneg_left (hq₁ theta) (sub_nonneg.mpr ha1))
    _ = (a • z + b • w) theta := by
      have hb_eq : b = 1 - a := by linarith
      simp [hb_eq]

/-- Under given [likelihood coefficients](hyp:P), every risk vector attained by feasible ambient
coordinates [is dominated by the risk of the associated ordinary finite procedure](goal). -/
theorem riskVector_image_subset_dominated
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ) (l u : ℝ) :
    riskVector P tau '' procedureSet X l u ⊆ dominatedRiskVectors P tau l u := by
  -- Convert the feasible preimage point with `Procedure.ofAmbient`; risks agree definitionally.
  rintro z ⟨y, hy, rfl⟩
  refine ⟨Procedure.ofAmbient hy, ?_⟩
  intro theta
  rw [← rawRisk_toAmbient]
  rw [Procedure.toAmbient_ofAmbient]
  rfl

/-- With [nonnegative](hyp:hP) [likelihood coefficients](hyp:P) and [an ordered action interval](hyp:hlu),
every [convex combination of attainable risk vectors](hyp:hz) is [coordinatewise dominated
by the risk vector of an ordinary finite procedure](goal). -/
theorem exists_procedure_risk_le_of_mem_convexHull
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (hP : ∀ theta r x, 0 ≤ P theta r x) {l u : ℝ} (hlu : l ≤ u)
    {z : Theta → ℝ}
    (hz : z ∈ convexHull ℝ (riskVector P tau '' procedureSet X l u)) :
    ∃ q : Procedure X l u, ∀ theta, risk P tau q theta ≤ z theta := by
  -- Apply `convexHull_min` to the convex dominated set and the attainable-image inclusion.
  exact (convexHull_min
    (riskVector_image_subset_dominated P tau l u)
    (convex_dominatedRiskVectors P tau hP hlu)) hz

/-- Under given [likelihood coefficients](hyp:P), the convex hull of the attainable finite risk
vectors [is compact](goal). -/
theorem isCompact_convexHull_riskVectors
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ) (l u : ℝ) :
    IsCompact (convexHull ℝ (riskVector P tau '' procedureSet X l u)) := by
  /- Carathéodory bounds every representation by `card Theta + 1` points.  After
  padding shorter representations with zero-weight copies of a fixed source point,
  the hull is the continuous barycenter image of a compact power of the source
  times a standard simplex. -/
  classical
  let s : Set (Theta → ℝ) := riskVector P tau '' procedureSet X l u
  have hs : IsCompact s := isCompact_riskVector_image P tau l u
  by_cases hs_empty : s = ∅
  · simp [s, hs_empty]
  have hs_nonempty : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hs_empty
  let z₀ : Theta → ℝ := hs_nonempty.some
  have hz₀ : z₀ ∈ s := hs_nonempty.some_mem
  let n := Fintype.card Theta + 1
  let A : Set ((Fin n → Theta → ℝ) × (Fin n → ℝ)) :=
    {p | (∀ i, p.1 i ∈ s) ∧ p.2 ∈ stdSimplex ℝ (Fin n)}
  have hpoints : IsCompact {z : Fin n → Theta → ℝ | ∀ i, z i ∈ s} := by
    rw [show {z : Fin n → Theta → ℝ | ∀ i, z i ∈ s} =
        Set.univ.pi (fun _ ↦ s) by ext z; simp]
    exact isCompact_univ_pi (fun _ ↦ hs)
  have hA : IsCompact A := by
    rw [show A = {z : Fin n → Theta → ℝ | ∀ i, z i ∈ s} ×ˢ
        stdSimplex ℝ (Fin n) by ext p; simp [A]]
    exact hpoints.prod (isCompact_stdSimplex ℝ (Fin n))
  have hbarycenter : Continuous
      (fun p : (Fin n → Theta → ℝ) × (Fin n → ℝ) ↦
        ∑ i, p.2 i • p.1 i) := by
    fun_prop
  have himage : IsCompact
      ((fun p : (Fin n → Theta → ℝ) × (Fin n → ℝ) ↦
        ∑ i, p.2 i • p.1 i) '' A) := hA.image hbarycenter
  convert himage using 1
  ext x
  constructor
  · intro hx
    rw [convexHull_eq_union] at hx
    simp only [exists_prop, Set.mem_iUnion] at hx
    obtain ⟨t, hts, ht_ind, hxt⟩ := hx
    rw [Finset.mem_convexHull'] at hxt
    obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := hxt
    have ht_card : Fintype.card t ≤ n := by
      calc
        Fintype.card t ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Theta → ℝ))) + 1 :=
          ht_ind.card_le_finrank_succ
        _ ≤ Module.finrank ℝ (Theta → ℝ) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_le _) 1
        _ = n := by simp [n]
    let e : t ↪ Fin n := Classical.choice
      (Function.Embedding.nonempty_of_card_le (by simpa using ht_card))
    let w' : Fin n → ℝ := Function.extend e (fun i ↦ w i) (fun _ ↦ 0)
    let z' : Fin n → Theta → ℝ :=
      Function.extend e (fun i ↦ (i : Theta → ℝ)) (fun _ ↦ z₀)
    have hz' : ∀ i, z' i ∈ s := by
      intro i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        rw [show z' (e j) = (j : Theta → ℝ) by
          simp [z', e.injective.extend_apply]]
        exact hts j.property
      · simpa [z', Function.extend_apply' _ _ _ hi] using hz₀
    have hw'_nonneg : ∀ i, 0 ≤ w' i := by
      intro i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        simpa [w', e.injective.extend_apply] using hw_nonneg j j.property
      · simp [w', Function.extend_apply' _ _ _ hi]
    have hw'_sum : ∑ i, w' i = 1 := by
      calc
        ∑ i, w' i = ∑ i ∈ Finset.univ.map e, w' i := by
          symm
          apply Finset.sum_subset (by simp)
          intro i _ hi
          have hi' : i ∉ Set.range e := by simpa using hi
          simp [w', Function.extend_apply' _ _ _ hi']
        _ = ∑ i : t, w i := by simp [w', e.injective.extend_apply]
        _ = 1 := by
          rw [← hw_sum]
          exact (Finset.sum_subtype t (fun _ ↦ Iff.rfl) w).symm
    have hcenter : ∑ i, w' i • z' i = x := by
      calc
        ∑ i, w' i • z' i = ∑ i ∈ Finset.univ.map e, w' i • z' i := by
          symm
          apply Finset.sum_subset (by simp)
          intro i _ hi
          have hi' : i ∉ Set.range e := by simpa using hi
          simp [w', Function.extend_apply' _ _ _ hi']
        _ = ∑ i : t, w i • (i : Theta → ℝ) := by
          simp [w', z', e.injective.extend_apply]
        _ = x := by
          rw [← hw_center]
          exact (Finset.sum_subtype t (fun _ ↦ Iff.rfl)
            (fun y ↦ w y • y)).symm
    exact ⟨(z', w'), ⟨hz', ⟨hw'_nonneg, hw'_sum⟩⟩, hcenter⟩
  · rintro ⟨p, hp, rfl⟩
    exact mem_convexHull_of_exists_fintype p.2 p.1 hp.2.1 hp.2.2 hp.1 rfl

end Causalean.Stat.Minimax.FiniteSquaredLoss
