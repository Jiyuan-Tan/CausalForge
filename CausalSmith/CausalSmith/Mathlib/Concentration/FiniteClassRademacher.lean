/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-class Rademacher envelopes

This file supplies a finite-class Massart producer for the
`RademacherUpperBound` predicate used by the localized concentration layer.

The theorem below is intentionally the global finite-class envelope:
`ψ(r) = b / sqrt n * sqrt(2 log(2 |ι|))`.  It is a genuine sub-root upper
bound for every localized star-hull radius, because `starHullZeroOut` is
pointwise dominated by the original finite class.

The second theorem is the sharp linear localized envelope
`ψ(r) = r * sqrt(2 log(2 |ι|) / n)` under the faithful radius regularity
condition that active star-hull rays at radius `r` have scalar coefficient at
most `r`, plus the unit finite-class envelope on the observed coordinates.
-/

import Causalean.Stat.Concentration.UniformDeviation.CriticalRadius
import Causalean.Stat.Concentration.Rademacher.Contraction
import FoML.Massart

namespace CausalSmith.Mathlib.Concentration

open MeasureTheory ProbabilityTheory Real
open Causalean.Stat.Concentration
open scoped BigOperators

variable {Ω ι 𝒳 : Type*} [MeasurableSpace Ω]

/-- The signed doubling of a class, used to convert the absolute-value
Rademacher complexity into a one-sided finite supremum. -/
private noncomputable def signedClass (F : ι → 𝒳 → ℝ) :
    ι × Bool → 𝒳 → ℝ
  | (i, true), x => F i x
  | (i, false), x => -F i x

private lemma abs_signedClass_bound
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {b : ℝ}
    (hbound : ∀ i k, |F i (S k)| ≤ b) :
    ∀ j : ι × Bool, ∀ k : Fin n, |signedClass F j (S k)| ≤ b := by
  intro j k
  cases j with
  | mk i s =>
      cases s <;> simpa [signedClass] using hbound i k

/-- For a finite class, the absolute-value empirical Rademacher complexity is
bounded by the one-sided complexity of the signed doubled class. -/
private lemma empiricalRademacherComplexity_le_signed_without_abs
    [Fintype ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S
      ≤ empiricalRademacherComplexity_without_abs n
          (ProbabilityTheory.F_on (signedClass F)
            (Finset.univ : Finset (ι × Bool))) S := by
  classical
  unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine ciSup_le ?_
  intro i
  let T : ℝ := (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)
  have hbdd :
      BddAbove
        (Set.range
          (fun j : {j // j ∈ (Finset.univ : Finset (ι × Bool))} =>
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              ProbabilityTheory.F_on (signedClass F)
                (Finset.univ : Finset (ι × Bool)) j (S k))) :=
    (Set.toFinite _).bddAbove
  by_cases hT : 0 ≤ T
  · have hval :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            ProbabilityTheory.F_on (signedClass F)
              (Finset.univ : Finset (ι × Bool))
              ⟨(i, true), by simp⟩ (S k)
          = T := by
      simp [T, ProbabilityTheory.F_on, signedClass]
    rw [abs_of_nonneg hT]
    exact hval ▸
      le_ciSup hbdd (⟨(i, true), by simp⟩ :
        {j // j ∈ (Finset.univ : Finset (ι × Bool))})
  · have hT' : T < 0 := lt_of_not_ge hT
    have hval :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            ProbabilityTheory.F_on (signedClass F)
              (Finset.univ : Finset (ι × Bool))
              ⟨(i, false), by simp⟩ (S k)
          = -T := by
      simp [T, ProbabilityTheory.F_on, signedClass, Finset.mul_sum]
    rw [abs_of_neg hT']
    exact hval ▸
      le_ciSup hbdd (⟨(i, false), by simp⟩ :
        {j // j ∈ (Finset.univ : Finset (ι × Bool))})

/-- Pointwise domination of the localized star-hull zero-out class by the
original finite class.  The scalar star-hull parameter lies in `[0,1]`, and the
zeroed branch contributes `0`. -/
private lemma empirical_starHullZeroOut_le
    [Finite ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (r : ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
      ≤ empiricalRademacherComplexity n F S := by
  classical
  unfold empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine ciSup_le ?_
  intro p
  let T : ℝ := (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F p.2 (S k)
  have hbdd :
      BddAbove
        (Set.range
          (fun i : ι =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) :=
    Finite.bddAbove_range _
  have hsup_nonneg :
      0 ≤ ⨆ i : ι,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
    let i0 : ι := Classical.choice inferInstance
    exact le_trans
      (abs_nonneg ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i0 (S k)))
      (le_ciSup hbdd i0)
  by_cases hp : norm (starHullEval F p) ≤ r
  · have hsum :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)
          = p.1.val * T := by
      have hsum' :
          ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p (S k)
            = p.1.val * ∑ k : Fin n, (σ k : ℝ) * F p.2 (S k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        simp [starHullZeroOut, hp, starHullEval]
        ring
      rw [hsum']
      dsimp [T]
      ring
    have hα_nonneg : 0 ≤ p.1.val := p.1.property.1
    have hα_le_one : p.1.val ≤ 1 := p.1.property.2
    calc
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r p (S k)|
          = p.1.val * |T| := by
            rw [hsum, abs_mul, abs_of_nonneg hα_nonneg]
      _ ≤ |T| := by
            simpa [one_mul] using mul_le_mul_of_nonneg_right hα_le_one (abs_nonneg T)
      _ ≤ ⨆ i : ι,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| :=
            le_ciSup hbdd p.2
  · have hzero :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k) = 0 := by
      have hsum :
          ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p (S k) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k _
        simp [starHullZeroOut, hp]
      rw [hsum]
      ring
    rw [hzero, abs_zero]
    exact hsup_nonneg

private lemma finite_empirical_massart_abs
    [Fintype ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) {n : ℕ} (hn : 0 < n)
    (S : Fin n → 𝒳) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ i k, |F i (S k)| ≤ b) :
    empiricalRademacherComplexity n F S
      ≤ (b / Real.sqrt (n : ℝ)) *
          Real.sqrt (2 * Real.log (2 * Fintype.card ι)) := by
  classical
  let J : Type _ := ι × Bool
  let t : Finset J := Finset.univ
  have ht : t.Nonempty := Finset.univ_nonempty
  have hbridge :
      empiricalRademacherComplexity_without_abs n
          (ProbabilityTheory.F_on (signedClass F) t) S
        =
      empiricalRademacherComplexity_pmf_without_abs n
          (ProbabilityTheory.F_on (signedClass F) t) S := by
    simpa using
      (empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs
        (n := n) (f := ProbabilityTheory.F_on (signedClass F) t) (S := S))
  have hmass :
      empiricalRademacherComplexity_pmf_without_abs n
          (ProbabilityTheory.F_on (signedClass F) t) S
        ≤
      (Finset.sup' t ht
        (fun j =>
          Real.sqrt (∑ k : Fin n,
            (((n : ℝ)⁻¹ * |signedClass F j (S k)|) ^ 2))))
        * Real.sqrt (2 * Real.log t.card) :=
    ProbabilityTheory.massart_lemma_pmf
      (F := signedClass F) (S := S) (f := t) ht hn b
      (by
        intro j _ k
        exact abs_signedClass_bound (F := F) (S := S) hbound j k)
      ht
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsup :
      (Finset.sup' t ht
        (fun j =>
          Real.sqrt (∑ k : Fin n,
            (((n : ℝ)⁻¹ * |signedClass F j (S k)|) ^ 2))))
        ≤ b / Real.sqrt (n : ℝ) := by
    have hconst_nonneg : 0 ≤ (n : ℝ)⁻¹ * b :=
      mul_nonneg (inv_nonneg.mpr (le_of_lt hnR)) hb
    have hsqrt_const :
        Real.sqrt ((n : ℝ) * (((n : ℝ)⁻¹ * b) ^ 2))
          = b / Real.sqrt (n : ℝ) := by
      calc
        Real.sqrt ((n : ℝ) * (((n : ℝ)⁻¹ * b) ^ 2))
            = Real.sqrt (n : ℝ) * Real.sqrt (((n : ℝ)⁻¹ * b) ^ 2) := by
              rw [Real.sqrt_mul (le_of_lt hnR)]
        _ = Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * b) := by
              simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hconst_nonneg]
        _ = b / Real.sqrt (n : ℝ) := by
              have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
              have hsqrt0 : Real.sqrt (n : ℝ) ≠ 0 :=
                ne_of_gt (Real.sqrt_pos.2 hnR)
              have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
                simp [Real.sq_sqrt (le_of_lt hnR)]
              field_simp [hn0, hsqrt0]
              rw [hsq]
    rw [Finset.sup'_le_iff]
    intro j _
    have hterm :
        ∀ k : Fin n,
          (((n : ℝ)⁻¹ * |signedClass F j (S k)|) ^ 2)
            ≤ (((n : ℝ)⁻¹ * b) ^ 2) := by
      intro k
      have hjk : |signedClass F j (S k)| ≤ b :=
        abs_signedClass_bound (F := F) (S := S) hbound j k
      have hmul :
          (n : ℝ)⁻¹ * |signedClass F j (S k)|
            ≤ (n : ℝ)⁻¹ * b :=
        mul_le_mul_of_nonneg_left hjk (inv_nonneg.mpr (le_of_lt hnR))
      have hmul_nonneg :
          0 ≤ (n : ℝ)⁻¹ * |signedClass F j (S k)| :=
        mul_nonneg (inv_nonneg.mpr (le_of_lt hnR)) (abs_nonneg _)
      nlinarith
    have hsum :
        (∑ k : Fin n, (((n : ℝ)⁻¹ * |signedClass F j (S k)|) ^ 2))
          ≤ ∑ _k : Fin n, (((n : ℝ)⁻¹ * b) ^ 2) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    calc
      Real.sqrt (∑ k : Fin n,
          (((n : ℝ)⁻¹ * |signedClass F j (S k)|) ^ 2))
          ≤ Real.sqrt (∑ _k : Fin n, (((n : ℝ)⁻¹ * b) ^ 2)) :=
            Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((n : ℝ) * (((n : ℝ)⁻¹ * b) ^ 2)) := by simp
      _ = b / Real.sqrt (n : ℝ) := hsqrt_const
  have hcard : (t.card : ℝ) = 2 * Fintype.card ι := by
    simp [t, J]
    ring
  have hnoabs :
      empiricalRademacherComplexity_without_abs n
          (ProbabilityTheory.F_on (signedClass F) t) S
        ≤
      (b / Real.sqrt (n : ℝ)) *
          Real.sqrt (2 * Real.log (2 * Fintype.card ι)) := by
    have htmp :
        empiricalRademacherComplexity_without_abs n
            (ProbabilityTheory.F_on (signedClass F) t) S
          ≤
        (Finset.sup' t ht
          (fun j =>
            Real.sqrt (∑ k : Fin n,
              (((n : ℝ)⁻¹ * |signedClass F j (S k)|) ^ 2))))
          * Real.sqrt (2 * Real.log t.card) := by
      simpa [hbridge] using hmass
    exact htmp.trans
      (by
        have hmul :=
          mul_le_mul_of_nonneg_right hsup
            (Real.sqrt_nonneg (2 * Real.log t.card))
        simpa [hcard] using hmul)
  exact (empiricalRademacherComplexity_le_signed_without_abs F n S).trans hnoabs

private lemma finite_global_rademacher_starHullZeroOut
    [Fintype ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → 𝒳)
    {n : ℕ} (hn : 0 < n) (r : ℝ)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ i ω, |F i (X ω)| ≤ b) :
    rademacherComplexity n (starHullZeroOut F norm r) μ X
      ≤ (b / Real.sqrt (n : ℝ)) *
          Real.sqrt (2 * Real.log (2 * Fintype.card ι)) := by
  classical
  let C : ℝ :=
    (b / Real.sqrt (n : ℝ)) *
      Real.sqrt (2 * Real.log (2 * Fintype.card ι))
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg
      (div_nonneg hb (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  unfold rademacherComplexity
  have hpoint :
      ∀ᵐ ω : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω)
          ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    exact (empirical_starHullZeroOut_le F norm r n (X ∘ ω)).trans
      (finite_empirical_massart_abs F hn (X ∘ ω) b hb
        (fun i k => hbound i (ω k)))
  calc
    ∫ ω : Fin n → Ω,
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω)
        ∂Measure.pi (fun _ : Fin n => μ)
        ≤ ∫ _ω : Fin n → Ω, C ∂Measure.pi (fun _ : Fin n => μ) := by
          exact MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω =>
              by
                unfold empiricalRademacherComplexity
                refine mul_nonneg ?_ ?_
                · positivity
                · refine Finset.sum_nonneg ?_
                  intro σ _
                  refine Real.iSup_nonneg ?_
                  intro p
                  exact abs_nonneg _)
            (integrable_const C)
            hpoint
    _ = C := by simp [C]

private lemma finiteClass_logFactor_nonneg [Fintype ι] [Nonempty ι] :
    0 ≤ 2 * Real.log (2 * Fintype.card ι) := by
  have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hcard_one_nat : 1 ≤ Fintype.card ι := Nat.succ_le_of_lt hcard_pos
  have hcard_one : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard_one_nat
  have harg : (1 : ℝ) ≤ 2 * Fintype.card ι := by
    nlinarith
  have hlog : 0 ≤ Real.log (2 * Fintype.card ι) :=
    Real.log_nonneg harg
  nlinarith

private lemma finiteClass_unitMassart_constant_eq
    [Fintype ι] [Nonempty ι] {n : ℕ} (_hn : 0 < n) :
    (1 / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * Fintype.card ι))
      =
    Real.sqrt ((2 * Real.log (2 * Fintype.card ι)) / (n : ℝ)) := by
  have hA : 0 ≤ 2 * Real.log (2 * Fintype.card ι) :=
    finiteClass_logFactor_nonneg (ι := ι)
  calc
    (1 / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * Fintype.card ι))
        =
      Real.sqrt (2 * Real.log (2 * Fintype.card ι)) /
        Real.sqrt (n : ℝ) := by ring
    _ =
      Real.sqrt ((2 * Real.log (2 * Fintype.card ι)) / (n : ℝ)) := by
        exact (Real.sqrt_div hA (n : ℝ)).symm

/-- Localized star-hull domination by the finite class scaled by the radius.

The hypothesis `hscale` is the normal radius regularity condition: whenever a
star-hull ray is active at radius `r`, its scalar coefficient is at most `r`.
For normalized homogeneous norms this follows from `norm (F i) ≥ 1` together
with positive homogeneity; here it is kept as the exact local substrate needed
by the finite-class proof. -/
private lemma empirical_starHullZeroOut_le_smul_radius
    [Finite ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (r : ℝ) (hr : 0 ≤ r)
    (hscale : ∀ p : starHullParam ι,
      norm (starHullEval F p) ≤ r → p.1.val ≤ r)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
      ≤ empiricalRademacherComplexity n (fun i x => r * F i x) S := by
  classical
  unfold empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine ciSup_le ?_
  intro p
  let T : ℝ := (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F p.2 (S k)
  have hbdd :
      BddAbove
        (Set.range
          (fun i : ι =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                (r * F i (S k))|)) :=
    Finite.bddAbove_range _
  have hsup_nonneg :
      0 ≤ ⨆ i : ι,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              (r * F i (S k))| := by
    let i0 : ι := Classical.choice inferInstance
    exact le_trans
      (abs_nonneg
        ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          (r * F i0 (S k))))
      (le_ciSup hbdd i0)
  by_cases hp : norm (starHullEval F p) ≤ r
  · have hsum :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)
          = p.1.val * T := by
      have hsum' :
          ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p (S k)
            = p.1.val * ∑ k : Fin n, (σ k : ℝ) * F p.2 (S k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        simp [starHullZeroOut, hp, starHullEval]
        ring
      rw [hsum']
      dsimp [T]
      ring
    have hscaled :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (r * F p.2 (S k))
          = r * T := by
      have hsum_scaled :
          ∑ k : Fin n, (σ k : ℝ) * (r * F p.2 (S k))
            = r * ∑ k : Fin n, (σ k : ℝ) * F p.2 (S k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        ring
      rw [hsum_scaled]
      dsimp [T]
      ring
    have hα_nonneg : 0 ≤ p.1.val := p.1.property.1
    have hα_le_r : p.1.val ≤ r := hscale p hp
    calc
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r p (S k)|
          = p.1.val * |T| := by
            rw [hsum, abs_mul, abs_of_nonneg hα_nonneg]
      _ ≤ r * |T| :=
            mul_le_mul_of_nonneg_right hα_le_r (abs_nonneg T)
      _ = |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            (r * F p.2 (S k))| := by
            symm
            rw [hscaled, abs_mul, abs_of_nonneg hr]
      _ ≤ ⨆ i : ι,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              (r * F i (S k))| :=
            le_ciSup hbdd p.2
  · have hzero :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k) = 0 := by
      have hsum :
          ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p (S k) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k _
        simp [starHullZeroOut, hp]
      rw [hsum]
      ring
    rw [hzero, abs_zero]
    exact hsup_nonneg

private lemma finite_linear_rademacher_starHullZeroOut
    [Fintype ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → 𝒳)
    {n : ℕ} (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r)
    (hscale : ∀ p : starHullParam ι,
      norm (starHullEval F p) ≤ r → p.1.val ≤ r)
    (hunit : ∀ i ω, |F i (X ω)| ≤ 1) :
    rademacherComplexity n (starHullZeroOut F norm r) μ X
      ≤ r *
          Real.sqrt ((2 * Real.log (2 * Fintype.card ι)) / (n : ℝ)) := by
  classical
  let C : ℝ :=
    Real.sqrt ((2 * Real.log (2 * Fintype.card ι)) / (n : ℝ))
  unfold rademacherComplexity
  have hpoint :
      ∀ᵐ ω : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω)
          ≤ r * C := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hbase :
        empiricalRademacherComplexity n F (X ∘ ω) ≤ C := by
      have hmass :=
        finite_empirical_massart_abs F hn (X ∘ ω) (1 : ℝ) zero_le_one
          (fun i k => hunit i (ω k))
      have hconst :
          (1 / Real.sqrt (n : ℝ)) *
              Real.sqrt (2 * Real.log (2 * Fintype.card ι))
            = C := by
        change
          (1 / Real.sqrt (n : ℝ)) *
              Real.sqrt (2 * Real.log (2 * Fintype.card ι))
            =
          Real.sqrt ((2 * Real.log (2 * Fintype.card ι)) / (n : ℝ))
        exact finiteClass_unitMassart_constant_eq (ι := ι) hn
      calc
        empiricalRademacherComplexity n F (X ∘ ω)
            ≤ (1 / Real.sqrt (n : ℝ)) *
                Real.sqrt (2 * Real.log (2 * Fintype.card ι)) :=
              hmass
        _ = C := hconst
    calc
      empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω)
          ≤ empiricalRademacherComplexity n (fun i x => r * F i x) (X ∘ ω) :=
            empirical_starHullZeroOut_le_smul_radius F norm r hr hscale n (X ∘ ω)
      _ = |r| * empiricalRademacherComplexity n F (X ∘ ω) :=
            empiricalRademacherComplexity_smul_class F r n (X ∘ ω)
      _ = r * empiricalRademacherComplexity n F (X ∘ ω) := by
            rw [abs_of_nonneg hr]
      _ ≤ r * C :=
            mul_le_mul_of_nonneg_left hbase hr
  calc
    ∫ ω : Fin n → Ω,
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω)
        ∂Measure.pi (fun _ : Fin n => μ)
        ≤ ∫ _ω : Fin n → Ω, r * C ∂Measure.pi (fun _ : Fin n => μ) := by
          exact MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω =>
              by
                unfold empiricalRademacherComplexity
                refine mul_nonneg ?_ ?_
                · positivity
                · refine Finset.sum_nonneg ?_
                  intro σ _
                  refine Real.iSup_nonneg ?_
                  intro p
                  exact abs_nonneg _)
            (integrable_const (r * C))
            hpoint
    _ = r * C := by simp [C]

private lemma subRoot_const {C : ℝ} (hC : 0 ≤ C) :
    SubRoot (fun _ : ℝ => C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _
    exact hC
  · intro _ _ _ _
    exact le_rfl
  · intro r₁ r₂ hr₁ hrle
    have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hrle
    have hdiv : C / r₂ ≤ C / r₁ :=
      div_le_div_of_nonneg_left hC hr₁ hrle
    exact hdiv

private lemma subRoot_linear {C : ℝ} (hC : 0 ≤ C) :
    SubRoot (fun r : ℝ => r * C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact mul_nonneg hr hC
  · intro r₁ r₂ _ hrle
    exact mul_le_mul_of_nonneg_right hrle hC
  · intro r₁ r₂ hr₁ hrle
    have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hrle
    have h₁ : (r₁ * C) / r₁ = C := by
      field_simp [ne_of_gt hr₁]
    have h₂ : (r₂ * C) / r₂ = C := by
      field_simp [ne_of_gt hr₂]
    rw [h₁, h₂]

/-- Global finite-class Massart producer for the localized
`RademacherUpperBound` predicate.

This is the staged, non-vacuous finite-class envelope: it bounds every
localized star-hull radius by the global Massart complexity of the original
finite class.  The sharper localized linear envelope is provided separately
as `finiteClass_rademacherUpperBound_linear`. -/
theorem finiteClass_rademacherUpperBound
    [Fintype ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → 𝒳)
    {n : ℕ} (hn : 0 < n)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i ω, |F i (X ω)| ≤ b) :
    ∃ ψ : ℝ → ℝ,
      SubRoot ψ ∧
      RademacherUpperBound F norm μ X n ψ ∧
      (∀ r,
        ψ r =
          (b / Real.sqrt (n : ℝ)) *
            Real.sqrt (2 * Real.log (2 * Fintype.card ι))) := by
  let C : ℝ :=
    (b / Real.sqrt (n : ℝ)) *
      Real.sqrt (2 * Real.log (2 * Fintype.card ι))
  refine ⟨fun _ => C, ?_, ?_, ?_⟩
  · exact subRoot_const
      (mul_nonneg
        (div_nonneg hb (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  · intro r _hr
    exact finite_global_rademacher_starHullZeroOut
      F norm μ X hn r b hb hbound
  · intro r
    rfl

/-- Sharp linear finite-class Massart producer for the localized
`RademacherUpperBound` predicate.

The class is normalized by the unit envelope `|F i (X ω)| ≤ 1`.  The
additional radius regularity hypothesis says that every active star-hull ray
at radius `r` has coefficient at most `r`; this is the faithful local
condition that converts the continuum star-hull supremum into the finite
signed `ι` proxy scaled by `r`. -/
theorem finiteClass_rademacherUpperBound_linear
    [Fintype ι] [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → 𝒳)
    {n : ℕ} (hn : 0 < n)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ p : starHullParam ι,
      norm (starHullEval F p) ≤ r → p.1.val ≤ r)
    (hunit : ∀ i ω, |F i (X ω)| ≤ 1) :
    ∃ ψ : ℝ → ℝ,
      SubRoot ψ ∧
      RademacherUpperBound F norm μ X n ψ ∧
      (∀ r,
        ψ r =
          r *
            Real.sqrt ((2 * Real.log (2 * Fintype.card ι)) / (n : ℝ))) := by
  let C : ℝ :=
    Real.sqrt ((2 * Real.log (2 * Fintype.card ι)) / (n : ℝ))
  refine ⟨fun r => r * C, ?_, ?_, ?_⟩
  · exact subRoot_linear (Real.sqrt_nonneg _)
  · intro r hr
    exact finite_linear_rademacher_starHullZeroOut
      F norm μ X hn r hr (hscale r hr) hunit
  · intro r
    rfl

end CausalSmith.Mathlib.Concentration
