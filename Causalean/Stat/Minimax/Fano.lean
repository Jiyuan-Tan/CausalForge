/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Multiple-hypothesis (M-ary) minimax lower bound — the Fano / Le Cam–Birgé tier

The two-point method (`Causalean/Stat/Minimax/LeCam.lean`) reduces estimation to a
*binary* test.  When a single pair of hypotheses cannot be packed far enough apart
to certify a rate, one uses **many** hypotheses `{P i}ᵢ` whose parameter values are
*pairwise* `2s`-separated.  An estimator induces the disjoint acceptance regions

  `A i = {ω | dist (est ω) (θ i) < s}`   (disjoint by the `2s`-separation),

and the total probability of *correct* recovery is controlled by total variation:

  `∑ᵢ Pᵢ(A i) ≤ 1 + ∑ᵢ tvDist (P i₀) (P i)`,

for any reference index `i₀`.  Hence the **average** (and therefore worst-case) error
probability over the `N = card ι` hypotheses obeys

  `1 − (1 + ∑ᵢ tvDist (P i₀) (P i)) / N ≤ (1/N) ∑ᵢ Pᵢ(error i)`.

This is the total-variation / testing form of Fano's lemma (cf. Tsybakov §2.6, the
Le Cam–Birgé bound).  It is proven **unconditionally** from the elementary testing
inequality `measureReal_sub_le_tvDist`, with no entropy or mutual-information
machinery — the divergence input enters only through `tvDist`, which the companion
files bound by KL (`Pinsker.lean`) or χ² (`ChiSquared.lean`).

## Main results

* `acceptanceRegion_pairwiseDisjoint` — the acceptance regions of a `2s`-separated
  family are pairwise disjoint.
* `sum_correct_le` — `∑ᵢ Pᵢ(A i) ≤ 1 + ∑ᵢ tvDist (P i₀) (P i)` (the heart of Fano).
* `fano_average_error` — the average-error minimax lower bound.
* `fano_exists_error` — uniform-`β` corollary: under `tvDist (P i₀) (P i) ≤ β`, some
  hypothesis has error probability `≥ 1 − 1/N − β`.

We deliberately use a *reference hypothesis* `i₀` (rather than the centroid mixture)
so this file does not depend on `Stat/Minimax/Mixture.lean`; the symmetric
mixture-centroid refinement `(1/N) ∑ᵢ tvDist (P i) Q̄` is a strict sharpening that
can be layered on top.
-/

import Causalean.Stat.Minimax.LeCam

/-! # Fano-Type Multiple-Hypothesis Bound

This file proves a total-variation form of the multiple-hypothesis minimax lower
bound. It converts pairwise-separated parameter values and a common reference
measure into an average error lower bound for any estimator. -/

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]

/-- The acceptance region of an estimator for hypothesis value `θ`:
the points it places strictly within `s` of `θ`. -/
def acceptanceRegion (est : Ω → Θ) (θ : Θ) (s : ℝ) : Set Ω :=
  {ω | dist (est ω) θ < s}

/-- A measurable estimator has a measurable acceptance region around any target. -/
theorem measurableSet_acceptanceRegion {est : Ω → Θ} (hest : Measurable est)
    (θ : Θ) (s : ℝ) : MeasurableSet (acceptanceRegion est θ s) := by
  have h : acceptanceRegion est θ s = {ω | s ≤ dist (est ω) θ}ᶜ := by
    ext ω; simp [acceptanceRegion, not_le]
  rw [h]
  exact (measurableSet_error hest θ s).compl

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] in
/-- The acceptance region is the complement of the error region. -/
theorem acceptanceRegion_compl (est : Ω → Θ) (θ : Θ) (s : ℝ) :
    (acceptanceRegion est θ s)ᶜ = {ω | s ≤ dist (est ω) θ} := by
  ext ω; simp [acceptanceRegion, not_lt]

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] in
/-- **Disjointness of acceptance regions.** If two target values are `2s`-separated,
their acceptance regions are disjoint: a point within `s` of both would force the
targets within `2s` of each other. -/
theorem acceptanceRegion_disjoint {est : Ω → Θ} {θ₀ θ₁ : Θ} {s : ℝ}
    (hsep : 2 * s ≤ dist θ₀ θ₁) :
    Disjoint (acceptanceRegion est θ₀ s) (acceptanceRegion est θ₁ s) := by
  rw [Set.disjoint_left]
  intro ω h0 h1
  have h0' : dist (est ω) θ₀ < s := h0
  have h1' : dist (est ω) θ₁ < s := h1
  have htri : dist θ₀ θ₁ ≤ dist (est ω) θ₀ + dist (est ω) θ₁ := by
    simpa [dist_comm] using dist_triangle θ₀ (est ω) θ₁
  linarith

variable {ι : Type*}

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] in
/-- **Pairwise disjointness** of the acceptance regions of a `2s`-separated family. -/
theorem acceptanceRegion_pairwiseDisjoint {est : Ω → Θ} {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) :
    Pairwise (Function.onFun Disjoint (fun i => acceptanceRegion est (θ i) s)) :=
  fun i k hik => acceptanceRegion_disjoint (hsep i k hik)

variable [Fintype ι] (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]

/-- A reference hypothesis assigns total mass `≤ 1` across the disjoint acceptance
regions, since their union has measure `≤ 1`. -/
theorem sum_refReal_acceptance_le {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ}
    {s : ℝ} (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) :
    ∑ i, (P i₀).real (acceptanceRegion est (θ i) s) ≤ 1 := by
  have hmeas : ∀ i, MeasurableSet (acceptanceRegion est (θ i) s) := fun i =>
    measurableSet_acceptanceRegion hest (θ i) s
  have hdisj : Pairwise
      (Function.onFun Disjoint (fun i => acceptanceRegion est (θ i) s)) :=
    acceptanceRegion_pairwiseDisjoint (est := est) (θ := θ) (s := s) hsep
  have hunion : (P i₀) (⋃ i, acceptanceRegion est (θ i) s)
      = ∑ i, (P i₀) (acceptanceRegion est (θ i) s) := by
    rw [measure_iUnion hdisj hmeas, tsum_fintype]
  have hle : (P i₀) (⋃ i, acceptanceRegion est (θ i) s) ≤ 1 := by
    calc (P i₀) (⋃ i, acceptanceRegion est (θ i) s)
        ≤ (P i₀) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hfin : ∀ i, (P i₀) (acceptanceRegion est (θ i) s) ≠ ⊤ := fun i =>
    measure_ne_top _ _
  have hsumeq : ∑ i, (P i₀).real (acceptanceRegion est (θ i) s)
      = ((P i₀) (⋃ i, acceptanceRegion est (θ i) s)).toReal := by
    rw [hunion, ENNReal.toReal_sum (fun i _ => hfin i)]; rfl
  rw [hsumeq]
  calc ((P i₀) (⋃ i, acceptanceRegion est (θ i) s)).toReal
      ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hle
    _ = 1 := ENNReal.toReal_one

/-- **Heart of Fano.** The total probability of correct recovery, summed over the
family, is at most `1 + ∑ᵢ tvDist (P i₀) (P i)`: comparing each `Pᵢ(A i)` to the
reference `P i₀(A i)` costs one `tvDist`, and the reference masses sum to `≤ 1`. -/
theorem sum_correct_le {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) :
    ∑ i, (P i).real (acceptanceRegion est (θ i) s)
      ≤ 1 + ∑ i, tvDist (P i₀) (P i) := by
  have hterm : ∀ i, (P i).real (acceptanceRegion est (θ i) s)
      ≤ (P i₀).real (acceptanceRegion est (θ i) s) + tvDist (P i₀) (P i) := by
    intro i
    have hmeas : MeasurableSet (acceptanceRegion est (θ i) s) :=
      measurableSet_acceptanceRegion hest (θ i) s
    have h := measureReal_sub_le_tvDist (μ := P i₀) (ν := P i) hmeas
    linarith
  calc ∑ i, (P i).real (acceptanceRegion est (θ i) s)
      ≤ ∑ i, ((P i₀).real (acceptanceRegion est (θ i) s) + tvDist (P i₀) (P i)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, (P i₀).real (acceptanceRegion est (θ i) s))
          + ∑ i, tvDist (P i₀) (P i) := by rw [Finset.sum_add_distrib]
    _ ≤ 1 + ∑ i, tvDist (P i₀) (P i) := by
        have := sum_refReal_acceptance_le P hest hsep i₀
        linarith

/-- **Fano average-error lower bound.** For a family whose parameter values are
pairwise `2s`-separated, the average probability of error over the `N = card ι`
hypotheses is at least `1 − (1 + ∑ᵢ tvDist (P i₀) (P i)) / N`. -/
theorem fano_average_error {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) :
    1 - (1 + ∑ i, tvDist (P i₀) (P i)) / (Fintype.card ι)
      ≤ (∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}) / (Fintype.card ι) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN, Nat.cast_pos]
    exact Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have herr : ∀ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}
      = 1 - (P i).real (acceptanceRegion est (θ i) s) := by
    intro i
    rw [← acceptanceRegion_compl est (θ i) s,
      measureReal_compl (measurableSet_acceptanceRegion hest (θ i) s)]
    simp [probReal_univ]
  have hsumerr : ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}
      = N - ∑ i, (P i).real (acceptanceRegion est (θ i) s) := by
    simp_rw [herr]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
  have hcorrect := sum_correct_le P hest hsep i₀
  rw [hsumerr, le_div_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ hNne, one_mul]
  linarith [hcorrect]

/-- **Fano existence-of-bad-hypothesis bound (uniform `β`).** If every hypothesis is
within total variation `β` of the reference `P i₀`, then some hypothesis has error
probability at least `1 − 1/N − β`.  This is the directly usable minimax statement:
choosing the number of hypotheses `N` large and the divergence `β` small forces
error. -/
theorem fano_exists_error {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) {β : ℝ}
    (hβ : ∀ i, tvDist (P i₀) (P i) ≤ β) :
    ∃ i, 1 - 1 / (Fintype.card ι) - β
      ≤ (P i).real {ω | s ≤ dist (est ω) (θ i)} := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN, Nat.cast_pos]; exact Fintype.card_pos_iff.mpr ⟨i₀⟩
  have havg := fano_average_error P hest hsep i₀
  rw [← hN] at havg
  have hsumtv : ∑ i, tvDist (P i₀) (P i) ≤ N * β := by
    calc ∑ i, tvDist (P i₀) (P i) ≤ ∑ _i : ι, β := Finset.sum_le_sum (fun i _ => hβ i)
      _ = N * β := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  have hstep : (1 + ∑ i, tvDist (P i₀) (P i)) / N ≤ 1 / N + β := by
    rw [add_div]
    have hle : (∑ i, tvDist (P i₀) (P i)) / N ≤ β := by
      rw [div_le_iff₀ hNpos]; linarith [hsumtv]
    linarith
  have hbound : 1 - 1 / N - β
      ≤ (∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}) / N := by
    refine le_trans ?_ havg
    linarith [hstep]
  by_contra hcon
  push_neg at hcon
  have hstrict : ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)} < N * (1 - 1 / N - β) := by
    calc ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}
        < ∑ _i : ι, (1 - 1 / N - β) :=
          Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨i₀⟩)
            (fun i _ => hcon i)
      _ = N * (1 - 1 / N - β) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  rw [le_div_iff₀ hNpos] at hbound
  nlinarith [hbound, hstrict]

end Causalean.Stat
