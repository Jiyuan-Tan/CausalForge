/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Kernel
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.GeometryBasic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Hölder interpolation Taylor-term geometry

Internal implementation layer for the multivariate Hölder pointwise-to-local-mass interpolation theorem.
-/

namespace Causalean.Stat.Nonparametric.HolderInterpolation.Internal

open MeasureTheory
open scoped BigOperators Pointwise Manifold ContDiff

/- Almost every point of the closed unit cube lies strictly inside every coordinate
face; its boundary has Lebesgue measure zero. -/
lemma ae_lt_one_on_cube {d : ℕ} :
    ∀ᵐ u ∂(volume.restrict (supBall (0 : Fin d → ℝ) 1)), ∀ i, |u i| < 1 := by
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_supBall 0 1)]
  have hnull : ∀ i : Fin d, ∀ c : ℝ, volume {u : Fin d → ℝ | u i = c} = 0 := by
    intro i c
    have hsub : {u : Fin d → ℝ | u i = c}
        ⊆ Set.univ.pi (fun j => if j = i then ({c} : Set ℝ) else Set.univ) := by
      intro u hu j _
      by_cases hj : j = i
      · subst hj; simp only [if_pos rfl, Set.mem_singleton_iff]; exact hu
      · simp [hj]
    refine measure_mono_null hsub ?_
    rw [MeasureTheory.volume_pi_pi]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp
  have hbadnull : volume {u : Fin d → ℝ | ∃ i, |u i| = 1} = 0 := by
    have hsub : {u : Fin d → ℝ | ∃ i, |u i| = 1}
        ⊆ ⋃ i : Fin d, ({u | u i = 1} ∪ {u | u i = -1}) := by
      intro u hu
      obtain ⟨i, hi⟩ := hu
      rw [Set.mem_iUnion]
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hi with h | h
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr h⟩
    refine measure_mono_null hsub ?_
    refine measure_iUnion_null (fun i => ?_)
    exact measure_union_null (hnull i 1) (hnull i (-1))
  have hae_not : ∀ᵐ u ∂(volume : Measure (Fin d → ℝ)), ¬ ∃ i, |u i| = 1 := by
    rw [MeasureTheory.ae_iff]; simpa using hbadnull
  filter_upwards [hae_not] with u hu hmem i
  have h1 : |u i| ≤ 1 := by simpa using hmem i
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd ⟨i, h⟩ hu

/- Standard-basis decomposition `h • u = ∑ᵢ (h·uᵢ) • eᵢ` in `Fin d → ℝ`. -/
/--A scaled finite-dimensional vector is the sum of its scaled coordinate-basis vectors. -/
lemma smul_eq_sum_single {d : ℕ} (h : ℝ) (u : Fin d → ℝ) :
    (h • u : Fin d → ℝ) = ∑ i : Fin d, (h * u i) • (Pi.single i 1 : Fin d → ℝ) := by
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ a (fun i => h * u i)]
  simp

/-- **Kernel kills the diagonal Taylor term (Milestone 2, step 4).** For `1 ≤ j ≤ m`,
integrating the diagonal iterated derivative `iteratedFDeriv ℝ j g x0 (fun _ => h•u)`
against the kernel over the cube gives `0`: expand the diagonal multilinear map into
monomials and apply the moment cancellation `prodKernel_monomial_p_cube`. -/
/-- Integrating any positive-degree diagonal Taylor term against a sufficiently
moment-cancelling product kernel over the unit cube gives zero. -/
lemma integral_diagonal_taylor_term_cube {d : ℕ} {k : ℝ → ℝ} {m : ℕ}
    (hk_cont : Continuous k)
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ m → (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (g : (Fin d → ℝ) → ℝ) (x0 : Fin d → ℝ) (h : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    ∫ u in supBall (0 : Fin d → ℝ) 1,
        prodKernel k d u * iteratedFDeriv ℝ j g x0 (fun _ => h • u) = 0 := by
  classical
  set F := iteratedFDeriv ℝ j g x0 with hFdef
  have hKcont : Continuous (prodKernel k d) := by
    unfold prodKernel
    exact continuous_finset_prod _ (fun i _ => hk_cont.comp (continuous_apply i))
  -- pointwise monomial expansion of `K(u) · F(fun _ => h•u)`.
  have hpt : ∀ u : Fin d → ℝ, prodKernel k d u * F (fun _ => h • u)
      = ∑ p : Fin j → Fin d, (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
          * ((∏ l, u (p l)) * prodKernel k d u) := by
    intro u
    have h1 : F (fun _ : Fin j => h • u)
        = ∑ p : Fin j → Fin d,
            (∏ l, (h * u (p l))) * F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) := by
      have hexp : (fun _ : Fin j => h • u)
          = (fun _ : Fin j => ∑ i : Fin d, (h * u i) • (Pi.single i 1 : Fin d → ℝ)) := by
        funext l; exact smul_eq_sum_single h u
      rw [hexp, ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [ContinuousMultilinearMap.map_smul_univ]
      simp only [smul_eq_mul]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  calc ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * F (fun _ => h • u)
      = ∫ u in supBall (0 : Fin d → ℝ) 1, ∑ p : Fin j → Fin d,
          (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
            * ((∏ l, u (p l)) * prodKernel k d u) := by simp_rw [hpt]
    _ = ∑ p : Fin j → Fin d, ∫ u in supBall (0 : Fin d → ℝ) 1,
          (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
            * ((∏ l, u (p l)) * prodKernel k d u) := by
        refine MeasureTheory.integral_finset_sum _ (fun p _ => ?_)
        have hc : Continuous (fun u : Fin d → ℝ =>
            (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
              * ((∏ l, u (p l)) * prodKernel k d u)) :=
          continuous_const.mul
            ((continuous_finset_prod _ (fun l _ => continuous_apply (p l))).mul hKcont)
        exact hc.continuousOn.integrableOn_compact (isCompact_supBall 0 1)
    _ = 0 := by
        refine Finset.sum_eq_zero (fun p _ => ?_)
        rw [MeasureTheory.integral_const_mul,
          prodKernel_monomial_p_cube hk_supp hk_mom p hj1 hjm, mul_zero]

/-- **Line chain rule.** The `i`-th 1-D iterated derivative of the line
`s ↦ g (x0 + s • y)` equals the `i`-th iterated Fréchet derivative of `g` at
`x0 + t • y` evaluated on the constant diagonal `fun _ => y` (needs GLOBAL
`ContDiff ℝ i g`). -/

end Causalean.Stat.Nonparametric.HolderInterpolation.Internal
