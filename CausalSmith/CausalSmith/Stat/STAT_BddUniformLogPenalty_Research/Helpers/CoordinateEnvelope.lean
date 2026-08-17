import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.LawClass
import Causalean.Stat.Nonparametric.LocalPolynomial.CoordinateDerivative

/-!
# Coordinate-partial envelope assembly

This file converts uniform Fréchet-derivative bounds into the scalar
coordinate-partial suprema used by the paper's Euclidean extension class.
-/

open Set
open scoped Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Stat.Nonparametric.LocalPolynomial

/-- Uniform bounds on all required Fréchet derivatives and their Lipschitz
increments imply the exact scalar coordinate-partial extension envelope. -/
-- @node: euclideanCExtEnvelope_of_iteratedFDeriv_bounds
lemma euclideanCExtEnvelope_of_iteratedFDeriv_bounds
    (f g : Score → ℝ) (p : ℕ) (L B D : ℝ) (S : Set Score)
    (hS : S.Nonempty) (hSpair : ∃ x ∈ S, ∃ z ∈ S, x ≠ z)
    (hg : ContDiff ℝ (p + 1 : ℕ) g) (hgf : Set.EqOn g f S)
    (hBD : B + D ≤ L)
    (hbound : ∀ alpha : Fin 2 → ℕ, coordinateMultiOrder alpha ≤ p →
      ∀ x ∈ S, ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha) g x‖ ≤ B)
    (hlip : ∀ alpha : Fin 2 → ℕ, coordinateMultiOrder alpha ≤ p →
      ∀ x ∈ S, ∀ z ∈ S,
      ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha) g x -
        iteratedFDeriv ℝ (coordinateMultiOrder alpha) g z‖ ≤ D * ‖x - z‖) :
    EuclideanCExtEnvelope f p L S := by
  refine ⟨Set.univ, isOpen_univ, subset_univ _, g, hg.contDiffOn,
    hgf, ?_, ?_, ?_⟩
  · refine ⟨B, ?_⟩
    rintro r ⟨alpha, ha, x, hx, rfl⟩
    exact (coordinatePartial_abs_le_iteratedFDeriv_norm g alpha x).trans
      (hbound alpha ha x hx)
  · refine ⟨D, ?_⟩
    rintro r ⟨alpha, ha, x, hx, z, hz, hxz, rfl⟩
    have hnorm : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    apply (div_le_iff₀ hnorm).2
    exact (coordinatePartial_sub_abs_le_iteratedFDeriv_sub_norm
      g alpha x z).trans (hlip alpha ha x hx z hz)
  · have hpartial : sSup (coordinatePartialValues g p S) ≤ B := by
      apply csSup_le
      · rcases hS with ⟨x, hx⟩
        exact ⟨|coordinatePartial g (fun _ ↦ 0) x|, fun _ ↦ 0,
          by simp [coordinateMultiOrder], x, hx, rfl⟩
      · rintro r ⟨alpha, ha, x, hx, rfl⟩
        exact (coordinatePartial_abs_le_iteratedFDeriv_norm g alpha x).trans
          (hbound alpha ha x hx)
    have hlipsup : sSup (coordinatePartialLipschitzValues g p S) ≤ D := by
      apply csSup_le
      · rcases hSpair with ⟨x, hx, z, hz, hxz⟩
        exact ⟨|coordinatePartial g (fun _ ↦ 0) x -
            coordinatePartial g (fun _ ↦ 0) z| / ‖x - z‖,
          fun _ ↦ 0, by simp [coordinateMultiOrder], x, hx, z, hz, hxz, rfl⟩
      · rintro r ⟨alpha, ha, x, hx, z, hz, hxz, rfl⟩
        have hnorm : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
        apply (div_le_iff₀ hnorm).2
        exact (coordinatePartial_sub_abs_le_iteratedFDeriv_sub_norm
          g alpha x z).trans (hlip alpha ha x hx z hz)
    linarith

end CausalSmith.Stat.BddUniformLogPenalty
