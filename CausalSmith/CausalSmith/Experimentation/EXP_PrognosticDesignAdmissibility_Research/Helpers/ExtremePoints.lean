/- Extreme-point and rank-one spectrahedron helper namespace for Stage 3. -/
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Basic

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

open Set

noncomputable section

-- @node: not_mem_extremePoints_of_add_sub_mem
/-- A nonzero two-sided feasible perturbation witnesses that a point is not extreme. -/
theorem not_mem_extremePoints_of_add_sub_mem
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} {X D : E} (hD : D ≠ 0)
    (hplus : X + D ∈ K) (hminus : X - D ∈ K) :
    X ∉ K.extremePoints ℝ := by
  intro hX
  have hmid : X ∈ openSegment ℝ (X + D) (X - D) := by
    refine ⟨(2 : ℝ)⁻¹, (2 : ℝ)⁻¹, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have heq : X + D = X := hX.2 hplus hminus hmid
  apply hD
  exact add_left_injective X (by simpa using heq)

-- @node: active_liftedAdversary_perturbation_not_extreme
/-- At an active score boundary, a nonzero centered perturbation with zero trace and
zero score trace rules out extremality whenever both perturbed matrices remain positive
semidefinite. -/
theorem active_liftedAdversary_perturbation_not_extreme
    {n : ℕ} {rho : ℝ} {S : Submodule ℝ (EVec n)}
    {X D : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ liftedAdversary rho S)
    (hactive : rho ^ 2 = (projMatrix S * X).trace)
    (hDsupport : D = projHMat n * D * projHMat n)
    (hDtrace : D.trace = 0)
    (hDscore : (projMatrix S * D).trace = 0)
    (hplusPSD : (X + D).PosSemidef)
    (hminusPSD : (X - D).PosSemidef)
    (hD : D ≠ 0) :
    X ∉ (liftedAdversary rho S).extremePoints ℝ := by
  apply not_mem_extremePoints_of_add_sub_mem hD
  · refine ⟨hplusPSD, ?_, ?_, ?_⟩
    · rw [Matrix.mul_add, Matrix.add_mul, ← hX.2.1, ← hDsupport]
    · simp [hX.2.2.1, hDtrace]
    · rw [Matrix.mul_add, Matrix.trace_add, hDscore, add_zero, ← hactive]
  · refine ⟨hminusPSD, ?_, ?_, ?_⟩
    · rw [Matrix.mul_sub, Matrix.sub_mul, ← hX.2.1, ← hDsupport]
    · simp [hX.2.2.1, hDtrace]
    · rw [Matrix.mul_sub, Matrix.trace_sub, hDscore, sub_zero, ← hactive]

end

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
