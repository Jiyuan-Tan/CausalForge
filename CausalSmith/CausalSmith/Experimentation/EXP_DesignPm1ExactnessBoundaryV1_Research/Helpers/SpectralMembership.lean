/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic

/-! # Membership algebra for block spectral coordinates -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: blockSymMatrix_mem_blockElliptope_iff_reducedTriangle
/-- For `m ≥ 2`, membership of the concrete block-symmetric matrix `X(u,v)` in
`E_m^blk` is equivalent to the three reduced-coordinate PSD inequalities plus
the trace identity `q x + y + z = 2m`. -/
lemma blockSymMatrix_mem_blockElliptope_iff_reducedTriangle
    (m : ℕ) (a b u v : ℝ) (hHom : TwoBlockHomophily m a b) :
    blockSymMatrix m u v ∈ blockElliptope m a b ↔
      InReducedTriangle m (1 - u)
        (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
  have hm2 : 2 ≤ m := hHom.1
  constructor
  · rintro ⟨u', v', hX, hmem⟩
    have hfin0 : 0 < 2 * m := by omega
    have hfin1 : 1 < 2 * m := by omega
    have hfinm : m < 2 * m := by omega
    have hu : u = u' := by
      let i0 : Fin (2 * m) := ⟨0, hfin0⟩
      let j0 : Fin (2 * m) := ⟨1, hfin1⟩
      have hentry := congrFun (congrFun hX i0) j0
      have hne : i0 ≠ j0 := by
        intro h
        have := congrArg Fin.val h
        simp [i0, j0] at this
      have hi : i0.val < m := by simp [i0]; omega
      have hj : j0.val < m := by simp [j0]; omega
      simpa [blockSymMatrix, hne, hi, hj] using hentry
    have hv : v = v' := by
      let i0 : Fin (2 * m) := ⟨0, hfin0⟩
      let k0 : Fin (2 * m) := ⟨m, hfinm⟩
      have hentry := congrFun (congrFun hX i0) k0
      have hne : i0 ≠ k0 := by
        intro h
        have := congrArg Fin.val h
        simp [i0, k0] at this
        omega
      have hi : i0.val < m := by simp [i0]; omega
      have hk : ¬ k0.val < m := by simp [k0]
      simp [blockSymMatrix, hne, hi, hk] at hentry
      exact hentry
    subst u'
    subst v'
    exact ⟨hmem.psd_x, hmem.psd_y, hmem.psd_z, by simp [qParam]; ring⟩
  · intro h
    exact ⟨u, v, rfl, ⟨hHom, h.1, h.2.1, h.2.2.1⟩⟩

end CausalSmith.Experimentation.DesignPm1
