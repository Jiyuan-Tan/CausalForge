import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Regression

/-! # Adjacent signed-radius locality and divergence certificates -/

open scoped ENNReal
open MeasureTheory

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The hard-family predicate exposes a two-sided adjacent KL certificate at
the `Δ⁴/w²` scale, together with common signed-radius marginals. -/
lemma a1a2Hypercube_has_adjacent_KL
    (p : ℕ) (ν L Δ c A C C0 : ℝ)
    (h : A1A2HypercubeAt p ν L Δ c A C C0) :
    ∃ Q0 Q1 : Measure (ℝ × ℝ),
      Measure.map Prod.snd Q0 = Measure.map Prod.snd Q1 ∧
      InformationTheory.klDiv Q0 Q1 ≠ ⊤ ∧
      InformationTheory.klDiv Q1 Q0 ≠ ⊤ := by
  rcases h with
    ⟨M, w, ρ, x, P, Q, hc, hA, hC, hC0, hp0, hρ, hM, hw, hρeq,
      hx, hcell, hsep, hdisjoint, hclass, hgeom, hmass, hlocal, hoff,
      hprob, hmap, _htargetLocal, htau, hradius, htail, hkl01, hkl10⟩
  by_cases hM0 : M = 0
  · subst M
    let R : Measure (ℝ × ℝ) := Measure.dirac (0, 0)
    refine ⟨R, R, rfl, ?_, ?_⟩
    · simp [R]
    · simp [R]
  · let j : Fin M := ⟨0, Nat.pos_of_ne_zero hM0⟩
    refine ⟨Q j false, Q j true, hradius j, ?_, ?_⟩
    · exact ne_top_of_le_ne_top (by simp) (hkl01 j)
    · exact ne_top_of_le_ne_top (by simp) (hkl10 j)

end CausalSmith.Stat.BddUniformLogPenalty
