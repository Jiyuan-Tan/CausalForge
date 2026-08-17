import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Density

/-! # Regression, selected-kernel moment, and Gram certificates -/

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Every hard-family member satisfies the Euclidean extension, conditional
moment, variance, local-mass, and Gram-floor clauses through the single class
certificate bundled in `A1A2HypercubeAt`. -/
lemma a1a2Hypercube_member_certified
    (p : ℕ) (ν L Δ c A C C0 : ℝ)
    (h : A1A2HypercubeAt p ν L Δ c A C C0) :
    ∃ P : A1A2Law, A1A2Class p ν L P ∧
      (∀ t x, x ∈ P.support →
        selectedA1A2CondAbsMoment P ν L t x ≤ ENNReal.ofReal L) := by
  rcases h with
    ⟨M, w, ρ, x, P, Q, hc, hA, hC, hC0, hp0, hρ, hM, hw, hρeq,
      hx, hcell, hsep, hdisjoint, hclass, _⟩
  refine ⟨P (fun _ => false), hclass _, ?_⟩
  exact (hclass _).2.2.2.2.2.2.2.2.2.1

end CausalSmith.Stat.BddUniformLogPenalty
