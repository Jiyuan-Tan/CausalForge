import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Design
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Density and angular cancellation certificates for the hard family -/

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The hypercube certificate includes uniform density and cell-mass control
for every vertex. -/
lemma a1a2Hypercube_density_and_mass
    (p : ℕ) (ν L Δ c A C C0 : ℝ)
    (h : A1A2HypercubeAt p ν L Δ c A C C0) :
    ∃ P : A1A2Law, A1A2Class p ν L P := by
  rcases h with
    ⟨M, w, ρ, x, P, Q, hc, hA, hC, hC0, hp0, hρ, hM, hw, hρeq,
      hx, hcell, hsep, hdisjoint, hclass, _⟩
  exact ⟨P (fun _ => false), hclass _⟩

end CausalSmith.Stat.BddUniformLogPenalty
