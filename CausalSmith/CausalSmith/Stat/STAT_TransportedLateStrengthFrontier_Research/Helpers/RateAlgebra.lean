/-
# Frontier rate algebra
-/

import Causalean.Stat.Inference.AffineInversion

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

/-- Converts an inverse-root plus inverse-strength bound to the compact
`min(1,t⁻¹/²)` frontier form. -/
lemma inverse_strength_to_frontier
    {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 < t) :
    min 2 (A / Real.sqrt t + B / t) ≤
      max 2 (A + B) * min 1 (t ^ (-1 / 2 : ℝ)) := by
  clear hA
  exact Causalean.Stat.inverseStrength_to_frontier hB ht

end CausalSmith.Stat.TransportedLateStrengthFrontier
