import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T5

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace CausalSmith
namespace Stat
namespace PolicyRegretMarginOverlap

open MeasureTheory

-- @node: thm:rate-characterization
theorem rate_characterization_lower (alpha gamma C_m u_0 C_o c_o underline_p : ℝ)
    (Pi : Set (Policy ℝ)) (lawClass : Set (PolicyRegretLaw ℝ))
    (sampleLawForRegret : ∀ n : ℕ, PolicyRegretLaw ℝ → Measure (Fin n → Observation ℝ))
    (hlawClass : ∀ P : PolicyRegretLaw ℝ,
      PolicyRegretLawClass P Pi alpha gamma C_m u_0 C_o c_o underline_p → P ∈ lawClass)
    (hiid : ∀ n : ℕ, ∀ P : PolicyRegretLaw ℝ,
      iidSample n P.observedLaw (sampleLawForRegret n P))
    (hwindow : marginWindow u_0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * Real.rpow (n : ℝ) (-(rStar alpha gamma)) ≤
        minimaxRegret n Pi lawClass (sampleLawForRegret n) := by
  sorry

end PolicyRegretMarginOverlap
end Stat
end CausalSmith
