import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T1

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace CausalSmith
namespace Stat
namespace PolicyRegretMarginOverlap

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: thm:margin-localization
theorem margin_localization (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (alpha C_m u_0 : ℝ)
    (hmargin : marginTail P alpha C_m u_0)
    (hzero : zeroEffectAgreement P Pi)
    (hbounded : boundedOutcome P) :
    ∃ C : ℝ, 0 < C ∧ ∀ pi : Policy 𝒳,
      pi ∈ Pi →
        (P.covariateMeasure (disagreementSet P pi)).toReal ≤
        C * Real.rpow (max (P.lawRegret pi) 0) (alpha / (1 + alpha)) := by
  sorry

end PolicyRegretMarginOverlap
end Stat
end CausalSmith
