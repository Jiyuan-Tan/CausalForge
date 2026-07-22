import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace CausalSmith
namespace Stat
namespace PolicyRegretMarginOverlap

open MeasureTheory

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: thm:welfare-identity
theorem welfareRegret_identity (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (pi : Policy 𝒳) (hbounded : boundedOutcome P) :
    P.lawRegret pi =
      ∫ x, |P.contrast x| * disagreementIndicator P pi x ∂P.covariateMeasure := by
  sorry

end PolicyRegretMarginOverlap
end Stat
end CausalSmith
