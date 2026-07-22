import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace CausalSmith
namespace Stat
namespace PolicyRegretMarginOverlap

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: prop:overlap-envelope
theorem overlap_envelope_admissibility (P : PolicyRegretLaw 𝒳)
    (alpha gamma C_o c_o h beta : ℝ)
    (hoverlap : overlapDecay P alpha gamma C_o c_o)
    (hgamma : 0 < gamma) (hh0 : 0 < h) (hh1 : h < 1) (hbeta : 0 ≤ beta) :
    Real.rpow (Real.rpow h (beta / gamma)) alpha *
        Real.rpow (Real.rpow h beta) (1 / gamma) =
          Real.rpow h (((alpha + 1) * beta) / gamma) ∧
      (Real.rpow (Real.rpow h (beta / gamma)) alpha *
          Real.rpow (Real.rpow h beta) (1 / gamma) ≥ Real.rpow h alpha ↔
            beta ≤ alpha * gamma / (alpha + 1)) ∧
        betaWeak alpha gamma = alpha * gamma / (alpha + 1) := by
  sorry

end PolicyRegretMarginOverlap
end Stat
end CausalSmith
