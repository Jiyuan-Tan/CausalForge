import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace CausalSmith
namespace Stat
namespace PolicyRegretMarginOverlap

open MeasureTheory

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: oeq:feasible-upper
theorem feasible_upper_rate (d_Pi K : ℕ) (P : PolicyRegretLaw 𝒳)
    (Pi : Set (Policy 𝒳)) (alpha gamma C_m u_0 C_o c_o underline_p a c : ℝ)
    (q0 uBar s_feas t_feas : ℝ) (r_mu r_e : ℕ → ℝ)
    (Pi0 : ℕ → Policy 𝒳) (foldOf : ∀ n : ℕ, Fin n → Fin K)
    (mu0 mu1 e : ∀ n : ℕ, Fin K → 𝒳 → ℝ)
    (lawClass : Set (PolicyRegretLaw 𝒳))
    (sampleLawFor : ∀ n : ℕ, PolicyRegretLaw 𝒳 → Measure (Fin n → Observation 𝒳))
    (hclass : PolicyRegretLawClass P Pi alpha gamma C_m u_0 C_o c_o underline_p)
    (hopt : optimalInClass P Pi)
    (hnuis : ∀ n : ℕ, ∀ k : Fin K,
      crossfitNuisanceRate P (mu0 n k) (mu1 n k) (e n k) n (r_mu n) (r_e n))
    (hboundedNuis : ∀ n : ℕ, ∀ k : Fin K, boundedCrossfitNuisances (mu0 n k) (mu1 n k))
    (hpoly : polynomialNuisanceExponents r_mu r_e)
    (hpolicy : pointwiseMeasurableVCClass Pi d_Pi)
    (hvc : ∀ n : ℕ, vcLocalizedEnvelope P Pi alpha d_Pi n)
    (hoffset : ∀ n : ℕ, vcLocalizedOffsetEnvelope P Pi alpha d_Pi n)
    (hfold : ∀ n : ℕ, fixedCrossfitFoldCount K n)
    (hschedule : feasibleSchedule alpha gamma a c q0 uBar s_feas t_feas)
    (hwindowSchedule :
      (gamma = 0 ∧ q0 ≤ underline_p / 2 ∧ t_feas = 0) ∨
        (gamma ≠ 0 ∧ q0 ≤ c_o * Real.rpow uBar gamma ∧
          ∃ N : ℕ, ∀ n ≥ N,
            feasibleClipSchedule q0 s_feas n ≤
              c_o * Real.rpow (feasibleMarginSchedule uBar t_feas n) gamma)) :
    ∃ C p : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      feasibleUpperRisk n K d_Pi Pi alpha gamma C_m u_0 C_o c_o underline_p
        a c q0 uBar s_feas t_feas r_mu r_e Pi0 (foldOf n)
        (mu0 n) (mu1 n) (e n) lawClass (sampleLawFor n) ≤
        C * Real.rpow (n : ℝ) (-(rFeas alpha gamma a c)) *
          Real.rpow (Real.log ((n : ℝ) + 1)) p := by
  sorry

end PolicyRegretMarginOverlap
end Stat
end CausalSmith
