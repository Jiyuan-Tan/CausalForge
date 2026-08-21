import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.KnownZeroAssembly

/-!
# Known transform-zero instrument
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- Take [at least one observation](hyp:hn), a model in [the broad non-Gaussian
class](hyp:hclass), and a complex point at which [the treatment-noise moment generating
function vanishes](hyp:hz) to [a known finite order](hyp:hmult) that is [at least
one](hyp:hell). Build the instrument that raises its argument to the power one below that order
and multiplies by the exponential of the zero times the argument. Then [the instrument is
exactly orthogonal to the treatment noise — its mean is zero however the noise is shifted, and
its conditional mean given the covariates vanishes almost surely; its covariance with the
observable learned residual equals the derivative of that order of the treatment transform at
the zero times the treatment-code-error transform there; and whenever that covariance is
nonzero the treatment coefficient equals the ratio of the outcome-weighted instrument mean to
it](goal).

Knowing one exact transform zero and its multiplicity thus buys a genuine instrument: no
Neyman-orthogonality construction or sample splitting is needed, and the identifying ratio is a
population moment condition. -/
-- @node: thm:known-zero-instrument
theorem known_zero_instrument (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) (hn : 1 ≤ n) (hclass : NonGaussianClass p n m)
    (ell : ℕ) (hell : 1 ≤ ell) (z0 : ℂ)
    (hz : treatmentMGF p m z0 = 0)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) :
    (∀ d : ℝ,
      ∫ o, zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
        ((eta p m o + d : ℝ) : ℂ) ∂m.P = 0) ∧
    (@MeasureTheory.condExp (Obs Xspace) ℂ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
      (fun o ↦ zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
        (learnedResidual p m n o))) =ᵐ[m.P] 0 ∧
    (∫ o, (learnedResidual p m n o : ℂ) *
        zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
          (learnedResidual p m n o) ∂m.P =
      iteratedDeriv ell (treatmentMGF p m) z0 * nuisanceMGF p m n z0) ∧
    ((∫ o, (learnedResidual p m n o : ℂ) *
          zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
            (learnedResidual p m n o) ∂m.P) ≠ 0 →
      (m.theta0 : ℂ) =
        (∫ o, (outcome o : ℂ) *
          zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
            (learnedResidual p m n o) ∂m.P) /
        (∫ o, (learnedResidual p m n o : ℂ) *
          zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
            (learnedResidual p m n o) ∂m.P)) := by
  refine ⟨fun d ↦ zeroInstrument_integral_add_eq_zero
    p m n ell hclass z0 hell hz hmult d,
    zeroInstrument_condExp_learnedResidual_eq_zero
      p m n ell hclass z0 hell hz hmult,
    zeroInstrument_learnedResidual_integral_eq
      p m n ell hclass z0 hell hz hmult, ?_⟩
  intro hne
  rw [outcome_zeroInstrument_integral_eq_theta_mul
    p m n ell hclass z0 hell hz hmult]
  exact (eq_div_iff hne).2 (by ring)

end CausalSmith.Stat.SaPlmCumulantConverse
