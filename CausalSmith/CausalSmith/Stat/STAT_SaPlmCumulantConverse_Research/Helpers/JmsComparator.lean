import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Causalean.Stat.Quantile.Quantile

/-!
# Jin--Mackey--Syrgkanis ACE comparator
-/

noncomputable section

open Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- The published estimator is indexed by its order, sample size, and the one
fixed supplied treatment/outcome code pair for that experiment. -/
abbrev AceEstimator :=
  ∀ (_r n : ℕ), (ℕ → Xspace → ℝ) → (ℕ → Xspace → ℝ) →
    Estimator (Xspace := Xspace) n

/-- Citation interface for the single published order-`r` ACE procedure.
The handle is supplied once at the cited boundary and then shared unchanged by
both cited statements and all of their consumers. -/
structure PublishedAceHandle (Xspace : Type*) [MeasurableSpace Xspace] where
  estimator : AceEstimator (Xspace := Xspace)
    -- @realizes thetahatACE(the published order-r ACE estimator)

-- @env: S5
/-- The first exponential-tilt scale of the published eligibility condition:
twice the logarithm of six times the sum of the treatment-regression bound and
the treatment sub-Gaussian scale, divided by the treatment-code accuracy budget
at sample size `n`. -/
def jmsA1 (p : Parameters) (n : ℕ) : ℝ :=
  2 * Real.log (6 * (p.Cg + p.psieta) * (p.eps1n n)⁻¹)
  -- @realizes a1n(2 log(6(Cg+psieta)/eps1n))

/-- The first budget quantity of the published eligibility condition: the
logarithm of the effective sample size — the overlap exponent times `n` — divided
by nine. -/
def jmsB1 (p : Parameters) (n : ℕ) : ℝ :=
  Real.log (p.gamma * n / 9) -- @realizes b1n(log(gamma*n/9))

/-- The second exponential-tilt scale of the published eligibility condition:
four times the sum of the treatment-regression bound and the treatment
sub-Gaussian scale. -/
def jmsA2 (p : Parameters) : ℝ :=
  4 * (p.Cg + p.psieta) -- @realizes a2(4(Cg+psieta))

/-- The second budget quantity of the published eligibility condition: two
hundred times the smaller of one and the treatment-effect bound, times the
cumulant separation, divided by the largest of the treatment-code budget, the
outcome-code budget, and the parametric-rate noise level — the effective sample
size to the power −1/2 times the sum of the outcome sub-Gaussian scale and the
treatment-effect bound times the treatment sub-Gaussian scale.

The separation defaults to the model's own cumulant separation; supplying it
explicitly is what the shrinking-separation benchmark needs. -/
def jmsB2 (p : Parameters) (n : ℕ) (delta : ℝ := p.delta) : ℝ :=
  200 * min 1 p.Ctheta * delta /
    max (p.eps1n n) (max (p.eps2n n)
      ((p.gamma * n) ^ (-1 / 2 : ℝ) * (p.psixi + p.Ctheta * p.psieta)))
  -- @realizes b2n(JMS separation and nuisance quantity)

/-- Condition (21) evaluated at an explicitly supplied separation.  This is
the generalization used only by the shrinking-separation benchmark. -/
def jmsEligibleAt (p : Parameters) (n : ℕ) (delta : ℝ) : Prop :=
  jmsA1 p n ≠ 0 ∧ 0 < jmsB1 p n / jmsA1 p n ∧
  0 < jmsA2 p * jmsB2 p n delta ∧
  jmsA2 p * Real.log (jmsA2 p * jmsB2 p n delta) ≠ 0 ∧
  (p.r : ℝ) ≤ min
    (jmsB1 p n / jmsA1 p n - (jmsA1 p n)⁻¹ * Real.log (jmsB1 p n / jmsA1 p n))
    (jmsB2 p n delta / (jmsA2 p * Real.log (jmsA2 p * jmsB2 p n delta)))

/-- Exact paper condition (21), evaluated at the model separation `p.delta`,
with precisely the nonzero denominators and positive logarithm arguments
needed for the displayed expression to be defined. -/
-- @node: def:jms-eligibility
def jmsEligible (p : Parameters) (n : ℕ) : Prop :=
  jmsEligibleAt p n p.delta
  -- @realizes EJMS(exact theorem 5.4 eligibility predicate)

/-- The published finite-order ACE error bound of Jin, Mackey and Syrgkanis: an
overlap-dependent constant times the factorial of the expansion order, times
sixteen to that order, divided by the cumulant separation, multiplied by the sum
of three terms — the treatment-code budget raised to the expansion order times
the outcome-code budget, the treatment-effect bound times the treatment-code
budget raised to one plus the expansion order, and a nuisance-scale factor times
the effective sample size to the power −1/2.

The nuisance-scale factor is sixty-four times the sum of the treatment-regression
bound and the treatment sub-Gaussian scale raised to the expansion order, times
the squared expansion order times that same sum plus the outcome sub-Gaussian
scale plus the treatment-effect bound times the treatment sub-Gaussian scale. -/
def jmsBound (p : Parameters) (n : ℕ) (Cgamma delta : ℝ) : ℝ :=
  Cgamma * p.r.factorial * 16 ^ p.r * delta⁻¹ *
    ((p.eps1n n) ^ p.r * p.eps2n n + p.Ctheta * (p.eps1n n) ^ (p.r + 1) +
      64 * (p.Cg + p.psieta) ^ p.r *
        (p.r ^ 2 * (p.Cg + p.psieta) + p.psixi + p.Ctheta * p.psieta) *
        (p.gamma * n) ^ (-1 / 2 : ℝ))
  -- @realizes BACE(exact JMS theorem 5.4 bound)

/-- The published ACE class with its cumulant separation evaluated at an
explicit value rather than at `p.delta`. -/
def JmsAceClassAt (p : Parameters) (n : ℕ)
    (m : Model (Xspace := Xspace) p) (delta : ℝ) : Prop :=
  1 ≤ n ∧ IndependentTreatmentNoise p m ∧ OutcomeMeanIndependence p m ∧
  ThetaRange p m ∧ GRange p m ∧ QRange p m ∧ EtaSubGaussian p m ∧
  XiSubGaussian p m ∧ |kappaEta p m| ≥ delta ∧
  TreatmentCodeRadiusLrAt p m n ∧ OutcomeCodeRadiusLrAt p m n

/--
Jikai Jin, Lester Mackey, and Vasilis Syrgkanis (2025), *It is hard to be
normal*, Theorem 5.4, equations (21)--(22), arXiv:2507.02275v3: fixed-separation
generalized-quantile upper bound for the estimator carried by the sealed
published-procedure handle.
-/
-- @node: lem:jms-ace-quantile-upper
def JmsAceQuantileUpper (published : PublishedAceHandle Xspace)
    (gamma Cgamma : ℝ) : Prop :=
  0 < Cgamma ∧ -- @realizes Cgamma(positive constant depending only on gamma)
    ∀ (p : Parameters), p.gamma = gamma →
      0 < p.eps1n p.n → 0 < p.eps2n p.n →
      ∀ (gcode qcode : ℕ → Xspace → ℝ) (m : Model (Xspace := Xspace) p),
        barG p m p.n = clippedTreatmentCode p gcode p.n →
        barQ p m p.n = clippedOutcomeCode p qcode p.n →
        JmsAceClass p p.n m → jmsEligible p p.n →
        generalizedQuantile p p.n m
          (fun data ↦ abs
            (published.estimator p.r p.n gcode qcode data - m.theta0)) ≤
          jmsBound p p.n Cgamma p.delta

/--
Jikai Jin, Lester Mackey, and Vasilis Syrgkanis (2025), *It is hard to be
normal*, Theorem 5.4, equations (21)--(22), arXiv:2507.02275v3: the same bound
for the estimator carried by the same sealed published-procedure handle,
universally specialized to a positive separation constant.
-/
-- @node: lem:jms-ace-theorem-five-four
def JmsAceTheoremFiveFour (published : PublishedAceHandle Xspace)
    (gamma Cgamma : ℝ) : Prop :=
  0 < Cgamma ∧
    ∀ (p : Parameters), p.gamma = gamma →
      ∀ delta : ℝ, 0 < delta →
        0 < p.eps1n p.n → 0 < p.eps2n p.n →
        ∀ (gcode qcode : ℕ → Xspace → ℝ) (m : Model (Xspace := Xspace) p),
          barG p m p.n = clippedTreatmentCode p gcode p.n →
          barQ p m p.n = clippedOutcomeCode p qcode p.n →
          JmsAceClassAt p p.n m delta → jmsEligibleAt p p.n delta →
          generalizedQuantile p p.n m
            (fun data ↦ abs
              (published.estimator p.r p.n gcode qcode data - m.theta0)) ≤
            jmsBound p p.n Cgamma delta

end CausalSmith.Stat.SaPlmCumulantConverse
