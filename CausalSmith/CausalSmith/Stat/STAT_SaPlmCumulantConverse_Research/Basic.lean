import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Distributions.Gaussian.Real
import Causalean.Stat.Quantile.Quantile

/-!
# Spectral annihilation for partially linear models: common setup

This file gives the observed-data law, residuals, exact assumptions, model
classes, and decision-theoretic losses shared by the paper's statements.
The PO substrate is deliberately bypassed: this paper ranges over triangular
classes of observed-data laws rather than one fixed potential-outcome system.
-/

noncomputable section

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- The observation space: a single observed unit is a triple made of a covariate
value drawn from the covariate space, a real-valued treatment, and a real-valued
outcome. Every law considered in the paper is a probability distribution on this
space. -/
abbrev Obs (Xspace : Type*) := Xspace × ℝ × ℝ

/-- Primitive constants and deterministic code-radius sequences. -/
structure Parameters where
  n : ℕ -- @realizes n(natural sample size)
  n_pos : 1 ≤ n -- @realizes n(positive sample size)
  r : ℕ -- @realizes r(fixed ACE order)
  k : ℕ -- @realizes k(cumulant order)
  k_eq : k = r + 1 -- @realizes k(k = r+1)
  r_ge_two : 2 ≤ r -- @realizes r(r at least two)
  s : ℝ≥0∞ -- @realizes s(Lp exponent in [r,infinity])
  r_le_s : (r : ℝ≥0∞) ≤ s -- @realizes s(s at least r)
  gamma : ℝ -- @realizes gamma(probability level)
  gamma_mem : gamma ∈ Ioo (1 / 2 : ℝ) 1 -- @realizes gamma(range (1/2,1))
  Ctheta : ℝ -- @realizes Ctheta(positive target bound)
  Cg : ℝ -- @realizes Cg(positive treatment-regression bound)
  Cq : ℝ -- @realizes Cq(positive outcome bound)
  psieta : ℝ -- @realizes psieta(positive treatment-noise scale)
  psixi : ℝ -- @realizes psixi(positive outcome-noise scale)
  delta : ℝ -- @realizes delta(positive cumulant separation)
  sigma : ℝ -- @realizes sigma(positive Gaussian standard deviation)
  constants_pos :
    0 < Ctheta ∧ -- @realizes Ctheta(strictly positive)
    0 < Cg ∧ -- @realizes Cg(strictly positive)
    0 < Cq ∧ -- @realizes Cq(strictly positive)
    0 < psieta ∧ -- @realizes psieta(strictly positive)
    0 < psixi ∧ -- @realizes psixi(strictly positive)
    0 < delta ∧ -- @realizes delta(strictly positive)
    0 < sigma -- @realizes sigma(strictly positive)
  eps1n : ℕ → ℝ -- @realizes eps1n(nonnegative nonincreasing sequence)
  eps2n : ℕ → ℝ -- @realizes eps2n(nonnegative nonincreasing sequence)
  eps1_nonneg : ∀ n, 1 ≤ n → 0 ≤ eps1n n -- @realizes eps1n(values nonnegative for n>=1)
  eps2_nonneg : ∀ n, 1 ≤ n → 0 ≤ eps2n n -- @realizes eps2n(values nonnegative for n>=1)
  eps1_antitone : ∀ ⦃a b⦄, 1 ≤ a → a ≤ b → eps1n b ≤ eps1n a
    -- @realizes eps1n(nonincreasing on positive indices)
  eps2_antitone : ∀ ⦃a b⦄, 1 ≤ a → a ≤ b → eps2n b ≤ eps2n a
    -- @realizes eps2n(nonincreasing on positive indices)

-- @env: S1
variable {Xspace : Type*} [MeasurableSpace Xspace]
  -- @realizes Xspace(general measurable covariate space)

/-- A law and its deterministic supplied regression codes. -/
structure Model (p : Parameters) where
  P : Measure (Obs Xspace) -- @realizes P(probability law on O)
  probability : IsProbabilityMeasure P -- @realizes P(total mass one)
  theta0 : ℝ -- @realizes theta0(real law functional; range constrained by ThetaRange)
  g0 : Xspace → ℝ -- @realizes g0(carrier Xspace to real; conditional mean pinned by model assumptions)
  q0 : Xspace → ℝ -- @realizes q0(carrier Xspace to real; conditional mean pinned by model assumptions)
  gcode : ℕ → Xspace → ℝ -- @realizes gcode(deterministic sequence Xspace to real)
  qcode : ℕ → Xspace → ℝ -- @realizes qcode(deterministic sequence Xspace to real)
  g0_measurable : Measurable g0 -- @realizes g0(measurable)
  q0_measurable : Measurable q0 -- @realizes q0(measurable)
  gcode_measurable : ∀ n, Measurable (gcode n) -- @realizes gcode(each code measurable)
  qcode_measurable : ∀ n, Measurable (qcode n) -- @realizes qcode(each code measurable)
  treatment_integrable : Integrable (fun o : Obs Xspace ↦ o.2.1) P
    -- @realizes T(integrable domain of the conditional mean)
  outcome_integrable : Integrable (fun o : Obs Xspace ↦ o.2.2) P
    -- @realizes Y(integrable domain of the conditional mean)
  g0_condMean :
    @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap (fun o : Obs Xspace ↦ o.1) inferInstance)
      inferInstance _ _ P (fun o ↦ o.2.1) =ᵐ[P] fun o ↦ g0 o.1
    -- @realizes g0(g0(X) = E[T|X])
  q0_condMean :
    @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap (fun o : Obs Xspace ↦ o.1) inferInstance)
      inferInstance _ _ P (fun o ↦ o.2.2) =ᵐ[P] fun o ↦ q0 o.1
    -- @realizes q0(q0(X) = E[Y|X])

/-- The observed-data law carried by a model is a probability measure, i.e. it
assigns total mass one to the observation space. This is exactly the
normalization recorded among the model's defining conditions, made available
automatically wherever a probability law is required. -/
instance (p : Parameters) (m : Model (Xspace := Xspace) p) : IsProbabilityMeasure m.P :=
  m.probability

/-- Covariate coordinate. -/
def covariate (o : Obs Xspace) : Xspace := o.1 -- @realizes X(random element in Xspace)

/-- Treatment coordinate. -/
def treatment (o : Obs Xspace) : ℝ := o.2.1 -- @realizes T(real treatment)

/-- Outcome coordinate. -/
def outcome (o : Obs Xspace) : ℝ := o.2.2 -- @realizes Y(real outcome)

/-- An observed unit is the coordinate triple `(X,T,Y)`. -/
def observedUnit (o : Obs Xspace) : Obs Xspace := o -- @realizes O(observed triple X,T,Y)

/-- Covariate marginal of the observed law. -/
def covariateLaw (p : Parameters) (m : Model (Xspace := Xspace) p) : Measure Xspace :=
  m.P.map covariate -- @realizes PX(covariate marginal of P)

/-- Current-index clipping of an externally supplied treatment-code sequence. -/
def clippedTreatmentCode (p : Parameters) (gcode : ℕ → Xspace → ℝ)
    (n : ℕ) (x : Xspace) : ℝ :=
  min (max (gcode n x) (-p.Cg)) p.Cg

/-- Clipped treatment code. -/
def barG (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ) (x : Xspace) : ℝ :=
  min (max (m.gcode n x) (-p.Cg)) p.Cg
  -- @realizes bargn(projection of gcode onto [-Cg,Cg])

/-- Current-index clipping of an externally supplied outcome-code sequence. -/
def clippedOutcomeCode (p : Parameters) (qcode : ℕ → Xspace → ℝ)
    (n : ℕ) (x : Xspace) : ℝ :=
  min (max (qcode n x) (-p.Cq)) p.Cq

/-- Clipped outcome code. -/
def barQ (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ) (x : Xspace) : ℝ :=
  min (max (m.qcode n x) (-p.Cq)) p.Cq
  -- @realizes barqn(projection of qcode onto [-Cq,Cq])

/-- Treatment noise `T-g0(X)`. -/
def eta (p : Parameters) (m : Model (Xspace := Xspace) p) (o : Obs Xspace) : ℝ :=
  treatment o - m.g0 (covariate o) -- @realizes eta(T - g0(X))

/-- Outcome noise `Y-q0(X)-theta0*eta`. -/
def xi (p : Parameters) (m : Model (Xspace := Xspace) p) (o : Obs Xspace) : ℝ :=
  outcome o - m.q0 (covariate o) - m.theta0 * eta p m o
  -- @realizes xi(Y - q0(X) - theta0*eta)

/-- Treatment-code residual contamination. -/
def treatmentError (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) (o : Obs Xspace) : ℝ :=
  m.g0 (covariate o) - barG p m n (covariate o) -- @realizes D(g0(X) - bargn(X))

/-- Observable learned treatment residual. -/
def learnedResidual (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) (o : Obs Xspace) : ℝ :=
  treatment o - barG p m n (covariate o) -- @realizes Z(T - bargn(X) = eta + D)

/-- Outcome-side contamination. -/
def outcomeContamination (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) (x : Xspace) : ℝ :=
  m.q0 x - m.theta0 * (m.g0 x - barG p m n x)
  -- @realizes b(q0 - theta0*D)

/-- The cumulant is the real part of the `k`th derivative at zero of the
analytic logarithm of the treatment-noise complex MGF. -/
def kappaEta (p : Parameters) (m : Model (Xspace := Xspace) p) : ℝ :=
  (iteratedDeriv p.k (fun z : ℂ ↦ Complex.log (complexMGF (eta p m) m.P z)) 0).re
  -- @realizes kappaEta(kth derivative at zero of log M)

/-- The fourth cumulant, independent of the parameter field `k`. -/
def fourthCumulant (p : Parameters) (m : Model (Xspace := Xspace) p) : ℝ :=
  (iteratedDeriv 4 (fun z : ℂ ↦ Complex.log (complexMGF (eta p m) m.P z)) 0).re

/-- Exact order-dependent constant in the localization radius. -/
def Ak (k : ℕ) : ℝ :=
  (2 ^ (k + 4) * k.factorial : ℝ) ^ ((k - 2 : ℝ)⁻¹)
  -- @realizes Ak((2^(k+4) k!)^(1/(k-2)))

/-- Explicit transform-zero localization radius. -/
def zeroRadius (p : Parameters) : ℝ :=
  Ak p.k * (p.psieta ^ 2 / p.delta) ^ ((p.k - 2 : ℝ)⁻¹)
  -- @realizes R0(Ak*(psieta^2/delta)^(1/(k-2)))

/-- The radius of the window over which the procedure searches for a zero of the
treatment-noise transform: one unit larger than the explicit localization radius.
The extra unit guarantees that the window strictly contains the zero whose
existence the localization radius certifies, so the search cannot fail by
landing on the boundary. -/
def searchRadius (p : Parameters) : ℝ :=
  zeroRadius p + 1 -- @realizes R1(R0+1)

/-- The deterministic lower and upper inference folds. -/
def fold0 (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.1 < n / 2 -- @realizes I0(indices below floor n/2)

/-- The upper inference fold at sample size n: the collection of unit indices
lying at or beyond the halfway point of the sample, the halfway point being the
integer part of half the sample size. Together with the lower fold it splits the
sample deterministically into two halves for cross-fitting. -/
def fold1 (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ n / 2 ≤ i.1 -- @realizes I1(indices from floor n/2 onward)

-- @env: S2
/-- Independent and identically distributed sampling: the joint law of the n
observed units is the n-fold product of the single-unit observed-data law, so
the units are drawn independently, each from that same law. -/
-- @node: ass:iid-sampling
def IidSampling (n : ℕ) (P : Measure (Obs Xspace))
    (mu : Measure (Fin n → Obs Xspace)) : Prop :=
  mu = Measure.pi (fun _ : Fin n ↦ P)
  -- @realizes i(index in Fin n, representing paper indices 1,...,n)

/-- The treatment noise, that is the treatment minus its conditional mean given
the covariates, is statistically independent of the covariates under the
observed-data law.

This is strictly stronger than the usual conditional-mean-zero restriction: it
makes the treatment equation a genuine location shift, so the entire shape of
the noise distribution — and in particular its higher cumulants — is the same at
every covariate value. That homogeneity is what allows a single population
cumulant to be identified from the pooled residuals. -/
-- @node: ass:independent-treatment-noise
def IndependentTreatmentNoise (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ProbabilityTheory.IndepFun (eta p m) covariate m.P

/-- The sigma-algebra generated by `(X,T)`. -/
def xTSigma : MeasurableSpace (Obs Xspace) :=
  MeasurableSpace.comap (fun o : Obs Xspace ↦ (covariate o, treatment o)) inferInstance

/-- The outcome noise — the outcome minus its conditional mean given the
covariates minus the target coefficient times the treatment noise — is integrable
and has conditional mean zero given the covariates and the treatment jointly.

This is the partially linear outcome equation in exact form: the outcome equals
its covariate regression plus the target coefficient times the treatment noise
plus a disturbance that is mean-independent of the covariate-treatment pair. -/
-- @node: ass:outcome-mean-independence
def OutcomeMeanIndependence (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  Integrable (xi p m) m.P ∧
    @MeasureTheory.condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace)) inferInstance _ _
        m.P (xi p m) =ᵐ[m.P] 0

/-- The target coefficient of the partially linear model is bounded in absolute
value by the target range constant Ctheta, i.e. it lies in the symmetric
interval of that half-width. -/
-- @node: ass:theta-range
def ThetaRange (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  |m.theta0| ≤ p.Ctheta -- @realizes theta0(range [-Ctheta,Ctheta])

/-- The treatment regression function — the conditional mean of the treatment
given the covariates — is bounded in absolute value by the treatment-regression
range constant Cg at almost every covariate value under the covariate
marginal. -/
-- @node: ass:g-range
def GRange (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ∀ᵐ x ∂covariateLaw p m, |m.g0 x| ≤ p.Cg -- @realizes g0(essential range bounded by Cg)

/-- The outcome regression function — the conditional mean of the outcome given
the covariates — is bounded in absolute value by the outcome range constant Cq at
almost every covariate value under the covariate marginal. -/
-- @node: ass:q-range
def QRange (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ∀ᵐ x ∂covariateLaw p m, |m.q0 x| ≤ p.Cq -- @realizes q0(essential range bounded by Cq)

/-- The outcome variable itself is bounded in absolute value by the outcome
range constant Cq almost surely under the observed-data law.

This is a strengthening of the bound on the outcome regression function: it
constrains the realized outcome, not merely its covariate-conditional mean, and
is imposed only in the Gaussian comparison class. -/
-- @node: ass:bounded-gaussian-outcome
def BoundedGaussianOutcome (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ∀ᵐ o ∂m.P, |outcome o| ≤ p.Cq

/-- The treatment noise is sub-Gaussian at the treatment-noise scale psieta:
the exponential of its squared value divided by the squared scale is integrable
and has expectation at most two.

This is the Luxemburg normalization of the squared-exponential Orlicz norm, so
the condition says exactly that the treatment noise has sub-Gaussian norm no
larger than psieta; it delivers the tail and moment control the cumulant
argument needs. -/
-- @node: ass:eta-subgaussian
def EtaSubGaussian (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  Integrable (fun o ↦ Real.exp ((eta p m o) ^ 2 / p.psieta ^ 2)) m.P ∧
    ∫ o, Real.exp ((eta p m o) ^ 2 / p.psieta ^ 2) ∂m.P ≤ 2
  -- @realizes psieta(exact Luxemburg psi2 expectation at scale psieta)

/-- The outcome noise is conditionally sub-Gaussian given the covariates at the
outcome-noise scale psixi: the exponential of its squared value divided by the
squared scale is integrable, and its conditional expectation given the
covariates is at most two at almost every covariate value.

Requiring the Luxemburg bound conditionally rather than only on average rules
out covariate regions where the disturbance is heavy-tailed, which is what the
conditional moment bounds in the risk analysis rely on. -/
-- @node: ass:xi-subgaussian
def XiSubGaussian (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  Integrable (fun w ↦ Real.exp ((xi p m w) ^ 2 / p.psixi ^ 2)) m.P ∧
    ∀ᵐ o ∂m.P,
      (@MeasureTheory.condExp (Obs Xspace) ℝ
        (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
        (fun w ↦ Real.exp ((xi p m w) ^ 2 / p.psixi ^ 2))) o ≤ 2
  -- @realizes psixi(conditional Luxemburg psi2 bound given X)

/-- The cumulant of the treatment noise at the order used throughout the paper
is bounded away from zero: its absolute value is at least the separation
constant delta.

Because every cumulant of order three and above vanishes for a Gaussian
variable, this is a quantitative departure-from-normality requirement — it is
the amount of non-Gaussianity in the treatment noise that the identification
argument converts into information about the target coefficient. -/
-- @node: ass:cumulant-separation
def CumulantSeparation (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  |kappaEta p m| ≥ p.delta -- @realizes delta(lower cumulant separation)

/-- At every sample size of one or more, the clipped treatment code approximates
the true treatment regression function to within the first accuracy sequence,
the error being measured in the norm of exponent s under the covariate marginal.

This is the nuisance-accuracy budget on the treatment side: the codes are
supplied from outside the sample, so the requirement is a deterministic rate
condition rather than an estimation guarantee. -/
-- @node: ass:treatment-code-radius
def TreatmentCodeRadiusLs (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    eLpNorm (fun x ↦ barG p m n x - m.g0 x) p.s (covariateLaw p m) ≤
      ENNReal.ofReal (p.eps1n n)

/-- The treatment-side accuracy budget imposed at a single sample size: the
clipped treatment code approximates the true treatment regression function to
within the first accuracy sequence evaluated at that sample size, measured in
the norm of exponent s under the covariate marginal.

This is the one-index form of the treatment code-radius condition, used when a
model class is indexed by a fixed sample size. -/
def TreatmentCodeRadiusLsAt (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) : Prop :=
  eLpNorm (fun x ↦ barG p m n x - m.g0 x) p.s (covariateLaw p m) ≤
    ENNReal.ofReal (p.eps1n n)

/-- At every sample size of one or more, the clipped outcome code approximates
the true outcome regression function to within the second accuracy sequence, the
error being measured in the norm of exponent s under the covariate marginal.

This is the outcome-side counterpart of the treatment code-radius budget. -/
-- @node: ass:outcome-code-radius
def OutcomeCodeRadiusLs (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    eLpNorm (fun x ↦ barQ p m n x - m.q0 x) p.s (covariateLaw p m) ≤
      ENNReal.ofReal (p.eps2n n)

/-- The outcome-side accuracy budget imposed at a single sample size: the
clipped outcome code approximates the true outcome regression function to within
the second accuracy sequence evaluated at that sample size, measured in the norm
of exponent s under the covariate marginal.

This is the one-index form of the outcome code-radius condition. -/
def OutcomeCodeRadiusLsAt (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) : Prop :=
  eLpNorm (fun x ↦ barQ p m n x - m.q0 x) p.s (covariateLaw p m) ≤
    ENNReal.ofReal (p.eps2n n)

/-- At every sample size of one or more, the clipped treatment code approximates
the true treatment regression function to within the first accuracy sequence,
with the error measured in the norm of exponent r — the fixed order of the
cumulant analysis — under the covariate marginal.

This is the accuracy budget in the form used by the published comparator, whose
nuisance rates are stated at exponent r rather than at the exponent s used by
the paper's own classes. -/
-- @node: ass:jms-treatment-code-radius
def TreatmentCodeRadiusLr (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    eLpNorm (fun x ↦ barG p m n x - m.g0 x) (p.r : ℝ≥0∞) (covariateLaw p m) ≤
      ENNReal.ofReal (p.eps1n n)

/-- The comparator's treatment-side accuracy budget imposed at a single sample
size: the clipped treatment code approximates the true treatment regression
function to within the first accuracy sequence evaluated at that sample size,
measured in the norm of exponent r under the covariate marginal. -/
def TreatmentCodeRadiusLrAt (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) : Prop :=
  eLpNorm (fun x ↦ barG p m n x - m.g0 x) (p.r : ℝ≥0∞) (covariateLaw p m) ≤
    ENNReal.ofReal (p.eps1n n)

/-- At every sample size of one or more, the clipped outcome code approximates
the true outcome regression function to within the second accuracy sequence,
with the error measured in the norm of exponent r under the covariate marginal.

This is the outcome-side accuracy budget in the form used by the published
comparator. -/
-- @node: ass:jms-outcome-code-radius
def OutcomeCodeRadiusLr (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    eLpNorm (fun x ↦ barQ p m n x - m.q0 x) (p.r : ℝ≥0∞) (covariateLaw p m) ≤
      ENNReal.ofReal (p.eps2n n)

/-- The comparator's outcome-side accuracy budget imposed at a single sample
size: the clipped outcome code approximates the true outcome regression function
to within the second accuracy sequence evaluated at that sample size, measured
in the norm of exponent r under the covariate marginal. -/
def OutcomeCodeRadiusLrAt (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) : Prop :=
  eLpNorm (fun x ↦ barQ p m n x - m.q0 x) (p.r : ℝ≥0∞) (covariateLaw p m) ≤
    ENNReal.ofReal (p.eps2n n)

/-- The treatment noise is exactly centered Gaussian with standard deviation
sigma, i.e. its distribution under the observed-data law is the normal law with
mean zero and variance the square of sigma.

This is the null case of the paper's comparison: every cumulant of order three
and above vanishes, so the non-Gaussian signal the estimator exploits is
entirely absent. -/
-- @node: ass:gaussian-treatment-noise
def GaussianTreatmentNoise (p : Parameters) (m : Model (Xspace := Xspace) p) : Prop :=
  m.P.map (eta p m) = ProbabilityTheory.gaussianReal 0 ⟨p.sigma ^ 2, sq_nonneg p.sigma⟩
  -- @realizes sigma(positive standard deviation; variance sigma squared)

/-- At every sample size of one or more, the absolute deviation between the
clipped treatment code and the true treatment regression function is integrable
under the covariate marginal, and its mean is at most the first accuracy
sequence evaluated at that sample size.

This is the weakest of the treatment-side accuracy budgets — mean absolute
error rather than a higher-order norm — and is the one under which the paper's
broad non-Gaussian class is stated. -/
-- @node: ass:l1-treatment-code-radius
def TreatmentCodeRadiusL1 (p : Parameters) (m : Model (Xspace := Xspace) p)
    : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Integrable (fun x ↦ |barG p m n x - m.g0 x|) (covariateLaw p m) ∧
      ∫ x, |barG p m n x - m.g0 x| ∂covariateLaw p m ≤ p.eps1n n

/-- The mean-absolute-error accuracy budget imposed at a single sample size: the
deviation between the clipped treatment code and the true treatment regression
function is integrable under the covariate marginal, with mean at most the first
accuracy sequence evaluated at that sample size. -/
def TreatmentCodeRadiusL1At (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) : Prop :=
  Integrable (fun x ↦ |barG p m n x - m.g0 x|) (covariateLaw p m) ∧
    ∫ x, |barG p m n x - m.g0 x| ∂covariateLaw p m ≤ p.eps1n n

/-- The broad non-Gaussian model class at a given sample size: partially linear
laws whose treatment noise is independent of the covariates, whose outcome noise
is mean-independent of the covariate-treatment pair, whose target coefficient
and whose two regression functions all obey their range bounds, whose treatment
noise is sub-Gaussian and whose outcome noise is conditionally sub-Gaussian at
the stated scales, whose treatment-noise cumulant is separated from zero, and
whose treatment code attains the first accuracy sequence in mean absolute error
at that sample size.

This is the class over which the paper's positive result is stated. Only the
treatment code is subject to an accuracy budget, and only in the weak mean-
absolute sense; imposing no outcome-code budget is what makes the class broad
relative to the published comparator. -/
-- @node: def:non-gaussian-class
structure NonGaussianClass (p : Parameters) (n : ℕ)
    (m : Model (Xspace := Xspace) p) : Prop where
  n_pos : 1 ≤ n -- @realizes n(positive class index)
  independentTreatmentNoise : IndependentTreatmentNoise p m
  outcomeMeanIndependence : OutcomeMeanIndependence p m
  thetaRange : ThetaRange p m
  gRange : GRange p m
  qRange : QRange p m
  etaSubGaussian : EtaSubGaussian p m
  xiSubGaussian : XiSubGaussian p m
  cumulantSeparation : CumulantSeparation p m
  treatmentCodeRadiusL1 : TreatmentCodeRadiusL1At p m n
  -- @realizes PNG(broad direct-L1 non-Gaussian spectral class)

/-- The Gaussian model class at a given sample size: partially linear laws whose
treatment noise is independent of the covariates and exactly centered Gaussian
with standard deviation sigma, whose outcome noise is mean-independent of the
covariate-treatment pair, whose target coefficient and treatment regression
function obey their range bounds, whose outcome is bounded almost surely, and
whose treatment and outcome codes both attain their accuracy sequences in the
norm of exponent s at that sample size.

This is the class against which the paper's converse is proved: the treatment
noise carries no higher-cumulant signal, so no estimator can exploit
non-Gaussianity, and both nuisance codes are held to the stronger accuracy
budget so that the converse cannot be blamed on weak nuisance control. -/
-- @node: def:gaussian-class
structure GaussianClass (p : Parameters) (n : ℕ)
    (m : Model (Xspace := Xspace) p) : Prop where
  n_pos : 1 ≤ n -- @realizes n(positive class index)
  independentTreatmentNoise : IndependentTreatmentNoise p m
  outcomeMeanIndependence : OutcomeMeanIndependence p m
  thetaRange : ThetaRange p m
  gRange : GRange p m
  boundedGaussianOutcome : BoundedGaussianOutcome p m
  gaussianTreatmentNoise : GaussianTreatmentNoise p m
  treatmentCodeRadius : TreatmentCodeRadiusLsAt p m n
  outcomeCodeRadius : OutcomeCodeRadiusLsAt p m n
  -- @realizes PG(simultaneous bounded-outcome Gaussian class)

/-- The published comparator's model class at a given sample size: partially
linear laws with treatment noise independent of the covariates, outcome noise
mean-independent of the covariate-treatment pair, target coefficient and both
regression functions inside their range bounds, sub-Gaussian treatment noise and
conditionally sub-Gaussian outcome noise, a treatment-noise cumulant separated
from zero, and both the treatment and the outcome code attaining their accuracy
sequences in the norm of exponent r at that sample size.

It differs from the paper's broad non-Gaussian class in the nuisance
requirements alone: the comparator constrains the outcome code as well as the
treatment code, and states both budgets at exponent r instead of in mean
absolute error. -/
-- @node: def:jms-ace-class
structure JmsAceClass (p : Parameters) (n : ℕ)
    (m : Model (Xspace := Xspace) p) : Prop where
  n_pos : 1 ≤ n -- @realizes n(positive class index)
  independentTreatmentNoise : IndependentTreatmentNoise p m
  outcomeMeanIndependence : OutcomeMeanIndependence p m
  thetaRange : ThetaRange p m
  gRange : GRange p m
  qRange : QRange p m
  etaSubGaussian : EtaSubGaussian p m
  xiSubGaussian : XiSubGaussian p m
  cumulantSeparation : CumulantSeparation p m
  treatmentCodeRadiusLr : TreatmentCodeRadiusLrAt p m n
  outcomeCodeRadiusLr : OutcomeCodeRadiusLrAt p m n
  -- @realizes PACE(published ACE comparator class)

/-- The comparison subclass at a given sample size: every law in the broad
non-Gaussian class that additionally has both its treatment code and its outcome
code attaining their accuracy sequences in the norm of exponent s.

Restricting to laws whose nuisance codes meet the stronger budget puts the
paper's result and the published comparator on a common footing, so the two
minimax rates can be compared over the same set of laws. -/
-- @node: def:ace-comparison-subclass
structure AceComparisonSubclass (p : Parameters) (n : ℕ)
    (m : Model (Xspace := Xspace) p) : Prop extends NonGaussianClass p n m where
  treatmentCodeRadius : TreatmentCodeRadiusLsAt p m n
  outcomeCodeRadius : OutcomeCodeRadiusLsAt p m n
  -- @realizes PNGACE(non-Gaussian ACE comparison subclass)

-- @env: S4
/-- An estimator at sample size n is a real-valued function of the entire
sample, that is of the n observed covariate-treatment-outcome triples. No
measurability is imposed here; the risk definitions restrict to measurable
estimators where that is needed. -/
abbrev Estimator (n : ℕ) := (Fin n → Obs Xspace) → ℝ

/-- I.i.d. product law used by all risks. -/
def iidLaw (m : Model (Xspace := Xspace) p) (n : ℕ) : Measure (Fin n → Obs Xspace) :=
  Measure.pi fun _ ↦ m.P

/-- Extended nonnegative mean squared error of an estimator at one law. -/
def mseRisk (m : Model (Xspace := Xspace) p) (n : ℕ)
    (est : Estimator (Xspace := Xspace) n) : ℝ≥0∞ :=
  ∫⁻ data, ENNReal.ofReal ((est data - m.theta0) ^ 2) ∂iidLaw m n

/-- Minimax mean squared error on a supplied set of laws. -/
def minimaxRiskOn (p : Parameters) (n : ℕ)
    (laws : Set (Model (Xspace := Xspace) p)) : ℝ≥0∞ :=
  ⨅ est : {e : Estimator (Xspace := Xspace) n // Measurable e},
    ⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ laws), mseRisk m n est.1

/-- The lower quantile at level one minus the confidence parameter gamma of a
real-valued statistic of the sample, the quantile being taken of the
distribution the statistic induces when the n units are drawn independently from
the given law.

Since gamma lies strictly between one half and one, the level is below one half,
so applied to the absolute estimation error this is a value the error exceeds
with probability at least gamma. Bounding it from below therefore says that the
estimator misses by at least that much with high probability, which is the
high-probability form of the paper's converse. The generalized inverse is used
so that no continuity of the error distribution need be assumed. -/
def generalizedQuantile (p : Parameters) (n : ℕ)
    (m : Model (Xspace := Xspace) p)
    (W : (Fin n → Obs Xspace) → ℝ) : ℝ :=
  Causalean.Stat.quantile (Measure.map W (iidLaw m n)) (1 - p.gamma)
  -- @realizes Qgen(generalized lower quantile at 1-gamma)

/-- Gaussian generalized-quantile minimax loss with fixed supplied codes. -/
def minimaxQuantileRiskGOn (p : Parameters) (n : ℕ)
    (gcode qcode : ℕ → Xspace → ℝ) : ℝ≥0∞ :=
  ⨅ est : {e : Estimator (Xspace := Xspace) n // Measurable e},
    ⨆ m : Model (Xspace := Xspace) p,
      ⨆ (_ : GaussianClass p n m ∧
        barG p m n = clippedTreatmentCode p gcode n ∧
        barQ p m n = clippedOutcomeCode p qcode n),
        ENNReal.ofReal (generalizedQuantile p n m (fun data ↦ |est.1 data - m.theta0|))

/-- The three losses defined together in the paper: non-Gaussian MSE,
Gaussian-intersection MSE, and Gaussian generalized-quantile risk. -/
-- @node: def:minimax-risks
def minimaxRisks (p : Parameters) (n : ℕ)
    (gcode qcode : ℕ → Xspace → ℝ) : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ :=
  (minimaxRiskOn p n
      {m | NonGaussianClass p n m ∧
        barG p m n = clippedTreatmentCode p gcode n ∧
        barQ p m n = clippedOutcomeCode p qcode n},
    minimaxRiskOn p n
      {m | GaussianClass p n m ∧
        barG p m n = clippedTreatmentCode p gcode n ∧
        barQ p m n = clippedOutcomeCode p qcode n},
    minimaxQuantileRiskGOn p n gcode qcode)
  -- @realizes RNG(infimum estimator supremum non-Gaussian MSE)
  -- @realizes RG(Gaussian-intersection minimax MSE)
  -- @realizes MGquant(Gaussian-intersection minimax generalized-quantile error)

/-- First projection of the jointly anchored minimax-loss triple. -/
def minimaxRisk (p : Parameters) (n : ℕ)
    (gcode qcode : ℕ → Xspace → ℝ) : ℝ≥0∞ :=
  (minimaxRisks p n gcode qcode).1

/-- Second projection of the jointly anchored minimax-loss triple. -/
def minimaxRiskG (p : Parameters) (n : ℕ)
    (gcode qcode : ℕ → Xspace → ℝ) : ℝ≥0∞ :=
  (minimaxRisks p n gcode qcode).2.1

/-- Third projection of the jointly anchored minimax-loss triple. -/
def minimaxQuantileRiskG (p : Parameters) (n : ℕ)
    (gcode qcode : ℕ → Xspace → ℝ) : ℝ≥0∞ :=
  (minimaxRisks p n gcode qcode).2.2

end CausalSmith.Stat.SaPlmCumulantConverse
