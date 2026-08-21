import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.JmsComparator
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.GaussianRademacherBenchmark

/-!
# Closed local-to-Gaussian upper benchmarks
-/

noncomputable section

open MeasureTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- Along a cumulant-separation schedule that is [strictly positive at every sample
size](hyp:hdeltaPos), [nonincreasing](hyp:hdeltaAnti), and [shrinking to zero](hyp:hdeltaZero),
so that the treatment noise drifts toward Gaussian as the sample grows, [two closed upper
benchmarks are available and can be combined: first, one constant, depending only on the range
and regression bounds and the outcome-noise scale, delivers the parametric mean squared error
bound for every Gaussian--Rademacher mixture whose mixing weight is strictly positive and at
most one, under the usual regularity conditions of the class; second, any published
adaptive-cumulant-estimator procedure carrying its stated generalized-quantile guarantee keeps
that guarantee at each sample size along this schedule, and a risk that respects both the
double-machine-learning benchmark and the adaptive-cumulant benchmark also respects the smaller
of the two](goal).

The theorem is deliberately partial: it supplies upper benchmarks and their combination rule,
not a sharp rate. The matching lower bound over the local-to-Gaussian path is recorded as an
open problem rather than asserted. -/
-- @node: thm:local-to-gaussian-partial-benchmarks
theorem local_to_gaussian_partial_benchmarks
    (deltaSeq : ℕ → ℝ) -- @realizes deltaSeq(carrier Nat to Real)
    (hdeltaPos : ∀ n, 0 < deltaSeq n) -- @realizes deltaSeq(pointwise positive)
    (hdeltaAnti : Antitone deltaSeq) -- @realizes deltaSeq(nonincreasing)
    (hdeltaZero : Filter.Tendsto deltaSeq Filter.atTop (nhds 0))
      -- @realizes deltaSeq(converges to zero)
    (Ctheta Cg Cq psixi : ℝ) :
    (∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg →
        p.Cq = Cq → p.psixi = psixi → p.k = 4 → p.r = 3 →
      ∀ a : ℝ, a ∈ Ioc (0 : ℝ) 1 →
        ∀ m : Model (Xspace := Xspace) p,
          m.P.map (eta p m) = gaussianRademacherLaw a →
          IidSampling p.n m.P (iidLaw m p.n) →
          IndependentTreatmentNoise p m → OutcomeMeanIndependence p m →
          ThetaRange p m → GRange p m → QRange p m →
          XiSubGaussian p m → TreatmentCodeRadiusL1At p m p.n →
          GaussianRademacherPathConclusion p m a C) ∧
    (∀ (published : PublishedAceHandle Xspace) (gamma Cgamma : ℝ),
      JmsAceTheoremFiveFour published gamma Cgamma →
      (0 < Cgamma ∧
      ∀ (p : Parameters), p.gamma = gamma →
      0 < p.eps1n p.n → 0 < p.eps2n p.n →
        ∀ (gcode qcode : ℕ → Xspace → ℝ) (m : Model (Xspace := Xspace) p),
          barG p m p.n = clippedTreatmentCode p gcode p.n →
          barQ p m p.n = clippedOutcomeCode p qcode p.n →
          JmsAceClassAt p p.n m (deltaSeq p.n) →
          jmsEligibleAt p p.n (deltaSeq p.n) →
          generalizedQuantile p p.n m
            (fun data ↦ abs
              (published.estimator p.r p.n gcode qcode data - m.theta0)) ≤
              jmsBound p p.n Cgamma (deltaSeq p.n))) := by
  constructor
  · obtain ⟨C, hC, hpath⟩ :=
      gaussian_rademacher_l1_benchmark (Xspace := Xspace) Ctheta Cg Cq psixi
    refine ⟨C, hC, ?_⟩
    intro p hCtheta hCg hCq hpsixi hk hr a ha m hlaw hiid hind hout htheta hg hq hxi hcode
    exact hpath p hCtheta hCg hCq hpsixi hk a ha m hlaw hiid hind hout htheta hg hq hxi hcode
  · intro published gamma Cgamma hJms
    rcases hJms with ⟨hCgamma, hbound⟩
    refine ⟨hCgamma, ?_⟩
    intro p hgamma heps1 heps2 gcode qcode m hgcode hqcode hclass heligible
    exact hbound p hgamma (deltaSeq p.n) (hdeltaPos p.n) heps1 heps2
      gcode qcode m hgcode hqcode hclass heligible

end CausalSmith.Stat.SaPlmCumulantConverse
