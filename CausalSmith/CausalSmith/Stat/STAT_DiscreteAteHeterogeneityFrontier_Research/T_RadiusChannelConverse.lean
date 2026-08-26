/- Radius-channel minimax converse. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.LowerTransfer
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ConcreteExactHandle
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ConcreteRadialHandle
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ConcreteHandleCertificates
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialChannelKernel
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialContractedBinary
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialHardFamily
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialMembership
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialFiniteSampleScale
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialFullCoupling
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialProductDataProcessing
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialRateAlgebra
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RadialTarget
import Causalean.Mathlib.InformationTheory.CommonStatisticBernoulli
import Causalean.Stat.Minimax.MaximalCoupling
import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

private abbrev BinObs := CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

-- @node: radial_risk_of_kernel_transport
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the transport scale satisfies
  the stated condition](hyp:ha) and [the target law is the specified transported law](hyp:hQ) and
  [the target parameter has the stated affine relation](hyp:htheta) and [the source parameter set
  has the stated form](hyp:hsource) and [the target separation has the stated
  scaling](hyp:hscale), [the generic Markov-kernel comparison specializes to the radial source
  family: once the one-coordinate channel law and affine target identity are available, every
  bounded ambient estimator is defeated by a radial source member at the transported scale](goal). -/
lemma radial_risk_of_kernel_transport {n d : ℕ} {epsilon M sigma c L a b : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) (hM : 0 ≤ M)
    (K : ProbabilityTheory.Kernel (BinObs H.radialCap) (Obs d))
    [ProbabilityTheory.IsMarkovKernel K]
    (ha : a ≠ 0)
    (hQ : ∀ P ∈ H.radialSource,
      (H.radialEmbedding P).observedLaw =
        K ∘ₘ CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1)
    (htheta : ∀ P ∈ H.radialSource,
      rawAteFormula (H.radialEmbedding P) =
        a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 + b)
    (hsource : ∀ sourceEst : (Fin n → BinObs H.radialCap) → ℝ,
      Measurable sourceEst → Causalean.Stat.UniformlyBounded sourceEst →
      ∃ P ∈ H.radialSource,
        L ≤ Causalean.Stat.sqRisk
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          sourceEst
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1))
    (hscale : c * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
      a ^ 2 * L) (est : Estimator n d M) :
    ∃ P ∈ H.radialSource,
      c * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
        mse (H.radialEmbedding P) est.1 := by
  let I := {P :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw
        n H.radialCap epsilon // P ∈ H.radialSource}
  have htransport :=
    Causalean.Stat.forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport_pi
      (Iota := I) (n := n)
      (P := fun j => CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw j.1.1)
      (Q := fun j => (H.radialEmbedding j.1).observedLaw)
      K
      (theta := fun j =>
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional j.1.1)
      a b L ha
      (fun j => hQ j.1 j.2)
      (by
        intro sourceEst hmeas hbounded
        obtain ⟨P, hP, hrisk⟩ := hsource sourceEst hmeas hbounded
        exact ⟨⟨P, hP⟩, by
          simpa [CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw] using hrisk⟩)
      est.1 est.2.1
      ⟨M, hM, fun x => (abs_le).2 (est.2.2 x)⟩
  obtain ⟨P, hrisk⟩ := htransport
  refine ⟨P.1, P.2, hscale.trans ?_⟩
  rw [← htheta P.1 P.2] at hrisk
  simpa [Causalean.Stat.sqRisk, productLaw, mse] using hrisk

-- @node: exact_risk_of_affine_transport
/-- If [the transport scale satisfies the stated condition](hyp:ha) and [the affine observation
  map has the stated form](hyp:hphi) and [the target law is the specified transported law](hyp:hQ)
  and [the target parameter has the stated affine relation](hyp:htheta) and [the source parameter
  set has the stated form](hyp:hsource) and [the target separation has the stated
  scaling](hyp:hscale), [the deterministic affine comparison specializes to the exact source
  family carried by a least-favorable handle. This is the exact-family analogue of
  `radial_risk_of_kernel_transport` and retains the witnessing source law, which is needed by
  `RiskTransferCertificate`](goal). -/
lemma exact_risk_of_affine_transport {n d : ℕ} {epsilon M sigma c L a b : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (phi : BinObs H.exactCap → Obs d) (ha : a ≠ 0)
    (hphi : Measurable phi)
    (hQ : ∀ P ∈ H.exactSource,
      (H.exactEmbedding P).observedLaw =
        Measure.map phi
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1))
    (htheta : ∀ P ∈ H.exactSource,
      rawAteFormula (H.exactEmbedding P) =
        a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1 + b)
    (hsource : ∀ sourceEst : (Fin n → BinObs H.exactCap) → ℝ,
      Measurable sourceEst →
      ∃ P ∈ H.exactSource,
        L ≤ Causalean.Stat.sqRisk
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          sourceEst
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1))
    (hscale : c * M ^ 2 *
        (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤ a ^ 2 * L)
    (est : Estimator n d M) :
    ∃ P ∈ H.exactSource,
      c * M ^ 2 *
          (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
        mse (H.exactEmbedding P) est.1 := by
  let I := {P : BinaryExactLaw n H.exactCap epsilon // P ∈ H.exactSource}
  have htransport :=
    Causalean.Stat.forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport_pi
      (Iota := I) (n := n)
      (P := fun j ↦ CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw j.1.1)
      (Q := fun j ↦ (H.exactEmbedding j.1).observedLaw)
      (theta := fun j ↦
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional j.1.1)
      phi a b L ha hphi
      (fun j ↦ hQ j.1 j.2)
      (by
        intro sourceEst hmeas
        obtain ⟨P, hP, hrisk⟩ := hsource sourceEst hmeas
        exact ⟨⟨P, hP⟩, by
          simpa [CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw] using hrisk⟩)
      est.1 est.2.1
  obtain ⟨P, hrisk⟩ := htransport
  refine ⟨P.1, P.2, hscale.trans ?_⟩
  rw [← htheta P.1 P.2] at hrisk
  simpa [Causalean.Stat.sqRisk, productLaw, mse] using hrisk

-- @node: exactRiskTransfer_of_affine_transport
/-- If [the transport scale satisfies the stated condition](hyp:ha) and [the affine observation
  map has the stated form](hyp:hphi) and [the target law is the specified transported law](hyp:hQ)
  and [the target parameter has the stated affine relation](hyp:htheta) and [the source parameter
  set has the stated form](hyp:hsource) and [the target separation has the stated
  scaling](hyp:hscale), [pointwise deterministic affine transport packages directly as the exact
  half of a `RiskTransferCertificate`](goal). -/
lemma exactRiskTransfer_of_affine_transport {n d : ℕ}
    {epsilon M sigma c L a b : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (phi : BinObs H.exactCap → Obs d) (ha : a ≠ 0)
    (hphi : Measurable phi)
    (hQ : ∀ P ∈ H.exactSource,
      (H.exactEmbedding P).observedLaw =
        Measure.map phi
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1))
    (htheta : ∀ P ∈ H.exactSource,
      rawAteFormula (H.exactEmbedding P) =
        a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1 + b)
    (hsource : ∀ sourceEst : (Fin n → BinObs H.exactCap) → ℝ,
      Measurable sourceEst →
      ∃ P ∈ H.exactSource,
        L ≤ Causalean.Stat.sqRisk
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          sourceEst
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1))
    (hscale : c * M ^ 2 *
        (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤ a ^ 2 * L) :
    ∀ est : Estimator n d M,
      ∃ P ∈ H.exactSource,
        c * M ^ 2 *
            (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
          mse (H.exactEmbedding P) est.1 := by
  intro est
  exact exact_risk_of_affine_transport H phi ha hphi hQ htheta hsource hscale est

-- @node: riskTransferCertificate_of_kernel_transport
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the transport scale satisfies
  the stated condition](hyp:ha) and [the target law is the specified transported law](hyp:hQ) and
  [the target parameter has the stated affine relation](hyp:htheta) and [the source parameter set
  has the stated form](hyp:hsource) and [the target separation has the stated scaling](hyp:hscale)
  and [the exact risk-transfer identity holds](hyp:hexact), [a radial Markov-kernel transport and
  the independently transferred exact family together discharge the two halves of
  `RiskTransferCertificate`](goal). -/
lemma riskTransferCertificate_of_kernel_transport {n d : ℕ}
    {epsilon M sigma c L a b : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) (hM : 0 ≤ M)
    (K : Kernel (BinObs H.radialCap) (Obs d)) [IsMarkovKernel K]
    (ha : a ≠ 0)
    (hQ : ∀ P ∈ H.radialSource,
      (H.radialEmbedding P).observedLaw =
        K ∘ₘ CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1)
    (htheta : ∀ P ∈ H.radialSource,
      rawAteFormula (H.radialEmbedding P) =
        a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 + b)
    (hsource : ∀ sourceEst : (Fin n → BinObs H.radialCap) → ℝ,
      Measurable sourceEst → Causalean.Stat.UniformlyBounded sourceEst →
      ∃ P ∈ H.radialSource,
        L ≤ Causalean.Stat.sqRisk
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          sourceEst
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1))
    (hscale : c * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
      a ^ 2 * L)
    (hexact : ∀ est : Estimator n d M,
      ∃ P ∈ H.exactSource,
        c * M ^ 2 *
            (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
          mse (H.exactEmbedding P) est.1) :
    RiskTransferCertificate c H := by
  intro est
  exact ⟨radial_risk_of_kernel_transport H hM K ha hQ htheta hsource hscale est,
    hexact est⟩

-- @node: bernoulliContraction_success_mem
/-- If [the heterogeneity radius is nonnegative](hyp:hsigma), [for a radius parameter in `[0,2]`,
  the Bernoulli contraction probability lies in the advertised interval, including both endpoint
  bits](goal). -/
lemma bernoulliContraction_success_mem {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (b : Bool) :
    1 / 2 + sigma / 2 * ((if b then 1 else 0) - 1 / 2) ∈
      Icc (1 / 2 - sigma / 4) (1 / 2 + sigma / 4) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · constructor <;> linarith
  · constructor <;> linarith

/-- If [the specified least-favorable family is available](hyp:hfamily) and [the heterogeneity
  radius is nonnegative](hyp:hsigma), [the channel formula stored by a least-favorable family
  automatically discharges the theorem's pointwise probability-range certificate](goal). -/
lemma leastFavorableFamily_channel_success_mem {n d : ℕ}
    {epsilon M sigma bRad bExact : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (hfamily : leastFavorableAt n d epsilon M sigma bRad bExact H)
    (hsigma : 0 ≤ sigma) :
    ∀ b, H.channelSuccess b ∈
      Icc (1 / 2 - sigma / 4) (1 / 2 + sigma / 4) := by
  rcases hfamily with
    ⟨_hbRad, _hbExact, hlambda, _hradialCap, _hexactCap,
      _hradialHard, _hexactHard, _hradialCoupling, _hexactCoupling,
      hsuccess, _hscaled⟩
  intro b
  rw [hsuccess b, hlambda]
  exact bernoulliContraction_success_mem hsigma b

-- @node: converseRate_lower_of_base_and_radius
/-- If [the base-rate constant is positive](hyp:hcBase) and [the radius-rate constant is
  positive](hyp:hcRad) and [the base lower bound holds](hyp:hbase) and [the radial source lower
  bound holds](hyp:hradius), [two lower bounds against the same minimax risk combine into the
  displayed three-term converse rate after halving the smaller constant](goal). -/
lemma converseRate_lower_of_base_and_radius {n d : ℕ} {M sigma R cBase cRad : ℝ}
    (hcBase : 0 < cBase) (hcRad : 0 < cRad)
    (hbase : cBase * M ^ 2 *
      (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤ R)
    (hradius : cRad * M ^ 2 * sigma ^ 2 *
      min 1 (polynomialComponent n d) ≤ R) :
    min cBase cRad / 2 * M ^ 2 * converseRate n d sigma ≤ R := by
  let A : ℝ := 1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)
  let B : ℝ := sigma ^ 2 * min 1 (polynomialComponent n d)
  have hpoly : 0 ≤ polynomialComponent n d := by
    unfold polynomialComponent
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hc : 0 ≤ min cBase cRad := le_min hcBase.le hcRad.le
  have hc_base : min cBase cRad ≤ cBase := min_le_left _ _
  have hc_rad : min cBase cRad ≤ cRad := min_le_right _ _
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hbase' : min cBase cRad * M ^ 2 * A ≤ R := by
    calc
      min cBase cRad * M ^ 2 * A ≤ cBase * M ^ 2 * A := by gcongr
      _ ≤ R := by simpa [A] using hbase
  have hradius' : min cBase cRad * M ^ 2 * B ≤ R := by
    calc
      min cBase cRad * M ^ 2 * B ≤ cRad * M ^ 2 * B := by gcongr
      _ = cRad * M ^ 2 * sigma ^ 2 *
          min 1 (polynomialComponent n d) := by dsimp [B]; ring
      _ ≤ R := hradius
  have hsum : min cBase cRad * M ^ 2 * (A + B) ≤ 2 * R := by
    nlinarith
  calc
    min cBase cRad / 2 * M ^ 2 * converseRate n d sigma =
        (min cBase cRad * M ^ 2 * (A + B)) / 2 := by
          unfold converseRate
          dsimp [A, B]
          ring
    _ ≤ (2 * R) / 2 := div_le_div_of_nonneg_right hsum (by norm_num)
    _ = R := by ring

-- @node: minimaxRisk_ge_radius_of_transfer_certificate
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the transported family belongs
  to the target model class](hyp:hmembership) and [the risk-transfer certificate
  holds](hyp:htransfer), [the radial half of a risk-transfer certificate gives a lower bound on
  the ambient minimax risk once every embedded source law has a class witness](goal). -/
lemma minimaxRisk_ge_radius_of_transfer_certificate {n d : ℕ}
    {epsilon M sigma c : ℝ} (H : LeastFavorableHandle n d epsilon M sigma)
    (hM : 0 ≤ M)
    (hmembership : RadialEmbeddingMembership H)
    (htransfer : RiskTransferCertificate c H) :
    c * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
      minimaxRisk n d epsilon M sigma := by
  let est0 : Estimator n d M :=
    ⟨fun _ ↦ 0, measurable_const, fun _ ↦ ⟨by linarith, hM⟩⟩
  letI : Nonempty (Estimator n d M) := ⟨est0⟩
  unfold minimaxRisk
  apply le_ciInf
  intro est
  obtain ⟨P, hP, hrisk⟩ := (htransfer est).1
  obtain ⟨Q, hQ⟩ := hmembership P hP
  unfold worstCaseMSE
  have hbounded : BddAbove (Set.range (fun R : ModelClass d epsilon M sigma ↦
      mse R.law est.1)) := by
    refine ⟨(2 * M) ^ 2, ?_⟩
    rintro _ ⟨R, rfl⟩
    exact test_model_mse_le R est
  have hriskQ : c * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
      mse Q.law est.1 := by simpa [hQ] using hrisk
  exact hriskQ.trans (le_ciSup hbounded Q)

-- @node: converseRate_lower_of_exact_transfer_and_handle
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the base-rate constant is
  positive](hyp:hcBase) and [the radius-rate constant is positive](hyp:hcRad) and [the base lower
  bound holds](hyp:hbase) and [the transported family belongs to the target model
  class](hyp:hmembership) and [the risk-transfer certificate holds](hyp:htransfer), [the proved
  all-alphabet exact transfer and a concrete radial handle assemble the full capped converse rate
  with the minimum of their constants](goal). -/
lemma converseRate_lower_of_exact_transfer_and_handle {n d : ℕ}
    {epsilon M sigma cBase cRad : ℝ}
    (hM : 0 ≤ M) (hcBase : 0 < cBase) (hcRad : 0 < cRad)
    (hbase : cBase * M ^ 2 *
      (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
        minimaxRisk n d epsilon M sigma)
    (H : LeastFavorableHandle n d epsilon M sigma)
    (hmembership : RadialEmbeddingMembership H)
    (htransfer : RiskTransferCertificate cRad H) :
    min cBase cRad / 2 * M ^ 2 * converseRate n d sigma ≤
      minimaxRisk n d epsilon M sigma := by
  exact converseRate_lower_of_base_and_radius hcBase hcRad hbase
    (minimaxRisk_ge_radius_of_transfer_certificate H hM hmembership htransfer)

-- @node: capped_positive_mass_alphabet_bounds
/-- If [the alphabet is nonempty](hyp:hd), [capping a positive ambient alphabet by a cutoff forced
  to be at least one always leaves a nonempty source alphabet and never exceeds the ambient
  one](goal). -/
lemma capped_positive_mass_alphabet_bounds {d cutoff : ℕ} (hd : 0 < d) :
    0 < min d (max 1 cutoff) ∧ min d (max 1 cutoff) ≤ d := by
  constructor
  · exact (Nat.lt_min).2
      ⟨hd, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 cutoff)⟩
  · exact min_le_left _ _

-- @node: radialCap_le_sourceRange
/-- If [the radial cap satisfies its stated bound](hyp:hb) and [the sample size satisfies the
  stated lower bound](hyp:hn) and [the source range is at least one](hyp:hone), [halving the
  source alphabet constant absorbs the `log (e n)` cutoff into the cited `log n` source range once
  `n ≥ 3`; the explicit unit lower bound also absorbs the nonempty-alphabet `max 1` guard](goal). -/
lemma radialCap_le_sourceRange {n d : ℕ} {b : ℝ}
    (hb : 0 < b) (hn : 3 ≤ n) (hone : 1 ≤ b * (n : ℝ) * Real.log n) :
    ((min d (max 1 (Nat.floor ((b / 2) * (n : ℝ) * logEN n))) : ℕ) : ℝ) ≤
      b * (n : ℝ) * Real.log n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog3 : 1 ≤ Real.log (3 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hlog : 1 ≤ Real.log (n : ℝ) :=
    hlog3.trans (Real.log_le_log (by norm_num) hnR)
  have hlogEN : logEN n ≤ 2 * Real.log (n : ℝ) := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
    linarith
  have hx0 : 0 ≤ (b / 2) * (n : ℝ) * logEN n := by
    have : 0 ≤ logEN n := by
      rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
      positivity
    positivity
  have hfloor : (Nat.floor ((b / 2) * (n : ℝ) * logEN n) : ℝ) ≤
      b * (n : ℝ) * Real.log n := by
    calc
      (Nat.floor ((b / 2) * (n : ℝ) * logEN n) : ℝ) ≤
          (b / 2) * (n : ℝ) * logEN n := Nat.floor_le hx0
      _ ≤ (b / 2) * (n : ℝ) * (2 * Real.log n) := by gcongr
      _ = b * (n : ℝ) * Real.log n := by ring
  calc
    ((min d (max 1 (Nat.floor ((b / 2) * (n : ℝ) * logEN n))) : ℕ) : ℝ) ≤
        (max 1 (Nat.floor ((b / 2) * (n : ℝ) * logEN n)) : ℕ) := by
          exact_mod_cast min_le_right d _
    _ = max (1 : ℝ)
        (Nat.floor ((b / 2) * (n : ℝ) * logEN n) : ℝ) := by norm_num
    _ ≤ b * (n : ℝ) * Real.log n := max_le hone hfloor

-- @node: exists_capped_radial_transport_package
/-- If [the overlap constant is positive](hyp:he0) and [the overlap constant is below one
  half](hyp:he1), [the Zeng one-arm constants can be shrunk once so that the paper's capped radial
  alphabet is nonempty, remains in the source theorem's range, and has exactly the transported
  product-radius scale needed in the large-sample branch](goal). -/
lemma exists_capped_radial_transport_package {epsilon : ℝ}
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    ∃ a bRad bCut cRad : ℝ, ∃ N : ℕ,
      0 < a ∧ 0 < bRad ∧ bRad < bCut ∧ 0 < cRad ∧
      ∀ n d : ℕ, 0 < n → 0 < d → N ≤ n →
        let m := min d (max 1 (Nat.floor (bRad * (n : ℝ) * logEN n)))
        0 < m ∧ m ≤ d ∧
        (m : ℝ) ≤ bCut * (n : ℝ) * Real.log n ∧
        (∀ sourceEst : (Fin n → BinObs m) → ℝ,
          Measurable sourceEst → Causalean.Stat.UniformlyBounded sourceEst →
          ∃ P ∈ (Set.univ : Set
              (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw
                n m epsilon)),
            a / 2 * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n m ≤
              Causalean.Stat.sqRisk
                (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
                sourceEst
                (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1)) ∧
        ∀ M sigma : ℝ,
          cRad * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
            (M * sigma / 2) ^ 2 *
              (a / 2 *
                CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n m) := by
  obtain ⟨a, b, N0, ha, hb, hlower⟩ :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.zengOneArmMinimaxLower epsilon
      ⟨he0, he1⟩
  let b0 : ℝ := min b 4
  have hb0 : 0 < b0 := lt_min hb (by norm_num)
  have hb0b : b0 ≤ b := min_le_left _ _
  have hb04 : b0 ≤ 4 := min_le_right _ _
  let N : ℕ := max 3 (max N0 (Nat.ceil (2 / b0)))
  let cRad : ℝ := a * b0 ^ 2 / 128
  refine ⟨a, b0 / 2, b, cRad, N, ha, by positivity, ?_, by
    dsimp [cRad]
    positivity, ?_⟩
  · have : b0 ≤ b := hb0b
    nlinarith
  intro n d hn hd hN
  have hn3 : 3 ≤ n := le_trans (Nat.le_max_left _ _) hN
  have hN0 : N0 ≤ n :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right 3 _)) hN
  have hceilNat : Nat.ceil (2 / b0) ≤ n :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right 3 _)) hN
  have hceil : 2 / b0 ≤ (Nat.ceil (2 / b0) : ℝ) := Nat.le_ceil _
  have hceilReal : (Nat.ceil (2 / b0) : ℝ) ≤ n := by exact_mod_cast hceilNat
  have hnLower : 2 / b0 ≤ (n : ℝ) := hceil.trans hceilReal
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogOne : 1 ≤ Real.log (n : ℝ) := by
    have hlog3 : 1 ≤ Real.log (3 : ℝ) := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.le.trans (by norm_num)
    exact hlog3.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn3))
  have hone : 1 ≤ b0 * (n : ℝ) * Real.log n := by
    have hbn : 1 ≤ b0 * (n : ℝ) := by
      have htwo' : 2 ≤ (n : ℝ) * b0 := (div_le_iff₀ hb0).mp hnLower
      have htwo : 2 ≤ b0 * (n : ℝ) := by nlinarith
      linarith
    nlinarith
  have hx : 1 ≤ (b0 / 2) * (n : ℝ) * logEN n := by
    have hlogEN : 1 ≤ logEN n := by
      rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
      linarith
    have hbn : 1 ≤ (b0 / 2) * (n : ℝ) := by
      calc
        1 = (b0 / 2) * (2 / b0) := by field_simp [hb0.ne']
        _ ≤ (b0 / 2) * (n : ℝ) := mul_le_mul_of_nonneg_left hnLower (by positivity)
    nlinarith
  let m := min d (max 1 (Nat.floor ((b0 / 2) * (n : ℝ) * logEN n)))
  have hm : 0 < m ∧ m ≤ d := capped_positive_mass_alphabet_bounds hd
  have hmrange0 : (m : ℝ) ≤ b0 * (n : ℝ) * Real.log n :=
    radialCap_le_sourceRange hb0 hn3 hone
  have hmrange : (m : ℝ) ≤ b * (n : ℝ) * Real.log n := by
    calc
      (m : ℝ) ≤ b0 * (n : ℝ) * Real.log n := hmrange0
      _ ≤ b * (n : ℝ) * Real.log n := by gcongr
  have hsource := radial_source_risk_of_oneArm_lower hn hm.1 he0 he1 ha
    (hlower n m hm.1 hN0 hmrange)
  refine ⟨hm.1, hm.2, hmrange, hsource, ?_⟩
  intro M sigma
  simpa [m, cRad] using
    (cappedRadial_transportScale (n := n) (d := d) (a := a) (b := b0)
      (M := M) (sigma := sigma) hn3 hd ha.le hb0 hb04 hx)

-- @node: exact_source_risk_of_binaryExact_lower
/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1) and [the
  transport scale satisfies the stated condition](hyp:ha) and [the stated lower bound
  holds](hyp:hlower), [a positive fixed-sample exact-homogeneity minimax lower bound supplies the
  estimator-wise source hardness interface used by deterministic affine transport, after the same
  strict half-constant reduction as in the radial family](goal). -/
lemma exact_source_risk_of_binaryExact_lower {n d : ℕ} {epsilon a : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (ha : 0 < a)
    (hlower : a * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
      binaryExactMinimaxRisk n d epsilon) :
    ∀ sourceEst : (Fin n → BinObs d) → ℝ, Measurable sourceEst →
      ∃ P ∈ (Set.univ : Set (BinaryExactLaw n d epsilon)),
        a / 2 * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
          Causalean.Stat.sqRisk
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            sourceEst
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrate : 0 < 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 := by
    have hone : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
    have hdim : 0 ≤ (d : ℝ) / (n : ℝ) ^ 2 := by positivity
    linarith
  have hstrict : a / 2 * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) <
      binaryExactMinimaxRisk n d epsilon :=
    (by nlinarith : a / 2 * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) <
      a * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2)).trans_le hlower
  intro sourceEst hmeas
  obtain ⟨P, hP⟩ := binaryExactMinimaxRisk_hard_family_of_lt
    hn hd he0 he1 hstrict sourceEst hmeas
  exact ⟨P, Set.mem_univ P, by
    simpa [Causalean.Stat.sqRisk,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse] using hP⟩

-- @node: exactSourceHard_of_source_eq_univ_and_lower
/-- If [the sample is nonempty](hyp:hn) and [the alphabet size satisfies the stated
  condition](hyp:hd) and [the overlap constant is positive](hyp:he0) and [the overlap constant is
  below one half](hyp:he1) and [the transport scale satisfies the stated condition](hyp:ha) and
  [the source parameter set has the stated form](hyp:hsource) and [the stated lower bound
  holds](hyp:hlower), [a handle whose exact source is the full exact binary class inherits the
  hard-family certificate from a positive fixed-sample exact minimax lower bound](goal). -/
lemma exactSourceHard_of_source_eq_univ_and_lower {n d : ℕ}
    {epsilon M sigma a : ℝ} (H : LeastFavorableHandle n d epsilon M sigma)
    (hn : 0 < n) (hd : 0 < H.exactCap)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (ha : 0 < a)
    (hsource : H.exactSource = Set.univ)
    (hlower : a * (1 / (n : ℝ) + (H.exactCap : ℝ) / (n : ℝ) ^ 2) ≤
      binaryExactMinimaxRisk n H.exactCap epsilon) :
    ExactSourceHard H := by
  refine ⟨a / 2, by positivity, ?_⟩
  intro est
  obtain ⟨P, _hP, hrisk⟩ := exact_source_risk_of_binaryExact_lower
    hn hd he0 he1 ha hlower est.1 est.2
  refine ⟨P, ?_, ?_⟩
  · rw [hsource]
    exact Set.mem_univ P
  · simpa [Causalean.Stat.sqRisk,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse] using hrisk

-- @node: exactSourceHard_of_source_eq_univ
/-- If [the sample is nonempty](hyp:hn) and [the alphabet size satisfies the stated
  condition](hyp:hd) and [the overlap constant is positive](hyp:he0) and [the overlap constant is
  below one half](hyp:he1) and [the source parameter set has the stated form](hyp:hsource), [for
  every positive sample size and capped alphabet, the full exact binary source class is a
  genuinely hard family. As in the radial source interface, the constant carried by the structural
  handle may depend on the concrete instance; the uniform constant used by the eventual
  risk-transfer certificate is supplied separately by the cited exact lower bound](goal). -/
lemma exactSourceHard_of_source_eq_univ {n d : ℕ}
    {epsilon M sigma : ℝ} (H : LeastFavorableHandle n d epsilon M sigma)
    (hn : 0 < n) (hd : 0 < H.exactCap)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hsource : H.exactSource = Set.univ) :
    ExactSourceHard H := by
  let r : ℝ := 1 / (n : ℝ) + (H.exactCap : ℝ) / (n : ℝ) ^ 2
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let a : ℝ := 1 / (100 * (n : ℝ) * r)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlower : a * r ≤ binaryExactMinimaxRisk n H.exactCap epsilon := by
    have hparam := binaryExactMinimaxRisk_parametric_lower
      hn hd he0 he1
    have har : a * r = 1 / (100 * (n : ℝ)) := by
      dsimp [a]
      field_simp [hnR.ne', hr.ne']
    rw [har]
    exact hparam
  exact exactSourceHard_of_source_eq_univ_and_lower H hn hd he0 he1 ha
    hsource (by simpa [r] using hlower)

-- @node: exact_source_risk_of_parametric_lower
/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1), [the exact
  source's two-point subexperiment gives the estimator-wise parametric risk interface at every
  positive sample size. The strict half-constant is what permits extraction of an actual hard
  source law from the minimax infimum/supremum](goal). -/
lemma exact_source_risk_of_parametric_lower {n d : ℕ} {epsilon : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon)
    (he1 : epsilon < 1 / 2) :
    ∀ sourceEst : (Fin n → BinObs d) → ℝ, Measurable sourceEst →
      ∃ P : BinaryExactLaw n d epsilon,
        1 / (200 * (n : ℝ)) ≤
          Causalean.Stat.sqRisk
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            sourceEst
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hstrict : 1 / (200 * (n : ℝ)) <
      binaryExactMinimaxRisk n d epsilon := by
    have hparam := binaryExactMinimaxRisk_parametric_lower hn hd he0 he1
    have hdenom : 100 * (n : ℝ) < 200 * (n : ℝ) := by nlinarith
    exact (one_div_lt_one_div_of_lt (by positivity) hdenom).trans_le hparam
  intro sourceEst hmeas
  obtain ⟨P, hP⟩ := binaryExactMinimaxRisk_hard_family_of_lt
    hn hd he0 he1 hstrict sourceEst hmeas
  exact ⟨P, by
    simpa [Causalean.Stat.sqRisk,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse] using hP⟩

-- @node: exists_capped_exact_transport_package
/-- If [the overlap constant is positive](hyp:he0) and [the overlap constant is below one
  half](hyp:he1), [the cited exact lower bound, its capped alphabet, and the finite-sample
  parametric fallback can be normalized to one estimator-wise transport scale valid for every
  positive sample size and ambient alphabet](goal). -/
lemma exists_capped_exact_transport_package {epsilon : ℝ}
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    ∃ bExact cExact : ℝ, ∃ NExact : ℕ,
      0 < bExact ∧ 0 < cExact ∧
      ∀ n d : ℕ, 0 < n → 0 < d →
        let m := min d (max 1 (Nat.floor (bExact * (n : ℝ) ^ 2)))
        0 < m ∧ m ≤ d ∧
        (NExact ≤ n → (m : ℝ) ≤ bExact * (n : ℝ) ^ 2) ∧
        ∃ L : ℝ,
          (∀ sourceEst : (Fin n → BinObs m) → ℝ, Measurable sourceEst →
            ∃ P : BinaryExactLaw n m epsilon,
              L ≤ Causalean.Stat.sqRisk
                (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
                sourceEst
                (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1)) ∧
          ∀ M : ℝ, cExact * M ^ 2 *
              (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤ M ^ 2 * L := by
  obtain ⟨a, b, N, ha, hb, hexact⟩ :=
    zengBinaryExactHomogeneityLower epsilon ⟨he0, he1⟩
  let b0 : ℝ := min b (1 / 2)
  have hb0 : 0 < b0 := lt_min hb (by norm_num)
  have hb0b : b0 ≤ b := min_le_left _ _
  have hb0half : b0 ≤ 1 / 2 := min_le_right _ _
  let K : ℝ := 1 + (N : ℝ) + 1 / b0
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := min (a * b0 / 4) ((1 / 200) / K)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  let NExact : ℕ := max N (Nat.ceil (1 / b0))
  refine ⟨b0, c, NExact, hb0, hc, ?_⟩
  intro n d hn hd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  let x : ℝ := b0 * (n : ℝ) ^ 2
  let m : ℕ := min d (max 1 (Nat.floor x))
  have hm : 0 < m ∧ m ≤ d := capped_positive_mass_alphabet_bounds hd
  have hcut : NExact ≤ n → (m : ℝ) ≤ x := by
    intro hN
    have hceilNat : Nat.ceil (1 / b0) ≤ n :=
      (Nat.le_max_right _ _).trans hN
    have hceil : 1 / b0 ≤ (Nat.ceil (1 / b0) : ℝ) := Nat.le_ceil _
    have hnLower : 1 / b0 ≤ (n : ℝ) := hceil.trans (by exact_mod_cast hceilNat)
    have hxOne : 1 ≤ x := by
      dsimp [x]
      have : 1 ≤ b0 * (n : ℝ) := by
        calc
          1 = b0 * (1 / b0) := by field_simp [hb0.ne']
          _ ≤ b0 * (n : ℝ) := mul_le_mul_of_nonneg_left hnLower hb0.le
      nlinarith [hnOne]
    calc
      (m : ℝ) ≤ (max 1 (Nat.floor x) : ℕ) := by
        exact_mod_cast min_le_right d _
      _ = max (1 : ℝ) (Nat.floor x : ℝ) := by norm_num
      _ ≤ x := max_le hxOne (Nat.floor_le (by linarith))
  refine ⟨hm.1, hm.2, hcut, ?_⟩
  by_cases hlarge : N ≤ n ∧ 1 ≤ x
  · have hmFloor : m = min d (Nat.floor x) := by
      dsimp [m]
      rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.floor_pos.mpr hlarge.2)))]
    have hmx : (m : ℝ) ≤ x := by
      rw [hmFloor]
      exact (show ((min d (Nat.floor x) : ℕ) : ℝ) ≤ Nat.floor x by
        exact_mod_cast min_le_right d (Nat.floor x)).trans
          (Nat.floor_le (by linarith [hlarge.2]))
    have hmb : (m : ℝ) ≤ b * (n : ℝ) ^ 2 := by
      exact hmx.trans (by dsimp [x]; exact mul_le_mul_of_nonneg_right hb0b (sq_nonneg _))
    let sourceRate : ℝ := 1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2
    let L : ℝ := a / 2 * sourceRate
    have hsource := exact_source_risk_of_binaryExact_lower hn hm.1 he0 he1 ha
      (by simpa [sourceRate] using hexact n m hm.1 hlarge.1 hmb)
    have hfloorHalf : x / 2 ≤ (Nat.floor x : ℝ) :=
      half_le_natFloor_of_one_le hlarge.2
    have hbcoef : b0 / 2 ≤ 1 := by linarith
    have honeDiv : 0 ≤ 1 / (n : ℝ) := by positivity
    have htarget : b0 / 2 *
        (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤ sourceRate := by
      by_cases hdcap : d ≤ Nat.floor x
      · have hmEq : m = d := by rw [hmFloor, min_eq_left hdcap]
        have hdRatio : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (sq_pos_of_pos hnR)]
          calc
            (d : ℝ) ≤ Nat.floor x := by exact_mod_cast hdcap
            _ ≤ x := Nat.floor_le (by linarith [hlarge.2])
            _ ≤ (n : ℝ) ^ 2 := by
              dsimp [x]
              exact mul_le_of_le_one_left (sq_nonneg _) (by linarith)
        rw [min_eq_right hdRatio]
        dsimp [sourceRate]
        rw [hmEq]
        have hratePos : 0 ≤ 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 := by positivity
        simpa using mul_le_mul_of_nonneg_right hbcoef hratePos
      · have hmEq : m = Nat.floor x := by
          rw [hmFloor, min_eq_right (Nat.le_of_not_ge hdcap)]
        have hmLower : b0 / 2 ≤ (m : ℝ) / (n : ℝ) ^ 2 := by
          rw [hmEq]
          apply (le_div_iff₀ (sq_pos_of_pos hnR)).2
          dsimp [x] at hfloorHalf
          nlinarith
        have hmin := min_le_left (1 : ℝ) ((d : ℝ) / (n : ℝ) ^ 2)
        dsimp [sourceRate]
        calc
          b0 / 2 * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
              b0 / 2 * (1 / (n : ℝ) + 1) := by gcongr
          _ ≤ 1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2 := by
            have hfirst : b0 / 2 * (1 / (n : ℝ)) ≤ 1 / (n : ℝ) :=
              mul_le_of_le_one_left honeDiv hbcoef
            nlinarith
    have hsource' : ∀ sourceEst : (Fin n → BinObs m) → ℝ,
        Measurable sourceEst → ∃ P : BinaryExactLaw n m epsilon,
          L ≤ Causalean.Stat.sqRisk
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            sourceEst
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) := by
      intro sourceEst hmeas
      obtain ⟨P, _hP, hrisk⟩ := hsource sourceEst hmeas
      exact ⟨P, by simpa [L, sourceRate] using hrisk⟩
    refine ⟨L, hsource', ?_⟩
    intro M
    have hcHigh : c ≤ a * b0 / 4 := min_le_left _ _
    let rate : ℝ := 1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)
    have hrate0 : 0 ≤ rate := by dsimp [rate]; positivity
    dsimp [L]
    calc
      c * M ^ 2 * rate = M ^ 2 * (c * rate) := by ring
      _ ≤ M ^ 2 * ((a * b0 / 4) * rate) := by gcongr
      _ = M ^ 2 * (a / 2 * (b0 / 2 * rate)) := by ring
      _ ≤ M ^ 2 * (a / 2 * sourceRate) := by gcongr
  · let L : ℝ := 1 / (200 * (n : ℝ))
    have hsource := exact_source_risk_of_parametric_lower hn hm.1 he0 he1
    have hfallback :
        1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤ K / (n : ℝ) := by
      have hmin := min_le_left (1 : ℝ) ((d : ℝ) / (n : ℝ) ^ 2)
      rcases not_and_or.mp hlarge with hN | hx
      · have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hN)
        have hone : 1 ≤ (N : ℝ) / (n : ℝ) := by
          apply (le_div_iff₀ hnR).2
          simpa using hnN
        have hbterm : 0 ≤ 1 / b0 / (n : ℝ) := by positivity
        calc
          1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤
              1 / (n : ℝ) + 1 := by linarith
          _ ≤ 1 / (n : ℝ) + (N : ℝ) / (n : ℝ) + 1 / b0 / (n : ℝ) := by linarith
          _ = K / (n : ℝ) := by dsimp [K]; ring
      · have hxlt : x < 1 := lt_of_not_ge hx
        have hone : 1 ≤ (1 / b0) / (n : ℝ) := by
          rw [div_div]
          apply (le_div_iff₀ (mul_pos hb0 hnR)).2
          dsimp [x] at hxlt
          nlinarith [hnOne]
        have hNterm : 0 ≤ (N : ℝ) / (n : ℝ) := by positivity
        calc
          1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤
              1 / (n : ℝ) + 1 := by linarith
          _ ≤ 1 / (n : ℝ) + (N : ℝ) / (n : ℝ) + 1 / b0 / (n : ℝ) := by linarith
          _ = K / (n : ℝ) := by dsimp [K]; ring
    refine ⟨L, hsource, ?_⟩
    intro M
    have hcLow : c ≤ (1 / 200) / K := min_le_right _ _
    let rate : ℝ := 1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)
    have hrate0 : 0 ≤ rate := by dsimp [rate]; positivity
    dsimp [L]
    calc
      c * M ^ 2 * rate = M ^ 2 * (c * rate) := by ring
      _ ≤ M ^ 2 * (((1 / 200) / K) * rate) := by gcongr
      _ ≤ M ^ 2 * (((1 / 200) / K) * (K / (n : ℝ))) := by gcongr
      _ = M ^ 2 * (1 / (200 * (n : ℝ))) := by field_simp [hK.ne', hnR.ne']

-- @node: thm:radius-channel-converse-all-d
/-- [The hypothesis-independent Bernoulli contraction transfers the one-arm source bound, while
  the exact-homogeneity source supplies the capped `d/n²` term](goal). -/
theorem radius_channel_converse_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon bRad : ℝ,
      0 < c_epsilon ∧ c_epsilon ≤ 1 ∧
      0 < bRad ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → -- @realizes M(range [1,infinity))
        0 ≤ sigma → sigma ≤ 2 →
        c_epsilon * M ^ 2 * converseRate n d sigma ≤
          minimaxRisk n d epsilon M sigma ∧
        RadialTargetRiskTransferCertificate n d epsilon M sigma
          c_epsilon bRad := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨aRad, bRad, bRadCutoff, cRad, NRad0,
      haRad, hbRad, hbRadCutoff, hcRad, hradial⟩ :=
    exists_capped_radial_transport_package hepsilon hepsilon_half
  obtain ⟨bExact, cExact, NExact,
      hbExact, hcExact, hexact⟩ :=
    exists_capped_exact_transport_package hepsilon hepsilon_half
  obtain ⟨cBase, hcBase, hbase⟩ :=
    scaled_binary_exact_lower_transfer_all_d epsilon hepsilon hepsilon_half
  let NRad : ℕ := max NRad0 1
  have hNRad : 0 < NRad := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  let cSmall : ℝ := 1 / (800 * (NRad : ℝ))
  have hcSmall : 0 < cSmall := by dsimp [cSmall]; positivity
  let cTransfer : ℝ := min (min cRad cSmall) cExact
  have hcTransfer : 0 < cTransfer := lt_min (lt_min hcRad hcSmall) hcExact
  have hcTransferRad : cTransfer ≤ cRad :=
    (min_le_left (min cRad cSmall) cExact).trans (min_le_left _ _)
  have hcTransferSmall : cTransfer ≤ cSmall :=
    (min_le_left (min cRad cSmall) cExact).trans (min_le_right _ _)
  have hcTransferExact : cTransfer ≤ cExact := min_le_right _ _
  let cE : ℝ := min (min cBase cTransfer / 2) 1
  have hcE : 0 < cE := lt_min (by positivity) (by norm_num)
  have hcEOne : cE ≤ 1 := min_le_right _ _
  have hcERate : cE ≤ min cBase cTransfer / 2 := min_le_left _ _
  have hcETransfer : cE ≤ cTransfer := by
    calc
      cE ≤ min cBase cTransfer / 2 := hcERate
      _ ≤ cTransfer / 2 := div_le_div_of_nonneg_right
        (min_le_right _ _) (by norm_num)
      _ ≤ cTransfer := by linarith
  have hcERad : cE ≤ cRad := by
    calc
      cE ≤ min cBase cTransfer / 2 := min_le_left _ _
      _ ≤ cTransfer := by
        have : 0 ≤ min cBase cTransfer := le_min hcBase.le hcTransfer.le
        have := min_le_right cBase cTransfer
        nlinarith
      _ ≤ min cRad cSmall := min_le_left _ _
      _ ≤ cRad := min_le_left _ _
  have hcESmall : cE ≤ cSmall := by
    calc
      cE ≤ min cBase cTransfer / 2 := min_le_left _ _
      _ ≤ cTransfer := by
        have : 0 ≤ min cBase cTransfer := le_min hcBase.le hcTransfer.le
        have := min_le_right cBase cTransfer
        nlinarith
      _ ≤ min cRad cSmall := min_le_left _ _
      _ ≤ cSmall := min_le_right _ _
  have hcEExact : cE ≤ cExact := by
    calc
      cE ≤ min cBase cTransfer / 2 := min_le_left _ _
      _ ≤ cTransfer := by
        have : 0 ≤ min cBase cTransfer := le_min hcBase.le hcTransfer.le
        have := min_le_right cBase cTransfer
        nlinarith
      _ ≤ cExact := min_le_right _ _
  refine ⟨cE, bRad, hcE, hcEOne, hbRad, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigmaTwo
  let mRad := min d (max 1 (Nat.floor (bRad * (n : ℝ) * logEN n)))
  let mExact := min d (max 1 (Nat.floor (bExact * (n : ℝ) ^ 2)))
  have hmRad := capped_positive_mass_alphabet_bounds
    (d := d) (cutoff := Nat.floor (bRad * (n : ℝ) * logEN n)) hd
  have hmExact := capped_positive_mass_alphabet_bounds
    (d := d) (cutoff := Nat.floor (bExact * (n : ℝ) ^ 2)) hd
  let padRad : Fin mRad → Fin d := fun k => ⟨k, lt_of_lt_of_le k.isLt hmRad.2⟩
  let padExact : Fin mExact → Fin d := fun k => ⟨k, lt_of_lt_of_le k.isLt hmExact.2⟩
  let H : LeastFavorableHandle n d epsilon M sigma := {
    lambda := sigma / 2
    radialCap := mRad
    exactCap := mExact
    radialSource := Set.univ
    exactSource := Set.univ
    radialIndex := padRad
    exactIndex := padExact
    radialIndex_injective := by
      intro x y h
      apply Fin.ext
      simpa [padRad] using congrArg Fin.val h
    exactIndex_injective := by
      intro x y h
      apply Fin.ext
      simpa [padExact] using congrArg Fin.val h
    radialEmbedding := fun P => affineBinaryRealLaw M
      (binaryPadLaw hmRad.2 (radialContractedBinaryLaw P.1 sigma hsigma hsigmaTwo))
    exactEmbedding := fun P => affineBinaryRealLaw M (binaryPadLaw hmExact.2 P.1)
    radialCoupling := fun P => (binaryIndependentFullPMF P.1).toMeasure
    exactCoupling := fun P => (binaryIndependentFullPMF P.1).toMeasure
    radial_mass_preserved := by
      intro P _hP k
      exact radialPaddedAffine_cellMass_image hmRad.2 M sigma hsigma hsigmaTwo P.1 k
    exact_mass_preserved := by
      intro P _hP k
      exact affineBinaryPadded_cellMass_image hmExact.2 M P.1 k
    radial_zero_extension := by
      intro P _hP k hk
      exact radialPaddedAffine_cellMass_off_image hmRad.2 M sigma hsigma hsigmaTwo P.1 k hk
    exact_zero_extension := by
      intro P _hP k hk
      exact affineBinaryPadded_cellMass_off_image hmExact.2 M P.1 k hk
    channelSuccess := bernoulliContractionSuccess sigma
    scaledOutcome := fun b => M * ((if b then 1 else 0) - 1 / 2)
    radial_channel_law := by
      intro P _hP
      exact radialPaddedAffine_fullLaw_eq_binaryFullChannel
        P hmRad.2 hepsilon M sigma hsigma hsigmaTwo
    exact_affine_law := by
      intro P _hP
      exact affineBinaryPadded_fullLaw hmExact.2 M P.1
  }
  have hRadCouple : RadialCouplingCertificate H :=
    radialCouplingCertificate_of_independentFullPMF H (fun _ => rfl)
  have hExactCouple : ExactCouplingCertificate H :=
    exactCouplingCertificate_of_independentFullPMF H (fun _ => rfl)
  have hfamily : leastFavorableAt n d epsilon M sigma bRad bExact H := by
    refine ⟨hbRad, hbExact, rfl, rfl, rfl, ?_, ?_, hRadCouple, hExactCouple, ?_, ?_⟩
    · exact radialSourceHard_of_source_eq_univ H hn hmRad.1
        hepsilon hepsilon_half rfl
    · exact exactSourceHard_of_source_eq_univ H hn hmExact.1
        hepsilon hepsilon_half rfl
    · intro b
      rfl
    · intro b
      rfl
  have hRadMem : RadialEmbeddingMembership H :=
    radialEmbeddingMembership_of_contractedPadded H hmRad.2 hepsilon
      hepsilon_half hM hsigma hsigmaTwo (fun _ => rfl)
  have hExactMem : ExactEmbeddingMembership H :=
    exactEmbeddingMembership_of_affinePadded H hmExact.1 hmExact.2
      hepsilon hepsilon_half hM (fun _ => rfl)
  have hRadius : RadiusCertificate H :=
    radiusCertificate_of_radialEmbeddingMembership H hRadMem
  have hRadTarget : ∀ P ∈ H.radialSource,
      rawAteFormula (H.radialEmbedding P) =
        (M * sigma / 2) *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1 + 0 := by
    intro P _hP
    simpa using radialPaddedAffine_rawAteFormula P hmRad.2 hepsilon hsigma hsigmaTwo
  have hExactTarget : ∀ P ∈ H.exactSource,
      rawAteFormula (H.exactEmbedding P) =
        M * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1 := by
    intro P _hP
    exact affineBinaryPadded_rawAteFormula hmExact.2 P.1 P.2.1
  have hTarget : TargetSeparationCertificate H :=
    targetSeparationCertificate_of_pointwise_targets H (by simp [H]; ring)
      hRadTarget hExactTarget
  let K := bernoulliContractionObservedKernel padRad M sigma
  letI : IsMarkovKernel K :=
    bernoulliContractionObservedKernel_isMarkovKernel padRad M sigma hsigma hsigmaTwo
  have hQRad : ∀ P ∈ H.radialSource,
      (H.radialEmbedding P).observedLaw =
        K ∘ₘ CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1 := by
    intro P _hP
    exact radialPaddedAffine_observedLaw hmRad.2 M sigma hsigma hsigmaTwo P.1
  have hProcessing : DataProcessingCertificate H :=
    radialDataProcessingCertificate_of_kernel H K hQRad
  obtain ⟨_hmEpos, _hmEd, hcutExact, LExact, hsourceExact, hscaleExact⟩ :=
    hexact n d hn hd
  have hExactTransfer : ∀ est : Estimator n d M,
      ∃ P ∈ H.exactSource,
        cTransfer * M ^ 2 *
            (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
          mse (H.exactEmbedding P) est.1 := by
    apply exactRiskTransfer_of_affine_transport (c := cTransfer)
      (L := LExact) (a := M) (b := 0) H
      (fun z : BinObs H.exactCap => affineObserved M (binaryPadObs hmExact.2 z))
      (by nlinarith [hM]) (by fun_prop)
    · intro P _hP
      exact affineBinaryPadded_observedLaw hmExact.2 M P.1
    · intro P _hP
      simpa using hExactTarget P (Set.mem_univ P)
    · simpa [H, mExact] using hsourceExact
    · calc
        cTransfer * M ^ 2 * _ ≤ cExact * M ^ 2 * _ := by
          have hrate : 0 ≤ 1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by positivity
          gcongr
        _ ≤ M ^ 2 * LExact := hscaleExact M
  have hRadTransfer : ∀ est : Estimator n d M,
      ∃ P ∈ H.radialSource,
        cTransfer * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
          mse (H.radialEmbedding P) est.1 := by
    by_cases hsZero : sigma = 0
    · intro est
      obtain ⟨P, _hP, _hrisk⟩ := radial_source_risk_of_parametric_lower
        hn hmRad.1 hepsilon hepsilon_half (fun _ => 0) measurable_const
          ⟨0, le_rfl, by simp⟩
      refine ⟨P, Set.mem_univ P, ?_⟩
      subst sigma
      norm_num
      unfold mse
      exact integral_nonneg (fun _ => sq_nonneg _)
    · by_cases hnLarge : NRad0 ≤ n
      · obtain ⟨_hmRpos, _hmRd, _hcutR, hsourceRad, hscaleRad⟩ :=
          hradial n d hn hd hnLarge
        exact radial_risk_of_kernel_transport H (by linarith) K
          (div_ne_zero (mul_ne_zero (by linarith) hsZero) (by norm_num)) hQRad hRadTarget
          (by simpa [H, mRad] using hsourceRad)
          (by
          calc
            cTransfer * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
                cRad * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) := by
                  have hp : 0 ≤ min 1 (polynomialComponent n d) := by
                    apply le_min (by norm_num)
                    unfold polynomialComponent
                    positivity
                  gcongr
            _ ≤ (M * sigma / 2) ^ 2 *
                (aRad / 2 *
                  CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n mRad) := by
                    simpa [mRad] using hscaleRad M sigma)
      · have hnSmall : n ≤ NRad := by
          exact le_trans (Nat.le_of_lt (Nat.lt_of_not_ge hnLarge))
            (Nat.le_max_left _ _)
        exact radial_risk_of_kernel_transport H (by linarith) K
          (div_ne_zero (mul_ne_zero (by linarith) hsZero) (by norm_num)) hQRad hRadTarget
          (by
            intro sourceEst hmeas _hbounded
            exact radial_source_risk_of_parametric_lower
              hn hmRad.1 hepsilon hepsilon_half sourceEst hmeas _hbounded)
          (by
          calc
            cTransfer * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
                cSmall * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) := by
                  have hp : 0 ≤ min 1 (polynomialComponent n d) := by
                    apply le_min (by norm_num)
                    unfold polynomialComponent
                    positivity
                  gcongr
            _ ≤ (M * sigma / 2) ^ 2 * (1 / (200 * (n : ℝ))) := by
              simpa [cSmall] using finiteSampleRadial_transportScale hn hnSmall M sigma)
  have hTransferStrong : RiskTransferCertificate cTransfer H := by
    intro est
    exact ⟨hRadTransfer est, hExactTransfer est⟩
  have hTransfer : RiskTransferCertificate cE H := by
    intro est
    obtain ⟨hr, he⟩ := hTransferStrong est
    refine ⟨⟨hr.choose, hr.choose_spec.1, ?_⟩,
      ⟨he.choose, he.choose_spec.1, ?_⟩⟩
    · have hp : 0 ≤ M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) := by
        have : 0 ≤ min 1 (polynomialComponent n d) := by
          apply le_min (by norm_num)
          unfold polynomialComponent
          positivity
        positivity
      calc
        cE * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) =
            cE * (M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d)) := by ring
        _ ≤ cTransfer * (M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d)) :=
          mul_le_mul_of_nonneg_right hcETransfer hp
        _ = cTransfer * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) := by ring
        _ ≤ mse (H.radialEmbedding hr.choose) est.1 := hr.choose_spec.2
    · have hrate : 0 ≤ M ^ 2 *
          (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) := by positivity
      calc
        cE * M ^ 2 * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) =
            cE * (M ^ 2 * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2))) := by ring
        _ ≤ cTransfer * (M ^ 2 *
            (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_right hcETransfer hrate
        _ = cTransfer * M ^ 2 *
            (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) := by ring
        _ ≤ mse (H.exactEmbedding he.choose) est.1 := he.choose_spec.2
  have hcutRad : NRad ≤ n → (mRad : ℝ) ≤
      bRadCutoff * (n : ℝ) * Real.log n := by
    intro hN
    exact (hradial n d hn hd ((Nat.le_max_left _ _).trans hN)).2.2.1
  have hCutoff : SourceCutoffCertificate bRadCutoff bExact NRad NExact H := by
    exact ⟨hmRad.1, hmRad.2, hmExact.1, hmExact.2, hcutRad,
      by change NExact ≤ n → (mExact : ℝ) ≤ bExact * (n : ℝ) ^ 2
         exact hcutExact⟩
  have hbaseNow := hbase n d M sigma hn hd hM hsigma hsigmaTwo
  have hrisk : cE * M ^ 2 * converseRate n d sigma ≤
      minimaxRisk n d epsilon M sigma := by
    calc
      cE * M ^ 2 * converseRate n d sigma ≤
          (min cBase cTransfer / 2) * M ^ 2 * converseRate n d sigma := by
            have hrate : 0 ≤ converseRate n d sigma := by
              unfold converseRate polynomialComponent
              positivity
            gcongr
      _ ≤ minimaxRisk n d epsilon M sigma :=
        converseRate_lower_of_exact_transfer_and_handle (by linarith)
          hcBase hcTransfer hbaseNow H hRadMem hTransferStrong
  exact ⟨hrisk, radialTargetRiskTransferCertificate_of_handle H hfamily
    hRadMem hRadius hProcessing hTarget hTransfer⟩

-- @node: thm:radius-channel-converse
/-- [Restricted-range corollary of the all-alphabet radius-channel converse](goal). -/
theorem radius_channel_converse :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon bRad : ℝ,
      0 < c_epsilon ∧ c_epsilon ≤ 1 ∧
      0 < bRad ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
        c_epsilon * M ^ 2 *
            (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 +
              sigma ^ 2 * min 1 (polynomialComponent n d)) ≤
          minimaxRisk n d epsilon M sigma ∧
        RadialTargetRiskTransferCertificate n d epsilon M sigma
          c_epsilon bRad := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨c_epsilon, bRad, hc, hc_one, hbRad, hall⟩ :=
    radius_channel_converse_all_d epsilon hepsilon hepsilon_half
  refine ⟨c_epsilon, bRad, hc, hc_one, hbRad, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two hd_range
  obtain ⟨hrisk, htransfer⟩ := hall n d M sigma hn hd hM hsigma hsigma_two
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_one : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hlog : 1 ≤ logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hn_real), Real.log_exp]
    exact le_add_of_nonneg_right (Real.log_nonneg hn_one)
  have hnumerator :
      c_epsilon * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hcap : (d : ℝ) ≤ (n : ℝ) ^ 2 := calc
    (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n := hd_range
    _ ≤ c_epsilon * (n : ℝ) ^ 2 :=
      div_le_self (mul_nonneg (le_of_lt hc) (sq_nonneg (n : ℝ))) hlog
    _ ≤ (n : ℝ) ^ 2 := hnumerator
  have hratio : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hn_real)]
    exact hcap
  refine ⟨?_, htransfer⟩
  simpa [converseRate, min_eq_right hratio] using hrisk

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
