/- Binary-to-real lower-bound transfer constructions. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.Estimators
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ExactHardFamily
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.OneArmLowerDischarge
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ParametricLower
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.AffineEmbedding
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.AffineRealLaw
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.AffineMembership
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.BinaryPadding
import Causalean.Stat.Minimax.MaximalCoupling
import Causalean.Stat.Minimax.MarkovKernelTransport
import Causalean.Stat.Minimax.MinimaxRisk
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set

/-- Apply the same Bernoulli contraction to both potential responses, then scale
the contracted bits.  The formula is a law-level Markov pushforward and is
hypothesis-independent: only the common success function is used. -/
noncomputable def binaryFullChannel {d e : ℕ}
    (pad : Fin d → Fin e) (success scaled : Bool → ℝ)
    (R : Measure (BinaryFullObs d)) : Measure (FullObs e) :=
  ∑ z : BinaryFullObs d, ∑ c0 : Bool, ∑ c1 : Bool,
    (R {z} *
      ENNReal.ofReal (if c0 then success z.b0 else 1 - success z.b0) *
      ENNReal.ofReal (if c1 then success z.b1 else 1 - success z.b1)) •
      Measure.dirac
        (⟨pad z.x, z.a, scaled c0, scaled c1,
          if z.a then scaled c1 else scaled c0⟩ : FullObs e)

/-- Concrete data carried by the two padded, embedded least-favorable families. -/
structure LeastFavorableHandle (n d : ℕ) (epsilon M sigma : ℝ) where
  lambda : ℝ
  radialCap : ℕ
  exactCap : ℕ
  radialSource : Set
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n radialCap epsilon)
  exactSource : Set (BinaryExactLaw n exactCap epsilon)
  radialIndex : Fin radialCap → Fin d
  exactIndex : Fin exactCap → Fin d
  radialIndex_injective : Function.Injective radialIndex
  exactIndex_injective : Function.Injective exactIndex
  radialEmbedding :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n radialCap epsilon →
      RealLaw d
  exactEmbedding : BinaryExactLaw n exactCap epsilon → RealLaw d
  radialCoupling :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n radialCap epsilon →
      Measure (BinaryFullObs radialCap)
  exactCoupling : BinaryExactLaw n exactCap epsilon →
    Measure (BinaryFullObs exactCap)
  radial_mass_preserved : ∀ P ∈ radialSource, ∀ k,
    (radialEmbedding P).cellMass (radialIndex k) =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k
  exact_mass_preserved : ∀ P ∈ exactSource, ∀ k,
    (exactEmbedding P).cellMass (exactIndex k) =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k
  radial_zero_extension : ∀ P ∈ radialSource, ∀ k : Fin d,
    (∀ r, radialIndex r ≠ k) → (radialEmbedding P).cellMass k = 0
  exact_zero_extension : ∀ P ∈ exactSource, ∀ k : Fin d,
    (∀ r, exactIndex r ≠ k) → (exactEmbedding P).cellMass k = 0
  channelSuccess : Bool → ℝ
  scaledOutcome : Bool → ℝ
  radial_channel_law : ∀ P ∈ radialSource,
    (radialEmbedding P).fullLaw =
      binaryFullChannel radialIndex channelSuccess scaledOutcome (radialCoupling P)
  exact_affine_law : ∀ P ∈ exactSource,
    (exactEmbedding P).fullLaw =
      Measure.map (BinaryFullObs.affine M exactIndex) (exactCoupling P)

/-- The selected control-zero source family retains a genuine fixed-sample
minimax lower bound; in particular, it cannot be an arbitrary nonempty set. -/
def RadialSourceHard {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ est : {f : (Fin n →
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs H.radialCap) → ℝ //
          Measurable f},
      ∃ P ∈ H.radialSource,
        c * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n H.radialCap ≤
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            est.1
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1)

/-- The selected uniform exactly-homogeneous source family retains the cited
fixed-sample lower bound. -/
def ExactSourceHard {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ est : {f : (Fin n →
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs H.exactCap) → ℝ //
          Measurable f},
      ∃ P ∈ H.exactSource,
        c * (1 / (n : ℝ) + (H.exactCap : ℝ) / (n : ℝ) ^ 2) ≤
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            est.1
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1)

/-- The chosen full-data couplings have the prescribed radial source margins. -/
def RadialCouplingCertificate {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∀ P ∈ H.radialSource, BinaryFullCoupling P.1 (H.radialCoupling P)

/-- The chosen full-data couplings have the prescribed exact source margins. -/
def ExactCouplingCertificate {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∀ P ∈ H.exactSource, BinaryFullCoupling P.1 (H.exactCoupling P)

/-- Pointwise realization of the two padded source families for fixed model
parameters. -/
def leastFavorableAt (n d : ℕ) (epsilon M sigma bRad bExact : ℝ)
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  0 < bRad ∧ 0 < bExact ∧
  H.lambda = sigma / 2 ∧
  H.radialCap = min d (max 1 (Nat.floor (bRad * n * logEN n))) ∧
  H.exactCap = min d (max 1 (Nat.floor (bExact * (n : ℝ) ^ 2))) ∧
  RadialSourceHard H ∧ ExactSourceHard H ∧
  RadialCouplingCertificate H ∧ ExactCouplingCertificate H ∧
  (∀ b, H.channelSuccess b =
    1 / 2 + H.lambda * ((if b then 1 else 0) - 1 / 2)) ∧
  (∀ b, H.scaledOutcome b = M * ((if b then 1 else 0) - 1 / 2))
  -- @realizes epsilon(overlap index of both binary source families)
  -- @realizes sigma(lambda=sigma/2 contraction radius)
  -- @realizes M(Y(a)=M(B'(a)-1/2))
  -- @realizes Y(a)(affine binary potential-outcome embedding)

-- @node: def:least-favorable-handle
/-- A global least-favorable family.  The two cap constants are selected from
`epsilon` before every sample size, alphabet size, scale, and radius; hence they
cannot vary with model parameters. -/
def leastFavorableFamily (epsilon : ℝ) : Prop :=
  ∃ bRad bExact : ℝ,
    0 < bRad ∧ 0 < bExact ∧
    ∀ n d : ℕ, ∀ M sigma : ℝ,
      0 < n → 0 < d → OutcomeScale M → -- @realizes M(range [1,infinity))
      0 ≤ sigma → sigma ≤ 2 →
      ∃ H : LeastFavorableHandle n d epsilon M sigma,
        leastFavorableAt n d epsilon M sigma bRad bExact H

/-- Every radial embedding belongs to the radius-indexed ambient class.  This
is deliberately downstream of the construction handle. -/
def RadialEmbeddingMembership {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∀ P ∈ H.radialSource,
    ∃ Q : ModelClass d epsilon M sigma, Q.law = H.radialEmbedding P

/-- Every exact-homogeneity embedding belongs to the radius-zero ambient class.
This is deliberately downstream of the construction handle. -/
def ExactEmbeddingMembership {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∀ P ∈ H.exactSource,
    ∃ Q : ModelClass d epsilon M 0, Q.law = H.exactEmbedding P

/-- Every embedded realization obeys the stated heterogeneity radius. -/
def RadiusCertificate {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∀ P ∈ H.radialSource, ∀ k : Fin d,
    0 < (H.radialEmbedding P).cellMass k →
      |cellDeviation (H.radialEmbedding P) k| ≤ sigma * M

/-- The channel and affine embedding scale the source targets by their declared
factors. -/
def TargetSeparationCertificate {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  (∀ P0 ∈ H.radialSource, ∀ P1 ∈ H.radialSource,
    rawAteFormula (H.radialEmbedding P1) -
        rawAteFormula (H.radialEmbedding P0) =
      M * H.lambda *
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P1.1 -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P0.1)) ∧
  (∀ P0 ∈ H.exactSource, ∀ P1 ∈ H.exactSource,
    rawAteFormula (H.exactEmbedding P1) -
        rawAteFormula (H.exactEmbedding P0) =
      M *
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P1.1 -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1))

/-- Product-sample total variation cannot increase under the radial channel. -/
def DataProcessingCertificate {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∀ P0 ∈ H.radialSource, ∀ P1 ∈ H.radialSource,
  Causalean.Stat.tvDist
      (productLaw n (H.radialEmbedding P0))
      (productLaw n (H.radialEmbedding P1)) ≤
    Causalean.Stat.tvDist
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n)
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1.1 n)

/-- A source set, independently of the two-family construction handle, retains
the fixed-sample one-arm lower bound. -/
def RadialSourceHardData {n cap : ℕ} {epsilon : ℝ}
    (source : Set
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon)) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ est : {f : (Fin n →
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs cap) → ℝ //
          Measurable f},
      ∃ P ∈ source,
        c * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n cap ≤
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            est.1
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1)

/-- The common data asserted for one realization of the radial Bernoulli
channel.  Factoring it out keeps the construction and its lower-transfer
certificate tied to the same source, padding, embedding, and coupling. -/
def RadialChannelData (n d : ℕ) (epsilon M sigma bRad : ℝ)
    (cap : ℕ)
    (source : Set
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon))
    (pad : Fin cap → Fin d)
    (embedding :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon →
        RealLaw d)
    (coupling :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon →
        Measure (BinaryFullObs cap)) : Prop :=
    cap = min d (max 1 (Nat.floor (bRad * n * logEN n))) ∧
    Function.Injective pad ∧
    RadialSourceHardData source ∧
    (∀ P ∈ source, ∀ k,
      (embedding P).cellMass (pad k) =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P.1 k) ∧
    (∀ P ∈ source, ∀ k : Fin d,
      (∀ r, pad r ≠ k) → (embedding P).cellMass k = 0) ∧
    (∀ P ∈ source, BinaryFullCoupling P.1 (coupling P)) ∧
    (∀ P ∈ source,
      (embedding P).fullLaw =
        binaryFullChannel pad
          (fun b => 1 / 2 + sigma / 2 * ((if b then 1 else 0) - 1 / 2))
          (fun b => M * ((if b then 1 else 0) - 1 / 2))
          (coupling P)) ∧
    (∀ P ∈ source,
      ∃ Q : ModelClass d epsilon M sigma, Q.law = embedding P) ∧
    (∀ P ∈ source, ∀ k : Fin d,
      0 < (embedding P).cellMass k →
        |cellDeviation (embedding P) k| ≤ sigma * M) ∧
    (∀ P0 ∈ source, ∀ P1 ∈ source,
      Causalean.Stat.tvDist
          (productLaw n (embedding P0))
          (productLaw n (embedding P1)) ≤
        Causalean.Stat.tvDist
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n)
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1.1 n))

/-- The radial family and its Bernoulli channel, including capping, ambient
membership, realization-wise radius, and product-sample data processing. -/
def RadialChannelConstruction (n d : ℕ) (epsilon M sigma bRad : ℝ) : Prop :=
  ∃ cap : ℕ,
  ∃ source : Set
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon),
  ∃ pad : Fin cap → Fin d,
  ∃ embedding :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon →
        RealLaw d,
  ∃ coupling :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon →
        Measure (BinaryFullObs cap),
    RadialChannelData n d epsilon M sigma bRad cap source pad embedding coupling

/-- The same realized radial channel carries both its exact target scaling and
an estimator-wise lower-risk witness on the channel image. -/
def RadialTargetRiskTransferCertificate (n d : ℕ)
    (epsilon M sigma c bRad : ℝ) : Prop :=
  ∃ cap : ℕ,
  ∃ source : Set
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon),
  ∃ pad : Fin cap → Fin d,
  ∃ embedding :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon →
        RealLaw d,
  ∃ coupling :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n cap epsilon →
        Measure (BinaryFullObs cap),
    RadialChannelData n d epsilon M sigma bRad cap source pad embedding coupling ∧
    (∀ P0 ∈ source, ∀ P1 ∈ source,
      rawAteFormula (embedding P1) - rawAteFormula (embedding P0) =
        M * (sigma / 2) *
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P1.1 -
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P0.1)) ∧
    ∀ est : Estimator n d M,
      ∃ P ∈ source,
        c * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
          mse (embedding P) est.1

/-- If [the specified least-favorable family is available](hyp:hfamily) and [the transported
  family belongs to the target model class](hyp:hmembership) and [the radial source lower bound
  holds](hyp:hradius) and [the channel satisfies data processing](hyp:hprocessing), [project the
  radial construction asserted by the two-family internal handle to the radial-only public
  construction statement](goal). -/
lemma radialChannelConstruction_of_handle {n d : ℕ} {epsilon M sigma bRad bExact : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (hfamily : leastFavorableAt n d epsilon M sigma bRad bExact H)
    (hmembership : RadialEmbeddingMembership H)
    (hradius : RadiusCertificate H)
    (hprocessing : DataProcessingCertificate H) :
    RadialChannelConstruction n d epsilon M sigma bRad := by
  rcases hfamily with
    ⟨_hbRad, _hbExact, hlambda, hradialCap, _hexactCap,
      hradialHard, _hexactHard, hcoupling, _hexactCoupling,
      hsuccess, hscaled⟩
  refine ⟨H.radialCap, H.radialSource, H.radialIndex, H.radialEmbedding,
    H.radialCoupling, hradialCap, H.radialIndex_injective, ?_,
    H.radial_mass_preserved, H.radial_zero_extension, hcoupling, ?_,
    hmembership, hradius, hprocessing⟩
  · exact hradialHard
  · intro P hP
    have hsuccess' : H.channelSuccess =
        fun b => 1 / 2 + sigma / 2 * ((if b then 1 else 0) - 1 / 2) := by
      funext b
      rw [hsuccess b, hlambda]
    have hscaled' : H.scaledOutcome =
        fun b => M * ((if b then 1 else 0) - 1 / 2) := by
      funext b
      exact hscaled b
    rw [H.radial_channel_law P hP, hsuccess', hscaled']

/-- After the finite-sample cutoffs, both capped alphabets lie in the respective
source theorem ranges. -/
def SourceCutoffCertificate {n d : ℕ} {epsilon M sigma : ℝ}
    (bRad bExact : ℝ) (NRad NExact : ℕ)
    (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  0 < H.radialCap ∧ H.radialCap ≤ d ∧
  0 < H.exactCap ∧ H.exactCap ≤ d ∧
  (NRad ≤ n →
    (H.radialCap : ℝ) ≤ bRad * (n : ℝ) * Real.log n) ∧
  (NExact ≤ n →
    (H.exactCap : ℝ) ≤ bExact * (n : ℝ) ^ 2)

/-- Each admissible ambient estimator is defeated by a member of each selected
source family at the corresponding transferred lower-bound scale. -/
def RiskTransferCertificate {n d : ℕ} {epsilon M sigma : ℝ}
    (c : ℝ) (H : LeastFavorableHandle n d epsilon M sigma) : Prop :=
  ∀ est : Estimator n d M,
    (∃ P ∈ H.radialSource,
      c * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) ≤
        mse (H.radialEmbedding P) est.1) ∧
    (∃ P ∈ H.exactSource,
      c * M ^ 2 *
          (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
        mse (H.exactEmbedding P) est.1)

/-- If [the specified least-favorable family is available](hyp:hfamily) and [the transported
  family belongs to the target model class](hyp:hmembership) and [the radial source lower bound
  holds](hyp:hradius) and [the channel satisfies data processing](hyp:hprocessing) and [the target
  separation certificate holds](hyp:htarget) and [the risk-transfer certificate
  holds](hyp:htransfer), [package one realized least-favorable handle as a radial certificate
  whose target scaling and estimator-wise risk transfer use those same witnesses](goal). -/
lemma radialTargetRiskTransferCertificate_of_handle {n d : ℕ}
    {epsilon M sigma c bRad bExact : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (hfamily : leastFavorableAt n d epsilon M sigma bRad bExact H)
    (hmembership : RadialEmbeddingMembership H)
    (hradius : RadiusCertificate H)
    (hprocessing : DataProcessingCertificate H)
    (htarget : TargetSeparationCertificate H)
    (htransfer : RiskTransferCertificate c H) :
    RadialTargetRiskTransferCertificate n d epsilon M sigma c bRad := by
  rcases hfamily with
    ⟨_hbRad, _hbExact, hlambda, hradialCap, _hexactCap,
      hradialHard, _hexactHard, hcoupling, _hexactCoupling,
      hsuccess, hscaled⟩
  refine ⟨H.radialCap, H.radialSource, H.radialIndex, H.radialEmbedding,
    H.radialCoupling, ?_, ?_, ?_⟩
  · refine ⟨hradialCap, H.radialIndex_injective, hradialHard,
      H.radial_mass_preserved, H.radial_zero_extension, hcoupling, ?_,
      hmembership, hradius, hprocessing⟩
    intro P hP
    have hsuccess' : H.channelSuccess =
        fun b => 1 / 2 + sigma / 2 * ((if b then 1 else 0) - 1 / 2) := by
      funext b
      rw [hsuccess b, hlambda]
    have hscaled' : H.scaledOutcome =
        fun b => M * ((if b then 1 else 0) - 1 / 2) := by
      funext b
      exact hscaled b
    rw [H.radial_channel_law P hP, hsuccess', hscaled']
  · intro P0 hP0 P1 hP1
    simpa [hlambda] using htarget.1 P0 hP0 P1 hP1
  · intro est
    exact (htransfer est).1

-- @node: radiusCertificate_of_radialEmbeddingMembership
/-- If [the transported family belongs to the target model class](hyp:hmembership), [ambient
  membership already contains the realization-wise homogeneity bound, so it immediately supplies
  the handle's radius certificate](goal). -/
lemma radiusCertificate_of_radialEmbeddingMembership {n d : ℕ}
    {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (hmembership : RadialEmbeddingMembership H) :
    RadiusCertificate H := by
  intro P hP k hk
  obtain ⟨Q, hQ⟩ := hmembership P hP
  have hhom := Q.homogeneity
  rw [hQ] at hhom
  exact hhom k hk

-- @node: lem:parametric-lower
/-- [A one-cell two-point experiment gives the uniform parametric minimax term](goal). -/
lemma parametric_lower :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon : ℝ, 0 < c_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        c_epsilon * M ^ 2 / n ≤ minimaxRisk n d epsilon M sigma := by
  exact parametric_lower_core

-- @node: lem:scaled-binary-exact-lower-transfer-all-d
/-- [The cited exact-homogeneity binary converse transfers through the affine outcome embedding
  and capped-alphabet restriction](goal). -/
lemma scaled_binary_exact_lower_transfer_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon : ℝ, 0 < c_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        c_epsilon * M ^ 2 *
            (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
          minimaxRisk n d epsilon M sigma := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨a, b, N, ha, hb, hexact⟩ :=
    zengBinaryExactHomogeneityLower epsilon ⟨hepsilon, hepsilon_half⟩
  obtain ⟨cp, hcp, hparam⟩ := parametric_lower epsilon hepsilon hepsilon_half
  let b0 : ℝ := min b (1 / 2)
  have hb0 : 0 < b0 := lt_min hb (by norm_num)
  have hb0b : b0 ≤ b := min_le_left _ _
  have hb0half : b0 ≤ 1 / 2 := min_le_right _ _
  let K : ℝ := 1 + (N : ℝ) + 1 / b0
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := min (a * b0 / 4) (cp / K)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  let x : ℝ := b0 * (n : ℝ) ^ 2
  by_cases hlarge : N ≤ n ∧ 1 ≤ x
  · let m : ℕ := min d (Nat.floor x)
    have hfloor : 0 < Nat.floor x := Nat.floor_pos.mpr hlarge.2
    have hm : 0 < m := (Nat.lt_min).2 ⟨hd, hfloor⟩
    have hmd : m ≤ d := min_le_left _ _
    have hmx : (m : ℝ) ≤ x := calc
      (m : ℝ) ≤ Nat.floor x := by exact_mod_cast min_le_right d (Nat.floor x)
      _ ≤ x := Nat.floor_le (le_trans (by norm_num) hlarge.2)
    have hmb : (m : ℝ) ≤ b * (n : ℝ) ^ 2 := by
      dsimp [x] at hmx
      exact hmx.trans (mul_le_mul_of_nonneg_right hb0b (sq_nonneg (n : ℝ)))
    have hbinary := hexact n m hm hlarge.1 hmb
    let sourceRate : ℝ := 1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2
    let L : ℝ := a / 2 * sourceRate
    have hsourceRate : 0 < sourceRate := by dsimp [sourceRate]; positivity
    have hLlt : L < binaryExactMinimaxRisk n m epsilon := by
      have hhalf : L < a * sourceRate := by dsimp [L]; nlinarith [ha, hsourceRate]
      exact hhalf.trans_le (by simpa [sourceRate] using hbinary)
    have hhard := binaryExactMinimaxRisk_hard_family_of_lt
      (n := n) (d := m) hn hm hepsilon hepsilon_half hLlt
    have htransfer := minimaxRisk_ge_of_padded_exact_hard_family
      hmd hm hepsilon hepsilon_half hM hsigma hsigma_two hhard
    have hfloorHalf : x / 2 ≤ (Nat.floor x : ℝ) :=
      half_le_natFloor_of_one_le hlarge.2
    have hb0le : b0 / 2 ≤ 1 := by linarith
    have htarget : b0 / 2 *
          (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤ sourceRate := by
      by_cases hdcap : d ≤ Nat.floor x
      · have hmEq : m = d := min_eq_left hdcap
        have hdRatio : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (sq_pos_of_pos hnR)]
          calc
            (d : ℝ) ≤ Nat.floor x := by exact_mod_cast hdcap
            _ ≤ x := Nat.floor_le (le_trans (by norm_num) hlarge.2)
            _ = b0 * (n : ℝ) ^ 2 := rfl
            _ ≤ 1 * (n : ℝ) ^ 2 := by gcongr; linarith
            _ = (n : ℝ) ^ 2 := one_mul _
        rw [min_eq_right hdRatio]
        dsimp [sourceRate]
        rw [hmEq]
        have hrate0 : 0 ≤ 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 := by positivity
        nlinarith
      · have hmEq : m = Nat.floor x := min_eq_right (Nat.le_of_not_ge hdcap)
        have hmLower : b0 / 2 ≤ (m : ℝ) / (n : ℝ) ^ 2 := by
          rw [hmEq]
          apply (le_div_iff₀ (sq_pos_of_pos hnR)).2
          dsimp [x] at hfloorHalf
          nlinarith [hfloorHalf]
        have hmin : min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤ 1 := min_le_left _ _
        have hone : b0 / 2 * (1 / (n : ℝ)) ≤ 1 / (n : ℝ) := by
          simpa using mul_le_mul_of_nonneg_right hb0le (one_div_nonneg.mpr hnR.le)
        dsimp [sourceRate]
        nlinarith
    have hcHigh : c ≤ a * b0 / 4 := min_le_left _ _
    have hrateNonneg : 0 ≤
        1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by positivity
    have hcoef : c *
        (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
          a / 2 * sourceRate := calc
      c * _ ≤ (a * b0 / 4) * _ :=
        mul_le_mul_of_nonneg_right hcHigh hrateNonneg
      _ = a / 2 * (b0 / 2 *
          (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2))) := by ring
      _ ≤ a / 2 * sourceRate :=
        mul_le_mul_of_nonneg_left htarget (by positivity)
    calc
      c * M ^ 2 * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2))
          ≤ M ^ 2 * (a / 2 * sourceRate) := by
            calc
              _ = M ^ 2 * (c *
                  (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2))) := by ring
              _ ≤ M ^ 2 * (a / 2 * sourceRate) := by gcongr
      _ = M ^ 2 * L := by rfl
      _ ≤ minimaxRisk n d epsilon M sigma := htransfer
  · have hfallback :
        1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤ K / (n : ℝ) := by
      have hmin : min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤ 1 := min_le_left _ _
      rcases not_and_or.mp hlarge with hN | hx
      · have hnN : n < N := Nat.lt_of_not_ge hN
        have hnNreal : (n : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hnN)
        have hone : 1 ≤ (N : ℝ) / (n : ℝ) := by
          apply (le_div_iff₀ hnR).2
          simpa using hnNreal
        have hbterm : 0 ≤ 1 / b0 / (n : ℝ) := by positivity
        calc
          1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)
              ≤ 1 / (n : ℝ) + 1 := by
                simpa [add_comm] using add_le_add_right hmin (1 / (n : ℝ))
          _ ≤ 1 / (n : ℝ) + (N : ℝ) / (n : ℝ) + 1 / b0 / (n : ℝ) := by
            linarith
          _ = K / (n : ℝ) := by dsimp [K]; ring
      · have hxlt : x < 1 := lt_of_not_ge hx
        have hbn : b0 * (n : ℝ) ≤ 1 := by
          dsimp [x] at hxlt
          nlinarith [hnOne, mul_pos hb0 hnR]
        have hone : 1 ≤ (1 / b0) / (n : ℝ) := by
          rw [div_div]
          apply (le_div_iff₀ (mul_pos hb0 hnR)).2
          simpa [mul_comm] using hbn
        have hNterm : 0 ≤ (N : ℝ) / (n : ℝ) := by positivity
        calc
          1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)
              ≤ 1 / (n : ℝ) + 1 := by
                simpa [add_comm] using add_le_add_right hmin (1 / (n : ℝ))
          _ ≤ 1 / (n : ℝ) + (N : ℝ) / (n : ℝ) + 1 / b0 / (n : ℝ) := by
            linarith
          _ = K / (n : ℝ) := by dsimp [K]; ring
    have hcFallback : c ≤ cp / K := min_le_right _ _
    have hscaled : c *
        (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤ cp / (n : ℝ) := by
      have hrate0 : 0 ≤ 1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by
        positivity
      have h1 := mul_le_mul_of_nonneg_left hfallback (le_of_lt hc)
      have h2 := mul_le_mul_of_nonneg_right hcFallback hrate0
      calc
        c * _ ≤ (cp / K) * _ := h2
        _ ≤ (cp / K) * (K / (n : ℝ)) := by gcongr
        _ = cp / (n : ℝ) := by field_simp [hK.ne', hnR.ne']
    have hp := hparam n d M sigma hn hd hM hsigma hsigma_two
    calc
      c * M ^ 2 * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2))
          ≤ cp * M ^ 2 / n := by
            have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
            calc
              _ = M ^ 2 * (c * (1 / (n : ℝ) +
                    min 1 ((d : ℝ) / (n : ℝ) ^ 2))) := by ring
              _ ≤ M ^ 2 * (cp / (n : ℝ)) := by gcongr
              _ = cp * M ^ 2 / n := by ring
      _ ≤ minimaxRisk n d epsilon M sigma := hp

-- @node: lem:scaled-binary-exact-lower-transfer
/-- [Restricted-range corollary of the exact-homogeneity transfer](goal). -/
lemma scaled_binary_exact_lower_transfer :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ a_epsilon b_epsilon : ℝ, ∃ N_epsilon : ℕ,
      0 < a_epsilon ∧ 0 < b_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        N_epsilon ≤ n → 0 < d → (d : ℝ) ≤ b_epsilon * (n : ℝ) ^ 2 →
        1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        a_epsilon * M ^ 2 * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
          minimaxRisk n d epsilon M sigma := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨c_epsilon, hc, hall⟩ :=
    scaled_binary_exact_lower_transfer_all_d epsilon hepsilon hepsilon_half
  refine ⟨c_epsilon, 1, 1, hc, zero_lt_one, ?_⟩
  intro n d M sigma hn hd hd_range hM hsigma hsigma_two
  have hn_pos : 0 < n := Nat.zero_lt_of_lt hn
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hratio : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hn_real)]
    simpa using hd_range
  simpa [min_eq_right hratio] using
    hall n d M sigma hn_pos hd hM hsigma hsigma_two

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
