import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareClassGeometry
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.SmoothEnvelope
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareGramCertificate
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSlice
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedObservation
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.CommonStatisticBernoulli
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedCancellation
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedKL
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedCertificate
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedSuccess
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedNormalized
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.DecisionClass
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Fixed-geometry angular hypercube

The predicate in this file records the whole certified least-favourable
family: common geometry, class membership, disjoint local cells, locality,
target separation, radial agreement, and the two directed KL bounds.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- All quantitative certificates supplied by the rectangle-angular
hypercube at separation `Δ`. -/
def A1A2HypercubeAt (p : ℕ) (ν L Δ c A C C0 : ℝ) : Prop :=
  ∃ (M : ℕ) (w ρ : ℝ)
      (x : Fin M → Score) (P : (Fin M → Bool) → A1A2Law)
      (Q : Fin M → Bool → Measure (ℝ × ℝ)),
    0 < c ∧ 0 < A ∧ 0 < C ∧ 0 < C0 ∧ (p = 0 → 2 * C < A) ∧ 0 < ρ ∧
    (M : ℝ) ≥ c * Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) ∧
    w = A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) ∧
    ρ = Real.pi * w ^ 2 / 36 ∧
    (∀ j, x j ∈ causalHardBottomEdge) ∧
    (∀ j, causalHardCell (x j) w ⊆ causalHardSquare) ∧
    (∀ j k, j ≠ k → dist (x j) (x k) ≥ 2 * w) ∧
    (∀ j k, j ≠ k → Disjoint (causalHardCell (x j) w)
      (causalHardCell (x k) w)) ∧
    (∀ ω, A1A2Class p ν L (P ω)) ∧
    (∀ ω, (P ω).support = causalHardSquare ∧
      (P ω).A1 = causalHardArmOne ∧
      (P ω).A0 = causalHardSquare \ causalHardArmOne ∧
      (P ω).boundary = frontier causalHardArmOne) ∧
    (∀ ω j, (P ω).law {z | causalScore z ∈ causalHardCell (x j) w} =
      ENNReal.ofReal ρ) ∧
    (∀ ω ω' j, ω j = ω' j →
      (P ω).law.restrict {z | causalScore z ∈ causalHardCell (x j) w} =
        (P ω').law.restrict {z | causalScore z ∈ causalHardCell (x j) w}) ∧
    (∀ ω ω', (P ω).law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (x j) w} =
      (P ω').law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (x j) w}) ∧
    (∀ j b, IsProbabilityMeasure (Q j b)) ∧
    (∀ ω j, Measure.map (signedObservationAt (P ω) (x j))
        ((P ω).law.restrict {z | causalScore z ∈ causalHardCell (x j) w}) =
      ENNReal.ofReal ρ • Q j (ω j)) ∧
    (∀ ω ω' j, ω j = ω' j → (P ω).tau (x j) = (P ω').tau (x j)) ∧
    (∀ ω j, |(P ω).tau (x j) -
      (P (Function.update ω j (!ω j))).tau (x j)| = Δ) ∧
    (∀ j, Measure.map Prod.snd (Q j false) = Measure.map Prod.snd (Q j true)) ∧
    (∀ j, (Q j false).restrict
        {yd | ¬ (0 < yd.2 ∧ yd.2 < 2 * C * Δ)} =
      (Q j true).restrict {yd | ¬ (0 < yd.2 ∧ yd.2 < 2 * C * Δ)}) ∧
    (∀ j, InformationTheory.klDiv (Q j false) (Q j true) ≤
      ENNReal.ofReal (C0 * Δ ^ 4 / w ^ 2)) ∧
    (∀ j, InformationTheory.klDiv (Q j true) (Q j false) ≤
      ENNReal.ofReal (C0 * Δ ^ 4 / w ^ 2))

/-- A single order-dependent bandwidth constant dominates every normalized
bump derivative needed through order `p + 1` and is strictly larger than the
twice-cutoff threshold used in the order-zero construction. -/
-- @node: causalHardConstructionBandwidthConstant
lemma causalHardConstructionBandwidthConstant (p : ℕ) :
    ∃ A : ℝ, 256 < A ∧ 1 ≤ A ∧
      ∀ j, j ≤ p + 1 → packingBumpDerivativeBound j ≤ A := by
  refine ⟨257 + packingBumpDerivativeScale (p + 1), ?_, ?_, ?_⟩
  · have hscale := packingBumpDerivativeScale_pos (p + 1)
    linarith
  · have hscale := packingBumpDerivativeScale_pos (p + 1)
    linarith
  · intro j hj
    exact (packingBumpDerivativeBound_le_scale hj).trans (by linarith)

/-- For a fixed positive bandwidth constant, the power-law bandwidth is at
most `1/24` throughout a sufficiently small positive separation interval. -/
-- @node: causalHardPowerBandwidthEventuallySmall
lemma causalHardPowerBandwidthEventuallySmall (p : ℕ) {A : ℝ}
    (hA : 0 < A) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ0 →
      Δ ≤ 1 / 16 ∧ Δ * A ≤ 1 ∧
        A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) ≤ 1 / 24 := by
  have he : 0 < (1 : ℝ) / (p + 1 : ℝ) := by positivity
  have hcont : ContinuousAt
      (fun Δ : ℝ => A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))) 0 := by
    have hp : ContinuousAt
        (fun Δ : ℝ => (Δ, (1 : ℝ) / (p + 1 : ℝ))) 0 :=
      continuousAt_id.prodMk continuousAt_const
    have hr := (Real.continuousAt_rpow_of_pos
      (0, (1 : ℝ) / (p + 1 : ℝ)) he).comp_of_eq hp rfl
    exact continuousAt_const.mul hr
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδmap⟩ := hcont (1 / 24) (by norm_num)
  refine ⟨min (min (δ / 2) (1 / 16)) A⁻¹,
    lt_min (lt_min (half_pos hδ) (by norm_num)) (inv_pos.mpr hA), ?_⟩
  intro Δ hΔ hΔ0
  have hsmall : Δ ≤ 1 / 16 := hΔ0.trans (min_le_left _ _ |>.trans (min_le_right _ _))
  have hscale : Δ * A ≤ 1 := by
    have hΔA : Δ ≤ A⁻¹ := hΔ0.trans (min_le_right _ _)
    calc
      Δ * A ≤ A⁻¹ * A := mul_le_mul_of_nonneg_right hΔA hA.le
      _ = 1 := inv_mul_cancel₀ hA.ne'
  have hdist : dist Δ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hΔ]
    exact hΔ0.trans_lt
      (min_le_left _ _ |>.trans (min_le_left _ _) |>.trans_lt (half_lt_self hδ))
  have hm := hδmap hdist
  have hz : Real.rpow 0 ((1 : ℝ) / (p + 1 : ℝ)) = 0 :=
    (Real.rpow_eq_zero le_rfl (ne_of_gt he)).2 rfl
  rw [hz, mul_zero, dist_zero_right, Real.norm_eq_abs] at hm
  have hnonneg : 0 ≤ A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) :=
    mul_nonneg hA.le (Real.rpow_nonneg hΔ.le _)
  rw [abs_of_nonneg hnonneg] at hm
  exact ⟨hsmall, hscale, hm.le⟩

/-- The order-dependent constant and a small-separation interval jointly
provide the scaled grid and the treatment-profile smooth-extension
certificate.  These are the geometric and smoothness leaves of the final
hypercube constructor. -/
-- @node: causalHardSmoothGridPackage
lemma causalHardSmoothGridPackage (p : ℕ) :
    ∃ A δ0 : ℝ, 256 < A ∧ 0 < δ0 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ0 →
        let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
        let M := angularGridSize w
        0 < w ∧
        (M : ℝ) ≥ (1 / (24 * A)) *
          Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) ∧
        (∀ j : Fin M, causalHardGridCenter M j ∈ causalHardBottomEdge) ∧
        (∀ j : Fin M,
          causalHardCell (causalHardGridCenter M j) w ⊆ causalHardSquare) ∧
        (∀ i j : Fin M, i ≠ j →
          3 * w ≤ dist (causalHardGridCenter M i)
            (causalHardGridCenter M j)) ∧
        (∀ i j : Fin M, i ≠ j →
          Disjoint (causalHardCell (causalHardGridCenter M i) w)
            (causalHardCell (causalHardGridCenter M j) w)) ∧
        ∀ omega : Fin M → Bool,
          EuclideanCExtEnvelope
            (causalHardTreatmentProfile Δ w
              (causalHardGridCenter M) omega)
            p 48 causalHardSquare := by
  obtain ⟨A, hA16, hA1, hderiv⟩ :=
    causalHardConstructionBandwidthConstant p
  obtain ⟨δ0, hδ0, hsmall⟩ :=
    causalHardPowerBandwidthEventuallySmall p (lt_trans (by norm_num) hA16)
  refine ⟨A, δ0, hA16, hδ0, ?_⟩
  intro Δ hΔ hΔ0
  let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
  let M := angularGridSize w
  obtain ⟨hΔsmall, hΔscale, hwsmall⟩ := hsmall Δ hΔ hΔ0
  have hgeom := causalHardGrid_scaled_family_geometry p
    (lt_trans (by norm_num) hA16) hΔ hwsmall
  refine ⟨hgeom.1, hgeom.2.1, hgeom.2.2.2.1,
    hgeom.2.2.2.2.1, hgeom.2.2.2.2.2.1,
    hgeom.2.2.2.2.2.2, ?_⟩
  intro omega
  apply causalHardTreatmentProfile_euclideanCExtEnvelope_powerBandwidth
    p (by norm_num) hA1 hΔ hΔsmall hgeom.2.2.2.2.2.1 omega hderiv
  calc
    Δ * packingBumpDerivativeBound 0 ≤ Δ * A :=
      mul_le_mul_of_nonneg_left (hderiv 0 (by omega)) hΔ.le
    _ ≤ 1 := hΔscale

/-- The geometric/smooth package supplies constructor-ready positive packing
and cutoff constants.  In particular, the cutoff is strictly below half the
bandwidth constant, as required in the order-zero branch. -/
-- @node: causalHardHypercubeConstructorPrefix
lemma causalHardHypercubeConstructorPrefix (p : ℕ) :
    ∃ c A C δ0 : ℝ,
      0 < c ∧ 0 < A ∧ 0 < C ∧ (p = 0 → 2 * C < A) ∧ 0 < δ0 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ0 →
        let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
        let M := angularGridSize w
        0 < w ∧
        (M : ℝ) ≥ c *
          Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) ∧
        (∀ j : Fin M, causalHardGridCenter M j ∈ causalHardBottomEdge) ∧
        (∀ j : Fin M,
          causalHardCell (causalHardGridCenter M j) w ⊆ causalHardSquare) ∧
        (∀ i j : Fin M, i ≠ j →
          3 * w ≤ dist (causalHardGridCenter M i)
            (causalHardGridCenter M j)) ∧
        (∀ i j : Fin M, i ≠ j →
          Disjoint (causalHardCell (causalHardGridCenter M i) w)
            (causalHardCell (causalHardGridCenter M j) w)) ∧
        ∀ omega : Fin M → Bool,
          EuclideanCExtEnvelope
            (causalHardTreatmentProfile Δ w
              (causalHardGridCenter M) omega)
            p 48 causalHardSquare := by
  obtain ⟨A, δ0, hA, hδ0, hpackage⟩ := causalHardSmoothGridPackage p
  refine ⟨1 / (24 * A), A, 128, δ0, ?_, by linarith, by norm_num, ?_, hδ0, ?_⟩
  · positivity
  · intro _
    linarith
  · intro Δ hΔ hΔ0
    simpa using hpackage Δ hΔ hΔ0

/-- The constructor prefix with the quantitative small-separation facts kept
explicit.  These bounds are the common input to the Bernoulli variance,
complete-cell, and localized signed-radius certificates in the final
hypercube assembly. -/
-- @node: causalHardHypercubeConstructorData
lemma causalHardHypercubeConstructorData (p : ℕ) :
    ∃ c A C δ0 : ℝ,
      0 < c ∧ 256 < A ∧ 0 < C ∧ (p = 0 → 2 * C < A) ∧ 0 < δ0 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ0 →
        let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
        let M := angularGridSize w
        Δ ≤ 1 / 16 ∧ Δ * A ≤ 1 ∧ w ≤ 1 / 24 ∧ 0 < w ∧
        (M : ℝ) ≥ c *
          Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) ∧
        (∀ j : Fin M, causalHardGridCenter M j ∈ causalHardBottomEdge) ∧
        (∀ j : Fin M,
          causalHardCell (causalHardGridCenter M j) w ⊆ causalHardSquare) ∧
        (∀ i j : Fin M, i ≠ j →
          3 * w ≤ dist (causalHardGridCenter M i)
            (causalHardGridCenter M j)) ∧
        (∀ i j : Fin M, i ≠ j →
          Disjoint (causalHardCell (causalHardGridCenter M i) w)
            (causalHardCell (causalHardGridCenter M j) w)) ∧
        ∀ omega : Fin M → Bool,
          EuclideanCExtEnvelope
            (causalHardTreatmentProfile Δ w
              (causalHardGridCenter M) omega)
            p 48 causalHardSquare := by
  obtain ⟨A, hA16, hA1, hderiv⟩ :=
    causalHardConstructionBandwidthConstant p
  have hA0 : 0 < A := lt_trans (by norm_num) hA16
  obtain ⟨δ0, hδ0, hsmall⟩ :=
    causalHardPowerBandwidthEventuallySmall p hA0
  refine ⟨1 / (24 * A), A, 128, δ0, ?_, hA16, by norm_num, ?_, hδ0, ?_⟩
  · positivity
  · intro _
    linarith
  · intro Δ hΔ hΔ0
    let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
    let M := angularGridSize w
    obtain ⟨hΔsmall, hΔscale, hwsmall⟩ := hsmall Δ hΔ hΔ0
    have hgeom := causalHardGrid_scaled_family_geometry p hA0 hΔ hwsmall
    refine ⟨hΔsmall, hΔscale, hwsmall, hgeom.1, hgeom.2.1,
      hgeom.2.2.2.1, hgeom.2.2.2.2.1, hgeom.2.2.2.2.2.1,
      hgeom.2.2.2.2.2.2, ?_⟩
    intro omega
    apply causalHardTreatmentProfile_euclideanCExtEnvelope_powerBandwidth
      p (by norm_num) hA1 hΔ hΔsmall hgeom.2.2.2.2.2.1 omega hderiv
    calc
      Δ * packingBumpDerivativeBound 0 ≤ Δ * A :=
        mul_le_mul_of_nonneg_left (hderiv 0 (by omega)) hΔ.le
      _ ≤ 1 := hΔscale

/-- The constructor data, analytic certificates, and normalized signed-cell
comparison assemble into the complete hypercube predicate. -/
-- @node: causalHardHypercubeAt_of_constructorData
lemma causalHardHypercubeAt_of_constructorData (p : ℕ) {L0 L ν c A δ0 Δ : ℝ}
    (hL0 : 48 ≤ L0)
    (hGram : ∀ L : ℝ, L0 ≤ L →
      ∀ {M : ℕ} (b cA delta w : ℝ) (centers : Fin M → Score)
        (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
        (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
        (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
        (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare),
        PopulationGramFloor
          (causalHardA1A2Law b cA delta w centers omega hb hscale hcA
            hdelta hw hsep hcell) p L)
    (hν : 2 ≤ ν) (hL : L0 ≤ L) (hc : 0 < c) (hA : 0 < A)
    (hA256 : 256 < A) (hδ0 : 0 < δ0) (hΔ : 0 < Δ) (hΔ0 : Δ ≤ δ0)
    (hdata :
      let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
      let M := angularGridSize w
      Δ ≤ 1 / 16 ∧ Δ * A ≤ 1 ∧ w ≤ 1 / 24 ∧ 0 < w ∧
      (M : ℝ) ≥ c * Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) ∧
      (∀ j : Fin M, causalHardGridCenter M j ∈ causalHardBottomEdge) ∧
      (∀ j : Fin M, causalHardCell (causalHardGridCenter M j) w ⊆
        causalHardSquare) ∧
      (∀ i j : Fin M, i ≠ j →
        3 * w ≤ dist (causalHardGridCenter M i) (causalHardGridCenter M j)) ∧
      (∀ i j : Fin M, i ≠ j →
        Disjoint (causalHardCell (causalHardGridCenter M i) w)
          (causalHardCell (causalHardGridCenter M j) w)) ∧
      ∀ omega : Fin M → Bool,
        EuclideanCExtEnvelope
          (causalHardTreatmentProfile Δ w (causalHardGridCenter M) omega)
          p 48 causalHardSquare) :
    A1A2HypercubeAt p ν L Δ c A 128 262144 := by
  let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
  let M := angularGridSize w
  let centers : Fin M → Score := causalHardGridCenter M
  obtain ⟨hΔsmall, hΔscale, hwsmall, hw, hM, hcenter, hcell, hsep,
    hdisjoint, hsmooth⟩ := hdata
  have hL48 : 48 ≤ L := hL0.trans hL
  have hb : (0 : ℝ) < 1 / 16 := by norm_num
  have hscale : (0 : ℝ) < 8 * Δ := by positivity
  let P := fun omega => causalHardA1A2Law (1 / 16) 8 Δ w centers omega
    hb hscale (by norm_num) hΔ hw hsep hcell
  let Q := fun j bit => causalHardCellBitObservationLaw (1 / 16) 8 Δ w centers
    hb hscale (by norm_num) hΔ hw hsep hcell j bit
  have hvertex := causalHardA1A2Law_vertex_core (1 / 16) 8 Δ w centers hb
    hscale (by norm_num) hΔ hΔsmall hw hsep
    (fun j => hcell j (Metric.mem_closedBall_self hw.le)) hcell
  dsimp only at hvertex
  refine ⟨M, w, Real.pi * w ^ 2 / 36, centers, P, Q,
    hc, hA, by norm_num, by norm_num, ?_, ?_, hM, rfl, rfl,
    hcenter, hcell, ?_, hdisjoint, ?_, hvertex.1, hvertex.2.1,
    hvertex.2.2.1, hvertex.2.2.2.1, ?_, ?_, ?_, hvertex.2.2.2.2,
    ?_, ?_, ?_, ?_⟩
  · intro hp0
    linarith
  · positivity
  · intro j k hjk
    exact (by linarith [hsep j k hjk])
  · intro omega
    apply causalHardA1A2Law_mem_class_of_analytic_certificates p ν L
      (1 / 16) 8 Δ w centers omega hb hscale (by norm_num) hΔ hΔsmall hw
      hsep hcell hν hL48
    · obtain ⟨U, hUopen, hsub, g, hgdiff, hgeq, hbdd, hbddLip, henv⟩ :=
        hsmooth omega
      refine ⟨U, hUopen, hsub, g, hgdiff, ?_, hbdd, hbddLip,
        henv.trans hL48⟩
      exact hgeq
    · exact hGram L hL (1 / 16) 8 Δ w centers omega hb hscale
        (by norm_num) hΔ hw hsep hcell
    · exact causalHardA1A2Law_localMass_certificate (1 / 16) 8 Δ w centers
        omega hb hscale (by norm_num) hΔ hw hsep hcell hL48
    · exact causalHardA1A2Law_slice_certificate (1 / 16) 8 Δ w centers omega
        hb hscale (by norm_num) hΔ hw hsep hcell hL48
  · intro j bit
    dsimp [Q]
    infer_instance
  · intro omega j
    exact causalHardCellSignedObservationMeasure_eq_bitLaw j (1 / 16) 8 Δ w
      centers omega hb hscale (by norm_num) hΔ hw hsep hcell
  · intro omega omega' j hbit
    exact causalHardA1A2Law_tau_center_eq_of_bit_eq j (1 / 16) 8 Δ w
      centers omega omega' hb hscale (by norm_num) hΔ hΔsmall hw hsep
      (fun k => hcell k (Metric.mem_closedBall_self hw.le)) hcell hbit
  · intro j
    exact causalHardCellBitObservationLaw_common_signedMarginal j (1 / 16) 8 Δ w
      centers hb hscale (by norm_num) hΔ hw (hwsmall.trans (by norm_num))
      hsep (hcenter j) hcell
  · intro j
    have hout := causalHardCellBitObservationLaw_restrict_compl_eq j centers
      (b := 1 / 16) (cA := 8) (delta := Δ) (w := w) rfl hb hscale
      (by norm_num) hΔ hΔsmall hw (hwsmall.trans (by norm_num)) hsep
      (hcenter j) hcell
    have hcut : 2 * (8 * Δ) / (1 / 16 : ℝ) = 2 * 128 * Δ := by ring
    simpa only [hcut] using hout
  · intro j
    exact (causalHardCellBitObservationLaw_klDiv_le j centers hΔ hΔsmall hw
      (hwsmall.trans (by norm_num)) hsep (hcenter j) hcell).1
  · intro j
    exact (causalHardCellBitObservationLaw_klDiv_le j centers hΔ hΔsmall hw
      (hwsmall.trans (by norm_num)) hsep (hcenter j) hcell).2

-- @node: lem:cty-a1-a2-rectangle-angular-hypercube-all-orders
/-- For every local-polynomial order, all sufficiently small separations allow
the fixed-square, fixed-assignment rectangle-angular hypercube. -/
lemma cty_a1_a2_rectangle_angular_hypercube (p : ℕ) :
    ∃ L0 : ℝ, 48 ≤ L0 ∧ ∀ ν : ℝ, 2 ≤ ν → ∀ L : ℝ, L0 ≤ L →
      ∃ c A C C0 : ℝ,
        0 < c ∧ 0 < A ∧ 0 < C ∧ 0 < C0 ∧ (p = 0 → 2 * C < A) ∧
        ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ0 →
          A1A2HypercubeAt p ν L Δ c A C C0 := by
  obtain ⟨LGram, hLGram48, hGram⟩ :=
    causalHardA1A2Law_populationGram_certificate p
  obtain ⟨c, A, C, δ0, hc, hA, hC, hp0, hδ0, hdata⟩ :=
    causalHardHypercubeConstructorData p
  have hApos : 0 < A := lt_trans (by norm_num) hA
  refine ⟨LGram, hLGram48, ?_⟩
  intro ν hν L hL
  refine ⟨c, A, 128, 262144, hc, hApos, by norm_num, by norm_num, ?_,
    δ0, hδ0, ?_⟩
  · intro hp
    have := hp0 hp
    norm_num at this ⊢
    linarith
  · intro Δ hΔ hΔ0
    apply causalHardHypercubeAt_of_constructorData p hLGram48 hGram hν hL
      hc hApos hA
    · exact hδ0
    · exact hΔ
    · exact hΔ0
    · exact hdata Δ hΔ hΔ0

end CausalSmith.Stat.BddUniformLogPenalty
