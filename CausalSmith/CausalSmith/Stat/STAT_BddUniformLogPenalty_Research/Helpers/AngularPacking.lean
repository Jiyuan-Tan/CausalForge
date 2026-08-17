import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Basic
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularGrid
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularCoordinates
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.SquareBoundary
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.BumpHolder
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.Polar
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularMeasure
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularDesign
import Causalean.Stat.Minimax.Assouad
import Causalean.Stat.Minimax.ChiSquared
import Causalean.Stat.Minimax.Pinsker
import Causalean.Mathlib.Probability.BernoulliMeasure
import Causalean.Mathlib.InformationTheory.KLBind
import Causalean.Mathlib.InformationTheory.ProductKLLeCam
import Causalean.Mathlib.Probability.Kernel.GraphMapProd
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Angular hard-family packing

This file provides the low-level probability and geometry primitives for the
square-support hypercube construction.  The complete certificate is stated
downstream in `AngularPackingTheorem`, after the faithful law constructor is
available without an import cycle.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The fixed unit square supporting every law in the hard family. -/
def packingSquare : Set Score :=
  scoreCube (1 / 2 : ℝ)

/-- The square used by the hard family is compact. -/
-- @node: packingSquare_isCompact
lemma packingSquare_isCompact : IsCompact packingSquare := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · unfold packingSquare scoreCube
    rw [show {x : Score | ∀ i, |x i| ≤ (1 / 2 : ℝ)} =
        ⋂ i : Fin 2, {x : Score | |x i| ≤ (1 / 2 : ℝ)} by
      ext x
      simp]
    apply isClosed_iInter
    intro i
    simpa [Real.norm_eq_abs] using
      (isClosed_le
        ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).norm)
        continuous_const)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, ?_⟩
    intro x hx
    unfold packingSquare scoreCube at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [EuclideanSpace.norm_eq]
    have h0 := hx (0 : Fin 2)
    have h1 := hx (1 : Fin 2)
    have h0sq : |x 0| ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) := by
      nlinarith [abs_nonneg (x 0)]
    have h1sq : |x 1| ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) := by
      nlinarith [abs_nonneg (x 1)]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs]
    rw [Real.sqrt_le_one]
    nlinarith

/-- Any envelope at least one half contains the packing square in its ambient
coordinate cube. -/
-- @node: packingSquare_subset_scoreCube
lemma packingSquare_subset_scoreCube {L : ℝ} (hL : 1 / 2 ≤ L) :
    packingSquare ⊆ scoreCube L := by
  intro x hx i
  exact (hx i).trans hL

/-- The half-disc cell cut out by the square at a boundary packing point. -/
def packingCell {M : ℕ} (centers : Fin M → Score) (w : ℝ) (j : Fin M) : Set Score :=
  Metric.closedBall (centers j) w ∩ packingSquare

/-- The explicit lower-edge grid centers lie on the frontier of the packing
square. -/
-- @node: angularGridCenter_mem_packingSquare_frontier
lemma angularGridCenter_mem_packingSquare_frontier (M : ℕ) (j : Fin M) :
    angularGridCenter M j ∈ frontier packingSquare := by
  simpa [packingSquare] using angularGridCenter_mem_frontier M j

/-- The explicit grid yields pairwise disjoint packing cells whenever twice
the cell radius is smaller than one grid spacing. -/
-- @node: angularGridPackingCells_disjoint
lemma angularGridPackingCells_disjoint (M : ℕ) (w : ℝ)
    (hw : 2 * w < 1 / (2 * (M + 1 : ℕ) : ℝ))
    (i j : Fin M) (hij : i ≠ j) :
    Disjoint (packingCell (angularGridCenter M) w i)
      (packingCell (angularGridCenter M) w j) := by
  simpa [packingCell, packingSquare] using angularGridCells_disjoint M w hw i j hij

/-- Whenever the frontier-rate radius is small, the explicit grid supplies the
entire geometric prefix of `AngularPackingAt`, with constants `c₀ = 1/24` and
both radius-comparison constants equal to one. -/
-- @node: angularPacking_geometry
lemma angularPacking_geometry (n q : ℕ) (hn : 2 ≤ n)
    (hsmall : angularGridRadius n q ≤ 1 / 24) :
      ∃ M : ℕ, ∃ w : ℝ, ∃ centers : Fin M → Score,
        (1 / 24 : ℝ) * Real.rpow (frontierRate n) (-(1 : ℝ) / q) ≤ M ∧
        ((1 : ℝ) * Real.rpow (frontierRate n) ((1 : ℝ) / q) ≤ w ∧
          w ≤ (1 : ℝ) * Real.rpow (frontierRate n) ((1 : ℝ) / q)) ∧
        (∀ j, centers j ∈ frontier packingSquare) ∧
        (∀ i j, i ≠ j →
          dist (centers i) (centers j) ≥
            (1 : ℝ) * Real.rpow (frontierRate n) ((1 : ℝ) / q)) ∧
        (∀ i j, i ≠ j →
          Disjoint (packingCell centers w i) (packingCell centers w j)) := by
  let w := angularGridRadius n q
  let M := angularGridSize w
  have hw0 : 0 < w := by
    exact Real.rpow_pos_of_pos (frontierRate_pos hn) _
  have hwEq : w = Real.rpow (frontierRate n) ((1 : ℝ) / q) := rfl
  have hM := angularGridSize_frontier_lower n q hn hsmall
  have hgeometry := angularGridSize_geometry w hw0 hsmall
  rcases hgeometry with ⟨_, hcenters, hpairs⟩
  refine ⟨M, w, angularGridCenter M, hM, ?_, ?_, ?_, ?_⟩
  · simpa [hwEq]
  · intro j
    simpa [packingSquare] using (hcenters j).1
  · intro i j hij
    have hsep := (hpairs i j hij).1
    simp only [one_mul]
    calc
      Real.rpow (frontierRate n) ((1 : ℝ) / q) = w := hwEq.symm
      _ ≤ dist (angularGridCenter M i) (angularGridCenter M j) := by
        nlinarith [hw0]
  · intro i j hij
    simpa [packingCell, packingSquare] using (hpairs i j hij).2

/-- The one-observation unsigned radial-outcome law at a query point. -/
noncomputable def onePointDistanceLaw (P : CtyLaw) (x : Score) : Measure (ℝ × ℝ) :=
  Measure.map (fun o : Observation => (o.1, dist o.2 x)) P.law

/-- The one-observation radial-outcome law is a probability measure. -/
-- @node: onePointDistanceLaw_isProbabilityMeasure
lemma onePointDistanceLaw_isProbabilityMeasure (P : CtyLaw) (x : Score) :
    IsProbabilityMeasure (onePointDistanceLaw P x) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The `n`-observation distance-compressed law at a query point. -/
noncomputable def compressedSampleLaw (P : CtyLaw) (n : ℕ) (x : Score) :
    Measure (DistanceSample n) :=
  Measure.map (fun w => distanceData n w x) (sampleLaw P n)

/-- The distance-compressed i.i.d. sample law is a probability measure. -/
-- @node: compressedSampleLaw_isProbabilityMeasure
lemma compressedSampleLaw_isProbabilityMeasure (P : CtyLaw) (n : ℕ) (x : Score) :
    IsProbabilityMeasure (compressedSampleLaw P n x) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  letI : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw
    infer_instance
  exact Measure.isProbabilityMeasure_map (measurable_distanceData n x).aemeasurable

/-- The compressed i.i.d. sample law is exactly the finite product of the
one-observation radial-outcome law.  This is the bridge that permits KL
tensorization directly after distance compression. -/
-- @node: compressedSampleLaw_eq_pi_onePointDistanceLaw
lemma compressedSampleLaw_eq_pi_onePointDistanceLaw
    (P : CtyLaw) (n : ℕ) (x : Score) :
    compressedSampleLaw P n x =
      Measure.pi (fun _ : Fin n => onePointDistanceLaw P x) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  unfold compressedSampleLaw sampleLaw onePointDistanceLaw distanceData
  change Measure.map
      (fun w i => (fun o : Observation => (o.1, dist o.2 x)) (w i))
      (Measure.pi fun _ : Fin n => P.law) = _
  exact Measure.pi_map_pi (f := fun _ : Fin n =>
    fun o : Observation => (o.1, dist o.2 x)) (fun _ =>
      (show Measurable (fun o : Observation => (o.1, dist o.2 x)) by
        fun_prop).aemeasurable)

/-- A finite one-observation radial KL bound tensorizes to the compressed
sample law.  Absolute continuity and log-likelihood integrability are the
standard finite-KL guards required by product tensorization. -/
-- @node: compressedSampleLaw_klDiv_le_of_onePoint
lemma compressedSampleLaw_klDiv_le_of_onePoint
    (P P' : CtyLaw) (n : ℕ) (x : Score) {B : ℝ} (hB : 0 ≤ B)
    (hac : onePointDistanceLaw P x ≪ onePointDistanceLaw P' x)
    (hint : Integrable
      (llr (onePointDistanceLaw P x) (onePointDistanceLaw P' x))
      (onePointDistanceLaw P x))
    (hKL : InformationTheory.klDiv (onePointDistanceLaw P x)
      (onePointDistanceLaw P' x) ≤ ENNReal.ofReal B) :
    InformationTheory.klDiv (compressedSampleLaw P n x)
      (compressedSampleLaw P' n x) ≤ ENNReal.ofReal ((n : ℝ) * B) := by
  letI : IsProbabilityMeasure (onePointDistanceLaw P x) :=
    onePointDistanceLaw_isProbabilityMeasure P x
  letI : IsProbabilityMeasure (onePointDistanceLaw P' x) :=
    onePointDistanceLaw_isProbabilityMeasure P' x
  have ht := Causalean.Mathlib.InformationTheory.productKL_tensorization
    n (onePointDistanceLaw P x) (onePointDistanceLaw P' x) hac hint
  rw [compressedSampleLaw_eq_pi_onePointDistanceLaw,
    compressedSampleLaw_eq_pi_onePointDistanceLaw]
  rw [← ENNReal.toReal_le_toReal ht.product_ne_top ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg n) hB)]
  calc
    _ ≤ (n : ℝ) * (InformationTheory.klDiv (onePointDistanceLaw P x)
        (onePointDistanceLaw P' x)).toReal := ht.apply
    _ ≤ (n : ℝ) * B := by
      gcongr
      simpa [ENNReal.toReal_ofReal hB] using
        ENNReal.toReal_mono (by simp) hKL

-- @node: compressedSampleLaw_klDiv_le
/-- Unsigned-distance compression of an i.i.d. sample cannot increase its
Kullback--Leibler divergence. -/
lemma compressedSampleLaw_klDiv_le (P P' : CtyLaw) (n : ℕ) (x : Score) :
    InformationTheory.klDiv (compressedSampleLaw P n x) (compressedSampleLaw P' n x) ≤
      InformationTheory.klDiv (sampleLaw P n) (sampleLaw P' n) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  letI : IsProbabilityMeasure P'.law := P'.law_isProbability
  letI : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw
    infer_instance
  letI : IsProbabilityMeasure (sampleLaw P' n) := by
    unfold sampleLaw
    infer_instance
  exact Causalean.Mathlib.InformationTheory.Measure.klDiv_map_le
    (measurable_distanceData n x)

/-- The common additive standard-Gaussian channel used to turn Bernoulli
outcomes into the smooth conditional outcome laws of the packing. -/
-- @node: gaussianNoiseKernel
noncomputable def gaussianNoiseKernel : Kernel ℝ ℝ :=
  Causalean.Mathlib.GraphMapProd.mechanismKernel (gaussianReal 0 1)
    (fun p : ℝ × ℝ => p.1 + p.2)

-- @node: gaussianNoiseKernel_isMarkovKernel
/-- The stated conditional distribution is a Markov kernel: it is a probability law at each input and varies measurably with that input. -/
instance gaussianNoiseKernel_isMarkovKernel : IsMarkovKernel gaussianNoiseKernel := by
  unfold gaussianNoiseKernel
  exact Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel
    (gaussianReal 0 1) (by fun_prop)

/-- At input `b`, the additive standard-Gaussian channel has law `N(b,1)`. -/
-- @node: gaussianNoiseKernel_apply
lemma gaussianNoiseKernel_apply (b : ℝ) :
    gaussianNoiseKernel b = gaussianReal b 1 := by
  rw [gaussianNoiseKernel,
    Causalean.Mathlib.GraphMapProd.mechanismKernel_apply _ (by fun_prop)]
  simpa using gaussianReal_map_const_add (μ := 0) (v := 1) b

/-- Convolution with the common additive Gaussian noise in the packing cannot
increase the Bernoulli-stage Kullback--Leibler divergence. -/
-- @node: gaussianNoiseKernel_klDiv_bind_le
lemma gaussianNoiseKernel_klDiv_bind_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    InformationTheory.klDiv (μ.bind gaussianNoiseKernel)
        (ν.bind gaussianNoiseKernel) ≤
      InformationTheory.klDiv μ ν := by
  exact Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_le_of_isProbabilityMeasure
    μ ν gaussianNoiseKernel

/-- The conditional outcome law obtained by adding independent standard
Gaussian noise to a real-valued Bernoulli draw. -/
-- @node: bernoulliGaussianLaw
noncomputable def bernoulliGaussianLaw (p : ℝ) : Measure ℝ :=
  (Causalean.Mathlib.Probability.bernoulliLaw p).bind gaussianNoiseKernel

/-- The Bernoulli-plus-Gaussian outcome law is the explicit mixture of the
unit-variance Gaussians centered at one and zero. -/
-- @node: bernoulliGaussianLaw_eq_gaussian_mixture
lemma bernoulliGaussianLaw_eq_gaussian_mixture (p : ℝ) :
    bernoulliGaussianLaw p = ENNReal.ofReal p • gaussianReal 1 1 +
      ENNReal.ofReal (1 - p) • gaussianReal 0 1 := by
  ext s hs
  rw [bernoulliGaussianLaw,
    Measure.bind_apply hs gaussianNoiseKernel.measurable.aemeasurable]
  rw [Causalean.Mathlib.Probability.bernoulliLaw_lintegral_ofReal]
  rw [gaussianNoiseKernel_apply, gaussianNoiseKernel_apply]
  simp [Measure.add_apply, Measure.smul_apply]

/-- Adding the common Gaussian noise preserves the quadratic KL bound for
Bernoulli parameters in the middle half of the unit interval. -/
-- @node: bernoulliGaussianLaw_klDiv_le_four_sq_sub
lemma bernoulliGaussianLaw_klDiv_le_four_sq_sub {p q : ℝ}
    (hp_lo : (1 : ℝ) / 4 ≤ p) (hp_hi : p ≤ 3 / 4)
    (hq_lo : (1 : ℝ) / 4 ≤ q) (hq_hi : q ≤ 3 / 4) :
    InformationTheory.klDiv (bernoulliGaussianLaw p) (bernoulliGaussianLaw q) ≤
      ENNReal.ofReal (4 * (p - q) ^ 2) := by
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw p) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith) (by linarith)
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw q) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith) (by linarith)
  exact (gaussianNoiseKernel_klDiv_bind_le
      (Causalean.Mathlib.Probability.bernoulliLaw p)
      (Causalean.Mathlib.Probability.bernoulliLaw q)).trans
    (Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
      hp_lo hp_hi hq_lo hq_hi)

/-- For a success probability in the unit interval, the
Bernoulli-plus-Gaussian outcome law is a probability measure. -/
-- @node: bernoulliGaussianLaw_isProbabilityMeasure
lemma bernoulliGaussianLaw_isProbabilityMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliGaussianLaw p) := by
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw p) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp0 hp1
  exact MeasureTheory.isProbabilityMeasure_bind
    gaussianNoiseKernel.measurable.aemeasurable
    (Filter.Eventually.of_forall fun _ => inferInstance)

/-- The identity is integrable under every Bernoulli-plus-Gaussian outcome
law, including parameter values outside the unit interval. -/
-- @node: bernoulliGaussianLaw_integrable_id
lemma bernoulliGaussianLaw_integrable_id (p : ℝ) :
    Integrable id (bernoulliGaussianLaw p) := by
  rw [bernoulliGaussianLaw_eq_gaussian_mixture]
  apply Integrable.add_measure
  · exact ((memLp_id_gaussianReal (μ := (1 : ℝ)) (v := 1) 1).integrable
      (by norm_num)).smul_measure (by simp)
  · exact ((memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 1).integrable
      (by norm_num)).smul_measure (by simp)

/-- The identity is square-integrable under every Bernoulli-plus-Gaussian
outcome law.  This supplies the `CtyLaw.sq_integrable` field of the eventual
hard-family construction. -/
-- @node: bernoulliGaussianLaw_memLp_id_two
lemma bernoulliGaussianLaw_memLp_id_two (p : ℝ) :
    MemLp id 2 (bernoulliGaussianLaw p) := by
  rw [memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable,
    bernoulliGaussianLaw_eq_gaussian_mixture]
  apply Integrable.add_measure
  · have h : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 1 1) := by
      simpa [id, Real.norm_eq_abs, sq_abs] using
        (memLp_id_gaussianReal (μ := (1 : ℝ)) (v := 1) 2).integrable_norm_pow
          (by norm_num : (2 : ℕ) ≠ 0)
    exact h.smul_measure (by simp)
  · have h : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
      simpa [id, Real.norm_eq_abs, sq_abs] using
        (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).integrable_norm_pow
          (by norm_num : (2 : ℕ) ≠ 0)
    exact h.smul_measure (by simp)

/-- The conditional mean of a Bernoulli draw plus centered Gaussian noise is
its Bernoulli success probability. -/
-- @node: bernoulliGaussianLaw_integral_id
lemma bernoulliGaussianLaw_integral_id {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ y, y ∂bernoulliGaussianLaw p = p := by
  rw [bernoulliGaussianLaw_eq_gaussian_mixture, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [hp0, sub_nonneg.mpr hp1]
  · exact ((memLp_id_gaussianReal (μ := (1 : ℝ)) (v := 1) 1).integrable
      (by norm_num)).smul_measure (by simp)
  · exact ((memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 1).integrable
      (by norm_num)).smul_measure (by simp)

/-- The second moment about an arbitrary center under `N(m,1)` equals one
plus the squared displacement from the Gaussian mean. -/
-- @node: gaussianReal_integral_sq_sub
lemma gaussianReal_integral_sq_sub (m p : ℝ) :
    ∫ y, (y - p) ^ 2 ∂gaussianReal m 1 = 1 + (m - p) ^ 2 := by
  have hcenterLp : MemLp (fun y : ℝ => y - m) 2 (gaussianReal m 1) := by
    exact (memLp_id_gaussianReal' (μ := m) (v := 1) 2 (by simp)).sub
      (memLp_const m)
  have hsq : Integrable (fun y : ℝ => (y - m) ^ 2) (gaussianReal m 1) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      hcenterLp.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hlin : Integrable (fun y : ℝ => 2 * (m - p) * (y - m))
      (gaussianReal m 1) := by
    exact (hcenterLp.integrable (by norm_num)).const_mul _
  have hvar : ∫ y, (y - m) ^ 2 ∂gaussianReal m 1 = 1 := by
    have hv := variance_id_gaussianReal (μ := m) (v := 1)
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    simp only [id_eq, integral_id_gaussianReal] at hv
    norm_num at hv
    exact hv
  have hcenterMean : ∫ y, y - m ∂gaussianReal m 1 = 0 := by
    have hi := integral_sub
      ((memLp_id_gaussianReal (μ := m) (v := 1) 1).integrable (by norm_num))
      (integrable_const m)
    calc
      _ = (∫ y, y ∂gaussianReal m 1) - ∫ _y, m ∂gaussianReal m 1 := by
        simpa only [Pi.sub_apply, id_eq] using hi
      _ = 0 := by simp
  rw [show (fun y : ℝ => (y - p) ^ 2) =
      fun y => (y - m) ^ 2 + 2 * (m - p) * (y - m) + (m - p) ^ 2 by
    funext y
    ring]
  change (∫ y, ((y - m) ^ 2 + 2 * (m - p) * (y - m)) +
      (m - p) ^ 2 ∂gaussianReal m 1) = _
  calc
    _ = (∫ y, (y - m) ^ 2 + 2 * (m - p) * (y - m) ∂gaussianReal m 1) +
        ∫ _y, (m - p) ^ 2 ∂gaussianReal m 1 := by
      simpa only [Pi.add_apply] using
        integral_add (hsq.add hlin) (by fun_prop :
          Integrable (fun _y : ℝ => (m - p) ^ 2) (gaussianReal m 1))
    _ = ((∫ y, (y - m) ^ 2 ∂gaussianReal m 1) +
          ∫ y, 2 * (m - p) * (y - m) ∂gaussianReal m 1) +
        ∫ _y, (m - p) ^ 2 ∂gaussianReal m 1 := by
      rw [integral_add hsq hlin]
    _ = _ := by
      rw [hvar, integral_const_mul, hcenterMean]
      simp

/-- The conditional variance of a Bernoulli draw plus independent standard
Gaussian noise is `1 + p(1-p)`. -/
-- @node: bernoulliGaussianLaw_variance_id
lemma bernoulliGaussianLaw_variance_id {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    variance id (bernoulliGaussianLaw p) = 1 + p * (1 - p) := by
  letI : IsProbabilityMeasure (bernoulliGaussianLaw p) :=
    bernoulliGaussianLaw_isProbabilityMeasure hp0 hp1
  rw [variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq, bernoulliGaussianLaw_integral_id hp0 hp1]
  rw [bernoulliGaussianLaw_eq_gaussian_mixture, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    rw [gaussianReal_integral_sq_sub, gaussianReal_integral_sq_sub]
    simp [hp0, sub_nonneg.mpr hp1]
    ring
  · apply Integrable.smul_measure _ (by simp)
    simpa [id] using
      (((memLp_id_gaussianReal (μ := (1 : ℝ)) (v := 1) 2).sub
        (memLp_const p)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  · apply Integrable.smul_measure _ (by simp)
    simpa [id] using
      (((memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).sub
        (memLp_const p)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

/-- The measurable Bernoulli-plus-Gaussian kernel of a regression function. -/
-- @node: bernoulliGaussianKernel
noncomputable def bernoulliGaussianKernel (p : Score → ℝ) (hp : Measurable p) :
    Kernel Score ℝ where
  toFun x := bernoulliGaussianLaw (p x)
  measurable' := by
    unfold bernoulliGaussianLaw Causalean.Mathlib.Probability.bernoulliLaw
    fun_prop

/-- A unit-range regression function makes the outcome kernel Markov. -/
-- @node: bernoulliGaussianKernel_isMarkovKernel
lemma bernoulliGaussianKernel_isMarkovKernel (p : Score → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    IsMarkovKernel (bernoulliGaussianKernel p hp) := by
  constructor
  intro x
  exact bernoulliGaussianLaw_isProbabilityMeasure (h0 x) (h1 x)

/-- The joint `(Y,X)` law from a design and the explicit outcome kernel. -/
-- @node: jointBernoulliGaussianLaw
noncomputable def jointBernoulliGaussianLaw
    (nu : Measure Score) (p : Score → ℝ) (hp : Measurable p) : Measure Observation :=
  Measure.map Prod.swap (Measure.compProd nu (bernoulliGaussianKernel p hp))

/-- A probability design and unit-range regression give a probability law. -/
-- @node: jointBernoulliGaussianLaw_isProbabilityMeasure
lemma jointBernoulliGaussianLaw_isProbabilityMeasure
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p : Score → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    IsProbabilityMeasure (jointBernoulliGaussianLaw nu p hp) := by
  letI : IsMarkovKernel (bernoulliGaussianKernel p hp) :=
    bernoulliGaussianKernel_isMarkovKernel p hp h0 h1
  unfold jointBernoulliGaussianLaw
  exact Measure.isProbabilityMeasure_map measurable_swap.aemeasurable

/-- The score marginal is exactly the supplied design law. -/
-- @node: jointBernoulliGaussianLaw_map_snd
lemma jointBernoulliGaussianLaw_map_snd
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p : Score → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    Measure.map Prod.snd (jointBernoulliGaussianLaw nu p hp) = nu := by
  letI : IsMarkovKernel (bernoulliGaussianKernel p hp) :=
    bernoulliGaussianKernel_isMarkovKernel p hp h0 h1
  unfold jointBernoulliGaussianLaw
  rw [Measure.map_map measurable_snd measurable_swap]
  change Measure.map Prod.fst (Measure.compProd nu (bernoulliGaussianKernel p hp)) = nu
  exact Measure.fst_compProd nu (bernoulliGaussianKernel p hp)

/-- Disintegration recovers the supplied outcome kernel almost everywhere. -/
-- @node: jointBernoulliGaussianLaw_condDistrib
lemma jointBernoulliGaussianLaw_condDistrib
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p : Score → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    (let _ : IsProbabilityMeasure (jointBernoulliGaussianLaw nu p hp) :=
        jointBernoulliGaussianLaw_isProbabilityMeasure nu p hp h0 h1
     (fun x => condDistrib Prod.fst Prod.snd (jointBernoulliGaussianLaw nu p hp) x)
       =ᵐ[nu] bernoulliGaussianKernel p hp) := by
  letI : IsMarkovKernel (bernoulliGaussianKernel p hp) :=
    bernoulliGaussianKernel_isMarkovKernel p hp h0 h1
  letI : IsProbabilityMeasure (jointBernoulliGaussianLaw nu p hp) :=
    jointBernoulliGaussianLaw_isProbabilityMeasure nu p hp h0 h1
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := jointBernoulliGaussianLaw nu p hp) (X := Prod.snd) (Y := Prod.fst)
    measurable_snd measurable_fst (κ := bernoulliGaussianKernel p hp) (by
      rw [jointBernoulliGaussianLaw_map_snd nu p hp h0 h1]
      unfold jointBernoulliGaussianLaw
      rw [Measure.map_map (measurable_snd.prodMk measurable_fst) measurable_swap]
      simp [Function.comp_def])
  rwa [jointBernoulliGaussianLaw_map_snd nu p hp h0 h1] at h

/-- The second moment of a Bernoulli draw plus standard Gaussian noise is
`1+p`. -/
-- @node: bernoulliGaussianLaw_integral_sq
lemma bernoulliGaussianLaw_integral_sq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∫ y, y ^ 2 ∂bernoulliGaussianLaw p = 1 + p := by
  have hg1 : ∫ y, y ^ 2 ∂gaussianReal 1 1 = 1 + (1 : ℝ) ^ 2 := by
    simpa only [sub_zero] using gaussianReal_integral_sq_sub (1 : ℝ) 0
  have hg0 : ∫ y, y ^ 2 ∂gaussianReal 0 1 = 1 + (0 : ℝ) ^ 2 := by
    simpa only [sub_zero] using gaussianReal_integral_sq_sub (0 : ℝ) 0
  rw [bernoulliGaussianLaw_eq_gaussian_mixture, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure, hg1, hg0]
    simp [h0, sub_nonneg.mpr h1]
    ring
  · simpa [Real.norm_eq_abs, sq_abs] using
      ((memLp_id_gaussianReal (μ := (1 : ℝ)) (v := 1) 2).integrable_norm_pow
        (by norm_num : (2 : ℕ) ≠ 0)).smul_measure (by simp)
  · simpa [Real.norm_eq_abs, sq_abs] using
      ((memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).integrable_norm_pow
        (by norm_num : (2 : ℕ) ≠ 0)).smul_measure (by simp)

/-- The outcome coordinate of the explicit joint law is square-integrable. -/
-- @node: jointBernoulliGaussianLaw_memLp_fst_two
lemma jointBernoulliGaussianLaw_memLp_fst_two
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p : Score → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    MemLp Prod.fst 2 (jointBernoulliGaussianLaw nu p hp) := by
  letI : IsMarkovKernel (bernoulliGaussianKernel p hp) :=
    bernoulliGaussianKernel_isMarkovKernel p hp h0 h1
  have hbase : MemLp Prod.snd 2
      (Measure.compProd nu (bernoulliGaussianKernel p hp)) := by
    rw [memLp_two_iff_integrable_sq measurable_snd.aestronglyMeasurable]
    apply (Measure.integrable_compProd_iff (by fun_prop)).2
    constructor
    · filter_upwards with x
      simpa [bernoulliGaussianKernel, Real.norm_eq_abs, sq_abs] using
        (bernoulliGaussianLaw_memLp_id_two (p x)).integrable_norm_pow
          (by norm_num : (2 : ℕ) ≠ 0)
    · have heq : (fun x => ∫ y, ‖y ^ 2‖ ∂bernoulliGaussianKernel p hp x) =
          fun x => 1 + p x := by
        funext x
        simpa [bernoulliGaussianKernel, Real.norm_eq_abs, abs_sq] using
          bernoulliGaussianLaw_integral_sq (h0 x) (h1 x)
      rw [heq]
      have hpLp : MemLp p 1 nu := MemLp.of_bound hp.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using h1 x)
      exact (integrable_const (1 : ℝ)).add (hpLp.integrable (by norm_num))
  have hswap : MeasurePreserving Prod.swap (jointBernoulliGaussianLaw nu p hp)
      (Measure.compProd nu (bernoulliGaussianKernel p hp)) :=
    { measurable := measurable_swap
      map_eq := by
        unfold jointBernoulliGaussianLaw
        rw [Measure.map_map measurable_swap measurable_swap]
        simp [Function.comp_def] }
  simpa [Function.comp_def] using hbase.comp_measurePreserving hswap

/-- The conditional mean is the regression used in the construction. -/
-- @node: jointBernoulliGaussianLaw_condMean
lemma jointBernoulliGaussianLaw_condMean
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p : Score → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    (let _ : IsProbabilityMeasure (jointBernoulliGaussianLaw nu p hp) :=
        jointBernoulliGaussianLaw_isProbabilityMeasure nu p hp h0 h1
     ∀ᵐ x ∂nu, p x = ∫ y, y ∂condDistrib Prod.fst Prod.snd
       (jointBernoulliGaussianLaw nu p hp) x) := by
  filter_upwards [jointBernoulliGaussianLaw_condDistrib nu p hp h0 h1] with x hx
  rw [hx]
  exact (bernoulliGaussianLaw_integral_id (h0 x) (h1 x)).symm

/-- The conditional variance is `1+p(1-p)`. -/
-- @node: jointBernoulliGaussianLaw_condVar
lemma jointBernoulliGaussianLaw_condVar
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p : Score → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    (let _ : IsProbabilityMeasure (jointBernoulliGaussianLaw nu p hp) :=
        jointBernoulliGaussianLaw_isProbabilityMeasure nu p hp h0 h1
     ∀ᵐ x ∂nu, 1 + p x * (1 - p x) = variance id
       (condDistrib Prod.fst Prod.snd (jointBernoulliGaussianLaw nu p hp) x)) := by
  filter_upwards [jointBernoulliGaussianLaw_condDistrib nu p hp h0 h1] with x hx
  rw [hx]
  exact (bernoulliGaussianLaw_variance_id (h0 x) (h1 x)).symm

end CausalSmith.Stat.BddUniformLogPenalty
