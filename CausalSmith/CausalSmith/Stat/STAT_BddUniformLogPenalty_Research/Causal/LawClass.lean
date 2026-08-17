import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EuclideanBallsVC
import Causalean.Stat.Nonparametric.LocalPolynomial.CoordinateDerivative
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# The exact uniformized CTY Assumptions 1--2 class

The ten conjuncts below retain the Euclidean carrier, selected conditional
kernel, open-neighborhood smooth extension, uniform-kernel VC condition, Gram
floor, local mass, and Hausdorff slice requirements of the paper.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Stat.Nonparametric.LocalPolynomial
export Causalean.Stat.Nonparametric.LocalPolynomial
  (coordinateMultiOrder coordinateDirections coordinatePartial)

/-- A compact axis-aligned square contained in `[-L,L]²`. -/
def RectangularScoreSupport (S : Set Score) (L : ℝ) : Prop :=
  ∃ lo hi : ℝ, lo ≤ hi ∧
    S = {x | ∀ i, lo ≤ x i ∧ x i ≤ hi} ∧ S ⊆ scoreCube L

/-- Rectifiability of a specified curve, rather than of a support frontier. -/
def RectifiableCurve (B : Set Score) : Prop :=
  ∃ K : ℝ≥0, ∃ γ : ℝ → Score,
    LipschitzOnWith K γ (Set.Icc (0 : ℝ) 1) ∧
      γ '' Set.Icc (0 : ℝ) 1 = B


/-- Absolute coordinate partials of total order at most `p` on `S`. -/
def coordinatePartialValues (f : Score → ℝ) (p : ℕ) (S : Set Score) : Set ℝ :=
  {r | ∃ alpha : Fin 2 → ℕ, coordinateMultiOrder alpha ≤ p ∧
    ∃ x ∈ S, r = |coordinatePartial f alpha x|}

/-- Coordinate-partial Lipschitz quotients of total order at most `p`. -/
def coordinatePartialLipschitzValues (f : Score → ℝ) (p : ℕ)
    (S : Set Score) : Set ℝ :=
  {r | ∃ alpha : Fin 2 → ℕ, coordinateMultiOrder alpha ≤ p ∧
    ∃ x ∈ S, ∃ z ∈ S, x ≠ z ∧
      r = |coordinatePartial f alpha x - coordinatePartial f alpha z| / ‖x - z‖}

/-- The paper's Euclidean `C^{p+1}`-extension envelope, using exactly the
displayed maxima of scalar coordinate multi-index partial derivatives and
their Lipschitz quotients.  The two bounded-above guards make the real
suprema faithful to those finite displayed maxima. -/
def EuclideanCExtEnvelope (f : Score → ℝ) (p : ℕ) (L : ℝ)
    (S : Set Score) : Prop :=
  ∃ U : Set Score, IsOpen U ∧ S ⊆ U ∧
    ∃ g : Score → ℝ,
      ContDiffOn ℝ (p + 1 : ℕ) g U ∧
      Set.EqOn g f S ∧
      BddAbove (coordinatePartialValues g p S) ∧
      BddAbove (coordinatePartialLipschitzValues g p S) ∧
      sSup (coordinatePartialValues g p S) +
        sSup (coordinatePartialLipschitzValues g p S) ≤ L

/-- The degree-`p` population Gram matrix from the signed-distance design. -/
noncomputable def populationGram (P : A1A2Law) (p : ℕ) (t : Bool)
    (x : Score) (h : ℝ) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun j k => ∫ w,
    h⁻¹ ^ 2 *
      (if (if t then 0 ≤ signedDistance (knownGeometry P) x (causalScore w)
        else signedDistance (knownGeometry P) x (causalScore w) < 0) then 1 else 0) *
      uniformKernel (signedDistance (knownGeometry P) x (causalScore w) / h) *
      polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) j *
      polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k ∂P.law
  -- @realizes \Psi_{t,P,x}(h)(population signed-distance Gram matrix)

/-- Quadratic form of a real square matrix. -/
def matrixQuadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

/-- The quantitative minimum-eigenvalue condition, expressed without a
spectral API. -/
def PopulationGramFloor (P : A1A2Law) (p : ℕ) (L : ℝ) : Prop :=
  ∀ t x h, x ∈ P.boundary → 0 < h → h ≤ L⁻¹ → ∀ v : Fin (p + 1) → ℝ,
    L⁻¹ * ∑ i, (v i) ^ 2 ≤ matrixQuadratic (populationGram P p t x h) v

/-- Lebesgue mass of the arm-`t` uniform-kernel neighborhood. -/
noncomputable def armLocalMass (P : A1A2Law) (t : Bool)
    (x : Score) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in (if t then P.A1 else P.A0),
    ENNReal.ofReal (h⁻¹ ^ 2 *
      uniformKernel (((if t then 1 else -1 : ℝ) * dist z x) / h)) ∂volume

/-- Hausdorff integral of the score density over an armwise distance slice. -/
noncomputable def armSliceDensityMass (P : A1A2Law) (t : Bool)
    (x : Score) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in {z | z ∈ (if t then P.A1 else P.A0) ∧ dist z x = s},
    ENNReal.ofReal (P.density z) ∂Measure.hausdorffMeasure 1

/-- One admissible selected disintegration kernel for a bare causal law.  The
pointwise clauses are properties of this witness, not of the arbitrary kernel
decoration stored in `A1A2Law`. -/
structure A1A2KernelWitness (P : A1A2Law) (ν L : ℝ) where
  condKer : Bool → ProbabilityTheory.Kernel Score ℝ
  condKer_markov : ∀ t, ProbabilityTheory.IsMarkovKernel (condKer t)
  condKer_disint : ∀ t,
    (Measure.map causalScore P.law).compProd (condKer t) =
      Measure.map (fun w => (causalScore w, armCoord t w)) P.law
  mean_eq : ∀ t, ∀ x ∈ P.support,
    P.muPO t x = ∫ y, y ∂condKer t x
  variance_eq : ∀ t, ∀ x ∈ P.support,
    P.sigmaSqPO t x = ProbabilityTheory.variance id (condKer t x)
  moment_le : ∀ t, ∀ x ∈ P.support,
    (∫⁻ y, ENNReal.ofReal (|y| ^ (2 + ν)) ∂condKer t x) ≤ ENNReal.ofReal L

/-- The kernel selected from an existential class-membership certificate. -/
noncomputable def selectedA1A2CondKer (P : A1A2Law) (ν L : ℝ) :
    Bool → ProbabilityTheory.Kernel Score ℝ := by
  classical
  exact if h : Nonempty (A1A2KernelWitness P ν L) then
      (Classical.choice h).condKer
    else P.condKer

/-- Conditional absolute moment computed from the selected class witness. -/
noncomputable def selectedA1A2CondAbsMoment (P : A1A2Law) (ν L : ℝ)
    (t : Bool) (x : Score) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (|y| ^ (2 + ν)) ∂selectedA1A2CondKer P ν L t x

/-- The stated conditional distribution is a Markov kernel: it is a probability law at each input and varies measurably with that input. -/
lemma selectedA1A2CondKer_markov {P : A1A2Law} {ν L : ℝ}
    (h : Nonempty (A1A2KernelWitness P ν L)) (t : Bool) :
    ProbabilityTheory.IsMarkovKernel (selectedA1A2CondKer P ν L t) := by
  simp only [selectedA1A2CondKer, dif_pos h]
  exact (Classical.choice h).condKer_markov t

/-- The selected conditional kernel disintegrates the causal law as stated. -/
lemma selectedA1A2CondKer_disint {P : A1A2Law} {ν L : ℝ}
    (h : Nonempty (A1A2KernelWitness P ν L)) (t : Bool) :
    (Measure.map causalScore P.law).compProd (selectedA1A2CondKer P ν L t) =
      Measure.map (fun w => (causalScore w, armCoord t w)) P.law := by
  simp only [selectedA1A2CondKer, dif_pos h]
  exact (Classical.choice h).condKer_disint t

/-- The two stated constructions agree under the theorem's assumptions. -/
lemma selectedA1A2CondKer_mean_eq {P : A1A2Law} {ν L : ℝ}
    (h : Nonempty (A1A2KernelWitness P ν L)) (t : Bool)
    (x : Score) (hx : x ∈ P.support) :
    P.muPO t x = ∫ y, y ∂selectedA1A2CondKer P ν L t x := by
  simp only [selectedA1A2CondKer, dif_pos h]
  exact (Classical.choice h).mean_eq t x hx

/-- The two stated constructions agree under the theorem's assumptions. -/
lemma selectedA1A2CondKer_variance_eq {P : A1A2Law} {ν L : ℝ}
    (h : Nonempty (A1A2KernelWitness P ν L)) (t : Bool)
    (x : Score) (hx : x ∈ P.support) :
    P.sigmaSqPO t x =
      ProbabilityTheory.variance id (selectedA1A2CondKer P ν L t x) := by
  simp only [selectedA1A2CondKer, dif_pos h]
  exact (Classical.choice h).variance_eq t x hx

/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma selectedA1A2CondAbsMoment_le {P : A1A2Law} {ν L : ℝ}
    (h : Nonempty (A1A2KernelWitness P ν L)) (t : Bool)
    (x : Score) (hx : x ∈ P.support) :
    selectedA1A2CondAbsMoment P ν L t x ≤ ENNReal.ofReal L := by
  simp only [selectedA1A2CondAbsMoment, selectedA1A2CondKer, dif_pos h]
  exact (Classical.choice h).moment_le t x hx

/-- Pointwise conditions on one admissible selected-kernel representative.
In particular, the selected kernel's mean and variance are pinned pointwise
on the support, rather than merely by the a.e. fields of `A1A2Law`. -/
def A1A2ClassWitness (p : ℕ) (ν L : ℝ) (P : A1A2Law) : Prop :=
  2 ≤ ν ∧ -- @realizes \nu(regime ν≥2)
  4 ≤ L ∧ -- @realizes L(regime L≥4)
  RectangularScoreSupport P.support L ∧
    -- @realizes \mathcal{X}_P(rectangular compact support inside [-L,L]²)
  ContinuousOn P.density P.support ∧
  (∀ x ∈ P.support, L⁻¹ ≤ P.density x ∧ P.density x ≤ L) ∧
    -- @realizes f_P(continuous density in [L⁻¹,L])
  (∀ t, EuclideanCExtEnvelope (P.muPO t) p L P.support) ∧
    -- @realizes \mu_{t,P}(C^{p+1} extension and derivative envelope)
  (∀ t, ContinuousOn (P.sigmaSqPO t) P.support ∧
    ∀ x ∈ P.support, L⁻¹ ≤ P.sigmaSqPO t x ∧ P.sigmaSqPO t x ≤ L) ∧
    -- @realizes \sigma^2_{t,P}(continuous variance in [L⁻¹,L])
  (Nonempty (A1A2KernelWitness P ν L) ∧
    ∀ t, ∀ x ∈ P.support,
      P.muPO t x = ∫ y, y ∂selectedA1A2CondKer P ν L t x) ∧
    -- @realizes \mu_{t,P}(pointwise mean of selected conditional law)
  (∀ t, ∀ x ∈ P.support,
    P.sigmaSqPO t x =
      ProbabilityTheory.variance id (selectedA1A2CondKer P ν L t x)) ∧
    -- @realizes \sigma^2_{t,P}(pointwise variance of selected conditional law)
  (∀ t, ∀ x ∈ P.support,
    selectedA1A2CondAbsMoment P ν L t x ≤ ENNReal.ofReal L) ∧
    -- @realizes Y(t)(pointwise conditional (2+ν)-moment at most L)
  (MeasurableSet P.A0 ∧ MeasurableSet P.A1 ∧
    P.A0 ∪ P.A1 = P.support ∧ Disjoint P.A0 P.A1 ∧
    P.boundary = frontier P.A0 ∩ frontier P.A1 ∧
    IsCompact P.boundary ∧ P.boundary ⊆ interior P.support ∧
    RectifiableCurve P.boundary ∧
    ENNReal.ofReal L⁻¹ ≤ Measure.hausdorffMeasure 1 P.boundary ∧
    Measure.hausdorffMeasure 1 P.boundary ≤ ENNReal.ofReal L) ∧
    -- @realizes \mathcal{A}_{t,P}(Borel partition)
    -- @realizes \mathcal{B}_P(compact rectifiable interior common interface with H¹ bounds)
  EuclideanBallsVCProperty ∧
    -- @realizes d_P(Euclidean metric) @realizes K_\square(uniform-kernel VC index ≤4)
  PopulationGramFloor P p L ∧
    -- @realizes \Psi_{t,P,x}(h)(quadratic-form floor L⁻¹)
  (∀ t x h, x ∈ P.boundary → 0 < h → h ≤ L⁻¹ →
    ENNReal.ofReal L⁻¹ ≤ armLocalMass P t x h) ∧
  ∀ t x s, x ∈ P.boundary → 0 < s → s ≤ L⁻¹ →
    0 < armSliceDensityMass P t x s ∧ armSliceDensityMass P t x s < ∞

-- @node: def:cty-a1-a2-class
/-- The exact displayed `L`-uniformized Euclidean-distance, uniform-kernel CTY
Assumptions 1--2 plus Theorem-2-envelope class.  Membership existentially
selects one admissible disintegration kernel and constrains that same witness
pointwise; it does not constrain the arbitrary kernel decoration of `P`. -/
def A1A2Class (p : ℕ) (ν L : ℝ) (P : A1A2Law) : Prop :=
  A1A2ClassWitness p ν L P
  -- @realizes \mathcal{P}_{12}(exact uniformized causal law class)

/-- A pointwise-admissible decorated law belongs to the class. -/
lemma A1A2ClassWitness.toA1A2Class {p : ℕ} {ν L : ℝ} {P : A1A2Law}
    (hP : A1A2ClassWitness p ν L P) : A1A2Class p ν L P := by
  exact hP

/-- The class as a set of causal laws. -/
def admissibleA1A2Laws (p : ℕ) (ν L : ℝ) : Set A1A2Law :=
  {P | A1A2Class p ν L P}

/-- The pointwise selected-kernel moment envelope implies the global armwise
`L^(2+ν)` scope required by conditional-mean and conditional-variance APIs. -/
-- @node: A1A2Law.memLp_armCoord_of_condAbsMoment_le
lemma A1A2Law.memLp_armCoord_of_condAbsMoment_le
    (P : A1A2Law) (p : ℕ) (ν L : ℝ) (hP : A1A2Class p ν L P)
    (t : Bool) :
    MemLp (armCoord t) (ENNReal.ofReal (2 + ν)) P.law := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hK : Nonempty (A1A2KernelWitness P ν L) :=
    hP.2.2.2.2.2.2.2.1.1
  letI : ProbabilityTheory.IsMarkovKernel (selectedA1A2CondKer P ν L t) :=
    selectedA1A2CondKer_markov hK t
  have harm : Measurable (armCoord t) := by
    cases t
    · exact measurable_fst
    · exact measurable_fst.comp measurable_snd
  have hscore : Measurable causalScore := by
    unfold causalScore
    fun_prop
  have hpair : Measurable (fun w => (causalScore w, armCoord t w)) :=
    hscore.prodMk harm
  have hnu : 0 < 2 + ν := by linarith [hP.1]
  have hp0 : ENNReal.ofReal (2 + ν) ≠ 0 := (ENNReal.ofReal_pos.2 hnu).ne'
  have hptop : ENNReal.ofReal (2 + ν) ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨harm.aestronglyMeasurable,
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop).2 ?_⟩
  have hmap : Measure.map (fun w => (causalScore w, armCoord t w)) P.law =
      (Measure.map causalScore P.law).compProd (selectedA1A2CondKer P ν L t) :=
    (selectedA1A2CondKer_disint hK t).symm
  have hmoment : ∀ x ∈ P.support,
      selectedA1A2CondAbsMoment P ν L t x ≤ ENNReal.ofReal L :=
    hP.2.2.2.2.2.2.2.2.2.1 t
  have hsupport : ∀ᵐ x ∂Measure.map causalScore P.law, x ∈ P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  have hinner : ∀ᵐ x ∂Measure.map causalScore P.law,
      (∫⁻ y, ‖y‖ₑ ^ (ENNReal.ofReal (2 + ν)).toReal
        ∂selectedA1A2CondKer P ν L t x) ≤
        ENNReal.ofReal L := by
    filter_upwards [hsupport] with x hx
    have hintegrand (y : ℝ) :
        ‖y‖ₑ ^ (ENNReal.ofReal (2 + ν)).toReal =
          ENNReal.ofReal (|y| ^ (2 + ν)) := by
      rw [ENNReal.toReal_ofReal hnu.le, ← ofReal_norm_eq_enorm,
        Real.norm_eq_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg y) hnu.le]
    simpa only [selectedA1A2CondAbsMoment, hintegrand] using hmoment x hx
  have hfinite : (∫⁻ x, ∫⁻ y,
      ‖y‖ₑ ^ (ENNReal.ofReal (2 + ν)).toReal
        ∂selectedA1A2CondKer P ν L t x
      ∂Measure.map causalScore P.law) < ∞ := by
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal L ∂Measure.map causalScore P.law :=
        lintegral_mono_ae hinner
      _ < ∞ := by
        rw [lintegral_const]
        have huniv : (Measure.map causalScore P.law) Set.univ = 1 := by
          rw [Measure.map_apply_of_aemeasurable hscore.aemeasurable MeasurableSet.univ]
          simp
        rw [huniv, mul_one]
        exact ENNReal.ofReal_lt_top
  rw [← lintegral_map (by fun_prop : Measurable
      (fun z : Score × ℝ => ‖z.2‖ₑ ^ (ENNReal.ofReal (2 + ν)).toReal)) hpair]
  rw [hmap, Measure.lintegral_compProd (by fun_prop)]
  exact hfinite

end CausalSmith.Stat.BddUniformLogPenalty
