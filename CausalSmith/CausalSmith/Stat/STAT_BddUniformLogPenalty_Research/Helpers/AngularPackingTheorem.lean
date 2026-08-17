import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularLaw
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularCellMass
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularLocality
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadial
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialOutcome
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularHolder
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialFibre
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialAssembly
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialKL
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularPackingOnePointKL
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularScaledDelta

/-!
# Angular hard-family certificate

This downstream module states the complete finite packing certificate and its
eventual fixed-constant construction.  Keeping it downstream of `AngularLaw`
lets the assembly use the faithful CTY-law constructor without an import cycle.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The full finite hard-family certificate at sample size `n`, with constants
fixed outside `n`. -/
def AngularPackingAt
    (n q : ℕ) (L c0 c1 cwLow cwHigh cRadial alpha : ℝ) : Prop :=
  ∃ M : ℕ, ∃ w m : ℝ,
  ∃ centers : Fin M → Score,
  ∃ laws : (Fin M → Bool) → CtyLaw,
  ∃ values : Fin M → Bool → ℝ,
    (c0 * Real.rpow (frontierRate n) (-(1 : ℝ) / q) ≤ M) ∧
    (cwLow * Real.rpow (frontierRate n) ((1 : ℝ) / q) ≤ w ∧
      w ≤ cwHigh * Real.rpow (frontierRate n) ((1 : ℝ) / q)) ∧
    (∀ j, centers j ∈ frontier packingSquare) ∧
    (∀ i j, i ≠ j →
      dist (centers i) (centers j) ≥ cwLow * Real.rpow (frontierRate n) ((1 : ℝ) / q)) ∧
    (∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j)) ∧
    (∀ omega, CtyNonparametricClass q L (laws omega)) ∧
    (∀ omega, (laws omega).support = packingSquare) ∧
    (∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m) ∧
    (∀ omega omega' j, omega j = omega' j →
      (laws omega).law.restrict
          {o | o.2 ∈ packingCell centers w j} =
        (laws omega').law.restrict
          {o | o.2 ∈ packingCell centers w j}) ∧
    (∀ omega omega',
      (laws omega).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j} =
        (laws omega').law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j}) ∧
    (∀ omega j,
      (laws omega).mu (centers j) = values j (omega j)) ∧
    (∀ j, |values j true - values j false| ≥ c1 * frontierRate n) ∧
    (∀ omega j,
      Measure.map (fun o : Observation => dist o.2 (centers j)) (laws omega).law =
        Measure.map (fun o : Observation => dist o.2 (centers j))
          (laws (Causalean.Stat.flipBit j omega)).law) ∧
    (∀ omega j,
      (onePointDistanceLaw (laws omega) (centers j)).restrict
          {z | cRadial * frontierRate n ≤ z.2} =
        (onePointDistanceLaw (laws (Causalean.Stat.flipBit j omega))
          (centers j)).restrict {z | cRadial * frontierRate n ≤ z.2}) ∧
    ∀ omega j,
      InformationTheory.klDiv
        (compressedSampleLaw (laws omega) n (centers j))
        (compressedSampleLaw (laws (Causalean.Stat.flipBit j omega)) n (centers j)) ≤
          ENNReal.ofReal (alpha * Real.log M)

/-- The score marginal of a faithful angular packing law assigns each grid
cell exactly its Lebesgue volume, independently of the Boolean vertex. -/
-- @node: angularPackingCtyLaw_cell_mass_eq_volume
lemma angularPackingCtyLaw_cell_mass_eq_volume {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw0 : 0 < w)
    (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    Measure.map Prod.snd
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0
          hw hsep).law
        (packingCell (angularGridCenter M) w j) =
      volume (packingCell (angularGridCenter M) w j) := by
  rw [angularPackingCtyLaw_map_snd]
  simpa [packingCell, packingSquare] using
    angularDesignMeasure_gridCell_eq_volume j hb hscale hcA hdelta hw0 hw hsep omega

/-- All lower-edge grid cells have the same Lebesgue volume.  Translation
along the lower edge carries one closed half-disc exactly onto any other and
preserves planar Lebesgue measure. -/
-- @node: angularGrid_packingCell_volume_eq
lemma angularGrid_packingCell_volume_eq {M : ℕ} (i j : Fin M) {w : ℝ}
    (hw : w ≤ 1 / 4) :
    volume (packingCell (angularGridCenter M) w i) =
      volume (packingCell (angularGridCenter M) w j) := by
  let d : Score := angularGridCenter M j - angularGridCenter M i
  let T : Score → Score := fun x => d + x
  have hT : MeasurableEmbedding T := (Homeomorph.addLeft d).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure Score) volume :=
    measurePreserving_add_left volume d
  have himage : T '' packingCell (angularGridCenter M) w i =
      packingCell (angularGridCenter M) w j := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hw _).mpr
      have hi :=
        (mem_angularGrid_packingCell_iff_closedUpperHalfDisc i hw y).mp hy
      refine ⟨?_, ?_⟩
      · simpa [T, d, scoreCoordinates, angularGridCenter_apply_one] using hi.1
      · rw [show scoreCoordinates (T y) - scoreCoordinates (angularGridCenter M j) =
              scoreCoordinates y - scoreCoordinates (angularGridCenter M i) by
            ext <;> simp [T, d, scoreCoordinates] <;> ring]
        exact hi.2
    · intro hx
      let y : Score := -d + x
      have hy : y ∈ packingCell (angularGridCenter M) w i := by
        apply (mem_angularGrid_packingCell_iff_closedUpperHalfDisc i hw _).mpr
        have hj :=
          (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hw x).mp hx
        refine ⟨?_, ?_⟩
        · simpa [y, d, scoreCoordinates, angularGridCenter_apply_one] using hj.1
        · rw [show scoreCoordinates y - scoreCoordinates (angularGridCenter M i) =
                scoreCoordinates x - scoreCoordinates (angularGridCenter M j) by
              ext <;> simp [y, d, scoreCoordinates] <;> ring]
          exact hj.2
      refine ⟨y, hy, ?_⟩
      simp [T, y]
  have hC : MeasurableSet (packingCell (angularGridCenter M) w i) :=
    Metric.isClosed_closedBall.measurableSet.inter (scoreCube_measurableSet _)
  rw [← himage]
  symm
  calc
    volume (T '' packingCell (angularGridCenter M) w i) =
        Measure.map T volume (T '' packingCell (angularGridCenter M) w i) := by
      rw [hmp.map_eq]
    _ = volume (packingCell (angularGridCenter M) w i) := by
      rw [Measure.map_apply hT.measurable (hT.measurableSet_image' hC),
        hT.injective.preimage_image]

/-- At the selected amplitude, the faithful angular laws take their declared
Boolean values at every grid center, and the two values have the exact fixed
frontier-rate separation. -/
-- @node: angularPackingCtyLaw_center_value_certificate
lemma angularPackingCtyLaw_center_value_certificate {M n : ℕ} (hn : 2 ≤ n)
    {b cA w : ℝ} (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * angularPackingDelta n) (hcA : 8 ≤ cA)
    (hdelta : 0 < angularPackingDelta n)
    (hdeltaSmall : angularPackingDelta n ≤ 1 / 8)
    (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k)) :
    (∀ omega j,
      (angularPackingCtyLaw b cA (angularPackingDelta n) w omega hb hscale hcA
        hdelta hw0 hw hsep).mu (angularGridCenter M j) =
        packingCenterValue b (angularPackingDelta n) (angularGridCenter M) j (omega j)) ∧
      (∀ j,
        |packingCenterValue b (angularPackingDelta n) (angularGridCenter M) j true -
          packingCenterValue b (angularPackingDelta n) (angularGridCenter M) j false| =
            (1 / 1024 : ℝ) * frontierRate n) := by
  constructor
  · intro omega j
    exact angularPackingCtyLaw_mu_center hb hbSmall hscale hcA hdelta
      hdeltaSmall hw0 hw hsep j
  · exact packingCenterValue_frontierRate_separation hn b (angularGridCenter M)

/-- The faithful angular laws satisfy both exact locality clauses appearing in
`AngularPackingAt`: a cell sees only its own bit, while the law off the union
of cells is independent of the entire Boolean vertex. -/
-- @node: angularPackingCtyLaw_locality_certificate
lemma angularPackingCtyLaw_locality_certificate {M : ℕ}
    {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k)) :
    (∀ omega omega' j, omega j = omega' j →
      (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
        hwQuarter hsep).law.restrict
          {o | o.2 ∈ packingCell (angularGridCenter M) w j} =
      (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw
        hwQuarter hsep).law.restrict
          {o | o.2 ∈ packingCell (angularGridCenter M) w j}) ∧
    (∀ omega omega',
      (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
        hwQuarter hsep).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j,
            packingCell (angularGridCenter M) w j} =
      (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw
        hwQuarter hsep).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j,
            packingCell (angularGridCenter M) w j}) := by
  constructor
  · intro omega omega' j hbit
    exact angularPackingCtyLaw_restrict_cell_eq hb hbSmall hscale hcA hdelta
      hdeltaSmall hw hwQuarter hsep hbit
  · intro omega omega'
    exact angularPackingCtyLaw_restrict_off_cells_eq hb hbSmall hscale hcA
      hdelta hdeltaSmall hw hwQuarter hsep omega omega'

/-- Adjacent faithful angular laws have the same complete unsigned-radius
law at the grid center whose bit is changed. -/
-- @node: angularPackingCtyLaw_map_distance_eq
lemma angularPackingCtyLaw_map_distance_eq {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw0 : 0 < w)
    (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega omega' : Fin M → Bool)
    (hother : ∀ k, k ≠ j → omega k = omega' k) :
    Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j))
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0
          hw hsep).law =
      Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j))
        (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw0
          hw hsep).law := by
  let radial : Score → ℝ := fun x => dist x (angularGridCenter M j)
  have hscore := angularDesignMeasure_map_distance_eq j hb hscale hcA hdelta
    hw0 hw hsep omega omega' hother
  calc
    Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j))
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0
          hw hsep).law =
        Measure.map radial (Measure.map Prod.snd
          (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0
            hw hsep).law) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map radial
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega) := by
      rw [angularPackingCtyLaw_map_snd]
    _ = Measure.map radial
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega') := hscore
    _ = Measure.map radial (Measure.map Prod.snd
          (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw0
            hw hsep).law) := by
      rw [angularPackingCtyLaw_map_snd]
    _ = Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j))
        (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw0
          hw hsep).law := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl

/-- Flipping one packing bit preserves the full unsigned-radius law at the
corresponding grid center. -/
-- @node: angularPackingCtyLaw_flip_map_distance_eq
lemma angularPackingCtyLaw_flip_map_distance_eq {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw0 : 0 < w)
    (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j))
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0
          hw hsep).law =
      Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j))
        (angularPackingCtyLaw b cA delta w (Causalean.Stat.flipBit j omega)
          hb hscale hcA hdelta hw0 hw hsep).law := by
  apply angularPackingCtyLaw_map_distance_eq j hb hscale hcA hdelta hw0 hw hsep
    omega (Causalean.Stat.flipBit j omega)
  intro k hkj
  simp [Causalean.Stat.flipBit, hkj]

/-- The derivative-scaling leaves for the normalized bump assemble into the
complete CTY-class certificate for every vertex of the angular family.  This
is the Hölder part of the final packing construction; none of its bounds
depend on the number of cells or on the Boolean vertex. -/
-- @node: angularPackingCtyLaw_mem_nonparametricClass_of_scaling_bounds
lemma angularPackingCtyLaw_mem_nonparametricClass_of_scaling_bounds
    {M q : ℕ} {L b cA delta w : ℝ}
    (hq : 1 ≤ q) (hL : 4 ≤ L)
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscalePos : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (C : ℕ → ℝ)
    (hC0 : ∀ j, 0 ≤ C j)
    (hC : ∀ j z, ‖iteratedFDeriv ℝ j packingBump z‖ ≤ C j)
    (hscale : ∀ j, j ≤ q → |delta| * (w⁻¹) ^ j * C j ≤ 1) :
    ∀ omega : Fin M → Bool,
      CtyNonparametricClass q L
        (angularPackingCtyLaw b cA delta w omega hb hscalePos hcA hdelta hw
          hwQuarter hsep) := by
  intro omega
  apply angularPackingCtyLaw_mem_nonparametricClass_of_holder omega hq hL hb
    hbSmall hscalePos hcA hdelta hdeltaSmall hw hwQuarter hsep
  simpa [packingSquare] using
    clippedPackingRegression_mem_holder_of_scaling_bounds hq hL hbSmall
      hdelta.le hdeltaSmall hw hsep omega C hC0 hC hscale

/-- The radial-cancellation and disintegration leaves jointly give the common
radius marginal and explicit radial fibre representations for both endpoints
of every adjacent edge of the Boolean hypercube. -/
-- @node: angularPackingCtyLaw_radial_representation_certificate
lemma angularPackingCtyLaw_radial_representation_certificate
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    let P := angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
      hwQuarter hsep
    let omega' := Causalean.Stat.flipBit j omega
    let P' := angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw
      hwQuarter hsep
    Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j)) P.law =
        Measure.map (fun o : Observation => dist o.2 (angularGridCenter M j)) P'.law ∧
      onePointDistanceLaw P (angularGridCenter M j) =
        Measure.map
          (fun z : Score × ℝ => (z.2, dist z.1 (angularGridCenter M j)))
          (Measure.compProd
            (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
            (bernoulliGaussianKernel
              (clippedPackingRegression b delta w (angularGridCenter M) omega)
              (clippedPackingRegression_measurable b delta w
                (angularGridCenter M) omega))) ∧
      onePointDistanceLaw P' (angularGridCenter M j) =
        Measure.map
          (fun z : Score × ℝ => (z.2, dist z.1 (angularGridCenter M j)))
          (Measure.compProd
            (angularDesignMeasure b cA delta w (angularGridCenter M) omega')
            (bernoulliGaussianKernel
              (clippedPackingRegression b delta w (angularGridCenter M) omega')
              (clippedPackingRegression_measurable b delta w
                (angularGridCenter M) omega'))) := by
  dsimp only
  constructor
  · exact angularPackingCtyLaw_flip_map_distance_eq j hb hscale hcA hdelta hw
      hwQuarter hsep omega
  constructor
  · exact angularPackingCtyLaw_onePointDistanceLaw_eq_map_compProd hb hscale
      hcA hdelta hw hwQuarter hsep omega (angularGridCenter M j)
  · exact angularPackingCtyLaw_onePointDistanceLaw_eq_map_compProd hb hscale
      hcA hdelta hw hwQuarter hsep (Causalean.Stat.flipBit j omega)
        (angularGridCenter M j)

/-- The two Boolean regression values at a packing center have exactly the
smoothness-normalized frontier-rate separation. -/
-- @node: packingCenterValue_scaledDelta_separation
lemma packingCenterValue_scaledDelta_separation {M n q : ℕ}
    (hn : 2 ≤ n) (centers : Fin M → Score) (j : Fin M) :
    |packingCenterValue (1 / 8) (angularPackingScaledDelta q n) centers j true -
        packingCenterValue (1 / 8) (angularPackingScaledDelta q n) centers j false| =
      (1 / (1024 * packingBumpDerivativeScale q)) * frontierRate n := by
  rw [packingCenterValue_true_false]
  · exact angularPackingScaledDelta_eq_scale_mul_frontierRate q n
  · unfold angularPackingScaledDelta
    exact div_nonneg (frontierRate_pos hn).le
      (mul_nonneg (by norm_num) (packingBumpDerivativeScale_pos q).le)

/-- For an admissible sample size, the normalized amplitude and frontier-rate
bandwidth satisfy every derivative scaling inequality through order `q`. -/
-- @node: angularPackingScaledDelta_derivative_scaling
lemma angularPackingScaledDelta_derivative_scaling (n q : ℕ)
    (hq : 1 ≤ q) (hn : 2 ≤ n) (hrate : frontierRate n ≤ 1) :
    ∀ j, j ≤ q →
      |angularPackingScaledDelta q n| *
          ((angularGridRadius n q)⁻¹) ^ j * packingBumpDerivativeBound j ≤ 1 := by
  intro j hjq
  let r := frontierRate n
  let w := angularGridRadius n q
  let K := 1024 * packingBumpDerivativeScale q
  have hr0 : 0 < r := frontierRate_pos hn
  have hK0 : 0 < K := by
    dsimp [K]
    exact mul_pos (by norm_num) (packingBumpDerivativeScale_pos q)
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr0 _
  have hexp0 : 0 ≤ (1 : ℝ) / q := by positivity
  have hw1 : w ≤ 1 := by
    exact Real.rpow_le_one hr0.le hrate hexp0
  have hwq : w ^ q = r := by
    dsimp [w, angularGridRadius, r]
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow hr0.le (show q ≠ 0 by omega))
  have hpows : w ^ q ≤ w ^ j :=
    pow_le_pow_of_le_one hw0.le hw1 hjq
  have hradial : r * (w⁻¹) ^ j ≤ 1 := by
    rw [inv_pow, ← hwq]
    simpa [div_eq_mul_inv] using (div_le_one (pow_pos hw0 j)).2 hpows
  have hfrac0 : 0 ≤ packingBumpDerivativeBound j / K :=
    div_nonneg (packingBumpDerivativeBound_nonneg j) hK0.le
  have hfrac1 : packingBumpDerivativeBound j / K ≤ 1 :=
    (div_le_one hK0).2 (by
      have hscale0 := (packingBumpDerivativeScale_pos q).le
      have hj := packingBumpDerivativeBound_le_scale hjq
      dsimp [K]
      nlinarith)
  have hmul := mul_le_one₀ hradial hfrac0 hfrac1
  have hdelta : |angularPackingScaledDelta q n| = r / K := by
    change |r / K| = r / K
    exact abs_of_pos (div_pos hr0 hK0)
  rw [hdelta]
  calc
    (r / K) * w⁻¹ ^ j * packingBumpDerivativeBound j =
        (r * w⁻¹ ^ j) * (packingBumpDerivativeBound j / K) := by ring
    _ ≤ 1 := hmul

/-- The smoothness-normalized amplitude turns the derivative/scaling leaves
into the complete Hölder-class certificate for an angular packing vertex. -/
-- @node: angularPackingCtyLaw_mem_class_scaledDelta
lemma angularPackingCtyLaw_mem_class_scaledDelta
    {M n q : ℕ} {L : ℝ} (hq : 1 ≤ q) (hL : 4 ≤ L) (hn : 2 ≤ n)
    (hrate : frontierRate n ≤ 1)
    (hdelta : 0 < angularPackingScaledDelta q n)
    (hdeltaSmall : angularPackingScaledDelta q n ≤ 1 / 8)
    (hw : 0 < angularGridRadius n q)
    (hwQuarter : angularGridRadius n q ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * angularGridRadius n q ≤
        dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    CtyNonparametricClass q L
      (angularPackingCtyLaw (1 / 8) 8 (angularPackingScaledDelta q n)
        (angularGridRadius n q) omega (by norm_num)
        (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw hwQuarter hsep) := by
  apply angularPackingCtyLaw_mem_nonparametricClass_of_scaling_bounds hq hL
    (by norm_num) (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num)
    hdelta hdeltaSmall hw hwQuarter hsep packingBumpDerivativeBound
    packingBumpDerivativeBound_nonneg
    packingBump_iteratedFDeriv_le_derivativeBound
  exact angularPackingScaledDelta_derivative_scaling n q hq hn hrate

/-- Eventually the smoothness-normalized amplitude is positive, stays inside
the regression envelope, and its complete angular-cancellation radius lies
inside the frontier-rate cell bandwidth. -/
-- @node: angularPackingScaledDelta_eventually_admissible
lemma angularPackingScaledDelta_eventually_admissible (q : ℕ) (hq : 1 ≤ q) :
    ∀ᶠ n in atTop,
      2 ≤ n ∧ frontierRate n ≤ 1 ∧
      0 < angularPackingScaledDelta q n ∧
      angularPackingScaledDelta q n ≤ 1 / 8 ∧
      2 * (8 * angularPackingScaledDelta q n) ≤
        (1 / 8 : ℝ) * angularGridRadius n q := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), frontierRate_eventually_le_one]
    with n hn hrate
  have hr0 : 0 < frontierRate n := frontierRate_pos hn
  have hK0 : 0 < packingBumpDerivativeScale q := packingBumpDerivativeScale_pos q
  have hK1 : 1 ≤ packingBumpDerivativeScale q := by
    unfold packingBumpDerivativeScale
    have hsum : 0 ≤ ∑ j ∈ Finset.range (q + 1), packingBumpDerivativeBound j :=
      Finset.sum_nonneg fun j _ => packingBumpDerivativeBound_nonneg j
    linarith
  have hrw : frontierRate n ≤ angularGridRadius n q :=
    frontierRate_le_angularGridRadius n q hq hn hrate
  have hdelta : angularPackingScaledDelta q n =
      frontierRate n / (1024 * packingBumpDerivativeScale q) := rfl
  refine ⟨hn, hrate, ?_, ?_, ?_⟩
  · rw [hdelta]
    positivity
  · rw [hdelta]
    apply (div_le_iff₀ (by positivity : 0 < 1024 * packingBumpDerivativeScale q)).2
    nlinarith
  · rw [hdelta]
    rw [show 2 * (8 * (frontierRate n /
        (1024 * packingBumpDerivativeScale q))) =
        frontierRate n / (64 * packingBumpDerivativeScale q) by ring]
    apply (div_le_iff₀
      (by positivity : 0 < 64 * packingBumpDerivativeScale q)).2
    calc
      frontierRate n ≤ angularGridRadius n q := hrw
      _ ≤ (1 / 8 : ℝ) * angularGridRadius n q *
          (64 * packingBumpDerivativeScale q) := by
        have hw0 : 0 ≤ angularGridRadius n q := (lt_of_lt_of_le hr0 hrw).le
        have hmul := mul_le_mul_of_nonneg_left hK1 hw0
        nlinarith

/-- Every radius beyond one eighth of the frontier rate lies in the region
where the angular cutoff is fully active for the smoothness-normalized
amplitude.  This is the numerical bridge used by radial outcome cancellation. -/
-- @node: angularPackingScaledDelta_cutoff_fully_active
lemma angularPackingScaledDelta_cutoff_fully_active {q n : ℕ} {r : ℝ}
    (hn : 2 ≤ n) (hr : (1 / 8 : ℝ) * frontierRate n ≤ r) :
    2 * (8 * angularPackingScaledDelta q n) ≤ (1 / 8 : ℝ) * r := by
  have hscale : 1 ≤ packingBumpDerivativeScale q := by
    unfold packingBumpDerivativeScale
    have hsum : 0 ≤ ∑ j ∈ Finset.range (q + 1), packingBumpDerivativeBound j :=
      Finset.sum_nonneg fun j _ => packingBumpDerivativeBound_nonneg j
    linarith
  have hrate0 : 0 ≤ frontierRate n := (frontierRate_pos hn).le
  rw [angularPackingScaledDelta]
  rw [show 2 * (8 * (frontierRate n /
      (1024 * packingBumpDerivativeScale q))) =
      frontierRate n / (64 * packingBumpDerivativeScale q) by ring]
  apply (div_le_iff₀
    (by positivity : 0 < 64 * packingBumpDerivativeScale q)).2
  have hr0 : 0 ≤ r := by nlinarith
  have hrs : r ≤ r * packingBumpDerivativeScale q := by
    simpa using mul_le_mul_of_nonneg_left hscale hr0
  nlinarith [hr, hrs]

/-- On every measurable tail beginning at one eighth of the frontier rate,
the scaled angular cutoff is fully active.  This is the exact quantified form
needed by the radial-slice cancellation argument. -/
-- @node: angularPackingScaledDelta_cutoff_active_on_tail
lemma angularPackingScaledDelta_cutoff_active_on_tail {q n : ℕ} (hn : 2 ≤ n)
    {A : Set ℝ} (hA : A ⊆ Set.Ici ((1 / 8 : ℝ) * frontierRate n)) :
    ∀ r ∈ A,
      2 * (8 * angularPackingScaledDelta q n) ≤ (1 / 8 : ℝ) * r := by
  intro r hr
  exact angularPackingScaledDelta_cutoff_fully_active hn (hA hr)

/-- Assembly interface for the final angular certificate.  It isolates the
three genuinely radial obligations (common cell mass, equality off the active
radius, and compressed KL) from the already-closed geometry, class, locality,
and center-value parts of the construction. -/
-- @node: angularPackingAt_of_certificates
lemma angularPackingAt_of_certificates
    {n q M : ℕ} {L c0 c1 cwLow cwHigh cRadial alpha w m : ℝ}
    {centers : Fin M → Score} {laws : (Fin M → Bool) → CtyLaw}
    {values : Fin M → Bool → ℝ}
    (hM : c0 * Real.rpow (frontierRate n) (-(1 : ℝ) / q) ≤ M)
    (hw : cwLow * Real.rpow (frontierRate n) ((1 : ℝ) / q) ≤ w ∧
      w ≤ cwHigh * Real.rpow (frontierRate n) ((1 : ℝ) / q))
    (hcenters : ∀ j, centers j ∈ frontier packingSquare)
    (hsep : ∀ i j, i ≠ j →
      dist (centers i) (centers j) ≥
        cwLow * Real.rpow (frontierRate n) ((1 : ℝ) / q))
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (hclass : ∀ omega, CtyNonparametricClass q L (laws omega))
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (hcell : ∀ omega omega' j, omega j = omega' j →
      (laws omega).law.restrict {o | o.2 ∈ packingCell centers w j} =
        (laws omega').law.restrict {o | o.2 ∈ packingCell centers w j})
    (hoff : ∀ omega omega',
      (laws omega).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j} =
        (laws omega').law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j})
    (hvalue : ∀ omega j, (laws omega).mu (centers j) = values j (omega j))
    (hvalueSep : ∀ j,
      |values j true - values j false| ≥ c1 * frontierRate n)
    (hradius : ∀ omega j,
      Measure.map (fun o : Observation => dist o.2 (centers j)) (laws omega).law =
        Measure.map (fun o : Observation => dist o.2 (centers j))
          (laws (Causalean.Stat.flipBit j omega)).law)
    (houtside : ∀ omega j,
      (onePointDistanceLaw (laws omega) (centers j)).restrict
          {z | cRadial * frontierRate n ≤ z.2} =
        (onePointDistanceLaw (laws (Causalean.Stat.flipBit j omega))
          (centers j)).restrict {z | cRadial * frontierRate n ≤ z.2})
    (hkl : ∀ omega j,
      InformationTheory.klDiv
        (compressedSampleLaw (laws omega) n (centers j))
        (compressedSampleLaw (laws (Causalean.Stat.flipBit j omega)) n
          (centers j)) ≤ ENNReal.ofReal (alpha * Real.log M)) :
    AngularPackingAt n q L c0 c1 cwLow cwHigh cRadial alpha := by
  exact ⟨M, w, m, centers, laws, values, hM, hw, hcenters, hsep, hdisjoint,
    hclass, hsupport, hmass, hcell, hoff, hvalue, hvalueSep, hradius, houtside,
    hkl⟩

/-- At the smoothness-normalized amplitude, the already-proved geometric,
Hölder, locality, support, center-value, and radial-marginal leaves reduce the
full angular packing certificate to its three remaining radial estimates. -/
-- @node: angularPackingAt_scaledDelta_of_radial_certificates
lemma angularPackingAt_scaledDelta_of_radial_certificates
    {n q : ℕ} {L cRadial alpha : ℝ}
    (hq : 1 ≤ q) (hL : 4 ≤ L) (hn : 2 ≤ n)
    (hrate : frontierRate n ≤ 1)
    (hsmall : angularGridRadius n q ≤ 1 / 24)
    (hdelta : 0 < angularPackingScaledDelta q n)
    (hdeltaSmall : angularPackingScaledDelta q n ≤ 1 / 8)
    (houtside : ∀ omega j,
      (onePointDistanceLaw
          (angularPackingCtyLaw (1 / 8) 8 (angularPackingScaledDelta q n)
            (angularGridRadius n q) omega (by norm_num)
            (mul_pos (by norm_num) hdelta) (by norm_num) hdelta
            (Real.rpow_pos_of_pos (frontierRate_pos hn) _)
            (by linarith) (fun i k hik =>
              (angularGridSize_geometry (angularGridRadius n q)
                (Real.rpow_pos_of_pos (frontierRate_pos hn) _) hsmall).2.2 i k hik |>.1))
          (angularGridCenter (angularGridSize (angularGridRadius n q)) j)).restrict
          {z | cRadial * frontierRate n ≤ z.2} =
        (onePointDistanceLaw
          (angularPackingCtyLaw (1 / 8) 8 (angularPackingScaledDelta q n)
            (angularGridRadius n q) (Causalean.Stat.flipBit j omega) (by norm_num)
            (mul_pos (by norm_num) hdelta) (by norm_num) hdelta
            (Real.rpow_pos_of_pos (frontierRate_pos hn) _)
            (by linarith) (fun i k hik =>
              (angularGridSize_geometry (angularGridRadius n q)
                (Real.rpow_pos_of_pos (frontierRate_pos hn) _) hsmall).2.2 i k hik |>.1))
          (angularGridCenter (angularGridSize (angularGridRadius n q)) j)).restrict
          {z | cRadial * frontierRate n ≤ z.2})
    (hkl : ∀ omega j,
      InformationTheory.klDiv
        (compressedSampleLaw
          (angularPackingCtyLaw (1 / 8) 8 (angularPackingScaledDelta q n)
            (angularGridRadius n q) omega (by norm_num)
            (mul_pos (by norm_num) hdelta) (by norm_num) hdelta
            (Real.rpow_pos_of_pos (frontierRate_pos hn) _)
            (by linarith) (fun i k hik =>
              (angularGridSize_geometry (angularGridRadius n q)
                (Real.rpow_pos_of_pos (frontierRate_pos hn) _) hsmall).2.2 i k hik |>.1))
          n (angularGridCenter (angularGridSize (angularGridRadius n q)) j))
        (compressedSampleLaw
          (angularPackingCtyLaw (1 / 8) 8 (angularPackingScaledDelta q n)
            (angularGridRadius n q) (Causalean.Stat.flipBit j omega) (by norm_num)
            (mul_pos (by norm_num) hdelta) (by norm_num) hdelta
            (Real.rpow_pos_of_pos (frontierRate_pos hn) _)
            (by linarith) (fun i k hik =>
              (angularGridSize_geometry (angularGridRadius n q)
                (Real.rpow_pos_of_pos (frontierRate_pos hn) _) hsmall).2.2 i k hik |>.1))
          n (angularGridCenter (angularGridSize (angularGridRadius n q)) j)) ≤
        ENNReal.ofReal
          (alpha * Real.log (angularGridSize (angularGridRadius n q)))) :
    AngularPackingAt n q L (1 / 24)
      (1 / (1024 * packingBumpDerivativeScale q)) 1 1 cRadial alpha := by
  let w := angularGridRadius n q
  let M := angularGridSize w
  have hw0 : 0 < w := Real.rpow_pos_of_pos (frontierRate_pos hn) _
  have hgeometry := angularGridSize_geometry w hw0 hsmall
  have hsep3 : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k) :=
    fun i k hik => (hgeometry.2.2 i k hik).1
  have hMpos : 0 < M := by
    have hleft : 0 < (1 / (24 * w) : ℝ) := by positivity
    have hcast : (0 : ℝ) < M := lt_of_lt_of_le hleft hgeometry.1
    exact_mod_cast hcast
  let j0 : Fin M := ⟨0, hMpos⟩
  let m : ℝ :=
    (volume (packingCell (angularGridCenter M) w j0)).toReal
  let laws : (Fin M → Bool) → CtyLaw := fun omega =>
    angularPackingCtyLaw (1 / 8) 8 (angularPackingScaledDelta q n) w omega
      (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw0
      (by linarith) hsep3
  let values : Fin M → Bool → ℝ :=
    packingCenterValue (1 / 8) (angularPackingScaledDelta q n)
      (angularGridCenter M)
  apply angularPackingAt_of_certificates (M := M) (w := w) (m := m)
    (centers := angularGridCenter M) (laws := laws) (values := values)
  · simpa [w, M] using angularGridSize_frontier_lower n q hn hsmall
  · simp [w, angularGridRadius]
  · exact fun j => angularGridCenter_mem_packingSquare_frontier M j
  · intro i j hij
    have hij' := hsep3 i j hij
    rw [one_mul]
    change angularGridRadius n q ≤
      dist (angularGridCenter M i) (angularGridCenter M j)
    change 3 * angularGridRadius n q ≤
      dist (angularGridCenter M i) (angularGridCenter M j) at hij'
    have hw0' : 0 < angularGridRadius n q := by simpa [w] using hw0
    linarith
  · exact fun i j hij => hgeometry.2.2 i j hij |>.2
  · intro omega
    exact angularPackingCtyLaw_mem_class_scaledDelta hq hL hn hrate hdelta
      hdeltaSmall hw0 (by linarith) hsep3 omega
  · intro omega
    dsimp [laws]
    exact angularPackingCtyLaw_support (1 / 8) 8
      (angularPackingScaledDelta q n) w omega (by norm_num)
      (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw0 (by linarith)
      hsep3
  · intro omega j
    dsimp [laws]
    rw [angularPackingCtyLaw_cell_mass_eq_volume j (by norm_num)
      (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw0 (by linarith)
      hsep3 omega]
    rw [angularGrid_packingCell_volume_eq j j0 (by linarith)]
    exact (ENNReal.ofReal_toReal
      (((isCompact_closedBall (angularGridCenter M j0) w).inter_right
        packingScoreCube_isCompact.isClosed).measure_lt_top.ne)).symm
  · exact (angularPackingCtyLaw_locality_certificate (M := M)
      (by norm_num) (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num)
      hdelta hdeltaSmall hw0 (by linarith) hsep3).1
  · exact (angularPackingCtyLaw_locality_certificate (M := M)
      (by norm_num) (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num)
      hdelta hdeltaSmall hw0 (by linarith) hsep3).2
  · intro omega j
    exact angularPackingCtyLaw_mu_center (by norm_num) (by norm_num)
      (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hdeltaSmall hw0
      (by linarith) hsep3 j
  · intro j
    rw [packingCenterValue_scaledDelta_separation hn (angularGridCenter M) j]
  · exact fun omega j => angularPackingCtyLaw_flip_map_distance_eq j
      (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw0
      (by linarith) hsep3 omega
  · simpa [laws, w, M] using houtside
  · simpa [laws, w, M] using hkl

-- @node: lem:cty-support-boundary-angular-packing
/-- For every admissible smoothness order and envelope, fixed positive constants
and a fixed `α < 1/8` yield the CTY square-support angular hard family for all
sufficiently large sample sizes. -/
lemma cty_support_boundary_angular_packing :
    ∀ q : ℕ, ∀ L : ℝ, 1 ≤ q → 4 ≤ L →
    ∃ c0 c1 cwLow cwHigh cRadial alpha : ℝ,
      0 < c0 ∧ 0 < c1 ∧ 0 < cwLow ∧ 0 < cwHigh ∧ 0 < cRadial ∧
      0 < alpha ∧ alpha < 1 / 8 ∧
      ∃ N : ℕ, ∀ n ≥ N,
        AngularPackingAt n q L c0 c1 cwLow cwHigh cRadial alpha := by
  intro q L hq hL
  refine ⟨1 / 24, 1 / (1024 * packingBumpDerivativeScale q), 1, 1,
    1 / 8, 1 / 16, by norm_num, ?_, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  · exact div_pos (by norm_num)
      (mul_pos (by norm_num) (packingBumpDerivativeScale_pos q))
  have hsum : 0 ≤ ∑ j ∈ Finset.range (q + 1), packingBumpDerivativeBound j :=
    Finset.sum_nonneg fun j _ => packingBumpDerivativeBound_nonneg j
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hqle : (q : ℝ) ≤ packingBumpDerivativeScale q := by
    unfold packingBumpDerivativeScale
    linarith
  have hCle : angularPackingOnePointKLConstant ≤ packingBumpDerivativeScale q := by
    unfold angularPackingOnePointKLConstant packingBumpDerivativeScale
    linarith
  have hS0 : 0 ≤ packingBumpDerivativeScale q :=
    (packingBumpDerivativeScale_pos q).le
  have hprod : (q : ℝ) * angularPackingOnePointKLConstant ≤
      packingBumpDerivativeScale q ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hqle hCle
      (by unfold angularPackingOnePointKLConstant; norm_num) hS0
  have hS1 : 1 ≤ packingBumpDerivativeScale q := by
    unfold packingBumpDerivativeScale
    linarith
  have hSsq1 : 1 ≤ packingBumpDerivativeScale q ^ 2 := by nlinarith
  have hCbudget : 256 * (q : ℝ) * angularPackingOnePointKLConstant ≤
      (1024 * packingBumpDerivativeScale q) ^ 4 := by
    calc
      256 * (q : ℝ) * angularPackingOnePointKLConstant ≤
          256 * packingBumpDerivativeScale q ^ 2 := by nlinarith
      _ ≤ (1024 * packingBumpDerivativeScale q) ^ 4 := by
        nlinarith [sq_nonneg (packingBumpDerivativeScale q ^ 2 - 1)]
  have hcert : ∀ᶠ n in atTop,
      AngularPackingAt n q L (1 / 24)
        (1 / (1024 * packingBumpDerivativeScale q)) 1 1 (1 / 8) (1 / 16) := by
    filter_upwards [angularGridRadius_eventually_small q hq,
      angularPackingScaledDelta_eventually_admissible q hq,
      angularPackingScaledDelta_eventually_klBudget q hq
        angularPackingOnePointKLConstant hCbudget] with n hgrid hadm hbudget
    apply angularPackingAt_scaledDelta_of_radial_certificates hq hL hadm.1
      hadm.2.1 hgrid.2 hadm.2.2.1 hadm.2.2.2.1
    · intro omega j
      apply angularPackingCtyLaw_flip_restrict_Ici_eq_of_active j
        (by norm_num) (by norm_num) (mul_pos (by norm_num) hadm.2.2.1)
        (by norm_num) hadm.2.2.1 hadm.2.2.2.1
        hgrid.1 (by linarith)
        (fun i k hik =>
          (angularGridSize_geometry (angularGridRadius n q) hgrid.1 hgrid.2).2.2
            i k hik |>.1)
      intro r hr
      exact angularPackingScaledDelta_cutoff_fully_active hadm.1 hr
    · intro omega j
      let M := angularGridSize (angularGridRadius n q)
      let delta := angularPackingScaledDelta q n
      let w := angularGridRadius n q
      let P := angularPackingCtyLaw (1 / 8) 8 delta w omega (by norm_num)
        (mul_pos (by norm_num) hadm.2.2.1) (by norm_num) hadm.2.2.1
        hgrid.1 (by linarith)
        (fun i k hik =>
          (angularGridSize_geometry w hgrid.1 hgrid.2).2.2 i k hik |>.1)
      let P' := angularPackingCtyLaw (1 / 8) 8 delta w
        (Causalean.Stat.flipBit j omega) (by norm_num)
        (mul_pos (by norm_num) hadm.2.2.1) (by norm_num) hadm.2.2.1
        hgrid.1 (by linarith)
        (fun i k hik =>
          (angularGridSize_geometry w hgrid.1 hgrid.2).2.2 i k hik |>.1)
      have hrepr := angularPackingCtyLaw_radial_representation_certificate
        (M := M) (b := (1 / 8 : ℝ)) (cA := 8) (delta := delta) (w := w) j
        (by norm_num) (mul_pos (by norm_num) hadm.2.2.1) (by norm_num)
        hadm.2.2.1 hgrid.1 (by linarith)
        (fun i k hik =>
          (angularGridSize_geometry w hgrid.1 hgrid.2).2.2 i k hik |>.1) omega
      have hone : InformationTheory.klDiv
          (onePointDistanceLaw P (angularGridCenter M j))
          (onePointDistanceLaw P' (angularGridCenter M j)) ≤
          ENNReal.ofReal (angularPackingOnePointKLConstant * delta ^ 4) := by
        dsimp [P, P', M, delta, w]
        rw [hrepr.2.1, hrepr.2.2]
        exact angularPacking_radialOutcome_klDiv_le j hadm.2.2.1
          hadm.2.2.2.1 hgrid.1 (by linarith)
          (fun i k hik =>
            (angularGridSize_geometry (angularGridRadius n q) hgrid.1
              hgrid.2).2.2 i k hik |>.1) omega
      have htensor := compressedSampleLaw_klDiv_le_of_onePoint_finite_bound
        P P' n (angularGridCenter M j)
        (B := angularPackingOnePointKLConstant * delta ^ 4)
        (mul_nonneg (by unfold angularPackingOnePointKLConstant; norm_num)
          (by positivity)) hone
      exact htensor.trans (ENNReal.ofReal_le_ofReal (by
        dsimp [delta, M]
        exact hbudget hgrid.2))
  exact Filter.eventually_atTop.1 hcert

end CausalSmith.Stat.BddUniformLogPenalty
