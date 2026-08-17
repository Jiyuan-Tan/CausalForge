import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedOutside

/-!
# Normalized signed hard-cell certificate

This module chooses canonical bit representatives and transfers the raw
signed-observation localization results to normalized conditional cell laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The canonical hypercube vertex representing one cell bit. -/
-- @node: causalHardCellBitRepresentative
def causalHardCellBitRepresentative {M : ℕ} (j : Fin M) (bit : Bool) :
    Fin M → Bool := fun k => if k = j then bit else false

/-- The canonical normalized signed-observation law for a cell bit. -/
-- @node: causalHardCellBitObservationLaw
noncomputable def causalHardCellBitObservationLaw {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare)
    (j : Fin M) (bit : Bool) : Measure (ℝ × ℝ) :=
  causalHardCellSignedObservationLaw
    (causalHardA1A2Law b cA delta w centers
      (causalHardCellBitRepresentative j bit) hb hscale hcA hdelta hw hsep hcell)
    (centers j) w

-- @node: causalHardCellBitObservationLaw_isProbabilityMeasure
/-- The stated experiment law has total mass one and therefore defines a probability distribution. -/
instance causalHardCellBitObservationLaw_isProbabilityMeasure {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare)
    (j : Fin M) (bit : Bool) :
    IsProbabilityMeasure (causalHardCellBitObservationLaw b cA delta w centers
      hb hscale hcA hdelta hw hsep hcell j bit) := by
  unfold causalHardCellBitObservationLaw
  infer_instance

/-- Every raw cell observation measure is the common cell mass times the
canonical normalized law selected by that vertex's cell bit. -/
-- @node: causalHardCellSignedObservationMeasure_eq_bitLaw
lemma causalHardCellSignedObservationMeasure_eq_bitLaw {M : ℕ}
    (j : Fin M) (b cA delta w : ℝ) (centers : Fin M → Score)
    (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    causalHardCellSignedObservationMeasure
        (causalHardA1A2Law b cA delta w centers omega hb hscale hcA
          hdelta hw hsep hcell) (centers j) w =
      ENNReal.ofReal (Real.pi * w ^ 2 / 36) •
        causalHardCellBitObservationLaw b cA delta w centers hb hscale hcA
          hdelta hw hsep hcell j (omega j) := by
  have hbit : omega j = causalHardCellBitRepresentative j (omega j) j := by
    simp [causalHardCellBitRepresentative]
  have hlaw := causalHardCellSignedObservationLaw_eq_of_bit_eq
    j b cA delta w centers omega (causalHardCellBitRepresentative j (omega j))
    hb hscale hcA hdelta hw hsep hcell hbit
  have hmass := causalHardA1A2Law_cell_mass j b cA delta w centers omega hb
    hscale hcA hdelta hw hsep hcell
  rw [causalHardCellSignedObservationMeasure_eq_mass_smul_law _ _ _ _
    (by positivity) hmass]
  rw [hlaw]
  rfl

/-- The second marginal of a raw signed observation is its restricted
signed-statistic marginal. -/
-- @node: causalHardCellSignedObservationMeasure_map_snd
lemma causalHardCellSignedObservationMeasure_map_snd {M : ℕ}
    (j : Fin M) (b cA delta w : ℝ) (centers : Fin M → Score)
    (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    Measure.map Prod.snd
        (causalHardCellSignedObservationMeasure
          (causalHardA1A2Law b cA delta w centers omega hb hscale hcA
            hdelta hw hsep hcell) (centers j) w) =
      Measure.map (causalHardSignedStatistic (centers j))
        ((causalHardScoreMeasure b cA delta w centers omega).restrict
          (causalHardCell (centers j) w)) := by
  let nu := (causalHardScoreMeasure b cA delta w centers omega).restrict
    (causalHardCell (centers j) w)
  let p := causalHardObservedSuccessProfile delta w centers omega
  letI : IsProbabilityMeasure
      (causalHardScoreMeasure b cA delta w centers omega) :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega hb hscale hcA
      hdelta hw hsep hcell
  letI : IsFiniteMeasure nu := by dsimp [nu]; infer_instance
  have hp := causalHardObservedSuccessProfile_measurable delta w centers omega
  have hpunit : ∀ x, 0 ≤ p x ∧ p x ≤ 1 := by
    intro x
    have hprof := causalHardProfiles_mem_unitInterval delta w centers omega x
    dsimp [p, causalHardObservedSuccessProfile]
    split_ifs <;> simp_all
  letI : IsMarkovKernel (causalSelectedBernoulliKernel p hp) :=
    causalSelectedBernoulliKernel_isMarkovKernel p hp
      (fun x => (hpunit x).1) (fun x => (hpunit x).2)
  rw [causalHardCellSignedObservationMeasure_eq_scoreBernoulli j b cA delta w
    centers omega hb hscale hcA hdelta hw hsep hcell]
  have hpair : Measurable (fun z : Score × ℝ =>
      (z.2, causalHardSignedStatistic (centers j) z.1)) :=
    measurable_snd.prodMk
      ((causalHardSignedStatistic_measurable _).comp measurable_fst)
  rw [Measure.map_map measurable_snd hpair]
  change Measure.map (causalHardSignedStatistic (centers j) ∘ Prod.fst)
      (Measure.compProd nu (causalSelectedBernoulliKernel p hp)) = _
  rw [← Measure.map_map (causalHardSignedStatistic_measurable _) measurable_fst]
  have hfst : Measure.map Prod.fst
      (Measure.compProd nu (causalSelectedBernoulliKernel p hp)) = nu := by
    simpa [Measure.fst] using
      (Measure.fst_compProd nu (causalSelectedBernoulliKernel p hp))
  rw [hfst]

/-- The canonical normalized bit laws have a common signed-radius marginal. -/
-- @node: causalHardCellBitObservationLaw_common_signedMarginal
lemma causalHardCellBitObservationLaw_common_signedMarginal {M : ℕ}
    (j : Fin M) (b cA delta w : ℝ) (centers : Fin M → Score)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    Measure.map Prod.snd (causalHardCellBitObservationLaw b cA delta w centers
        hb hscale hcA hdelta hw hsep hcell j false) =
      Measure.map Prod.snd (causalHardCellBitObservationLaw b cA delta w centers
        hb hscale hcA hdelta hw hsep hcell j true) := by
  let omega0 := causalHardCellBitRepresentative j false
  let omega1 := causalHardCellBitRepresentative j true
  let rho := Real.pi * w ^ 2 / 36
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hraw0 := congrArg (Measure.map Prod.snd)
    (causalHardCellSignedObservationMeasure_eq_bitLaw j b cA delta w centers
      omega0 hb hscale hcA hdelta hw hsep hcell)
  have hraw1 := congrArg (Measure.map Prod.snd)
    (causalHardCellSignedObservationMeasure_eq_bitLaw j b cA delta w centers
      omega1 hb hscale hcA hdelta hw hsep hcell)
  rw [Measure.map_smul] at hraw0
  rw [Measure.map_smul] at hraw1
  have hbit0 : omega0 j = false := by
    simp [omega0, causalHardCellBitRepresentative]
  have hbit1 : omega1 j = true := by
    simp [omega1, causalHardCellBitRepresentative]
  rw [hbit0] at hraw0
  rw [hbit1] at hraw1
  apply measure_eq_of_pos_ofReal_smul_eq _ _ hrho
  dsimp [rho] at hraw0 hraw1 ⊢
  rw [← hraw0]
  rw [causalHardCellSignedObservationMeasure_map_snd j b cA delta w centers
    omega0 hb hscale hcA hdelta hw hsep hcell]
  rw [← hraw1]
  rw [causalHardCellSignedObservationMeasure_map_snd j b cA delta w centers
    omega1 hb hscale hcA hdelta hw hsep hcell]
  exact causalHardScoreMeasure_restrict_map_signedStatistic_eq j centers
    omega0 omega1 hb hscale hcA hdelta hw hwHalf hsep hcenter (hcell j)

/-- The canonical normalized bit laws agree away from the positive
short-radius window. -/
-- @node: causalHardCellBitObservationLaw_restrict_compl_eq
lemma causalHardCellBitObservationLaw_restrict_compl_eq {M : ℕ}
    (j : Fin M) {b cA delta w : ℝ} (centers : Fin M → Score)
    (hbEq : b = 1 / 16) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16)
    (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    (causalHardCellBitObservationLaw b cA delta w centers hb hscale hcA
        hdelta hw hsep hcell j false).restrict
          {yd | ¬ (0 < yd.2 ∧ yd.2 < 2 * (cA * delta) / b)} =
      (causalHardCellBitObservationLaw b cA delta w centers hb hscale hcA
        hdelta hw hsep hcell j true).restrict
          {yd | ¬ (0 < yd.2 ∧ yd.2 < 2 * (cA * delta) / b)} := by
  let omega0 := causalHardCellBitRepresentative j false
  let omega1 := causalHardCellBitRepresentative j true
  let rho := Real.pi * w ^ 2 / 36
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hupdate : Function.update omega0 j true = omega1 := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [omega0, omega1, causalHardCellBitRepresentative]
    · simp [omega0, omega1, causalHardCellBitRepresentative, hkj]
  have hout := causalHardCellSignedObservationMeasure_restrict_compl_enable_eq
    j centers omega0 hbEq hb hscale hcA hdelta hdeltaSmall hw hwHalf hsep
      hcenter hcell (by simp [omega0, causalHardCellBitRepresentative])
  rw [hupdate] at hout
  dsimp only at hout
  have hraw0 := causalHardCellSignedObservationMeasure_eq_bitLaw
    j b cA delta w centers omega0 hb hscale hcA hdelta hw hsep hcell
  have hraw1 := causalHardCellSignedObservationMeasure_eq_bitLaw
    j b cA delta w centers omega1 hb hscale hcA hdelta hw hsep hcell
  rw [show omega0 j = false by simp [omega0, causalHardCellBitRepresentative]] at hraw0
  rw [show omega1 j = true by simp [omega1, causalHardCellBitRepresentative]] at hraw1
  rw [hraw0, hraw1, Measure.restrict_smul, Measure.restrict_smul] at hout
  apply measure_eq_of_pos_ofReal_smul_eq _ _ hrho
  simpa [rho] using hout

/-- Both KL orientations between the canonical normalized bit laws have the
paper's fourth-order localized bound. -/
-- @node: causalHardCellBitObservationLaw_klDiv_le
lemma causalHardCellBitObservationLaw_klDiv_le {M : ℕ}
    (j : Fin M) {delta w : ℝ} (centers : Fin M → Score)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16)
    (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    let Q := causalHardCellBitObservationLaw (1 / 16) 8 delta w centers
      (by norm_num) (by positivity) (by norm_num) hdelta hw hsep hcell j
    InformationTheory.klDiv (Q false) (Q true) ≤
        ENNReal.ofReal (262144 * delta ^ 4 / w ^ 2) ∧
      InformationTheory.klDiv (Q true) (Q false) ≤
        ENNReal.ofReal (262144 * delta ^ 4 / w ^ 2) := by
  dsimp only
  let omega0 := causalHardCellBitRepresentative j false
  let omega1 := causalHardCellBitRepresentative j true
  let rho : ℝ := Real.pi * w ^ 2 / 36
  let rhoNN : ℝ≥0 := ⟨rho, (by dsimp [rho]; positivity)⟩
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoNNcoe : (rhoNN : ℝ≥0∞) = ENNReal.ofReal rho :=
    (ENNReal.ofReal_coe_nnreal (p := rhoNN)).symm
  have hupdate : Function.update omega0 j true = omega1 := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [omega0, omega1, causalHardCellBitRepresentative]
    · simp [omega0, omega1, causalHardCellBitRepresentative, hkj]
  have hraw := causalHardCellSignedObservationMeasure_klDiv_enable_le
    (b := 1 / 16) (cA := 8) (delta := delta) (w := w)
      j centers omega0 (by norm_num) (by norm_num) (by positivity) (by norm_num)
      hdelta hdeltaSmall hw hwHalf hsep hcenter hcell
      (by simp [omega0, causalHardCellBitRepresentative])
  rw [hupdate] at hraw
  dsimp only at hraw
  have hraw0 := causalHardCellSignedObservationMeasure_eq_bitLaw
    j (1 / 16) 8 delta w centers omega0 (by norm_num) (by positivity)
      (by norm_num) hdelta hw hsep hcell
  have hraw1 := causalHardCellSignedObservationMeasure_eq_bitLaw
    j (1 / 16) 8 delta w centers omega1 (by norm_num) (by positivity)
      (by norm_num) hdelta hw hsep hcell
  rw [show omega0 j = false by simp [omega0, causalHardCellBitRepresentative]] at hraw0
  rw [show omega1 j = true by simp [omega1, causalHardCellBitRepresentative]] at hraw1
  have hraw0NN : causalHardCellSignedObservationMeasure
      (causalHardA1A2Law (1 / 16) 8 delta w centers omega0 (by norm_num)
        (by positivity) (by norm_num) hdelta hw hsep hcell) (centers j) w =
      rhoNN • causalHardCellBitObservationLaw
      (1 / 16) 8 delta w centers (by norm_num) (by positivity) (by norm_num)
        hdelta hw hsep hcell j false := by
    rw [← Measure.coe_nnreal_smul, hrhoNNcoe]
    exact hraw0
  have hraw1NN : causalHardCellSignedObservationMeasure
      (causalHardA1A2Law (1 / 16) 8 delta w centers omega1 (by norm_num)
        (by positivity) (by norm_num) hdelta hw hsep hcell) (centers j) w =
      rhoNN • causalHardCellBitObservationLaw
      (1 / 16) 8 delta w centers (by norm_num) (by positivity) (by norm_num)
        hdelta hw hsep hcell j true := by
    rw [← Measure.coe_nnreal_smul, hrhoNNcoe]
    exact hraw1
  rw [hraw0NN, hraw1NN] at hraw
  simp only [InformationTheory.klDiv_smul_same] at hraw
  have hmass := causalHardScoreMeasure_signedStatistic_Ioo_le j centers omega0
    (b := 1 / 16) (cA := 8) (delta := delta) (w := w)
    (R := 2 * (8 * delta) / (1 / 16)) (by norm_num) (by positivity)
      (by norm_num) hdelta hw hwHalf (by positivity) hsep hcenter (hcell j)
  have hbound : ENNReal.ofReal (4 * delta ^ 2) *
      Measure.map (causalHardSignedStatistic (centers j))
        ((causalHardScoreMeasure (1 / 16) 8 delta w centers omega0).restrict
          (causalHardCell (centers j) w))
        (Ioo 0 (2 * (8 * delta) / (1 / 16))) ≤
      (rhoNN : ℝ≥0∞) * ENNReal.ofReal (262144 * delta ^ 4 / w ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (4 * delta ^ 2) *
          ENNReal.ofReal (Real.pi * (2 * (8 * delta) / (1 / 16)) ^ 2 / 36) :=
        mul_le_mul_right hmass _
      _ = (rhoNN : ℝ≥0∞) *
          ENNReal.ofReal (262144 * delta ^ 4 / w ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * delta ^ 2)]
        rw [hrhoNNcoe]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ rho)]
        congr 1
        dsimp [rho]
        field_simp
        ring
  constructor
  · have hrhoNN0 : (rhoNN : ℝ≥0∞) ≠ 0 := by
      apply ENNReal.coe_ne_zero.mpr
      intro hz
      have hzv : rho = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) hz
      linarith
    apply (ENNReal.mul_le_mul_iff_right (a := (rhoNN : ℝ≥0∞)) hrhoNN0
      ENNReal.coe_ne_top).mp
    exact hraw.1.trans hbound
  · have hrhoNN0 : (rhoNN : ℝ≥0∞) ≠ 0 := by
      apply ENNReal.coe_ne_zero.mpr
      intro hz
      have hzv : rho = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) hz
      linarith
    apply (ENNReal.mul_le_mul_iff_right (a := (rhoNN : ℝ≥0∞)) hrhoNN0
      ENNReal.coe_ne_top).mp
    exact hraw.2.trans hbound

end CausalSmith.Stat.BddUniformLogPenalty
