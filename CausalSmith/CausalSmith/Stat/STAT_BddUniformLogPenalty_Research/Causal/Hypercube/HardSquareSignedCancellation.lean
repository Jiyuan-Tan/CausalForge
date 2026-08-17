import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedObservation
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareGramCertificate
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialQuantitative

/-!
# Half-disc cancellation for signed hard-square observations

This module transports the quantitative polar cancellation estimate to an
arbitrary score-space center.  In particular it applies without another
change of coordinates to the translated centers on the bottom edge of the
hard assignment rectangle.
-/

open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Reflecting horizontally through the cell center preserves every measurable
signed-radius slice and reverses the angular density correction.  Consequently
the correction has zero integral on each such slice. -/
-- @node: scoreCenter_signedRadialSet_angularTerm_integral_eq_zero
lemma scoreCenter_signedRadialSet_angularTerm_integral_eq_zero
    (c : Score) (b cA delta w : ℝ) {A : Set ℝ}
    (_hA : MeasurableSet A) :
    (∫ x in
      (Metric.closedBall c w ∩ {x |
        (if 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 then dist x c
          else -dist x c) ∈ A}),
      packingAngularTerm b cA delta w c x) = 0 := by
  let e : Score ≃ᵐ Score :=
    (hardSquareSectorEquiv c true true).symm.trans
      (hardSquareSectorEquiv c false true)
  let D : Set Score :=
    Metric.closedBall c w ∩ {x |
      (if 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 then dist x c
        else -dist x c) ∈ A}
  have hePres : MeasurePreserving e (volume : Measure Score) volume :=
    (hardSquareSectorEquiv_volumePreserving c false true).comp
      (hardSquareSectorEquiv_volumePreserving c true true).symm
  have heDist (x : Score) : dist (e x) c = dist x c := by
    let q : ℝ × ℝ := (hardSquareSectorEquiv c true true).symm x
    have hx : hardSquareSectorEquiv c true true q = x := by
      simp [q]
    calc
      dist (e x) c = planarRadius q := by
        simpa [e, q] using hardSquareSectorEquiv_dist c false true q
      _ = dist x c := by
        rw [← hx]
        exact (hardSquareSectorEquiv_dist c true true q).symm
  have heVertical (x : Score) :
      (scoreCoordinates (e x) - scoreCoordinates c).2 =
        (scoreCoordinates x - scoreCoordinates c).2 := by
    let q : ℝ × ℝ := (hardSquareSectorEquiv c true true).symm x
    have hx : hardSquareSectorEquiv c true true q = x := by
      simp [q]
    have he1 := hardSquareSectorEquiv_apply_one c false true q
    have hx1 := hardSquareSectorEquiv_apply_one c true true q
    change e x 1 - c 1 = x 1 - c 1
    rw [← hx]
    simpa [e, q] using congrArg (fun z : ℝ => z - c 1) (he1.trans hx1.symm)
  have heSigned (x : Score) :
      (if 0 ≤ (scoreCoordinates (e x) - scoreCoordinates c).2 then
          dist (e x) c else -dist (e x) c) =
        if 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 then
          dist x c else -dist x c := by
    rw [heDist, heVertical]
  have heImage : e '' D = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, heDist]
        exact hy.1
      · change (if 0 ≤ (scoreCoordinates (e y) - scoreCoordinates c).2 then
            dist (e y) c else -dist (e y) c) ∈ A
        rw [heSigned]
        exact hy.2
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      have hdistInv := heDist (e.symm x)
      have hsignedInv := heSigned (e.symm x)
      simp only [e.apply_symm_apply] at hdistInv hsignedInv
      constructor
      · rw [Metric.mem_closedBall, ← hdistInv]
        exact hx.1
      · change (if 0 ≤ (scoreCoordinates (e.symm x) - scoreCoordinates c).2
            then dist (e.symm x) c else -dist (e.symm x) c) ∈ A
        rw [← hsignedInv]
        exact hx.2
  have heOdd (x : Score) :
      packingAngularTerm b cA delta w c (e x) =
        -packingAngularTerm b cA delta w c x := by
    let q : ℝ × ℝ := (hardSquareSectorEquiv c true true).symm x
    have hx : hardSquareSectorEquiv c true true q = x := by
      simp [q]
    have he0 := hardSquareSectorEquiv_apply_zero c false true q
    have hx0 := hardSquareSectorEquiv_apply_zero c true true q
    unfold packingAngularTerm packingDirectionCos
    rw [heDist]
    by_cases hd : dist x c = 0
    · simp [hd]
    · simp only [hd, if_false]
      have hcoord : e x 0 - c 0 = -(x 0 - c 0) := by
        rw [← hx]
        rw [show e (hardSquareSectorEquiv c true true q) =
          hardSquareSectorEquiv c false true q by simp [e]]
        simp at he0 hx0
        rw [he0, hx0]
        ring
      rw [hcoord]
      ring
  change (∫ x in D, packingAngularTerm b cA delta w c x) = 0
  have hchange := hePres.setIntegral_image_emb e.measurableEmbedding
    (packingAngularTerm b cA delta w c) D
  rw [heImage] at hchange
  simp_rw [heOdd] at hchange
  rw [integral_neg] at hchange
  linarith

/-- On a sufficiently small cell centered on the middle bottom edge, the
hard-family signed statistic is the Euclidean radius with the sign of the
vertical displacement. -/
-- @node: causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
lemma causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
    {c z : Score} {w : ℝ} (hc : c ∈ causalHardBottomEdge)
    (hw : w ≤ 1 / 2) (hz : z ∈ causalHardCell c w) :
    causalHardSignedStatistic c z =
      if 0 ≤ (scoreCoordinates z - scoreCoordinates c).2 then dist z c
      else -dist z c := by
  have hdist : dist z c ≤ w := by
    simpa [causalHardCell, Metric.mem_closedBall, dist_comm] using hz
  have hcoord (i : Fin 2) : |z i - c i| ≤ dist z c := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (z - c) i
  have hzSquare : z ∈ causalHardSquare :=
    causalHardCell_subset_square hc (hw.trans (by norm_num)) hz
  have hc0lo : -1 / 2 ≤ c 0 := hc.1
  have hc0hi : c 0 ≤ 1 / 2 := hc.2.1
  have hc1 : c 1 = 0 := hc.2.2
  have hz0lo : -1 ≤ z 0 := by
    have := hcoord 0
    rw [abs_le] at this
    linarith
  have hz0hi : z 0 ≤ 1 := by
    have := hcoord 0
    rw [abs_le] at this
    linarith
  have hz1lohi : |z 1| ≤ 1 / 2 := by
    calc
      |z 1| = |z 1 - c 1| := by rw [hc1, sub_zero]
      _ ≤ dist z c := hcoord 1
      _ ≤ w := hdist
      _ ≤ 1 / 2 := hw
  by_cases hup : 0 ≤ (scoreCoordinates z - scoreCoordinates c).2
  · have hz1lo : 0 ≤ z 1 := by
      change 0 ≤ z 1 - c 1 at hup
      linarith
    have hz1hi : z 1 ≤ 2 := by
      exact (le_abs_self (z 1)).trans (hz1lohi.trans (by norm_num))
    have hA1 : z ∈ causalHardArmOne := by
      exact ⟨hz0lo, hz0hi, hz1lo, hz1hi⟩
    have horder : (scoreCoordinates c).2 ≤ (scoreCoordinates z).2 := by
      change c 1 ≤ z 1
      linarith
    simp [causalHardSignedStatistic, hA1, hzSquare, horder]
  · have hA1 : z ∉ causalHardArmOne := by
      intro hA1
      apply hup
      change 0 ≤ z 1 - c 1
      linarith [hA1.2.2.1]
    have hA0 : z ∈ causalHardSquare \ causalHardArmOne := ⟨hzSquare, hA1⟩
    have horder : ¬(scoreCoordinates c).2 ≤ (scoreCoordinates z).2 := by
      intro h
      apply hup
      change 0 ≤ z 1 - c 1
      change c 1 ≤ z 1 at h
      linarith
    simp [causalHardSignedStatistic, hA1, hA0, horder]

/-- The angular correction has zero integral on every measurable slice of the
actual signed-distance statistic used by the hard family. -/
-- @node: scoreCenter_causalHardSignedStatistic_angularTerm_integral_eq_zero
lemma scoreCenter_causalHardSignedStatistic_angularTerm_integral_eq_zero
    {c : Score} (hc : c ∈ causalHardBottomEdge) (b cA delta w : ℝ)
    (hw : w ≤ 1 / 2) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x in
      (causalHardCell c w ∩ {x | causalHardSignedStatistic c x ∈ A}),
      packingAngularTerm b cA delta w c x) = 0 := by
  have hset :
      causalHardCell c w ∩ {x | causalHardSignedStatistic c x ∈ A} =
        Metric.closedBall c w ∩ {x |
          (if 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 then dist x c
            else -dist x c) ∈ A} := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      change (if 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 then
          dist x c else -dist x c) ∈ A
      rw [← causalHardSignedStatistic_eq_verticalSignedRadius_on_cell hc hw hx.1]
      exact hx.2
    · intro hx
      refine ⟨hx.1, ?_⟩
      change causalHardSignedStatistic c x ∈ A
      rw [causalHardSignedStatistic_eq_verticalSignedRadius_on_cell hc hw hx.1]
      exact hx.2
  rw [hset]
  exact scoreCenter_signedRadialSet_angularTerm_integral_eq_zero
    c b cA delta w hA

/-- On every measurable radial slice of a translated complete disk, the
angular density correction has zero mass.  Point reflection through the
center preserves the slice and negates the direction cosine. -/
-- @node: scoreCenter_closedBall_radial_angularTerm_integral_eq_zero
lemma scoreCenter_closedBall_radial_angularTerm_integral_eq_zero
    (c : Score) (b cA delta w : ℝ) {A : Set ℝ}
    (_hA : MeasurableSet A) :
    (∫ x in
      (Metric.closedBall c w ∩ {x | dist x c ∈ A}),
      packingAngularTerm b cA delta w c x) = 0 := by
  let T : Score → Score := fun x => (2 : ℝ) • c - x
  let D : Set Score := Metric.closedBall c w ∩ {x | dist x c ∈ A}
  have hT : MeasurePreserving T (volume : Measure Score) volume := by
    exact (measurePreserving_add_left volume ((2 : ℝ) • c)).comp
      (Measure.measurePreserving_neg volume)
  have hTemb : MeasurableEmbedding T := by
    let e : Score ≃ₜ Score := (Homeomorph.neg Score).trans
      (Homeomorph.addLeft ((2 : ℝ) • c))
    exact e.measurableEmbedding
  have hdist (x : Score) : dist (T x) c = dist x c := by
    rw [dist_eq_norm, dist_eq_norm, show T x - c = -(x - c) by
      dsimp [T]
      module]
    exact norm_neg _
  have himage : T '' D = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa [D, Metric.mem_closedBall, hdist] using hy.1,
        by simpa [D, hdist] using hy.2⟩
    · intro hx
      refine ⟨T x, ?_, ?_⟩
      · exact ⟨by simpa [D, Metric.mem_closedBall, hdist] using hx.1,
          by simpa [D, hdist] using hx.2⟩
      · simp [T]
  have hodd : ∀ x, packingAngularTerm b cA delta w c (T x) =
      -packingAngularTerm b cA delta w c x := by
    intro x
    unfold packingAngularTerm packingDirectionCos
    rw [hdist]
    by_cases hx : dist x c = 0
    · simp [hx]
    · simp only [hx, if_false]
      simp [T]
      ring
  have hchange := hT.setIntegral_image_emb hTemb
    (packingAngularTerm b cA delta w c) D
  rw [himage] at hchange
  simp_rw [hodd] at hchange
  rw [integral_neg] at hchange
  linarith [hchange]

/-- On every measurable radial slice of a translated closed upper half-disc,
the angular density correction has zero mass.  Unlike the older grid-specific
version, this statement applies directly to the hard-square centers. -/
-- @node: scoreCenter_closedUpperHalf_radial_angularTerm_integral_eq_zero
lemma scoreCenter_closedUpperHalf_radial_angularTerm_integral_eq_zero
    (c : Score) (b cA delta w : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (∫ x in
      ({x | 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}),
      packingAngularTerm b cA delta w c x) = 0 := by
  let D : Set Score :=
    {x | 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  let E : Set (ℝ × ℝ) :=
    {z | 0 ≤ (z - scoreCoordinates c).2 ∧
      planarRadius (z - scoreCoordinates c) ≤ w} ∩
      {z | planarRadius (z - scoreCoordinates c) ∈ A}
  have himage : scoreCoordinates '' D = E := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [D, E, planarRadius_scoreCoordinates_sub] using hx
    · intro hz
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      refine ⟨x, ?_, hcoord⟩
      simpa [D, E, hcoord, ← planarRadius_scoreCoordinates_sub] using hz
  have hfun : packingAngularTerm b cA delta w c = fun x =>
      angularTilt b cA delta w
          (planarRadius (scoreCoordinates x - scoreCoordinates c)) *
        ((scoreCoordinates x - scoreCoordinates c).1 /
          planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [packingAngularTerm, packingDirectionCos_eq_planarFirst_div_radius,
      planarRadius_scoreCoordinates_sub]
  change (∫ x in D, packingAngularTerm b cA delta w c x) = 0
  rw [hfun]
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
    scoreCoordinates_measurableEmbedding
    (fun z : ℝ × ℝ =>
      angularTilt b cA delta w
          (planarRadius (z - scoreCoordinates c)) *
        ((z - scoreCoordinates c).1 /
          planarRadius (z - scoreCoordinates c))) D]
  rw [himage]
  exact translatedClosedHalfDisc_radialSet_weighted_first_div_radius_cancellation
    (angularTilt b cA delta w) w (scoreCoordinates c) hA

/-- The matching cancellation holds on every translated closed lower
half-disc radial slice.  Reflection through the center carries the upper
slice to the lower slice and reverses the angular correction. -/
-- @node: scoreCenter_closedLowerHalf_radial_angularTerm_integral_eq_zero
lemma scoreCenter_closedLowerHalf_radial_angularTerm_integral_eq_zero
    (c : Score) (b cA delta w : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (∫ x in
      ({x | (scoreCoordinates x - scoreCoordinates c).2 ≤ 0 ∧
          dist x c ≤ w} ∩ {x | dist x c ∈ A}),
      packingAngularTerm b cA delta w c x) = 0 := by
  let T : Score → Score := fun x => (2 : ℝ) • c - x
  let U : Set Score :=
    {x | 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  let D : Set Score :=
    {x | (scoreCoordinates x - scoreCoordinates c).2 ≤ 0 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  have hT : MeasurePreserving T (volume : Measure Score) volume := by
    exact (measurePreserving_add_left volume ((2 : ℝ) • c)).comp
      (Measure.measurePreserving_neg volume)
  have hTemb : MeasurableEmbedding T := by
    let e : Score ≃ₜ Score := (Homeomorph.neg Score).trans
      (Homeomorph.addLeft ((2 : ℝ) • c))
    exact e.measurableEmbedding
  have hdist (x : Score) : dist (T x) c = dist x c := by
    rw [dist_eq_norm, dist_eq_norm, show T x - c = -(x - c) by
      dsimp [T]
      module]
    exact norm_neg _
  have hcoord (x : Score) :
      (scoreCoordinates (T x) - scoreCoordinates c).2 =
        -(scoreCoordinates x - scoreCoordinates c).2 := by
    change (T x) 1 - c 1 = -(x 1 - c 1)
    simp [T]
    ring
  have himage : T '' U = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨by rw [hcoord]; linarith [hy.1.1], by simpa [hdist] using hy.1.2⟩,
        by simpa [hdist] using hy.2⟩
    · intro hx
      refine ⟨T x, ?_, ?_⟩
      · exact ⟨⟨by rw [hcoord]; linarith [hx.1.1],
          by simpa [hdist] using hx.1.2⟩, by simpa [hdist] using hx.2⟩
      · simp [T]
  have hodd : ∀ x, packingAngularTerm b cA delta w c (T x) =
      -packingAngularTerm b cA delta w c x := by
    intro x
    unfold packingAngularTerm packingDirectionCos
    rw [hdist]
    by_cases hx : dist x c = 0
    · simp [hx]
    · simp only [hx, if_false]
      simp [T]
      ring
  have hchange := hT.setIntegral_image_emb hTemb
    (packingAngularTerm b cA delta w c) U
  rw [himage] at hchange
  simp_rw [hodd] at hchange
  rw [integral_neg] at hchange
  have hupper := scoreCenter_closedUpperHalf_radial_angularTerm_integral_eq_zero
    c b cA delta w hA
  change (∫ x in D, packingAngularTerm b cA delta w c x) = 0
  change (∫ x in U, packingAngularTerm b cA delta w c x) = 0 at hupper
  linarith [hchange, hupper]

/-- The quantitative upper-half-disc cancellation estimate is invariant
under translation to an arbitrary score-space center. -/
-- @node: scoreCenter_radialSet_angular_outcome_abs_le
lemma scoreCenter_radialSet_angular_outcome_abs_le
    (c : Score) {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hdelta : 0 ≤ delta)
    {A : Set ℝ} (hA : MeasurableSet A) :
    let D : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    let Dloc : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A ∩ Iio (2 * (cA * delta) / b)}
    |(∫ x in D, delta * angularRadialProfile w (dist x c)) +
      (∫ x in D,
        b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c))| ≤
      delta * (volume Dloc).toReal := by
  dsimp only
  let cp : ℝ × ℝ := scoreCoordinates c
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  let Dloc : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A ∩ Iio (2 * (cA * delta) / b)}
  let E : Set (ℝ × ℝ) :=
    {z | 0 < (z - cp).2 ∧ planarRadius (z - cp) ≤ w} ∩
      {z | planarRadius (z - cp) ∈ A}
  let Eloc : Set (ℝ × ℝ) :=
    {z | 0 < (z - cp).2 ∧ planarRadius (z - cp) ≤ w} ∩
      {z | planarRadius (z - cp) ∈ A ∩ Iio (2 * (cA * delta) / b)}
  have himage : scoreCoordinates '' D = E := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [D, E, cp, planarRadius_scoreCoordinates_sub] using hx
    · intro hz
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      refine ⟨x, ?_, hcoord⟩
      simpa [D, E, cp, hcoord, ← planarRadius_scoreCoordinates_sub] using hz
  have himageLoc : scoreCoordinates '' Dloc = Eloc := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Dloc, Eloc, cp, planarRadius_scoreCoordinates_sub] using hx
    · intro hz
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      refine ⟨x, ?_, hcoord⟩
      simpa [Dloc, Eloc, cp, hcoord,
        ← planarRadius_scoreCoordinates_sub] using hz
  change |(∫ x in D, delta * angularRadialProfile w (dist x c)) +
      (∫ x in D, b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c))| ≤
    delta * (volume Dloc).toReal
  have hfirst : (fun x : Score => delta * angularRadialProfile w (dist x c)) =
      fun x => delta * angularRadialProfile w
        (planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  have hsecond : (fun x : Score =>
      b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) =
      fun x => b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w
          (planarRadius (scoreCoordinates x - scoreCoordinates c)) *
        ((scoreCoordinates x - scoreCoordinates c).1 /
          planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  rw [hfirst, hsecond]
  change |(∫ x in D, (fun z : ℝ × ℝ =>
      delta * angularRadialProfile w (planarRadius (z - scoreCoordinates c)))
        (scoreCoordinates x)) +
    (∫ x in D, (fun z : ℝ × ℝ =>
      b * (z - scoreCoordinates c).1 *
        angularTilt b cA delta w (planarRadius (z - scoreCoordinates c)) *
        ((z - scoreCoordinates c).1 / planarRadius (z - scoreCoordinates c)))
          (scoreCoordinates x))| ≤ delta * (volume Dloc).toReal
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ => delta * angularRadialProfile w
        (planarRadius (z - scoreCoordinates c))) D,
    ← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ => b * (z - scoreCoordinates c).1 *
        angularTilt b cA delta w (planarRadius (z - scoreCoordinates c)) *
        ((z - scoreCoordinates c).1 / planarRadius (z - scoreCoordinates c))) D]
  have hvolScore : (volume Dloc).toReal =
      (volume (scoreCoordinates '' Dloc)).toReal := by
    have h := scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding (fun _ : ℝ × ℝ => (1 : ℝ)) Dloc
    simpa [integral_const, Measure.real_def] using h.symm
  rw [hvolScore, himage, himageLoc]
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun u => cp + u
  let E0 : Set (ℝ × ℝ) :=
    {u | 0 < u.2 ∧ planarRadius u ≤ w} ∩ planarRadius ⁻¹' A
  let E0loc : Set (ℝ × ℝ) :=
    {u | 0 < u.2 ∧ planarRadius u ≤ w} ∩
      planarRadius ⁻¹' (A ∩ Iio (2 * (cA * delta) / b))
  have hT : MeasurableEmbedding T := (Homeomorph.addLeft cp).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_left volume cp
  have hE : E = T '' E0 := by
    ext z
    constructor
    · rintro ⟨hz, hAz⟩
      refine ⟨z - cp, ⟨?_, ?_⟩, by simp [T]⟩
      · simpa [E0] using hz
      · simpa [E0] using hAz
    · rintro ⟨u, ⟨hu, hAu⟩, rfl⟩
      simpa [E, E0, T] using And.intro hu hAu
  have hEloc : Eloc = T '' E0loc := by
    ext z
    constructor
    · rintro ⟨hz, hAz⟩
      refine ⟨z - cp, ⟨?_, ?_⟩, by simp [T]⟩
      · simpa [E0loc] using hz
      · simpa [E0loc] using hAz
    · rintro ⟨u, ⟨hu, hAu⟩, rfl⟩
      simpa [Eloc, E0loc, T] using And.intro hu hAu
  rw [hE, hmp.setIntegral_image_emb hT, hmp.setIntegral_image_emb hT]
  rw [hEloc]
  have hvol : (volume (T '' E0loc)).toReal = (volume E0loc).toReal := by
    have h := hmp.setIntegral_image_emb hT (fun _ : ℝ × ℝ => (1 : ℝ)) E0loc
    simpa [integral_const, Measure.real_def] using h
  rw [hvol]
  simpa [T, cp, E0, E0loc] using
    halfDisc_radialSet_angular_outcome_abs_le
      (w := w) (R := w) hb hscale hdelta hA

/-- The quantitative cancellation estimate at a hard-square packing center. -/
-- @node: causalHardGridCenter_radialSet_angular_outcome_abs_le
lemma causalHardGridCenter_radialSet_angular_outcome_abs_le
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hdelta : 0 ≤ delta)
    {A : Set ℝ} (hA : MeasurableSet A) :
    let c := causalHardGridCenter M j
    let D : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    let Dloc : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A ∩ Iio (2 * (cA * delta) / b)}
    |(∫ x in D, delta * angularRadialProfile w (dist x c)) +
      (∫ x in D,
        b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c))| ≤
      delta * (volume Dloc).toReal := by
  exact scoreCenter_radialSet_angular_outcome_abs_le
    (causalHardGridCenter M j) hb hscale hdelta hA

end CausalSmith.Stat.BddUniformLogPenalty
