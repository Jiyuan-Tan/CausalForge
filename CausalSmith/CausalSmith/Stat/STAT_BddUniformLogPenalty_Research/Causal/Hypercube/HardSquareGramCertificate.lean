import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareGram

/-!
# Population-Gram certificate for the hard square

This module transports the hard law to its score density, restricts the Gram
quadratic form to a fixed radial sector in either assignment arm, and combines
the resulting polar integral with finite-dimensional polynomial coercivity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Stat.Nonparametric.LocalPolynomial

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: scoreOfProd
noncomputable def scoreOfProd : (ℝ × ℝ) ≃ᵐ Score :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: scoreOfProd_apply
lemma scoreOfProd_apply (q : ℝ × ℝ) :
    scoreOfProd q = scorePoint q.1 q.2 := by
  ext i
  fin_cases i <;> rfl

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: scoreOfProd_volumePreserving
lemma scoreOfProd_volumePreserving :
    MeasurePreserving scoreOfProd (volume : Measure (ℝ × ℝ)) volume := by
  have h1 : MeasurePreserving MeasurableEquiv.finTwoArrow.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  have h2 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure Score) :=
    PiLp.volume_preserving_toLp (Fin 2)
  exact h2.comp h1

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: signedProdEquiv
noncomputable def signedProdEquiv (sx sy : Bool) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr
    (if sx then MeasurableEquiv.refl ℝ else MeasurableEquiv.neg ℝ)
    (if sy then MeasurableEquiv.refl ℝ else MeasurableEquiv.neg ℝ)

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: signedProdEquiv_volumePreserving
lemma signedProdEquiv_volumePreserving (sx sy : Bool) :
    MeasurePreserving (signedProdEquiv sx sy) volume volume := by
  cases sx <;> cases sy
  · exact
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  · exact
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
  · exact
      (MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  · exact
      (MeasurePreserving.id (volume : Measure ℝ)).prod
        (MeasurePreserving.id (volume : Measure ℝ))

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareSectorEquiv
noncomputable def hardSquareSectorEquiv (x : Score) (sx sy : Bool) :
    (ℝ × ℝ) ≃ᵐ Score :=
  (signedProdEquiv sx sy).trans scoreOfProd |>.trans (MeasurableEquiv.addLeft x)

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareSectorEquiv_volumePreserving
lemma hardSquareSectorEquiv_volumePreserving (x : Score) (sx sy : Bool) :
    MeasurePreserving (hardSquareSectorEquiv x sx sy) volume volume := by
  exact (measurePreserving_add_left volume x).comp
    (scoreOfProd_volumePreserving.comp (signedProdEquiv_volumePreserving sx sy))

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareSectorEquiv_dist
lemma hardSquareSectorEquiv_dist (x : Score) (sx sy : Bool) (q : ℝ × ℝ) :
    dist (hardSquareSectorEquiv x sx sy q) x = planarRadius q := by
  cases sx <;> cases sy
  all_goals
  rw [hardSquareSectorEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_addLeft]
  conv_lhs => rhs; rw [← add_zero x]
  rw [dist_add_left]
  rw [scoreOfProd_apply, dist_zero_right, EuclideanSpace.norm_eq]
  all_goals simp [signedProdEquiv, MeasurableEquiv.prodCongr, Equiv.prodCongr,
    Fin.sum_univ_two, scorePoint_apply_zero,
    scorePoint_apply_one, Real.norm_eq_abs, sq_abs, planarRadius]

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareSectorEquiv_apply_zero
lemma hardSquareSectorEquiv_apply_zero (x : Score) (sx sy : Bool) (q : ℝ × ℝ) :
    hardSquareSectorEquiv x sx sy q 0 = x 0 + if sx then q.1 else -q.1 := by
  cases sx <;> cases sy <;>
    simp [hardSquareSectorEquiv, signedProdEquiv, MeasurableEquiv.prodCongr,
      Equiv.prodCongr, scoreOfProd_apply, scorePoint_apply_zero]

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareSectorEquiv_apply_one
lemma hardSquareSectorEquiv_apply_one (x : Score) (sx sy : Bool) (q : ℝ × ℝ) :
    hardSquareSectorEquiv x sx sy q 1 = x 1 + if sy then q.2 else -q.2 := by
  cases sx <;> cases sy <;>
    simp [hardSquareSectorEquiv, signedProdEquiv, MeasurableEquiv.prodCongr,
      Equiv.prodCongr, scoreOfProd_apply, scorePoint_apply_one]

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: fst_le_planarRadius
lemma fst_le_planarRadius (q : ℝ × ℝ) :
    q.1 ≤ planarRadius q := by
  rw [planarRadius]
  exact (le_abs_self q.1).trans
    (Real.abs_le_sqrt (by nlinarith [sq_nonneg q.2]))

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: snd_le_planarRadius
lemma snd_le_planarRadius (q : ℝ × ℝ) :
    q.2 ≤ planarRadius q := by
  rw [planarRadius]
  exact (le_abs_self q.2).trans
    (Real.abs_le_sqrt (by nlinarith [sq_nonneg q.1]))

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareSectorDomain
def hardSquareSectorDomain (h : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ 0 < q.2 ∧ planarRadius q ≤ h}

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareArmOne_sector_subset
lemma hardSquareArmOne_sector_subset {x : Score} {h : ℝ}
    (hx : x ∈ frontier causalHardArmOne) (hh1 : h ≤ 1)
    (sx sy : Bool)
    (hsx : (sx = true ∧ x 0 ≤ 0) ∨ (sx = false ∧ 0 ≤ x 0))
    (hsy : (sy = true ∧ x 1 ≤ 1) ∨ (sy = false ∧ 1 ≤ x 1)) :
    hardSquareSectorEquiv x sx sy '' hardSquareSectorDomain h ⊆
      causalHardArmOne ∩ Metric.closedBall x h := by
  have hx' := (mem_frontier_causalHardArmOne_iff x).mp hx
  cases sx <;> cases sy
  all_goals simp at hsx hsy
  all_goals
    rintro z ⟨q, hq, rfl⟩
    change 0 < q.1 ∧ 0 < q.2 ∧ planarRadius q ≤ h at hq
    have hq0 := fst_le_planarRadius q
    have hq1 := snd_le_planarRadius q
    refine ⟨?_, ?_⟩
    · simp only [causalHardArmOne, mem_setOf_eq, hardSquareSectorEquiv_apply_zero,
        hardSquareSectorEquiv_apply_one, Bool.false_eq_true, Bool.true_eq,
        if_true, if_false]
      repeat' apply And.intro
      all_goals linarith [hq.2.2]
    · rw [Metric.mem_closedBall, hardSquareSectorEquiv_dist]
      exact hq.2.2

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareArmOne_contains_sector
lemma hardSquareArmOne_contains_sector {x : Score} {h : ℝ}
    (hx : x ∈ frontier causalHardArmOne) (_hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ sx sy : Bool,
      hardSquareSectorEquiv x sx sy '' hardSquareSectorDomain h ⊆
        causalHardArmOne ∩ Metric.closedBall x h := by
  by_cases hx0 : x 0 ≤ 0 <;> by_cases hx1 : x 1 ≤ 1
  · exact ⟨true, true, hardSquareArmOne_sector_subset hx hh1 true true
      (Or.inl ⟨rfl, hx0⟩) (Or.inl ⟨rfl, hx1⟩)⟩
  · exact ⟨true, false, hardSquareArmOne_sector_subset hx hh1 true false
      (Or.inl ⟨rfl, hx0⟩) (Or.inr ⟨rfl, le_of_not_ge hx1⟩)⟩
  · exact ⟨false, true, hardSquareArmOne_sector_subset hx hh1 false true
      (Or.inr ⟨rfl, le_of_not_ge hx0⟩) (Or.inl ⟨rfl, hx1⟩)⟩
  · exact ⟨false, false, hardSquareArmOne_sector_subset hx hh1 false false
      (Or.inr ⟨rfl, le_of_not_ge hx0⟩) (Or.inr ⟨rfl, le_of_not_ge hx1⟩)⟩

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareArmZero_sector_subset
lemma hardSquareArmZero_sector_subset {x : Score} {h : ℝ}
    (hx : x ∈ frontier causalHardArmOne) (hh1 : h ≤ 1)
    (sx sy : Bool)
    (hedge : (sx = false ∧ x 0 = -1) ∨ (sx = true ∧ x 0 = 1) ∨
      (sy = false ∧ x 1 = 0) ∨ (sy = true ∧ x 1 = 2)) :
    hardSquareSectorEquiv x sx sy '' hardSquareSectorDomain h ⊆
      (causalHardSquare \ causalHardArmOne) ∩ Metric.closedBall x h := by
  have hx' := (mem_frontier_causalHardArmOne_iff x).mp hx
  rintro z ⟨q, hq, rfl⟩
  change 0 < q.1 ∧ 0 < q.2 ∧ planarRadius q ≤ h at hq
  have hq0 := fst_le_planarRadius q
  have hq1 := snd_le_planarRadius q
  have hz0 := hardSquareSectorEquiv_apply_zero x sx sy q
  have hz1 := hardSquareSectorEquiv_apply_one x sx sy q
  have hq0h : q.1 ≤ h := hq0.trans hq.2.2
  have hq1h : q.2 ≤ h := hq1.trans hq.2.2
  have hdiff0 :
      |hardSquareSectorEquiv x sx sy q 0 - x 0| ≤ h := by
    rw [hz0]
    cases sx <;> simp [abs_of_pos hq.1] <;> linarith
  have hdiff1 :
      |hardSquareSectorEquiv x sx sy q 1 - x 1| ≤ h := by
    rw [hz1]
    cases sy <;> simp [abs_of_pos hq.2.1] <;> linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · change -3 ≤ hardSquareSectorEquiv x sx sy q 0 ∧
        hardSquareSectorEquiv x sx sy q 0 ≤ 3
      rw [abs_le] at hdiff0
      constructor <;> linarith
    · change -3 ≤ hardSquareSectorEquiv x sx sy q 1 ∧
        hardSquareSectorEquiv x sx sy q 1 ≤ 3
      rw [abs_le] at hdiff1
      constructor <;> linarith
  · intro hA
    simp only [causalHardArmOne, mem_setOf_eq] at hA
    rcases hedge with ⟨rfl, hedge⟩ | ⟨rfl, hedge⟩ |
      ⟨rfl, hedge⟩ | ⟨rfl, hedge⟩
    · simp at hz0
      rw [hz0, hedge] at hA
      linarith
    · simp at hz0
      rw [hz0, hedge] at hA
      linarith
    · simp at hz1
      rw [hz1, hedge] at hA
      linarith
    · simp at hz1
      rw [hz1, hedge] at hA
      linarith
  · rw [Metric.mem_closedBall, hardSquareSectorEquiv_dist]
    exact hq.2.2

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareArmZero_contains_sector
lemma hardSquareArmZero_contains_sector {x : Score} {h : ℝ}
    (hx : x ∈ frontier causalHardArmOne) (_hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ sx sy : Bool,
      hardSquareSectorEquiv x sx sy '' hardSquareSectorDomain h ⊆
        (causalHardSquare \ causalHardArmOne) ∩ Metric.closedBall x h := by
  rcases (mem_frontier_causalHardArmOne_iff x).mp hx |>.2.2.2.2 with h | h | h | h
  · exact ⟨false, true, hardSquareArmZero_sector_subset hx hh1 false true
      (Or.inl ⟨rfl, h⟩)⟩
  · exact ⟨true, true, hardSquareArmZero_sector_subset hx hh1 true true
      (Or.inr (Or.inl ⟨rfl, h⟩))⟩
  · exact ⟨true, false, hardSquareArmZero_sector_subset hx hh1 true false
      (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))⟩
  · exact ⟨true, true, hardSquareArmZero_sector_subset hx hh1 true true
      (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))⟩

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareGramScoreIntegrand
noncomputable def hardSquareGramScoreIntegrand (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) (h : ℝ) (v : Fin (p + 1) → ℝ)
    (z : Score) : ℝ :=
  h⁻¹ ^ 2 *
    (if (if t then 0 ≤ signedDistance (knownGeometry P) x z
      else signedDistance (knownGeometry P) x z < 0) then 1 else 0) *
    uniformKernel (signedDistance (knownGeometry P) x z / h) *
    (∑ i, v i * (signedDistance (knownGeometry P) x z / h) ^ (i : ℕ)) ^ 2

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareGramScoreIntegrand_measurable
lemma hardSquareGramScoreIntegrand_measurable (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) (h : ℝ) (v : Fin (p + 1) → ℝ) :
    Measurable (hardSquareGramScoreIntegrand P p t x h v) := by
  have hd : Measurable (fun z => signedDistance (knownGeometry P) x z) := by
    unfold signedDistance knownGeometry
    exact ((measurable_const.indicator P.A1_measurable).sub
      (measurable_const.indicator P.A0_measurable)).mul
        (continuous_dist.measurable.comp (measurable_id.prodMk measurable_const))
  have harm : MeasurableSet {z | if t then
      0 ≤ signedDistance (knownGeometry P) x z
      else signedDistance (knownGeometry P) x z < 0} := by
    cases t
    · exact measurableSet_lt hd measurable_const
    · exact measurableSet_le measurable_const hd
  have hind : Measurable (fun z =>
      if (if t then 0 ≤ signedDistance (knownGeometry P) x z
        else signedDistance (knownGeometry P) x z < 0) then (1 : ℝ) else 0) :=
    measurable_const.ite harm measurable_const
  have hk : Measurable (fun z =>
      uniformKernel (signedDistance (knownGeometry P) x z / h)) := by
    unfold uniformKernel
    exact (measurable_const.indicator measurableSet_Icc).comp (hd.div_const h)
  unfold hardSquareGramScoreIntegrand
  fun_prop

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareGramScoreIntegrand_nonneg
lemma hardSquareGramScoreIntegrand_nonneg (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) (h : ℝ) (v : Fin (p + 1) → ℝ) (z : Score) :
    0 ≤ hardSquareGramScoreIntegrand P p t x h v z := by
  unfold hardSquareGramScoreIntegrand
  by_cases ha : if t then 0 ≤ signedDistance (knownGeometry P) x z
      else signedDistance (knownGeometry P) x z < 0
  · rw [if_pos ha]
    have hk : 0 ≤ uniformKernel (signedDistance (knownGeometry P) x z / h) := by
      unfold uniformKernel
      by_cases hu : signedDistance (knownGeometry P) x z / h ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hu]; positivity
      · rw [indicator_of_notMem hu]
    positivity
  · simp [ha]

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareGramScoreIntegrand_integrable
lemma hardSquareGramScoreIntegrand_integrable (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) {h : ℝ} (hh : h ≠ 0)
    (v : Fin (p + 1) → ℝ) :
    Integrable (hardSquareGramScoreIntegrand P p t x h v)
      (P.law.map causalScore) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  letI : IsProbabilityMeasure (P.law.map causalScore) :=
    Measure.isProbabilityMeasure_map (measurable_snd.comp measurable_snd).aemeasurable
  let C : ℝ := |h⁻¹ ^ 2| * (∑ i, |v i|) ^ 2
  apply Integrable.of_bound
    ((hardSquareGramScoreIntegrand_measurable P p t x h v).aestronglyMeasurable)
    C
  filter_upwards with z
  let d := signedDistance (knownGeometry P) x z
  by_cases hu : d / h ∈ Icc (-1 : ℝ) 1
  · have habsu : |d / h| ≤ 1 := abs_le.mpr hu
    have hsum : |∑ i, v i * (d / h) ^ (i : ℕ)| ≤ ∑ i, |v i| := by
      calc
        |∑ i, v i * (d / h) ^ (i : ℕ)| ≤
            ∑ i, |v i * (d / h) ^ (i : ℕ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |v i| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_pow]
          exact mul_le_of_le_one_right (abs_nonneg (v i))
            (pow_le_one₀ (abs_nonneg _) habsu)
    unfold hardSquareGramScoreIntegrand
    change |h⁻¹ ^ 2 *
      (if (if t then 0 ≤ d else d < 0) then 1 else 0) *
      uniformKernel (d / h) * (∑ i, v i * (d / h) ^ (i : ℕ)) ^ 2| ≤ C
    rw [uniformKernel, indicator_of_mem hu]
    by_cases ha : if t then 0 ≤ d else d < 0
    · rw [if_pos ha]
      dsimp [C]
      simp only [mul_one, abs_mul, abs_pow]
      gcongr
    · rw [if_neg ha]
      simp [C]
      positivity
  · have hk : uniformKernel (d / h) = 0 := by
      rw [uniformKernel, indicator_of_notMem hu]
    unfold hardSquareGramScoreIntegrand
    change |h⁻¹ ^ 2 *
      (if (if t then 0 ≤ d else d < 0) then 1 else 0) *
      uniformKernel (d / h) * (∑ i, v i * (d / h) ^ (i : ℕ)) ^ 2| ≤ C
    rw [hk]
    simp [C]
    positivity

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: populationGram_quadratic_eq_scoreIntegral
lemma populationGram_quadratic_eq_scoreIntegral (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) {h : ℝ} (hh : h ≠ 0)
    (v : Fin (p + 1) → ℝ) :
    matrixQuadratic (populationGram P p t x h) v =
      ∫ z, hardSquareGramScoreIntegrand P p t x h v z ∂(P.law.map causalScore) := by
  rw [populationGram_quadratic_eq_integral P p t x hh v]
  symm
  apply integral_map (measurable_snd.comp measurable_snd).aemeasurable
  exact (hardSquareGramScoreIntegrand_integrable P p t x hh v).aestronglyMeasurable

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquareGramScoreIntegrand_on_arm
lemma hardSquareGramScoreIntegrand_on_arm (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) {h : ℝ} (hh : 0 < h)
    (v : Fin (p + 1) → ℝ) (z : Score)
    (hA1 : P.A1 = causalHardArmOne)
    (hA0 : P.A0 = causalHardSquare \ causalHardArmOne)
    (hz : z ∈ (if t then causalHardArmOne else
      causalHardSquare \ causalHardArmOne))
    (hzball : z ∈ Metric.closedBall x h) (hzd : 0 < dist z x) :
    hardSquareGramScoreIntegrand P p t x h v z =
      h⁻¹ ^ 2 *
        (∑ i, v i * (if t then dist z x / h else -(dist z x / h)) ^
          (i : ℕ)) ^ 2 := by
  cases t
  · have hzA0 : z ∈ P.A0 := by simpa [hA0] using hz
    have hzA1 : z ∉ P.A1 := by rw [hA1]; exact hz.2
    have hd : signedDistance (knownGeometry P) x z = -dist z x := by
      simp [signedDistance, knownGeometry, hzA0, hzA1]
    rw [hardSquareGramScoreIntegrand, hd]
    have hk := (uniformKernel_signedDist_eq_one_iff false x z hh).2 hzball
    simp at hk
    simp only [Bool.false_eq_true, if_false]
    rw [if_pos (by linarith), hk]
    simp only [mul_one]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · have hzA1 : z ∈ P.A1 := by simpa [hA1] using hz
    have hzA0 : z ∉ P.A0 := by rw [hA0]; exact fun hz0 => hz0.2 hz
    have hd : signedDistance (knownGeometry P) x z = dist z x := by
      simp [signedDistance, knownGeometry, hzA0, hzA1]
    rw [hardSquareGramScoreIntegrand, hd]
    have hk := (uniformKernel_signedDist_eq_one_iff true x z hh).2 hzball
    simp at hk
    simp only [if_true]
    rw [if_pos hzd.le, hk]
    ring

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquare_sector_scaledPolynomial_integral
lemma hardSquare_sector_scaledPolynomial_integral (p : ℕ) (t : Bool)
    (v : Fin (p + 1) → ℝ) (x : Score) (sx sy : Bool)
    {h : ℝ} (hh : 0 < h) :
    (∫ z : Score in hardSquareSectorEquiv x sx sy '' hardSquareSectorDomain h,
      h⁻¹ ^ 2 *
        (∑ i, v i * (if t then dist z x / h else -(dist z x / h)) ^
          (i : ℕ)) ^ 2) =
      (Real.pi / 2) *
        ∫ u in (0 : ℝ)..1,
          (∑ i, v i * (if t then u else -u) ^ (i : ℕ)) ^ 2 * u := by
  let D : Set (ℝ × ℝ) := hardSquareSectorDomain h
  let e := hardSquareSectorEquiv x sx sy
  let F : Score → ℝ := fun z => h⁻¹ ^ 2 *
    (∑ i, v i * (if t then dist z x / h else -(dist z x / h)) ^
      (i : ℕ)) ^ 2
  have ht := (hardSquareSectorEquiv_volumePreserving x sx sy).setIntegral_preimage_emb
    e.measurableEmbedding F (e '' D)
  rw [e.injective.preimage_image D] at ht
  change (∫ z in e '' D, F z) = _
  rw [← ht]
  calc
    (∫ q in D, F (e q)) =
        ∫ q : ℝ × ℝ in D, h⁻¹ ^ 2 *
          (∑ i, v i * (if t then planarRadius q / h else
            -(planarRadius q / h)) ^ (i : ℕ)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with q
      simp only [F, e, hardSquareSectorEquiv_dist]
    _ = _ := firstQuadrant_scaledPolynomial_integral p t v hh

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquare_populationGram_quadratic_lower
lemma hardSquare_populationGram_quadratic_lower (P : A1A2Law) (p : ℕ)
    (t : Bool) (x : Score) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (v : Fin (p + 1) → ℝ)
    (hSupport : P.support = causalHardSquare)
    (hA1 : P.A1 = causalHardArmOne)
    (hA0 : P.A0 = causalHardSquare \ causalHardArmOne)
    (hBoundary : P.boundary = frontier causalHardArmOne)
    (hx : x ∈ P.boundary) (hdensMeas : Measurable P.density)
    (hdensLower : ∀ z ∈ P.support, (1 / 48 : ℝ) ≤ P.density z) :
    (1 / 48 : ℝ) * (Real.pi / 2) *
        (∫ u in (0 : ℝ)..1,
          (∑ i, v i * (if t then u else -u) ^ (i : ℕ)) ^ 2 * u) ≤
      matrixQuadratic (populationGram P p t x h) v := by
  let G : Score → ℝ := hardSquareGramScoreIntegrand P p t x h v
  let W : Score → ℝ := fun z =>
    (ENNReal.ofReal (P.support.indicator P.density z)).toReal
  let F : Score → ℝ := fun z => h⁻¹ ^ 2 *
    (∑ i, v i * (if t then dist z x / h else -(dist z x / h)) ^
      (i : ℕ)) ^ 2
  have hx' : x ∈ frontier causalHardArmOne := hBoundary ▸ hx
  obtain ⟨sx, sy, hsector⟩ : ∃ sx sy : Bool,
      hardSquareSectorEquiv x sx sy '' hardSquareSectorDomain h ⊆
        (if t then causalHardArmOne else causalHardSquare \ causalHardArmOne) ∩
          Metric.closedBall x h := by
    cases t
    · simpa using hardSquareArmZero_contains_sector hx' hh hh1
    · simpa using hardSquareArmOne_contains_sector hx' hh hh1
  let S : Set Score := hardSquareSectorEquiv x sx sy '' hardSquareSectorDomain h
  have hsupportArm : (if t then causalHardArmOne else
      causalHardSquare \ causalHardArmOne) ⊆ P.support := by
    rw [hSupport]
    cases t
    · exact fun z hz => hz.1
    · simpa using causalHardArmOne_subset_square
  have hFonS : ∀ z ∈ S, G z = F z := by
    intro z hzS
    obtain ⟨q, hq, rfl⟩ := hzS
    have hs := hsector ⟨q, hq, rfl⟩
    have hdist := hardSquareSectorEquiv_dist x sx sy q
    apply hardSquareGramScoreIntegrand_on_arm P p t x hh v _ hA1 hA0
      hs.1 hs.2
    rw [hdist]
    change 0 < Real.sqrt (q.1 ^ 2 + q.2 ^ 2)
    apply Real.sqrt_pos.2
    change 0 < q.1 ^ 2 + q.2 ^ 2
    nlinarith [sq_pos_of_pos hq.1]
  have hWlower : ∀ z ∈ S, (1 / 48 : ℝ) ≤ W z := by
    intro z hzS
    have hzArm := (hsector hzS).1
    have hzSupport := hsupportArm hzArm
    have hd := hdensLower z hzSupport
    dsimp [W]
    rw [indicator_of_mem hzSupport, ENNReal.toReal_ofReal (by linarith)]
    exact hd
  have hsuppMeas : MeasurableSet P.support := by
    rw [hSupport]
    exact causalHardSquare_measurableSet
  have hweightMeas : Measurable (fun z =>
      ENNReal.ofReal (P.support.indicator P.density z)) :=
    (hdensMeas.indicator hsuppMeas).ennreal_ofReal
  have hweightFinite : ∀ᵐ z ∂volume,
      ENNReal.ofReal (P.support.indicator P.density z) < ∞ := by
    filter_upwards with z
    exact ENNReal.ofReal_lt_top
  have hGintMap := hardSquareGramScoreIntegrand_integrable P p t x hh.ne' v
  have hGintDensity : Integrable G
      (volume.withDensity (fun z => ENNReal.ofReal
        (P.support.indicator P.density z))) := by
    rw [← P.marginal_eq]
    exact hGintMap
  have hWGint : Integrable (fun z => W z * G z) volume := by
    have h := (integrable_withDensity_iff hweightMeas hweightFinite).1 hGintDensity
    simpa [W, mul_comm] using h
  have hWGnonneg (z : Score) : 0 ≤ W z * G z := by
    exact mul_nonneg ENNReal.toReal_nonneg
      (hardSquareGramScoreIntegrand_nonneg P p t x h v z)
  have hglobal : (∫ z in S, W z * G z) ≤ ∫ z, W z * G z := by
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ hWGnonneg) hWGint
  have hFmeas : Measurable F := by
    cases t <;> dsimp [F] <;> fun_prop
  have hSmeas : MeasurableSet S := by
    let e := hardSquareSectorEquiv x sx sy
    have hD : MeasurableSet (hardSquareSectorDomain h) := by
      exact ((measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le planarRadius_measurable measurable_const)))
    exact e.measurableEmbedding.measurableSet_image' hD
  have hscaledFint : Integrable (fun z => (1 / 48 : ℝ) * F z)
      (volume.restrict S) := by
    apply Integrable.mono' hWGint.restrict
      ((hFmeas.const_mul (1 / 48 : ℝ)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hSmeas] with z hzS
    rw [← hFonS z hzS]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
      (hardSquareGramScoreIntegrand_nonneg P p t x h v z))]
    exact mul_le_mul_of_nonneg_right (hWlower z hzS)
      (hardSquareGramScoreIntegrand_nonneg P p t x h v z)
  have hsectorCompare :
      (∫ z in S, (1 / 48 : ℝ) * F z) ≤ ∫ z in S, W z * G z := by
    apply integral_mono_ae hscaledFint hWGint.restrict
    filter_upwards [ae_restrict_mem hSmeas] with z hzS
    rw [← hFonS z hzS]
    exact mul_le_mul_of_nonneg_right (hWlower z hzS)
      (hardSquareGramScoreIntegrand_nonneg P p t x h v z)
  rw [populationGram_quadratic_eq_scoreIntegral P p t x hh.ne' v,
    P.marginal_eq,
    integral_withDensity_eq_integral_toReal_smul hweightMeas hweightFinite]
  change _ ≤ ∫ z, W z * G z
  calc
    (1 / 48 : ℝ) * (Real.pi / 2) *
        (∫ u in (0 : ℝ)..1,
          (∑ i, v i * (if t then u else -u) ^ (i : ℕ)) ^ 2 * u) =
      ∫ z in S, (1 / 48 : ℝ) * F z := by
        rw [integral_const_mul]
        rw [hardSquare_sector_scaledPolynomial_integral p t v x sx sy hh]
        ring
    _ ≤ ∫ z in S, W z * G z := hsectorCompare
    _ ≤ _ := hglobal

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: hardSquare_populationGramFloor_eventually
lemma hardSquare_populationGramFloor_eventually (p : ℕ) :
    ∃ L0 : ℝ, 48 ≤ L0 ∧ ∀ (P : A1A2Law) (L : ℝ), L0 ≤ L →
      P.support = causalHardSquare →
      P.A1 = causalHardArmOne →
      P.A0 = causalHardSquare \ causalHardArmOne →
      P.boundary = frontier causalHardArmOne →
      Measurable P.density →
      (∀ z ∈ P.support, (1 / 48 : ℝ) ≤ P.density z) →
      PopulationGramFloor P p L := by
  obtain ⟨c, hc, hcoerce⟩ := signedRadialPolynomialEnergy_coercive p
  let gamma : ℝ := (1 / 48 : ℝ) * (Real.pi / 2) * c
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  refine ⟨max 48 gamma⁻¹, le_max_left _ _, ?_⟩
  intro P L hL hSupport hA1 hA0 hBoundary hdensMeas hdensLower
  have hL48 : 48 ≤ L := (le_max_left 48 gamma⁻¹).trans hL
  have hLpos : 0 < L := (by norm_num : (0 : ℝ) < 48).trans_le hL48
  have hgammaInv : gamma⁻¹ ≤ L := (le_max_right 48 gamma⁻¹).trans hL
  have hInv : L⁻¹ ≤ gamma := by
    apply (inv_le_iff_one_le_mul₀' hLpos).2
    calc
      1 = gamma * gamma⁻¹ := (mul_inv_cancel₀ hgamma.ne').symm
      _ ≤ gamma * L := mul_le_mul_of_nonneg_left hgammaInv hgamma.le
      _ = L * gamma := mul_comm _ _
  intro t x h hx hh hhL v
  have hh1 : h ≤ 1 := by
    exact hhL.trans ((inv_le_one₀ hLpos).2 (by linarith))
  have hlower := hardSquare_populationGram_quadratic_lower P p t x hh hh1 v
    hSupport hA1 hA0 hBoundary hx hdensMeas hdensLower
  have hfactor : 0 ≤ (1 / 48 : ℝ) * (Real.pi / 2) := by positivity
  calc
    L⁻¹ * ∑ i, (v i) ^ 2 ≤ gamma * ∑ i, (v i) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hInv (Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ ≤ (1 / 48 : ℝ) * (Real.pi / 2) *
        (∫ u in (0 : ℝ)..1,
          (∑ i, v i * (if t then u else -u) ^ (i : ℕ)) ^ 2 * u) := by
      dsimp [gamma]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left (hcoerce t v) hfactor)
    _ ≤ matrixQuadratic (populationGram P p t x h) v := hlower

/-- A component of the fixed hard-square population-Gram certificate. -/
-- @node: causalHardA1A2Law_populationGram_certificate
lemma causalHardA1A2Law_populationGram_certificate (p : ℕ) :
    ∃ L0 : ℝ, 48 ≤ L0 ∧ ∀ (L : ℝ), L0 ≤ L →
      ∀ {M : ℕ} (b cA delta w : ℝ) (centers : Fin M → Score)
        (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
        (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
        (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
        (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare),
        let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
          hdelta hw hsep hcell
        PopulationGramFloor P p L := by
  obtain ⟨L0, hL0, hcert⟩ := hardSquare_populationGramFloor_eventually p
  refine ⟨L0, hL0, ?_⟩
  intro L hL M b cA delta w centers omega hb hscale hcA hdelta hw hsep hcell
  let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
    hdelta hw hsep hcell
  have hgeom := causalHardA1A2Law_geometry b cA delta w centers omega hb hscale
    hcA hdelta hw hsep hcell
  apply hcert P L hL hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2
  · exact (causalHardScoreDensity_continuous centers omega hb hscale).measurable
  · intro z hz
    change (1 / 48 : ℝ) ≤
      causalHardScoreDensity b cA delta w centers omega z
    exact (causalHardScoreDensity_mem_Icc (b := b) hcA hdelta hw hsep omega z).1

end CausalSmith.Stat.BddUniformLogPenalty
