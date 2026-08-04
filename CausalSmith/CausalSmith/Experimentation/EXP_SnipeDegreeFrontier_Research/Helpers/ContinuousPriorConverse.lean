import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockPriorHellinger
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.MinimaxRisk

/-!
# Continuous-prior minimax converse
-/

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
open Causalean.Stat

/-- Defines baseline product density. -/
noncomputable def baselineProductDensity
    (B : ℝ) (m : ℕ) (U : Fin m → ℝ) : ℝ :=
  ∏ b, cosSqDensity (B / 2) (U b)
-- @realizes s(halfwidth pinned to B/2 here; positive whenever B > 0)
-- @realizes f_s(product of cosine-squared baseline densities at halfwidth B/2)

/-- Defines baseline product measure. -/
noncomputable def baselineProductMeasure (B : ℝ) (m : ℕ) :
    Measure (Fin m → ℝ) :=
  (Measure.pi (fun _ : Fin m => volume)).withDensity
    (fun U => ENNReal.ofReal (baselineProductDensity B m U))

/-- Establishes the stated mathematical result for baseline product density nonneg. -/
lemma baselineProductDensity_nonneg
    (B : ℝ) (m : ℕ) (hB : 0 < B) :
    0 ≤ baselineProductDensity B m := by
  intro U
  unfold baselineProductDensity
  apply Finset.prod_nonneg
  intro b hb
  unfold cosSqDensity
  split_ifs <;> positivity

/-- Establishes the stated mathematical result for baseline product density integrable. -/
lemma baselineProductDensity_integrable
    (B : ℝ) (m : ℕ) :
    Integrable (baselineProductDensity B m)
      (Measure.pi (fun _ : Fin m => volume)) := by
  unfold baselineProductDensity
  exact Integrable.fintype_prod fun _ => cosSqDensity_integrable (B / 2)

/-- Establishes the stated mathematical result for baseline product density integral one. -/
lemma baselineProductDensity_integral_one
    (B : ℝ) (m : ℕ) (hB : 0 < B) :
    ∫ U, baselineProductDensity B m U
        ∂(Measure.pi (fun _ : Fin m => volume)) = 1 := by
  unfold baselineProductDensity
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  simp_rw [cosSqDensity_integral_one (B / 2) (by linarith)]
  simp

/-- Establishes the stated mathematical result for baseline product measure is probability. -/
lemma baselineProductMeasure_isProbability
    (B : ℝ) (m : ℕ) (hB : 0 < B) :
    IsProbabilityMeasure (baselineProductMeasure B m) := by
  rw [isProbabilityMeasure_iff_real]
  unfold baselineProductMeasure
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ]
  rw [setLIntegral_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (baselineProductDensity_integrable B m)]
  · rw [baselineProductDensity_integral_one B m hB]
    simp
  · exact Filter.Eventually.of_forall
      (baselineProductDensity_nonneg B m hB)

/-- Repeat the observed block statistic over all active units and put zero on
the inactive remainder. -/
noncomputable def blockObservedVector
    (n d : ℕ)
    (x : (Fin n → Bool) × (Fin (blockCount n d) → ℝ)) :
    Fin n → ℝ :=
  fun i =>
    if hi : i.val < activeCount n d then
      x.2 ⟨i.val / d, by
        have hd0 : 0 < d := by
          by_contra hd
          have hd' : d = 0 := Nat.eq_zero_of_not_pos hd
          simp [activeCount, hd'] at hi
        rw [Nat.div_lt_iff_lt_mul hd0]
        simpa [activeCount, blockCount, Nat.mul_comm] using hi⟩
    else 0

/-- Defines block estimator statistic. -/
noncomputable def blockEstimatorStatistic
    (n d : ℕ) (est : Estimator (Fin n)) :
    ((Fin n → Bool) × (Fin (blockCount n d) → ℝ)) → ℝ :=
  by
    classical
    exact fun x => est (fun j i => decide (blockGraph n d j i))
      x.1 (blockObservedVector n d x)

/-- Establishes the stated mathematical result for block observed vector measurable. -/
lemma blockObservedVector_measurable (n d : ℕ) :
    Measurable (blockObservedVector n d) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val < activeCount n d
  · simp only [blockObservedVector, dif_pos hi]
    fun_prop
  · simp [blockObservedVector, hi]

/-- Establishes the stated mathematical result for block estimator statistic measurable. -/
lemma blockEstimatorStatistic_measurable
    (n d : ℕ) (est : Estimator (Fin n))
    (hest : OutcomeMeasurable est) :
    Measurable (blockEstimatorStatistic n d est) := by
  classical
  let G : Fin n → Fin n → Bool :=
    fun j i => decide (blockGraph n d j i)
  have hsum : Measurable (fun x :
      (Fin n → Bool) × (Fin (blockCount n d) → ℝ) =>
      ∑ z : Fin n → Bool,
        if x.1 = z then est G z (blockObservedVector n d x) else 0) := by
    apply Finset.measurable_sum Finset.univ
    intro z hz
    apply Measurable.ite
    · exact (measurableSet_singleton z).preimage measurable_fst
    · apply (hest G z).comp
      exact blockObservedVector_measurable n d
    · exact measurable_const
  convert hsum using 1
  funext x
  simp [blockEstimatorStatistic, G]

/-- Establishes the stated mathematical result for block observed vector translate. -/
lemma blockObservedVector_translate
    (n d β : ℕ) (B p σ : ℝ) (hd : 1 ≤ d)
    (hσ : σ = -1 ∨ σ = 1)
    (z : Fin n → Bool) (U : Fin (blockCount n d) → ℝ) :
    blockObservedVector n d
        (z, fun b => U b +
          σ * tiltAmplitude B β p (blockCount n d) d *
            blockRepresenter β p d (blockAssignment n d b z)) =
      obsOutcome (blockGraph n d) (blockSchedule n d β B p σ hσ U) z := by
  funext i
  by_cases hi : i.val < activeCount n d
  · rw [show blockObservedVector n d
        (z, fun b => U b +
          σ * tiltAmplitude B β p (blockCount n d) d *
            blockRepresenter β p d (blockAssignment n d b z)) i =
        U ⟨i.val / d, by
          simp only [activeCount] at hi
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          simpa [Nat.mul_comm] using hi⟩ +
        σ * tiltAmplitude B β p (blockCount n d) d *
          blockRepresenter β p d
            (blockAssignment n d
              ⟨i.val / d, by
                simp only [activeCount] at hi
                rw [Nat.div_lt_iff_lt_mul (by omega)]
                simpa [Nat.mul_comm] using hi⟩ z) by
      simp [blockObservedVector, hi]]
    exact (potentialOutcome_blockSchedule n d β B p σ hd hσ U i hi z).symm
  · rw [show blockObservedVector n d
        (z, fun b => U b +
          σ * tiltAmplitude B β p (blockCount n d) d *
            blockRepresenter β p d (blockAssignment n d b z)) i = 0 by
      simp [blockObservedVector, hi]]
    exact (potentialOutcome_blockSchedule_inactive
      n d β B p σ hσ U i hi z).symm

/-- A translated-coordinate Fubini identity for bounded measurable test
functions. -/
lemma blockPrior_integral_eq_baseline
    (n d β : ℕ) (B p σ : ℝ)
    (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ((Fin n → Bool) × (Fin (blockCount n d) → ℝ)) → ℝ)
    (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    ∫ x, blockPriorDensity n d β B p σ x * φ x
        ∂blockDominatingMeasure n d =
      ∫ U, baselineProductDensity B (blockCount n d) U *
          ∑ z : Fin n → Bool, assignmentMass n p z *
            φ (z, fun b => U b +
              σ * tiltAmplitude B β p (blockCount n d) d *
                blockRepresenter β p d (blockAssignment n d b z))
        ∂(Measure.pi (fun _ : Fin (blockCount n d) => volume)) := by
  classical
  let μy : Measure (Fin (blockCount n d) → ℝ) :=
    Measure.pi (fun _ : Fin (blockCount n d) => volume)
  let shift : (Fin n → Bool) → Fin (blockCount n d) → ℝ :=
    fun z b => σ * tiltAmplitude B β p (blockCount n d) d *
      blockRepresenter β p d (blockAssignment n d b z)
  have hleftInt :
      Integrable (fun x => blockPriorDensity n d β B p σ x * φ x)
        (blockDominatingMeasure n d) := by
    apply Integrable.mono'
      (blockPriorDensity_integrable n d β B p σ hB hp0 hp1)
      ((blockPriorDensity_integrable n d β B p σ hB hp0 hp1).1.mul
        hφ.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change |blockPriorDensity n d β B p σ x * φ x| ≤
        blockPriorDensity n d β B p σ x
      rw [abs_mul, abs_of_nonneg
        (blockPriorDensity_nonneg n d β B p σ hB hp0 hp1 x),
        abs_of_nonneg (hφ0 x)]
      exact mul_le_of_le_one_right
        (blockPriorDensity_nonneg n d β B p σ hB hp0 hp1 x) (hφ1 x)
  rw [blockDominatingMeasure, integral_prod _ hleftInt]
  have htranslate (z : Fin n → Bool) :
      (∫ y, blockPriorDensity n d β B p σ (z, y) * φ (z, y) ∂μy) =
        assignmentMass n p z *
          ∫ U, baselineProductDensity B (blockCount n d) U *
            φ (z, fun b => U b + shift z b) ∂μy := by
    change (∫ y, (assignmentMass n p z *
        ∏ b, cosSqDensity (B / 2) (y b - shift z b)) * φ (z, y) ∂μy) =
      assignmentMass n p z *
        ∫ U, baselineProductDensity B (blockCount n d) U *
          φ (z, fun b => U b + shift z b) ∂μy
    rw [show
        (∫ y, (assignmentMass n p z *
            ∏ b, cosSqDensity (B / 2) (y b - shift z b)) * φ (z, y) ∂μy) =
          assignmentMass n p z *
            ∫ y, (∏ b, cosSqDensity (B / 2) (y b - shift z b)) *
              φ (z, y) ∂μy by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by ring]
    congr 1
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun y => (∏ b, cosSqDensity (B / 2) (y b - shift z b)) *
        φ (z, y)) (shift z)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun U => by
      change (∏ b, cosSqDensity (B / 2)
          ((U + shift z) b - shift z b)) *
          φ (z, U + shift z) =
        baselineProductDensity B (blockCount n d) U *
          φ (z, fun b => U b + shift z b)
      congr 1
      · unfold baselineProductDensity
        apply Finset.prod_congr rfl
        intro b hb
        congr 2
        simp
  change (∫ x, ∫ y,
      blockPriorDensity n d β B p σ (x, y) * φ (x, y) ∂μy
      ∂Measure.count) =
    ∫ U, baselineProductDensity B (blockCount n d) U *
        ∑ z : Fin n → Bool, assignmentMass n p z *
          φ (z, fun b => U b + shift z b) ∂μy
  simp_rw [htranslate]
  rw [MeasureTheory.integral_fintype]
  · have hcount (z : Fin n → Bool) :
        Measure.count.real ({z} : Set (Fin n → Bool)) = 1 := by
      rw [measureReal_def, Measure.count_apply_finite]
      · simp
      · exact Set.finite_singleton z
    simp_rw [hcount, one_smul]
    rw [show
        (∑ z : Fin n → Bool,
          assignmentMass n p z *
            ∫ U, baselineProductDensity B (blockCount n d) U *
              φ (z, fun b => U b + shift z b) ∂μy) =
        ∫ U, ∑ z : Fin n → Bool,
          assignmentMass n p z *
            (baselineProductDensity B (blockCount n d) U *
              φ (z, fun b => U b + shift z b)) ∂μy by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro z hz
        rw [integral_const_mul]
      · intro z hz
        have hcomp : AEStronglyMeasurable
            (fun U : Fin (blockCount n d) → ℝ =>
              φ (z, fun b => U b + shift z b)) μy :=
          (hφ.comp (measurable_const.prodMk
            (measurable_id.add measurable_const))).aestronglyMeasurable
        have hmul : Integrable
            (fun U : Fin (blockCount n d) → ℝ =>
              baselineProductDensity B (blockCount n d) U *
                φ (z, fun b => U b + shift z b)) μy :=
          (baselineProductDensity_integrable B (blockCount n d)).mono'
            ((baselineProductDensity_integrable B (blockCount n d)).1.mul hcomp)
            (Filter.Eventually.of_forall fun U => by
            change
              |baselineProductDensity B (blockCount n d) U *
                φ (z, fun b => U b + shift z b)| ≤
                baselineProductDensity B (blockCount n d) U
            rw [abs_mul, abs_of_nonneg
              (baselineProductDensity_nonneg B (blockCount n d) hB U),
              abs_of_nonneg (hφ0 _)]
            exact mul_le_of_le_one_right
              (baselineProductDensity_nonneg B (blockCount n d) hB U)
              (hφ1 _))
        exact hmul.const_mul (assignmentMass n p z)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun U => by
      change
        (∑ z : Fin n → Bool, assignmentMass n p z *
          (baselineProductDensity B (blockCount n d) U *
            φ (z, fun b => U b + shift z b))) =
        baselineProductDensity B (blockCount n d) U *
          ∑ z : Fin n → Bool, assignmentMass n p z *
            φ (z, fun b => U b + shift z b)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
  · exact Integrable.of_finite

/-- Establishes the stated mathematical result for block prior law is probability. -/
lemma blockPriorLaw_isProbability
    (n d β : ℕ) (B p σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (hσ : σ = -1 ∨ σ = 1) :
    IsProbabilityMeasure (blockPriorLaw n d β B p σ) := by
  rw [isProbabilityMeasure_iff_real]
  unfold blockPriorLaw
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (blockPriorDensity_integrable n d β B p σ hB hp0 hp1)]
  · rw [blockPriorDensity_integral_one n d β B p σ
      hn hd hdn hB hp0 hp1 hσ]
    simp
  · exact Filter.Eventually.of_forall
      (blockPriorDensity_nonneg n d β B p σ hB hp0 hp1)

/-- Establishes the stated mathematical result for block prior tv dist le sqrt hellinger. -/
lemma blockPrior_tvDist_le_sqrt_hellinger
    (n d β : ℕ) (B p : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1) :
    Causalean.Stat.tvDist
        (blockPriorLaw n d β B p 1)
        (blockPriorLaw n d β B p (-1)) ≤
      Real.sqrt
        (hellingerSqDensity (blockDominatingMeasure n d)
          (blockPriorDensity n d β B p 1)
          (blockPriorDensity n d β B p (-1))) := by
  let μ := blockDominatingMeasure n d
  let f := blockPriorDensity n d β B p 1
  let g := blockPriorDensity n d β B p (-1)
  have hf := blockPriorDensity_integrable n d β B p 1 hB hp0 hp1
  have hg := blockPriorDensity_integrable n d β B p (-1) hB hp0 hp1
  have hf0 := blockPriorDensity_nonneg n d β B p 1 hB hp0 hp1
  have hg0 := blockPriorDensity_nonneg n d β B p (-1) hB hp0 hp1
  have hf1 := blockPriorDensity_integral_one n d β B p 1
    hn hd hdn hB hp0 hp1 (Or.inr rfl)
  have hg1 := blockPriorDensity_integral_one n d β B p (-1)
    hn hd hdn hB hp0 hp1 (Or.inl rfl)
  have htv := tvDist_le_sqrt_two_mul_one_sub_affinity
    μ f g hf hg hf0 hg0 hf1 hg1
  have hhell := hellingerSqDensity_eq_two_mul_one_sub_affinity
    μ f g hf hg hf0 hg0 hf1 hg1
  simpa [blockPriorLaw, μ, f, g, hhell] using htv

/-- Defines miss indicator. -/
noncomputable def missIndicator {Ω : Type*} (T : Ω → ℝ) (θ s : ℝ) (x : Ω) : ℝ :=
  if s ≤ |T x - θ| then 1 else 0

/-- Establishes the stated mathematical result for miss indicator measurable. -/
lemma missIndicator_measurable
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → ℝ)
    (hT : Measurable T) (θ s : ℝ) :
    Measurable (missIndicator T θ s) := by
  unfold missIndicator
  apply Measurable.ite
  · exact measurableSet_le measurable_const
      ((continuous_abs.measurable).comp (hT.sub measurable_const))
  · exact measurable_const
  · exact measurable_const

/-- Establishes the stated mathematical result for miss indicator nonneg. -/
lemma missIndicator_nonneg {Ω : Type*} (T : Ω → ℝ) (θ s : ℝ) :
    0 ≤ missIndicator T θ s := by
  intro x
  unfold missIndicator
  split <;> norm_num

/-- Establishes the stated mathematical result for miss indicator le one. -/
lemma missIndicator_le_one {Ω : Type*} (T : Ω → ℝ) (θ s : ℝ) :
    missIndicator T θ s ≤ 1 := by
  intro x
  unfold missIndicator
  split <;> norm_num

/-- Establishes the stated mathematical result for assignment mass eq bernoulli p. -/
lemma assignmentMass_eq_bernoulli_p
    (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (z : Fin n → Bool) :
    assignmentMass n p z =
      (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
        (fun _ => hp1)).p z := by
  simp [assignmentMass, bernoulliDesign,
    Causalean.Experimentation.DesignBased.prodDesign_p, coinDesign]
  apply Finset.prod_congr rfl
  intro i hi
  cases hzi : z i <;> simp [hzi]

/-- Establishes the stated mathematical result for sum assignment mass one. -/
lemma sum_assignmentMass_one
    (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ z : Fin n → Bool, assignmentMass n p z = 1 := by
  simp_rw [assignmentMass_eq_bernoulli_p n p hp0 hp1]
  exact (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
    (fun _ => hp1)).p_sum

/-- Establishes the stated mathematical result for block prior law real miss. -/
lemma blockPriorLaw_real_miss
    (n d β : ℕ) (B p σ θ s : ℝ)
    (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (est : Estimator (Fin n)) (hest : OutcomeMeasurable est) :
    (blockPriorLaw n d β B p σ).real
        {x | s ≤ |blockEstimatorStatistic n d est x - θ|} =
      ∫ U, baselineProductDensity B (blockCount n d) U *
          ∑ z : Fin n → Bool, assignmentMass n p z *
            missIndicator (blockEstimatorStatistic n d est) θ s
              (z, fun b => U b +
                σ * tiltAmplitude B β p (blockCount n d) d *
                  blockRepresenter β p d (blockAssignment n d b z))
        ∂(Measure.pi (fun _ : Fin (blockCount n d) => volume)) := by
  let T := blockEstimatorStatistic n d est
  have hT : Measurable T := blockEstimatorStatistic_measurable n d est hest
  have hmiss : Measurable (missIndicator T θ s) :=
    missIndicator_measurable T hT θ s
  have hdens := blockPriorDensity_integrable n d β B p σ hB hp0 hp1
  have hset : MeasurableSet {x | s ≤ |T x - θ|} := by
    exact measurableSet_le measurable_const
      ((continuous_abs.measurable).comp (hT.sub measurable_const))
  have hreal :
      (blockPriorLaw n d β B p σ).real {x | s ≤ |T x - θ|} =
        ∫ x in {x | s ≤ |T x - θ|},
          blockPriorDensity n d β B p σ x
            ∂blockDominatingMeasure n d := by
    rw [blockPriorLaw, measureReal_def, withDensity_apply _ hset]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hdens.integrableOn]
    · rw [ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x =>
          blockPriorDensity_nonneg n d β B p σ hB hp0 hp1 x)
    · exact Filter.Eventually.of_forall
        (blockPriorDensity_nonneg n d β B p σ hB hp0 hp1)
  rw [hreal]
  rw [← integral_indicator hset]
  have hind :
      Set.indicator {x | s ≤ |T x - θ|}
          (blockPriorDensity n d β B p σ) =
        fun x => blockPriorDensity n d β B p σ x *
          missIndicator T θ s x := by
    funext x
    by_cases hx : s ≤ |T x - θ|
    · simp [Set.indicator, missIndicator, hx]
    · simp [Set.indicator, missIndicator, hx]
  rw [hind]
  exact blockPrior_integral_eq_baseline n d β B p σ hB hp0 hp1
    (missIndicator T θ s) hmiss
    (missIndicator_nonneg T θ s) (missIndicator_le_one T θ s)

/-- Defines block baseline support. -/
def blockBaselineSupport (B : ℝ) {m : ℕ} (U : Fin m → ℝ) : Prop :=
  ∀ b, |U b| ≤ B / 2

/-- Establishes the stated mathematical result for measurable set block baseline support. -/
lemma measurableSet_blockBaselineSupport (B : ℝ) (m : ℕ) :
    MeasurableSet {U : Fin m → ℝ | blockBaselineSupport B U} := by
  rw [show {U : Fin m → ℝ | blockBaselineSupport B U} =
      ⋂ b : Fin m, {U | |U b| ≤ B / 2} by
    ext U
    simp [blockBaselineSupport]]
  exact MeasurableSet.iInter fun b =>
    measurableSet_le
    ((continuous_abs.measurable).comp (measurable_pi_apply b))
      measurable_const

/-- Establishes the stated mathematical result for baseline product density eq zero of not support. -/
lemma baselineProductDensity_eq_zero_of_not_support
    (B : ℝ) (m : ℕ) (U : Fin m → ℝ)
    (hU : ¬ blockBaselineSupport B U) :
    baselineProductDensity B m U = 0 := by
  classical
  obtain ⟨b, hb⟩ := not_forall.mp hU
  unfold baselineProductDensity
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  unfold cosSqDensity
  rw [if_neg hb]

/-- Defines block miss probability. -/
noncomputable def blockMissProbability
    (n d β : ℕ) (B p σ θ s : ℝ)
    (est : Estimator (Fin n)) (U : Fin (blockCount n d) → ℝ) : ℝ :=
  ∑ z : Fin n → Bool, assignmentMass n p z *
    missIndicator (blockEstimatorStatistic n d est) θ s
      (z, fun b => U b +
        σ * tiltAmplitude B β p (blockCount n d) d *
          blockRepresenter β p d (blockAssignment n d b z))

/-- Establishes the stated mathematical result for block miss probability measurable. -/
lemma blockMissProbability_measurable
    (n d β : ℕ) (B p σ θ s : ℝ)
    (est : Estimator (Fin n)) (hest : OutcomeMeasurable est) :
    Measurable (blockMissProbability n d β B p σ θ s est) := by
  classical
  unfold blockMissProbability
  apply Finset.measurable_sum
  intro z hz
  apply Measurable.const_mul
  exact (missIndicator_measurable _ 
    (blockEstimatorStatistic_measurable n d est hest) θ s).comp
      (measurable_const.prodMk (measurable_id.add measurable_const))

/-- Establishes the stated mathematical result for block miss probability bounds. -/
lemma blockMissProbability_bounds
    (n d β : ℕ) (B p σ θ s : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (est : Estimator (Fin n)) (U : Fin (blockCount n d) → ℝ) :
    0 ≤ blockMissProbability n d β B p σ θ s est U ∧
      blockMissProbability n d β B p σ θ s est U ≤ 1 := by
  constructor
  · unfold blockMissProbability
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg
      (by rw [assignmentMass_eq_bernoulli_p n p hp0 hp1];
          exact (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
            (fun _ => hp1)).p_nonneg z)
      (missIndicator_nonneg _ θ s _)
  · calc
      blockMissProbability n d β B p σ θ s est U ≤
          ∑ z : Fin n → Bool, assignmentMass n p z * 1 := by
        unfold blockMissProbability
        apply Finset.sum_le_sum
        intro z hz
        apply mul_le_mul_of_nonneg_left
          (missIndicator_le_one _ θ s _) 
        rw [assignmentMass_eq_bernoulli_p n p hp0 hp1]
        exact (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
          (fun _ => hp1)).p_nonneg z
      _ = 1 := by
        rw [← Finset.sum_mul, sum_assignmentMass_one n p hp0 hp1]
        ring

/-- The continuous least-favourable prior converts a miss probability into
the coefficient-class worst squared risk.  This is the paper-specific use of
`integral_le_sSup_range_of_isProbabilityMeasure`. -/
lemma blockPrior_miss_sq_le_worstRisk
    (n d β : ℕ) (B p σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 < B) (hβ : 1 ≤ β)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hσ : σ = -1 ∨ σ = 1)
    (est : Estimator (Fin n))
    (hest : AdmissibleEstimator p (le_of_lt hp0) (le_of_lt hp1)
      d β B est) :
    let s := activeShare n d *
      tiltAmplitude B β p (blockCount n d) d
    s ^ 2 * (blockPriorLaw n d β B p σ).real
        {x | s ≤ |blockEstimatorStatistic n d est x - σ * s|} ≤
      worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B est := by
  classical
  let s := activeShare n d *
    tiltAmplitude B β p (blockCount n d) d
  let q := blockMissProbability n d β B p σ (σ * s) s est
  let r : (Fin (blockCount n d) → ℝ) → ℝ :=
    fun U => if blockBaselineSupport B U then s ^ 2 * q U else 0
  let ν := baselineProductMeasure B (blockCount n d)
  let R := worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B est
  have hρ0 : 0 ≤ activeShare n d := by
    unfold activeShare
    positivity
  have hH : 0 < representerMassSup β p :=
    representerMassSup_pos β p hβ hp0 hp1
  have hδ0 :
      0 ≤ tiltAmplitude B β p (blockCount n d) d := by
    unfold tiltAmplitude
    positivity
  have hs0 : 0 ≤ s := mul_nonneg hρ0 hδ0
  have hR0 : 0 ≤ R := by
    let U0 : Fin (blockCount n d) → ℝ := fun _ => 0
    have hU0 : blockBaselineSupport B U0 := by
      intro b
      change |(0 : ℝ)| ≤ B / 2
      norm_num
      linarith
    let M0 := blockScheduleModel n d β B p σ hn hd hdn hB.le hβ
      hp0 hp1 hσ U0 hU0
    have hr0 : 0 ≤ riskAt p (le_of_lt hp0) (le_of_lt hp1) M0 est := by
      unfold riskAt
      exact (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).mse_nonneg _ _
    exact hr0.trans (le_csSup hest.2 (Set.mem_range_self M0))
  have hpoint (U : Fin (blockCount n d) → ℝ) : r U ≤ R := by
    by_cases hU : blockBaselineSupport B U
    · rw [show r U = s ^ 2 * q U by simp [r, hU]]
      let M := blockScheduleModel n d β B p σ hn hd hdn hB.le hβ
        hp0 hp1 hσ U hU
      have hrange :
          riskAt p (le_of_lt hp0) (le_of_lt hp1) M est ≤ R :=
        le_csSup hest.2 (Set.mem_range_self M)
      apply le_trans _ hrange
      unfold riskAt Causalean.Experimentation.DesignBased.FiniteDesign.mse
      unfold q blockMissProbability
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      rw [show s ^ 2 * (assignmentMass n p z *
          missIndicator (blockEstimatorStatistic n d est) (σ * s) s
            (z, fun b => U b +
              σ * tiltAmplitude B β p (blockCount n d) d *
                blockRepresenter β p d (blockAssignment n d b z))) =
        assignmentMass n p z *
          (s ^ 2 * missIndicator (blockEstimatorStatistic n d est)
            (σ * s) s
            (z, fun b => U b +
              σ * tiltAmplitude B β p (blockCount n d) d *
                blockRepresenter β p d (blockAssignment n d b z))) by ring]
      rw [assignmentMass_eq_bernoulli_p n p
        (le_of_lt hp0) (le_of_lt hp1)]
      apply mul_le_mul_of_nonneg_left _ <|
        (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).p_nonneg z
      have ht :
          tte M.edge M.coef = σ * s := by
        change tte (blockGraph n d)
          (blockSchedule n d β B p σ hσ U) = σ * s
        rw [tte_blockSchedule n d β B p σ hn hd hβ hp0 hp1 hσ U]
        dsimp [s]
        ring
      have hobs := blockObservedVector_translate n d β B p σ hd hσ z U
      change s ^ 2 *
          missIndicator (blockEstimatorStatistic n d est) (σ * s) s
            (z, fun b => U b +
              σ * tiltAmplitude B β p (blockCount n d) d *
                blockRepresenter β p d (blockAssignment n d b z)) ≤
        (est (edgeFn M) z (obsOutcome M.edge M.coef z) -
          tte M.edge M.coef) ^ 2
      rw [ht]
      have hedge :
          edgeFn M = fun j i => decide (blockGraph n d j i) := by
        rfl
      rw [hedge]
      change s ^ 2 *
          missIndicator (blockEstimatorStatistic n d est) (σ * s) s
            (z, fun b => U b +
              σ * tiltAmplitude B β p (blockCount n d) d *
                blockRepresenter β p d (blockAssignment n d b z)) ≤
        (est (fun j i => decide (blockGraph n d j i)) z
          (obsOutcome (blockGraph n d)
            (blockSchedule n d β B p σ hσ U) z) - σ * s) ^ 2
      rw [← hobs]
      unfold blockEstimatorStatistic missIndicator
      split_ifs with he
      · simpa [sq_abs] using (sq_le_sq₀ hs0 (abs_nonneg _)|>.2 he)
      · simp
        positivity
    · simp [r, hU, hR0]
  have hrmeas : Measurable r := by
    unfold r
    apply Measurable.ite (measurableSet_blockBaselineSupport B _)
    · exact measurable_const.mul
        (blockMissProbability_measurable n d β B p σ (σ * s) s est hest.1)
    · exact measurable_const
  letI : IsProbabilityMeasure ν :=
    baselineProductMeasure_isProbability B (blockCount n d) hB
  have hrint : Integrable r ν := by
    apply Integrable.of_bound hrmeas.aestronglyMeasurable |R|
    exact Filter.Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact (hpoint U).trans (le_abs_self R)
      · unfold r
        split_ifs
        · exact mul_nonneg (sq_nonneg _) (blockMissProbability_bounds
            n d β B p σ (σ * s) s (le_of_lt hp0) (le_of_lt hp1) est U).1
        · norm_num
  have hrbdd : BddAbove (Set.range r) := ⟨R, by
    rintro _ ⟨U, rfl⟩
    exact hpoint U⟩
  have havg :
      ∫ U, r U ∂ν ≤ sSup (Set.range r) :=
    integral_le_sSup_range_of_isProbabilityMeasure ν r hrint hrbdd
  have hsup : sSup (Set.range r) ≤ R := csSup_le
    (Set.range_nonempty r) (fun _ h => by
      rcases h with ⟨U, rfl⟩
      exact hpoint U)
  calc
    s ^ 2 * (blockPriorLaw n d β B p σ).real
        {x | s ≤ |blockEstimatorStatistic n d est x - σ * s|} =
        ∫ U, r U ∂ν := by
      rw [blockPriorLaw_real_miss n d β B p σ (σ * s) s
        hB hp0 hp1 est hest.1]
      unfold ν baselineProductMeasure
      rw [integral_withDensity_eq_integral_toReal_smul₀]
      · rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun U => by
          change s ^ 2 *
              (baselineProductDensity B (blockCount n d) U * q U) =
            (ENNReal.ofReal
              (baselineProductDensity B (blockCount n d) U)).toReal * r U
          by_cases hU : blockBaselineSupport B U
          · rw [ENNReal.toReal_ofReal
              (baselineProductDensity_nonneg B (blockCount n d) hB U)]
            simp only [r, hU, if_pos]
            unfold q blockMissProbability
            ring
          · rw [baselineProductDensity_eq_zero_of_not_support B _ U hU]
            simp [r, hU]
      · exact (baselineProductDensity_integrable B
          (blockCount n d)).1.aemeasurable.ennreal_ofReal
      · exact Filter.Eventually.of_forall fun U => ENNReal.ofReal_lt_top
    _ ≤ sSup (Set.range r) := havg
    _ ≤ R := hsup

/-- Establishes the stated mathematical result for potential outcome abs le mass. -/
lemma potentialOutcome_abs_le_mass
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : V → V → Prop} {c : V → Finset V → ℝ} {B : ℝ}
    (hmass : BoundedCoeffMass G c B) (i : V) (z : V → Bool) :
    |potentialOutcome G c i z| ≤ B := by
  classical
  unfold potentialOutcome
  calc
    |∑ S ∈ (nbhd G i).powerset,
        c i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0| ≤
      ∑ S ∈ (nbhd G i).powerset,
        |c i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (nbhd G i).powerset, |c i S| := by
      apply Finset.sum_le_sum
      intro S hS
      rw [abs_mul]
      apply mul_le_of_le_one_right (abs_nonneg _)
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
        (fun j _ => by cases z j <;> norm_num)
    _ ≤ B := hmass i

/-- Establishes the stated mathematical result for tte abs le two mul of model class. -/
lemma tte_abs_le_two_mul_of_modelClass
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {d β : ℕ} {B : ℝ} (M : ModelClass V d β B) :
    |tte M.edge M.coef| ≤ 2 * B := by
  classical
  have hcard : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  unfold tte
  rw [abs_mul, abs_of_pos (inv_pos.mpr hcard)]
  calc
    (Fintype.card V : ℝ)⁻¹ *
        |∑ i : V, (potentialOutcome M.edge M.coef i (fun _ => true) -
          potentialOutcome M.edge M.coef i (fun _ => false))| ≤
      (Fintype.card V : ℝ)⁻¹ *
        ∑ i : V, |potentialOutcome M.edge M.coef i (fun _ => true) -
          potentialOutcome M.edge M.coef i (fun _ => false)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ∑ _i : V, (2 * B) := by
      gcongr with i
      calc
        |_ - _| ≤ |potentialOutcome M.edge M.coef i (fun _ => true)| +
            |potentialOutcome M.edge M.coef i (fun _ => false)| := abs_sub _ _
        _ ≤ B + B := add_le_add
          (potentialOutcome_abs_le_mass M.mass_le i _)
          (potentialOutcome_abs_le_mass M.mass_le i _)
        _ = 2 * B := by ring
    _ = 2 * B := by simp [ne_of_gt hcard]

/-- Establishes the stated mathematical result for zero estimator admissible. -/
lemma zeroEstimator_admissible
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) :
    AdmissibleEstimator (V := V) p hp0 hp1 d β B
      (fun _ _ _ => 0) := by
  constructor
  · intro G z
    exact measurable_const
  · refine ⟨4 * B ^ 2, ?_⟩
    rintro _ ⟨M, rfl⟩
    unfold riskAt Causalean.Experimentation.DesignBased.FiniteDesign.mse
    simp only
    change (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E (fun _ => (0 - tte M.edge M.coef) ^ 2) ≤ 4 * B ^ 2
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_const]
    have ht := tte_abs_le_two_mul_of_modelClass M
    have hB0 : 0 ≤ B := by
      let i := Classical.choice ‹Nonempty V›
      exact (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (M.mass_le i)
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (tte M.edge M.coef)) (by positivity)).2 ht
    rw [sq_abs] at hsquare
    nlinarith

/-- Continuous-prior Le Cam converse for the block family. -/
lemma minimaxRisk_blockPrior_lower
    (n d β : ℕ) (B p : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 < B) (hβ : 1 ≤ β)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hhell :
      hellingerSqDensity (blockDominatingMeasure n d)
          (blockPriorDensity n d β B p 1)
          (blockPriorDensity n d β B p (-1)) ≤ 1 / 4) :
    let s := activeShare n d *
      tiltAmplitude B β p (blockCount n d) d
    s ^ 2 / 4 ≤
      minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B := by
  classical
  let s := activeShare n d *
    tiltAmplitude B β p (blockCount n d) d
  have hs0 : 0 ≤ s := by
    unfold s activeShare tiltAmplitude
    have hH := representerMassSup_pos β p hβ hp0 hp1
    positivity
  let Pplus := blockPriorLaw n d β B p 1
  let Pminus := blockPriorLaw n d β B p (-1)
  letI : IsProbabilityMeasure Pplus :=
    blockPriorLaw_isProbability n d β B p 1 hn hd hdn hB hp0 hp1
      (Or.inr rfl)
  letI : IsProbabilityMeasure Pminus :=
    blockPriorLaw_isProbability n d β B p (-1) hn hd hdn hB hp0 hp1
      (Or.inl rfl)
  have htv0 := blockPrior_tvDist_le_sqrt_hellinger
    n d β B p hn hd hdn hB hp0 hp1
  have htv : Causalean.Stat.tvDist Pplus Pminus ≤ 1 / 2 := by
    apply htv0.trans
    calc
      Real.sqrt (hellingerSqDensity (blockDominatingMeasure n d)
          (blockPriorDensity n d β B p 1)
          (blockPriorDensity n d β B p (-1))) ≤
          Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hhell
      _ = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by ring,
          Real.sqrt_sq_eq_abs]
        norm_num
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold minimaxRisk
  apply le_csInf
  · refine ⟨worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
        ((fun _ _ _ => (0 : ℝ)) : Estimator (Fin n)), ?_⟩
    exact ⟨(fun _ _ _ => (0 : ℝ) : Estimator (Fin n)),
      zeroEstimator_admissible p (le_of_lt hp0) (le_of_lt hp1) d β B, rfl⟩
  · intro R hR
    rcases hR with ⟨est, hest, rfl⟩
    let T := blockEstimatorStatistic n d est
    have hT : Measurable T :=
      blockEstimatorStatistic_measurable n d est hest.1
    have hsep : 2 * s ≤ |s - (-s)| := by
      rw [sub_neg_eq_add]
      rw [abs_of_nonneg (add_nonneg hs0 hs0)]
      ring_nf
      exact le_rfl
    have hcam := Causalean.Stat.two_point_lower_bound_of_tvDist_le
      (P₀ := Pplus) (P₁ := Pminus) hT hsep htv
    have hplus := blockPrior_miss_sq_le_worstRisk n d β B p 1
      hn hd hdn hB hβ hp0 hp1 (Or.inr rfl) est hest
    have hminus := blockPrior_miss_sq_le_worstRisk n d β B p (-1)
      hn hd hdn hB hβ hp0 hp1 (Or.inl rfl) est hest
    change (1 - (1 / 2 : ℝ)) / 2 ≤
      max (Pplus.real {x | s ≤ |T x - s|})
        (Pminus.real {x | s ≤ |T x - -s|}) at hcam
    dsimp only at hplus hminus
    simp only [one_mul] at hplus
    simp only [neg_one_mul] at hminus
    change s ^ 2 * Pplus.real {x | s ≤ |T x - s|} ≤
      worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B est at hplus
    change s ^ 2 * Pminus.real {x | s ≤ |T x - -s|} ≤
      worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B est at hminus
    have hmax :
        s ^ 2 * max (Pplus.real {x | s ≤ |T x - s|})
            (Pminus.real {x | s ≤ |T x - -s|}) ≤
          worstRisk p (le_of_lt hp0) (le_of_lt hp1) d β B est := by
      by_cases hle :
          Pplus.real {x | s ≤ |T x - s|} ≤
            Pminus.real {x | s ≤ |T x - -s|}
      · rw [max_eq_right hle]
        exact hminus
      · rw [max_eq_left (le_of_not_ge hle)]
        exact hplus
    have hquarter :
        (1 / 4 : ℝ) ≤
          max (Pplus.real {x | s ≤ |T x - s|})
            (Pminus.real {x | s ≤ |T x - -s|}) := by
      convert hcam using 1 <;> norm_num
    nlinarith [mul_le_mul_of_nonneg_left hquarter (sq_nonneg s)]

/-- An estimator's worst-case mean-squared error over the coefficient-mass model class is
unchanged when the assignment probability, its bounds, model-class parameters, and estimator
are replaced by equal values. -/
add_decl_doc worstRisk.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
