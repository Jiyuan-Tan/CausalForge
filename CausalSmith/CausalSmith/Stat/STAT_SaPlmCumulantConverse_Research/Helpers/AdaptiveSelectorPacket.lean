import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.PopulationNumeratorBound
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.SelectorSoundness
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.T2_ExactContourIdentification
import Mathlib.MeasureTheory.Measure.Map

/-!
# Good-event assembly for the adaptive contour selector

This module packages the deterministic split-fold facts, measurable empirical
transform errors, and selected-contour certificate used by the root-risk proof.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace CausalSmith.Stat.SaPlmCumulantConverse

private lemma fold0_card (n : ℕ) : (fold0 n).card = n / 2 := by
  unfold fold0
  rw [Fin.card_filter_val_lt, min_eq_right (Nat.div_le_self n 2)]

private lemma fold1_card (n : ℕ) : (fold1 n).card = n - n / 2 := by
  rw [show fold1 n = (Finset.univ : Finset (Fin n)) \ fold0 n by
    ext i
    simp [fold0, fold1]
    ]
  rw [Finset.card_sdiff]
  simp [fold0_card]

private lemma inferenceFold_card (n : ℕ) (a : Fin 2) :
    (inferenceFold n a).card = if a = 0 then n / 2 else n - n / 2 := by
  unfold inferenceFold
  split <;> simp_all [fold0_card, fold1_card]

private lemma inferenceFold_nonempty (n : ℕ) (hn : 2 ≤ n) (a : Fin 2) :
    (inferenceFold n a).Nonempty := by
  apply Finset.card_pos.mp
  rw [inferenceFold_card]
  split
  · omega
  · omega

private lemma inferenceFold_card_third (n : ℕ) (hn : 2 ≤ n) (a : Fin 2) :
    n ≤ 3 * (inferenceFold n a).card := by
  rw [inferenceFold_card]
  split <;> omega

private lemma measurable_diskSupNorm_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] (H : Ω → ℂ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hmeas : ∀ z, ‖z‖ ≤ R → Measurable (fun ω ↦ ‖H ω z‖))
    (hcont : ∀ ω, ContinuousOn (H ω) {z : ℂ | ‖z‖ ≤ R}) :
    Measurable (diskSupNorm H R) := by
  let S : Set ℂ := {z | ‖z‖ ≤ R}
  letI : Nonempty S := ⟨⟨0, by simpa [S] using hR⟩⟩
  let seq : ℕ → S := TopologicalSpace.denseSeq S
  let D : Set ℂ := Subtype.val '' Set.range seq
  have hD : D.Countable := (Set.countable_range seq).image Subtype.val
  have hDS : D ⊆ S := by
    rintro z ⟨y, hy, rfl⟩
    rcases hy with ⟨k, rfl⟩
    exact (seq k).property
  apply measurable_diskSupNorm_of_countable_dense H R D hD
  · intro z hz
    exact hmeas z (hDS hz)
  intro ω
  rw [diskSupNorm_eq_sSup_image]
  apply Causalean.Mathlib.MeasureTheory.sSup_image_eq_of_dense_tendsto
      (fun z ↦ ‖H ω z‖) S D hDS
  · have hcompact : IsCompact S := by
      simpa [S, Metric.closedBall, dist_zero_right] using
        (isCompact_closedBall (0 : ℂ) R)
    exact hcompact.bddAbove_image (hcont ω).norm
  intro x hx
  have hdense : Dense (Set.range seq) :=
    TopologicalSpace.denseRange_denseSeq S
  have hxcl : (⟨x, hx⟩ : S) ∈ closure (Set.range seq) := by
    rw [(dense_iff_closure_eq).mp hdense]
    exact Set.mem_univ _
  obtain ⟨q, hq, hqt⟩ := mem_closure_iff_seq_limit.mp hxcl
  refine ⟨fun k ↦ (q k).1, ?_, ?_⟩
  · intro k
    exact ⟨q k, hq k, rfl⟩
  · have hcsub : Continuous (fun y : S ↦ ‖H ω y.1‖) :=
      (hcont ω).norm.comp_continuous continuous_subtype_val (fun y ↦ y.property)
    simpa [Function.comp_def] using (hcsub.tendsto ⟨x, hx⟩).comp hqt

private lemma weightedTransform_continuousOn_of_factorial_envelope
    {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P]
    (W V : X → ℝ) (hW : Measurable W) (hV : Measurable V)
    (R : ℝ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C)
    (henv : ∫⁻ o, ENNReal.ofReal
      ((|W o| * Real.exp (2 * R * |V o|)) ^ 2) ∂P ≤ ENNReal.ofReal (C ^ 2)) :
    ContinuousOn (weightedTransform P W V) {z : ℂ | ‖z‖ ≤ R} := by
  let f : ℕ → X → ℝ := fun k o ↦ W o * V o ^ k / k.factorial
  have hf (k : ℕ) : MemLp (f k) 2 P ∧
      eLpNorm (f k) 2 P ≤ ENNReal.ofReal (C / (2 * R) ^ k) := by
    simpa [f] using factorial_coefficient_memLp_two P W V hW hV R hR C hC henv k
  have hmean (k : ℕ) : |∫ o, f k o ∂P| ≤ C / (2 * R) ^ k := by
    have hle := Causalean.Stat.abs_integral_le_eLpNorm_two (hf k).1
    exact hle.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hf k).2).trans_eq
      (ENNReal.toReal_ofReal
        (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _))))
  let u : ℕ → ℝ := fun k ↦ (C / (2 * R) ^ k) * R ^ k
  have hu : Summable u := by
    refine ((summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C).congr (fun k ↦ ?_)
    symm
    have hR0 : R ≠ 0 := hR.ne'
    dsimp [u]
    field_simp
    have ht : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
      rw [one_div, inv_pow, inv_mul_cancel₀]
      positivity
    calc
      C * R ^ k = C * R ^ k * 1 := by ring
      _ = C * R ^ k * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by rw [ht]
      _ = _ := by ring
  let series : ℂ → ℂ := fun z ↦
    ∑' k : ℕ, ((∫ o, f k o ∂P : ℝ) : ℂ) * z ^ k
  have hseries : ContinuousOn series {z : ℂ | ‖z‖ ≤ R} := by
    apply continuousOn_tsum (u := u)
    · intro k
      fun_prop
    · exact hu
    intro k z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    exact mul_le_mul (hmean k) (pow_le_pow_left₀ (norm_nonneg z) hz k)
      (pow_nonneg (norm_nonneg z) k)
      (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) k))
  apply hseries.congr
  intro z hz
  change ‖z‖ ≤ R at hz
  have hdom : Integrable (fun o ↦ |W o| * Real.exp (2 * ‖z‖ * |V o|)) P := by
    let E : X → ℝ := fun o ↦ |W o| * Real.exp (2 * R * |V o|)
    have hEmeas : Measurable E := hW.abs.mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul hV.abs))
    have hEmem := memLp_two_and_eLpNorm_le_of_sq_lintegral_le P hEmeas hC henv |>.1
    apply (hEmem.integrable (by norm_num)).mono'
      ((hW.abs.fun_mul (Real.continuous_exp.measurable.comp
        (measurable_const.fun_mul hV.abs))).aestronglyMeasurable)
    filter_upwards [] with o
    simp only [Function.comp_apply, E, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by gcongr)) (abs_nonneg _)
  have hpop := weighted_exp_integral_eq_moment_tsum P W V hW hV z hdom
  symm
  rw [weightedTransform, hpop]
  apply tsum_congr
  intro k
  dsimp [series, f]
  rw [integral_div]
  push_cast
  ring

/-- The split-fold empirical residual-transform supremum error is Borel
measurable as a function of the finite sample. -/
lemma measurable_residual_transformSupError
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (hclass : NonGaussianClass p p.n m) :
    Measurable (transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n a) z)
      (residualMGF p m p.n) (searchRadius p)) := by
  let A := 2 * Real.exp (8 * searchRadius p * p.Cg +
    4 * searchRadius p ^ 2 * p.psieta ^ 2)
  let C := Real.sqrt A
  have hR : 0 < searchRadius p := by
    unfold searchRadius
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henv : ∫⁻ o, ENNReal.ofReal
      ((|(1 : ℝ)| * Real.exp
        (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal (C ^ 2) := by
    have h := learnedResidual_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    rw [show C ^ 2 = A by exact Real.sq_sqrt hA]
    simpa [A, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have hcont := weightedTransform_continuousOn_of_factorial_envelope
    (P := m.P) (fun _ : Obs Xspace ↦ (1 : ℝ)) (learnedResidual p m p.n)
    measurable_const hZmeas (searchRadius p) hR C (Real.sqrt_nonneg A) henv
  have hcontF : ContinuousOn (residualMGF p m p.n)
      {z : ℂ | ‖z‖ ≤ searchRadius p} := by
    rw [show residualMGF p m p.n = weightedTransform m.P
        (fun _ : Obs Xspace ↦ (1 : ℝ)) (learnedResidual p m p.n) by
      funext z
      simp [residualMGF, weightedTransform, ProbabilityTheory.complexMGF]]
    exact hcont
  rw [transformSupError_eq_diskSupNorm]
  apply measurable_diskSupNorm_of_continuous _ (searchRadius p) hR.le
  · intro z _hz
    have hg := m.gcode_measurable p.n
    unfold empiricalF learnedResidual treatment barG covariate
    fun_prop
  · intro data
    have hemp : Continuous
        (empiricalF p m p.n data (inferenceFold p.n a)) := by
      unfold empiricalF
      fun_prop
    exact hemp.continuousOn.sub hcontF

/-- The split-fold empirical outcome-transform supremum error is Borel
measurable as a function of the finite sample. -/
lemma measurable_outcome_transformSupError
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (hclass : NonGaussianClass p p.n m) :
    Measurable (transformSupError
      (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n a) z)
      (outcomeResidualTransform p m p.n) (searchRadius p)) := by
  let A := 64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 +
      4 * p.psixi ^ 4) +
    2 * Real.exp (16 * searchRadius p * p.Cg +
      16 * searchRadius p ^ 2 * p.psieta ^ 2)
  let C := Real.sqrt A
  have hR : 0 < searchRadius p := by
    unfold searchRadius
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henv : ∫⁻ o, ENNReal.ofReal
      ((|outcome o| * Real.exp
        (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal (C ^ 2) := by
    have h := outcome_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    rw [show C ^ 2 = A by exact Real.sq_sqrt hA]
    exact h
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have hcont := weightedTransform_continuousOn_of_factorial_envelope
    (P := m.P) outcome (learnedResidual p m p.n) measurable_snd.snd hZmeas
    (searchRadius p) hR C (Real.sqrt_nonneg A) henv
  have hcontG : ContinuousOn (outcomeResidualTransform p m p.n)
      {z : ℂ | ‖z‖ ≤ searchRadius p} := by
    exact hcont
  rw [transformSupError_eq_diskSupNorm]
  apply measurable_diskSupNorm_of_continuous _ (searchRadius p) hR.le
  · intro z _hz
    have hg := m.gcode_measurable p.n
    unfold empiricalG learnedResidual treatment barG covariate outcome
    fun_prop
  · intro data
    have hemp : Continuous
        (empiricalG p m p.n data (inferenceFold p.n a)) := by
      unfold empiricalG
      fun_prop
    exact hemp.continuousOn.sub hcontG

private lemma weighted_transformSupError_le_centered_factorial_majorant
    {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P]
    {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty)
    (W V : X → ℝ) (hW : Measurable W) (hV : Measurable V)
    (R : ℝ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C)
    (henv : ∫⁻ o, ENNReal.ofReal
      ((|W o| * Real.exp (2 * R * |V o|)) ^ 2) ∂P ≤ ENNReal.ofReal (C ^ 2))
    (data : Fin n → X) :
    let c : ℕ → ℝ := fun k ↦ (I.card : ℝ)⁻¹ * ∑ i ∈ I,
      (W (data i) * V (data i) ^ k / k.factorial -
        ∫ o, W o * V o ^ k / k.factorial ∂P)
    transformSupError
        (fun _data z ↦ (I.card : ℂ)⁻¹ * ∑ i ∈ I,
          (W (data i) : ℂ) * Complex.exp (z * V (data i)))
        (weightedTransform P W V) R data ≤
      ∑' k, |c k| * R ^ k := by
  dsimp only
  let f : ℕ → X → ℝ := fun k o ↦ W o * V o ^ k / k.factorial
  let c : ℕ → ℝ := fun k ↦ (I.card : ℝ)⁻¹ * ∑ i ∈ I,
    (f k (data i) - ∫ o, f k o ∂P)
  have hf (k : ℕ) : MemLp (f k) 2 P ∧
      eLpNorm (f k) 2 P ≤ ENNReal.ofReal (C / (2 * R) ^ k) := by
    simpa [f] using factorial_coefficient_memLp_two P W V hW hV R hR C hC henv k
  have hmean_bound (k : ℕ) : |∫ o, f k o ∂P| ≤ C / (2 * R) ^ k := by
    have hle := Causalean.Stat.abs_integral_le_eLpNorm_two (hf k).1
    exact hle.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hf k).2).trans_eq
      (ENNReal.toReal_ofReal
        (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _))))
  have hcsum : Summable (fun k ↦ |c k| * R ^ k) := by
    have hpoint (x : X) : Summable (fun k ↦ |f k x| * R ^ k) := by
      refine ((Real.summable_pow_div_factorial (|V x| * R)).mul_left |W x|).congr
        (fun k ↦ ?_)
      symm
      simp only [f, abs_div, abs_mul, abs_pow, Nat.cast_nonneg, abs_of_nonneg,
        mul_pow]
      ring
    have hfinite : Summable (fun k ↦ ∑ i ∈ I, |f k (data i)| * R ^ k) := by
      classical
      have haux : ∀ s : Finset (Fin n),
          Summable (fun k ↦ ∑ i ∈ s, |f k (data i)| * R ^ k) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            simp_rw [Finset.sum_insert hi]
            exact (hpoint (data i)).add ih
      exact haux I
    have hmean : Summable (fun k ↦ |∫ o, f k o ∂P| * R ^ k) := by
      apply Summable.of_nonneg_of_le
        (fun k ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hR.le _))
        (fun k ↦ mul_le_mul_of_nonneg_right (hmean_bound k) (pow_nonneg hR.le _))
      refine ((summable_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C).congr (fun k ↦ ?_)
      symm
      have hR0 : R ≠ 0 := hR.ne'
      field_simp
      have ht : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
        rw [one_div, inv_pow, inv_mul_cancel₀]
        positivity
      calc
        C * R ^ k = C * R ^ k * 1 := by ring
        _ = C * R ^ k * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by rw [ht]
        _ = _ := by ring
    apply Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hR.le _)) (fun k ↦ ?_)
      ((hfinite.mul_left (I.card : ℝ)⁻¹).add hmean)
    have hinv : 0 ≤ (I.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    dsimp [c]
    calc
      |(I.card : ℝ)⁻¹ * ∑ i ∈ I, (f k (data i) - ∫ o, f k o ∂P)| * R ^ k =
          (I.card : ℝ)⁻¹ * |∑ i ∈ I, (f k (data i) - ∫ o, f k o ∂P)| *
            R ^ k := by rw [abs_mul, abs_of_nonneg hinv]
      _ ≤ (I.card : ℝ)⁻¹ *
          (∑ i ∈ I, |f k (data i) - ∫ o, f k o ∂P|) * R ^ k := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (I.card : ℝ)⁻¹ *
          (∑ i ∈ I, (|f k (data i)| + |∫ o, f k o ∂P|)) * R ^ k := by
        gcongr with i hi
        exact abs_sub _ _
      _ = (I.card : ℝ)⁻¹ * (∑ i ∈ I, |f k (data i)| * R ^ k) +
          |∫ o, f k o ∂P| * R ^ k := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        have hcard : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI.card_pos.ne'
        field_simp
        rw [add_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have herr : transformSupError
      (fun _data z ↦ (I.card : ℂ)⁻¹ * ∑ i ∈ I,
        (W (data i) : ℂ) * Complex.exp (z * V (data i)))
      (weightedTransform P W V) R data =
      diskSupNorm (fun _data z ↦ ∑' k, (c k : ℂ) * z ^ k) R data := by
    rw [transformSupError_eq_diskSupNorm, diskSupNorm_eq_sSup_image,
      diskSupNorm_eq_sSup_image]
    apply congrArg sSup
    ext x
    constructor <;> rintro ⟨z, hz, rfl⟩ <;> refine ⟨z, hz, ?_⟩
    · symm
      exact congrArg norm (by simpa [c, f] using
        (weighted_empirical_sub_eq_centered_factorial_series I hI W V hW hV
          R hR C hC henv data z hz))
    · exact congrArg norm (by simpa [c, f] using
        (weighted_empirical_sub_eq_centered_factorial_series I hI W V hW hV
          R hR C hC henv data z hz))
  rw [herr]
  calc
    diskSupNorm (fun _data z ↦ ∑' k, (c k : ℂ) * z ^ k) R data ≤
        ∑' k, ‖(c k : ℂ)‖ * R ^ k :=
      diskSupNorm_tsum_mul_pow_le (fun _ k ↦ (c k : ℂ)) hR.le data
        (by simpa using hcsum)
    _ = _ := by
      apply tsum_congr
      intro k
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rfl

/-- Absolute centered-factorial coefficient majorant for the residual
transform on one inference fold. -/
def residualTransformMajorant
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (data : Fin p.n → Obs Xspace) : ℝ :=
  let I := inferenceFold p.n a
  ∑' k : ℕ, |(I.card : ℝ)⁻¹ * ∑ i ∈ I,
      (learnedResidual p m p.n (data i) ^ k / k.factorial -
        ∫ o, learnedResidual p m p.n o ^ k / k.factorial ∂m.P)| *
    searchRadius p ^ k

/-- Absolute centered-factorial coefficient majorant for the
outcome-weighted transform on one inference fold. -/
def outcomeTransformMajorant
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (data : Fin p.n → Obs Xspace) : ℝ :=
  let I := inferenceFold p.n a
  ∑' k : ℕ, |(I.card : ℝ)⁻¹ * ∑ i ∈ I,
      (outcome (data i) * learnedResidual p m p.n (data i) ^ k / k.factorial -
        ∫ o, outcome o * learnedResidual p m p.n o ^ k / k.factorial ∂m.P)| *
    searchRadius p ^ k

/-- The residual-transform disk error is pointwise dominated by its
centered factorial-series majorant. -/
lemma residual_transformSupError_le_majorant
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (hn : 2 ≤ p.n) (hclass : NonGaussianClass p p.n m)
    (data : Fin p.n → Obs Xspace) :
    transformSupError
        (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n a) z)
        (residualMGF p m p.n) (searchRadius p) data ≤
      residualTransformMajorant p m a data := by
  let A := 2 * Real.exp (8 * searchRadius p * p.Cg +
    4 * searchRadius p ^ 2 * p.psieta ^ 2)
  let C := Real.sqrt A
  have hR : 0 < searchRadius p := by
    unfold searchRadius
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henv : ∫⁻ o, ENNReal.ofReal
      ((|(1 : ℝ)| * Real.exp
        (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal (C ^ 2) := by
    have h := learnedResidual_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    rw [show C ^ 2 = A by exact Real.sq_sqrt hA]
    simpa [A, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  rw [show residualMGF p m p.n = weightedTransform m.P
      (fun _ : Obs Xspace ↦ (1 : ℝ)) (learnedResidual p m p.n) by
    funext z
    simp [residualMGF, weightedTransform, ProbabilityTheory.complexMGF]]
  have h := weighted_transformSupError_le_centered_factorial_majorant
      (P := m.P) (inferenceFold p.n a) (inferenceFold_nonempty p.n hn a)
      (fun _ : Obs Xspace ↦ (1 : ℝ)) (learnedResidual p m p.n)
      measurable_const hZmeas (searchRadius p) hR C (Real.sqrt_nonneg A) henv data
  simp [residualTransformMajorant, empiricalF, residualMGF, weightedTransform,
    ProbabilityTheory.complexMGF] at h ⊢
  exact h

/-- The outcome-transform disk error is pointwise dominated by its centered
factorial-series majorant. -/
lemma outcome_transformSupError_le_majorant
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (hn : 2 ≤ p.n) (hclass : NonGaussianClass p p.n m)
    (data : Fin p.n → Obs Xspace) :
    transformSupError
        (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n a) z)
        (outcomeResidualTransform p m p.n) (searchRadius p) data ≤
      outcomeTransformMajorant p m a data := by
  let A := 64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 +
      4 * p.psixi ^ 4) +
    2 * Real.exp (16 * searchRadius p * p.Cg +
      16 * searchRadius p ^ 2 * p.psieta ^ 2)
  let C := Real.sqrt A
  have hR : 0 < searchRadius p := by
    unfold searchRadius
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henv : ∫⁻ o, ENNReal.ofReal
      ((|outcome o| * Real.exp
        (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal (C ^ 2) := by
    have h := outcome_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    rw [show C ^ 2 = A by exact Real.sq_sqrt hA]
    exact h
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have h := weighted_transformSupError_le_centered_factorial_majorant
      (P := m.P) (inferenceFold p.n a) (inferenceFold_nonempty p.n hn a)
      outcome (learnedResidual p m p.n) measurable_snd.snd hZmeas
      (searchRadius p) hR C (Real.sqrt_nonneg A) henv data
  simp [outcomeTransformMajorant, empiricalG, outcomeResidualTransform] at h ⊢
  exact h

private lemma transformSupError_nonneg
    (Fhat : Ω → ℂ → ℂ) (F : ℂ → ℂ) (R : ℝ) (w : Ω) :
    0 ≤ transformSupError Fhat F R w := by
  unfold transformSupError
  apply Real.sSup_nonneg
  rintro x ⟨z, hz, rfl⟩
  exact norm_nonneg _

private lemma norm_sub_le_transformSupError
    (Fhat : Ω → ℂ → ℂ) (F : ℂ → ℂ) (R : ℝ) (w : Ω)
    (hcont : ContinuousOn (fun z ↦ Fhat w z - F z) {z : ℂ | ‖z‖ ≤ R})
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Fhat w z - F z‖ ≤ transformSupError Fhat F R w := by
  unfold transformSupError
  apply le_csSup
  · have hcompact : IsCompact {z : ℂ | ‖z‖ ≤ R} := by
      simpa [Metric.closedBall, dist_zero_right] using
        (isCompact_closedBall (0 : ℂ) R)
    have heq : {x : ℝ | ∃ z : ℂ, ‖z‖ ≤ R ∧
        x = ‖Fhat w z - F z‖} =
        (fun z : ℂ ↦ ‖Fhat w z - F z‖) '' {z : ℂ | ‖z‖ ≤ R} := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [heq]
    exact hcompact.bddAbove_image hcont.norm
  · exact ⟨z, hz, rfl⟩

private lemma semanticEmpiricalF_analyticOnNhd
    {Xspace : Type*}
    (p : Parameters) (gcode : ℕ → Xspace → ℝ)
    (data : Fin p.n → Obs Xspace) (I : Finset (Fin p.n)) (derivative : ℕ) :
    AnalyticOnNhd ℂ (semanticEmpiricalF p gcode data I derivative) Set.univ := by
  unfold semanticEmpiricalF
  apply analyticOnNhd_const.mul
  have hexp (i : Fin p.n) : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ Complex.exp
        (z * (semanticEmpiricalResidual p gcode data i : ℂ))) Set.univ := by
    exact analyticOnNhd_cexp.comp
      (analyticOnNhd_id.mul analyticOnNhd_const) (mapsTo_univ _ _)
  have hsum : AnalyticOnNhd ℂ
      (∑ i ∈ I, fun z : ℂ ↦
        ((semanticEmpiricalResidual p gcode data i ^ derivative : ℝ) : ℂ) *
          Complex.exp (z * semanticEmpiricalResidual p gcode data i)) Set.univ :=
    Finset.analyticOnNhd_sum I (fun i hi ↦ analyticOnNhd_const.mul (hexp i))
  convert hsum using 1
  case e'_7 => rfl
  case e'_8 => rfl
  funext z
  simp

private lemma semanticEmpiricalG_analyticOnNhd
    {Xspace : Type*}
    (p : Parameters) (gcode : ℕ → Xspace → ℝ)
    (data : Fin p.n → Obs Xspace) (I : Finset (Fin p.n)) (derivative : ℕ) :
    AnalyticOnNhd ℂ (semanticEmpiricalG p gcode data I derivative) Set.univ := by
  unfold semanticEmpiricalG
  apply analyticOnNhd_const.mul
  have hexp (i : Fin p.n) : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ Complex.exp
        (z * (semanticEmpiricalResidual p gcode data i : ℂ))) Set.univ := by
    exact analyticOnNhd_cexp.comp
      (analyticOnNhd_id.mul analyticOnNhd_const) (mapsTo_univ _ _)
  have hsum : AnalyticOnNhd ℂ
      (∑ i ∈ I, fun z : ℂ ↦
        ((outcome (data i) * semanticEmpiricalResidual p gcode data i ^ derivative : ℝ) : ℂ) *
          Complex.exp (z * semanticEmpiricalResidual p gcode data i)) Set.univ :=
    Finset.analyticOnNhd_sum I (fun i hi ↦ analyticOnNhd_const.mul (hexp i))
  convert hsum using 1
  case e'_7 => rfl
  case e'_8 => rfl
  funext z
  simp

private lemma semanticEmpiricalF_zero_eq_empiricalF
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p)
    (data : Fin p.n → Obs Xspace) (I : Finset (Fin p.n)) (hI : I.Nonempty) :
    semanticEmpiricalF p m.gcode data I 0 = empiricalF p m p.n data I := by
  funext z
  unfold semanticEmpiricalF semanticEmpiricalResidual empiricalF learnedResidual
  have hc : (1 : ℝ) ≤ I.card := by exact_mod_cast hI.card_pos
  rw [max_eq_left hc]
  simp [barG]

private lemma semanticEmpiricalG_zero_eq_empiricalG
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p)
    (data : Fin p.n → Obs Xspace) (I : Finset (Fin p.n)) (hI : I.Nonempty) :
    semanticEmpiricalG p m.gcode data I 0 = empiricalG p m p.n data I := by
  funext z
  unfold semanticEmpiricalG semanticEmpiricalResidual empiricalG learnedResidual
  have hc : (1 : ℝ) ≤ I.card := by exact_mod_cast hI.card_pos
  rw [max_eq_left hc]
  simp [barG]

private lemma deriv_semanticEmpiricalF_zero
    {Xspace : Type*}
    (p : Parameters) (gcode : ℕ → Xspace → ℝ)
    (data : Fin p.n → Obs Xspace) (I : Finset (Fin p.n)) (z : ℂ) :
    deriv (semanticEmpiricalF p gcode data I 0) z =
      semanticEmpiricalF p gcode data I 1 z := by
  apply HasDerivAt.deriv
  unfold semanticEmpiricalF
  convert (HasDerivAt.fun_sum (u := I) (fun i hi ↦ by
    have hin : HasDerivAt
        (fun w : ℂ ↦ w * (semanticEmpiricalResidual p gcode data i : ℂ))
        (semanticEmpiricalResidual p gcode data i : ℂ) z := by
      exact ((hasDerivAt_id z).mul_const
        (semanticEmpiricalResidual p gcode data i : ℂ)).congr_deriv (by ring)
    exact (Complex.hasDerivAt_exp _).comp z hin)).const_mul
      (((max I.card 1 : ℝ) : ℂ)⁻¹) using 1
  case e'_4 => rfl
  case e'_8 =>
    funext w
    simp
  case e'_9 =>
    apply congrArg
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring

private lemma selectedContourFrom_some_best
    (B : ContourBankData) (outcomes : Fin (B.JBase + 1) → PilotOutcome)
    (hexists : ∃ j, (outcomes j).admissible B = true) :
    ∃ j, selectedContourFrom B outcomes = some j ∧
      (outcomes j).admissible B = true ∧
      ∀ k, (outcomes k).admissible B = true →
        (outcomes k).modulus.lo ≤ (outcomes j).modulus.lo := by
  let A : Finset (Fin (B.JBase + 1)) :=
    Finset.univ.filter fun j ↦ (outcomes j).admissible B = true
  have hA : A.Nonempty := by
    obtain ⟨j, hj⟩ := hexists
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨jmax, hjmax, hmax⟩ := Finset.exists_max_image A
    (fun j ↦ (outcomes j).modulus.lo) hA
  have hadm : (outcomes jmax).admissible B = true :=
    (Finset.mem_filter.mp hjmax).2
  have hbest : pilotBestFrom B outcomes jmax = true := by
    simp only [pilotBestFrom, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hadm, ?_⟩
    intro k hk
    exact hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
  have hsome : ∃ j, pilotBestFrom B outcomes j = true := ⟨jmax, hbest⟩
  let j := Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch.leastTrue
    (pilotBestFrom B outcomes)
  have hjbest : pilotBestFrom B outcomes j = true :=
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch.leastTrue_accepts
      hsome
  refine ⟨j, ?_, ?_⟩
  · simp [selectedContourFrom, hsome, j]
  · simpa only [pilotBestFrom, Bool.and_eq_true, decide_eq_true_eq] using hjbest

private lemma residual_error_le_sup
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m) (data : Fin p.n → Obs Xspace)
    (a : Fin 2) {z : ℂ} (hz : ‖z‖ ≤ searchRadius p) :
    ‖semanticEmpiricalF p m.gcode data (spectralFold p.n a) 0 z -
        residualMGF p m p.n z‖ ≤
      transformSupError
        (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n a) z)
        (residualMGF p m p.n) (searchRadius p) data := by
  have hI : (spectralFold p.n a).Nonempty :=
    inferenceFold_nonempty p.n hn a
  have hsem := semanticEmpiricalF_zero_eq_empiricalF p m data
    (spectralFold p.n a) hI
  have hfold : spectralFold p.n a = inferenceFold p.n a := rfl
  rw [hsem, hfold]
  apply norm_sub_le_transformSupError
  have hemp : AnalyticOnNhd ℂ
      (empiricalF p m p.n data (inferenceFold p.n a)) Set.univ := by
    rw [← hfold, ← hsem]
    exact semanticEmpiricalF_analyticOnNhd p m.gcode data (spectralFold p.n a) 0
  have hpop : ContinuousOn (residualMGF p m p.n)
      {z : ℂ | ‖z‖ ≤ searchRadius p} := by
    simpa [Metric.closedBall, dist_zero_right] using
      (residualMGF_analyticOn_closedBall p m p.n hclass
        (searchRadius p)).continuousOn
  exact (hemp.mono (fun _ _ ↦ Set.mem_univ _)).continuousOn.sub hpop
  exact hz

private lemma outcome_error_le_sup
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m) (data : Fin p.n → Obs Xspace)
    (a : Fin 2) {z : ℂ} (hz : ‖z‖ ≤ searchRadius p) :
    ‖semanticEmpiricalG p m.gcode data (spectralFold p.n a) 0 z -
        outcomeResidualTransform p m p.n z‖ ≤
      transformSupError
        (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n a) z)
        (outcomeResidualTransform p m p.n) (searchRadius p) data := by
  have hI : (spectralFold p.n a).Nonempty :=
    inferenceFold_nonempty p.n hn a
  have hsem := semanticEmpiricalG_zero_eq_empiricalG p m data
    (spectralFold p.n a) hI
  have hfold : spectralFold p.n a = inferenceFold p.n a := rfl
  rw [hsem, hfold]
  apply norm_sub_le_transformSupError
  have hemp : AnalyticOnNhd ℂ
      (empiricalG p m p.n data (inferenceFold p.n a)) Set.univ := by
    rw [← hfold, ← hsem]
    exact semanticEmpiricalG_analyticOnNhd p m.gcode data (spectralFold p.n a) 0
  let A := 64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 +
      4 * p.psixi ^ 4) +
    2 * Real.exp (16 * searchRadius p * p.Cg +
      16 * searchRadius p ^ 2 * p.psieta ^ 2)
  let C := Real.sqrt A
  have hR : 0 < searchRadius p := by
    unfold searchRadius
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henv : ∫⁻ o, ENNReal.ofReal
      ((|outcome o| * Real.exp
        (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal (C ^ 2) := by
    have h := outcome_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    rw [show C ^ 2 = A by exact Real.sq_sqrt hA]
    exact h
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have hcont := weightedTransform_continuousOn_of_factorial_envelope
    (P := m.P) outcome (learnedResidual p m p.n) measurable_snd.snd hZmeas
    (searchRadius p) hR C (Real.sqrt_nonneg A) henv
  have hpop : ContinuousOn (outcomeResidualTransform p m p.n)
      {z : ℂ | ‖z‖ ≤ searchRadius p} := by
    exact hcont
  exact (hemp.mono (fun _ _ ↦ Set.mem_univ _)).continuousOn.sub hpop
  exact hz

private lemma zeroMultiplicityCount_eq_of_analyticOrders_pre
    (f g : ℂ → ℂ) (rho R : ℝ) (hrho : rho < R)
    (horder : ∀ z : ℂ, ‖z‖ ≤ R → analyticOrderAt f z = analyticOrderAt g z) :
    Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount f 0 rho =
      Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount g 0 rho := by
  unfold Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
  apply finsum_congr
  intro z
  by_cases hz : z ∈ Metric.ball (0 : ℂ) rho
  · simp only [hz, if_true]
    unfold analyticOrderNatAt
    rw [horder z]
    rw [Metric.mem_ball, dist_zero_right] at hz
    linarith
  · simp [hz]

private lemma population_candidate_pre
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m)
    (heps : p.eps1n p.n ≤
      (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹) :
    let B := contourBank p pStar
    ∃ j : Fin (B.JBase + 1),
      1 ≤ Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (residualMGF p m p.n) 0 (B.rho j) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) (B.rho j),
        3 * B.aStar / 4 ≤ ‖residualMGF p m p.n z‖) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) (B.rho j),
        nuisanceMGF p m p.n z ≠ 0) := by
  dsimp only
  rcases finite_contour_bank p pStar p.n (by omega) m hclass with
    ⟨ha, -, -, -, -, -, -, -, -, -, -, hradii, j, hcountM, hM⟩
  have hl1 := l1_nuisance_zero_free (p := p) (m := m) p.n hclass
  rcases hl1.2.2.2 heps with ⟨hH, horder⟩
  have hcountEq := zeroMultiplicityCount_eq_of_analyticOrders_pre
    (residualMGF p m p.n) (treatmentMGF p m)
      ((contourBank p pStar).rho j) (searchRadius p) (hradii j).2 horder
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [hcountEq]
    omega
  · intro z hz
    rw [(observable_factorization p m p.n hclass z).1, norm_mul]
    have hHz : 3 / 4 ≤ ‖nuisanceMGF p m p.n z‖ :=
      hH z (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        linarith [(hradii j).2])
    have hMz := hM z hz
    have hprod := mul_le_mul hMz hHz (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (norm_nonneg (treatmentMGF p m z))
    nlinarith
  · intro z hz
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4)
      (hH z (by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        linarith [(hradii j).2])))

private lemma canonical_candidate_admissible
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m)
    (heps : p.eps1n p.n ≤
      (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹)
    (data : Fin p.n → Obs Xspace)
    (d0 : ℝ)
    (hd0def : d0 = transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 0) z)
      (residualMGF p m p.n) (searchRadius p) data)
    (hd0 : d0 ≤ ((contourBank p pStar).aStarRat : ℝ) / 8) :
    let input := canonicalRepresentedInput p pStar cStar m.gcode data
    let B := contourBank p pStar
    ∃ j : Fin (B.JBase + 1),
      (pilotOutcome input B j).admissible B = true ∧
      39 * (B.aStarRat : ℝ) / 64 ≤
        ((pilotOutcome input B j).modulus.lo : ℝ) ∧
      1 ≤ Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (residualMGF p m p.n) 0 (B.rho j) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) (B.rho j),
        3 * B.aStar / 4 ≤ ‖residualMGF p m p.n z‖) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) (B.rho j),
        nuisanceMGF p m p.n z ≠ 0) := by
  dsimp only
  let B := contourBank p pStar
  let input := canonicalRepresentedInput p pStar cStar m.gcode data
  rcases population_candidate_pre p pStar m hn hclass heps with
    ⟨j, hcount, hpop, hHzero⟩
  rcases finite_contour_bank p pStar p.n (by omega) m hclass with
    ⟨-, -, -, -, -, -, -, -, -, -, -, hradii, -⟩
  have hRj : B.rho j < searchRadius p := by simpa [B] using (hradii j).2
  have hspec := ((representedNodeSpecifications p) pStar cStar m.gcode data).1 j
  have hp0 := hspec.1
  dsimp [PilotModulusSpecification, input, B] at hp0
  let S : Set ℝ := (fun z ↦ ‖(spectralDenominatorMap input B
    (spectralFold p.n 0) 0).value z‖) '' Metric.sphere (0 : ℂ) (B.rho j)
  have hSnonempty : S.Nonempty := by
    have hrho : 0 < B.rho j := contourBank_rho_pos p pStar j
    let z : ℂ := B.rho j
    refine ⟨‖(spectralDenominatorMap input B (spectralFold p.n 0) 0).value z‖,
      z, ?_, rfl⟩
    simp [z, abs_of_pos hrho]
  have hinfLower : 5 * (B.aStarRat : ℝ) / 8 ≤ sInf S := by
    apply le_csInf hSnonempty
    rintro y ⟨z, hz, rfl⟩
    change 5 * (B.aStarRat : ℝ) / 8 ≤
      ‖(spectralDenominatorMap
        (canonicalRepresentedInput p pStar cStar m.gcode data) B
        (spectralFold p.n 0) 0).value z‖
    rw [spectralDenominatorMap_value_canonical]
    have herr := residual_error_le_sup p m hn hclass data 0
      (z := z) (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        linarith)
    rw [← hd0def] at herr
    have htri : ‖residualMGF p m p.n z‖ ≤
        ‖semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z -
          residualMGF p m p.n z‖ +
        ‖semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z‖ := by
      calc
        _ = ‖-(semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z -
              residualMGF p m p.n z) +
            semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z‖ := by
              congr 1
              ring
        _ ≤ _ := by
          simpa only [norm_neg] using norm_add_le
            (-(semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z -
              residualMGF p m p.n z))
            (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z)
    have haeq : B.aStar = (B.aStarRat : ℝ) := B.aStar_eq
    rw [haeq] at hpop
    nlinarith [hpop z hz]
  have hp0lo : 39 * (B.aStarRat : ℝ) / 64 ≤
      ((pilotModulus input B 0 j).lo : ℝ) := by
    have hcontains : (pilotModulus input B 0 j).Contains (sInf S) := by
      exact hp0.1
    have hwidth : (pilotModulus input B 0 j).width ≤ B.aStarRat / 64 := by
      exact hp0.2.1
    unfold Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.RatInterval.Contains at hcontains
    unfold Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.RatInterval.width at hwidth
    have hwidthR : ((pilotModulus input B 0 j).hi : ℝ) -
        ((pilotModulus input B 0 j).lo : ℝ) ≤ (B.aStarRat : ℝ) / 64 := by
      exact_mod_cast hwidth
    nlinarith
  have hp0pos : 0 < (pilotModulus input B 0 j).lo := by
    have ha : (0 : ℝ) < B.aStarRat := by exact_mod_cast B.aStarRat_pos
    exact_mod_cast (lt_of_lt_of_le (by positivity :
      0 < 39 * (B.aStarRat : ℝ) / 64) hp0lo)
  have hFanalytic := residualMGF_analyticOn_closedBall p m p.n hclass (B.rho j)
  have hempanalytic : AnalyticOnNhd ℂ
      (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0)
      (Metric.closedBall (0 : ℂ) (B.rho j)) :=
    (semanticEmpiricalF_analyticOnNhd p m.gcode data
      (spectralFold p.n 0) 0).mono (fun _ _ ↦ Set.mem_univ _)
  have hrouche : Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
      (residualMGF p m p.n) 0 (B.rho j) =
      Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j) := by
    apply Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.rouche_circle
      (contourBank_rho_pos p pStar j) hFanalytic hempanalytic
    intro z hz
    have herr := residual_error_le_sup p m hn hclass data 0
      (z := z) (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        linarith)
    rw [← hd0def] at herr
    have haeq : B.aStar = (B.aStarRat : ℝ) := B.aStar_eq
    rw [haeq] at hpop
    have ha : (0 : ℝ) < B.aStarRat := by exact_mod_cast B.aStarRat_pos
    exact lt_of_le_of_lt herr (by nlinarith [hpop z hz])
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) (B.rho j),
      semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z ≠ 0 := by
    intro z hz hzero
    have herr := residual_error_le_sup p m hn hclass data 0
      (z := z) (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        linarith)
    rw [hzero, zero_sub, norm_neg, ← hd0def] at herr
    have haeq : B.aStar = (B.aStarRat : ℝ) := B.aStar_eq
    rw [haeq] at hpop
    have ha : (0 : ℝ) < B.aStarRat := by exact_mod_cast B.aStarRat_pos
    nlinarith [hpop z hz]
  have hap := Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.argumentPrinciple_circle
    (contourBank_rho_pos p pStar j) hempanalytic hboundary
  have hw := hspec.2.2.1
  dsimp [WindingEnclosureSpecification, input, B] at hw
  have hwcontains := (hw.2.2.2.1 hp0pos).2.1
  have hnormalized : normalizedContourValue
      (spectralWindingEvaluator input B j ⟨(pilotModulus input B 0 j).lo, hp0pos⟩) =
      (Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j) : ℂ) := by
    rw [← hap]
    unfold normalizedContourValue
    simp only [spectralWindingEvaluator]
    dsimp only [input, B]
    rw [circleContourIntegral_eq_circleIntegral, (contourBank p pStar).rho_value]
    simp only [max_self, Nat.cast_one]
    unfold Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.normalizedLogDerivCircleIntegral
    congr 1
    · norm_num
    · apply circleIntegral.integral_congr (contourBank_rho_pos p pStar j).le
      intro z hz
      simp only [spectralDenominatorMap_value_canonical]
      rw [logDeriv_apply, deriv_semanticEmpiricalF_zero]
  have hwcount : (windingEnclosure input B j).Contains
      ((Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j) : ℝ) : ℂ) := by
    change (windingEnclosure input B j).Contains
      (normalizedContourValue
        (spectralWindingEvaluator input B j
          ⟨(pilotModulus input B 0 j).lo, hp0pos⟩)) at hwcontains
    rw [hnormalized] at hwcontains
    exact hwcontains
  have hdecodedEmp := uniqueNonnegativeInteger_complete
    (windingEnclosure input B j)
    (Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
      (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j))
    hwcount hw.1 hw.2.1
  have hdecoded : (pilotOutcome input B j).decoded = some
      (Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (residualMGF p m p.n) 0 (B.rho j)) := by
    dsimp [pilotOutcome]
    rw [hrouche]
    exact hdecodedEmp
  refine ⟨j, ?_, by simpa [pilotOutcome] using hp0lo, hcount, hpop, hHzero⟩
  · unfold PilotOutcome.admissible
    simp only [decide_eq_true_eq]
    dsimp [pilotOutcome]
    constructor
    · change B.aStarRat / 2 ≤ (pilotModulus input B 0 j).lo
      have hloQ : 39 * B.aStarRat / 64 ≤ (pilotModulus input B 0 j).lo := by
        exact_mod_cast hp0lo
      nlinarith [B.aStarRat_pos]
    · exact ⟨_, hdecoded, hcount⟩

private lemma canonicalSelectorGoodEvent_of_small_errors
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m)
    (heps : p.eps1n p.n ≤
      (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹)
    (data : Fin p.n → Obs Xspace)
    (hd0 : transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 0) z)
      (residualMGF p m p.n) (searchRadius p) data ≤
        ((contourBank p pStar).aStarRat : ℝ) / 8)
    (hd1 : transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 1) z)
      (residualMGF p m p.n) (searchRadius p) data ≤
        ((contourBank p pStar).aStarRat : ℝ) / 8) :
    let d1 := transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 1) z)
      (residualMGF p m p.n) (searchRadius p) data
    let e1 := transformSupError
      (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n 1) z)
      (outcomeResidualTransform p m p.n) (searchRadius p) data
    let mu := 31 * ((contourBank p pStar).aStarRat : ℝ) / 64
    let nu := 23 * ((contourBank p pStar).aStarRat : ℝ) / 64
    CanonicalSelectorGoodEvent p pStar cStar m.gcode data
      (residualMGF p m p.n) (outcomeResidualTransform p m p.n)
      d1 e1 (populationNumeratorEnvelope p) mu nu := by
  dsimp only
  let B := contourBank p pStar
  let input := canonicalRepresentedInput p pStar cStar m.gcode data
  let d0 := transformSupError
    (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 0) z)
    (residualMGF p m p.n) (searchRadius p) data
  let d1 := transformSupError
    (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 1) z)
    (residualMGF p m p.n) (searchRadius p) data
  let e1 := transformSupError
    (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n 1) z)
    (outcomeResidualTransform p m p.n) (searchRadius p) data
  rcases canonical_candidate_admissible p pStar cStar m hn hclass heps data d0 rfl
    (by simpa [d0] using hd0) with ⟨j0, hj0adm, hj0lo, -, -, -⟩
  have hsel := selectedContourFrom_some_best B (fun j ↦ pilotOutcome input B j)
    ⟨j0, by simpa [input, B] using hj0adm⟩
  rcases hsel with ⟨j, hjselect, hjadm, hjmax⟩
  have hjlo : 39 * (B.aStarRat : ℝ) / 64 ≤
      ((pilotOutcome input B j).modulus.lo : ℝ) := by
    have hm := hjmax j0 (by simpa [input, B] using hj0adm)
    exact hj0lo.trans (by exact_mod_cast hm)
  have hspec := ((representedNodeSpecifications p) pStar cStar m.gcode data).1 j
  have hp0 := hspec.1
  dsimp [PilotModulusSpecification, input, B] at hp0
  have hmu : ∀ z ∈ Metric.sphere (0 : ℂ) (B.rho j),
      31 * (B.aStarRat : ℝ) / 64 ≤ ‖residualMGF p m p.n z‖ := by
    intro z hz
    have hbdd : BddBelow ((fun w ↦ ‖(spectralDenominatorMap input B
        (spectralFold p.n 0) 0).value w‖) '' Metric.sphere (0 : ℂ) (B.rho j)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      exact norm_nonneg _
    have hinf := csInf_le hbdd ⟨z, hz, rfl⟩
    have hlo := hp0.1.1.trans hinf
    have herr := residual_error_le_sup p m hn hclass data 0
      (z := z) (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        rcases finite_contour_bank p pStar p.n (by omega) m hclass with
          ⟨-, -, -, -, -, -, -, -, -, -, -, hrs, -⟩
        linarith [(hrs j).2])
    have htri : ‖semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z‖ ≤
        ‖semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z -
          residualMGF p m p.n z‖ + ‖residualMGF p m p.n z‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z -
          residualMGF p m p.n z) (residualMGF p m p.n z)
    dsimp only [input, B] at hlo
    simp only [spectralDenominatorMap_value_canonical] at hlo
    dsimp [pilotOutcome] at hjlo
    have hlo' : ((pilotModulus input B 0 j).lo : ℝ) ≤
        ‖semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z‖ := by
      exact hlo
    have hd0' : transformSupError
        (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 0) z)
        (residualMGF p m p.n) (searchRadius p) data ≤ (B.aStarRat : ℝ) / 8 := by
      simpa [B] using hd0
    nlinarith
  rcases (show (pilotOutcome input B j).admissible B = true from hjadm) with hjadm'
  unfold PilotOutcome.admissible at hjadm'
  rw [decide_eq_true_eq] at hjadm'
  rcases hjadm'.2 with ⟨N, hdecoded, hN⟩
  have hp1 := hspec.2.1
  dsimp [PilotModulusSpecification, input, B] at hp1
  let S1 : Set ℝ := (fun z ↦ ‖(spectralDenominatorMap input B
    (spectralFold p.n 1) 0).value z‖) '' Metric.sphere (0 : ℂ) (B.rho j)
  have hS1 : S1.Nonempty := by
    have hr := contourBank_rho_pos p pStar j
    refine ⟨‖(spectralDenominatorMap input B (spectralFold p.n 1) 0).value
      (B.rho j)‖, (B.rho j : ℂ), ?_, rfl⟩
    simp
    simpa [B] using hr.le
  have hinf1 : 23 * (B.aStarRat : ℝ) / 64 ≤ sInf S1 := by
    apply le_csInf hS1
    rintro y ⟨z, hz, rfl⟩
    change 23 * (B.aStarRat : ℝ) / 64 ≤
      ‖(spectralDenominatorMap
        (canonicalRepresentedInput p pStar cStar m.gcode data) B
        (spectralFold p.n 1) 0).value z‖
    rw [spectralDenominatorMap_value_canonical]
    have herr := residual_error_le_sup p m hn hclass data 1
      (z := z) (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        rcases finite_contour_bank p pStar p.n (by omega) m hclass with
          ⟨-, -, -, -, -, -, -, -, -, -, -, hrs, -⟩
        linarith [(hrs j).2])
    have htri : ‖residualMGF p m p.n z‖ ≤
        ‖semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0 z -
          residualMGF p m p.n z‖ +
        ‖semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0 z‖ := by
      calc
        _ = ‖-(semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0 z -
              residualMGF p m p.n z) +
            semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0 z‖ := by
              congr 1
              ring
        _ ≤ _ := by
          simpa only [norm_neg] using norm_add_le
            (-(semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0 z -
              residualMGF p m p.n z))
            (semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0 z)
    nlinarith [hmu z hz]
  have hp1lo : 11 * (B.aStarRat : ℝ) / 32 ≤
      ((pilotModulus input B 1 j).lo : ℝ) := by
    have hc : (pilotModulus input B 1 j).Contains (sInf S1) := by
      exact hp1.1
    have hw : (pilotModulus input B 1 j).width ≤ B.aStarRat / 64 := by
      exact hp1.2.1
    unfold Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.RatInterval.Contains at hc
    unfold Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.RatInterval.width at hw
    have hwR : ((pilotModulus input B 1 j).hi : ℝ) -
        ((pilotModulus input B 1 j).lo : ℝ) ≤ (B.aStarRat : ℝ) / 64 := by
      exact_mod_cast hw
    nlinarith
  refine ⟨transformSupError_nonneg _ _ _ _, transformSupError_nonneg _ _ _ _,
    by unfold populationNumeratorEnvelope; positivity, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · have ha : (0 : ℝ) < B.aStarRat := by exact_mod_cast B.aStarRat_pos
    positivity
  · have ha : (0 : ℝ) < B.aStarRat := by exact_mod_cast B.aStarRat_pos
    positivity
  · nlinarith
  · refine ⟨j, N, ?_, hdecoded, hN, ?_, ?_⟩
    · simpa [selectedContour, input, B] using hjselect
    · have hloQ : 11 * B.aStarRat / 32 ≤ (pilotModulus input B 1 j).lo := by
        exact_mod_cast hp1lo
      nlinarith [B.aStarRat_pos]
    · intro z hz
      refine ⟨hmu z hz,
        outcomeResidualTransform_norm_le_populationNumeratorEnvelope p m hclass ?_, ?_, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right] at hz
        rcases finite_contour_bank p pStar p.n (by omega) m hclass with
          ⟨-, -, -, -, -, -, -, -, -, -, -, hrs, -⟩
        linarith [(hrs j).2]
      · simpa [d1] using residual_error_le_sup p m hn hclass data 1
          (z := z) (by
            rw [Metric.mem_sphere, dist_zero_right] at hz
            rcases finite_contour_bank p pStar p.n (by omega) m hclass with
              ⟨-, -, -, -, -, -, -, -, -, -, -, hrs, -⟩
            linarith [(hrs j).2])
      · simpa [e1] using outcome_error_le_sup p m hn hclass data 1
          (z := z) (by
            rw [Metric.mem_sphere, dist_zero_right] at hz
            rcases finite_contour_bank p pStar p.n (by omega) m hclass with
              ⟨-, -, -, -, -, -, -, -, -, -, -, hrs, -⟩
            linarith [(hrs j).2])

private lemma outcomeResidualTransform_continuousOn_searchDisk
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p)
    (hclass : NonGaussianClass p p.n m) :
    ContinuousOn (outcomeResidualTransform p m p.n)
      {z : ℂ | ‖z‖ ≤ searchRadius p} := by
  let A := 64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 +
      4 * p.psixi ^ 4) +
    2 * Real.exp (16 * searchRadius p * p.Cg +
      16 * searchRadius p ^ 2 * p.psieta ^ 2)
  let C := Real.sqrt A
  have hR : 0 < searchRadius p := by
    unfold searchRadius
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henv : ∫⁻ o, ENNReal.ofReal
      ((|outcome o| * Real.exp
        (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal (C ^ 2) := by
    have h := outcome_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    rw [show C ^ 2 = A by exact Real.sq_sqrt hA]
    exact h
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  exact weightedTransform_continuousOn_of_factorial_envelope
    (P := m.P) outcome (learnedResidual p m p.n) measurable_snd.snd hZmeas
    (searchRadius p) hR C (Real.sqrt_nonneg A) henv

private lemma selected_decoded_eq_population_count
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m) (data : Fin p.n → Obs Xspace)
    (hd0 : transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 0) z)
      (residualMGF p m p.n) (searchRadius p) data ≤
        ((contourBank p pStar).aStarRat : ℝ) / 8)
    (j : Fin ((contourBank p pStar).JBase + 1))
    (N : ℕ)
    (hj : selectedContour (canonicalRepresentedInput p pStar cStar m.gcode data)
      (contourBank p pStar) = some j)
    (hdecoded : (pilotOutcome
      (canonicalRepresentedInput p pStar cStar m.gcode data)
      (contourBank p pStar) j).decoded = some N)
    (hmu : ∀ z ∈ Metric.sphere (0 : ℂ) ((contourBank p pStar).rho j),
      31 * ((contourBank p pStar).aStarRat : ℝ) / 64 ≤
        ‖residualMGF p m p.n z‖) :
    N = Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
      (residualMGF p m p.n) 0 ((contourBank p pStar).rho j) := by
  let B := contourBank p pStar
  let input := canonicalRepresentedInput p pStar cStar m.gcode data
  have hjbest : pilotBestFrom B (fun k ↦ pilotOutcome input B k) j = true := by
    change selectedContourFrom B (fun k ↦ pilotOutcome input B k) = some j at hj
    by_cases hsome : ∃ k, pilotBestFrom B (fun k ↦ pilotOutcome input B k) k = true
    · rw [selectedContourFrom, if_pos hsome] at hj
      have hjEq :
          Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch.leastTrue
            (pilotBestFrom B (fun k ↦ pilotOutcome input B k)) = j :=
        Option.some.inj hj
      rw [← hjEq]
      exact Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch.leastTrue_accepts
        hsome
    · rw [selectedContourFrom, if_neg hsome] at hj
      simp at hj
  have hjadm : (pilotOutcome input B j).admissible B = true := by
    rw [pilotBestFrom, Bool.and_eq_true] at hjbest
    exact hjbest.1
  unfold PilotOutcome.admissible at hjadm
  rw [decide_eq_true_eq] at hjadm
  have hp0pos : 0 < (pilotModulus input B 0 j).lo :=
    lt_of_lt_of_le (div_pos B.aStarRat_pos (by norm_num)) hjadm.1
  rcases finite_contour_bank p pStar p.n (by omega) m hclass with
    ⟨-, -, -, -, -, -, -, -, -, -, -, hradii, -⟩
  have hRj := (hradii j).2
  have hFanalytic := residualMGF_analyticOn_closedBall p m p.n hclass (B.rho j)
  have hempanalytic : AnalyticOnNhd ℂ
      (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0)
      (Metric.closedBall (0 : ℂ) (B.rho j)) :=
    (semanticEmpiricalF_analyticOnNhd p m.gcode data
      (spectralFold p.n 0) 0).mono (fun _ _ ↦ Set.mem_univ _)
  have hrouche : Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
      (residualMGF p m p.n) 0 (B.rho j) =
      Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j) := by
    apply Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.rouche_circle
      (contourBank_rho_pos p pStar j) hFanalytic hempanalytic
    intro z hz
    have herr := residual_error_le_sup p m hn hclass data 0
      (z := z) (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        linarith)
    exact lt_of_le_of_lt herr (by
      have ha : (0 : ℝ) < B.aStarRat := by exact_mod_cast B.aStarRat_pos
      nlinarith [hmu z hz])
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) (B.rho j),
      semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0 z ≠ 0 := by
    intro z hz hzero
    have herr := residual_error_le_sup p m hn hclass data 0
      (z := z) (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        linarith)
    rw [hzero, zero_sub, norm_neg] at herr
    have ha : (0 : ℝ) < B.aStarRat := by exact_mod_cast B.aStarRat_pos
    nlinarith [hmu z hz]
  have hap := Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.argumentPrinciple_circle
    (contourBank_rho_pos p pStar j) hempanalytic hboundary
  have hspec := ((representedNodeSpecifications p) pStar cStar m.gcode data).1 j
  have hw := hspec.2.2.1
  dsimp [WindingEnclosureSpecification, input, B] at hw
  have hwcontains := (hw.2.2.2.1 hp0pos).2.1
  have hnormalized : normalizedContourValue
      (spectralWindingEvaluator input B j ⟨(pilotModulus input B 0 j).lo, hp0pos⟩) =
      (Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j) : ℂ) := by
    rw [← hap]
    unfold normalizedContourValue
    simp only [spectralWindingEvaluator]
    dsimp only [input, B]
    rw [circleContourIntegral_eq_circleIntegral, (contourBank p pStar).rho_value]
    simp only [max_self, Nat.cast_one]
    unfold Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.normalizedLogDerivCircleIntegral
    congr 1
    · norm_num
    · apply circleIntegral.integral_congr (contourBank_rho_pos p pStar j).le
      intro z hz
      simp only [spectralDenominatorMap_value_canonical]
      rw [logDeriv_apply, deriv_semanticEmpiricalF_zero]
  have hwcount : (windingEnclosure input B j).Contains
      ((Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j) : ℝ) : ℂ) := by
    change (windingEnclosure input B j).Contains
      (normalizedContourValue
        (spectralWindingEvaluator input B j
          ⟨(pilotModulus input B 0 j).lo, hp0pos⟩)) at hwcontains
    rw [hnormalized] at hwcontains
    exact hwcontains
  have hdecodedEmp := uniqueNonnegativeInteger_complete
    (windingEnclosure input B j)
    (Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
      (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j))
    hwcount hw.1 hw.2.1
  have hdecoded' : (pilotOutcome input B j).decoded = some N := by
    simpa [input, B] using hdecoded
  dsimp [pilotOutcome] at hdecoded' hdecodedEmp
  have hNemp : N = Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
      (semanticEmpiricalF p m.gcode data (spectralFold p.n 0) 0) 0 (B.rho j) := by
    exact Option.some.inj (hdecoded'.symm.trans hdecodedEmp)
  exact hNemp.trans hrouche.symm

private lemma canonicalSelectorPacket_of_small_errors
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m)
    (heps : p.eps1n p.n ≤
      (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹)
    (data : Fin p.n → Obs Xspace)
    (hd0 : transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 0) z)
      (residualMGF p m p.n) (searchRadius p) data ≤
        ((contourBank p pStar).aStarRat : ℝ) / 8)
    (hd1 : transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 1) z)
      (residualMGF p m p.n) (searchRadius p) data ≤
        ((contourBank p pStar).aStarRat : ℝ) / 8) :
    let d1 := transformSupError
      (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n 1) z)
      (residualMGF p m p.n) (searchRadius p) data
    let e1 := transformSupError
      (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n 1) z)
      (outcomeResidualTransform p m p.n) (searchRadius p) data
    let mu := 31 * ((contourBank p pStar).aStarRat : ℝ) / 64
    let nu := 23 * ((contourBank p pStar).aStarRat : ℝ) / 64
    CanonicalSelectorGoodEvent p pStar cStar m.gcode data
      (residualMGF p m p.n) (outcomeResidualTransform p m p.n)
      d1 e1 (populationNumeratorEnvelope p) mu nu ∧
    (∀ j, selectedContour (canonicalRepresentedInput p pStar cStar m.gcode data)
        (contourBank p pStar) = some j →
      CircleIntegrable
        (fun z ↦ semanticEmpiricalG p m.gcode data (spectralFold p.n 1) 0 z /
          semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0 z)
        0 ((contourBank p pStar).rho j) ∧
      CircleIntegrable (fun z ↦ outcomeResidualTransform p m p.n z /
        residualMGF p m p.n z) 0 ((contourBank p pStar).rho j)) ∧
    (∀ j N, selectedContour (canonicalRepresentedInput p pStar cStar m.gcode data)
        (contourBank p pStar) = some j →
      (pilotOutcome (canonicalRepresentedInput p pStar cStar m.gcode data)
        (contourBank p pStar) j).decoded = some N →
      m.theta0 = ((((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun z ↦ outcomeResidualTransform p m p.n z /
          residualMGF p m p.n z) 0 ((contourBank p pStar).rho j)).re)) := by
  dsimp only
  have hgood := canonicalSelectorGoodEvent_of_small_errors
    p pStar cStar m hn hclass heps data hd0 hd1
  refine ⟨hgood, ?_, ?_⟩
  · intro j hj
    rcases hgood with ⟨hd1nonneg, he1nonneg, hCG, hmu0, hnu0, -, -, hsmall,
      j0, N0, hj0, hdecoded0, hN0, heval0, hboundary0⟩
    have hjEq : j = j0 := Option.some.inj (hj.symm.trans hj0)
    subst j0
    have hradii := (by
      rcases finite_contour_bank p pStar p.n (by omega) m hclass with
        ⟨-, -, -, -, -, -, -, -, -, -, -, hrs, -⟩
      exact hrs)
    have hrho : (contourBank p pStar).rho j < searchRadius p := (hradii j).2
    constructor
    · have hGcont : ContinuousOn
          (semanticEmpiricalG p m.gcode data (spectralFold p.n 1) 0)
          (Metric.sphere (0 : ℂ) ((contourBank p pStar).rho j)) :=
        (semanticEmpiricalG_analyticOnNhd p m.gcode data
          (spectralFold p.n 1) 0).continuousOn.mono (fun _ _ ↦ Set.mem_univ _)
      have hFcont : ContinuousOn
          (semanticEmpiricalF p m.gcode data (spectralFold p.n 1) 0)
          (Metric.sphere (0 : ℂ) ((contourBank p pStar).rho j)) :=
        (semanticEmpiricalF_analyticOnNhd p m.gcode data
          (spectralFold p.n 1) 0).continuousOn.mono (fun _ _ ↦ Set.mem_univ _)
      apply (hGcont.div hFcont ?_).circleIntegrable
        (contourBank_rho_pos p pStar j).le
      intro z hz
      have hnu := empirical_denominator_margin_of_population_margin
        (hboundary0 z hz).1 (hboundary0 z hz).2.2.1 hsmall
      exact norm_pos_iff.mp (hnu0.trans_le hnu)
    · have hGcont := (outcomeResidualTransform_continuousOn_searchDisk p m hclass).mono
        (fun z hz ↦ by
          rw [Metric.mem_sphere, dist_zero_right] at hz
          exact le_of_lt (hz.trans_lt hrho))
      have hFcont := (residualMGF_analyticOn_closedBall p m p.n hclass
        ((contourBank p pStar).rho j)).continuousOn.mono sphere_subset_closedBall
      apply (hGcont.div hFcont ?_).circleIntegrable
        (contourBank_rho_pos p pStar j).le
      intro z hz
      exact norm_pos_iff.mp (hmu0.trans_le (hboundary0 z hz).1)
  · intro j N hj hdecoded
    rcases hgood with ⟨hd1nonneg, he1nonneg, hCG, hmu0, hnu0, -, -, hsmall,
      j0, N0, hj0, hdecoded0, hN0, heval0, hboundary0⟩
    have hjEq : j = j0 := Option.some.inj (hj.symm.trans hj0)
    subst j0
    have hNEq : N = N0 := Option.some.inj (hdecoded.symm.trans hdecoded0)
    subst N0
    have hcount := selected_decoded_eq_population_count p pStar cStar m hn hclass data
      hd0 j N hj hdecoded (fun z hz ↦ hboundary0 z hz |>.1)
    rcases finite_contour_bank p pStar p.n (by omega) m hclass with
      ⟨-, -, -, -, -, -, -, -, -, -, -, hradii, -⟩
    have hl1 := l1_nuisance_zero_free (p := p) (m := m) p.n hclass
    rcases hl1.2.2.2 heps with ⟨hH, horder⟩
    have hHzero : ∀ z ∈ Metric.closedBall (0 : ℂ) ((contourBank p pStar).rho j),
        nuisanceMGF p m p.n z ≠ 0 := by
      intro z hz
      apply norm_pos_iff.mp
      apply lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4)
      apply hH z
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      linarith [(hradii j).2]
    have hFzero : ∀ z ∈ Metric.sphere (0 : ℂ) ((contourBank p pStar).rho j),
        residualMGF p m p.n z ≠ 0 := by
      intro z hz
      exact norm_pos_iff.mp (hmu0.trans_le (hboundary0 z hz).1)
    have hid := exact_contour_identification p m p.n (by omega) hclass pStar j
      hFzero hHzero (by simpa [hcount] using hN0)
    have hap : contourCount (residualMGF p m p.n) ((contourBank p pStar).rho j) =
        (Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
          (residualMGF p m p.n) 0 ((contourBank p pStar).rho j) : ℂ) :=
      Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.argumentPrinciple_circle
        (contourBank_rho_pos p pStar j)
        (residualMGF_analyticOn_closedBall p m p.n hclass
          ((contourBank p pStar).rho j)) hFzero
    have hcomplex : (m.theta0 : ℂ) =
        ((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral (fun z ↦ outcomeResidualTransform p m p.n z /
            residualMGF p m p.n z) 0 ((contourBank p pStar).rho j) := by
      rw [hid.1, hid.2, hap, ← hcount]
      simp only [mul_assoc]
    exact_mod_cast congrArg Complex.re hcomplex

private lemma zeroMultiplicityCount_eq_of_analyticOrders
    (f g : ℂ → ℂ) (rho R : ℝ) (hrho : rho < R)
    (horder : ∀ z : ℂ, ‖z‖ ≤ R → analyticOrderAt f z = analyticOrderAt g z) :
    Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount f 0 rho =
      Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount g 0 rho := by
  unfold Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
  apply finsum_congr
  intro z
  by_cases hz : z ∈ Metric.ball (0 : ℂ) rho
  · simp only [hz, if_true]
    unfold analyticOrderNatAt
    rw [horder z]
    rw [Metric.mem_ball, dist_zero_right] at hz
    linarith
  · simp [hz]

private lemma population_candidate
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m)
    (heps : p.eps1n p.n ≤
      (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹) :
    let B := contourBank p pStar
    ∃ j : Fin (B.JBase + 1),
      1 ≤ Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount
        (residualMGF p m p.n) 0 (B.rho j) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) (B.rho j),
        3 * B.aStar / 4 ≤ ‖residualMGF p m p.n z‖) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) (B.rho j),
        nuisanceMGF p m p.n z ≠ 0) := by
  dsimp only
  rcases finite_contour_bank p pStar p.n (by omega) m hclass with
    ⟨ha, -, -, -, -, -, -, -, -, -, -, hradii, j, hcountM, hM⟩
  have hl1 := l1_nuisance_zero_free (p := p) (m := m) p.n hclass
  rcases hl1.2.2.2 heps with ⟨hH, horder⟩
  have hcountEq := zeroMultiplicityCount_eq_of_analyticOrders
    (residualMGF p m p.n) (treatmentMGF p m)
      ((contourBank p pStar).rho j) (searchRadius p) (hradii j).2 horder
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [hcountEq]
    omega
  · intro z hz
    rw [(observable_factorization p m p.n hclass z).1, norm_mul]
    have hHz : 3 / 4 ≤ ‖nuisanceMGF p m p.n z‖ :=
      hH z (by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        linarith [(hradii j).2])
    have hMz := hM z hz
    have hprod := mul_le_mul hMz hHz (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (norm_nonneg (treatmentMGF p m z))
    nlinarith
  · intro z hz
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4)
      (hH z (by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        linarith [(hradii j).2])))

/-- Residual-transform disk error on one inference fold. -/
def residualFoldError {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (data : Fin p.n → Obs Xspace) : ℝ :=
  transformSupError
    (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n a) z)
    (residualMGF p m p.n) (searchRadius p) data

/-- Outcome-transform disk error on one inference fold. -/
def outcomeFoldError {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (data : Fin p.n → Obs Xspace) : ℝ :=
  transformSupError
    (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n a) z)
    (outcomeResidualTransform p m p.n) (searchRadius p) data

/-- For a model in [the non-Gaussian spectral class](hyp:hclass), [the residual-transform
error on either inference fold — the largest discrepancy, over all points of the search disk,
between the fold's empirical residual transform and its population counterpart — is a
measurable function of the sample](goal). -/
lemma measurable_residualFoldError
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (hclass : NonGaussianClass p p.n m) :
    Measurable (residualFoldError p m a) := by
  exact measurable_residual_transformSupError p m a hclass

/-- For a model in [the non-Gaussian spectral class](hyp:hclass), [the outcome-transform error
on either inference fold — the largest discrepancy, over all points of the search disk, between
the fold's empirical outcome transform and its population counterpart — is a measurable
function of the sample](goal). -/
lemma measurable_outcomeFoldError
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (a : Fin 2)
    (hclass : NonGaussianClass p p.n m) :
    Measurable (outcomeFoldError p m a) := by
  exact measurable_outcome_transformSupError p m a hclass

private lemma measure_gt_of_sq_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (t B : ℝ) (ht : 0 < t)
    (hL2 : ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂Q ≤ ENNReal.ofReal B) :
    Q {x | t < f x} ≤ ENNReal.ofReal (B / t ^ 2) := by
  let F : Ω → ENNReal := fun x ↦ ENNReal.ofReal ((f x) ^ 2)
  have hF : AEMeasurable F Q := (hf.pow_const 2).ennreal_ofReal.aemeasurable
  have hsub : {x | t < f x} ⊆ {x | ENNReal.ofReal (t ^ 2) ≤ F x} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (sq_le_sq₀ ht.le (hf0 x) |>.2 hx.le)
  calc
    Q {x | t < f x} ≤ Q {x | ENNReal.ofReal (t ^ 2) ≤ F x} := measure_mono hsub
    _ ≤ (∫⁻ x, F x ∂Q) / ENNReal.ofReal (t ^ 2) :=
      meas_ge_le_lintegral_div hF (by positivity) (by simp)
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (t ^ 2) :=
      ENNReal.div_le_div_right hL2 _
    _ = ENNReal.ofReal (B / t ^ 2) :=
      (ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht)).symm

private lemma fold_errors_l2_le
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (a : Fin 2) (K : ℝ) (hK : 0 ≤ K)
    (hL2 :
      (∫⁻ data, ENNReal.ofReal ((residualFoldError p m a data) ^ 2) ∂iidLaw m p.n) +
      (∫⁻ data, ENNReal.ofReal ((outcomeFoldError p m a data) ^ 2) ∂iidLaw m p.n) ≤
        ENNReal.ofReal (K / (inferenceFold p.n a).card)) :
    (∫⁻ data, ENNReal.ofReal ((residualFoldError p m a data) ^ 2) ∂iidLaw m p.n) +
      (∫⁻ data, ENNReal.ofReal ((outcomeFoldError p m a data) ^ 2) ∂iidLaw m p.n) ≤
        ENNReal.ofReal (3 * K / p.n) := by
  apply hL2.trans
  apply ENNReal.ofReal_le_ofReal
  have hcardPos : (0 : ℝ) < (inferenceFold p.n a).card := by
    exact_mod_cast Finset.card_pos.mpr (inferenceFold_nonempty p.n hn a)
  have hnPos : (0 : ℝ) < p.n := by positivity
  rw [div_le_div_iff₀ hcardPos hnPos]
  have hcard := inferenceFold_card_third p.n hn a
  have hcardReal : (p.n : ℝ) ≤ 3 * (inferenceFold p.n a).card := by exact_mod_cast hcard
  nlinarith

/-- Deterministic perturbation scale of the selected population contour. -/
def adaptiveSelectorRatioConstant (p : Parameters) (pStar : CertifiedBankInputs p) : ℝ :=
  let aStar := ((contourBank p pStar).aStarRat : ℝ)
  ordinaryContourPerturbationConstant p (populationNumeratorEnvelope p)
    (31 * aStar / 64) (23 * aStar / 64)

/-- The explicit constant in the adaptive selector's inverse-sample-size MSE bound. -/
def adaptiveSelectorRiskConstant (p : Parameters) (pStar : CertifiedBankInputs p)
    (K : ℝ) : ℝ :=
  let aStar := ((contourBank p pStar).aStarRat : ℝ)
  let Lrat := adaptiveSelectorRatioConstant p pStar
  12 * Lrat ^ 2 * K + 1536 * p.Ctheta ^ 2 * K / aStar ^ 2 + 2

/-- Whenever [the transform-accuracy input is strictly positive](hyp:hK), [the explicit
constant appearing in the adaptive selector's inverse-sample-size mean squared error bound is
strictly positive](goal), so that bound is never vacuous. -/
lemma adaptiveSelectorRiskConstant_pos
    (p : Parameters) (pStar : CertifiedBankInputs p) (K : ℝ) (hK : 0 < K) :
    0 < adaptiveSelectorRiskConstant p pStar K := by
  dsimp [adaptiveSelectorRiskConstant]
  have ha : (0 : ℝ) < ((contourBank p pStar).aStarRat : ℝ) := by
    exact_mod_cast (contourBank p pStar).aStarRat_pos
  positivity

/-- On the two-fold small-error event, the selected estimator has the
deterministic squared perturbation bound used by the risk proof. -/
lemma thetaHatSpec_sq_error_le_on_good
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m)
    (heps : p.eps1n p.n ≤
      (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹)
    (data : Fin p.n → Obs Xspace)
    (hd0 : residualFoldError p m 0 data ≤
      ((contourBank p pStar).aStarRat : ℝ) / 8)
    (hd1 : residualFoldError p m 1 data ≤
      ((contourBank p pStar).aStarRat : ℝ) / 8) :
    (thetaHatSpec p pStar cStar m.gcode data - m.theta0) ^ 2 ≤
      4 * (adaptiveSelectorRatioConstant p pStar) ^ 2 *
          ((residualFoldError p m 1 data) ^ 2 +
            (outcomeFoldError p m 1 data) ^ 2) +
        2 / (p.n : ℝ) ^ 2 := by
  let d1 := residualFoldError p m 1 data
  let e1 := outcomeFoldError p m 1 data
  let aStar := ((contourBank p pStar).aStarRat : ℝ)
  let mu := 31 * aStar / 64
  let nu := 23 * aStar / 64
  let Lrat := adaptiveSelectorRatioConstant p pStar
  have hpacket := canonicalSelectorPacket_of_small_errors
    p pStar cStar m hn hclass heps data hd0 hd1
  dsimp only at hpacket
  rcases hpacket with ⟨hgood, hratio, hidentify⟩
  have hpert := thetaHatSpec_good_event_exact_contour_perturbation
    p pStar cStar m.gcode data (residualMGF p m p.n)
      (outcomeResidualTransform p m p.n) d1 e1
      (populationNumeratorEnvelope p) mu nu m.theta0
      hclass.thetaRange hgood hratio hidentify
  have hnmax : max (p.n : ℝ) 1 = (p.n : ℝ) :=
    max_eq_left (by exact_mod_cast (show 1 ≤ p.n by omega))
  rw [hnmax] at hpert
  have hL : 0 ≤ Lrat := by
    change 0 ≤ searchRadius p *
      max nu⁻¹ (populationNumeratorEnvelope p * (mu * nu)⁻¹)
    apply mul_nonneg
    · unfold searchRadius
      have hR0 : 0 ≤ zeroRadius p := by
        unfold zeroRadius Ak
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg
            (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
      linarith
    · apply le_max_of_le_left
      exact inv_nonneg.mpr hgood.2.2.2.2.1.le
  have hd : 0 ≤ d1 := hgood.1
  have he : 0 ≤ e1 := hgood.2.1
  have hnpos : (0 : ℝ) < p.n := by positivity
  have hrhs : 0 ≤ Lrat * (d1 + e1) + 1 / (p.n : ℝ) := by positivity
  change |thetaHatSpec p pStar cStar m.gcode data - m.theta0| ≤
      Lrat * (d1 + e1) + 1 / (p.n : ℝ) at hpert
  have hsquare :
      (thetaHatSpec p pStar cStar m.gcode data - m.theta0) ^ 2 ≤
        (Lrat * (d1 + e1) + 1 / (p.n : ℝ)) ^ 2 := by
    rw [← sq_abs (thetaHatSpec p pStar cStar m.gcode data - m.theta0)]
    exact sq_le_sq₀ (abs_nonneg _) hrhs |>.2 hpert
  change (thetaHatSpec p pStar cStar m.gcode data - m.theta0) ^ 2 ≤
      4 * Lrat ^ 2 * (d1 ^ 2 + e1 ^ 2) + 2 / (p.n : ℝ) ^ 2
  calc
    _ ≤ (Lrat * (d1 + e1) + 1 / (p.n : ℝ)) ^ 2 := hsquare
    _ ≤ 2 * (Lrat * (d1 + e1)) ^ 2 + 2 * (1 / (p.n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (Lrat * (d1 + e1) - 1 / (p.n : ℝ))]
    _ ≤ 4 * Lrat ^ 2 * (d1 ^ 2 + e1 ^ 2) + 2 / (p.n : ℝ) ^ 2 := by
      have hde : (d1 + e1) ^ 2 ≤ 2 * (d1 ^ 2 + e1 ^ 2) := by
        nlinarith [sq_nonneg (d1 - e1)]
      have hmain : 2 * (Lrat * (d1 + e1)) ^ 2 ≤
          4 * Lrat ^ 2 * (d1 ^ 2 + e1 ^ 2) := by
        calc
          _ = (2 * Lrat ^ 2) * (d1 + e1) ^ 2 := by ring
          _ ≤ (2 * Lrat ^ 2) * (2 * (d1 ^ 2 + e1 ^ 2)) :=
            mul_le_mul_of_nonneg_left hde
              (mul_nonneg (by norm_num) (sq_nonneg Lrat))
          _ = _ := by ring
      have hrec : 2 * (1 / (p.n : ℝ)) ^ 2 = 2 / (p.n : ℝ) ^ 2 := by
        field_simp
      rw [hrec]
      linarith

/-- Projection onto the certified parameter range globally bounds squared loss. -/
lemma thetaHatSpec_sq_error_le_clip
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hclass : NonGaussianClass p p.n m)
    (data : Fin p.n → Obs Xspace) :
    (thetaHatSpec p pStar cStar m.gcode data - m.theta0) ^ 2 ≤
      4 * p.Ctheta ^ 2 := by
  rcases thetaHatSpec_mem_Icc p pStar cStar m.gcode data with ⟨hestlo, hesthi⟩
  rcases abs_le.mp hclass.thetaRange with ⟨hthetalo, hthetahi⟩
  have habs : |thetaHatSpec p pStar cStar m.gcode data - m.theta0| ≤
      2 * p.Ctheta := by
    rw [abs_le]
    constructor <;> linarith [p.constants_pos.1]
  rw [← sq_abs (thetaHatSpec p pStar cStar m.gcode data - m.theta0)]
  have hC : 0 ≤ 2 * p.Ctheta := by linarith [p.constants_pos.1]
  convert (sq_le_sq₀ (abs_nonneg _) hC).2 habs using 1 <;> first | rfl | ring

/-- Risk bridge from the foldwise transform L² estimate to the adaptive
selector's explicit MSE constant. -/
theorem thetaHatSpec_mseRisk_le_of_l2
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
    (hclass : NonGaussianClass p p.n m)
    (heps : p.eps1n p.n ≤
      (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹)
    (K : ℝ) (hK : 0 ≤ K)
    (hL2 : ∀ a : Fin 2,
      (∫⁻ data, ENNReal.ofReal ((residualFoldError p m a data) ^ 2) ∂iidLaw m p.n) +
      (∫⁻ data, ENNReal.ofReal ((outcomeFoldError p m a data) ^ 2) ∂iidLaw m p.n) ≤
        ENNReal.ofReal (K / (inferenceFold p.n a).card)) :
    mseRisk m p.n (thetaHatSpec p pStar cStar m.gcode) ≤
      ENNReal.ofReal (adaptiveSelectorRiskConstant p pStar K / p.n) := by
  let Q := iidLaw m p.n
  let aStar := ((contourBank p pStar).aStarRat : ℝ)
  let Lrat := adaptiveSelectorRatioConstant p pStar
  let d0 := residualFoldError p m 0
  let d1 := residualFoldError p m 1
  let e1 := outcomeFoldError p m 1
  let good : Set (Fin p.n → Obs Xspace) :=
    {data | d0 data ≤ aStar / 8 ∧ d1 data ≤ aStar / 8}
  have ha : 0 < aStar := by
    dsimp [aStar]
    exact_mod_cast (contourBank p pStar).aStarRat_pos
  have hnreal : (0 : ℝ) < p.n := by positivity
  have hd0meas : Measurable d0 := measurable_residualFoldError p m 0 hclass
  have hd1meas : Measurable d1 := measurable_residualFoldError p m 1 hclass
  have he1meas : Measurable e1 := measurable_outcomeFoldError p m 1 hclass
  have hgoodMeas : MeasurableSet good :=
    (measurableSet_le hd0meas measurable_const).inter
      (measurableSet_le hd1meas measurable_const)
  have hd0nonneg : ∀ data, 0 ≤ d0 data := by
    intro data
    exact transformSupError_nonneg _ _ _ _
  have hd1nonneg : ∀ data, 0 ≤ d1 data := by
    intro data
    exact transformSupError_nonneg _ _ _ _
  have he1nonneg : ∀ data, 0 ≤ e1 data := by
    intro data
    exact transformSupError_nonneg _ _ _ _
  have hfold0 := fold_errors_l2_le p m hn 0 K hK (hL2 0)
  have hfold1 := fold_errors_l2_le p m hn 1 K hK (hL2 1)
  have hd0L2 : (∫⁻ data, ENNReal.ofReal ((d0 data) ^ 2) ∂Q) ≤
      ENNReal.ofReal (3 * K / p.n) := by
    exact (le_add_right le_rfl).trans hfold0
  have hd1L2 : (∫⁻ data, ENNReal.ofReal ((d1 data) ^ 2) ∂Q) ≤
      ENNReal.ofReal (3 * K / p.n) := by
    exact (le_add_right le_rfl).trans hfold1
  have hd0bad : Q {data | aStar / 8 < d0 data} ≤
      ENNReal.ofReal (192 * K / (aStar ^ 2 * p.n)) := by
    have h := measure_gt_of_sq_lintegral_le Q d0 hd0meas hd0nonneg
      (aStar / 8) (3 * K / p.n) (by positivity) hd0L2
    convert h using 1
    congr 1
    field_simp
    <;> ring
  have hd1bad : Q {data | aStar / 8 < d1 data} ≤
      ENNReal.ofReal (192 * K / (aStar ^ 2 * p.n)) := by
    have h := measure_gt_of_sq_lintegral_le Q d1 hd1meas hd1nonneg
      (aStar / 8) (3 * K / p.n) (by positivity) hd1L2
    convert h using 1
    congr 1
    field_simp
    <;> ring
  have hgoodCompl : goodᶜ =
      {data | aStar / 8 < d0 data} ∪ {data | aStar / 8 < d1 data} := by
    ext data
    change ¬(d0 data ≤ aStar / 8 ∧ d1 data ≤ aStar / 8) ↔
      aStar / 8 < d0 data ∨ aStar / 8 < d1 data
    constructor
    · intro h
      by_cases h0 : d0 data ≤ aStar / 8
      · exact Or.inr (lt_of_not_ge (fun h1 ↦ h ⟨h0, h1⟩))
      · exact Or.inl (lt_of_not_ge h0)
    · rintro (h0 | h1) h
      · exact (not_lt_of_ge h.1) h0
      · exact (not_lt_of_ge h.2) h1
  have hbad : Q goodᶜ ≤ ENNReal.ofReal
      (384 * K / (aStar ^ 2 * p.n)) := by
    rw [hgoodCompl]
    calc
      _ ≤ Q {data | aStar / 8 < d0 data} + Q {data | aStar / 8 < d1 data} :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal (192 * K / (aStar ^ 2 * p.n)) +
          ENNReal.ofReal (192 * K / (aStar ^ 2 * p.n)) := add_le_add hd0bad hd1bad
      _ = ENNReal.ofReal (384 * K / (aStar ^ 2 * p.n)) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · positivity
        · positivity
  have hL : 0 ≤ Lrat := by
    dsimp [Lrat, adaptiveSelectorRatioConstant,
      ordinaryContourPerturbationConstant]
    have hR : 0 ≤ searchRadius p := by
      unfold searchRadius
      have hR0 : 0 ≤ zeroRadius p := by
        unfold zeroRadius Ak
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg
            (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
      linarith
    exact mul_nonneg hR (le_max_of_le_left (by positivity))
  let loss : (Fin p.n → Obs Xspace) → ENNReal := fun data ↦
    ENNReal.ofReal ((thetaHatSpec p pStar cStar m.gcode data - m.theta0) ^ 2)
  let goodBound : (Fin p.n → Obs Xspace) → ℝ := fun data ↦
    4 * Lrat ^ 2 * (d1 data ^ 2 + e1 data ^ 2) + 2 / (p.n : ℝ) ^ 2
  have hlossMeas : Measurable loss :=
    (((thetaHatSpec_measurable p pStar cStar m.gcode
      (m.gcode_measurable p.n)).sub measurable_const).pow_const 2)
      |>.ennreal_ofReal
  have hgoodBoundMeas : Measurable (fun data ↦ ENNReal.ofReal (goodBound data)) :=
    ((measurable_const.mul
      ((hd1meas.pow_const 2).add (he1meas.pow_const 2))).add measurable_const).ennreal_ofReal
  have hgoodBoundENN (data : Fin p.n → Obs Xspace) :
      ENNReal.ofReal (goodBound data) =
        ENNReal.ofReal (4 * Lrat ^ 2) *
          (ENNReal.ofReal (d1 data ^ 2) + ENNReal.ofReal (e1 data ^ 2)) +
        ENNReal.ofReal (2 / (p.n : ℝ) ^ 2) := by
    dsimp [goodBound]
    rw [ENNReal.ofReal_add
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Lrat))
        (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by positivity)]
    rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (sq_nonneg Lrat))]
    rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have hd1ENN : Measurable (fun data ↦ ENNReal.ofReal (d1 data ^ 2)) :=
    (hd1meas.pow_const 2).ennreal_ofReal
  have he1ENN : Measurable (fun data ↦ ENNReal.ofReal (e1 data ^ 2)) :=
    (he1meas.pow_const 2).ennreal_ofReal
  have hgoodInt : (∫⁻ data in good, loss data ∂Q) ≤
      ENNReal.ofReal ((12 * Lrat ^ 2 * K + 2) / p.n) := by
    calc
      _ ≤ ∫⁻ data in good, ENNReal.ofReal (goodBound data) ∂Q := by
        apply setLIntegral_mono hgoodBoundMeas
        intro data hdata
        apply ENNReal.ofReal_le_ofReal
        exact thetaHatSpec_sq_error_le_on_good p pStar cStar m hn hclass heps data
          hdata.1 hdata.2
      _ ≤ ∫⁻ data, ENNReal.ofReal (goodBound data) ∂Q :=
        setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (4 * Lrat ^ 2) *
            ((∫⁻ data, ENNReal.ofReal (d1 data ^ 2) ∂Q) +
              (∫⁻ data, ENNReal.ofReal (e1 data ^ 2) ∂Q)) +
            ENNReal.ofReal (2 / (p.n : ℝ) ^ 2) := by
        simp_rw [hgoodBoundENN]
        rw [lintegral_add_left (measurable_const.fun_mul (hd1ENN.fun_add he1ENN)),
          lintegral_const_mul _ (hd1ENN.fun_add he1ENN),
          lintegral_add_left hd1ENN, lintegral_const]
        simp [Q, iidLaw, mul_add]
      _ ≤ ENNReal.ofReal (4 * Lrat ^ 2) * ENNReal.ofReal (3 * K / p.n) +
            ENNReal.ofReal (2 / (p.n : ℝ) ^ 2) := by
        have hmul := mul_le_mul_right hfold1 (ENNReal.ofReal (4 * Lrat ^ 2))
        exact add_le_add (by simpa [d1, e1, Q] using hmul) le_rfl
      _ = ENNReal.ofReal
          (12 * Lrat ^ 2 * K / p.n + 2 / (p.n : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add]
        · congr 1
          ring
        · positivity
        · positivity
      _ ≤ ENNReal.ofReal ((12 * Lrat ^ 2 * K + 2) / p.n) := by
        apply ENNReal.ofReal_le_ofReal
        have hnOne : (1 : ℝ) ≤ p.n := by exact_mod_cast (show 1 ≤ p.n by omega)
        have hsmall : 2 / (p.n : ℝ) ^ 2 ≤ 2 / (p.n : ℝ) := by
          rw [div_le_div_iff₀ (sq_pos_of_pos hnreal) hnreal]
          nlinarith
        calc
          _ ≤ 12 * Lrat ^ 2 * K / p.n + 2 / p.n := by linarith
          _ = _ := by ring
  have hbadInt : (∫⁻ data in goodᶜ, loss data ∂Q) ≤
      ENNReal.ofReal (1536 * p.Ctheta ^ 2 * K / (aStar ^ 2 * p.n)) := by
    calc
      _ ≤ ∫⁻ _data in goodᶜ, ENNReal.ofReal (4 * p.Ctheta ^ 2) ∂Q := by
        apply setLIntegral_mono measurable_const
        intro data _
        exact ENNReal.ofReal_le_ofReal
          (thetaHatSpec_sq_error_le_clip p pStar cStar m hclass data)
      _ = ENNReal.ofReal (4 * p.Ctheta ^ 2) * Q goodᶜ :=
        setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (4 * p.Ctheta ^ 2) *
          ENNReal.ofReal (384 * K / (aStar ^ 2 * p.n)) :=
        mul_le_mul_right hbad _
      _ = ENNReal.ofReal
          (1536 * p.Ctheta ^ 2 * K / (aStar ^ 2 * p.n)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  change ∫⁻ data, loss data ∂Q ≤ _
  rw [← lintegral_add_compl loss hgoodMeas]
  calc
    _ ≤ ENNReal.ofReal ((12 * Lrat ^ 2 * K + 2) / p.n) +
        ENNReal.ofReal (1536 * p.Ctheta ^ 2 * K / (aStar ^ 2 * p.n)) :=
      add_le_add hgoodInt hbadInt
    _ = ENNReal.ofReal (adaptiveSelectorRiskConstant p pStar K / p.n) := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        dsimp [adaptiveSelectorRiskConstant, Lrat, aStar]
        field_simp
        <;> ring
      · positivity
      · positivity

/-- Uniform adaptive-selector MSE bound obtained from the empirical-transform
L² theorem.  The witness `K` depends only on the six displayed fixed class
constants. -/
theorem thetaHatSpec_mseRisk_le
    {Xspace : Type*} [MeasurableSpace Xspace]
    (Ctheta Cg Cq psieta psixi R1 : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg → p.Cq = Cq →
        p.psieta = psieta → p.psixi = psixi → searchRadius p = R1 →
      ∀ (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
        (m : Model (Xspace := Xspace) p),
        2 ≤ p.n → NonGaussianClass p p.n m →
        IidSampling p.n m.P (iidLaw m p.n) →
        p.eps1n p.n ≤
          (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹ →
        mseRisk m p.n (thetaHatSpec p pStar cStar m.gcode) ≤
          ENNReal.ofReal (adaptiveSelectorRiskConstant p pStar K / p.n) := by
  rcases empirical_transform_uniform_l2 (Xspace := Xspace)
      Ctheta Cg Cq psieta psixi R1 with
    ⟨K, hK, hUniform⟩
  refine ⟨K, hK, ?_⟩
  intro p hpθ hpg hpq hpη hpξ hpR pStar cStar m hn hclass hiid heps
  apply thetaHatSpec_mseRisk_le_of_l2 p pStar cStar m hn hclass heps K hK.le
  intro a
  simpa [residualFoldError, outcomeFoldError, hpR] using
    hUniform p hpθ hpg hpq hpη hpξ hpR hn m hclass hiid a
      (inferenceFold_nonempty p.n hn a)

/-- The preceding risk theorem with its proof's explicit transform constant,
quantified before the covariate space. -/
theorem thetaHatSpec_mseRisk_le_explicit
    (Ctheta Cg Cq psieta psixi R1 : ℝ) :
    ∀ {Xspace : Type*} [MeasurableSpace Xspace]
      (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg → p.Cq = Cq →
        p.psieta = psieta → p.psixi = psixi → searchRadius p = R1 →
      ∀ (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
        (m : Model (Xspace := Xspace) p),
        2 ≤ p.n → NonGaussianClass p p.n m →
        IidSampling p.n m.P (iidLaw m p.n) →
        p.eps1n p.n ≤
          (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹ →
        mseRisk m p.n (thetaHatSpec p pStar cStar m.gcode) ≤
          ENNReal.ofReal (adaptiveSelectorRiskConstant p pStar
            (empiricalTransformL2Constant Ctheta Cg Cq psieta psixi R1) / p.n) := by
  intro Xspace inst p hpθ hpg hpq hpη hpξ hpR pStar cStar m hn hclass hiid heps
  apply thetaHatSpec_mseRisk_le_of_l2 p pStar cStar m hn hclass heps
    (empiricalTransformL2Constant Ctheta Cg Cq psieta psixi R1)
    (empiricalTransformL2Constant_pos _ _ _ _ _ _).le
  intro a
  simpa [residualFoldError, outcomeFoldError, hpR] using
    empirical_transform_uniform_l2_explicit Ctheta Cg Cq psieta psixi R1
      p hpθ hpg hpq hpη hpξ hpR hn m hclass hiid a
        (inferenceFold_nonempty p.n hn a)

/-- The generalized-quantile consequence of any positive adaptive-selector
MSE constant, at the paper's probability level `1 - gamma`. -/
theorem thetaHatSpec_generalizedQuantile_le_of_mseRisk_le
    {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (m : Model (Xspace := Xspace) p) (hn : 1 ≤ p.n)
    (C : ℝ) (hC : 0 < C)
    (hrisk : mseRisk m p.n (thetaHatSpec p pStar cStar m.gcode) ≤
      ENNReal.ofReal (C / p.n)) :
    generalizedQuantile p p.n m
        (fun data ↦ |thetaHatSpec p pStar cStar m.gcode data - m.theta0|) ≤
      Real.sqrt (C / (p.gamma * p.n)) := by
  let Q := iidLaw m p.n
  let W : (Fin p.n → Obs Xspace) → ℝ := fun data ↦
    |thetaHatSpec p pStar cStar m.gcode data - m.theta0|
  let t := Real.sqrt (C / (p.gamma * p.n))
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, iidLaw]
    infer_instance
  have hgamma : 0 < p.gamma := lt_trans (by norm_num) p.gamma_mem.1
  have hnreal : (0 : ℝ) < p.n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have htarg : 0 < C / (p.gamma * p.n) := by positivity
  have ht : 0 < t := Real.sqrt_pos.2 htarg
  have hWmeas : Measurable W :=
    ((thetaHatSpec_measurable p pStar cStar m.gcode
      (m.gcode_measurable p.n)).sub measurable_const).abs
  letI : IsProbabilityMeasure (Measure.map W Q) :=
    Measure.isProbabilityMeasure_map hWmeas.aemeasurable
  have hWL2 : (∫⁻ data, ENNReal.ofReal ((W data) ^ 2) ∂Q) ≤
      ENNReal.ofReal (C / p.n) := by
    simpa [mseRisk, Q, W, sq_abs] using hrisk
  have hbad : Q {data | t < W data} ≤ ENNReal.ofReal p.gamma := by
    have h := measure_gt_of_sq_lintegral_le Q W hWmeas
      (fun data ↦ abs_nonneg _) t (C / p.n) ht hWL2
    convert h using 1
    congr 1
    dsimp [t]
    rw [Real.sq_sqrt htarg.le]
    field_simp
  have hbadMeas : MeasurableSet {data | t < W data} :=
    measurableSet_lt measurable_const hWmeas
  have hbadReal : Q.real {data | t < W data} ≤ p.gamma := by
    rw [measureReal_def]
    calc
      (Q {data | t < W data}).toReal ≤ (ENNReal.ofReal p.gamma).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
      _ = p.gamma := ENNReal.toReal_ofReal hgamma.le
  have hgoodSet : {data | W data ≤ t} = {data | t < W data}ᶜ := by
    ext data
    simp
  have hgoodReal : 1 - p.gamma ≤ Q.real {data | W data ≤ t} := by
    rw [hgoodSet, measureReal_compl hbadMeas]
    have hQ : Q.real Set.univ = 1 := by simp [Q, iidLaw]
    rw [hQ]
    linarith
  have htau0 : 0 < 1 - p.gamma := sub_pos.mpr p.gamma_mem.2
  have htau1 : 1 - p.gamma < 1 := sub_lt_self 1 hgamma
  apply (Causalean.Stat.quantile_le_iff htau0 htau1).2
  rw [ProbabilityTheory.cdf_eq_real]
  change 1 - p.gamma ≤ (Measure.map W Q).real (Set.Iic t)
  rw [measureReal_def]
  rw [Measure.map_apply hWmeas measurableSet_Iic]
  change 1 - p.gamma ≤ Q.real {data | W data ≤ t}
  exact hgoodReal

end CausalSmith.Stat.SaPlmCumulantConverse
