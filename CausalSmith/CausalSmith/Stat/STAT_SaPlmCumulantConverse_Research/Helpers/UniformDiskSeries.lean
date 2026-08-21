import Causalean.Mathlib.MeasureTheory.SupCountableDense
import Causalean.Mathlib.IIDCenteredSum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Measurable uniform bounds for analytic series on a disk

This file isolates the two generic steps used by empirical analytic-transform
arguments: a power-series coefficient majorant controls the supremum norm on a
closed disk, and a countable dense skeleton makes that supremum measurable and
transfers an `L²` envelope bound to it.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- The uniform norm of a complex-valued random function on the closed disk of
radius `R`. -/
def diskSupNorm {Ω : Type*} (H : Ω → ℂ → ℂ) (R : ℝ) (ω : Ω) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ ≤ R ∧ x = ‖H ω z‖}

/-- The set-builder presentation of the disk supremum agrees with its image
presentation. -/
theorem diskSupNorm_eq_sSup_image {Ω : Type*} (H : Ω → ℂ → ℂ) (R : ℝ) (ω : Ω) :
    diskSupNorm H R ω = sSup ((fun z ↦ ‖H ω z‖) '' {z : ℂ | ‖z‖ ≤ R}) := by
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- An absolutely summable coefficient majorant bounds an analytic series
uniformly on the closed disk of radius `R`. -/
theorem norm_tsum_mul_pow_le_tsum_norm_mul_pow
    (c : ℕ → ℂ) {R : ℝ}
    (hsum : Summable (fun k ↦ ‖c k‖ * R ^ k))
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖∑' k : ℕ, c k * z ^ k‖ ≤ ∑' k : ℕ, ‖c k‖ * R ^ k := by
  apply tsum_of_norm_bounded hsum.hasSum
  intro k
  rw [norm_mul, norm_pow]
  gcongr

/-- The coefficient majorant of an analytic series bounds its uniform norm on
the closed disk. -/
theorem diskSupNorm_tsum_mul_pow_le
    {Ω : Type*} (c : Ω → ℕ → ℂ) {R : ℝ} (hR : 0 ≤ R) (ω : Ω)
    (hsum : Summable (fun k ↦ ‖c ω k‖ * R ^ k)) :
    diskSupNorm (fun ω z ↦ ∑' k : ℕ, c ω k * z ^ k) R ω ≤
      ∑' k : ℕ, ‖c ω k‖ * R ^ k := by
  apply csSup_le
  · exact ⟨‖∑' k : ℕ, c ω k * (0 : ℂ) ^ k‖, 0, by simpa using hR, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    exact norm_tsum_mul_pow_le_tsum_norm_mul_pow (c ω) hsum hz

/-- A countable dense skeleton makes a pointwise disk supremum measurable once
the supremum over the skeleton is known to equal the full supremum. -/
theorem measurable_diskSupNorm_of_countable_dense
    {Ω : Type*} [MeasurableSpace Ω] (H : Ω → ℂ → ℂ) (R : ℝ)
    (D : Set ℂ) (hD : D.Countable)
    (hH : ∀ z ∈ D, Measurable (fun ω ↦ ‖H ω z‖))
    (heq : ∀ ω,
      diskSupNorm H R ω = sSup ((fun z ↦ ‖H ω z‖) '' D)) :
    Measurable (diskSupNorm H R) := by
  have hm := Causalean.Mathlib.MeasureTheory.measurable_sSup_image_of_countable_dense
    {z : ℂ | ‖z‖ ≤ R} D (fun ω z ↦ ‖H ω z‖) hD hH (fun ω ↦ by
      rw [← diskSupNorm_eq_sSup_image]
      exact heq ω)
  convert hm using 1
  ext ω
  exact diskSupNorm_eq_sSup_image H R ω

/-- A measurable pointwise envelope transfers its squared `lintegral` bound to
the uniform norm on a nonempty closed disk. -/
theorem diskSupNorm_sq_lintegral_le_of_countable_dense
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Ω → ℂ → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (D : Set ℂ) (hD : D.Countable)
    (hH : ∀ z ∈ D, Measurable (fun ω ↦ ‖H ω z‖))
    (heq : ∀ ω,
      diskSupNorm H R ω = sSup ((fun z ↦ ‖H ω z‖) '' D))
    (A : Ω → ℝ) (hA : ∀ ω, 0 ≤ A ω)
    (hbound : ∀ ω z, ‖z‖ ≤ R → ‖H ω z‖ ≤ A ω)
    {B : ℝ≥0∞}
    (hA2 : ∫⁻ ω, ENNReal.ofReal ((A ω) ^ 2) ∂μ ≤ B) :
    Measurable (diskSupNorm H R) ∧
      ∫⁻ ω, ENNReal.ofReal ((diskSupNorm H R ω) ^ 2) ∂μ ≤ B := by
  constructor
  · exact measurable_diskSupNorm_of_countable_dense H R D hD hH heq
  · refine (lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal ?_).trans hA2
    have hbdd : BddAbove ((fun z ↦ ‖H ω z‖) '' {z : ℂ | ‖z‖ ≤ R}) :=
      ⟨A ω, by
        rintro x ⟨z, hz, rfl⟩
        exact hbound ω z hz⟩
    have hzero_mem : ‖(0 : ℂ)‖ ≤ R := by simpa using hR
    have hsup_nonneg : 0 ≤ diskSupNorm H R ω := by
      exact (norm_nonneg (H ω 0)).trans
        (by
          rw [diskSupNorm_eq_sSup_image]
          exact le_csSup hbdd ⟨0, hzero_mem, rfl⟩)
    have hsup_le : diskSupNorm H R ω ≤ A ω := by
      rw [diskSupNorm_eq_sSup_image]
      apply csSup_le
      · exact ⟨‖H ω 0‖, 0, hzero_mem, rfl⟩
      · rintro x ⟨z, hz, rfl⟩
        exact hbound ω z hz
    exact (sq_le_sq₀ hsup_nonneg (hA ω)).2 hsup_le

/-- Under a finite product probability law, the centered empirical average of
a real square-integrable coefficient has second moment at most its population
`L²` energy divided by the sample size. -/
theorem pi_centered_average_sq_lintegral_le
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {P : Measure X} [IsProbabilityMeasure P]
    (hcard : 0 < Fintype.card ι) {f : X → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ v : ι → X, ENNReal.ofReal
        ((((Fintype.card ι : ℝ)⁻¹) *
          ∑ i, (f (v i) - ∫ x, f x ∂P)) ^ 2) ∂Measure.pi (fun _ : ι ↦ P)
      ≤ (Fintype.card ι : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) := by
  let nE : ENNReal := Fintype.card ι
  let B : ENNReal := ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2)
  have hnE_ne_zero : nE ≠ 0 := by simp [nE, Nat.ne_of_gt hcard]
  have hnE_ne_top : nE ≠ ∞ := by simp [nE]
  have hraw :
      ∫⁻ v : ι → X, ENNReal.ofReal
          ((∑ i, (f (v i) - ∫ x, f x ∂P)) ^ 2) ∂Measure.pi (fun _ : ι ↦ P)
        ≤ nE * B := by
    simpa [nE, B] using
      (Causalean.Mathlib.pi_centered_sum_sq_lintegral_le
        (ι := ι) (X := fun _ : ι ↦ X) (P := fun _ : ι ↦ P)
        (f := fun _ : ι ↦ f) (fun _ ↦ hf))
  have hnR_pos : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hcard
  have hscale : ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹ ^ 2) = nE⁻¹ ^ 2 := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hnR_pos]
    simp [nE]
  calc
    ∫⁻ v : ι → X, ENNReal.ofReal
        ((((Fintype.card ι : ℝ)⁻¹) *
          ∑ i, (f (v i) - ∫ x, f x ∂P)) ^ 2) ∂Measure.pi (fun _ : ι ↦ P)
        = nE⁻¹ ^ 2 * ∫⁻ v : ι → X, ENNReal.ofReal
            ((∑ i, (f (v i) - ∫ x, f x ∂P)) ^ 2) ∂Measure.pi (fun _ : ι ↦ P) := by
          rw [← lintegral_const_mul' _ _ (by simp [hnE_ne_zero])]
          apply lintegral_congr
          intro v
          rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), hscale]
    _ ≤ nE⁻¹ ^ 2 * (nE * B) := mul_le_mul_right hraw _
    _ = nE⁻¹ * B := by
      rw [pow_two]
      calc
        nE⁻¹ * nE⁻¹ * (nE * B) = nE⁻¹ * ((nE⁻¹ * nE) * B) := by ac_rfl
        _ = nE⁻¹ * B := by
          rw [ENNReal.inv_mul_cancel hnE_ne_zero hnE_ne_top, one_mul]
    _ = (Fintype.card ι : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) := rfl

/-- Restricting a product sample to a nonempty deterministic finset preserves
the inverse-cardinality second-moment bound for a centered average. -/
theorem pi_finset_centered_average_sq_lintegral_le
    {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P]
    {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty)
    {f : X → ℝ} (hf : MemLp f 2 P) {C : ℝ} (hC : 0 ≤ C)
    (hnorm : eLpNorm f 2 P ≤ ENNReal.ofReal C) :
    ∫⁻ v : Fin n → X, ENNReal.ofReal
        ((((I.card : ℝ)⁻¹) * ∑ i ∈ I, (f (v i) - ∫ x, f x ∂P)) ^ 2)
        ∂Measure.pi (fun _ : Fin n ↦ P) ≤
      (I.card : ℝ≥0∞)⁻¹ * ENNReal.ofReal (C ^ 2) := by
  let fi : Fin n → X → ℝ := fun i x ↦ if i ∈ I then f x else 0
  have hfi : ∀ i, MemLp (fi i) 2 P := by
    intro i
    by_cases hi : i ∈ I <;> simp [fi, hi, hf]
  have hraw := Causalean.Mathlib.pi_centered_sum_sq_lintegral_le
    (P := fun _ : Fin n ↦ P) (f := fi) hfi
  have hsum (v : Fin n → X) :
      ∑ i, (fi i (v i) - ∫ x, fi i x ∂P) =
        ∑ i ∈ I, (f (v i) - ∫ x, f x ∂P) := by
    classical
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    congr 1
    · simpa [fi] using Finset.sum_ite_mem_eq I (fun i ↦ f (v i))
    · calc
        ∑ i, ∫ x, fi i x ∂P =
            ∑ i, if i ∈ I then ∫ x, f x ∂P else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hmem : i ∈ I <;> simp [fi, hmem]
        _ = _ := by simpa using
          Finset.sum_ite_mem_eq I (fun _ : Fin n ↦ ∫ x, f x ∂P)
  have hrhs :
      ∑ i : Fin n, ENNReal.ofReal ((eLpNorm (fi i) 2 P).toReal ^ 2) ≤
        (I.card : ℝ≥0∞) * ENNReal.ofReal (C ^ 2) := by
    rw [show ∑ i : Fin n, ENNReal.ofReal ((eLpNorm (fi i) 2 P).toReal ^ 2) =
        ∑ i ∈ I, ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) by
      classical
      calc
        ∑ i, ENNReal.ofReal ((eLpNorm (fi i) 2 P).toReal ^ 2) =
            ∑ i, if i ∈ I then
              ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) else 0 := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases hmem : i ∈ I <;> simp [fi, hmem]
        _ = _ := Finset.sum_ite_mem_eq I _]
    rw [Finset.sum_const, nsmul_eq_mul]
    gcongr
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq
      (ENNReal.toReal_ofReal hC)
  have hraw' :
      ∫⁻ v : Fin n → X, ENNReal.ofReal
          ((∑ i ∈ I, (f (v i) - ∫ x, f x ∂P)) ^ 2)
          ∂Measure.pi (fun _ : Fin n ↦ P) ≤
        (I.card : ℝ≥0∞) * ENNReal.ofReal (C ^ 2) := by
    simpa only [hsum] using hraw.trans hrhs
  let cE : ℝ≥0∞ := I.card
  have hc0 : cE ≠ 0 := by simp [cE, hI.card_pos.ne']
  have hctop : cE ≠ ∞ := by simp [cE]
  have hcR : 0 < (I.card : ℝ) := Nat.cast_pos.mpr hI.card_pos
  calc
    _ = cE⁻¹ ^ 2 * ∫⁻ v : Fin n → X, ENNReal.ofReal
          ((∑ i ∈ I, (f (v i) - ∫ x, f x ∂P)) ^ 2)
          ∂Measure.pi (fun _ : Fin n ↦ P) := by
      rw [← lintegral_const_mul' _ _ (by simp [hc0])]
      apply lintegral_congr
      intro v
      rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hcR]
      simp [cE]
    _ ≤ cE⁻¹ ^ 2 * (cE * ENNReal.ofReal (C ^ 2)) :=
      mul_le_mul_right hraw' _
    _ = cE⁻¹ * ENNReal.ofReal (C ^ 2) := by
      rw [pow_two]
      calc
        cE⁻¹ * cE⁻¹ * (cE * ENNReal.ofReal (C ^ 2)) =
            cE⁻¹ * ((cE⁻¹ * cE) * ENNReal.ofReal (C ^ 2)) := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ = _ := rfl

/-- A measurable real function whose squared nonnegative integral is bounded
by `C²` belongs to `L²` and has `L²` norm at most `C`. -/
theorem memLp_two_and_eLpNorm_le_of_sq_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hsq : ∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂μ ≤ ENNReal.ofReal (C ^ 2)) :
    MemLp f 2 μ ∧ eLpNorm f 2 μ ≤ ENNReal.ofReal C := by
  have hsq_integrable : Integrable (fun ω ↦ (f ω) ^ 2) μ := by
    refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    exact hsq.trans_lt ENNReal.ofReal_lt_top
  have hf_mem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hsq_integrable
  refine ⟨hf_mem, ?_⟩
  have hsq' :
      ENNReal.ofReal ((eLpNorm f 2 μ).toReal ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
    rw [Causalean.Mathlib.eLpNorm_two_sq_toReal_eq_integral_sq hf_mem]
    calc
      ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) =
          ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
        · simpa [Real.norm_eq_abs, sq_abs] using hsq_integrable
        · exact Filter.Eventually.of_forall fun _ ↦ sq_nonneg _
      _ = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
        apply lintegral_congr
        intro x
        rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ENNReal.ofReal (C ^ 2) := hsq
  have hreal_sq : (eLpNorm f 2 μ).toReal ^ 2 ≤ C ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg C)).1 hsq'
  have hreal : (eLpNorm f 2 μ).toReal ≤ C :=
    (sq_le_sq₀ ENNReal.toReal_nonneg hC).1 hreal_sq
  rw [← ENNReal.ofReal_toReal hf_mem.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hreal

set_option maxHeartbeats 400000 in
-- Elaborating the finite `eLpNorm` sums and their liminf bound exceeds the default budget.
/-- Countably many measurable nonnegative coefficient envelopes obey the `L²`
Minkowski bound when their individual `L²` norms have a summable real
majorant.  This packages the finite-truncation and `L²` limit step needed after
applying `pi_centered_average_sq_lintegral_le` coefficient by coefficient. -/
theorem tsum_sq_lintegral_le_tsum_lpNorm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Ω → ℝ)
    (hAmeas : ∀ k, Measurable (A k))
    (hAsum : ∀ ω, Summable (fun k ↦ A k ω))
    (b : ℕ → ℝ) (hbnonneg : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hAbound : ∀ k, eLpNorm (A k) 2 μ ≤ ENNReal.ofReal (b k)) :
    ∫⁻ ω, ENNReal.ofReal ((∑' k, A k ω) ^ 2) ∂μ ≤
      ENNReal.ofReal ((∑' k, b k) ^ 2) := by
  let S : ℕ → Ω → ℝ := fun n ↦ ∑ k ∈ Finset.range n, A k
  have hSmeas : ∀ n, Measurable (S n) := by
    intro n
    rw [show S n = (fun ω ↦ ∑ k ∈ Finset.range n, A k ω) by
      funext ω
      simp [S]]
    exact Finset.measurable_sum (Finset.range n) fun k _ ↦ hAmeas k
  have hStendsto : ∀ ω, Filter.Tendsto (fun n ↦ S n ω) Filter.atTop
      (𝓝 (∑' k, A k ω)) := by
    intro ω
    simpa [S, Finset.sum_apply] using (hAsum ω).hasSum.tendsto_sum_nat
  have hpartial : ∀ n,
      eLpNorm (S n) 2 μ ≤ ENNReal.ofReal (∑' k, b k) := by
    intro n
    calc
      eLpNorm (S n) 2 μ = eLpNorm (∑ k ∈ Finset.range n, A k) 2 μ := rfl
      _ ≤ ∑ k ∈ Finset.range n, eLpNorm (A k) 2 μ := by
        exact eLpNorm_sum_le
          (fun k _ ↦ (hAmeas k).aestronglyMeasurable) (by norm_num)
      _ ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (b k) := by
        exact Finset.sum_le_sum fun k _ ↦ hAbound k
      _ = ENNReal.ofReal (∑ k ∈ Finset.range n, b k) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        exact fun k _ ↦ hbnonneg k
      _ ≤ ENNReal.ofReal (∑' k, b k) := by
        apply ENNReal.ofReal_le_ofReal
        exact hbsum.sum_le_tsum (Finset.range n) fun k _ ↦ hbnonneg k
  have hlimnorm : eLpNorm (fun ω ↦ ∑' k, A k ω) 2 μ ≤
      ENNReal.ofReal (∑' k, b k) := by
    refine (MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
      (p := 2) (fun n ↦ (hSmeas n).aestronglyMeasurable)
      (fun ω ↦ ∑' k, A k ω) ?_).trans ?_
    · exact Filter.Eventually.of_forall hStendsto
    · refine liminf_le_of_le (by isBoundedDefault) fun c hc ↦ ?_
      obtain ⟨n, hn⟩ := (hc.and (Filter.Eventually.of_forall hpartial)).exists
      exact hn.1.trans hn.2
  have hsum_b_nonneg : 0 ≤ ∑' k, b k := tsum_nonneg hbnonneg
  have hlimit_meas : AEStronglyMeasurable (fun ω ↦ ∑' k, A k ω) μ := by
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n ↦ (hSmeas n).aestronglyMeasurable)
      (Filter.Eventually.of_forall hStendsto)
  have hlimit_mem : MemLp (fun ω ↦ ∑' k, A k ω) 2 μ :=
    ⟨hlimit_meas, hlimnorm.trans_lt ENNReal.ofReal_lt_top⟩
  have hlintegral_eq :
      ∫⁻ ω, ENNReal.ofReal ((∑' k, A k ω) ^ 2) ∂μ =
        ENNReal.ofReal ((eLpNorm (fun ω ↦ ∑' k, A k ω) 2 μ).toReal ^ 2) := by
    calc
      ∫⁻ ω, ENNReal.ofReal ((∑' k, A k ω) ^ 2) ∂μ =
          ENNReal.ofReal (∫ ω, (∑' k, A k ω) ^ 2 ∂μ) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
        · exact hlimit_mem.integrable_sq
        · exact Filter.Eventually.of_forall fun _ ↦ sq_nonneg _
      _ = ENNReal.ofReal (∫ ω, ‖∑' k, A k ω‖ ^ 2 ∂μ) := by
        congr 2
        funext ω
        rw [Real.norm_eq_abs, sq_abs]
      _ = ENNReal.ofReal
          ((eLpNorm (fun ω ↦ ∑' k, A k ω) 2 μ).toReal ^ 2) :=
        (Causalean.Mathlib.eLpNorm_two_sq_toReal_eq_integral_sq hlimit_mem).symm
  rw [hlintegral_eq]
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ ENNReal.toReal_nonneg hsum_b_nonneg).2
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hlimnorm |>.trans_eq
    (ENNReal.toReal_ofReal hsum_b_nonneg)

end CausalSmith.Stat.SaPlmCumulantConverse
