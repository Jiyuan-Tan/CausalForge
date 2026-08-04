import CausalSmith.Substrate.UniformGibbsRadiusConcentration.RelativeBernstein
import CausalSmith.Substrate.UniformGibbsRadiusConcentration.NetTransfer
import Causalean.Stat.Concentration.FiniteDimensionalNet
import Causalean.Stat.Sample.PiTransport

/-!
# Uniform relative concentration from finite-dimensional nets

This file combines `Causalean.exists_internal_net_card_le` (the internal
volumetric net), sharp finite-class relative concentration, and exact
three-error transfer.
-/

noncomputable section

namespace CausalSmith.Substrate

open MeasureTheory ProbabilityTheory Metric Module Set
open scoped BigOperators

variable {Ω X E : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem integrable_of_mem_Icc
    {h : X → ℝ} (hh : Measurable h)
    (h01 : ∀ x, h x ∈ Set.Icc (0 : ℝ) 1)
    [IsFiniteMeasure P] :
    Integrable h P := by
  refine Integrable.of_bound hh.aestronglyMeasurable 1
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [(h01 x).1], (h01 x).2⟩

/-- A pointwise Lipschitz bound between bounded measurable functions transfers
to their population integrals under a probability measure. -/
theorem integral_sub_le_of_pointwise
    [IsProbabilityMeasure P]
    {h k : X → ℝ} (hh : Measurable h) (hk : Measurable k)
    (h01 : ∀ x, h x ∈ Set.Icc (0 : ℝ) 1)
    (k01 : ∀ x, k x ∈ Set.Icc (0 : ℝ) 1)
    {eps : ℝ} (hpoint : ∀ x, |h x - k x| ≤ eps) :
    |(∫ x, h x ∂P) - ∫ x, k x ∂P| ≤ eps := by
  have hhint := integrable_of_mem_Icc (P := P) hh h01
  have hkint := integrable_of_mem_Icc (P := P) hk k01
  rw [← integral_sub hhint hkint, ← Real.norm_eq_abs]
  simpa [measureReal_univ_eq_one] using
    (norm_integral_le_of_norm_le_const
      (μ := P) (f := fun x => h x - k x)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hpoint x))

/-- A pointwise Lipschitz bound transfers to every empirical mean. -/
theorem sampleMean_sub_le_of_pointwise
    (S : Causalean.Stat.IIDSample Ω X μ P)
    {h k : X → ℝ} {eps : ℝ}
    (hpoint : ∀ x, |h x - k x| ≤ eps)
    (n : ℕ) (hn : 0 < n) (ω : Ω) :
    |S.sampleMean h n ω - S.sampleMean k n ω| ≤ eps := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold Causalean.Stat.IIDSample.sampleMean
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hnR.le)]
  calc
    (n : ℝ)⁻¹ *
        |∑ i ∈ Finset.range n, (h (S.Z i ω) - k (S.Z i ω))| ≤
      (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, |h (S.Z i ω) - k (S.Z i ω)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, eps := by
      gcongr with i hi
      exact hpoint (S.Z i ω)
    _ = eps := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- Uniform relative comparison for a subset of the unit ball in a
finite-dimensional normed space.  A pointwise `L`-Lipschitz `[0,1]`-valued
functional is controlled with entropy dimension `D`. -/
theorem uniform_relative_comparison_of_finiteDimensional
    (S : Causalean.Stat.IIDSample Ω X μ P)
    (A : Set E) (hAne : A.Nonempty)
    (hunit : ∀ e ∈ A, ‖e‖ ≤ 1)
    (R : E → X → ℝ)
    (hmeas : ∀ e ∈ A, Measurable (R e))
    (h01 : ∀ e ∈ A, ∀ x, R e x ∈ Set.Icc (0 : ℝ) 1)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ e ∈ A, ∀ e' ∈ A, ∀ x,
      |R e x - R e' x| ≤ L * ‖e - e'‖)
    (D n : ℕ) (hdim : finrank ℝ E ≤ D) (hn : 0 < n)
    (zeta : ℝ) (hzeta : 0 < zeta) :
    μ.real {ω | ∀ e ∈ A,
      (∫ x, R e x ∂P) ≤
          2 * S.sampleMean (R e) n ω +
            8 / (3 * n) *
              (Real.log (2 / zeta) +
                D * Real.log (1 + 4 * n * L)) + 3 / n ∧
      S.sampleMean (R e) n ω ≤
          2 * (∫ x, R e x ∂P) +
            8 / (3 * n) *
              (Real.log (2 / zeta) +
                D * Real.log (1 + 4 * n * L)) + 3 / n} ≥
      1 - zeta := by
  classical
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let v : ℝ := 1 / (2 * n * L)
  have hv : 0 < v := by
    dsimp [v]
    positivity
  obtain ⟨N, hNsub, hNcover, hNcard⟩ :=
    Causalean.exists_internal_net_card_le E A hunit hv
  let H : Finset (X → ℝ) := N.image R
  have hHmeas : ∀ h ∈ H, Measurable h := by
    intro h hh
    simp only [H, Finset.mem_image] at hh
    obtain ⟨e, heN, rfl⟩ := hh
    exact hmeas e (hNsub e heN)
  have hH01 : ∀ h ∈ H, ∀ x, h x ∈ Set.Icc (0 : ℝ) 1 := by
    intro h hh
    simp only [H, Finset.mem_image] at hh
    obtain ⟨e, heN, rfl⟩ := hh
    exact h01 e (hNsub e heN)
  have hfinite := finite_relative_comparison_core
    S H hHmeas hH01 n hn zeta hzeta
  let base : ℝ := 1 + 4 * n * L
  have hbase : 1 ≤ base := by
    dsimp [base]
    have : 0 ≤ (n : ℝ) * L :=
      mul_nonneg (Nat.cast_nonneg _) hL.le
    nlinarith
  have hHne : H.Nonempty := by
    obtain ⟨e, heA⟩ := hAne
    obtain ⟨q, hqN, _⟩ := hNcover e heA
    exact ⟨R q, by
      simpa only [H] using Finset.mem_image.mpr ⟨q, hqN, rfl⟩⟩
  have hHcardpos : 0 < H.card := Finset.card_pos.mpr hHne
  have hHcard :
      (H.card : ℝ) ≤ base ^ D := by
    have himage : H.card ≤ N.card := by
      simpa only [H] using (Finset.card_image_le (s := N) (f := R))
    have himageR : (H.card : ℝ) ≤ N.card := by exact_mod_cast himage
    have hvbase : 1 + 2 / v = base := by
      dsimp [v, base]
      field_simp
      ring
    calc
      (H.card : ℝ) ≤ N.card := himageR
      _ ≤ (1 + 2 / v) ^ finrank ℝ E := hNcard
      _ = base ^ finrank ℝ E := by rw [hvbase]
      _ ≤ base ^ D := pow_le_pow_right₀ hbase hdim
  have hlog :
      Real.log (2 * (H.card : ℝ) / zeta) ≤
        Real.log (2 / zeta) + D * Real.log base := by
    have hleft : 0 < 2 * (H.card : ℝ) / zeta := by positivity
    have hright : 0 < 2 * (base ^ D) / zeta := by positivity
    have harg :
        2 * (H.card : ℝ) / zeta ≤ 2 * (base ^ D) / zeta := by
      gcongr
    calc
      Real.log (2 * (H.card : ℝ) / zeta) ≤
          Real.log (2 * (base ^ D) / zeta) :=
        Real.strictMonoOn_log.monotoneOn hleft hright harg
      _ = Real.log (2 / zeta) + D * Real.log base := by
        rw [Real.log_div (by positivity) hzeta.ne',
          Real.log_mul (by norm_num) (by positivity),
          Real.log_pow,
          Real.log_div (by norm_num) hzeta.ne']
        ring
  apply hfinite.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω e heA
  obtain ⟨q, hqN, heq⟩ := hNcover e heA
  have hqA := hNsub q hqN
  have hqH : R q ∈ H := by
    simpa only [H] using Finset.mem_image.mpr ⟨q, hqN, rfl⟩
  have hpoint (x : X) :
      |R e x - R q x| ≤ 1 / (2 * n) := by
    calc
      |R e x - R q x| ≤ L * ‖e - q‖ := hLip e heA q hqA x
      _ ≤ L * v := mul_le_mul_of_nonneg_left heq hL.le
      _ = 1 / (2 * n) := by
        dsimp [v]
        field_simp
  have hpop :
      |(∫ x, R e x ∂P) - ∫ x, R q x ∂P| ≤ 1 / (2 * n) :=
    integral_sub_le_of_pointwise
      (hmeas e heA) (hmeas q hqA) (h01 e heA) (h01 q hqA) hpoint
  have hemp :
      |S.sampleMean (R e) n ω - S.sampleMean (R q) n ω| ≤ 1 / (2 * n) :=
    sampleMean_sub_le_of_pointwise S hpoint n hn ω
  have htrans := relative_comparison_transfer hpop hemp
    (hω (R q) hqH).1 (hω (R q) hqH).2
  have hrem :
      relativeLogRemainder n H.card zeta + 3 * (1 / (2 * n)) ≤
        8 / (3 * n) *
          (Real.log (2 / zeta) + D * Real.log (1 + 4 * n * L)) +
          3 / n := by
    unfold relativeLogRemainder
    rw [show base = 1 + 4 * n * L from rfl] at hlog
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfac : 0 ≤ 8 / (3 * (n : ℝ)) := by positivity
    have hlogmul := mul_le_mul_of_nonneg_left hlog hfac
    have hslack :
        3 * (1 / (2 * (n : ℝ))) ≤ 3 / (n : ℝ) := by
      have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnR
      rw [show 1 / (2 * (n : ℝ)) = (n : ℝ)⁻¹ / 2 by
        field_simp]
      rw [show 3 / (n : ℝ) = 3 * (n : ℝ)⁻¹ by
        rw [div_eq_mul_inv]]
      nlinarith
    exact add_le_add hlogmul hslack
  exact ⟨htrans.1.trans (by linarith), htrans.2.trans (by linarith)⟩

/-- Product-measure form of
`uniform_relative_comparison_of_finiteDimensional`, with empirical means
written as sums over `Fin n`. -/
theorem uniform_relative_comparison_pi
    [Fintype X] [MeasurableSingletonClass X]
    (P : Measure X) (hP : IsProbabilityMeasure P)
    (A : Set E) (hAne : A.Nonempty)
    (hunit : ∀ e ∈ A, ‖e‖ ≤ 1)
    (R : E → X → ℝ)
    (hmeas : ∀ e ∈ A, Measurable (R e))
    (h01 : ∀ e ∈ A, ∀ x, R e x ∈ Set.Icc (0 : ℝ) 1)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ e ∈ A, ∀ e' ∈ A, ∀ x,
      |R e x - R e' x| ≤ L * ‖e - e'‖)
    (D n : ℕ) (hdim : finrank ℝ E ≤ D) (hn : 0 < n)
    (zeta : ℝ) (hzeta : 0 < zeta) :
    (Measure.pi (fun _ : Fin n => P)).real
      {sample | ∀ e ∈ A,
        (∫ x, R e x ∂P) ≤
            2 * ((n : ℝ)⁻¹ * ∑ i, R e (sample i)) +
              8 / (3 * n) *
                (Real.log (2 / zeta) +
                  D * Real.log (1 + 4 * n * L)) + 3 / n ∧
        ((n : ℝ)⁻¹ * ∑ i, R e (sample i)) ≤
            2 * (∫ x, R e x ∂P) +
              8 / (3 * n) *
                (Real.log (2 / zeta) +
                  D * Real.log (1 + 4 * n * L)) + 3 / n} ≥
      1 - zeta := by
  classical
  letI : IsProbabilityMeasure P := hP
  let ν : Measure (ℕ → X) := Measure.infinitePi (fun _ : ℕ => P)
  let S : Causalean.Stat.IIDSample (ℕ → X) X ν P :=
    Causalean.Stat.iidSample_infinitePi P
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  letI : IsProbabilityMeasure ν := hν
  have hu := uniform_relative_comparison_of_finiteDimensional
    S A hAne hunit R hmeas h01 L hL hLip D n hdim hn zeta hzeta
  let Ψ : (ℕ → X) → (Fin n → X) := fun ω i => S.Z i ω
  let T : Set (Fin n → X) :=
    {sample | ∀ e ∈ A,
      (∫ x, R e x ∂P) ≤
          2 * ((n : ℝ)⁻¹ * ∑ i, R e (sample i)) +
            8 / (3 * n) *
              (Real.log (2 / zeta) +
                D * Real.log (1 + 4 * n * L)) + 3 / n ∧
      ((n : ℝ)⁻¹ * ∑ i, R e (sample i)) ≤
          2 * (∫ x, R e x ∂P) +
            8 / (3 * n) *
              (Real.log (2 / zeta) +
                D * Real.log (1 + 4 * n * L)) + 3 / n}
  have hT : MeasurableSet T := Set.toFinite T |>.measurableSet
  have hΨ : Measurable Ψ :=
    Causalean.Stat.iidSample_finN_measurable S n
  have hpush :
      Measure.map Ψ ν = Measure.pi (fun _ : Fin n => P) := by
    exact Causalean.Stat.iidSample_finN_pushforward S n
  have hpre :
      Ψ ⁻¹' T =
        {ω | ∀ e ∈ A,
          (∫ x, R e x ∂P) ≤
              2 * S.sampleMean (R e) n ω +
                8 / (3 * n) *
                  (Real.log (2 / zeta) +
                    D * Real.log (1 + 4 * n * L)) + 3 / n ∧
          S.sampleMean (R e) n ω ≤
              2 * (∫ x, R e x ∂P) +
                8 / (3 * n) *
                  (Real.log (2 / zeta) +
                    D * Real.log (1 + 4 * n * L)) + 3 / n} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, T]
    have hmean (e : E) :
        (n : ℝ)⁻¹ * ∑ i : Fin n, R e (Ψ ω i) =
          S.sampleMean (R e) n ω := by
      unfold Causalean.Stat.IIDSample.sampleMean
      congr 1
      simpa [Ψ] using
        (Fin.sum_univ_eq_sum_range (fun i => R e (S.Z i ω)) n)
    simp_rw [hmean]
  have hmeasure :
      (Measure.pi (fun _ : Fin n => P)).real T =
        ν.real (Ψ ⁻¹' T) := by
    change (Measure.pi (fun _ : Fin n => P) T).toReal =
      (ν (Ψ ⁻¹' T)).toReal
    congr 1
    rw [← hpush, Measure.map_apply hΨ hT]
  change (Measure.pi (fun _ : Fin n => P)).real T ≥ 1 - zeta
  rw [hmeasure, hpre]
  exact hu

end CausalSmith.Substrate
