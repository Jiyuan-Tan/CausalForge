import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Learner.PredictionPolytope
import CausalSmith.Substrate.UniformGibbsRadiusConcentration

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

/-- Paper-independent formula to which `gibbsRadius` is definitionally reduced. -/
noncomputable def substrateGibbsRadius
    (E : CommonExperiment d 𝒳 𝒜) (g f : 𝒳 → 𝒜 → ℝ) (x : 𝒳) : ℝ :=
  ∑ a,
    (E.reference x a * Real.exp (E.eta * g x a) /
      ∑ b, E.reference x b * Real.exp (E.eta * g x b)) *
      (g x a - f x a) ^ 2

/-- Explicit remainder furnished by the reusable uniform comparison theorem. -/
noncomputable def substrateGibbsRemainder
    (d n : ℕ) (eta zeta : ℝ) : ℝ :=
  8 / (3 * n) *
    (Real.log (2 / zeta) + 2 * d * Real.log (1 + 4 * n * (eta + 2))) + 3 / n

private def predictionLinearMap
    (E : CommonExperiment d 𝒳 𝒜) :
    (Fin d → ℝ) →ₗ[ℝ] ((𝒳 × 𝒜) → ℝ) where
  toFun θ w := ∑ i, E.feature w.1 w.2 i * θ i
  map_add' θ φ := by
    ext w
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c θ := by
    ext w
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RingHom.id_apply]
    ac_rfl

private abbrev GibbsPairSpace
    (E : CommonExperiment d 𝒳 𝒜) :=
  (CausalSmith.Substrate.pairDifferenceLinearMap
    (predictionLinearMap E)).range

private def boundedGibbsPairs
    (E : CommonExperiment d 𝒳 𝒜) : Set (GibbsPairSpace E) :=
  {z | ∀ w,
    z.1.1 w ∈ Set.Icc (0 : ℝ) 1 ∧
    |z.1.2 w| ≤ 1}

private def pairGibbsRadius
    (E : CommonExperiment d 𝒳 𝒜)
    (z : GibbsPairSpace E) (x : 𝒳) : ℝ :=
  CausalSmith.Substrate.finiteGibbsSquaredRadius
    (E.reference x) E.eta
    ((fun a => z.1.1 (x, a)), (fun a => z.1.2 (x, a)))

private lemma boundedGibbsPairs_nonempty
    (E : CommonExperiment d 𝒳 𝒜) :
    (boundedGibbsPairs E).Nonempty := by
  let z : GibbsPairSpace E :=
    ⟨0, ⟨(0, 0), by
      ext w <;> simp [CausalSmith.Substrate.pairDifferenceLinearMap]⟩⟩
  refine ⟨z, ?_⟩
  intro w
  simp [z]

private lemma boundedGibbsPairs_unit
    (E : CommonExperiment d 𝒳 𝒜) :
    ∀ z ∈ boundedGibbsPairs E, ‖z‖ ≤ 1 := by
  intro z hz
  change ‖z.1‖ ≤ 1
  rw [Prod.norm_def]
  apply max_le
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [(hz w).1.1], (hz w).1.2⟩
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    rw [Real.norm_eq_abs]
    exact (hz w).2

private lemma pairGibbsRadius_measurable
    (E : CommonExperiment d 𝒳 𝒜) :
    ∀ z ∈ boundedGibbsPairs E, Measurable (pairGibbsRadius E z) := by
  intro z hz
  exact measurable_of_finite _

private lemma pairGibbsRadius_mem_Icc
    (E : CommonExperiment d 𝒳 𝒜) :
    ∀ z ∈ boundedGibbsPairs E, ∀ x,
      pairGibbsRadius E z x ∈ Set.Icc (0 : ℝ) 1 := by
  intro z hz x
  exact CausalSmith.Substrate.finiteGibbsSquaredRadius_mem_Icc
    (E.reference x) E.eta
    ((fun a => z.1.1 (x, a)), (fun a => z.1.2 (x, a)))
    (E.reference_isPolicy.1 x) (E.reference_isPolicy.2 x)
    (fun a => (hz (x, a)).2)

private lemma restricted_pair_norm_le
    (E : CommonExperiment d 𝒳 𝒜)
    (x : 𝒳) (z z' : GibbsPairSpace E) :
    ‖((fun a => z.1.1 (x, a)), (fun a => z.1.2 (x, a))) -
      ((fun a => z'.1.1 (x, a)), (fun a => z'.1.2 (x, a)))‖ ≤
      ‖z - z'‖ := by
  change
    ‖((fun a => (z.1 - z'.1).1 (x, a)),
      (fun a => (z.1 - z'.1).2 (x, a)))‖ ≤ ‖z.1 - z'.1‖
  rw [Prod.norm_def]
  apply max_le
  · calc
      ‖fun a => (z.1 - z'.1).1 (x, a)‖ ≤ ‖(z.1 - z'.1).1‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
          (fun a => norm_le_pi_norm _ (x, a))
      _ ≤ ‖z.1 - z'.1‖ := norm_fst_le _
  · calc
      ‖fun a => (z.1 - z'.1).2 (x, a)‖ ≤ ‖(z.1 - z'.1).2‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
          (fun a => norm_le_pi_norm _ (x, a))
      _ ≤ ‖z.1 - z'.1‖ := norm_snd_le _

private lemma pairGibbsRadius_lipschitz
    (E : CommonExperiment d 𝒳 𝒜) :
    ∀ z ∈ boundedGibbsPairs E, ∀ z' ∈ boundedGibbsPairs E, ∀ x,
      |pairGibbsRadius E z x - pairGibbsRadius E z' x| ≤
        (E.eta + 2) * ‖z - z'‖ := by
  intro z hz z' hz' x
  have hlocal :=
    CausalSmith.Substrate.finiteGibbsSquaredRadius_lipschitz
      (E.reference x) E.eta
      (E.reference_isPolicy.1 x) (E.reference_isPolicy.2 x)
      E.eta_pos
      ((fun a => z.1.1 (x, a)), (fun a => z.1.2 (x, a)))
      ((fun a => z'.1.1 (x, a)), (fun a => z'.1.2 (x, a)))
      (fun a => ⟨(hz (x, a)).1, (hz (x, a)).2⟩)
      (fun a => ⟨(hz' (x, a)).1, (hz' (x, a)).2⟩)
  exact hlocal.trans
    (mul_le_mul_of_nonneg_left
      (restricted_pair_norm_le E x z z') (by linarith [E.eta_pos]))

private lemma pair_of_predictions
    (E : CommonExperiment d 𝒳 𝒜)
    (g f : 𝒳 → 𝒜 → ℝ)
    (hg : g ∈ predictionPolytope E)
    (hf : f ∈ predictionPolytope E) :
    ∃ z ∈ boundedGibbsPairs E,
      ∀ x, pairGibbsRadius E z x = substrateGibbsRadius E g f x := by
  rcases hg with ⟨hg01, θ, hθ⟩
  rcases hf with ⟨hf01, φ, hφ⟩
  let g' : (𝒳 × 𝒜) → ℝ := fun w => g w.1 w.2
  let f' : (𝒳 × 𝒜) → ℝ := fun w => f w.1 w.2
  have hg' : g' = predictionLinearMap E θ := by
    funext w
    exact hθ w.1 w.2
  have hf' : f' = predictionLinearMap E φ := by
    funext w
    exact hφ w.1 w.2
  let z : GibbsPairSpace E :=
    ⟨(g', g' - f'),
      CausalSmith.Substrate.pairDifference_mem_range
        (predictionLinearMap E) g' f' ⟨θ, hg'⟩ ⟨φ, hf'⟩⟩
  have hz : z ∈ boundedGibbsPairs E := by
    intro w
    constructor
    · exact hg01 w.1 w.2
    · change |g w.1 w.2 - f w.1 w.2| ≤ 1
      exact abs_le.2 ⟨by linarith [(hg01 w.1 w.2).1, (hf01 w.1 w.2).2],
        by linarith [(hg01 w.1 w.2).2, (hf01 w.1 w.2).1]⟩
  refine ⟨z, hz, ?_⟩
  intro x
  unfold pairGibbsRadius CausalSmith.Substrate.finiteGibbsSquaredRadius
    CausalSmith.Substrate.finiteGibbsDenominator substrateGibbsRadius
  change
    (∑ a, E.reference x a * Real.exp (E.eta * g x a) *
      (g x a - f x a) ^ 2) /
        (∑ a, E.reference x a * Real.exp (E.eta * g x a)) =
      ∑ a, (E.reference x a * Real.exp (E.eta * g x a) /
        ∑ b, E.reference x b * Real.exp (E.eta * g x b)) *
        (g x a - f x a) ^ 2
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Exact application of the reusable substrate to the paper's prediction
polytope and Gibbs-radius formula. -/
theorem substrate_uniform_gibbs_radius_comparison
    (E : CommonExperiment d 𝒳 𝒜)
    (rho : Measure 𝒳) (hrho : IsProbabilityMeasure rho)
    (zeta : ℝ) (hzeta : 0 < zeta) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => rho)).real
      {sample | ∀ g ∈ predictionPolytope E, ∀ f ∈ predictionPolytope E,
        (∫ x, substrateGibbsRadius E g f x ∂rho) ≤
            2 * ((n : ℝ)⁻¹ * ∑ i, substrateGibbsRadius E g f (sample i)) +
              substrateGibbsRemainder d n E.eta zeta ∧
        ((n : ℝ)⁻¹ * ∑ i, substrateGibbsRadius E g f (sample i)) ≤
            2 * (∫ x, substrateGibbsRadius E g f x ∂rho) +
              substrateGibbsRemainder d n E.eta zeta}
      ≥ 1 - zeta := by
  have hu :=
    CausalSmith.Substrate.uniform_relative_comparison_pi
      (E := GibbsPairSpace E)
      rho hrho (boundedGibbsPairs E)
      (boundedGibbsPairs_nonempty E)
      (boundedGibbsPairs_unit E)
      (pairGibbsRadius E)
      (pairGibbsRadius_measurable E)
      (pairGibbsRadius_mem_Icc E)
      (E.eta + 2) (by linarith [E.eta_pos])
      (pairGibbsRadius_lipschitz E)
      (2 * d) n
      (CausalSmith.Substrate.finrank_pairDifference_range_le_two_mul
        (predictionLinearMap E))
      hn zeta hzeta
  apply hu.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro sample hs g hg f hf
  obtain ⟨z, hz, hzgf⟩ := pair_of_predictions E g f hg hf
  have hzbound := hs z hz
  simpa [hzgf, substrateGibbsRemainder, add_assoc] using hzbound

end

end CausalSmith.Stat.ReverseKLTwoCoverage
