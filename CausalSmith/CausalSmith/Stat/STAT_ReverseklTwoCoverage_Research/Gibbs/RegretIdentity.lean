import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentityCore
import CausalSmith.Substrate.FiniteExponentialTiltCalculus

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators
open CausalSmith.Substrate.FiniteExponentialTiltCalculus

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

-- @node: gibbs_tilt_partition_one
lemma gibbs_tilt_partition_one
    (r g : 𝒳 → 𝒜 → ℝ) (x : 𝒳) :
    partition (gibbsFromPotential E r x)
        (fun a => E.eta * (g x a - r x a)) 1 =
      (∑ a, E.reference x a * Real.exp (E.eta * g x a)) /
        ∑ a, E.reference x a * Real.exp (E.eta * r x a) := by
  simp only [partition, gibbsFromPotential, one_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

-- @node: gibbs_tilt_at_one
lemma gibbs_tilt_at_one
    (r g : 𝒳 → 𝒜 → ℝ) (x : 𝒳) :
    CausalSmith.Substrate.FiniteExponentialTiltCalculus.tilt
        (gibbsFromPotential E r x)
        (fun a => E.eta * (g x a - r x a)) 1 =
      gibbsFromPotential E g x := by
  funext a
  rw [tilt, gibbs_tilt_partition_one E r g x]
  simp only [gibbsFromPotential, one_mul]
  have hZr :
      (∑ b, E.reference x b * Real.exp (E.eta * r x b)) ≠ 0 :=
    ne_of_gt (gibbsPotentialNormalizer_pos E r x)
  have hZg :
      (∑ b, E.reference x b * Real.exp (E.eta * g x b)) ≠ 0 :=
    ne_of_gt (gibbsPotentialNormalizer_pos E g x)
  field_simp [hZr, hZg]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

-- @node: gibbs_endpoint_remainder_eq_policyKL
lemma gibbs_endpoint_remainder_eq_policyKL
    (r g : 𝒳 → 𝒜 → ℝ) (x : 𝒳) :
    mean (gibbsFromPotential E r x)
          (fun a => E.eta * (g x a - r x a)) 1 -
        (Real.log
            (partition (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1) -
          Real.log
            (partition (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 0)) =
      policyKL (gibbsFromPotential E g) (gibbsFromPotential E r) x := by
  have hmass :
      ∑ a, gibbsFromPotential E r x a = 1 :=
    (gibbsFromPotential_isPolicy E r).2 x
  have hZr :
      (∑ a, E.reference x a * Real.exp (E.eta * r x a)) ≠ 0 :=
    ne_of_gt (gibbsPotentialNormalizer_pos E r x)
  have hZg :
      (∑ a, E.reference x a * Real.exp (E.eta * g x a)) ≠ 0 :=
    ne_of_gt (gibbsPotentialNormalizer_pos E g x)
  have hmean :
      (∑ a, gibbsFromPotential E g x a *
        (E.eta * (g x a - r x a))) =
      E.eta * ∑ a, gibbsFromPotential E g x a * (g x a - r x a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [mean_eq_sum_tilt, gibbs_tilt_at_one E r g x,
    gibbs_tilt_partition_one E r g x, partition_zero _ _ hmass,
    Real.log_div hZg hZr, Real.log_one,
    policyKL_gibbsPotentials_expansion E]
  rw [hmean]
  ring

-- @node: gibbs_regret_eq_weighted_endpoint_remainder
lemma gibbs_regret_eq_weighted_endpoint_remainder
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ) :
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) =
      E.eta⁻¹ * ∑ x, rho x *
        (mean (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1 -
          (Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1) -
            Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 0))) := by
  rw [welfareFromPotential_regret_eq_kl E]
  congr 2
  funext x
  rw [gibbs_endpoint_remainder_eq_policyKL E r g x]

-- @node: weighted_context_sqrt_le_sqrt
lemma weighted_context_sqrt_le_sqrt
    (rho q : 𝒳 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hq_nonneg : ∀ x, 0 ≤ q x) :
    ∑ x, rho x * Real.sqrt (q x) ≤
      Real.sqrt (∑ x, rho x * q x) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun x => Real.sqrt (rho x))
    (fun x => Real.sqrt (rho x) * Real.sqrt (q x))
  have hrho_sq : ∀ x, (Real.sqrt (rho x)) ^ 2 = rho x :=
    fun x => Real.sq_sqrt (hrho_nonneg x)
  have hq_sq : ∀ x, (Real.sqrt (q x)) ^ 2 = q x :=
    fun x => Real.sq_sqrt (hq_nonneg x)
  simp_rw [← mul_assoc, ← pow_two, hrho_sq, mul_pow, hrho_sq, hq_sq] at hcs
  simpa [hrho_mass, Real.sqrt_one, one_mul] using hcs

-- @node: gibbs_scaled_endpoint_remainder_le_pessimistic_linear
lemma gibbs_scaled_endpoint_remainder_le_pessimistic_linear
    (r g : 𝒳 → 𝒜 → ℝ) (x : 𝒳)
    (hpess : ∀ a, g x a - r x a ≤ 0) :
    E.eta⁻¹ *
        (mean (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1 -
          (Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1) -
            Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 0))) ≤
      ∑ a, gibbsFromPotential E r x a * (-(g x a - r x a)) := by
  let w := gibbsFromPotential E r x
  let h : 𝒜 → ℝ := fun a => E.eta * (g x a - r x a)
  have hw : ∀ a, 0 ≤ w a :=
    fun a => (gibbsFromPotential_isPolicy E r).1 x a
  have hmass : ∑ a, w a = 1 :=
    (gibbsFromPotential_isPolicy E r).2 x
  have hnonpos : ∀ a, h a ≤ 0 :=
    fun a => mul_nonpos_of_nonneg_of_nonpos E.eta_pos.le (hpess a)
  have hb :=
    endpointRemainder_le_neg_mean_zero_of_nonpos w h hw hmass hnonpos
  have hscaled := mul_le_mul_of_nonneg_left hb (inv_pos.mpr E.eta_pos).le
  rw [mean_zero w h hmass] at hscaled
  change E.eta⁻¹ *
      (mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤
    ∑ a, w a * (-(g x a - r x a))
  calc
    E.eta⁻¹ *
        (mean w h 1 -
          (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤
        E.eta⁻¹ * (-(∑ a, w a * h a)) := hscaled
    _ = _ := by
      simp only [h]
      have hsum :
          (∑ a, w a * (E.eta * (g x a - r x a))) =
            E.eta * ∑ a, w a * (g x a - r x a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      have hneg :
          (∑ a, w a * (-(g x a - r x a))) =
            -(∑ a, w a * (g x a - r x a)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [hsum, hneg]
      field_simp [ne_of_gt E.eta_pos]

-- @node: gibbs_scaled_endpoint_remainder_le_pessimistic_quadratic
lemma gibbs_scaled_endpoint_remainder_le_pessimistic_quadratic
    (r g : 𝒳 → 𝒜 → ℝ) (x : 𝒳)
    (hpess : ∀ a, g x a - r x a ≤ 0) :
    E.eta⁻¹ *
        (mean (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1 -
          (Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1) -
            Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 0))) ≤
      E.eta / 2 *
        ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2 := by
  let w := gibbsFromPotential E r x
  let h : 𝒜 → ℝ := fun a => E.eta * (g x a - r x a)
  have hw : ∀ a, 0 ≤ w a :=
    fun a => (gibbsFromPotential_isPolicy E r).1 x a
  have hmass : ∑ a, w a = 1 :=
    (gibbsFromPotential_isPolicy E r).2 x
  have hnonpos : ∀ a, h a ≤ 0 :=
    fun a => mul_nonpos_of_nonneg_of_nonpos E.eta_pos.le (hpess a)
  have hb :=
    endpointRemainder_le_half_secondMoment_zero_of_nonpos
      w h hw hmass hnonpos
  have hscaled := mul_le_mul_of_nonneg_left hb (inv_pos.mpr E.eta_pos).le
  rw [secondMoment_zero w h hmass] at hscaled
  change E.eta⁻¹ *
      (mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤
    E.eta / 2 * ∑ a, w a * (g x a - r x a) ^ 2
  calc
    E.eta⁻¹ *
        (mean w h 1 -
          (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤
        E.eta⁻¹ * ((2 : ℝ)⁻¹ * ∑ a, w a * (h a) ^ 2) := hscaled
    _ = _ := by
      simp only [h]
      have hsq :
          (∑ a, w a * (E.eta * (g x a - r x a)) ^ 2) =
            E.eta ^ 2 * ∑ a, w a * (g x a - r x a) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [hsq]
      field_simp [ne_of_gt E.eta_pos]

-- @node: lem:gibbs-pessimism-conversion
lemma gibbs_pessimism_conversion
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1)
    (hpess : ∀ x a, g x a - r x a ≤ 0) :
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤
      min
        (∑ x, rho x * ∑ a, gibbsFromPotential E r x a * (-(g x a - r x a)))
        (E.eta / 2 *
          ∑ x, rho x * ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2) := by
  rw [gibbs_regret_eq_weighted_endpoint_remainder E]
  apply le_min
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    calc
      E.eta⁻¹ * (rho x *
          (mean (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1 -
            (Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1) -
              Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 0)))) =
          rho x * (E.eta⁻¹ *
            (mean (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1 -
              (Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 1) -
                Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 0)))) := by ring
      _ ≤ rho x *
          ∑ a, gibbsFromPotential E r x a * (-(g x a - r x a)) :=
        mul_le_mul_of_nonneg_left
          (gibbs_scaled_endpoint_remainder_le_pessimistic_linear
            E r g x (hpess x)) (hrho_nonneg x)
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    calc
      E.eta⁻¹ * (rho x *
          (mean (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1 -
            (Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1) -
              Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 0)))) =
          rho x * (E.eta⁻¹ *
            (mean (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1 -
              (Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 1) -
                Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 0)))) := by ring
      _ ≤ rho x * (E.eta / 2 *
          ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (gibbs_scaled_endpoint_remainder_le_pessimistic_quadratic
            E r g x (hpess x)) (hrho_nonneg x)
      _ = E.eta / 2 *
          (rho x * ∑ a, gibbsFromPotential E r x a *
            (g x a - r x a) ^ 2) := by ring

/-- Temperature-dependent plug-in quadratic constant. -/
noncomputable def kappa (eta : ℝ) : ℝ :=
  eta * ∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t)
  -- @realizes \kappa_\eta(η∫_0^1 t exp(2ηt)dt)

-- @node: gibbs_scaled_endpoint_remainder_le_plugin_quadratic
lemma gibbs_scaled_endpoint_remainder_le_plugin_quadratic
    (r g : 𝒳 → 𝒜 → ℝ) (x : 𝒳)
    (hdelta : ∀ a, |g x a - r x a| ≤ 1) :
    E.eta⁻¹ *
        (mean (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1 -
          (Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1) -
            Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 0))) ≤
      kappa E.eta *
        ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2 := by
  let w := gibbsFromPotential E r x
  let delta : 𝒜 → ℝ := fun a => g x a - r x a
  have hw : ∀ a, 0 ≤ w a :=
    fun a => (gibbsFromPotential_isPolicy E r).1 x a
  have hmass : ∑ a, w a = 1 :=
    (gibbsFromPotential_isPolicy E r).2 x
  have hb := scaledEndpointRemainder_le_exact_expIntegral
    w delta E.eta hw hmass E.eta_pos hdelta
  simpa only [w, delta, kappa] using hb

-- @node: gibbs_scaled_endpoint_remainder_le_plugin_sqrt
lemma gibbs_scaled_endpoint_remainder_le_plugin_sqrt
    (r g : 𝒳 → 𝒜 → ℝ) (x : 𝒳)
    (hdelta : ∀ a, |g x a - r x a| ≤ 1) :
    E.eta⁻¹ *
        (mean (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1 -
          (Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1) -
            Real.log
              (partition (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 0))) ≤
      (1 + Real.exp E.eta) *
        Real.sqrt
          (∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2) := by
  let w := gibbsFromPotential E r x
  let h : 𝒜 → ℝ := fun a => E.eta * (g x a - r x a)
  have hw : ∀ a, 0 ≤ w a :=
    fun a => (gibbsFromPotential_isPolicy E r).1 x a
  have hmass : ∑ a, w a = 1 :=
    (gibbsFromPotential_isPolicy E r).2 x
  have hbound : ∀ a, |h a| ≤ E.eta := by
    intro a
    simp only [h, abs_mul, abs_of_pos E.eta_pos]
    exact (mul_le_mul_of_nonneg_left (hdelta a) E.eta_pos.le).trans_eq
      (mul_one E.eta)
  have hb :=
    endpointRemainder_le_one_add_exp_mul_sqrt
      w h E.eta hw hmass hbound
  have hscaled := mul_le_mul_of_nonneg_left hb (inv_pos.mpr E.eta_pos).le
  have hsm :
      secondMoment w h 0 =
        E.eta ^ 2 * ∑ a, w a * (g x a - r x a) ^ 2 := by
    rw [secondMoment_zero w h hmass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [h]
    ring
  change E.eta⁻¹ *
      (mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤
    (1 + Real.exp E.eta) *
      Real.sqrt (∑ a, w a * (g x a - r x a) ^ 2)
  calc
    E.eta⁻¹ *
        (mean w h 1 -
          (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤
      E.eta⁻¹ * ((1 + Real.exp E.eta) *
        Real.sqrt (secondMoment w h 0)) := hscaled
    _ = _ := by
      rw [hsm, Real.sqrt_mul (sq_nonneg E.eta),
        Real.sqrt_sq E.eta_pos.le]
      field_simp [ne_of_gt E.eta_pos]

-- @node: lem:gibbs-plugin-conversion
lemma gibbs_plugin_conversion
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1) :
    let DeltaSq :=
      ∑ x, rho x * ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤
      min (kappa E.eta * DeltaSq)
        ((1 + Real.exp (2 * E.eta)) * Real.sqrt DeltaSq) := by
  dsimp only
  have hdelta : ∀ x a, |g x a - r x a| ≤ 1 := by
    intro x a
    have hr0 : 0 ≤ r x a := (hr x a).1
    have hr1 : r x a ≤ 1 := (hr x a).2
    have hg0 : 0 ≤ g x a := (hg x a).1
    have hg1 : g x a ≤ 1 := (hg x a).2
    rw [abs_le]
    constructor
    · linarith
    · linarith
  rw [gibbs_regret_eq_weighted_endpoint_remainder E]
  apply le_min
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    calc
      E.eta⁻¹ * (rho x *
          (mean (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1 -
            (Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1) -
              Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 0)))) =
          rho x * (E.eta⁻¹ *
            (mean (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1 -
              (Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 1) -
                Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 0)))) := by ring
      _ ≤ rho x * (kappa E.eta *
          ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (gibbs_scaled_endpoint_remainder_le_plugin_quadratic
            E r g x (hdelta x)) (hrho_nonneg x)
      _ = kappa E.eta *
          (rho x * ∑ a, gibbsFromPotential E r x a *
            (g x a - r x a) ^ 2) := by ring
  · let q : 𝒳 → ℝ := fun x =>
      ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2
    have hq_nonneg : ∀ x, 0 ≤ q x := by
      intro x
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg ((gibbsFromPotential_isPolicy E r).1 x a)
          (sq_nonneg (g x a - r x a))
    have hlocal :
        E.eta⁻¹ * ∑ x, rho x *
            (mean (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1 -
              (Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 1) -
                Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 0))) ≤
          (1 + Real.exp E.eta) * ∑ x, rho x * Real.sqrt (q x) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      calc
        E.eta⁻¹ * (rho x *
            (mean (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1 -
              (Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 1) -
                Real.log
                  (partition (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 0)))) =
            rho x * (E.eta⁻¹ *
              (mean (gibbsFromPotential E r x)
                    (fun a => E.eta * (g x a - r x a)) 1 -
                (Real.log
                    (partition (gibbsFromPotential E r x)
                      (fun a => E.eta * (g x a - r x a)) 1) -
                  Real.log
                    (partition (gibbsFromPotential E r x)
                      (fun a => E.eta * (g x a - r x a)) 0)))) := by ring
        _ ≤ rho x * ((1 + Real.exp E.eta) * Real.sqrt (q x)) := by
          apply mul_le_mul_of_nonneg_left _ (hrho_nonneg x)
          simpa only [q] using
            gibbs_scaled_endpoint_remainder_le_plugin_sqrt
              E r g x (hdelta x)
        _ = (1 + Real.exp E.eta) * (rho x * Real.sqrt (q x)) := by ring
    calc
      E.eta⁻¹ * ∑ x, rho x *
          (mean (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1 -
            (Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1) -
              Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 0))) ≤
          (1 + Real.exp E.eta) * ∑ x, rho x * Real.sqrt (q x) := hlocal
      _ ≤ (1 + Real.exp E.eta) *
          Real.sqrt (∑ x, rho x * q x) :=
        mul_le_mul_of_nonneg_left
          (weighted_context_sqrt_le_sqrt rho q
            hrho_nonneg hrho_mass hq_nonneg)
          (by positivity)
      _ ≤ (1 + Real.exp (2 * E.eta)) *
          Real.sqrt (∑ x, rho x * q x) := by
        have hexp : Real.exp E.eta ≤ Real.exp (2 * E.eta) :=
          Real.exp_le_exp.mpr (by linarith [E.eta_pos])
        exact mul_le_mul_of_nonneg_right (by linarith)
          (Real.sqrt_nonneg _)
      _ = (1 + Real.exp (2 * E.eta)) *
          Real.sqrt
            (∑ x, rho x * ∑ a, gibbsFromPotential E r x a *
              (g x a - r x a) ^ 2) := by rfl

-- @node: lem:two-endpoint-gibbs-conversion
lemma two_endpoint_gibbs_conversion
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1) :
    let A :=
      ∑ x, rho x * ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2
    let B :=
      ∑ x, rho x * ∑ a, gibbsFromPotential E g x a * (g x a - r x a) ^ 2
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤
      min (E.eta * (A + B)) (Real.sqrt A + Real.sqrt B) := by
  dsimp only
  exact le_min
    (two_endpoint_gibbs_fast E rho r g hrho_nonneg)
    (two_endpoint_gibbs_slow E rho r g hrho_nonneg hrho_mass)

end CausalSmith.Stat.ReverseKLTwoCoverage
