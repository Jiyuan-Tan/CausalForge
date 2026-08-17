import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialKL
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialAssembly
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# One-point KL bound for the angular radial construction

This module supplies the paper-local common-radius kernel representation and
the quantitative exceptional-radius estimate used by the angular packing.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The success-weighted radius measure associated with a score law and a
Bernoulli regression. -/
-- @node: radialSuccessMeasure
noncomputable def radialSuccessMeasure
    (nu : Measure Score) (p : Score → ℝ) (center : Score) : Measure ℝ :=
  Measure.map (fun x : Score => dist x center)
    (nu.withDensity fun x => ENNReal.ofReal (p x))

/-- The measurable radial Bernoulli parameter obtained as the density of the
success-weighted radius measure with respect to the radius marginal. -/
-- @node: radialSuccessParameter
noncomputable def radialSuccessParameter
    (nu : Measure Score) (p : Score → ℝ) (center : Score) : ℝ → ℝ :=
  fun r => ((radialSuccessMeasure nu p center).rnDeriv
    (Measure.map (fun x : Score => dist x center) nu) r).toReal

/-- The success-weighted radius measure is absolutely continuous with respect
to the radius marginal whenever the regression is at most one. -/
-- @node: radialSuccessMeasure_absolutelyContinuous
lemma radialSuccessMeasure_absolutelyContinuous
    (nu : Measure Score) [IsFiniteMeasure nu] (p : Score → ℝ)
    (hp : Measurable p) (hp1 : ∀ x, p x ≤ 1) (center : Score) :
    radialSuccessMeasure nu p center ≪
      Measure.map (fun x : Score => dist x center) nu := by
  apply Measure.absolutelyContinuous_of_le
  apply Measure.map_mono
  · calc
      nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤
          nu.withDensity 1 := by
        apply withDensity_mono
        filter_upwards with x
        simpa using ENNReal.ofReal_le_one.mpr (hp1 x)
      _ = nu := withDensity_one
  · fun_prop

/-- Integrating the radial success parameter over a measurable radial set
recovers the success-weighted score integral on its preimage. -/
-- @node: radialSuccessParameter_setIntegral
lemma radialSuccessParameter_setIntegral
    (nu : Measure Score) [IsFiniteMeasure nu] (p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (center : Score) (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ r in A, radialSuccessParameter nu p center r
        ∂(Measure.map (fun x : Score => dist x center) nu)) =
      ∫ x in {x | dist x center ∈ A}, p x ∂nu := by
  let rho : Score → ℝ := fun x => dist x center
  let m : Measure ℝ := Measure.map rho nu
  let s : Measure ℝ := radialSuccessMeasure nu p center
  have hle : s ≤ m := by
    dsimp [s, m, rho]
    apply Measure.map_mono
    · calc
        nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤
            nu.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (hp1 x)
        _ = nu := withDensity_one
    · fun_prop
  have hac : s ≪ m := Measure.absolutelyContinuous_of_le hle
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu rho
  letI : IsFiniteMeasure s := isFiniteMeasure_of_le m hle
  have hleft := Measure.setIntegral_toReal_rnDeriv hac A
  have hsA : s A = ENNReal.ofReal (∫ x in {x | rho x ∈ A}, p x ∂nu) := by
    change (Measure.map rho
      (nu.withDensity fun x => ENNReal.ofReal (p x))) A = _
    rw [Measure.map_apply (by fun_prop) hA,
      withDensity_apply _ (hA.preimage (by fun_prop))]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rfl
    · apply Measure.integrableOn_of_bounded (measure_ne_top _ _)
        hp.aestronglyMeasurable
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 x)]
      exact hp1 x
    · exact Filter.Eventually.of_forall hp0
  change (∫ r in A, ((s.rnDeriv m) r).toReal ∂m) = _
  rw [hleft]
  rw [Measure.real_def, hsA, ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => hp0 x)

/-- A scorewise middle-half bound passes to the Radon--Nikodym radial success
parameter. -/
-- @node: radialSuccessParameter_mem_Icc_ae
lemma radialSuccessParameter_mem_Icc_ae
    (nu : Measure Score) [IsFiniteMeasure nu] (p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 1 / 4 ≤ p x)
    (hp1 : ∀ x, p x ≤ 3 / 4) (center : Score) :
    ∀ᵐ r ∂(Measure.map (fun x : Score => dist x center) nu),
      radialSuccessParameter nu p center r ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  let rho : Score → ℝ := fun x => dist x center
  let m : Measure ℝ := Measure.map rho nu
  let g : ℝ → ℝ := radialSuccessParameter nu p center
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu rho
  let s : Measure ℝ := radialSuccessMeasure nu p center
  have hsle : s ≤ m := by
    dsimp [s, m, rho]
    apply Measure.map_mono
    · calc
        nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤
            nu.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (by linarith [hp1 x])
        _ = nu := withDensity_one
    · fun_prop
  letI : IsFiniteMeasure s := isFiniteMeasure_of_le m hsle
  have hg : Integrable g m := by
    dsimp [g, radialSuccessParameter, m, rho]
    exact Measure.integrable_toReal_rnDeriv
  have hcLo : Integrable (fun _ : ℝ => (1 / 4 : ℝ)) m := integrable_const _
  have hcHi : Integrable (fun _ : ℝ => (3 / 4 : ℝ)) m := integrable_const _
  have hlo : (fun _ : ℝ => (1 / 4 : ℝ)) ≤ᵐ[m] g := by
    apply ae_le_of_forall_setIntegral_le hcLo hg
    intro A hA _
    rw [radialSuccessParameter_setIntegral nu p hp
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) center A hA]
    rw [integral_const]
    change (m.restrict A).real Set.univ * (1 / 4 : ℝ) ≤ _
    rw [Measure.real_def, Measure.restrict_apply_univ]
    have hmap : m A = nu {x | rho x ∈ A} := by
      rw [Measure.map_apply (by fun_prop) hA]
      rfl
    rw [hmap]
    have hmono : (∫ x in {x | rho x ∈ A}, (1 / 4 : ℝ) ∂nu) ≤
        ∫ x in {x | rho x ∈ A}, p x ∂nu := by
      apply integral_mono_ae
      · exact integrableOn_const
      · apply Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
          hp.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hp0 x], by linarith [hp1 x]⟩
      · exact ae_restrict_of_forall_mem (hA.preimage (by fun_prop))
          (fun x _ => hp0 x)
    simpa [Measure.real_def] using hmono
  have hhi : g ≤ᵐ[m] (fun _ : ℝ => (3 / 4 : ℝ)) := by
    apply ae_le_of_forall_setIntegral_le hg hcHi
    intro A hA _
    rw [radialSuccessParameter_setIntegral nu p hp
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) center A hA]
    rw [integral_const]
    change _ ≤ (m.restrict A).real Set.univ * (3 / 4 : ℝ)
    rw [Measure.real_def, Measure.restrict_apply_univ]
    have hmap : m A = nu {x | rho x ∈ A} := by
      rw [Measure.map_apply (by fun_prop) hA]
      rfl
    rw [hmap]
    have hmono : (∫ x in {x | rho x ∈ A}, p x ∂nu) ≤
        ∫ x in {x | rho x ∈ A}, (3 / 4 : ℝ) ∂nu := by
      apply integral_mono_ae
      · apply Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
          hp.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hp0 x], by linarith [hp1 x]⟩
      · exact integrableOn_const
      · exact ae_restrict_of_forall_mem (hA.preimage (by fun_prop))
          (fun x _ => hp1 x)
    simpa [Measure.real_def] using hmono
  filter_upwards [hlo, hhi] with r hr0 hr1
  exact ⟨hr0, hr1⟩

/-- A globally clipped version of the radial success parameter.  Clipping is
silent almost everywhere under the radius marginal but makes the associated
Bernoulli--Gaussian kernel a Markov kernel without exceptional values. -/
-- @node: clippedRadialSuccessParameter
noncomputable def clippedRadialSuccessParameter
    (nu : Measure Score) (p : Score → ℝ) (center : Score) : ℝ → ℝ :=
  fun r => max (1 / 4 : ℝ) (min (3 / 4 : ℝ)
    (radialSuccessParameter nu p center r))

-- @node: clippedRadialSuccessParameter_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma clippedRadialSuccessParameter_measurable
    (nu : Measure Score) (p : Score → ℝ) (center : Score) :
    Measurable (clippedRadialSuccessParameter nu p center) := by
  unfold clippedRadialSuccessParameter radialSuccessParameter
  fun_prop

-- @node: clippedRadialSuccessParameter_mem_Icc
/-- The clipped success parameter lies in the displayed closed interval. -/
lemma clippedRadialSuccessParameter_mem_Icc
    (nu : Measure Score) (p : Score → ℝ) (center : Score) (r : ℝ) :
    clippedRadialSuccessParameter nu p center r ∈
      Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  unfold clippedRadialSuccessParameter
  constructor <;> simp <;> norm_num

-- @node: clippedRadialSuccessParameter_ae_eq
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma clippedRadialSuccessParameter_ae_eq
    (nu : Measure Score) [IsFiniteMeasure nu] (p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 1 / 4 ≤ p x)
    (hp1 : ∀ x, p x ≤ 3 / 4) (center : Score) :
    clippedRadialSuccessParameter nu p center =ᵐ[
      Measure.map (fun x : Score => dist x center) nu]
        radialSuccessParameter nu p center := by
  filter_upwards [radialSuccessParameter_mem_Icc_ae nu p hp hp0 hp1 center]
    with r hr
  unfold clippedRadialSuccessParameter
  rw [min_eq_right hr.2, max_eq_right hr.1]

/-- The Bernoulli--Gaussian kernel over an arbitrary measurable base type. -/
-- @node: bernoulliGaussianKernelOn
noncomputable def bernoulliGaussianKernelOn
    {A : Type*} [MeasurableSpace A] (p : A → ℝ) (hp : Measurable p) :
    Kernel A ℝ where
  toFun x := bernoulliGaussianLaw (p x)
  measurable' := by
    unfold bernoulliGaussianLaw Causalean.Mathlib.Probability.bernoulliLaw
    fun_prop

-- @node: bernoulliGaussianKernelOn_isMarkovKernel
/-- The stated conditional distribution is a Markov kernel: it is a probability law at each input and varies measurably with that input. -/
lemma bernoulliGaussianKernelOn_isMarkovKernel
    {A : Type*} [MeasurableSpace A] (p : A → ℝ) (hp : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    IsMarkovKernel (bernoulliGaussianKernelOn p hp) := by
  constructor
  intro x
  exact bernoulliGaussianLaw_isProbabilityMeasure (h0 x) (h1 x)

/-- Two Bernoulli--Gaussian mixtures over possibly different base spaces have
the same outcome mass when the base masses and integrated success parameters
agree. -/
-- @node: bernoulliGaussianKernel_setLIntegral_eq_of_mass_and_mean_general
lemma bernoulliGaussianKernel_setLIntegral_eq_of_mass_and_mean_general
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (nu : Measure A) [IsFiniteMeasure nu]
    (nu' : Measure B) [IsFiniteMeasure nu']
    (p : A → ℝ) (p' : B → ℝ) (hp : Measurable p) (hp' : Measurable p')
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hp0' : ∀ x, 0 ≤ p' x) (hp1' : ∀ x, p' x ≤ 1)
    {D : Set A} {D' : Set B} (hmass : nu D = nu' D')
    (hmean : ∫ x in D, p x ∂nu = ∫ x in D', p' x ∂nu')
    (E : Set ℝ) :
    (∫⁻ x in D, bernoulliGaussianKernelOn p hp x E ∂nu) =
      ∫⁻ x in D', bernoulliGaussianKernelOn p' hp' x E ∂nu' := by
  have hpInt : IntegrableOn p D nu := by
    apply Measure.integrableOn_of_bounded (M := 1) (measure_ne_top nu D)
      hp.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hp0 x)]
    exact hp1 x
  have hpInt' : IntegrableOn p' D' nu' := by
    apply Measure.integrableOn_of_bounded (M := 1) (measure_ne_top nu' D')
      hp'.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hp0' x)]
    exact hp1' x
  have hqInt : IntegrableOn (fun x => 1 - p x) D nu :=
    (integrableOn_const (s := D) (C := (1 : ℝ))).sub hpInt
  have hqInt' : IntegrableOn (fun x => 1 - p' x) D' nu' :=
    (integrableOn_const (s := D') (C := (1 : ℝ))).sub hpInt'
  have hpL : (∫⁻ x in D, ENNReal.ofReal (p x) ∂nu) =
      ∫⁻ x in D', ENNReal.ofReal (p' x) ∂nu' := by
    rw [← ofReal_integral_eq_lintegral_ofReal hpInt
      (Filter.Eventually.of_forall hp0),
      ← ofReal_integral_eq_lintegral_ofReal hpInt'
        (Filter.Eventually.of_forall hp0'), hmean]
  have hqmean : ∫ x in D, (1 - p x) ∂nu =
      ∫ x in D', (1 - p' x) ∂nu' := by
    rw [integral_sub (integrableOn_const (s := D) (C := (1 : ℝ))) hpInt,
      integral_sub (integrableOn_const (s := D') (C := (1 : ℝ))) hpInt']
    simp only [integral_const, Measure.real_def]
    rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, hmass, hmean]
  have hqL : (∫⁻ x in D, ENNReal.ofReal (1 - p x) ∂nu) =
      ∫⁻ x in D', ENNReal.ofReal (1 - p' x) ∂nu' := by
    rw [← ofReal_integral_eq_lintegral_ofReal hqInt
      (Filter.Eventually.of_forall fun x => sub_nonneg.mpr (hp1 x)),
      ← ofReal_integral_eq_lintegral_ofReal hqInt'
        (Filter.Eventually.of_forall fun x => sub_nonneg.mpr (hp1' x)), hqmean]
  simp only [bernoulliGaussianKernelOn, Kernel.coe_mk,
    bernoulliGaussianLaw_eq_gaussian_mixture, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  change (∫⁻ x, ENNReal.ofReal (p x) * (gaussianReal 1 1) E +
      ENNReal.ofReal (1 - p x) * (gaussianReal 0 1) E ∂(nu.restrict D)) =
    ∫⁻ x, ENNReal.ofReal (p' x) * (gaussianReal 1 1) E +
      ENNReal.ofReal (1 - p' x) * (gaussianReal 0 1) E ∂(nu'.restrict D')
  rw [lintegral_add_left (by fun_prop) _, lintegral_add_left (by fun_prop) _]
  simp_rw [mul_comm (ENNReal.ofReal (p _)), mul_comm (ENNReal.ofReal (1 - p _)),
    mul_comm (ENNReal.ofReal (p' _)), mul_comm (ENNReal.ofReal (1 - p' _))]
  have hmulP : (∫⁻ x in D, (gaussianReal 1 1) E * ENNReal.ofReal (p x) ∂nu) =
      (gaussianReal 1 1) E * ∫⁻ x in D, ENNReal.ofReal (p x) ∂nu := by
    exact lintegral_const_mul _ (by fun_prop)
  have hmulQ : (∫⁻ x in D, (gaussianReal 0 1) E * ENNReal.ofReal (1 - p x) ∂nu) =
      (gaussianReal 0 1) E * ∫⁻ x in D, ENNReal.ofReal (1 - p x) ∂nu := by
    exact lintegral_const_mul _ (by fun_prop)
  have hmulP' : (∫⁻ x in D', (gaussianReal 1 1) E * ENNReal.ofReal (p' x) ∂nu') =
      (gaussianReal 1 1) E * ∫⁻ x in D', ENNReal.ofReal (p' x) ∂nu' := by
    exact lintegral_const_mul _ (by fun_prop)
  have hmulQ' : (∫⁻ x in D', (gaussianReal 0 1) E * ENNReal.ofReal (1 - p' x) ∂nu') =
      (gaussianReal 0 1) E * ∫⁻ x in D', ENNReal.ofReal (1 - p' x) ∂nu' := by
    exact lintegral_const_mul _ (by fun_prop)
  rw [hmulP, hmulQ, hmulP', hmulQ', hpL, hqL]

/-- After forgetting score direction, a Bernoulli--Gaussian score mixture is a
composition product over the radius marginal with the clipped radial success
parameter, followed by swapping radius and outcome coordinates. -/
-- @node: radialOutcomeLaw_eq_map_swap_compProd
lemma radialOutcomeLaw_eq_map_swap_compProd
    (nu : Measure Score) [IsFiniteMeasure nu] (p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 1 / 4 ≤ p x)
    (hp1 : ∀ x, p x ≤ 3 / 4) (center : Score) :
    Measure.map (fun z : Score × ℝ => (z.2, dist z.1 center))
        (Measure.compProd nu (bernoulliGaussianKernel p hp)) =
      Measure.map Prod.swap
        (Measure.compProd (Measure.map (fun x : Score => dist x center) nu)
          (bernoulliGaussianKernelOn
            (clippedRadialSuccessParameter nu p center)
            (clippedRadialSuccessParameter_measurable nu p center))) := by
  let rho : Score → ℝ := fun x => dist x center
  let m : Measure ℝ := Measure.map rho nu
  let g : ℝ → ℝ := clippedRadialSuccessParameter nu p center
  let hg : Measurable g := clippedRadialSuccessParameter_measurable nu p center
  letI : IsMarkovKernel
      (bernoulliGaussianKernel p hp) :=
    bernoulliGaussianKernel_isMarkovKernel p hp
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x])
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu rho
  letI : IsMarkovKernel (bernoulliGaussianKernelOn g hg) :=
    bernoulliGaussianKernelOn_isMarkovKernel g hg
      (fun r => by
        dsimp [g]
        exact (by linarith [
          (clippedRadialSuccessParameter_mem_Icc nu p center r).1]))
      (fun r => by
        dsimp [g]
        exact (by linarith [
          (clippedRadialSuccessParameter_mem_Icc nu p center r).2]))
  apply Measure.ext_prod
  intro A B hA hB
  rw [map_radiusOutcome_compProd_apply_prod nu
    (bernoulliGaussianKernel p hp) center hA hB]
  have hright : (Measure.map Prod.swap
      (Measure.compProd m (bernoulliGaussianKernelOn g hg))) (A ×ˢ B) =
      ∫⁻ r in B, bernoulliGaussianKernelOn g hg r A ∂m := by
    rw [Measure.map_apply measurable_swap (hA.prod hB), Measure.compProd_apply]
    · rw [← lintegral_indicator hB]
      congr 1
      funext r
      by_cases hr : r ∈ B
      · simp [hr]
      · simp [hr]
    · exact (hA.prod hB).preimage measurable_swap
  rw [hright]
  apply bernoulliGaussianKernel_setLIntegral_eq_of_mass_and_mean_general
    (D := {x | rho x ∈ B}) (D' := B) nu m p g hp hg
    (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x])
    (fun r => by
      dsimp [g]
      linarith [(clippedRadialSuccessParameter_mem_Icc nu p center r).1])
    (fun r => by
      dsimp [g]
      linarith [(clippedRadialSuccessParameter_mem_Icc nu p center r).2])
  · rw [Measure.map_apply (by fun_prop) hB]
    rfl
  · have heq := clippedRadialSuccessParameter_ae_eq nu p hp hp0 hp1 center
    rw [integral_congr_ae (ae_restrict_of_ae heq)]
    exact (radialSuccessParameter_setIntegral nu p hp
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x])
      center B hB).symm

/-- A setwise bound on success-weighted radial masses gives the corresponding
almost-everywhere bound on the two radial Bernoulli parameters. -/
-- @node: clippedRadialSuccessParameter_abs_sub_le_ae
lemma clippedRadialSuccessParameter_abs_sub_le_ae
    (nu nu' : Measure Score) [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (p p' : Score → ℝ) (hp : Measurable p) (hp' : Measurable p')
    (hp0 : ∀ x, 1 / 4 ≤ p x) (hp1 : ∀ x, p x ≤ 3 / 4)
    (hp0' : ∀ x, 1 / 4 ≤ p' x) (hp1' : ∀ x, p' x ≤ 3 / 4)
    (center : Score)
    (hmap : Measure.map (fun x : Score => dist x center) nu =
      Measure.map (fun x : Score => dist x center) nu')
    {D : ℝ} (hD : 0 ≤ D) {E : Set ℝ} (hE : MeasurableSet E)
    (hdiff : ∀ A : Set ℝ, MeasurableSet A →
      |(∫ x in {x | dist x center ∈ A}, p x ∂nu) -
        ∫ x in {x | dist x center ∈ A}, p' x ∂nu'| ≤
          D * (Measure.map (fun x : Score => dist x center) nu (A ∩ E)).toReal) :
    ∀ᵐ r ∂(Measure.map (fun x : Score => dist x center) nu),
      |clippedRadialSuccessParameter nu p center r -
        clippedRadialSuccessParameter nu' p' center r| ≤
          E.indicator (fun _ => D) r := by
  let rho : Score → ℝ := fun x => dist x center
  let m : Measure ℝ := Measure.map rho nu
  let g : ℝ → ℝ := radialSuccessParameter nu p center
  let g' : ℝ → ℝ := radialSuccessParameter nu' p' center
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu rho
  let s : Measure ℝ := radialSuccessMeasure nu p center
  let s' : Measure ℝ := radialSuccessMeasure nu' p' center
  have hsle : s ≤ m := by
    dsimp [s, m, rho]
    apply Measure.map_mono
    · calc
        nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤ nu.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (by linarith [hp1 x])
        _ = nu := withDensity_one
    · fun_prop
  have hs'le : s' ≤ m := by
    have hm' : Measure.map rho nu' = m := by simpa [m, rho] using hmap.symm
    rw [← hm']
    dsimp [s', rho]
    apply Measure.map_mono
    · calc
        nu'.withDensity (fun x => ENNReal.ofReal (p' x)) ≤ nu'.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (by linarith [hp1' x])
        _ = nu' := withDensity_one
    · fun_prop
  letI : IsFiniteMeasure s := isFiniteMeasure_of_le m hsle
  letI : IsFiniteMeasure s' := isFiniteMeasure_of_le m hs'le
  have hg : Integrable g m := by
    dsimp [g, radialSuccessParameter, m, rho]
    exact Measure.integrable_toReal_rnDeriv
  have hg' : Integrable g' m := by
    have hm' : Measure.map rho nu' = m := by simpa [m, rho] using hmap.symm
    rw [← hm']
    dsimp [g', radialSuccessParameter, rho]
    exact Measure.integrable_toReal_rnDeriv
  have hc : Integrable (E.indicator (fun _ : ℝ => D)) m :=
    (integrable_const _).indicator hE
  have hconst (A : Set ℝ) (hA : MeasurableSet A) :
      (∫ r in A, E.indicator (fun _ : ℝ => D) r ∂m) =
        D * (m (A ∩ E)).toReal := by
    rw [integral_indicator hE, integral_const]
    simp [Measure.real_def, Measure.restrict_apply, hA, hE, inter_comm, mul_comm]
  have hup : (fun r => g r - g' r) ≤ᵐ[m]
      E.indicator (fun _ => D) := by
    apply ae_le_of_forall_setIntegral_le (hg.sub hg') hc
    intro A hA _
    change (∫ r in A, g r - g' r ∂m) ≤ _
    rw [integral_sub hg.integrableOn hg'.integrableOn]
    rw [radialSuccessParameter_setIntegral nu p hp
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) center A hA]
    have hp'Int := radialSuccessParameter_setIntegral nu' p' hp'
      (fun x => by linarith [hp0' x]) (fun x => by linarith [hp1' x]) center A hA
    have hm' : Measure.map rho nu' = m := by simpa [m, rho] using hmap.symm
    change (∫ r in A, g' r ∂Measure.map rho nu') = _ at hp'Int
    rw [hm'] at hp'Int
    rw [hp'Int]
    rw [hconst A hA]
    have hh := (abs_le.mp (hdiff A hA)).2
    simpa [m, rho, mul_comm] using hh
  have hdown : (fun r => g' r - g r) ≤ᵐ[m]
      E.indicator (fun _ => D) := by
    apply ae_le_of_forall_setIntegral_le (hg'.sub hg) hc
    intro A hA _
    change (∫ r in A, g' r - g r ∂m) ≤ _
    rw [integral_sub hg'.integrableOn hg.integrableOn]
    have hp'Int := radialSuccessParameter_setIntegral nu' p' hp'
      (fun x => by linarith [hp0' x]) (fun x => by linarith [hp1' x]) center A hA
    have hm' : Measure.map rho nu' = m := by simpa [m, rho] using hmap.symm
    change (∫ r in A, g' r ∂Measure.map rho nu') = _ at hp'Int
    rw [hm'] at hp'Int
    rw [hp'Int]
    rw [radialSuccessParameter_setIntegral nu p hp
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) center A hA]
    rw [hconst A hA]
    have hh := (abs_le.mp (hdiff A hA)).1
    simpa [m, rho, mul_comm, sub_eq_add_neg] using hh
  have heq := clippedRadialSuccessParameter_ae_eq nu p hp hp0 hp1 center
  have heq' := clippedRadialSuccessParameter_ae_eq nu' p' hp' hp0' hp1' center
  rw [← hmap] at heq'
  filter_upwards [hup, hdown, heq, heq'] with r hrup hrdown hr hr'
  rw [hr, hr']
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The common-radius disintegration and a localized radial-parameter bound
give a one-observation KL estimate proportional to the exceptional radial
mass. -/
-- @node: radialOutcomeLaw_klDiv_le_of_localized_success_bound
lemma radialOutcomeLaw_klDiv_le_of_localized_success_bound
    (nu nu' : Measure Score) [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (p p' : Score → ℝ) (hp : Measurable p) (hp' : Measurable p')
    (hp0 : ∀ x, 1 / 4 ≤ p x) (hp1 : ∀ x, p x ≤ 3 / 4)
    (hp0' : ∀ x, 1 / 4 ≤ p' x) (hp1' : ∀ x, p' x ≤ 3 / 4)
    (center : Score)
    (hmap : Measure.map (fun x : Score => dist x center) nu =
      Measure.map (fun x : Score => dist x center) nu')
    {D : ℝ} (hD : 0 ≤ D) {E : Set ℝ} (hE : MeasurableSet E)
    (hdiff : ∀ A : Set ℝ, MeasurableSet A →
      |(∫ x in {x | dist x center ∈ A}, p x ∂nu) -
        ∫ x in {x | dist x center ∈ A}, p' x ∂nu'| ≤
          D * (Measure.map (fun x : Score => dist x center) nu (A ∩ E)).toReal) :
    InformationTheory.klDiv
        (Measure.map (fun z : Score × ℝ => (z.2, dist z.1 center))
          (Measure.compProd nu (bernoulliGaussianKernel p hp)))
        (Measure.map (fun z : Score × ℝ => (z.2, dist z.1 center))
          (Measure.compProd nu' (bernoulliGaussianKernel p' hp'))) ≤
      ENNReal.ofReal (4 * D ^ 2) *
        Measure.map (fun x : Score => dist x center) nu E := by
  let rho : Score → ℝ := fun x => dist x center
  let m : Measure ℝ := Measure.map rho nu
  let g : ℝ → ℝ := clippedRadialSuccessParameter nu p center
  let g' : ℝ → ℝ := clippedRadialSuccessParameter nu' p' center
  let hg : Measurable g := clippedRadialSuccessParameter_measurable nu p center
  let hg' : Measurable g' := clippedRadialSuccessParameter_measurable nu' p' center
  let k : Kernel ℝ ℝ := bernoulliGaussianKernelOn g hg
  let k' : Kernel ℝ ℝ := bernoulliGaussianKernelOn g' hg'
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu rho
  letI : IsMarkovKernel k := bernoulliGaussianKernelOn_isMarkovKernel g hg
    (fun r => by
      dsimp [g]
      linarith [(clippedRadialSuccessParameter_mem_Icc nu p center r).1])
    (fun r => by
      dsimp [g]
      linarith [(clippedRadialSuccessParameter_mem_Icc nu p center r).2])
  letI : IsMarkovKernel k' := bernoulliGaussianKernelOn_isMarkovKernel g' hg'
    (fun r => by
      dsimp [g']
      linarith [(clippedRadialSuccessParameter_mem_Icc nu' p' center r).1])
    (fun r => by
      dsimp [g']
      linarith [(clippedRadialSuccessParameter_mem_Icc nu' p' center r).2])
  rw [radialOutcomeLaw_eq_map_swap_compProd nu p hp hp0 hp1 center,
    radialOutcomeLaw_eq_map_swap_compProd nu' p' hp' hp0' hp1' center]
  have hm' : Measure.map rho nu' = m := by simpa [m, rho] using hmap.symm
  rw [show Measure.map (fun x : Score => dist x center) nu = m by rfl,
    show Measure.map (fun x : Score => dist x center) nu' = m by exact hm']
  rw [show (Prod.swap : ℝ × ℝ → ℝ × ℝ) =
    ⇑(MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) by rfl]
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
    (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding]
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac]
  · have hpar := clippedRadialSuccessParameter_abs_sub_le_ae nu nu' p p' hp hp'
      hp0 hp1 hp0' hp1' center hmap hD hE hdiff
    calc
      (∫⁻ r, InformationTheory.klDiv (k r) (k' r) ∂m) ≤
          ∫⁻ r, E.indicator (fun _ => ENNReal.ofReal (4 * D ^ 2)) r ∂m := by
        apply lintegral_mono_ae
        filter_upwards [hpar] with r hr
        have hk := bernoulliGaussianLaw_klDiv_le_four_sq_sub
          (clippedRadialSuccessParameter_mem_Icc nu p center r).1
          (clippedRadialSuccessParameter_mem_Icc nu p center r).2
          (clippedRadialSuccessParameter_mem_Icc nu' p' center r).1
          (clippedRadialSuccessParameter_mem_Icc nu' p' center r).2
        change InformationTheory.klDiv (k r) (k' r) ≤ _ at hk
        by_cases hrE : r ∈ E
        · rw [Set.indicator_of_mem hrE]
          exact hk.trans (ENNReal.ofReal_le_ofReal (by
            have habs : |g r - g' r| ≤ D := by simpa [hrE] using hr
            have hsq := (sq_le_sq₀ (abs_nonneg (g r - g' r)) hD).2 habs
            rw [← sq_abs (g r - g' r)]
            nlinarith))
        · rw [Set.indicator_of_notMem hrE]
          have hz : g r = g' r := by
            have : |g r - g' r| ≤ 0 := by simpa [hrE] using hr
            exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
          have hkk : k r = k' r := by
            ext A hA
            simp [k, k', bernoulliGaussianKernelOn, hz]
          rw [hkk, InformationTheory.klDiv_self]
      _ = ∫⁻ _r in E, ENNReal.ofReal (4 * D ^ 2) ∂m :=
        lintegral_indicator hE _
      _ = ENNReal.ofReal (4 * D ^ 2) * m E :=
        setLIntegral_const E (ENNReal.ofReal (4 * D ^ 2))
  · filter_upwards with r
    have hk := bernoulliGaussianLaw_klDiv_le_four_sq_sub
      (clippedRadialSuccessParameter_mem_Icc nu p center r).1
      (clippedRadialSuccessParameter_mem_Icc nu p center r).2
      (clippedRadialSuccessParameter_mem_Icc nu' p' center r).1
      (clippedRadialSuccessParameter_mem_Icc nu' p' center r).2
    have hfinite : InformationTheory.klDiv (k r) (k' r) ≠ ⊤ := by
      change InformationTheory.klDiv (k r) (k' r) ≤ _ at hk
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk
    exact (InformationTheory.klDiv_ne_top_iff.mp hfinite).1

end CausalSmith.Stat.BddUniformLogPenalty
