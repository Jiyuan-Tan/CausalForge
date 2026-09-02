/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.InformationTheory.KLBind
import Causalean.Mathlib.Probability.BernoulliMeasure
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Bernoulli disintegration over a common measurable statistic

This module constructs conditional Bernoulli success parameters by
Radon–Nikodym differentiation, identifies the associated composition-product
law, and bounds its KL divergence under localized parameter changes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Causalean.Mathlib.InformationTheory

/-- A Bernoulli parameter in the middle half of the unit interval has
variance between zero and one quarter, so adding unit noise gives variance
between one and five quarters. -/
theorem one_add_mul_one_sub_mem_Icc {p : ℝ}
    (hp : p ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    1 + p * (1 - p) ∈ Icc (1 : ℝ) (5 / 4 : ℝ) := by
  constructor
  · have hp0 : 0 ≤ p := by linarith [hp.1]
    have hp1 : p ≤ 1 := by linarith [hp.2]
    have hprod : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
    linarith
  · nlinarith [sq_nonneg (p - 1 / 2)]

/-- A measurable success-probability function determines the Markov kernel
that returns the corresponding real-valued Bernoulli law at each input. -/
-- @node: commonStatisticBernoulliKernel
noncomputable def commonStatisticBernoulliKernel
    {S : Type*} [MeasurableSpace S] (p : S → ℝ) (hp : Measurable p) :
    Kernel S ℝ where
  toFun r := Causalean.Mathlib.Probability.bernoulliLaw (p r)
  measurable' := by
    unfold Causalean.Mathlib.Probability.bernoulliLaw
    fun_prop

/-- Pointwise unit-interval parameters make the common-statistic Bernoulli
kernel Markov. -/
-- @node: commonStatisticBernoulliKernel_isMarkovKernel
lemma commonStatisticBernoulliKernel_isMarkovKernel
    {S : Type*} [MeasurableSpace S] (p : S → ℝ) (hp : Measurable p)
    (h0 : ∀ r, 0 ≤ p r) (h1 : ∀ r, p r ≤ 1) :
    IsMarkovKernel (commonStatisticBernoulliKernel p hp) := by
  constructor
  intro r
  exact Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
    (h0 r) (h1 r)

/-- A common statistic with conditionally Bernoulli outcomes has KL bounded
by the squared change in its success parameter, integrated only over the
statistic region where that parameter can change.  This is the generic
disintegration step used by the signed hard-cell comparison. -/
-- @node: commonStatisticBernoulli_klDiv_le_of_localized_parameter
lemma commonStatisticBernoulli_klDiv_le_of_localized_parameter
    (m : Measure ℝ) [IsFiniteMeasure m] (p q : ℝ → ℝ)
    (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ r, 1 / 4 ≤ p r) (hp1 : ∀ r, p r ≤ 3 / 4)
    (hq0 : ∀ r, 1 / 4 ≤ q r) (hq1 : ∀ r, q r ≤ 3 / 4)
    {D : ℝ} (hD : 0 ≤ D) {E : Set ℝ} (hE : MeasurableSet E)
    (hdiff : ∀ᵐ r ∂m, |p r - q r| ≤ E.indicator (fun _ => D) r) :
    InformationTheory.klDiv
        (Measure.compProd m (commonStatisticBernoulliKernel p hp))
        (Measure.compProd m (commonStatisticBernoulliKernel q hq)) ≤
      ENNReal.ofReal (4 * D ^ 2) * m E := by
  let k : Kernel ℝ ℝ := commonStatisticBernoulliKernel p hp
  let k' : Kernel ℝ ℝ := commonStatisticBernoulliKernel q hq
  letI : IsMarkovKernel k :=
    commonStatisticBernoulliKernel_isMarkovKernel p hp
      (fun r => by linarith [hp0 r]) (fun r => by linarith [hp1 r])
  letI : IsMarkovKernel k' :=
    commonStatisticBernoulliKernel_isMarkovKernel q hq
      (fun r => by linarith [hq0 r]) (fun r => by linarith [hq1 r])
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac]
  · calc
      (∫⁻ r, InformationTheory.klDiv (k r) (k' r) ∂m) ≤
          ∫⁻ r, E.indicator (fun _ => ENNReal.ofReal (4 * D ^ 2)) r ∂m := by
        apply lintegral_mono_ae
        filter_upwards [hdiff] with r hr
        have hkl :=
          Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
            (hp0 r) (hp1 r) (hq0 r) (hq1 r)
        change InformationTheory.klDiv (k r) (k' r) ≤ _ at hkl
        by_cases hrE : r ∈ E
        · rw [Set.indicator_of_mem hrE]
          exact hkl.trans (ENNReal.ofReal_le_ofReal (by
            have habs : |p r - q r| ≤ D := by simpa [hrE] using hr
            have hsq := (sq_le_sq₀ (abs_nonneg (p r - q r)) hD).2 habs
            rw [← sq_abs (p r - q r)]
            nlinarith))
        · rw [Set.indicator_of_notMem hrE]
          have hpq : p r = q r := by
            have hz : |p r - q r| ≤ 0 := by simpa [hrE] using hr
            exact sub_eq_zero.mp (abs_eq_zero.mp
              (le_antisymm hz (abs_nonneg _)))
          have hkk : k r = k' r := by
            ext A hA
            simp [k, k', commonStatisticBernoulliKernel, hpq]
          rw [hkk, InformationTheory.klDiv_self]
      _ = ∫⁻ _r in E, ENNReal.ofReal (4 * D ^ 2) ∂m :=
        lintegral_indicator hE _
      _ = ENNReal.ofReal (4 * D ^ 2) * m E :=
        setLIntegral_const E (ENNReal.ofReal (4 * D ^ 2))
  · filter_upwards with r
    have hkl :=
      Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
        (hp0 r) (hp1 r) (hq0 r) (hq1 r)
    have hfinite : InformationTheory.klDiv (k r) (k' r) ≠ ⊤ := by
      change InformationTheory.klDiv (k r) (k' r) ≤ _ at hkl
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
    exact (InformationTheory.klDiv_ne_top_iff.mp hfinite).1

/-- Swapping a common statistic behind its Bernoulli outcome preserves the
localized KL estimate, giving the `(outcome, statistic)` coordinate order
used by signed observations. -/
-- @node: commonStatisticBernoulliOutcome_klDiv_le_of_localized_parameter
lemma commonStatisticBernoulliOutcome_klDiv_le_of_localized_parameter
    (m : Measure ℝ) [IsFiniteMeasure m] (p q : ℝ → ℝ)
    (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ r, 1 / 4 ≤ p r) (hp1 : ∀ r, p r ≤ 3 / 4)
    (hq0 : ∀ r, 1 / 4 ≤ q r) (hq1 : ∀ r, q r ≤ 3 / 4)
    {D : ℝ} (hD : 0 ≤ D) {E : Set ℝ} (hE : MeasurableSet E)
    (hdiff : ∀ᵐ r ∂m, |p r - q r| ≤ E.indicator (fun _ => D) r) :
    InformationTheory.klDiv
        (Measure.map Prod.swap
          (Measure.compProd m (commonStatisticBernoulliKernel p hp)))
        (Measure.map Prod.swap
          (Measure.compProd m (commonStatisticBernoulliKernel q hq))) ≤
      ENNReal.ofReal (4 * D ^ 2) * m E := by
  letI : IsMarkovKernel (commonStatisticBernoulliKernel p hp) :=
    commonStatisticBernoulliKernel_isMarkovKernel p hp
      (fun r => by linarith [hp0 r]) (fun r => by linarith [hp1 r])
  letI : IsMarkovKernel (commonStatisticBernoulliKernel q hq) :=
    commonStatisticBernoulliKernel_isMarkovKernel q hq
      (fun r => by linarith [hq0 r]) (fun r => by linarith [hq1 r])
  rw [show (Prod.swap : ℝ × ℝ → ℝ × ℝ) =
    ⇑(MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) by rfl]
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
    (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding]
  exact commonStatisticBernoulli_klDiv_le_of_localized_parameter m p q hp hq
    hp0 hp1 hq0 hq1 hD hE hdiff


/-- The success-weighted pushforward associated with a real statistic. -/
-- @node: statisticSuccessMeasure
noncomputable def statisticSuccessMeasure {A : Type*} [MeasurableSpace A]
    (nu : Measure A) (p : A → ℝ) (stat : A → ℝ) : Measure ℝ :=
  Measure.map stat (nu.withDensity fun x => ENNReal.ofReal (p x))

/-- A measurable version of the Bernoulli success probability conditional on
the statistic. -/
-- @node: statisticSuccessParameter
noncomputable def statisticSuccessParameter {A : Type*} [MeasurableSpace A]
    (nu : Measure A) (p : A → ℝ) (stat : A → ℝ) : ℝ → ℝ :=
  fun r => ((statisticSuccessMeasure nu p stat).rnDeriv
    (Measure.map stat nu) r).toReal

/-- The success-weighted statistic law is dominated by the statistic
marginal when the pointwise success probability is at most one. -/
-- @node: statisticSuccessMeasure_absolutelyContinuous
lemma statisticSuccessMeasure_absolutelyContinuous
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsFiniteMeasure nu]
    (p : A → ℝ) (stat : A → ℝ) (hstat : Measurable stat)
    (hp1 : ∀ x, p x ≤ 1) :
    statisticSuccessMeasure nu p stat ≪ Measure.map stat nu := by
  apply Measure.absolutelyContinuous_of_le
  apply Measure.map_mono
  · calc
      nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤
          nu.withDensity 1 := by
        apply withDensity_mono
        filter_upwards with x
        simpa using ENNReal.ofReal_le_one.mpr (hp1 x)
      _ = nu := withDensity_one
  · exact hstat

/-- Set integrals of the conditional parameter recover success-weighted
integrals on statistic preimages. -/
-- @node: statisticSuccessParameter_setIntegral
lemma statisticSuccessParameter_setIntegral
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsFiniteMeasure nu]
    (p : A → ℝ) (stat : A → ℝ) (hp : Measurable p)
    (hstat : Measurable stat) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ r in B, statisticSuccessParameter nu p stat r ∂(Measure.map stat nu)) =
      ∫ x in {x | stat x ∈ B}, p x ∂nu := by
  let m : Measure ℝ := Measure.map stat nu
  let s : Measure ℝ := statisticSuccessMeasure nu p stat
  have hle : s ≤ m := by
    dsimp [s, m, statisticSuccessMeasure]
    apply Measure.map_mono
    · calc
        nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤
            nu.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (hp1 x)
        _ = nu := withDensity_one
    · exact hstat
  have hac : s ≪ m := Measure.absolutelyContinuous_of_le hle
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu stat
  letI : IsFiniteMeasure s := isFiniteMeasure_of_le m hle
  have hleft := Measure.setIntegral_toReal_rnDeriv hac B
  have hsB : s B = ENNReal.ofReal (∫ x in {x | stat x ∈ B}, p x ∂nu) := by
    change (Measure.map stat
      (nu.withDensity fun x => ENNReal.ofReal (p x))) B = _
    rw [Measure.map_apply hstat hB, withDensity_apply _ (hB.preimage hstat)]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rfl
    · apply Measure.integrableOn_of_bounded (measure_ne_top _ _)
          hp.aestronglyMeasurable
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 x)]
      exact hp1 x
    · exact Filter.Eventually.of_forall hp0
  change (∫ r in B, ((s.rnDeriv m) r).toReal ∂m) = _
  rw [hleft, Measure.real_def, hsB, ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall hp0)

/-- Middle-half pointwise bounds pass to the conditional statistic
parameter almost everywhere. -/
-- @node: statisticSuccessParameter_mem_Icc_ae
lemma statisticSuccessParameter_mem_Icc_ae
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsFiniteMeasure nu]
    (p : A → ℝ) (stat : A → ℝ) (hp : Measurable p)
    (hstat : Measurable stat) (hp0 : ∀ x, 1 / 4 ≤ p x)
    (hp1 : ∀ x, p x ≤ 3 / 4) :
    ∀ᵐ r ∂(Measure.map stat nu),
      statisticSuccessParameter nu p stat r ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  let m : Measure ℝ := Measure.map stat nu
  let g : ℝ → ℝ := statisticSuccessParameter nu p stat
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu stat
  let s : Measure ℝ := statisticSuccessMeasure nu p stat
  have hsle : s ≤ m := by
    dsimp [s, m, statisticSuccessMeasure]
    apply Measure.map_mono
    · calc
        nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤
            nu.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (by linarith [hp1 x])
        _ = nu := withDensity_one
    · exact hstat
  letI : IsFiniteMeasure s := isFiniteMeasure_of_le m hsle
  have hg : Integrable g m := by
    dsimp [g, statisticSuccessParameter, m]
    exact Measure.integrable_toReal_rnDeriv
  have hcLo : Integrable (fun _ : ℝ => (1 / 4 : ℝ)) m := integrable_const _
  have hcHi : Integrable (fun _ : ℝ => (3 / 4 : ℝ)) m := integrable_const _
  have hlo : (fun _ : ℝ => (1 / 4 : ℝ)) ≤ᵐ[m] g := by
    apply ae_le_of_forall_setIntegral_le hcLo hg
    intro B hB _
    rw [statisticSuccessParameter_setIntegral nu p stat hp hstat
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) B hB]
    rw [integral_const]
    change (m.restrict B).real Set.univ * (1 / 4 : ℝ) ≤ _
    rw [Measure.real_def, Measure.restrict_apply_univ]
    have hmap : m B = nu {x | stat x ∈ B} := by
      rw [Measure.map_apply hstat hB]
      rfl
    rw [hmap]
    have hmono : (∫ x in {x | stat x ∈ B}, (1 / 4 : ℝ) ∂nu) ≤
        ∫ x in {x | stat x ∈ B}, p x ∂nu := by
      apply integral_mono_ae
      · exact integrableOn_const
      · apply Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
            hp.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hp0 x], by linarith [hp1 x]⟩
      · exact ae_restrict_of_forall_mem (hB.preimage hstat)
          (fun x _ => hp0 x)
    simpa [Measure.real_def] using hmono
  have hhi : g ≤ᵐ[m] (fun _ : ℝ => (3 / 4 : ℝ)) := by
    apply ae_le_of_forall_setIntegral_le hg hcHi
    intro B hB _
    rw [statisticSuccessParameter_setIntegral nu p stat hp hstat
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) B hB]
    rw [integral_const]
    change _ ≤ (m.restrict B).real Set.univ * (3 / 4 : ℝ)
    rw [Measure.real_def, Measure.restrict_apply_univ]
    have hmap : m B = nu {x | stat x ∈ B} := by
      rw [Measure.map_apply hstat hB]
      rfl
    rw [hmap]
    have hmono : (∫ x in {x | stat x ∈ B}, p x ∂nu) ≤
        ∫ x in {x | stat x ∈ B}, (3 / 4 : ℝ) ∂nu := by
      apply integral_mono_ae
      · apply Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
            hp.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hp0 x], by linarith [hp1 x]⟩
      · exact integrableOn_const
      · exact ae_restrict_of_forall_mem (hB.preimage hstat)
          (fun x _ => hp1 x)
    simpa [Measure.real_def] using hmono
  filter_upwards [hlo, hhi] with r hr0 hr1
  exact ⟨hr0, hr1⟩

/-- Globally clip the conditional parameter to the middle half. -/
-- @node: clippedStatisticSuccessParameter
noncomputable def clippedStatisticSuccessParameter
    {A : Type*} [MeasurableSpace A]
    (nu : Measure A) (p : A → ℝ) (stat : A → ℝ) : ℝ → ℝ :=
  fun r => max (1 / 4 : ℝ) (min (3 / 4 : ℝ)
    (statisticSuccessParameter nu p stat r))

-- @node: clippedStatisticSuccessParameter_measurable
@[fun_prop]
lemma clippedStatisticSuccessParameter_measurable
    {A : Type*} [MeasurableSpace A]
    (nu : Measure A) (p : A → ℝ) (stat : A → ℝ) :
    Measurable (clippedStatisticSuccessParameter nu p stat) := by
  unfold clippedStatisticSuccessParameter statisticSuccessParameter
  fun_prop

-- @node: clippedStatisticSuccessParameter_mem_Icc
lemma clippedStatisticSuccessParameter_mem_Icc
    {A : Type*} [MeasurableSpace A]
    (nu : Measure A) (p : A → ℝ) (stat : A → ℝ) (r : ℝ) :
    clippedStatisticSuccessParameter nu p stat r ∈
      Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  unfold clippedStatisticSuccessParameter
  constructor <;> simp <;> norm_num

-- @node: clippedStatisticSuccessParameter_ae_eq
lemma clippedStatisticSuccessParameter_ae_eq
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsFiniteMeasure nu]
    (p : A → ℝ) (stat : A → ℝ) (hp : Measurable p)
    (hstat : Measurable stat) (hp0 : ∀ x, 1 / 4 ≤ p x)
    (hp1 : ∀ x, p x ≤ 3 / 4) :
    clippedStatisticSuccessParameter nu p stat =ᵐ[Measure.map stat nu]
      statisticSuccessParameter nu p stat := by
  filter_upwards [statisticSuccessParameter_mem_Icc_ae nu p stat hp hstat hp0 hp1]
    with r hr
  unfold clippedStatisticSuccessParameter
  rw [min_eq_right hr.2, max_eq_right hr.1]

/-- Integrating Bernoulli kernels over two base sets gives the same outcome
measure when the base masses and success-weighted masses agree. -/
-- @node: commonStatisticBernoulliKernel_setLIntegral_eq
lemma commonStatisticBernoulliKernel_setLIntegral_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (nu : Measure A) [IsFiniteMeasure nu]
    (nu' : Measure B) [IsFiniteMeasure nu']
    (p : A → ℝ) (p' : B → ℝ) (hp : Measurable p) (hp' : Measurable p')
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hp0' : ∀ x, 0 ≤ p' x) (hp1' : ∀ x, p' x ≤ 1)
    {D : Set A} {D' : Set B} (hmass : nu D = nu' D')
    (hmean : ∫ x in D, p x ∂nu = ∫ x in D', p' x ∂nu')
    (E : Set ℝ) :
    (∫⁻ x in D, commonStatisticBernoulliKernel p hp x E ∂nu) =
      ∫⁻ x in D', commonStatisticBernoulliKernel p' hp' x E ∂nu' := by
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
  simp only [commonStatisticBernoulliKernel, Kernel.coe_mk,
    Causalean.Mathlib.Probability.bernoulliLaw, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  change (∫⁻ x, ENNReal.ofReal (p x) * Measure.dirac (1 : ℝ) E +
      ENNReal.ofReal (1 - p x) * Measure.dirac (0 : ℝ) E ∂(nu.restrict D)) =
    ∫⁻ x, ENNReal.ofReal (p' x) * Measure.dirac (1 : ℝ) E +
      ENNReal.ofReal (1 - p' x) * Measure.dirac (0 : ℝ) E ∂(nu'.restrict D')
  rw [lintegral_add_left (by fun_prop) _, lintegral_add_left (by fun_prop) _]
  simp_rw [mul_comm (ENNReal.ofReal (p _)),
    mul_comm (ENNReal.ofReal (1 - p _)),
    mul_comm (ENNReal.ofReal (p' _)),
    mul_comm (ENNReal.ofReal (1 - p' _))]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
    hpL, hqL]

/-- Compressing the base coordinate to a statistic turns a Bernoulli mixture
into a Bernoulli composition product over the statistic marginal. -/
-- @node: statisticBernoulliOutcomeLaw_eq_map_swap_compProd
lemma statisticBernoulliOutcomeLaw_eq_map_swap_compProd
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsFiniteMeasure nu]
    (p : A → ℝ) (stat : A → ℝ) (hp : Measurable p)
    (hstat : Measurable stat) (hp0 : ∀ x, 1 / 4 ≤ p x)
    (hp1 : ∀ x, p x ≤ 3 / 4) :
    Measure.map (fun z : A × ℝ => (z.2, stat z.1))
        (Measure.compProd nu (commonStatisticBernoulliKernel p hp)) =
      Measure.map Prod.swap
        (Measure.compProd (Measure.map stat nu)
          (commonStatisticBernoulliKernel
            (clippedStatisticSuccessParameter nu p stat)
            (clippedStatisticSuccessParameter_measurable nu p stat))) := by
  let m : Measure ℝ := Measure.map stat nu
  let g : ℝ → ℝ := clippedStatisticSuccessParameter nu p stat
  let hg : Measurable g := clippedStatisticSuccessParameter_measurable nu p stat
  letI : IsMarkovKernel (commonStatisticBernoulliKernel p hp) :=
    commonStatisticBernoulliKernel_isMarkovKernel p hp
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x])
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu stat
  letI : IsMarkovKernel (commonStatisticBernoulliKernel g hg) :=
    commonStatisticBernoulliKernel_isMarkovKernel g hg
      (fun r => by dsimp [g]; linarith [
        (clippedStatisticSuccessParameter_mem_Icc nu p stat r).1])
      (fun r => by dsimp [g]; linarith [
        (clippedStatisticSuccessParameter_mem_Icc nu p stat r).2])
  apply Measure.ext_prod
  intro E B hE hB
  have hleft : (Measure.map (fun z : A × ℝ => (z.2, stat z.1))
      (Measure.compProd nu (commonStatisticBernoulliKernel p hp))) (E ×ˢ B) =
      ∫⁻ x in {x | stat x ∈ B},
        commonStatisticBernoulliKernel p hp x E ∂nu := by
    rw [Measure.map_apply (by fun_prop) (hE.prod hB), Measure.compProd_apply]
    · change _ = ∫⁻ x in stat ⁻¹' B,
          commonStatisticBernoulliKernel p hp x E ∂nu
      rw [← lintegral_indicator (hB.preimage hstat)]
      apply lintegral_congr
      intro x
      by_cases hx : stat x ∈ B
      · have hpre : Prod.mk x ⁻¹'
            ((fun z : A × ℝ => (z.2, stat z.1)) ⁻¹' (E ×ˢ B)) = E := by
          ext y
          simp [hx]
        have hx' : x ∈ stat ⁻¹' B := hx
        rw [hpre, Set.indicator_of_mem hx']
      · have hpre : Prod.mk x ⁻¹'
            ((fun z : A × ℝ => (z.2, stat z.1)) ⁻¹' (E ×ˢ B)) = ∅ := by
          ext y
          simp [hx]
        have hx' : x ∉ stat ⁻¹' B := hx
        rw [hpre, measure_empty, Set.indicator_of_notMem hx']
    · exact (hE.prod hB).preimage (by fun_prop)
  rw [hleft]
  have hright : (Measure.map Prod.swap
      (Measure.compProd m (commonStatisticBernoulliKernel g hg))) (E ×ˢ B) =
      ∫⁻ r in B, commonStatisticBernoulliKernel g hg r E ∂m := by
    rw [Measure.map_apply measurable_swap (hE.prod hB), Measure.compProd_apply]
    · rw [← lintegral_indicator hB]
      congr 1
      funext r
      by_cases hr : r ∈ B <;> simp [hr]
    · exact (hE.prod hB).preimage measurable_swap
  rw [hright]
  apply commonStatisticBernoulliKernel_setLIntegral_eq
    nu m p g hp hg
    (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x])
    (fun r => by dsimp [g]; linarith [
      (clippedStatisticSuccessParameter_mem_Icc nu p stat r).1])
    (fun r => by dsimp [g]; linarith [
      (clippedStatisticSuccessParameter_mem_Icc nu p stat r).2])
  · rw [Measure.map_apply hstat hB]
    rfl
  · have heq := clippedStatisticSuccessParameter_ae_eq
      nu p stat hp hstat hp0 hp1
    rw [integral_congr_ae (ae_restrict_of_ae heq)]
    exact (statisticSuccessParameter_setIntegral nu p stat hp hstat
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) B hB).symm

/-- A localized setwise bound on success-weighted statistic masses yields
the corresponding almost-everywhere bound on conditional Bernoulli
parameters. -/
-- @node: clippedStatisticSuccessParameter_abs_sub_le_ae
lemma clippedStatisticSuccessParameter_abs_sub_le_ae
    {A : Type*} [MeasurableSpace A]
    (nu nu' : Measure A) [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (p p' : A → ℝ) (stat : A → ℝ)
    (hp : Measurable p) (hp' : Measurable p') (hstat : Measurable stat)
    (hp0 : ∀ x, 1 / 4 ≤ p x) (hp1 : ∀ x, p x ≤ 3 / 4)
    (hp0' : ∀ x, 1 / 4 ≤ p' x) (hp1' : ∀ x, p' x ≤ 3 / 4)
    (hmap : Measure.map stat nu = Measure.map stat nu')
    {D : ℝ} (hD : 0 ≤ D) {E : Set ℝ} (hE : MeasurableSet E)
    (hdiff : ∀ B : Set ℝ, MeasurableSet B →
      |(∫ x in {x | stat x ∈ B}, p x ∂nu) -
        ∫ x in {x | stat x ∈ B}, p' x ∂nu'| ≤
          D * (Measure.map stat nu (B ∩ E)).toReal) :
    ∀ᵐ r ∂(Measure.map stat nu),
      |clippedStatisticSuccessParameter nu p stat r -
        clippedStatisticSuccessParameter nu' p' stat r| ≤
          E.indicator (fun _ => D) r := by
  let m : Measure ℝ := Measure.map stat nu
  let g : ℝ → ℝ := statisticSuccessParameter nu p stat
  let g' : ℝ → ℝ := statisticSuccessParameter nu' p' stat
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu stat
  let s : Measure ℝ := statisticSuccessMeasure nu p stat
  let s' : Measure ℝ := statisticSuccessMeasure nu' p' stat
  have hsle : s ≤ m := by
    dsimp [s, m, statisticSuccessMeasure]
    apply Measure.map_mono
    · calc
        nu.withDensity (fun x => ENNReal.ofReal (p x)) ≤
            nu.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (by linarith [hp1 x])
        _ = nu := withDensity_one
    · exact hstat
  have hs'le : s' ≤ m := by
    change statisticSuccessMeasure nu' p' stat ≤ Measure.map stat nu
    rw [hmap]
    dsimp [s', statisticSuccessMeasure]
    apply Measure.map_mono
    · calc
        nu'.withDensity (fun x => ENNReal.ofReal (p' x)) ≤
            nu'.withDensity 1 := by
          apply withDensity_mono
          filter_upwards with x
          simpa using ENNReal.ofReal_le_one.mpr (by linarith [hp1' x])
        _ = nu' := withDensity_one
    · exact hstat
  letI : IsFiniteMeasure s := isFiniteMeasure_of_le m hsle
  letI : IsFiniteMeasure s' := isFiniteMeasure_of_le m hs'le
  have hg : Integrable g m := by
    dsimp [g, statisticSuccessParameter, m]
    exact Measure.integrable_toReal_rnDeriv
  have hg' : Integrable g' m := by
    change Integrable (statisticSuccessParameter nu' p' stat) (Measure.map stat nu)
    rw [hmap]
    unfold statisticSuccessParameter
    exact Measure.integrable_toReal_rnDeriv
  have hc : Integrable (E.indicator (fun _ : ℝ => D)) m :=
    (integrable_const _).indicator hE
  have hconst (B : Set ℝ) (hB : MeasurableSet B) :
      (∫ r in B, E.indicator (fun _ : ℝ => D) r ∂m) =
        D * (m (B ∩ E)).toReal := by
    rw [integral_indicator hE, integral_const]
    simp [Measure.real_def, Measure.restrict_apply, hB, hE, inter_comm, mul_comm]
  have hup : (fun r => g r - g' r) ≤ᵐ[m]
      E.indicator (fun _ => D) := by
    apply ae_le_of_forall_setIntegral_le (hg.sub hg') hc
    intro B hB _
    change (∫ r in B, g r - g' r ∂m) ≤ _
    rw [integral_sub hg.integrableOn hg'.integrableOn]
    rw [statisticSuccessParameter_setIntegral nu p stat hp hstat
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) B hB]
    have hp'Int := statisticSuccessParameter_setIntegral nu' p' stat hp' hstat
      (fun x => by linarith [hp0' x]) (fun x => by linarith [hp1' x]) B hB
    change (∫ r in B, g' r ∂Measure.map stat nu') = _ at hp'Int
    rw [← hmap] at hp'Int
    rw [hp'Int, hconst B hB]
    exact (abs_le.mp (hdiff B hB)).2
  have hdown : (fun r => g' r - g r) ≤ᵐ[m]
      E.indicator (fun _ => D) := by
    apply ae_le_of_forall_setIntegral_le (hg'.sub hg) hc
    intro B hB _
    change (∫ r in B, g' r - g r ∂m) ≤ _
    rw [integral_sub hg'.integrableOn hg.integrableOn]
    have hp'Int := statisticSuccessParameter_setIntegral nu' p' stat hp' hstat
      (fun x => by linarith [hp0' x]) (fun x => by linarith [hp1' x]) B hB
    change (∫ r in B, g' r ∂Measure.map stat nu') = _ at hp'Int
    rw [← hmap] at hp'Int
    rw [hp'Int, statisticSuccessParameter_setIntegral nu p stat hp hstat
      (fun x => by linarith [hp0 x]) (fun x => by linarith [hp1 x]) B hB,
      hconst B hB]
    have hh := (abs_le.mp (hdiff B hB)).1
    dsimp [m]
    linarith
  have heq := clippedStatisticSuccessParameter_ae_eq
    nu p stat hp hstat hp0 hp1
  have heq' := clippedStatisticSuccessParameter_ae_eq
    nu' p' stat hp' hstat hp0' hp1'
  rw [← hmap] at heq'
  filter_upwards [hup, hdown, heq, heq'] with r hrup hrdown hr hr'
  rw [hr, hr']
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For a measurable space `A`, two finite measures `nu` and `nu'` on it, and success-probability
    functions `p`, `p'` on `A`, suppose [`p`, `p'`, and a statistic `stat` are all
    measurable](hyp:hp,hp',hstat), [`p` takes values in `[1/4, 3/4]`](hyp:hp0,hp1) and
    [`p'` likewise takes values in `[1/4, 3/4]`](hyp:hp0',hp1'), and [`stat` pushes `nu` and `nu'`
    forward to the same marginal law](hyp:hmap). Given [a nonnegative discrepancy bound
    `D`](hyp:hD) and [a measurable exceptional set `E`](hyp:hE) such that [for every measurable
    set `B` of statistic values, the setwise success-mass discrepancy
    `|∫_{stat∈B} p dnu − ∫_{stat∈B} p' dnu'|` is at most `D` times the `stat`-pushforward mass of
    `nu` on `B ∩ E`](hyp:hdiff), then [the Kullback–Leibler divergence between the compressed
    Bernoulli-outcome laws obtained by pairing the outcome with `stat` under `nu` and under `nu'`
    is at most `4·D²` times the `stat`-pushforward mass of `E` under `nu`](goal). -/
-- @node: statisticBernoulliOutcome_klDiv_le_of_localized_success_bound
lemma statisticBernoulliOutcome_klDiv_le_of_localized_success_bound
    {A : Type*} [MeasurableSpace A]
    (nu nu' : Measure A) [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (p p' : A → ℝ) (stat : A → ℝ)
    (hp : Measurable p) (hp' : Measurable p') (hstat : Measurable stat)
    (hp0 : ∀ x, 1 / 4 ≤ p x) (hp1 : ∀ x, p x ≤ 3 / 4)
    (hp0' : ∀ x, 1 / 4 ≤ p' x) (hp1' : ∀ x, p' x ≤ 3 / 4)
    (hmap : Measure.map stat nu = Measure.map stat nu')
    {D : ℝ} (hD : 0 ≤ D) {E : Set ℝ} (hE : MeasurableSet E)
    (hdiff : ∀ B : Set ℝ, MeasurableSet B →
      |(∫ x in {x | stat x ∈ B}, p x ∂nu) -
        ∫ x in {x | stat x ∈ B}, p' x ∂nu'| ≤
          D * (Measure.map stat nu (B ∩ E)).toReal) :
    InformationTheory.klDiv
        (Measure.map (fun z : A × ℝ => (z.2, stat z.1))
          (Measure.compProd nu (commonStatisticBernoulliKernel p hp)))
        (Measure.map (fun z : A × ℝ => (z.2, stat z.1))
          (Measure.compProd nu' (commonStatisticBernoulliKernel p' hp'))) ≤
      ENNReal.ofReal (4 * D ^ 2) * Measure.map stat nu E := by
  rw [statisticBernoulliOutcomeLaw_eq_map_swap_compProd nu p stat hp hstat hp0 hp1,
    statisticBernoulliOutcomeLaw_eq_map_swap_compProd nu' p' stat hp' hstat hp0' hp1']
  rw [← hmap]
  apply commonStatisticBernoulliOutcome_klDiv_le_of_localized_parameter
  · exact fun r => (clippedStatisticSuccessParameter_mem_Icc nu p stat r).1
  · exact fun r => (clippedStatisticSuccessParameter_mem_Icc nu p stat r).2
  · exact fun r => (clippedStatisticSuccessParameter_mem_Icc nu' p' stat r).1
  · exact fun r => (clippedStatisticSuccessParameter_mem_Icc nu' p' stat r).2
  · exact hD
  · exact hE
  · exact clippedStatisticSuccessParameter_abs_sub_le_ae
      nu nu' p p' stat hp hp' hstat hp0 hp1 hp0' hp1' hmap hD hE hdiff

/-- Common statistic marginals and a localized setwise success-mass bound
also imply exact agreement of the compressed outcome laws away from the
exceptional statistic set. -/
-- @node: statisticBernoulliOutcome_restrict_compl_eq_of_localized_success_bound
lemma statisticBernoulliOutcome_restrict_compl_eq_of_localized_success_bound
    {A : Type*} [MeasurableSpace A]
    (nu nu' : Measure A) [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (p p' : A → ℝ) (stat : A → ℝ)
    (hp : Measurable p) (hp' : Measurable p') (hstat : Measurable stat)
    (hp0 : ∀ x, 1 / 4 ≤ p x) (hp1 : ∀ x, p x ≤ 3 / 4)
    (hp0' : ∀ x, 1 / 4 ≤ p' x) (hp1' : ∀ x, p' x ≤ 3 / 4)
    (hmap : Measure.map stat nu = Measure.map stat nu')
    {D : ℝ} (hD : 0 ≤ D) {E : Set ℝ} (hE : MeasurableSet E)
    (hdiff : ∀ B : Set ℝ, MeasurableSet B →
      |(∫ x in {x | stat x ∈ B}, p x ∂nu) -
        ∫ x in {x | stat x ∈ B}, p' x ∂nu'| ≤
          D * (Measure.map stat nu (B ∩ E)).toReal) :
    (Measure.map (fun z : A × ℝ => (z.2, stat z.1))
        (Measure.compProd nu (commonStatisticBernoulliKernel p hp))).restrict
          {z | z.2 ∉ E} =
      (Measure.map (fun z : A × ℝ => (z.2, stat z.1))
        (Measure.compProd nu'
          (commonStatisticBernoulliKernel p' hp'))).restrict
            {z | z.2 ∉ E} := by
  rw [statisticBernoulliOutcomeLaw_eq_map_swap_compProd nu p stat hp hstat hp0 hp1,
    statisticBernoulliOutcomeLaw_eq_map_swap_compProd nu' p' stat hp' hstat hp0' hp1']
  rw [← hmap]
  let m : Measure ℝ := Measure.map stat nu
  let g : ℝ → ℝ := clippedStatisticSuccessParameter nu p stat
  let g' : ℝ → ℝ := clippedStatisticSuccessParameter nu' p' stat
  let hg : Measurable g := clippedStatisticSuccessParameter_measurable nu p stat
  let hg' : Measurable g' := clippedStatisticSuccessParameter_measurable nu' p' stat
  letI : IsFiniteMeasure m := Measure.isFiniteMeasure_map nu stat
  letI : IsMarkovKernel (commonStatisticBernoulliKernel g hg) :=
    commonStatisticBernoulliKernel_isMarkovKernel g hg
      (fun r => by dsimp [g]; linarith [
        (clippedStatisticSuccessParameter_mem_Icc nu p stat r).1])
      (fun r => by dsimp [g]; linarith [
        (clippedStatisticSuccessParameter_mem_Icc nu p stat r).2])
  letI : IsMarkovKernel (commonStatisticBernoulliKernel g' hg') :=
    commonStatisticBernoulliKernel_isMarkovKernel g' hg'
      (fun r => by dsimp [g']; linarith [
        (clippedStatisticSuccessParameter_mem_Icc nu' p' stat r).1])
      (fun r => by dsimp [g']; linarith [
        (clippedStatisticSuccessParameter_mem_Icc nu' p' stat r).2])
  have hparam := clippedStatisticSuccessParameter_abs_sub_le_ae
    nu nu' p p' stat hp hp' hstat hp0 hp1 hp0' hp1' hmap hD hE hdiff
  ext S hS
  have houtside : {z : ℝ × ℝ | z.2 ∉ E} = Prod.snd ⁻¹' Eᶜ := by
    ext z
    simp
  rw [houtside]
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  rw [Measure.map_apply measurable_swap (hS.inter
      (hE.compl.preimage measurable_snd)),
    Measure.map_apply measurable_swap (hS.inter
      (hE.compl.preimage measurable_snd))]
  rw [Measure.compProd_apply, Measure.compProd_apply]
  · apply lintegral_congr_ae
    filter_upwards [hparam] with r hr
    by_cases hrE : r ∈ E
    · have hempty : Prod.mk r ⁻¹'
          (Prod.swap ⁻¹' (S ∩ Prod.snd ⁻¹' Eᶜ)) = ∅ := by
        ext y
        simp [hrE]
      rw [hempty, measure_empty, measure_empty]
    · have hzero : |g r - g' r| ≤ 0 := by
        simpa [g, g', Set.indicator_of_notMem hrE] using hr
      have heq : g r = g' r := sub_eq_zero.mp (abs_eq_zero.mp
        (le_antisymm hzero (abs_nonneg _)))
      have hk : commonStatisticBernoulliKernel g hg r =
          commonStatisticBernoulliKernel g' hg' r := by
        ext B hB
        simp [commonStatisticBernoulliKernel, heq]
      rw [hk]
  · exact (hS.inter (hE.compl.preimage measurable_snd)).preimage measurable_swap
  · exact (hS.inter (hE.compl.preimage measurable_snd)).preimage measurable_swap


end Causalean.Mathlib.InformationTheory
