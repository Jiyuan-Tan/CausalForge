/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy-regret rate: minimax lower bound (headline converse)

Stage-2 scaffold. The explicit two-point witness, its class membership and
χ²/separation analysis, the in-core Le Cam testing lemma, the CRUX converse
`thm:minimax-lower`, and the headline corollary `thm:rate-characterization`.
Every proof body is `sorry`.
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
import CausalSmith.Mathlib.InformationTheory.ProductChiSquared
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Causalean.Mathlib.MeasureTheory.PartitionRnDeriv
import Causalean.Stat.Minimax.ChiSquared
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Pi

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators Topology

/-- `{0,1}`-supported Bernoulli observation-treatment measure on the treatment
space `Bool` (`true ↦ 1`) with `P(A=1)=p`. -/
noncomputable def bernoulliBool (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true
    + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- `{-1,1}`-supported outcome measure with mean `m` (`P(Y=1)=(1+m)/2`). -/
noncomputable def bernoulliPM (m : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 + m) / 2) • Measure.dirac (1 : ℝ)
    + ENNReal.ofReal ((1 - m) / 2) • Measure.dirac (-1 : ℝ)

@[fun_prop] lemma measurable_bernoulliBool : Measurable bernoulliBool := by
  unfold bernoulliBool
  fun_prop

@[fun_prop] lemma measurable_bernoulliPM : Measurable bernoulliPM := by
  unfold bernoulliPM
  fun_prop

lemma bernoulliBool_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliBool p) := by
  rw [isProbabilityMeasure_iff]
  unfold bernoulliBool
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  rw [show p + (1 - p) = (1 : ℝ) by ring]
  simp

lemma bernoulliPM_isProbabilityMeasure {m : ℝ} (hm_lo : -1 ≤ m) (hm_hi : m ≤ 1) :
    IsProbabilityMeasure (bernoulliPM m) := by
  rw [isProbabilityMeasure_iff]
  unfold bernoulliPM
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add]
  · rw [show (1 + m) / 2 + (1 - m) / 2 = (1 : ℝ) by ring]
    simp
  · linarith
  · linarith

lemma bernoulliBool_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Bool → ℝ) :
    ∫ a, f a ∂bernoulliBool p = p * f true + (1 - p) * f false := by
  unfold bernoulliBool
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [hp0, sub_nonneg.mpr hp1, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac true)
      (c := ENNReal.ofReal p)
      (integrable_dirac (f := f) (a := true) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac false)
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac (f := f) (a := false) (by simp [enorm])) (by simp)

lemma bernoulliPM_integral {m : ℝ} (hm_lo : -1 ≤ m) (hm_hi : m ≤ 1)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂bernoulliPM m =
      ((1 + m) / 2) * f 1 + ((1 - m) / 2) * f (-1) := by
  unfold bernoulliPM
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [show 0 ≤ (1 + m) / 2 by linarith,
      show 0 ≤ (1 - m) / 2 by linarith, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac (1 : ℝ))
      (c := ENNReal.ofReal ((1 + m) / 2))
      (integrable_dirac (f := f) (a := (1 : ℝ)) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (-1 : ℝ))
      (c := ENNReal.ofReal ((1 - m) / 2))
      (integrable_dirac (f := f) (a := (-1 : ℝ)) (by simp [enorm])) (by simp)

lemma bernoulliPM_mean {m : ℝ} (hm_lo : -1 ≤ m) (hm_hi : m ≤ 1) :
    ∫ y, y ∂bernoulliPM m = m := by
  rw [bernoulliPM_integral hm_lo hm_hi]
  ring

lemma bernoulliPM_bad_support_zero (m : ℝ) :
    (bernoulliPM m) {y | y ∉ Set.Icc (-1 : ℝ) 1} = 0 := by
  unfold bernoulliPM
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

lemma bernoulliBool_bind {β : Type*} [MeasurableSpace β] (p : ℝ)
    (K : Bool → Measure β) :
    (bernoulliBool p).bind K =
      ENNReal.ofReal p • K true + ENNReal.ofReal (1 - p) • K false := by
  ext s hs
  have hKmeas : AEMeasurable K (bernoulliBool p) :=
    (measurable_of_finite K).aemeasurable
  rw [Measure.bind_apply hs hKmeas]
  unfold bernoulliBool
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

private lemma integrable_of_measurable_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hfmeas : Measurable f) (hfbdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    Integrable f μ := by
  rcases hfbdd with ⟨M, hM⟩
  refine Integrable.of_bound hfmeas.aestronglyMeasurable (max M 0) ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using le_trans (hM x) (le_max_left M 0)

private lemma measurable_observation_X : Measurable (fun O : Observation ℝ => O.X) := by
  have htuple : Measurable (fun O : Observation ℝ => (O.X, O.A, O.Y)) :=
    Measurable.of_comap_le le_rfl
  change Measurable ((fun p : ℝ × (Bool × ℝ) => p.1) ∘
    (fun O : Observation ℝ => (O.X, O.A, O.Y)))
  exact measurable_fst.comp htuple

private lemma measurable_observation_A : Measurable (fun O : Observation ℝ => O.A) := by
  have htuple : Measurable (fun O : Observation ℝ => (O.X, O.A, O.Y)) :=
    Measurable.of_comap_le le_rfl
  change Measurable ((fun p : ℝ × (Bool × ℝ) => p.2.1) ∘
    (fun O : Observation ℝ => (O.X, O.A, O.Y)))
  exact (measurable_fst.comp measurable_snd).comp htuple

private lemma measurable_observation_Y : Measurable (fun O : Observation ℝ => O.Y) := by
  have htuple : Measurable (fun O : Observation ℝ => (O.X, O.A, O.Y)) :=
    Measurable.of_comap_le le_rfl
  change Measurable ((fun p : ℝ × (Bool × ℝ) => p.2.2) ∘
    (fun O : Observation ℝ => (O.X, O.A, O.Y)))
  exact (measurable_snd.comp measurable_snd).comp htuple

lemma measurable_observation_tuple_real :
    Measurable (fun O : Observation ℝ => (O.X, O.A, O.Y)) :=
  Measurable.of_comap_le le_rfl

instance instMeasurableSingletonClassObservationReal :
    MeasurableSingletonClass (Observation ℝ) := by
  refine ⟨?_⟩
  intro O
  have hset : MeasurableSet ((fun O' : Observation ℝ => (O'.X, O'.A, O'.Y)) ⁻¹'
      ({(O.X, O.A, O.Y)} : Set (ℝ × Bool × ℝ))) :=
    measurable_observation_tuple_real (measurableSet_singleton _)
  convert hset using 1
  ext O'
  cases O
  cases O'
  simp

@[fun_prop] lemma measurable_observation_mk (x : ℝ) (a : Bool) :
    Measurable (fun y : ℝ => Observation.mk x a y) := by
  rw [measurable_comap_iff]
  fun_prop

@[fun_prop] lemma measurable_observation_mk_X (a : Bool) (y : ℝ) :
    Measurable (fun x : ℝ => Observation.mk x a y) := by
  rw [measurable_comap_iff]
  fun_prop

lemma measurable_smul_measure_variable {ι β : Type*} [MeasurableSpace ι] [MeasurableSpace β]
    {c : ι → ENNReal} {μ : ι → Measure β} (hc : Measurable c) (hμ : Measurable μ) :
    Measurable fun x => c x • μ x := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  exact hc.mul ((Measure.measurable_coe hs).comp hμ)

lemma measurable_map_observation_dirac (a : Bool) (y0 : ℝ) :
    Measurable fun x : ℝ =>
      Measure.map (Observation.mk x a) (Measure.dirac y0 : Measure ℝ) := by
  rw [show (fun x : ℝ =>
      Measure.map (Observation.mk x a) (Measure.dirac y0 : Measure ℝ)) =
      fun x => Measure.dirac (Observation.mk x a y0) by
    funext x
    rw [Measure.map_dirac]]
  exact Measure.measurable_dirac.comp (measurable_observation_mk_X a y0)

lemma measurable_map_observation_bernoulliPM (a : Bool) (m : ℝ) :
    Measurable fun x : ℝ => Measure.map (Observation.mk x a) (bernoulliPM m) := by
  rw [show (fun x : ℝ => Measure.map (Observation.mk x a) (bernoulliPM m)) =
      fun x =>
        ENNReal.ofReal ((1 + m) / 2) • Measure.dirac (Observation.mk x a (1 : ℝ)) +
          ENNReal.ofReal ((1 - m) / 2) • Measure.dirac (Observation.mk x a (-1 : ℝ)) by
    funext x
    unfold bernoulliPM
    rw [Measure.map_add _ _ (measurable_observation_mk x a)]
    rw [Measure.map_smul, Measure.map_smul]
    rw [Measure.map_dirac, Measure.map_dirac]]
  have hdir1 : Measurable fun x : ℝ => Measure.dirac (Observation.mk x a (1 : ℝ)) :=
    Measure.measurable_dirac.comp (measurable_observation_mk_X a 1)
  have hdirNeg : Measurable fun x : ℝ => Measure.dirac (Observation.mk x a (-1 : ℝ)) :=
    Measure.measurable_dirac.comp (measurable_observation_mk_X a (-1))
  exact (measurable_smul_measure_variable measurable_const hdir1).add
    (measurable_smul_measure_variable measurable_const hdirNeg)

lemma twoPointWitness_expanded_kernel_measurable
    (α cB σ h q τ0 : ℝ) :
    Measurable fun x : ℝ =>
      ENNReal.ofReal (if 0 ≤ x ∧ x ≤ cB * h ^ α then q else 1 / 2) •
          Measure.map (Observation.mk x true)
            (if 0 ≤ x ∧ x ≤ cB * h ^ α then bernoulliPM (σ * h)
             else bernoulliPM (τ0 / 2)) +
        ENNReal.ofReal (1 - if 0 ≤ x ∧ x ≤ cB * h ^ α then q else 1 / 2) •
          Measure.map (Observation.mk x false)
            (if 0 ≤ x ∧ x ≤ cB * h ^ α then Measure.dirac 0
             else bernoulliPM (-τ0 / 2)) := by
  have hB : MeasurableSet {x : ℝ | 0 ≤ x ∧ x ≤ cB * h ^ α} := measurableSet_Icc
  have hbase : Measurable fun x : ℝ =>
      if 0 ≤ x ∧ x ≤ cB * h ^ α then q else 1 / 2 := by
    exact Measurable.ite hB measurable_const measurable_const
  have hcoefT : Measurable fun x : ℝ =>
      ENNReal.ofReal (if 0 ≤ x ∧ x ≤ cB * h ^ α then q else 1 / 2) := by
    fun_prop
  have hcoefF : Measurable fun x : ℝ =>
      ENNReal.ofReal (1 - if 0 ≤ x ∧ x ≤ cB * h ^ α then q else 1 / 2) := by
    fun_prop
  have houtT : Measurable fun x : ℝ =>
      if 0 ≤ x ∧ x ≤ cB * h ^ α then bernoulliPM (σ * h) else bernoulliPM (τ0 / 2) := by
    exact Measurable.ite hB measurable_const measurable_const
  have houtF : Measurable fun x : ℝ =>
      if 0 ≤ x ∧ x ≤ cB * h ^ α then (Measure.dirac 0 : Measure ℝ)
      else bernoulliPM (-τ0 / 2) := by
    exact Measurable.ite hB measurable_const measurable_const
  have hmapT : Measurable fun x : ℝ =>
      Measure.map (Observation.mk x true)
        (if 0 ≤ x ∧ x ≤ cB * h ^ α then bernoulliPM (σ * h)
         else bernoulliPM (τ0 / 2)) := by
    rw [show (fun x : ℝ =>
        Measure.map (Observation.mk x true)
          (if 0 ≤ x ∧ x ≤ cB * h ^ α then bernoulliPM (σ * h)
           else bernoulliPM (τ0 / 2))) =
        (fun x : ℝ =>
          if 0 ≤ x ∧ x ≤ cB * h ^ α then
            Measure.map (Observation.mk x true) (bernoulliPM (σ * h))
          else
            Measure.map (Observation.mk x true) (bernoulliPM (τ0 / 2))) by
      funext x
      by_cases hx : 0 ≤ x ∧ x ≤ cB * h ^ α <;> simp [hx]]
    exact Measurable.ite hB (measurable_map_observation_bernoulliPM true (σ * h))
      (measurable_map_observation_bernoulliPM true (τ0 / 2))
  have hmapF : Measurable fun x : ℝ =>
      Measure.map (Observation.mk x false)
        (if 0 ≤ x ∧ x ≤ cB * h ^ α then Measure.dirac 0
         else bernoulliPM (-τ0 / 2)) := by
    rw [show (fun x : ℝ =>
        Measure.map (Observation.mk x false)
          (if 0 ≤ x ∧ x ≤ cB * h ^ α then Measure.dirac 0
           else bernoulliPM (-τ0 / 2))) =
        (fun x : ℝ =>
          if 0 ≤ x ∧ x ≤ cB * h ^ α then
            Measure.map (Observation.mk x false) (Measure.dirac 0)
          else
            Measure.map (Observation.mk x false) (bernoulliPM (-τ0 / 2))) by
      funext x
      by_cases hx : 0 ≤ x ∧ x ≤ cB * h ^ α <;> simp [hx]]
    exact Measurable.ite hB (measurable_map_observation_dirac false 0)
      (measurable_map_observation_bernoulliPM false (-τ0 / 2))
  exact (measurable_smul_measure_variable hcoefT hmapT).add
    (measurable_smul_measure_variable hcoefF hmapF)

lemma restricted_volume_Icc01_isProbabilityMeasure :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [isProbabilityMeasure_iff]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp

lemma restricted_volume_real_Icc_zero_le {a : ℝ} (ha0 : 0 ≤ a) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Icc (0 : ℝ) a) ≤ a := by
  by_cases ha1 : a ≤ 1
  · rw [measureReal_def, Measure.restrict_apply measurableSet_Icc]
    have hinter :
        Set.Icc (0 : ℝ) a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) a := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, ⟨hx.1, le_trans hx.2 ha1⟩⟩
    rw [hinter]
    have hvol :
        volume.real (Set.Icc (0 : ℝ) a) = a := by
      simpa using
        (Real.volume_real_Icc_of_le ha0 :
          volume.real (Set.Icc (0 : ℝ) a) = a - 0)
    simpa [measureReal_def] using le_of_eq hvol
  · have hprob : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      restricted_volume_Icc01_isProbabilityMeasure
    letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := hprob
    have hle_one :
        (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Icc (0 : ℝ) a) ≤ 1 :=
      measureReal_le_one
    have hone_le : (1 : ℝ) ≤ a := le_of_not_ge ha1
    exact hle_one.trans hone_le

lemma betaAG_nonneg_of_nonneg (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    0 ≤ betaAG α γ := by
  unfold betaAG
  by_cases hγ0 : γ = 0
  · simp [hγ0]
  · have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
    have hdenpos : 0 < α + 1 := by linarith
    simp [hγ0, div_nonneg (mul_nonneg hα hγpos.le) hdenpos.le]

lemma Dag_pos_of_nonneg (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    0 < Dag α γ := by
  have hb : 0 ≤ betaAG α γ := betaAG_nonneg_of_nonneg α γ hα hγ
  unfold Dag
  linarith

lemma hLower_pos_of_pos_nat (α γ : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < hLower α γ n := by
  unfold hLower
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma hLower_le_one_of_one_le_nat (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    {n : ℕ} (hn : 1 ≤ n) :
    hLower α γ n ≤ 1 := by
  have hD : 0 < Dag α γ := Dag_pos_of_nonneg α γ hα hγ
  unfold hLower
  have hdiv_nonneg : 0 ≤ 1 / Dag α γ := by positivity
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

lemma eventually_hLower_le_half (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    ∀ᶠ n : ℕ in Filter.atTop, hLower α γ n ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Dag α γ := Dag_pos_of_nonneg α γ hα hγ
  have htend :
      Filter.Tendsto (fun n : ℕ => hLower α γ n) Filter.atTop (𝓝 (0 : ℝ)) := by
    unfold hLower
    exact (tendsto_rpow_neg_atTop (by positivity : 0 < 1 / Dag α γ)).comp
      tendsto_natCast_atTop_atTop
  exact htend.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

lemma eventually_qLower_pos_le_half (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < qLower α γ n ∧ qLower α γ n ≤ (1 / 2 : ℝ) := by
  have hb_nonneg : 0 ≤ betaAG α γ := betaAG_nonneg_of_nonneg α γ hα hγ
  have hD : 0 < Dag α γ := Dag_pos_of_nonneg α γ hα hγ
  by_cases hb0 : betaAG α γ = 0
  · filter_upwards with n
    constructor
    · simp [qLower, hb0]
    · simp [qLower, hb0]
      norm_num
  · have hbpos : 0 < betaAG α γ := lt_of_le_of_ne hb_nonneg (Ne.symm hb0)
    have hrate_pos : 0 < betaAG α γ / Dag α γ := div_pos hbpos hD
    have htend :
        Filter.Tendsto
          (fun n : ℕ => (n : ℝ) ^ (-(betaAG α γ / Dag α γ)))
          Filter.atTop (𝓝 (0 : ℝ)) := by
      exact (tendsto_rpow_neg_atTop hrate_pos).comp tendsto_natCast_atTop_atTop
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) ^ (-(betaAG α γ / Dag α γ)) ≤ (1 / 2 : ℝ) :=
      htend.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsmall, Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with
      n hsmalln hn1
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hn1)
    have hnnon : 0 ≤ (n : ℝ) := le_of_lt hnpos
    have hpoweq :
        ((n : ℝ) ^ (-(1 / Dag α γ))) ^ betaAG α γ =
          (n : ℝ) ^ (-(betaAG α γ / Dag α γ)) := by
      rw [← Real.rpow_mul hnnon]
      congr 1
      ring
    constructor
    · unfold qLower hLower
      rw [if_neg hb0, hpoweq]
      exact Real.rpow_pos_of_pos hnpos _
    · unfold qLower hLower
      rw [if_neg hb0, hpoweq]
      exact hsmalln

lemma activeBlock_overlap_bound_gpos {α γ cB Co co h u v : ℝ}
    (hαpos : 0 < α) (hγpos : 0 < γ) (hCo : 0 < Co) (hco : 0 < co)
    (hcB : cB ≤ Co * co ^ (-(α / γ)))
    (hh0 : 0 < h) (hu0 : 0 < u) (hv0 : 0 < v)
    (hqv : h ^ betaAG α γ ≤ v) (hvle : v ≤ co * u ^ γ) :
    cB * h ^ α ≤ Co * u ^ α * v ^ (1 / γ) := by
  have hβeq : betaAG α γ = α * γ / (α + 1) := by
    unfold betaAG
    simp [ne_of_gt hγpos]
  have hγ_nonneg : 0 ≤ γ := le_of_lt hγpos
  have hα_nonneg : 0 ≤ α := le_of_lt hαpos
  have hβ_nonneg : 0 ≤ betaAG α γ :=
    betaAG_nonneg_of_nonneg α γ hα_nonneg hγ_nonneg
  have hq_pos : 0 < h ^ betaAG α γ := Real.rpow_pos_of_pos hh0 _
  have hq_nonneg : 0 ≤ h ^ betaAG α γ := le_of_lt hq_pos
  have hvpow_nonneg : 0 ≤ v ^ (1 / γ) := Real.rpow_nonneg hv0.le _
  have hpart1 : (h ^ betaAG α γ) ^ (1 / γ) ≤ v ^ (1 / γ) := by
    exact Real.rpow_le_rpow hq_nonneg hqv (by positivity : 0 ≤ 1 / γ)
  have hpart2a : (h ^ betaAG α γ) ^ (α / γ) ≤ v ^ (α / γ) := by
    exact Real.rpow_le_rpow hq_nonneg hqv (by positivity : 0 ≤ α / γ)
  have hcou_split : (co * u ^ γ) ^ (α / γ) = co ^ (α / γ) * u ^ α := by
    have huγ_nonneg : 0 ≤ u ^ γ := Real.rpow_nonneg hu0.le _
    rw [Real.mul_rpow hco.le huγ_nonneg]
    rw [← Real.rpow_mul hu0.le]
    congr 1
    field_simp [hγpos.ne']
  have hpart2b : v ^ (α / γ) ≤ co ^ (α / γ) * u ^ α := by
    calc
      v ^ (α / γ) ≤ (co * u ^ γ) ^ (α / γ) := by
        exact Real.rpow_le_rpow hv0.le hvle (by positivity : 0 ≤ α / γ)
      _ = co ^ (α / γ) * u ^ α := hcou_split
  have hpart2 : (h ^ betaAG α γ) ^ (α / γ) ≤ co ^ (α / γ) * u ^ α :=
    hpart2a.trans hpart2b
  have hpow_bound : h ^ α ≤ v ^ (1 / γ) * (co ^ (α / γ) * u ^ α) := by
    have hsplit : (h ^ betaAG α γ) ^ ((α + 1) / γ) = h ^ α := by
      rw [← Real.rpow_mul hh0.le]
      congr 1
      rw [hβeq]
      have hden_ne : α + 1 ≠ 0 := by linarith
      field_simp [hγpos.ne', hden_ne]
    calc
      h ^ α = (h ^ betaAG α γ) ^ ((α + 1) / γ) := hsplit.symm
      _ = (h ^ betaAG α γ) ^ (1 / γ + α / γ) := by
        congr 1
        ring
      _ = (h ^ betaAG α γ) ^ (1 / γ) * (h ^ betaAG α γ) ^ (α / γ) := by
        rw [Real.rpow_add hq_pos]
      _ ≤ v ^ (1 / γ) * (co ^ (α / γ) * u ^ α) := by
        exact mul_le_mul hpart1 hpart2
          (Real.rpow_nonneg hq_nonneg _) hvpow_nonneg
  have hmul1 : cB * h ^ α ≤ (Co * co ^ (-(α / γ))) * h ^ α := by
    exact mul_le_mul_of_nonneg_right hcB (Real.rpow_nonneg hh0.le _)
  have hmul2 : (Co * co ^ (-(α / γ))) * h ^ α ≤
      (Co * co ^ (-(α / γ))) *
        (v ^ (1 / γ) * (co ^ (α / γ) * u ^ α)) := by
    have hcoef_nonneg : 0 ≤ Co * co ^ (-(α / γ)) := by positivity
    exact mul_le_mul_of_nonneg_left hpow_bound hcoef_nonneg
  have hcancel : co ^ (-(α / γ)) * co ^ (α / γ) = 1 := by
    rw [← Real.rpow_add hco]
    have : -(α / γ) + α / γ = (0 : ℝ) := by ring
    rw [this]
    simp
  calc
    cB * h ^ α ≤ (Co * co ^ (-(α / γ))) * h ^ α := hmul1
    _ ≤ (Co * co ^ (-(α / γ))) *
        (v ^ (1 / γ) * (co ^ (α / γ) * u ^ α)) := hmul2
    _ = Co * u ^ α * v ^ (1 / γ) := by
      rw [show (Co * co ^ (-(α / γ))) *
            (v ^ (1 / γ) * (co ^ (α / γ) * u ^ α)) =
          Co * (co ^ (-(α / γ)) * co ^ (α / γ)) *
            (u ^ α * v ^ (1 / γ)) by ring]
      rw [hcancel]
      ring

lemma activeBlock_overlap_bound_gzero {γ cB Co v : ℝ}
    (hγpos : 0 < γ) (hCo : 0 < Co)
    (hcB : cB ≤ Co * (4 : ℝ) ^ (-(1 / γ)))
    (hv : (1 / 4 : ℝ) ≤ v) :
    cB ≤ Co * v ^ (1 / γ) := by
  have hqpos : 0 < (1 / 4 : ℝ) := by norm_num
  have hpow : (4 : ℝ) ^ (-(1 / γ)) = (1 / 4 : ℝ) ^ (1 / γ) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hmono : (4 : ℝ) ^ (-(1 / γ)) ≤ v ^ (1 / γ) := by
    rw [hpow]
    exact Real.rpow_le_rpow hqpos.le hv (by positivity : 0 ≤ 1 / γ)
  calc
    cB ≤ Co * (4 : ℝ) ^ (-(1 / γ)) := hcB
    _ ≤ Co * v ^ (1 / γ) := mul_le_mul_of_nonneg_left hmono hCo.le

-- @node: def:two-point-witness
/-- Explicit two-point least-favorable law `P_{n,σ}` on `𝒳=ℝ` with covariate
marginal Lebesgue on `[0,1]`, active block `B_n=[0, c_B h_n^α]`, weak-arm
propensity `q_n` on `B_n`, charged treated cell carrying contrast `σ h_n`, and
off-block contrast `τ_0=(u_0+2)/2 ∈ (u_0,2)`. The weak-arm scale is EXACTLY the
displayed `q_n = qLower α γ n` (`= 1/4` if `β_{α,γ}=0`, else `h_n^{β_{α,γ}}`),
which lies in `(0,1/2]` for all large `n`; the constants admissibility
`8 c_B c_Q < log 5` (`c_Q = 1` here) is carried by the divergence lemma. -/
noncomputable def twoPointWitness (α γ u0 cB : ℝ) (n : ℕ) (σ : ℝ) :
    ObservedLaw ℝ :=
  let h := hLower α γ n
  let q := qLower α γ n
  let τ0 := (u0 + 2) / 2
  let inBlock : ℝ → Prop := fun x => 0 ≤ x ∧ x ≤ cB * h ^ α
  let prop : ℝ → ℝ := fun x => if inBlock x then q else 1 / 2
  let contrast : ℝ → ℝ := fun x => if inBlock x then σ * h else τ0
  let mu0 : ℝ → ℝ := fun x => if inBlock x then 0 else -τ0 / 2
  let mu1 : ℝ → ℝ := fun x => if inBlock x then σ * h else τ0 / 2
  let outcome : ℝ → Bool → Measure ℝ := fun x a =>
    if inBlock x then (if a then bernoulliPM (σ * h) else Measure.dirac 0)
    else (if a then bernoulliPM (τ0 / 2) else bernoulliPM (-τ0 / 2))
  { dataMeasure :=
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).bind fun x =>
        (bernoulliBool (prop x)).bind fun a =>
          (outcome x a).map (Observation.mk x a))
    PX := volume.restrict (Set.Icc (0 : ℝ) 1)
    contrast := contrast
    propensity := prop
    mu0 := mu0
    mu1 := mu1 }

lemma twoPointWitness_optimal_plus (α γ u0 cB : ℝ) {n : ℕ}
    (hn1 : 1 ≤ n) (hwin : MarginWindow u0) :
    ∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true := by
  intro x
  unfold lawOptimalPolicy optimalPolicy
  have hh_nonneg : 0 ≤ hLower α γ n := by
    have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    exact (hLower_pos_of_pos_nat α γ hnpos).le
  have hτ0_nonneg : 0 ≤ (u0 + 2) / 2 := by linarith [hwin.1]
  by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
  · simp [twoPointWitness, hxB, hh_nonneg]
  · simp [twoPointWitness, hxB, hτ0_nonneg]

lemma twoPointWitness_optimal_minus (α γ u0 cB : ℝ) {n : ℕ}
    (hn1 : 1 ≤ n) (hwin : MarginWindow u0) :
    ∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
      ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α) := by
  intro x
  unfold lawOptimalPolicy optimalPolicy
  have hh_pos : 0 < hLower α γ n := by
    have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    exact hLower_pos_of_pos_nat α γ hnpos
  have hτ0_nonneg : 0 ≤ (u0 + 2) / 2 := by linarith [hwin.1]
  by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
  · simp [twoPointWitness, hxB, not_le.mpr (neg_neg_of_pos hh_pos)]
  · simp [twoPointWitness, hxB, hτ0_nonneg]

lemma twoPointWitness_positivity (α γ u0 cB σ : ℝ) (n : ℕ)
    (hq : 0 < qLower α γ n ∧ qLower α γ n ≤ 1 / 2) :
    Positivity (twoPointWitness α γ u0 cB n σ) := by
  exact Filter.Eventually.of_forall fun x => by
    by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
    · simp [twoPointWitness, hxB]
      constructor
      · exact hq.1
      · linarith [hq.2]
    · simp [twoPointWitness, hxB]
      norm_num

lemma twoPointWitness_strictOverlapEndpoint (α γ u0 cB underlineP σ : ℝ) (n : ℕ)
    (hq : 0 < qLower α γ n ∧ qLower α γ n ≤ 1 / 2)
    (hup : 0 < underlineP) (huple : underlineP ≤ 1 / 4) :
    StrictOverlapEndpoint (twoPointWitness α γ u0 cB n σ) γ underlineP := by
  intro hγ0
  have hq_eq_quarter : qLower α γ n = (1 / 4 : ℝ) := by
    simp [qLower, betaAG, hγ0]
  refine ⟨hup, by linarith, ?_⟩
  exact Filter.Eventually.of_forall fun x => by
    by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
    · simp [overlap, twoPointWitness, hxB]
      constructor
      · rw [hq_eq_quarter]
        exact huple
      · rw [hq_eq_quarter]
        linarith
    · simp [overlap, twoPointWitness, hxB]
      norm_num
      linarith

lemma twoPointWitness_zeroEffect (α γ u0 cB : ℝ) (policySet : Set (Policy ℝ))
    {n : ℕ} (σ : ℝ) (hn1 : 1 ≤ n) (hwin : MarginWindow u0)
    (hσ : σ = 1 ∨ σ = -1) :
    ZeroEffectRegular (twoPointWitness α γ u0 cB n σ) policySet := by
  left
  let P : ObservedLaw ℝ := twoPointWitness α γ u0 cB n σ
  change P.PX.real {x | P.contrast x = 0} = 0
  have hh_pos : 0 < hLower α γ n := by
    have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    exact hLower_pos_of_pos_nat α γ hnpos
  have hτ0_pos : 0 < (u0 + 2) / 2 := by linarith [hwin.1]
  have hzero_empty : {x | P.contrast x = 0} = ∅ := by
    ext x
    constructor
    · intro hx
      change P.contrast x = 0 at hx
      by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
      · have hc : P.contrast x = σ * hLower α γ n := by
          simp [P, twoPointWitness, hxB]
        rw [hc] at hx
        rcases hσ with rfl | rfl
        · linarith
        · linarith
      · have hc : P.contrast x = (u0 + 2) / 2 := by
          simp [P, twoPointWitness, hxB]
        rw [hc] at hx
        linarith
    · intro hx
      cases hx
  rw [hzero_empty, measureReal_empty]

lemma twoPointWitness_marginTail (α γ u0 cB Cm : ℝ) {n : ℕ} (σ : ℝ)
    (hα : 0 ≤ α) (hwin : MarginWindow u0) (hCm : 0 < Cm) (hcB : 0 < cB)
    (hcBm : cB ≤ Cm) (hn1 : 1 ≤ n) (hσ : σ = 1 ∨ σ = -1) :
    MarginTail (twoPointWitness α γ u0 cB n σ) Cm α u0 := by
  refine ⟨hα, hCm, hwin.1, ?_⟩
  intro u hu hu_le
  let P : ObservedLaw ℝ := twoPointWitness α γ u0 cB n σ
  let h : ℝ := hLower α γ n
  let B : Set ℝ := Set.Icc (0 : ℝ) (cB * h ^ α)
  let E : Set ℝ := {x | 0 < |P.contrast x| ∧ |P.contrast x| ≤ u}
  change P.PX.real E ≤ Cm * u ^ α
  have hnposNat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hh_pos : 0 < h := by simpa [h] using hLower_pos_of_pos_nat α γ hnposNat
  have hsig_abs : |σ * h| = h := by
    rcases hσ with rfl | rfl
    · simp [abs_of_pos hh_pos]
    · simp [abs_of_pos hh_pos]
  have hτ0_pos : 0 < (u0 + 2) / 2 := by linarith [hwin.1]
  have hτ0_gt : u0 < (u0 + 2) / 2 := by linarith [hwin.2]
  have hprobPX : IsProbabilityMeasure P.PX := by
    simpa [P, twoPointWitness] using restricted_volume_Icc01_isProbabilityMeasure
  letI : IsProbabilityMeasure P.PX := hprobPX
  have hB_nonneg : 0 ≤ cB * h ^ α :=
    mul_nonneg hcB.le (Real.rpow_nonneg hh_pos.le _)
  have hsubsetB : E ⊆ B := by
    intro x hx
    by_contra hxB
    have hxBpred : ¬ (0 ≤ x ∧ x ≤ cB * h ^ α) := by simpa [B] using hxB
    have hcontrast_off : P.contrast x = (u0 + 2) / 2 := by
      simp [P, twoPointWitness, h, hxBpred]
    have hτ0_le_u : (u0 + 2) / 2 ≤ u := by
      have := hx.2
      rw [hcontrast_off] at this
      simpa [abs_of_pos hτ0_pos] using this
    linarith
  have hBmass : P.PX.real B ≤ cB * h ^ α := by
    have hbase := restricted_volume_real_Icc_zero_le (a := cB * h ^ α) hB_nonneg
    simpa [P, twoPointWitness, B, h] using hbase
  have hmass : P.PX.real E ≤ cB * h ^ α :=
    (measureReal_mono (μ := P.PX) hsubsetB (measure_ne_top P.PX B)).trans hBmass
  by_cases hhu : h ≤ u
  · have hhpow : h ^ α ≤ u ^ α := Real.rpow_le_rpow hh_pos.le hhu hα
    calc
      P.PX.real E ≤ cB * h ^ α := hmass
      _ ≤ cB * u ^ α := mul_le_mul_of_nonneg_left hhpow hcB.le
      _ ≤ Cm * u ^ α := mul_le_mul_of_nonneg_right hcBm (Real.rpow_nonneg hu.le _)
  · have hEempty : E = ∅ := by
      ext x
      constructor
      · intro hx
        have hxB : x ∈ B := hsubsetB hx
        have hxBpred : 0 ≤ x ∧ x ≤ cB * h ^ α := by simpa [B] using hxB
        have hcontrast_on : P.contrast x = σ * h := by
          simp [P, twoPointWitness, h, hxBpred]
        have hle : h ≤ u := by
          have := hx.2
          rw [hcontrast_on, hsig_abs] at this
          exact this
        exact False.elim (hhu hle)
      · intro hx
        cases hx
    rw [hEempty, measureReal_empty]
    exact mul_nonneg hCm.le (Real.rpow_nonneg hu.le _)

lemma twoPointWitness_boundedOutcome (α γ u0 cB σ : ℝ) {n : ℕ}
    (hwin : MarginWindow u0) (hn1 : 1 ≤ n)
    (hh_le_half : hLower α γ n ≤ 1 / 2) (hσ : σ = 1 ∨ σ = -1) :
    BoundedOutcome (twoPointWitness α γ u0 cB n σ) := by
  let h : ℝ := hLower α γ n
  let q : ℝ := qLower α γ n
  let τ0 : ℝ := (u0 + 2) / 2
  let inBlock : ℝ → Prop := fun x => 0 ≤ x ∧ x ≤ cB * h ^ α
  let prop : ℝ → ℝ := fun x => if inBlock x then q else 1 / 2
  let outcome : ℝ → Bool → Measure ℝ := fun x a =>
    if inBlock x then (if a then bernoulliPM (σ * h) else Measure.dirac 0)
    else (if a then bernoulliPM (τ0 / 2) else bernoulliPM (-τ0 / 2))
  let m : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hbad_meas : MeasurableSet {O : Observation ℝ | O.Y ∉ Set.Icc (-1 : ℝ) 1} := by
    exact measurableSet_Icc.compl.preimage measurable_observation_Y
  have hout_bad : ∀ x a, outcome x a {y | y ∉ Set.Icc (-1 : ℝ) 1} = 0 := by
    intro x a
    by_cases hxB : inBlock x
    · dsimp [outcome]
      simp [hxB]
      by_cases ha : a
      · simpa [ha, Set.mem_Icc] using bernoulliPM_bad_support_zero (σ * h)
      · simp [ha]
    · dsimp [outcome]
      simp [hxB]
      by_cases ha : a
      · simpa [ha, Set.mem_Icc] using bernoulliPM_bad_support_zero (τ0 / 2)
      · simpa [ha, Set.mem_Icc] using bernoulliPM_bad_support_zero (-τ0 / 2)
  have hbad_zero :
      ((m.bind fun x => (bernoulliBool (prop x)).bind fun a =>
        (outcome x a).map (Observation.mk x a)) {O | O.Y ∉ Set.Icc (-1 : ℝ) 1}) = 0 := by
    have ha_zero : ∀ x a,
        ((outcome x a).map (Observation.mk x a)) {O | O.Y ∉ Set.Icc (-1 : ℝ) 1} = 0 := by
      intro x a
      rw [Measure.map_apply (measurable_observation_mk x a) hbad_meas]
      simpa using hout_bad x a
    have ha_zero' : ∀ x a,
        ((outcome x a).map (Observation.mk x a)) {O | -1 ≤ O.Y → 1 < O.Y} = 0 := by
      intro x a
      simpa [Set.mem_Icc] using ha_zero x a
    apply le_antisymm
    · calc
        ((m.bind fun x => (bernoulliBool (prop x)).bind fun a =>
          (outcome x a).map (Observation.mk x a)) {O | O.Y ∉ Set.Icc (-1 : ℝ) 1})
            ≤ ∫⁻ x, (((bernoulliBool (prop x)).bind fun a =>
                (outcome x a).map (Observation.mk x a))
                {O | O.Y ∉ Set.Icc (-1 : ℝ) 1}) ∂m :=
              Measure.bind_apply_le _ hbad_meas
        _ ≤ ∫⁻ x, ∫⁻ a,
              (((outcome x a).map (Observation.mk x a))
                {O | O.Y ∉ Set.Icc (-1 : ℝ) 1}) ∂bernoulliBool (prop x) ∂m := by
              exact lintegral_mono fun x => Measure.bind_apply_le _ hbad_meas
        _ = 0 := by simp [ha_zero']
    · exact bot_le
  constructor
  · rw [ae_iff]
    simpa [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m] using hbad_zero
  · intro x
    by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
    · constructor
      · simp [twoPointWitness, hxB]
      · have hh_pos : 0 < hLower α γ n := by
          have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
          exact hLower_pos_of_pos_nat α γ hnpos
        have habs : |σ * hLower α γ n| = hLower α γ n := by
          rcases hσ with rfl | rfl
          · simp [abs_of_pos hh_pos]
          · simp [abs_of_pos hh_pos]
        have hle : |σ * hLower α γ n| ≤ 1 := by rw [habs]; linarith
        simpa [twoPointWitness, hxB] using
          (show (σ * hLower α γ n) ∈ Set.Icc (-1 : ℝ) 1 from
            ⟨(abs_le.mp hle).1, (abs_le.mp hle).2⟩)
    · constructor
      · have hτlo : -1 ≤ -((u0 + 2) / 2) / 2 := by linarith [hwin.2]
        have hτhi : -((u0 + 2) / 2) / 2 ≤ 1 := by linarith [hwin.1]
        simpa [twoPointWitness, hxB] using
          (show (-((u0 + 2) / 2) / 2) ∈ Set.Icc (-1 : ℝ) 1 from ⟨hτlo, hτhi⟩)
      · have hτlo : -1 ≤ ((u0 + 2) / 2) / 2 := by linarith [hwin.1]
        have hτhi : ((u0 + 2) / 2) / 2 ≤ 1 := by linarith [hwin.2]
        simpa [twoPointWitness, hxB] using
          (show (((u0 + 2) / 2) / 2) ∈ Set.Icc (-1 : ℝ) 1 from ⟨hτlo, hτhi⟩)

lemma twoPointWitness_wellFormed (α γ u0 cB σ : ℝ) {n : ℕ}
    (hwin : MarginWindow u0) (hn1 : 1 ≤ n)
    (hh_le_half : hLower α γ n ≤ 1 / 2) (hσ : σ = 1 ∨ σ = -1)
    (hq : 0 < qLower α γ n ∧ qLower α γ n ≤ 1 / 2) :
    WellFormedLaw (twoPointWitness α γ u0 cB n σ) := by
  classical
  let h : ℝ := hLower α γ n
  let q : ℝ := qLower α γ n
  let τ0 : ℝ := (u0 + 2) / 2
  let inBlock : ℝ → Prop := fun x => 0 ≤ x ∧ x ≤ cB * h ^ α
  let prop : ℝ → ℝ := fun x => if inBlock x then q else 1 / 2
  let contrast : ℝ → ℝ := fun x => if inBlock x then σ * h else τ0
  let mu0 : ℝ → ℝ := fun x => if inBlock x then 0 else -τ0 / 2
  let mu1 : ℝ → ℝ := fun x => if inBlock x then σ * h else τ0 / 2
  let outcome : ℝ → Bool → Measure ℝ := fun x a =>
    if inBlock x then (if a then bernoulliPM (σ * h) else Measure.dirac 0)
    else (if a then bernoulliPM (τ0 / 2) else bernoulliPM (-τ0 / 2))
  let m : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let data : Measure (Observation ℝ) :=
    m.bind fun x => (bernoulliBool (prop x)).bind fun a =>
      (outcome x a).map (Observation.mk x a)
  have hmprob : IsProbabilityMeasure m := by
    simpa [m] using restricted_volume_Icc01_isProbabilityMeasure
  letI : IsProbabilityMeasure m := hmprob
  have hprop_bounds : ∀ x, 0 ≤ prop x ∧ prop x ≤ 1 := by
    intro x
    by_cases hxB : inBlock x
    · simp [prop, hxB]
      exact ⟨hq.1.le, hq.2.trans (by norm_num)⟩
    · simp [prop, hxB]
      norm_num
  have hp1 : ∀ x, IsProbabilityMeasure (bernoulliBool (prop x)) := by
    intro x
    exact bernoulliBool_isProbabilityMeasure (hprop_bounds x).1 (hprop_bounds x).2
  have hBmeas : MeasurableSet {x | inBlock x} := by
    dsimp [inBlock]
    exact measurableSet_Icc
  have hprop_meas : Measurable prop := by
    dsimp [prop]
    exact Measurable.ite hBmeas measurable_const measurable_const
  have hcontrast_meas : Measurable contrast := by
    dsimp [contrast]
    exact Measurable.ite hBmeas measurable_const measurable_const
  have hmu0_meas : Measurable mu0 := by
    dsimp [mu0]
    exact Measurable.ite hBmeas measurable_const measurable_const
  have hmu1_meas : Measurable mu1 := by
    dsimp [mu1]
    exact Measurable.ite hBmeas measurable_const measurable_const
  have hnposNat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hh_pos : 0 < h := by
    simpa [h] using hLower_pos_of_pos_nat α γ hnposNat
  have hsig_abs : |σ * h| = h := by
    rcases hσ with rfl | rfl
    · simp [abs_of_pos hh_pos]
    · simp [abs_of_pos hh_pos]
  have hsig_le : |σ * h| ≤ 1 := by
    rw [hsig_abs]
    linarith
  have hp2 : ∀ x a, IsProbabilityMeasure (outcome x a) := by
    intro x a
    by_cases hxB : inBlock x
    · by_cases ha : a
      · dsimp [outcome]
        simp [hxB, ha]
        exact bernoulliPM_isProbabilityMeasure (abs_le.mp hsig_le).1
          (abs_le.mp hsig_le).2
      · dsimp [outcome]
        simpa [hxB, ha] using
          (show IsProbabilityMeasure (Measure.dirac (0 : ℝ)) by infer_instance)
    · by_cases ha : a
      · dsimp [outcome]
        simp [hxB, ha]
        have hlo : -1 ≤ τ0 / 2 := by dsimp [τ0]; linarith [hwin.1]
        have hhi : τ0 / 2 ≤ 1 := by dsimp [τ0]; linarith [hwin.2]
        exact bernoulliPM_isProbabilityMeasure hlo hhi
      · dsimp [outcome]
        simp [hxB, ha]
        have hlo : -1 ≤ -τ0 / 2 := by dsimp [τ0]; linarith [hwin.2]
        have hhi : -τ0 / 2 ≤ 1 := by dsimp [τ0]; linarith [hwin.1]
        exact bernoulliPM_isProbabilityMeasure hlo hhi
  have hκ1 : Measurable (fun x : ℝ => bernoulliBool (prop x)) := by
    exact measurable_bernoulliBool.comp hprop_meas
  have hκ2 : Measurable fun p : ℝ × Bool => outcome p.1 p.2 := by
    dsimp [outcome, inBlock]
    have hBprod : MeasurableSet {p : ℝ × Bool | 0 ≤ p.1 ∧ p.1 ≤ cB * h ^ α} :=
      measurableSet_Icc.preimage measurable_fst
    have hAtrue : MeasurableSet {p : ℝ × Bool | p.2 = true} :=
      (measurableSet_singleton true).preimage measurable_snd
    have hOn : Measurable fun p : ℝ × Bool =>
        if p.2 = true then bernoulliPM (σ * h) else (Measure.dirac (0 : ℝ) : Measure ℝ) := by
      exact Measurable.ite hAtrue
        (show Measurable (fun _ : ℝ × Bool => bernoulliPM (σ * h)) from measurable_const)
        (show Measurable (fun _ : ℝ × Bool => (Measure.dirac (0 : ℝ) : Measure ℝ)) from
          measurable_const)
    have hOff : Measurable fun p : ℝ × Bool =>
        if p.2 = true then bernoulliPM (τ0 / 2) else bernoulliPM (-τ0 / 2) := by
      exact Measurable.ite hAtrue
        (show Measurable (fun _ : ℝ × Bool => bernoulliPM (τ0 / 2)) from measurable_const)
        (show Measurable (fun _ : ℝ × Bool => bernoulliPM (-τ0 / 2)) from measurable_const)
    exact Measurable.ite hBprod hOn hOff
  have hg : ∀ (x : ℝ) (a : Bool), Measurable (fun y : ℝ => Observation.mk x a y) := by
    intro x a
    exact measurable_observation_mk x a
  have hmap : ∀ (x : ℝ), Measurable fun a : Bool =>
      (outcome x a).map (Observation.mk x a) := by
    intro x
    exact measurable_of_finite _
  have hker : Measurable fun x => (bernoulliBool (prop x)).bind fun a =>
      (outcome x a).map (Observation.mk x a) := by
    rw [show (fun x => (bernoulliBool (prop x)).bind fun a =>
        (outcome x a).map (Observation.mk x a)) =
      (fun x => ENNReal.ofReal (if inBlock x then q else 1 / 2) •
          Measure.map (Observation.mk x true)
            (if inBlock x then bernoulliPM (σ * h) else bernoulliPM (τ0 / 2)) +
        ENNReal.ofReal (1 - (if inBlock x then q else 1 / 2)) •
          Measure.map (Observation.mk x false)
            (if inBlock x then Measure.dirac 0 else bernoulliPM (-τ0 / 2))) by
      funext x
      rw [bernoulliBool_bind]
      simp [outcome, prop]]
    exact twoPointWitness_expanded_kernel_measurable α cB σ h q τ0
  have hdata_prob : IsProbabilityMeasure data := by
    have hmapprob : ∀ x a, IsProbabilityMeasure ((outcome x a).map (Observation.mk x a)) := by
      intro x a
      letI : IsProbabilityMeasure (outcome x a) := hp2 x a
      exact Measure.isProbabilityMeasure_map (hg x a).aemeasurable
    have hinner : ∀ x, IsProbabilityMeasure ((bernoulliBool (prop x)).bind fun a =>
        (outcome x a).map (Observation.mk x a)) := by
      intro x
      letI : IsProbabilityMeasure (bernoulliBool (prop x)) := hp1 x
      exact isProbabilityMeasure_bind (hmap x).aemeasurable
        (Filter.Eventually.of_forall fun a => hmapprob x a)
    change IsProbabilityMeasure (m.bind fun x => (bernoulliBool (prop x)).bind fun a =>
      (outcome x a).map (Observation.mk x a))
    exact isProbabilityMeasure_bind hker.aemeasurable
      (Filter.Eventually.of_forall fun x => hinner x)
  have hmapX : data.map (fun O : Observation ℝ => O.X) = m := by
    have hmap_eq := Causalean.Mathlib.MeasureTheory.map_bind_bind_map_proj
      (m := m)
      (κ₁ := fun x : ℝ => bernoulliBool (prop x))
      (κ₂ := outcome)
      (g := fun x a y => Observation.mk x a y)
      (π := fun O : Observation ℝ => O.X)
      hκ1 hp1 hκ2 hp2 hg hmap hker measurable_observation_X
      (by intro x a y; rfl)
    simpa [data] using hmap_eq
  have hmu1_abs : ∀ x, |mu1 x| ≤ 1 := by
    intro x
    by_cases hxB : inBlock x
    · simp [mu1, hxB, hsig_abs]
      linarith
    · dsimp [mu1]
      simp [hxB]
      have hlo : -1 ≤ τ0 / 2 := by dsimp [τ0]; linarith [hwin.1]
      have hhi : τ0 / 2 ≤ 1 := by dsimp [τ0]; linarith [hwin.2]
      exact abs_le.mpr ⟨hlo, hhi⟩
  have hmu0_abs : ∀ x, |mu0 x| ≤ 1 := by
    intro x
    by_cases hxB : inBlock x
    · simp [mu0, hxB]
    · dsimp [mu0]
      simp [hxB]
      have hlo : -1 ≤ -τ0 / 2 := by dsimp [τ0]; linarith [hwin.2]
      have hhi : -τ0 / 2 ≤ 1 := by dsimp [τ0]; linarith [hwin.1]
      exact abs_le.mpr ⟨hlo, hhi⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m, data] using hdata_prob
  · simpa [twoPointWitness, m] using hmprob
  · simpa [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m, data] using hmapX
  · simpa [twoPointWitness, h, q, τ0, inBlock, contrast] using hcontrast_meas
  · simpa [twoPointWitness, h, q, τ0, inBlock, prop] using hprop_meas
  · simpa [twoPointWitness, h, q, τ0, inBlock, mu0] using hmu0_meas
  · simpa [twoPointWitness, h, q, τ0, inBlock, mu1] using hmu1_meas
  · intro x
    by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
    · simp [twoPointWitness, hxB]
    · simp [twoPointWitness, hxB]
      ring
  · intro x
    by_cases hxB : 0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α
    · simp [twoPointWitness, hxB]
      exact ⟨hq.1.le, hq.2.trans (by norm_num)⟩
    · simp [twoPointWitness, hxB]
      norm_num
  · intro φ hφmeas hφbdd
    let f : Observation ℝ → ℝ := fun O => boolIndicator O.A * φ O.X
    have hfmeas : Measurable f := by
      exact ((measurable_of_finite (fun b : Bool => boolIndicator b)).comp
        measurable_observation_A).mul (hφmeas.comp measurable_observation_X)
    rcases hφbdd with ⟨M, hM⟩
    have hMnonneg : 0 ≤ M := (abs_nonneg (φ 0)).trans (hM 0)
    have hfbdd : ∃ M' : ℝ, ∀ O, |f O| ≤ M' := by
      refine ⟨M, ?_⟩
      intro O
      have hb : |boolIndicator O.A| ≤ (1 : ℝ) := by
        cases O.A <;> simp [boolIndicator]
      calc
        |f O| = |boolIndicator O.A| * |φ O.X| := by simp [f, abs_mul]
        _ ≤ 1 * M := mul_le_mul hb (hM O.X) (abs_nonneg _) (by norm_num)
        _ = M := one_mul M
    have hf : Integrable f data := by
      letI : IsProbabilityMeasure data := hdata_prob
      exact integrable_of_measurable_bounded hfmeas hfbdd
    have hinner_const : ∀ x a,
        ∫ y, f (Observation.mk x a y) ∂outcome x a = boolIndicator a * φ x := by
      intro x a
      letI : IsProbabilityMeasure (outcome x a) := hp2 x a
      simp [f]
    have hf₂ : ∀ᵐ x ∂m, Integrable
        (fun a => ∫ y, f (Observation.mk x a y) ∂outcome x a)
        (bernoulliBool (prop x)) := by
      exact Filter.Eventually.of_forall fun x => by
        letI : IsProbabilityMeasure (bernoulliBool (prop x)) := hp1 x
        exact Integrable.of_finite
    have hf' : Integrable
        (fun x => ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
          ∂bernoulliBool (prop x)) m := by
      have hcollapse_point :
          (fun x => ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
              ∂bernoulliBool (prop x)) =
            fun x => prop x * φ x := by
        funext x
        rw [bernoulliBool_integral (hprop_bounds x).1 (hprop_bounds x).2]
        simp [hinner_const, boolIndicator]
      rw [hcollapse_point]
      have hmeas : Measurable (fun x => prop x * φ x) := by
        exact hprop_meas.mul hφmeas
      have hbdd : ∃ M' : ℝ, ∀ x, |prop x * φ x| ≤ M' := by
        refine ⟨M, ?_⟩
        intro x
        have hp_nonneg := (hprop_bounds x).1
        have hp_le := (hprop_bounds x).2
        have hpabs : |prop x| ≤ 1 := by rwa [abs_of_nonneg hp_nonneg]
        calc
          |prop x * φ x| = |prop x| * |φ x| := abs_mul _ _
          _ ≤ 1 * M := mul_le_mul hpabs (hM x) (abs_nonneg _) (by norm_num)
          _ = M := one_mul M
      exact integrable_of_measurable_bounded hmeas hbdd
    have hcollapse := Causalean.Mathlib.MeasureTheory.integral_bind_bind_map
      (m := m) (κ₁ := fun x : ℝ => bernoulliBool (prop x)) (κ₂ := outcome)
      (g := fun x a y => Observation.mk x a y) (f := f)
      hκ1 hκ2 hg hmap hker hf hf₂ hf'
    calc
      ∫ O, boolIndicator O.A * φ O.X ∂(twoPointWitness α γ u0 cB n σ).dataMeasure
          = ∫ O, f O ∂data := by
            simp [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m, data, f]
      _ = ∫ x, ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
            ∂bernoulliBool (prop x) ∂m := hcollapse
      _ = ∫ x, prop x * φ x ∂m := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
              ∂bernoulliBool (prop x)) = prop x * φ x
          rw [bernoulliBool_integral (hprop_bounds x).1 (hprop_bounds x).2]
          simp [hinner_const, boolIndicator]
      _ = ∫ x, (twoPointWitness α γ u0 cB n σ).propensity x * φ x
            ∂(twoPointWitness α γ u0 cB n σ).PX := by
        simp [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m]
  · intro φ hφmeas hφbdd
    let f : Observation ℝ → ℝ := fun O => boolIndicator O.A * O.Y * φ O.X
    have hbdd := twoPointWitness_boundedOutcome α γ u0 cB σ hwin hn1 hh_le_half hσ
    have hYae : ∀ᵐ O ∂data, O.Y ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m, data] using hbdd.1
    have hfmeas : Measurable f := by
      exact (((measurable_of_finite (fun b : Bool => boolIndicator b)).comp
        measurable_observation_A).mul measurable_observation_Y).mul
        (hφmeas.comp measurable_observation_X)
    rcases hφbdd with ⟨M, hM⟩
    have hMnonneg : 0 ≤ M := (abs_nonneg (φ 0)).trans (hM 0)
    have hf : Integrable f data := by
      letI : IsProbabilityMeasure data := hdata_prob
      refine Integrable.of_bound hfmeas.aestronglyMeasurable M ?_
      exact hYae.mono fun O hY => by
        have hb : |boolIndicator O.A| ≤ (1 : ℝ) := by
          cases O.A <;> simp [boolIndicator]
        have hYabs : |O.Y| ≤ (1 : ℝ) := abs_le.mpr hY
        have hprod1 : |boolIndicator O.A| * |O.Y| ≤ 1 * 1 :=
          mul_le_mul hb hYabs (abs_nonneg _) (by norm_num)
        have hprod2 : |boolIndicator O.A| * |O.Y| * |φ O.X| ≤ (1 * 1) * M :=
          mul_le_mul hprod1 (hM O.X) (abs_nonneg _)
            (mul_nonneg (by norm_num) (by norm_num))
        simpa [f, Real.norm_eq_abs, abs_mul, mul_assoc] using hprod2
    have hinner_const : ∀ x a,
        ∫ y, f (Observation.mk x a y) ∂outcome x a =
          boolIndicator a * mu1 x * φ x := by
      intro x a
      by_cases hxB : inBlock x
      · by_cases ha : a
        · dsimp [f, outcome, mu1]
          simp [hxB, ha, boolIndicator]
          rw [integral_mul_const]
          rw [bernoulliPM_mean (abs_le.mp hsig_le).1 (abs_le.mp hsig_le).2]
        · dsimp [f, outcome, mu1]
          simp [hxB, ha, boolIndicator]
      · by_cases ha : a
        · dsimp [f, outcome, mu1]
          simp [hxB, ha, boolIndicator]
          rw [integral_mul_const]
          have hlo : -1 ≤ τ0 / 2 := by dsimp [τ0]; linarith [hwin.1]
          have hhi : τ0 / 2 ≤ 1 := by dsimp [τ0]; linarith [hwin.2]
          rw [bernoulliPM_mean hlo hhi]
        · dsimp [f, outcome, mu1]
          simp [hxB, ha, boolIndicator]
    have hf₂ : ∀ᵐ x ∂m, Integrable
        (fun a => ∫ y, f (Observation.mk x a y) ∂outcome x a)
        (bernoulliBool (prop x)) := by
      exact Filter.Eventually.of_forall fun x => by
        letI : IsProbabilityMeasure (bernoulliBool (prop x)) := hp1 x
        exact Integrable.of_finite
    have hf' : Integrable
        (fun x => ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
          ∂bernoulliBool (prop x)) m := by
      have hcollapse_point :
          (fun x => ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
              ∂bernoulliBool (prop x)) =
            fun x => prop x * mu1 x * φ x := by
        funext x
        rw [bernoulliBool_integral (hprop_bounds x).1 (hprop_bounds x).2]
        simp [hinner_const, boolIndicator]
        ring
      rw [hcollapse_point]
      have hmeas : Measurable (fun x => prop x * mu1 x * φ x) := by
        exact (hprop_meas.mul hmu1_meas).mul hφmeas
      have hbdd' : ∃ M' : ℝ, ∀ x, |prop x * mu1 x * φ x| ≤ M' := by
        refine ⟨M, ?_⟩
        intro x
        have hp_nonneg := (hprop_bounds x).1
        have hp_le := (hprop_bounds x).2
        have hpabs : |prop x| ≤ 1 := by rwa [abs_of_nonneg hp_nonneg]
        have hprod1 : |prop x| * |mu1 x| ≤ 1 * 1 :=
          mul_le_mul hpabs (hmu1_abs x) (abs_nonneg _) (by norm_num)
        have hprod2 : |prop x| * |mu1 x| * |φ x| ≤ (1 * 1) * M :=
          mul_le_mul hprod1 (hM x) (abs_nonneg _)
            (mul_nonneg (by norm_num) (by norm_num))
        simpa [abs_mul, mul_assoc] using hprod2
      exact integrable_of_measurable_bounded hmeas hbdd'
    have hcollapse := Causalean.Mathlib.MeasureTheory.integral_bind_bind_map
      (m := m) (κ₁ := fun x : ℝ => bernoulliBool (prop x)) (κ₂ := outcome)
      (g := fun x a y => Observation.mk x a y) (f := f)
      hκ1 hκ2 hg hmap hker hf hf₂ hf'
    calc
      ∫ O, boolIndicator O.A * O.Y * φ O.X
          ∂(twoPointWitness α γ u0 cB n σ).dataMeasure
          = ∫ O, f O ∂data := by
            simp [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m, data, f]
      _ = ∫ x, ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
            ∂bernoulliBool (prop x) ∂m := hcollapse
      _ = ∫ x, prop x * mu1 x * φ x ∂m := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
              ∂bernoulliBool (prop x)) = prop x * mu1 x * φ x
          rw [bernoulliBool_integral (hprop_bounds x).1 (hprop_bounds x).2]
          simp [hinner_const, boolIndicator]
          ring
      _ = ∫ x, (twoPointWitness α γ u0 cB n σ).propensity x *
            (twoPointWitness α γ u0 cB n σ).mu1 x * φ x
            ∂(twoPointWitness α γ u0 cB n σ).PX := by
        simp [twoPointWitness, h, q, τ0, inBlock, prop, mu1, outcome, m]
  · intro φ hφmeas hφbdd
    let f : Observation ℝ → ℝ := fun O => (1 - boolIndicator O.A) * O.Y * φ O.X
    have hbdd := twoPointWitness_boundedOutcome α γ u0 cB σ hwin hn1 hh_le_half hσ
    have hYae : ∀ᵐ O ∂data, O.Y ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m, data] using hbdd.1
    have hfmeas : Measurable f := by
      have hnotA : Measurable (fun O : Observation ℝ => 1 - boolIndicator O.A) :=
        measurable_const.sub
          ((measurable_of_finite (fun b : Bool => boolIndicator b)).comp
            measurable_observation_A)
      exact (hnotA.mul measurable_observation_Y).mul
        (hφmeas.comp measurable_observation_X)
    rcases hφbdd with ⟨M, hM⟩
    have hMnonneg : 0 ≤ M := (abs_nonneg (φ 0)).trans (hM 0)
    have hf : Integrable f data := by
      letI : IsProbabilityMeasure data := hdata_prob
      refine Integrable.of_bound hfmeas.aestronglyMeasurable M ?_
      exact hYae.mono fun O hY => by
        have hb : |1 - boolIndicator O.A| ≤ (1 : ℝ) := by
          cases O.A <;> simp [boolIndicator]
        have hYabs : |O.Y| ≤ (1 : ℝ) := abs_le.mpr hY
        have hprod1 : |1 - boolIndicator O.A| * |O.Y| ≤ 1 * 1 :=
          mul_le_mul hb hYabs (abs_nonneg _) (by norm_num)
        have hprod2 : |1 - boolIndicator O.A| * |O.Y| * |φ O.X| ≤ (1 * 1) * M :=
          mul_le_mul hprod1 (hM O.X) (abs_nonneg _)
            (mul_nonneg (by norm_num) (by norm_num))
        simpa [f, Real.norm_eq_abs, abs_mul, mul_assoc] using hprod2
    have hinner_const : ∀ x a,
        ∫ y, f (Observation.mk x a y) ∂outcome x a =
          (1 - boolIndicator a) * mu0 x * φ x := by
      intro x a
      by_cases hxB : inBlock x
      · by_cases ha : a
        · dsimp [f, outcome, mu0]
          simp [hxB, ha, boolIndicator]
        · dsimp [f, outcome, mu0]
          simp [hxB, ha, boolIndicator]
      · by_cases ha : a
        · dsimp [f, outcome, mu0]
          simp [hxB, ha, boolIndicator]
        · dsimp [f, outcome, mu0]
          simp [hxB, ha, boolIndicator]
          rw [integral_mul_const]
          have hlo : -1 ≤ -τ0 / 2 := by dsimp [τ0]; linarith [hwin.2]
          have hhi : -τ0 / 2 ≤ 1 := by dsimp [τ0]; linarith [hwin.1]
          rw [bernoulliPM_mean hlo hhi]
    have hf₂ : ∀ᵐ x ∂m, Integrable
        (fun a => ∫ y, f (Observation.mk x a y) ∂outcome x a)
        (bernoulliBool (prop x)) := by
      exact Filter.Eventually.of_forall fun x => by
        letI : IsProbabilityMeasure (bernoulliBool (prop x)) := hp1 x
        exact Integrable.of_finite
    have hf' : Integrable
        (fun x => ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
          ∂bernoulliBool (prop x)) m := by
      have hcollapse_point :
          (fun x => ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
              ∂bernoulliBool (prop x)) =
            fun x => (1 - prop x) * mu0 x * φ x := by
        funext x
        rw [bernoulliBool_integral (hprop_bounds x).1 (hprop_bounds x).2]
        simp [hinner_const, boolIndicator]
        ring
      rw [hcollapse_point]
      have hmeas : Measurable (fun x => (1 - prop x) * mu0 x * φ x) := by
        exact ((measurable_const.sub hprop_meas).mul hmu0_meas).mul hφmeas
      have hbdd' : ∃ M' : ℝ, ∀ x, |(1 - prop x) * mu0 x * φ x| ≤ M' := by
        refine ⟨M, ?_⟩
        intro x
        have hp_nonneg := (hprop_bounds x).1
        have hp_le := (hprop_bounds x).2
        have hpabs : |1 - prop x| ≤ 1 := by
          have hnon : 0 ≤ 1 - prop x := by linarith
          rw [abs_of_nonneg hnon]
          linarith
        have hprod1 : |1 - prop x| * |mu0 x| ≤ 1 * 1 :=
          mul_le_mul hpabs (hmu0_abs x) (abs_nonneg _) (by norm_num)
        have hprod2 : |1 - prop x| * |mu0 x| * |φ x| ≤ (1 * 1) * M :=
          mul_le_mul hprod1 (hM x) (abs_nonneg _)
            (mul_nonneg (by norm_num) (by norm_num))
        simpa [abs_mul, mul_assoc] using hprod2
      exact integrable_of_measurable_bounded hmeas hbdd'
    have hcollapse := Causalean.Mathlib.MeasureTheory.integral_bind_bind_map
      (m := m) (κ₁ := fun x : ℝ => bernoulliBool (prop x)) (κ₂ := outcome)
      (g := fun x a y => Observation.mk x a y) (f := f)
      hκ1 hκ2 hg hmap hker hf hf₂ hf'
    calc
      ∫ O, (1 - boolIndicator O.A) * O.Y * φ O.X
          ∂(twoPointWitness α γ u0 cB n σ).dataMeasure
          = ∫ O, f O ∂data := by
            simp [twoPointWitness, h, q, τ0, inBlock, prop, outcome, m, data, f]
      _ = ∫ x, ∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
            ∂bernoulliBool (prop x) ∂m := hcollapse
      _ = ∫ x, (1 - prop x) * mu0 x * φ x ∂m := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (∫ a, ∫ y, f (Observation.mk x a y) ∂outcome x a
              ∂bernoulliBool (prop x)) = (1 - prop x) * mu0 x * φ x
          rw [bernoulliBool_integral (hprop_bounds x).1 (hprop_bounds x).2]
          simp [hinner_const, boolIndicator]
          ring
      _ = ∫ x, (1 - (twoPointWitness α γ u0 cB n σ).propensity x) *
            (twoPointWitness α γ u0 cB n σ).mu0 x * φ x
            ∂(twoPointWitness α γ u0 cB n σ).PX := by
        simp [twoPointWitness, h, q, τ0, inBlock, prop, mu0, outcome, m]

-- @node: lem:witness-membership
/-- `lem:witness-membership`. For all large `n` the two witness laws belong to
`def:law-class`, and the two explicit witness-optimal policies are
`x ↦ 1` (under `P_{n,+}`) and `x ↦ 1{x ∉ B_n}` (under `P_{n,-}`); if these belong
to `Π` they are the two policy actions of the two-point reduction. The membership
is DERIVED from the construction, not assumed. -/
lemma witness_membership (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (Policy ℝ)) (σ : ℝ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hwin : MarginWindow u0)
    (hCm : 0 < Cm) (hCo : 0 < Co) (hco : 0 < co) (hcB : 0 < cB)
    (hcBm : cB ≤ Cm) (hcBo : cB ≤ Co) (hup : 0 < underlineP)
    -- note c_B overlap-decay smallness (def:two-point-witness constant choice)
    (hcB_gpos : 0 < γ → 0 < α → cB ≤ Co * co ^ (-(α / γ)))
    (hcB_gzero : 0 < γ → α = 0 → cB ≤ Co * (4 : ℝ) ^ (-(1 / γ)))
    (huple : underlineP ≤ 1 / 4) (hσ : σ = 1 ∨ σ = -1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      LawClass α γ Cm u0 Co co underlineP policySet
        (twoPointWitness α γ u0 cB n σ) ∧
      (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true) ∧
      (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
        ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α))
    := by
  /-
  The note's active-block overlap-decay verification needs exactly `hcBo`,
  `hcB_gpos`, and `hcB_gzero`: for `γ = 0` the block mass is controlled by
  `cB ≤ Co`; for `0 < γ, 0 < α` by
  `cB ≤ Co * co ^ (-(α / γ))`; and for `0 < γ, α = 0` by
  `cB ≤ Co * 4 ^ (-(1 / γ))`.

  The `OverlapDecay` window now includes the required hypothesis `u ≤ u0`.
  Since the off-block contrast is `(u0 + 2) / 2 > u0`, every admissible
  overlap-decay event is confined to the active block.  The remaining
  calculation is the active-block mass/exponent split used in the note:
  `γ=0` by `hcBo`, `γ>0, α>0` by `hcB_gpos` and
  `(α+1) * betaAG α γ / γ = α`, and `γ>0, α=0` by `hcB_gzero`.
  -/
  classical
    have hod_eventually :
        ∀ᶠ n : ℕ in Filter.atTop,
          OverlapDecay (twoPointWitness α γ u0 cB n σ) u0 Co co α γ := by
    /-
    For `0 < u ≤ u0`, the off-block branch has contrast
    `τ0 = (u0 + 2) / 2 > u0`, so the event cannot contain off-block points.
      What remains is the active block `B_n`, with mass `cB * hLower α γ n ^ α`
      and overlap scale `qLower α γ n`.  The three note cases listed above
      discharge the bound.
      -/
      have hh_event := eventually_hLower_le_half α γ hα hγ
      have hq_event := eventually_qLower_pos_le_half α γ hα hγ
      filter_upwards [hh_event, hq_event,
        Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with
        n hh_le_half hq_props hn1
      intro u v hu hu_le hv hv_le
      let P : ObservedLaw ℝ := twoPointWitness α γ u0 cB n σ
      let h : ℝ := hLower α γ n
      let q : ℝ := qLower α γ n
      let B : Set ℝ := Set.Icc (0 : ℝ) (cB * h ^ α)
      let E : Set ℝ :=
        {x | overlap P x ≤ v ∧ 0 < |P.contrast x| ∧ |P.contrast x| ≤ u}
      change P.PX.real E ≤ Co * u ^ α * (if γ = 0 then 1 else v ^ (1 / γ))
      have hnposNat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
      have hh_pos : 0 < h := by
        simpa [h] using hLower_pos_of_pos_nat α γ hnposNat
      have hq_pos : 0 < q := by simpa [q] using hq_props.1
      have hq_le_half : q ≤ (1 / 2 : ℝ) := by simpa [q] using hq_props.2
      have hq_le_one_sub : q ≤ 1 - q := by linarith
      have hsig_abs : |σ * h| = h := by
        rcases hσ with rfl | rfl
        · simp [abs_of_pos hh_pos]
        · simp [abs_of_pos hh_pos]
      have hτ0_pos : 0 < (u0 + 2) / 2 := by linarith [hwin.1]
      have hτ0_gt : u0 < (u0 + 2) / 2 := by linarith [hwin.2]
      have hprobPX : IsProbabilityMeasure P.PX := by
        simpa [P, twoPointWitness] using restricted_volume_Icc01_isProbabilityMeasure
      letI : IsProbabilityMeasure P.PX := hprobPX
      have hB_nonneg : 0 ≤ cB * h ^ α :=
        mul_nonneg hcB.le (Real.rpow_nonneg hh_pos.le _)
      have hsubsetB : E ⊆ B := by
        intro x hx
        by_contra hxB
        have hxBpred : ¬ (0 ≤ x ∧ x ≤ cB * h ^ α) := by
          simpa [B] using hxB
        have hcontrast_off : P.contrast x = (u0 + 2) / 2 := by
          simp [P, twoPointWitness, h, hxBpred]
        have habs : |P.contrast x| ≤ u := hx.2.2
        have hτ0_le_u : (u0 + 2) / 2 ≤ u := by
          rw [hcontrast_off] at habs
          simpa [abs_of_pos hτ0_pos] using habs
        linarith
      have hBmass : P.PX.real B ≤ cB * h ^ α := by
        have hbase := restricted_volume_real_Icc_zero_le (a := cB * h ^ α) hB_nonneg
        simpa [P, twoPointWitness, B, h] using hbase
      have hmass : P.PX.real E ≤ cB * h ^ α :=
        (measureReal_mono (μ := P.PX) hsubsetB (measure_ne_top P.PX B)).trans hBmass
      have hrhs_nonneg :
          0 ≤ Co * u ^ α * (if γ = 0 then 1 else v ^ (1 / γ)) := by
          by_cases hγ0 : γ = 0
          · simp [hγ0, mul_nonneg hCo.le (Real.rpow_nonneg hu.le _)]
          · simpa [hγ0] using
              mul_nonneg (mul_nonneg hCo.le (Real.rpow_nonneg hu.le _))
                (Real.rpow_nonneg hv.le _)
      have hE_empty_of_not_hle : ¬ h ≤ u → E = ∅ := by
        intro hnot
        ext x
        constructor
        · intro hx
          have hxB : x ∈ B := hsubsetB hx
          have hxBpred : 0 ≤ x ∧ x ≤ cB * h ^ α := by simpa [B] using hxB
          have hcontrast_on : P.contrast x = σ * h := by
            simp [P, twoPointWitness, h, hxBpred]
          have hle : h ≤ u := by
            have := hx.2.2
            rw [hcontrast_on, hsig_abs] at this
            exact this
          exact False.elim (hnot hle)
        · intro hx
          simp at hx
      have hE_empty_of_not_qle : ¬ q ≤ v → E = ∅ := by
          intro hnot
          ext x
          constructor
          · intro hx
            have hxB : x ∈ B := hsubsetB hx
            have hxBpred : 0 ≤ x ∧ x ≤ cB * h ^ α := by simpa [B] using hxB
            have hoverlap_on : overlap P x = q := by
              simp [P, overlap, twoPointWitness, h, q, hxBpred]
              simpa [q] using hq_le_one_sub
            have hle : q ≤ v := by simpa [hoverlap_on] using hx.1
            exact False.elim (hnot hle)
          · intro hx
            cases hx
      by_cases hγ0 : γ = 0
      · by_cases hhu : h ≤ u
        · have hhpow : h ^ α ≤ u ^ α := Real.rpow_le_rpow hh_pos.le hhu hα
          calc
            P.PX.real E ≤ cB * h ^ α := hmass
            _ ≤ cB * u ^ α := mul_le_mul_of_nonneg_left hhpow hcB.le
            _ ≤ Co * u ^ α := mul_le_mul_of_nonneg_right hcBo
              (Real.rpow_nonneg hu.le _)
            _ = Co * u ^ α * (if γ = 0 then 1 else v ^ (1 / γ)) := by
              simp [hγ0]
        · have hEempty := hE_empty_of_not_hle hhu
          rw [hEempty, measureReal_empty]
          exact hrhs_nonneg
      · have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
        by_cases hhu : h ≤ u
        · by_cases hqv : q ≤ v
          · by_cases hα0 : α = 0
            · have hβ0 : betaAG α γ = 0 := by
                unfold betaAG
                simp [hγ0, hα0]
              have hq_eq : q = (1 / 4 : ℝ) := by
                simp [q, qLower, hβ0]
              have hquarter_le_v : (1 / 4 : ℝ) ≤ v := by simpa [hq_eq] using hqv
              have hmass_cB : P.PX.real E ≤ cB := by simpa [hα0] using hmass
              calc
                P.PX.real E ≤ cB := hmass_cB
                _ ≤ Co * v ^ (1 / γ) :=
                  activeBlock_overlap_bound_gzero hγpos hCo
                    (hcB_gzero hγpos hα0) hquarter_le_v
                _ = Co * u ^ α * (if γ = 0 then 1 else v ^ (1 / γ)) := by
                  simp [hγ0, hα0]
            · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
              have hβpos : 0 < betaAG α γ := by
                unfold betaAG
                have hdenpos : 0 < α + 1 := by linarith
                simp [hγ0, div_pos (mul_pos hαpos hγpos) hdenpos]
              have hβne : betaAG α γ ≠ 0 := ne_of_gt hβpos
              have hq_eq : q = h ^ betaAG α γ := by
                simp [q, qLower, h, hβne]
              have hqv' : h ^ betaAG α γ ≤ v := by simpa [hq_eq] using hqv
              calc
                P.PX.real E ≤ cB * h ^ α := hmass
                _ ≤ Co * u ^ α * v ^ (1 / γ) :=
                  activeBlock_overlap_bound_gpos hαpos hγpos hCo hco
                    (hcB_gpos hγpos hαpos) hh_pos hu hv hqv' hv_le
                _ = Co * u ^ α * (if γ = 0 then 1 else v ^ (1 / γ)) := by
                  simp [hγ0]
          · have hEempty := hE_empty_of_not_qle hqv
            rw [hEempty, measureReal_empty]
            exact hrhs_nonneg
        · have hEempty := hE_empty_of_not_hle hhu
          rw [hEempty, measureReal_empty]
          exact hrhs_nonneg
  filter_upwards [hod_eventually, eventually_hLower_le_half α γ hα hγ,
    eventually_qLower_pos_le_half α γ hα hγ,
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with
    n hod hh_le_half hq_props hn1
  have hrest :
      LawClass α γ Cm u0 Co co underlineP policySet
          (twoPointWitness α γ u0 cB n σ) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
          ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α)) := by
    have hwf : WellFormedLaw (twoPointWitness α γ u0 cB n σ) :=
      twoPointWitness_wellFormed α γ u0 cB σ hwin hn1 hh_le_half hσ hq_props
    have hbdd : BoundedOutcome (twoPointWitness α γ u0 cB n σ) :=
      twoPointWitness_boundedOutcome α γ u0 cB σ hwin hn1 hh_le_half hσ
    have hpos : Positivity (twoPointWitness α γ u0 cB n σ) :=
      twoPointWitness_positivity α γ u0 cB σ n hq_props
    have hmargin : MarginTail (twoPointWitness α γ u0 cB n σ) Cm α u0 :=
      twoPointWitness_marginTail α γ u0 cB Cm σ hα hwin hCm hcB hcBm hn1 hσ
    have hzero : ZeroEffectRegular (twoPointWitness α γ u0 cB n σ) policySet :=
      twoPointWitness_zeroEffect α γ u0 cB policySet σ hn1 hwin hσ
    have hstrict : StrictOverlapEndpoint
        (twoPointWitness α γ u0 cB n σ) γ underlineP :=
      twoPointWitness_strictOverlapEndpoint α γ u0 cB underlineP σ n
        hq_props hup huple
    have hopt_plus := twoPointWitness_optimal_plus α γ u0 cB hn1 hwin
    have hopt_minus := twoPointWitness_optimal_minus α γ u0 cB hn1 hwin
    exact ⟨
      { wf := hwf
        bdd := hbdd
        pos := hpos
        margin := hmargin
        zero := hzero
        overlapDecay := hod
        strict := hstrict },
      hopt_plus, hopt_minus⟩
  rcases hrest with ⟨hclass, hopt_plus, hopt_minus⟩
  exact ⟨{ hclass with overlapDecay := hod }, hopt_plus, hopt_minus⟩

-- @node: lem:three-cell-chiSq-bound
/-- Three-cell χ² bound from proportional restrictions.

The cells are ordered as an off/dummy cell, a charged `Y=1` cell, and a charged
`Y=-1` cell.  If the numerator measure is a constant multiple of the denominator
on each cell, with ratios `1`, `(1+h)/(1-h)`, and `(1-h)/(1+h)`, and the
denominator charged-cell masses are `A(1-h)/2` and `A(1+h)/2`, then the
contribution is bounded by `8 * m * q * h^2` whenever `A ≤ m q` and
`0 ≤ h ≤ 1/2`. -/
lemma chiSqDiv_three_cell_bound_of_restrict
    {Ω : Type*} [MeasurableSpace Ω]
    (Pplus Pminus : Measure Ω) [IsFiniteMeasure Pminus]
    (s : Fin 3 → Set Ω) (A m q h : ℝ)
    (hac : Pplus ≪ Pminus)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ (1 / 2 : ℝ))
    (hA_nonneg : 0 ≤ A)
    (hA_le : A ≤ m * q)
    (hν1 : (Pminus (s 1)).toReal = A * ((1 - h) / 2))
    (hν2 : (Pminus (s 2)).toReal = A * ((1 + h) / 2))
    (hrestrict : ∀ i,
      Pplus.restrict (s i) =
        ENNReal.ofReal
          (if i = 0 then (1 : ℝ)
           else if i = 1 then (1 + h) / (1 - h)
           else (1 - h) / (1 + h)) • Pminus.restrict (s i)) :
    Causalean.Stat.chiSqDiv Pplus Pminus ≤
      8 * m * q * h ^ (2 : ℕ) := by
  classical
  let c : Fin 3 → ℝ := fun i =>
    if i = 0 then (1 : ℝ)
    else if i = 1 then (1 + h) / (1 - h)
    else (1 - h) / (1 + h)
  have hc_nonneg : ∀ i, 0 ≤ c i := by
    intro i
    dsimp [c]
    fin_cases i <;> simp only [Fin.isValue]
    · norm_num
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_nonneg (by linarith) (by linarith)
  have hχ := CausalSmith.Mathlib.ProductChiSquared.chiSqDiv_eq_sum_partition_of_restrict_eq_smul
    Pplus Pminus s c hac hs hdisj hcover hc_nonneg (by
      intro i
      dsimp [c]
      exact hrestrict i)
  have hsum :
      (∑ i : Fin 3, (c i - 1) ^ (2 : ℕ) * (Pminus (s i)).toReal) ≤
        8 * (m * q * h ^ (2 : ℕ)) := by
    rw [Fin.sum_univ_three]
    dsimp [c]
    rw [hν1, hν2]
    have h1ph_pos : 0 < 1 + h := by linarith
    have h1mh_pos : 0 < 1 - h := by linarith
    have hden_pos : 0 < 1 - h ^ (2 : ℕ) := by
      nlinarith [sq_nonneg h, hh1]
    have hbound_factor : 4 / (1 - h ^ (2 : ℕ)) ≤ 8 := by
      have hhalf : (1 : ℝ) / 2 ≤ 1 - h ^ (2 : ℕ) := by
        nlinarith [sq_nonneg h, hh1]
      exact (div_le_iff₀ hden_pos).mpr (by nlinarith)
    have hAh_nonneg : 0 ≤ A * h ^ (2 : ℕ) :=
      mul_nonneg hA_nonneg (sq_nonneg h)
    have hmq_nonneg : 0 ≤ m * q :=
      hA_nonneg.trans hA_le
    have hmqh_nonneg : 0 ≤ m * q * h ^ (2 : ℕ) :=
      mul_nonneg hmq_nonneg (sq_nonneg h)
    have hA_h_le : A * h ^ (2 : ℕ) ≤ m * q * h ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hA_le (sq_nonneg h)
    calc
      ((1 : ℝ) - 1) ^ (2 : ℕ) * (Pminus (s 0)).toReal +
            ((1 + h) / (1 - h) - 1) ^ (2 : ℕ) *
              (A * ((1 - h) / 2)) +
          ((1 - h) / (1 + h) - 1) ^ (2 : ℕ) *
            (A * ((1 + h) / 2))
          = (4 / (1 - h ^ (2 : ℕ))) * (A * h ^ (2 : ℕ)) := by
            field_simp [ne_of_gt h1ph_pos, ne_of_gt h1mh_pos, ne_of_gt hden_pos]
            ring
      _ ≤ 8 * (A * h ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hbound_factor hAh_nonneg
      _ ≤ 8 * (m * q * h ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hA_h_le (by norm_num)
  calc
    Causalean.Stat.chiSqDiv Pplus Pminus
        = ∑ i : Fin 3, (c i - 1) ^ (2 : ℕ) * (Pminus (s i)).toReal := hχ
    _ ≤ 8 * (m * q * h ^ (2 : ℕ)) := hsum
    _ = 8 * m * q * h ^ (2 : ℕ) := by ring

lemma twoPointWitness_one_draw_chiSq_bound (α γ u0 cB : ℝ)
    (hwin : MarginWindow u0) (hcB : 0 < cB) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      IsProbabilityMeasure (twoPointWitness α γ u0 cB n 1).dataMeasure ∧
      IsProbabilityMeasure (twoPointWitness α γ u0 cB n (-1)).dataMeasure ∧
      (twoPointWitness α γ u0 cB n 1).dataMeasure ≪
        (twoPointWitness α γ u0 cB n (-1)).dataMeasure ∧
      Integrable
        (fun x =>
          (((twoPointWitness α γ u0 cB n 1).dataMeasure.rnDeriv
              (twoPointWitness α γ u0 cB n (-1)).dataMeasure x).toReal - 1) ^ 2)
        (twoPointWitness α γ u0 cB n (-1)).dataMeasure ∧
      Causalean.Stat.chiSqDiv
          (twoPointWitness α γ u0 cB n 1).dataMeasure
          (twoPointWitness α γ u0 cB n (-1)).dataMeasure
        ≤ 8 * cB * (hLower α γ n) ^ (2 + α + betaAG α γ) := by
  /-
  Local computation needed by `two_point_divergence`: for large `n`,
  `h = hLower α γ n ≤ 1/2`, `q = qLower α γ n ∈ (0,1/2]`, and the two
  witness laws have the same `(X,A)` kernel and the same outcome kernel except
  on `{x ∈ B_n, A = true}`.  On that cell the outcome kernels are
  `bernoulliPM h` and `bernoulliPM (-h)`, so the RN ratio is the pulled-back
  Bernoulli ratio and the χ² contribution is
  `PX(B_n) * q * 4*h^2/(1-h^2) ≤ 8*cB*h^(2+α+betaAG α γ)`.

    The reusable finite-partition χ² reduction is now built above as
    `chiSqDiv_three_cell_bound_of_restrict`; the remaining substrate gap is the
    concrete restriction/mass calculation for this nested
    `Measure.bind`/`Measure.map` witness, namely the three cells
    `{¬(B_n X ∧ A)}`, `{B_n X ∧ A ∧ Y=1}`, and `{B_n X ∧ A ∧ Y=-1}`.
    -/
  classical
  filter_upwards [eventually_hLower_le_half α γ hα hγ,
    eventually_qLower_pos_le_half α γ hα hγ,
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with
    n hh_le_half hq hn1
  let h : ℝ := hLower α γ n
  let q : ℝ := qLower α γ n
  let τ0 : ℝ := (u0 + 2) / 2
  let B : Set ℝ := Set.Icc (0 : ℝ) (cB * h ^ α)
  let prop : ℝ → ℝ := fun x => if x ∈ B then q else 1 / 2
  let outcomeP : ℝ → Bool → Measure ℝ := fun x a =>
    if x ∈ B then (if a then bernoulliPM h else Measure.dirac 0)
    else (if a then bernoulliPM (τ0 / 2) else bernoulliPM (-τ0 / 2))
  let outcomeM : ℝ → Bool → Measure ℝ := fun x a =>
    if x ∈ B then (if a then bernoulliPM (-h) else Measure.dirac 0)
    else (if a then bernoulliPM (τ0 / 2) else bernoulliPM (-τ0 / 2))
  let m : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let Pp : Measure (Observation ℝ) := (twoPointWitness α γ u0 cB n 1).dataMeasure
  let Pm : Measure (Observation ℝ) := (twoPointWitness α γ u0 cB n (-1)).dataMeasure
  let s1 : Set (Observation ℝ) := {O | O.X ∈ B ∧ O.A = true ∧ O.Y = (1 : ℝ)}
  let s2 : Set (Observation ℝ) := {O | O.X ∈ B ∧ O.A = true ∧ O.Y = (-1 : ℝ)}
  let s0 : Set (Observation ℝ) := (s1 ∪ s2)ᶜ
  let s : Fin 3 → Set (Observation ℝ) := fun i =>
    if i = 0 then s0 else if i = 1 then s1 else s2
  have hnposNat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hh_pos : 0 < h := by
    simpa [h] using hLower_pos_of_pos_nat α γ hnposNat
  have hh0 : 0 ≤ h := hh_pos.le
  have hq_pos : 0 < q := by simpa [q] using hq.1
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hq_le_half : q ≤ (1 / 2 : ℝ) := by simpa [q] using hq.2
  have hB_nonneg : 0 ≤ cB * h ^ α :=
    mul_nonneg hcB.le (Real.rpow_nonneg hh_pos.le _)
  have hB_meas : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_Icc
  have hs1 : MeasurableSet s1 := by
    have hX : MeasurableSet {O : Observation ℝ | O.X ∈ B} :=
      hB_meas.preimage measurable_observation_X
    have hA : MeasurableSet {O : Observation ℝ | O.A = true} :=
      (measurableSet_singleton true).preimage measurable_observation_A
    have hY : MeasurableSet {O : Observation ℝ | O.Y = (1 : ℝ)} :=
      (measurableSet_singleton (1 : ℝ)).preimage measurable_observation_Y
    change MeasurableSet
      ({O : Observation ℝ | O.X ∈ B} ∩
        ({O : Observation ℝ | O.A = true} ∩ {O : Observation ℝ | O.Y = (1 : ℝ)}))
    exact hX.inter (hA.inter hY)
  have hs2 : MeasurableSet s2 := by
    have hX : MeasurableSet {O : Observation ℝ | O.X ∈ B} :=
      hB_meas.preimage measurable_observation_X
    have hA : MeasurableSet {O : Observation ℝ | O.A = true} :=
      (measurableSet_singleton true).preimage measurable_observation_A
    have hY : MeasurableSet {O : Observation ℝ | O.Y = (-1 : ℝ)} :=
      (measurableSet_singleton (-1 : ℝ)).preimage measurable_observation_Y
    change MeasurableSet
      ({O : Observation ℝ | O.X ∈ B} ∩
        ({O : Observation ℝ | O.A = true} ∩ {O : Observation ℝ | O.Y = (-1 : ℝ)}))
    exact hX.inter (hA.inter hY)
  have hs0 : MeasurableSet s0 := by
    dsimp [s0]
    exact (hs1.union hs2).compl
  have hs : ∀ i, MeasurableSet (s i) := by
    intro i
    fin_cases i <;> simp [s, hs0, hs1, hs2]
  have hdisj01 : Disjoint s0 s1 := by
    rw [Set.disjoint_left]
    intro O h0 h1
    exact h0 (Or.inl h1)
  have hdisj02 : Disjoint s0 s2 := by
    rw [Set.disjoint_left]
    intro O h0 h2
    exact h0 (Or.inr h2)
  have hdisj12 : Disjoint s1 s2 := by
    rw [Set.disjoint_left]
    intro O h1 h2
    have hy1 : O.Y = (1 : ℝ) := h1.2.2
    have hy2 : O.Y = (-1 : ℝ) := h2.2.2
    linarith
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [s] at hij ⊢
    · exact hdisj01
    · exact hdisj02
    · exact hdisj01.symm
    · exact hdisj12
    · exact hdisj02.symm
    · exact hdisj12.symm
  have hcover : (⋃ i, s i) = Set.univ := by
    ext O
    constructor
    · intro _
      trivial
    · intro _
      by_cases hO : O ∈ s1 ∪ s2
      · rcases hO with hO1 | hO2
        · exact Set.mem_iUnion.mpr ⟨(1 : Fin 3), by simp [s, hO1]⟩
        · exact Set.mem_iUnion.mpr ⟨(2 : Fin 3), by simp [s, hO2]⟩
      · have hnot1 : O ∉ s1 := fun hO1 => hO (Or.inl hO1)
        have hnot2 : O ∉ s2 := fun hO2 => hO (Or.inr hO2)
        exact Set.mem_iUnion.mpr ⟨(0 : Fin 3), by simp [s, s0, hnot1, hnot2]⟩
  have hPp_data :
      Pp = m.bind fun x => (bernoulliBool (prop x)).bind fun a =>
        (outcomeP x a).map (Observation.mk x a) := by
    simp [Pp, twoPointWitness, h, q, τ0, B, prop, outcomeP, m]
  have hPm_data :
      Pm = m.bind fun x => (bernoulliBool (prop x)).bind fun a =>
        (outcomeM x a).map (Observation.mk x a) := by
    simp [Pm, twoPointWitness, h, q, τ0, B, prop, outcomeM, m]
  have hkerP : Measurable fun x => (bernoulliBool (prop x)).bind fun a =>
      (outcomeP x a).map (Observation.mk x a) := by
    rw [show (fun x => (bernoulliBool (prop x)).bind fun a =>
        (outcomeP x a).map (Observation.mk x a)) =
        (fun x => ENNReal.ofReal (if x ∈ B then q else 1 / 2) •
            Measure.map (Observation.mk x true)
              (if x ∈ B then bernoulliPM h else bernoulliPM (τ0 / 2)) +
          ENNReal.ofReal (1 - (if x ∈ B then q else 1 / 2)) •
            Measure.map (Observation.mk x false)
              (if x ∈ B then Measure.dirac 0 else bernoulliPM (-τ0 / 2))) by
      funext x
      rw [bernoulliBool_bind]
      simp [outcomeP, prop]]
    simpa [B] using twoPointWitness_expanded_kernel_measurable α cB 1 h q τ0
  have hkerM : Measurable fun x => (bernoulliBool (prop x)).bind fun a =>
      (outcomeM x a).map (Observation.mk x a) := by
    rw [show (fun x => (bernoulliBool (prop x)).bind fun a =>
        (outcomeM x a).map (Observation.mk x a)) =
        (fun x => ENNReal.ofReal (if x ∈ B then q else 1 / 2) •
            Measure.map (Observation.mk x true)
              (if x ∈ B then bernoulliPM ((-1 : ℝ) * h) else bernoulliPM (τ0 / 2)) +
          ENNReal.ofReal (1 - (if x ∈ B then q else 1 / 2)) •
            Measure.map (Observation.mk x false)
              (if x ∈ B then Measure.dirac 0 else bernoulliPM (-τ0 / 2))) by
      funext x
      rw [bernoulliBool_bind]
      simp [outcomeM, prop]]
    simpa [B] using twoPointWitness_expanded_kernel_measurable α cB (-1) h q τ0
  have hinner0 : ∀ x (t : Set (Observation ℝ)), MeasurableSet t →
      ((bernoulliBool (prop x)).bind fun a => (outcomeP x a).map (Observation.mk x a))
          (t ∩ s0) =
        ((bernoulliBool (prop x)).bind fun a => (outcomeM x a).map (Observation.mk x a))
          (t ∩ s0) := by
    intro x t ht
    rw [bernoulliBool_bind, bernoulliBool_bind]
    rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.smul_apply, Measure.smul_apply]
    repeat rw [Measure.map_apply (measurable_observation_mk x true)]
    repeat rw [Measure.map_apply (measurable_observation_mk x false)]
    · by_cases hxB : x ∈ B <;>
        simp [prop, outcomeP, outcomeM, s0, s1, s2, hxB, bernoulliPM]
    all_goals exact ht.inter hs0
  have hinner1P : ∀ x (t : Set (Observation ℝ)), MeasurableSet t →
      ((bernoulliBool (prop x)).bind fun a => (outcomeP x a).map (Observation.mk x a))
          (t ∩ s1) =
        (if x ∈ B then ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) *
          (if Observation.mk x true (1 : ℝ) ∈ t then 1 else 0) else 0) := by
    intro x t ht
    rw [bernoulliBool_bind]
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    rw [Measure.map_apply (measurable_observation_mk x true)]
    rw [Measure.map_apply (measurable_observation_mk x false)]
    · by_cases hxB : x ∈ B
      · by_cases hxt : Observation.mk x true (1 : ℝ) ∈ t
        · simp [prop, outcomeP, s1, hxB, hxt, bernoulliPM,
              Pi.single_eq_of_ne (show (-1 : ℝ) ≠ 1 by norm_num)]
        · simp [prop, outcomeP, s1, hxB, hxt, bernoulliPM]
      · simp [prop, outcomeP, s1, hxB, bernoulliPM]
    all_goals exact ht.inter hs1
  have hinner1M : ∀ x (t : Set (Observation ℝ)), MeasurableSet t →
      ((bernoulliBool (prop x)).bind fun a => (outcomeM x a).map (Observation.mk x a))
          (t ∩ s1) =
        (if x ∈ B then ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) *
          (if Observation.mk x true (1 : ℝ) ∈ t then 1 else 0) else 0) := by
    intro x t ht
    rw [bernoulliBool_bind]
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    rw [Measure.map_apply (measurable_observation_mk x true)]
    rw [Measure.map_apply (measurable_observation_mk x false)]
    · by_cases hxB : x ∈ B
      · by_cases hxt : Observation.mk x true (1 : ℝ) ∈ t
        · simp [prop, outcomeM, s1, hxB, hxt, bernoulliPM,
              Pi.single_eq_of_ne (show (-1 : ℝ) ≠ 1 by norm_num),
            show (1 + -h) / 2 = (1 - h) / 2 by ring]
        · simp [prop, outcomeM, s1, hxB, hxt, bernoulliPM]
      · simp [prop, outcomeM, s1, hxB, bernoulliPM]
    all_goals exact ht.inter hs1
  have hinner2P : ∀ x (t : Set (Observation ℝ)), MeasurableSet t →
      ((bernoulliBool (prop x)).bind fun a => (outcomeP x a).map (Observation.mk x a))
          (t ∩ s2) =
        (if x ∈ B then ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) *
          (if Observation.mk x true (-1 : ℝ) ∈ t then 1 else 0) else 0) := by
    intro x t ht
    rw [bernoulliBool_bind]
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    rw [Measure.map_apply (measurable_observation_mk x true)]
    rw [Measure.map_apply (measurable_observation_mk x false)]
    · by_cases hxB : x ∈ B
      · by_cases hxt : Observation.mk x true (-1 : ℝ) ∈ t
        · simp [prop, outcomeP, s2, hxB, hxt, bernoulliPM,
              Pi.single_eq_of_ne (show (1 : ℝ) ≠ -1 by norm_num)]
        · simp [prop, outcomeP, s2, hxB, hxt, bernoulliPM]
      · simp [prop, outcomeP, s2, hxB, bernoulliPM]
    all_goals exact ht.inter hs2
  have hinner2M : ∀ x (t : Set (Observation ℝ)), MeasurableSet t →
      ((bernoulliBool (prop x)).bind fun a => (outcomeM x a).map (Observation.mk x a))
          (t ∩ s2) =
        (if x ∈ B then ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) *
          (if Observation.mk x true (-1 : ℝ) ∈ t then 1 else 0) else 0) := by
    intro x t ht
    rw [bernoulliBool_bind]
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    rw [Measure.map_apply (measurable_observation_mk x true)]
    rw [Measure.map_apply (measurable_observation_mk x false)]
    · by_cases hxB : x ∈ B
      · by_cases hxt : Observation.mk x true (-1 : ℝ) ∈ t
        · simp [prop, outcomeM, s2, hxB, hxt, bernoulliPM,
              Pi.single_eq_of_ne (show (1 : ℝ) ≠ -1 by norm_num),
            show (1 + -h) / 2 = (1 - h) / 2 by ring]
        · simp [prop, outcomeM, s2, hxB, hxt, bernoulliPM]
      · simp [prop, outcomeM, s2, hxB, bernoulliPM]
    all_goals exact ht.inter hs2
  have hratio1 : ∀ I : ENNReal,
      ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) * I =
        ENNReal.ofReal ((1 + h) / (1 - h)) *
          (ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) * I) := by
    intro I
    have hplus : 0 ≤ (1 + h) / 2 := by linarith
    have hminus : 0 ≤ (1 - h) / 2 := by linarith
    have hratio0 : 0 ≤ (1 + h) / (1 - h) :=
      div_nonneg (by linarith : 0 ≤ 1 + h) (by linarith : 0 ≤ 1 - h)
    have hcoef :
        ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) =
          ENNReal.ofReal ((1 + h) / (1 - h)) *
            (ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2)) := by
      rw [← ENNReal.ofReal_mul hq_nonneg, ← ENNReal.ofReal_mul hq_nonneg,
        ← ENNReal.ofReal_mul hratio0]
      congr 1
      field_simp [show (1 - h) ≠ 0 by linarith]
    rw [hcoef, mul_assoc]
  have hratio2 : ∀ I : ENNReal,
      ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) * I =
        ENNReal.ofReal ((1 - h) / (1 + h)) *
          (ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) * I) := by
    intro I
    have hplus : 0 ≤ (1 + h) / 2 := by linarith
    have hminus : 0 ≤ (1 - h) / 2 := by linarith
    have hratio0 : 0 ≤ (1 - h) / (1 + h) :=
      div_nonneg (by linarith : 0 ≤ 1 - h) (by linarith : 0 ≤ 1 + h)
    have hcoef :
        ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) =
          ENNReal.ofReal ((1 - h) / (1 + h)) *
            (ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2)) := by
      rw [← ENNReal.ofReal_mul hq_nonneg, ← ENNReal.ofReal_mul hq_nonneg,
        ← ENNReal.ofReal_mul hratio0]
      congr 1
      field_simp [show (1 + h) ≠ 0 by linarith]
    rw [hcoef, mul_assoc]
  have hrestrict0 : Pp.restrict s0 = ENNReal.ofReal (1 : ℝ) • Pm.restrict s0 := by
    ext t ht
    rw [Measure.restrict_apply ht, Measure.smul_apply, Measure.restrict_apply ht]
    simp only [ENNReal.ofReal_one, one_smul]
    rw [hPp_data, hPm_data]
    rw [Measure.bind_apply (ht.inter hs0) hkerP.aemeasurable,
      Measure.bind_apply (ht.inter hs0) hkerM.aemeasurable]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun x => hinner0 x t ht)
  have hrestrict1 :
      Pp.restrict s1 =
        ENNReal.ofReal ((1 + h) / (1 - h)) • Pm.restrict s1 := by
    ext t ht
    rw [Measure.restrict_apply ht, Measure.smul_apply, Measure.restrict_apply ht]
    simp only [smul_eq_mul]
    rw [hPp_data, hPm_data]
    rw [Measure.bind_apply (ht.inter hs1) hkerP.aemeasurable,
      Measure.bind_apply (ht.inter hs1) hkerM.aemeasurable]
    rw [← lintegral_const_mul' (ENNReal.ofReal ((1 + h) / (1 - h)))
      (fun x => ((bernoulliBool (prop x)).bind fun a =>
        (outcomeM x a).map (Observation.mk x a)) (t ∩ s1)) ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ((bernoulliBool (prop x)).bind fun a =>
        (outcomeP x a).map (Observation.mk x a)) (t ∩ s1) =
      ENNReal.ofReal ((1 + h) / (1 - h)) *
        (((bernoulliBool (prop x)).bind fun a =>
          (outcomeM x a).map (Observation.mk x a)) (t ∩ s1))
    rw [hinner1P x t ht, hinner1M x t ht]
    by_cases hxB : x ∈ B
    · simp [hxB, hratio1]
    · simp [hxB]
  have hrestrict2 :
      Pp.restrict s2 =
        ENNReal.ofReal ((1 - h) / (1 + h)) • Pm.restrict s2 := by
    ext t ht
    rw [Measure.restrict_apply ht, Measure.smul_apply, Measure.restrict_apply ht]
    simp only [smul_eq_mul]
    rw [hPp_data, hPm_data]
    rw [Measure.bind_apply (ht.inter hs2) hkerP.aemeasurable,
      Measure.bind_apply (ht.inter hs2) hkerM.aemeasurable]
    rw [← lintegral_const_mul' (ENNReal.ofReal ((1 - h) / (1 + h)))
      (fun x => ((bernoulliBool (prop x)).bind fun a =>
        (outcomeM x a).map (Observation.mk x a)) (t ∩ s2)) ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ((bernoulliBool (prop x)).bind fun a =>
        (outcomeP x a).map (Observation.mk x a)) (t ∩ s2) =
      ENNReal.ofReal ((1 - h) / (1 + h)) *
        (((bernoulliBool (prop x)).bind fun a =>
          (outcomeM x a).map (Observation.mk x a)) (t ∩ s2))
    rw [hinner2P x t ht, hinner2M x t ht]
    by_cases hxB : x ∈ B
    · simp [hxB, hratio2]
    · simp [hxB]
  have hrestrict : ∀ i,
      Pp.restrict (s i) =
        ENNReal.ofReal
          (if i = 0 then (1 : ℝ)
           else if i = 1 then (1 + h) / (1 - h)
           else (1 - h) / (1 + h)) • Pm.restrict (s i) := by
    intro i
    fin_cases i <;> simp [s, hrestrict0, hrestrict1, hrestrict2]
  let A : ℝ := m.real B * q
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg measureReal_nonneg hq_nonneg
  have hBmass_le : m.real B ≤ cB * h ^ α := by
    simpa [m, B] using restricted_volume_real_Icc_zero_le (a := cB * h ^ α) hB_nonneg
  have hA_le : A ≤ (cB * h ^ α) * q := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right hBmass_le hq_nonneg
  have hPm_s1 :
      Pm s1 = ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) * m B := by
    rw [hPm_data, Measure.bind_apply hs1 hkerM.aemeasurable]
    have hpoint : ∀ x,
        ((bernoulliBool (prop x)).bind fun a => (outcomeM x a).map (Observation.mk x a)) s1 =
          (if x ∈ B then ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) *
            (if Observation.mk x true (1 : ℝ) ∈ (Set.univ : Set (Observation ℝ))
              then 1 else 0) else 0) := by
      intro x
      simpa using hinner1M x Set.univ MeasurableSet.univ
    have hC :
        (fun x => (if x ∈ B then
            ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2) *
              (if Observation.mk x true (1 : ℝ) ∈ (Set.univ : Set (Observation ℝ))
                then 1 else 0) else 0)) =
          fun x => B.indicator
            (fun _ => ENNReal.ofReal q * ENNReal.ofReal ((1 - h) / 2)) x := by
      funext x
      by_cases hxB : x ∈ B <;> simp [hxB]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpoint), hC,
      lintegral_indicator_const hB_meas]
  have hPm_s2 :
      Pm s2 = ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) * m B := by
    rw [hPm_data, Measure.bind_apply hs2 hkerM.aemeasurable]
    have hpoint : ∀ x,
        ((bernoulliBool (prop x)).bind fun a => (outcomeM x a).map (Observation.mk x a)) s2 =
          (if x ∈ B then ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) *
            (if Observation.mk x true (-1 : ℝ) ∈ (Set.univ : Set (Observation ℝ))
              then 1 else 0) else 0) := by
      intro x
      simpa using hinner2M x Set.univ MeasurableSet.univ
    have hC :
        (fun x => (if x ∈ B then
            ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2) *
              (if Observation.mk x true (-1 : ℝ) ∈ (Set.univ : Set (Observation ℝ))
                then 1 else 0) else 0)) =
          fun x => B.indicator
            (fun _ => ENNReal.ofReal q * ENNReal.ofReal ((1 + h) / 2)) x := by
      funext x
      by_cases hxB : x ∈ B <;> simp [hxB]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpoint), hC,
      lintegral_indicator_const hB_meas]
  have hν1 : (Pm (s 1)).toReal = A * ((1 - h) / 2) := by
    have hf : 0 ≤ (1 - h) / 2 := by linarith
    simp [s, hPm_s1, A, measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hq_nonneg, ENNReal.toReal_ofReal hf, mul_assoc]
    ring
  have hν2 : (Pm (s 2)).toReal = A * ((1 + h) / 2) := by
    have hf : 0 ≤ (1 + h) / 2 := by linarith
    simp [s, hPm_s2, A, measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hq_nonneg, ENNReal.toReal_ofReal hf, mul_assoc]
    ring
  have hprobPp : IsProbabilityMeasure Pp := by
    have hwf := twoPointWitness_wellFormed α γ u0 cB 1 hwin hn1 hh_le_half
      (Or.inl rfl) hq
    simpa [Pp] using hwf.1
  have hprobPm : IsProbabilityMeasure Pm := by
    have hwf := twoPointWitness_wellFormed α γ u0 cB (-1) hwin hn1 hh_le_half
      (Or.inr rfl) hq
    simpa [Pm] using hwf.1
  letI : IsProbabilityMeasure Pp := hprobPp
  letI : IsProbabilityMeasure Pm := hprobPm
  have hc_nonneg : ∀ i : Fin 3,
      0 ≤ (if i = 0 then (1 : ℝ)
           else if i = 1 then (1 + h) / (1 - h)
           else (1 - h) / (1 + h)) := by
    have hp : 0 ≤ 1 + h := by linarith
    have hm : 0 ≤ 1 - h := by linarith
    intro i
    fin_cases i <;> simp [div_nonneg, hp, hm]
  have hac : Pp ≪ Pm :=
    Causalean.Mathlib.MeasureTheory.partition_restrict_absolutelyContinuous
      Pp Pm s
      (fun i : Fin 3 =>
        if i = 0 then (1 : ℝ)
        else if i = 1 then (1 + h) / (1 - h)
        else (1 - h) / (1 + h))
      hs hdisj hcover hc_nonneg hrestrict
  have hint :
      Integrable (fun x => ((Pp.rnDeriv Pm x).toReal - 1) ^ (2 : ℕ)) Pm :=
    Causalean.Mathlib.MeasureTheory.partition_restrict_integrable_sq_rnDeriv
      Pp Pm s
      (fun i : Fin 3 =>
        if i = 0 then (1 : ℝ)
        else if i = 1 then (1 + h) / (1 - h)
        else (1 - h) / (1 + h))
      hs hdisj hcover hc_nonneg hrestrict
  have hchi_partition :
      Causalean.Stat.chiSqDiv Pp Pm ≤
        8 * (cB * h ^ α) * q * h ^ (2 : ℕ) :=
    chiSqDiv_three_cell_bound_of_restrict Pp Pm s A (cB * h ^ α) q h hac hs
      hdisj hcover hh0 (by simpa [h] using hh_le_half) hA_nonneg hA_le hν1 hν2 hrestrict
  have hβ_nonneg : 0 ≤ betaAG α γ := betaAG_nonneg_of_nonneg α γ hα hγ
  have hq_le_hβ : q ≤ h ^ betaAG α γ := by
    by_cases hβ0 : betaAG α γ = 0
    · have hq_eq : q = (1 / 4 : ℝ) := by simp [q, qLower, hβ0]
      have hpow_eq : h ^ betaAG α γ = 1 := by simp [hβ0]
      rw [hq_eq, hpow_eq]
      norm_num
    · simp [q, qLower, h, hβ0]
  have hchi :
      Causalean.Stat.chiSqDiv Pp Pm ≤ 8 * cB * h ^ (2 + α + betaAG α γ) := by
    calc
      Causalean.Stat.chiSqDiv Pp Pm
          ≤ 8 * (cB * h ^ α) * q * h ^ (2 : ℕ) := hchi_partition
      _ ≤ 8 * (cB * h ^ α) * (h ^ betaAG α γ) * h ^ (2 : ℕ) := by
          gcongr
      _ = 8 * cB * h ^ (2 + α + betaAG α γ) := by
          have hpows :
              h ^ α * h ^ betaAG α γ * h ^ (2 : ℝ) =
                h ^ (2 + α + betaAG α γ) := by
            calc
              h ^ α * h ^ betaAG α γ * h ^ (2 : ℝ)
                  = (h ^ α * h ^ betaAG α γ) * h ^ (2 : ℝ) := by ring
              _ = h ^ (α + betaAG α γ) * h ^ (2 : ℝ) := by
                  rw [← Real.rpow_add hh_pos]
              _ = h ^ ((α + betaAG α γ) + 2) := by
                  rw [← Real.rpow_add hh_pos]
              _ = h ^ (2 + α + betaAG α γ) := by
                  ring_nf
          rw [show h ^ (2 : ℕ) = h ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
          rw [show 8 * (cB * h ^ α) * h ^ betaAG α γ * h ^ (2 : ℝ) =
              8 * cB * (h ^ α * h ^ betaAG α γ * h ^ (2 : ℝ)) by ring]
          rw [hpows]
  exact ⟨by simpa [Pp] using hprobPp,
    by simpa [Pm] using hprobPm,
    by simpa [Pp, Pm] using hac,
    by simpa [Pp, Pm] using hint,
    by simpa [Pp, Pm, h] using hchi⟩

-- @node: lem:two-point-divergence
/-- `lem:two-point-divergence`. The per-observation χ²-divergence scales as
`χ² ≤ C h_n^{2+α+β_{α,γ}} = C h_n^{D_{α,γ}}` (i.e. `m_n q_n h_n²` with
`m_n ~ h_n^α`, `q_n ~ h_n^{β_{α,γ}}`); with `h_n = n^{-1/D_{α,γ}}` the per-draw
divergence is `≤ C/n`, so by the product identity the `n`-fold divergence is
uniformly bounded. The admissibility `8 c_B c_Q < log 5` (`c_Q = 1` for the
`qLower` weak-arm scale) keeps the product divergence below a constant. -/
lemma two_point_divergence (α γ u0 cB : ℝ) (hwin : MarginWindow u0)
    (hcB : 0 < cB) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hconst : 8 * cB < Real.log 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n 1).dataMeasure) ≪
          (Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n (-1)).dataMeasure) ∧
      Integrable
          (fun x =>
            (((Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n 1).dataMeasure).rnDeriv
                (Measure.pi fun _ : Fin n =>
                  (twoPointWitness α γ u0 cB n (-1)).dataMeasure) x).toReal - 1) ^ 2)
          (Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n (-1)).dataMeasure) ∧
      Causalean.Stat.chiSqDiv
            (twoPointWitness α γ u0 cB n 1).dataMeasure
            (twoPointWitness α γ u0 cB n (-1)).dataMeasure
          ≤ C * (hLower α γ n) ^ (2 + α + betaAG α γ) ∧
      Causalean.Stat.chiSqDiv
          (Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n 1).dataMeasure)
          (Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n (-1)).dataMeasure)
        ≤ C
    := by
  classical
  let C : ℝ := max (8 * cB) 5
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5) (le_max_right _ _)
  refine ⟨C, hCpos, ?_⟩
  have hone := twoPointWitness_one_draw_chiSq_bound α γ u0 cB hwin hcB hα hγ
  filter_upwards [hone, Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with
    n hone_n hn1
  rcases hone_n with ⟨hprobPp0, hprobPm0, hac0, hint0, hchi8_0⟩
  let Pp : Measure (Observation ℝ) := (twoPointWitness α γ u0 cB n 1).dataMeasure
  let Pm : Measure (Observation ℝ) := (twoPointWitness α γ u0 cB n (-1)).dataMeasure
  letI : IsProbabilityMeasure Pp := by
    simpa [Pp] using hprobPp0
  letI : IsProbabilityMeasure Pm := by
    simpa [Pm] using hprobPm0
  have hac : Pp ≪ Pm := by
    simpa [Pp, Pm] using hac0
  have hint :
      Integrable (fun x => ((Pp.rnDeriv Pm x).toReal - 1) ^ 2) Pm := by
    simpa [Pp, Pm] using hint0
  have hchi8 :
      Causalean.Stat.chiSqDiv Pp Pm ≤
        8 * cB * (hLower α γ n) ^ (2 + α + betaAG α γ) := by
    simpa [Pp, Pm] using hchi8_0
  have hnposNat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hbeta_nonneg : 0 ≤ betaAG α γ := by
    unfold betaAG
    by_cases hγ0 : γ = 0
    · simp [hγ0]
    · have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
      have hdenpos : 0 < α + 1 := by linarith
      simp [hγ0, div_nonneg (mul_nonneg hα hγpos.le) hdenpos.le]
  have hDpos : 0 < Dag α γ := by
    unfold Dag
    linarith
  have hpowD :
      (hLower α γ n) ^ (2 + α + betaAG α γ) = (n : ℝ) ^ (-1 : ℝ) := by
    have hExp : 2 + α + betaAG α γ = Dag α γ := by rfl
    calc
      (hLower α γ n) ^ (2 + α + betaAG α γ)
          = (hLower α γ n) ^ (Dag α γ) := by rw [hExp]
      _ = ((n : ℝ) ^ (-(1 / Dag α γ))) ^ (Dag α γ) := by rfl
      _ = (n : ℝ) ^ (-(1 / Dag α γ) * Dag α γ) := by
        rw [← Real.rpow_mul hnpos.le]
      _ = (n : ℝ) ^ (-1 : ℝ) := by
        congr 1
        field_simp [hDpos.ne']
  have hp_pos : 0 < hLower α γ n := by
    unfold hLower
    exact Real.rpow_pos_of_pos hnpos _
  have hpow_nonneg : 0 ≤ (hLower α γ n) ^ (2 + α + betaAG α γ) :=
    Real.rpow_nonneg hp_pos.le _
  have hchi_one :
      Causalean.Stat.chiSqDiv Pp Pm ≤
        C * (hLower α γ n) ^ (2 + α + betaAG α γ) := by
    calc
      Causalean.Stat.chiSqDiv Pp Pm
          ≤ 8 * cB * (hLower α γ n) ^ (2 + α + betaAG α γ) := hchi8
      _ ≤ C * (hLower α γ n) ^ (2 + α + betaAG α γ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpow_nonneg
  let Pprod : Measure (Fin n → Observation ℝ) := Measure.pi fun _ : Fin n => Pp
  let Qprod : Measure (Fin n → Observation ℝ) := Measure.pi fun _ : Fin n => Pm
  have hac_prod : Pprod ≪ Qprod := by
    dsimp [Pprod, Qprod]
    exact Causalean.Stat.pi_iid_absolutelyContinuous Pp Pm hac n
  have hint_prod :
      Integrable (fun x => ((Pprod.rnDeriv Qprod x).toReal - 1) ^ 2) Qprod := by
    dsimp [Pprod, Qprod]
    exact Causalean.Stat.pi_iid_integrable_sq_dev Pp Pm hac hint n
  have hchi_non : 0 ≤ Causalean.Stat.chiSqDiv Pp Pm :=
    Causalean.Stat.chiSqDiv_nonneg
  have hchi_per_inv :
      Causalean.Stat.chiSqDiv Pp Pm ≤ 8 * cB * (n : ℝ) ^ (-1 : ℝ) := by
    simpa [hpowD] using hchi8
  have hmul_budget : (n : ℝ) * Causalean.Stat.chiSqDiv Pp Pm ≤ 8 * cB := by
    calc
      (n : ℝ) * Causalean.Stat.chiSqDiv Pp Pm
          ≤ (n : ℝ) * (8 * cB * (n : ℝ) ^ (-1 : ℝ)) :=
            mul_le_mul_of_nonneg_left hchi_per_inv hnpos.le
      _ = 8 * cB := by
        rw [Real.rpow_neg_one]
        field_simp [hnpos.ne']
  have hpow_exp :
      (1 + Causalean.Stat.chiSqDiv Pp Pm) ^ n ≤
        Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv Pp Pm) := by
    calc
      (1 + Causalean.Stat.chiSqDiv Pp Pm) ^ n
          ≤ (Real.exp (Causalean.Stat.chiSqDiv Pp Pm)) ^ n := by
            exact pow_le_pow_left₀ (by linarith)
              (by
                linarith [Real.add_one_le_exp (Causalean.Stat.chiSqDiv Pp Pm)])
              n
      _ = Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv Pp Pm) := by
          rw [← Real.exp_nat_mul]
  have hpow_le_five :
      (1 + Causalean.Stat.chiSqDiv Pp Pm) ^ n ≤ 5 := by
    calc
      (1 + Causalean.Stat.chiSqDiv Pp Pm) ^ n
          ≤ Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv Pp Pm) := hpow_exp
      _ ≤ Real.exp (Real.log 5) :=
          Real.exp_le_exp.mpr (le_of_lt (lt_of_le_of_lt hmul_budget hconst))
      _ = 5 := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  have hprod_eq :
      1 + Causalean.Stat.chiSqDiv Pprod Qprod =
        (1 + Causalean.Stat.chiSqDiv Pp Pm) ^ n := by
    dsimp [Pprod, Qprod]
    exact Causalean.Stat.one_add_chiSqDiv_pi_iid_general Pp Pm hac hint n
  have hchi_prod_four : Causalean.Stat.chiSqDiv Pprod Qprod ≤ 4 := by
    have hone_le : 1 + Causalean.Stat.chiSqDiv Pprod Qprod ≤ 5 := by
      rw [hprod_eq]
      exact hpow_le_five
    linarith
  have hchi_prod : Causalean.Stat.chiSqDiv Pprod Qprod ≤ C := by
    exact hchi_prod_four.trans
      ((by norm_num : (4 : ℝ) ≤ 5).trans (le_max_right (8 * cB) 5))
  exact ⟨by simpa [Pprod, Qprod, Pp, Pm] using hac_prod,
    by simpa [Pprod, Qprod, Pp, Pm] using hint_prod,
    by simpa [Pp, Pm] using hchi_one,
    by simpa [Pprod, Qprod, Pp, Pm] using hchi_prod⟩

-- @node: restricted_volume_real_Icc_zero
/-- Lebesgue mass of `[0,a]` under Lebesgue measure restricted to `[0,1]`. -/
lemma restricted_volume_real_Icc_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Icc (0 : ℝ) a) = a := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Icc]
  have hinter :
      Set.Icc (0 : ℝ) a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) a := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, ⟨hx.1, le_trans hx.2 ha1⟩⟩
  rw [hinter]
  have hvol : volume.real (Set.Icc (0 : ℝ) a) = a := by
    simpa using (Real.volume_real_Icc_of_le ha0 : volume.real (Set.Icc (0 : ℝ) a) = a - 0)
  simpa [measureReal_def] using hvol

-- @node: lem:regret-separation
/-- `lem:regret-separation`. The witness optimal labels are opposite on `B_n`,
forcing regret separation `≥ c h_n^{1+α}` for every policy. -/
lemma regret_separation (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (Policy ℝ))
    (hwin : MarginWindow u0) (hcB : 0 < cB) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hCm : 0 < Cm) (hCo : 0 < Co) (hco : 0 < co)
    (hcBm : cB ≤ Cm) (hcBo : cB ≤ Co) (hup : 0 < underlineP)
    -- note c_B overlap-decay smallness (def:two-point-witness constant choice)
    (hcB_gpos : 0 < γ → 0 < α → cB ≤ Co * co ^ (-(α / γ)))
    (hcB_gzero : 0 < γ → α = 0 → cB ≤ Co * (4 : ℝ) ^ (-(1 / γ)))
    (huple : underlineP ≤ 1 / 4) (hπmeas : ∀ π ∈ policySet, Measurable π) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ π ∈ policySet,
      max (lawRegret (twoPointWitness α γ u0 cB n 1) π)
          (lawRegret (twoPointWitness α γ u0 cB n (-1)) π)
        ≥ c * (hLower α γ n) ^ (1 + α)
    := by
  classical
  let csep : ℝ := min cB 1 / 4
  have hcmin_pos : 0 < min cB 1 := lt_min hcB zero_lt_one
  have hcsep_pos : 0 < csep := by
    dsimp [csep]
    positivity
  refine ⟨csep, hcsep_pos, ?_⟩
  have hmemP :
      ∀ᶠ n : ℕ in Filter.atTop,
        LawClass α γ Cm u0 Co co underlineP policySet
          (twoPointWitness α γ u0 cB n 1) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
          ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α)) :=
    witness_membership α γ u0 cB Cm Co co underlineP policySet 1 hα hγ hwin
      hCm hCo hco hcB hcBm hcBo hup hcB_gpos hcB_gzero huple (Or.inl rfl)
  have hmemM :
      ∀ᶠ n : ℕ in Filter.atTop,
        LawClass α γ Cm u0 Co co underlineP policySet
          (twoPointWitness α γ u0 cB n (-1)) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
          ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α)) :=
    witness_membership α γ u0 cB Cm Co co underlineP policySet (-1) hα hγ hwin
      hCm hCo hco hcB hcBm hcBo hup hcB_gpos hcB_gzero huple (Or.inr rfl)
  filter_upwards [hmemP, hmemM, Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩]
    with n hwitP hwitM hn1
  intro π hπ
  let hp : ℝ := hLower α γ n
  let ell : ℝ := min cB 1 * hp ^ α
  let E : Set ℝ := Set.Icc (0 : ℝ) ell
  let Pp : ObservedLaw ℝ := twoPointWitness α γ u0 cB n 1
  let Pm : ObservedLaw ℝ := twoPointWitness α γ u0 cB n (-1)
  have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num) hn1
  have hp_pos : 0 < hp := by
    simpa [hp] using hLower_pos_of_pos_nat α γ hnposNat
  have hp_le_one : hp ≤ 1 := by
    simpa [hp] using hLower_le_one_of_one_le_nat α γ hα hγ hn1
  have hp_pow_nonneg : 0 ≤ hp ^ α := Real.rpow_nonneg hp_pos.le α
  have hp_pow_le_one : hp ^ α ≤ 1 := Real.rpow_le_one hp_pos.le hp_le_one hα
  have hmin_nonneg : 0 ≤ min cB 1 := le_of_lt hcmin_pos
  have hmin_le_cB : min cB 1 ≤ cB := min_le_left _ _
  have hmin_le_one : min cB 1 ≤ (1 : ℝ) := min_le_right _ _
  have hell_nonneg : 0 ≤ ell := by
    dsimp [ell]
    exact mul_nonneg hmin_nonneg hp_pow_nonneg
  have hell_le_one : ell ≤ 1 := by
    dsimp [ell]
    calc
      min cB 1 * hp ^ α ≤ 1 * 1 :=
        mul_le_mul hmin_le_one hp_pow_le_one hp_pow_nonneg zero_le_one
      _ = 1 := by norm_num
  have hEreal : Pp.PX.real E = ell := by
    have hbase := restricted_volume_real_Icc_zero (a := ell) hell_nonneg hell_le_one
    simpa [Pp, twoPointWitness, E] using hbase
  rcases hwitP with ⟨hclassP, hoptp, _⟩
  rcases hwitM with ⟨hclassM, _, hoptm⟩
  have hwfpP : WellFormedLaw Pp := by simpa [Pp] using hclassP.wf
  have hbddp : BoundedOutcome Pp := by simpa [Pp] using hclassP.bdd
  letI : IsProbabilityMeasure Pp.PX := hwfpP.2.1
  let Dp : Set ℝ := disagreementSet π (lawOptimalPolicy Pp)
  let Dm : Set ℝ := disagreementSet π (lawOptimalPolicy Pm)
  let Bp : Set ℝ := Dp ∩ {x | hp / 2 < |Pp.contrast x|}
  let Bm : Set ℝ := Dm ∩ {x | hp / 2 < |Pm.contrast x|}
  have hhalf_pos : 0 < hp / 2 := by positivity
  have hregp_le :=
    regret_disagreement_large_contrast_le Pp π hwfpP hbddp (hπmeas π hπ) hhalf_pos
  have hwfmP : WellFormedLaw Pm := by simpa [Pm] using hclassM.wf
  have hbddm : BoundedOutcome Pm := by simpa [Pm] using hclassM.bdd
  have hregm_le :=
    regret_disagreement_large_contrast_le Pm π hwfmP hbddm (hπmeas π hπ) hhalf_pos
  have hRplus : (hp / 2) * Pp.PX.real Bp ≤ lawRegret Pp π := by
    have hmul := mul_le_mul_of_nonneg_left hregp_le hhalf_pos.le
    have hcalc : (hp / 2) * (lawRegret Pp π / (hp / 2)) = lawRegret Pp π := by
      field_simp [hhalf_pos.ne']
    simpa [Bp, Dp, hcalc] using hmul
  have hRminus : (hp / 2) * Pm.PX.real Bm ≤ lawRegret Pm π := by
    have hmul := mul_le_mul_of_nonneg_left hregm_le hhalf_pos.le
    have hcalc : (hp / 2) * (lawRegret Pm π / (hp / 2)) = lawRegret Pm π := by
      field_simp [hhalf_pos.ne']
    simpa [Bm, Dm, hcalc] using hmul
  have hEsubset : E ⊆ Bp ∪ Bm := by
    intro x hxE
    have hx0 : 0 ≤ x := hxE.1
    have hxell : x ≤ ell := hxE.2
    have hxblock : 0 ≤ x ∧ x ≤ cB * hp ^ α := by
      refine ⟨hx0, ?_⟩
      calc
        x ≤ ell := hxell
        _ = min cB 1 * hp ^ α := rfl
        _ ≤ cB * hp ^ α := mul_le_mul_of_nonneg_right hmin_le_cB hp_pow_nonneg
    have hcp : Pp.contrast x = hp := by
      simp [Pp, twoPointWitness, hp, hxblock]
    have hcm : Pm.contrast x = -hp := by
      simp [Pm, twoPointWitness, hp, hxblock]
    have hbigp : hp / 2 < |Pp.contrast x| := by
      rw [hcp, abs_of_pos hp_pos]
      linarith
    have hbigm : hp / 2 < |Pm.contrast x| := by
      rw [hcm, abs_neg, abs_of_pos hp_pos]
      linarith
    have hoptp_true : lawOptimalPolicy Pp x = true := by
      simpa [Pp] using hoptp x
    have hoptm_false : lawOptimalPolicy Pm x = false := by
      cases hopt : lawOptimalPolicy Pm x
      · rfl
      · have hnotblock : ¬ (0 ≤ x ∧ x ≤ cB * hp ^ α) := by
          have := (hoptm x).mp hopt
          simpa [Pm, hp] using this
        exact False.elim (hnotblock hxblock)
    by_cases hπtrue : π x = true
    · right
      refine ⟨?_, hbigm⟩
      simp [Dm, disagreementSet, hπtrue, hoptm_false]
    · left
      have hπfalse : π x = false := by
        cases hπx : π x
        · rfl
        · exact False.elim (hπtrue hπx)
      refine ⟨?_, hbigp⟩
      simp [Dp, disagreementSet, hπfalse, hoptp_true]
  have hmeasure_union : Pp.PX.real E ≤ Pp.PX.real Bp + Pp.PX.real Bm := by
    calc
      Pp.PX.real E ≤ Pp.PX.real (Bp ∪ Bm) :=
        measureReal_mono (μ := Pp.PX) hEsubset (measure_ne_top Pp.PX (Bp ∪ Bm))
      _ ≤ Pp.PX.real Bp + Pp.PX.real Bm := measureReal_union_le Bp Bm
  have hmeasure : ell ≤ Pp.PX.real Bp + Pm.PX.real Bm := by
    have hsame : Pp.PX = Pm.PX := by
      simp [Pp, Pm, twoPointWitness]
    calc
      ell = Pp.PX.real E := hEreal.symm
      _ ≤ Pp.PX.real Bp + Pp.PX.real Bm := hmeasure_union
      _ = Pp.PX.real Bp + Pm.PX.real Bm := by rw [← hsame]
  have hsumR : (hp / 2) * ell ≤ lawRegret Pp π + lawRegret Pm π := by
    have hmul_measure :
        (hp / 2) * ell ≤ (hp / 2) * (Pp.PX.real Bp + Pm.PX.real Bm) :=
      mul_le_mul_of_nonneg_left hmeasure hhalf_pos.le
    have hparts : (hp / 2) * (Pp.PX.real Bp + Pm.PX.real Bm) ≤
        lawRegret Pp π + lawRegret Pm π := by
      nlinarith [hRplus, hRminus]
    exact hmul_measure.trans hparts
  have hpow_add : hp ^ (1 + α) = hp * hp ^ α := by
    rw [Real.rpow_add hp_pos, Real.rpow_one]
  have hsumR' :
      (min cB 1 / 2) * hp ^ (1 + α) ≤ lawRegret Pp π + lawRegret Pm π := by
    calc
      (min cB 1 / 2) * hp ^ (1 + α)
          = (hp / 2) * ell := by
              rw [hpow_add]
              ring
      _ ≤ lawRegret Pp π + lawRegret Pm π := hsumR
  have hmaxsum : lawRegret Pp π + lawRegret Pm π ≤
      2 * max (lawRegret Pp π) (lawRegret Pm π) := by
    nlinarith [le_max_left (lawRegret Pp π) (lawRegret Pm π),
      le_max_right (lawRegret Pp π) (lawRegret Pm π)]
  have htarget : csep * hp ^ (1 + α) ≤ max (lawRegret Pp π) (lawRegret Pm π) := by
    dsimp [csep]
    nlinarith [hsumR', hmaxsum]
  simpa [Pp, Pm, hp] using htarget

-- @node: lawRegret_nonneg_of_wellformed
/-- Welfare regret is nonnegative under the welfare-identity hypotheses. -/
lemma lawRegret_nonneg_of_wellformed {𝒳 : Type*} [MeasurableSpace 𝒳]
    (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    0 ≤ lawRegret P π := by
  have hreg := regret_eq_disagreement_integral P π hwf hbdd hπ
  rw [hreg]
  exact integral_nonneg (fun x =>
    mul_nonneg (abs_nonneg _) (by
      unfold disagreementIndicator
      split <;> norm_num))

-- @node: lawRegret_le_two_of_wellformed
/-- Under bounded outcomes, any measurable deterministic policy has regret at most `2`. -/
lemma lawRegret_le_two_of_wellformed {𝒳 : Type*} [MeasurableSpace 𝒳]
    (P : ObservedLaw 𝒳) (π : Policy 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hπ : Measurable π) :
    lawRegret P π ≤ 2 := by
  rcases hwf with
    ⟨hprobData, hprobPX, hmap, hτmeas, hemeas, hmu0meas, hmu1meas,
      hτeq, herange, heSem, hmu1Sem, hmu0Sem⟩
  letI : IsProbabilityMeasure P.PX := hprobPX
  have hτ_bound : ∀ x, |P.contrast x| ≤ (2 : ℝ) := by
    intro x
    rw [hτeq x]
    have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
    have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
    calc
      |P.mu1 x - P.mu0 x| ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hmu1 hmu0
      _ = (2 : ℝ) := by norm_num
  let f : 𝒳 → ℝ :=
    fun x => |P.contrast x| * disagreementIndicator π (lawOptimalPolicy P) x
  have hDmeas : MeasurableSet (disagreementSet π (lawOptimalPolicy P)) :=
    measurableSet_disagreementSet P π hτmeas hπ
  have hf_meas : Measurable f := by
    have hτabs : Measurable (fun x => |P.contrast x|) := by
      simpa [Real.norm_eq_abs] using hτmeas.norm
    dsimp [f]
    apply hτabs.mul
    unfold disagreementIndicator
    exact Measurable.ite hDmeas measurable_const measurable_const
  have hf_int : Integrable f P.PX := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 2 ?_
    filter_upwards with x
    have hind : |disagreementIndicator π (lawOptimalPolicy P) x| ≤ (1 : ℝ) := by
      unfold disagreementIndicator
      split <;> simp
    calc
      |f x| =
          |P.contrast x| * |disagreementIndicator π (lawOptimalPolicy P) x| := by
        simp [f, abs_mul]
      _ ≤ 2 * 1 := by
        gcongr
        exact hτ_bound x
      _ = (2 : ℝ) := by norm_num
  have hreg := regret_eq_disagreement_integral P π
    ⟨hprobData, hprobPX, hmap, hτmeas, hemeas, hmu0meas, hmu1meas,
      hτeq, herange, heSem, hmu1Sem, hmu0Sem⟩ hbdd hπ
  rw [hreg]
  change ∫ x, f x ∂P.PX ≤ 2
  calc
    ∫ x, f x ∂P.PX ≤ ∫ _x, (2 : ℝ) ∂P.PX := by
      refine integral_mono hf_int (integrable_const (2 : ℝ)) ?_
      intro x
      calc
        f x = |P.contrast x| * disagreementIndicator π (lawOptimalPolicy P) x := rfl
        _ ≤ 2 * 1 := by
          have hind_nonneg : 0 ≤ disagreementIndicator π (lawOptimalPolicy P) x := by
            unfold disagreementIndicator
            split <;> norm_num
          have hind_le : disagreementIndicator π (lawOptimalPolicy P) x ≤ (1 : ℝ) := by
            unfold disagreementIndicator
            split <;> norm_num
          exact mul_le_mul (hτ_bound x) hind_le hind_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        _ = 2 := by norm_num
    _ = 2 := by simp

-- @node: thm:minimax-lower
/-- `thm:minimax-lower` (CRUX). The sharp constructive converse over the
baseline observed-law class: `M_n ≥ c n^{-r_⋆(α,γ)}` for all large `n`. -/
theorem minimax_lower (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (Policy ℝ))
    (hwin : MarginWindow u0) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hCm : 0 < Cm) (hCo : 0 < Co) (hco : 0 < co) (hcB : 0 < cB)
    (hcBm : cB ≤ Cm) (hcBo : cB ≤ Co) (hup : 0 < underlineP)
    -- note c_B overlap-decay smallness (def:two-point-witness constant choice)
    (hcB_gpos : 0 < γ → 0 < α → cB ≤ Co * co ^ (-(α / γ)))
    (hcB_gzero : 0 < γ → α = 0 → cB ≤ Co * (4 : ℝ) ^ (-(1 / γ)))
    (huple : underlineP ≤ 1 / 4) (hsmall : 8 * cB < Real.log 5)
    (hπnonempty : policySet.Nonempty)
    (hπmeas : ∀ π ∈ policySet, Measurable π) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      minimaxRegret
          {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P}
          policySet n
        ≥ c * (n : ℝ) ^ (-(rStar α γ))
    := by
  classical
  rcases regret_separation α γ u0 cB Cm Co co underlineP policySet hwin hcB hα hγ
      hCm hCo hco hcBm hcBo hup hcB_gpos hcB_gzero huple hπmeas with
    ⟨csep, hcsep, hsep_eventual⟩
  rcases two_point_divergence α γ u0 cB hwin hcB hα hγ hsmall with
    ⟨Cchi, hCchi, hdiv_eventual⟩
  rcases (Causalean.Stat.le_cam_two_point_chisq.1 Cchi hCchi.le) with
    ⟨ctest, hctest, htest_floor⟩
  let c : ℝ := csep * ctest / 2
  refine ⟨c, by positivity, ?_⟩
  have hmemP :
      ∀ᶠ n : ℕ in Filter.atTop,
        LawClass α γ Cm u0 Co co underlineP policySet
          (twoPointWitness α γ u0 cB n 1) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
          ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α)) :=
    witness_membership α γ u0 cB Cm Co co underlineP policySet 1 hα hγ hwin
      hCm hCo hco hcB hcBm hcBo hup hcB_gpos hcB_gzero huple (Or.inl rfl)
  have hmemM :
      ∀ᶠ n : ℕ in Filter.atTop,
        LawClass α γ Cm u0 Co co underlineP policySet
          (twoPointWitness α γ u0 cB n (-1)) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true) ∧
        (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
          ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α)) :=
    witness_membership α γ u0 cB Cm Co co underlineP policySet (-1) hα hγ hwin
      hCm hCo hco hcB hcBm hcBo hup hcB_gpos hcB_gzero huple (Or.inr rfl)
  filter_upwards
    [hsep_eventual, hdiv_eventual, hmemP, hmemM,
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with
    n hsep_n hdiv_n hwitP hwitM hn1
  rcases hwitP with ⟨hclassP0, _hoptP, _hoptM_P⟩
  rcases hwitM with ⟨hclassM0, _hoptP_M, _hoptM⟩
  rcases hdiv_n with ⟨hac_prod0, hint_prod0, _hchi_one, hchi_prod0⟩
  let Pp : ObservedLaw ℝ := twoPointWitness α γ u0 cB n 1
  let Pm : ObservedLaw ℝ := twoPointWitness α γ u0 cB n (-1)
  have hclassP : LawClass α γ Cm u0 Co co underlineP policySet Pp := by
    simpa [Pp] using hclassP0
  have hclassM : LawClass α γ Cm u0 Co co underlineP policySet Pm := by
    simpa [Pm] using hclassM0
  letI : IsProbabilityMeasure Pp.dataMeasure := hclassP.wf.1
  letI : IsProbabilityMeasure Pm.dataMeasure := hclassM.wf.1
  let Sample : Type := Fin n → Observation ℝ
  let Pprod : Measure Sample := Measure.pi fun _ : Fin n => Pp.dataMeasure
  let Qprod : Measure Sample := Measure.pi fun _ : Fin n => Pm.dataMeasure
  have hac_prod : Pprod ≪ Qprod := by
    simpa [Pprod, Qprod, Pp, Pm] using hac_prod0
  have hint_prod :
      Integrable (fun x => ((Pprod.rnDeriv Qprod x).toReal - 1) ^ 2) Qprod := by
    simpa [Pprod, Qprod, Pp, Pm] using hint_prod0
  have hchi_prod : Causalean.Stat.chiSqDiv Pprod Qprod ≤ Cchi := by
    simpa [Pprod, Qprod, Pp, Pm] using hchi_prod0
  have hnposNat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hrate_eq :
      (hLower α γ n) ^ (1 + α) = (n : ℝ) ^ (-(rStar α γ)) := by
    have hDpos : 0 < Dag α γ := Dag_pos_of_nonneg α γ hα hγ
    unfold hLower rStar
    rw [← Real.rpow_mul (le_of_lt hnpos)]
    congr 1
    field_simp [ne_of_gt hDpos]
  change
    c * (n : ℝ) ^ (-(rStar α γ)) ≤
      minimaxRegret
          {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P}
          policySet n
  rcases hπnonempty with ⟨π0, hπ0⟩
  let est0 : (Fin n → Observation ℝ) → Policy ℝ := fun _ => π0
  letI : Nonempty {est : (Fin n → Observation ℝ) → Policy ℝ //
      (∀ sample, est sample ∈ policySet) ∧
        ∀ P : ObservedLaw ℝ,
          Measurable (fun sample : Fin n → Observation ℝ => lawRegret P (est sample))} :=
    ⟨⟨est0, ⟨fun _ => hπ0, fun P => by
      simpa [est0] using
        (measurable_const :
          Measurable (fun _ : Fin n → Observation ℝ => lawRegret P π0))⟩⟩⟩
  rw [minimaxRegret]
  refine le_ciInf ?_
  intro est
  let Rp : ℝ :=
    ∫ sample, lawRegret Pp (est.1 sample) ∂Pprod
  let Rm : ℝ :=
    ∫ sample, lawRegret Pm (est.1 sample) ∂Qprod
  let sep : ℝ := csep * (hLower α γ n) ^ (1 + α)
  let fP : Sample → ℝ := fun sample => lawRegret Pp (est.1 sample)
  let fM : Sample → ℝ := fun sample => lawRegret Pm (est.1 sample)
  let A : Set Sample := {sample | sep ≤ fM sample}
  have hsep_pos : 0 < sep := by
    dsimp [sep]
    exact mul_pos hcsep (Real.rpow_pos_of_pos (hLower_pos_of_pos_nat α γ hnposNat) _)
  have hsep_nonneg : 0 ≤ sep := hsep_pos.le
  have hfP_meas : Measurable fP := by
    simpa [fP, Pprod, Pp] using est.2.2 Pp
  have hfM_meas : Measurable fM := by
    simpa [fM, Qprod, Pm] using est.2.2 Pm
  have hfP_nonneg : 0 ≤ᵐ[Pprod] fP := by
    filter_upwards with sample
    exact lawRegret_nonneg_of_wellformed Pp (est.1 sample) hclassP.wf hclassP.bdd
      (hπmeas (est.1 sample) (est.2.1 sample))
  have hfM_nonneg : 0 ≤ᵐ[Qprod] fM := by
    filter_upwards with sample
    exact lawRegret_nonneg_of_wellformed Pm (est.1 sample) hclassM.wf hclassM.bdd
      (hπmeas (est.1 sample) (est.2.1 sample))
  have hfP_int : Integrable fP Pprod := by
    refine Integrable.of_bound hfP_meas.aestronglyMeasurable 2 ?_
    filter_upwards with sample
    have hnon := lawRegret_nonneg_of_wellformed Pp (est.1 sample) hclassP.wf
      hclassP.bdd (hπmeas (est.1 sample) (est.2.1 sample))
    have hle := lawRegret_le_two_of_wellformed Pp (est.1 sample) hclassP.wf
      hclassP.bdd (hπmeas (est.1 sample) (est.2.1 sample))
    simpa [fP, Real.norm_eq_abs, abs_of_nonneg hnon] using hle
  have hfM_int : Integrable fM Qprod := by
    refine Integrable.of_bound hfM_meas.aestronglyMeasurable 2 ?_
    filter_upwards with sample
    have hnon := lawRegret_nonneg_of_wellformed Pm (est.1 sample) hclassM.wf
      hclassM.bdd (hπmeas (est.1 sample) (est.2.1 sample))
    have hle := lawRegret_le_two_of_wellformed Pm (est.1 sample) hclassM.wf
      hclassM.bdd (hπmeas (est.1 sample) (est.2.1 sample))
    simpa [fM, Real.norm_eq_abs, abs_of_nonneg hnon] using hle
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le measurable_const hfM_meas
  have htest :
      ctest ≤ Pprod.real Aᶜ + Qprod.real A := by
    exact htest_floor Pprod Qprod hac_prod hint_prod hchi_prod A hAmeas
  have hP_mark :
      sep * Pprod.real {sample | sep ≤ fP sample} ≤ Rp := by
    simpa [Rp, fP] using
      (mul_meas_ge_le_integral_of_nonneg (μ := Pprod) hfP_nonneg hfP_int sep)
  have hM_mark :
      sep * Qprod.real A ≤ Rm := by
    simpa [Rm, fM, A] using
      (mul_meas_ge_le_integral_of_nonneg (μ := Qprod) hfM_nonneg hfM_int sep)
  have hcomp_subset : Aᶜ ⊆ {sample | sep ≤ fP sample} := by
    intro sample hsample
    have hm_not : ¬ sep ≤ fM sample := by
      simpa [A] using hsample
    have hm_lt : fM sample < sep := lt_of_not_ge hm_not
    have hsep_sample : sep ≤ max (fP sample) (fM sample) := by
      simpa [sep, fP, fM, Pp, Pm] using hsep_n (est.1 sample) (est.2.1 sample)
    by_contra hp_not
    have hp_lt : fP sample < sep := lt_of_not_ge hp_not
    have hmax_lt : max (fP sample) (fM sample) < sep := max_lt hp_lt hm_lt
    exact not_lt_of_ge hsep_sample hmax_lt
  have hcomp_measure :
      Pprod.real Aᶜ ≤ Pprod.real {sample | sep ≤ fP sample} :=
    measureReal_mono (μ := Pprod) hcomp_subset
      (measure_ne_top Pprod {sample | sep ≤ fP sample})
  have hP_event : sep * Pprod.real Aᶜ ≤ Rp :=
    (mul_le_mul_of_nonneg_left hcomp_measure hsep_nonneg).trans hP_mark
  have hsum_event : sep * (Pprod.real Aᶜ + Qprod.real A) ≤ Rp + Rm := by
    nlinarith [hP_event, hM_mark]
  have hsum_lower : sep * ctest ≤ Rp + Rm := by
    have hmul := mul_le_mul_of_nonneg_left htest hsep_nonneg
    exact hmul.trans hsum_event
  have hmax_lower : sep * ctest / 2 ≤ max Rp Rm := by
    have hsum_max : Rp + Rm ≤ 2 * max Rp Rm := by
      nlinarith [le_max_left Rp Rm, le_max_right Rp Rm]
    nlinarith [hsum_lower, hsum_max]
  have htarget_eq :
      c * (n : ℝ) ^ (-(rStar α γ)) = sep * ctest / 2 := by
    dsimp [c, sep]
    rw [← hrate_eq]
    ring
  let F :
      {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P} → ℝ :=
    fun P =>
      ∫ sample, lawRegret P.1 (est.1 sample)
        ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure)
  letI : Nonempty
      {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P} :=
    ⟨⟨Pp, hclassP⟩⟩
  have hF_bdd : BddAbove (Set.range F) := by
    refine ⟨2, ?_⟩
    rintro y ⟨Psub, rfl⟩
    letI : IsProbabilityMeasure Psub.1.dataMeasure := Psub.2.wf.1
    let f : (Fin n → Observation ℝ) → ℝ :=
      fun sample => lawRegret Psub.1 (est.1 sample)
    have hf_meas : Measurable f := by
      simpa [f] using est.2.2 Psub.1
    have hf_int : Integrable f (Measure.pi fun _ : Fin n => Psub.1.dataMeasure) := by
      refine Integrable.of_bound hf_meas.aestronglyMeasurable 2 ?_
      filter_upwards with sample
      have hnon := lawRegret_nonneg_of_wellformed Psub.1 (est.1 sample)
        Psub.2.wf Psub.2.bdd (hπmeas (est.1 sample) (est.2.1 sample))
      have hle := lawRegret_le_two_of_wellformed Psub.1 (est.1 sample)
        Psub.2.wf Psub.2.bdd (hπmeas (est.1 sample) (est.2.1 sample))
      simpa [f, Real.norm_eq_abs, abs_of_nonneg hnon] using hle
    calc
      F Psub = ∫ sample, f sample ∂(Measure.pi fun _ : Fin n => Psub.1.dataMeasure) := by
        rfl
      _ ≤ ∫ _sample, (2 : ℝ) ∂(Measure.pi fun _ : Fin n => Psub.1.dataMeasure) := by
        refine integral_mono hf_int (integrable_const (2 : ℝ)) ?_
        intro sample
        exact lawRegret_le_two_of_wellformed Psub.1 (est.1 sample)
          Psub.2.wf Psub.2.bdd (hπmeas (est.1 sample) (est.2.1 sample))
      _ = 2 := by simp
  have hp_sup :
      Rp ≤
        (⨆ P : {P : ObservedLaw ℝ |
            LawClass α γ Cm u0 Co co underlineP policySet P},
          ∫ sample, lawRegret P.1 (est.1 sample)
            ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure)) := by
    simpa [Rp, Pprod, Pp] using
      (le_ciSup hF_bdd
        (⟨Pp, hclassP⟩ :
          {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P}))
  have hm_sup :
      Rm ≤
        (⨆ P : {P : ObservedLaw ℝ |
            LawClass α γ Cm u0 Co co underlineP policySet P},
          ∫ sample, lawRegret P.1 (est.1 sample)
            ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure)) := by
    simpa [Rm, Qprod, Pm] using
      (le_ciSup hF_bdd
        (⟨Pm, hclassM⟩ :
          {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P}))
  have hmax_sup :
      max Rp Rm ≤
        (⨆ P : {P : ObservedLaw ℝ |
            LawClass α γ Cm u0 Co co underlineP policySet P},
          ∫ sample, lawRegret P.1 (est.1 sample)
            ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure)) :=
    max_le hp_sup hm_sup
  calc
    c * (n : ℝ) ^ (-(rStar α γ)) = sep * ctest / 2 := htarget_eq
    _ ≤ max Rp Rm := hmax_lower
    _ ≤
        (⨆ P : {P : ObservedLaw ℝ |
            LawClass α γ Cm u0 Co co underlineP policySet P},
          ∫ sample, lawRegret P.1 (est.1 sample)
            ∂(Measure.pi fun _ : Fin n => P.1.dataMeasure)) := hmax_sup

-- @node: thm:rate-characterization
/-- `thm:rate-characterization` (HEADLINE, lower-bound only).
`M_n ≥ c n^{-(1+α)/(2+α+β_{α,γ})}`. -/
theorem rate_characterization (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (Policy ℝ))
    (hwin : MarginWindow u0) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hCm : 0 < Cm) (hCo : 0 < Co) (hco : 0 < co) (hcB : 0 < cB)
    (hcBm : cB ≤ Cm) (hcBo : cB ≤ Co) (hup : 0 < underlineP)
    -- note c_B overlap-decay smallness (def:two-point-witness constant choice)
    (hcB_gpos : 0 < γ → 0 < α → cB ≤ Co * co ^ (-(α / γ)))
    (hcB_gzero : 0 < γ → α = 0 → cB ≤ Co * (4 : ℝ) ^ (-(1 / γ)))
    (huple : underlineP ≤ 1 / 4) (hsmall : 8 * cB < Real.log 5)
    (hπnonempty : policySet.Nonempty)
    (hπmeas : ∀ π ∈ policySet, Measurable π) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      minimaxRegret
          {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P}
          policySet n
        ≥ c * (n : ℝ) ^ (-((1 + α) / (2 + α + betaAG α γ))) := by
  simpa [rStar, Dag] using
    minimax_lower α γ u0 cB Cm Co co underlineP policySet hwin hα hγ hCm hCo
      hco hcB hcBm hcBo hup hcB_gpos hcB_gzero huple hsmall hπnonempty hπmeas

end CausalSmith.Stat.PolicyRegretMarginOverlap
