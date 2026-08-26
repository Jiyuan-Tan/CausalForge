/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.BernoulliMeasure
import Mathlib.Probability.ProductMeasure

/-!
# A nested finite-product count bound

This module proves the zero-safe reciprocal-count estimate used by a fixed
stratum ratio.  It enumerates the outer and inner index sets, exposing the
conditional binomial law of the inner count without using a conditional
probability API.
-/

namespace Causalean.Stat.FiniteStratumMarkedRatioMse

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability

/-- The finite set of product coordinates whose observations belong to a set. -/
noncomputable def sampleIndexSet {I Omega : Type*} [Fintype I]
    (z : I → Omega) (S : Set Omega) : Finset I := by
  classical
  exact Finset.univ.filter fun i => z i ∈ S

private def nestedCountEvent {I Omega : Type*} [Fintype I] [DecidableEq I]
    (C R : Set Omega) (U V : Finset I) : Set (I → Omega) :=
  {z | sampleIndexSet z C = U ∧ sampleIndexSet z R = V}

private lemma sampleIndexSet_mono {I Omega : Type*} [Fintype I] [DecidableEq I]
    (z : I → Omega) {R C : Set Omega} (hRC : R ⊆ C) :
    sampleIndexSet z R ⊆ sampleIndexSet z C := by
  classical
  intro i hi
  simp only [sampleIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hRC hi

private lemma nestedCountEvent_eq_pi {I Omega : Type*} [Fintype I] [DecidableEq I]
    (C R : Set Omega) (hRC : R ⊆ C) (U V : Finset I) (hVU : V ⊆ U) :
    nestedCountEvent C R U V =
      Set.univ.pi (fun i => if i ∈ V then R else if i ∈ U then C \ R else Cᶜ) := by
  classical
  ext z
  simp only [nestedCountEvent, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨hC, hR⟩ i
    have hCi : z i ∈ C ↔ i ∈ U := by
      have hi := congrArg (fun W : Finset I => i ∈ W) hC
      simpa [sampleIndexSet] using hi
    have hRi : z i ∈ R ↔ i ∈ V := by
      have hi := congrArg (fun W : Finset I => i ∈ W) hR
      simpa [sampleIndexSet] using hi
    by_cases hiV : i ∈ V
    · simp [hiV, hRi.mpr hiV]
    · by_cases hiU : i ∈ U
      · simp [hiV, hiU, hCi.mpr hiU, hRi.not.mpr hiV]
      · simp [hiV, hiU, hCi.not.mpr hiU]
  · intro h
    constructor
    · apply Finset.ext
      intro i
      simp only [sampleIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := h i
      by_cases hiV : i ∈ V
      · have hiU := hVU hiV
        simp only [hiV, if_true] at hi
        exact ⟨fun _ => hiU, fun _ => hRC hi⟩
      · by_cases hiU : i ∈ U
        · simp only [hiV, if_false, hiU, if_true, Set.mem_diff] at hi
          exact ⟨fun _ => hiU, fun _ => hi.1⟩
        · simp only [hiV, if_false, hiU, Set.mem_compl_iff] at hi
          exact ⟨fun hmem => (hi hmem).elim, fun hmem => (hiU hmem).elim⟩
    · apply Finset.ext
      intro i
      simp only [sampleIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := h i
      by_cases hiV : i ∈ V
      · simp only [hiV, if_true] at hi
        exact ⟨fun _ => hiV, fun _ => hi⟩
      · by_cases hiU : i ∈ U
        · simp only [hiV, if_false, hiU, if_true, Set.mem_diff] at hi
          exact ⟨fun hmem => (hi.2 hmem).elim, fun hmem => (hiV hmem).elim⟩
        · simp only [hiV, if_false, hiU, Set.mem_compl_iff] at hi
          exact ⟨fun hmem => (hi (hRC hmem)).elim, fun hmem => (hiV hmem).elim⟩

private lemma prod_nested_count_partition {I : Type*} [Fintype I] [DecidableEq I]
    (U V : Finset I) (hVU : V ⊆ U) (r s q : ℝ≥0∞) :
    (∏ i : I, if i ∈ V then r else if i ∈ U then s else q) =
      r ^ V.card * s ^ (U.card - V.card) *
        q ^ (Fintype.card I - U.card) := by
  classical
  change (∏ i ∈ (Finset.univ : Finset I),
    if i ∈ V then r else if i ∈ U then s else q) = _
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_ite]
  have h₁ : ((Finset.univ : Finset I).filter (fun i => i ∉ V)).filter
      (fun i => i ∈ U) = U \ V := by
    ext i
    simp [and_comm]
  have h₂ : ((Finset.univ : Finset I).filter (fun i => i ∉ V)).filter
      (fun i => i ∉ U) = (Finset.univ : Finset I) \ U := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hiU
      exact ⟨fun hiV => hiU (hVU hiV), hiU⟩
  rw [h₁, h₂]
  simp [Finset.prod_const, Finset.card_sdiff_of_subset hVU,
    Finset.card_sdiff_of_subset (Finset.subset_univ U)]
  ring

private lemma measure_nestedCountEvent {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (C R : Set Omega) (hC : MeasurableSet C) (hR : MeasurableSet R)
    (hRC : R ⊆ C) (U V : Finset I) (hVU : V ⊆ U) :
    (Measure.pi (fun _ : I => mu)) (nestedCountEvent C R U V) =
      mu R ^ V.card * mu (C \ R) ^ (U.card - V.card) *
        mu Cᶜ ^ (Fintype.card I - U.card) := by
  rw [nestedCountEvent_eq_pi C R hRC U V hVU, Measure.pi_pi]
  have hfun : (fun i : I =>
      mu (if i ∈ V then R else if i ∈ U then C \ R else Cᶜ)) =
      fun i => if i ∈ V then mu R else if i ∈ U then mu (C \ R) else mu Cᶜ := by
    funext i
    by_cases hiV : i ∈ V <;> by_cases hiU : i ∈ U <;> simp [hiV, hiU]
  rw [hfun]
  exact prod_nested_count_partition U V hVU _ _ _

private lemma measurableSet_nestedCountEvent {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega] (C R : Set Omega)
    (hC : MeasurableSet C) (hR : MeasurableSet R) (hRC : R ⊆ C)
    (U V : Finset I) :
    MeasurableSet (nestedCountEvent C R U V) := by
  classical
  by_cases hVU : V ⊆ U
  · rw [nestedCountEvent_eq_pi C R hRC U V hVU]
    apply MeasurableSet.univ_pi
    intro i
    by_cases hiV : i ∈ V
    · simp [hiV, hR]
    · by_cases hiU : i ∈ U
      · simp [hiV, hiU, hC, hR]
      · simp [hiV, hiU, hC]
  · have hempty : nestedCountEvent C R U V = ∅ := by
      ext z
      simp only [nestedCountEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      intro hz
      exact hVU (hz.2 ▸ hz.1 ▸ sampleIndexSet_mono z hRC)
    rw [hempty]
    exact MeasurableSet.empty

private lemma binomial_first_moment (m : Nat) (p : Real) :
    (∑ t ∈ Finset.range (m + 1), binomialWeight m p t * (t : Real)) =
      (m : Real) * p := by
  by_cases hm : m = 0
  · subst m
    simp [binomialWeight]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    calc
      (∑ t ∈ Finset.range (m + 1), binomialWeight m p t * (t : Real)) =
          ∑ j ∈ Finset.range m,
            (m : Real) * p * ((Nat.choose (m - 1) j : Real) *
              p ^ j * (1 - p) ^ ((m - 1) - j)) := by
        rw [Finset.sum_range_succ' (f := fun t =>
          binomialWeight m p t * (t : Real))]
        simp only [Nat.cast_zero, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hchoose : (Nat.choose m (j + 1) : Real) * (j + 1 : Nat) =
            (m : Real) * (Nat.choose (m - 1) j : Real) := by
          rw [show m = (m - 1) + 1 by omega]
          exact_mod_cast (Nat.add_one_mul_choose_eq (m - 1) j).symm
        have hsub : m - (j + 1) = (m - 1) - j := by omega
        rw [binomialWeight, hsub, pow_succ]
        push_cast
        rw [show (j : Real) + 1 = ((j + 1 : Nat) : Real) by norm_num]
        calc
          (Nat.choose m (j + 1) : Real) * (p ^ j * p) *
              (1 - p) ^ (m - 1 - j) * ((j + 1 : Nat) : Real) =
              ((Nat.choose m (j + 1) : Real) * (j + 1 : Nat)) * p *
                (p ^ j * (1 - p) ^ (m - 1 - j)) := by ring
          _ = _ := by rw [hchoose]; ring
      _ = (m : Real) * p *
          ∑ j ∈ Finset.range m, (Nat.choose (m - 1) j : Real) *
            p ^ j * (1 - p) ^ ((m - 1) - j) := by rw [Finset.mul_sum]
      _ = (m : Real) * p := by
        rw [show ∑ j ∈ Finset.range m, (Nat.choose (m - 1) j : Real) *
            p ^ j * (1 - p) ^ ((m - 1) - j) = (p + (1 - p)) ^ (m - 1) by
          rw [show m = (m - 1) + 1 by omega]
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro j hj
          ring]
        ring

private lemma nested_binomial_count_bound (m : Nat) (p rho : Real)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (∑ t ∈ Finset.range (m + 1), binomialWeight m p t * (t : Real) ^ 2 *
      (∑ l ∈ Finset.range (t + 1), binomialWeight t rho l *
        (if 0 < l then (l : Real)⁻¹ else 0))) ≤
      2 * (m : Real) * p / rho := by
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have houter (t : Nat) (ht : t ∈ Finset.range (m + 1)) :
      0 ≤ binomialWeight m p t := by
    unfold binomialWeight
    positivity
  calc
    _ ≤ ∑ t ∈ Finset.range (m + 1),
        binomialWeight m p t * (t : Real) ^ 2 *
          (2 / (((t + 1 : Nat) : Real) * rho)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (binomial_totalized_inverse_count_le t rho hrho hrho1)
        (mul_nonneg (houter t ht) (sq_nonneg (t : Real)))
    _ ≤ ∑ t ∈ Finset.range (m + 1),
        (2 / rho) * (binomialWeight m p t * (t : Real)) := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        simp
      · have htpos : (0 : Real) < t := by exact_mod_cast Nat.pos_of_ne_zero ht0
        have ht1pos : (0 : Real) < (t + 1 : Nat) := by positivity
        have hfrac : (t : Real) / (t + 1 : Nat) ≤ 1 := by
          exact (div_le_one ht1pos).2 (by norm_num)
        have hnonneg : 0 ≤ binomialWeight m p t * (t : Real) :=
          mul_nonneg (houter t ht) htpos.le
        calc
          binomialWeight m p t * (t : Real) ^ 2 *
              (2 / (((t + 1 : Nat) : Real) * rho)) =
            (2 / rho) * (binomialWeight m p t * (t : Real)) *
              ((t : Real) / (t + 1 : Nat)) := by
                field_simp
                <;> ring
          _ ≤ (2 / rho) * (binomialWeight m p t * (t : Real)) * 1 := by
            gcongr
          _ = _ := by ring
    _ = (2 / rho) *
        (∑ t ∈ Finset.range (m + 1), binomialWeight m p t * (t : Real)) := by
      rw [Finset.mul_sum]
    _ = 2 * (m : Real) * p / rho := by
      rw [binomial_first_moment]
      field_simp

/-- [Measurable outer and inner events](hyp:hC,hR), [nesting of the inner event
inside the outer event](hyp:hRC), [a positive overlap margin](hyp:hepsilon), and
[inner-event mass at least that margin times outer-event mass](hyp:hoverlap)
imply that [the expected squared outer count times the zero-safe inverse inner
count is at most twice sample size times outer-event mass divided by the
margin](goal). -/
lemma integral_nested_count_sq_mul_totalized_inverse_le {m : Nat}
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (C R : Set Omega) (hC : MeasurableSet C) (hR : MeasurableSet R)
    (hRC : R ⊆ C) (epsilon : Real) (hepsilon : 0 < epsilon)
    (hoverlap : epsilon * (mu C).toReal ≤ (mu R).toReal) :
    ∫ z : Fin m → Omega, ((sampleIndexSet z C).card : Real) ^ 2 *
        (if 0 < (sampleIndexSet z R).card then
          ((sampleIndexSet z R).card : Real)⁻¹ else 0)
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      2 * (m : Real) * (mu C).toReal / epsilon := by
  classical
  let p : Real := (mu C).toReal
  by_cases hp : p = 0
  · have hCzero : mu C = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (mu C)).mp (by simpa [p] using hp) with h | h
      · exact h
      · exact (measure_ne_top mu C h).elim
    have hcount_zero : ∀ᵐ z ∂Measure.pi (fun _ : Fin m => mu),
        (sampleIndexSet z C).card = 0 := by
      have hcoord (i : Fin m) : ∀ᵐ z ∂Measure.pi (fun _ : Fin m => mu), z i ∉ C := by
        exact measure_eq_zero_iff_ae_notMem.mp
          ((measurePreserving_eval (fun _ : Fin m => mu) i).preimage_null hCzero)
      have hall : ∀ᵐ z ∂Measure.pi (fun _ : Fin m => mu), ∀ i, z i ∉ C :=
        ae_all_iff.mpr hcoord
      filter_upwards [hall] with z hz
      apply Finset.card_eq_zero.mpr
      ext i
      simp [sampleIndexSet, hz i]
    rw [show 2 * (m : Real) * (mu C).toReal / epsilon = 0 by simp [p, hp]]
    exact (le_of_eq (integral_eq_zero_of_ae (by
      filter_upwards [hcount_zero] with z hz
      simp [hz])))
  · have hp0 : 0 < p := lt_of_le_of_ne (ENNReal.toReal_nonneg) (Ne.symm hp)
    have hp1 : p ≤ 1 := by
      dsimp [p]
      calc
        (mu C).toReal ≤ (mu Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top mu Set.univ)
            (measure_mono (Set.subset_univ C))
        _ = 1 := by simp
    let rho : Real := (mu R).toReal / p
    have hrho : 0 < rho := by
      have hRpos : 0 < (mu R).toReal := lt_of_lt_of_le (mul_pos hepsilon hp0) hoverlap
      exact div_pos hRpos hp0
    have hrho1 : rho ≤ 1 := by
      apply (div_le_one hp0).2
      exact ENNReal.toReal_mono (measure_ne_top mu C) (measure_mono hRC)
    have hpR : (mu R).toReal = p * rho := by
      dsimp [rho]
      field_simp
    have hpDiff : (mu (C \ R)).toReal = p * (1 - rho) := by
      have hdiff : mu C = mu R + mu (C \ R) := by
        rw [← measure_union (Set.disjoint_sdiff_right) (hC.diff hR)]
        congr 1
        exact (Set.union_diff_cancel hRC).symm
      have hreal : p = (mu R).toReal + (mu (C \ R)).toReal := by
        dsimp [p]
        rw [hdiff, ENNReal.toReal_add (measure_ne_top mu R) (measure_ne_top mu (C \ R))]
      rw [hpR] at hreal
      linarith
    have hpCompl : (mu Cᶜ).toReal = 1 - p := by
      rw [measure_compl hC (measure_ne_top mu C), ENNReal.toReal_sub_of_le]
      · simp [p]
      · exact measure_mono (Set.subset_univ C)
      · exact measure_ne_top mu Set.univ
    have hfun (z : Fin m → Omega) :
        ((sampleIndexSet z C).card : Real) ^ 2 *
            (if 0 < (sampleIndexSet z R).card then
              ((sampleIndexSet z R).card : Real)⁻¹ else 0) =
          ∑ U : Finset (Fin m), ∑ V : Finset (Fin m),
            (nestedCountEvent C R U V).indicator
              (fun _ => (U.card : Real) ^ 2 *
                (if 0 < V.card then (V.card : Real)⁻¹ else 0)) z := by
      rw [Finset.sum_eq_single (sampleIndexSet z C)]
      · rw [Finset.sum_eq_single (sampleIndexSet z R)]
        · simp [nestedCountEvent]
        · intro V hV hne
          rw [Set.indicator_of_notMem]
          intro hz
          exact hne hz.2.symm
        · simp
      · intro U hU hne
        apply Finset.sum_eq_zero
        intro V hV
        rw [Set.indicator_of_notMem]
        intro hz
        exact hne hz.1.symm
      · simp
    rw [show (∫ z : Fin m → Omega, ((sampleIndexSet z C).card : Real) ^ 2 *
          (if 0 < (sampleIndexSet z R).card then
            ((sampleIndexSet z R).card : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin m => mu))) =
        ∑ U : Finset (Fin m), ∑ V : Finset (Fin m),
          ((Measure.pi (fun _ : Fin m => mu)) (nestedCountEvent C R U V)).toReal *
            ((U.card : Real) ^ 2 *
              (if 0 < V.card then (V.card : Real)⁻¹ else 0)) by
      rw [integral_congr_ae (Filter.Eventually.of_forall hfun), integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro U hU
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro V hV
          rw [integral_indicator (measurableSet_nestedCountEvent C R hC hR hRC U V),
            setIntegral_const]
          rfl
        · intro V hV
          exact (integrable_const _).indicator
            (measurableSet_nestedCountEvent C R hC hR hRC U V)
      · intro U hU
        exact integrable_finsetSum Finset.univ fun V hV =>
          (integrable_const _).indicator
            (measurableSet_nestedCountEvent C R hC hR hRC U V)]
    calc
      _ = ∑ U ∈ (Finset.univ : Finset (Finset (Fin m))),
          ∑ V ∈ U.powerset,
            (p * rho) ^ V.card * (p * (1 - rho)) ^ (U.card - V.card) *
              (1 - p) ^ (m - U.card) *
              ((U.card : Real) ^ 2 *
                (if 0 < V.card then (V.card : Real)⁻¹ else 0)) := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [show (∑ V : Finset (Fin m),
            ((Measure.pi (fun _ : Fin m => mu)) (nestedCountEvent C R U V)).toReal *
              ((U.card : Real) ^ 2 *
                (if 0 < V.card then (V.card : Real)⁻¹ else 0))) =
            ∑ V ∈ U.powerset,
              ((Measure.pi (fun _ : Fin m => mu)) (nestedCountEvent C R U V)).toReal *
                ((U.card : Real) ^ 2 *
                  (if 0 < V.card then (V.card : Real)⁻¹ else 0)) by
          apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro V hV hnot
          have hnotVU : ¬ V ⊆ U := by simpa using hnot
          have hempty : nestedCountEvent C R U V = ∅ := by
            ext z
            simp only [nestedCountEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false,
              iff_false]
            intro hz
            exact hnotVU (hz.2 ▸ hz.1 ▸ sampleIndexSet_mono z hRC)
          simp [hempty]]
        apply Finset.sum_congr rfl
        intro V hV
        have hVU := Finset.mem_powerset.mp hV
        rw [measure_nestedCountEvent mu C R hC hR hRC U V hVU,
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_pow, ENNReal.toReal_pow, hpR, hpDiff, hpCompl]
        simp only [Fintype.card_fin]
      _ = ∑ t ∈ Finset.range (m + 1), binomialWeight m p t * (t : Real) ^ 2 *
          (∑ l ∈ Finset.range (t + 1), binomialWeight t rho l *
            (if 0 < l then (l : Real)⁻¹ else 0)) := by
        let G : Nat → Real := fun t => p ^ t * (1 - p) ^ (m - t) *
          (t : Real) ^ 2 *
            (∑ l ∈ Finset.range (t + 1), binomialWeight t rho l *
              (if 0 < l then (l : Real)⁻¹ else 0))
        have hinner (U : Finset (Fin m)) :
            (∑ V ∈ U.powerset,
              (p * rho) ^ V.card * (p * (1 - rho)) ^ (U.card - V.card) *
                (1 - p) ^ (m - U.card) *
                ((U.card : Real) ^ 2 *
                  (if 0 < V.card then (V.card : Real)⁻¹ else 0))) = G U.card := by
          rw [show ∑ V ∈ U.powerset,
              (p * rho) ^ V.card * (p * (1 - rho)) ^ (U.card - V.card) *
                (1 - p) ^ (m - U.card) *
                ((U.card : Real) ^ 2 *
                  (if 0 < V.card then (V.card : Real)⁻¹ else 0)) =
              p ^ U.card * (1 - p) ^ (m - U.card) * (U.card : Real) ^ 2 *
                ∑ V ∈ U.powerset, rho ^ V.card *
                  (1 - rho) ^ (U.card - V.card) *
                    (if 0 < V.card then (V.card : Real)⁻¹ else 0) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro V hV
            rw [mul_pow, mul_pow]
            have hcard : V.card + (U.card - V.card) = U.card :=
              Nat.add_sub_of_le (Finset.card_le_card (Finset.mem_powerset.mp hV))
            calc
              p ^ V.card * rho ^ V.card *
                    (p ^ (U.card - V.card) * (1 - rho) ^ (U.card - V.card)) *
                    (1 - p) ^ (m - U.card) *
                    ((U.card : Real) ^ 2 *
                      (if 0 < V.card then (V.card : Real)⁻¹ else 0)) =
                  (p ^ V.card * p ^ (U.card - V.card)) *
                    (1 - p) ^ (m - U.card) * (U.card : Real) ^ 2 *
                    (rho ^ V.card * (1 - rho) ^ (U.card - V.card) *
                      (if 0 < V.card then (V.card : Real)⁻¹ else 0)) := by ring
              _ = _ := by rw [← pow_add, hcard]]
          let F : Nat → Real := fun l => rho ^ l * (1 - rho) ^ (U.card - l) *
            (if 0 < l then (l : Real)⁻¹ else 0)
          rw [show (∑ V ∈ U.powerset, rho ^ V.card *
              (1 - rho) ^ (U.card - V.card) *
                (if 0 < V.card then (V.card : Real)⁻¹ else 0)) =
              ∑ l ∈ Finset.range (U.card + 1), (Nat.choose U.card l : Real) * F l by
            change (∑ V ∈ U.powerset, F V.card) = _
            rw [Finset.sum_powerset_apply_card F]
            simp only [nsmul_eq_mul]]
          simp only [G, F, binomialWeight]
          congr 2
          funext l
          ring
        simp_rw [hinner]
        have huniv : (Finset.univ : Finset (Finset (Fin m))) =
            (Finset.univ : Finset (Fin m)).powerset := by ext U; simp
        rw [huniv, Finset.sum_powerset_apply_card G]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, G,
          binomialWeight]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ ≤ 2 * (m : Real) * p / rho :=
        nested_binomial_count_bound m p rho hp0.le hp1 hrho hrho1
      _ ≤ 2 * (m : Real) * p / epsilon := by
        have herho : epsilon ≤ rho := by
          rw [show epsilon = epsilon * p / p by field_simp]
          exact div_le_div_of_nonneg_right hoverlap hp0.le
        gcongr

end Causalean.Stat.FiniteStratumMarkedRatioMse
