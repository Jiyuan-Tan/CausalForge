/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Minimax.ChiSquared
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Product / i.i.d. tensorization of the χ²-divergence

General, measure-theoretic facts about the χ²-divergence under products that carry
no dependence on any particular statistical model.  Staged here (CausalSmith side)
out of the policy-regret converse derivation; the χ² analogue of
`Causalean.Mathlib.InformationTheory.ProductKLLeCam`.  Promotion to
`Causalean/` is gated on a second consumer.

* `one_add_chiSqDiv_pi_iid_general` — the `n`-fold i.i.d. tensorization
  `1 + χ²(μ^⊗n ‖ ν^⊗n) = (1 + χ²(μ‖ν))^n`, with no `Fintype` assumption on the
  observation space.
* `absolutelyContinuous_of_partition_restrict_eq_smul` and
  `integrable_sq_rnDeriv_of_partition_restrict_eq_smul` — side-condition
  extraction from the same finite-partition proportional-restriction hypotheses.
* `chiSqDiv_eq_sum_partition_of_restrict_eq_smul` — the χ²-divergence on a finite
  measurable partition on whose cells `μ` is a constant multiple of `ν`.
-/

namespace CausalSmith.Mathlib.ProductChiSquared

open MeasureTheory
open scoped BigOperators

/-- Product χ²-integrability from the two marginal χ²-integrability hypotheses.
This is the side-condition construction used to iterate
`Causalean.Stat.chiSqDiv_prod` without assuming the sample space is finite. -/
private lemma chiSqDiv_prod_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂)
    (hint₁ : Integrable (fun x => ((μ₁.rnDeriv ν₁ x).toReal - 1) ^ (2 : ℕ)) ν₁)
    (hint₂ : Integrable (fun y => ((μ₂.rnDeriv ν₂ y).toReal - 1) ^ (2 : ℕ)) ν₂) :
    Integrable
      (fun z : α × β =>
        (((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) z).toReal - 1) ^ (2 : ℕ))
      (ν₁.prod ν₂) := by
  set p₁ : α → ℝ := fun x => (μ₁.rnDeriv ν₁ x).toReal with hp₁_def
  set p₂ : β → ℝ := fun y => (μ₂.rnDeriv ν₂ y).toReal with hp₂_def
  have hp₁_int : Integrable p₁ ν₁ := Measure.integrable_toReal_rnDeriv
  have hp₂_int : Integrable p₂ ν₂ := Measure.integrable_toReal_rnDeriv
  have hp₁_sq : Integrable (fun x => p₁ x ^ (2 : ℕ)) ν₁ := by
    have hexp :
        (fun x => p₁ x ^ (2 : ℕ)) =
          fun x => (p₁ x - 1) ^ (2 : ℕ) + (2 * p₁ x - 1) := by
      funext x
      ring
    rw [hexp]
    exact hint₁.add ((hp₁_int.const_mul 2).sub (integrable_const 1))
  have hp₂_sq : Integrable (fun y => p₂ y ^ (2 : ℕ)) ν₂ := by
    have hexp :
        (fun y => p₂ y ^ (2 : ℕ)) =
          fun y => (p₂ y - 1) ^ (2 : ℕ) + (2 * p₂ y - 1) := by
      funext y
      ring
    rw [hexp]
    exact hint₂.add ((hp₂_int.const_mul 2).sub (integrable_const 1))
  set P : α × β → ℝ :=
    fun z => ((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) z).toReal with hP_def
  have hdens : (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂)
      =ᵐ[ν₁.prod ν₂] fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 :=
    Causalean.Stat.rnDeriv_prod_eq μ₁ ν₁ μ₂ ν₂ h₁ h₂
  have hPeq : (fun z => P z ^ (2 : ℕ))
      =ᵐ[ν₁.prod ν₂] fun z => (p₁ z.1 ^ (2 : ℕ)) * (p₂ z.2 ^ (2 : ℕ)) := by
    filter_upwards [hdens] with z hz
    rw [hP_def]
    simp only [hz, ENNReal.toReal_mul, hp₁_def, hp₂_def]
    ring
  have hPint :
      Integrable
        (fun z : α × β => (p₁ z.1 ^ (2 : ℕ)) * (p₂ z.2 ^ (2 : ℕ)))
        (ν₁.prod ν₂) :=
    Integrable.mul_prod hp₁_sq hp₂_sq
  have hPint' : Integrable (fun z => P z ^ (2 : ℕ)) (ν₁.prod ν₂) :=
    hPint.congr hPeq.symm
  have hP_int : Integrable P (ν₁.prod ν₂) := Measure.integrable_toReal_rnDeriv
  have hPdev : Integrable (fun z => (P z - 1) ^ (2 : ℕ)) (ν₁.prod ν₂) := by
    have hexp :
        (fun z => (P z - 1) ^ (2 : ℕ)) =
          fun z => P z ^ (2 : ℕ) + (-(2 * P z) + 1) := by
      funext z
      ring
    rw [hexp]
    exact hPint'.add (((hP_int.const_mul 2).neg).add (integrable_const 1))
  simpa [P, hP_def] using hPdev

/-- The χ²-integrability side condition for an arbitrary finite iid product,
proved without any finiteness assumption on the observation space. -/
lemma chiSqDiv_pi_iid_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ (2 : ℕ)) ν)
    (n : ℕ) :
    Integrable
      (fun sample : Fin n → Ω =>
        (((Measure.pi (fun _ : Fin n => μ)).rnDeriv
            (Measure.pi (fun _ : Fin n => ν)) sample).toReal - 1) ^ (2 : ℕ))
      (Measure.pi (fun _ : Fin n => ν)) := by
  induction n with
  | zero =>
      have hpi : Measure.pi (fun _ : Fin 0 => μ) = Measure.pi (fun _ : Fin 0 => ν) := by
        rw [Measure.pi_of_empty (fun _ : Fin 0 => μ),
          Measure.pi_of_empty (fun _ : Fin 0 => ν)]
      rw [hpi]
      refine (integrable_zero (Fin 0 → Ω) ℝ _).congr ?_
      filter_upwards [(Measure.pi (fun _ : Fin 0 => ν)).rnDeriv_self] with x hx
      simp [hx]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
      have hμ : (Measure.pi (fun _ : Fin (n + 1) => μ)).map e =
          μ.prod (Measure.pi (fun _ : Fin n => μ)) :=
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
      have hν : (Measure.pi (fun _ : Fin (n + 1) => ν)).map e =
          ν.prod (Measure.pi (fun _ : Fin n => ν)) :=
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
      have hac_pi :
          Measure.pi (fun _ : Fin n => μ) ≪ Measure.pi (fun _ : Fin n => ν) :=
        Causalean.Stat.pi_iid_absolutelyContinuous μ ν hac n
      have hprod : Integrable
          (fun z : Ω × (Fin n → Ω) =>
            (((μ.prod (Measure.pi (fun _ : Fin n => μ))).rnDeriv
                (ν.prod (Measure.pi (fun _ : Fin n => ν))) z).toReal - 1) ^ (2 : ℕ))
          (ν.prod (Measure.pi (fun _ : Fin n => ν))) :=
        chiSqDiv_prod_integrable μ ν (Measure.pi (fun _ : Fin n => μ))
          (Measure.pi (fun _ : Fin n => ν)) hac hac_pi hint ih
      let g : Ω × (Fin n → Ω) → ℝ := fun z =>
        (((((Measure.pi (fun _ : Fin (n + 1) => μ)).map e).rnDeriv
            ((Measure.pi (fun _ : Fin (n + 1) => ν)).map e) z).toReal - 1) ^ (2 : ℕ))
      have hmap : Integrable g ((Measure.pi (fun _ : Fin (n + 1) => ν)).map e) := by
        dsimp [g]
        rw [hμ, hν]
        exact hprod
      have hcomp := (integrable_map_equiv e g).1 hmap
      refine hcomp.congr ?_
      have hrn := e.measurableEmbedding.rnDeriv_map
        (Measure.pi (fun _ : Fin (n + 1) => μ))
        (Measure.pi (fun _ : Fin (n + 1) => ν))
      filter_upwards [hrn] with x hx
      dsimp [g]
      rw [hx]

/-- General `n`-fold i.i.d. χ² tensorization, without a `Fintype` assumption on
the observation space. -/
lemma one_add_chiSqDiv_pi_iid_general
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ (2 : ℕ)) ν)
    (n : ℕ) :
    1 + Causalean.Stat.chiSqDiv
        (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
      = (1 + Causalean.Stat.chiSqDiv μ ν) ^ n := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty (fun _ : Fin 0 => μ),
        Measure.pi_of_empty (fun _ : Fin 0 => ν), Causalean.Stat.chiSqDiv_self]
      simp
  | succ n ih =>
      have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
      have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
      rw [← Causalean.Stat.chiSqDiv_map_measurableEquiv
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0), hμ, hν]
      have hac_pi :
          Measure.pi (fun _ : Fin n => μ) ≪ Measure.pi (fun _ : Fin n => ν) :=
        Causalean.Stat.pi_iid_absolutelyContinuous μ ν hac n
      have hint_pi := chiSqDiv_pi_iid_integrable μ ν hac hint n
      rw [Causalean.Stat.chiSqDiv_prod μ ν (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν)) hac hac_pi hint hint_pi, ih, pow_succ]
      ring

-- @node: lem:partition-restrict-ac
/-- Absolute continuity from a finite measurable partition on whose cells `μ` is a
constant multiple of `ν`. -/
lemma absolutelyContinuous_of_partition_restrict_eq_smul
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ ν : Measure Ω)
    (s : Fin k → Set Ω) (c : Fin k → ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (_hc_nonneg : ∀ i, 0 ≤ c i)
    (hrestrict : ∀ i, μ.restrict (s i) = ENNReal.ofReal (c i) • ν.restrict (s i)) :
    μ ≪ ν := by
  classical
  let d : Ω → ENNReal :=
    fun x => ∑ i : Fin k, (s i).indicator (fun _ => ENNReal.ofReal (c i)) x
  have hμ_sum : μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := by
    have h := Measure.restrict_iUnion (μ := μ) (s := s) hdisj hs
    rw [hcover, Measure.restrict_univ] at h
    exact h
  have hν_density_sum :
      ν.withDensity d =
        Measure.sum (fun i : Fin k =>
          ν.withDensity ((s i).indicator (fun _ => ENNReal.ofReal (c i)))) := by
    ext t ht
    rw [withDensity_apply _ ht]
    simp_rw [Measure.sum_apply _ ht, withDensity_apply _ ht]
    dsimp [d]
    rw [lintegral_finset_sum]
    · simp
    · intro i _
      exact measurable_const.indicator (hs i)
  have hν_density :
      ν.withDensity d =
        Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
    rw [hν_density_sum]
    refine congrArg Measure.sum ?_
    funext i
    rw [withDensity_indicator (μ := ν) (hs i), withDensity_const]
  have hμ_density : μ = ν.withDensity d := by
    calc
      μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := hμ_sum
      _ = Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
          refine congrArg Measure.sum ?_
          funext i
          exact hrestrict i
      _ = ν.withDensity d := hν_density.symm
  rw [hμ_density]
  exact withDensity_absolutelyContinuous ν d

-- @node: lem:partition-restrict-rnDeriv-integrable
/-- Square-deviation integrability from a finite measurable partition on whose
cells `μ` is a constant multiple of `ν`. -/
lemma integrable_sq_rnDeriv_of_partition_restrict_eq_smul
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ ν : Measure Ω) [IsFiniteMeasure ν]
    (s : Fin k → Set Ω) (c : Fin k → ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hrestrict : ∀ i, μ.restrict (s i) = ENNReal.ofReal (c i) • ν.restrict (s i)) :
    Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ (2 : ℕ)) ν := by
  classical
  let d : Ω → ENNReal :=
    fun x => ∑ i : Fin k, (s i).indicator (fun _ => ENNReal.ofReal (c i)) x
  have hd_meas : Measurable d := by
    dsimp [d]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hs i))
  have hd_cell : ∀ i, ∀ x ∈ s i, d x = ENNReal.ofReal (c i) := by
    intro i x hx
    dsimp [d]
    change (∑ j : Fin k, (s j).indicator (fun _ => ENNReal.ofReal (c j)) x) =
      ENNReal.ofReal (c i)
    simpa [Set.indicator_of_mem hx] using
      (Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : Fin k => (s j).indicator (fun _ => ENNReal.ofReal (c j)) x) i
        (by
          intro j _ hji
          have hxnot : x ∉ s j := by
            have hsd : Disjoint (s j) (s i) := hdisj hji
            exact fun hxj => (Set.disjoint_left.mp hsd) hxj hx
          simp [Set.indicator_of_notMem hxnot])
        (by simp))
  have hμ_sum : μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := by
    have h := Measure.restrict_iUnion (μ := μ) (s := s) hdisj hs
    rw [hcover, Measure.restrict_univ] at h
    exact h
  have hν_density_sum :
      ν.withDensity d =
        Measure.sum (fun i : Fin k =>
          ν.withDensity ((s i).indicator (fun _ => ENNReal.ofReal (c i)))) := by
    ext t ht
    rw [withDensity_apply _ ht]
    simp_rw [Measure.sum_apply _ ht, withDensity_apply _ ht]
    dsimp [d]
    rw [lintegral_finset_sum]
    · simp
    · intro i _
      exact measurable_const.indicator (hs i)
  have hν_density :
      ν.withDensity d =
        Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
    rw [hν_density_sum]
    refine congrArg Measure.sum ?_
    funext i
    rw [withDensity_indicator (μ := ν) (hs i), withDensity_const]
  have hμ_density : μ = ν.withDensity d := by
    calc
      μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := hμ_sum
      _ = Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
          refine congrArg Measure.sum ?_
          funext i
          exact hrestrict i
      _ = ν.withDensity d := hν_density.symm
  have hrn : μ.rnDeriv ν =ᵐ[ν] d := by
    rw [hμ_density]
    exact Measure.rnDeriv_withDensity ν hd_meas
  have hpiece_int :
      ∀ i, IntegrableOn (fun x => ((d x).toReal - 1) ^ (2 : ℕ)) (s i) ν := by
    intro i
    refine ((integrable_const ((c i - 1) ^ (2 : ℕ)) :
      Integrable (fun _ : Ω => (c i - 1) ^ (2 : ℕ)) ν).integrableOn.congr_fun ?_ (hs i))
    intro x hx
    change (c i - 1) ^ (2 : ℕ) = ((d x).toReal - 1) ^ (2 : ℕ)
    rw [hd_cell i x hx, ENNReal.toReal_ofReal (hc_nonneg i)]
  have hd_int_on :
      IntegrableOn (fun x => ((d x).toReal - 1) ^ (2 : ℕ)) (⋃ i, s i) ν := by
    exact integrableOn_finite_iUnion.2 hpiece_int
  have hd_int : Integrable (fun x => ((d x).toReal - 1) ^ (2 : ℕ)) ν := by
    rw [← integrableOn_univ, ← hcover]
    exact hd_int_on
  have heq :
      (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ (2 : ℕ))
        =ᵐ[ν] fun x => ((d x).toReal - 1) ^ (2 : ℕ) := by
    filter_upwards [hrn] with x hx
    rw [hx]
  exact hd_int.congr heq.symm

/-- χ² divergence for a finite measurable partition on whose cells `μ` is a
constant multiple of `ν`. -/
lemma chiSqDiv_eq_sum_partition_of_restrict_eq_smul
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ ν : Measure Ω) [IsFiniteMeasure ν]
    (s : Fin k → Set Ω) (c : Fin k → ℝ)
    (_hμν : μ ≪ ν)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hrestrict : ∀ i, μ.restrict (s i) = ENNReal.ofReal (c i) • ν.restrict (s i)) :
    Causalean.Stat.chiSqDiv μ ν = ∑ i, (c i - 1) ^ (2 : ℕ) * (ν (s i)).toReal := by
  classical
  let d : Ω → ENNReal :=
    fun x => ∑ i : Fin k, (s i).indicator (fun _ => ENNReal.ofReal (c i)) x
  have hd_meas : Measurable d := by
    dsimp [d]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hs i))
  have hd_cell : ∀ i, ∀ x ∈ s i, d x = ENNReal.ofReal (c i) := by
    intro i x hx
    dsimp [d]
    change (∑ j : Fin k, (s j).indicator (fun _ => ENNReal.ofReal (c j)) x) =
      ENNReal.ofReal (c i)
    simpa [Set.indicator_of_mem hx] using
      (Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : Fin k => (s j).indicator (fun _ => ENNReal.ofReal (c j)) x) i
        (by
          intro j _ hji
          have hxnot : x ∉ s j := by
            have hsd : Disjoint (s j) (s i) := hdisj hji
            exact fun hxj => (Set.disjoint_left.mp hsd) hxj hx
          simp [Set.indicator_of_notMem hxnot])
        (by simp))
  have hμ_sum : μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := by
    have h := Measure.restrict_iUnion (μ := μ) (s := s) hdisj hs
    rw [hcover, Measure.restrict_univ] at h
    exact h
  have hν_density_sum :
      ν.withDensity d =
        Measure.sum (fun i : Fin k =>
          ν.withDensity ((s i).indicator (fun _ => ENNReal.ofReal (c i)))) := by
    ext t ht
    rw [withDensity_apply _ ht]
    simp_rw [Measure.sum_apply _ ht, withDensity_apply _ ht]
    dsimp [d]
    rw [lintegral_finset_sum]
    · simp
    · intro i _
      exact measurable_const.indicator (hs i)
  have hν_density :
      ν.withDensity d =
        Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
    rw [hν_density_sum]
    refine congrArg Measure.sum ?_
    funext i
    rw [withDensity_indicator (μ := ν) (hs i), withDensity_const]
  have hμ_density : μ = ν.withDensity d := by
    calc
      μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := hμ_sum
      _ = Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
          refine congrArg Measure.sum ?_
          funext i
          exact hrestrict i
      _ = ν.withDensity d := hν_density.symm
  have hrn : μ.rnDeriv ν =ᵐ[ν] d := by
    rw [hμ_density]
    exact Measure.rnDeriv_withDensity ν hd_meas
  have hpiece_int : ∀ i, IntegrableOn (fun x => ((d x).toReal - 1) ^ (2 : ℕ)) (s i) ν := by
    intro i
    refine ((integrable_const ((c i - 1) ^ (2 : ℕ)) :
      Integrable (fun _ : Ω => (c i - 1) ^ (2 : ℕ)) ν).integrableOn.congr_fun ?_ (hs i))
    intro x hx
    change (c i - 1) ^ (2 : ℕ) = ((d x).toReal - 1) ^ (2 : ℕ)
    rw [hd_cell i x hx, ENNReal.toReal_ofReal (hc_nonneg i)]
  rw [Causalean.Stat.chiSqDiv]
  calc
    ∫ x, ((μ.rnDeriv ν x).toReal - 1) ^ (2 : ℕ) ∂ν
        = ∫ x, ((d x).toReal - 1) ^ (2 : ℕ) ∂ν := by
          apply integral_congr_ae
          filter_upwards [hrn] with x hx
          rw [hx]
    _ = ∫ x in (Set.univ : Set Ω), ((d x).toReal - 1) ^ (2 : ℕ) ∂ν := by
          rw [setIntegral_univ]
    _ = ∫ x in ⋃ i, s i, ((d x).toReal - 1) ^ (2 : ℕ) ∂ν := by
          rw [hcover]
    _ = ∑ i : Fin k, ∫ x in s i, ((d x).toReal - 1) ^ (2 : ℕ) ∂ν := by
          exact integral_iUnion_fintype hs hdisj hpiece_int
    _ = ∑ i : Fin k, (c i - 1) ^ (2 : ℕ) * (ν (s i)).toReal := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hconst : ∫ x in s i, ((d x).toReal - 1) ^ (2 : ℕ) ∂ν =
              ∫ x in s i, (c i - 1) ^ (2 : ℕ) ∂ν := by
            refine setIntegral_congr_fun (hs i) ?_
            intro x hx
            change ((d x).toReal - 1) ^ (2 : ℕ) = (c i - 1) ^ (2 : ℕ)
            rw [hd_cell i x hx, ENNReal.toReal_ofReal (hc_nonneg i)]
          rw [hconst, setIntegral_const, smul_eq_mul, measureReal_def]
          ring

end CausalSmith.Mathlib.ProductChiSquared
