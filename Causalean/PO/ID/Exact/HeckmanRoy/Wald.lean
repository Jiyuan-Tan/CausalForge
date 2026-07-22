/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Heckman–Vytlacil IV / generalized Roy: pairwise Wald identification

Implements prop:po-iv-heckman-roy-wald and the supporting steps in
rem:po-iv-heckman-roy-lean.

For two instrument values `z₀, z₁ : α` with `p z₀ < p z₁`,

    (E[Y | Z=z₁] - E[Y | Z=z₀]) / (E[D | Z=z₁] - E[D | Z=z₀])
        = E[Y(1) - Y(0) | p z₀ < U ≤ p z₁]
        = LATE z₀ z₁.

The proof is split into the five steps named in rem:po-iv-heckman-roy-lean:
consistency rewrite, threshold rewrite, exogeneity drop, uniform-threshold
lemma, and interval-subtraction lemma.  The proof shapes mirror
`PO/ID/Exact/LATE.lean`.
-/

import Causalean.PO.ID.Exact.HeckmanRoy.Setup

/-! # Heckman-Roy Wald Identification

This file proves the pairwise Wald identification theorem for the
Heckman-Vytlacil generalized Roy instrumental-variables model. For two
instrument values with ordered propensities, it identifies the observable Wald
ratio with the latent interval average treatment effect. -/

namespace Causalean
namespace PO

namespace POHeckmanRoySystem

open MeasureTheory ProbabilityTheory

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POHeckmanRoySystem P α)

/-! ### Step 1 — consistency rewrites -/

/-- Pointwise D-consistency on `{Z = z}`: `D(z)(ω) = D(ω)`.  One-line
specialisation of `POVar.cf_eq_factual_on_event`.  Analogue of
`POIVSystem.DofZ_eq_factualD_on_zEvent` in LATE.lean. -/
lemma DofZ_eq_factualD_on_zEvent (hA : S.Assumptions) (z : α)
    {ω : P.Ω} (hω : ω ∈ S.zEvent z) :
    S.DofZ z ω = S.factualD ω :=
  POVar.cf_eq_factual_on_event hA.consistency S.dVar S.zVar z S.hZD.symm hω

/-- Pointwise Y-consistency: `Y(ω) = Y(D(ω))(ω)` for every `ω`.  One-line
specialisation of `POVar.factual_eq_cfUnder_self_selected`. -/
lemma factualY_eq_YofD_factualD (hA : S.Assumptions) (ω : P.Ω) :
    S.factualY ω = S.YofD (S.factualD ω) ω :=
  POVar.factual_eq_cfUnder_self_selected hA.consistency S.yVar S.dVar S.hDY.symm ω

/-! ### Step 5 (algebra-level) — interval-subtraction lemma -/

/-- Pointwise: for `q₀ ≤ q₁`,
    `1_{U ω ≤ q₁} - 1_{U ω ≤ q₀} = 1_{q₀ < U ω ≤ q₁}`.

This is the pointwise interval-subtraction identity of
rem:po-iv-heckman-roy-lean (item 5), formulated on the latent rank `U` of
`S` so that it can be plugged directly into the indicator-difference
rewrites in `first_stage_identity` and `complier_measure`. -/
lemma interval_indicator_sub (z₀ z₁ : α) (hpz : S.p z₀ ≤ S.p z₁) (ω : P.Ω) :
    (if S.factualU ω ≤ S.p z₁ then (1:ℝ) else 0)
      - (if S.factualU ω ≤ S.p z₀ then (1:ℝ) else 0)
    = (S.intervalComplierEvent z₀ z₁).indicator (fun _ => (1:ℝ)) ω := by
  -- Pure pointwise indicator algebra: case-split on `U ω ≤ p z₀` and
  -- `U ω ≤ p z₁`, then unfold `intervalComplierEvent`.
  unfold intervalComplierEvent
  by_cases h₁ : S.factualU ω ≤ S.p z₁
  · by_cases h₀ : S.factualU ω ≤ S.p z₀
    · have hnC : ω ∉ {ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁} := by
        intro hω
        exact (not_lt_of_ge h₀) hω.1
      rw [Set.indicator_of_notMem hnC]
      simp [h₀, h₁]
    · have h₀' : S.p z₀ < S.factualU ω := lt_of_not_ge h₀
      have hC : ω ∈ {ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁} := ⟨h₀', h₁⟩
      simp [h₀, h₁, Set.indicator_of_mem hC]
  · have h₁' : S.p z₁ < S.factualU ω := lt_of_not_ge h₁
    have h₀ : ¬ S.factualU ω ≤ S.p z₀ := fun h => (not_le_of_gt h₁') (le_trans h hpz)
    have hnC : ω ∉ {ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁} := by
      intro hω
      exact (not_le_of_gt h₁') hω.2
    rw [Set.indicator_of_notMem hnC]
    simp [h₀, h₁]

/-! ### Step 4 — uniform-threshold lemma applied to the complier interval -/

/-- Real-valued measure of the interval complier event:
    `(μ {p z₀ < U ≤ p z₁}).toReal = p z₁ - p z₀`,
provided `0 ≤ p z₀ ≤ p z₁ ≤ 1` (which holds because `p` lands in `[0,1]`
by `S.hp_mem`, plus the user-supplied ordering `p z₀ < p z₁`).

Implements rem:po-iv-heckman-roy-lean items 4–5: split
`{p z₀ < U ≤ p z₁} = {U ≤ p z₁} \ {U ≤ p z₀}`, then evaluate each via
`uniformU`. -/
lemma complier_measure (hA : S.Assumptions) (z₀ z₁ : α) (hpz : S.p z₀ < S.p z₁) :
    (P.μ (S.intervalComplierEvent z₀ z₁)).toReal = S.p z₁ - S.p z₀ := by
  -- Evaluate the two threshold sets with `uniformU`, subtract the lower set
  -- from the upper set, and convert the finite ENNReal difference to a real
  -- difference. `S.hp_mem z₀`, `S.hp_mem z₁`, and `hpz` discharge the
  -- `q ∈ [0,1]` side conditions.
  have hC_eq :
      S.intervalComplierEvent z₀ z₁ =
        {ω | S.factualU ω ≤ S.p z₁} \ {ω | S.factualU ω ≤ S.p z₀} := by
    ext ω
    constructor
    · rintro ⟨h₀, h₁⟩
      refine ⟨h₁, ?_⟩
      intro h
      exact (lt_irrefl _ (lt_of_lt_of_le h₀ h))
    · rintro ⟨h₁, h₀⟩
      refine ⟨?_, h₁⟩
      exact lt_of_not_ge h₀
  have hp0 : S.p z₀ ∈ Set.Icc (0 : ℝ) 1 := S.hp_mem z₀
  have hp1 : S.p z₁ ∈ Set.Icc (0 : ℝ) 1 := S.hp_mem z₁
  have h_sub : {ω | S.factualU ω ≤ S.p z₀} ⊆ {ω | S.factualU ω ≤ S.p z₁} :=
    fun _ h => le_trans h (le_of_lt hpz)
  have hμ0 : P.μ {ω | S.factualU ω ≤ S.p z₀} = ENNReal.ofReal (S.p z₀) :=
    hA.uniformU _ hp0
  have hμ1 : P.μ {ω | S.factualU ω ≤ S.p z₁} = ENNReal.ofReal (S.p z₁) :=
    hA.uniformU _ hp1
  have hμ0_finite : P.μ {ω | S.factualU ω ≤ S.p z₀} ≠ ⊤ := by
    rw [hμ0]
    exact ENNReal.ofReal_ne_top
  rw [hC_eq,
    MeasureTheory.measure_diff h_sub
      (measurableSet_le S.measurable_factualU measurable_const).nullMeasurableSet hμ0_finite,
    hμ1, hμ0]
  rw [ENNReal.toReal_sub_of_le]
  · simp [ENNReal.toReal_ofReal hp1.1, ENNReal.toReal_ofReal hp0.1]
  · exact ENNReal.ofReal_le_ofReal (le_of_lt hpz)
  · exact ENNReal.ofReal_ne_top

/-! ### Step 1+3 — first-stage identity (analogue of LATE.first_stage_identity) -/

/-- First-stage identity: `E[D | Z=z₁] - E[D | Z=z₀] = p z₁ - p z₀`.

Mirrors `POIVSystem.first_stage_identity` in LATE.lean, with two
differences:
  * the bundle now projects to the `U`-component (index 0) instead of
    `D(0)/D(1)`;
  * the threshold-crossing assumption replaces monotonicity in folding the
    indicator difference back to `1_{p z₀ < U ≤ p z₁}` (a.s.). -/
theorem first_stage_identity (hA : S.Assumptions) (z₀ z₁ : α)
    (hZ0 : 0 < (P.μ (S.zEvent z₀)).toReal)
    (hZ1 : 0 < (P.μ (S.zEvent z₁)).toReal)
    (hpz : S.p z₀ < S.p z₁) :
    S.condExpDZ z₁ - S.condExpDZ z₀ = S.p z₁ - S.p z₀ := by
  classical
  have hμne_zero : ∀ z, 0 < (P.μ (S.zEvent z)).toReal →
      P.μ (S.zVar.event z) ≠ 0 := fun z hZ h =>
    absurd hZ (by simp [show S.zEvent z = S.zVar.event z from rfl, h])
  have hμne_top : ∀ z, P.μ (S.zVar.event z) ≠ ⊤ := fun _ => measure_ne_top _ _
  have hDofZ_to_indicator : ∀ z, ∀ᵐ ω ∂P.μ,
      ((S.DofZ z ω).toNat : ℝ) =
        (if S.factualU ω ≤ S.p z then (1:ℝ) else 0) := by
    intro z
    filter_upwards [hA.thresholdCrossing z] with ω hω
    by_cases hu : S.factualU ω ≤ S.p z
    · have hD : S.DofZ z ω = true := hω.mpr hu
      simp [hD, hu]
    · have hD : S.DofZ z ω = false := by
        cases hd : S.DofZ z ω
        · rfl
        · exact absurd (hω.mp hd) hu
      simp [hD, hu]
  have hCE : ∀ z (_hZ : 0 < (P.μ (S.zEvent z)).toReal),
      S.condExpDZ z = ∫ ω, (if S.factualU ω ≤ S.p z then (1:ℝ) else 0) ∂P.μ := by
    intro z hZ
    let getU : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ := fun f => by
      exact f (0 : Fin 3)
    have hgetU_meas : Measurable getU := by
      change Measurable fun f : ∀ i : Fin 3,
          (POCFBundle.cons (RegimedVar.ofFactual S.uVar) <|
            POCFBundle.cons (S.yUnderD true) <|
            POCFBundle.cons (S.yUnderD false) <|
            POCFBundle.nil P).type i =>
        f (0 : Fin 3)
      exact measurable_pi_apply (0 : Fin 3)
    have hgetU_joint : ∀ ω, getU (S.cfBundle.jointValue ω) = S.factualU ω := by
      intro ω
      rfl
    let h_proj : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
      fun f => if getU f ≤ S.p z then (1:ℝ) else 0
    have hh_meas : Measurable h_proj := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le hgetU_meas measurable_const
    have h_cons : ∀ ω ∈ S.zVar.event z,
        (if S.factualU ω ≤ S.p z then (1:ℝ) else 0) =
          h_proj (S.cfBundle.jointValue ω) := by
      intro ω _
      dsimp [h_proj]
      rw [hgetU_joint]
    have hcond_d :
        S.condExpDZ z =
          eventCondExp P.μ (S.zVar.event z)
            (fun ω => ((S.DofZ z ω).toNat : ℝ)) := by
      unfold POHeckmanRoySystem.condExpDZ eventCondExp
      congr 1
      refine MeasureTheory.setIntegral_congr_fun (S.measurableSet_zEvent z) ?_
      intro ω hω
      exact congrArg (fun d : Bool => ((d.toNat : ℝ)))
        (S.DofZ_eq_factualD_on_zEvent hA z hω).symm
    have hcond_ind :
        eventCondExp P.μ (S.zVar.event z)
            (fun ω => ((S.DofZ z ω).toNat : ℝ)) =
          eventCondExp P.μ (S.zVar.event z)
            (fun ω => if S.factualU ω ≤ S.p z then (1:ℝ) else 0) := by
      unfold eventCondExp
      congr 1
      refine MeasureTheory.setIntegral_congr_ae (S.measurableSet_zEvent z) ?_
      filter_upwards [hDofZ_to_indicator z] with ω hω _
      exact hω
    rw [hcond_d, hcond_ind,
      POSystem.eventCondExp_of_consistency_IndepCF hA.instrumentIndep
        (a := S.zVar) hh_meas h_cons (hμne_zero z hZ) (hμne_top z)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    dsimp [h_proj]
    rw [hgetU_joint]
  rw [hCE z₁ hZ1, hCE z₀ hZ0]
  have hbdd : ∀ z, ∀ ω, |if S.factualU ω ≤ S.p z then (1:ℝ) else 0| ≤ 1 := by
    intro z ω
    by_cases h : S.factualU ω ≤ S.p z <;> simp [h]
  have hint : ∀ z, Integrable
      (fun ω => if S.factualU ω ≤ S.p z then (1:ℝ) else 0) P.μ := by
    intro z
    refine (MeasureTheory.integrable_const (1:ℝ)).mono'
      ?_ (Filter.Eventually.of_forall (hbdd z))
    exact (Measurable.ite (measurableSet_le S.measurable_factualU measurable_const)
      measurable_const measurable_const).aestronglyMeasurable
  rw [← MeasureTheory.integral_sub (hint z₁) (hint z₀)]
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (S.interval_indicator_sub z₀ z₁ (le_of_lt hpz)))]
  rw [MeasureTheory.integral_indicator_const (1:ℝ)
    (S.measurableSet_intervalComplierEvent z₀ z₁)]
  simpa [MeasureTheory.measureReal_def] using S.complier_measure hA z₀ z₁ hpz

/-! ### Step 1+3 — reduced-form identity -/

/-- Reduced-form identity:
    `E[Y | Z=z₁] - E[Y | Z=z₀] = ∫ (Y(D(z₁)) - Y(D(z₀))) ∂μ`.

Analogue of `POIVSystem.reduced_form_identity` in LATE.lean.  The bundle
projection now reads `U` from index 0 and `Y(1), Y(0)` from indices 1, 2. -/
theorem reduced_form_identity (hA : S.Assumptions) (z₀ z₁ : α)
    (hZ0 : 0 < (P.μ (S.zEvent z₀)).toReal)
    (hZ1 : 0 < (P.μ (S.zEvent z₁)).toReal)
    (hY1 : Integrable (S.YofD true) P.μ)
    (hY0 : Integrable (S.YofD false) P.μ) :
    S.condExpYZ z₁ - S.condExpYZ z₀ =
      ∫ ω, (S.YofDofZ z₁ ω - S.YofDofZ z₀ ω) ∂P.μ := by
  have hYDZ_meas : ∀ z, Measurable (S.YofDofZ z) := fun z => S.measurable_YofDofZ z
  have hYDZ_bdd : ∀ z, ∀ ω,
      |S.YofDofZ z ω| ≤ |S.YofD true ω| + |S.YofD false ω| := fun z ω => by
    have h1 := abs_nonneg (S.YofD true ω)
    have h0 := abs_nonneg (S.YofD false ω)
    unfold YofDofZ
    cases S.DofZ z ω <;> simp [h1, h0]
  have hYDZ_int : ∀ z, Integrable (S.YofDofZ z) P.μ := fun z =>
    (hY1.norm.add hY0.norm).mono' (hYDZ_meas z).aestronglyMeasurable
      (Filter.Eventually.of_forall (hYDZ_bdd z))
  have hμne_zero : ∀ z, 0 < (P.μ (S.zEvent z)).toReal →
      P.μ (S.zVar.event z) ≠ 0 := fun z hZ h =>
    absurd hZ (by simp [show S.zEvent z = S.zVar.event z from rfl, h])
  have hμne_top : ∀ z, P.μ (S.zVar.event z) ≠ ⊤ := fun _ => measure_ne_top _ _
  have h_factualY_ae : ∀ z, ∀ᵐ ω ∂P.μ,
      (ω ∈ S.zEvent z) →
        S.factualY ω =
          (if S.factualU ω ≤ S.p z then S.YofD true ω else S.YofD false ω) := by
    intro z
    filter_upwards [hA.thresholdCrossing z] with ω hth hω
    rw [S.factualY_eq_YofD_factualD hA ω,
      ← S.DofZ_eq_factualD_on_zEvent hA z hω]
    by_cases hu : S.factualU ω ≤ S.p z
    · have hD : S.DofZ z ω = true := hth.mpr hu
      simp [hD, hu]
    · have hD : S.DofZ z ω = false := by
        cases hd : S.DofZ z ω
        · rfl
        · exact absurd (hth.mp hd) hu
      simp [hD, hu]
  have hCE : ∀ z (_hZ : 0 < (P.μ (S.zEvent z)).toReal),
      S.condExpYZ z =
        ∫ ω, (if S.factualU ω ≤ S.p z then S.YofD true ω else S.YofD false ω) ∂P.μ := by
    intro z hZ
    let getU : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ := fun f => by
      exact f (0 : Fin 3)
    have hgetU_meas : Measurable getU := by
      change Measurable fun f : ∀ i : Fin 3,
          (POCFBundle.cons (RegimedVar.ofFactual S.uVar) <|
            POCFBundle.cons (S.yUnderD true) <|
            POCFBundle.cons (S.yUnderD false) <|
            POCFBundle.nil P).type i =>
        f (0 : Fin 3)
      exact measurable_pi_apply (0 : Fin 3)
    have hgetU_joint : ∀ ω, getU (S.cfBundle.jointValue ω) = S.factualU ω := by
      intro ω
      rfl
    let h_proj : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
      fun f => if getU f ≤ S.p z
        then ((f (1 : Fin 3)) : ℝ) else ((f (2 : Fin 3)) : ℝ)
    have hh_meas : Measurable h_proj := by
      change Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
        if getU f ≤ S.p z
        then ((f (1 : Fin 3)) : ℝ) else ((f (2 : Fin 3)) : ℝ)
      refine Measurable.ite ?_ ?_ ?_
      · exact measurableSet_le hgetU_meas measurable_const
      · exact measurable_pi_apply (1 : Fin 3)
      · exact measurable_pi_apply (2 : Fin 3)
    have h_cons : ∀ ω ∈ S.zVar.event z,
        (if S.factualU ω ≤ S.p z then S.YofD true ω else S.YofD false ω)
          = h_proj (S.cfBundle.jointValue ω) := by
      intro ω _
      dsimp [h_proj]
      rw [hgetU_joint]
      have hJV1 : (S.cfBundle.jointValue ω (1 : Fin 3) : ℝ) = S.YofD true ω := rfl
      have hJV2 : (S.cfBundle.jointValue ω (2 : Fin 3) : ℝ) = S.YofD false ω := rfl
      rw [hJV1, hJV2]
    have hbridge :
        S.condExpYZ z =
          eventCondExp P.μ (S.zVar.event z)
            (fun ω => if S.factualU ω ≤ S.p z then S.YofD true ω else S.YofD false ω) := by
      unfold POHeckmanRoySystem.condExpYZ eventCondExp
      change (∫ ω in S.zEvent z, S.factualY ω ∂P.μ) / (P.μ (S.zEvent z)).toReal =
        (∫ ω in S.zVar.event z,
            (if S.factualU ω ≤ S.p z then S.YofD true ω else S.YofD false ω) ∂P.μ) /
          (P.μ (S.zVar.event z)).toReal
      have hzev : S.zEvent z = S.zVar.event z := rfl
      rw [hzev]
      congr 1
      refine MeasureTheory.setIntegral_congr_ae (S.measurableSet_zEvent z) ?_
      filter_upwards [h_factualY_ae z] with ω hω hin
      rw [show S.zEvent z = S.zVar.event z from rfl] at hω
      exact hω hin
    rw [hbridge,
      POSystem.eventCondExp_of_consistency_IndepCF hA.instrumentIndep
        (a := S.zVar) hh_meas h_cons (hμne_zero z hZ) (hμne_top z)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    dsimp [h_proj]
    rw [hgetU_joint]
    have hJV1 : (S.cfBundle.jointValue ω (1 : Fin 3) : ℝ) = S.YofD true ω := rfl
    have hJV2 : (S.cfBundle.jointValue ω (2 : Fin 3) : ℝ) = S.YofD false ω := rfl
    rw [hJV1, hJV2]
  have hAlt_eq : ∀ z,
      (∫ ω, (if S.factualU ω ≤ S.p z then S.YofD true ω else S.YofD false ω) ∂P.μ)
        = ∫ ω, S.YofDofZ z ω ∂P.μ := by
    intro z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hA.thresholdCrossing z] with ω hth
    unfold YofDofZ
    by_cases hu : S.factualU ω ≤ S.p z
    · have hD : S.DofZ z ω = true := hth.mpr hu
      simp [hD, hu]
    · have hD : S.DofZ z ω = false := by
        cases hd : S.DofZ z ω
        · rfl
        · exact absurd (hth.mp hd) hu
      simp [hD, hu]
  rw [hCE z₁ hZ1, hCE z₀ hZ0, hAlt_eq z₁, hAlt_eq z₀]
  rw [← MeasureTheory.integral_sub (hYDZ_int z₁) (hYDZ_int z₀)]

/-! ### Step 2 — pointwise threshold identity -/

/-- Pointwise threshold identity:
    `Y(D(z₁)) - Y(D(z₀))
        = (Y(1) - Y(0)) · 1_{p z₀ < U ≤ p z₁}` a.s.

Analogue of `POIVSystem.pointwise_monotonicity` in LATE.lean.  Replaces
the binary monotonicity case-split by a case-split on
`U ω ≤ p z₀` and `U ω ≤ p z₁`, using `hA.thresholdCrossing` at both
instrument values. -/
theorem pointwise_threshold_identity (hA : S.Assumptions) (z₀ z₁ : α)
    (hpz : S.p z₀ ≤ S.p z₁) :
    ∀ᵐ ω ∂P.μ,
      S.YofDofZ z₁ ω - S.YofDofZ z₀ ω
        = (S.YofD true ω - S.YofD false ω)
            * (S.intervalComplierEvent z₀ z₁).indicator (fun _ => (1:ℝ)) ω := by
  -- Combine threshold crossing at `z₀` and `z₁`; then unfold `YofDofZ` and
  -- case-split on `U ω ≤ p z₀` and `U ω ≤ p z₁`, using
  -- `intervalComplierEvent` membership in each case.
  filter_upwards [hA.thresholdCrossing z₀, hA.thresholdCrossing z₁] with ω h₀ h₁
  unfold YofDofZ intervalComplierEvent
  by_cases hu1 : S.factualU ω ≤ S.p z₁
  · by_cases hu0 : S.factualU ω ≤ S.p z₀
    · have hD0 : S.DofZ z₀ ω = true := h₀.mpr hu0
      have hD1 : S.DofZ z₁ ω = true := h₁.mpr hu1
      have hnC : ω ∉ ({ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁} : Set P.Ω) := by
        intro hω
        exact (not_lt_of_ge hu0) hω.1
      simp [hD0, hD1, Set.indicator_of_notMem hnC]
    · have hu0' : S.p z₀ < S.factualU ω := lt_of_not_ge hu0
      have hD0 : S.DofZ z₀ ω = false := by
        cases hd : S.DofZ z₀ ω
        · rfl
        · exact absurd (h₀.mp hd) hu0
      have hD1 : S.DofZ z₁ ω = true := h₁.mpr hu1
      have hC : ω ∈ ({ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁} : Set P.Ω) :=
        ⟨hu0', hu1⟩
      simp [hD0, hD1, Set.indicator_of_mem hC]
  · have hu0 : ¬ S.factualU ω ≤ S.p z₀ := fun h => hu1 (le_trans h hpz)
    have hD0 : S.DofZ z₀ ω = false := by
      cases hd : S.DofZ z₀ ω
      · rfl
      · exact absurd (h₀.mp hd) hu0
    have hD1 : S.DofZ z₁ ω = false := by
      cases hd : S.DofZ z₁ ω
      · rfl
      · exact absurd (h₁.mp hd) hu1
    have hnC : ω ∉ ({ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁} : Set P.Ω) := by
      intro hω
      exact hu1 hω.2
    simp [hD0, hD1, Set.indicator_of_notMem hnC]

/-! ### Step (integrate against `Set.indicator`) — event-conditioning identity -/

/-- Event-conditioning identity:
    `∫ (Y(1) - Y(0)) · 1_{C(z₀,z₁)} ∂μ = μ(C(z₀,z₁)).toReal · LATE z₀ z₁`.

This is the interval-complier analogue of `POIVSystem.event_conditioning_identity`. -/
theorem event_conditioning_identity (z₀ z₁ : α) :
    ∫ ω, (S.YofD true ω - S.YofD false ω) *
           (S.intervalComplierEvent z₀ z₁).indicator (fun _ => (1:ℝ)) ω ∂P.μ
      = (P.μ (S.intervalComplierEvent z₀ z₁)).toReal * S.LATE z₀ z₁ := by
  -- Same event-conditioning algebra as binary LATE, with the interval
  -- complier event in place of the binary complier event.
  unfold LATE
  have hC : MeasurableSet (S.intervalComplierEvent z₀ z₁) :=
    S.measurableSet_intervalComplierEvent z₀ z₁
  have h_rw :
      (fun ω => (S.YofD true ω - S.YofD false ω) *
                (S.intervalComplierEvent z₀ z₁).indicator (fun _ => (1:ℝ)) ω)
      = (S.intervalComplierEvent z₀ z₁).indicator
          (fun ω => S.YofD true ω - S.YofD false ω) := by
    funext ω
    by_cases hω : ω ∈ S.intervalComplierEvent z₀ z₁
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [h_rw, MeasureTheory.integral_indicator hC]
  by_cases hμ : (P.μ (S.intervalComplierEvent z₀ z₁)).toReal = 0
  · rw [hμ, zero_mul]
    have hμ0 : P.μ (S.intervalComplierEvent z₀ z₁) = 0 := by
      have hne : P.μ (S.intervalComplierEvent z₀ z₁) ≠ ⊤ := measure_ne_top _ _
      exact (ENNReal.toReal_eq_zero_iff _).mp hμ |>.resolve_right hne
    have hrest : P.μ.restrict (S.intervalComplierEvent z₀ z₁) = 0 := by
      rw [MeasureTheory.Measure.restrict_eq_zero]; exact hμ0
    simp [hrest]
  · field_simp

/-! ### Main theorem — pairwise Wald identification -/

/-- Pairwise Wald identification of LATE -- prop:po-iv-heckman-roy-wald.

For any `z₀, z₁ : α` with `μ {Z = z₀} > 0`, `μ {Z = z₁} > 0`, and
`p z₀ < p z₁`,
    `(E[Y | Z=z₁] - E[Y | Z=z₀]) / (E[D | Z=z₁] - E[D | Z=z₀])
        = LATE z₀ z₁`. -/
theorem wald_pairwise (hA : S.Assumptions) (z₀ z₁ : α)
    (hZ0 : 0 < (P.μ (S.zEvent z₀)).toReal)
    (hZ1 : 0 < (P.μ (S.zEvent z₁)).toReal)
    (hpz : S.p z₀ < S.p z₁)
    (hY1 : Integrable (S.YofD true) P.μ)
    (hY0 : Integrable (S.YofD false) P.μ) :
    (S.condExpYZ z₁ - S.condExpYZ z₀) /
      (S.condExpDZ z₁ - S.condExpDZ z₀)
      = S.LATE z₀ z₁ := by
  rw [S.first_stage_identity hA z₀ z₁ hZ0 hZ1 hpz]
  rw [S.reduced_form_identity hA z₀ z₁ hZ0 hZ1 hY1 hY0]
  rw [MeasureTheory.integral_congr_ae
    (S.pointwise_threshold_identity hA z₀ z₁ (le_of_lt hpz))]
  rw [S.event_conditioning_identity z₀ z₁]
  rw [S.complier_measure hA z₀ z₁ hpz]
  have hp_ne : S.p z₁ - S.p z₀ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpz)
  field_simp

end POHeckmanRoySystem

end PO
end Causalean
