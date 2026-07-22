/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-Period Dynamic LATE: when-to-treat ratio identifications

The Wald-style ratio identification of the when-to-treat dynamic LATE
`τ_d := θ(d, d)` and the dynamic mixture LATE `β_z`
(prop:po-dynamic-late-when-to-treat).  Both are algebraic consequences of
the four bridge identities in `Bridges.lean` plus:

* one-sided noncompliance (`oneSidedNoncompliance`) — used to evaluate
  `D(0) = 0` a.s. and to decompose `Y(D(d))` on `{D(d) = d} ∪ {D(d) = 0}`
  for `d ∈ {(1,0), (0,1)}`;
* composition consistency on the encouragement event — used to identify
  `Y(D(z))` with `Y(d)` on `{D(z) = d}` (a structural rewrite, factored
  into the helper `YofDofZ_eq_YofD_on_DofZEq` below).

The structural helpers are stated here alongside the main ratio theorems,
which are assembled from those helpers plus the bridge identities in
`Bridges.lean`.
-/

import Causalean.PO.ID.Exact.DynamicLATE.Bridges

/-! # Two-period dynamic LATE when-to-treat ratios

This file proves the Wald-style ratio identifications for the dynamic
when-to-treat and mixture LATE parameters. The arguments combine bridge
identities for two-period encouragement regimes with one-sided noncompliance and
composition-consistency rewrites on the observed encouragement event.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace PODynLATESystem

variable {P : POSystem} {γ₀ γ₁ : Type}
variable [MeasurableSpace γ₀] [MeasurableSpace γ₁]
variable [MeasurableSingletonClass γ₀] [MeasurableSingletonClass γ₁]
variable [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
variable {S : PODynLATESystem P γ₀ γ₁}

/-! ### Composition-consistency rewrites on the encouragement event

These helper lemmas factor the structural content needed to turn `Y(D(z))`
into `Y(d)` on `{D(z) = d}`.  They are consequences of PO composition
consistency (def:po-consistency) applied to the encouragement regime. -/

omit [MeasurableSingletonClass γ₀] [MeasurableSingletonClass γ₁]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] in
/-- Helper: assignment of `S.D1` in the two-target treatment regime is
`S.hD1bool.symm (d 0)`. -/
private lemma treatmentRegime_assign_D1 (S : PODynLATESystem P γ₀ γ₁)
    (d : Fin 2 → Bool)
    (hv : S.D1 ∈ (S.treatmentRegime d).target) :
    (S.treatmentRegime d).assign S.D1 hv = S.hD1bool.symm (d 0) := by
  change Regime.listLookup _ _ _ = _
  exact Regime.listLookup_cons_self _

omit [MeasurableSingletonClass γ₀] [MeasurableSingletonClass γ₁]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] in
/-- Helper: assignment of `S.D2` in the two-target treatment regime is
`S.hD2bool.symm (d 1)`. -/
private lemma treatmentRegime_assign_D2 (S : PODynLATESystem P γ₀ γ₁)
    (d : Fin 2 → Bool)
    (hv : S.D2 ∈ (S.treatmentRegime d).target) :
    (S.treatmentRegime d).assign S.D2 hv = S.hD2bool.symm (d 1) := by
  change Regime.listLookup _ _ _ = _
  have hv' : S.D2 ∈ ([⟨S.D2, S.hD2bool.symm (d 1)⟩] :
      List ((v : P.V) × P.X v)).map Sigma.fst := by
    simp
  rw [Regime.listLookup_cons_of_ne S.D1_ne_D2.symm _ hv']
  exact Regime.listLookup_cons_self _

/-- On the event `{D(z) = d}`, the encouragement-regime outcome `Y(D(z))`
agrees pointwise with the treatment-regime outcome `Y(d)`.

Proof: combine PO composition consistency (which gives `Y under (r_z ⊔ r_d)
= Y under r_z = YofDofZ z` on the event `{D(z) = d}`) with the exclusion
assumption (which gives `Y under (r_z ⊔ r_d) = Y under r_d = YofD d`). -/
theorem YofDofZ_eq_YofD_on_DofZEq (As : S.Assumptions) (z d : Fin 2 → Bool) :
    ∀ᵐ ω ∂P.μ, S.DofZ z ω = d → S.YofDofZ z ω = S.YofD d ω := by
  refine Filter.Eventually.of_forall ?_
  intro ω hd
  -- Step 0: extract coordinate-wise treatment values from `S.DofZ z ω = d`.
  have hd1 : S.D1ofZ z ω = d 0 := by
    have := congrFun hd 0
    simpa [DofZ] using this
  have hd2 : S.D2ofZ z ω = d 1 := by
    have := congrFun hd 1
    simpa [DofZ] using this
  -- Y disjoint from regime targets (uses distinctness Z_i ≠ Y, D_i ≠ Y).
  have hYdisj :
      _root_.Disjoint ({S.Y} : Finset P.V)
        ((S.encouragementRegime z).target ∪ (S.treatmentRegime d).target) := by
    unfold encouragementRegime treatmentRegime
    rw [Regime.ofList_target, Regime.ofList_target]
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.disjoint_singleton_left, Finset.mem_union, Finset.mem_insert, not_or]
    refine ⟨⟨S.Z1_ne_Y.symm, S.Z2_ne_Y.symm, fun h => (Finset.notMem_empty _ h).elim⟩,
            ⟨S.D1_ne_Y.symm, S.D2_ne_Y.symm, fun h => (Finset.notMem_empty _ h).elim⟩⟩
  -- Construct IntermediateAgrees from D1ofZ z ω = d 0 and D2ofZ z ω = d 1.
  have hIA : P.IntermediateAgrees
      (S.encouragementRegime z) (S.treatmentRegime d) ω := by
    intro v hv
    -- treatmentRegime's target is {D₁, D₂}.  Case-split.
    have hv' : v = S.D1 ∨ v = S.D2 := by
      unfold treatmentRegime at hv
      rw [Regime.ofList_target] at hv
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        Finset.mem_insert] at hv
      rcases hv with hv | hv | hv
      · exact Or.inl hv
      · exact Or.inr hv
      · exact (Finset.notMem_empty _ hv).elim
    rcases hv' with rfl | rfl
    · -- v = S.D1
      rw [treatmentRegime_assign_D1]
      have : S.hD1bool (P.eval (S.encouragementRegime z) ω S.D1) = d 0 := by
        simpa [D1ofZ, POVar.cf, d1Var] using hd1
      have := congrArg S.hD1bool.symm this
      simpa using this
    · -- v = S.D2
      rw [treatmentRegime_assign_D2]
      have : S.hD2bool (P.eval (S.encouragementRegime z) ω S.D2) = d 1 := by
        simpa [D2ofZ, POVar.cf, d2Var] using hd2
      have := congrArg S.hD2bool.symm this
      simpa using this
  -- Apply composition consistency: poVariable (r_z ⊔ r_d) {Y} = poVariable r_z {Y}.
  have hComp := As.consistency.composition
    (S.encouragementRegime z) (S.treatmentRegime d)
    (S.encouragementRegime_disjoint_treatmentRegime z d) {S.Y} hYdisj ω hIA
  -- Extract pointwise eval at S.Y.
  have hEvalEq : P.eval (S.encTreatRegime z d) ω S.Y
      = P.eval (S.encouragementRegime z) ω S.Y := by
    have := congrFun hComp ⟨S.Y, Finset.mem_singleton_self _⟩
    exact this
  -- Use exclusion: yVar.cf (encTreatRegime z d) ω = YofD d ω.
  have hExcl := As.exclusion z d ω
  -- Combine.
  have hYofDofZ : S.YofDofZ z ω = S.yVar.cf (S.encTreatRegime z d) ω := by
    change S.yVar.cf (S.encouragementRegime z) ω = S.yVar.cf (S.encTreatRegime z d) ω
    unfold POVar.cf
    congr 1
    exact hEvalEq.symm
  rw [hYofDofZ, hExcl]

omit [MeasurableSingletonClass γ₀] [MeasurableSingletonClass γ₁] in
/-- Under one-sided noncompliance, the zero-encouragement counterfactual
treatment is identically zero a.s.: `D(0) = 0` a.s. -/
theorem DofZ_zero_eq_zero (As : S.Assumptions) :
    ∀ᵐ ω ∂P.μ, S.DofZ ![false, false] ω = ![false, false] := by
  filter_upwards [As.oneSidedNoncompliance ![false, false]] with ω hω
  obtain ⟨h1, h2⟩ := hω
  have hz0 : (![false, false] : Fin 2 → Bool) 0 = false := rfl
  have hz1 : (![false, false] : Fin 2 → Bool) 1 = false := rfl
  rw [hz0] at h1
  rw [hz1] at h2
  have hD1 : S.D1ofZ ![false, false] ω = false := by
    cases h : S.D1ofZ ![false, false] ω <;>
      [rfl; (rw [h] at h1; exact absurd h1 (by decide))]
  have hD2 : S.D2ofZ ![false, false] ω = false := by
    cases h : S.D2ofZ ![false, false] ω <;>
      [rfl; (rw [h] at h2; exact absurd h2 (by decide))]
  funext i
  refine i.cases ?_ ?_
  · simp [DofZ, hD1]
  · intro _; simp [DofZ, hD2]

/-- A.s. `Y(D(0)) = Y(0)`, the zero-encouragement composition collapse. -/
theorem YofDofZ_zero_ae_eq_YofD_zero (As : S.Assumptions) :
    S.YofDofZ ![false, false] =ᵐ[P.μ] S.YofD ![false, false] := by
  have hcomp := YofDofZ_eq_YofD_on_DofZEq As ![false, false] ![false, false]
  filter_upwards [hcomp, DofZ_zero_eq_zero As] with ω hcomp hzero
  exact hcomp hzero

omit [MeasurableSingletonClass γ₀] [MeasurableSingletonClass γ₁] in
/-- For `d ≼ z` and one-sided noncompliance, `D(z) ∈ {d, 0}` a.s. when
`d` is one of the two single-period treatment vectors `(1,0)` or `(0,1)`,
because the only `d' ≼ z` with `d' ≠ d` and `d' ≠ 0` would have to flip a
coordinate that one-sided rules out.  Used to decompose `Y(D(z))` on
the encouragement event into the two-piece sum
`Y(d)·1_{D(z)=d} + Y(0)·1_{D(z)=0}`. -/
theorem DofZ_in_two_values (As : S.Assumptions) (d : Fin 2 → Bool)
    (hd : d = ![true, false] ∨ d = ![false, true]) :
    ∀ᵐ ω ∂P.μ,
      S.DofZ d ω = d ∨ S.DofZ d ω = ![false, false] := by
  filter_upwards [As.oneSidedNoncompliance d] with ω hω
  obtain ⟨h1, h2⟩ := hω
  rcases hd with hd | hd
  · subst d
    have hz0 : (![true, false] : Fin 2 → Bool) 0 = true := rfl
    have hz1 : (![true, false] : Fin 2 → Bool) 1 = false := rfl
    rw [hz0] at h1
    rw [hz1] at h2
    have hD2 : S.D2ofZ ![true, false] ω = false := by
      cases h : S.D2ofZ ![true, false] ω <;>
        [rfl; (rw [h] at h2; exact absurd h2 (by decide))]
    cases hD1 : S.D1ofZ ![true, false] ω
    · right
      funext i
      refine i.cases ?_ ?_
      · simp [DofZ, hD1]
      · intro _; simp [DofZ, hD2]
    · left
      funext i
      refine i.cases ?_ ?_
      · simp [DofZ, hD1]
      · intro _; simp [DofZ, hD2]
  · subst d
    have hz0 : (![false, true] : Fin 2 → Bool) 0 = false := rfl
    have hz1 : (![false, true] : Fin 2 → Bool) 1 = true := rfl
    rw [hz0] at h1
    rw [hz1] at h2
    have hD1 : S.D1ofZ ![false, true] ω = false := by
      cases h : S.D1ofZ ![false, true] ω <;>
        [rfl; (rw [h] at h1; exact absurd h1 (by decide))]
    cases hD2 : S.D2ofZ ![false, true] ω
    · right
      funext i
      refine i.cases ?_ ?_
      · simp [DofZ, hD1]
      · intro _; simp [DofZ, hD2]
    · left
      funext i
      refine i.cases ?_ ?_
      · simp [DofZ, hD1]
      · intro _; simp [DofZ, hD2]

/-! ### Outcome-difference identification

Compose the outcome bridge with the structural helpers above to identify
the *difference* `obsMean(d) - obsMean(0)` with the conditional outcome
contrast `∫_{D(d)=d} (Y(d) - Y(0)) dμ`. -/

/-- Under one-sided noncompliance, the encouragement-regime outcome under
encouragement `d ∈ {(1,0), (0,1)}` decomposes pointwise as
`Y(d)·1_{D(d)=d} + Y(0)·1_{D(d)=0}` a.s. -/
theorem YofDofZ_decomposition (As : S.Assumptions) (d : Fin 2 → Bool)
    (hd : d = ![true, false] ∨ d = ![false, true]) :
    S.YofDofZ d =ᵐ[P.μ]
      fun ω => S.YofD d ω * (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω +
               S.YofD ![false, false] ω *
                 (S.DofZEq d ![false, false]).indicator (fun _ => (1 : ℝ)) ω := by
  filter_upwards [DofZ_in_two_values As d hd,
      YofDofZ_eq_YofD_on_DofZEq As d d,
      YofDofZ_eq_YofD_on_DofZEq As d ![false, false]] with ω hcase hdd hd0
  rcases hcase with h | h
  · have h1 : (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω = 1 := by
      exact Set.indicator_of_mem (s := S.DofZEq d d) (f := fun _ => (1 : ℝ)) h
    have h2 : (S.DofZEq d ![false, false]).indicator (fun _ => (1 : ℝ)) ω = 0 := by
      apply Set.indicator_of_notMem
      intro h0
      have hd_ne_zero : d ≠ ![false, false] := by
        rcases hd with rfl | rfl <;> decide
      exact hd_ne_zero (h.symm.trans h0)
    rw [h1, h2]
    ring_nf
    exact hdd h
  · have h1 : (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω = 0 := by
      apply Set.indicator_of_notMem
      intro hd'
      have hd_ne_zero : d ≠ ![false, false] := by
        rcases hd with rfl | rfl <;> decide
      exact hd_ne_zero (hd'.symm.trans h)
    have h2 : (S.DofZEq d ![false, false]).indicator (fun _ => (1 : ℝ)) ω = 1 := by
      exact Set.indicator_of_mem (s := S.DofZEq d ![false, false])
        (f := fun _ => (1 : ℝ)) h
    rw [h1, h2]
    ring_nf
    exact hd0 h

/-- The numerator identity: the difference of the encouragement-regime
outcome integrals collapses to the conditional contrast on `{D(d) = d}`.

`∫ Y(D(d)) - ∫ Y(D(0)) = ∫_{D(d)=d} (Y(d) - Y(0)) dμ`. -/
theorem int_outcome_difference_identity (As : S.Assumptions) (d : Fin 2 → Bool)
    (hd : d = ![true, false] ∨ d = ![false, true]) :
    (∫ ω, S.YofDofZ d ω ∂P.μ) - (∫ ω, S.YofDofZ ![false, false] ω ∂P.μ)
      = ∫ ω in S.DofZEq d d, (S.YofD d ω - S.YofD ![false, false] ω) ∂P.μ := by
  have hpoint :
      (fun ω => S.YofDofZ d ω - S.YofDofZ ![false, false] ω) =ᵐ[P.μ]
        fun ω => (S.YofD d ω - S.YofD ![false, false] ω) *
          (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [YofDofZ_decomposition As d hd,
        YofDofZ_zero_ae_eq_YofD_zero As,
        DofZ_in_two_values As d hd] with ω hdecomp hzero hcase
    rw [hdecomp, hzero]
    rcases hcase with h | h
    · have h1 : (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω = 1 := by
        exact Set.indicator_of_mem (s := S.DofZEq d d) (f := fun _ => (1 : ℝ)) h
      have h2 : (S.DofZEq d ![false, false]).indicator (fun _ => (1 : ℝ)) ω = 0 := by
        apply Set.indicator_of_notMem
        intro h0
        have hd_ne_zero : d ≠ ![false, false] := by
          rcases hd with rfl | rfl <;> decide
        exact hd_ne_zero (h.symm.trans h0)
      rw [h1, h2]
      ring_nf
    · have h1 : (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω = 0 := by
        apply Set.indicator_of_notMem
        intro hd'
        have hd_ne_zero : d ≠ ![false, false] := by
          rcases hd with rfl | rfl <;> decide
        exact hd_ne_zero (hd'.symm.trans h)
      have h2 : (S.DofZEq d ![false, false]).indicator (fun _ => (1 : ℝ)) ω = 1 := by
        exact Set.indicator_of_mem (s := S.DofZEq d ![false, false])
          (f := fun _ => (1 : ℝ)) h
      rw [h1, h2]
      ring_nf
  rw [← MeasureTheory.integral_sub (As.integrable_YofDofZ d)
      (As.integrable_YofDofZ ![false, false])]
  rw [MeasureTheory.integral_congr_ae hpoint]
  have h_rw :
      (fun ω => (S.YofD d ω - S.YofD ![false, false] ω) *
          (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω)
        = (S.DofZEq d d).indicator
            (fun ω => S.YofD d ω - S.YofD ![false, false] ω) := by
    funext ω
    by_cases hω : ω ∈ S.DofZEq d d
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [h_rw, MeasureTheory.integral_indicator (S.measurableSet_DofZEq d d)]

/-! ### Main when-to-treat identification (prop:po-dynamic-late-when-to-treat) -/

/-- **When-to-treat dynamic LATE Wald identity** (unconditional).

For `d ∈ {(1,0), (0,1)}`,
`τ_d = (obsMean(d) - obsMean(0)) / obsProb(d, d)`. -/
theorem whenToTreat_wald (As : S.Assumptions) (d : Fin 2 → Bool)
    (hd : d = ![true, false] ∨ d = ![false, true]) :
    S.whenToTreatLATE d
      = (S.obsMean d - S.obsMean ![false, false]) / S.obsProb d d := by
  -- Numerator: combine the outcome bridge (twice) with the
  -- one-sided-noncompliance decomposition.
  have hNum : (∫ ω in S.DofZEq d d,
                  (S.YofD d ω - S.YofD ![false, false] ω) ∂P.μ)
      = S.obsMean d - S.obsMean ![false, false] := by
    have hbr_d : ∫ ω, S.YofDofZ d ω ∂P.μ = S.obsMean d := by
      exact outcome_bridge As d
    have hbr_0 : ∫ ω, S.YofDofZ ![false, false] ω ∂P.μ
                  = S.obsMean ![false, false] := by
      exact outcome_bridge As ![false, false]
    have hdiff := int_outcome_difference_identity As d hd
    -- ∫ Y(D(d)) - ∫ Y(D(0)) = ∫_{D(d)=d} (Y(d)-Y(0)) dμ
    -- and the LHS rewrites to obsMean(d) - obsMean(0) via the bridges.
    rw [hbr_d, hbr_0] at hdiff
    linarith [hdiff]
  -- Denominator: compliance bridge.
  have hDen : (P.μ (S.DofZEq d d)).toReal = S.obsProb d d := by
    have hd_pre : Preceq d d := by
      rcases hd with h | h <;>
        (subst h; refine ⟨?_, ?_⟩ <;> simp)
    exact compliance_bridge As d d hd_pre
  -- Combine.
  unfold whenToTreatLATE LATE
  rw [hNum, hDen]

/-- **Mixture dynamic LATE Wald identity** (unconditional).

For every `z` (totalized at `z = 0`),
`β_z = (obsMean(z) - obsMean(0)) / (1 - obsProb(z, 0))`.

The denominator `1 - obsProb(z, 0)` is `P{D(z) ≠ 0}` by the compliance
bridge applied at `(z, 0)`. -/
theorem mixtureLATE_wald (As : S.Assumptions) (z : Fin 2 → Bool) :
    S.mixtureLATE z
      = (S.obsMean z - S.obsMean ![false, false]) / (1 - S.obsProb z ![false, false]) := by
  let z0 : Fin 2 → Bool := ![false, false]
  have hset : {ω | S.DofZ z ω ≠ z0} = (S.DofZEq z z0)ᶜ := by
    ext ω
    rfl
  have hpre_z0 : Preceq z0 z := by
    refine ⟨?_, ?_⟩ <;> simp [z0]
  have hpre_00 : Preceq z0 z0 := by
    refine ⟨?_, ?_⟩ <;> simp [z0]
  have hbr_z : ∫ ω, S.YofDofZ z ω ∂P.μ = S.obsMean z := by
    exact outcome_bridge As z
  have hbr_0 : ∫ ω, S.YofDofZ z0 ω ∂P.μ = S.obsMean z0 := by
    exact outcome_bridge As z0
  have hY0_int :
      ∫ ω, S.YofD z0 ω ∂P.μ = ∫ ω, S.YofDofZ z0 ω ∂P.μ := by
    exact (MeasureTheory.integral_congr_ae (YofDofZ_zero_ae_eq_YofD_zero As).symm)
  have hzero_set :
      ∫ ω in S.DofZEq z z0, (S.YofDofZ z ω - S.YofD z0 ω) ∂P.μ = 0 := by
    have hpoint : ∀ᵐ ω ∂P.μ,
        ω ∈ S.DofZEq z z0 → S.YofDofZ z ω - S.YofD z0 ω = 0 := by
      filter_upwards [YofDofZ_eq_YofD_on_DofZEq As z z0] with ω hω hmem
      rw [hω hmem]
      ring
    rw [MeasureTheory.setIntegral_congr_ae (S.measurableSet_DofZEq z z0) hpoint]
    simp
  have hNum :
      (∫ ω in {ω | S.DofZ z ω ≠ z0}, (S.YofDofZ z ω - S.YofD z0 ω) ∂P.μ)
        = S.obsMean z - S.obsMean z0 := by
    have hint : Integrable (fun ω => S.YofDofZ z ω - S.YofD z0 ω) P.μ :=
      (As.integrable_YofDofZ z).sub (As.integrable_YofD z0)
    calc
      (∫ ω in {ω | S.DofZ z ω ≠ z0}, (S.YofDofZ z ω - S.YofD z0 ω) ∂P.μ)
          = ∫ ω in (S.DofZEq z z0)ᶜ, (S.YofDofZ z ω - S.YofD z0 ω) ∂P.μ := by
            rw [hset]
      _ = ∫ ω, (S.YofDofZ z ω - S.YofD z0 ω) ∂P.μ
            - ∫ ω in S.DofZEq z z0, (S.YofDofZ z ω - S.YofD z0 ω) ∂P.μ := by
            exact MeasureTheory.setIntegral_compl (S.measurableSet_DofZEq z z0) hint
      _ = ∫ ω, (S.YofDofZ z ω - S.YofD z0 ω) ∂P.μ := by
            rw [hzero_set, sub_zero]
      _ = (∫ ω, S.YofDofZ z ω ∂P.μ) - (∫ ω, S.YofD z0 ω ∂P.μ) := by
            rw [MeasureTheory.integral_sub (As.integrable_YofDofZ z) (As.integrable_YofD z0)]
      _ = S.obsMean z - S.obsMean z0 := by
            rw [hbr_z, hY0_int, hbr_0]
  have hDen :
      (P.μ {ω | S.DofZ z ω ≠ z0}).toReal = 1 - S.obsProb z z0 := by
    calc
      (P.μ {ω | S.DofZ z ω ≠ z0}).toReal
          = (P.μ (S.DofZEq z z0)ᶜ).toReal := by
            rw [hset]
      _ = 1 - (P.μ (S.DofZEq z z0)).toReal := by
            simpa using
              (MeasureTheory.probReal_compl_eq_one_sub
                (μ := P.μ) (s := S.DofZEq z z0) (S.measurableSet_DofZEq z z0))
      _ = 1 - S.obsProb z z0 := by
            rw [compliance_bridge As z z0 hpre_z0]
  unfold mixtureLATE
  rw [hNum, hDen]

/-! ### Conditional (heterogeneous in `S₀`) versions

Both ratio identifications carry over to the bundle conditional form via
`historyBundle1.condExpRatio`, using `cOutcome_bridge` / `cCompliance_bridge`
in place of the unconditional bridges. -/

/-- **When-to-treat dynamic LATE Wald identity** (heterogeneous in `S₀`).

`τ_d(S₀) =ᵐ (cObsMean(d; S₀) - cObsMean(0; S₀)) / cObsProb(d, d; S₀)`. -/
theorem cWhenToTreat_wald (As : S.Assumptions) (d : Fin 2 → Bool)
    (hd : d = ![true, false] ∨ d = ![false, true]) :
    S.cWhenToTreatLATE d =ᵐ[P.μ]
      fun ω => (S.cObsMean d ω - S.cObsMean ![false, false] ω) / S.cObsProb d d ω := by
  let z0 : Fin 2 → Bool := ![false, false]
  have hd_pre : Preceq d d := by
    rcases hd with h | h <;>
      (subst h; refine ⟨?_, ?_⟩ <;> simp)
  have hpre_00 : Preceq z0 z0 := by
    refine ⟨?_, ?_⟩ <;> simp [z0]
  have hpoint :
      (fun ω => S.YofDofZ d ω - S.YofDofZ z0 ω) =ᵐ[P.μ]
        fun ω => (S.YofD d ω - S.YofD z0 ω) *
          (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [YofDofZ_decomposition As d hd,
        YofDofZ_zero_ae_eq_YofD_zero As,
        DofZ_in_two_values As d hd] with ω hdecomp hzero hcase
    rw [hdecomp, hzero]
    rcases hcase with h | h
    · have h1 : (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω = 1 := by
        exact Set.indicator_of_mem (s := S.DofZEq d d) (f := fun _ => (1 : ℝ)) h
      have h2 : (S.DofZEq d z0).indicator (fun _ => (1 : ℝ)) ω = 0 := by
        apply Set.indicator_of_notMem
        intro h0
        have hd_ne_zero : d ≠ z0 := by
          rcases hd with hdz | hdz <;> subst hdz <;> simp [z0]
        exact hd_ne_zero (h.symm.trans h0)
      rw [h1, h2]
      ring_nf
      simp [z0]
    · have h1 : (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω = 0 := by
        apply Set.indicator_of_notMem
        intro hd'
        have hd_ne_zero : d ≠ z0 := by
          rcases hd with hdz | hdz <;> subst hdz <;> simp [z0]
        exact hd_ne_zero (hd'.symm.trans h)
      have h2 : (S.DofZEq d z0).indicator (fun _ => (1 : ℝ)) ω = 1 := by
        exact Set.indicator_of_mem (s := S.DofZEq d z0)
          (f := fun _ => (1 : ℝ)) h
      rw [h1, h2]
      ring_nf
  have hce_congr :
      S.historyBundle1.condExpGiven
          (fun ω => S.YofDofZ d ω - S.YofDofZ z0 ω) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven
          (fun ω => (S.YofD d ω - S.YofD z0 ω) *
            (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω) P.μ := by
    exact S.historyBundle1.condExpGiven_congr_ae hpoint
  have hsub :
      S.historyBundle1.condExpGiven
          (fun ω => S.YofDofZ d ω - S.YofDofZ z0 ω) P.μ
        =ᵐ[P.μ]
      fun ω => S.historyBundle1.condExpGiven (S.YofDofZ d) P.μ ω -
        S.historyBundle1.condExpGiven (S.YofDofZ z0) P.μ ω := by
    unfold POCFBundle.condExpGiven
    simpa using
      (MeasureTheory.condExp_sub (μ := P.μ)
        (f := S.YofDofZ d) (g := S.YofDofZ z0)
        (As.integrable_YofDofZ d) (As.integrable_YofDofZ z0)
        S.historyBundle1.sigma)
  have hbr_d := cOutcome_bridge As d d hd_pre
  have hbr_0 := cOutcome_bridge As z0 z0 hpre_00
  have hNum :
      S.historyBundle1.condExpGiven
          (fun ω => (S.YofD d ω - S.YofD z0 ω) *
            (S.DofZEq d d).indicator (fun _ => (1 : ℝ)) ω) P.μ
        =ᵐ[P.μ]
      fun ω => S.cObsMean d ω - S.cObsMean z0 ω := by
    filter_upwards [hce_congr, hsub, hbr_d, hbr_0] with ω hcg hs hbd hb0
    rw [← hcg, hs, hbd, hb0]
  have hDen := cCompliance_bridge As d d hd_pre
  unfold cWhenToTreatLATE cLATE POCFBundle.condExpRatio
  filter_upwards [hNum, hDen] with ω hN hD
  rw [hN, hD]

/-- **Mixture dynamic LATE Wald identity** (heterogeneous in `S₀`). -/
theorem cMixtureLATE_wald (As : S.Assumptions) (z : Fin 2 → Bool) :
    (S.cMixtureLATE z =ᵐ[P.μ]
      fun ω => (S.cObsMean z ω - S.cObsMean ![false, false] ω) /
               (1 - S.cObsProb z ![false, false] ω)) := by
  let z0 : Fin 2 → Bool := ![false, false]
  have hpre_z0 : Preceq z0 z := by
    refine ⟨?_, ?_⟩ <;> simp [z0]
  have hpre_00 : Preceq z0 z0 := by
    refine ⟨?_, ?_⟩ <;> simp [z0]
  have hpoint :
      (fun ω => S.YofDofZ z ω - S.YofDofZ z0 ω) =ᵐ[P.μ]
        fun ω => (S.YofDofZ z ω - S.YofD z0 ω) *
          ({ω | S.DofZ z ω ≠ z0}).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [YofDofZ_zero_ae_eq_YofD_zero As,
        YofDofZ_eq_YofD_on_DofZEq As z z0] with ω hzero hzero_event
    by_cases h : S.DofZ z ω = z0
    · have hind :
          ({ω | S.DofZ z ω ≠ z0}).indicator (fun _ => (1 : ℝ)) ω = 0 := by
        apply Set.indicator_of_notMem
        simpa using h
      rw [hzero, hzero_event h, hind]
      ring
    · have hind :
          ({ω | S.DofZ z ω ≠ z0}).indicator (fun _ => (1 : ℝ)) ω = 1 := by
        exact Set.indicator_of_mem (s := {ω | S.DofZ z ω ≠ z0})
          (f := fun _ => (1 : ℝ)) h
      rw [hzero, hind]
      ring
  have hce_congr :
      S.historyBundle1.condExpGiven
          (fun ω => S.YofDofZ z ω - S.YofDofZ z0 ω) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven
          (fun ω => (S.YofDofZ z ω - S.YofD z0 ω) *
            ({ω | S.DofZ z ω ≠ z0}).indicator (fun _ => (1 : ℝ)) ω) P.μ := by
    exact S.historyBundle1.condExpGiven_congr_ae hpoint
  have hsub :
      S.historyBundle1.condExpGiven
          (fun ω => S.YofDofZ z ω - S.YofDofZ z0 ω) P.μ
        =ᵐ[P.μ]
      fun ω => S.historyBundle1.condExpGiven (S.YofDofZ z) P.μ ω -
        S.historyBundle1.condExpGiven (S.YofDofZ z0) P.μ ω := by
    unfold POCFBundle.condExpGiven
    simpa using
      (MeasureTheory.condExp_sub (μ := P.μ)
        (f := S.YofDofZ z) (g := S.YofDofZ z0)
        (As.integrable_YofDofZ z) (As.integrable_YofDofZ z0)
        S.historyBundle1.sigma)
  have hbr_z := cOutcome_bridge As z z0 hpre_z0
  have hbr_0 := cOutcome_bridge As z0 z0 hpre_00
  have hNum :
      S.historyBundle1.condExpGiven
          (fun ω => (S.YofDofZ z ω - S.YofD z0 ω) *
            ({ω | S.DofZ z ω ≠ z0}).indicator (fun _ => (1 : ℝ)) ω) P.μ
        =ᵐ[P.μ]
      fun ω => S.cObsMean z ω - S.cObsMean z0 ω := by
    filter_upwards [hce_congr, hsub, hbr_z, hbr_0] with ω hcg hs hbz hb0
    rw [← hcg, hs, hbz, hb0]
  have hInd :
      (({ω | S.DofZ z ω ≠ z0}).indicator (fun _ => (1 : ℝ)) : P.Ω → ℝ)
        = fun ω => (1 : ℝ) - (S.DofZEq z z0).indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases h : S.DofZ z ω = z0
    · have hne : ω ∉ {ω | S.DofZ z ω ≠ z0} := by
        simpa using h
      rw [Set.indicator_of_notMem hne,
        Set.indicator_of_mem (s := S.DofZEq z z0) (f := fun _ => (1 : ℝ)) h]
      ring
    · have hzero : ω ∉ S.DofZEq z z0 := by
        simpa [DofZEq] using h
      rw [Set.indicator_of_mem (s := {ω | S.DofZ z ω ≠ z0})
          (f := fun _ => (1 : ℝ)) h,
        Set.indicator_of_notMem hzero]
      ring
  have hconst :
      S.historyBundle1.condExpGiven (fun _ : P.Ω => (1 : ℝ)) P.μ
        = fun _ : P.Ω => (1 : ℝ) := by
    unfold POCFBundle.condExpGiven
    exact MeasureTheory.condExp_const S.historyBundle1.sigma_le (1 : ℝ)
  have hind_int :
      Integrable ((S.DofZEq z z0).indicator (fun _ => (1 : ℝ)) : P.Ω → ℝ) P.μ := by
    exact (integrable_const (1 : ℝ)).indicator (S.measurableSet_DofZEq z z0)
  have hden_sub :
      S.historyBundle1.condExpGiven
          (fun ω => (1 : ℝ) - (S.DofZEq z z0).indicator (fun _ => (1 : ℝ)) ω) P.μ
        =ᵐ[P.μ]
      fun ω => (1 : ℝ) -
        S.historyBundle1.condExpGiven
          ((S.DofZEq z z0).indicator (fun _ => (1 : ℝ))) P.μ ω := by
    have hsub' :
        S.historyBundle1.condExpGiven
            (fun ω => (fun _ : P.Ω => (1 : ℝ)) ω -
              (S.DofZEq z z0).indicator (fun _ => (1 : ℝ)) ω) P.μ
          =ᵐ[P.μ]
        fun ω => S.historyBundle1.condExpGiven (fun _ : P.Ω => (1 : ℝ)) P.μ ω -
          S.historyBundle1.condExpGiven
            ((S.DofZEq z z0).indicator (fun _ => (1 : ℝ))) P.μ ω := by
      unfold POCFBundle.condExpGiven
      simpa using
        (MeasureTheory.condExp_sub (μ := P.μ)
          (f := fun _ : P.Ω => (1 : ℝ))
          (g := (S.DofZEq z z0).indicator (fun _ => (1 : ℝ)))
          (integrable_const (1 : ℝ)) hind_int S.historyBundle1.sigma)
    filter_upwards [hsub'] with ω hω
    rw [hω, hconst]
  have hDen_bridge := cCompliance_bridge As z z0 hpre_z0
  have hDen :
      S.historyBundle1.condExpGiven
          (({ω | S.DofZ z ω ≠ z0}).indicator (fun _ => (1 : ℝ))) P.μ
        =ᵐ[P.μ]
      fun ω => 1 - S.cObsProb z z0 ω := by
    have hcompl := S.historyBundle1.condExpGiven_congr_ae
      (μ := P.μ) (Filter.Eventually.of_forall (congrFun hInd))
    filter_upwards [hcompl, hden_sub, hDen_bridge] with ω hc hs hb
    rw [hc, hs, hb]
  unfold cMixtureLATE POCFBundle.condExpRatio
  filter_upwards [hNum, hDen] with ω hN hD
  rw [hN, hD]

end PODynLATESystem

end PO
end Causalean
