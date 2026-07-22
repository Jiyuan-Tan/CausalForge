/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-Period Dynamic LATE: counterfactual / observable bridge identities

The four bridge lemmas (rem:po-dynamic-late-bridge) connecting the
counterfactual-side averages `E[Y(D(z))]`, `P{D(z) = d}` to the observable
nested-regression functionals `obsMean(z)`, `obsProb(z, d)` (and their
`S₀`-conditional versions).  These are the measure-theoretic core of
prop:po-dynamic-late-when-to-treat -- once they are in hand, the ratio
identifications in `WhenToTreat.lean` are short algebraic consequences.

## Design

The four bridge identities decompose into:

* **Two `S₀`-conditional bridges** (`cOutcome_bridge`, `cCompliance_bridge`):
  the meat — each is a *two-stage* application of the bundle workhorse
  `POCFBundle.condExpRatio_of_consistency_CondIndepCFBundle`
  (in `PO/Conditioning/EventCondExpBundle.lean`), once at stage 2 (peeling the inner
  ratio with `ignorability2`), once at stage 1 (peeling the outer ratio
  with `ignorability1`), interleaved with consistency-on-event rewrites
  from `DynamicLATE/Consistency.lean`.
* **Two unconditional bridges** (`outcome_bridge`, `compliance_bridge`):
  short corollaries obtained by integrating the conditional versions and
  using the property `∫ B.condExpGiven f dμ = ∫ f dμ`.

The structural shape mirrors the DTR `cdtr_step` induction (in
`PO/ID/Exact/DTR/Induction.lean`), but adapted to *nested
event-conditioning* rather than nested bundle-conditioning: the inner ratio
at stage 2 is cancelled with the indicator of `Z₁ = z₁`, the outer ratio at
stage 1 with the unconditional indicator.
-/

import Causalean.PO.ID.Exact.DynamicLATE.Consistency
import Causalean.PO.Conditioning.EventCondExpBundle

/-! # Dynamic LATE Counterfactual Bridges

This file proves the counterfactual-to-observable bridge identities for the
two-period dynamic LATE setup. Conditional bridges given the baseline state are
the workhorses, and the unconditional bridges follow by integration. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace PODynLATESystem

variable {P : POSystem} {γ₀ γ₁ : Type}
variable [MeasurableSpace γ₀] [MeasurableSpace γ₁]
variable [MeasurableSingletonClass γ₀] [MeasurableSingletonClass γ₁]
variable [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
variable {S : PODynLATESystem P γ₀ γ₁}

/-! ### One-sided noncompliance corollary

Under the noncompliance assumption, `D(z)` lies in `{d | d ≼ z}` almost
surely, so the probability of `{D(z) = d}` for `¬ d ≼ z` is zero.  This is
used by `WhenToTreat.lean` to identify the denominator of the mixture
ratio, namely `1 - obsProb(z, 0)`. -/

/-- Under one-sided noncompliance, a treatment path not below the encouragement path has zero probability. -/
theorem probDofZ_eq_zero_of_not_preceq (As : S.Assumptions)
    (z d : Fin 2 → Bool) (h : ¬ Preceq d z) :
    P.μ (S.DofZEq z d) = 0 := by
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.ae_iff.mp (As.oneSidedNoncompliance z))
  intro ω hω hgood
  apply h
  unfold DofZEq at hω
  have hD1 : S.D1ofZ z ω = d 0 := by
    have := congrFun hω 0
    simpa [DofZ] using this
  have hD2 : S.D2ofZ z ω = d 1 := by
    have := congrFun hω 1
    simpa [DofZ] using this
  exact ⟨by simpa [hD1] using hgood.1, by simpa [hD2] using hgood.2⟩

/-! ### Stage-2 inner ratio bridges

The inner regression `innerCondY z` (resp. `innerCondD z d`) is identified
on the event `{Z₁ = z₁}` with the bundle conditional expectation under
`historyBundle2` of the counterfactual outcome (resp. compliance event).
These are obtained by applying the bundle workhorse with `a := S.z2Var`,
`B := S.cfBundle2 (z 1)`, `C := S.historyBundle2`, then pulling out the
`historyBundle2`-measurable `1_{Z₁=z₁}` factor and cancelling on the ratio.

Each bridge uses `condExpRatio_of_consistency_CondIndepCFBundle`, together
with `condExpGiven`-pullout for the bundle2-measurable indicators
`1_{Z₁=z 0}`, `1_{D₁=d 0}` and the consistency rewrite at `Z₂`. -/

/-- The stage-2 outcome ratio bridge identifies the inner outcome regression on a first-encouragement cell.

On the event `{Z₁ = z₁}`,

`innerCondY(z) =ᵐ historyBundle2.condExpGiven (Y(D₁,D₂(Z₁,z 1)))`. -/
theorem innerCondY_mul_z1_indicator (As : S.Assumptions) (z : Fin 2 → Bool) :
    (fun ω => S.innerCondY z ω * S.z1Var.indicator (z 0) ω)
      =ᵐ[P.μ]
    fun ω => S.z1Var.indicator (z 0) ω
      * S.historyBundle2.condExpGiven (S.YofZ2 (z 1)) P.μ ω := by
  have hcf2_n : (S.cfBundle2 (z 1)).n = 2 := rfl
  let i0 : Fin (S.cfBundle2 (z 1)).n := ⟨0, by rw [hcf2_n]; decide⟩
  let ψ : (∀ i : Fin (S.cfBundle2 (z 1)).n, (S.cfBundle2 (z 1)).type i) → ℝ :=
    fun f => f i0
  have hψ_meas : Measurable ψ := by
    change Measurable (fun f : (∀ i, (S.cfBundle2 (z 1)).type i) => f i0)
    exact measurable_pi_apply i0
  have hψ_eq : (fun ω => ψ ((S.cfBundle2 (z 1)).jointValue ω)) = S.YofZ2 (z 1) := by
    funext ω
    rfl
  have hψ_int : Integrable (fun ω => ψ ((S.cfBundle2 (z 1)).jointValue ω)) P.μ := by
    rw [hψ_eq]
    exact As.integrable_YofZ2 (z 1)
  have hF_eq :
      (fun ω => S.factualY ω * S.z2Var.indicator (z 1) ω) =ᵐ[P.μ]
        fun ω => ψ ((S.cfBundle2 (z 1)).jointValue ω) *
          S.z2Var.indicator (z 1) ω := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    by_cases hz2 : S.factualZ2 ω = z 1
    · have hi : S.z2Var.indicator (z 1) ω = 1 :=
        S.z2Var.indicator_apply_eq_one hz2
      have hc := YofZ2_eq_factualY_on_z2Event (S := S) As (z 1) hz2
      simp [hi, congrFun hψ_eq ω, hc]
    · have hi : S.z2Var.indicator (z 1) ω = 0 :=
        S.z2Var.indicator_apply_eq_zero hz2
      simp [hi]
  have hover :
      ∀ᵐ ω ∂P.μ, S.historyBundle2.condExpGiven (S.z2Var.indicator (z 1)) P.μ ω ≠ 0 := by
    filter_upwards [As.overlap2 (z 1)] with ω hpos
    linarith
  have hRatio2 :
      S.historyBundle2.condExpRatio
        (fun ω => S.factualY ω * S.z2Var.indicator (z 1) ω)
        (S.z2Var.indicator (z 1)) P.μ
        =ᵐ[P.μ]
      S.historyBundle2.condExpGiven (S.YofZ2 (z 1)) P.μ := by
    have h := POCFBundle.condExpRatio_of_consistency_CondIndepCFBundle
      (B := S.cfBundle2 (z 1)) (C := S.historyBundle2)
      (a := S.z2Var) (x := z 1)
      (As.ignorability2 (z 1)) S.measurable_factualY
      hψ_meas hψ_int hF_eq hover
    rw [hψ_eq] at h
    exact h
  let q : P.Ω → ℝ := S.z1Var.indicator (z 0)
  have hq_sm : StronglyMeasurable[S.historyBundle2.sigma] q := by
    dsimp [q]
    unfold POVar.indicator
    refine (stronglyMeasurable_const (b := (1 : ℝ))).indicator ?_
    have hn : S.historyBundle2.n = 4 := rfl
    let iZ1 : Fin S.historyBundle2.n := ⟨2, by rw [hn]; decide⟩
    let A : Set (∀ i : Fin S.historyBundle2.n, S.historyBundle2.type i) :=
      {f | f iZ1 = z 0}
    change MeasurableSet[MeasurableSpace.comap S.historyBundle2.jointValue inferInstance]
      (S.z1Var.event (z 0))
    refine ⟨A, ?_, ?_⟩
    · dsimp [A]
      measurability
    · ext ω
      rfl
  have hz2_int : Integrable (S.z2Var.indicator (z 1)) P.μ :=
    S.z2Var.integrable_indicator (z 1)
  have hY_z2_int :
      Integrable (fun ω => S.factualY ω * S.z2Var.indicator (z 1) ω) P.μ :=
    S.z2Var.integrable_mul_indicator (z 1) As.integrable_factualY S.measurable_factualY
  have hq_z2_int : Integrable (q * S.z2Var.indicator (z 1)) P.μ := by
    have h := S.z1Var.integrable_mul_indicator (z 0) hz2_int
      (S.z2Var.measurable_indicator (z 1))
    exact h.congr (Filter.Eventually.of_forall (fun ω => by dsimp [q]; ring))
  have hq_Y_z2_int :
      Integrable
        (q * fun ω => S.factualY ω * S.z2Var.indicator (z 1) ω) P.μ := by
    have h := S.z1Var.integrable_mul_indicator (z 0) hY_z2_int
      (S.measurable_factualY.mul (S.z2Var.measurable_indicator (z 1)))
    exact h.congr (Filter.Eventually.of_forall (fun ω => by dsimp [q]; ring))
  have hNumPull :
      S.historyBundle2.condExpGiven
        (q * fun ω => S.factualY ω * S.z2Var.indicator (z 1) ω) P.μ
        =ᵐ[P.μ]
      q * S.historyBundle2.condExpGiven
        (fun ω => S.factualY ω * S.z2Var.indicator (z 1) ω) P.μ :=
    S.historyBundle2.condExpGiven_mul_of_stronglyMeasurable_left
      hq_sm hq_Y_z2_int hY_z2_int
  have hDenPull :
      S.historyBundle2.condExpGiven (q * S.z2Var.indicator (z 1)) P.μ
        =ᵐ[P.μ]
      q * S.historyBundle2.condExpGiven (S.z2Var.indicator (z 1)) P.μ :=
    S.historyBundle2.condExpGiven_mul_of_stronglyMeasurable_left
      hq_sm hq_z2_int hz2_int
  filter_upwards [hRatio2, hNumPull, hDenPull] with ω hR hN hD
  unfold innerCondY indZ POCFBundle.condExpRatio
  have hargN :
      (fun ω => S.factualY ω *
          (S.z1Var.indicator (z 0) ω * S.z2Var.indicator (z 1) ω))
        =
      q * fun ω => S.factualY ω * S.z2Var.indicator (z 1) ω := by
    funext ω
    dsimp [q]
    ring
  have hargD :
      (fun ω => S.z1Var.indicator (z 0) ω * S.z2Var.indicator (z 1) ω)
        =
      q * S.z2Var.indicator (z 1) := rfl
  rw [hargN, hargD, hN, hD]
  rcases S.z1Var.indicator_eq_one_or_zero (z 0) ω with hz1 | hz1
  · simp [q, hz1]
    simpa [POCFBundle.condExpRatio] using hR
  · simp [q, hz1]

/-- Real-valued indicator of `{D₂(Z₁, z₂) = b}`. -/
private noncomputable def d2ofZ2EqIndicator (S : PODynLATESystem P γ₀ γ₁)
    (z₂ b : Bool) : P.Ω → ℝ :=
  (S.D2ofZ2 z₂ ⁻¹' {b}).indicator (fun _ => (1 : ℝ))

private lemma measurable_d2ofZ2EqIndicator (S : PODynLATESystem P γ₀ γ₁)
    (z₂ b : Bool) : Measurable (S.d2ofZ2EqIndicator z₂ b) := by
  unfold d2ofZ2EqIndicator
  exact (measurable_const).indicator
    (S.measurable_D2ofZ2 z₂ (MeasurableSet.singleton b))

/-- **Stage-2 compliance ratio bridge** (multiplied by `1_{Z₁=z₁}`).
On the event `{Z₁ = z₁}`,

`innerCondD(z, d) =ᵐ 1_{D₁ = d 0} · historyBundle2.condExpGiven 1_{D₂(Z₁,z 1) = d 1}`. -/
theorem innerCondD_mul_z1_indicator (As : S.Assumptions) (z d : Fin 2 → Bool) :
    (fun ω => S.innerCondD z d ω * S.z1Var.indicator (z 0) ω)
      =ᵐ[P.μ]
    fun ω => S.z1Var.indicator (z 0) ω * S.d1Var.indicator (d 0) ω
      * S.historyBundle2.condExpGiven (S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ ω := by
  have hcf2_n : (S.cfBundle2 (z 1)).n = 2 := rfl
  let i1 : Fin (S.cfBundle2 (z 1)).n := ⟨1, by rw [hcf2_n]; decide⟩
  let ψ : (∀ i : Fin (S.cfBundle2 (z 1)).n, (S.cfBundle2 (z 1)).type i) → ℝ :=
    fun f => ({d 1} : Set Bool).indicator (fun _ => (1 : ℝ)) (f i1)
  have hψ_meas : Measurable ψ := by
    change Measurable (fun f : (∀ i, (S.cfBundle2 (z 1)).type i) =>
      ({d 1} : Set Bool).indicator (fun _ => (1 : ℝ)) (f i1))
    measurability
  have hψ_eq :
      (fun ω => ψ ((S.cfBundle2 (z 1)).jointValue ω)) =
        S.d2ofZ2EqIndicator (z 1) (d 1) := by
    funext ω
    rfl
  have hψ_int : Integrable (fun ω => ψ ((S.cfBundle2 (z 1)).jointValue ω)) P.μ := by
    rw [hψ_eq]
    exact (integrable_const (1 : ℝ)).indicator
      (S.measurable_D2ofZ2 (z 1) (MeasurableSet.singleton (d 1)))
  have hF_eq :
      (fun ω => S.d2Var.indicator (d 1) ω * S.z2Var.indicator (z 1) ω) =ᵐ[P.μ]
        fun ω => ψ ((S.cfBundle2 (z 1)).jointValue ω) *
          S.z2Var.indicator (z 1) ω := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    by_cases hz2 : S.factualZ2 ω = z 1
    · have hc := D2ofZ2_eq_factualD2_on_z2Event (S := S) As (z 1) hz2
      by_cases hd2 : S.factualD2 ω = d 1
      · have hiL : S.d2Var.indicator (d 1) ω = 1 :=
          S.d2Var.indicator_apply_eq_one hd2
        have hiR : ψ ((S.cfBundle2 (z 1)).jointValue ω) = 1 := by
          rw [congrFun hψ_eq ω]
          unfold d2ofZ2EqIndicator
          exact Set.indicator_of_mem
            (show ω ∈ S.D2ofZ2 (z 1) ⁻¹' ({d 1} : Set Bool) from by
              simpa [hc] using hd2) _
        simp [hiL, hiR]
      · have hiL : S.d2Var.indicator (d 1) ω = 0 :=
          S.d2Var.indicator_apply_eq_zero hd2
        have hiR : ψ ((S.cfBundle2 (z 1)).jointValue ω) = 0 := by
          rw [congrFun hψ_eq ω]
          unfold d2ofZ2EqIndicator
          exact Set.indicator_of_notMem
            (show ω ∉ S.D2ofZ2 (z 1) ⁻¹' ({d 1} : Set Bool) from by
              simpa [hc] using hd2) _
        simp [hiL, hiR]
    · have hi : S.z2Var.indicator (z 1) ω = 0 :=
        S.z2Var.indicator_apply_eq_zero hz2
      simp [hi]
  have hover :
      ∀ᵐ ω ∂P.μ, S.historyBundle2.condExpGiven (S.z2Var.indicator (z 1)) P.μ ω ≠ 0 := by
    filter_upwards [As.overlap2 (z 1)] with ω hpos
    linarith
  have hRatio2 :
      S.historyBundle2.condExpRatio
        (fun ω => S.d2Var.indicator (d 1) ω * S.z2Var.indicator (z 1) ω)
        (S.z2Var.indicator (z 1)) P.μ
        =ᵐ[P.μ]
      S.historyBundle2.condExpGiven (S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ := by
    have h := POCFBundle.condExpRatio_of_consistency_CondIndepCFBundle
      (B := S.cfBundle2 (z 1)) (C := S.historyBundle2)
      (a := S.z2Var) (x := z 1)
      (As.ignorability2 (z 1)) (S.d2Var.measurable_indicator (d 1))
      hψ_meas hψ_int hF_eq hover
    rw [hψ_eq] at h
    exact h
  have hz1_sm : StronglyMeasurable[S.historyBundle2.sigma] (S.z1Var.indicator (z 0)) := by
    unfold POVar.indicator
    refine (stronglyMeasurable_const (b := (1 : ℝ))).indicator ?_
    have hn : S.historyBundle2.n = 4 := rfl
    let iZ1 : Fin S.historyBundle2.n := ⟨2, by rw [hn]; decide⟩
    let A : Set (∀ i : Fin S.historyBundle2.n, S.historyBundle2.type i) :=
      {f | f iZ1 = z 0}
    change MeasurableSet[MeasurableSpace.comap S.historyBundle2.jointValue inferInstance]
      (S.z1Var.event (z 0))
    refine ⟨A, ?_, ?_⟩
    · dsimp [A]
      measurability
    · ext ω
      rfl
  have hd1_sm : StronglyMeasurable[S.historyBundle2.sigma] (S.d1Var.indicator (d 0)) := by
    unfold POVar.indicator
    refine (stronglyMeasurable_const (b := (1 : ℝ))).indicator ?_
    have hn : S.historyBundle2.n = 4 := rfl
    let iD1 : Fin S.historyBundle2.n := ⟨3, by rw [hn]; decide⟩
    let A : Set (∀ i : Fin S.historyBundle2.n, S.historyBundle2.type i) :=
      {f | f iD1 = d 0}
    change MeasurableSet[MeasurableSpace.comap S.historyBundle2.jointValue inferInstance]
      (S.d1Var.event (d 0))
    refine ⟨A, ?_, ?_⟩
    · dsimp [A]
      measurability
    · ext ω
      rfl
  let q : P.Ω → ℝ := fun ω => S.z1Var.indicator (z 0) ω * S.d1Var.indicator (d 0) ω
  have hq_sm : StronglyMeasurable[S.historyBundle2.sigma] q := by
    dsimp [q]
    exact hz1_sm.mul hd1_sm
  have hz2_int : Integrable (S.z2Var.indicator (z 1)) P.μ :=
    S.z2Var.integrable_indicator (z 1)
  have hd2z2_int :
      Integrable (fun ω => S.d2Var.indicator (d 1) ω *
        S.z2Var.indicator (z 1) ω) P.μ :=
    by
      have h := S.d2Var.integrable_mul_indicator (d 1) hz2_int
        (S.z2Var.measurable_indicator (z 1))
      exact h.congr (Filter.Eventually.of_forall
        (fun ω => by simp [mul_comm]))
  have hd1_z2_int :
      Integrable (S.d1Var.indicator (d 0) * S.z2Var.indicator (z 1)) P.μ :=
    by
      have h := S.d1Var.integrable_mul_indicator (d 0) hz2_int
        (S.z2Var.measurable_indicator (z 1))
      exact h.congr (Filter.Eventually.of_forall
        (fun ω => by simp [mul_comm]))
  have hz1_z2_int : Integrable (S.z1Var.indicator (z 0) * S.z2Var.indicator (z 1)) P.μ := by
    have h := S.z1Var.integrable_mul_indicator (z 0) hz2_int
      (S.z2Var.measurable_indicator (z 1))
    exact h.congr (Filter.Eventually.of_forall
      (fun ω => by simp [mul_comm]))
  have hq_z2_int : Integrable (q * S.z2Var.indicator (z 1)) P.μ := by
    have h := S.z1Var.integrable_mul_indicator (z 0) hd1_z2_int
      ((S.d1Var.measurable_indicator (d 0)).mul (S.z2Var.measurable_indicator (z 1)))
    exact h.congr (Filter.Eventually.of_forall (fun ω => by dsimp [q]; ring))
  have hd1_d2z2_int :
      Integrable
        (S.d1Var.indicator (d 0) *
          fun ω => S.d2Var.indicator (d 1) ω * S.z2Var.indicator (z 1) ω) P.μ :=
    by
      have h := S.d1Var.integrable_mul_indicator (d 0) hd2z2_int
        ((S.d2Var.measurable_indicator (d 1)).mul (S.z2Var.measurable_indicator (z 1)))
      exact h.congr (Filter.Eventually.of_forall
        (fun ω => by simp [mul_comm]))
  have hq_d2z2_int :
      Integrable
        (q * fun ω => S.d2Var.indicator (d 1) ω * S.z2Var.indicator (z 1) ω) P.μ := by
    have h := S.z1Var.integrable_mul_indicator (z 0) hd1_d2z2_int
      ((S.d1Var.measurable_indicator (d 0)).mul
        ((S.d2Var.measurable_indicator (d 1)).mul (S.z2Var.measurable_indicator (z 1))))
    exact h.congr (Filter.Eventually.of_forall (fun ω => by dsimp [q]; ring))
  have hNumPull :
      S.historyBundle2.condExpGiven
        (q * fun ω => S.d2Var.indicator (d 1) ω * S.z2Var.indicator (z 1) ω) P.μ
        =ᵐ[P.μ]
      q * S.historyBundle2.condExpGiven
        (fun ω => S.d2Var.indicator (d 1) ω * S.z2Var.indicator (z 1) ω) P.μ :=
    S.historyBundle2.condExpGiven_mul_of_stronglyMeasurable_left
      hq_sm hq_d2z2_int hd2z2_int
  have hDenPull :
      S.historyBundle2.condExpGiven (S.z1Var.indicator (z 0) * S.z2Var.indicator (z 1)) P.μ
        =ᵐ[P.μ]
      S.z1Var.indicator (z 0) *
        S.historyBundle2.condExpGiven (S.z2Var.indicator (z 1)) P.μ :=
    S.historyBundle2.condExpGiven_mul_of_stronglyMeasurable_left
      hz1_sm hz1_z2_int hz2_int
  filter_upwards [hRatio2, hNumPull, hDenPull] with ω hR hN hD
  unfold innerCondD indD indZ POCFBundle.condExpRatio
  have hargN :
      (fun ω => (S.d1Var.indicator (d 0) ω * S.d2Var.indicator (d 1) ω) *
          (S.z1Var.indicator (z 0) ω * S.z2Var.indicator (z 1) ω))
        =
      q * fun ω => S.d2Var.indicator (d 1) ω * S.z2Var.indicator (z 1) ω := by
    funext ω
    simp [q, Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc]
  have hargD :
      (fun ω => S.z1Var.indicator (z 0) ω * S.z2Var.indicator (z 1) ω)
        =
      S.z1Var.indicator (z 0) * S.z2Var.indicator (z 1) := rfl
  rw [hargN, hargD, hN, hD]
  rcases S.z1Var.indicator_eq_one_or_zero (z 0) ω with hz1 | hz1
  · rcases S.d1Var.indicator_eq_one_or_zero (d 0) ω with hd1 | hd1
    · simp [q, hz1, hd1]
      simpa [POCFBundle.condExpRatio] using hR
    · simp [q, hz1, hd1]
  · simp [q, hz1]

/-! ### `S₀`-conditional bridges (the workhorses) -/

/-- **Outcome bridge** (`S₀`-conditional): the bundle conditional expectation
of `Y(D(z))` given `historyBundle1 = (S₀,)` agrees a.s. with the inner-outer
observable regression `cObsMean z`.

`E[Y(D(z)) | S₀] =ᵐ cObsMean(z; S₀)`. -/
theorem cOutcome_bridge (As : S.Assumptions) (z d : Fin 2 → Bool)
    (_hd : Preceq d z) :
    S.historyBundle1.condExpGiven (S.YofDofZ z) P.μ =ᵐ[P.μ] S.cObsMean z := by
  have hYofZ2_int : Integrable (S.YofZ2 (z 1)) P.μ :=
    As.integrable_YofZ2 (z 1)
  have hcf1_n : (S.cfBundle1 z).n = 3 := rfl
  let i0 : Fin (S.cfBundle1 z).n := ⟨0, by rw [hcf1_n]; decide⟩
  let ψ : (∀ i : Fin (S.cfBundle1 z).n, (S.cfBundle1 z).type i) → ℝ :=
    fun f => f i0
  have hψ_meas : Measurable ψ := by
    change Measurable (fun f : (∀ i, (S.cfBundle1 z).type i) => f i0)
    exact measurable_pi_apply i0
  have hψ_eq : (fun ω => ψ ((S.cfBundle1 z).jointValue ω)) = S.YofDofZ z := by
    funext ω
    rfl
  have hψ_int : Integrable (fun ω => ψ ((S.cfBundle1 z).jointValue ω)) P.μ := by
    rw [hψ_eq]
    exact As.integrable_YofDofZ z
  have hF_eq :
      (fun ω => S.YofDofZ z ω * S.z1Var.indicator (z 0) ω) =ᵐ[P.μ]
        fun ω => ψ ((S.cfBundle1 z).jointValue ω) *
          S.z1Var.indicator (z 0) ω := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp [congrFun hψ_eq ω]
  have hStage1 := POCFBundle.condExpGiven_mul_of_consistency_CondIndepCFBundle
    (B := S.cfBundle1 z) (C := S.historyBundle1)
    (a := S.z1Var) (x := z 0)
    (As.ignorability1 z) (S.measurable_YofDofZ z) hψ_meas hψ_int hF_eq
  rw [hψ_eq] at hStage1
  have hσ12 : S.historyBundle1.sigma ≤ S.historyBundle2.sigma := by
    have hn2 : S.historyBundle2.n = 4 := rfl
    let iS0 : Fin S.historyBundle2.n := ⟨0, by rw [hn2]; decide⟩
    let hb12_proj :
        (∀ i, S.historyBundle2.type i) → (∀ i, S.historyBundle1.type i) :=
      fun f j => Fin.cases (f iS0) (fun j0 => j0.elim0) j
    have hproj_meas : Measurable hb12_proj := by
      apply measurable_pi_lambda
      intro j
      refine Fin.cases ?_ ?_ j
      · exact measurable_pi_apply iS0
      · intro j0
        exact j0.elim0
    have hjoint : S.historyBundle1.jointValue = hb12_proj ∘ S.historyBundle2.jointValue := by
      funext ω j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro j0
        exact j0.elim0
    change MeasurableSpace.comap S.historyBundle1.jointValue inferInstance ≤
      MeasurableSpace.comap S.historyBundle2.jointValue inferInstance
    rw [hjoint, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hproj_meas.comap_le
  have hz1_sm2 : StronglyMeasurable[S.historyBundle2.sigma] (S.z1Var.indicator (z 0)) := by
    unfold POVar.indicator
    refine (stronglyMeasurable_const (b := (1 : ℝ))).indicator ?_
    have hn : S.historyBundle2.n = 4 := rfl
    let iZ1 : Fin S.historyBundle2.n := ⟨2, by rw [hn]; decide⟩
    let A : Set (∀ i : Fin S.historyBundle2.n, S.historyBundle2.type i) :=
      {f | f iZ1 = z 0}
    change MeasurableSet[MeasurableSpace.comap S.historyBundle2.jointValue inferInstance]
      (S.z1Var.event (z 0))
    refine ⟨A, ?_, ?_⟩
    · dsimp [A]
      measurability
    · ext ω
      rfl
  have hz1_YofZ2_int : Integrable (S.z1Var.indicator (z 0) * S.YofZ2 (z 1)) P.μ := by
    have h := S.z1Var.integrable_mul_indicator (z 0) hYofZ2_int
      (S.measurable_YofZ2 (z 1))
    exact h.congr (Filter.Eventually.of_forall
      (fun ω => by simp [mul_comm]))
  have hRevPull :
      (fun ω => S.z1Var.indicator (z 0) ω *
        S.historyBundle2.condExpGiven (S.YofZ2 (z 1)) P.μ ω)
        =ᵐ[P.μ]
      S.historyBundle2.condExpGiven (S.z1Var.indicator (z 0) * S.YofZ2 (z 1)) P.μ := by
    have hpull := S.historyBundle2.condExpGiven_mul_of_stronglyMeasurable_left
      hz1_sm2 hz1_YofZ2_int hYofZ2_int
    filter_upwards [hpull] with ω hω
    simpa [Pi.mul_apply] using hω.symm
  haveI : IsFiniteMeasure (P.μ.trim S.historyBundle2.sigma_le) := isFiniteMeasure_trim _
  have hTower :
      S.historyBundle1.condExpGiven
        (S.historyBundle2.condExpGiven
          (S.z1Var.indicator (z 0) * S.YofZ2 (z 1)) P.μ) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven (S.z1Var.indicator (z 0) * S.YofZ2 (z 1)) P.μ := by
    have h := S.historyBundle2.condExpGiven_tower_of_le
      (g := S.z1Var.indicator (z 0) * S.YofZ2 (z 1)) (μ := P.μ)
      (m := S.historyBundle1.sigma) hσ12
    simpa [POCFBundle.condExpGiven] using h
  have hCons :
      (S.z1Var.indicator (z 0) * S.YofZ2 (z 1)) =ᵐ[P.μ]
      (fun ω => S.YofDofZ z ω * S.z1Var.indicator (z 0) ω) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    by_cases hz1 : S.factualZ1 ω = z 0
    · have hi : S.z1Var.indicator (z 0) ω = 1 := S.z1Var.indicator_apply_eq_one hz1
      have hc := YofDofZ_eq_YofZ2_on_z1Event (S := S) As z hz1
      simp [Pi.mul_apply, hi, hc]
    · have hi : S.z1Var.indicator (z 0) ω = 0 := S.z1Var.indicator_apply_eq_zero hz1
      simp [Pi.mul_apply, hi]
  have hOuterLhs :
      S.historyBundle1.condExpGiven
        (fun ω => S.innerCondY z ω * S.z1Var.indicator (z 0) ω) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven
        (fun ω => S.YofDofZ z ω * S.z1Var.indicator (z 0) ω) P.μ := by
    refine (S.historyBundle1.condExpGiven_congr_ae
      (innerCondY_mul_z1_indicator (S := S) As z)).trans ?_
    refine (S.historyBundle1.condExpGiven_congr_ae hRevPull).trans ?_
    refine hTower.trans ?_
    exact S.historyBundle1.condExpGiven_congr_ae hCons
  have hprod :
      S.historyBundle1.condExpGiven
        (fun ω => S.innerCondY z ω * S.z1Var.indicator (z 0) ω) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven (S.z1Var.indicator (z 0)) P.μ *
        S.historyBundle1.condExpGiven (S.YofDofZ z) P.μ := by
    refine hOuterLhs.trans ?_
    filter_upwards [hStage1] with ω hω
    simpa [Pi.mul_apply, mul_comm] using hω
  have hne :
      ∀ᵐ ω ∂P.μ, S.historyBundle1.condExpGiven (S.z1Var.indicator (z 0)) P.μ ω ≠ 0 := by
    filter_upwards [As.overlap1 (z 0)] with ω hpos
    linarith
  have hratio := S.historyBundle1.condExpRatio_eq_of_mul hprod hne
  unfold cObsMean
  exact hratio.symm

/-- **Compliance bridge** (`S₀`-conditional): the bundle conditional
probability of the dynamic complier event given `historyBundle1` agrees
a.s. with the inner-outer observable regression `cObsProb z d`.

`P{D(z) = d | S₀} =ᵐ cObsProb(z, d; S₀)`. -/
theorem cCompliance_bridge (As : S.Assumptions) (z d : Fin 2 → Bool)
    (_hd : Preceq d z) :
    S.historyBundle1.condExpGiven
        ((S.DofZEq z d).indicator (fun _ => (1 : ℝ))) P.μ
      =ᵐ[P.μ] S.cObsProb z d := by
  -- Same shape as `cOutcome_bridge`, using `innerCondD_mul_z1_indicator` at
  -- stage 2 and stage-1 consistency to align the dynamic compliance event.
  have htarget_meas : Measurable ((S.DofZEq z d).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (S.measurableSet_DofZEq z d)
  have htarget_int : Integrable ((S.DofZEq z d).indicator (fun _ => (1 : ℝ))) P.μ :=
    (integrable_const (1 : ℝ)).indicator (S.measurableSet_DofZEq z d)
  have hcf1_n : (S.cfBundle1 z).n = 3 := rfl
  let iD1 : Fin (S.cfBundle1 z).n := ⟨1, by rw [hcf1_n]; decide⟩
  let iD2 : Fin (S.cfBundle1 z).n := ⟨2, by rw [hcf1_n]; decide⟩
  let ψ : (∀ i : Fin (S.cfBundle1 z).n, (S.cfBundle1 z).type i) → ℝ :=
    fun f => ({d} : Set (Fin 2 → Bool)).indicator (fun _ => (1 : ℝ))
      (fun i => Fin.cases (f iD1) (fun _ => f iD2) i)
  have hψ_meas : Measurable ψ := by
    dsimp [ψ]
    refine measurable_const.indicator ?_
    exact (measurable_pi_lambda _ (fun i => by
      refine Fin.cases ?_ ?_ i
      · exact measurable_pi_apply iD1
      · intro _
        exact measurable_pi_apply iD2)) (MeasurableSet.singleton d)
  have hψ_eq :
      (fun ω => ψ ((S.cfBundle1 z).jointValue ω)) =
        (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rfl
  have hψ_int : Integrable (fun ω => ψ ((S.cfBundle1 z).jointValue ω)) P.μ := by
    rw [hψ_eq]
    exact htarget_int
  have hF_eq :
      (fun ω => (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω *
          S.z1Var.indicator (z 0) ω) =ᵐ[P.μ]
        fun ω => ψ ((S.cfBundle1 z).jointValue ω) *
          S.z1Var.indicator (z 0) ω := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp [congrFun hψ_eq ω]
  have hStage1 := POCFBundle.condExpGiven_mul_of_consistency_CondIndepCFBundle
    (B := S.cfBundle1 z) (C := S.historyBundle1)
    (a := S.z1Var) (x := z 0)
    (As.ignorability1 z) htarget_meas hψ_meas hψ_int hF_eq
  rw [hψ_eq] at hStage1
  have hσ12 : S.historyBundle1.sigma ≤ S.historyBundle2.sigma := by
    have hn2 : S.historyBundle2.n = 4 := rfl
    let iS0 : Fin S.historyBundle2.n := ⟨0, by rw [hn2]; decide⟩
    let hb12_proj :
        (∀ i, S.historyBundle2.type i) → (∀ i, S.historyBundle1.type i) :=
      fun f j => Fin.cases (f iS0) (fun j0 => j0.elim0) j
    have hproj_meas : Measurable hb12_proj := by
      apply measurable_pi_lambda
      intro j
      refine Fin.cases ?_ ?_ j
      · exact measurable_pi_apply iS0
      · intro j0
        exact j0.elim0
    have hjoint : S.historyBundle1.jointValue = hb12_proj ∘ S.historyBundle2.jointValue := by
      funext ω j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro j0
        exact j0.elim0
    change MeasurableSpace.comap S.historyBundle1.jointValue inferInstance ≤
      MeasurableSpace.comap S.historyBundle2.jointValue inferInstance
    rw [hjoint, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hproj_meas.comap_le
  have hz1_sm : StronglyMeasurable[S.historyBundle2.sigma] (S.z1Var.indicator (z 0)) := by
    unfold POVar.indicator
    refine (stronglyMeasurable_const (b := (1 : ℝ))).indicator ?_
    have hn : S.historyBundle2.n = 4 := rfl
    let iZ1 : Fin S.historyBundle2.n := ⟨2, by rw [hn]; decide⟩
    let A : Set (∀ i : Fin S.historyBundle2.n, S.historyBundle2.type i) :=
      {f | f iZ1 = z 0}
    change MeasurableSet[MeasurableSpace.comap S.historyBundle2.jointValue inferInstance]
      (S.z1Var.event (z 0))
    refine ⟨A, ?_, ?_⟩
    · dsimp [A]
      measurability
    · ext ω
      rfl
  have hd1_sm : StronglyMeasurable[S.historyBundle2.sigma] (S.d1Var.indicator (d 0)) := by
    unfold POVar.indicator
    refine (stronglyMeasurable_const (b := (1 : ℝ))).indicator ?_
    have hn : S.historyBundle2.n = 4 := rfl
    let iD1h : Fin S.historyBundle2.n := ⟨3, by rw [hn]; decide⟩
    let A : Set (∀ i : Fin S.historyBundle2.n, S.historyBundle2.type i) :=
      {f | f iD1h = d 0}
    change MeasurableSet[MeasurableSpace.comap S.historyBundle2.jointValue inferInstance]
      (S.d1Var.event (d 0))
    refine ⟨A, ?_, ?_⟩
    · dsimp [A]
      measurability
    · ext ω
      rfl
  let q : P.Ω → ℝ := fun ω => S.z1Var.indicator (z 0) ω * S.d1Var.indicator (d 0) ω
  have hq_sm : StronglyMeasurable[S.historyBundle2.sigma] q := by
    dsimp [q]
    exact hz1_sm.mul hd1_sm
  have hd2cf_meas : Measurable (S.d2ofZ2EqIndicator (z 1) (d 1)) := by
    unfold d2ofZ2EqIndicator
    exact measurable_const.indicator
      (S.measurable_D2ofZ2 (z 1) (MeasurableSet.singleton (d 1)))
  have hd2cf_int : Integrable (S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ :=
    (integrable_const (1 : ℝ)).indicator
      (S.measurable_D2ofZ2 (z 1) (MeasurableSet.singleton (d 1)))
  have hd1_d2cf_int :
      Integrable
        (S.d1Var.indicator (d 0) * S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ := by
    have h := S.d1Var.integrable_mul_indicator (d 0) hd2cf_int hd2cf_meas
    exact h.congr (Filter.Eventually.of_forall
      (fun ω => by simp [mul_comm]))
  have hq_d2cf_int :
      Integrable (q * S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ := by
    have h := S.z1Var.integrable_mul_indicator (z 0) hd1_d2cf_int
      ((S.d1Var.measurable_indicator (d 0)).mul hd2cf_meas)
    exact h.congr (Filter.Eventually.of_forall
      (fun ω => by dsimp [q]; ring))
  have hRevPull :
      (fun ω => S.z1Var.indicator (z 0) ω * S.d1Var.indicator (d 0) ω *
        S.historyBundle2.condExpGiven (S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ ω)
        =ᵐ[P.μ]
      S.historyBundle2.condExpGiven
        (q * S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ := by
    have hpull := S.historyBundle2.condExpGiven_mul_of_stronglyMeasurable_left
      hq_sm hq_d2cf_int hd2cf_int
    filter_upwards [hpull] with ω hω
    simpa [q, Pi.mul_apply, mul_assoc] using hω.symm
  haveI : IsFiniteMeasure (P.μ.trim S.historyBundle2.sigma_le) := isFiniteMeasure_trim _
  have hTower :
      S.historyBundle1.condExpGiven
        (S.historyBundle2.condExpGiven
          (q * S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven
        (q * S.d2ofZ2EqIndicator (z 1) (d 1)) P.μ := by
    have h := S.historyBundle2.condExpGiven_tower_of_le
      (g := q * S.d2ofZ2EqIndicator (z 1) (d 1)) (μ := P.μ)
      (m := S.historyBundle1.sigma) hσ12
    simpa [POCFBundle.condExpGiven] using h
  have hCons :
      (q * S.d2ofZ2EqIndicator (z 1) (d 1)) =ᵐ[P.μ]
      (fun ω => (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω *
        S.z1Var.indicator (z 0) ω) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    by_cases hz1 : S.factualZ1 ω = z 0
    · have hiZ1 : S.z1Var.indicator (z 0) ω = 1 :=
        S.z1Var.indicator_apply_eq_one hz1
      have hcD1 := D1ofZ_eq_factualD1_on_z1Event (S := S) As z hz1
      have hcD2 := D2ofZ_eq_D2ofZ2_on_z1Event (S := S) As z hz1
      by_cases hD : S.DofZ z ω = d
      · have hD1 : S.D1ofZ z ω = d 0 := by
          have := congrFun hD 0
          simpa [DofZ] using this
        have hfD1 : S.factualD1 ω = d 0 := by
          simpa [hcD1] using hD1
        have hD2 : S.D2ofZ z ω = d 1 := by
          have := congrFun hD 1
          simpa [DofZ] using this
        have hcfD2 : S.D2ofZ2 (z 1) ω = d 1 := by
          simpa [hcD2] using hD2
        have hiD1 : S.d1Var.indicator (d 0) ω = 1 :=
          S.d1Var.indicator_apply_eq_one hfD1
        have hiD2 : S.d2ofZ2EqIndicator (z 1) (d 1) ω = 1 := by
          unfold d2ofZ2EqIndicator
          exact Set.indicator_of_mem
            (show ω ∈ S.D2ofZ2 (z 1) ⁻¹' ({d 1} : Set Bool) from hcfD2) _
        have hiTarget : (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω = 1 :=
          Set.indicator_of_mem (show ω ∈ S.DofZEq z d from hD) _
        simp [q, hiZ1, hiD1, hiD2, hiTarget]
      · have hiTarget : (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω = 0 :=
          Set.indicator_of_notMem (show ω ∉ S.DofZEq z d from hD) _
        by_cases hfD1 : S.factualD1 ω = d 0
        · have hiD1 : S.d1Var.indicator (d 0) ω = 1 :=
            S.d1Var.indicator_apply_eq_one hfD1
          have hcfD2_ne : S.D2ofZ2 (z 1) ω ≠ d 1 := by
            intro hcfD2
            apply hD
            funext i
            refine Fin.cases ?_ ?_ i
            · simp [DofZ, hcD1, hfD1]
            · intro j
              refine Fin.cases ?_ ?_ j
              · calc
                  S.DofZ z ω (Fin.succ 0) = S.D2ofZ z ω := by rfl
                  _ = S.D2ofZ2 (z 1) ω := hcD2
                  _ = d 1 := hcfD2
                  _ = d (Fin.succ 0) := by rfl
              · intro j0
                exact j0.elim0
          have hiD2 : S.d2ofZ2EqIndicator (z 1) (d 1) ω = 0 := by
            unfold d2ofZ2EqIndicator
            exact Set.indicator_of_notMem
              (show ω ∉ S.D2ofZ2 (z 1) ⁻¹' ({d 1} : Set Bool) from hcfD2_ne) _
          simp [q, hiZ1, hiD1, hiD2, hiTarget]
        · have hiD1 : S.d1Var.indicator (d 0) ω = 0 :=
            S.d1Var.indicator_apply_eq_zero hfD1
          simp [q, hiZ1, hiD1, hiTarget]
    · have hiZ1 : S.z1Var.indicator (z 0) ω = 0 :=
        S.z1Var.indicator_apply_eq_zero hz1
      simp [q, hiZ1]
  have hOuterLhs :
      S.historyBundle1.condExpGiven
        (fun ω => S.innerCondD z d ω * S.z1Var.indicator (z 0) ω) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven
        (fun ω => (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω *
          S.z1Var.indicator (z 0) ω) P.μ := by
    refine (S.historyBundle1.condExpGiven_congr_ae
      (innerCondD_mul_z1_indicator (S := S) As z d)).trans ?_
    refine (S.historyBundle1.condExpGiven_congr_ae hRevPull).trans ?_
    refine hTower.trans ?_
    exact S.historyBundle1.condExpGiven_congr_ae hCons
  have hprod :
      S.historyBundle1.condExpGiven
        (fun ω => S.innerCondD z d ω * S.z1Var.indicator (z 0) ω) P.μ
        =ᵐ[P.μ]
      S.historyBundle1.condExpGiven (S.z1Var.indicator (z 0)) P.μ *
        S.historyBundle1.condExpGiven
          ((S.DofZEq z d).indicator (fun _ => (1 : ℝ))) P.μ := by
    refine hOuterLhs.trans ?_
    filter_upwards [hStage1] with ω hω
    simpa [Pi.mul_apply, mul_comm] using hω
  have hne :
      ∀ᵐ ω ∂P.μ, S.historyBundle1.condExpGiven (S.z1Var.indicator (z 0)) P.μ ω ≠ 0 := by
    filter_upwards [As.overlap1 (z 0)] with ω hpos
    linarith
  have hratio := S.historyBundle1.condExpRatio_eq_of_mul hprod hne
  unfold cObsProb
  exact hratio.symm

/-! ### Unconditional bridges (corollaries via integration) -/

/-- **Outcome bridge** (unconditional): the counterfactual mean of `Y(D(z))`
equals the observable nested regression `obsMean z`.

`E[Y(D(z))] = E[ E[ E[Y | S, D₁, Z = z] | S₀, Z₁ = z₁ ] ]`.

Derived from `cOutcome_bridge` by integrating both sides and using
`∫ B.condExpGiven f dμ = ∫ f dμ`. -/
theorem outcome_bridge (As : S.Assumptions) (z : Fin 2 → Bool) :
    ∫ ω, S.YofDofZ z ω ∂P.μ = S.obsMean z := by
  have hz_pre : Preceq z z := by
    refine ⟨?_, ?_⟩ <;> simp
  calc
    ∫ ω, S.YofDofZ z ω ∂P.μ
        = ∫ ω, S.historyBundle1.condExpGiven (S.YofDofZ z) P.μ ω ∂P.μ := by
          exact (MeasureTheory.integral_condExp S.historyBundle1.sigma_le).symm
    _ = ∫ ω, S.cObsMean z ω ∂P.μ := by
          exact integral_congr_ae (cOutcome_bridge (S := S) As z z hz_pre)
    _ = S.obsMean z := rfl

/-- **Compliance bridge** (unconditional): the counterfactual probability of
the dynamic complier event `{D(z) = d}` equals the observable nested
regression `obsProb z d`.

`P{D(z) = d} = E[ E[ P(D = d | S, D₁, Z = z) | S₀, Z₁ = z₁ ] ]`.

Derived from `cCompliance_bridge` by integrating the indicator. -/
theorem compliance_bridge (As : S.Assumptions) (z d : Fin 2 → Bool)
    (hd : Preceq d z) :
    (P.μ (S.DofZEq z d)).toReal = S.obsProb z d := by
  calc
    (P.μ (S.DofZEq z d)).toReal
        = ∫ ω, (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω ∂P.μ := by
          exact (MeasureTheory.integral_indicator_one (S.measurableSet_DofZEq z d)).symm
    _ = ∫ ω, S.historyBundle1.condExpGiven
          ((S.DofZEq z d).indicator (fun _ => (1 : ℝ))) P.μ ω ∂P.μ := by
          exact (MeasureTheory.integral_condExp S.historyBundle1.sigma_le).symm
    _ = ∫ ω, S.cObsProb z d ω ∂P.μ := by
          exact integral_congr_ae (cCompliance_bridge (S := S) As z d hd)
    _ = S.obsProb z d := rfl

end PODynLATESystem

end PO
end Causalean
