import Causalean.PO.ID.Exact.ATE

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Backdoor ATT identification in the Potential Outcome Framework

ATT identification under backdoor assumptions, parallel to the ATE counterpart
in `PO/ID/Exact/ATE.lean`. The PO-level estimand is
`ATT = E[A · (Y(1) − Y(0))] / π_T`; under unconfoundedness it equals the
observable `adjustedATT = E[A · (μ₁(X) − μ₀(X))] / π_T`, with an AIPW corollary.

This file extends `POBackdoorSystem` (defined in `PO/ID/Exact/ATE.lean`) and reuses
its bundled definitions (`YofD`, `factualD`, `factualY`, `factualX`, `sigmaX`,
`propScore`, `CATE`, `Assumptions`).
-/

/-!
This file identifies the average treatment effect on the treated from observed
data under back-door assumptions, expressing the causal target through
covariate-adjusted treated outcomes and an equivalent augmented
inverse-probability weighted form.

It reuses `POBackdoorSystem` from the ATE file but weakens the overlap
requirement to the control arm. The public API includes `ATTAssumptions`,
`ATT_eq_adjustedATT`, and `adjustedATT_eq_aipwForm`, respectively packaging the
one-sided assumptions, the adjusted ATT identification theorem, and the AIPW
representation.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- Marginal probability of being treated, `π_T = E[1_{D=1}] = P[D=1]`. -/
noncomputable def propTreated : ℝ :=
  ∫ ω, S.dVar.indicator true ω ∂P.μ

/-- ATT (Average Treatment Effect on the Treated):
`ATT = E[A · (Y(1) − Y(0))] / π_T`. -/
noncomputable def ATT : ℝ :=
  (∫ ω, S.dVar.indicator true ω * (S.YofD true ω - S.YofD false ω) ∂P.μ)
    / S.propTreated

/-- Adjusted ATT (observable, control-regression form):
`E[A · (Y − μ₀(X))] / π_T`. Only the CONTROL regression `μ₀(X) = adjustedCE false`
appears — the treated potential outcome is observed directly on `{D = 1}` via
consistency (`A · Y = A · Y(1)`), so no treated regression `μ₁(X)` and hence no
`0 < e(X)` is needed. This is the standard ATT estimand and requires only
one-sided overlap `e(X) < 1`. The AIPW form is recovered as a corollary
(`adjustedATT_eq_aipwForm`). -/
noncomputable def adjustedATT : ℝ :=
  (∫ ω, S.dVar.indicator true ω * (S.factualY ω - S.adjustedCE false ω) ∂P.μ)
    / S.propTreated

/-- Backdoor assumptions for ATT identification. These are the standard ATT
conditions, with overlap required on only **one** side — every covariate stratum
keeps a positive chance of the control arm (`e(X) < 1`) — which is strictly
weaker than the two-sided overlap the ATE needs, because on the treated the
outcome is observed directly.

Fields:
* `consistency` (SUTVA) — on `{D = d}`, `Y = Y(d)`.
* `unconfoundedness` — `D ⟂ (Y(1), Y(0)) | X`.
* `overlapControl` — one-sided overlap `P[D=1 | σ(X)] < 1` a.s.: every covariate
  stratum keeps a positive chance of the CONTROL arm. This is all ATT needs,
  because the treated potential outcome is observed directly on `{D = 1}`
  (`A · Y = A · Y(1)` by consistency), so no `0 < e(X)` is required.
* `integrable_Y1`, `integrable_Y0` — the potential outcomes are integrable.
* `propTreated_pos` — the marginal treatment probability `π_T = P[D=1]` is
  positive, so the ATT (which conditions on the treated) is well-defined (no
  division by zero). -/
structure ATTAssumptions (S : POBackdoorSystem P γ)
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] : Prop where
  /-- Consistency (SUTVA): on `{D = d}`, the observed outcome equals `Y(d)`. -/
  consistency : P.Consistency
  /-- Unconfoundedness: `D ⟂ (Y(1), Y(0)) | X`, as conditional independence of the
  realized `D` and the counterfactual bundle given `σ(X)`. -/
  unconfoundedness :
    P.CondIndepCF (RegimedVar.ofFactual S.dVar) S.cfBundle
      (RegimedVar.ofFactual S.xVar) P.μ
  /-- One-sided overlap (control common support): `P[D=1 | σ(X)] < 1` a.s. Only the
  upper bound is needed for ATT — the treated arm is observed directly. -/
  overlapControl : ∀ᵐ ω ∂P.μ, S.propScore true ω < 1
  /-- Regularity: the treated potential outcome `Y(1)` is integrable. -/
  integrable_Y1 : Integrable (S.YofD true) P.μ
  /-- Regularity: the control potential outcome `Y(0)` is integrable. -/
  integrable_Y0 : Integrable (S.YofD false) P.μ
  /-- Positivity of the marginal treatment probability `π_T = P[D=1]`. -/
  propTreated_pos : 0 < S.propTreated

private lemma propScore_false_ae [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] :
    S.propScore false =ᵐ[P.μ] (fun ω => 1 - S.propScore true ω) := by
  have hindD_integrable : ∀ e : Bool, Integrable (S.dVar.indicator e) P.μ :=
    fun e => S.dVar.integrable_indicator e
  have hsum_ptwise :
      (fun ω => S.dVar.indicator true ω + S.dVar.indicator false ω)
        = (fun _ : P.Ω => (1 : ℝ)) := by
    funext ω
    exact S.dVar.indicator_add_indicator_not ω
  have hsum :
      P.μ[fun ω => S.dVar.indicator true ω + S.dVar.indicator false ω | S.sigmaX]
        =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    rw [hsum_ptwise]
    exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const S.sigmaX_le (1 : ℝ))
  have hadd :
      P.μ[fun ω => S.dVar.indicator true ω + S.dVar.indicator false ω | S.sigmaX]
        =ᵐ[P.μ]
          P.μ[S.dVar.indicator true | S.sigmaX]
            + P.μ[S.dVar.indicator false | S.sigmaX] :=
    MeasureTheory.condExp_add (hindD_integrable true) (hindD_integrable false) S.sigmaX
  filter_upwards [hsum, hadd] with ω h1 h2
  have hsum_ω :
      P.μ[S.dVar.indicator true | S.sigmaX] ω
        + P.μ[S.dVar.indicator false | S.sigmaX] ω = 1 := by
    rw [← Pi.add_apply, ← h2, h1]
  unfold POBackdoorSystem.propScore
  linarith

/-- Under one-sided overlap (`e(X) < 1`), the control propensity score
`P[D=0 | σ(X)] = 1 - e(X)` is a.s. nonzero. -/
lemma ATTAssumptions.propScore_false_ne [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions) : ∀ᵐ ω ∂P.μ, S.propScore false ω ≠ 0 := by
  filter_upwards [S.propScore_false_ae, hA.overlapControl] with ω hf hlt
  rw [hf]
  intro h
  linarith

private lemma stronglyMeasurable_adjustedCE_comap
    (d : Bool) :
    StronglyMeasurable[S.sigmaX] (S.adjustedCE d) := by
  unfold POBackdoorSystem.adjustedCE POBackdoorSystem.propScore
  exact ((MeasureTheory.stronglyMeasurable_condExp
    (μ := P.μ) (m := S.sigmaX)
    (f := fun ω' => S.factualY ω' * S.dVar.indicator d ω')).measurable.div
    (MeasureTheory.stronglyMeasurable_condExp
      (μ := P.μ) (m := S.sigmaX) (f := S.dVar.indicator d)).measurable).stronglyMeasurable

private lemma measurable_adjustedCE
    (d : Bool) : Measurable (S.adjustedCE d) :=
  (S.stronglyMeasurable_adjustedCE_comap d).mono S.sigmaX_le |>.measurable

/-- Control-arm backdoor CATE identification under the one-sided ATT assumptions:
`μ[Y(0) | σ(X)] =ᵐ adjustedCE false`. Discharges the per-arm nonvanishing
hypothesis of `cate_backdoor_of_propScore_ne` from `overlapControl` (`e < 1`),
never using `0 < e`. -/
private lemma cate_backdoor_control [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions) : S.CATE false =ᵐ[P.μ] S.adjustedCE false :=
  S.cate_backdoor_of_propScore_ne hA.consistency hA.unconfoundedness
    hA.integrable_Y1 hA.integrable_Y0 false hA.propScore_false_ne

private lemma integrable_adjustedCE_control [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions) :
    Integrable (S.adjustedCE false) P.μ := by
  have hcate_int : Integrable (S.CATE false) P.μ := by
    unfold POBackdoorSystem.CATE
    exact MeasureTheory.integrable_condExp
  exact hcate_int.congr (S.cate_backdoor_control hA)

private lemma att_numerator_arm [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions) (d : Bool)
    (hcate : S.CATE d =ᵐ[P.μ] S.adjustedCE d)
    (hAdjCE_int : Integrable (S.adjustedCE d) P.μ) :
    ∫ ω, S.dVar.indicator true ω * S.YofD d ω ∂P.μ
      = ∫ ω, S.dVar.indicator true ω * S.adjustedCE d ω ∂P.μ := by
  have hindT_integrable : Integrable (S.dVar.indicator true) P.μ :=
    S.dVar.integrable_indicator true
  have hYofD_integrable : Integrable (S.YofD d) P.μ := by
    cases d
    · exact hA.integrable_Y0
    · exact hA.integrable_Y1
  have hAY_int : Integrable (fun ω => S.dVar.indicator true ω * S.YofD d ω) P.μ := by
    have h := S.dVar.integrable_mul_indicator true hYofD_integrable (S.measurable_YofD d)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
  have hAdj_int : Integrable (S.adjustedCE d) P.μ := hAdjCE_int
  have hAdj_meas : Measurable (S.adjustedCE d) :=
    S.measurable_adjustedCE d
  have hAdjA_int : Integrable (fun ω => S.adjustedCE d ω * S.dVar.indicator true ω) P.μ :=
    S.dVar.integrable_mul_indicator true hAdj_int hAdj_meas
  have hAAdj_int : Integrable (fun ω => S.dVar.indicator true ω * S.adjustedCE d ω) P.μ :=
    hAdjA_int.congr (Filter.Eventually.of_forall (fun ω => by ring))
  let u : Bool → ℝ := ({true} : Set Bool).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u :=
    measurable_const.indicator (MeasurableSet.singleton true)
  have hu_eq : (fun ω => u (S.factualD ω)) = S.dVar.indicator true := by
    funext ω
    unfold POVar.indicator
    by_cases h : S.factualD ω = true
    · have h1 : S.factualD ω ∈ ({true} : Set Bool) := h
      have h2 : ω ∈ S.dVar.event true := h
      rw [show u (S.factualD ω) = (1 : ℝ) from Set.indicator_of_mem h1 _,
        Set.indicator_of_mem h2]
    · have h1 : S.factualD ω ∉ ({true} : Set Bool) := h
      have h2 : ω ∉ S.dVar.event true := h
      rw [show u (S.factualD ω) = (0 : ℝ) from Set.indicator_of_notMem h1 _,
        Set.indicator_of_notMem h2]
  let ψ : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
    fun f => match d with
      | true => f (0 : Fin 2)
      | false => f (1 : Fin 2)
  have hψ_meas : Measurable ψ := by
    cases d with
    | true => exact measurable_pi_apply (0 : Fin 2)
    | false => exact measurable_pi_apply (1 : Fin 2)
  have hYofD_eq : S.YofD d = ψ ∘ S.cfBundle.jointValue := by
    funext ω
    cases d <;> rfl
  have hCI :
      ProbabilityTheory.CondIndepFun S.sigmaX S.sigmaX_le
        S.factualD (S.YofD d) P.μ := by
    have hproj := hA.unconfoundedness.project (ψ := ψ) hψ_meas
    rw [hYofD_eq]
    exact hproj
  have huMul_int :
      Integrable (fun ω => u (S.factualD ω) * S.YofD d ω) P.μ := by
    refine hAY_int.congr ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change S.dVar.indicator true ω * S.YofD d ω = u (S.factualD ω) * S.YofD d ω
    rw [← congr_fun hu_eq ω]
  have hfact :
      P.μ[fun ω => S.dVar.indicator true ω * S.YofD d ω | S.sigmaX]
        =ᵐ[P.μ] S.propScore true * S.CATE d := by
    have hraw :=
      condExp_mul_of_condIndep (μ := P.μ) (m := S.sigmaX) S.sigmaX_le
        (f := S.factualD) (g := S.YofD d)
        S.measurable_factualD (S.measurable_YofD d) hCI
        (u := u) (v := id) hu_meas measurable_id
        (by rw [hu_eq]; exact hindT_integrable)
        hYofD_integrable huMul_int
    unfold POBackdoorSystem.CATE POBackdoorSystem.propScore
    rw [hu_eq] at hraw
    exact hraw
  have hfact_adj :
      P.μ[fun ω => S.dVar.indicator true ω * S.YofD d ω | S.sigmaX]
        =ᵐ[P.μ] S.propScore true * S.adjustedCE d := by
    refine hfact.trans ?_
    filter_upwards [hcate] with ω hω
    rw [Pi.mul_apply, Pi.mul_apply, hω]
  have hpull :
      P.μ[fun ω => S.adjustedCE d ω * S.dVar.indicator true ω | S.sigmaX]
        =ᵐ[P.μ] S.adjustedCE d * S.propScore true := by
    have h :=
      S.xVar.condExpGiven_mul_of_stronglyMeasurable_left
        (S.stronglyMeasurable_adjustedCE_comap d) hAdjA_int hindT_integrable
    simpa [POVar.condExpGiven, POBackdoorSystem.propScore,
      POBackdoorSystem.sigmaX, POBackdoorSystem.factualX] using h
  have hpull_comm :
      P.μ[fun ω => S.dVar.indicator true ω * S.adjustedCE d ω | S.sigmaX]
        =ᵐ[P.μ] S.propScore true * S.adjustedCE d := by
    have hce_congr :
        P.μ[fun ω => S.dVar.indicator true ω * S.adjustedCE d ω | S.sigmaX]
          =ᵐ[P.μ]
        P.μ[fun ω => S.adjustedCE d ω * S.dVar.indicator true ω | S.sigmaX] := by
      apply MeasureTheory.condExp_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by ring)
    refine hce_congr.trans ?_
    refine hpull.trans ?_
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Pi.mul_apply, Pi.mul_apply]
      ring)
  calc
    ∫ ω, S.dVar.indicator true ω * S.YofD d ω ∂P.μ
        = ∫ ω, P.μ[fun ω => S.dVar.indicator true ω * S.YofD d ω | S.sigmaX] ω ∂P.μ := by
          exact (MeasureTheory.integral_condExp S.sigmaX_le).symm
    _ = ∫ ω, S.propScore true ω * S.adjustedCE d ω ∂P.μ :=
          MeasureTheory.integral_congr_ae hfact_adj
    _ = ∫ ω, P.μ[fun ω => S.dVar.indicator true ω * S.adjustedCE d ω | S.sigmaX] ω ∂P.μ := by
          exact (MeasureTheory.integral_congr_ae hpull_comm).symm
    _ = ∫ ω, S.dVar.indicator true ω * S.adjustedCE d ω ∂P.μ := by
          exact MeasureTheory.integral_condExp S.sigmaX_le

private lemma condExp_indicator_residual_adjusted_zero
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions) (d : Bool)
    (hcate : S.CATE d =ᵐ[P.μ] S.adjustedCE d)
    (hAdjCE_int : Integrable (S.adjustedCE d) P.μ)
    (h_ne : ∀ᵐ ω ∂P.μ, S.propScore d ω ≠ 0) :
    P.μ[fun ω => S.dVar.indicator d ω * (S.factualY ω - S.adjustedCE d ω) | S.sigmaX]
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  have hYind_int : Integrable
      (fun ω => S.factualY ω * S.dVar.indicator d ω) P.μ :=
    S.dVar.integrable_mul_indicator d
      (S.integrable_factualY_of_consistency
        hA.consistency hA.integrable_Y1 hA.integrable_Y0)
      S.measurable_factualY
  have hAdj_int : Integrable (S.adjustedCE d) P.μ := hAdjCE_int
  have hAdj_meas : Measurable (S.adjustedCE d) :=
    S.measurable_adjustedCE d
  have hAdjind_int : Integrable
      (fun ω => S.adjustedCE d ω * S.dVar.indicator d ω) P.μ :=
    S.dVar.integrable_mul_indicator d hAdj_int hAdj_meas
  have hres_eq :
      (fun ω => S.dVar.indicator d ω * (S.factualY ω - S.adjustedCE d ω))
        = (fun ω => S.factualY ω * S.dVar.indicator d ω
            - S.adjustedCE d ω * S.dVar.indicator d ω) := by
    funext ω
    ring
  have hsub :
      P.μ[fun ω => S.factualY ω * S.dVar.indicator d ω
            - S.adjustedCE d ω * S.dVar.indicator d ω | S.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.factualY ω * S.dVar.indicator d ω | S.sigmaX]
            - P.μ[fun ω => S.adjustedCE d ω * S.dVar.indicator d ω | S.sigmaX] :=
    MeasureTheory.condExp_sub hYind_int hAdjind_int S.sigmaX
  have hYce :
      P.μ[fun ω => S.factualY ω * S.dVar.indicator d ω | S.sigmaX]
        =ᵐ[P.μ] S.propScore d * S.CATE d := by
    filter_upwards [hcate, h_ne] with ω hcat hneω
    unfold POBackdoorSystem.adjustedCE at hcat
    rw [Pi.mul_apply, hcat]
    field_simp [hneω]
  have hpull :
      P.μ[fun ω => S.adjustedCE d ω * S.dVar.indicator d ω | S.sigmaX]
        =ᵐ[P.μ] S.adjustedCE d * S.propScore d := by
    have hind_int : Integrable (S.dVar.indicator d) P.μ :=
      S.dVar.integrable_indicator d
    have h :=
      S.xVar.condExpGiven_mul_of_stronglyMeasurable_left
        (S.stronglyMeasurable_adjustedCE_comap d) hAdjind_int hind_int
    simpa [POVar.condExpGiven, POBackdoorSystem.propScore,
      POBackdoorSystem.sigmaX, POBackdoorSystem.factualX] using h
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hYce, hpull, hcate] with ω hy hp hcat
  rw [Pi.sub_apply, hy, hp, Pi.mul_apply, Pi.mul_apply, hcat]
  ring

private lemma weighted_false_residual_integral_zero
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions)
    (w : P.Ω → ℝ) (hw_sm : StronglyMeasurable[S.sigmaX] w)
    (h_int : Integrable
      (fun ω => w ω *
        (S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω))) P.μ) :
    ∫ ω, w ω *
        (S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω)) ∂P.μ = 0 := by
  have hYind_int : Integrable
      (fun ω => S.factualY ω * S.dVar.indicator false ω) P.μ :=
    S.dVar.integrable_mul_indicator false
      (S.integrable_factualY_of_consistency
        hA.consistency hA.integrable_Y1 hA.integrable_Y0)
      S.measurable_factualY
  have hAdjind_int : Integrable
      (fun ω => S.adjustedCE false ω * S.dVar.indicator false ω) P.μ :=
    S.dVar.integrable_mul_indicator false (S.integrable_adjustedCE_control hA)
      (S.measurable_adjustedCE false)
  have hresid_int : Integrable
      (fun ω => S.dVar.indicator false ω *
        (S.factualY ω - S.adjustedCE false ω)) P.μ := by
    have hYind_int' : Integrable
        (fun ω => S.dVar.indicator false ω * S.factualY ω) P.μ :=
      hYind_int.congr (Filter.Eventually.of_forall (fun ω => by ring))
    have hAdjind_int' : Integrable
        (fun ω => S.dVar.indicator false ω * S.adjustedCE false ω) P.μ :=
      hAdjind_int.congr (Filter.Eventually.of_forall (fun ω => by ring))
    exact (hYind_int'.sub hAdjind_int').congr
      (Filter.Eventually.of_forall (fun ω => by
        change S.dVar.indicator false ω * S.factualY ω
            - S.dVar.indicator false ω * S.adjustedCE false ω
          = S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω)
        ring))
  have hpull :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.sigmaX) hw_sm h_int hresid_int
  have hresid_zero := S.condExp_indicator_residual_adjusted_zero hA false
    (S.cate_backdoor_control hA) (S.integrable_adjustedCE_control hA)
    hA.propScore_false_ne
  have hweighted_zero :
      P.μ[fun ω => w ω *
          (S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω)) | S.sigmaX]
        =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    refine hpull.trans ?_
    filter_upwards [hresid_zero] with ω hω
    rw [Pi.mul_apply, hω, mul_zero]
  calc
    ∫ ω, w ω *
        (S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω)) ∂P.μ
        = ∫ ω, P.μ[fun ω => w ω *
            (S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω)) |
            S.sigmaX] ω ∂P.μ := by
          exact (MeasureTheory.integral_condExp S.sigmaX_le).symm
    _ = ∫ _, (0 : ℝ) ∂P.μ :=
          MeasureTheory.integral_congr_ae hweighted_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-- **ATT identification (one-sided overlap).** Under consistency,
unconfoundedness, one-sided overlap (`e(X) < 1`, the control arm), and positivity
of the marginal treatment probability, the PO-level `ATT` equals the observable
`adjustedATT`:

    E[A · (Y(1) − Y(0))] / π_T  =  E[A · (Y − μ₀(X))] / π_T.

Only the control regression `μ₀(X)` appears, so `0 < e(X)` is NOT required:
* `congr 1` on the positive `propTreated` divisor reduces to equality of
  numerators ∫ A·(Y(1) − Y(0)) dμ = ∫ A·(Y − μ₀(X)) dμ.
* On the treated set `Y = Y(1)` (consistency), so ∫ A·Y(1) = ∫ A·Y with NO
  overlap used.
* For the control term, unconfoundedness + the control-arm CATE identity
  (`cate_backdoor_control`, needing only `e(X) < 1`) give ∫ A·Y(0) = ∫ A·μ₀(X).
* Subtraction gives numerator equality; division by `propTreated > 0` finishes. -/
theorem ATT_eq_adjustedATT [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions) : S.ATT = S.adjustedATT := by
  unfold POBackdoorSystem.ATT POBackdoorSystem.adjustedATT
  congr 1
  have hfalse := S.att_numerator_arm hA false
    (S.cate_backdoor_control hA) (S.integrable_adjustedCE_control hA)
  have hY1 : Integrable (fun ω => S.dVar.indicator true ω * S.YofD true ω) P.μ := by
    have h := S.dVar.integrable_mul_indicator true hA.integrable_Y1 (S.measurable_YofD true)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
  have hY0 : Integrable (fun ω => S.dVar.indicator true ω * S.YofD false ω) P.μ := by
    have h := S.dVar.integrable_mul_indicator true hA.integrable_Y0 (S.measurable_YofD false)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
  have hAfact : Integrable (fun ω => S.dVar.indicator true ω * S.factualY ω) P.μ := by
    have h := S.dVar.integrable_mul_indicator true
      (S.integrable_factualY_of_consistency
        hA.consistency hA.integrable_Y1 hA.integrable_Y0)
      S.measurable_factualY
    exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
  have hAdj0 : Integrable (fun ω => S.dVar.indicator true ω * S.adjustedCE false ω) P.μ := by
    have h := S.dVar.integrable_mul_indicator true (S.integrable_adjustedCE_control hA)
      (S.measurable_adjustedCE false)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
  -- On the treated set, consistency gives `A · Y = A · Y(1)`.
  have hcons :
      (fun ω => S.dVar.indicator true ω * S.factualY ω)
        = (fun ω => S.dVar.indicator true ω * S.YofD true ω) := by
    have hfm :=
      POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
        hA.consistency S.yVar S.dVar true (Ne.symm S.hDY)
    funext ω
    have hω := congr_fun hfm ω
    change S.dVar.indicator true ω * S.factualY ω
      = S.dVar.indicator true ω * S.YofD true ω
    rw [mul_comm (S.dVar.indicator true ω) (S.factualY ω),
      mul_comm (S.dVar.indicator true ω) (S.YofD true ω)]
    exact hω
  calc
    ∫ ω, S.dVar.indicator true ω * (S.YofD true ω - S.YofD false ω) ∂P.μ
        = ∫ ω, (S.dVar.indicator true ω * S.YofD true ω)
            - (S.dVar.indicator true ω * S.YofD false ω) ∂P.μ := by
          congr with ω
          ring
    _ = (∫ ω, S.dVar.indicator true ω * S.YofD true ω ∂P.μ)
          - (∫ ω, S.dVar.indicator true ω * S.YofD false ω ∂P.μ) := by
          exact MeasureTheory.integral_sub hY1 hY0
    _ = (∫ ω, S.dVar.indicator true ω * S.factualY ω ∂P.μ)
          - (∫ ω, S.dVar.indicator true ω * S.adjustedCE false ω ∂P.μ) := by
          rw [← MeasureTheory.integral_congr_ae (Filter.EventuallyEq.of_eq hcons), hfalse]
    _ = ∫ ω, (S.dVar.indicator true ω * S.factualY ω)
          - (S.dVar.indicator true ω * S.adjustedCE false ω) ∂P.μ := by
          exact (MeasureTheory.integral_sub hAfact hAdj0).symm
    _ = ∫ ω, S.dVar.indicator true ω *
          (S.factualY ω - S.adjustedCE false ω) ∂P.μ := by
          congr with ω
          ring

/-- **AIPW corollary.** The `adjustedATT` equals the AIPW-form functional

    ( ∫ A · (Y − μ₀(X))
        − (1 − A) · (e(X) / (1 − e(X))) · (Y − μ₀(X))  dμ ) / π_T,

written here at the PO level using the σ(X)-measurable representatives
`adjustedCE false` (for `μ₀(X)`) and `propScore true` (for `e(X)`). The one-sided
overlap `e(X) < 1` (`ATTAssumptions.overlapControl`) ensures the IPW correction is
a.s. well-defined. The theorem carries the explicit integrability hypothesis on
the observed IPW correction because bare `e(X) < 1` does not uniformly bound
`e(X) / (1 - e(X))`.

Proof structure:
* The IPW-correction term has zero conditional expectation given σ(X) under
  unconfoundedness:
    μ[(1−A) · (e/(1−e)) · (Y − adjCE false) | σ(X)] =ᵐ 0,
  via `weighted_false_residual_integral_zero` (control arm, one-sided overlap).
* Therefore the IPW term integrates to 0, and the remaining term
  ∫ A · (Y − adjCE false) dμ is exactly the numerator of `adjustedATT`.
* Divide both sides by `propTreated`. -/
theorem adjustedATT_eq_aipwForm [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.ATTAssumptions)
    (hIPW : Integrable (fun ω =>
      (1 - S.dVar.indicator true ω)
        * (S.propScore true ω / (1 - S.propScore true ω))
        * (S.factualY ω - S.adjustedCE false ω)) P.μ) :
    S.adjustedATT
      = ((∫ ω,
            S.dVar.indicator true ω * (S.factualY ω - S.adjustedCE false ω)
              - (1 - S.dVar.indicator true ω)
                  * (S.propScore true ω / (1 - S.propScore true ω))
                  * (S.factualY ω - S.adjustedCE false ω)
            ∂P.μ))
          / S.propTreated := by
  let W : P.Ω → ℝ := fun ω => S.propScore true ω / (1 - S.propScore true ω)
  let R : P.Ω → ℝ := fun ω => S.factualY ω - S.adjustedCE false ω
  have hW_sm : StronglyMeasurable[S.sigmaX] W := by
    unfold W POBackdoorSystem.propScore
    exact ((MeasureTheory.stronglyMeasurable_condExp
      (μ := P.μ) (m := S.sigmaX) (f := S.dVar.indicator true)).measurable.div
      (measurable_const.sub
        (MeasureTheory.stronglyMeasurable_condExp
          (μ := P.μ) (m := S.sigmaX) (f := S.dVar.indicator true)).measurable)).stronglyMeasurable
  have hfalse_indicator : ∀ ω, 1 - S.dVar.indicator true ω = S.dVar.indicator false ω := by
    intro ω
    have hsum := S.dVar.indicator_add_indicator_not ω
    linarith
  have hIPW_weighted : Integrable
      (fun ω => W ω * (S.dVar.indicator false ω * R ω)) P.μ := by
    refine hIPW.congr ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    unfold W R
    change (1 - S.dVar.indicator true ω)
        * (S.propScore true ω / (1 - S.propScore true ω))
        * (S.factualY ω - S.adjustedCE false ω)
      = S.propScore true ω / (1 - S.propScore true ω)
        * (S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω))
    rw [hfalse_indicator ω]
    ring
  have hIPW_zero :
      ∫ ω, (1 - S.dVar.indicator true ω)
          * (S.propScore true ω / (1 - S.propScore true ω))
          * (S.factualY ω - S.adjustedCE false ω) ∂P.μ = 0 := by
    have hweighted_zero :=
      S.weighted_false_residual_integral_zero hA W hW_sm hIPW_weighted
    calc
      ∫ ω, (1 - S.dVar.indicator true ω)
          * (S.propScore true ω / (1 - S.propScore true ω))
          * (S.factualY ω - S.adjustedCE false ω) ∂P.μ
          = ∫ ω, W ω * (S.dVar.indicator false ω * R ω) ∂P.μ := by
            apply MeasureTheory.integral_congr_ae
            refine Filter.Eventually.of_forall (fun ω => ?_)
            unfold W R
            change (1 - S.dVar.indicator true ω)
                * (S.propScore true ω / (1 - S.propScore true ω))
                * (S.factualY ω - S.adjustedCE false ω)
              = S.propScore true ω / (1 - S.propScore true ω)
                * (S.dVar.indicator false ω * (S.factualY ω - S.adjustedCE false ω))
            rw [hfalse_indicator ω]
            ring
      _ = 0 := hweighted_zero
  have htreated_int :
      Integrable (fun ω => S.dVar.indicator true ω *
        (S.factualY ω - S.adjustedCE false ω)) P.μ := by
    have hYind_int : Integrable (fun ω => S.dVar.indicator true ω * S.factualY ω) P.μ := by
      have h := S.dVar.integrable_mul_indicator true
        (S.integrable_factualY_of_consistency
          hA.consistency hA.integrable_Y1 hA.integrable_Y0)
        S.measurable_factualY
      exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
    have hAdjind_int : Integrable
        (fun ω => S.dVar.indicator true ω * S.adjustedCE false ω) P.μ := by
      have h :=
        S.dVar.integrable_mul_indicator true
          (S.integrable_adjustedCE_control hA)
          (S.measurable_adjustedCE false)
      exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
    exact (hYind_int.sub hAdjind_int).congr
      (Filter.Eventually.of_forall (fun ω => by
        change S.dVar.indicator true ω * S.factualY ω
            - S.dVar.indicator true ω * S.adjustedCE false ω
          = S.dVar.indicator true ω * (S.factualY ω - S.adjustedCE false ω)
        ring))
  have hnumer :
      ∫ ω,
          S.dVar.indicator true ω * (S.factualY ω - S.adjustedCE false ω)
            - (1 - S.dVar.indicator true ω)
                * (S.propScore true ω / (1 - S.propScore true ω))
                * (S.factualY ω - S.adjustedCE false ω) ∂P.μ
        = ∫ ω, S.dVar.indicator true ω *
            (S.factualY ω - S.adjustedCE false ω) ∂P.μ := by
    calc
      ∫ ω,
          S.dVar.indicator true ω * (S.factualY ω - S.adjustedCE false ω)
            - (1 - S.dVar.indicator true ω)
                * (S.propScore true ω / (1 - S.propScore true ω))
                * (S.factualY ω - S.adjustedCE false ω) ∂P.μ
          = (∫ ω, S.dVar.indicator true ω *
              (S.factualY ω - S.adjustedCE false ω) ∂P.μ)
            - ∫ ω, (1 - S.dVar.indicator true ω)
                * (S.propScore true ω / (1 - S.propScore true ω))
                * (S.factualY ω - S.adjustedCE false ω) ∂P.μ := by
            exact MeasureTheory.integral_sub htreated_int hIPW
      _ = ∫ ω, S.dVar.indicator true ω *
            (S.factualY ω - S.adjustedCE false ω) ∂P.μ := by
            rw [hIPW_zero, sub_zero]
  unfold POBackdoorSystem.adjustedATT
  congr 1
  exact hnumer.symm

end POBackdoorSystem

end PO
end Causalean
