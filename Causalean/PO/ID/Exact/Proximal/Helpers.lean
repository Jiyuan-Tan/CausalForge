/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal ATE — auxiliary conditional-expectation helpers

Auxiliary lemmas for the proximal ATE proof (`Main.lean`).  Each lemma
corresponds to one "drop conditioning" manipulation step in the proof outline
of def:po-proximal-ate (Basic Concepts.tex §2555–2622):

1. `condExp_drop_Z`         — Y ⟂ Z | (A,U,X) ⇒ E[Y | σ(A,Z,U,X)] =ᵐ E[Y | σ(A,U,X)].
2. `condExp_h_drop_Z`       — W ⟂ (A,Z) | (U,X) ⇒ E[h(a,W,X) | σ(A,Z,U,X)] =ᵐ E[h(a,W,X) | σ(A,U,X)].
3. `condExp_h_drop_A`       — W ⟂ A | (U,X) ⇒ E[h(a,W,X) | σ(A,U,X)] =ᵐ E[h(a,W,X) | σ(U,X)].
4. `latent_exch_to_condExp` — Y(a) ⟂ A | (U,X) ⇒ E[Y(a) | σ(A,U,X)] =ᵐ E[Y(a) | σ(U,X)].
5. `consistency_event`      — on {A=a}, Y =ᵐ Y(a), so E[Y|σ(A,U,X)] =ᵐ E[Y(a)|σ(A,U,X)].

Each lemma comes in two forms: a *primed* form that takes individual field
hypotheses (reusable from sibling partial-identification modules with
different assumption bundles), and a *bundled* form that takes the full
`POProximalSystem.Assumptions` (used by `Main.lean`).
-/

import Causalean.PO.ID.Exact.Proximal.Assumptions
import Causalean.Mathlib.CondIndep

/-! # Conditional-expectation helpers for proximal ATE

This file supplies the conditional-expectation reductions used by the proximal
ATE theorem: dropping proxy or treatment coordinates under conditional
independence, transporting consistency through event restrictions, and exposing
both field-level and bundled forms for reuse by exact and partial proximal
identification modules.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POProximalSystem

variable {P : POSystem}
  {γ_X γ_Z γ_W γ_U : Type*}
  [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
  [MeasurableSpace γ_W] [MeasurableSpace γ_U]
  {S : POProximalSystem P γ_X γ_Z γ_W γ_U}
  {μ : Measure P.Ω} [IsFiniteMeasure μ] [StandardBorelSpace P.Ω]

/-! ### Lemma 1: drop Z from E[Y | σ(A,Z,U,X)] -/

/-- Field-level form: from `proxy_YZ : Y ⟂ Z | (A,U,X)` and integrability of `Y`,
`E[Y | σ(A,Z,U,X)] =ᵐ[μ] E[Y | σ(A,U,X)]`. -/
lemma condExp_drop_Z'
    (proxy_YZ : CondIndepFun S.σ_AUX S.σ_AUX_le S.Y S.Z μ)
    (hYInt : Integrable S.Y μ) :
    μ[S.Y | S.σ_AZUX] =ᵐ[μ] μ[S.Y | S.σ_AUX] := by
  -- Show σ_AZUX = σ_AUX ⊔ comap S.Z.
  have hσ_eq : S.σ_AZUX = S.σ_AUX ⊔ MeasurableSpace.comap S.Z inferInstance := by
    change MeasurableSpace.comap (fun ω => (S.A ω, S.Z ω, S.U ω, S.X ω)) _ = _
    rw [show (inferInstance : MeasurableSpace (Bool × γ_Z × γ_U × γ_X))
          = (inferInstance : MeasurableSpace Bool).prod inferInstance from rfl,
        MeasurableSpace.comap_prodMk,
        show (inferInstance : MeasurableSpace (γ_Z × γ_U × γ_X))
          = (inferInstance : MeasurableSpace γ_Z).prod inferInstance from rfl,
        MeasurableSpace.comap_prodMk]
    have hAUX : S.σ_AUX = MeasurableSpace.comap S.A inferInstance
        ⊔ MeasurableSpace.comap (fun ω => (S.U ω, S.X ω)) inferInstance := by
      change MeasurableSpace.comap (fun ω => (S.A ω, S.U ω, S.X ω)) _ = _
      rw [show (inferInstance : MeasurableSpace (Bool × γ_U × γ_X))
            = (inferInstance : MeasurableSpace Bool).prod inferInstance from rfl,
          MeasurableSpace.comap_prodMk]
    rw [hAUX]
    ac_rfl
  rw [hσ_eq]
  exact condExp_sup_comap_eq_of_condIndep
    (m := S.σ_AUX) S.σ_AUX_le S.measurable_Z S.measurable_Y proxy_YZ
    (h := id) measurable_id (by simpa using hYInt)

/-- From `proxy_YZ : Y ⟂ Z | (A,U,X)`, conclude
`E[Y | σ(A,Z,U,X)] =ᵐ[μ] E[Y | σ(A,U,X)]`.

Key idea: `σ(A,Z,U,X) = σ(A,U,X) ⊔ σ(Z)` and Y ⟂ Z | (A,U,X), so the extra
conditioning on Z is irrelevant.  Needs `condExp_sup_comap_eq_of_condIndep`. -/
lemma condExp_drop_Z (HA : Assumptions S μ) (hAY : S.Avar.v ≠ S.Yvar.v) :
    μ[S.Y | S.σ_AZUX] =ᵐ[μ] μ[S.Y | S.σ_AUX] :=
  condExp_drop_Z' HA.proxy_YZ (HA.integrable_Y hAY)

/-! ### Lemma 2: drop Z from E[h(a,W,X) | σ(A,Z,U,X)] -/

/-- Field-level form: from `proxy_WAZ : W ⟂ (A,Z) | (U,X)`, measurability and
arm-integrability of the bridge `h`, conclude
`E[h(a,W,X) | σ(A,Z,U,X)] =ᵐ[μ] E[h(a,W,X) | σ(A,U,X)]`. -/
lemma condExp_h_drop_Z' {h_fun : Bool × γ_W × γ_X → ℝ}
    (proxy_WAZ : CondIndepFun S.σ_UX S.σ_UX_le S.W (fun ω => (S.A ω, S.Z ω)) μ)
    (measurable_h : Measurable h_fun)
    (a : Bool) (h_int : Integrable (fun ω => h_fun (a, S.W ω, S.X ω)) μ) :
    μ[fun ω => h_fun (a, S.W ω, S.X ω) | S.σ_AZUX]
      =ᵐ[μ] μ[fun ω => h_fun (a, S.W ω, S.X ω) | S.σ_AUX] := by
  -- σ-algebra: σ_AZUX = σ_AUX ⊔ comap Z.
  have hσ_eq : S.σ_AZUX = S.σ_AUX ⊔ MeasurableSpace.comap S.Z inferInstance := by
    change MeasurableSpace.comap (fun ω => (S.A ω, S.Z ω, S.U ω, S.X ω)) _ = _
    rw [show (inferInstance : MeasurableSpace (Bool × γ_Z × γ_U × γ_X))
          = (inferInstance : MeasurableSpace Bool).prod inferInstance from rfl,
        MeasurableSpace.comap_prodMk,
        show (inferInstance : MeasurableSpace (γ_Z × γ_U × γ_X))
          = (inferInstance : MeasurableSpace γ_Z).prod inferInstance from rfl,
        MeasurableSpace.comap_prodMk]
    have hAUX : S.σ_AUX = MeasurableSpace.comap S.A inferInstance
        ⊔ MeasurableSpace.comap (fun ω => (S.U ω, S.X ω)) inferInstance := by
      change MeasurableSpace.comap (fun ω => (S.A ω, S.U ω, S.X ω)) _ = _
      rw [show (inferInstance : MeasurableSpace (Bool × γ_U × γ_X))
            = (inferInstance : MeasurableSpace Bool).prod inferInstance from rfl,
          MeasurableSpace.comap_prodMk]
    rw [hAUX]
    ac_rfl
  -- Weak union: W ⟂ (A,Z) | σ_UX  ⇒  W ⟂ Z | σ_UX ⊔ comap A = σ_AUX.
  have hWZA : CondIndepFun S.σ_UX S.σ_UX_le S.W (fun ω => (S.Z ω, S.A ω)) μ := by
    have h := proxy_WAZ.comp (φ := id)
      (ψ := fun (p : Bool × γ_Z) => (p.2, p.1))
      measurable_id (by fun_prop)
    simpa [Function.comp] using h
  have hWZ_AUX : CondIndepFun
      (S.σ_UX ⊔ MeasurableSpace.comap S.A inferInstance)
      (sup_le S.σ_UX_le S.measurable_A.comap_le)
      S.W S.Z μ :=
    Causalean.condIndepFun_weak_union_of_prodMk S.σ_UX_le S.measurable_W
      S.measurable_Z S.measurable_A hWZA
  -- σ_AUX = σ_UX ⊔ comap A.
  have hσ_AUX : S.σ_AUX = S.σ_UX ⊔ MeasurableSpace.comap S.A inferInstance := by
    change MeasurableSpace.comap (fun ω => (S.A ω, S.U ω, S.X ω)) _ = _
    rw [show (inferInstance : MeasurableSpace (Bool × γ_U × γ_X))
          = (inferInstance : MeasurableSpace Bool).prod inferInstance from rfl,
        MeasurableSpace.comap_prodMk]
    exact sup_comm _ _
  -- Cast hWZ_AUX to use σ_AUX.
  have hWZ_AUX' : CondIndepFun S.σ_AUX S.σ_AUX_le S.W S.Z μ := by
    convert hWZ_AUX
  -- X is σ_AUX-measurable.
  have hX_m : Measurable[S.σ_AUX] S.X := by
    change Measurable[MeasurableSpace.comap S.AUX inferInstance] S.X
    intro s hs
    refine ⟨(fun p : Bool × γ_U × γ_X => p.2.2) ⁻¹' s, ?_, rfl⟩
    exact (measurable_snd.comp measurable_snd) hs
  -- Lift to (W, X) ⟂ Z | σ_AUX.
  have hWX_Z : CondIndepFun S.σ_AUX S.σ_AUX_le (fun ω => (S.W ω, S.X ω)) S.Z μ :=
    Causalean.condIndepFun_prodMk_of_measurable_left S.σ_AUX_le S.measurable_W S.measurable_Z
      S.measurable_X hX_m hWZ_AUX'
  let h_comb : γ_W × γ_X → ℝ := fun p => h_fun (a, p.1, p.2)
  have h_comb_meas : Measurable h_comb := by
    have : Measurable (fun p : γ_W × γ_X => (a, p.1, p.2)) := by fun_prop
    exact measurable_h.comp this
  rw [hσ_eq]
  exact condExp_sup_comap_eq_of_condIndep
    (m := S.σ_AUX) S.σ_AUX_le S.measurable_Z
    (Measurable.prodMk S.measurable_W S.measurable_X) hWX_Z h_comb_meas h_int

/-- From `proxy_WAZ : W ⟂ (A,Z) | (U,X)`, for any `a : Bool`,
`E[h(a,W,X) | σ(A,Z,U,X)] =ᵐ[μ] E[h(a,W,X) | σ(A,U,X)]`. -/
lemma condExp_h_drop_Z (HA : Assumptions S μ) (a : Bool) :
    μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AZUX]
      =ᵐ[μ] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] := by
  have h_int : Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ := by
    cases a
    · exact HA.integrable_h0WX
    · exact HA.integrable_h1WX
  exact condExp_h_drop_Z' HA.proxy_WAZ HA.measurable_h a h_int

/-! ### Lemma 3: drop A from E[h(a,W,X) | σ(A,U,X)] -/

/-- Field-level form: from `proxy_WA : W ⟂ A | (U,X)`, measurability and
arm-integrability of the bridge `h`, conclude
`E[h(a,W,X) | σ(A,U,X)] =ᵐ[μ] E[h(a,W,X) | σ(U,X)]`. -/
lemma condExp_h_drop_A' {h_fun : Bool × γ_W × γ_X → ℝ}
    (proxy_WA : CondIndepFun S.σ_UX S.σ_UX_le S.W S.A μ)
    (measurable_h : Measurable h_fun)
    (a : Bool) (h_int : Integrable (fun ω => h_fun (a, S.W ω, S.X ω)) μ) :
    μ[fun ω => h_fun (a, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ] μ[fun ω => h_fun (a, S.W ω, S.X ω) | S.σ_UX] := by
  -- σ-algebra: σ_AUX = σ_UX ⊔ comap A.
  have hσ_eq : S.σ_AUX = S.σ_UX ⊔ MeasurableSpace.comap S.A inferInstance := by
    change MeasurableSpace.comap (fun ω => (S.A ω, S.U ω, S.X ω)) _ = _
    rw [show (inferInstance : MeasurableSpace (Bool × γ_U × γ_X))
          = (inferInstance : MeasurableSpace Bool).prod inferInstance from rfl,
        MeasurableSpace.comap_prodMk]
    exact sup_comm _ _
  -- X is σ_UX-measurable.
  have hX_m : Measurable[S.σ_UX] S.X := by
    change Measurable[MeasurableSpace.comap S.UX inferInstance] S.X
    intro s hs
    exact ⟨Prod.snd ⁻¹' s, measurable_snd hs, rfl⟩
  -- Lift to (W, X) ⟂ A | σ_UX.
  have hWX_A : CondIndepFun S.σ_UX S.σ_UX_le (fun ω => (S.W ω, S.X ω)) S.A μ :=
    Causalean.condIndepFun_prodMk_of_measurable_left S.σ_UX_le S.measurable_W S.measurable_A
      S.measurable_X hX_m proxy_WA
  let h_comb : γ_W × γ_X → ℝ := fun p => h_fun (a, p.1, p.2)
  have h_comb_meas : Measurable h_comb := by
    have : Measurable (fun p : γ_W × γ_X => (a, p.1, p.2)) := by fun_prop
    exact measurable_h.comp this
  rw [hσ_eq]
  exact condExp_sup_comap_eq_of_condIndep
    (m := S.σ_UX) S.σ_UX_le S.measurable_A
    (Measurable.prodMk S.measurable_W S.measurable_X) hWX_A h_comb_meas h_int

/-- From `proxy_WAZ : W ⟂ (A,Z) | (U,X)`, projecting to `W ⟂ A | (U,X)`,
`E[h(a,W,X) | σ(A,U,X)] =ᵐ[μ] E[h(a,W,X) | σ(U,X)]`. -/
lemma condExp_h_drop_A (HA : Assumptions S μ) (a : Bool) :
    μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] := by
  -- Project proxy_WAZ to W ⟂ A | σ_UX via .comp with Prod.fst.
  have hWA : CondIndepFun S.σ_UX S.σ_UX_le S.W S.A μ := by
    have h := HA.proxy_WAZ.comp (φ := id) (ψ := Prod.fst) measurable_id measurable_fst
    simpa [Function.comp] using h
  have h_int : Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ := by
    cases a
    · exact HA.integrable_h0WX
    · exact HA.integrable_h1WX
  exact condExp_h_drop_A' hWA HA.measurable_h a h_int

/-! ### Lemma 4: drop A from E[Y(a) | σ(A,U,X)] -/

/-- Field-level form: from `latent_exch a : Y(a) ⟂ A | (U,X)` and integrability
of `Y(a)`, conclude `E[Y(a) | σ(A,U,X)] =ᵐ[μ] E[Y(a) | σ(U,X)]`. -/
lemma latent_exch_to_condExp' (a : Bool)
    (latent_exch : CondIndepFun S.σ_UX S.σ_UX_le (S.YofA a) S.A μ)
    (hYaInt : Integrable (S.YofA a) μ) :
    μ[S.YofA a | S.σ_AUX] =ᵐ[μ] μ[S.YofA a | S.σ_UX] := by
  -- Show σ_AUX = σ_UX ⊔ comap S.A.
  have hσ_eq : S.σ_AUX = S.σ_UX ⊔ MeasurableSpace.comap S.A inferInstance := by
    change MeasurableSpace.comap (fun ω => (S.A ω, S.U ω, S.X ω)) _ = _
    rw [show (inferInstance : MeasurableSpace (Bool × γ_U × γ_X))
          = (inferInstance : MeasurableSpace Bool).prod inferInstance from rfl,
        MeasurableSpace.comap_prodMk]
    exact sup_comm _ _
  rw [hσ_eq]
  exact condExp_sup_comap_eq_of_condIndep
    (m := S.σ_UX) S.σ_UX_le S.measurable_A (S.measurable_YofA a) latent_exch
    (h := id) measurable_id (by simpa using hYaInt)

/-- From `latent_exch a : Y(a) ⟂ A | (U,X)`:
`E[Y(a) | σ(A,U,X)] =ᵐ[μ] E[Y(a) | σ(U,X)]`. -/
lemma latent_exch_to_condExp (HA : Assumptions S μ) (a : Bool) :
    μ[S.YofA a | S.σ_AUX] =ᵐ[μ] μ[S.YofA a | S.σ_UX] := by
  have hYaInt : Integrable (S.YofA a) μ := by
    cases a
    · exact HA.integrable_YofA0
    · exact HA.integrable_YofA1
  exact latent_exch_to_condExp' a (HA.latent_exch a) hYaInt

/-! ### Lemma 5: on {A=a}, condExp of Y equals condExp of Y(a) -/

/-- Field-level form: from consistency, integrability of `Y` and `Y(a)`, on
`{A=a}` we have `E[Y | σ(A,U,X)] =ᵐ[μ.restrict {A=a}] E[Y(a) | σ(A,U,X)]`. -/
lemma consistency_event' (HC : POSystem.Consistency P) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (hYInt : Integrable S.Y μ) (hYaInt : Integrable (S.YofA a) μ) :
    μ[S.Y | S.σ_AUX] =ᵐ[μ.restrict {ω | S.A ω = a}] μ[S.YofA a | S.σ_AUX] := by
  -- Step 1: Y =ᵐ[μ.restrict {A=a}] Y(a) pointwise from consistency.
  have hYeq : S.Y =ᵐ[μ.restrict {ω | S.A ω = a}] S.YofA a := by
    have hs : MeasurableSet {ω : P.Ω | S.A ω = a} := S.measurable_A (measurableSet_singleton a)
    apply ae_restrict_of_forall_mem hs
    intro ω hω
    exact (POVar.cf_eq_factual_on_event HC S.Yvar S.Avar a hAY.symm hω).symm
  set s : Set P.Ω := {ω | S.A ω = a}
  have hs_in_m : MeasurableSet[S.σ_AUX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  have hs : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  let h : P.Ω → ℝ := fun ω => S.Y ω - S.YofA a ω
  have hint : Integrable h μ := hYInt.sub hYaInt
  -- s.indicator h = 0 μ-a.e.
  have hind_zero : s.indicator h =ᵐ[μ] 0 := by
    have h_zero_on_s : h =ᵐ[μ.restrict s] 0 := by
      filter_upwards [hYeq] with ω hω
      simp [h, hω]
    simpa using Causalean.indicator_aeEq_of_aeEq_restrict hs h_zero_on_s
  have hh_zero_on_s : μ[h | S.σ_AUX] =ᵐ[μ.restrict s] 0 := by
    have hindCE_zero : s.indicator (μ[h | S.σ_AUX]) =ᵐ[μ] 0 :=
      Causalean.condExp_indicator_aeEq_zero hs_in_m hint hind_zero
    have hindCE_zero' :
        s.indicator (μ[h | S.σ_AUX]) =ᵐ[μ] s.indicator (0 : P.Ω → ℝ) := by
      simpa using hindCE_zero
    simpa using Causalean.aeEq_restrict_of_indicator_aeEq hs hindCE_zero'
  have hCE_sub : μ[h | S.σ_AUX] =ᵐ[μ] μ[S.Y | S.σ_AUX] - μ[S.YofA a | S.σ_AUX] :=
    MeasureTheory.condExp_sub (m := S.σ_AUX) hYInt hYaInt
  have hCE_sub_restrict : μ[h | S.σ_AUX]
      =ᵐ[μ.restrict s] μ[S.Y | S.σ_AUX] - μ[S.YofA a | S.σ_AUX] :=
    ae_restrict_of_ae hCE_sub
  have hdiff_zero : (μ[S.Y | S.σ_AUX] - μ[S.YofA a | S.σ_AUX])
      =ᵐ[μ.restrict s] 0 :=
    hCE_sub_restrict.symm.trans hh_zero_on_s
  filter_upwards [hdiff_zero] with ω hω
  have : (μ[S.Y | S.σ_AUX]) ω - (μ[S.YofA a | S.σ_AUX]) ω = 0 := by
    simpa [Pi.sub_apply, Pi.zero_apply] using hω
  linarith

/-- From `consistency`, on the event `{A=a}`, `Y = Y(a)` pointwise.
Hence `E[Y | σ(A,U,X)] =ᵐ[μ.restrict {A=a}] E[Y(a) | σ(A,U,X)]`.

Requires `hAY : S.Avar.v ≠ S.Yvar.v` (treatment and outcome are distinct nodes). -/
lemma consistency_event (HA : Assumptions S μ) (a : Bool) (hAY : S.Avar.v ≠ S.Yvar.v) :
    μ[S.Y | S.σ_AUX] =ᵐ[μ.restrict {ω | S.A ω = a}] μ[S.YofA a | S.σ_AUX] := by
  have hYaInt : Integrable (S.YofA a) μ := by
    cases a
    · exact HA.integrable_YofA0
    · exact HA.integrable_YofA1
  exact consistency_event' HA.consistency a hAY (HA.integrable_Y hAY) hYaInt

/-! ### Lemma 6: lift stratum-wise zero σ_UX-measurable function to global -/

/-- From `positivity_arm a` and a σ_UX-measurable function that is μ-a.e.
zero on the arm `{A=a}`, conclude it is μ-a.e. zero globally.

Proof: the carrier `B := {ω | f ω ≠ 0}` is σ_UX-measurable; the arm
hypothesis gives `μ(B ∩ {A=a}) = 0`; positivity_arm forces `μ B = 0`. -/
lemma eq_zero_globally_of_eq_zero_on_arm
    (HA : Assumptions S μ) (a : Bool) {f : P.Ω → ℝ}
    (hf_meas : Measurable[S.σ_UX] f)
    (hf_zero_on_arm : f =ᵐ[μ.restrict {ω | S.A ω = a}] 0) :
    f =ᵐ[μ] 0 := by
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  have hs : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  -- Carrier B := {ω | f ω ≠ 0}, σ_UX-measurable.
  set B : Set P.Ω := {ω | f ω ≠ 0} with hB_def
  have hB_eq : B = f ⁻¹' {0}ᶜ := by
    ext ω; simp [B, hB_def]
  have hB_meas : MeasurableSet[S.σ_UX] B := by
    rw [hB_eq]
    exact hf_meas (MeasurableSet.compl (measurableSet_singleton (0 : ℝ)))
  -- arm hypothesis: μ(B ∩ s) = 0.
  have hB_meas' : MeasurableSet B := S.σ_UX_le _ hB_meas
  have hBs_zero : μ (B ∩ s) = 0 := by
    have h1 : (μ.restrict s) B = 0 := by
      have := hf_zero_on_arm
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at this
      convert this using 2
    rwa [MeasureTheory.Measure.restrict_apply hB_meas'] at h1
  -- positivity_arm gives μ B = 0, i.e. f =ᵐ[μ] 0.
  have hB_zero : μ B = 0 := HA.positivity_arm a B hB_meas hBs_zero
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  convert hB_zero using 2

end POProximalSystem

end PO
end Causalean
