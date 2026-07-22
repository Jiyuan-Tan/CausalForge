/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal ATE identification theorem

Main result of the proximal causal identification approach
(prop:po-proximal-ate, `doc/Basic Concepts.tex` §2541–2623).

Two theorems:
- `Eofyofa_eq_Eh`  : E[Y(a)] = E[h(a,W,X)] for each a ∈ {0,1}.
- `ate_proximal`   : ATE = E[h(1,W,X)] - E[h(0,W,X)].
-/

import Causalean.PO.ID.Exact.Proximal.Helpers
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Proximal ATE Identification

This file proves the proximal causal identification equalities from the
`POProximalSystem.Assumptions` bundle. The theorem
`Assumptions.Eofyofa_eq_Eh` shows that each treatment-specific counterfactual
mean equals the corresponding bridge-function mean,
`integral Y(a) = integral h(a,W,X)`. The theorem `Assumptions.ate_proximal`
then identifies the average treatment effect as
`integral h(true,W,X) - integral h(false,W,X)`.

The proof uses the helper reductions from `Proximal.Helpers`, a Doob-Dynkin
factorization through `(U,X)`, treatment-arm completeness, and arm positivity
to globalize the arm-wise bridge equality. -/

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

namespace Assumptions

/-! ### Main theorem 1: E[Y(a)] = E[h(a,W,X)] -/

/-- **Proximal ATE identification** (prop:po-proximal-ate step 1).

For each treatment level `a`, the counterfactual mean equals the bridge mean:
  ∫ ω, S.YofA a ω ∂μ = ∫ ω, HA.h (a, S.W ω, S.X ω) ∂μ.

**Proof sketch** (see `doc/Basic Concepts.tex` §2555–2622):
1. Define auxiliary function g_a via σ-algebra factorisation.
2. Use `condExp_drop_Z`/`condExp_h_drop_Z` to reduce σ_AZUX to σ_AUX.
3. Tower into σ_AZX; apply `bridge` to get E[g_a(U,X)|σ_AZX]=ᵐ 0.
4. Apply `completeness` to get g_a(U,X)=ᵐ[restrict {A=a}] 0.
5. Use `condExp_h_drop_A`, `latent_exch_to_condExp`, `consistency_event`.
6. Integrate both sides via `MeasureTheory.integral_condExp`.
-/
theorem Eofyofa_eq_Eh (HA : Assumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v) :
    ∫ ω, S.YofA a ω ∂μ = ∫ ω, HA.h (a, S.W ω, S.X ω) ∂μ := by
  -- Set s = {A = a}; needed throughout.
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  -- Integrability shortcuts.
  have hYInt : Integrable S.Y μ := HA.integrable_Y hAY
  have hYaInt : Integrable (S.YofA a) μ := by
    cases a
    · exact HA.integrable_YofA0
    · exact HA.integrable_YofA1
  have hhInt : Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ := by
    cases a
    · exact HA.integrable_h0WX
    · exact HA.integrable_h1WX
  have hhAInt : Integrable (fun ω => HA.h (S.A ω, S.W ω, S.X ω)) μ := HA.integrable_hAWX
  have h_meas_haWX : Measurable (fun ω => HA.h (a, S.W ω, S.X ω)) := by
    have hp : Measurable (fun ω : P.Ω => (a, S.W ω, S.X ω)) := by
      exact Measurable.prodMk measurable_const
        (Measurable.prodMk S.measurable_W S.measurable_X)
    exact HA.measurable_h.comp hp
  -- ============================================================
  -- Step 1: Construct g_a : γ_U × γ_X → ℝ via Doob–Dynkin.
  -- ============================================================
  -- μ[Y | σ_AUX] is σ_AUX = comap S.AUX-measurable, so factors through S.AUX.
  have hCEY_meas : Measurable[S.σ_AUX] (μ[S.Y | S.σ_AUX]) :=
    MeasureTheory.stronglyMeasurable_condExp.measurable
  have hCEY_meas' : Measurable[MeasurableSpace.comap S.AUX inferInstance]
      (μ[S.Y | S.σ_AUX]) := hCEY_meas
  obtain ⟨f_Y, hf_Y_meas, hf_Y_eq⟩ :=
    Measurable.exists_eq_measurable_comp (f := S.AUX) (Z := ℝ) hCEY_meas'
  -- μ[h(a,W,X) | σ_AUX] is also σ_AUX-measurable.
  have hCEh_meas : Measurable[S.σ_AUX]
      (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) :=
    MeasureTheory.stronglyMeasurable_condExp.measurable
  have hCEh_meas' : Measurable[MeasurableSpace.comap S.AUX inferInstance]
      (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) := hCEh_meas
  obtain ⟨f_h, hf_h_meas, hf_h_eq⟩ :=
    Measurable.exists_eq_measurable_comp (f := S.AUX) (Z := ℝ) hCEh_meas'
  -- Define g_a (u, x) := f_Y (a, u, x) - f_h (a, u, x).
  let g_a : γ_U × γ_X → ℝ := fun p => f_Y (a, p.1, p.2) - f_h (a, p.1, p.2)
  have g_a_meas : Measurable g_a := by
    have h1 : Measurable (fun p : γ_U × γ_X => f_Y (a, p.1, p.2)) := by
      have : Measurable (fun p : γ_U × γ_X => (a, p.1, p.2)) := by fun_prop
      exact hf_Y_meas.comp this
    have h2 : Measurable (fun p : γ_U × γ_X => f_h (a, p.1, p.2)) := by
      have : Measurable (fun p : γ_U × γ_X => (a, p.1, p.2)) := by fun_prop
      exact hf_h_meas.comp this
    exact h1.sub h2
  -- g_a ∘ S.UX is integrable on the restriction to s = {A = a}.
  -- On s, S.AUX ω = (a, S.U ω, S.X ω), so g_a ∘ UX = (μ[Y|σ_AUX]) - (μ[h|σ_AUX])
  -- pointwise. Both condExps are integrable globally, hence on restrict, and
  -- their difference is integrable; congr lifts to g_a ∘ UX.
  have g_a_UX_int : Integrable (fun ω => g_a (S.UX ω)) (μ.restrict s) := by
    have hCEY_int : Integrable (μ[S.Y | S.σ_AUX]) μ := MeasureTheory.integrable_condExp
    have hCEh_int : Integrable (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) μ :=
      MeasureTheory.integrable_condExp
    have hCEY_int_r : Integrable (μ[S.Y | S.σ_AUX]) (μ.restrict s) := hCEY_int.restrict
    have hCEh_int_r : Integrable (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX])
        (μ.restrict s) := hCEh_int.restrict
    have hdiff_int : Integrable
        (fun ω => (μ[S.Y | S.σ_AUX]) ω -
          (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω) (μ.restrict s) :=
      hCEY_int_r.sub hCEh_int_r
    -- Show on s: g_a (S.UX ω) = (μ[Y|σ_AUX]) ω - (μ[h|σ_AUX]) ω.
    have hae : (fun ω => (μ[S.Y | S.σ_AUX]) ω -
          (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω)
        =ᵐ[μ.restrict s] (fun ω => g_a (S.UX ω)) := by
      filter_upwards [ae_restrict_mem hs_meas] with ω hω_s
      have hAa : S.A ω = a := hω_s
      have hAUX_eq : S.AUX ω = (a, S.U ω, S.X ω) := by
        change (S.A ω, S.U ω, S.X ω) = (a, S.U ω, S.X ω); rw [hAa]
      have hY : (μ[S.Y | S.σ_AUX]) ω = f_Y (a, S.U ω, S.X ω) := by
        have h1 := congrFun hf_Y_eq ω
        change (μ[S.Y | S.σ_AUX]) ω = f_Y (a, S.U ω, S.X ω)
        rw [h1]; change f_Y (S.AUX ω) = f_Y (a, S.U ω, S.X ω); rw [hAUX_eq]
      have hh : (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
          = f_h (a, S.U ω, S.X ω) := by
        have h1 := congrFun hf_h_eq ω
        change (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω = f_h (a, S.U ω, S.X ω)
        rw [h1]; change f_h (S.AUX ω) = f_h (a, S.U ω, S.X ω); rw [hAUX_eq]
      have hUX : S.UX ω = (S.U ω, S.X ω) := rfl
      simp [hY, hh, g_a, hUX]
    exact hdiff_int.congr hae
  -- ============================================================
  -- Step 2: μ[Y - h(a,W,X) | σ_AZUX] =ᵐ[μ.restrict s] g_a ∘ S.UX.
  -- ============================================================
  -- By linearity + helpers 1, 2:
  --   μ[Y - h(a,W,X) | σ_AZUX]
  --   =ᵐ μ[Y | σ_AZUX] - μ[h(a,W,X) | σ_AZUX]            (linearity)
  --   =ᵐ μ[Y | σ_AUX] - μ[h(a,W,X) | σ_AUX]              (helpers 1, 2)
  --   = (f_Y ∘ S.AUX) - (f_h ∘ S.AUX)                      (Doob–Dynkin)
  -- On s = {A=a}, S.AUX ω = (a, S.U ω, S.X ω), so this evaluates to
  --   f_Y(a, S.U ω, S.X ω) - f_h(a, S.U ω, S.X ω) = g_a (S.UX ω).
  have step2 : (μ[fun ω => S.Y ω - HA.h (a, S.W ω, S.X ω) | S.σ_AZUX])
      =ᵐ[μ.restrict s] (fun ω => g_a (S.UX ω)) := by
    -- Linearity: μ[Y - h(a,W,X)|σ_AZUX] =ᵐ μ[Y|σ_AZUX] - μ[h(a,W,X)|σ_AZUX].
    have hlin : μ[fun ω => S.Y ω - HA.h (a, S.W ω, S.X ω) | S.σ_AZUX]
        =ᵐ[μ] μ[S.Y | S.σ_AZUX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AZUX] :=
      MeasureTheory.condExp_sub (m := S.σ_AZUX) hYInt hhInt
    -- Helpers 1, 2: drop Z.
    have h1 : μ[S.Y | S.σ_AZUX] =ᵐ[μ] μ[S.Y | S.σ_AUX] := condExp_drop_Z HA hAY
    have h2 : μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AZUX]
        =ᵐ[μ] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] := condExp_h_drop_Z HA a
    -- Combine globally:
    --   μ[Y-h|σ_AZUX] =ᵐ μ[Y|σ_AUX] - μ[h|σ_AUX].
    have hglobal : μ[fun ω => S.Y ω - HA.h (a, S.W ω, S.X ω) | S.σ_AZUX]
        =ᵐ[μ] μ[S.Y | S.σ_AUX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] := by
      refine hlin.trans ?_
      filter_upwards [h1, h2] with ω hω1 hω2
      simp [Pi.sub_apply, hω1, hω2]
    -- Now restrict to s.
    have hrestrict : μ[fun ω => S.Y ω - HA.h (a, S.W ω, S.X ω) | S.σ_AZUX]
        =ᵐ[μ.restrict s]
          μ[S.Y | S.σ_AUX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
      ae_restrict_of_ae hglobal
    -- On s, the RHS = g_a ∘ S.UX (Doob–Dynkin substitution, same as step 5).
    refine hrestrict.trans ?_
    filter_upwards [ae_restrict_mem hs_meas] with ω hω_s
    have hAa : S.A ω = a := hω_s
    have hAUX_eq : S.AUX ω = (a, S.U ω, S.X ω) := by
      change (S.A ω, S.U ω, S.X ω) = (a, S.U ω, S.X ω); rw [hAa]
    have hY : (μ[S.Y | S.σ_AUX]) ω = f_Y (a, S.U ω, S.X ω) := by
      have h1 := congrFun hf_Y_eq ω
      change (μ[S.Y | S.σ_AUX]) ω = f_Y (a, S.U ω, S.X ω)
      rw [h1]; change f_Y (S.AUX ω) = f_Y (a, S.U ω, S.X ω); rw [hAUX_eq]
    have hh : (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
        = f_h (a, S.U ω, S.X ω) := by
      have h1 := congrFun hf_h_eq ω
      change (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω = f_h (a, S.U ω, S.X ω)
      rw [h1]; change f_h (S.AUX ω) = f_h (a, S.U ω, S.X ω); rw [hAUX_eq]
    show (μ[S.Y | S.σ_AUX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
        = g_a (S.UX ω)
    have hUX : S.UX ω = (S.U ω, S.X ω) := rfl
    simp [Pi.sub_apply, hY, hh, g_a, hUX]
  -- ============================================================
  -- Step 3: μ[g_a ∘ S.UX | σ_AZX] =ᵐ[μ.restrict s] 0.
  -- ============================================================
  -- σ_AZX ≤ σ_AZUX (σ_AZUX includes U), so by tower:
  --   μ[Y - h(A,W,X) | σ_AZX] =ᵐ μ[μ[Y - h(A,W,X) | σ_AZUX] | σ_AZX].
  -- Bridge gives LHS =ᵐ 0; on s, h(A,W,X) =ᵐ h(a,W,X) (since A=a on s), and
  -- s ∈ σ_AZX, so we can swap to get
  --   μ[μ[Y - h(a,W,X) | σ_AZUX] | σ_AZX] =ᵐ[restrict s] 0.
  -- Combining with step2: μ[g_a ∘ S.UX | σ_AZX] =ᵐ[restrict s] 0.
  have step3 : (μ[fun ω => g_a (S.UX ω) | S.σ_AZX]) =ᵐ[μ.restrict s] 0 := by
    -- Strategy:
    --   1. Tower: σ_AZX ≤ σ_AZUX. Get
    --      μ[g_a∘UX | σ_AZX] =ᵐ μ[μ[g_a∘UX | σ_AZUX] | σ_AZX].
    --   2. Step 2 says μ[Y - h(a,W,X) | σ_AZUX] =ᵐ[restrict s] g_a∘UX.
    --      Lift LHS to global: bridge gives μ[Y - h(A,W,X) | σ_AZX] =ᵐ 0,
    --      so condExp through indicator on {A=a} (where h(A,W,X)=h(a,W,X))
    --      gives the goal.
    -- σ_AZX ≤ σ_AZUX (since AZUX projects onto AZX measurably).
    have hAZX_le_AZUX : S.σ_AZX ≤ S.σ_AZUX := by
      -- Show S.AZX is σ_AZUX-measurable.
      have hAZX_meas : Measurable[S.σ_AZUX] S.AZX := by
        show Measurable[MeasurableSpace.comap S.AZUX inferInstance] S.AZX
        intro u hu
        refine ⟨(fun p : Bool × γ_Z × γ_U × γ_X => (p.1, p.2.1, p.2.2.2)) ⁻¹' u, ?_, ?_⟩
        · exact (measurable_fst.prodMk
            (measurable_fst.comp measurable_snd |>.prodMk
              (measurable_snd.comp (measurable_snd.comp measurable_snd)))) hu
        · ext ω; rfl
      exact hAZX_meas.comap_le
    -- s = {A=a} ∈ σ_AZX (use comap of (A,Z,X) on the first coordinate).
    have hs_in_AZX : MeasurableSet[S.σ_AZX] s := by
      refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
      · exact measurable_fst (measurableSet_singleton a)
      · ext ω; rfl
    -- Difference function and integrability.
    let h : P.Ω → ℝ := fun ω => S.Y ω - HA.h (S.A ω, S.W ω, S.X ω)
    let h' : P.Ω → ℝ := fun ω => S.Y ω - HA.h (a, S.W ω, S.X ω)
    have hint : Integrable h μ := hYInt.sub hhAInt
    have hint' : Integrable h' μ := hYInt.sub hhInt
    -- On s, h = h' pointwise.
    have hh_eq_on_s : ∀ᵐ ω ∂(μ.restrict s), h ω = h' ω := by
      filter_upwards [ae_restrict_mem hs_meas] with ω hω_s
      have hAa : S.A ω = a := hω_s
      show S.Y ω - HA.h (S.A ω, S.W ω, S.X ω) = S.Y ω - HA.h (a, S.W ω, S.X ω)
      rw [hAa]
    -- Tower step 2 to σ_AZX:
    --   μ[h' | σ_AZX] =ᵐ μ[μ[h' | σ_AZUX] | σ_AZX].
    have h_tower : μ[h' | S.σ_AZX] =ᵐ[μ] μ[μ[h' | S.σ_AZUX] | S.σ_AZX] :=
      (MeasureTheory.condExp_condExp_of_le hAZX_le_AZUX S.σ_AZUX_le).symm
    -- step2 (restricted) lifts: μ[μ[h' | σ_AZUX] | σ_AZX] =ᵐ[restrict s] μ[g_a∘UX | σ_AZX].
    -- Use indicator technique: 1_s · μ[h' | σ_AZUX] =ᵐ 1_s · g_a∘UX  (both globally).
    -- Then condExp_indicator with s ∈ σ_AZX.
    -- Actually simpler: condExp_congr on restrict requires inner =ᵐ on restrict,
    -- which doesn't directly give condExp =ᵐ on restrict.
    -- We use: indicator s · μ[h'|σ_AZUX] =ᵐ[μ] indicator s · g_a∘UX.
    have hCEh'_AZUX_int : Integrable (μ[h' | S.σ_AZUX]) μ := MeasureTheory.integrable_condExp
    -- Case split: if g_a ∘ UX is not globally integrable, μ[g_a∘UX|σ_AZX] = 0
    -- everywhere, so the goal is trivial. Otherwise, use original argument.
    by_cases hg_a_int : Integrable (fun ω => g_a (S.UX ω)) μ
    case neg =>
      -- μ[g_a∘UX|σ_AZX] = 0 globally, so a.e. zero on restrict s.
      have h0 : (μ[fun ω => g_a (S.UX ω) | S.σ_AZX]) = 0 :=
        MeasureTheory.condExp_of_not_integrable hg_a_int
      rw [h0]
    -- pos branch: hg_a_int : Integrable (fun ω => g_a (S.UX ω)) μ holds.
    -- 1_s · μ[h'|σ_AZUX] =ᵐ[μ] 1_s · g_a∘UX (from step2 restricted to s).
    have hind_eq : s.indicator (μ[h' | S.σ_AZUX]) =ᵐ[μ] s.indicator (fun ω => g_a (S.UX ω)) := by
      exact Causalean.indicator_aeEq_of_aeEq_restrict hs_meas step2
    -- Apply condExp to both sides and use condExp_indicator.
    have hCE_ind_h' := MeasureTheory.condExp_indicator (m := S.σ_AZX) hCEh'_AZUX_int hs_in_AZX
    have hCE_ind_g := MeasureTheory.condExp_indicator (m := S.σ_AZX) hg_a_int hs_in_AZX
    -- μ[1_s · μ[h'|σ_AZUX] | σ_AZX] =ᵐ μ[1_s · g_a∘UX | σ_AZX] (by hind_eq + condExp_congr).
    have hCE_eq : μ[s.indicator (μ[h' | S.σ_AZUX]) | S.σ_AZX]
        =ᵐ[μ] μ[s.indicator (fun ω => g_a (S.UX ω)) | S.σ_AZX] :=
      MeasureTheory.condExp_congr_ae hind_eq
    -- Combine: 1_s · μ[μ[h'|σ_AZUX] | σ_AZX] =ᵐ 1_s · μ[g_a∘UX | σ_AZX].
    have hind_CE : s.indicator (μ[μ[h' | S.σ_AZUX] | S.σ_AZX])
        =ᵐ[μ] s.indicator (μ[fun ω => g_a (S.UX ω) | S.σ_AZX]) :=
      hCE_ind_h'.symm.trans (hCE_eq.trans hCE_ind_g)
    -- Now we need: 1_s · μ[μ[h'|σ_AZUX] | σ_AZX] =ᵐ 0, since by tower
    --   μ[μ[h'|σ_AZUX] | σ_AZX] =ᵐ μ[h' | σ_AZX]
    -- and on s (since {A=a} ∈ σ_AZX), μ[h'|σ_AZX] =ᵐ μ[h|σ_AZX] =ᵐ 0 (bridge).
    -- We prove 1_s · μ[h'|σ_AZX] =ᵐ 0 using bridge.
    -- Step (a): μ[h'|σ_AZX] =ᵐ[restrict s] 0.
    -- Use indicator technique: 1_s · h =ᵐ 1_s · h' globally (both pointwise on s).
    have hind_h_h' : s.indicator h =ᵐ[μ] s.indicator h' := by
      exact Causalean.indicator_aeEq_of_aeEq_restrict hs_meas hh_eq_on_s
    -- Apply condExp_indicator to both:
    have hCE_ind_h := MeasureTheory.condExp_indicator (m := S.σ_AZX) hint hs_in_AZX
    have hCE_ind_h'_AZX := MeasureTheory.condExp_indicator (m := S.σ_AZX) hint' hs_in_AZX
    -- μ[1_s · h | σ_AZX] =ᵐ μ[1_s · h' | σ_AZX] (by hind_h_h').
    have hCE_eq2 : μ[s.indicator h | S.σ_AZX] =ᵐ[μ] μ[s.indicator h' | S.σ_AZX] :=
      MeasureTheory.condExp_congr_ae hind_h_h'
    have hind_CE_h : s.indicator (μ[h | S.σ_AZX]) =ᵐ[μ] s.indicator (μ[h' | S.σ_AZX]) :=
      hCE_ind_h.symm.trans (hCE_eq2.trans hCE_ind_h'_AZX)
    -- Bridge: μ[h | σ_AZX] =ᵐ 0, so 1_s · μ[h|σ_AZX] =ᵐ 0.
    have hbridge : (μ[h | S.σ_AZX]) =ᵐ[μ] 0 := HA.bridge
    have hind_h_zero : s.indicator (μ[h | S.σ_AZX]) =ᵐ[μ] 0 := by
      filter_upwards [hbridge] with ω hω
      by_cases hωs : ω ∈ s
      · rw [Set.indicator_of_mem hωs, hω]
      · rw [Set.indicator_of_notMem hωs]; rfl
    -- So 1_s · μ[h'|σ_AZX] =ᵐ 0, hence μ[h'|σ_AZX] =ᵐ[restrict s] 0.
    have hind_h'_zero : s.indicator (μ[h' | S.σ_AZX]) =ᵐ[μ] 0 :=
      hind_CE_h.symm.trans hind_h_zero
    have hh'_AZX_zero : (μ[h' | S.σ_AZX]) =ᵐ[μ.restrict s] 0 := by
      have hind_h'_zero' :
          s.indicator (μ[h' | S.σ_AZX]) =ᵐ[μ] s.indicator (0 : P.Ω → ℝ) := by
        simpa using hind_h'_zero
      simpa using Causalean.aeEq_restrict_of_indicator_aeEq hs_meas hind_h'_zero'
    -- Tower h_tower says μ[h'|σ_AZX] =ᵐ μ[μ[h'|σ_AZUX]|σ_AZX]. Restrict to s:
    have h_tower_s : μ[h' | S.σ_AZX] =ᵐ[μ.restrict s] μ[μ[h' | S.σ_AZUX] | S.σ_AZX] :=
      ae_restrict_of_ae h_tower
    -- So μ[μ[h'|σ_AZUX]|σ_AZX] =ᵐ[restrict s] 0.
    have hinner_zero : (μ[μ[h' | S.σ_AZUX] | S.σ_AZX]) =ᵐ[μ.restrict s] 0 :=
      h_tower_s.symm.trans hh'_AZX_zero
    -- 1_s · μ[μ[h'|σ_AZUX]|σ_AZX] =ᵐ 0 globally.
    have hind_inner_zero : s.indicator (μ[μ[h' | S.σ_AZUX] | S.σ_AZX]) =ᵐ[μ] 0 := by
      simpa using Causalean.indicator_aeEq_of_aeEq_restrict hs_meas hinner_zero
    -- So 1_s · μ[g_a∘UX | σ_AZX] =ᵐ 0, hence the goal.
    have hind_g_zero : s.indicator (μ[fun ω => g_a (S.UX ω) | S.σ_AZX]) =ᵐ[μ] 0 :=
      hind_CE.symm.trans hind_inner_zero
    rw [Filter.EventuallyEq, ae_restrict_iff' hs_meas]
    filter_upwards [hind_g_zero] with ω hω hωs
    have : s.indicator (μ[fun ω => g_a (S.UX ω) | S.σ_AZX]) ω
        = (μ[fun ω => g_a (S.UX ω) | S.σ_AZX]) ω :=
      Set.indicator_of_mem hωs _
    simp [this] at hω
    simpa using hω
  -- ============================================================
  -- Step 4: Apply completeness → g_a ∘ S.UX =ᵐ[μ] 0.
  -- ============================================================
  have step4_r : (fun ω => g_a (S.UX ω)) =ᵐ[μ.restrict s] 0 :=
    HA.completeness a g_a g_a_meas g_a_UX_int step3
  -- ============================================================
  -- Step 5: μ[Y | σ_AUX] =ᵐ[restrict s] μ[h(a,W,X) | σ_AUX].
  -- ============================================================
  -- From step4, on s: f_Y(a, U, X) = f_h(a, U, X), and on s, S.AUX = (a, U, X),
  -- so (f_Y ∘ S.AUX) =ᵐ[restrict s] (f_h ∘ S.AUX), i.e.,
  -- μ[Y|σ_AUX] =ᵐ[restrict s] μ[h(a,W,X)|σ_AUX].
  have step5 : (μ[S.Y | S.σ_AUX])
      =ᵐ[μ.restrict s] (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) := by
    -- step4 gives g_a ∘ S.UX =ᵐ[μ] 0, i.e., f_Y(a,U,X) - f_h(a,U,X) =ᵐ 0.
    -- On s, S.AUX ω = (a, U ω, X ω), so f_Y ∘ S.AUX =ᵐ[restrict s] f_h ∘ S.AUX,
    -- which equals μ[Y|σ_AUX] resp. μ[h(a,W,X)|σ_AUX] by hf_Y_eq, hf_h_eq.
    have h0 : ∀ᵐ ω ∂(μ.restrict s),
        f_Y (a, S.U ω, S.X ω) - f_h (a, S.U ω, S.X ω) = 0 := by
      filter_upwards [step4_r] with ω hω
      exact hω
    filter_upwards [h0, ae_restrict_mem hs_meas] with ω hω hω_s
    -- On s, S.A ω = a, hence S.AUX ω = (a, S.U ω, S.X ω).
    have hAa : S.A ω = a := hω_s
    have hAUX_eq : S.AUX ω = (a, S.U ω, S.X ω) := by
      change (S.A ω, S.U ω, S.X ω) = (a, S.U ω, S.X ω)
      rw [hAa]
    have hY : (μ[S.Y | S.σ_AUX]) ω = f_Y (a, S.U ω, S.X ω) := by
      have h1 := congrFun hf_Y_eq ω
      change (μ[S.Y | S.σ_AUX]) ω = f_Y (a, S.U ω, S.X ω)
      rw [h1]
      change f_Y (S.AUX ω) = f_Y (a, S.U ω, S.X ω)
      rw [hAUX_eq]
    have hh : (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
        = f_h (a, S.U ω, S.X ω) := by
      have h1 := congrFun hf_h_eq ω
      change (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω = f_h (a, S.U ω, S.X ω)
      rw [h1]
      change f_h (S.AUX ω) = f_h (a, S.U ω, S.X ω)
      rw [hAUX_eq]
    linarith [hY, hh, hω]
  -- ============================================================
  -- Step 6: Chain helpers 5, 3, 4 to get on s:
  --   μ[YofA a | σ_UX] =ᵐ[restrict s] μ[h(a,W,X) | σ_UX].
  -- ============================================================
  have hHelper5 : μ[S.Y | S.σ_AUX] =ᵐ[μ.restrict s] μ[S.YofA a | S.σ_AUX] :=
    consistency_event HA a hAY
  have hHelper4 : μ[S.YofA a | S.σ_AUX] =ᵐ[μ] μ[S.YofA a | S.σ_UX] :=
    latent_exch_to_condExp HA a
  have hHelper3 : μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] :=
    condExp_h_drop_A HA a
  -- Combine: on s,
  --   μ[YofA a | σ_AUX] =ᵐ[restrict s] μ[Y | σ_AUX]                     (helper 5, sym)
  --   μ[Y | σ_AUX] =ᵐ[restrict s] μ[h(a,W,X) | σ_AUX]                   (step5)
  --   μ[h(a,W,X) | σ_AUX] =ᵐ μ[h(a,W,X) | σ_UX]                          (helper 3)
  --   μ[YofA a | σ_AUX] =ᵐ μ[YofA a | σ_UX]                              (helper 4)
  -- ⇒ on s, μ[YofA a | σ_UX] =ᵐ μ[h(a,W,X) | σ_UX].
  have step6 : μ[S.YofA a | S.σ_UX]
      =ᵐ[μ.restrict s] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] := by
    have hH4r : μ[S.YofA a | S.σ_AUX] =ᵐ[μ.restrict s] μ[S.YofA a | S.σ_UX] :=
      ae_restrict_of_ae hHelper4
    have hH3r : μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]
        =ᵐ[μ.restrict s] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] :=
      ae_restrict_of_ae hHelper3
    -- Chain: μ[YofA a|σ_UX] =ᵐ[s] μ[YofA a|σ_AUX] =ᵐ[s] μ[Y|σ_AUX]
    --                       =ᵐ[s] μ[h|σ_AUX] =ᵐ[s] μ[h|σ_UX].
    exact hH4r.symm.trans (hHelper5.symm.trans (step5.trans hH3r))
  -- ============================================================
  -- Step 7: Globalize step6 via completeness applied to D.
  -- ============================================================
  -- Both sides of step6 are σ_UX-measurable. Set D = LHS - RHS.
  -- D is σ_UX-measurable and D =ᵐ[restrict s] 0.
  -- We want D =ᵐ[μ] 0 (globally), to integrate.
  -- Construct g_D : γ_U × γ_X → ℝ via Doob–Dynkin so D = g_D ∘ S.UX a.e.
  -- Then g_D ∘ S.UX =ᵐ[restrict s] 0.
  -- To apply completeness we need μ[g_D ∘ S.UX | σ_AZX] =ᵐ[restrict s] 0.
  -- Strategy: μ[g_D ∘ S.UX | σ_AZX] = μ[μ[YofA a|σ_UX] - μ[h|σ_UX] | σ_AZX].
  -- Each of μ[YofA a|σ_UX] and μ[h|σ_UX] is σ_UX-measurable but not σ_AZX-measurable;
  -- we need to use further chain identities to push down. This step is genuinely
  -- subtle and may require an additional helper that we don't currently have.
  --
  -- s ∈ σ_AZX (used by completeness setup).
  have hs_in_AZX : MeasurableSet[S.σ_AZX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  -- Doob–Dynkin: factor μ[YofA a | σ_UX] and μ[h(a,W,X) | σ_UX] through S.UX.
  have hCEYa_meas : Measurable[S.σ_UX] (μ[S.YofA a | S.σ_UX]) :=
    MeasureTheory.stronglyMeasurable_condExp.measurable
  have hCEYa_meas' : Measurable[MeasurableSpace.comap S.UX inferInstance]
      (μ[S.YofA a | S.σ_UX]) := hCEYa_meas
  obtain ⟨f_Ya, hf_Ya_meas, hf_Ya_eq⟩ :=
    Measurable.exists_eq_measurable_comp (f := S.UX) (Z := ℝ) hCEYa_meas'
  have hCEhUX_meas : Measurable[S.σ_UX]
      (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) :=
    MeasureTheory.stronglyMeasurable_condExp.measurable
  have hCEhUX_meas' : Measurable[MeasurableSpace.comap S.UX inferInstance]
      (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) := hCEhUX_meas
  obtain ⟨f_hUX, hf_hUX_meas, hf_hUX_eq⟩ :=
    Measurable.exists_eq_measurable_comp (f := S.UX) (Z := ℝ) hCEhUX_meas'
  -- Define g_D : γ_U × γ_X → ℝ.
  let g_D : γ_U × γ_X → ℝ := fun p => f_Ya p - f_hUX p
  have g_D_meas : Measurable g_D := hf_Ya_meas.sub hf_hUX_meas
  -- D := μ[YofA a | σ_UX] - μ[h(a,W,X) | σ_UX] =ᵐ g_D ∘ S.UX (globally).
  -- More precisely: μ[YofA a | σ_UX] = f_Ya ∘ S.UX (eq_fun) and similarly for h.
  have hD_eq : (μ[S.YofA a | S.σ_UX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX])
      = (fun ω => g_D (S.UX ω)) := by
    funext ω
    show (μ[S.YofA a | S.σ_UX]) ω - (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) ω
      = g_D (S.UX ω)
    rw [congrFun hf_Ya_eq ω, congrFun hf_hUX_eq ω]
    rfl
  -- Integrabilities.
  have hCEYa_int : Integrable (μ[S.YofA a | S.σ_UX]) μ := MeasureTheory.integrable_condExp
  have hCEhUX_int : Integrable (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) μ :=
    MeasureTheory.integrable_condExp
  have hg_D_int : Integrable (fun ω => g_D (S.UX ω)) μ := by
    have : Integrable (μ[S.YofA a | S.σ_UX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) μ :=
      hCEYa_int.sub hCEhUX_int
    rwa [hD_eq] at this
  -- step6 ⇒ g_D ∘ S.UX =ᵐ[restrict s] 0.
  have hg_D_zero_on_s : (fun ω => g_D (S.UX ω)) =ᵐ[μ.restrict s] 0 := by
    -- step6 : μ[YofA a|σ_UX] =ᵐ[restrict s] μ[h|σ_UX].
    -- So D = LHS - RHS =ᵐ[restrict s] 0.
    have : (μ[S.YofA a | S.σ_UX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX])
        =ᵐ[μ.restrict s] 0 := by
      filter_upwards [step6] with ω hω
      simp [Pi.sub_apply, hω]
    rw [hD_eq] at this
    exact this
  -- 1_s · (g_D ∘ UX) =ᵐ[μ] 0 (globally).
  have hind_g_D_zero : s.indicator (fun ω => g_D (S.UX ω)) =ᵐ[μ] 0 := by
    simpa using Causalean.indicator_aeEq_of_aeEq_restrict hs_meas hg_D_zero_on_s
  -- condExp_indicator with s ∈ σ_AZX:
  --   μ[1_s · (g_D ∘ UX) | σ_AZX] =ᵐ 1_s · μ[g_D ∘ UX | σ_AZX].
  -- So 1_s · μ[g_D ∘ UX | σ_AZX] =ᵐ 0.
  have hind_CE_zero : s.indicator (μ[fun ω => g_D (S.UX ω) | S.σ_AZX]) =ᵐ[μ] 0 :=
    Causalean.condExp_indicator_aeEq_zero hs_in_AZX hg_D_int hind_g_D_zero
  -- Hence μ[g_D ∘ UX | σ_AZX] =ᵐ[restrict s] 0.
  have hCE_g_D_zero : (μ[fun ω => g_D (S.UX ω) | S.σ_AZX]) =ᵐ[μ.restrict s] 0 := by
    have hind_CE_zero' :
        s.indicator (μ[fun ω => g_D (S.UX ω) | S.σ_AZX])
          =ᵐ[μ] s.indicator (0 : P.Ω → ℝ) := by
      simpa using hind_CE_zero
    simpa using Causalean.aeEq_restrict_of_indicator_aeEq hs_meas hind_CE_zero'
  -- Apply completeness: g_D ∘ UX =ᵐ[μ] 0 globally.
  -- Completeness expects integrability on μ.restrict {A=a}; restrict the global one.
  have hg_D_int_r : Integrable (fun ω => g_D (S.UX ω)) (μ.restrict {ω | S.A ω = a}) :=
    hg_D_int.restrict
  have hg_D_zero_on_arm : (fun ω => g_D (S.UX ω)) =ᵐ[μ.restrict s] 0 :=
    HA.completeness a g_D g_D_meas hg_D_int_r hCE_g_D_zero
  have hg_D_meas_UX : Measurable[S.σ_UX] (fun ω => g_D (S.UX ω)) := by
    show Measurable[MeasurableSpace.comap S.UX inferInstance] (fun ω => g_D (S.UX ω))
    intro u hu
    exact ⟨g_D ⁻¹' u, g_D_meas hu, rfl⟩
  have hg_D_zero : (fun ω => g_D (S.UX ω)) =ᵐ[μ] 0 :=
    eq_zero_globally_of_eq_zero_on_arm HA a hg_D_meas_UX hg_D_zero_on_arm
  -- So D =ᵐ[μ] 0, i.e., μ[YofA a|σ_UX] =ᵐ[μ] μ[h(a,W,X)|σ_UX].
  have hD_zero : (μ[S.YofA a | S.σ_UX] - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX])
      =ᵐ[μ] 0 := by rw [hD_eq]; exact hg_D_zero
  have hCE_eq : μ[S.YofA a | S.σ_UX]
      =ᵐ[μ] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] := by
    filter_upwards [hD_zero] with ω hω
    have : (μ[S.YofA a | S.σ_UX]) ω - (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) ω = 0 := by
      simpa [Pi.sub_apply, Pi.zero_apply] using hω
    linarith
  -- Integrate both sides via integral_condExp.
  have hint_eq : ∫ ω, (μ[S.YofA a | S.σ_UX]) ω ∂μ
      = ∫ ω, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) ω ∂μ :=
    MeasureTheory.integral_congr_ae hCE_eq
  -- ∫ μ[YofA a|σ_UX] ∂μ = ∫ YofA a ∂μ.
  have hint_Ya : ∫ ω, (μ[S.YofA a | S.σ_UX]) ω ∂μ = ∫ ω, S.YofA a ω ∂μ :=
    MeasureTheory.integral_condExp S.σ_UX_le
  -- ∫ μ[h|σ_UX] ∂μ = ∫ h ∂μ.
  have hint_h : ∫ ω, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) ω ∂μ
      = ∫ ω, HA.h (a, S.W ω, S.X ω) ∂μ :=
    MeasureTheory.integral_condExp S.σ_UX_le
  rw [← hint_Ya, hint_eq, hint_h]

/-! ### Main theorem 2: proximal ATE formula -/

/-- **Proximal ATE** (prop:po-proximal-ate).

  ATE  =  E[Y(1)] − E[Y(0)]
       =  E[h(1,W,X)] − E[h(0,W,X)].
-/
theorem ate_proximal (HA : Assumptions S μ) (hAY : S.Avar.v ≠ S.Yvar.v) :
    ∫ ω, S.YofA true ω ∂μ - ∫ ω, S.YofA false ω ∂μ
      = ∫ ω, HA.h (true, S.W ω, S.X ω) ∂μ
        - ∫ ω, HA.h (false, S.W ω, S.X ω) ∂μ := by
  rw [Eofyofa_eq_Eh HA true hAY, Eofyofa_eq_Eh HA false hAY]

end Assumptions

end POProximalSystem

end PO
end Causalean
