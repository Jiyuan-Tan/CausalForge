/-
Population residualization core (Frisch-Waugh-Lovell) — shared Panel primitive.

Framework primitives only — no `POSystem`, `CausalModel`, or `SWIGGraph`
dependency (imports only Mathlib L²/Bochner). Panel papers instantiate these
primitives for their specific nuisance class `H` and invoke the population
Frisch-Waugh-Lovell theorem `residualizedCoefficient_eq_of_normalEqs` to reduce
a paper-specific β to `E[D̃·Ỹ] / E[D̃²]`. The estimand-characterization papers
(Sloczynski OLS, Goodman-Bacon TWFE, Sun-Abraham event study, MTW IV, ...) are
current consumers, but the machinery is panel-program-agnostic.

NL artifact: `doc/basic_concepts/po/estimand_characterization/residualization_core.md`.
Source LaTeX: `doc/basic_concepts/po/estimand_characterization.tex`,
items `def:po-estimand-residualization-witness`,
`def:po-estimand-residualized-coefficient`, and `prop:po-estimand-fwl`.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Population Residualization

This file defines the population residualization primitives used by
Frisch-Waugh-Lovell style estimand-characterization results. It is independent
of any particular potential-outcome system so paper-specific modules can
instantiate the same nuisance-class interface. -/

namespace Causalean
namespace Panel

open MeasureTheory

/-- A linear square-integrable class is a nuisance space of real-valued
functions closed under zero, addition, and real scalar multiplication, with
every member square-integrable.

The class is represented predicate-style: `mem` carves out the underlying set
of functions. Membership entails `MemLp 2`, so integrability is bundled. -/
structure LinearL2Class {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The membership predicate cutting out `H ⊆ (Ω → ℝ)`. -/
  mem : (Ω → ℝ) → Prop
  /-- Every member is square-integrable. -/
  memLp : ∀ ⦃f : Ω → ℝ⦄, mem f → MemLp f 2 μ
  /-- The class contains the zero function. -/
  zero_mem : mem (fun _ => (0 : ℝ))
  /-- The class is closed under addition. -/
  add_mem : ∀ ⦃f g : Ω → ℝ⦄, mem f → mem g → mem (f + g)
  /-- The class is closed under scalar multiplication. -/
  smul_mem : ∀ (c : ℝ) ⦃f : Ω → ℝ⦄, mem f → mem (c • f)

/-- A residualization witness decomposes a real-valued function into a
nuisance-class component and a square-integrable residual that is orthogonal in
expectation to every nuisance function.

Bundles the in-class projection `VH`, the residual `Vtilde`, and the three
witness conditions: `VH ∈ H`, `V = VH + Vtilde` a.e., orthogonality of
`Vtilde` to every `h ∈ H`. The residual is required to be in `MemLp 2` so that
`∫ Vtilde · h` is well-defined for every `h ∈ H`. -/
structure ResidualizationWitness {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : LinearL2Class μ) (V : Ω → ℝ) where
  /-- The in-class projection `V_H ∈ H`. -/
  VH : Ω → ℝ
  /-- The residual `Ṽ`. -/
  Vtilde : Ω → ℝ
  /-- The projection lies in the nuisance class. -/
  VH_mem : H.mem VH
  /-- The residual is square-integrable. -/
  Vtilde_memLp : MemLp Vtilde 2 μ
  /-- Almost-everywhere decomposition `V = VH + Vtilde`. -/
  decomp : V =ᵐ[μ] VH + Vtilde
  /-- Population orthogonality: the residual is uncorrelated with every
  member of `H`. -/
  orthogonal : ∀ ⦃h : Ω → ℝ⦄, H.mem h → ∫ ω, Vtilde ω * h ω ∂μ = 0

/-- The residualized population coefficient is the ratio of the covariance-like
integral of treatment and outcome residuals to the second moment of the
treatment residual.

The denominator is left as-is here; positivity is supplied at theorem-use time. -/
noncomputable def residualizedCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : LinearL2Class μ) {Y D : Ω → ℝ}
    (wY : ResidualizationWitness μ H Y)
    (wD : ResidualizationWitness μ H D) : ℝ :=
  (∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ) / (∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ)

/-- Population Frisch-Waugh-Lovell theorem (`prop:po-estimand-fwl`).

If `(Y_H, Ỹ)` and `(D_H, D̃)` are residualization witnesses for `Y` and `D`
against a linear nuisance class `H`, `E[D̃²] > 0`, and `(β, H_β)` with
`H_β ∈ H` satisfy the population normal equations

    ∫ (Y - β·D - H_β) · D dμ = 0,
    ∫ (Y - β·D - H_β) · h dμ = 0   for every h ∈ H,

then `β = E[D̃ · Ỹ] / E[D̃²] = residualizedCoefficient μ H wY wD`.

Side hypotheses ensure the appearing integrals are well-defined: `Y` and `D`
are square-integrable (so their witnesses' decompositions integrate against
L² nuisance terms via Cauchy-Schwarz). -/
theorem residualizedCoefficient_eq_of_normalEqs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : LinearL2Class μ)
    {Y D : Ω → ℝ}
    (Y_memLp : MemLp Y 2 μ) (D_memLp : MemLp D 2 μ)
    (wY : ResidualizationWitness μ H Y)
    (wD : ResidualizationWitness μ H D)
    (hDtilde_pos : 0 < ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ)
    (β : ℝ) (Hβ : Ω → ℝ) (Hβ_mem : H.mem Hβ)
    (h_normal_D : ∫ ω, (Y ω - β * D ω - Hβ ω) * D ω ∂μ = 0)
    (h_normal_H : ∀ ⦃h : Ω → ℝ⦄, H.mem h →
      ∫ ω, (Y ω - β * D ω - Hβ ω) * h ω ∂μ = 0) :
    β = residualizedCoefficient μ H wY wD := by
  let e : Ω → ℝ := fun ω => Y ω - β * D ω - Hβ ω
  let h_star : Ω → ℝ := fun ω => -Hβ ω + (wY.VH ω + (-β) * wD.VH ω)
  have Hβ_mem' : MemLp Hβ 2 μ := H.memLp Hβ_mem
  have h_star_mem : H.mem h_star := by
    have h_neg_Hβ : H.mem (fun ω => -Hβ ω) := by
      simpa [smul_eq_mul] using (H.smul_mem (-1 : ℝ) Hβ_mem)
    have h_beta : H.mem (fun ω => (-β) * wD.VH ω) := by
      simpa [smul_eq_mul] using (H.smul_mem (-β) wD.VH_mem)
    have h_inner : H.mem (fun ω ↦ wY.VH ω + (-β) * wD.VH ω) := H.add_mem wY.VH_mem h_beta
    exact H.add_mem h_neg_Hβ h_inner
  have h_orth : ∫ ω, wD.Vtilde ω * h_star ω ∂μ = 0 := wD.orthogonal h_star_mem
  have e_mem : MemLp e 2 μ := by
    dsimp [e]
    exact (Y_memLp.sub (MemLp.const_mul D_memLp β)).sub Hβ_mem'
  have hD_decomp_int : ∫ ω, e ω * D ω ∂μ = ∫ ω, e ω * (wD.VH ω + wD.Vtilde ω) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [wD.decomp] with ω hD
    simp [e, hD]
  have hD_VH_plus_Vtilde : ∫ ω, e ω * (wD.VH ω + wD.Vtilde ω) ∂μ = 0 := by
    calc
      ∫ ω, e ω * (wD.VH ω + wD.Vtilde ω) ∂μ = ∫ ω, e ω * D ω ∂μ := hD_decomp_int.symm
      _ = 0 := by simpa [e] using h_normal_D
  have h_mul_split : (fun ω => e ω * (wD.VH ω + wD.Vtilde ω)) =ᵐ[μ]
      (fun ω => e ω * wD.VH ω + e ω * wD.Vtilde ω) := by
    exact Filter.EventuallyEq.of_eq (by
      funext ω
      ring)
  have h_mul_split_int :
      (∫ ω, e ω * wD.VH ω ∂μ) + ∫ ω, e ω * wD.Vtilde ω ∂μ =
        ∫ ω, e ω * (wD.VH ω + wD.Vtilde ω) ∂μ := by
    calc
      (∫ ω, e ω * wD.VH ω ∂μ) + ∫ ω, e ω * wD.Vtilde ω ∂μ =
          ∫ ω, e ω * wD.VH ω + e ω * wD.Vtilde ω ∂μ := by
            have hVH_int : Integrable (fun ω => e ω * wD.VH ω) μ :=
              e_mem.integrable_mul (H.memLp wD.VH_mem)
            have hVt_int : Integrable (fun ω => e ω * wD.Vtilde ω) μ :=
              e_mem.integrable_mul wD.Vtilde_memLp
            exact (integral_add hVH_int hVt_int).symm
      _ = ∫ ω, e ω * (wD.VH ω + wD.Vtilde ω) ∂μ :=
            (integral_congr_ae h_mul_split).symm
  have hVH : ∫ ω, e ω * wD.VH ω ∂μ = 0 := by simpa [e] using h_normal_H wD.VH_mem
  have h_eVtilde_int : ∫ ω, e ω * wD.Vtilde ω ∂μ = 0 := by
    have hsplit :
        (∫ ω, e ω * wD.VH ω ∂μ) + ∫ ω, e ω * wD.Vtilde ω ∂μ = 0 := by
      calc
        (∫ ω, e ω * wD.VH ω ∂μ) + ∫ ω, e ω * wD.Vtilde ω ∂μ
            = ∫ ω, e ω * (wD.VH ω + wD.Vtilde ω) ∂μ := h_mul_split_int
        _ = 0 := hD_VH_plus_Vtilde
    linarith [hsplit, hVH]
  have h_eVtilde_mul : ∫ ω, wD.Vtilde ω * e ω ∂μ = 0 := by
    simpa [mul_comm] using h_eVtilde_int
  have hV_decomp :
      (fun ω => wD.Vtilde ω * e ω) =ᵐ[μ]
        (fun ω => wD.Vtilde ω * (h_star ω + (wY.Vtilde ω - β * wD.Vtilde ω))) := by
    filter_upwards [wY.decomp, wD.decomp] with ω hY hD
    have hE : e ω = h_star ω + (wY.Vtilde ω - β * wD.Vtilde ω) := by
      simp [e, h_star, hY, hD]
      ring
    rw [hE]
  have hV_mul_split :
      (fun ω => wD.Vtilde ω * (h_star ω + (wY.Vtilde ω - β * wD.Vtilde ω))) =ᵐ[μ]
        (fun ω => wD.Vtilde ω * h_star ω + wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω)) := by
    exact Filter.EventuallyEq.of_eq (by
      funext ω
      ring)
  have h_star_int : Integrable (fun ω => wD.Vtilde ω * h_star ω) μ :=
    wD.Vtilde_memLp.integrable_mul (H.memLp h_star_mem)
  have h_second_mem : MemLp (fun ω => wY.Vtilde ω - β * wD.Vtilde ω) 2 μ :=
    wY.Vtilde_memLp.sub (MemLp.const_mul wD.Vtilde_memLp β)
  have h_second_int : Integrable (fun ω => wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω)) μ :=
    wD.Vtilde_memLp.integrable_mul h_second_mem
  have h_expanded :
      ∫ ω, wD.Vtilde ω * e ω ∂μ =
        ∫ ω, wD.Vtilde ω * h_star ω ∂μ + ∫ ω, wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω) ∂μ := by
    calc
      ∫ ω, wD.Vtilde ω * e ω ∂μ =
          ∫ ω, wD.Vtilde ω * h_star ω + wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω) ∂μ := by
        exact integral_congr_ae (hV_decomp.trans hV_mul_split)
      _ = ∫ ω, wD.Vtilde ω * h_star ω ∂μ + ∫ ω, wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω) ∂μ :=
        integral_add h_star_int h_second_int
  have h_num_zero : ∫ ω, wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω) ∂μ = 0 := by
    linarith [h_expanded, h_eVtilde_mul, h_orth]
  have hβ_mul : ∫ ω, wD.Vtilde ω * (β * wD.Vtilde ω) ∂μ =
      β * ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ := by
    have htmp :
        (fun ω => wD.Vtilde ω * (β * wD.Vtilde ω)) =ᵐ[μ]
          (fun ω => β * (wD.Vtilde ω * wD.Vtilde ω)) := by
      exact Filter.EventuallyEq.of_eq (by
        funext ω
        ring)
    calc
      ∫ ω, wD.Vtilde ω * (β * wD.Vtilde ω) ∂μ = ∫ ω, β * (wD.Vtilde ω * wD.Vtilde ω) ∂μ :=
        integral_congr_ae htmp
      _ = β * ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ := by
        simp [integral_const_mul]
  have h_num_expand :
      ∫ ω, wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω) ∂μ
        = ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ
          - β * ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ := by
    have htmp :
        (fun ω => wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω)) =ᵐ[μ]
          (fun ω => wD.Vtilde ω * wY.Vtilde ω - wD.Vtilde ω * (β * wD.Vtilde ω)) := by
      exact Filter.EventuallyEq.of_eq (by
        funext ω
        ring)
    have h1 : Integrable (fun ω => wD.Vtilde ω * wY.Vtilde ω) μ :=
      wD.Vtilde_memLp.integrable_mul wY.Vtilde_memLp
    have h2 : Integrable (fun ω => wD.Vtilde ω * (β * wD.Vtilde ω)) μ :=
      wD.Vtilde_memLp.integrable_mul (MemLp.const_mul wD.Vtilde_memLp β)
    calc
      ∫ ω, wD.Vtilde ω * (wY.Vtilde ω - β * wD.Vtilde ω) ∂μ =
          ∫ ω, wD.Vtilde ω * wY.Vtilde ω - wD.Vtilde ω * (β * wD.Vtilde ω) ∂μ :=
            integral_congr_ae htmp
      _ = ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ - ∫ ω, wD.Vtilde ω * (β * wD.Vtilde ω) ∂μ :=
        integral_sub h1 h2
      _ = ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ - β * ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ := by
        rw [hβ_mul]
  have hcoeff : β * ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ = ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ := by
    have hzero := h_num_zero
    rw [h_num_expand] at hzero
    linarith
  have hdenom_ne : (∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ) ≠ 0 := hDtilde_pos.ne'
  have hβ_eq : β = (∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ) / (∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ) :=
    (eq_div_iff hdenom_ne).2 hcoeff
  simpa [residualizedCoefficient] using hβ_eq

end Panel
end Causalean
