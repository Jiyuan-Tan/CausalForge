/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The order-2 U-statistic CLT as a specialization of the order-`m` CLT

The fixed-order theory (`OrderM.CLT`) subsumes the bespoke order-2 CLT of
`UStatistic.Hajek` / `UStatistic.Variance`.  This file makes that precise: it
records the `m = 2` bridge identities relating the order-`m` objects for the
paired kernel `pairKernel h` (`z ↦ h (z 0) (z 1)`) to the order-2 objects
(`uMean`, `uProj`, `uDegen`), and then re-derives the symmetric-kernel order-2
CLT `√n (Uₙ − θ) ⇒ N(0, 4 ζ₁)` from `uStatisticOrder_clt_of_regular`.

The bridge (for a symmetric kernel `h`):

* `uMeanOrder (pairKernel h) P = uMean h P`
* `uProjOrderAt j (pairKernel h) P = uProj h P` for each `j : Fin 2`
* `uInfluenceOrder (pairKernel h) P = fun x => 2 · uProj h P x`
* `uDegenOrder (pairKernel h) P z = uDegen h P (z 0) (z 1)`
* `uStatisticOrder S (pairKernel h) n = uStatistic S h n` (already
  `uStatisticOrder_two_eq_uStatistic`).

The `Fin 2 → X` product law is bridged to `P ×ₘ P` via the finite-product/`piFinTwo`
measure equivalence.
-/

import Causalean.Stat.UStatistic.OrderM.CLT

/-!
Specializes the fixed-order U-statistic CLT to the order-2 theory.

The bridge sends a two-argument kernel `h : X → X → ℝ` to `pairKernel h :
(Fin 2 → X) → ℝ` and proves that the order-`m` mean, projections, influence
function, degenerate residual, and statistic agree with their order-2
counterparts.  The final theorem, `uStatistic_clt_of_symmetric_via_orderM`,
derives the classical symmetric-kernel order-2 CLT from
`uStatisticOrder_clt_of_regular`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## `m = 2` bridge identities -/

section Bridge

variable [IsProbabilityMeasure P] {h : X → X → ℝ}

/-- The order-`2` population mean of `pairKernel h` is the order-2 mean of `h`.
Requires product-integrability of `h` so that the joint integral over
`Fin 2 → X` agrees (via Fubini) with the iterated integral defining `uMean`. -/
theorem uMeanOrder_pairKernel
    (hh_int : Integrable (fun p : X × X => h p.1 p.2) (P.prod P)) :
    uMeanOrder (pairKernel h) P = uMean h P := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => X)
  have hmp : MeasurePreserving e
      (Measure.pi fun _ : Fin 2 => P) (P.prod P) := by
    simpa [e] using (measurePreserving_piFinTwo (fun _ : Fin 2 => P))
  have hsplit :
      ∫ z : Fin 2 → X, h (z 0) (z 1) ∂(Measure.pi fun _ : Fin 2 => P)
        = ∫ p : X × X, h p.1 p.2 ∂(P.prod P) := by
    simpa [e] using hmp.integral_comp' (fun p : X × X => h p.1 p.2)
  unfold uMeanOrder pairKernel uMean
  rw [hsplit, integral_prod _ hh_int]

/-- Each coordinate first projection of `pairKernel h` equals the order-2 first
projection of `h`, for a symmetric kernel.  (For `j = 0` no symmetry is needed;
for `j = 1` it is used to swap the integration coordinate.) -/
theorem uProjOrderAt_pairKernel_of_symm (hsymm : ∀ x y, h x y = h y x)
    (hh_int : Integrable (fun p : X × X => h p.1 p.2) (P.prod P))
    (hrow : ∀ x, Integrable (fun y => h x y) P) (j : Fin 2) :
    uProjOrderAt j (pairKernel h) P = uProj h P := by
  funext x
  fin_cases j
  · have htail :
        (∫ tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X,
            pairKernel h (insertCoord (0 : Fin 2) x tail)
              ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P))
          = ∫ y, h x y ∂P := by
      let a : {k : Fin 2 // ¬ k = (0 : Fin 2)} := ⟨1, by norm_num⟩
      have h_eval := integral_pi_eval_eq (P := P) (i := a) (f := fun y => h x y)
        (hrow x)
      have hfun :
          (fun tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X =>
            pairKernel h (insertCoord (0 : Fin 2) x tail))
            = fun tail => h x (tail a) := by
        funext tail
        simp [pairKernel, insertCoord, a]
      rw [hfun, h_eval]
    unfold uProjOrderAt uProj
    change
      (∫ tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X,
          pairKernel h (insertCoord (0 : Fin 2) x tail)
            ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P))
        - uMeanOrder (pairKernel h) P
        = (∫ y, h x y ∂P) - uMean h P
    rw [htail, uMeanOrder_pairKernel (P := P) (h := h) hh_int]
  · have hcol : Integrable (fun y => h y x) P := by
      have hfun : (fun y => h y x) = fun y => h x y := by
        funext y
        exact hsymm y x
      rw [hfun]
      exact hrow x
    have htail :
        (∫ tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X,
            pairKernel h (insertCoord (1 : Fin 2) x tail)
              ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P))
          = ∫ y, h x y ∂P := by
      let a : {k : Fin 2 // ¬ k = (1 : Fin 2)} := ⟨0, by norm_num⟩
      have h_eval := integral_pi_eval_eq (P := P) (i := a) (f := fun y => h y x)
        hcol
      have hswap : (∫ y, h y x ∂P) = ∫ y, h x y ∂P := by
        congr 1
        funext y
        exact hsymm y x
      have hfun :
          (fun tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X =>
            pairKernel h (insertCoord (1 : Fin 2) x tail))
            = fun tail => h (tail a) x := by
        funext tail
        simp [pairKernel, insertCoord, a]
      rw [hfun, h_eval, hswap]
    unfold uProjOrderAt uProj
    change
      (∫ tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X,
          pairKernel h (insertCoord (1 : Fin 2) x tail)
            ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P))
        - uMeanOrder (pairKernel h) P
        = (∫ y, h x y ∂P) - uMean h P
    rw [htail, uMeanOrder_pairKernel (P := P) (h := h) hh_int]

/-- The order-`2` influence function of `pairKernel h` is `2 · h₁`, matching the
order-2 CLT influence function `ψ = 2 · uProj h P`. -/
theorem uInfluenceOrder_pairKernel_of_symm (hsymm : ∀ x y, h x y = h y x)
    (hh_int : Integrable (fun p : X × X => h p.1 p.2) (P.prod P))
    (hrow : ∀ x, Integrable (fun y => h x y) P) :
    uInfluenceOrder (pairKernel h) P = fun x => 2 * uProj h P x := by
  simpa using
    (uInfluenceOrder_eq_card_mul_of_common_projection
      (P := P) (h := pairKernel h) (φ := uProj h P)
      (fun j x => congrFun
        (uProjOrderAt_pairKernel_of_symm (P := P) (h := h) hsymm hh_int hrow j) x))

/-- The order-`2` degenerate residual of `pairKernel h` is the order-2 degenerate
kernel `uDegen h P`, evaluated at the two coordinates. -/
theorem uDegenOrder_pairKernel_of_symm (hsymm : ∀ x y, h x y = h y x)
    (hh_int : Integrable (fun p : X × X => h p.1 p.2) (P.prod P))
    (hrow : ∀ x, Integrable (fun y => h x y) P) :
    uDegenOrder (pairKernel h) P = fun z => uDegen h P (z 0) (z 1) := by
  funext z
  have hproj0 :
      uProjOrderAt (0 : Fin 2) (pairKernel h) P (z 0) = uProj h P (z 0) :=
    congrFun (uProjOrderAt_pairKernel_of_symm (P := P) (h := h) hsymm hh_int hrow 0)
      (z 0)
  have hproj1 :
      uProjOrderAt (1 : Fin 2) (pairKernel h) P (z 1) = uProj h P (z 1) :=
    congrFun (uProjOrderAt_pairKernel_of_symm (P := P) (h := h) hsymm hh_int hrow 1)
      (z 1)
  simp [uDegenOrder, uDegen, pairKernel, uMeanOrder_pairKernel (P := P) (h := h) hh_int,
    Fin.sum_univ_two, hproj0, hproj1]
  ring

end Bridge

/-! ## The order-2 CLT via the order-`m` result -/

/-- **Order-2 U-statistic CLT, derived from the fixed-order-`m` CLT.**  For a
symmetric, square-integrable kernel `h` with finite first-projection variance
`ζ₁ = ∫ h₁² dP`, the order-2 U-statistic is `√n`-asymptotically normal,
`√n (Uₙ − θ) ⇒ N(0, ∫ (2 h₁)² dP) = N(0, 4 ζ₁)`.

This has the same statement as `uStatistic_clt_of_symmetric`, but its proof runs
through `uStatisticOrder_clt_of_regular` (order `m = 2`, kernel `pairKernel h`)
using the bridge identities above — demonstrating that the general fixed-order
theory subsumes the order-2 result. -/
theorem uStatistic_clt_of_symmetric_via_orderM
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (h : X → X → ℝ)
    (hsymm : ∀ x y, h x y = h y x)
    (hmeas : Measurable fun p : X × X => h p.1 p.2)
    (hL2 : Integrable (fun p : X × X => (uDegen h P p.1 p.2) ^ 2) (P.prod P))
    (hint : Integrable (fun x => ∫ y, h x y ∂P) P)
    (hrow : ∀ x, Integrable (fun y => h x y) P)
    (hproj_sq : Integrable (fun x => (uProj h P x) ^ 2) P)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (uStatistic S h) (uMean h P)
        (fun m => Finset.range m) n) μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S (fun x => 2 * uProj h P x)
        (fun m => Finset.range m) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator (uStatistic S h) (uMean h P)
        (fun m => Finset.range m))
      (gaussianMeasure 0 (∫ x, ((fun x => 2 * uProj h P x) x) ^ 2 ∂P))
      μ
      hθn_meas := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => X)
  have hmp : MeasurePreserving e
      (Measure.pi fun _ : Fin 2 => P) (P.prod P) := by
    simpa [e] using (measurePreserving_piFinTwo (fun _ : Fin 2 => P))
  have hproj_meas : Measurable (uProj h P) := by
    have hsm : StronglyMeasurable fun x => ∫ y, h x y ∂P :=
      hmeas.stronglyMeasurable.integral_prod_right'
    exact hsm.measurable.sub measurable_const
  have hdeg_meas_prod : Measurable (fun p : X × X => uDegen h P p.1 p.2) := by
    have h1 : Measurable fun p : X × X => uProj h P p.1 := hproj_meas.comp measurable_fst
    have h2 : Measurable fun p : X × X => uProj h P p.2 := hproj_meas.comp measurable_snd
    simp only [uDegen]
    exact ((hmeas.sub measurable_const).sub h1).sub h2
  have hproj_int : Integrable (uProj h P) P := uProj_integrable hint
  have hdegen_int : Integrable (fun p : X × X => uDegen h P p.1 p.2) (P.prod P) :=
    ((memLp_two_iff_integrable_sq hdeg_meas_prod.aestronglyMeasurable).mpr hL2).integrable
      (by norm_num)
  have hh_int : Integrable (fun p : X × X => h p.1 p.2) (P.prod P) := by
    have hsum_int : Integrable
        (fun p : X × X =>
          uMean h P + uProj h P p.1 + uProj h P p.2 + uDegen h P p.1 p.2)
        (P.prod P) := by
      have hfst : Integrable (fun p : X × X => uProj h P p.1) (P.prod P) :=
        hproj_int.comp_fst P
      have hsnd : Integrable (fun p : X × X => uProj h P p.2) (P.prod P) :=
        hproj_int.comp_snd P
      simpa [add_assoc] using
        (((integrable_const (uMean h P)).add hfst).add hsnd).add hdegen_int
    have hfun :
        (fun p : X × X =>
          uMean h P + uProj h P p.1 + uProj h P p.2 + uDegen h P p.1 p.2)
          = fun p => h p.1 p.2 := by
      funext p
      exact (hoeffding_decomp h P p.1 p.2).symm
    simpa [hfun] using hsum_int
  have hmean_bridge : uMeanOrder (pairKernel h) P = uMean h P :=
    uMeanOrder_pairKernel (P := P) (h := h) hh_int
  have hproj_bridge :
      ∀ j : Fin 2, uProjOrderAt j (pairKernel h) P = uProj h P :=
    fun j => uProjOrderAt_pairKernel_of_symm (P := P) (h := h) hsymm hh_int hrow j
  have hψ_bridge : uInfluenceOrder (pairKernel h) P = fun x => 2 * uProj h P x :=
    uInfluenceOrder_pairKernel_of_symm (P := P) (h := h) hsymm hh_int hrow
  have hstat_bridge : uStatisticOrder S (pairKernel h) = uStatistic S h := by
    funext n
    exact uStatisticOrder_two_eq_uStatistic S h n
  have hdeg_bridge :
      uDegenOrder (pairKernel h) P = fun z => uDegen h P (z 0) (z 1) :=
    uDegenOrder_pairKernel_of_symm (P := P) (h := h) hsymm hh_int hrow
  have hmeas' : Measurable (uDegenOrder (pairKernel h) P) := by
    have hraw : Measurable (fun z : Fin 2 → X => uDegen h P (z 0) (z 1)) := by
      simpa [e] using hdeg_meas_prod.comp e.measurable
    simpa [hdeg_bridge] using hraw
  have hL2' : Integrable (fun z => (uDegenOrder (pairKernel h) P z) ^ 2)
      (Measure.pi fun _ : Fin 2 => P) := by
    have hraw : Integrable (fun z : Fin 2 → X => (uDegen h P (z 0) (z 1)) ^ 2)
        (Measure.pi fun _ : Fin 2 => P) := by
      simpa [e] using hmp.integrable_comp_of_integrable hL2
    simpa [hdeg_bridge] using hraw
  have hslice_int' : ∀ j : Fin 2, Integrable
      (fun x => ∫ tail : ({k : Fin 2 // k ≠ j}) → X,
        pairKernel h (insertCoord j x tail)
          ∂(Measure.pi fun _ : {k : Fin 2 // k ≠ j} => P)) P := by
    intro j
    fin_cases j
    · change Integrable
        (fun x => ∫ tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X,
          pairKernel h (insertCoord (0 : Fin 2) x tail)
            ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P)) P
      have hfun :
          (fun x => ∫ tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X,
            pairKernel h (insertCoord (0 : Fin 2) x tail)
              ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P))
            = fun x => ∫ y, h x y ∂P := by
        funext x
        let a : {k : Fin 2 // ¬ k = (0 : Fin 2)} := ⟨1, by norm_num⟩
        have h_eval := integral_pi_eval_eq (P := P) (i := a) (f := fun y => h x y)
          (hrow x)
        have htail :
            (fun tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X =>
              pairKernel h (insertCoord (0 : Fin 2) x tail))
              = fun tail => h x (tail a) := by
          funext tail
          simp [pairKernel, insertCoord, a]
        rw [htail, h_eval]
      simpa [hfun] using hint
    · change Integrable
        (fun x => ∫ tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X,
          pairKernel h (insertCoord (1 : Fin 2) x tail)
            ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P)) P
      have hfun :
          (fun x => ∫ tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X,
            pairKernel h (insertCoord (1 : Fin 2) x tail)
              ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P))
            = fun x => ∫ y, h x y ∂P := by
        funext x
        let a : {k : Fin 2 // ¬ k = (1 : Fin 2)} := ⟨0, by norm_num⟩
        have hcol : Integrable (fun y => h y x) P := by
          have hfun_col : (fun y => h y x) = fun y => h x y := by
            funext y
            exact hsymm y x
          rw [hfun_col]
          exact hrow x
        have h_eval := integral_pi_eval_eq (P := P) (i := a) (f := fun y => h y x)
          hcol
        have hswap : (∫ y, h y x ∂P) = ∫ y, h x y ∂P := by
          congr 1
          funext y
          exact hsymm y x
        have htail :
            (fun tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X =>
              pairKernel h (insertCoord (1 : Fin 2) x tail))
              = fun tail => h (tail a) x := by
          funext tail
          simp [pairKernel, insertCoord, a]
        rw [htail, h_eval, hswap]
      simpa [hfun] using hint
  have hmean' : ∀ j : Fin 2,
      ∫ x, (∫ tail : ({k : Fin 2 // k ≠ j}) → X,
        pairKernel h (insertCoord j x tail)
          ∂(Measure.pi fun _ : {k : Fin 2 // k ≠ j} => P)) ∂P
        = uMeanOrder (pairKernel h) P := by
    intro j
    fin_cases j
    · change
        ∫ x, (∫ tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X,
          pairKernel h (insertCoord (0 : Fin 2) x tail)
            ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P)) ∂P
          = uMeanOrder (pairKernel h) P
      have hfun :
          (fun x => ∫ tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X,
            pairKernel h (insertCoord (0 : Fin 2) x tail)
              ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P))
            = fun x => ∫ y, h x y ∂P := by
        funext x
        let a : {k : Fin 2 // ¬ k = (0 : Fin 2)} := ⟨1, by norm_num⟩
        have h_eval := integral_pi_eval_eq (P := P) (i := a) (f := fun y => h x y)
          (hrow x)
        have htail :
            (fun tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X =>
              pairKernel h (insertCoord (0 : Fin 2) x tail))
              = fun tail => h x (tail a) := by
          funext tail
          simp [pairKernel, insertCoord, a]
        rw [htail, h_eval]
      rw [hfun, hmean_bridge]
      rfl
    · change
        ∫ x, (∫ tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X,
          pairKernel h (insertCoord (1 : Fin 2) x tail)
            ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P)) ∂P
          = uMeanOrder (pairKernel h) P
      have hfun :
          (fun x => ∫ tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X,
            pairKernel h (insertCoord (1 : Fin 2) x tail)
              ∂(Measure.pi fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P))
            = fun x => ∫ y, h x y ∂P := by
        funext x
        let a : {k : Fin 2 // ¬ k = (1 : Fin 2)} := ⟨0, by norm_num⟩
        have hcol : Integrable (fun y => h y x) P := by
          have hfun_col : (fun y => h y x) = fun y => h x y := by
            funext y
            exact hsymm y x
          rw [hfun_col]
          exact hrow x
        have h_eval := integral_pi_eval_eq (P := P) (i := a) (f := fun y => h y x)
          hcol
        have hswap : (∫ y, h y x ∂P) = ∫ y, h x y ∂P := by
          congr 1
          funext y
          exact hsymm y x
        have htail :
            (fun tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X =>
              pairKernel h (insertCoord (1 : Fin 2) x tail))
              = fun tail => h (tail a) x := by
          funext tail
          simp [pairKernel, insertCoord, a]
        rw [htail, h_eval, hswap]
      rw [hfun, hmean_bridge]
      rfl
  have hrow' : ∀ (j : Fin 2) (x : X),
      Integrable (fun tail : ({k : Fin 2 // k ≠ j}) → X =>
        pairKernel h (insertCoord j x tail))
        (Measure.pi fun _ : {k : Fin 2 // k ≠ j} => P) := by
    intro j x
    fin_cases j
    · change Integrable
        (fun tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X =>
          pairKernel h (insertCoord (0 : Fin 2) x tail))
        (Measure.pi fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P)
      let a : {k : Fin 2 // ¬ k = (0 : Fin 2)} := ⟨1, by norm_num⟩
      have htail :
          (fun tail : ({k : Fin 2 // ¬ k = (0 : Fin 2)}) → X =>
            pairKernel h (insertCoord (0 : Fin 2) x tail))
            = fun tail => h x (tail a) := by
        funext tail
        simp [pairKernel, insertCoord, a]
      rw [htail]
      have hmp_eval := measurePreserving_eval
        (fun _ : {k : Fin 2 // ¬ k = (0 : Fin 2)} => P) a
      simpa [Function.comp_def] using hmp_eval.integrable_comp_of_integrable (hrow x)
    · change Integrable
        (fun tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X =>
          pairKernel h (insertCoord (1 : Fin 2) x tail))
        (Measure.pi fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P)
      let a : {k : Fin 2 // ¬ k = (1 : Fin 2)} := ⟨0, by norm_num⟩
      have hcol : Integrable (fun y => h y x) P := by
        have hfun_col : (fun y => h y x) = fun y => h x y := by
          funext y
          exact hsymm y x
        rw [hfun_col]
        exact hrow x
      have htail :
          (fun tail : ({k : Fin 2 // ¬ k = (1 : Fin 2)}) → X =>
            pairKernel h (insertCoord (1 : Fin 2) x tail))
            = fun tail => h (tail a) x := by
        funext tail
        simp [pairKernel, insertCoord, a]
      rw [htail]
      have hmp_eval := measurePreserving_eval
        (fun _ : {k : Fin 2 // ¬ k = (1 : Fin 2)} => P) a
      simpa [Function.comp_def] using hmp_eval.integrable_comp_of_integrable hcol
  have hψ_meas' : Measurable (uInfluenceOrder (pairKernel h) P) := by
    simpa [hψ_bridge] using (hproj_meas.const_mul 2)
  have hψ_mean' : ∫ x, uInfluenceOrder (pairKernel h) P x ∂P = 0 := by
    rw [hψ_bridge]
    rw [integral_const_mul]
    rw [uProj_integral_eq_zero hint, mul_zero]
  have hψ_sq' : Integrable (fun x => (uInfluenceOrder (pairKernel h) P x) ^ 2) P := by
    have hscaled : Integrable (fun x => (4 : ℝ) * (uProj h P x) ^ 2) P :=
      hproj_sq.const_mul 4
    have hfun :
        (fun x => (uInfluenceOrder (pairKernel h) P x) ^ 2)
          = fun x => (4 : ℝ) * (uProj h P x) ^ 2 := by
      funext x
      rw [hψ_bridge]
      ring
    simpa [hfun] using hscaled
  have hθn_meas' : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S (pairKernel h))
        (uMeanOrder (pairKernel h) P) (fun r => Finset.range r) n) μ := by
    intro n
    simpa [hstat_bridge, hmean_bridge] using hθn_meas n
  have hSum_meas' : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S (uInfluenceOrder (pairKernel h) P)
        (fun r => Finset.range r) n) μ := by
    intro n
    simpa [hψ_bridge] using hSum_meas n
  have hclt := uStatisticOrder_clt_of_regular S (pairKernel h)
    hmeas' hL2' hslice_int' hmean' hrow' hψ_meas' hψ_mean' hψ_sq'
    hθn_meas' hSum_meas'
  simpa [hstat_bridge, hmean_bridge, hψ_bridge] using hclt

end Causalean.Stat
