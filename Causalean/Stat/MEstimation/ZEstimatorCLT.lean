/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Z- / M-estimator asymptotic linearity (parametric inference theorem layer)

Headline asymptotic-linearity theorem for an estimator `θ̂_n` solving an
estimating equation `(1/n) Σ_{i<n} ψ(Z_i; θ̂_n) = 0`.  This is the
linearization core used before applying a separate vector CLT: OLS, MLE,
and IV-2SLS can instantiate it via different choices of `ψ`.

Reference: van der Vaart (1998), §5.6, Theorem 5.41; Newey & McFadden (1994).
Spec: `def:par-smoothness`, `thm:par-z-clt` in
`doc/basic_concepts/Semi-parametric Inference/parametric_inference.tex`.

The proof reduces to `localStochasticExpansion` from
`Causalean/Stat/MEstimation/EmpiricalExpansion.lean` plus a structural rearrangement and
Slutsky-style algebra.  All three `IsAsymLinearVec` fields are
discharged: `mean_zero` (push `−J₀⁻¹` through the Bochner integral using
`identification`), `finite_var` (operator-norm bound via `J₀_inv` +
`finite_var`), and `remainder` (combine `localStochasticExpansion` with
`hMoment`, then bound the rescaled remainder by applying `J₀_inv` and using
the finite-dimensional left-inverse derived from `J₀_inverse`).  The
remaining empirical-process content is exposed as hypotheses upstream,
especially `StochEquicontAt`, rather than proved from a Donsker or chaining
theorem in this file.

This file is split out from `Stat/ZEstimator.lean` (which now contains only
the structure `ZEstimatorRegularity`) to avoid an import cycle: the proof
imports `EmpiricalExpansion.lean`, which itself imports `ZEstimator.lean` for
the structure.
-/

import Causalean.Stat.CLT.AsymptoticLinearityVec
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.MEstimation.EmpiricalExpansion
import Causalean.Stat.Sample
import Causalean.Stat.MEstimation.ZEstimator
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-! # Z-estimator asymptotic linearity

This module proves `zEstimator_clt`, the theorem layer for parametric estimators
that solve empirical estimating equations.  It connects the local stochastic
expansion from `EmpiricalExpansion.lean` to an `IsAsymLinearVec`
influence-function representation with influence function
`fun z => -(reg.J₀_inv (ψ θ₀ z))`; a separate vector CLT can then turn this
asymptotic-linear representation into a normal limit.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Z-estimator asymptotic linearity.**  An estimator that solves the
empirical estimating equation, is consistent at the target parameter, has
root-sample-size stochastic order, and satisfies the stated local
empirical-process condition admits the influence-function representation
obtained by applying the negative inverse Jacobian to the target score.

More concretely, this applies to a sequence of estimators that

* solves the empirical moment `(1/n) Σ ψ(Z_i; θn n ω) = 0` eventually,
* is consistent (`θn → θ₀` in probability),
* satisfies the rate of convergence `‖θn − θ₀‖ = O_p(1/√n)`, and
* `ψ` satisfies the regularity conditions above (notably Jacobian
  invertibility and the `L²`-smoothness modulus),

then `θn` is asymptotically linear at `θ₀` with the Chernozhukov-form
influence function, indexed over the full sample `I n = Finset.range n`.
The formal conclusion is the asymptotic-linear representation; a normal
limit requires applying a separate vector CLT to that representation.

The hypothesis `hRate` (`θn − θ₀ = O_p(1/√n)`) is a separate input rather
than a derivation: classically (van der Vaart 1998 §5.3) it follows from
consistency + non-singular Jacobian, but exposing it as an input keeps the
linearization step modular.  The proof reduces to
`localStochasticExpansion` from `Causalean/Stat/MEstimation/EmpiricalExpansion.lean`,
followed by a structural rearrangement and Slutsky absorption. -/
theorem zEstimator_clt
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - θ₀‖)
      (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec
      (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z)))
      S
      (fun n => Finset.range n) := by
  /-
  Proof outline (van der Vaart 1998 Thm 5.41):

  1. Apply `localStochasticExpansion ψ θ₀ P reg S θn hConsistent hRate` to
     obtain
       (1/√n) ∑ (ψ(θn,Z_i) − ψ(θ₀,Z_i)) − √n · J₀ (θn − θ₀) = o_p(1).
  2. Combine with `hMoment`: `∑ ψ(θn, Z_i) = 0` eventually a.s., so
       (1/√n) ∑ ψ(θ₀, Z_i) + √n · J₀ (θn − θ₀) = o_p(1).
  3. Apply `reg.J₀_inv` (a continuous linear map; in particular bounded), so
       √n · (θn − θ₀) + (√n)⁻¹ • ∑ J₀⁻¹ (ψ(θ₀, Z_i)) = o_p(1).
  4. Rearrange to match `IsAsymLinearVec.remainder` with `ψ_IF` =
     `−J₀⁻¹ · ψ(·;θ₀)`; mean_zero from `reg.identification` + linearity of
     `J₀⁻¹`; finite_var from `reg.finite_var` + boundedness of `J₀⁻¹`.
  -/
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero: `∫ -(reg.J₀_inv (ψ θ₀ z)) dP = 0`.
    rcases reg.psi_int_neighborhood with ⟨δ, hδ_pos, hδ_int⟩
    have hψ₀ : Integrable (ψ θ₀) P := by
      exact hδ_int θ₀ (by simpa using hδ_pos)
    calc
      ∫ x, -(reg.J₀_inv (ψ θ₀ x)) ∂P
          = -(∫ x, reg.J₀_inv (ψ θ₀ x) ∂P) := by
            rw [MeasureTheory.integral_neg]
      _ = -(reg.J₀_inv (∫ x, ψ θ₀ x ∂P)) := by
            rw [ContinuousLinearMap.integral_comp_comm reg.J₀_inv hψ₀]
      _ = 0 := by
            simp [reg.identification]
  · -- finite_var: `Integrable (fun z => ‖-(reg.J₀_inv (ψ θ₀ z))‖²) P`.
    have hbound : ∀ z, ‖-(reg.J₀_inv (ψ θ₀ z))‖^2 ≤
        ‖reg.J₀_inv‖^2 * ‖ψ θ₀ z‖^2 := by
      intro z
      have hnorm : ‖reg.J₀_inv (ψ θ₀ z)‖ ≤ ‖reg.J₀_inv‖ * ‖ψ θ₀ z‖ :=
        reg.J₀_inv.le_opNorm (ψ θ₀ z)
      have hleft_nonneg : 0 ≤ ‖reg.J₀_inv (ψ θ₀ z)‖ := norm_nonneg _
      have hop_nonneg : 0 ≤ ‖reg.J₀_inv‖ := norm_nonneg _
      have hψ_nonneg : 0 ≤ ‖ψ θ₀ z‖ := norm_nonneg _
      calc
        ‖-(reg.J₀_inv (ψ θ₀ z))‖^2 = ‖reg.J₀_inv (ψ θ₀ z)‖^2 := by
          rw [norm_neg]
        _ ≤ ‖reg.J₀_inv‖^2 * ‖ψ θ₀ z‖^2 := by
          nlinarith
    refine (reg.finite_var.const_mul (‖reg.J₀_inv‖^2)).mono' ?_ ?_
    · have hL : Measurable fun z => reg.J₀_inv (ψ θ₀ z) :=
        reg.J₀_inv.continuous.measurable.comp (reg.psi_meas θ₀)
      exact (hL.neg.norm.pow_const 2).aestronglyMeasurable
    · refine Eventually.of_forall ?_
      intro z
      have hz_nonneg : 0 ≤ ‖-(reg.J₀_inv (ψ θ₀ z))‖^2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hz_nonneg] using hbound z
  · -- remainder: combine `localStochasticExpansion` with `hMoment`,
    -- multiply by `reg.J₀_inv` (using `reg.J₀_inverse`), and collect into
    -- `IsAsymLinearVec.remainder` shape.
    have hA :
        IsLittleOp
          (fun n ω =>
            ‖(Real.sqrt (n : ℝ))⁻¹ •
                ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
              - Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀)‖)
          (fun _ => (1 : ℝ)) μ :=
      localStochasticExpansion ψ θ₀ P reg S θn hConsistent hStochEquicont hRate
    let A : ℕ → Ω → E := fun n ω =>
      (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
        - Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀)
    let B : ℕ → Ω → E := fun n ω =>
      Real.sqrt (n : ℝ) • (θn n ω - θ₀)
        - (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, -reg.J₀_inv (ψ θ₀ (S.Z i ω))
    have hA' : IsLittleOp (fun n ω => ‖A n ω‖) (fun _ => (1 : ℝ)) μ := by
      simpa [A] using hA
    have hJ_left : ∀ x : E, reg.J₀_inv (reg.J₀ x) = x := by
      have hJ_surj : Function.Surjective reg.J₀ := fun y =>
        ⟨reg.J₀_inv y, by
          have := congrArg (fun T : E →L[ℝ] E => T y) reg.J₀_inverse
          simpa using this⟩
      have hJ_inj : Function.Injective reg.J₀ := by
        exact (LinearMap.injective_iff_surjective (f := (reg.J₀ : E →ₗ[ℝ] E))).mpr hJ_surj
      intro x
      apply hJ_inj
      have := congrArg (fun T : E →L[ℝ] E => T (reg.J₀ x)) reg.J₀_inverse
      simpa using this
    have hJInvA : IsLittleOp (fun n ω => ‖reg.J₀_inv (A n ω)‖) (fun _ => (1 : ℝ)) μ := by
      intro ε hε
      let C : ℝ := ‖reg.J₀_inv‖ + 1
      have hC_pos : 0 < C := by
        have hnonneg : 0 ≤ ‖reg.J₀_inv‖ := norm_nonneg _
        dsimp [C]
        linarith
      have hAε := hA' (ε / C) (div_pos hε hC_pos)
      rw [ENNReal.tendsto_nhds_zero] at hAε ⊢
      intro δ hδ
      exact (hAε δ hδ).mono fun n hn => by
        refine (measure_mono ?_).trans hn
        intro ω hω
        have hbound0 : ‖reg.J₀_inv (A n ω)‖ ≤ ‖reg.J₀_inv‖ * ‖A n ω‖ :=
          reg.J₀_inv.le_opNorm (A n ω)
        have hC_le : ‖reg.J₀_inv‖ ≤ C := by
          dsimp [C]
          linarith [norm_nonneg reg.J₀_inv]
        have hbound : ‖reg.J₀_inv (A n ω)‖ ≤ C * ‖A n ω‖ :=
          le_trans hbound0 (mul_le_mul_of_nonneg_right hC_le (norm_nonneg _))
        have hω' : ε < ‖reg.J₀_inv (A n ω)‖ := by
          simpa [abs_of_nonneg (norm_nonneg _)] using hω
        have hmul : ε < C * ‖A n ω‖ := lt_of_lt_of_le hω' hbound
        have hdiv : ε / C < ‖A n ω‖ :=
          (div_lt_iff₀ hC_pos).2 (by simpa [mul_comm] using hmul)
        simpa [abs_of_nonneg (norm_nonneg _)] using hdiv
    have hB : IsLittleOp (fun n ω => ‖B n ω‖) (fun _ => (1 : ℝ)) μ := by
      intro ε hε
      have hJ := hJInvA ε hε
      rw [ENNReal.tendsto_nhds_zero] at hJ ⊢
      intro δ hδ
      filter_upwards [hMoment, hJ δ hδ] with n hzero_ae hn
      have hmeasure :
          μ {ω | ε * (fun _ => (1 : ℝ)) n < |‖B n ω‖|} ≤
            μ {ω | ε * (fun _ => (1 : ℝ)) n < |‖reg.J₀_inv (A n ω)‖|} := by
        apply MeasureTheory.measure_mono_ae
        exact hzero_ae.mono fun ω hzero hω => by
          have hsumdiff :
              (∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))) =
                -∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω) := by
            calc
              (∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))) =
                  (∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)) -
                    ∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω) := by
                    rw [Finset.sum_sub_distrib]
              _ = -∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω) := by
                    simp [hzero]
          have hnormeq : ‖B n ω‖ = ‖reg.J₀_inv (A n ω)‖ := by
            calc
              ‖B n ω‖ =
                  ‖Real.sqrt (n : ℝ) • (θn n ω - θ₀)
                    - (Real.sqrt (n : ℝ))⁻¹ •
                      ∑ i ∈ Finset.range n, -reg.J₀_inv (ψ θ₀ (S.Z i ω))‖ := by
                rfl
              _ = ‖-reg.J₀_inv
                    ((Real.sqrt (n : ℝ))⁻¹ •
                        ∑ i ∈ Finset.range n,
                          (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
                      - Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀))‖ := by
                rw [hsumdiff]
                simp [map_sum, hJ_left, sub_eq_add_neg,
                  add_comm, add_left_comm, add_assoc]
              _ = ‖-reg.J₀_inv (A n ω)‖ := by
                simp [A, map_sum, hJ_left, sub_eq_add_neg,
                  add_comm, add_left_comm, add_assoc]
              _ = ‖reg.J₀_inv (A n ω)‖ := by
                rw [norm_neg]
          have hω' : ε < ‖B n ω‖ := by
            simpa [abs_of_nonneg (norm_nonneg _)] using hω
          have hω'' : ε < ‖reg.J₀_inv (A n ω)‖ := by
            rwa [hnormeq] at hω'
          simpa [abs_of_nonneg (norm_nonneg _)] using hω''
      exact by simpa using hmeasure.trans hn
    simpa [B, Finset.card_range] using hB

end Causalean.Stat
