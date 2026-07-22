/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic

/-! # Cited conditional upper-risk comparator (Bonvini–Kennedy 2022)

This supportive cited leaf records the conditional risk implication in
arXiv:2207.11825v1, Section 3.4, Theorem 1 and Remarks 7–8/Figure 1
(Theorem 3.1 in v2). It deliberately does not state a class-level minimax bound.
-/

namespace CausalSmith.Stat.DoseResponseMinimax

open Filter MeasureTheory Set
open scoped BigOperators

/-- `u ≲ v` eventually, with the positive constant made explicit. -/
def EventuallyAtMostConstant (u v : ℕ → ℝ) : Prop :=
  ∃ C, 0 < C ∧ ∀ᶠ n : ℕ in atTop, u n ≤ C * v n

/-- Two-sided eventual comparison, used for the source's `≍` tuning relations. -/
def EventuallyComparable (u v : ℕ → ℝ) : Prop :=
  EventuallyAtMostConstant u v ∧ EventuallyAtMostConstant v u

/-- Inputs from which the Bonvini–Kennedy second-order estimator used in the
Figure 1 `rho_n` comparison is constructed. The nuisance estimates are indexed by
training-sample size. The estimator and every risk/error quantity below are
definitions computed from these inputs; no influence kernel is a free field. -/
structure BKHOIFEstimatorSpec (d : ℕ) where
  law : DoseLaw d
  targetDose : ℝ
  muHat : ℕ → ℝ → (Fin d → ℝ) → ℝ
  piHat : ℕ → ℝ → (Fin d → ℝ) → ℝ
  jointDensityHat : ℕ → ℝ → (Fin d → ℝ) → ℝ
  kernel : ℝ → ℝ
  bandwidth : ℕ → ℝ
  projectionDimension : ℕ → ℝ
  projectionKernel : ℕ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  projectionHatKernel : ℕ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ

/-- The localized kernel `K_ht` appearing in the source theorem. -/
noncomputable def bkKernelAt {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) (a : ℝ) : ℝ :=
  (E.bandwidth n)⁻¹ * E.kernel ((a - E.targetDose) / E.bandwidth n)

/-- The source's first approximate influence function: the localized inverse-density
residual score plus the plug-in regression value at the target dose. -/
noncomputable def bkFirstApproxInfluence {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) (O : DoseObs d) : ℝ :=
  E.muHat n E.targetDose O.X +
    bkKernelAt E n O.A * (O.Y - E.muHat n O.A O.X) / E.piHat n O.A O.X

/-- The source's first residual factor `f₁`. -/
noncomputable def bkResidualOne {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) (O : DoseObs d) : ℝ :=
  bkKernelAt E n O.A * (O.Y - E.muHat n O.A O.X)

/-- The source's inverse-density residual factor `f₂`. -/
noncomputable def bkResidualTwo {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) (O : DoseObs d) : ℝ :=
  bkKernelAt E n O.A / E.piHat n O.A O.X - 1

/-- The second approximate influence kernel from Section 3.3:
`-f₁(Z₁) Π_hat(X₁,X₂) f₂(Z₂)`. It is definitionally pinned to the
estimated projection kernel and nuisance estimates. -/
noncomputable def bkSecondApproxInfluence {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) (z : Fin 2 → DoseObs d) : ℝ :=
  -bkResidualOne E n (z 0) * E.projectionHatKernel n (z 0).X (z 1).X *
    bkResidualTwo E n (z 1)

/-- The specified second-order estimator used for the source's Figure 1 rate:
the empirical mean of the first approximate influence function plus the order-two
U-statistic. The injection sum counts each unordered pair `2!` times, so the
normalization is exactly `2! * choose n 2`, not merely `choose n 2`. -/
noncomputable def bkSpecifiedHOIFEstimator {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) (sample : Fin n → DoseObs d) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, bkFirstApproxInfluence E n (sample i) +
    ((Nat.factorial 2 * Nat.choose n 2 : ℕ) : ℝ)⁻¹ *
      ∑ t : Fin 2 ↪ Fin n, bkSecondApproxInfluence E n (fun i => sample (t i))

/-- Conditional MSE of the specified estimator, conditional on its nuisance-training
sample, under the actual i.i.d. evaluation-sample law. -/
noncomputable def bkConditionalMSE {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) : ℝ :=
  ∫ sample, (bkSpecifiedHOIFEstimator E n sample -
      thetaFunctional E.law E.targetDose) ^ 2
    ∂(Measure.pi fun _ : Fin n => E.law.dataMeasure)

/-- Lebesgue `L²` norm on the covariate cube. -/
noncomputable def bkL2NormCube {d : ℕ} (f : (Fin d → ℝ) → ℝ) : ℝ :=
  Real.sqrt (∫ x in cube d, (f x) ^ 2)

/-- Application of the source's true finite-dimensional projection kernel. -/
noncomputable def bkProject {d : ℕ} (E : BKHOIFEstimatorSpec d)
    (n : ℕ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ z in cube d, E.projectionKernel n x z * f z

/-- Actual outcome-regression nuisance error `‖v‖_g`. -/
noncomputable def bkVNorm {d : ℕ} (E : BKHOIFEstimatorSpec d) (n : ℕ) : ℝ :=
  bkL2NormCube (fun x => E.muHat n E.targetDose x - E.law.mu E.targetDose x)

/-- Actual reciprocal-treatment-density nuisance error `‖q‖_g`. -/
noncomputable def bkQNorm {d : ℕ} (E : BKHOIFEstimatorSpec d) (n : ℕ) : ℝ :=
  bkL2NormCube (fun x =>
    (E.piHat n E.targetDose x)⁻¹ - (E.law.pi E.targetDose x)⁻¹)

/-- Product of the actual projection-residual norms of the two nuisance errors. -/
noncomputable def bkProjectionProductError {d : ℕ}
    (E : BKHOIFEstimatorSpec d) (n : ℕ) : ℝ :=
  let v := fun x => E.muHat n E.targetDose x - E.law.mu E.targetDose x
  let q := fun x =>
    (E.piHat n E.targetDose x)⁻¹ - (E.law.pi E.targetDose x)⁻¹
  bkL2NormCube (fun x => v x - bkProject E n v x) *
    bkL2NormCube (fun x => q x - bkProject E n q x)

/-- Actual uniform error of the estimated joint density at the target dose. -/
noncomputable def bkDensitySupError {d : ℕ}
    (E : BKHOIFEstimatorSpec d) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ cube d,
    r = |E.jointDensityHat n E.targetDose x -
      E.law.pi E.targetDose x * E.law.px x|}

/-- Assumptions 1–2 and Conditions 1–4 of Bonvini–Kennedy Theorem 1/3.1,
spelled out on the source estimator inputs. -/
structure BKTheorem31Conditions {d : ℕ} (alpha beta : ℝ)
    (E : BKHOIFEstimatorSpec d) : Prop where
  evaluationLaw : IsProbabilityMeasure E.law.dataMeasure
  outcomeRegressionLaw : MuIsRegression E.law
  covariateDensityLaw : PxIsXDensity E.law
  treatmentDensityLaw : PiIsCondTreatmentDensity E.law
  positivity : ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
    ∀ n a x, lo ≤ E.law.pi a x ∧ E.law.pi a x ≤ hi ∧
      lo ≤ E.piHat n a x ∧ E.piHat n a x ≤ hi
  boundedness : ∃ B : ℝ, 0 < B ∧
    (∀ᵐ O ∂E.law.dataMeasure, |O.Y| ≤ B ∧ |O.A| ≤ B) ∧
    ∀ n a x, |E.muHat n a x| ≤ B
  treatmentSmoothness :
    (∀ x, HolderBall1D (fun a => E.law.mu a x) alpha 1 univ) ∧
    (∀ n x, HolderBall1D (fun a => E.muHat n a x) alpha 1 univ) ∧
    (∀ x, HolderBall1D (fun a => E.law.pi a x) beta 1 univ) ∧
    (∀ n x, HolderBall1D (fun a => E.piHat n a x) beta 1 univ)
  kernelCondition : ∃ Kmax glo ghi : ℝ,
    0 < Kmax ∧ 0 < glo ∧ glo ≤ ghi ∧
    (∀ u, |E.kernel u| ≤ Kmax) ∧
    Function.support E.kernel ⊆ Set.Icc (-1 : ℝ) 1 ∧
    (∫ u, E.kernel u) = 1 ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ ⌈alpha⌉₊ - 1 →
      (∫ u, (u ^ j) * E.kernel u) = 0) ∧
    (∀ n, 0 < E.bandwidth n) ∧
    (∀ n, (∫ a, bkKernelAt E n a) = 1) ∧
    ∀ n x, glo ≤ ∫ a, bkKernelAt E n a * (E.law.pi a x * E.law.px x) ∧
      (∫ a, bkKernelAt E n a * (E.law.pi a x * E.law.px x)) ≤ ghi
  projectionDiagonal : ∃ Cpi : ℝ, 0 < Cpi ∧
    ∀ n x, E.projectionKernel n x x ≤ Cpi * E.projectionDimension n ∧
      E.projectionHatKernel n x x ≤ Cpi * E.projectionDimension n
  localizedDensityRatio : ∃ rlo rhi : ℝ, 0 < rlo ∧ rlo ≤ rhi ∧
    ∀ n x,
      rlo ≤
        (∫ a, bkKernelAt E n a * (E.law.pi a x * E.law.px x)) /
          (∫ a, bkKernelAt E n a * E.jointDensityHat n a x) ∧
      (∫ a, bkKernelAt E n a * (E.law.pi a x * E.law.px x)) /
          (∫ a, bkKernelAt E n a * E.jointDensityHat n a x) ≤ rhi

/-- The source's explicit post-theorem rate specialization. Every error sequence is
the actual quantity defined from `E`; no premise can be satisfied by choosing an
unrelated favorable sequence. -/
structure BKRateSpecialization {d : ℕ} (alpha beta s gamma₁ gamma₂ : ℝ)
    (E : BKHOIFEstimatorSpec d) : Prop where
  positiveParameters : 0 < d ∧ 0 < alpha ∧ 0 < beta ∧ 0 < s
  treatmentOrder : alpha ≤ beta
  equalCovariateSmoothness : gamma₁ = s ∧ gamma₂ = s ∧
    ∃ Bx : ℝ, 0 < Bx ∧
      (∀ a, HolderBallND (fun x => E.law.mu a x) s Bx (cube d)) ∧
      (∀ n a, HolderBallND (fun x => E.muHat n a x) s Bx (cube d)) ∧
      (∀ a, HolderBallND (fun x => E.law.pi a x) s Bx (cube d)) ∧
      ∀ n a, HolderBallND (fun x => E.piHat n a x) s Bx (cube d)
  projectionApproximation : EventuallyAtMostConstant (bkProjectionProductError E)
    (fun n => (E.projectionDimension n) ^ (-(gamma₁ + gamma₂) / (d : ℝ)))
  smoothTuning : d ≤ 4 * s →
    EventuallyComparable E.bandwidth
      (fun n => (n : ℝ) ^ (-(1 / (2 * alpha + 1)))) ∧
    EventuallyComparable E.projectionDimension
      (fun n => (n : ℝ) * E.bandwidth n)
  deficientTuning : 4 * s < d →
    EventuallyComparable E.bandwidth
      (fun n => (n : ℝ) ^ (-(4 * s / (alpha * (4 * s + d) + 4 * s)))) ∧
    EventuallyComparable E.projectionDimension
      (fun n => ((n : ℝ) * E.bandwidth n) ^ (2 * d / (d + 4 * s)))
  equalRateNuisanceEstimation : EventuallyComparable (bkVNorm E) (bkQNorm E)
  higherOrderDensityRemainderNegligible : EventuallyAtMostConstant
    (fun n => (bkVNorm E n * bkQNorm E n * bkDensitySupError E n) ^ 2)
    (fun n => publishedHoifRate n alpha s d)

-- @node: lem:published-upper-bound-cited
/-- **Cited conditional comparator** (Bonvini–Kennedy 2022, Theorem 1/3.1 and
rate discussion; arXiv:2207.11825v1, Section 3.4 and Remarks 7–8/Figure 1).
For the source's specified HOIF construction, the theorem conditions and explicit
rate specialization imply the eventual bound on its actual conditional MSE.

This is estimator-specific, not a minimax statement: `minimaxRisk` and
`HolderDoseClass` do not occur. -/
def publishedUpperBoundCited (d : ℕ) (alpha beta s gamma₁ gamma₂ : ℝ) : Prop :=
  ∀ E : BKHOIFEstimatorSpec d,
    BKTheorem31Conditions alpha beta E →
    BKRateSpecialization alpha beta s gamma₁ gamma₂ E →
    EventuallyAtMostConstant (bkConditionalMSE E)
      (fun n => publishedHoifRate n alpha s d)

end CausalSmith.Stat.DoseResponseMinimax
