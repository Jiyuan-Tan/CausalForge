/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-direction support-process CLT (Beresteanu–Molinari 2008, Theorem A.2)

The Tier-2 capstone of the random-set program, the general-`d` analogue of the
scalar interval CLT (`IntervalCLT.lean`).  Beresteanu–Molinari Theorem A.2 states
the support-function-process CLT

    √n · H((1/n)⊕Fᵢ, E[F])  ⇒  ‖z‖_{C(Sᵈ⁻¹)}

for a Gaussian process `z` on the unit sphere with covariance
`Cov(z(p),z(q)) = E[s(p,F)s(q,F)] − E[s(p,F)]E[s(q,F)]`.  The genuine continuum
`C(Sᵈ⁻¹)` Banach CLT is a deferred Mathlib gap.

This file proves the **honest finite-dimensional projection**: fix a finite set of
`k` directions `p₀,…,p_{k-1}` and consider the centered support process
`ψ(z)_j = s(pⱼ, F(z)) − E s(pⱼ, F)`, valued in `EuclideanSpace ℝ (Fin k)`.  The
Hausdorff-over-grid statistic is the `ℓ^∞` functional `maxAbsK`, and the
support-process vector CLT plus continuous mapping give

    √n · maxⱼ |s(pⱼ,·)-process|  ⇒  ‖z‖_∞ over the grid,

the law of `maxAbsK` of the `k`-variate Gaussian limit.  This is the exact
generalization of `normalizedSum_maxAbs_clt` (the `Fin 2` `maxAbs` CLT).

## Main results

* `maxAbsK` / `continuous_maxAbsK` / `measurable_maxAbsK` — the `ℓ^∞`/Hausdorff-
  over-grid functional `w ↦ supⱼ |wⱼ|` on `EuclideanSpace ℝ (Fin k)`.
* `supportProcess_sup_clt` — the abstract continuous-mapping CLT: `maxAbsK` of the
  vector normalised sum of the centered support process converges in distribution
  to `(gaussianLimit ψ).map maxAbsK`.
-/

import Causalean.PO.ID.Partial.SupportFunction.Calculus
import Causalean.PO.ID.Partial.RandomSet.SetValued
import Causalean.Stat.CLT.GaussianLimit

/-! # Finite-Direction Support-Process Central Limit Theorem

This file proves the finite-dimensional support-process central limit theorem
for random compact convex sets evaluated on a fixed grid of directions. It
turns support-function deviations into a vector-valued empirical process and
applies a continuous mapping theorem to the gridwise sup-norm statistic. This is
the honest finite-dimensional projection of Beresteanu--Molinari Theorem A.2;
the full continuum Banach-space central limit theorem is deferred. -/

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped RealInnerProductSpace

namespace Causalean.PartialID.RandomSet

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {k : ℕ} [NeZero k]

/-- The grid supremum statistic returns the largest absolute support-process
deviation across the chosen directions.

The **`ℓ^∞` / Hausdorff-over-grid functional** `w ↦ supⱼ |wⱼ|` on
`EuclideanSpace ℝ (Fin k)`.  This is the sup of the `|coordinate|` over the `k`
directions of the support-process grid — the finite-grid analogue of the
Hausdorff distance, and the direct generalization of `maxAbs` (the `Fin 2` case).
The `[NeZero k]` instance makes `Finset.univ` nonempty. -/
noncomputable def maxAbsK (w : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => |w j|)

/-- The grid supremum statistic is continuous. -/
lemma continuous_maxAbsK : Continuous (maxAbsK (k := k)) := by
  unfold maxAbsK
  fun_prop

/-- The grid supremum statistic is measurable. -/
lemma measurable_maxAbsK : Measurable (maxAbsK (k := k)) :=
  continuous_maxAbsK.measurable

section CLT

variable {ψ : X → EuclideanSpace ℝ (Fin k)} (hψ : Measurable ψ)
  (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)

/-- The finite-grid support statistic has a probability measure as its Gaussian
pushforward limit law.

The limit law of the finite-grid support statistic is a probability measure
(pushforward of the Gaussian limit by the continuous `maxAbsK`). -/
instance : IsProbabilityMeasure ((gaussianLimit hψ hvar).map maxAbsK) :=
  Measure.isProbabilityMeasure_map measurable_maxAbsK.aemeasurable

/-- The finite-grid supremum of a centered support process converges to the
corresponding supremum of its Gaussian limit.

**Abstract continuous-mapping support-process CLT (Beresteanu–Molinari Thm A.2,
finite-grid form).**  For a centered support process
`ψ(z)_j = s(pⱼ, F(z)) − E s(pⱼ, F)` on `k` fixed directions, `maxAbsK` of the
vector normalised sum converges in distribution to the pushforward
`(gaussianLimit ψ).map maxAbsK` — the law of `supⱼ |z(pⱼ)|` for the `k`-variate
Gaussian limit `z`.  Immediate from the multivariate CLT (`clt_normalizedSum_vec`)
and the continuous-mapping theorem (`Tendsto_dist_vec.map_continuous`).  This is
the direct general-`d` analogue of the `Fin 2` `normalizedSum_maxAbs_clt`. -/
theorem supportProcess_sup_clt
    (S : IIDSample Ω X μ P)
    (hψ_int : Integrable ψ P) (hmean : ∫ x, ψ x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n) μ) :
    Tendsto_dist_vec
      (fun n ω => maxAbsK (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n ω))
      ((gaussianLimit hψ hvar).map maxAbsK) μ
      (fun n => measurable_maxAbsK.comp_aemeasurable (hSum_meas n)) :=
  Tendsto_dist_vec.map_continuous continuous_maxAbsK hSum_meas
    (fun n => measurable_maxAbsK.comp_aemeasurable (hSum_meas n))
    (S.clt_normalizedSum_vec hψ hvar hψ_int hmean hSum_meas)

end CLT

/-! ## Instantiation on set-valued maps

The shell above is a CLT for an abstract centered process `ψ`.  Here we feed it
the **support process** of a set-valued random variable, giving a finite-grid
CLT for the normalized sum of centered support-function coordinates.  The
separate coordinate bridge below identifies that normalized sum with empirical
Minkowski-average support deviations only under the body-valued hypothesis it
states explicitly. -/

section SetValued

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The centered support process records each random set's support deviation
from its center on a finite grid of directions.

The **centered support process** of a set-valued random variable `F` on a
finite grid of directions `p : Fin k → V`:
`ψ(x)_j = s(pⱼ, F x) − s(pⱼ, E[F])`, valued in `EuclideanSpace ℝ (Fin k)`.  The
center `EF` plays the role of the Aumann expectation `E[F]`; the mean-zero
condition `∫ ψ = 0` is exactly the (general-`d`, carried-as-hypothesis) Artstein
identity `s(pⱼ, E[F]) = E[s(pⱼ, F)]`. -/
noncomputable def supportProcess (F : X → Set V) (EF : Set V) (p : Fin k → V) :
    X → EuclideanSpace ℝ (Fin k) :=
  fun x => (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun j => supportFn (F x) (p j) - supportFn EF (p j))

omit [MeasurableSpace X] [NeZero k] in
/-- Each coordinate of the centered support process is the corresponding support deviation. -/
@[simp] lemma supportProcess_ofLp (F : X → Set V) (EF : Set V) (p : Fin k → V)
    (x : X) (j : Fin k) :
    (supportProcess F EF p x).ofLp j
      = supportFn (F x) (p j) - supportFn EF (p j) := rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [NeZero k] in
/-- Each coordinate of the normalized support-process sum is the rescaled support
deviation of the empirical Minkowski average.

**The Minkowski-mean bridge in coordinates.**  The `j`-th coordinate of the
normalised sum of the support process is exactly the rescaled support deviation
of the empirical Minkowski average,
`√n · (s(pⱼ, F̄ₙ) − s(pⱼ, E[F]))`.  This is what makes the abstract shell a
statement about random sets — it is `supportFn_minkowskiMean` (the keystone of
`SetValued.lean`) pushed through the `EuclideanSpace` coordinate algebra. -/
lemma supportProcess_normalizedSum_apply
    (S : IIDSample Ω X μ P) (F : X → Set V) (EF : Set V) (p : Fin k → V)
    (hbody : ∀ x, IsBody (F x)) (n : ℕ) (ω : Ω) (j : Fin k) :
    IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
        (fun m => Finset.range m) n ω j
      = Real.sqrt (n : ℝ)
        * (supportFn (minkowskiMean (Finset.range n) (fun i => F (S.Z i ω))) (p j)
            - supportFn EF (p j)) := by
  rw [IsAsymLinearVec.normalizedSum]
  simp only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply,
    supportProcess_ofLp]
  rw [supportFn_minkowskiMean (Finset.range n) (fun i => F (S.Z i ω)) (p j)
        (fun i _ => hbody (S.Z i ω)), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]

/-- For a set-valued random variable, the finite-grid supremum of the normalized
centered support-process sum converges to the supremum of its Gaussian limit.

This is the abstract finite-grid support-process CLT specialized to the support
process generated by `F`, `EF`, and the grid `p`.  It assumes measurability,
integrability, mean zero, and measurability of the normalized sums, and concludes
convergence in distribution of `maxAbsK` applied to those normalized sums.  It
does not by itself identify the statistic with empirical Minkowski-average
support deviations; that identification is provided separately by
`supportProcess_normalizedSum_apply` under the body-valued hypothesis. -/
-- TODO(faithfulness): Beresteanu-Molinari finite-grid CLT — to reach the
-- empirical-Minkowski statement directly, the public theorem should include
-- the body-valued bridge hypotheses and identify this normalized support-process
-- statistic with the Hausdorff-over-grid empirical-Minkowski statistic.
theorem setValued_supportProcess_clt
    (S : IIDSample Ω X μ P) (F : X → Set V) (EF : Set V) (p : Fin k → V)
    (hψ : Measurable (supportProcess F EF p))
    (hvar : Integrable (fun x => ‖supportProcess F EF p x‖ ^ 2) P)
    (hint : Integrable (supportProcess F EF p) P)
    (hmean : ∫ x, supportProcess F EF p x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
        (fun m => Finset.range m) n) μ) :
    Tendsto_dist_vec
      (fun n ω => maxAbsK (IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
        (fun m => Finset.range m) n ω))
      ((gaussianLimit hψ hvar).map maxAbsK) μ
      (fun n => measurable_maxAbsK.comp_aemeasurable (hSum_meas n)) :=
  supportProcess_sup_clt hψ hvar S hint hmean hSum_meas

end SetValued

end Causalean.PartialID.RandomSet
