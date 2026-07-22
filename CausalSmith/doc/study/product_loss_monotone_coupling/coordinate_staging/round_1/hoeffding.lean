/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.HoeffdingFubiniIntegrability

/-!
# Hoeffding's covariance identity

For a coupling `π ∈ Π(μ, ν)` of two `L²` real measures, with marginal cdfs
`F = cdf μ`, `G = cdf ν` and joint cdf `H_π`, Hoeffding's identity expresses the
covariance as a double integral of the gap between the joint cdf and the product
of the marginals:

    `Cov_π(X, Y) = ∫∫ (H_π x y - F x · G y) dx dy`,

where `Cov_π(X,Y) = E_π[XY] - E[X] E[Y]`.

## Proof structure

Everything is assembled from `HoeffdingFubini.lean` and `Survival.lean`:

1. `integral_prod_eq_integral_fiber` : `E_π[XY] = ∫ q, (∫ Φ q p ∂π) dq`, where
   `Φ q p = signedTail p.1 q.1 * signedTail p.2 q.2` is the product tail
   representation of `p.1 * p.2`.
2. `fiber_integral_pi` : the inner integral is
   `S - 𝟙{t<0}·SX - 𝟙{s<0}·SY + 𝟙{s<0}·𝟙{t<0}` in terms of survival functions.
3. `mean_fst_tail`, `mean_snd_tail` and `integral_prod_mul` : the product of the
   means is `∫ q, (SX q.1 - 𝟙{q.1<0})·(SY q.2 - 𝟙{q.2<0}) dq`.
4. Subtracting (2) and (3) pointwise, the three inhomogeneous terms cancel and
   what remains is the **survival gap** `S - SX·SY`.
5. `surv_gap_eq` : the survival gap equals the Fréchet gap `H_π - F·G`.

The `MemLp 2` hypotheses on the marginals enter exactly once, through
Cauchy–Schwarz, to give `E|XY| < ∞` and hence the Fubini domination.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-- Pointwise cancellation: the fibre integral minus the product of the centred
marginal survival functions is exactly the Fréchet gap `H_π - F·G`.

    `(S - 𝟙{t<0}·SX - 𝟙{s<0}·SY + 𝟙{s<0}𝟙{t<0}) - (SX - 𝟙{s<0})(SY - 𝟙{t<0})
       = S - SX·SY = H_π - F·G`.

This is the algebraic heart of the identity: the constants `𝟙{s<0}`, `𝟙{t<0}`
introduced by the signed tail representation cancel identically. -/
lemma fiber_sub_mean_prod (h : IsCoupling π μ ν) (q : ℝ × ℝ) :
    (∫ p : ℝ × ℝ, signedTail p.1 q.1 * signedTail p.2 q.2 ∂π)
        - (survFst π q.1 - tailInd 0 q.1) * (survSnd π q.2 - tailInd 0 q.2)
      = jointCdf π q.1 q.2 - cdf μ q.1 * cdf ν q.2 := by
  rw [fiber_integral_pi h q.1 q.2, ← surv_gap_eq h q.1 q.2]
  ring

/-- The Fréchet gap `H_π - F·G` is integrable on `ℝ × ℝ` for an `L²` coupling;
this is the integrability side-condition consumed by `hoeffding_cov_identity`
and by the monotone comparison of double integrals in `Optimality.lean`.

Proof: it is the difference of the integrable fibre `q ↦ ∫ Φ q p ∂π`
(`integrable_fiber`) and the integrable tensor product
`(SX - 𝟙{·<0}) ⊗ (SY - 𝟙{·<0})` (`Integrable.mul_prod`), by
`fiber_sub_mean_prod`. -/
theorem integrable_frechet_gap (h : IsCoupling π μ ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    Integrable (fun p : ℝ × ℝ => jointCdf π p.1 p.2 - cdf μ p.1 * cdf ν p.2)
      (volume.prod volume) := by
  have hfib := integrable_fiber h hμ hν
  have hmean :=
    (integrable_survFst_sub h hμ).mul_prod (integrable_survSnd_sub h hν)
  have hsub := hfib.sub hmean
  refine hsub.congr ?_
  filter_upwards with q using fiber_sub_mean_prod h q

/-- **Hoeffding's covariance identity, product form.** For a coupling `π` of two
`L²` probability measures `μ, ν`,

    `E_π[XY] - E[X]·E[Y] = ∫ q, (H_π q.1 q.2 - F q.1 · G q.2) ∂(volume ⊗ volume)`.

Proof: rewrite `E_π[XY]` by `integral_prod_eq_integral_fiber`, rewrite
`E[X]·E[Y]` by `mean_fst_tail`, `mean_snd_tail` and `integral_prod_mul`, then
combine the two integrals with `integral_sub` (integrability from
`integrable_fiber` and `Integrable.mul_prod`) and apply `fiber_sub_mean_prod`
pointwise. -/
theorem hoeffding_cov_identity_prod (h : IsCoupling π μ ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p, p.1 * p.2 ∂π) - (∫ x, x ∂μ) * (∫ y, y ∂ν)
      = ∫ q : ℝ × ℝ, (jointCdf π q.1 q.2 - cdf μ q.1 * cdf ν q.2)
          ∂(volume.prod volume) := by
  rw [integral_prod_eq_integral_fiber h hμ hν, mean_fst_tail h hμ, mean_snd_tail h hν]
  rw [← integral_prod_mul (fun s : ℝ => survFst π s - tailInd 0 s)
      (fun t : ℝ => survSnd π t - tailInd 0 t)]
  rw [← integral_sub (integrable_fiber h hμ hν)
      ((integrable_survFst_sub h hμ).mul_prod (integrable_survSnd_sub h hν))]
  exact integral_congr_ae (Filter.Eventually.of_forall (fiber_sub_mean_prod h))

/-- **Hoeffding's covariance identity.** For a coupling `π` of two `L²`
probability measures `μ, ν`, the covariance equals the double integral of the
Fréchet gap `H_π - F·G`:

    `(∫ p, p.1 * p.2 ∂π) - (∫ x, x ∂μ)(∫ y, y ∂ν)
       = ∫ x, ∫ y, (jointCdf π x y - cdf μ x * cdf ν y) dy dx`.

`MemLp 2` on each marginal guarantees the first moments exist and the double
integral converges. Iterated form of `hoeffding_cov_identity_prod` via
`MeasureTheory.integral_prod`. -/
theorem hoeffding_cov_identity (h : IsCoupling π μ ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p, p.1 * p.2 ∂π) - (∫ x, x ∂μ) * (∫ y, y ∂ν)
      = ∫ x, ∫ y, (jointCdf π x y - cdf μ x * cdf ν y) ∂volume ∂volume := by
  rw [hoeffding_cov_identity_prod h hμ hν]
  exact integral_prod _ (integrable_frechet_gap h hμ hν)

end Causalean.Stat
