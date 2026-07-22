/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# The projected localized HOIF kernel: L²-energy equals the projection dimension

Trace and degeneracy identities for projected HOIF kernels, showing that a rank-`J` projection
kernel has L² energy equal to the projection dimension under inverse-Gram weighting.

The order-2 stochastic term of the order-`m` HOIF estimator is a *degenerate U-statistic* whose
kernel is the `J`-dimensional projection

  `g(x, y) = ⟨c(x), M c(y)⟩ = ∑_{k,l} c(x)_k · M_{kl} · c(y)_l`,

where `c : X → ℝ^J` is the (bandwidth-localized, residual-weighted) basis evaluated at the
covariate and `M` is the projection weighting matrix.  Writing `Σ = 𝔼[c cᵀ]` for the
second-moment (Gram) matrix, the L²-energy of the kernel factors, by the independence of the two
sample points, into

  `ζ = ∬ g² dP dP = ∑_{k,l,k',l'} M_{kl} M_{k'l'} Σ_{kk'} Σ_{ll'} = tr(Σ M Σ Mᵀ)`.

With the natural HOIF weighting `M = Σ⁻¹` this collapses to **`ζ = J`** — the projected
degenerate kernel's L²-energy is exactly the projection dimension.  In localized analyses this
identity is paired with the separate bandwidth scaling hypothesis `ζ ≤ C·J/h²` used by
`Causalean.Stat.Nonparametric.HOIF.DegenerateUStatVariance`
(`Var = 2ζ/(n(n−1))`), this is the source of the `O(J/(nh)²)` term in the HOIF projection risk.

`projKernel_degen` records only the one-sided degeneracy field
`∫ g(x,·) dP = 0` when the basis coordinates are centered (`∫ c_l dP = 0`). It
does not by itself construct a `DegenKernel`, since that structure also carries
measurability, symmetry, and square-integrability requirements.
-/

namespace Causalean.Stat.Nonparametric.HOIF

open MeasureTheory Matrix
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P]
variable {J : ℕ}

/-- The second-moment (Gram) matrix of the basis `c`: `Σ_{kl} = ∫ c(x)_k c(x)_l dP`. -/
noncomputable def gram (c : X → Fin J → ℝ) (P : Measure X) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.of (fun k l => ∫ x, c x k * c x l ∂P)

/-- The projected HOIF kernel `g(x,y) = ∑_{k,l} c(x)_k M_{kl} c(y)_l`. -/
noncomputable def projKernel (c : X → Fin J → ℝ) (M : Matrix (Fin J) (Fin J) ℝ) :
    X → X → ℝ :=
  fun x y => ∑ k, ∑ l, c x k * M k l * c y l

/-- The Gram matrix is symmetric. -/
theorem gram_symm (c : X → Fin J → ℝ) : (gram c P)ᵀ = gram c P := by
  funext k l
  simp only [Matrix.transpose_apply, gram, Matrix.of_apply]
  simp_rw [mul_comm]

/-- **One-sided degeneracy of the projected kernel.** If the basis coordinates are
centered (`∫ c_l dP = 0` for every `l`), then `∫ g(x, ·) dP = 0` for every `x`.
This records the zero-integral field only; measurability, symmetry, and
square-integrability are separate requirements for packaging the kernel as a
degenerate U-statistic kernel. -/
theorem projKernel_degen (c : X → Fin J → ℝ) (M : Matrix (Fin J) (Fin J) ℝ)
    (hint : ∀ l, Integrable (fun x => c x l) P)
    (hzero : ∀ l, ∫ x, c x l ∂P = 0) (x : X) :
    ∫ y, projKernel c M x y ∂P = 0 := by
  unfold projKernel
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero (fun l _ => ?_)
      have : (fun y => c x k * M k l * c y l) = (fun y => (c x k * M k l) * c y l) := by
        funext y; ring
      rw [this, integral_const_mul, hzero l, mul_zero]
    · intro l _
      exact ((hint l).const_mul (c x k * M k l))
  · intro k _
    apply integrable_finset_sum
    intro l _
    exact ((hint l).const_mul (c x k * M k l))

/-- **L²-energy of the projected kernel (expanded form).**
By independence of the two sample points, the double integral of the squared projected kernel
factors into Gram entries:

  `∬ g² dP dP = ∑_{k,l,k',l'} M_{kl} M_{k'l'} Σ_{kk'} Σ_{ll'}`,  `Σ = gram c P`. -/
theorem projKernel_L2_eq_sum (c : X → Fin J → ℝ) (M : Matrix (Fin J) (Fin J) ℝ)
    (hc : ∀ k, MemLp (fun x => c x k) 2 P) :
    ∫ p, (projKernel c M p.1 p.2) ^ 2 ∂(P.prod P)
      = ∑ k, ∑ l, ∑ k', ∑ l',
          M k l * M k' l' * gram c P k k' * gram c P l l' := by
  have hsq : ∀ p : X × X,
      (projKernel c M p.1 p.2) ^ 2
        = ∑ k, ∑ l, ∑ k', ∑ l',
            (c p.1 k * M k l * c p.2 l) * (c p.1 k' * M k' l' * c p.2 l') := by
    intro p
    unfold projKernel
    rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun k' _ => by
        rw [Finset.sum_mul_sum]))]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
  have hInt : ∀ k l k' l' : Fin J,
      Integrable
        (fun p : X × X =>
          (c p.1 k * M k l * c p.2 l) * (c p.1 k' * M k' l' * c p.2 l'))
        (P.prod P) := by
    intro k l k' l'
    have hX : Integrable (fun x => c x k * c x k') P := (hc k).integrable_mul (hc k')
    have hY : Integrable (fun y => c y l * c y l') P := (hc l).integrable_mul (hc l')
    have hprod : Integrable
        (fun p : X × X => (c p.1 k * c p.1 k') * (c p.2 l * c p.2 l'))
        (P.prod P) := hX.mul_prod hY
    have hEq :
        (fun p : X × X =>
          (c p.1 k * M k l * c p.2 l) * (c p.1 k' * M k' l' * c p.2 l'))
          =
        (fun p : X × X =>
          (M k l * M k' l') * ((c p.1 k * c p.1 k') * (c p.2 l * c p.2 l'))) := by
      funext p
      ring
    rw [hEq]
    exact hprod.const_mul (M k l * M k' l')
  have hEval : ∀ k l k' l' : Fin J,
      ∫ p, (c p.1 k * M k l * c p.2 l) * (c p.1 k' * M k' l' * c p.2 l') ∂(P.prod P)
        = M k l * M k' l' * gram c P k k' * gram c P l l' := by
    intro k l k' l'
    have hEq :
        (fun p : X × X =>
          (c p.1 k * M k l * c p.2 l) * (c p.1 k' * M k' l' * c p.2 l'))
          =
        (fun p : X × X =>
          (M k l * M k' l') * ((c p.1 k * c p.1 k') * (c p.2 l * c p.2 l'))) := by
      funext p
      ring
    rw [hEq, integral_const_mul,
      integral_prod_mul (μ := P) (ν := P)
        (f := fun x => c x k * c x k') (g := fun y => c y l * c y l')]
    simp only [gram, Matrix.of_apply]
    ring
  simp_rw [hsq]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro l _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k' _
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro l' _
          exact hEval k l k' l'
        · intro l' _
          exact hInt k l k' l'
      · intro k' _
        apply integrable_finset_sum
        intro l' _
        exact hInt k l k' l'
    · intro l _
      apply integrable_finset_sum
      intro k' _
      apply integrable_finset_sum
      intro l' _
      exact hInt k l k' l'
  · intro k _
    apply integrable_finset_sum
    intro l _
    apply integrable_finset_sum
    intro k' _
    apply integrable_finset_sum
    intro l' _
    exact hInt k l k' l'

/-- **The 4-fold Gram sum collapses to the projection dimension.**
With the HOIF weighting `M = Σ⁻¹` (`Σ = gram c P` invertible), the expanded L²-energy equals the
projection dimension `J`, because `Σ Σ⁻¹ = Σ⁻¹ Σ = 1`. -/
theorem sum_collapse_dim (M S : Matrix (Fin J) (Fin J) ℝ)
    (hu : IsUnit S.det) (hM : M = S⁻¹) :
    ∑ k, ∑ l, ∑ k', ∑ l', M k l * M k' l' * S k k' * S l l' = (J : ℝ) := by
  have hSM : S * M = 1 := by rw [hM]; exact Matrix.mul_nonsing_inv S hu
  have hMS : M * S = 1 := by rw [hM]; exact Matrix.nonsing_inv_mul S hu
  -- For fixed k,l, the inner double sum collapses to `M k l * S l k`.
  have key : ∀ k l : Fin J,
      (∑ k', ∑ l', M k l * M k' l' * S k k' * S l l') = M k l * S l k := by
    intro k l
    rw [Finset.sum_comm]
    -- ∑ l', ∑ k', M k l * M k' l' * S k k' * S l l'
    have hinner : ∀ l' : Fin J,
        (∑ k', M k l * M k' l' * S k k' * S l l') = M k l * S l l' * (S * M) k l' := by
      intro l'
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k' _ => by ring)
    rw [Finset.sum_congr rfl (fun l' _ => hinner l'), hSM]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ k (fun l' => M k l * S l l')]
    simp
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => key k l))]
  -- ∑ k, ∑ l, M k l * S l k  =  ∑ k, (M*S) k k  =  ∑ k, 1  =  J
  have hrow : ∀ k : Fin J, (∑ l, M k l * S l k) = (M * S) k k :=
    fun k => (Matrix.mul_apply).symm
  rw [Finset.sum_congr rfl (fun k _ => hrow k), hMS]
  simp only [Matrix.one_apply_eq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **Projected degenerate-kernel L²-energy equals the dimension: `ζ = J`.**
For the HOIF projection kernel `g(x,y) = ⟨c(x), Σ⁻¹ c(y)⟩` (with `Σ = 𝔼[c cᵀ]` the second-moment
matrix), the squared L²-norm `ζ = ∬ g² dP dP` equals the projection dimension `J`.  This is the
trace identity `tr(Σ Σ⁻¹ Σ Σ⁻¹) = tr(1) = J`, and is the algebraic input behind the HOIF
degenerate U-statistic variance bound after the localized L²-energy scaling is supplied. -/
theorem projKernel_L2_eq_dim (c : X → Fin J → ℝ) (M : Matrix (Fin J) (Fin J) ℝ)
    (hc : ∀ k, MemLp (fun x => c x k) 2 P)
    (hu : IsUnit (gram c P).det) (hM : M = (gram c P)⁻¹) :
    ∫ p, (projKernel c M p.1 p.2) ^ 2 ∂(P.prod P) = (J : ℝ) := by
  rw [projKernel_L2_eq_sum c M hc]
  exact sum_collapse_dim M (gram c P) hu hM

end Causalean.Stat.Nonparametric.HOIF
