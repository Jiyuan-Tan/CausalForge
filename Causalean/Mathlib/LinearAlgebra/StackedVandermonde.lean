/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Stacked block-Vandermonde injectivity

For distinct nodes, the stacked contraction map
`B_D(e) = (Σ_j c_{j,n+k} e_j ℓ_j^k)_{k=0}^{n-2}` has generic rank `n` at `K = 2n - 2`
(partition the indices into blocks `J_k` of size `≤ k+1`, use Vandermonde independence),
so a concrete choice of weights makes `B_D(e) = 0 ⟹ e = 0`.
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Complex.Basic

/-!
# Stacked Vandermonde systems

This file gives a constructive injectivity certificate for a stacked family of
weighted Vandermonde evaluation maps at distinct complex nodes.
-/

namespace Causalean.Mathlib.LinearAlgebra

open scoped BigOperators

noncomputable section

/-- The coefficient vector of `(X₀ + z X₁)^k`, after dividing its `r`-th
coefficient by the nonzero binomial coefficient `\binom{k}{r}`.  Thus this is
the standard affine-chart model of a degree-`k` binary form. -/
def affineBinaryPower (z : ℂ) (k : ℕ) : Fin (k + 1) → ℂ :=
  fun r => z ^ (r : ℕ)

/-- The coefficient-vector version of the stacked contraction map.  In the
affine chart `ℓ j = X₀ + slopes j X₁`, its `k`-th component is exactly the
coefficient vector of `∑ j, weights j k * e j • (ℓ j)^k`, up to invertible
binomial diagonal rescaling. -/
def stackedContraction (N : ℕ) (slopes : Fin (N + 1) → ℂ)
    (weights : Fin (N + 1) → Fin N → ℂ) (e : Fin (N + 1) → ℂ) :
    (k : Fin N) → Fin (k.1 + 1) → ℂ :=
  fun k r => ∑ j, weights j k * e j * affineBinaryPower (slopes j) k.1 r

/-- The two-block specialization from the block-Vandermonde argument:
`J₀ = {0}` and `J_{N-1} = {1, …, N}`. -/
def blockVandermondeWitnessWeights (N : ℕ) (hN : 2 ≤ N) :
    Fin (N + 1) → Fin N → ℂ :=
  let zeroBlock : Fin N := ⟨0, by omega⟩
  let topBlock : Fin N := ⟨N - 1, Nat.sub_lt (by omega) (by omega)⟩
  fun j k =>
    if j = 0 then
      if k = zeroBlock then 1 else 0
    else if k = topBlock then 1 else 0

/-- At least three distinct complex nodes admit weights for which the stacked
contraction is injective. The first block detects coordinate `0`, while the
last block is a square Vandermonde system on coordinates `1,…,N`. -/
theorem stacked_contraction_injective_of_generic_weights
  {N : ℕ} (hN : 2 ≤ N) (slopes : Fin (N + 1) → ℂ)
    (hslopes : Function.Injective slopes) :
    ∃ weights : Fin (N + 1) → Fin N → ℂ,
      Function.Injective (stackedContraction N slopes weights) := by
  let zeroBlock : Fin N := ⟨0, by omega⟩
  let topBlock : Fin N := ⟨N - 1, Nat.sub_lt (by omega) (by omega)⟩
  have htop_ne_zero : topBlock ≠ zeroBlock := by
    intro h
    have : N - 1 = 0 := Fin.ext_iff.mp h
    omega
  have hzero_ne_top : (0 : ℕ) ≠ N - 1 := by omega
  refine ⟨blockVandermondeWitnessWeights N hN, ?_⟩
  intro e e' he
  have hzero : e 0 = e' 0 := by
    have h := congrFun (congrFun he zeroBlock) (0 : Fin 1)
    simpa [stackedContraction, blockVandermondeWitnessWeights,
      affineBinaryPower, zeroBlock, topBlock, htop_ne_zero,
      hzero_ne_top, Fin.sum_univ_succ] using h
  have hsucc : (fun i : Fin N => e i.succ) = fun i => e' i.succ := by
    have htop := fun r => congrFun (congrFun he topBlock) r
    have hsum : ∀ r : Fin N,
        (∑ i : Fin N, e i.succ * slopes i.succ ^ (r : ℕ)) =
          ∑ i : Fin N, e' i.succ * slopes i.succ ^ (r : ℕ) := by
      intro r
      let rTop : Fin (topBlock.1 + 1) := ⟨r.1, by
        change r.1 < N - 1 + 1
        omega⟩
      simpa [stackedContraction, blockVandermondeWitnessWeights,
        affineBinaryPower, zeroBlock, topBlock, htop_ne_zero,
        Fin.sum_univ_succ, rTop] using htop rTop
    have hv : (fun i : Fin N => e i.succ - e' i.succ) = 0 := by
      apply Matrix.eq_zero_of_vecMul_eq_zero
        (Matrix.det_vandermonde_ne_zero_iff.mpr
          (hslopes.comp (Fin.succ_injective N)))
      funext r
      change ∑ i : Fin N, (e i.succ - e' i.succ) * slopes i.succ ^ (r : ℕ) = 0
      calc
        ∑ i : Fin N, (e i.succ - e' i.succ) * slopes i.succ ^ (r : ℕ) =
            (∑ i : Fin N, e i.succ * slopes i.succ ^ (r : ℕ)) -
              ∑ i : Fin N, e' i.succ * slopes i.succ ^ (r : ℕ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := sub_eq_zero.mpr (hsum r)
    funext i
    exact sub_eq_zero.mp (congrFun hv i)
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hzero
  · exact congrFun hsucc i

end

end Causalean.Mathlib.LinearAlgebra
