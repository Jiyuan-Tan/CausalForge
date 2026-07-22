/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.HahnBanachSetup

/-!
# Strong duality: `primal ≤ dual` via the sublinear Hahn–Banach theorem

This is the hard direction of the ℓ¹/ℓ∞ duality: we must produce an admissible
weight `w ∈ MomentSol p β` whose ℓ¹ norm is `≤ sSup (dualValSet p β)`.  Combined
with `sSup_dual_le_sInf_primal` (weak duality) and `csInf_le`, this closes the
identity `sInf (primalNormSet p β) = sSup (dualValSet p β)`.

## The route (purely algebraic Hahn–Banach)

We use `exists_extension_of_le_sublinear` on the plain real vector space
`E := Fin (k+1) → ℝ` — **no** normed-space / `PiLp` / operator-norm machinery.
Write `M := sSup (dualValSet p β)` and majorant `N x := M * ninf x`
(`ninf` = sup norm, from `HahnBanachSetup`).

1. **Contrast on the node-value subspace.**  `Ev p β` is injective
   (`Ev_injective`), so `φ := contrastL β ∘ (Ev p β)⁻¹` is a well-defined linear
   functional on `V := range (Ev p β)`, packaged as a `LinearPMap`
   `f : E →ₗ.[ℝ] ℝ` with `f.domain = V` and `f ⟨Ev p β b, _⟩ = contrastL β b`.

2. **Domination.**  `N` is sublinear: `N (c • x) = c * N x` for `c > 0`
   (`ninf_smul` + `M ≥ 0` from `dual_nonneg`) and `N (x + y) ≤ N x + N y`
   (`ninf_add_le` + `M ≥ 0`).  On `V`, `f v ≤ N v` is exactly
   `contrastL_le_dual_mul_ninf`.

3. **Extension.**  `exists_extension_of_le_sublinear` yields a *total* linear map
   `g : E →ₗ[ℝ] ℝ` with `g v = f v` on `V` and `g x ≤ N x` everywhere.

4. **ℓ¹ representative.**  Set `w j := g (Pi.single j 1)`.  Linearity gives
   `g x = ∑ j, x j * w j`.  Testing on the monomial columns `Ev p β (Pi.single ℓ 1)`
   (`Ev_single`, `contrastL_single`) shows `∑ j, w j * (p j)^ℓ = if ℓ = 0 then 0
   else 1`, i.e. `w ∈ MomentSol p β`.

5. **Norm bound.**  Let `σ j := if 0 ≤ w j then 1 else -1`.  Then
   `∑ j, |w j| = ∑ j, σ j * w j = g σ ≤ N σ = M * ninf σ = M` (using
   `ninf_sign`).  Hence `∑ j, |w j| ≤ M`.
-/

open Polynomial

namespace Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

variable {k β : ℕ} {p : Fin (k + 1) → ℝ}

/-- **The Hahn–Banach certificate.**  For distinct nodes and `β ≤ k` there is a
weight vector `w` solving the moment system whose ℓ¹ norm is bounded by the dual
value `sSup (dualValSet p β)`.  Proved by the sublinear Hahn–Banach extension of
the endpoint-contrast functional from the node-value subspace to all of
`(Fin (k+1) → ℝ)`, dominated by `M · ‖·‖_∞`; see the module docstring for the
five-step recipe and the supporting lemmas in `HahnBanachSetup`. -/
private theorem exists_moment_le_dual_hahn_banach_gap
    (hp : Function.Injective p) (hβ : β ≤ k) :
    ∃ w : Fin (k + 1) → ℝ,
      (∀ ℓ, ℓ ≤ β → ∑ j, w j * p j ^ ℓ = if ℓ = 0 then (0 : ℝ) else 1) ∧
        ∑ j, |w j| ≤ sSup (dualValSet p β) := by
  classical
  let E := Fin (k + 1) → ℝ
  let M : ℝ := sSup (dualValSet p β)
  let N : E → ℝ := fun x => M * ninf x
  have hM : 0 ≤ M := dual_nonneg (p := p) hp hβ
  let e : (Fin (β + 1) → ℝ) ≃ₗ[ℝ] LinearMap.range (Ev p β) :=
    LinearEquiv.ofInjective (Ev p β) (Ev_injective (p := p) hp hβ)
  let φ : LinearMap.range (Ev p β) →ₗ[ℝ] ℝ :=
    (contrastL β).comp e.symm.toLinearMap
  let f : E →ₗ.[ℝ] ℝ := ⟨LinearMap.range (Ev p β), φ⟩
  have hφ (b : Fin (β + 1) → ℝ) :
      φ ⟨Ev p β b, LinearMap.mem_range_self (Ev p β) b⟩ = contrastL β b := by
    change (contrastL β) (e.symm (e b)) = contrastL β b
    rw [e.symm_apply_apply]
  have N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x := by
    intro c hc x
    dsimp [N]
    rw [ninf_smul, abs_of_pos hc]
    ring
  have N_add : ∀ x y, N (x + y) ≤ N x + N y := by
    intro x y
    dsimp [N]
    calc
      M * ninf (x + y) ≤ M * (ninf x + ninf y) :=
        mul_le_mul_of_nonneg_left (ninf_add_le x y) hM
      _ = M * ninf x + M * ninf y := by ring
  have hf : ∀ x : f.domain, f x ≤ N x := by
    rintro ⟨_, ⟨b, rfl⟩⟩
    calc
      f ⟨Ev p β b, LinearMap.mem_range_self (Ev p β) b⟩ = contrastL β b := hφ b
      _ ≤ M * ninf (Ev p β b) := contrastL_le_dual_mul_ninf (p := p) hp hβ b
      _ = N (Ev p β b) := rfl
  obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear f N N_hom N_add hf
  let w : Fin (k + 1) → ℝ := fun j => g (Pi.single j (1 : ℝ))
  have hg_expand (x : E) : g x = ∑ j, x j * w j := by
    have hxsum : (∑ j, Pi.single j (x j) : E) = x := by
      simpa using (Finset.univ_sum_single x)
    calc
      g x = g (∑ j, Pi.single j (x j)) := by rw [hxsum]
      _ = ∑ j, g (Pi.single j (x j)) := by rw [map_sum]
      _ = ∑ j, x j * w j := by
        refine Finset.sum_congr rfl ?_
        intro j _
        have hsingle :
            Pi.single j (x j) = (x j) • (Pi.single j (1 : ℝ) : E) := by
          ext i
          by_cases hij : i = j
          · subst i
            simp
          · simp [hij]
        rw [hsingle, map_smul]
        simp [w]
  refine ⟨w, ?_, ?_⟩
  · intro ℓ hℓ
    let ℓ' : Fin (β + 1) := ⟨ℓ, Nat.lt_succ_of_le hℓ⟩
    have hg_monomial :
        g (Ev p β (Pi.single ℓ' (1 : ℝ))) = contrastL β (Pi.single ℓ' (1 : ℝ)) := by
      let x : LinearMap.range (Ev p β) :=
        ⟨Ev p β (Pi.single ℓ' (1 : ℝ)),
          LinearMap.mem_range_self (Ev p β) (Pi.single ℓ' (1 : ℝ))⟩
      calc
        g (Ev p β (Pi.single ℓ' (1 : ℝ))) = f x := hg_ext x
        _ = contrastL β (Pi.single ℓ' (1 : ℝ)) := hφ (Pi.single ℓ' (1 : ℝ))
    calc
      ∑ j, w j * p j ^ ℓ =
          ∑ j, (Ev p β (Pi.single ℓ' (1 : ℝ)) j) * w j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Ev_single]
            simp [ℓ']
            ring
      _ = g (Ev p β (Pi.single ℓ' (1 : ℝ))) := (hg_expand _).symm
      _ = contrastL β (Pi.single ℓ' (1 : ℝ)) := hg_monomial
      _ = if ℓ = 0 then (0 : ℝ) else 1 := by
        simpa [ℓ'] using (contrastL_single (β := β) (ℓ := ℓ'))
  · let σ : E := fun j => if 0 ≤ w j then (1 : ℝ) else -1
    have hσ_abs : ∀ j, |σ j| = 1 := by
      intro j
      by_cases hj : 0 ≤ w j <;> simp [σ, hj]
    have hNσ : N σ = M := by
      simp [N, ninf_sign σ hσ_abs]
    have h_abs_sum : ∑ j, |w j| = ∑ j, σ j * w j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hj : 0 ≤ w j
      · simp [σ, hj, abs_of_nonneg hj]
      · have hjlt : w j < 0 := lt_of_not_ge hj
        simp [σ, hj, abs_of_neg hjlt]
    calc
      ∑ j, |w j| = ∑ j, σ j * w j := h_abs_sum
      _ = g σ := (hg_expand σ).symm
      _ ≤ N σ := hg_le σ
      _ = M := hNσ

/-- **Strong duality (existence of an optimal weight).**  For distinct nodes and
`β ≤ k` there is an admissible weight `w ∈ MomentSol p β` whose ℓ¹ norm does not
exceed the dual value `sSup (dualValSet p β)`.

This is the substantive direction, proved by the sublinear Hahn–Banach argument
outlined in the module docstring: extend the endpoint-contrast functional from the
node-value subspace to all of `(Fin (k+1) → ℝ, ‖·‖_∞)` with the same majorant, and
read off the representing ℓ¹ vector. -/
theorem exists_moment_le_dual (hp : Function.Injective p) (hβ : β ≤ k) :
    ∃ w ∈ MomentSol p β, ∑ j, |w j| ≤ sSup (dualValSet p β) := by
  obtain ⟨w, hw_mom, hw_norm⟩ := exists_moment_le_dual_hahn_banach_gap hp hβ
  exact ⟨w, hw_mom, hw_norm⟩

/-- **Strong duality (inequality form).**  `sInf (primalNormSet p β) ≤ sSup (dualValSet p β)`.
Immediate from `exists_moment_le_dual`: the witness `w` gives a primal value
`∑ j, |w j| ∈ primalNormSet p β` that is `≤` the dual value, and the infimum is a
lower bound. -/
theorem sInf_primal_le_sSup_dual (hp : Function.Injective p) (hβ : β ≤ k) :
    sInf (primalNormSet p β) ≤ sSup (dualValSet p β) := by
  obtain ⟨w, hw, hw_norm⟩ := exists_moment_le_dual hp hβ
  exact le_trans (csInf_le primalNormSet_bddBelow ⟨w, hw, rfl⟩) hw_norm

end Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality
