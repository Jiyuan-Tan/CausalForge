/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.HahnBanachSetup

/-!
# Finite-dimensional ℓ¹/ℓ∞ duality from moment-system feasibility

The generic theorem `l1_repr_eq_sup_dual` assumes distinct nodes and `β ≤ k` to
get injectivity of the node-evaluation map and hence feasibility of the moment
system.  Downstream formalizations sometimes already carry feasibility as a
hypothesis.  This file packages the same Hahn-Banach proof under the weaker and
more intrinsic assumption `(MomentSol p β).Nonempty`.

Main declarations:

* `primalNormSet_nonempty_of_momentSol_nonempty` and
  `dualValSet_bddAbove_of_momentSol_nonempty` establish that the primal infimum
  and dual supremum are well posed from feasibility alone.
* `momentSol_contrast_eq_sum_eval` identifies a feasible moment vector with a
  representation of the coefficient contrast on node-value vectors.
* `contrastL_le_dual_mul_ninf_of_momentSol_nonempty` is the Hahn-Banach
  domination estimate without a Vandermonde injectivity assumption.
* `exists_moment_le_dual_of_momentSol_nonempty` produces a feasible weight with
  ℓ¹ norm bounded by the dual value.
* `l1_repr_eq_sup_dual_of_momentSol_nonempty` is the resulting ℓ¹/ℓ∞ duality
  identity assuming only moment-system feasibility.
-/

open Polynomial

namespace Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

variable {k β : ℕ} {p : Fin (k + 1) → ℝ}

-- @node: primalNormSet_nonempty_of_momentSol_nonempty
/-- If the moment system is feasible, the primal norm set is nonempty. -/
theorem primalNormSet_nonempty_of_momentSol_nonempty
    (hne : (MomentSol p β).Nonempty) : (primalNormSet p β).Nonempty := by
  rcases hne with ⟨w, hw⟩
  exact ⟨∑ j, |w j|, w, hw, rfl⟩

-- @node: dualValSet_bddAbove_of_momentSol_nonempty
/-- Feasibility of the moment system bounds every dual value by any feasible
primal norm.  This is the weak-duality estimate: if `w ∈ MomentSol p β`, then
every node-bounded degree-`≤ β` polynomial has endpoint contrast at most
`∑ j, |w j|`, so the dual value set is bounded above. -/
theorem dualValSet_bddAbove_of_momentSol_nonempty
    (hne : (MomentSol p β).Nonempty) : BddAbove (dualValSet p β) := by
  rcases primalNormSet_nonempty_of_momentSol_nonempty (p := p) (β := β) hne with ⟨s, hs⟩
  exact ⟨s, fun t ht => dual_le_primal hs ht⟩

-- @node: dual_nonneg_of_momentSol_nonempty
/-- With a feasible primal system, the dual supremum is nonnegative because `0` is dual-feasible. -/
theorem dual_nonneg_of_momentSol_nonempty (hne : (MomentSol p β).Nonempty) :
    0 ≤ sSup (dualValSet p β) := by
  have h0 : 0 ∈ dualValSet p β := by
    refine ⟨(0 : Polynomial ℝ), ?_, ?_, ?_⟩
    · simp
    · intro j
      simp
    · simp
  exact le_csSup (dualValSet_bddAbove_of_momentSol_nonempty (p := p) (β := β) hne) h0

-- @node: momentSol_contrast_eq_sum_eval
/-- A feasible moment vector represents the coefficient contrast on node-value
vectors: for every coefficient vector `b`, `contrastL β b` equals the pairing of
`w` with the node-evaluation vector `Ev p β b`. -/
theorem momentSol_contrast_eq_sum_eval {w : Fin (k + 1) → ℝ} (hw : w ∈ MomentSol p β)
    (b : Fin (β + 1) → ℝ) :
    contrastL β b = ∑ j, w j * Ev p β b j := by
  have hrepr := repr_identity (p := p) (β := β) (w := w) hw (coeffPoly_natDegree_le b)
  rw [coeffPoly_contrast] at hrepr
  rw [hrepr]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [← coeffPoly_eval_node (p := p) b j]

-- @node: contrastL_le_dual_mul_ninf_of_momentSol_nonempty
/-- Hahn-Banach domination estimate on the node-value subspace, using feasibility
instead of node-evaluation injectivity:
`contrastL β b ≤ sSup (dualValSet p β) * ninf (Ev p β b)`.

If the node-value vector has sup norm zero, feasibility identifies the contrast
with zero.  Otherwise, scale `coeffPoly b` by this sup norm to make it dual
feasible and compare its contrast with the dual supremum. -/
theorem contrastL_le_dual_mul_ninf_of_momentSol_nonempty
    (hne : (MomentSol p β).Nonempty) (b : Fin (β + 1) → ℝ) :
    contrastL β b ≤ sSup (dualValSet p β) * ninf (Ev p β b) := by
  rcases hne with ⟨w0, hw0⟩
  let M := sSup (dualValSet p β)
  let s := ninf (Ev p β b)
  by_cases hs0 : s = 0
  · have hEvzero : Ev p β b = 0 := by
      ext j
      have hle : |Ev p β b j| ≤ 0 := by
        simpa [s, hs0] using le_ninf (Ev p β b) j
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg (Ev p β b j)))
    have hcontrast_zero : contrastL β b = 0 := by
      rw [momentSol_contrast_eq_sum_eval (p := p) (β := β) hw0 b]
      simp [hEvzero]
    simp only [hcontrast_zero]
    exact mul_nonneg
      (dual_nonneg_of_momentSol_nonempty (p := p) (β := β) ⟨w0, hw0⟩)
      (by simp [s, hs0])
  · have hspos : 0 < s :=
      lt_of_le_of_ne (by simpa [s] using ninf_nonneg (Ev p β b)) (Ne.symm hs0)
    let r' : Polynomial ℝ := s⁻¹ • coeffPoly b
    have hmem : |r'.eval 1 - r'.eval 0| ∈ dualValSet p β := by
      refine ⟨r', ?_, ?_, rfl⟩
      · exact (Polynomial.natDegree_smul_le s⁻¹ (coeffPoly b)).trans
          (coeffPoly_natDegree_le b)
      · intro j
        have hle : |Ev p β b j| ≤ s := by
          simpa [s] using le_ninf (Ev p β b) j
        calc
          |r'.eval (p j)| = |s⁻¹ * Ev p β b j| := by
            rw [show r'.eval (p j) = s⁻¹ * Ev p β b j by
              simp [r', Polynomial.eval_smul, coeffPoly_eval_node]]
          _ = s⁻¹ * |Ev p β b j| := by
            rw [abs_mul, abs_inv, abs_of_pos hspos]
          _ ≤ s⁻¹ * s :=
            mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hspos.le)
          _ = 1 := inv_mul_cancel₀ hspos.ne'
    have hdual : |r'.eval 1 - r'.eval 0| ≤ M := by
      exact le_csSup
        (dualValSet_bddAbove_of_momentSol_nonempty (p := p) (β := β) ⟨w0, hw0⟩) hmem
    have hscaled : r'.eval 1 - r'.eval 0 = s⁻¹ * contrastL β b := by
      calc
        r'.eval 1 - r'.eval 0 =
            s⁻¹ * (coeffPoly b).eval 1 - s⁻¹ * (coeffPoly b).eval 0 := by
          simp [r', Polynomial.eval_smul]
        _ = s⁻¹ * ((coeffPoly b).eval 1 - (coeffPoly b).eval 0) := by
          ring
        _ = s⁻¹ * contrastL β b := by
          rw [coeffPoly_contrast]
    have habs_le : |contrastL β b| ≤ M * s := by
      calc
        |contrastL β b| = s * |s⁻¹ * contrastL β b| := by
          rw [abs_mul, abs_inv, abs_of_pos hspos, ← mul_assoc, mul_inv_cancel₀ hspos.ne',
            one_mul]
        _ ≤ s * M :=
          mul_le_mul_of_nonneg_left (by simpa [hscaled] using hdual) hspos.le
        _ = M * s := by
          rw [mul_comm]
    exact (le_abs_self (contrastL β b)).trans (by simpa [M, s] using habs_le)

-- @node: exists_moment_le_dual_of_momentSol_nonempty
/-- Strong duality from moment-system feasibility: there is a feasible weight
whose ℓ¹ norm is bounded by the dual supremum.

The proof extends the functional represented by one feasible moment vector from
`range (Ev p β)` to the whole node-value space under the majorant
`sSup (dualValSet p β) * ninf`.  Evaluating the extension on coordinate vectors
gives a new feasible weight, and evaluating it on the sign vector gives the
ℓ¹-norm bound. -/
theorem exists_moment_le_dual_of_momentSol_nonempty
    (hne : (MomentSol p β).Nonempty) :
    ∃ w ∈ MomentSol p β, ∑ j, |w j| ≤ sSup (dualValSet p β) := by
  classical
  rcases hne with ⟨w0, hw0⟩
  let E := Fin (k + 1) → ℝ
  let M : ℝ := sSup (dualValSet p β)
  let N : E → ℝ := fun x => M * ninf x
  have hM : 0 ≤ M := dual_nonneg_of_momentSol_nonempty (p := p) (β := β) ⟨w0, hw0⟩
  let g0 : E →ₗ[ℝ] ℝ := {
    toFun := fun x => ∑ j, w0 j * x j
    map_add' := by
      intro x y
      calc
        ∑ j, w0 j * (x + y) j = ∑ j, (w0 j * x j + w0 j * y j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          change w0 j * (x j + y j) = w0 j * x j + w0 j * y j
          ring
        _ = ∑ j, w0 j * x j + ∑ j, w0 j * y j := by
          rw [Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      calc
        ∑ j, w0 j * (c • x) j = ∑ j, c * (w0 j * x j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          change w0 j * (c * x j) = c * (w0 j * x j)
          ring
        _ = c * ∑ j, w0 j * x j := by
          rw [Finset.mul_sum]
  }
  let φ : LinearMap.range (Ev p β) →ₗ[ℝ] ℝ :=
    g0.comp (LinearMap.range (Ev p β)).subtype
  let f : E →ₗ.[ℝ] ℝ := ⟨LinearMap.range (Ev p β), φ⟩
  have hφ (b : Fin (β + 1) → ℝ) :
      φ ⟨Ev p β b, LinearMap.mem_range_self (Ev p β) b⟩ = contrastL β b := by
    change g0 (Ev p β b) = contrastL β b
    exact (momentSol_contrast_eq_sum_eval (p := p) (β := β) hw0 b).symm
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
      _ = M * ninf x + M * ninf y := by
        ring
  have hf : ∀ x : f.domain, f x ≤ N x := by
    rintro ⟨_, ⟨b, rfl⟩⟩
    calc
      f ⟨Ev p β b, LinearMap.mem_range_self (Ev p β) b⟩ = contrastL β b := hφ b
      _ ≤ M * ninf (Ev p β b) :=
        contrastL_le_dual_mul_ninf_of_momentSol_nonempty (p := p) (β := β) ⟨w0, hw0⟩ b
      _ = N (Ev p β b) := rfl
  obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear f N N_hom N_add hf
  let w : Fin (k + 1) → ℝ := fun j => g (Pi.single j (1 : ℝ))
  have hg_expand (x : E) : g x = ∑ j, x j * w j := by
    have hxsum : (∑ j, Pi.single j (x j) : E) = x := by
      simpa using (Finset.univ_sum_single x)
    calc
      g x = g (∑ j, Pi.single j (x j)) := by
        rw [hxsum]
      _ = ∑ j, g (Pi.single j (x j)) := by
        rw [map_sum]
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

-- @node: sInf_primal_le_sSup_dual_of_momentSol_nonempty
/-- Inequality form of strong duality under moment-system feasibility. -/
theorem sInf_primal_le_sSup_dual_of_momentSol_nonempty
    (hne : (MomentSol p β).Nonempty) :
    sInf (primalNormSet p β) ≤ sSup (dualValSet p β) := by
  obtain ⟨w, hw, hw_norm⟩ :=
    exists_moment_le_dual_of_momentSol_nonempty (p := p) (β := β) hne
  exact le_trans (csInf_le primalNormSet_bddBelow ⟨w, hw, rfl⟩) hw_norm

-- @node: sSup_dual_le_sInf_primal_of_momentSol_nonempty
/-- Weak duality as an `sSup ≤ sInf` inequality under moment-system feasibility. -/
theorem sSup_dual_le_sInf_primal_of_momentSol_nonempty
    (hne : (MomentSol p β).Nonempty) :
    sSup (dualValSet p β) ≤ sInf (primalNormSet p β) := by
  exact csSup_le dualValSet_nonempty fun t ht =>
    le_csInf (primalNormSet_nonempty_of_momentSol_nonempty (p := p) (β := β) hne) fun s hs =>
      dual_le_primal hs ht

-- @node: l1_repr_eq_sup_dual_of_momentSol_nonempty
/-- Finite-dimensional ℓ¹/ℓ∞ duality assuming only that the representing moment
system is feasible:
`sInf (primalNormSet p β) = sSup (dualValSet p β)`.

This version is useful when a caller has a problem-specific feasibility witness
but not the distinct-node and `β ≤ k` hypotheses used by `l1_repr_eq_sup_dual`. -/
theorem l1_repr_eq_sup_dual_of_momentSol_nonempty
    (hne : (MomentSol p β).Nonempty) :
    sInf (primalNormSet p β) = sSup (dualValSet p β) :=
  le_antisymm
    (sInf_primal_le_sSup_dual_of_momentSol_nonempty (p := p) (β := β) hne)
    (sSup_dual_le_sInf_primal_of_momentSol_nonempty (p := p) (β := β) hne)

end Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality
