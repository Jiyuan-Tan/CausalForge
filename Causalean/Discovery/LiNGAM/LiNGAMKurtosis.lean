/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.LinearAlgebra.MonomialMatrix
import Causalean.Discovery.LiNGAM.Kurtosis

/-!
# LiNGAM identification, kurtosis route

This file assembles a LiNGAM identification theorem under the standard ICA
assumption that the disturbances have **non-zero fourth cumulant of one common
sign** (all super-Gaussian or all sub-Gaussian).  This kurtosis route bypasses
the general Darmois–Skitovich theorem and Marcinkiewicz's theorem on entire
functions:

* `colSupport_of_kurtosis` (`Kurtosis.lean`) supplies the column support `Wᵢⱼ·Wₖⱼ = 0`
  from fourth cumulants instead of from Darmois–Skitovich;
* `ica_genPerm_relation` (here) is the purely linear-algebraic core: column support plus
  invertibility give the generalized permutation relation between `A⁻¹` and `A'⁻¹`;
* `eq_of_genPerm_triangular_unitDiag` (`Mathlib/LinearAlgebra/MonomialMatrix.lean`) then forces
  `A⁻¹ = A'⁻¹`.
-/

namespace Causalean.Discovery.LiNGAM

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.LinearAlgebra
open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The linear-algebra core of ICA identifiability: if the generalized matrix
`W = A'⁻¹ A` has at most one non-zero entry per column (the column-support fact),
then `A⁻¹` and `A'⁻¹` agree up to a generalized permutation. -/
theorem ica_genPerm_relation {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℝ}
    (hAu : IsUnit A.det) (hA'u : IsUnit A'.det)
    (hcol : ∀ j i k, i ≠ k → (A'⁻¹ * A) i j = 0 ∨ (A'⁻¹ * A) k j = 0) :
    ∃ (τ : Equiv.Perm (Fin n)) (d : Fin n → ℝ),
      ∀ i j, A'⁻¹ i j = d i * A⁻¹ (τ i) j := by
  classical
  let W : Matrix (Fin n) (Fin n) ℝ := A'⁻¹ * A
  have hWu : IsUnit W.det := by
    dsimp [W]
    rw [Matrix.det_mul]
    exact IsUnit.mul (Matrix.isUnit_nonsing_inv_det A' hA'u) hAu
  obtain ⟨τ, d, _hd, hWform⟩ := genPerm_of_invertible_of_colSupport hWu hcol
  refine ⟨τ, d, ?_⟩
  intro i j
  have hAinv : A'⁻¹ = W * A⁻¹ := by
    calc
      A'⁻¹ = A'⁻¹ * 1 := by rw [Matrix.mul_one]
      _ = A'⁻¹ * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hAu]
      _ = W * A⁻¹ := by
        change A'⁻¹ * (A * A⁻¹) = (A'⁻¹ * A) * A⁻¹
        rw [Matrix.mul_assoc]
  calc
    A'⁻¹ i j = (W * A⁻¹) i j := by rw [hAinv]
    _ = ∑ c, W i c * A⁻¹ c j := by rw [Matrix.mul_apply]
    _ = d i * A⁻¹ (τ i) j := by
      rw [Finset.sum_eq_single (τ i)]
      · simp [hWform]
      · intro c _hc hc
        simp [hWform, hc]
      · simp

/-- **LiNGAM identification theorem (kurtosis route, Marcinkiewicz-free).**  Two
LiNGAM models with mixing matrices `A, A'` (coefficient matrices `A⁻¹ = I − B`,
`A'⁻¹ = I − B'`): both invertible, both with unit diagonal (`Bᵢᵢ = 0`), the first
acyclic in a causal order `σ`, driven by independent centered finite-fourth-moment
disturbances with non-zero fourth cumulant of one common sign, and producing the same
observed law.  Then the coefficient matrices coincide, `A⁻¹ = A'⁻¹` (i.e. `B = B'`).

Proof: push `hobs` through `A'⁻¹` so `W·e =ᵈ e'` has independent components, hence the
two output coordinates are independent; `colSupport_of_kurtosis` gives the column
support; `ica_genPerm_relation` upgrades it to the generalized-permutation relation;
`eq_of_genPerm_triangular_unitDiag` concludes. -/
theorem lingam_identifiability_kurtosis {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℝ}
    (hAu : IsUnit A.det) (hA'u : IsUnit A'.det)
    (hCdiag : ∀ i, A⁻¹ i i = 1) (hC'diag : ∀ i, A'⁻¹ i i = 1)
    {σ : Equiv.Perm (Fin n)} (hacyc : ∀ i j, σ i < σ j → A⁻¹ i j = 0)
    {e e' : Ω → Fin n → ℝ}
    (hem : ∀ i, Measurable (fun ω => e ω i)) (he'm : ∀ i, Measurable (fun ω => e' ω i))
    (heI : iIndepFun (fun i ω => e ω i) P) (he'I : iIndepFun (fun i ω => e' ω i) P)
    (heL4 : ∀ i, MemLp (fun ω => e ω i) 4 P)
    (hcent : ∀ i, ∫ ω, e ω i ∂P = 0)
    (hkurt : (∀ j, 0 < kurt (fun ω => e ω j) P) ∨ (∀ j, kurt (fun ω => e ω j) P < 0))
    (hobs : P.map (fun ω => A *ᵥ e ω) = P.map (fun ω => A' *ᵥ e' ω)) :
    A⁻¹ = A'⁻¹ := by
  classical
  let W : Matrix (Fin n) (Fin n) ℝ := A'⁻¹ * A
  have hyindep : ∀ i k, i ≠ k →
      IndepFun (fun ω => ∑ j, W i j * e ω j) (fun ω => ∑ j, W k j * e ω j) P := by
    let y : Ω → Fin n → ℝ := fun ω => W *ᵥ e ω
    have hy_meas : Measurable y := by
      fun_prop
    have he'_meas : Measurable e' := by
      rw [measurable_pi_iff]
      intro i
      exact he'm i
    let g : (Fin n → ℝ) → Fin n → ℝ := fun v => A'⁻¹ *ᵥ v
    have hg_meas : Measurable g := by
      fun_prop
    have hAe_meas : Measurable (fun ω => A *ᵥ e ω) := by
      fun_prop
    have hA'e'_meas : Measurable (fun ω => A' *ᵥ e' ω) := by
      fun_prop
    have hy : P.map y = P.map e' := by
      have hmap : Measure.map g (P.map (fun ω => A *ᵥ e ω)) =
          Measure.map g (P.map (fun ω => A' *ᵥ e' ω)) := by
        rw [hobs]
      rw [Measure.map_map hg_meas hAe_meas, Measure.map_map hg_meas hA'e'_meas] at hmap
      simpa [y, g, W, Function.comp_def, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hA'u, Matrix.one_mulVec] using hmap
    have hy_coord : ∀ r, P.map (fun ω => y ω r) = P.map (fun ω => e' ω r) := by
      intro r
      let π : (Fin n → ℝ) → ℝ := fun v => v r
      have h := congrArg (Measure.map π) hy
      rw [Measure.map_map (measurable_pi_apply r) hy_meas,
        Measure.map_map (measurable_pi_apply r) he'_meas] at h
      simpa [π, Function.comp_def] using h
    have hy_pair :
        ∀ i k, P.map (fun ω => (y ω i, y ω k)) = P.map (fun ω => (e' ω i, e' ω k)) := by
      intro i k
      let proj : (Fin n → ℝ) → ℝ × ℝ := fun v => (v i, v k)
      have hproj : Measurable proj := (measurable_pi_apply i).prodMk (measurable_pi_apply k)
      have h := congrArg (Measure.map proj) hy
      rw [Measure.map_map hproj hy_meas, Measure.map_map hproj he'_meas] at h
      simpa [proj, Function.comp_def] using h
    have hy_indep : ∀ {i k : Fin n}, i ≠ k → IndepFun (fun ω => y ω i) (fun ω => y ω k) P := by
      intro i k hik
      refine (indepFun_iff_map_prod_eq_prod_map_map
        (hy_meas.eval (a := i)).aemeasurable (hy_meas.eval (a := k)).aemeasurable).mpr ?_
      have he'_prod := (indepFun_iff_map_prod_eq_prod_map_map
        (he'm i).aemeasurable (he'm k).aemeasurable).mp (he'I.indepFun hik)
      calc
        P.map (fun ω => (y ω i, y ω k)) = P.map (fun ω => (e' ω i, e' ω k)) := hy_pair i k
        _ = (P.map (fun ω => e' ω i)).prod (P.map (fun ω => e' ω k)) := he'_prod
        _ = (P.map (fun ω => y ω i)).prod (P.map (fun ω => y ω k)) := by
          rw [← hy_coord i, ← hy_coord k]
    intro i k hik
    have h := hy_indep hik
    simpa [y, Matrix.mulVec, dotProduct, Finset.mul_sum] using h
  have hcol : ∀ j i k, i ≠ k → W i j = 0 ∨ W k j = 0 := by
    intro j i k hik
    exact mul_eq_zero.mp
      (colSupport_of_kurtosis (W := W) (hmeas := hem) (hindep := heI) (hL4 := heL4)
        (hcent := hcent) (hsign := hkurt) hik (hyindep i k hik) j)
  have hcol' : ∀ j i k, i ≠ k → (A'⁻¹ * A) i j = 0 ∨ (A'⁻¹ * A) k j = 0 := by
    simpa [W] using hcol
  obtain ⟨τ, d, hgp⟩ := ica_genPerm_relation hAu hA'u hcol'
  exact eq_of_genPerm_triangular_unitDiag hCdiag hC'diag hacyc (τ := τ) (d := d) hgp

end Causalean.Discovery.LiNGAM
