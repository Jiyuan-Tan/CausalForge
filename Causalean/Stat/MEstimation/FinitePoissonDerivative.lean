/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.MEstimation.FinitePoisson
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# One-cell derivatives of finite Poisson projections

This module differentiates the unique maximizer of a full-rank finite Poisson
criterion when one cell mean follows a positive exponential path.
-/

open scoped BigOperators
open Module Filter Topology

namespace Causalean.Stat

-- @node: expCellUpdatedMean
/-- Replace one cell mean by a positive exponential path. -/
noncomputable def expCellUpdatedMean {I : Type*} [DecidableEq I]
    (m : I → ℝ) (j : I) (B x : ℝ) : I → ℝ :=
  Function.update m j (B * Real.exp x)

-- @node: finitePoissonObjective_expCell_argmax_snd_hasDerivAt
/-- For a full-rank finite Poisson projection with one exponentially perturbed
cell mean, the derivative of the selected scalar coefficient is characterized
by the scalar coordinate of the linearized score solution. -/
lemma finitePoissonObjective_expCell_argmax_snd_hasDerivAt
    {U I : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] [Fintype I] [DecidableEq I] [Nonempty I]
    (q m : I → ℝ) (A : (U × ℝ) →ₗ[ℝ] (I → ℝ)) (j : I)
    (B x₀ betaDot : ℝ)
    (hq : ∀ i, 0 < q i) (hm : ∀ i, 0 < m i) (hB : 0 < B)
    (hA : Function.Injective A)
    (hbeta : ∀ v : U × ℝ,
      (∀ d : U × ℝ,
        ∑ i, q i * A d i *
          ((if i = j then B * Real.exp x₀ else 0) -
            Real.exp
              (A (maximizerOrZero
                (finitePoissonObjective q (expCellUpdatedMean m j B x₀) A)) i) *
              A v i) = 0) →
      v.2 = betaDot) :
    HasDerivAt
      (fun x =>
        (maximizerOrZero
          (finitePoissonObjective q (expCellUpdatedMean m j B x) A)).2)
      betaDot x₀ := by
  classical
  let E := U × ℝ
  let b := Basis.ofVectorSpace ℝ E
  let theta₀ : E := maximizerOrZero
    (finitePoissonObjective q (expCellUpdatedMean m j B x₀) A)
  let S : ℝ × E → (Basis.ofVectorSpaceIndex ℝ E → ℝ) := fun p k ↦
    ∑ i, q i * A (b k) i *
      ((if i = j then B * Real.exp p.1 else m i) - Real.exp (A p.2 i))
  let D : (ℝ × E) →L[ℝ] (Basis.ofVectorSpaceIndex ℝ E → ℝ) :=
    ContinuousLinearMap.pi fun k ↦
      ∑ i, (q i * A (b k) i) •
        (((if i = j then B * Real.exp x₀ else 0) • ContinuousLinearMap.fst ℝ ℝ E) -
          (Real.exp (A theta₀ i)) •
            ((ContinuousLinearMap.proj i).comp (A.toContinuousLinearMap.comp
              (ContinuousLinearMap.snd ℝ ℝ E))))
  have hSD : HasFDerivAt S D (x₀, theta₀) := by
    dsimp [S, D]
    rw [hasFDerivAt_pi]
    intro k
    apply HasFDerivAt.fun_sum
    intro i hi
    by_cases hij : i = j
    · subst i
      have hleft := (hasFDerivAt_fst (p := (x₀, theta₀))).exp.const_mul B
      have hright :=
        (((ContinuousLinearMap.proj j).comp
          (A.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ E))).hasFDerivAt
            (x := (x₀, theta₀))).exp
      convert (hleft.sub hright).const_mul (q j * A (b k) j) using 1 <;>
        ext z <;> simp <;> ring
    · have hleft : HasFDerivAt (fun _p : ℝ × E ↦ m i)
          (0 : (ℝ × E) →L[ℝ] ℝ) (x₀, theta₀) :=
        hasFDerivAt_const (x := (x₀, theta₀)) (c := m i)
      have hright :=
        (((ContinuousLinearMap.proj i).comp
          (A.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ E))).hasFDerivAt
            (x := (x₀, theta₀))).exp
      convert (hleft.sub hright).const_mul (q i * A (b k) i) using 1 <;>
        ext z <;> simp [hij] <;> ring
  let L : E →L[ℝ] (Basis.ofVectorSpaceIndex ℝ E → ℝ) :=
    D.comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hL_inj : Function.Injective L := by
    intro v w hvw
    have hzero : L (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    let G : E →ₗ[ℝ] ℝ :=
      { toFun := fun d ↦ ∑ i, q i * Real.exp (A theta₀ i) * A d i * A (v - w) i
        map_add' := by
          intro d e
          simp only [map_add, Pi.add_apply]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        map_smul' := by
          intro c d
          simp only [map_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring }
    have hG : G = 0 := by
      apply b.ext
      intro k
      have hk : L (v - w) k = 0 := by simpa using congrFun hzero k
      norm_num [L, D] at hk
      have hk' : -(∑ i, q i * A (b k) i *
          (Real.exp (A theta₀ i) * A (v - w) i)) = 0 := by
        convert hk using 1
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hij : i = j <;> simp [hij] <;> ring
      dsimp [G]
      have hk'' := neg_eq_zero.mp hk'
      convert hk'' using 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hsum : ∑ i, q i * Real.exp (A theta₀ i) * (A (v - w) i) ^ 2 = 0 := by
      have hu := LinearMap.congr_fun hG (v - w)
      change ∑ i, q i * Real.exp (A theta₀ i) * A (v - w) i * A (v - w) i = 0 at hu
      convert hu using 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hAv : A (v - w) = 0 := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
        mul_nonneg (mul_nonneg (le_of_lt (hq i)) (le_of_lt (Real.exp_pos _)))
          (sq_nonneg _))).mp hsum i (Finset.mem_univ i)
      have hpos : 0 < q i * Real.exp (A theta₀ i) := mul_pos (hq i) (Real.exp_pos _)
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt hpos))
    apply sub_eq_zero.mp
    apply hA
    simpa using hAv
  have hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Basis.ofVectorSpaceIndex ℝ E → ℝ) := by
    simpa [Module.finrank_pi_fintype, finrank_self] using Module.finrank_eq_card_basis b
  have hL_bij : Function.Bijective L := ⟨hL_inj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hL_inj⟩
  have hScont : ContDiffAt ℝ 1 S (x₀, theta₀) := by
    dsimp [S]
    rw [contDiffAt_pi]
    intro k
    apply ContDiffAt.sum
    intro i hi
    have heta : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ A p.2 i) (x₀, theta₀) :=
      ((ContinuousLinearMap.proj i).comp
        (A.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ E))).contDiff.contDiffAt
    by_cases hij : i = j
    · subst i
      have hBexp : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ B * Real.exp p.1) (x₀, theta₀) :=
        contDiffAt_const.mul contDiffAt_fst.exp
      simpa using contDiffAt_const.mul (hBexp.sub heta.exp)
    · have hmconst : ContDiffAt ℝ 1 (fun _p : ℝ × E ↦ m i) (x₀, theta₀) :=
        contDiffAt_const
      simpa [hij] using contDiffAt_const.mul (hmconst.sub heta.exp)
  let himp : IsContDiffImplicitAt 1 S D (x₀, theta₀) :=
    { hasFDerivAt := hSD
      contDiffAt := hScont
      bijective := hL_bij
      ne_zero := by norm_num }
  let phi : ℝ → E := himp.implicitFunction
  have hmexp (x : ℝ) : ∀ i, 0 < expCellUpdatedMean m j B x i := by
    intro i
    simp only [expCellUpdatedMean, Function.update_apply]
    split
    · exact mul_pos hB (Real.exp_pos _)
    · exact hm i
  have hmax0 : ∀ y, finitePoissonObjective q (expCellUpdatedMean m j B x₀) A y ≤
      finitePoissonObjective q (expCellUpdatedMean m j B x₀) A theta₀ := by
    obtain ⟨xstar, hxstar, huniq⟩ := finitePoissonObjective_exists_unique_max
      q (expCellUpdatedMean m j B x₀) A hq (hmexp x₀) hA
    have hex : ∃ x, ∀ y, finitePoissonObjective q (expCellUpdatedMean m j B x₀) A y ≤
        finitePoissonObjective q (expCellUpdatedMean m j B x₀) A x := ⟨xstar, hxstar⟩
    dsimp [theta₀, maximizerOrZero]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hS0 : S (x₀, theta₀) = 0 := by
    funext k
    have hs := finitePoissonObjective_score q (expCellUpdatedMean m j B x₀) A theta₀
      (b k) hmax0
    simpa [S, expCellUpdatedMean, Function.update_apply] using hs
  have hphi0 : phi x₀ = theta₀ := by
    have he := himp.eventually_implicitFunction_apply_eq
    exact he.self_of_nhds (hS0.trans hS0.symm)
  have hphi_score : ∀ᶠ x in nhds x₀, S (x, phi x) = 0 := by
    filter_upwards [himp.apply_implicitFunction] with x hx
    change S (x, himp.implicitFunction x) = 0
    simpa only [hS0] using hx
  have hselected_phi :
      (λ x ↦ maximizerOrZero (finitePoissonObjective q (expCellUpdatedMean m j B x) A))
        =ᶠ[nhds x₀] phi := by
    filter_upwards [hphi_score] with x hx
    let Gx : E →ₗ[ℝ] ℝ :=
      { toFun := fun d ↦ ∑ i, q i * A d i *
          (expCellUpdatedMean m j B x i - Real.exp (A (phi x) i))
        map_add' := by
          intro d e
          simp only [map_add, Pi.add_apply]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        map_smul' := by
          intro c d
          simp only [map_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring }
    have hGx : Gx = 0 := by
      apply b.ext
      intro k
      have hk := congrFun hx k
      simpa [Gx, S, expCellUpdatedMean, Function.update_apply] using hk
    have hscore : ∀ d : E, ∑ i, q i * A d i *
        (expCellUpdatedMean m j B x i - Real.exp (A (phi x) i)) = 0 := by
      intro d
      exact LinearMap.congr_fun hGx d
    have hphimax := finitePoissonObjective_isMax_of_score
      q (expCellUpdatedMean m j B x) A (phi x) (fun i ↦ (hq i).le) hscore
    obtain ⟨xstar, hxstar, huniq⟩ := finitePoissonObjective_exists_unique_max
      q (expCellUpdatedMean m j B x) A hq (hmexp x) hA
    have hex : ∃ z, ∀ y, finitePoissonObjective q (expCellUpdatedMean m j B x) A y ≤
        finitePoissonObjective q (expCellUpdatedMean m j B x) A z := ⟨xstar, hxstar⟩
    rw [maximizerOrZero, dif_pos hex]
    have hchoose : Classical.choose hex = xstar := huniq _ (Classical.choose_spec hex)
    have hphi : phi x = xstar := huniq _ hphimax
    exact hchoose.trans hphi.symm
  have hphidiff : DifferentiableAt ℝ phi x₀ := by
    exact himp.contDiffAt_implicitFunction.differentiableAt (by norm_num)
  let v : E := fderiv ℝ phi x₀ 1
  let P : ℝ →L[ℝ] (ℝ × E) :=
    (ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ phi x₀)
  have hpair : HasFDerivAt (fun x ↦ (x, phi x)) P x₀ := by
    exact (hasFDerivAt_id x₀).prodMk hphidiff.hasFDerivAt
  have hcomp : HasFDerivAt (fun x ↦ S (x, phi x)) (D.comp P) x₀ := by
    have hSD' : HasFDerivAt S D (x₀, phi x₀) := by simpa [hphi0] using hSD
    exact hSD'.comp x₀ hpair
  have hcompzero : HasFDerivAt (fun x ↦ S (x, phi x))
      (0 : ℝ →L[ℝ] (Basis.ofVectorSpaceIndex ℝ E → ℝ)) x₀ := by
    apply (hasFDerivAt_const (x := x₀)
      (c := (0 : Basis.ofVectorSpaceIndex ℝ E → ℝ))).congr_of_eventuallyEq
    exact hphi_score
  have hDPzero : D.comp P = 0 := hcomp.unique hcompzero
  have hvscore_basis (k : Basis.ofVectorSpaceIndex ℝ E) :
      ∑ i, q i * A (b k) i *
        ((if i = j then B * Real.exp x₀ else 0) -
          Real.exp (A theta₀ i) * A v i) = 0 := by
    have hk := congrFun (congrArg (fun F ↦ F 1) hDPzero) k
    dsimp [D, P, v] at hk
    rw [ContinuousLinearMap.sum_apply] at hk
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply] at hk
    simpa [mul_sub] using hk
  let H : E →ₗ[ℝ] ℝ :=
    { toFun := fun d ↦ ∑ i, q i * A d i *
        ((if i = j then B * Real.exp x₀ else 0) - Real.exp (A theta₀ i) * A v i)
      map_add' := by
        intro d e
        simp only [map_add, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      map_smul' := by
        intro c d
        simp only [map_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring }
  have hH : H = 0 := by
    apply b.ext
    exact hvscore_basis
  have hvscore : ∀ d : E, ∑ i, q i * A d i *
      ((if i = j then B * Real.exp x₀ else 0) -
        Real.exp (A theta₀ i) * A v i) = 0 := by
    intro d
    exact LinearMap.congr_fun hH d
  have hvbeta : v.2 = betaDot := hbeta v hvscore
  have hphi_snd : HasDerivAt (fun x ↦ (phi x).2) v.2 x₀ := by
    have hsnd :=
      (ContinuousLinearMap.snd ℝ U ℝ).hasFDerivAt.comp x₀ hphidiff.hasFDerivAt
    convert hsnd.hasDerivAt using 1 <;> simp [v]
  rw [← hvbeta]
  apply hphi_snd.congr_of_eventuallyEq
  exact hselected_phi.fun_comp (fun z : E ↦ z.2)

end Causalean.Stat
