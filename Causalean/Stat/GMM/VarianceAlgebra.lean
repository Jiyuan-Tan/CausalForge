/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# GMM asymptotic-variance algebra and the optimal-weighting theorem

Pure operator-algebra core of the Generalized Method of Moments (Hansen 1982).
No measure theory: everything here is finite-dimensional linear algebra on
continuous linear maps between real inner-product spaces.

Fix a Jacobian `G : E →L[ℝ] F` (the derivative of the population moment
`θ ↦ ∫ g(θ) dP` at the truth; `E` is the parameter space, `F` the moment space,
`dim E ≤ dim F`), a symmetric positive-definite weighting operator `W : F →L F`,
and the moment covariance `Cov : F →L F` (symmetric, positive).  The GMM
estimator with weighting `W` has **sandwich asymptotic variance**

    V(W) = (GᵀWG)⁻¹ GᵀW Σ WG (GᵀWG)⁻¹            (`gmmSandwich`)

while the **efficient** choice `W = Σ⁻¹` gives

    V★ = (GᵀΣ⁻¹G)⁻¹.                              (`effInv`)

(`Cov` stands for the covariance `Σ`, which is a reserved token in Lean.)

The headline `gmm_efficiency` is the Löwner-order optimality (Hansen 1982,
Thm 3.2):  `V(W) − V★` is a positive operator, with equality at `W = Σ⁻¹`.

The proof is the classical one.  With

    A := (GᵀWG)⁻¹ GᵀW,        B := (GᵀΣ⁻¹G)⁻¹ GᵀΣ⁻¹,

one has `AG = BG = id` (the inverse witnesses), and the cross terms collapse,
`AΣBᵀ = BΣAᵀ = BΣBᵀ = V★`, because `Σ` and `Σ⁻¹` cancel against the bread.
Hence

    (A − B) Σ (A − B)ᵀ = V(W) − V★,

and the left side is positive by `IsPositive.conj_adjoint` applied to `Σ ⪰ 0`.

Inverses are carried as *data with two-sided witnesses* (mirroring
`ZEstimatorRegularity.J₀_inv`/`J₀_inverse`) so no operator inverse needs to be
constructed; invertibility of `GᵀWG`/`Σ`/`GᵀΣ⁻¹G` is supplied by the caller.
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # GMM Variance Algebra

This file proves the finite-dimensional operator algebra behind GMM asymptotic
variance.  It defines the GMM bread operator `gmmBread` and the sandwich
variance operator `gmmSandwich`, using supplied two-sided inverse witnesses
rather than constructing operator inverses.

The headline theorem `gmm_efficiency` is Hansen's optimal-weighting result in
Loewner order: for a symmetric weighting `W`, positive covariance `Cov`, and
inverse covariance `CovInv`, the sandwich variance
`gmmSandwich G W Cov breadInv` dominates the efficient variance `effInv`.
The helper `adjoint_inv_self` records self-adjointness of a right inverse of a
self-adjoint operator and is used to collapse the cross terms in the proof. -/

namespace Causalean.Stat

open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The **bread** operator `GᵀWG : E →L E` of a GMM problem with Jacobian `G`
and weighting `W`.  Symmetric whenever `W` is, and invertible whenever `G` has
full column rank and `W ≻ 0`. -/
noncomputable def gmmBread (G : E →L[ℝ] F) (W : F →L[ℝ] F) : E →L[ℝ] E :=
  (adjoint G) ∘L W ∘L G

/-- The **sandwich asymptotic variance** `(GᵀWG)⁻¹ GᵀW Σ WG (GᵀWG)⁻¹`, given a
two-sided inverse `breadInv` of `GᵀWG`. -/
noncomputable def gmmSandwich (G : E →L[ℝ] F) (W Cov : F →L[ℝ] F)
    (breadInv : E →L[ℝ] E) : E →L[ℝ] E :=
  breadInv ∘L (adjoint G) ∘L W ∘L Cov ∘L W ∘L G ∘L breadInv

/-- The adjoint (self-adjointness) of a right inverse of a self-adjoint
operator: if `adjoint M = M` and `M ∘L N = id`, then `adjoint N = N`.
(`adjoint N` is then a left inverse of `M`, and in finite dimension a one-sided
inverse of an operator that already has a two-sided one is unique.)
Shared with `OverID.lean`. -/
theorem adjoint_inv_self {M N : E →L[ℝ] E}
    (hM : adjoint M = M) (hMN : M ∘L N = ContinuousLinearMap.id ℝ E) :
    adjoint N = N := by
  have h1 : adjoint N ∘L M = ContinuousLinearMap.id ℝ E := by
    have := congrArg adjoint hMN
    rwa [adjoint_comp, hM, adjoint_id] at this
  calc adjoint N = adjoint N ∘L ContinuousLinearMap.id ℝ E := by rw [comp_id]
    _ = adjoint N ∘L (M ∘L N) := by rw [hMN]
    _ = (adjoint N ∘L M) ∘L N := by rw [← comp_assoc]
    _ = ContinuousLinearMap.id ℝ E ∘L N := by rw [h1]
    _ = N := by rw [id_comp]

/-- `gmmBread G W` is self-adjoint when `W` is. -/
private theorem adjoint_gmmBread {G : E →L[ℝ] F} {W : F →L[ℝ] F}
    (hW : adjoint W = W) : adjoint (gmmBread G W) = gmmBread G W := by
  unfold gmmBread
  simp only [adjoint_comp, adjoint_adjoint, hW, comp_assoc]

/-- **GMM optimal-weighting theorem (Hansen 1982, Thm 3.2).**

For a Jacobian `G`, symmetric weighting `W`, and positive symmetric covariance
`Cov` (with `Cov⁻¹ = CovInv` and the two breads `GᵀWG`, `GᵀΣ⁻¹G` invertible via
the supplied two-sided inverses), the sandwich variance dominates the efficient
variance in the Löwner order:

    gmmSandwich G W Cov breadInv  −  effInv   is positive,

i.e. `V(W) ⪰ V★ = (GᵀΣ⁻¹G)⁻¹`. -/
theorem gmm_efficiency
    (G : E →L[ℝ] F) (W Cov CovInv : F →L[ℝ] F)
    (hWsa : adjoint W = W) (hCovpos : Cov.IsPositive)
    (hCovinvL : CovInv ∘L Cov = ContinuousLinearMap.id ℝ F)
    (hCovinvR : Cov ∘L CovInv = ContinuousLinearMap.id ℝ F)
    (breadInv : E →L[ℝ] E)
    (hbL : breadInv ∘L gmmBread G W = ContinuousLinearMap.id ℝ E)
    (hbR : gmmBread G W ∘L breadInv = ContinuousLinearMap.id ℝ E)
    (effInv : E →L[ℝ] E)
    (_heL : effInv ∘L gmmBread G CovInv = ContinuousLinearMap.id ℝ E)
    (heR : gmmBread G CovInv ∘L effInv = ContinuousLinearMap.id ℝ E) :
    (gmmSandwich G W Cov breadInv - effInv).IsPositive := by
  -- Self-adjointness of Cov, CovInv, breadInv, effInv.
  have hCovsa : adjoint Cov = Cov :=
    (ContinuousLinearMap.isSelfAdjoint_iff' ).mp hCovpos.isSelfAdjoint
  have hCovInvSa : adjoint CovInv = CovInv := adjoint_inv_self hCovsa hCovinvR
  have hbSa : adjoint breadInv = breadInv :=
    adjoint_inv_self (adjoint_gmmBread hWsa) hbR
  have heSa : adjoint effInv = effInv :=
    adjoint_inv_self (adjoint_gmmBread hCovInvSa) heR
  -- Pointwise forms of the inverse witnesses and the bread definition.
  have pCovR : ∀ y, Cov (CovInv y) = y := fun y => by
    rw [← comp_apply, hCovinvR, id_apply]
  have pCovL : ∀ y, CovInv (Cov y) = y := fun y => by
    rw [← comp_apply, hCovinvL, id_apply]
  have pBreadW : ∀ y, gmmBread G W y = adjoint G (W (G y)) := fun y => by
    simp only [gmmBread, comp_apply]
  have pBreadC : ∀ y, gmmBread G CovInv y = adjoint G (CovInv (G y)) := fun y => by
    simp only [gmmBread, comp_apply]
  have pbL : ∀ x, breadInv (gmmBread G W x) = x := fun x => by
    rw [← comp_apply, hbL, id_apply]
  have pbR : ∀ x, gmmBread G W (breadInv x) = x := fun x => by
    rw [← comp_apply, hbR, id_apply]
  have peR : ∀ x, gmmBread G CovInv (effInv x) = x := fun x => by
    rw [← comp_apply, heR, id_apply]
  -- The two "weight" maps A := breadInv Gᵀ W and B := effInv Gᵀ CovInv  (F →L E).
  set A : F →L[ℝ] E := breadInv ∘L (adjoint G) ∘L W with hA
  set B : F →L[ℝ] E := effInv ∘L (adjoint G) ∘L CovInv with hB
  have pA : ∀ y, A y = breadInv (adjoint G (W y)) := fun y => by
    rw [hA]; simp only [comp_apply]
  have pB : ∀ y, B y = effInv (adjoint G (CovInv y)) := fun y => by
    rw [hB]; simp only [comp_apply]
  -- Adjoints: Aᵀ = W G breadInv, Bᵀ = CovInv G effInv.
  have hAadj : adjoint A = W ∘L G ∘L breadInv := by
    simp only [hA, adjoint_comp, adjoint_adjoint, hWsa, hbSa, comp_assoc]
  have hBadj : adjoint B = CovInv ∘L G ∘L effInv := by
    simp only [hB, adjoint_comp, adjoint_adjoint, hCovInvSa, heSa, comp_assoc]
  have pAadj : ∀ y, adjoint A y = W (G (breadInv y)) := fun y => by
    rw [hAadj]; simp only [comp_apply]
  have pBadj : ∀ y, adjoint B y = CovInv (G (effInv y)) := fun y => by
    rw [hBadj]; simp only [comp_apply]
  -- The four bilinear terms.  Each reduces to gmmSandwich or effInv.
  have hAA : A ∘L Cov ∘L adjoint A = gmmSandwich G W Cov breadInv := by
    ext x; simp only [gmmSandwich, comp_apply, pA, pAadj]
  have hAB : A ∘L Cov ∘L adjoint B = effInv := by
    ext x; simp only [comp_apply, pA, pBadj, pCovR]
    rw [← pBreadW, pbL]
  have hBA : B ∘L Cov ∘L adjoint A = effInv := by
    ext x; simp only [comp_apply, pB, pAadj, pCovL]
    rw [← pBreadW, pbR]
  have hBB : B ∘L Cov ∘L adjoint B = effInv := by
    ext x; simp only [comp_apply, pB, pBadj, pCovR]
    rw [← pBreadC, peR]
  -- Assemble:  (A − B) Cov (A − B)ᵀ = gmmSandwich − effInv.
  have hconj : (A - B) ∘L Cov ∘L adjoint (A - B)
      = gmmSandwich G W Cov breadInv - effInv := by
    rw [map_sub]
    simp only [sub_comp, comp_sub, hAA, hAB, hBA, hBB]
    abel
  -- Positivity by conjugation of Cov ⪰ 0.
  rw [← hconj]
  exact hCovpos.conj_adjoint (A - B)

end Causalean.Stat
