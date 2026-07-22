/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SymmetryReduction
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SpectralCoordinates
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySlice
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ReducedSimplexBridge
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SimplexTruncation

/-! # Rounding-gap reduction

Assembles `prop:symmetry-reduction`, `lem:block-spectral-coordinates`, and
`lem:pm-reduced-slice-characterization` into the reduced-coordinate identity for
the implementability gap: `Δ_m^± = min_{T_m ∩ {y+z ≥ d_m}} φ − min_{T_m} φ`. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: lem:rounding-gap-reduction
/-- The implementability gap equals the reduced-coordinate implementable-minus-relaxed
value: `Δ_m^±(r,κ) = implementableReducedValue − relaxedReducedValue`. -/
lemma rounding_gap_reduction (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) :
    implementabilityGap m a b r kappa
      = implementableReducedValue m a b r kappa - relaxedReducedValue m a b r kappa := by
  have _hk : 0 ≤ kappa := hk
  have hm : 2 ≤ m := hHom.1
  have coord_inv : ∀ x y z : ℝ, InReducedTriangle m x y z →
      let u := 1 - x
      let v := (z - y) / (2 * (m : ℝ))
      (1 - u = x) ∧
      (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v = y) ∧
      (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v = z) := by
    intro x y z htri u v
    rcases htri with ⟨_hx, _hy, _hz, hsum⟩
    have hm0 : (m : ℝ) ≠ 0 := by
      have : (0 : ℕ) < m := lt_of_lt_of_le (by decide : 0 < 2) hm
      exact_mod_cast (ne_of_gt this)
    have hq : qParam m = 2 * ((m : ℝ) - 1) := rfl
    constructor
    · simp [u]
    constructor
    · dsimp [u, v]
      rw [hq] at hsum
      field_simp [hm0]
      nlinarith [hsum]
    · dsimp [u, v]
      rw [hq] at hsum
      field_simp [hm0]
      nlinarith [hsum]
  have hRel :
      Set.image (designObjective m a b r kappa) (blockElliptope m a b) =
        { val : ℝ | ∃ x y z, InReducedTriangle m x y z ∧
          val = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z } := by
    ext val
    constructor
    · rintro ⟨X, hX, rfl⟩
      rcases hX with ⟨u, v, rfl, hmem⟩
      have hspec := block_spectral_coordinates m a b r kappa u v hHom
      have htri : InReducedTriangle m (1 - u)
          (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
        exact hspec.1.mp ⟨u, v, rfl, hmem⟩
      exact ⟨1 - u, 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v,
        1 + ((m : ℝ) - 1) * u + (m : ℝ) * v, htri, hspec.2.1⟩
    · rintro ⟨x, y, z, htri, rfl⟩
      let u : ℝ := 1 - x
      let v : ℝ := (z - y) / (2 * (m : ℝ))
      have hcoords := coord_inv x y z htri
      have htri_uv : InReducedTriangle m (1 - u)
          (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
        simpa [u, v, hcoords.1, hcoords.2.1, hcoords.2.2] using htri
      have hspec := block_spectral_coordinates m a b r kappa u v hHom
      have hmem : blockSymMatrix m u v ∈ blockElliptope m a b := hspec.1.mpr htri_uv
      refine ⟨blockSymMatrix m u v, hmem, ?_⟩
      simpa [u, v, hcoords.1, hcoords.2.1, hcoords.2.2] using hspec.2.1
  have hImp :
      Set.image (designObjective m a b r kappa) (implementableCovarianceClass m) =
        { val : ℝ | ∃ x y z, InReducedTriangle m x y z ∧ parityThreshold m ≤ y + z ∧
          val = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z } := by
    ext val
    constructor
    · rintro ⟨X, hX, rfl⟩
      rcases hX with ⟨D, hDmem, hXeq⟩
      rcases secondMoment_blockSym_of_exchangeable m hm D hDmem with ⟨u, v, hblock⟩
      have hslice := pm_slice_forward m hm u v D hblock
      have hspec := block_spectral_coordinates m a b r kappa u v hHom
      refine ⟨1 - u, 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v,
        1 + ((m : ℝ) - 1) * u + (m : ℝ) * v, hslice.1, hslice.2, ?_⟩
      rw [hXeq, hblock]
      exact hspec.2.1
    · rintro ⟨x, y, z, htri, hpar, rfl⟩
      let u : ℝ := 1 - x
      let v : ℝ := (z - y) / (2 * (m : ℝ))
      have hcoords := coord_inv x y z htri
      have htri_uv : InReducedTriangle m (1 - u)
          (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
        simpa [u, v, hcoords.1, hcoords.2.1, hcoords.2.2] using htri
      have hpar_uv : parityThreshold m ≤
          (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) +
            (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
        simpa [u, v, hcoords.2.1, hcoords.2.2] using hpar
      have himp : blockSymMatrix m u v ∈ implementableCovarianceClass m := by
        rw [pm_reduced_slice_characterization m hm u v]
        exact ⟨htri_uv, hpar_uv⟩
      have hspec := block_spectral_coordinates m a b r kappa u v hHom
      refine ⟨blockSymMatrix m u v, himp, ?_⟩
      simpa [u, v, hcoords.1, hcoords.2.1, hcoords.2.2] using hspec.2.1
  unfold implementabilityGap implementableReducedValue relaxedReducedValue
  rw [hImp, hRel]

-- @node: implementabilityGap_nonneg
/-- **Range lemma for `Δ_m^±`.** The implementability gap lands in its core-declared
space `[0,∞)`: `0 ≤ Δ_m^±(r,κ)`. The reduction lemma identifies it with the reduced
constrained-minus-unconstrained value, whose nonnegativity is proved by
`roundingLossCertificate_nonneg`.
@realizes Delta_m^pm(r,kappa)(range [0,∞) pinned via the reduced
constrained-minus-unconstrained identity) -/
lemma implementabilityGap_nonneg (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hr0 : 0 ≤ r) (hk : 0 ≤ kappa) :
    0 ≤ implementabilityGap m a b r kappa := by
  rw [rounding_gap_reduction m a b r kappa hHom hk]
  simpa [roundingLossCertificate] using
    roundingLossCertificate_nonneg m a b r kappa hHom hr0 hk

/-- If the relaxed reduced objective has a unique minimizer outside the implementable
parity slice, and the implementable reduced problem is attained, then the implementability
gap is strictly positive. -/
lemma pos_gap_of_unique_min_outside_slice (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa)
    (X_rel X_impl : ℝ × ℝ × ℝ)
    (hRelMin : InReducedTriangle m X_rel.1 X_rel.2.1 X_rel.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_rel.1 X_rel.2.1 X_rel.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z)
    (hRelUnique : ∃! t : ℝ × ℝ × ℝ,
      InReducedTriangle m t.1 t.2.1 t.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              t.1 t.2.1 t.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z)
    (hOutside : X_rel.2.1 + X_rel.2.2 < parityThreshold m)
    (hImplMin : InReducedTriangle m X_impl.1 X_impl.2.1 X_impl.2.2 ∧
      parityThreshold m ≤ X_impl.2.1 + X_impl.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z → parityThreshold m ≤ y + z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z) :
    0 < implementabilityGap m a b r kappa := by
  let obj : ℝ × ℝ × ℝ → ℝ := fun t =>
    reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa t.1 t.2.1 t.2.2
  have hImpl_ne : X_impl ≠ X_rel := by
    intro hEq
    have hpar : parityThreshold m ≤ X_rel.2.1 + X_rel.2.2 := by
      simpa [hEq] using hImplMin.2.1
    linarith
  have hRel_le_impl : obj X_rel ≤ obj X_impl :=
    hRelMin.2 X_impl.1 X_impl.2.1 X_impl.2.2 hImplMin.1
  have hStrict : obj X_rel < obj X_impl := by
    by_contra hnot
    have hImpl_le_rel : obj X_impl ≤ obj X_rel := le_of_not_gt hnot
    have hEqObj : obj X_impl = obj X_rel := le_antisymm hImpl_le_rel hRel_le_impl
    have hImplRelMin : InReducedTriangle m X_impl.1 X_impl.2.1 X_impl.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              X_impl.1 X_impl.2.1 X_impl.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
      refine ⟨hImplMin.1, ?_⟩
      intro x y z hT
      rw [show reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              X_impl.1 X_impl.2.1 X_impl.2.2 =
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              X_rel.1 X_rel.2.1 X_rel.2.2 from hEqObj]
      exact hRelMin.2 x y z hT
    rcases hRelUnique with ⟨X0, hX0, huniq⟩
    have hImpl_eq : X_impl = X0 := huniq X_impl hImplRelMin
    have hRel_eq : X_rel = X0 := huniq X_rel hRelMin
    exact hImpl_ne (hImpl_eq.trans hRel_eq.symm)
  have hRelInf :
      relaxedReducedValue m a b r kappa = obj X_rel := by
    unfold relaxedReducedValue
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨obj X_rel,
        ⟨X_rel.1, X_rel.2.1, X_rel.2.2, hRelMin.1, rfl⟩⟩
    · rintro _ ⟨x, y, z, hT, rfl⟩
      exact hRelMin.2 x y z hT
    · intro w hw
      exact ⟨obj X_rel,
        ⟨X_rel.1, X_rel.2.1, X_rel.2.2, hRelMin.1, rfl⟩, hw⟩
  have hImplInf :
      implementableReducedValue m a b r kappa = obj X_impl := by
    unfold implementableReducedValue
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨obj X_impl,
        ⟨X_impl.1, X_impl.2.1, X_impl.2.2, hImplMin.1, hImplMin.2.1, rfl⟩⟩
    · rintro _ ⟨x, y, z, hT, hpar, rfl⟩
      exact hImplMin.2.2 x y z hT hpar
    · intro w hw
      exact ⟨obj X_impl,
        ⟨X_impl.1, X_impl.2.1, X_impl.2.2, hImplMin.1, hImplMin.2.1, rfl⟩, hw⟩
  rw [rounding_gap_reduction m a b r kappa hHom hk, hImplInf, hRelInf]
  exact sub_pos.mpr hStrict

/-- If a reduced triangle point globally minimizes the relaxed reduced objective,
then the `sInf` defining `relaxedReducedValue` is its objective value. -/
lemma relaxedReducedValue_eq_of_min (m : ℕ) (a b r kappa : ℝ)
    (X_rel : ℝ × ℝ × ℝ)
    (hRelMin : InReducedTriangle m X_rel.1 X_rel.2.1 X_rel.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_rel.1 X_rel.2.1 X_rel.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z) :
    relaxedReducedValue m a b r kappa =
      reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
        X_rel.1 X_rel.2.1 X_rel.2.2 := by
  unfold relaxedReducedValue
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
        X_rel.1 X_rel.2.1 X_rel.2.2,
      ⟨X_rel.1, X_rel.2.1, X_rel.2.2, hRelMin.1, rfl⟩⟩
  · rintro _ ⟨x, y, z, hT, rfl⟩
    exact hRelMin.2 x y z hT
  · intro w hw
    exact ⟨reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
        X_rel.1 X_rel.2.1 X_rel.2.2,
      ⟨X_rel.1, X_rel.2.1, X_rel.2.2, hRelMin.1, rfl⟩, hw⟩

/-- If a reduced triangle point globally minimizes the parity-truncated reduced
objective, then the `sInf` defining `implementableReducedValue` is its objective
value. -/
lemma implementableReducedValue_eq_of_min (m : ℕ) (a b r kappa : ℝ)
    (X_impl : ℝ × ℝ × ℝ)
    (hImplMin : InReducedTriangle m X_impl.1 X_impl.2.1 X_impl.2.2 ∧
      parityThreshold m ≤ X_impl.2.1 + X_impl.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z → parityThreshold m ≤ y + z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z) :
    implementableReducedValue m a b r kappa =
      reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
        X_impl.1 X_impl.2.1 X_impl.2.2 := by
  unfold implementableReducedValue
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
        X_impl.1 X_impl.2.1 X_impl.2.2,
      ⟨X_impl.1, X_impl.2.1, X_impl.2.2, hImplMin.1, hImplMin.2.1, rfl⟩⟩
  · rintro _ ⟨x, y, z, hT, hpar, rfl⟩
    exact hImplMin.2.2 x y z hT hpar
  · intro w hw
    exact ⟨reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
        X_impl.1 X_impl.2.1 X_impl.2.2,
      ⟨X_impl.1, X_impl.2.1, X_impl.2.2, hImplMin.1, hImplMin.2.1, rfl⟩, hw⟩

lemma exists_relaxed_reduced_minimizer (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) :
    ∃ X_rel : ℝ × ℝ × ℝ,
      InReducedTriangle m X_rel.1 X_rel.2.1 X_rel.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              X_rel.1 X_rel.2.1 X_rel.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
  classical
  have hm : 2 ≤ m := hHom.1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hq0 : 0 ≤ qParam m := le_of_lt hq
  have hM : 0 < 2 * (m : ℝ) := by positivity
  let alpha : Fin 3 → ℝ := ![cX m a b r / qParam m, cY b r, cZ m]
  let beta : Fin 3 → ℝ := ![1 / qParam m, 1, 1]
  have hbetaPos : ∀ i, 0 < beta i := by
    intro i
    fin_cases i
    · have : 0 < 1 / qParam m := by positivity
      simpa [beta] using this
    · simp [beta]
    · simp [beta]
  have hSimplexMin : ∃ t_rel : Fin 3 → ℝ,
      InSimplex (2 * (m : ℝ)) t_rel ∧
        ∀ s : Fin 3 → ℝ, InSimplex (2 * (m : ℝ)) s →
          wsObj alpha beta kappa t_rel ≤ wsObj alpha beta kappa s := by
    by_cases hkpos : 0 < kappa
    · obtain ⟨⟨S, lam⟩, hp, _huniq⟩ :=
        (weighted_simplex_active_set (2 * (m : ℝ)) hM alpha beta kappa hbetaPos hk).1
          hkpos
      refine ⟨activeSetPoint (2 * (m : ℝ)) alpha beta S lam, hp.2.1, ?_⟩
      intro s hs
      by_cases hsEq : s = activeSetPoint (2 * (m : ℝ)) alpha beta S lam
      · simp [hsEq]
      · exact le_of_lt (hp.2.2.1 s hs hsEq)
    · have hk0 : kappa = 0 := le_antisymm (le_of_not_gt hkpos) hk
      subst kappa
      obtain ⟨k, hkmin⟩ := (Finite.exists_min alpha : ∃ k : Fin 3, ∀ i, alpha k ≤ alpha i)
      let t_rel : Fin 3 → ℝ := fun i => if i = k then 2 * (m : ℝ) else 0
      have hface : t_rel ∈ exposedMinFace (2 * (m : ℝ)) alpha := by
        refine ⟨?_, ?_⟩
        · constructor
          · intro i
            dsimp [t_rel]
            by_cases hi : i = k
            · simp [hi, le_of_lt hM]
            · simp [hi]
          · dsimp [t_rel]
            fin_cases k <;> simp [Fin.sum_univ_three]
        · intro i hi j
          dsimp [t_rel] at hi
          by_cases hik : i = k
          · simpa [hik] using hkmin j
          · simp [hik] at hi
      exact ⟨t_rel, hface.1,
        exposedMinFace_isMinimizer (2 * (m : ℝ)) hM alpha beta t_rel hface⟩
  rcases hSimplexMin with ⟨t_rel, hrelS, hrelMin⟩
  let X_rel : ℝ × ℝ × ℝ := (t_rel 0 / qParam m, t_rel 1, t_rel 2)
  refine ⟨X_rel, by simpa [X_rel] using simplex_to_reducedTriangle m t_rel hq hrelS, ?_⟩
  intro x y z hT
  let s : Fin 3 → ℝ := ![qParam m * x, y, z]
  have hsS : InSimplex (2 * (m : ℝ)) s :=
    reducedTriangle_to_simplex m x y z hq0 hT
  have hle := hrelMin s hsS
  have hleft :
      wsObj alpha beta kappa t_rel =
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
          X_rel.1 X_rel.2.1 X_rel.2.2 := by
    rw [show wsObj alpha beta kappa t_rel =
        wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
          kappa t_rel by rfl]
    rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
      kappa t_rel (ne_of_gt hq)]
  have hright :
      wsObj alpha beta kappa s =
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
    rw [show wsObj alpha beta kappa s =
        wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
          kappa s by rfl]
    rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
      kappa x y z (ne_of_gt hq)]
  simpa [hleft, hright] using hle

lemma exists_implementable_reduced_minimizer (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) :
    ∃ X_impl : ℝ × ℝ × ℝ,
      InReducedTriangle m X_impl.1 X_impl.2.1 X_impl.2.2 ∧
        parityThreshold m ≤ X_impl.2.1 + X_impl.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z → parityThreshold m ≤ y + z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              X_impl.1 X_impl.2.1 X_impl.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
  classical
  have hm : 2 ≤ m := hHom.1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by positivity
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hq0 : 0 ≤ qParam m := le_of_lt hq
  have hM : 0 < 2 * (m : ℝ) := by positivity
  let alpha : Fin 3 → ℝ := ![cX m a b r / qParam m, cY b r, cZ m]
  let beta : Fin 3 → ℝ := ![1 / qParam m, 1, 1]
  have hbetaPos : ∀ i, 0 < beta i := by
    intro i
    fin_cases i
    · have : 0 < 1 / qParam m := by positivity
      simpa [beta] using this
    · simp [beta]
    · simp [beta]
  have hbetaY : beta 1 = 1 := by simp [beta]
  have hbetaZ : beta 2 = 1 := by simp [beta]
  have hd0 : 0 ≤ parityThreshold m := by
    unfold parityThreshold
    by_cases hEven : Even m
    · rw [if_pos hEven]
    · rw [if_neg hEven]
      positivity
  have hdM : parityThreshold m ≤ 2 * (m : ℝ) := by
    unfold parityThreshold
    by_cases hEven : Even m
    · rw [if_pos hEven]
      positivity
    · rw [if_neg hEven]
      have : 2 / (m : ℝ) ≤ 2 * (m : ℝ) := by
        rw [div_le_iff₀ hmpos]
        nlinarith [sq_nonneg ((m : ℝ) - 1)]
      exact this
  obtain ⟨X_rel, hRelMin⟩ := exists_relaxed_reduced_minimizer m a b r kappa hHom hk
  let t_rel : Fin 3 → ℝ := ![qParam m * X_rel.1, X_rel.2.1, X_rel.2.2]
  have hrelS : InSimplex (2 * (m : ℝ)) t_rel :=
    reducedTriangle_to_simplex m X_rel.1 X_rel.2.1 X_rel.2.2 hq0 hRelMin.1
  have hrelWsMin : ∀ s : Fin 3 → ℝ, InSimplex (2 * (m : ℝ)) s →
      wsObj alpha beta kappa t_rel ≤ wsObj alpha beta kappa s := by
    intro s hs
    have hsRed := simplex_to_reducedTriangle m s hq hs
    have hle := hRelMin.2 (s 0 / qParam m) (s 1) (s 2) hsRed
    have hleft :
        wsObj alpha beta kappa t_rel =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_rel.1 X_rel.2.1 X_rel.2.2 := by
      rw [show wsObj alpha beta kappa t_rel =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa t_rel by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa X_rel.1 X_rel.2.1 X_rel.2.2 (ne_of_gt hq)]
    have hright :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            (s 0 / qParam m) (s 1) (s 2) := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      exact wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa s (ne_of_gt hq)
    simpa [hleft, hright] using hle
  obtain ⟨htruncFeasOfFeas, htruncOfInfeas⟩ :=
    trunc_from_minimizer (2 * (m : ℝ)) (parityThreshold m) hd0 hdM
      alpha beta kappa hbetaPos hbetaY hbetaZ hk t_rel hrelS hrelWsMin
  by_cases hfeas : parityThreshold m ≤ t_rel 1 + t_rel 2
  · let X_impl : ℝ × ℝ × ℝ := (t_rel 0 / qParam m, t_rel 1, t_rel 2)
    have htruncMin := htruncFeasOfFeas ⟨hrelS, hfeas⟩
    refine ⟨X_impl, by simpa [X_impl] using simplex_to_reducedTriangle m t_rel hq hrelS,
      by simpa [X_impl] using hfeas, ?_⟩
    intro x y z hT hpar
    let s : Fin 3 → ℝ := ![qParam m * x, y, z]
    have hsS : InSimplex (2 * (m : ℝ)) s :=
      reducedTriangle_to_simplex m x y z hq0 hT
    have hsTrunc : InTruncSimplex (2 * (m : ℝ)) (parityThreshold m) s :=
      ⟨hsS, by simpa [s] using hpar⟩
    have hle := htruncMin s hsTrunc
    have hleft :
        wsObj alpha beta kappa t_rel =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2 := by
      rw [show wsObj alpha beta kappa t_rel =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa t_rel by rfl]
      rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa t_rel (ne_of_gt hq)]
    have hright :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa x y z (ne_of_gt hq)]
    simpa [hleft, hright] using hle
  · obtain ⟨htruncFeas, htruncMin⟩ := htruncOfInfeas hfeas
    let t_impl : Fin 3 → ℝ :=
      truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
        (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa)
    let X_impl : ℝ × ℝ × ℝ := (t_impl 0 / qParam m, t_impl 1, t_impl 2)
    refine ⟨X_impl,
      by simpa [X_impl, t_impl] using
        simplex_to_reducedTriangle m t_impl hq htruncFeas.1,
      by simpa [X_impl, t_impl] using htruncFeas.2, ?_⟩
    intro x y z hT hpar
    let s : Fin 3 → ℝ := ![qParam m * x, y, z]
    have hsS : InSimplex (2 * (m : ℝ)) s :=
      reducedTriangle_to_simplex m x y z hq0 hT
    have hsTrunc : InTruncSimplex (2 * (m : ℝ)) (parityThreshold m) s :=
      ⟨hsS, by simpa [s] using hpar⟩
    have hle := htruncMin s hsTrunc
    have hleft :
        wsObj alpha beta kappa t_impl =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2 := by
      rw [show wsObj alpha beta kappa t_impl =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa t_impl by rfl]
      rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa t_impl (ne_of_gt hq)]
    have hright :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa x y z (ne_of_gt hq)]
    simpa [t_impl, hleft, hright] using hle

lemma implementabilityGap_nonneg_of_reduced_minimizers (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) :
    0 ≤ implementabilityGap m a b r kappa := by
  obtain ⟨X_rel, hRelMin⟩ := exists_relaxed_reduced_minimizer m a b r kappa hHom hk
  obtain ⟨X_impl, hImplMin⟩ := exists_implementable_reduced_minimizer m a b r kappa hHom hk
  have hRelVal := relaxedReducedValue_eq_of_min m a b r kappa X_rel hRelMin
  have hImplVal := implementableReducedValue_eq_of_min m a b r kappa X_impl hImplMin
  have hle :
      reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
          X_rel.1 X_rel.2.1 X_rel.2.2
        ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
          X_impl.1 X_impl.2.1 X_impl.2.2 :=
    hRelMin.2 X_impl.1 X_impl.2.1 X_impl.2.2 hImplMin.1
  rw [rounding_gap_reduction m a b r kappa hHom hk, hImplVal, hRelVal]
  exact sub_nonneg.mpr hle

/-- Zero implementability gap is equivalent to the relaxed argmin set meeting the
implementable parity slice. -/
lemma zero_gap_iff_argmin_meets_slice (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) :
    implementabilityGap m a b r kappa = 0 ↔
      ∃ x y z, InReducedTriangle m x y z ∧
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
        parityThreshold m ≤ y + z := by
  obtain ⟨X_rel, hRelMin⟩ := exists_relaxed_reduced_minimizer m a b r kappa hHom hk
  obtain ⟨X_impl, hImplMin⟩ := exists_implementable_reduced_minimizer m a b r kappa hHom hk
  have hRelVal := relaxedReducedValue_eq_of_min m a b r kappa X_rel hRelMin
  have hImplVal := implementableReducedValue_eq_of_min m a b r kappa X_impl hImplMin
  constructor
  · intro hgap
    have hvalEq :
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2 =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_rel.1 X_rel.2.1 X_rel.2.2 := by
      have hsub :
          implementableReducedValue m a b r kappa - relaxedReducedValue m a b r kappa = 0 := by
        simpa [rounding_gap_reduction m a b r kappa hHom hk] using hgap
      have hEq := sub_eq_zero.mp hsub
      linarith
    refine ⟨X_impl.1, X_impl.2.1, X_impl.2.2, hImplMin.1, ?_, hImplMin.2.1⟩
    intro x y z hT
    rw [hvalEq]
    exact hRelMin.2 x y z hT
  · rintro ⟨x, y, z, hT, hRelMinAt, hpar⟩
    have hRelValAt :
        relaxedReducedValue m a b r kappa =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z :=
      relaxedReducedValue_eq_of_min m a b r kappa (x, y, z) ⟨hT, hRelMinAt⟩
    have hImpl_le :
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z :=
      hImplMin.2.2 x y z hT hpar
    have hRel_le :
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2 :=
      hRelMinAt X_impl.1 X_impl.2.1 X_impl.2.2 hImplMin.1
    have hObjEq :
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_impl.1 X_impl.2.1 X_impl.2.2 =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z :=
      le_antisymm hImpl_le hRel_le
    rw [rounding_gap_reduction m a b r kappa hHom hk, hImplVal, hRelValAt, hObjEq]
    ring

/-- In the unique-relaxed-minimizer case (in particular the `κ > 0` active-set
case), zero gap is equivalent to that unique minimizer lying in the parity slice. -/
lemma zero_gap_iff_unique_min_in_slice (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) (_hkpos : 0 < kappa)
    (X_rel : ℝ × ℝ × ℝ)
    (hRelMin : InReducedTriangle m X_rel.1 X_rel.2.1 X_rel.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            X_rel.1 X_rel.2.1 X_rel.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z)
    (hRelUnique : ∃! t : ℝ × ℝ × ℝ,
      InReducedTriangle m t.1 t.2.1 t.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              t.1 t.2.1 t.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z) :
    implementabilityGap m a b r kappa = 0 ↔
      parityThreshold m ≤ X_rel.2.1 + X_rel.2.2 := by
  constructor
  · intro hgap
    rcases (zero_gap_iff_argmin_meets_slice m a b r kappa hHom hk).1 hgap with
      ⟨x, y, z, hT, hMin, hpar⟩
    rcases hRelUnique with ⟨X0, _hX0, huniq⟩
    have hxyz_eq : ((x, y, z) : ℝ × ℝ × ℝ) = X0 := huniq (x, y, z) ⟨hT, hMin⟩
    have hrel_eq : X_rel = X0 := huniq X_rel hRelMin
    have hcoord : (x, y, z) = X_rel := hxyz_eq.trans hrel_eq.symm
    have hy : y = X_rel.2.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hcoord
    have hz : z = X_rel.2.2 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hcoord
    simpa [hy, hz] using hpar
  · intro hpar
    exact (zero_gap_iff_argmin_meets_slice m a b r kappa hHom hk).2
      ⟨X_rel.1, X_rel.2.1, X_rel.2.2, hRelMin.1, hRelMin.2, hpar⟩

/-- Unique-minimizer form matching the `sharp_rho_star` clause: with a unique relaxed
minimizer, zero gap is equivalent to every relaxed minimizer lying in the parity slice. -/
lemma zero_gap_iff_unique_argmin_subset_slice (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) (hkpos : 0 < kappa)
    (hRelUnique : ∃! t : ℝ × ℝ × ℝ,
      InReducedTriangle m t.1 t.2.1 t.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              t.1 t.2.1 t.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z) :
    implementabilityGap m a b r kappa = 0 ↔
      ∀ x y z, InReducedTriangle m x y z →
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') →
        parityThreshold m ≤ y + z := by
  constructor
  · intro hgap x y z hT hMin
    rcases hRelUnique with ⟨X_rel, hRelMin, huniq⟩
    have hSlice := (zero_gap_iff_unique_min_in_slice m a b r kappa hHom hk hkpos
      X_rel hRelMin ⟨X_rel, hRelMin, huniq⟩).1 hgap
    have hxyz_eq : ((x, y, z) : ℝ × ℝ × ℝ) = X_rel := huniq (x, y, z) ⟨hT, hMin⟩
    have hy : y = X_rel.2.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hxyz_eq
    have hz : z = X_rel.2.2 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hxyz_eq
    simpa [hy, hz] using hSlice
  · intro hall
    rcases hRelUnique with ⟨X_rel, hRelMin, huniq⟩
    exact (zero_gap_iff_unique_min_in_slice m a b r kappa hHom hk hkpos
      X_rel hRelMin ⟨X_rel, hRelMin, huniq⟩).2
        (hall X_rel.1 X_rel.2.1 X_rel.2.2 hRelMin.1 hRelMin.2)

/-- At `κ = 0`, if the exposed relaxed min-face is disjoint from the implementable
slice, then the implementability gap is strictly positive. -/
lemma pos_gap_kappa_zero_exposed_face (m : ℕ) (a b r : ℝ)
    (hHom : TwoBlockHomophily m a b)
    (hDisjoint : ∀ t : Fin 3 → ℝ,
      t ∈ exposedMinFace (2 * (m : ℝ))
          ![cX m a b r / qParam m, cY b r, cZ m] →
        ¬ parityThreshold m ≤ t 1 + t 2) :
    0 < implementabilityGap m a b r 0 := by
  classical
  have hm : 2 ≤ m := hHom.1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hq0 : 0 ≤ qParam m := le_of_lt hq
  have hM : 0 < 2 * (m : ℝ) := by positivity
  let alpha : Fin 3 → ℝ := ![cX m a b r / qParam m, cY b r, cZ m]
  let beta : Fin 3 → ℝ := ![1 / qParam m, 1, 1]
  have hNoMeet :
      ¬ ∃ x y z, InReducedTriangle m x y z ∧
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0 x y z
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0 x' y' z') ∧
        parityThreshold m ≤ y + z := by
    rintro ⟨x, y, z, hT, hMin, hpar⟩
    let t : Fin 3 → ℝ := ![qParam m * x, y, z]
    have htS : InSimplex (2 * (m : ℝ)) t :=
      reducedTriangle_to_simplex m x y z hq0 hT
    have hwsMin : ∀ s : Fin 3 → ℝ, InSimplex (2 * (m : ℝ)) s →
        wsObj alpha beta 0 t ≤ wsObj alpha beta 0 s := by
      intro s hs
      have hsRed := simplex_to_reducedTriangle m s hq hs
      have hle := hMin (s 0 / qParam m) (s 1) (s 2) hsRed
      have hleft :
          wsObj alpha beta 0 t =
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0 x y z := by
        rw [show wsObj alpha beta 0 t =
            wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
              0 t by rfl]
        rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
          0 x y z (ne_of_gt hq)]
      have hright :
          wsObj alpha beta 0 s =
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) 0
              (s 0 / qParam m) (s 1) (s 2) := by
        rw [show wsObj alpha beta 0 s =
            wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
              0 s by rfl]
        exact wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
          0 s (ne_of_gt hq)
      simpa [hleft, hright] using hle
    have hface : t ∈ exposedMinFace (2 * (m : ℝ)) alpha :=
      (kappa_zero_face (2 * (m : ℝ)) hM alpha beta t).1 ⟨htS, hwsMin⟩
    exact (hDisjoint t (by simpa [alpha] using hface)) (by simpa [t] using hpar)
  have hne : implementabilityGap m a b r 0 ≠ 0 := by
    intro hgap
    exact hNoMeet ((zero_gap_iff_argmin_meets_slice m a b r 0 hHom le_rfl).1 hgap)
  have hnonneg : 0 ≤ implementabilityGap m a b r 0 :=
    implementabilityGap_nonneg_of_reduced_minimizers m a b r 0 hHom le_rfl
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end CausalSmith.Experimentation.DesignPm1
