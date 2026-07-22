/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.GapReduction
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ReducedSimplexBridge
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SimplexTruncation

/-! # Spread-vertex gap assembly

Turns a reduced-coordinate spread-vertex certificate into the matrix relaxed minimizer
statement and the strict implementability gap in the odd-community slice. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

set_option maxHeartbeats 800000 in
-- @node: spread_certificate_relaxed_minimizer_and_gap
lemma spread_certificate_relaxed_minimizer_and_gap (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) (hOdd : OddCommunitySize m)
    (hcert :
      InReducedTriangle m (2 * (m : ℝ) / qParam m) 0 0 ∧
        ∀ x y z, InReducedTriangle m x y z →
          ((x, y, z) : ℝ × ℝ × ℝ) ≠ (2 * (m : ℝ) / qParam m, 0, 0) →
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
                (2 * (m : ℝ) / qParam m) 0 0
              < reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z) :
    (spreadCovariance m ∈ blockElliptope m a b ∧
        ∀ X ∈ blockElliptope m a b, X ≠ spreadCovariance m →
          designObjective m a b r kappa (spreadCovariance m)
            < designObjective m a b r kappa X) ∧
      spreadCovariance m ∉ implementableCovarianceClass m ∧
      0 < implementabilityGap m a b r kappa := by
  have hm : 2 ≤ m := hHom.1
  have hOddNat : Odd m := hOdd
  have hNotEven : ¬ Even m := Nat.not_even_iff_odd.mpr hOddNat
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have hmNat : (0 : ℕ) < m := lt_of_lt_of_le (by decide : 0 < 2) hm
    exact_mod_cast hmNat
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    nlinarith
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hq0 : 0 ≤ qParam m := le_of_lt hq
  have hxSpread :
      1 - (-1 / ((m : ℝ) - 1)) = 2 * (m : ℝ) / qParam m := by
    unfold qParam
    field_simp [hm1]
    ring
  have hySpread :
      1 + ((m : ℝ) - 1) * (-1 / ((m : ℝ) - 1)) - (m : ℝ) * (0 : ℝ) = 0 := by
    field_simp [hm1]
    ring
  have hzSpread :
      1 + ((m : ℝ) - 1) * (-1 / ((m : ℝ) - 1)) + (m : ℝ) * (0 : ℝ) = 0 := by
    field_simp [hm1]
    ring
  have hySpread' :
      1 + ((m : ℝ) - 1) * (-1 / ((m : ℝ) - 1)) = 0 := by
    field_simp [hm1]
    ring
  have hspecSpread :=
    block_spectral_coordinates m a b r kappa (-1 / ((m : ℝ) - 1)) 0 hHom
  have hspreadTriUV : InReducedTriangle m (1 - (-1 / ((m : ℝ) - 1)))
      (1 + ((m : ℝ) - 1) * (-1 / ((m : ℝ) - 1)) - (m : ℝ) * (0 : ℝ))
      (1 + ((m : ℝ) - 1) * (-1 / ((m : ℝ) - 1)) + (m : ℝ) * (0 : ℝ)) := by
    simpa [hxSpread, hySpread, hzSpread, hySpread'] using hcert.1
  have hspreadMem : spreadCovariance m ∈ blockElliptope m a b := by
    unfold spreadCovariance
    exact hspecSpread.1.mpr hspreadTriUV
  have hspreadObj : designObjective m a b r kappa (spreadCovariance m) =
      reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
        (2 * (m : ℝ) / qParam m) 0 0 := by
    simpa [spreadCovariance, hxSpread, hySpread, hzSpread, hySpread'] using hspecSpread.2.1
  have hrelStrict : ∀ X ∈ blockElliptope m a b, X ≠ spreadCovariance m →
      designObjective m a b r kappa (spreadCovariance m)
        < designObjective m a b r kappa X := by
    intro X hX hne
    rcases hX with ⟨u, v, rfl, hmem⟩
    have hspec := block_spectral_coordinates m a b r kappa u v hHom
    have htri : InReducedTriangle m (1 - u)
        (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := hspec.1.mp ⟨u, v, rfl, hmem⟩
    have hcoord_ne : ((1 - u,
        1 + ((m : ℝ) - 1) * u - (m : ℝ) * v,
        1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) : ℝ × ℝ × ℝ) ≠
        (2 * (m : ℝ) / qParam m, 0, 0) := by
      intro hcoord
      have hy0 : 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v = 0 :=
        congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hcoord
      have hz0 : 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v = 0 :=
        congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hcoord
      have hv : v = 0 := by
        have hmv : (2 * (m : ℝ)) * v = 0 := by nlinarith
        exact (mul_eq_zero.mp hmv).resolve_left (by positivity)
      have hu : u = -1 / ((m : ℝ) - 1) := by
        subst v
        have hmul : ((m : ℝ) - 1) * u = -1 := by linarith
        have hmul' : u * ((m : ℝ) - 1) = -1 := by linarith
        exact (eq_div_iff hm1).2 hmul'
      apply hne
      unfold spreadCovariance
      rw [hu, hv]
    calc
      designObjective m a b r kappa (spreadCovariance m)
          = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              (2 * (m : ℝ) / qParam m) 0 0 := hspreadObj
      _ < reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
            (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) :=
          hcert.2 _ _ _ htri hcoord_ne
      _ = designObjective m a b r kappa (blockSymMatrix m u v) := hspec.2.1.symm
  have hspreadNotImp : spreadCovariance m ∉ implementableCovarianceClass m :=
    spreadCovariance_not_implementable_of_odd m hm hOddNat
  let Xrel : ℝ × ℝ × ℝ := (2 * (m : ℝ) / qParam m, 0, 0)
  have hRelMin : InReducedTriangle m Xrel.1 Xrel.2.1 Xrel.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            Xrel.1 Xrel.2.1 Xrel.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
    refine ⟨by simpa [Xrel] using hcert.1, ?_⟩
    intro x y z hT
    by_cases hEq : ((x, y, z) : ℝ × ℝ × ℝ) = Xrel
    · have hx : x = Xrel.1 := congrArg Prod.fst hEq
      have hy : y = Xrel.2.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hEq
      have hz : z = Xrel.2.2 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hEq
      subst x
      subst y
      subst z
      rfl
    · exact le_of_lt (hcert.2 x y z hT hEq)
  have hRelUnique : ∃! t : ℝ × ℝ × ℝ,
      InReducedTriangle m t.1 t.2.1 t.2.2 ∧
        ∀ x y z, InReducedTriangle m x y z →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              t.1 t.2.1 t.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
    refine ⟨Xrel, hRelMin, ?_⟩
    rintro ⟨x, y, z⟩ ht
    by_cases hEq : ((x, y, z) : ℝ × ℝ × ℝ) = Xrel
    · exact hEq
    · have hlt := hcert.2 x y z ht.1 hEq
      have hle := ht.2 Xrel.1 Xrel.2.1 Xrel.2.2 hRelMin.1
      exact False.elim ((not_lt_of_ge hle) hlt)
  have hOutside : Xrel.2.1 + Xrel.2.2 < parityThreshold m := by
    unfold parityThreshold
    rw [if_neg hNotEven]
    dsimp [Xrel]
    have htwo : (0 : ℝ) < 2 := by norm_num
    simpa using div_pos htwo hmpos
  let alpha : Fin 3 → ℝ := ![cX m a b r / qParam m, cY b r, cZ m]
  let beta : Fin 3 → ℝ := ![1 / qParam m, 1, 1]
  let trel : Fin 3 → ℝ := ![2 * (m : ℝ), 0, 0]
  have htrelS : InSimplex (2 * (m : ℝ)) trel := by
    constructor
    · intro i
      fin_cases i
      · simp [trel]
      · simp [trel]
      · simp [trel]
    · simp [trel, Fin.sum_univ_three]
  have hws_min : ∀ s : Fin 3 → ℝ, InSimplex (2 * (m : ℝ)) s →
      wsObj alpha beta kappa trel ≤ wsObj alpha beta kappa s := by
    intro s hs
    have hsRed := simplex_to_reducedTriangle m s hq hs
    have hle := hRelMin.2 (s 0 / qParam m) (s 1) (s 2) hsRed
    have htrelObj :
        wsObj alpha beta kappa trel =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            (2 * (m : ℝ) / qParam m) 0 0 := by
      rw [show wsObj alpha beta kappa trel =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa trel by rfl]
      rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa trel (ne_of_gt hq)]
      simp [trel]
    have hsObj :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            (s 0 / qParam m) (s 1) (s 2) := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      exact wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa s (ne_of_gt hq)
    simpa [Xrel, htrelObj, hsObj] using hle
  have hd0 : 0 ≤ parityThreshold m := by
    unfold parityThreshold
    by_cases hEven : Even m
    · simp [hEven]
    · simp [hEven]
      positivity
  have hdM : parityThreshold m ≤ 2 * (m : ℝ) := by
    unfold parityThreshold
    by_cases hEven : Even m
    · simp [hEven]
    · simp [hEven]
      have : 2 / (m : ℝ) ≤ 2 * (m : ℝ) := by
        rw [div_le_iff₀ hmpos]
        nlinarith [sq_nonneg ((m : ℝ) - 1)]
      exact this
  have hbetaPos : ∀ i, 0 < beta i := by
    intro i
    fin_cases i
    · have : 0 < 1 / qParam m := by positivity
      simpa [beta] using this
    · simp [beta]
    · simp [beta]
  have hbetaY : beta 1 = 1 := by simp [beta]
  have hbetaZ : beta 2 = 1 := by simp [beta]
  have htrelInfeas : ¬ (parityThreshold m ≤ trel 1 + trel 2) := by
    simp [trel]
    linarith [hOutside]
  obtain ⟨htruncFeas, htruncMin⟩ :=
    (trunc_from_minimizer (2 * (m : ℝ)) (parityThreshold m) hd0 hdM
      alpha beta kappa hbetaPos hbetaY hbetaZ hk trel htrelS hws_min).2 htrelInfeas
  let Ximpl : ℝ × ℝ × ℝ :=
    (truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
      (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa) 0 / qParam m,
     truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
      (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa) 1,
     truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
      (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa) 2)
  have hImplMin : InReducedTriangle m Ximpl.1 Ximpl.2.1 Ximpl.2.2 ∧
      parityThreshold m ≤ Ximpl.2.1 + Ximpl.2.2 ∧
      ∀ x y z, InReducedTriangle m x y z → parityThreshold m ≤ y + z →
        reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            Ximpl.1 Ximpl.2.1 Ximpl.2.2
          ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
    refine ⟨by simpa [Ximpl] using simplex_to_reducedTriangle m _ hq htruncFeas.1,
      by simpa [Ximpl] using htruncFeas.2, ?_⟩
    intro x y z hT hpar
    let s : Fin 3 → ℝ := ![qParam m * x, y, z]
    have hsS : InSimplex (2 * (m : ℝ)) s :=
      reducedTriangle_to_simplex m x y z hq0 hT
    have hsTrunc : InTruncSimplex (2 * (m : ℝ)) (parityThreshold m) s := by
      exact ⟨hsS, by simpa [s] using hpar⟩
    have hle := htruncMin s hsTrunc
    have hleft :
        wsObj alpha beta kappa
            (truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
              (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa)) =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
            Ximpl.1 Ximpl.2.1 Ximpl.2.2 := by
      rw [show wsObj alpha beta kappa
            (truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
              (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa)) =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa
            (truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
              (truncSelector (2 * (m : ℝ)) (parityThreshold m) alpha beta kappa)) by rfl]
      rw [wsObj_eq_reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa _ (ne_of_gt hq)]
    have hright :
        wsObj alpha beta kappa s =
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z := by
      rw [show wsObj alpha beta kappa s =
          wsObj ![cX m a b r / qParam m, cY b r, cZ m] ![1 / qParam m, 1, 1]
            kappa s by rfl]
      rw [reducedObjective_eq_wsObj (qParam m) (cX m a b r) (cY b r) (cZ m)
        kappa x y z (ne_of_gt hq)]
    simpa [hleft, hright] using hle
  have hgapPos : 0 < implementabilityGap m a b r kappa :=
    pos_gap_of_unique_min_outside_slice m a b r kappa hHom hk Xrel Ximpl
      hRelMin hRelUnique hOutside hImplMin
  exact ⟨⟨hspreadMem, hrelStrict⟩, hspreadNotImp, hgapPos⟩

end CausalSmith.Experimentation.DesignPm1
