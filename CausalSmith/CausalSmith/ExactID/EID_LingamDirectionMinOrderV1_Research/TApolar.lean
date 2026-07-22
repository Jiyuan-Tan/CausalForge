/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Generic apolar full-opposite-fiber arrow recovery at order `K = 2m + 2`

The headline in-scope crux.  On Zariski-open dense parameter loci that meet the
real feasible regions, the complete order-`K = 2m + 2` cumulant truncation
excludes every full opposite-arrow fiber.  The proof
factors the squarefree degree-`n` support annihilator `Q_D` from the contractions
of the divided-power cumulant blocks and reads its vertical-versus-horizontal
fixed axis, reproving the apolar/catalecticant facts it uses from Vandermonde
minors (no general symmetric-tensor apolarity theory).
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarDefs
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarQD
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.EmptyFiber
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.GenericSlopes
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.MomentGate
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.SlopeUniqueness
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.Varieties
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ZariskiLocus
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Squarefree.Basic

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-- **Generic apolar arrow recovery.**  With `n = m + 2` and `K = 2n - 2 = 2m + 2`,
there are Zariski-open dense parameter loci `U^right ⊆ Θ^{right,∘}_{m,K}` and
`U^left ⊆ Θ^{left,∘}_{m,K}`, each meeting its real feasible region, on which the
full opposite-arrow fiber is empty: for every `θ ∈ U^right` the reverse fiber over
`Φ^right_{m,K}(θ)` is empty, and dually for `U^left`.  Recovery is by factoring the
degree-`n` support annihilator `Q_D` and reading its fixed axis.

The paper setup declares the structural complexity `m ∈ {1, 2, …}` (`n = m + 2 ≥ 3`
sources), so the hypothesis `ValidComplexity m` (`1 ≤ m`) is load-bearing: at
`m = 0` (`n = 2`) the lone `k = 0` contraction has a two-dimensional kernel, not
the claimed line `⟨Q_D⟩`.

This theorem is UNCONDITIONAL.  Its only external input used to be the truncated-moment
interior premise `TruncatedMomentInterior (2 * m + 2)` (the classical truncated Hamburger
moment problem with its nonempty-interior corollary — Akhiezer 1965, Curto–Fialkow 1991,
Schmüdgen 2017 Thm 10.7), which was carried as an explicit gate hypothesis.  That premise
is now PROVED, and promoted to Causalean as
`Causalean.Stat.MomentProblems.truncatedMomentInterior`, so the
hypothesis is discharged internally rather than assumed: the Euclidean-open real-feasibility
witness is *derived* (`exists_feasible_nonvanishing`), never assumed as a conclusion, and the
theorem depends on no substrate gate. -/
-- @node: thm:generic-apolar-arrow-recovery
theorem generic_apolar_arrow_recovery (m : ℕ) (hm : ValidComplexity m) :
    ∃ Ur Ul : Set (ParamSpace ℂ m),
      Ur ⊆ genericParameterLocus m (2 * m + 2) ∧
      Ul ⊆ genericParameterLocus m (2 * m + 2) ∧
      IsZariskiOpenParamIn (2 * m + 2) Ur ∧ IsZariskiDenseParamIn (2 * m + 2) Ur ∧
      IsZariskiOpenParamIn (2 * m + 2) Ul ∧ IsZariskiDenseParamIn (2 * m + 2) Ul ∧
      -- each open locus meets its real feasible region in a nonempty *relatively
      -- Euclidean-open* set (not merely at a single feasible witness):
      (∃ O : Set (ParamSpace ℝ m), IsOpen O ∧
          (O ∩ realFeasibleRegion m (2 * m + 2)).Nonempty ∧
          ∀ θ ∈ O ∩ realFeasibleRegion m (2 * m + 2), complexifyParam θ ∈ Ur) ∧
      (∃ O : Set (ParamSpace ℝ m), IsOpen O ∧
          (O ∩ realFeasibleRegion m (2 * m + 2)).Nonempty ∧
          ∀ η ∈ O ∩ realFeasibleRegion m (2 * m + 2), complexifyParam η ∈ Ul) ∧
      -- forward locus: empty reverse fiber, and the common-kernel / support-annihilator
      -- recovery — the squarefree degree-`n` support annihilator `Q_D`, whose roots
      -- are exactly the forward finite-slope set `D = {γ, ρ_i}` (factorization recovery
      -- of `D`), omits the horizontal fixed axis (`Q_D(0) ≠ 0`), and is determined by
      -- `t = Φ^right(θ)` (the common contraction kernel is the single line `⟨Q_D⟩`):
      (∀ θ ∈ Ur,
        fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
            (forwardCumulantMap m (2 * m + 2) θ) = (∅ : Set (ParamSpace ℂ m)) ∧
        (∃ QD : Polynomial ℂ, QD ≠ 0 ∧ Squarefree QD ∧
          QD.roots = θ.1 ::ₘ (Finset.univ.val.map (fun i => θ.2.1 i)) ∧
          QD.eval 0 ≠ 0 ∧
          (∀ θ'' ∈ genericParameterLocus m (2 * m + 2),
              forwardCumulantMap m (2 * m + 2) θ'' = forwardCumulantMap m (2 * m + 2) θ →
              θ''.1 ::ₘ (Finset.univ.val.map (fun i => θ''.2.1 i)) =
                θ.1 ::ₘ (Finset.univ.val.map (fun i => θ.2.1 i)))) ∧
        -- divided-power blocks, the degree-`n` support annihilator on ALL `n = m+2`
        -- projective directions, the common contraction-kernel identity `ker = ⟨Q_D⟩`,
        -- and the vertical(contained)-vs-horizontal(omitted) fixed axis:
        (let f := fun r => dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) r;
         let QD2 := supportAnnihilator (forwardLoading m θ.1 θ.2.1);
         QD2 ≠ 0 ∧
         (MvPolynomial.X (0 : Fin 2) ∣ QD2) ∧ ¬ (MvPolynomial.X (1 : Fin 2) ∣ QD2) ∧
         (∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
            ((∀ k, k ≤ m → diffApply q (f (m + 2 + k)) = 0) ↔ ∃ c : ℂ, q = c • QD2)))) ∧
      -- reverse locus: empty forward fiber, and the mirror `Q_D` recovery (roots are
      -- the reverse finite-slope set `{δ, σ_i}`, omitting the vertical fixed axis):
      (∀ η ∈ Ul,
        fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
            (reverseCumulantMap m (2 * m + 2) η) = (∅ : Set (ParamSpace ℂ m)) ∧
        (∃ QD : Polynomial ℂ, QD ≠ 0 ∧ Squarefree QD ∧
          QD.roots = η.1 ::ₘ (Finset.univ.val.map (fun i => η.2.1 i)) ∧
          QD.eval 0 ≠ 0 ∧
          (∀ η'' ∈ genericParameterLocus m (2 * m + 2),
              reverseCumulantMap m (2 * m + 2) η'' = reverseCumulantMap m (2 * m + 2) η →
              η''.1 ::ₘ (Finset.univ.val.map (fun i => η''.2.1 i)) =
                η.1 ::ₘ (Finset.univ.val.map (fun i => η.2.1 i)))) ∧
        -- mirror: horizontal axis contained, vertical omitted, same kernel identity:
        (let f := fun r => dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) r;
         let QD2 := supportAnnihilator (reverseLoading m η.1 η.2.1);
         QD2 ≠ 0 ∧
         (MvPolynomial.X (1 : Fin 2) ∣ QD2) ∧ ¬ (MvPolynomial.X (0 : Fin 2) ∣ QD2) ∧
         (∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
            ((∀ k, k ≤ m → diffApply q (f (m + 2 + k)) = 0) ↔ ∃ c : ℂ, q = c • QD2)))) := by
  -- the former substrate gate, now discharged in-run:
  have hgate : TruncatedMomentInterior (2 * m + 2) := truncatedMomentInterior (2 * m + 2)
  obtain ⟨Pf, hPf_ne, ⟨θf0, hθf0_pin, hθf0_ne⟩, hPf_inj⟩ :=
    forward_contraction_injective_of_generic_and_minor m hm
  obtain ⟨Pr, hPr_ne, ⟨θr0, hθr0_pin, hθr0_ne⟩, hPr_inj⟩ :=
    reverse_contraction_injective_of_generic_and_minor m hm
  let ρprod : MvPolynomial (ParamCoord m) ℂ :=
    ∏ i : Fin m, MvPolynomial.X (Sum.inr (Sum.inl i))
  let Rf := genericParameterPolynomial m (2 * m + 2) * ρprod * Pf
  let Rr := genericParameterPolynomial m (2 * m + 2) * ρprod * Pr
  let Ur : Set (ParamSpace ℂ m) :=
    bandSupportedParams m (2 * m + 2) ∩ {θ | MvPolynomial.eval (paramEval θ) Rf ≠ 0}
  let Ul : Set (ParamSpace ℂ m) :=
    bandSupportedParams m (2 * m + 2) ∩ {η | MvPolynomial.eval (paramEval η) Rr ≠ 0}
  have hρprod_ne : ρprod ≠ 0 := by
    dsimp [ρprod]
    apply Finset.prod_ne_zero_iff.mpr
    exact fun i _ => MvPolynomial.X_ne_zero _
  have hRf_ne : Rf ≠ 0 := by
    dsimp [Rf]
    exact mul_ne_zero
      (mul_ne_zero (genericParameterPolynomial_ne_zero m (2 * m + 2)) hρprod_ne) hPf_ne
  have hRr_ne : Rr ≠ 0 := by
    dsimp [Rr]
    exact mul_ne_zero
      (mul_ne_zero (genericParameterPolynomial_ne_zero m (2 * m + 2)) hρprod_ne) hPr_ne
  have hpinρ : pinSubst m (2 * m + 2) ρprod ≠ 0 := by
    dsimp [ρprod]
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [pinSubst_X_slope]
    exact MvPolynomial.X_ne_zero _
  have hpinRf : pinSubst m (2 * m + 2) Rf ≠ 0 := by
    dsimp [Rf]
    rw [map_mul, map_mul]
    exact mul_ne_zero
      (mul_ne_zero (pinSubst_genericParameterPolynomial_ne_zero m (2 * m + 2)) hpinρ)
      (pinSubst_ne_zero_of_pinned_witness Pf θf0 hθf0_pin hθf0_ne)
  have hpinRr : pinSubst m (2 * m + 2) Rr ≠ 0 := by
    dsimp [Rr]
    rw [map_mul, map_mul]
    exact mul_ne_zero
      (mul_ne_zero (pinSubst_genericParameterPolynomial_ne_zero m (2 * m + 2)) hpinρ)
      (pinSubst_ne_zero_of_pinned_witness Pr θr0 hθr0_pin hθr0_ne)
  have forward_data : ∀ θ ∈ Ur,
      θ ∈ genericParameterLocus m (2 * m + 2) ∧
      (∀ i, θ.2.1 i ≠ 0) ∧
      θ.1 ≠ 0 ∧
      Function.Injective (forwardWeightedContraction m θ) ∧
      Function.Injective
        (fun j : Fin (m + 1) => (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2) ∧
      (∀ j : Fin (m + 1),
        (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2 ≠ 0) := by
    intro θ hθ
    have hθne := hθ.2
    change MvPolynomial.eval (paramEval θ) Rf ≠ 0 at hθne
    dsimp [Rf] at hθne
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul] at hθne
    obtain ⟨hGρ, hP⟩ := mul_ne_zero_iff.mp hθne
    obtain ⟨hG, hRP⟩ := mul_ne_zero_iff.mp hGρ
    have hgen : θ ∈ genericParameterLocus m (2 * m + 2) := by
      rw [genericParameterLocus_eq_nonvanishing_poly]
      exact ⟨hθ.1, hG⟩
    have hρ : ∀ i, θ.2.1 i ≠ 0 := by
      have hprod : (∏ i : Fin m, θ.2.1 i) ≠ 0 := by
        simpa [ρprod, paramEval] using hRP
      rw [Finset.prod_ne_zero_iff] at hprod
      exact fun i => hprod i (Finset.mem_univ i)
    exact ⟨hgen, hρ, gamma_ne_zero_of_generic hgen, hPf_inj θ hP,
      forward_slopes_injective_of_generic hgen,
      forward_slopes_ne_zero_of_generic hgen hρ⟩
  have reverse_data : ∀ η ∈ Ul,
      η ∈ genericParameterLocus m (2 * m + 2) ∧
      (∀ i, η.2.1 i ≠ 0) ∧
      η.1 ≠ 0 ∧
      Function.Injective (reverseWeightedContraction m η) ∧
      Function.Injective
        (fun j : Fin (m + 1) => (reverseLoading m η.1 η.2.1 j.succ).1) ∧
      (∀ j : Fin (m + 1), (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0) := by
    intro η hη
    have hηne := hη.2
    change MvPolynomial.eval (paramEval η) Rr ≠ 0 at hηne
    dsimp [Rr] at hηne
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul] at hηne
    obtain ⟨hGρ, hP⟩ := mul_ne_zero_iff.mp hηne
    obtain ⟨hG, hRP⟩ := mul_ne_zero_iff.mp hGρ
    have hgen : η ∈ genericParameterLocus m (2 * m + 2) := by
      rw [genericParameterLocus_eq_nonvanishing_poly]
      exact ⟨hη.1, hG⟩
    have hσ : ∀ i, η.2.1 i ≠ 0 := by
      have hprod : (∏ i : Fin m, η.2.1 i) ≠ 0 := by
        simpa [ρprod, paramEval] using hRP
      rw [Finset.prod_ne_zero_iff] at hprod
      exact fun i => hprod i (Finset.mem_univ i)
    exact ⟨hgen, hσ, gamma_ne_zero_of_generic hgen, hPr_inj η hP,
      reverse_slopes_injective_of_generic hgen,
      reverse_slopes_ne_zero_of_generic hgen hσ⟩
  refine ⟨Ur, Ul, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    exact (forward_data θ hθ).1
  · intro η hη
    exact (reverse_data η hη).1
  · exact (isZariskiOpenIn_denseIn_of_pinSubst_ne_zero Rf hpinRf).1
  · exact (isZariskiOpenIn_denseIn_of_pinSubst_ne_zero Rf hpinRf).2
  · exact (isZariskiOpenIn_denseIn_of_pinSubst_ne_zero Rr hpinRr).1
  · exact (isZariskiOpenIn_denseIn_of_pinSubst_ne_zero Rr hpinRr).2
  · let O : Set (ParamSpace ℝ m) :=
      {θ | MvPolynomial.eval (paramEval (complexifyParam θ)) Rf ≠ 0}
    refine ⟨O, isOpen_realNonvanishingLocus Rf, ?_, ?_⟩
    · obtain ⟨θ, hfeas, hne⟩ := exists_feasible_nonvanishing hgate Rf hpinRf
      exact ⟨θ, hne, hfeas⟩
    · intro θ hθ
      refine ⟨?_, hθ.1⟩
      intro j r hr
      simp [complexifyParam, hθ.2.2.2.1 j r hr]
  · let O : Set (ParamSpace ℝ m) :=
      {η | MvPolynomial.eval (paramEval (complexifyParam η)) Rr ≠ 0}
    refine ⟨O, isOpen_realNonvanishingLocus Rr, ?_, ?_⟩
    · obtain ⟨η, hfeas, hne⟩ := exists_feasible_nonvanishing hgate Rr hpinRr
      exact ⟨η, hne, hfeas⟩
    · intro η hη
      refine ⟨?_, hη.1⟩
      intro j r hr
      simp [complexifyParam, hη.2.2.2.1 j r hr]
  · intro θ hθ
    obtain ⟨hgen, hρ, hγ, hrank, hslopes, hnonzero⟩ := forward_data θ hθ
    refine ⟨forward_reverse_fiber_empty m θ hslopes hγ hρ hnonzero hrank, ?_, ?_⟩
    · refine ⟨qDefault (rtsF θ), qDefault_ne_zero _, qDefault_squarefree _ ?_, ?_,
        qDefault_eval_zero_ne _ ?_, ?_⟩
      · exact rtsF_nodup θ hgen hρ
      · simpa [rtsF] using qDefault_roots (rtsF θ)
      · exact zero_notMem_rtsF θ hgen hρ
      · intro θ'' _hθ'' heq
        exact forward_slopes_determined_by_cumulants m θ hslopes hnonzero hrank θ'' heq
    · dsimp only
      refine ⟨supportAnnihilator_ne_zero (forwardLoading m θ.1 θ.2.1) ?_,
        X0_dvd_supportAnnihilator_forward θ.1 θ.2.1,
        not_X1_dvd_supportAnnihilator_forward θ.1 θ.2.1 hγ hρ, ?_⟩
      · intro j
        by_cases h0 : j.val = 0
        · left
          simp [forwardLoading, h0]
        by_cases hlast : j.val = m + 1
        · right
          simp [forwardLoading, hlast]
        · left
          simp [forwardLoading, h0, hlast]
      · exact forward_apolar_kernel_identity m θ hslopes hnonzero hrank
  · intro η hη
    obtain ⟨hgen, hσ, hδ, hrank, hslopes, hnonzero⟩ := reverse_data η hη
    refine ⟨reverse_forward_fiber_empty m η hslopes hδ hσ hnonzero hrank, ?_, ?_⟩
    · refine ⟨qDefault (rtsF η), qDefault_ne_zero _, qDefault_squarefree _ ?_, ?_,
        qDefault_eval_zero_ne _ ?_, ?_⟩
      · exact rtsF_nodup η hgen hσ
      · simpa [rtsF] using qDefault_roots (rtsF η)
      · exact zero_notMem_rtsF η hgen hσ
      · intro η'' _hη'' heq
        exact reverse_slopes_determined_by_cumulants m η hslopes hnonzero hrank η'' heq
    · dsimp only
      refine ⟨supportAnnihilator_ne_zero (reverseLoading m η.1 η.2.1) ?_,
        X1_dvd_supportAnnihilator_reverse η.1 η.2.1,
        not_X0_dvd_supportAnnihilator_reverse η.1 η.2.1 hδ hσ, ?_⟩
      · intro j
        by_cases h0 : j.val = 0
        · left
          simp [reverseLoading, h0]
        · right
          simp only [reverseLoading, h0, ↓reduceDIte]
          split <;> simp
      · exact reverse_apolar_kernel_identity m η hslopes hnonzero hrank

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
