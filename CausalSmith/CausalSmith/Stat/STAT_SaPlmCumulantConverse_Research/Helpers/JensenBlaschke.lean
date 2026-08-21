import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.ComplexAnalysisLocal
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.Basic
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-!
# Quantitative Jensen bridges

This file connects the open-disk multiplicity count used by the contour
library to Mathlib's logarithmic divisor count.  The resulting Jensen bound
does not require the outer circle to be zero-free.
-/

noncomputable section

open Filter Function Metric Real Set
open Causalean.Mathlib.Analysis.ArgumentPrincipleCircle
open scoped Topology

namespace CausalSmith.Stat.SaPlmCumulantConverse

open Classical in
/-- Keep precisely the strict-interior part of a closed-disk divisor. -/
noncomputable def interiorPart (R : ℝ)
    (D : locallyFinsuppWithin (closedBall (0 : ℂ) R) ℤ) :
    locallyFinsuppWithin (closedBall (0 : ℂ) R) ℤ where
  toFun z := if z ∈ ball (0 : ℂ) R then D z else 0
  supportWithinDomain' := by
    classical
    intro z hz
    change (if z ∈ ball (0 : ℂ) R then D z else 0) ≠ 0 at hz
    by_cases hzb : z ∈ ball (0 : ℂ) R
    · exact ball_subset_closedBall hzb
    · simp [hzb] at hz
  supportLocallyFiniteWithinDomain' := by
    classical
    intro z hz
    obtain ⟨t, ht, hfin⟩ := D.supportLocallyFiniteWithinDomain z hz
    refine ⟨t, ht, hfin.subset ?_⟩
    intro u hu
    rcases hu with ⟨hut, hu⟩
    exact ⟨hut, by
      change (if u ∈ ball (0 : ℂ) R then D u else 0) ≠ 0 at hu
      change D u ≠ 0
      by_cases hub : u ∈ ball (0 : ℂ) R
      · simpa [hub] using hu
      · simp [hub] at hu⟩

open Classical in
/-- [The strict-interior part of a divisor on a closed disk agrees with the divisor at every
point lying strictly inside the disk and is zero everywhere else](goal), so it records exactly
the multiplicities that the argument principle counts and discards those sitting on the
boundary circle. -/
@[simp] lemma interiorPart_apply (R : ℝ)
    (D : locallyFinsuppWithin (closedBall (0 : ℂ) R) ℤ) (z : ℂ) :
    interiorPart R D z = if z ∈ ball (0 : ℂ) R then D z else 0 := by
  classical
  rfl

/-- The analytic nonvanishing correction which converts the radius-`R`
Blaschke product back to the corresponding monic zero polynomial. -/
def blaschkeCorrection {N : ℕ} (R : ℝ) (a : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (((R : ℂ) ^ 2 - star (a i) * z) / (R : ℂ))

/-- A Blaschke product times its correction is the monic polynomial with the
listed zeros. -/
lemma blaschkeProduct_mul_blaschkeCorrection {N : ℕ} (R : ℝ)
    (a : Fin N → ℂ) (hR : 0 < R) (ha : ∀ i, ‖a i‖ < R) (z : ℂ)
    (hz : ‖z‖ ≤ R) :
    blaschkeProduct R a z * blaschkeCorrection R a z = ∏ i, (z - a i) := by
  rw [blaschkeProduct, blaschkeCorrection, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  unfold blaschkeFactor
  have hden : (R : ℂ) ^ 2 - star (a i) * z ≠ 0 := by
    intro hzero
    have heq : (R : ℂ) ^ 2 = star (a i) * z := sub_eq_zero.mp hzero
    have hn := congrArg norm heq
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      norm_mul, norm_star] at hn
    have hprodlt : ‖a i‖ * ‖z‖ < R * R := calc
      ‖a i‖ * ‖z‖ ≤ ‖a i‖ * R :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < R * R := mul_lt_mul_of_pos_right (ha i) hR
    nlinarith
  have hden' : (R : ℂ) ^ 2 - z * star (a i) ≠ 0 := by
    simpa [mul_comm] using hden
  field_simp [hR.ne', hden, hden']

/-- The Blaschke correction is analytic and nonzero throughout the closed
disk when all listed zeros lie strictly inside it. -/
lemma blaschkeCorrection_analyticOnNhd_and_ne_zero {N : ℕ} (R : ℝ)
    (a : Fin N → ℂ) (hR : 0 < R) (ha : ∀ i, ‖a i‖ < R) :
    AnalyticOnNhd ℂ (blaschkeCorrection R a) (closedBall (0 : ℂ) R) ∧
      ∀ z ∈ closedBall (0 : ℂ) R, blaschkeCorrection R a z ≠ 0 := by
  constructor
  · intro z hz
    unfold blaschkeCorrection
    fun_prop
  · intro z hz
    rw [blaschkeCorrection, Finset.prod_ne_zero_iff]
    intro i hi
    apply div_ne_zero
    · intro hzero
      have heq : (R : ℂ) ^ 2 = star (a i) * z := sub_eq_zero.mp hzero
      have hn := congrArg norm heq
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
        norm_mul, norm_star] at hn
      have hzR : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz
      have hprodlt : ‖a i‖ * ‖z‖ < R * R := calc
        ‖a i‖ * ‖z‖ ≤ ‖a i‖ * R :=
          mul_le_mul_of_nonneg_left hzR (norm_nonneg _)
        _ < R * R := mul_lt_mul_of_pos_right (ha i) hR
      nlinarith
    · exact_mod_cast hR.ne'

/-- On a closed disk, Mathlib's divisor extraction constructs the analytic
zero-free quotient.  The equality is in Mathlib's canonical codiscrete form;
this is the raw cancellation bridge from which a concrete finite Blaschke
factorization can be obtained after identifying the finite divisor. -/
lemma exists_analytic_zeroFree_factorizedRational_closedBall
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (han : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hzero : f 0 ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0) ∧
      EqOn f
        ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall 0 R) u)) * g)
        (closedBall (0 : ℂ) R) := by
  have h0mem : (0 : ℂ) ∈ closedBall 0 R := by simpa using hR.le
  have hmer := han.meromorphicOn
  have hbase : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(han 0 h0mem).meromorphicOrderAt_eq,
      (han 0 h0mem).analyticOrderAt_eq_zero.2 hzero]
    simp
  have hfiniteOrder : ∀ u : closedBall (0 : ℂ) R,
      meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    exact hmer.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected h0mem u.property hbase
  have hsupport : (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall (0 : ℂ) R)
  obtain ⟨g, hgAn, hgzero, hfactor⟩ :=
    hmer.extract_zeros_poles hfiniteOrder hsupport
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) R)
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hDnonneg : (0 : ℂ → ℤ) ≤ D := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · simp [D, hmer, hz, (han z hz).meromorphicOrderAt_nonneg]
    · simp [D, hz]
  have hPAn : AnalyticOnNhd ℂ P (closedBall (0 : ℂ) R) := by
    rw [← (Function.FactorizedRational.meromorphicNFOn D
      (closedBall (0 : ℂ) R)).divisor_nonneg_iff_analyticOnNhd]
    rw [Function.FactorizedRational.divisor hsupport]
    exact hDnonneg
  have hprodAn : AnalyticOnNhd ℂ (P * g) (closedBall (0 : ℂ) R) := hPAn.mul hgAn
  have hacc : AccPt (0 : ℂ) (𝓟 (closedBall (0 : ℂ) R)) := by
    apply accPt_iff_frequently_nhdsNE.mpr
    apply Filter.Eventually.frequently
    apply mem_nhdsWithin.mpr
    refine ⟨ball 0 R, isOpen_ball, mem_ball_self hR, ?_⟩
    intro z hz
    exact ball_subset_closedBall hz.1
  have hpunc : f =ᶠ[𝓝[≠] (0 : ℂ)] P * g := by
    apply (han 0 h0mem).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      (hprodAn 0 h0mem).meromorphicAt h0mem hacc
    simpa only [P, D, Pi.smul_apply', smul_eq_mul] using hfactor
  have heq : EqOn f (P * g) (closedBall (0 : ℂ) R) :=
    han.eqOn_of_preconnected_of_frequently_eq hprodAn
      (convex_closedBall (0 : ℂ) R).isPreconnected h0mem hpunc.frequently
  refine ⟨g, hgAn, ?_, ?_⟩
  · intro z hz
    exact hgzero ⟨z, hz⟩
  · simpa only [P, D] using heq

/-- A multiplicity-expanded enumeration of the disk divisor yields an actual
pointwise finite Blaschke factorization.  The zero-free remainder is
constructed from Mathlib's extracted quotient and the explicit nonvanishing
Blaschke correction; it is not an assumption. -/
lemma exists_pointwise_blaschke_factorization_of_divisor_enumeration
    {f : ℂ → ℂ} {R : ℝ} {N : ℕ} (a : Fin N → ℂ)
    (hR : 0 < R) (han : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hzero : f 0 ≠ 0) (ha : ∀ i, ‖a i‖ < R)
    (henum : EqOn
      (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall 0 R) u))
      (fun z ↦ ∏ i, (z - a i)) (closedBall (0 : ℂ) R)) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) ∧
      DiffContOnCl ℂ g (ball (0 : ℂ) R) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0) ∧
      ∀ z ∈ closedBall (0 : ℂ) R,
        f z = blaschkeProduct R a z * g z := by
  obtain ⟨g0, hg0An, hg0zero, hfP⟩ :=
    exists_analytic_zeroFree_factorizedRational_closedBall hR han hzero
  let g : ℂ → ℂ := blaschkeCorrection R a * g0
  have hcorr := blaschkeCorrection_analyticOnNhd_and_ne_zero R a hR ha
  have hgAn : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) := hcorr.1.mul hg0An
  refine ⟨g, hgAn, hgAn.differentiableOn.diffContOnCl_ball subset_rfl, ?_, ?_⟩
  · intro z hz
    exact mul_ne_zero (hcorr.2 z hz) (hg0zero z hz)
  · intro z hz
    rw [hfP hz]
    simp only [Pi.mul_apply]
    rw [henum hz]
    change (∏ i, (z - a i)) * g0 z = _
    have hzR : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz
    rw [← blaschkeProduct_mul_blaschkeCorrection R a hR ha z hzR]
    simp only [g, Pi.mul_apply]
    ring

/-- Every finite nonnegative divisor admits a multiplicity-expanded finite
enumeration whose monic product is its factorized rational function. -/
lemma exists_multiplicityEnumeration_of_finite_nonneg_divisor
    {D : locallyFinsuppWithin (closedBall (0 : ℂ) R) ℤ}
    (hfin : D.support.Finite) (hnonneg : (0 : ℂ → ℤ) ≤ D)
    (hsupportBall : D.support ⊆ ball (0 : ℂ) R) :
    ∃ (N : ℕ) (a : Fin N → ℂ),
      (∀ i, a i ∈ ball (0 : ℂ) R) ∧
      N = ∑ u ∈ hfin.toFinset, (D u).toNat ∧
      ∀ z : ℂ, (∏ᶠ u, (z - u) ^ D u) = ∏ i, (z - a i) := by
  classical
  let S := hfin.toFinset
  let I := Σ u : S, Fin (D u.1).toNat
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let a : Fin (Fintype.card I) → ℂ := fun i ↦ (e.symm i).1.1
  refine ⟨Fintype.card I, a, ?_, ?_, ?_⟩
  · intro i
    exact hsupportBall (hfin.mem_toFinset.mp (e.symm i).1.2)
  · simp [I, S]
    exact Finset.sum_attach hfin.toFinset (fun u ↦ (D u).toNat)
  · intro z
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · rw [show (∏ u ∈ S, (z - u) ^ D u) =
          ∏ u : S, (z - u.1) ^ D u.1 by
            rw [← Finset.prod_attach]
            rfl]
      calc
        (∏ u : S, (z - u.1) ^ D u.1) =
            ∏ u : S, (z - u.1) ^ (D u.1).toNat := by
          apply Fintype.prod_congr
          intro u
          rw [← zpow_natCast]
          congr 1
          exact (Int.toNat_of_nonneg (hnonneg u.1)).symm
        _ = ∏ x : I, (z - x.1.1) := by
          rw [Fintype.prod_sigma]
          apply Fintype.prod_congr
          intro u
          exact Fin.prod_const _ _ |>.symm
        _ = ∏ i, (z - a i) := by
          apply Fintype.prod_equiv e
          intro x
          simp [a]
    · intro u hu
      rw [Function.mem_mulSupport] at hu
      have hDu : D u ≠ 0 := by
        intro h
        simp [h] at hu
      exact hfin.mem_toFinset.mpr hDu

open Classical in
/-- The open-disk zero count can be evaluated on any finite set containing
all nonzero analytic orders in the disk. -/
lemma zeroMultiplicityCount_eq_sum_orders_on_finset
    {f : ℂ → ℂ} {R : ℝ} (S : Finset ℂ)
    (hS : ∀ z ∈ ball (0 : ℂ) R, analyticOrderNatAt f z ≠ 0 → z ∈ S) :
    zeroMultiplicityCount f 0 R =
      ∑ z ∈ S, if z ∈ ball (0 : ℂ) R then analyticOrderNatAt f z else 0 := by
  classical
  unfold zeroMultiplicityCount
  rw [finsum_eq_sum_of_support_subset (s := S)
    (fun z ↦ if z ∈ ball (0 : ℂ) R then analyticOrderNatAt f z else 0)]
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz
  by_cases hzball : z ∈ ball (0 : ℂ) R
  · exact hS z hzball (by simpa [hzball] using hz)
  · simp [hzball] at hz

/-- Factorized rational functions multiply when two finite exponent functions
are nonnegative.  Nonnegativity is essential at common zeros: it lets us
reduce integer powers to ordinary natural powers before using `pow_add`. -/
lemma factorizedRational_add_of_finite_nonneg
    {d e : ℂ → ℤ} (hdFin : d.support.Finite) (heFin : e.support.Finite)
    (hd : (0 : ℂ → ℤ) ≤ d) (he : (0 : ℂ → ℤ) ≤ e) :
    (∏ᶠ u, (· - u) ^ (d u + e u)) =
      (∏ᶠ u, (· - u) ^ d u) * (∏ᶠ u, (· - u) ^ e u) := by
  rw [← finprod_mul_distrib]
  · apply finprod_congr
    intro u
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hd u)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (he u)
    rw [hm, hn, ← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
  · rw [Function.HasFiniteMulSupport, Function.FactorizedRational.mulSupport]
    exact hdFin
  · rw [Function.HasFiniteMulSupport, Function.FactorizedRational.mulSupport]
    exact heFin

/-- A normalized analytic function admits a complete finite pointwise
Blaschke factorization on the disk even when it has zeros on the boundary.
Only strict-interior zeros enter the Blaschke product; boundary factors are
absorbed into a remainder which is zero-free on the open disk. -/
lemma exists_complete_pointwise_blaschke_factorization
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (han : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) (hzero : f 0 ≠ 0) :
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      (∀ i, ‖a i‖ < R) ∧
      AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) ∧
      DiffContOnCl ℂ g (ball (0 : ℂ) R) ∧
      (∀ z ∈ ball (0 : ℂ) R, g z ≠ 0) ∧
      N = zeroMultiplicityCount f 0 R ∧
      ∀ z ∈ closedBall (0 : ℂ) R, f z = blaschkeProduct R a z * g z := by
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) R)
  let Dint := interiorPart R D
  let Dbd := D - Dint
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall (0 : ℂ) R)
  have hnonneg : (0 : ℂ → ℤ) ≤ D := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · simp [D, han.meromorphicOn, hz, (han z hz).meromorphicOrderAt_nonneg]
    · simp [D, hz]
  have hintnonneg : (0 : ℂ → ℤ) ≤ Dint := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) R
    · simpa [Dint, hz] using hnonneg z
    · simp [Dint, hz]
  have hbdnonneg : (0 : ℂ → ℤ) ≤ Dbd := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) R
    · simp [Dbd, Dint, hz]
    · simpa [Dbd, Dint, hz] using hnonneg z
  have hintSupport : Dint.support ⊆ D.support := by
    intro z hz
    by_cases hzb : z ∈ ball (0 : ℂ) R
    · simpa [Dint, hzb] using hz
    · simp [Dint, hzb] at hz
  have hbdSupport : Dbd.support ⊆ D.support := by
    intro z hz
    by_contra hDz
    have hDz0 : D z = 0 := Function.notMem_support.mp hDz
    have hDi : Dint z = 0 := by
      by_cases hzb : z ∈ ball (0 : ℂ) R <;> simp [Dint, hzb, hDz0]
    exact hz (by simp [Dbd, hDz0, hDi])
  have hintFin : Dint.support.Finite := hfin.subset hintSupport
  have hbdFin : Dbd.support.Finite := hfin.subset hbdSupport
  have hintSupportBall : Dint.support ⊆ ball (0 : ℂ) R := by
    intro z hz
    by_contra hzb
    simp [Dint, hzb] at hz
  obtain ⟨N, a, haBall, hcard, henumAll⟩ :=
    exists_multiplicityEnumeration_of_finite_nonneg_divisor
      hintFin hintnonneg hintSupportBall
  have ha : ∀ i, ‖a i‖ < R := fun i ↦ by
    simpa [mem_ball, dist_zero_right] using haBall i
  have horderFinite (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) :
      analyticOrderAt f z ≠ ⊤ := by
    have hbase : meromorphicOrderAt f 0 ≠ ⊤ := by
      rw [(han 0 (by simpa using hR.le)).meromorphicOrderAt_eq,
        (han 0 (by simpa using hR.le)).analyticOrderAt_eq_zero.2 hzero]
      simp
    have hm := han.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected (by simpa using hR.le)
      hz hbase
    rw [(han z hz).meromorphicOrderAt_eq] at hm
    simpa using hm
  have hDorder (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) :
      D z = (analyticOrderNatAt f z : ℤ) := by
    dsimp [D]
    rw [MeromorphicOn.divisor_apply han.meromorphicOn hz,
      (han z hz).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (horderFinite z hz)]
    simp
  have hSin (z : ℂ) (hz : z ∈ ball (0 : ℂ) R)
      (hzord : analyticOrderNatAt f z ≠ 0) : z ∈ hintFin.toFinset := by
    apply hintFin.mem_toFinset.mpr
    simp only [Function.mem_support, Dint, interiorPart_apply, hz, if_true]
    rw [hDorder z (ball_subset_closedBall hz)]
    exact_mod_cast hzord
  have hcount := zeroMultiplicityCount_eq_sum_orders_on_finset
    hintFin.toFinset hSin
  have hcount' : N = zeroMultiplicityCount f 0 R := by
    rw [hcard, hcount]
    apply Finset.sum_congr rfl
    intro z hz
    have hzsupport : z ∈ Dint.support := hintFin.mem_toFinset.mp hz
    have hzball : z ∈ ball (0 : ℂ) R := hintSupportBall hzsupport
    simp only [hzball, if_true]
    simp only [Dint, interiorPart_apply, hzball, if_true] at hzsupport ⊢
    rw [hDorder z (ball_subset_closedBall hzball)]
    simp
  obtain ⟨g0, hg0An, hg0zero, hfD⟩ :=
    exists_analytic_zeroFree_factorizedRational_closedBall hR han hzero
  let Pbd : ℂ → ℂ := ∏ᶠ u, (· - u) ^ Dbd u
  have hPbdAn : AnalyticOnNhd ℂ Pbd (closedBall (0 : ℂ) R) := by
    intro z hz
    exact Function.FactorizedRational.analyticAt (hbdnonneg z)
  have hPbdZero : ∀ z ∈ ball (0 : ℂ) R, Pbd z ≠ 0 := by
    intro z hz
    apply Function.FactorizedRational.ne_zero
    simp [Dbd, Dint, hz]
  let g : ℂ → ℂ := blaschkeCorrection R a * (Pbd * g0)
  have hcorr := blaschkeCorrection_analyticOnNhd_and_ne_zero R a hR ha
  have hgAn : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) :=
    hcorr.1.mul (hPbdAn.mul hg0An)
  refine ⟨N, a, g, ha, hgAn,
    hgAn.differentiableOn.diffContOnCl_ball subset_rfl, ?_, hcount', ?_⟩
  · intro z hz
    exact mul_ne_zero (hcorr.2 z (ball_subset_closedBall hz))
      (mul_ne_zero (hPbdZero z hz) (hg0zero z (ball_subset_closedBall hz)))
  · intro z hz
    rw [hfD hz]
    simp only [Pi.mul_apply]
    have hDsplit : D = Dint + Dbd := by
      ext u
      simp [Dbd]
    have hPsplit :
        (∏ᶠ u, (· - u) ^ D u) =
          (∏ᶠ u, (· - u) ^ Dint u) * Pbd := by
      rw [hDsplit]
      exact factorizedRational_add_of_finite_nonneg
        hintFin hbdFin hintnonneg hbdnonneg
    rw [hPsplit]
    simp only [Pi.mul_apply]
    have henumAt : (∏ᶠ u, (· - u) ^ Dint u) z = ∏ i, (z - a i) := by
      rw [Function.FactorizedRational.finprod_eq_fun hintFin]
      exact henumAll z
    rw [henumAt]
    have hzR : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz
    rw [← blaschkeProduct_mul_blaschkeCorrection R a hR ha z hzR]
    simp only [g, Pbd, Pi.mul_apply]
    ring

/-- Jensen's formula bounds the logarithmic divisor count by any uniform
log-modulus bound on the outer circle, when the function is normalized at the
origin.  Zeros on that circle are allowed. -/
lemma jensen_logCounting_divisor_le {f : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (han : AnalyticOnNhd ℂ f Set.univ) (hzero : f 0 = 1)
    (hupper : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ Real.exp A) :
    locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f ⊤) R ≤ A := by
  have hmer : Meromorphic f := by simpa [Meromorphic] using han.meromorphicOn
  show locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f Set.univ) R ≤ A
  rw [locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
    hmer hR.ne']
  have htrail : meromorphicTrailingCoeffAt f 0 = 1 := by
    rw [(han 0 (mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero]
    · exact hzero
    · simp [hzero]
  rw [htrail]
  simp only [norm_one, Real.log_one, sub_zero]
  apply Real.circleAverage_mono_on_of_le_circle
  · exact circleIntegrable_log_norm_meromorphicOn
      (fun z hz ↦ (han z (mem_univ z)).meromorphicAt)
  · intro z hz
    have hz' : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hz
    by_cases hfz : f z = 0
    · simpa [hfz] using hA
    · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hfz)).2 (hupper z hz')

open Classical in
/-- The open-disk multiplicity count, after casting to the integers, is the
sum of the analytic orders over any finite set containing every zero in the
disk. -/
lemma zeroMultiplicityCount_eq_sum_analyticOrderNatAt
    {f : ℂ → ℂ} {R : ℝ} (S : Finset ℂ)
    (hS : ∀ z ∈ ball (0 : ℂ) R, analyticOrderNatAt f z ≠ 0 → z ∈ S) :
    zeroMultiplicityCount f 0 R =
      ∑ z ∈ S, if z ∈ ball (0 : ℂ) R then analyticOrderNatAt f z else 0 := by
  classical
  unfold zeroMultiplicityCount
  rw [finsum_eq_sum_of_support_subset (s := S)
    (fun z ↦ if z ∈ ball (0 : ℂ) R then analyticOrderNatAt f z else 0)]
  · intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    by_cases hzball : z ∈ ball (0 : ℂ) R
    · exact hS z hzball (by simpa [hzball] using hz)
    · simp [hzball] at hz

/-- Quantitative Jensen zero-counting inequality in the project's
`zeroMultiplicityCount` representation.  It has no boundary-zero hypothesis. -/
lemma zeroMultiplicityCount_mul_log_div_le_logCounting
    {f : ℂ → ℂ} {Rin Rout : ℝ}
    (hRin : 0 < Rin) (hlt : Rin < Rout)
    (han : AnalyticOnNhd ℂ f Set.univ) (hzero : f 0 = 1) :
    (zeroMultiplicityCount f 0 Rin : ℝ) * Real.log (Rout / Rin) ≤
      locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f ⊤) Rout := by
  classical
  let D := MeromorphicOn.divisor f ⊤
  let S : Finset ℂ :=
    (D.toClosedBall Rout).finiteSupport (isCompact_closedBall (0 : ℂ) |Rout|) |>.toFinset
  have hRout : 0 < Rout := hRin.trans hlt
  have hmer : Meromorphic f := by simpa [Meromorphic] using han.meromorphicOn
  have horderFinite (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
    have hbase : meromorphicOrderAt f 0 ≠ ⊤ := by
      rw [(han 0 (mem_univ 0)).meromorphicOrderAt_eq,
        (han 0 (mem_univ 0)).analyticOrderAt_eq_zero.2 (by simp [hzero])]
      simp
    have hm := han.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ 0) (mem_univ z) hbase
    rw [(han z (mem_univ z)).meromorphicOrderAt_eq] at hm
    simpa using hm
  have hDorder (z : ℂ) : D z = (analyticOrderNatAt f z : ℤ) := by
    dsimp [D]
    rw [MeromorphicOn.divisor_apply han.meromorphicOn (mem_univ z),
      (han z (mem_univ z)).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (horderFinite z)]
    simp
  have hSin (z : ℂ) (hz : z ∈ ball (0 : ℂ) Rin)
      (hzord : analyticOrderNatAt f z ≠ 0) : z ∈ S := by
    have hzclosed : z ∈ closedBall (0 : ℂ) |Rout| := by
      rw [mem_closedBall, dist_zero_right, abs_of_pos hRout]
      exact (mem_ball_zero_iff.mp hz).le.trans hlt.le
    have hDz : D z ≠ 0 := by rw [hDorder]; exact_mod_cast hzord
    exact Set.Finite.mem_toFinset
      ((D.toClosedBall Rout).finiteSupport (isCompact_closedBall (0 : ℂ) |Rout|)) |>.2
      (by simpa [S, locallyFinsuppWithin.toClosedBall_eval_within D hzclosed] using hDz)
  rw [zeroMultiplicityCount_eq_sum_analyticOrderNatAt S hSin]
  push_cast
  rw [Finset.sum_mul]
  have hlogexpand : locallyFinsuppWithin.logCounting D Rout =
      ∑ z ∈ S, (D.toClosedBall Rout z : ℝ) *
          Real.log (Rout * ‖z‖⁻¹) + (D 0 : ℝ) * Real.log Rout := by
    unfold locallyFinsuppWithin.logCounting
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [finsum_eq_sum_of_support_subset (s := S)]
    intro z hz
    have hfactor : (D.toClosedBall Rout z : ℝ) ≠ 0 := left_ne_zero_of_mul hz
    exact Set.Finite.mem_toFinset
      ((D.toClosedBall Rout).finiteSupport (isCompact_closedBall (0 : ℂ) |Rout|)) |>.2
      (by simpa [S, Function.mem_support] using hfactor)
  rw [hlogexpand]
  have hord0 : analyticOrderNatAt f 0 = 0 := by
    by_contra hne
    have hf0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hne
    simp [hzero] at hf0
  have hDzero : D 0 = 0 := by
    rw [hDorder, hord0]
    rfl
  rw [hDzero]
  simp only [Int.cast_zero, zero_mul, add_zero]
  apply Finset.sum_le_sum
  intro z hzS
  by_cases hz : z ∈ ball (0 : ℂ) Rin
  · have hzRout : z ∈ closedBall (0 : ℂ) |Rout| := by
      rw [mem_closedBall, dist_zero_right, abs_of_pos hRout]
      exact (mem_ball_zero_iff.mp hz).le.trans hlt.le
    rw [if_pos hz, locallyFinsuppWithin.toClosedBall_eval_within D hzRout, hDorder]
    push_cast
    have hznorm : ‖z‖ < Rin := mem_ball_zero_iff.mp hz
    by_cases hz0 : z = 0
    · subst z
      simp [hord0]
    · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.log_le_log (div_pos hRout hRin)
      rw [div_eq_mul_inv]
      apply (div_le_div_iff_of_pos_left hRout hRin (norm_pos_iff.mpr hz0)).2
      exact hznorm.le
  · simp only [hz, if_false, zero_mul]
    have hDnonneg : 0 ≤ (D.toClosedBall Rout z : ℝ) := by
      by_cases hzout : z ∈ closedBall (0 : ℂ) |Rout|
      · rw [locallyFinsuppWithin.toClosedBall_eval_within D hzout, hDorder]
        exact_mod_cast Nat.zero_le (analyticOrderNatAt f z)
      · simp [locallyFinsuppWithin.toClosedBall, hzout]
    exact mul_nonneg hDnonneg (Real.log_nonneg (by
      have hzclosed := locallyFinsuppWithin.toClosedBall_support_subset_closedBall D
        (Set.Finite.mem_toFinset
          ((D.toClosedBall Rout).finiteSupport (isCompact_closedBall (0 : ℂ) |Rout|)) |>.1 hzS)
      rw [mem_closedBall, dist_zero_right, abs_of_pos hRout] at hzclosed
      by_cases hz0 : z = 0
      · exact False.elim (hz (by simpa [hz0] using hRin))
      · exact (le_mul_inv_iff₀ (norm_pos_iff.mpr hz0)).2 (by
          simpa [mul_comm] using hzclosed)))

/-- A normalized entire function whose modulus is at most `exp A` on the
outer circle has at most Jensen growth worth of inner zeros. -/
lemma jensen_zeroMultiplicityCount_bound {f : ℂ → ℂ} {Rin Rout A : ℝ}
    (hRin : 0 < Rin) (hlt : Rin < Rout) (hA : 0 ≤ A)
    (han : AnalyticOnNhd ℂ f Set.univ) (hzero : f 0 = 1)
    (hupper : ∀ z ∈ sphere (0 : ℂ) Rout, ‖f z‖ ≤ Real.exp A) :
    (zeroMultiplicityCount f 0 Rin : ℝ) * Real.log (Rout / Rin) ≤ A :=
  (zeroMultiplicityCount_mul_log_div_le_logCounting hRin hlt han hzero).trans
    (jensen_logCounting_divisor_le (hRin.trans hlt) hA han hzero hupper)

/-- A supplied finite Blaschke factorization turns an outer boundary bound
into a quantitative interior lower bound.  This is the reusable consumer of a
complete multiplicity list: the remaining local burden is only to construct
the analytic zero-free quotient and the factorization equality. -/
lemma norm_lower_of_blaschke_factorization {N : ℕ}
    (f g : ℂ → ℂ) (a : Fin N → ℂ) (R R1 A : ℝ)
    (hR : 0 < R) (hR1 : 0 ≤ R1) (hsmall : R1 < R)
    (ha : ∀ i, ‖a i‖ < R)
    (hgAn : AnalyticOnNhd ℂ g (ball (0 : ℂ) R))
    (hgDiff : DiffContOnCl ℂ g (ball (0 : ℂ) R))
    (hgzero : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) R,
      f z = blaschkeProduct R a z * g z)
    (hfzero : f 0 = 1)
    (hfupper : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ Real.exp A) :
    ∀ z : ℂ, ‖z‖ ≤ R1 →
      Real.exp (-(((R + R1) / (R - R1)) - 1) * A) *
          ‖blaschkeProduct R a z‖ ≤ ‖f z‖ := by
  have hGupper : ∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ Real.exp A := by
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hgDiff _
      (by rw [closure_ball _ hR.ne']; exact ball_subset_closedBall hz)
    intro w hw
    have hwS : w ∈ sphere (0 : ℂ) R :=
      frontier_ball_subset_sphere hw
    have hwC : w ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hwS
    have hprod := congrArg norm (hfactor w hwC)
    rw [norm_mul, norm_blaschkeProduct_eq_one_of_mem_sphere R a hR ha hwS,
      one_mul] at hprod
    rw [← hprod]
    exact hfupper w hwS
  have hzeroC : (0 : ℂ) ∈ closedBall 0 R := by simpa using hR.le
  have hfactor0 := congrArg norm (hfactor 0 hzeroC)
  rw [hfzero, norm_one, norm_mul] at hfactor0
  have hBone := norm_blaschkeProduct_zero_le_one R a hR ha
  have hGone : 1 ≤ ‖g 0‖ := by
    nlinarith [norm_nonneg (blaschkeProduct R a 0), norm_nonneg (g 0)]
  have hlog := log_norm_ge_of_zero_free_ball g A R R1 hR hR1 hsmall
    hgAn hgzero hGupper hGone
  intro z hz
  have hzBall : z ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right]
    exact hz.trans hsmall.le
  rw [hfactor z hzBall, norm_mul]
  rw [mul_comm (Real.exp _) ‖blaschkeProduct R a z‖]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (Real.le_log_iff_exp_le (norm_pos_iff.mpr
    (hgzero z (by rw [mem_ball_zero_iff]; exact hz.trans_lt hsmall)))).1
  exact hlog z hz

end CausalSmith.Stat.SaPlmCumulantConverse
