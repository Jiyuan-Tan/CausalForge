/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation

/-!
# Monomial approximation of multivariate Hölder functions

This module converts the diagonal Fréchet Taylor polynomial supplied by a
multivariate Hölder condition into an explicitly indexed monomial polynomial.
The resulting remainder constant is uniform over the Hölder ball.
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators Pointwise Manifold ContDiff
open Causalean.Stat.Nonparametric

/-- **Line chain rule.** The `i`-th 1-D iterated derivative of the line
`s ↦ g (x0 + s • y)` equals the `i`-th iterated Fréchet derivative of `g` at
`x0 + t • y` evaluated on the constant diagonal `fun _ => y` (needs GLOBAL
`ContDiff ℝ i g`). -/
private lemma line_iteratedDeriv {d : ℕ} (g : (Fin d → ℝ) → ℝ) (i : ℕ)
    (hf : ContDiff ℝ i g) (x0 y : Fin d → ℝ) (t : ℝ) :
    iteratedDeriv i (fun s => g (x0 + s • y)) t
      = iteratedFDeriv ℝ i g (x0 + t • y) (fun _ => y) := by
  set L : ℝ →L[ℝ] (Fin d → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight y with hL
  have hL1 : L 1 = y := by simp [hL]
  have hLt : L t = t • y := by simp [hL]
  set f₁ : (Fin d → ℝ) → ℝ := fun z => g (x0 + z) with hf₁def
  have hshift : ContDiff ℝ i (fun z : Fin d → ℝ => x0 + z) :=
    ContDiff.add contDiff_const contDiff_id
  have hf₁ : ContDiff ℝ i f₁ := hf.comp hshift
  have hcomp : (fun s => g (x0 + s • y)) = f₁ ∘ L := by funext s; simp [hf₁def, hL]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right L hf₁ t (le_refl _)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hLt]
  have hval : (fun j : Fin i => L ((fun _ => (1 : ℝ)) j)) = (fun _ : Fin i => y) := by
    funext j; simp [hL1]
  rw [hval]
  rw [show iteratedFDeriv ℝ i f₁ (t • y) = iteratedFDeriv ℝ i g (x0 + t • y) from ?_]
  · exact congrFun (iteratedFDeriv_comp_add_left' i x0) (t • y)

/-- **Global smooth extension of a `ContDiffOn` function.** If `g` is `ContDiffOn ℝ m`
on `S`, `U ⊆ S` is open, and `K ⊆ U` is compact, then there is a GLOBALLY `ContDiff ℝ m`
function `g'` that agrees with `g` on a neighborhood of every point of `K`. -/
private lemma exists_global_contDiff_of_contDiffOn {d : ℕ} (m : ℕ)
    {g : (Fin d → ℝ) → ℝ} {S U K : Set (Fin d → ℝ)}
    (hg1 : ContDiffOn ℝ m g S) (hU : IsOpen U) (hUS : U ⊆ S)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g' : (Fin d → ℝ) → ℝ, ContDiff ℝ m g' ∧ ∀ p ∈ K, g' =ᶠ[nhds p] g := by
  obtain ⟨V, hVo, hKV, hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  have hKint : K ⊆ interior (closure V) := hKV.trans (interior_maximal subset_closure hVo)
  obtain ⟨χ, hχ1, hχ0, hχ01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, Fin d → ℝ)) (n := (m : ℕ∞))
      hK.isClosed hKint
  have hχcd : ContDiff ℝ (m : WithTop ℕ∞) (fun x => χ x) := by
    have := χ.contMDiff.contDiff (n := (m : ℕ∞)); simpa using this
  refine ⟨fun x => χ x * g x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ closure V
    · have hxU : x ∈ U := hVU hx
      have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun x => χ x) x := hχcd.contDiffAt
      have h2 : ContDiffAt ℝ (m : WithTop ℕ∞) g x :=
        (hg1.mono hUS).contDiffAt (hU.mem_nhds hxU)
      exact h1.mul h2
    · have hnhds : (closure V)ᶜ ∈ nhds x := (isClosed_closure.isOpen_compl).mem_nhds hx
      have heq : (fun x => χ x * g x) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hnhds] with z hz; simp [hχ0 z hz]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const heq
  · intro p hp
    have hp1 : ∀ᶠ x in nhds p, χ x = 1 := hχ1.filter_mono (nhds_le_nhdsSet hp)
    filter_upwards [hp1] with x hx
    simp [hx]

/-- Cast a `ℕ`-inequality into the `WithTop ℕ∞` smoothness index used by `ContDiff`. -/
private lemma natCast_le_withTop {a b : ℕ} (h : a ≤ b) :
    (a : WithTop ℕ∞) ≤ (b : WithTop ℕ∞) := Nat.mono_cast h

/-- Cast a strict `ℕ`-inequality into the `WithTop ℕ∞` smoothness index used by `ContDiff`. -/
private lemma natCast_lt_withTop {a b : ℕ} (h : a < b) :
    (a : WithTop ℕ∞) < (b : WithTop ℕ∞) := by
  rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  exact ENat.coe_lt_coe.mpr h

/-- Applying an order-`k` continuous multilinear map to the constant diagonal `fun _ => y`
is bounded by its operator norm times `‖y‖^k`. -/
private lemma cmm_diag_apply_abs_le {d k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => (Fin d → ℝ)) ℝ) (y : Fin d → ℝ) :
    |A (fun _ => y)| ≤ ‖A‖ * ‖y‖ ^ k := by
  have h := A.le_opNorm (fun _ : Fin k => y)
  rw [Real.norm_eq_abs] at h
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- Core Hölder bound on the diagonal: the difference of the order-`k` (`k = ⌈γ⌉₊-1`) iterated
Fréchet derivatives at two points `P, Q ∈ S`, evaluated on the constant diagonal `fun _ => y`,
is at most `M * ‖P - Q‖^(γ - k) * ‖y‖^k`. -/
private lemma holder_diag_diff_le {d : ℕ} {γ M : ℝ} {g : (Fin d → ℝ) → ℝ}
    {S : Set (Fin d → ℝ)} (hg : HolderBallStd g γ M S)
    (P Q : Fin d → ℝ) (hP : P ∈ S) (hQ : Q ∈ S) (y : Fin d → ℝ) :
    |iteratedFDeriv ℝ (⌈γ⌉₊ - 1) g P (fun _ => y)
        - iteratedFDeriv ℝ (⌈γ⌉₊ - 1) g Q (fun _ => y)|
      ≤ M * ‖P - Q‖ ^ (γ - ((⌈γ⌉₊ - 1 : ℕ) : ℝ)) * ‖y‖ ^ (⌈γ⌉₊ - 1) := by
  set k := ⌈γ⌉₊ - 1 with hk
  have hstep :
      |iteratedFDeriv ℝ k g P (fun _ => y) - iteratedFDeriv ℝ k g Q (fun _ => y)|
        ≤ ‖iteratedFDeriv ℝ k g P - iteratedFDeriv ℝ k g Q‖ * ‖y‖ ^ k := by
    have h := cmm_diag_apply_abs_le (iteratedFDeriv ℝ k g P - iteratedFDeriv ℝ k g Q) y
    rwa [ContinuousMultilinearMap.sub_apply] at h
  have hhol := hg.2.2 P hP Q hQ
  calc
    |iteratedFDeriv ℝ k g P (fun _ => y) - iteratedFDeriv ℝ k g Q (fun _ => y)|
        ≤ ‖iteratedFDeriv ℝ k g P - iteratedFDeriv ℝ k g Q‖ * ‖y‖ ^ k := hstep
    _ ≤ (M * ‖P - Q‖ ^ (γ - ((k : ℕ) : ℝ))) * ‖y‖ ^ k := by gcongr
    _ = M * ‖P - Q‖ ^ (γ - ((k : ℕ) : ℝ)) * ‖y‖ ^ k := by ring

/-- **Per-point Taylor + Hölder crux.** For `g` in the standard Hölder ball of order `γ`
and radius `M` on `S`, `U ⊆ S` open containing the segment `{x0 + t • y : t ∈ [0,1]}`, the
value `g (x0 + y)` differs from its order-`m` diagonal Taylor polynomial (`m = ⌈γ⌉₊ - 1`) by
at most `(M / m!) ‖y‖^γ`. -/
private lemma holder_line_taylor {d : ℕ} {γ M : ℝ} {g : (Fin d → ℝ) → ℝ}
    {S U : Set (Fin d → ℝ)}
    (hγ : 0 < γ) (hg : HolderBallStd g γ M S) (hU : IsOpen U) (hUS : U ⊆ S)
    (x0 y : Fin d → ℝ) (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • y ∈ U) :
    |g (x0 + y) - ∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1),
        (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => y)|
      ≤ (M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖y‖ ^ γ := by
  have h0mem : x0 ∈ U := by
    have := hseg 0 (Set.left_mem_Icc.mpr zero_le_one); simpa using this
  have h1mem : x0 + y ∈ U := by
    have := hseg 1 (Set.right_mem_Icc.mpr zero_le_one); simpa using this
  have hx0S : x0 ∈ S := hUS h0mem
  have hx0yS : x0 + y ∈ S := hUS h1mem
  rcases Nat.eq_zero_or_pos (⌈γ⌉₊ - 1) with hm0 | hmpos
  · -- Case m = 0 (0 < γ ≤ 1): the sum is just `g x0`, no Taylor needed.
    have hb := holder_diag_diff_le hg (x0 + y) x0 hx0yS hx0S y
    rw [hm0] at hb ⊢
    simp only [zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, one_div,
      inv_one, one_mul, iteratedFDeriv_zero_apply, div_one, Nat.cast_zero, sub_zero,
      pow_zero, mul_one] at hb ⊢
    rwa [add_sub_cancel_left] at hb
  · -- Case m ≥ 1 (γ > 1): Taylor with Lagrange remainder on the line.
    obtain ⟨n, hn⟩ : ∃ n, ⌈γ⌉₊ - 1 = n + 1 := ⟨⌈γ⌉₊ - 2, by omega⟩
    have hM : 0 ≤ M := le_trans (norm_nonneg _) (hg.2.1 0 (Nat.zero_le _) x0 hx0S)
    have hfac : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 1)
    set K : Set (Fin d → ℝ) := (fun t : ℝ => x0 + t • y) '' Set.Icc 0 1 with hKdef
    have hcontLine : Continuous (fun t : ℝ => x0 + t • y) := by fun_prop
    have hK : IsCompact K := isCompact_Icc.image hcontLine
    have hKU : K ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hseg t ht
    have hx0K : x0 ∈ K := ⟨0, Set.left_mem_Icc.mpr zero_le_one, by simp⟩
    have hx0yK : x0 + y ∈ K := ⟨1, Set.right_mem_Icc.mpr zero_le_one, by simp⟩
    have hxξK : ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 → x0 + ξ • y ∈ K :=
      fun ξ hξ => ⟨ξ, ⟨hξ.1.le, hξ.2.le⟩, rfl⟩
    obtain ⟨gt, hgt_cd, hgt_eq⟩ :=
      exists_global_contDiff_of_contDiffOn (⌈γ⌉₊ - 1) hg.1 hU hUS hK hKU
    have htrans : ∀ (i : ℕ) (p : Fin d → ℝ), p ∈ K →
        iteratedFDeriv ℝ i gt p = iteratedFDeriv ℝ i g p :=
      fun i p hp => ((hgt_eq p hp).iteratedFDeriv ℝ i).eq_of_nhds
    have hlineCD : ContDiff ℝ ((⌈γ⌉₊ - 1 : ℕ) : WithTop ℕ∞) (fun s : ℝ => x0 + s • y) := by
      fun_prop
    set φ : ℝ → ℝ := fun s => gt (x0 + s • y) with hφdef
    have hφCD : ContDiff ℝ ((⌈γ⌉₊ - 1 : ℕ) : WithTop ℕ∞) φ := by
      simpa [hφdef, Function.comp] using hgt_cd.comp hlineCD
    have hcoef : ∀ k : ℕ, k ≤ ⌈γ⌉₊ - 1 →
        iteratedDerivWithin k φ (Set.Icc (0 : ℝ) 1) 0
          = iteratedFDeriv ℝ k g x0 (fun _ => y) := by
      intro k hk
      have hCDk : ContDiff ℝ (k : WithTop ℕ∞) gt := hgt_cd.of_le (natCast_le_withTop hk)
      have hCDkφ : ContDiffAt ℝ (k : WithTop ℕ∞) φ 0 :=
        (hφCD.of_le (natCast_le_withTop hk)).contDiffAt
      rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one hCDkφ
        (Set.left_mem_Icc.mpr zero_le_one), hφdef, line_iteratedDeriv gt k hCDk x0 y 0]
      simp only [zero_smul, add_zero]
      rw [htrans k x0 hx0K]
    have hCDgt : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) gt := hn ▸ hgt_cd
    have hφn : ContDiffOn ℝ (n : WithTop ℕ∞) φ (Set.Icc (0 : ℝ) 1) :=
      ((hn ▸ hφCD).of_le (natCast_le_withTop (Nat.le_succ n))).contDiffOn
    have hφn1 : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) φ (Set.Icc (0 : ℝ) 1) :=
      (hn ▸ hφCD).contDiffOn
    have hf' : DifferentiableOn ℝ (iteratedDerivWithin n φ (Set.Icc (0 : ℝ) 1))
        (Set.Ioo 0 1) :=
      (hφn1.differentiableOn_iteratedDerivWithin (natCast_lt_withTop (Nat.lt_succ_self n))
        uniqueDiffOn_Icc_zero_one).mono Set.Ioo_subset_Icc_self
    obtain ⟨ξ, hξ, htay⟩ :=
      taylor_mean_remainder_lagrange (f := φ) zero_lt_one hφn hf'
    have hφ1 : φ 1 = g (x0 + y) := by
      have := (hgt_eq (x0 + y) hx0yK).eq_of_nhds; simpa [hφdef, one_smul] using this
    have hsum : taylorWithinEval φ n (Set.Icc (0 : ℝ) 1) 0 1
        = ∑ k ∈ Finset.range (n + 1),
            1 / (Nat.factorial k : ℝ) * iteratedFDeriv ℝ k g x0 (fun _ => y) := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [hcoef k (by rw [hn]; omega)]
      simp only [sub_zero, one_pow, mul_one, smul_eq_mul, one_div]
    have hR : iteratedDerivWithin (n + 1) φ (Set.Icc (0 : ℝ) 1) ξ
        = iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y) := by
      have hCDξ : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) φ ξ := (hn ▸ hφCD).contDiffAt
      rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one hCDξ
        (Set.Ioo_subset_Icc_self hξ), hφdef, line_iteratedDeriv gt (n + 1) hCDgt x0 y ξ,
        htrans (n + 1) (x0 + ξ • y) (hxξK ξ hξ)]
    have eq1 : g (x0 + y)
          - ∑ k ∈ Finset.range (n + 1),
              1 / (Nat.factorial k : ℝ) * iteratedFDeriv ℝ k g x0 (fun _ => y)
        = iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y)
            / (Nat.factorial (n + 1) : ℝ) := by
      rw [hφ1, hsum, hR] at htay; simpa using htay
    have hxξS : x0 + ξ • y ∈ S := hUS (hKU (hxξK ξ hξ))
    have hbound := holder_diag_diff_le hg (x0 + ξ • y) x0 hxξS hx0S y
    rw [hn] at hbound
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hξ.1] at hbound
    have hlt : ((n + 1 : ℕ) : ℝ) < γ := by
      have := Nat.lt_ceil.mp (show ⌈γ⌉₊ - 1 < ⌈γ⌉₊ by omega); rw [hn] at this; exact this
    have he_nonneg : 0 ≤ γ - ((n + 1 : ℕ) : ℝ) := by linarith
    have hem : (γ - ((n + 1 : ℕ) : ℝ)) + ((n + 1 : ℕ) : ℝ) = γ := by ring
    have hcombine : ‖y‖ ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1) = ‖y‖ ^ γ := by
      rw [← Real.rpow_natCast (‖y‖) (n + 1),
        ← Real.rpow_add' (norm_nonneg y) (by rw [hem]; exact ne_of_gt hγ), hem]
    have key : (ξ * ‖y‖) ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1) ≤ ‖y‖ ^ γ := by
      rw [Real.mul_rpow hξ.1.le (norm_nonneg y), mul_assoc, hcombine]
      calc ξ ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ γ
            ≤ 1 * ‖y‖ ^ γ :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_one hξ.1.le hξ.2.le he_nonneg) (Real.rpow_nonneg (norm_nonneg y) γ)
        _ = ‖y‖ ^ γ := one_mul _
    have hmid : M * (ξ * ‖y‖) ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1) ≤ M * ‖y‖ ^ γ := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left key hM
    have hgoal_eq : g (x0 + y)
          - ∑ j ∈ Finset.range (n + 1 + 1),
              1 / (Nat.factorial j : ℝ) * iteratedFDeriv ℝ j g x0 (fun _ => y)
        = 1 / (Nat.factorial (n + 1) : ℝ)
            * (iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y)
                - iteratedFDeriv ℝ (n + 1) g x0 (fun _ => y)) := by
      rw [Finset.sum_range_succ]; linear_combination eq1
    rw [hn, hgoal_eq, abs_mul, abs_of_pos (div_pos one_pos hfac)]
    calc 1 / (Nat.factorial (n + 1) : ℝ)
            * |iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y)
                - iteratedFDeriv ℝ (n + 1) g x0 (fun _ => y)|
          ≤ 1 / (Nat.factorial (n + 1) : ℝ)
              * (M * (ξ * ‖y‖) ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hbound (div_pos one_pos hfac).le
      _ ≤ 1 / (Nat.factorial (n + 1) : ℝ) * (M * ‖y‖ ^ γ) :=
          mul_le_mul_of_nonneg_left hmid (div_pos one_pos hfac).le
      _ = M / (Nat.factorial (n + 1) : ℝ) * ‖y‖ ^ γ := by ring



private def indexCount {d j : ℕ} (ι : Fin j → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter (fun l => ι l = i)).card

private lemma sum_indexCount {d j : ℕ} (ι : Fin j → Fin d) :
    ∑ i, indexCount ι i = j := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin j)))
    (t := (Finset.univ : Finset (Fin d))) (f := ι) (fun l _ => Finset.mem_univ (ι l))
  simpa [indexCount] using h.symm

private lemma prod_eq_monomial {d j : ℕ} (ι : Fin j → Fin d) (u : Fin d → ℝ) :
    ∏ l, u (ι l) = ∏ i, u i ^ indexCount ι i := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (fun l _ => Finset.mem_univ (ι l))
    (fun l => u (ι l))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_congr rfl (fun l hl => by rw [(Finset.mem_filter.mp hl).2]),
    Finset.prod_const]
  rfl

private lemma smul_eq_sum_single' {d : ℕ} (h : ℝ) (u : Fin d → ℝ) :
    (h • u : Fin d → ℝ) = ∑ i, (h * u i) • (Pi.single i 1 : Fin d → ℝ) := by
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ a]
  simp

private lemma diagonal_expansion {d j : ℕ} (f : (Fin d → ℝ) → ℝ)
    (x0 u : Fin d → ℝ) (h : ℝ) :
    iteratedFDeriv ℝ j f x0 (fun _ => h • u) =
      ∑ ι : Fin j → Fin d, h ^ j * iteratedFDeriv ℝ j f x0
        (fun l => Pi.single (ι l) 1) * ∏ i, u i ^ indexCount ι i := by
  classical
  have he : (fun _ : Fin j => h • u) =
      fun _ => ∑ i, (h * u i) • (Pi.single i 1 : Fin d → ℝ) := by
    funext l
    exact smul_eq_sum_single' h u
  rw [he, ContinuousMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro ι hι
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, prod_eq_monomial]
  ring

/-- A multivariate function in a Hölder ball can be approximated locally by any monomial basis
that contains every exponent up to the required Taylor order, with error proportional to the
smoothness radius times bandwidth raised to the Hölder exponent. -/
theorem holder_taylor_monomial_approx {d p : ℕ} {β L r : ℝ} {x0 : Fin d → ℝ}
    {S : Set (Fin d → ℝ)}
    (hβ : 0 < β) (hL : 0 < L) (hr : 0 < r)
    (hS : {x : Fin d → ℝ | ∀ i, |x i - x0 i| ≤ r} ⊆ S)
    (expo : Fin p → (Fin d → ℕ))
    (hcover : ∀ e : Fin d → ℕ, (∑ j, e j) ≤ ⌈β⌉₊ - 1 → ∃ k, expo k = e) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ f : (Fin d → ℝ) → ℝ, HolderBallStd f β L S →
        ∀ h : ℝ, 0 < h → h < r →
          ∃ θ : Fin p → ℝ,
            ∀ u : Fin d → ℝ, (∀ j, |u j| ≤ 1) →
              |f (x0 + h • u) - ∑ k, θ k * ∏ j, (u j) ^ (expo k j)| ≤
                Cb * L * h ^ β := by
  classical
  let m := ⌈β⌉₊ - 1
  refine ⟨1 / (Nat.factorial m : ℝ), by positivity, ?_⟩
  intro f hf h hh hhr
  let pick : ∀ (j : Fin (m + 1)) (ι : Fin j → Fin d), Fin p := fun j ι =>
    Classical.choose (hcover (indexCount ι) (by rw [sum_indexCount]; omega))
  have hpick : ∀ (j : Fin (m + 1)) (ι : Fin j → Fin d),
      expo (pick j ι) = indexCount ι := fun j ι =>
    Classical.choose_spec (hcover (indexCount ι) (by rw [sum_indexCount]; omega))
  let θ : Fin p → ℝ := fun k => ∑ j : Fin (m + 1), ∑ ι : Fin j → Fin d,
    if pick j ι = k then
      (1 / (Nat.factorial j : ℝ)) * h ^ (j : ℕ) *
        iteratedFDeriv ℝ (j : ℕ) f x0 (fun l => Pi.single (ι l) 1)
    else 0
  refine ⟨θ, ?_⟩
  intro u hu
  have hpoly : (∑ k, θ k * ∏ i, u i ^ expo k i) =
      ∑ j : Fin (m + 1), (1 / (Nat.factorial (j : ℕ) : ℝ)) *
        iteratedFDeriv ℝ (j : ℕ) f x0 (fun _ => h • u) := by
    simp only [θ, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm, diagonal_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ι hι
    rw [Finset.sum_eq_single (pick j ι)]
    · simp [hpick]
      ring
    · intro k hk hne
      simp [hne.symm]
    · simp
  have hpoly' : (∑ j ∈ Finset.range (m + 1),
      (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j f x0 (fun _ => h • u)) =
      ∑ k, θ k * ∏ i, u i ^ expo k i := by
    rw [hpoly]
    exact (Fin.sum_univ_eq_sum_range _ (m + 1)).symm
  set U : Set (Fin d → ℝ) := {x | ∀ i, |x i - x0 i| < r}
  have hU : IsOpen U := by
    rw [show U = ⋂ i, {x : Fin d → ℝ | |x i - x0 i| < r} by ext x; simp [U]]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)
  have hUS : U ⊆ S := fun x hx => hS (fun i => le_of_lt (hx i))
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • (h • u) ∈ U := by
    intro t ht i
    have he : (x0 + t • (h • u)) i - x0 i = t * (h * u i) := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [he, abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_pos hh]
    calc
      t * (h * |u i|) ≤ 1 * (h * |u i|) :=
        mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hh.le (abs_nonneg _))
      _ ≤ h := by simpa using mul_le_mul_of_nonneg_left (hu i) hh.le
      _ < r := hhr
  have hb := holder_line_taylor hβ hf hU hUS x0 (h • u) hseg
  rw [show ⌈β⌉₊ - 1 = m from rfl, hpoly'] at hb
  have hunorm : ‖u‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    simpa using hu i
  have hy : ‖h • u‖ ≤ h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    calc
      h * ‖u‖ ≤ h * 1 := mul_le_mul_of_nonneg_left hunorm hh.le
      _ = h := mul_one h
  calc
    _ ≤ (L / (Nat.factorial m : ℝ)) * ‖h • u‖ ^ β := hb
    _ ≤ (L / (Nat.factorial m : ℝ)) * h ^ β := by
      gcongr
    _ = (1 / (Nat.factorial m : ℝ)) * L * h ^ β := by ring

end Causalean.Stat.Nonparametric
