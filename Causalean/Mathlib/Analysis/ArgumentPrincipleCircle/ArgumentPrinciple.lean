/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.Basic

/-!
# The argument principle for a positively oriented circle

This module proves the circle argument principle: the normalized
logarithmic-derivative integral equals the multiplicity-weighted number of
zeros strictly inside the disk. It also records its integrality and positivity
consequences.
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace Causalean.Mathlib.Analysis.ArgumentPrincipleCircle

/-- A complex function analytic on a neighborhood of a closed disk and nonzero on its boundary
has only finitely many zeros strictly inside that disk. -/
theorem finite_interiorZeros {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    (interiorZeros f c R).Finite := by
  let w : ℂ := c + R
  have hwS : w ∈ sphere c R := by simp [w, abs_of_pos hR]
  have hwC : w ∈ closedBall c R := sphere_subset_closedBall hwS
  have hmw : meromorphicOrderAt f w ≠ ⊤ := by
    rw [(hf w hwC).meromorphicOrderAt_eq,
      (hf w hwC).analyticOrderAt_eq_zero.2 (hboundary w hwS)]
    simp
  have hfinite : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤ :=
    fun z hz ↦ hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hwC hz hmw
  apply ((MeromorphicOn.divisor f (closedBall c R)).finiteSupport
    (isCompact_closedBall c R)).subset
  intro z hz
  rcases hz with ⟨hzball, hzf⟩
  have hzC : z ∈ closedBall c R := ball_subset_closedBall hzball
  have hmzero : meromorphicOrderAt f z ≠ 0 := by
    rw [(hf z hzC).meromorphicOrderAt_eq]
    simpa using (hf z hzC).analyticOrderAt_ne_zero.2 hzf
  rw [Function.mem_support, MeromorphicOn.divisor_apply hf.meromorphicOn hzC]
  intro h
  rw [WithTop.untop₀_eq_zero] at h
  exact h.elim hmzero (hfinite z hzC)

open Classical in
/-- Under disk analyticity and boundary nonvanishing, the function assigning each interior zero
its analytic multiplicity and all other points zero has finite support. -/
theorem finiteSupport_orderWithinBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    Function.HasFiniteSupport
      (fun z : ℂ ↦ if z ∈ ball c R then analyticOrderNatAt f z else 0) := by
  apply (finite_interiorZeros hR hf hboundary).subset
  intro z hz
  rw [Function.mem_support] at hz
  by_cases hzb : z ∈ ball c R
  · exact ⟨hzb, apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa [hzb] using hz)⟩
  · simp [hzb] at hz

private theorem logDeriv_factorizedRational_eq_sum {D : ℂ → ℤ}
    (hD : D.HasFiniteSupport) {x : ℂ} (hx : D x = 0) :
    logDeriv (∏ᶠ u, (· - u) ^ D u) x =
      ∑ u ∈ hD.toFinset, (D u : ℂ) * (x - u)⁻¹ := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset (s := hD.toFinset)]
  · rw [show (∏ u ∈ hD.toFinset, (· - u) ^ D u) =
        fun z ↦ ∏ u ∈ hD.toFinset, (z - u) ^ D u by
          ext z
          simp]
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [logDeriv_fun_zpow (by fun_prop)]
      simp [logDeriv_apply]
    · intro u hu
      have hux : u ≠ x := by
        intro h
        subst u
        exact (Set.Finite.mem_toFinset _).mp hu hx
      exact zpow_ne_zero _ (sub_ne_zero.mpr hux.symm)
    · intro u hu
      have hux : u ≠ x := by
        intro h
        subst u
        exact (Set.Finite.mem_toFinset _).mp hu hx
      have hp : DifferentiableAt ℂ (fun y : ℂ ↦ y ^ D u) (x - u) :=
        differentiableAt_zpow.2 (.inl (sub_ne_zero.mpr hux.symm))
      exact hp.comp x (differentiableAt_id.sub_const u)
  · simp only [Function.FactorizedRational.mulSupport]
    intro y hy
    exact (Set.Finite.mem_toFinset _).mpr hy

/-- **Argument principle for a circle.** For [a positive radius `R`](hyp:hR), if
[the function `f` is complex-analytic on a neighborhood of the closed disk of
radius `R` centered at `c`](hyp:hf) and [`f` is nonzero on the boundary
circle](hyp:hboundary), then [the normalized logarithmic-derivative integral of
`f` around that circle equals the number of zeros of `f` strictly inside the
disk, counted with analytic multiplicity](goal). -/
theorem argumentPrinciple_circle {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    normalizedLogDerivCircleIntegral f c R = (zeroMultiplicityCount f c R : ℂ) := by
  classical
  let U := closedBall c R
  let D := MeromorphicOn.divisor f U
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  let w : ℂ := c + R
  have hwS : w ∈ sphere c R := by simp [w, abs_of_pos hR]
  have hwU : w ∈ U := sphere_subset_closedBall hwS
  have hmw : meromorphicOrderAt f w ≠ ⊤ := by
    rw [(hf w hwU).meromorphicOrderAt_eq,
      (hf w hwU).analyticOrderAt_eq_zero.2 (hboundary w hwS)]
    simp
  have hfinite : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤ :=
    fun z hz ↦ hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hwU hz hmw
  have hDfinite : D.support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall c R)
  obtain ⟨g, hg, hgne, hfg⟩ :=
    hf.meromorphicOn.extract_zeros_poles (fun z ↦ hfinite z z.property) hDfinite
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hPan : AnalyticOnNhd ℂ P U := by
    intro z hz
    exact Function.FactorizedRational.analyticAt (hDnonneg z)
  have hPgan : AnalyticOnNhd ℂ (fun z ↦ P z * g z) U := hPan.mul hg
  have hfg' : f =ᶠ[codiscreteWithin U] fun z ↦ P z * g z := by
    have h0 : f =ᶠ[codiscreteWithin U] P * g := by
      simpa [P, U, smul_eq_mul] using hfg
    exact h0
  have hcU : c ∈ U := by simp [U, hR.le]
  have hlocal : f =ᶠ[𝓝[≠] c] fun z ↦ P z * g z := by
    change {z | f z = P z * g z} ∈ codiscreteWithin U at hfg'
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hfg'
    filter_upwards [hfg' c hcU,
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds c hR)] with z hz hzU
    exact hz.resolve_right (by simpa [U] using hzU)
  have heq : EqOn f (fun z ↦ P z * g z) U :=
    hf.eqOn_of_preconnected_of_frequently_eq hPgan
      (convex_closedBall c R).isPreconnected hcU hlocal.frequently
  have hDz (z : ℂ) (hz : z ∈ sphere c R) : D z = 0 := by
    have hzU : z ∈ U := sphere_subset_closedBall hz
    dsimp [D]
    rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzU,
      (hf z hzU).meromorphicOrderAt_eq,
      (hf z hzU).analyticOrderAt_eq_zero.2 (hboundary z hz)]
    simp
  have hlogeq : EqOn (logDeriv f)
      (fun z ↦ (∑ u ∈ hDfinite.toFinset, (D u : ℂ) * (z - u)⁻¹) + logDeriv g z)
      (sphere c R) := by
    intro z hz
    have hzU : z ∈ U := sphere_subset_closedBall hz
    have hznb : z ∉ ball c R := by
      rw [mem_ball, mem_sphere] at *
      exact not_lt_of_ge hz.ge
    have hzcl : z ∈ closure (ball c R) := by
      rw [closure_ball c hR.ne']
      exact hzU
    have hfreq : ∃ᶠ y in 𝓝[≠] z, f y = P y * g y :=
      (mem_closure_ne_iff_frequently_within.mp (by
        rw [diff_singleton_eq_self hznb]
        exact hzcl)).mono
        fun y hy ↦ heq (by exact ball_subset_closedBall hy)
    have hnear : f =ᶠ[𝓝 z] fun y ↦ P y * g y :=
      ((hf z hzU).frequently_eq_iff_eventually_eq (hPgan z hzU)).mp hfreq
    calc
      logDeriv f z = logDeriv (fun y ↦ P y * g y) z := by
        simp only [logDeriv_apply, hnear.eq_of_nhds, hnear.deriv_eq]
      _ = logDeriv P z + logDeriv g z :=
        logDeriv_mul z (Function.FactorizedRational.ne_zero (hDz z hz))
          (hgne ⟨z, hzU⟩) (hPan z hzU).differentiableAt
          (hg z hzU).differentiableAt
      _ = _ := by rw [logDeriv_factorizedRational_eq_sum hDfinite (hDz z hz)]
  have hloggan : AnalyticOnNhd ℂ (logDeriv g) U := by
    intro z hz
    exact (hg.deriv z hz).div (hg z hz) (hgne ⟨z, hz⟩)
  have hloggzero : circleIntegral (logDeriv g) c R = 0 :=
    (hloggan.differentiableOn.diffContOnCl_ball (by simp [U])).circleIntegral_eq_zero hR.le
  have hterm (u : ℂ) (hu : u ∈ hDfinite.toFinset) :
      CircleIntegrable (fun z ↦ (D u : ℂ) * (z - u)⁻¹) c R := by
    have huD : D u ≠ 0 := by simpa using hu
    have huS : u ∉ sphere c R := by
      intro hus
      exact huD (hDz u hus)
    exact ((circleIntegrable_sub_inv_iff.mpr (.inr (by simpa [abs_of_pos hR] using huS))).const_mul _)
  have hsumInt : circleIntegral
      (fun z ↦ ∑ u ∈ hDfinite.toFinset, (D u : ℂ) * (z - u)⁻¹) c R =
      ∑ u ∈ hDfinite.toFinset, (D u : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [circleIntegral.integral_fun_sum hterm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball]
    have huSupp : u ∈ D.support := by simpa using hu
    have huU : u ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain huSupp
    have huNS : u ∉ sphere c R := by
      intro hus
      exact (show D u ≠ 0 by simpa using hu) (hDz u hus)
    have huUdist : dist u c ≤ R := by simpa [U, mem_closedBall] using huU
    have hdistne : dist u c ≠ R := by
      intro h
      apply huNS
      exact h
    rw [mem_ball]
    exact lt_of_le_of_ne huUdist hdistne
  have hloggCI : CircleIntegrable (logDeriv g) c R :=
    hloggan.continuousOn.mono (sphere_subset_closedBall : sphere c R ⊆ U) |>.circleIntegrable hR.le
  have hcircle : circleIntegral (logDeriv f) c R =
      ∑ u ∈ hDfinite.toFinset, (D u : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [circleIntegral.integral_congr hR.le hlogeq,
      circleIntegral.integral_add (CircleIntegrable.fun_sum _ hterm) hloggCI,
      hsumInt, hloggzero, add_zero]
  have hsum : (∑ u ∈ hDfinite.toFinset, (D u : ℂ)) =
      (zeroMultiplicityCount f c R : ℂ) := by
    unfold zeroMultiplicityCount
    rw [finsum_eq_sum_of_support_subset
      (s := hDfinite.toFinset) (fun u ↦ if u ∈ ball c R then analyticOrderNatAt f u else 0)]
    · push_cast
      apply Finset.sum_congr rfl
      intro u hu
      have huSupp : u ∈ D.support := by simpa using hu
      have huU : u ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain huSupp
      have huNS : u ∉ sphere c R := by
        intro hus
        exact (show D u ≠ 0 by simpa using hu) (hDz u hus)
      have huB : u ∈ ball c R := by
        have huUdist : dist u c ≤ R := by simpa [U, mem_closedBall] using huU
        have hdistne : dist u c ≠ R := by
          intro h
          apply huNS
          exact h
        rw [mem_ball]
        exact lt_of_le_of_ne huUdist hdistne
      simp only [huB, if_true]
      congr 1
      dsimp [D]
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn huU,
        (hf u huU).meromorphicOrderAt_eq]
      have haufinite : analyticOrderAt f u ≠ ⊤ := by
        have hm := hfinite u huU
        rw [(hf u huU).meromorphicOrderAt_eq] at hm
        simpa using hm
      rw [← Nat.cast_analyticOrderNatAt haufinite]
      simp
    · intro u hu
      rw [Function.mem_support] at hu
      by_cases huB : u ∈ ball c R
      · have huU : u ∈ U := ball_subset_closedBall huB
        have haufinite : analyticOrderAt f u ≠ ⊤ := by
          have hm := hfinite u huU
          rw [(hf u huU).meromorphicOrderAt_eq] at hm
          simpa using hm
        have hDu : D u = (analyticOrderNatAt f u : ℤ) := by
          dsimp [D]
          rw [MeromorphicOn.divisor_apply hf.meromorphicOn huU,
            (hf u huU).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt haufinite]
          simp
        have hnat : analyticOrderNatAt f u ≠ 0 := by simpa [huB] using hu
        have hDne : D u ≠ 0 := by
          rw [hDu]
          exact_mod_cast hnat
        rw [hDfinite.coe_toFinset, Function.mem_support]
        exact hDne
      · simp [huB] at hu
  rw [normalizedLogDerivCircleIntegral, hcircle, ← Finset.sum_mul, hsum]
  have hK : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  rw [mul_comm (zeroMultiplicityCount f c R : ℂ), inv_mul_cancel_left₀ hK]

/-- The normalized logarithmic-derivative integral of a boundary-zero-free analytic function is
a nonnegative whole number, viewed as a complex number. -/
theorem normalizedLogDerivCircleIntegral_exists_nat {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ n : ℕ, normalizedLogDerivCircleIntegral f c R = (n : ℂ) := by
  exact ⟨zeroMultiplicityCount f c R, argumentPrinciple_circle hR hf hboundary⟩

/-- A boundary-zero-free analytic function that vanishes somewhere strictly inside the disk has
a strictly positive multiplicity-weighted interior zero count. -/
theorem zeroMultiplicityCount_pos_of_exists_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0)
    (hzero : ∃ z ∈ ball c R, f z = 0) :
    0 < zeroMultiplicityCount f c R := by
  classical
  rcases hzero with ⟨z, hzball, hzf⟩
  let w : ℂ := c + R
  have hwS : w ∈ sphere c R := by simp [w, abs_of_pos hR]
  have hwC : w ∈ closedBall c R := sphere_subset_closedBall hwS
  have hmw : meromorphicOrderAt f w ≠ ⊤ := by
    rw [(hf w hwC).meromorphicOrderAt_eq,
      (hf w hwC).analyticOrderAt_eq_zero.2 (hboundary w hwS)]
    simp
  have hzC : z ∈ closedBall c R := ball_subset_closedBall hzball
  have hmfinite : meromorphicOrderAt f z ≠ ⊤ :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hwC hzC hmw
  have hafinite : analyticOrderAt f z ≠ ⊤ := by
    rw [(hf z hzC).meromorphicOrderAt_eq] at hmfinite
    simpa using hmfinite
  have hzpos : 0 < analyticOrderNatAt f z := Nat.pos_of_ne_zero fun hz0 ↦ by
    have := (hf z hzC).analyticOrderAt_ne_zero.2 hzf
    apply this
    rw [← Nat.cast_analyticOrderNatAt hafinite, hz0]
    rfl
  unfold zeroMultiplicityCount
  apply finsum_pos
  · intro u
    positivity
  · exact ⟨z, by simpa [hzball]⟩
  · exact finiteSupport_orderWithinBall hR hf hboundary

/-- A boundary-zero-free analytic function with an interior zero has normalized
logarithmic-derivative integral with strictly positive real part. -/
theorem normalizedLogDerivCircleIntegral_re_pos_of_exists_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0)
    (hzero : ∃ z ∈ ball c R, f z = 0) :
    0 < (normalizedLogDerivCircleIntegral f c R).re := by
  rw [argumentPrinciple_circle hR hf hboundary]
  simpa using zeroMultiplicityCount_pos_of_exists_zero hR hf hboundary hzero

end Causalean.Mathlib.Analysis.ArgumentPrincipleCircle
