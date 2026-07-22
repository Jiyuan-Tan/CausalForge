/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Experimentation.DesignBased.GaussianCDF
import Mathlib.Order.LiminfLimsup

/-!
# Design-based conservative Wald-interval coverage

A paper-agnostic asymptotic-coverage transfer for two-sided Wald intervals built from a
*deterministic conservative* standard error. It is stated over abstract per-stage sequences — a
design `D n`, an estimator `est n`, a target `θ n`, the true variance scale `v n`, a conservative
(dominating) variance `v̂ n`, and the normalization size `m n` — so every design-based paper with a
studentized CLT and a conservative variance estimator can instantiate it in one line instead of
re-cloning the liminf/`Pr_split`/coverage argument (as the exposure-mapping, two-stage, and
bipartite-interference formalizations each previously did).
-/

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]

open Classical in
/-- **Conservative Wald-interval liminf coverage.** Consider a sequence of finite designs with an
estimator `est n` of a target `θ n`. Suppose the studentized statistic
`√(m n) · (est n − θ n) / √(v n)` converges in distribution to the standard normal (its lower CDF
tends to `Φ` at every point), a deterministic conservative variance `v̂ n` dominates the true
variance scale `v n` at every stage, and the normalization size `m n` is eventually positive. Then
the two-sided interval `|θ n − est n| ≤ z · √(v̂ n / m n)`, with `z` the upper `1 − α/2` normal
quantile, has asymptotic (liminf) coverage at least `1 − α`.

The dominating conservative variance is what makes the interval *conservative*: replacing the true
`v n` by the larger `v̂ n` only widens it, so the standard-normal coverage limit becomes a lower
bound on the realized coverage. -/
lemma conservative_wald_liminf_of_studentized_cdf
    (D : ∀ n, FiniteDesign (Ω n))
    (est : ∀ n, Ω n → ℝ) (θ v vhat m : ℕ → ℝ)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hvarpos : ∀ᶠ n in atTop, 0 < v n)
    (hvar_le : ∀ n, v n ≤ vhat n)
    (hclt : ∀ s : ℝ, Tendsto (fun n =>
        (D n).Pr (fun zz =>
          Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) ≤ s))
        atTop (𝓝 (stdNormalCdf s)))
    (α z : ℝ) (hz0 : 0 ≤ z) (hz : stdNormalCdf z = 1 - α / 2) :
    1 - α ≤ liminf (fun n =>
        (D n).Pr (fun zz =>
          |θ n - est n zz| ≤ z * Real.sqrt (vhat n / m n)))
        atTop := by
  classical
  set S : ℕ → ℝ := fun n =>
    (D n).Pr (fun zz =>
      Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) ≤ z) with hSdef
  set Lo : ℕ → ℝ := fun n =>
    (D n).Pr (fun zz =>
      Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) ≤ -z) with hLodef
  set Iv : ℕ → ℝ := fun n =>
    (D n).Pr (fun zz =>
      |θ n - est n zz| ≤ z * Real.sqrt (vhat n / m n)) with hIdef
  have hS : Tendsto S atTop (𝓝 (stdNormalCdf z)) := by
    simpa [S] using hclt z
  have hLo : Tendsto Lo atTop (𝓝 (stdNormalCdf (-z))) := by
    simpa [Lo] using hclt (-z)
  have hlim : Tendsto (fun n => S n - Lo n) atTop (𝓝 (1 - α)) := by
    have h := hS.sub hLo
    rw [stdNormalCdf_neg z, hz] at h
    have he : (1 - α / 2) - (1 - (1 - α / 2)) = 1 - α := by ring
    rwa [he] at h
  have hbound : ∀ᶠ n in atTop, S n - Lo n ≤ Iv n := by
    filter_upwards [hvarpos, hmpos] with n hvpos hmposn
    set W : Ω n → ℝ := fun zz =>
      Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) with hWdef
    have hsplit := (D n).Pr_split (fun zz => W zz ≤ z) (fun zz => W zz ≤ -z)
    have hfirst : (D n).Pr (fun zz => W zz ≤ z ∧ W zz ≤ -z) = Lo n := by
      apply (D n).Pr_congr
      intro zz
      constructor
      · exact fun h => h.2
      · intro h2
        exact ⟨le_trans h2 (by linarith [hz0]), h2⟩
    have hSLo : S n - Lo n =
        (D n).Pr (fun zz => W zz ≤ z ∧ ¬ W zz ≤ -z) := by
      have : S n = (D n).Pr (fun zz => W zz ≤ z ∧ W zz ≤ -z)
          + (D n).Pr (fun zz => W zz ≤ z ∧ ¬ W zz ≤ -z) := by
        simpa [S, W, hWdef] using hsplit
      rw [this, hfirst]
      ring
    rw [hSLo]
    apply (D n).Pr_mono
    intro zz hzz
    obtain ⟨hzhi, hzlo_not⟩ := hzz
    rw [not_le] at hzlo_not
    have habsW : |W zz| ≤ z := abs_le.mpr ⟨le_of_lt hzlo_not, hzhi⟩
    set vn : ℝ := v n with hvndef
    set vhatn : ℝ := vhat n with hvhatndef
    set cardR : ℝ := m n with hcardRdef
    have hcardposR : 0 < cardR := by simpa [cardR] using hmposn
    have hsvar : 0 < Real.sqrt vn := Real.sqrt_pos.mpr (by simpa [vn] using hvpos)
    have hscard : 0 < Real.sqrt cardR := Real.sqrt_pos.mpr hcardposR
    have habs_est : |est n zz - θ n| ≤ z * Real.sqrt vn / Real.sqrt cardR := by
      rw [hWdef, abs_div, abs_mul, abs_of_pos hsvar,
        abs_of_nonneg (Real.sqrt_nonneg cardR), div_le_iff₀ hsvar] at habsW
      have hmul : Real.sqrt cardR * |est n zz - θ n| ≤ z * Real.sqrt vn := by
        simpa [vn, cardR, mul_comm, mul_left_comm, mul_assoc] using habsW
      exact (le_div_iff₀ hscard).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    have hsqrt_le : Real.sqrt vn / Real.sqrt cardR ≤ Real.sqrt (vhatn / cardR) := by
      rw [← Real.sqrt_div (le_of_lt (by simpa [vn] using hvpos)) cardR]
      exact Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right (by simpa [vn, vhatn] using hvar_le n) hcardposR.le)
    have hscale_le : z * Real.sqrt vn / Real.sqrt cardR ≤ z * Real.sqrt (vhatn / cardR) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hsqrt_le hz0
    have habs_tau : |θ n - est n zz| ≤ z * Real.sqrt (vhatn / cardR) := by
      rw [abs_sub_comm]
      exact habs_est.trans hscale_le
    simpa [Iv, vhatn, cardR] using habs_tau
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => S n - Lo n) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop Iv :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ)) (fun n => (D n).Pr_le_one _)
  calc
    1 - α = liminf (fun n => S n - Lo n) atTop := hlim.liminf_eq.symm
    _ ≤ liminf Iv atTop := Filter.liminf_le_liminf hbound hbdd hcobdd
    _ = liminf (fun n =>
        (D n).Pr (fun zz =>
          |θ n - est n zz| ≤ z * Real.sqrt (vhat n / m n)))
        atTop := by rfl

end DesignBased
end Experimentation
end Causalean
