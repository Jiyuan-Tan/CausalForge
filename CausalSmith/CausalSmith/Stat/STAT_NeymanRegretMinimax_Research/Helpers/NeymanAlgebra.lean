/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Neyman-gap algebra: exact gap identity and quadratic expansion

Stage-2 scaffold.  The exact Neyman-gap ratio identity, the quadratic
loss/oracle-sensitivity expansion along a local path.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Tilt

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics Filter
open scoped BigOperators Topology

-- @node: oracleAllocation_eq_root_ratio
/-- The reusable ratio form of the oracle allocation.  The definition goes through
`neymanFraction` on squared root moments; nonnegativity of `rootSecondMoment`
removes the absolute values. -/
lemma oracleAllocation_eq_root_ratio (nu : Measure (ℝ × ℝ)) :
    oracleAllocation nu =
      rootSecondMoment nu 1 / (rootSecondMoment nu 0 + rootSecondMoment nu 1) := by
  rw [oracleAllocation, Causalean.Experimentation.DesignBased.neymanFraction]
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ rootSecondMoment nu 1 from Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ rootSecondMoment nu 0 from Real.sqrt_nonneg _)]
  ring

-- @node: hasDerivAt_of_sq_asymptotic_nonneg
/-- If a nonnegative function has a first-order expansion after squaring at a
positive base point, then the function itself has the square-root linearization. -/
lemma hasDerivAt_of_sq_asymptotic_nonneg {f : ℝ → ℝ} {m ua : ℝ} (hm : 0 < m)
    (hf0 : f 0 = m) (hnonneg : ∀ t, 0 ≤ f t)
    (h : (fun t => f t ^ 2 - (m ^ 2 + t * ua)) =o[𝓝 (0 : ℝ)] fun t => t) :
    HasDerivAt f (ua / (2 * m)) 0 := by
  have hsquare : HasDerivAt (fun t => f t ^ 2) ua 0 := by
    apply HasDerivAt.of_isLittleO
    simpa [hf0, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_comm] using h
  have hsq0_ne : (fun t => f t ^ 2) 0 ≠ 0 := by
    simp [hf0, ne_of_gt hm]
  have hsqrt := hsquare.sqrt hsq0_ne
  convert hsqrt using 1
  · ext t
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg t)]
  · rw [hf0, Real.sqrt_sq_eq_abs, abs_of_pos hm]

-- @node: oracleAllocation_path_derivative
/-- Along any `IsLocalPath`, the oracle allocation has derivative
`oracleSensitivity nu u` at the base law. -/
lemma oracleAllocation_path_derivative (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (p : ℝ → Measure (ℝ × ℝ)) (hp : IsLocalPath nu u p) :
    HasDerivAt (fun h => oracleAllocation (p h)) (oracleSensitivity nu u) 0 := by
  let m0 : ℝ := rootSecondMoment nu 0
  let m1 : ℝ := rootSecondMoment nu 1
  let d0 : ℝ := u.1 / (2 * m0)
  let d1 : ℝ := u.2 / (2 * m1)
  have hm0 : 0 < m0 := hnu.interiorMoments 0
  have hm1 : 0 < m1 := hnu.interiorMoments 1
  have hm0_ne : m0 ≠ 0 := ne_of_gt hm0
  have hm1_ne : m1 ≠ 0 := ne_of_gt hm1
  have hS_ne : m0 + m1 ≠ 0 := ne_of_gt (add_pos hm0 hm1)
  have hroot0 : HasDerivAt (fun h => rootSecondMoment (p h) 0) d0 0 := by
    dsimp [d0, m0]
    refine hasDerivAt_of_sq_asymptotic_nonneg (hnu.interiorMoments 0) ?_ ?_ ?_
    · simp [hp.1]
    · intro t
      exact Real.sqrt_nonneg _
    · simpa using hp.2.2.2.2.1 0
  have hroot1 : HasDerivAt (fun h => rootSecondMoment (p h) 1) d1 0 := by
    dsimp [d1, m1]
    refine hasDerivAt_of_sq_asymptotic_nonneg (hnu.interiorMoments 1) ?_ ?_ ?_
    · simp [hp.1]
    · intro t
      exact Real.sqrt_nonneg _
    · simpa using hp.2.2.2.2.1 1
  have hden :
      HasDerivAt
        (fun h => rootSecondMoment (p h) 0 + rootSecondMoment (p h) 1)
        (d0 + d1) 0 :=
    hroot0.add hroot1
  have hden_ne :
      (fun h => rootSecondMoment (p h) 0 + rootSecondMoment (p h) 1) 0 ≠ 0 := by
    simpa [hp.1, m0, m1] using hS_ne
  have hratio := hroot1.div hden hden_ne
  have hratio_clean :
      HasDerivAt
        (fun h => rootSecondMoment (p h) 1 /
          (rootSecondMoment (p h) 0 + rootSecondMoment (p h) 1))
        ((d1 * (m0 + m1) - m1 * (d0 + d1)) / (m0 + m1) ^ 2) 0 := by
    simpa [hp.1, m0, m1] using hratio
  have hderiv_eq :
      ((d1 * (m0 + m1) - m1 * (d0 + d1)) / (m0 + m1) ^ 2)
        = oracleSensitivity nu u := by
    change
      (((u.2 / (2 * m1)) * (m0 + m1) -
          m1 * (u.1 / (2 * m0) + u.2 / (2 * m1))) / (m0 + m1) ^ 2)
        = (u.2 * m0 / m1 - u.1 * m1 / m0) / (2 * (m0 + m1) ^ 2)
    field_simp [hm0_ne, hm1_ne, hS_ne]
    ring
  have hratio' :
      HasDerivAt
        (fun h => rootSecondMoment (p h) 1 /
          (rootSecondMoment (p h) 0 + rootSecondMoment (p h) 1))
        (oracleSensitivity nu u) 0 := by
    simpa [hderiv_eq] using hratio_clean
  convert hratio' using 1
  · ext h
    rw [oracleAllocation_eq_root_ratio]

-- @node: lem:neyman-gap-identity
/-- Exact Neyman-gap identity: with `S = m₀+m₁` and `p = π_nu* = m₁/S`,
`V_nu(π) − V_nu(p) = S²(π−p)² / (π(1−π))` for every `π ∈ (0,1)`. -/
lemma neyman_gap_identity (nu : Measure (ℝ × ℝ)) (hm : InteriorSecondMoments nu)
    (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    varianceObjective nu π - varianceObjective nu (oracleAllocation nu)
      = (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2 * (π - oracleAllocation nu) ^ 2
        / (π * (1 - π)) := by
  have hm0 : 0 < rootSecondMoment nu 0 := hm 0
  have hm1 : 0 < rootSecondMoment nu 1 := hm 1
  have hpiden : π ≠ 0 := ne_of_gt hπ0
  have h1p_pos : 0 < 1 - π := sub_pos.mpr hπ1
  have h1pden : 1 - π ≠ 0 := ne_of_gt h1p_pos
  have hsum_pos : 0 < rootSecondMoment nu 0 + rootSecondMoment nu 1 :=
    add_pos hm0 hm1
  have hsum_ne : rootSecondMoment nu 0 + rootSecondMoment nu 1 ≠ 0 :=
    ne_of_gt hsum_pos
  have halloc :
      oracleAllocation nu =
        rootSecondMoment nu 1 / (rootSecondMoment nu 0 + rootSecondMoment nu 1) := by
    rw [oracleAllocation, Causalean.Experimentation.DesignBased.neymanFraction]
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    rw [abs_of_pos hm1, abs_of_pos hm0]
    ring
  rw [varianceObjective, varianceObjective, halloc]
  field_simp [hpiden, h1pden, hsum_ne, ne_of_gt hm0, ne_of_gt hm1]
  ring

-- @node: neymanGap_quadratic_isLittleO
/-- Quadratic expansion of the exact Neyman-gap identity around the oracle
allocation. -/
lemma neymanGap_quadratic_isLittleO (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) :
    (fun δ => neymanGap nu (oracleAllocation nu + δ) - lossCurvature nu * δ ^ 2)
        =o[𝓝 (0 : ℝ)] (fun δ => δ ^ 2) := by
  let m0 : ℝ := rootSecondMoment nu 0
  let m1 : ℝ := rootSecondMoment nu 1
  let S : ℝ := m0 + m1
  let pstar : ℝ := oracleAllocation nu
  have hm0 : 0 < m0 := hnu.interiorMoments 0
  have hm1 : 0 < m1 := hnu.interiorMoments 1
  have hm0_ne : m0 ≠ 0 := ne_of_gt hm0
  have hm1_ne : m1 ≠ 0 := ne_of_gt hm1
  have hS_pos : 0 < S := add_pos hm0 hm1
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hpstar_ratio : pstar = m1 / S := by
    dsimp [pstar, m0, m1, S]
    exact oracleAllocation_eq_root_ratio nu
  have hpstar_pos : 0 < pstar := by
    dsimp [pstar]
    rw [oracleAllocation]
    exact (Causalean.Experimentation.DesignBased.neymanFraction_mem_Ioo
      (by positivity) (by positivity)).1
  have hpstar_lt : pstar < 1 := by
    dsimp [pstar]
    rw [oracleAllocation]
    exact (Causalean.Experimentation.DesignBased.neymanFraction_mem_Ioo
      (by positivity) (by positivity)).2
  have hconst_p : Tendsto (fun _δ : ℝ => pstar) (𝓝 (0 : ℝ)) (𝓝 pstar) :=
    tendsto_const_nhds
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_id
  have hpi_tendsto :
      Tendsto (fun δ : ℝ => pstar + δ) (𝓝 (0 : ℝ)) (𝓝 pstar) := by
    simpa using hconst_p.add hid
  have hconst_one :
      Tendsto (fun _δ : ℝ => (1 : ℝ)) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hden_lim :
      Tendsto (fun δ : ℝ => (pstar + δ) * (1 - (pstar + δ)))
        (𝓝 (0 : ℝ)) (𝓝 (pstar * (1 - pstar))) := by
    exact hpi_tendsto.mul (hconst_one.sub hpi_tendsto)
  have hpden_ne : pstar * (1 - pstar) ≠ 0 := by
    exact mul_ne_zero (ne_of_gt hpstar_pos) (ne_of_gt (sub_pos.mpr hpstar_lt))
  have hcoef_lim :
      Tendsto
        (fun δ : ℝ => S ^ 2 / ((pstar + δ) * (1 - (pstar + δ))))
        (𝓝 (0 : ℝ)) (𝓝 (lossCurvature nu)) := by
    have hquot :
        Tendsto
          (fun δ : ℝ => S ^ 2 / ((pstar + δ) * (1 - (pstar + δ))))
          (𝓝 (0 : ℝ)) (𝓝 (S ^ 2 / (pstar * (1 - pstar)))) := by
      exact tendsto_const_nhds.div hden_lim hpden_ne
    have hcurv : S ^ 2 / (pstar * (1 - pstar)) = lossCurvature nu := by
      rw [hpstar_ratio]
      change S ^ 2 / (m1 / S * (1 - m1 / S)) = S ^ 4 / (m0 * m1)
      field_simp [hm0_ne, hm1_ne, hS_ne]
      rw [show S - m1 = m0 by dsimp [S]; ring]
      field_simp [hm0_ne]
    simpa [hcurv] using hquot
  have hconst_curv :
      Tendsto (fun _δ : ℝ => lossCurvature nu) (𝓝 (0 : ℝ))
        (𝓝 (lossCurvature nu)) :=
    tendsto_const_nhds
  have hcoef_o :
      (fun δ : ℝ =>
          S ^ 2 / ((pstar + δ) * (1 - (pstar + δ))) - lossCurvature nu)
        =o[𝓝 (0 : ℝ)] (fun _δ : ℝ => (1 : ℝ)) := by
    exact (isLittleO_one_iff ℝ).2 (by simpa using hcoef_lim.sub hconst_curv)
  have hprod_o :
      (fun δ : ℝ =>
          (S ^ 2 / ((pstar + δ) * (1 - (pstar + δ))) - lossCurvature nu)
            * δ ^ 2)
        =o[𝓝 (0 : ℝ)] (fun δ : ℝ => (1 : ℝ) * δ ^ 2) := by
    exact hcoef_o.mul_isBigO (isBigO_refl (fun δ : ℝ => δ ^ 2) (𝓝 (0 : ℝ)))
  have hprod_o' :
      (fun δ : ℝ =>
          δ ^ 2 *
            (S ^ 2 / ((pstar + δ) * (1 - (pstar + δ))) - lossCurvature nu))
        =o[𝓝 (0 : ℝ)] (fun δ : ℝ => δ ^ 2) := by
    convert hprod_o using 1
    · ext δ
      ring
    · ext δ
      ring
  have hpi_event :
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), pstar + δ ∈ Set.Ioo (0 : ℝ) 1 :=
    hpi_tendsto.eventually (isOpen_Ioo.mem_nhds ⟨hpstar_pos, hpstar_lt⟩)
  have heq_event :
      (fun δ : ℝ =>
          neymanGap nu (oracleAllocation nu + δ) - lossCurvature nu * δ ^ 2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun δ : ℝ =>
          δ ^ 2 *
            (S ^ 2 / ((pstar + δ) * (1 - (pstar + δ))) - lossCurvature nu)) := by
    filter_upwards [hpi_event] with δ hδ
    have hgap :=
      neyman_gap_identity nu hnu.interiorMoments (pstar + δ) hδ.1 hδ.2
    have hgap' :
        neymanGap nu (pstar + δ) =
          S ^ 2 * δ ^ 2 / ((pstar + δ) * (1 - (pstar + δ))) := by
      dsimp [neymanGap, S, pstar] at hgap ⊢
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hgap
    rw [hgap']
    dsimp [pstar]
    ring
  exact hprod_o'.congr' heq_event.symm EventuallyEq.rfl

-- @node: prop:quadratic-loss-expansion
/-- Quadratic loss expansion `g_nu(π_nu* + δ) = H_nu δ² + o(δ²)`, and along every
local path the oracle allocation moves as `π_{nu^(u,h)}* = π_nu* + h π̇_nu(u) + o(h)`. -/
lemma quadratic_loss_expansion (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (p : ℝ → Measure (ℝ × ℝ)) (hp : IsLocalPath nu u p) :
    (fun δ => neymanGap nu (oracleAllocation nu + δ) - lossCurvature nu * δ ^ 2)
        =o[𝓝 (0 : ℝ)] (fun δ => δ ^ 2)
      ∧ (fun h => oracleAllocation (p h)
            - (oracleAllocation nu + h * oracleSensitivity nu u))
        =o[𝓝 (0 : ℝ)] fun h => h := by
  constructor
  · exact neymanGap_quadratic_isLittleO nu hnu
  · have hderiv := oracleAllocation_path_derivative nu hnu u p hp
    have ho := hderiv.isLittleO
    simpa [hp.1, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_comm] using ho

end CausalSmith.Stat.NeymanRegretMinimax
