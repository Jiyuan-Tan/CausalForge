/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers

/-! # Odd-`m` positive-gap window (`thm:gap-window`)

For `0 ≤ κ < κ_gap` and `r ∈ (r_gap^-, r_gap^+)` the spread vertex is the unique
relaxed minimizer but violates `y+z ≥ 2/m`, so `Δ_m^± > 0`. Even `m` makes the whole
slice implementable, so the positive gap fails (parity necessity). -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

/-- The low-robustness gap ceiling `κ_gap(m,a,b) = ((2m−a−3b)(a−b)√q)/(a+b)`. -/
noncomputable def kappaGap (m : ℕ) (a b : ℝ) : ℝ :=
  ((2 * (m : ℝ) - a - 3 * b) * (a - b) * Real.sqrt (qParam m)) / (a + b)

/-- The cut-frontier value at the gap scale
`r_cut_gap(m,a,b,κ) = max 0 (2b(a+b)(1 − κ/(a−b)))` (the closed form is independent of `m`);
this is the first (`(a−b)`) branch of the cut-exactness frontier `r_cut(m,a,b,κ)`, active in
the low-scale gap regime, taken as a nonnegative frontier.
@realizes r_cut(m,a,b,kappa)(gap-scale branch 2b(a+b)(1−κ/(a−b)); the declared [0,∞) space is
PINNED BY CONSTRUCTION via the outer `max 0` clamp, so `r_cut_gap ∈ [0,∞)` holds
unconditionally, consistent with the `r_cut` cluster in `Tcut.lean`.) -/
noncomputable def rCutGap (a b kappa : ℝ) : ℝ :=
  max 0 (2 * b * (a + b) * (1 - kappa / (a - b)))

/-- Lower spread frontier `R_x^-(m,a,b,κ) = 2b(a+b)(1 + κ/((a−b)√q))`. -/
noncomputable def RxMinus (m : ℕ) (a b kappa : ℝ) : ℝ :=
  2 * b * (a + b) * (1 + kappa / ((a - b) * Real.sqrt (qParam m)))

/-- Upper spread frontier `R_x^+(m,a,b,κ) = (a+b)(2m−a−b−κ/√q)`. -/
noncomputable def RxPlus (m : ℕ) (a b kappa : ℝ) : ℝ :=
  (a + b) * (2 * (m : ℝ) - a - b - kappa / Real.sqrt (qParam m))

/-- Lower gap-window frontier `r_gap^-(m,a,b,κ) = (R_x^- + R_x^+)/2`.
@realizes r_gap^-(m,a,b,kappa), r_gap^+(m,a,b,kappa)(AUTHORITATIVE carrier of the FIRST
component `r_gap^-` of the pair symbol whose declared space is `[0,∞)^2`; closed form
`(R_x^- + R_x^+)/2` with `R_x^- = 2b(a+b)(1+κ/((a−b)√q))` and `R_x^+ = (a+b)(2m−a−b−κ/√q)`.
The bare closed form is a plain `ℝ`, NOT nonnegative by construction; the FIRST factor of the
`[0,∞)^2` range is carried by the CONJUNCTION of this carrier with the companion range lemma
`rGapFrontiers_nonneg` below — which pins `0 ≤ r_gap^-` on the consuming window
`0 ≤ κ < κ_gap` via `r_cut_gap = max 0 (…) ≥ 0 < r_gap^-` — exactly as
`implementabilityGap`/`roundingLossCertificate` pair with their `*_nonneg` lemmas in
`Basic.lean`.) -/
noncomputable def rGapMinus (m : ℕ) (a b kappa : ℝ) : ℝ :=
  (RxMinus m a b kappa + RxPlus m a b kappa) / 2

/-- Upper gap-window frontier `r_gap^+(m,a,b,κ) = R_x^+`.
@realizes r_gap^-(m,a,b,kappa), r_gap^+(m,a,b,kappa)(AUTHORITATIVE carrier of the SECOND
component `r_gap^+` of the pair symbol whose declared space is `[0,∞)^2`; closed form
`R_x^+ = (a+b)(2m−a−b−κ/√q)`. The bare closed form is a plain `ℝ`, NOT nonnegative by
construction; the SECOND factor of the `[0,∞)^2` range is carried by the CONJUNCTION of this
carrier with the companion range lemma `rGapFrontiers_nonneg` below, which pins `0 ≤ r_gap^+`
on the consuming window `0 ≤ κ < κ_gap` via `r_gap^- < r_gap^+` (placing the open gap interval
`(r_gap^-, r_gap^+) ⊂ [0,∞)`).) -/
noncomputable def rGapPlus (m : ℕ) (a b kappa : ℝ) : ℝ := RxPlus m a b kappa

/-- **Range lemma for the gap-window frontier pair `(r_gap^-, r_gap^+)`.** On the consuming
window `0 ≤ κ < κ_gap`, under two-block homophily and the low-scale normalization, the
frontier pair lands in its core-declared space `[0,∞)^2`: `0 ≤ r_gap^-` and `0 ≤ r_gap^+`.
This holds because `r_cut_gap = max 0 (…) ≥ 0` and the window strictly orders the frontiers
`r_cut_gap < r_gap^- < r_gap^+` (the ordering proved by `gap_window`), so both frontiers are
positive. Together with the `rGapMinus`/`rGapPlus` carrier `def`s above, this lemma IS the
realization of the pair's standing `[0,∞)^2` range condition (the bare `(R_x^- + R_x^+)/2` and
`R_x^+` closed forms are plain `ℝ`, not nonnegative by construction), exactly mirroring how
`implementabilityGap_nonneg` / `roundingLossCertificate_nonneg` pin the `Δ_m^±` / `ρ_⋆` ranges
in `Basic.lean`.
@realizes r_gap^-(m,a,b,kappa), r_gap^+(m,a,b,kappa)(AUTHORITATIVE range clause for the pair
symbol's declared space `[0,∞)^2`: the conjunction `0 ≤ r_gap^- ∧ 0 ≤ r_gap^+` pins BOTH
factors on the consuming window `0 ≤ κ < κ_gap`, via `r_cut_gap = max 0 (…) ≥ 0 < r_gap^- <
r_gap^+`. This lemma, together with the `rGapMinus`/`rGapPlus` carrier `def`s above, IS the
realizing cluster of the pair's standing `[0,∞)^2` range condition.) -/
lemma rGapFrontiers_nonneg (m : ℕ) (a b kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hLow : LowScaleTwoBlock m a b)
    (hk0 : 0 ≤ kappa) (hkGap : kappa < kappaGap m a b) :
    0 ≤ rGapMinus m a b kappa ∧ 0 ≤ rGapPlus m a b kappa := by
  rcases hHom with ⟨hm, hba, hb⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hsqrtq : 0 < Real.sqrt (qParam m) := Real.sqrt_pos.2 hq
  have hA : 0 < a + b := by nlinarith
  have hdiff : 0 < a - b := by linarith
  have hD : 0 < 2 * (m : ℝ) - a - 3 * b := by
    unfold LowScaleTwoBlock at hLow
    linarith
  have hkap_div :
      kappa / Real.sqrt (qParam m)
        < (2 * (m : ℝ) - a - 3 * b) * (a - b) / (a + b) := by
    unfold kappaGap at hkGap
    rw [div_lt_iff₀ hsqrtq]
    convert hkGap using 1
    field_simp [ne_of_gt hA]
  have hD_bound :
      (2 * (m : ℝ) - a - 3 * b) * (a - b) / (a + b)
        < 2 * (m : ℝ) - a - b := by
    rw [div_lt_iff₀ hA]
    nlinarith [hD, hb]
  have hplus_pos : 0 < rGapPlus m a b kappa := by
    unfold rGapPlus RxPlus
    have hinner : 0 < 2 * (m : ℝ) - a - b - kappa / Real.sqrt (qParam m) := by
      linarith
    exact mul_pos hA hinner
  have hminus_nonneg : 0 ≤ RxMinus m a b kappa := by
    unfold RxMinus
    have hden : 0 < (a - b) * Real.sqrt (qParam m) := mul_pos hdiff hsqrtq
    have hfrac : 0 ≤ kappa / ((a - b) * Real.sqrt (qParam m)) :=
      div_nonneg hk0 (le_of_lt hden)
    have hfactor : 0 ≤ 2 * b * (a + b) := by positivity
    have hinner : 0 ≤ 1 + kappa / ((a - b) * Real.sqrt (qParam m)) := by positivity
    exact mul_nonneg hfactor hinner
  constructor
  · unfold rGapMinus
    have hplus_nonneg : 0 ≤ RxPlus m a b kappa := by
      simpa [rGapPlus] using le_of_lt hplus_pos
    nlinarith [hminus_nonneg, hplus_nonneg]
  · exact le_of_lt hplus_pos

set_option maxHeartbeats 800000 in
-- @node: thm:gap-window
/-- **Positive-gap window.** Under two-block homophily and low-scale: *if* `m` is odd,
then for every `0 ≤ κ < κ_gap` the frontiers are strictly ordered
`r_cut_gap < r_gap^- < r_gap^+`, and for `r ∈ (r_gap^-, r_gap^+)` the spread vertex
is the unique relaxed minimizer of `F` over `E_m^blk` but is not ±1 implementable, so
`Δ_m^±(r,κ) > 0`. The oddness is necessary as a *separate* even-`m` case (NOT nested
under the odd hypothesis, so it does not fire vacuously): for even `m` the whole block
elliptope slice is implementable, hence the claimed positive gap is false. -/
theorem gap_window (m : ℕ) (a b : ℝ)
    (hHom : TwoBlockHomophily m a b) (hLow : LowScaleTwoBlock m a b) :
    (OddCommunitySize m → ∀ kappa : ℝ, 0 ≤ kappa → kappa < kappaGap m a b →
      rCutGap a b kappa < rGapMinus m a b kappa ∧ -- @realizes r_cut(m,a,b,kappa)
      rGapMinus m a b kappa < rGapPlus m a b kappa ∧
      -- @realizes r(bound within the gap window rGapMinus < r < rGapPlus ⊂ [0,∞))
      ∀ r : ℝ, rGapMinus m a b kappa < r → r < rGapPlus m a b kappa →
        (spreadCovariance m ∈ blockElliptope m a b ∧
          ∀ X ∈ blockElliptope m a b, X ≠ spreadCovariance m →
            designObjective m a b r kappa (spreadCovariance m)
              < designObjective m a b r kappa X) ∧
        spreadCovariance m ∉ implementableCovarianceClass m ∧
        0 < implementabilityGap m a b r kappa) ∧
    (Even m → blockElliptope m a b ⊆ implementableCovarianceClass m) := by
  rcases hHom with ⟨hm, hba, hb⟩
  have hHom' : TwoBlockHomophily m a b := ⟨hm, hba, hb⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by nlinarith
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hm1 : (m : ℝ) - 1 ≠ 0 := by nlinarith
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hq0 : 0 ≤ qParam m := le_of_lt hq
  have hsqrtq : 0 < Real.sqrt (qParam m) := Real.sqrt_pos.2 hq
  have hA : 0 < a + b := by linarith
  have hdiff : 0 < a - b := by linarith
  have hb2 : 0 < 2 * b := by positivity
  have hD : 0 < 2 * (m : ℝ) - a - 3 * b := by
    unfold LowScaleTwoBlock at hLow
    linarith
  constructor
  · intro hOdd kappa hk0 hkGap
    have hkA_div :
        kappa * (a + b) / ((a - b) * Real.sqrt (qParam m))
          < 2 * (m : ℝ) - a - 3 * b := by
      rw [div_lt_iff₀ (mul_pos hdiff hsqrtq)]
      have hmul := mul_lt_mul_of_pos_right hkGap hA
      unfold kappaGap at hmul
      field_simp [ne_of_gt hA] at hmul
      nlinarith
    have hRxDiff : 0 < RxPlus m a b kappa - RxMinus m a b kappa := by
      have hinner :
          0 < (2 * (m : ℝ) - a - 3 * b)
            - kappa * (a + b) / ((a - b) * Real.sqrt (qParam m)) := by
        linarith
      have hident :
          RxPlus m a b kappa - RxMinus m a b kappa =
            (a + b) * ((2 * (m : ℝ) - a - 3 * b)
              - kappa * (a + b) / ((a - b) * Real.sqrt (qParam m))) := by
        unfold RxPlus RxMinus
        field_simp [ne_of_gt hdiff, ne_of_gt hsqrtq]
        ring
      rw [hident]
      exact mul_pos hA hinner
    have hRx_lt : RxMinus m a b kappa < RxPlus m a b kappa := sub_pos.mp hRxDiff
    have hRx_minus_lt_gap : RxMinus m a b kappa < rGapMinus m a b kappa := by
      unfold rGapMinus
      nlinarith
    have hgap_lt_plus : rGapMinus m a b kappa < rGapPlus m a b kappa := by
      unfold rGapMinus rGapPlus
      nlinarith
    have hRx_nonneg : 0 ≤ RxMinus m a b kappa := by
      unfold RxMinus
      have hden : 0 < (a - b) * Real.sqrt (qParam m) := mul_pos hdiff hsqrtq
      have hfrac : 0 ≤ kappa / ((a - b) * Real.sqrt (qParam m)) :=
        div_nonneg hk0 (le_of_lt hden)
      positivity
    have hcutBare_le_Rx :
        2 * b * (a + b) * (1 - kappa / (a - b)) ≤ RxMinus m a b kappa := by
      unfold RxMinus
      have hfactor : 0 ≤ 2 * b * (a + b) := by positivity
      have hden : 0 < (a - b) * Real.sqrt (qParam m) := mul_pos hdiff hsqrtq
      have hfrac1 : 0 ≤ kappa / (a - b) := div_nonneg hk0 (le_of_lt hdiff)
      have hfrac2 : 0 ≤ kappa / ((a - b) * Real.sqrt (qParam m)) :=
        div_nonneg hk0 (le_of_lt hden)
      have hinner : 1 - kappa / (a - b)
          ≤ 1 + kappa / ((a - b) * Real.sqrt (qParam m)) := by
        linarith
      exact mul_le_mul_of_nonneg_left hinner hfactor
    have hcut_le_Rx : rCutGap a b kappa ≤ RxMinus m a b kappa := by
      unfold rCutGap
      exact max_le hRx_nonneg hcutBare_le_Rx
    have hcut_lt_gap : rCutGap a b kappa < rGapMinus m a b kappa :=
      lt_of_le_of_lt hcut_le_Rx hRx_minus_lt_gap
    refine ⟨hcut_lt_gap, hgap_lt_plus, ?_⟩
    intro r hrLower hrUpper
    have hrRx : RxMinus m a b kappa < r := lt_trans hRx_minus_lt_gap hrLower
    have h1 : cY b r > cX m a b r / qParam m + kappa / Real.sqrt (qParam m) := by
      unfold cX cY
      have hden : 0 < 2 * b * (a + b) := mul_pos hb2 hA
      have hrdiv :
          1 + kappa / ((a - b) * Real.sqrt (qParam m)) <
            r / (2 * b * (a + b)) := by
        have hrRx' : (1 + kappa / ((a - b) * Real.sqrt (qParam m))) *
            (2 * b * (a + b)) < r := by
          simpa [RxMinus, mul_assoc, mul_left_comm, mul_comm] using hrRx
        rw [lt_div_iff₀ hden]
        exact hrRx'
      have htarget :
          kappa / Real.sqrt (qParam m) <
            (a - b) * (r / (2 * b * (a + b)) - 1) := by
        have hmul := mul_lt_mul_of_pos_left (by linarith : kappa /
            ((a - b) * Real.sqrt (qParam m)) < r / (2 * b * (a + b)) - 1) hdiff
        have hleft :
            (a - b) * (kappa / ((a - b) * Real.sqrt (qParam m)))
              = kappa / Real.sqrt (qParam m) := by
          field_simp [ne_of_gt hdiff, ne_of_gt hsqrtq]
        nlinarith
      have hcx :
          qParam m * (a + b + r / (a + b)) / qParam m =
            a + b + r / (a + b) := by
        field_simp [ne_of_gt hq]
      rw [hcx]
      have hid :
          2 * b + r / (2 * b) - (a + b + r / (a + b)) =
            (a - b) * (r / (2 * b * (a + b)) - 1) := by
        field_simp [ne_of_gt hb2, ne_of_gt hA]
        ring
      nlinarith
    have h2 : cZ m > cX m a b r / qParam m + kappa / Real.sqrt (qParam m) := by
      unfold cX cZ
      have hrdiv :
          r / (a + b) <
            2 * (m : ℝ) - a - b - kappa / Real.sqrt (qParam m) := by
        have hrUpper' : r <
            (2 * (m : ℝ) - a - b - kappa / Real.sqrt (qParam m)) * (a + b) := by
          simpa [RxPlus, rGapPlus, mul_assoc, mul_left_comm, mul_comm] using hrUpper
        rw [div_lt_iff₀ hA]
        exact hrUpper'
      have hcx :
          qParam m * (a + b + r / (a + b)) / qParam m =
            a + b + r / (a + b) := by
        field_simp [ne_of_gt hq]
      rw [hcx]
      linarith
    have hcert := spread_vertex_certificate m (cX m a b r) (cY b r) (cZ m) kappa hq hk0 h1 h2
    exact spread_certificate_relaxed_minimizer_and_gap m a b r kappa hHom' hk0 hOdd hcert
  · intro hEven
    exact blockElliptope_subset_implementable_of_even m a b hEven

end CausalSmith.Experimentation.DesignPm1
