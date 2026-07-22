/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Reweighting / sensitivity models — applications of the support-function engine

A *sensitivity analysis* replaces an unidentified nuisance — typically a
reweighting `w` of the observed law that would recover the causal estimand under
unconfoundedness — by an **ambiguity set** `W` of admissible weights, and reports
the range of the linear target `w ↦ ⟪c, w⟫` (the reweighted mean) over `W`.  This
is exactly the support-function picture of `SupportFunction/Interval.lean`, so the
sharp robust bounds are

    robustLower W c = -supportFn W (-c)   ≤   ⟪c, w⟫   ≤   supportFn W c = robustUpper W c,

an interval whose width is `width W c`.  The first half of this file fixes that
vocabulary and records the two structural facts every sensitivity model uses: the
bounds are **monotone in the ambiguity budget** (a larger admissible set `W ⊆ W'`
widens the interval) and they **collapse to a point** when there is no ambiguity
(`W = {w₀}`), recovering the identified value `⟪c, w₀⟫`.

The second half instantiates a concrete budget — the **χ²/L² divergence ball**.
A reweighting constrained to this ball is a **ball around the base weight**
measured in the ambient inner product, together with the normalization that `w`
integrates to one against the base direction `e` (here `‖e‖ = 1`, the unit
"constant"):

    l2Ball e ρ = { w | ⟪e, w⟫ = 1  ∧  ‖w - e‖ ≤ ρ }.

(Reading `e` as the constant function and `c` as the centred outcome `Y` in
`L²(P)`, `⟪e, w⟫ = 1` is `𝔼_P[w] = 1` and `‖w - e‖² = χ²(Q‖P)`; the set is the
signed-reweighting relaxation of the χ²-ball.)

Substituting `v = w - e` turns this into the affine-ball fiber of
`SupportFunction/AffineBall.lean` for the operator `A = innerSL ℝ e` with `b = 0`
and minimum-norm solution `h₀ = 0`, so the support function is computed by the
engine.  Identifying `ker A = (ℝ ∙ e)ᗮ` and the orthogonal split
`‖c‖² = ‖P_{ℝ∙e} c‖² + ‖P_{(ℝ∙e)ᗮ} c‖²` (`‖P_{ℝ∙e} c‖ = |⟪e,c⟫|` under `‖e‖=1`)
collapse the closed form to the classic **mean ± `ρ · SD`** band

    supportFn (l2Ball e ρ) c = ⟪e, c⟫ + ρ · √(‖c‖² − ⟪e, c⟫²),

a width `2ρ · √(‖c‖² − ⟪e, c⟫²)` that collapses to a point exactly when `c` is
collinear with `e` (the outcome is `P`-a.e. constant), i.e. equality in
Cauchy–Schwarz.

## Main definitions

* `robustUpper` / `robustLower` — the sharp upper/lower robust bounds of the
  reweighted mean over an ambiguity set.
* `l2Ball` — the χ²/L² ambiguity set.

## Main results

* `robustLower_le_robustUpper` — the robust interval is nonempty (well-ordered).
* `robustUpper_mono` / `robustLower_antitone` — a larger ambiguity set widens the
  interval (monotonicity in the budget).
* `robustUpper_singleton` / `robustLower_singleton` — no ambiguity ⇒ point
  identification at `⟪c, w₀⟫`.
* `robustInterval_eq_image` — for a compact convex `W` the robust interval is
  exactly the identified set of the reweighted mean.
* `l2Ball_eq_translate` — the χ²-ball is the affine-ball fiber translated by `e`.
* `supportFn_l2Ball_eq` — the `mean + ρ·SD` closed-form worst case.
* `width_l2Ball_eq` — the closed-form width `2ρ·SD`.
* `l2Ball_point_identified_iff` — point identification ⇔ `‖c‖² = ⟪e,c⟫²`
  (outcome collinear with the constant).
-/

import Causalean.PO.ID.Partial.SupportFunction.Calculus
import Causalean.PO.ID.Partial.SupportFunction.Interval
import Causalean.PO.ID.Partial.SupportFunction.AffineBall

/-! # Support-function sensitivity models

This file applies the support-function engine to sensitivity analysis with
reweighted means. It defines robust upper and lower bounds over ambiguity sets,
records their monotonicity and singleton collapse properties, and computes the
closed form for the chi-square/L2-ball relaxation.
-/

open scoped RealInnerProductSpace

namespace Causalean
namespace PartialID

/-! ## Reweighting sensitivity intervals

Upper and lower robust bounds for a reweighted mean over an ambiguity set of
admissible weights, with monotonicity, singleton-collapse, and interval
characterization results reused by concrete sensitivity models. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **upper robust bound** of the reweighted mean `⟪c, ·⟫` over an ambiguity
set `W`: the worst case from above, `supportFn W c`. -/
noncomputable def robustUpper (W : Set E) (c : E) : ℝ := supportFn W c

/-- The **lower robust bound** of the reweighted mean `⟪c, ·⟫` over an ambiguity
set `W`: the worst case from below, `-supportFn W (-c)`. -/
noncomputable def robustLower (W : Set E) (c : E) : ℝ := -supportFn W (-c)

/-- The robust interval `[robustLower, robustUpper]` is well-ordered under the usual boundedness
conditions: its width is
`width W c ≥ 0`. -/
theorem robustLower_le_robustUpper {W : Set E} {c : E} (hne : W.Nonempty)
    (hbdd : BddAbove ((fun x => ⟪c, x⟫) '' W))
    (hbdd' : BddAbove ((fun x => ⟪-c, x⟫) '' W)) :
    robustLower W c ≤ robustUpper W c := by
  have hw := width_nonneg hne hbdd hbdd'
  simp only [robustLower, robustUpper, width] at *
  linarith

/-- Any admissible weight has a reweighted mean no larger than the upper robust bound. -/
theorem le_robustUpper {W : Set E} {c : E} {w : E} (hw : w ∈ W)
    (hbdd : BddAbove ((fun x => ⟪c, x⟫) '' W)) :
    ⟪c, w⟫ ≤ robustUpper W c :=
  le_supportFn hw hbdd

/-- Any admissible weight has a reweighted mean no smaller than the lower robust bound. -/
theorem robustLower_le {W : Set E} {c : E} {w : E} (hw : w ∈ W)
    (hbdd' : BddAbove ((fun x => ⟪-c, x⟫) '' W)) :
    robustLower W c ≤ ⟪c, w⟫ :=
  neg_supportFn_neg_le hw hbdd'

/-- **Monotonicity in the budget (upper).** A larger ambiguity set raises the
upper robust bound. -/
theorem robustUpper_mono {W W' : Set E} {c : E} (hWW' : W ⊆ W') (hne : W.Nonempty)
    (hbdd : BddAbove ((fun x => ⟪c, x⟫) '' W')) :
    robustUpper W c ≤ robustUpper W' c :=
  supportFn_mono hWW' hne hbdd

/-- **Monotonicity in the budget (lower).** A larger ambiguity set lowers the
lower robust bound, so the robust interval widens. -/
theorem robustLower_antitone {W W' : Set E} {c : E} (hWW' : W ⊆ W') (hne : W.Nonempty)
    (hbdd' : BddAbove ((fun x => ⟪-c, x⟫) '' W')) :
    robustLower W' c ≤ robustLower W c := by
  have h := supportFn_mono (d := -c) hWW' hne hbdd'
  simp only [robustLower]
  linarith

/-- **No ambiguity implies point identification (upper).** A singleton ambiguity set
returns the identified value `⟪c, w₀⟫`. -/
@[simp] theorem robustUpper_singleton (c w₀ : E) :
    robustUpper ({w₀} : Set E) c = ⟪c, w₀⟫ := by
  simp only [robustUpper, supportFn_singleton]

/-- With no ambiguity, the lower robust bound equals the single admissible reweighted mean.

**No ambiguity ⇒ point identification (lower).** -/
@[simp] theorem robustLower_singleton (c w₀ : E) :
    robustLower ({w₀} : Set E) c = ⟪c, w₀⟫ := by
  simp only [robustLower, supportFn_singleton, inner_neg_left, neg_neg]

/-- **The robust interval is the identified set.** For a nonempty compact convex
ambiguity set, the range of the reweighted mean is exactly
`[robustLower W c, robustUpper W c]` — the robust bounds are sharp. -/
theorem robustInterval_eq_image {W : Set E} {c : E}
    (hcomp : IsCompact W) (hW : Convex ℝ W) (hne : W.Nonempty) :
    (fun x => ⟪c, x⟫) '' W = Set.Icc (robustLower W c) (robustUpper W c) :=
  linearImage_eq_Icc_of_isCompact hcomp hW hne

/-! ## The χ²/L² divergence-ball model

Alternative distributions are represented by reweightings in an L²-ball around a
normalized baseline, yielding the familiar worst-case mean plus or minus a radius
times a standard deviation, in closed form via the affine-ball engine. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The **χ²/L² ambiguity set**: weights normalized against the unit base
direction `e` and within an L²-ball of radius `ρ` around it. -/
def l2Ball (e : H) (ρ : ℝ) : Set H := {w | ⟪e, w⟫ = 1 ∧ ‖w - e‖ ≤ ρ}

omit [CompleteSpace H] in
/-- Membership in the chi-square or L2 ambiguity set is exactly normalization and the radius
bound. -/
@[simp] theorem mem_l2Ball {e : H} {ρ : ℝ} {w : H} :
    w ∈ l2Ball e ρ ↔ ⟪e, w⟫ = 1 ∧ ‖w - e‖ ≤ ρ := Iff.rfl

omit [CompleteSpace H] in
/-- The free-direction kernel for normalization against the base direction is its orthogonal
complement: `ker (innerSL ℝ e) = (ℝ ∙ e)ᗮ`. -/
theorem opKer_innerSL_eq (e : H) : opKer (innerSL ℝ e) = (ℝ ∙ e)ᗮ := by
  ext x
  rw [opKer, LinearMap.mem_ker, Submodule.mem_orthogonal_singleton_iff_inner_right,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply]

omit [CompleteSpace H] in
/-- **Reduction to the affine-ball engine.** Under `⟪e, e⟫ = 1`, the χ²-ball is
the affine-ball fiber `{A v = 0, ‖v‖ ≤ ρ}` of `A = innerSL ℝ e` translated by `e`
(the substitution `v = w - e`). -/
theorem l2Ball_eq_translate {e : H} (he : ⟪e, e⟫ = 1) (ρ : ℝ) :
    l2Ball e ρ = (fun v => e + v) '' affineBall (innerSL ℝ e) 0 ρ := by
  ext w
  simp only [mem_l2Ball, Set.mem_image, mem_affineBall]
  constructor
  · rintro ⟨hmean, hnorm⟩
    refine ⟨w - e, ⟨?_, ?_⟩, by abel⟩
    · rw [innerSL_apply_apply, inner_sub_right, he, hmean, sub_self]
    · simpa using hnorm
  · rintro ⟨v, ⟨hv0, hvnorm⟩, rfl⟩
    rw [innerSL_apply_apply] at hv0
    refine ⟨?_, ?_⟩
    · rw [inner_add_right, he, hv0, add_zero]
    · simpa using hvnorm

/-- The norm of the free-direction projection equals the standard deviation
`√(‖c‖² − ⟪e,c⟫²)` under `‖e‖ = 1`. -/
theorem norm_orthogonalProjection_opKer_innerSL {e : H} (he : ‖e‖ = 1) (c : H) :
    ‖(Submodule.orthogonalProjection (opKer (innerSL ℝ e)) c : H)‖
      = Real.sqrt (‖c‖ ^ 2 - ⟪e, c⟫ ^ 2) := by
  have hcong : ∀ {K K' : Submodule ℝ H} [K.HasOrthogonalProjection]
      [K'.HasOrthogonalProjection], K = K' →
      (K.orthogonalProjection c : H) = (K'.orthogonalProjection c : H) := by
    intro K K' _ _ h; subst h; rfl
  rw [hcong (opKer_innerSL_eq e)]
  have hdec := Submodule.norm_sq_eq_add_norm_sq_projection c (ℝ ∙ e)
  -- the parallel component has norm |⟪e,c⟫|
  have hpar : ((ℝ ∙ e).orthogonalProjection c : H) = ⟪e, c⟫ • e := by
    rw [← Submodule.starProjection_apply, Submodule.starProjection_singleton ℝ, he]
    simp
  have hpar_sq : ‖((ℝ ∙ e).orthogonalProjection c : H)‖ ^ 2 = ⟪e, c⟫ ^ 2 := by
    rw [hpar, norm_smul, he, mul_one, Real.norm_eq_abs, ← sq_abs ⟪e, c⟫]
  -- the perpendicular component squared
  have hperp_sq : ‖((ℝ ∙ e)ᗮ.orthogonalProjection c : H)‖ ^ 2 = ‖c‖ ^ 2 - ⟪e, c⟫ ^ 2 := by
    have h1 : ‖(c : H)‖ ^ 2
        = ‖((ℝ ∙ e).orthogonalProjection c : H)‖ ^ 2
          + ‖((ℝ ∙ e)ᗮ.orthogonalProjection c : H)‖ ^ 2 := hdec
    rw [hpar_sq] at h1
    linarith
  rw [← Real.sqrt_sq (norm_nonneg _), hperp_sq]

/-- **Closed-form worst case (mean plus `ρ·SD`).** The largest reweighted value of
`⟪c, ·⟫` over the χ²-ball is `⟪e, c⟫ + ρ · √(‖c‖² − ⟪e,c⟫²)`. -/
theorem supportFn_l2Ball_eq {e : H} (he : ‖e‖ = 1) (c : H) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    supportFn (l2Ball e ρ) c = ⟪e, c⟫ + ρ * Real.sqrt (‖c‖ ^ 2 - ⟪e, c⟫ ^ 2) := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_mul_norm, he, mul_one]
  set A : H →L[ℝ] ℝ := innerSL ℝ e with hA
  have hsol : A 0 = 0 := map_zero A
  have hperp : (0 : H) ∈ (opKer A)ᗮ := Submodule.zero_mem _
  have hfit : ‖(0 : H)‖ ≤ ρ := by simpa using hρ
  have hne : (affineBall A 0 ρ).Nonempty := ⟨0, hsol, hfit⟩
  have hbdd : BddAbove ((fun x => ⟪c, x⟫) '' affineBall A 0 ρ) := by
    refine ⟨‖c‖ * ρ, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    calc ⟪c, h⟫ ≤ ‖c‖ * ‖h‖ := real_inner_le_norm c h
      _ ≤ ‖c‖ * ρ := mul_le_mul_of_nonneg_left hh.2 (norm_nonneg _)
  rw [l2Ball_eq_translate hee, supportFn_translate e hne hbdd,
    supportFn_affineBall_eq A hsol hperp hfit, norm_orthogonalProjection_opKer_innerSL he]
  rw [inner_zero_right, norm_zero, zero_add]
  rw [show (ρ : ℝ) ^ 2 - (0 : ℝ) ^ 2 = ρ ^ 2 by ring, Real.sqrt_sq hρ, real_inner_comm c e]

/-- **Closed-form width** of the χ²-ball identified interval: twice the radius times the standard
deviation. -/
theorem width_l2Ball_eq {e : H} (he : ‖e‖ = 1) (c : H) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    width (l2Ball e ρ) c = 2 * ρ * Real.sqrt (‖c‖ ^ 2 - ⟪e, c⟫ ^ 2) := by
  unfold width
  rw [supportFn_l2Ball_eq he c hρ, supportFn_l2Ball_eq he (-c) hρ]
  rw [inner_neg_right, norm_neg]
  rw [show (-⟪e, c⟫) ^ 2 = ⟪e, c⟫ ^ 2 by ring]
  ring

/-- **Point identification.** With a positive budget `ρ > 0`, the χ²-ball
identified interval collapses to a point iff `‖c‖² = ⟪e, c⟫²`, i.e. the target `c`
is collinear with the base direction `e` (equality in Cauchy–Schwarz: the outcome
is constant). -/
theorem l2Ball_point_identified_iff {e : H} (he : ‖e‖ = 1) (c : H) {ρ : ℝ}
    (hρ : 0 < ρ) :
    width (l2Ball e ρ) c = 0 ↔ ‖c‖ ^ 2 = ⟪e, c⟫ ^ 2 := by
  rw [width_l2Ball_eq he c (le_of_lt hρ)]
  -- Cauchy–Schwarz: ‖c‖² − ⟪e,c⟫² ≥ 0 under ‖e‖ = 1
  have hge : (0 : ℝ) ≤ ‖c‖ ^ 2 - ⟪e, c⟫ ^ 2 := by
    have h := abs_real_inner_le_norm e c
    rw [he, one_mul] at h
    have : ⟪e, c⟫ ^ 2 ≤ ‖c‖ ^ 2 := by
      rw [← sq_abs ⟪e, c⟫]; nlinarith [abs_nonneg ⟪e, c⟫, norm_nonneg c, h]
    linarith
  rw [mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · norm_num at h
    · exact absurd h (ne_of_gt hρ)
    · have hle : ‖c‖ ^ 2 - ⟪e, c⟫ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h
      linarith
  · intro h
    right
    rw [show ‖c‖ ^ 2 - ⟪e, c⟫ ^ 2 = 0 by linarith, Real.sqrt_zero]

end PartialID
end Causalean
