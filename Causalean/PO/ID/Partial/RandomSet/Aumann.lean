/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The d = 1 Aumann expectation through the support function (Artstein bridge)

`RandomSet/Interval.lean` computes the selection (Aumann) expectation of an
interval random set, `E[F] = [∫L, ∫U]`.  `SupportFunction/` gives the abstract
support-function engine.  This file is the bridge between them in the `d = 1`
case — the link Beresteanu & Molinari (2008) use to turn set-valued moments into
scalar moments of the support process.

The unit "sphere" `S⁰ ⊆ ℝ` is `{+1, −1}`, and for an interval `[a, b]`
(`a ≤ b`) the support function in those two directions is

    s(+1, [a,b]) = b,        s(−1, [a,b]) = −a.

Hence the **Artstein identity** `s(p, E[F]) = E[s(p, F)]` (`p ∈ {±1}`) reduces to
the endpoint identities `s(+1, E[F]) = ∫U = E[s(+1,F)]` and
`s(−1, E[F]) = −∫L = E[s(−1,F)]`, and the Hausdorff keystone of `Hausdorff.lean`
becomes the `d = 1` Hörmander identity `H(A,B) = sup_{p∈{±1}} |s(p,A) − s(p,B)|`.

## Main results

* `supportFn_Icc_one` / `supportFn_Icc_neg_one` — support function of a real
  interval at `+1` / `−1`.
* `hausdorffDist_Icc_eq_supportFn` — the `d = 1` Hörmander identity (A.1).
* `artstein_supportFn_one` / `artstein_supportFn_neg_one` — the `d = 1` Artstein
  identity `s(±1, E[F]) = E[s(±1, F)]`.
-/

import Causalean.PO.ID.Partial.RandomSet.Interval
import Causalean.PO.ID.Partial.RandomSet.Hausdorff
import Causalean.PO.ID.Partial.SupportFunction.Basic

/-! # The One-Dimensional Aumann Support Bridge

This file connects interval-valued Aumann expectations with support functions
in the two unit directions on the real line. The support function of `[a,b]` at
`+1` is `b`, and at `-1` is `-a`; these endpoint formulas turn both the
Hausdorff identity and the Artstein expectation identity into scalar interval
facts.

Main declarations:
* `supportFn_Icc_one` and `supportFn_Icc_neg_one` compute support functions of
  real intervals at the two unit directions.
* `hausdorffDist_Icc_eq_supportFn` rewrites interval Hausdorff distance in the
  `d = 1` support-function form.
* `artstein_supportFn_one` and `artstein_supportFn_neg_one` prove the
  one-dimensional Artstein identities for `selectionExpectation`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Causalean.PartialID.RandomSet

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L U : Ω → ℝ}

/-- The real inner product against `1` is the identity (`⟪1, y⟫ = y`). -/
private lemma inner_one_left (y : ℝ) : ⟪(1 : ℝ), y⟫ = y := by
  simpa using real_inner_smul_right (1 : ℝ) 1 y

/-- The real inner product against `−1` is negation (`⟪-1, y⟫ = -y`). -/
private lemma inner_neg_one_left (y : ℝ) : ⟪(-1 : ℝ), y⟫ = -y := by
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, inner_neg_left, inner_one_left]

/-- Support function of a real interval at `+1`: the upper endpoint. -/
theorem supportFn_Icc_one {a b : ℝ} (hab : a ≤ b) :
    supportFn (Set.Icc a b) (1 : ℝ) = b := by
  rw [supportFn_eq_iSup_image]
  simp only [inner_one_left, Set.image_id']
  exact csSup_Icc hab

/-- Support function of a real interval at `−1`: the negated lower endpoint. -/
theorem supportFn_Icc_neg_one {a b : ℝ} (hab : a ≤ b) :
    supportFn (Set.Icc a b) (-1 : ℝ) = -a := by
  rw [supportFn_eq_iSup_image]
  simp only [inner_neg_one_left]
  rw [Set.image_neg_Icc]
  exact csSup_Icc (by linarith)

/-- **The `d = 1` Hörmander identity (Beresteanu–Molinari eq. (A.1)).**  The
Hausdorff distance between two intervals is the sup over the unit "sphere"
`{+1, −1}` of the support-function differences. -/
theorem hausdorffDist_Icc_eq_supportFn {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    hausdorffDist (Set.Icc a b) (Set.Icc c d)
      = max |supportFn (Set.Icc a b) (-1 : ℝ) - supportFn (Set.Icc c d) (-1 : ℝ)|
            |supportFn (Set.Icc a b) (1 : ℝ) - supportFn (Set.Icc c d) (1 : ℝ)| := by
  rw [hausdorffDist_Icc hab hcd, supportFn_Icc_one hab, supportFn_Icc_one hcd,
    supportFn_Icc_neg_one hab, supportFn_Icc_neg_one hcd,
    show (-a) - (-c) = -(a - c) by ring, abs_neg]

/-- **Artstein identity, `d = 1`, direction `+1`.**  The upper support endpoint of
the Aumann expectation equals the expectation of the upper support endpoint:
`s(+1, E[F]) = E[s(+1, F)]`. -/
theorem artstein_supportFn_one (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    supportFn (selectionExpectation L U μ) (1 : ℝ)
      = ∫ ω, supportFn (randomInterval L U ω) (1 : ℝ) ∂μ := by
  have hfun : (fun ω => supportFn (randomInterval L U ω) (1 : ℝ)) = fun ω => U ω := by
    funext ω; exact supportFn_Icc_one (hLU ω)
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU,
    supportFn_Icc_one (integral_le_integral_of_le hLint hUint hLU), hfun]

/-- **Artstein identity, `d = 1`, direction `−1`.**  The (negated) lower support
endpoint of the Aumann expectation equals the expectation of the lower support
endpoint: `s(−1, E[F]) = E[s(−1, F)]`. -/
theorem artstein_supportFn_neg_one (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    supportFn (selectionExpectation L U μ) (-1 : ℝ)
      = ∫ ω, supportFn (randomInterval L U ω) (-1 : ℝ) ∂μ := by
  have hfun : (fun ω => supportFn (randomInterval L U ω) (-1 : ℝ)) = fun ω => -L ω := by
    funext ω; exact supportFn_Icc_neg_one (hLU ω)
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU,
    supportFn_Icc_neg_one (integral_le_integral_of_le hLint hUint hLU), hfun,
    integral_neg]

end Causalean.PartialID.RandomSet
