/-
Copyright (c) 2026 CausalSmith contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv

/-!
# Second directional derivative along an affine line

For `f : E → ℝ` and a direction `d : E`, the restriction of `f` to the line
`s ↦ f (q + s • d)` has first and second derivatives expressible as directional
derivatives of `f` at the moving base point `q + t • d`:

* `deriv_line`      : `deriv (fun s => f (q + s • d)) t = fderiv ℝ f (q + t • d) d`
* `deriv_deriv_line`: `deriv (deriv fun s => f (q + s • d)) t
                        = secondDirDeriv f d (q + t • d)`

where `secondDirDeriv f d q = fderiv ℝ (fun x => fderiv ℝ f x d) q d`. Two consequences
make `secondDirDeriv` usable as a *curvature modulus* over a constraint set:

* `continuous_secondDirDeriv` : it is continuous in the base point (so it is bounded on a
  compact set, giving the `BddAbove` needed for a `ciSup`), and
* `convexOn_deriv2_nonneg` : a convex `C²` function of one variable has nonnegative second
  derivative at interior points (so such a modulus is nonnegative).

Mathlib has `convexOn_of_deriv2_nonneg` (sufficiency) but not the converse used here.

The statements are objective-agnostic: callers supply `ContDiff ℝ 2 f` and read off the
directional curvature. This is the substrate behind the `dirModulus` / `EnvelopeLineC2Data`
discharge for the reciprocal-product variance envelope.
-/

open Set Filter Topology

namespace Causalean.Mathlib.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second directional derivative of `f` at `q` along `d`: the directional derivative,
along `d`, of the map `x ↦ fderiv ℝ f x d`. For `C²` functions this is the value
`Hess f q (d, d)` of the Hessian quadratic form. -/
noncomputable def secondDirDeriv (f : E → ℝ) (d : E) (q : E) : ℝ :=
  fderiv ℝ (fun x => fderiv ℝ f x d) q d

/-- The line `s ↦ q + s • d` is differentiable with derivative `d`, as a `HasDerivAt`. -/
lemma hasDerivAt_line (q d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => q + s • d) d t := by
  simpa using ((hasDerivAt_id t).smul_const d).const_add q

/-- **First directional derivative along a line.** -/
lemma deriv_line {f : E → ℝ} (q d : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (q + t • d)) :
    deriv (fun s : ℝ => f (q + s • d)) t = fderiv ℝ f (q + t • d) d := by
  exact
    (hf.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line q d t)).deriv

/-- `x ↦ fderiv ℝ f x d` is `Cⁿ` when `f` is `Cⁿ⁺¹`. It is the composition of the
derivative map with the continuous linear evaluation `L ↦ L d`. -/
lemma contDiff_one_fderiv_apply {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ (n + 1) f) (d : E) :
    ContDiff ℝ n (fun x => fderiv ℝ f x d) := by
  exact (ContinuousLinearMap.apply ℝ ℝ d).contDiff.comp
    (hf.fderiv_right (m := n) (by rfl))

/-- `x ↦ fderiv ℝ f x d` is differentiable when `f` is `C²`. -/
lemma differentiable_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (d : E) :
    Differentiable ℝ (fun x => fderiv ℝ f x d) :=
  (contDiff_one_fderiv_apply hf d).differentiable (by norm_num)

/-- **Second directional derivative along a line.** The second derivative of the line
restriction at parameter `t` is the second directional derivative of `f` at the moving base
point `q + t • d`. Note this is an identity of `deriv` (not `derivWithin`): it holds at every
`t` because the line restriction is differentiable on all of `ℝ`. -/
lemma deriv_deriv_line {f : E → ℝ} (hf : ContDiff ℝ 2 f) (q d : E) (t : ℝ) :
    deriv (deriv fun s : ℝ => f (q + s • d)) t = secondDirDeriv f d (q + t • d) := by
  have hstep : (deriv fun s : ℝ => f (q + s • d)) =
      fun s => fderiv ℝ f (q + s • d) d := by
    funext s
    exact deriv_line q d s ((hf.differentiable two_ne_zero) (q + s • d))
  rw [hstep]
  exact deriv_line q d t ((differentiable_fderiv_apply hf d) (q + t • d))

/-- **The curvature modulus is continuous in the base point.** Hence bounded on any compact
set, which supplies the `BddAbove` hypothesis of `le_ciSup`. -/
@[fun_prop]
lemma continuous_secondDirDeriv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (d : E) :
    Continuous (secondDirDeriv f d) := by
  exact (ContinuousLinearMap.apply ℝ ℝ d).continuous.comp
    ((contDiff_one_fderiv_apply hf d).continuous_fderiv (by norm_num))

/-- **A convex function of one real variable has nonnegative second derivative at interior points
of its domain.** If [`g` is convex on the set `S`](hyp:hconv), [differentiable at every point of
`S`](hyp:hdiff), [`x` lies in the interior of `S`](hyp:hx), and [the derivative of `g` is itself
differentiable at `x`](hyp:hdd), then [the second derivative of `g` at `x` is nonnegative](goal).

The converse direction (`convexOn_of_deriv2_nonneg`) is in Mathlib; this one is not. -/
lemma convexOn_deriv2_nonneg {S : Set ℝ} {g : ℝ → ℝ} {x : ℝ}
    (hconv : ConvexOn ℝ S g) (hdiff : ∀ y ∈ S, DifferentiableAt ℝ g y)
    (hx : x ∈ interior S) (hdd : DifferentiableAt ℝ (deriv g) x) :
    0 ≤ deriv (deriv g) x := by
  have hacc : AccPt x (𝓟 S) := by
    have hacc' : AccPt x (𝓟 (interior S)) := by
      simpa using
        (PerfectSpace.univ_preperfect.open_inter isOpen_interior x ⟨hx, mem_univ x⟩)
    exact hacc'.mono (principal_mono.mpr interior_subset)
  exact hdd.hasDerivAt.hasDerivWithinAt.nonneg_of_monotoneOn hacc
    (hconv.monotoneOn_deriv hdiff)

end Causalean.Mathlib.Analysis
