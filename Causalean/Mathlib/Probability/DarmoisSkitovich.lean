/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# The Darmois–Skitovich theorem (finite-variance case): Bernstein's theorem

This file develops the finite-variance Darmois–Skitovich theorem, starting from
its simplest non-degenerate instance, **Bernstein's theorem**: if two independent
real random variables `X` and `Y` (with finite second moments) are such that their
sum `X + Y` and difference `X − Y` are independent, then `X` and `Y` are each
Gaussian.  This is the analytic engine behind the identifiability of linear
non-Gaussian causal models (LiNGAM, Shimizu et al. 2006): non-Gaussian
disturbances are exactly what break the rotational symmetry that Bernstein's
theorem characterizes.

The proof works at the level of characteristic functions `f = charFun (P.map X)`
and `g = charFun (P.map Y)`:

1. `bernstein_charFun_funeq` — the **functional equation** obtained by computing
   the joint characteristic function of `(X, Y)` two ways (directly, and through
   the independent pair `(X + Y, X − Y)`):
   `f (u+v) · g (u−v) = f u · g u · f v · g (−v)`.
2. `charFun_eventually_ne_zero` — `f` and `g` are nonzero on a neighbourhood of
   `0`, so the logarithmic derivatives `f'/f`, `g'/g` are defined there.
3. `gaussianForm_of_funeq` / `bernstein_charFun_gaussian_nhds_zero` — the
   **analytic core**: working with the logarithmic derivative `h_f = f'/f` (no
   `Complex.log`, hence no branch cuts), differentiate the functional equation
   once in each of `u` and `v` to get `h_f'(u+v) = h_g'(u−v)`; as `(u+v, u−v)`
   ranges over a neighbourhood of `0`, both are one constant, so `h_f` is affine
   and `f` is a Gaussian characteristic function near `0`.
4. A **doubling bootstrap** (the instance `f (2t) = f t ^ 2 · g t · g (−t)` of the
   functional equation) propagates the Gaussian form from a neighbourhood of `0`
   to all of `ℝ`; `Measure.ext_of_charFun` then identifies the law as Gaussian.

The proof is organized into those four steps: a characteristic-function
functional equation, neighbourhood nonvanishing, the local Gaussian-form
argument, and the doubling bootstrap to a global Gaussian law. The supporting
infrastructure comes from Mathlib's `charFun`, differentiability, independent
sum, measure-extensionality, and real Gaussian characteristic-function APIs.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory ProbabilityTheory Complex
open scoped Real

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ}

/-- **Functional equation for Bernstein's theorem.**  If `X` and `Y` are
independent and the pair `(X + Y, X − Y)` is independent, then the characteristic
functions `f = charFun (P.map X)` and `g = charFun (P.map Y)` satisfy
`f (u+v) · g (u−v) = f u · g u · f v · g (−v)` for all `u, v`.

This is obtained by evaluating the joint characteristic function of `(X, Y)` at
`(u+v, u−v)` in two ways: directly (using `X ⟂ Y`) it factors as `f (u+v)·g (u−v)`,
and through the independent pair `(X+Y, X−Y)` it factors as `f u·g u · f v·g (−v)`. -/
lemma bernstein_charFun_funeq
    (mX : Measurable X) (mY : Measurable Y)
    (hXY : IndepFun X Y P) (hUV : IndepFun (X + Y) (X - Y) P) (u v : ℝ) :
    charFun (P.map X) (u + v) * charFun (P.map Y) (u - v)
      = charFun (P.map X) u * charFun (P.map Y) u
        * (charFun (P.map X) v * charFun (P.map Y) (-v)) := by
  have hscale : ∀ (Z : Ω → ℝ), Measurable Z → ∀ a t : ℝ,
      charFun (P.map (fun ω => a * Z ω)) t = charFun (P.map Z) (a * t) := by
    intro Z mZ a t
    rw [← charFun_map_mul (μ := P.map Z) a t]
    rw [Measure.map_map]
    · rfl
    · exact measurable_const_mul a
    · exact mZ
  have hlin : ∀ {Z W : Ω → ℝ}, Measurable Z → Measurable W → IndepFun Z W P →
      ∀ a b : ℝ,
        charFun (P.map (fun ω => a * Z ω + b * W ω)) (1 : ℝ)
          = charFun (P.map Z) a * charFun (P.map W) b := by
    intro Z W mZ mW hZW a b
    have hind : IndepFun (fun ω => a * Z ω) (fun ω => b * W ω) P :=
      hZW.comp (measurable_const_mul a) (measurable_const_mul b)
    have h := hind.charFun_map_fun_add_eq_mul
      ((mZ.const_mul a).aemeasurable) ((mW.const_mul b).aemeasurable)
    have h1 := congrFun h (1 : ℝ)
    rw [Pi.mul_apply] at h1
    rw [hscale Z mZ a 1, hscale W mW b 1] at h1
    simpa using h1
  have mAdd : Measurable (X + Y) := mX.add mY
  have mSub : Measurable (X - Y) := mX.sub mY
  have hAdd : ∀ t : ℝ,
      charFun (P.map (X + Y)) t = charFun (P.map X) t * charFun (P.map Y) t := by
    intro t
    calc
      charFun (P.map (X + Y)) t
          = charFun (P.map (fun ω => t * (X + Y) ω)) (1 : ℝ) := by
              rw [hscale (X + Y) mAdd t 1]
              simp
      _ = charFun (P.map (fun ω => t * X ω + t * Y ω)) (1 : ℝ) := by
              congr 2
              funext ω
              simp [Pi.add_apply]
              ring
      _ = charFun (P.map X) t * charFun (P.map Y) t := hlin mX mY hXY t t
  have hSub : ∀ t : ℝ,
      charFun (P.map (X - Y)) t = charFun (P.map X) t * charFun (P.map Y) (-t) := by
    intro t
    calc
      charFun (P.map (X - Y)) t
          = charFun (P.map (fun ω => t * (X - Y) ω)) (1 : ℝ) := by
              rw [hscale (X - Y) mSub t 1]
              simp
      _ = charFun (P.map (fun ω => t * X ω + (-t) * Y ω)) (1 : ℝ) := by
              congr 2
              funext ω
              simp [Pi.sub_apply]
              ring
      _ = charFun (P.map X) t * charFun (P.map Y) (-t) := hlin mX mY hXY t (-t)
  calc
    charFun (P.map X) (u + v) * charFun (P.map Y) (u - v)
        = charFun (P.map (fun ω => (u + v) * X ω + (u - v) * Y ω)) (1 : ℝ) := by
            exact (hlin mX mY hXY (u + v) (u - v)).symm
    _ = charFun (P.map (fun ω => u * (X + Y) ω + v * (X - Y) ω)) (1 : ℝ) := by
            congr 2
            funext ω
            simp [Pi.add_apply, Pi.sub_apply]
            ring
    _ = charFun (P.map (X + Y)) u * charFun (P.map (X - Y)) v :=
            hlin mAdd mSub hUV u v
    _ = charFun (P.map X) u * charFun (P.map Y) u
          * (charFun (P.map X) v * charFun (P.map Y) (-v)) := by
            rw [hAdd u, hSub v]

/-- The characteristic function of a probability measure on `ℝ` is nonzero on a
neighbourhood of `0`: it is continuous and equals `1` at `0`.  This is what makes
the logarithmic derivative `(charFun μ)' / charFun μ` well defined near `0`. -/
lemma charFun_eventually_ne_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᶠ t in nhds (0 : ℝ), charFun μ t ≠ 0 := by
  exact (continuous_charFun (μ := μ)).continuousAt.eventually_ne
    (by simp : charFun μ 0 ≠ 0)

/-- `charFun` of a pushforward with a finite second moment is `C²`.  This is a
specialisation of `contDiff_charFun` (the characteristic function is `Cⁿ` whenever
the `n`-th moment is finite), transferring `MemLp Z 2 P` to `MemLp id 2 (P.map Z)`
along the pushforward map. -/
lemma charFun_contDiff_two {Z : Ω → ℝ} (mZ : Measurable Z) (hZ : MemLp Z 2 P) :
    ContDiff ℝ 2 (charFun (P.map Z)) := by
  refine contDiff_charFun (μ := P.map Z) ?_
  exact (memLp_map_measure_iff aestronglyMeasurable_id mZ.aemeasurable).2
    (by simpa [Function.comp_def] using hZ)

/-- **Pure analytic core: the Bernstein functional equation forces a Gaussian form.**
Let `f, g : ℝ → ℂ` be `C²` with `f 0 = g 0 = 1` and satisfying the Bernstein
functional equation `f (u+v) · g (u−v) = f u · g u · (f v · g (−v))`.  Then there
is a single constant `c` such that, on a neighbourhood of `0`,
`f t = exp (f'(0)·t + c·t²/2)` and `g t = exp (g'(0)·t + c·t²/2)` — both with the
*same* `c`.

This is the genuinely hard analytic step and is pure complex analysis (no
probability).  Proof via logarithmic derivatives, which avoids `Complex.log` and
its branch cuts: `f, g` are nonzero near `0` (continuous, value `1` at `0`), so
`h_f := f'/f` and `h_g := g'/g` are `C¹` near `0`.  Differentiating the functional
equation in `u` and dividing by it gives `h_f(u+v) + h_g(u−v) = h_f(u) + h_g(u)`;
differentiating that in `v` gives `h_f'(u+v) = h_g'(u−v)`.  Since `(u+v, u−v)`
ranges over a neighbourhood of `0` in `ℝ²`, both `h_f'` and `h_g'` equal one
constant `c`, hence `h_f(t) = f'(0) + c·t`; the linear ODE `f' = h_f · f` with
`f 0 = 1` has the claimed exponential as unique solution (verify by differentiating
`f · exp(−(f'(0)·t + c·t²/2))`, which is constant `1`). -/
lemma gaussianForm_of_funeq {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hfe : ∀ u v : ℝ, f (u + v) * g (u - v) = f u * g u * (f v * g (-v))) :
    ∃ c : ℂ,
      (∀ᶠ t in nhds (0 : ℝ), f t = Complex.exp (deriv f 0 * t + c * t ^ 2 / 2)) ∧
      (∀ᶠ t in nhds (0 : ℝ), g t = Complex.exp (deriv g 0 * t + c * t ^ 2 / 2)) := by
  let lf : ℝ → ℂ := fun t => deriv f t / f t
  let lg : ℝ → ℂ := fun t => deriv g t / g t
  have hfD : Differentiable ℝ f :=
    (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
  have hgD : Differentiable ℝ g :=
    (hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
  have hdfD : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have hdgD : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hf_ne : ∀ᶠ t in nhds (0 : ℝ), f t ≠ 0 :=
    hf.continuous.continuousAt.eventually_ne (by simp [hf0] : f 0 ≠ 0)
  have hg_ne : ∀ᶠ t in nhds (0 : ℝ), g t ≠ 0 :=
    hg.continuous.continuousAt.eventually_ne (by simp [hg0] : g 0 ≠ 0)
  have hlf0 : lf 0 = deriv f 0 := by simp [lf, hf0]
  have hlg0 : lg 0 = deriv g 0 := by simp [lg, hg0]
  have hlfDiffAt : ∀ {x : ℝ}, f x ≠ 0 → DifferentiableAt ℝ lf x := by
    intro x hx
    exact (hdfD x).div (hfD x) hx
  have hlgDiffAt : ∀ {x : ℝ}, g x ≠ 0 → DifferentiableAt ℝ lg x := by
    intro x hx
    exact (hdgD x).div (hgD x) hx
  have hD1 : ∀ u v : ℝ,
      deriv f (u + v) * g (u - v) + f (u + v) * deriv g (u - v) =
        (deriv f u * g u + f u * deriv g u) * (f v * g (-v)) := by
    intro u v
    have hleftF : (fun x : ℝ => f (x + v) * g (x - v)) =
        (fun x : ℝ => f x * g x * (f v * g (-v))) := by
      funext x
      exact hfe x v
    have hfp : HasDerivAt (fun x : ℝ => f (x + v)) (deriv f (u + v)) u := by
      simpa using (hfD (u + v)).hasDerivAt.comp_add_const u v
    have hgm : HasDerivAt (fun x : ℝ => g (x - v)) (deriv g (u - v)) u := by
      simpa using (hgD (u - v)).hasDerivAt.comp_sub_const u v
    have hleft : HasDerivAt (fun x : ℝ => f (x + v) * g (x - v))
        (deriv f (u + v) * g (u - v) + f (u + v) * deriv g (u - v)) u := by
      convert hfp.mul hgm using 1
    have hfu : HasDerivAt (fun x : ℝ => f x) (deriv f u) u := (hfD u).hasDerivAt
    have hgu : HasDerivAt (fun x : ℝ => g x) (deriv g u) u := (hgD u).hasDerivAt
    have hright : HasDerivAt (fun x : ℝ => f x * g x * (f v * g (-v)))
        ((deriv f u * g u + f u * deriv g u) * (f v * g (-v))) u := by
      convert (hfu.mul hgu).mul_const (f v * g (-v)) using 1
    have hright' : HasDerivAt (fun x : ℝ => f (x + v) * g (x - v))
        ((deriv f u * g u + f u * deriv g u) * (f v * g (-v))) u := by
      simpa [hleftF] using hright
    exact hleft.unique hright'
  have hE1_at : ∀ u v : ℝ,
      f (u + v) ≠ 0 → g (u - v) ≠ 0 → f u ≠ 0 → g u ≠ 0 →
      f v ≠ 0 → g (-v) ≠ 0 →
        lf (u + v) + lg (u - v) = lf u + lg u := by
    intro u v hfp hgm hfu hgu hfv hgnv
    have hD1' := hD1 u v
    have hFE := hfe u v
    dsimp [lf, lg]
    calc
      deriv f (u + v) / f (u + v) + deriv g (u - v) / g (u - v)
          = (deriv f (u + v) * g (u - v) + f (u + v) * deriv g (u - v)) /
              (f (u + v) * g (u - v)) := by
              field_simp [hfp, hgm]
      _ = ((deriv f u * g u + f u * deriv g u) * f v * g (-v)) /
              (f u * g u * f v * g (-v)) := by
              rw [hD1', hFE]
              ring
      _ = (deriv f u * g u + f u * deriv g u) / (f u * g u) := by
              field_simp [hfu, hgu, hfv, hgnv]
      _ = deriv f u / f u + deriv g u / g u := by
              field_simp [hfu, hgu]
  have hsecondLogDeriv :
      ∃ c : ℂ,
        (∀ᶠ t in nhds (0 : ℝ), deriv lf t = c) ∧
        (∀ᶠ t in nhds (0 : ℝ), deriv lg t = c) := by
    let c : ℂ := deriv lg 0
    have hpair_ne : ∀ᶠ p : ℝ × ℝ in nhds ((0, 0) : ℝ × ℝ),
        f (p.1 + p.2) ≠ 0 ∧ g (p.1 - p.2) ≠ 0 ∧
        f p.1 ≠ 0 ∧ g p.1 ≠ 0 ∧ f p.2 ≠ 0 ∧ g (-p.2) ≠ 0 := by
      have h_add : Filter.Tendsto (fun p : ℝ × ℝ => p.1 + p.2)
          (nhds ((0, 0) : ℝ × ℝ)) (nhds (0 : ℝ)) := by
        simpa [ContinuousAt] using ((continuous_fst.add continuous_snd).continuousAt
          (x := ((0, 0) : ℝ × ℝ)))
      have h_sub : Filter.Tendsto (fun p : ℝ × ℝ => p.1 - p.2)
          (nhds ((0, 0) : ℝ × ℝ)) (nhds (0 : ℝ)) := by
        simpa [ContinuousAt] using ((continuous_fst.sub continuous_snd).continuousAt
          (x := ((0, 0) : ℝ × ℝ)))
      have h_fst : Filter.Tendsto (fun p : ℝ × ℝ => p.1)
          (nhds ((0, 0) : ℝ × ℝ)) (nhds (0 : ℝ)) := by
        simpa [ContinuousAt] using (continuous_fst.continuousAt (x := ((0, 0) : ℝ × ℝ)))
      have h_snd : Filter.Tendsto (fun p : ℝ × ℝ => p.2)
          (nhds ((0, 0) : ℝ × ℝ)) (nhds (0 : ℝ)) := by
        simpa [ContinuousAt] using (continuous_snd.continuousAt (x := ((0, 0) : ℝ × ℝ)))
      have h_neg_snd : Filter.Tendsto (fun p : ℝ × ℝ => -p.2)
          (nhds ((0, 0) : ℝ × ℝ)) (nhds (0 : ℝ)) := by
        simpa [ContinuousAt] using (continuous_snd.neg.continuousAt (x := ((0, 0) : ℝ × ℝ)))
      filter_upwards [h_add.eventually hf_ne, h_sub.eventually hg_ne,
        h_fst.eventually hf_ne, h_fst.eventually hg_ne,
        h_snd.eventually hf_ne, h_neg_snd.eventually hg_ne] with p h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    have hderiv_pair : ∀ᶠ p : ℝ × ℝ in nhds ((0, 0) : ℝ × ℝ),
        deriv lf (p.1 + p.2) = deriv lg (p.1 - p.2) := by
      filter_upwards [hpair_ne] with p hp
      rcases hp with ⟨hfp, hgm, hfu, hgu, hfv, hgnv⟩
      let u : ℝ := p.1
      let v : ℝ := p.2
      have hEq : (fun w : ℝ => lf (u + w) + lg (u - w))
          =ᶠ[nhds v] fun _ : ℝ => lf u + lg u := by
        have hfu' : f u ≠ 0 := by simpa [u] using hfu
        have hgu' : g u ≠ 0 := by simpa [u] using hgu
        have h1 : ∀ᶠ w in nhds v, f (u + w) ≠ 0 :=
            ((hf.continuous.continuousAt.comp
              ((continuous_const.add continuous_id).continuousAt))).eventually_ne
            (by simpa [u, v] using hfp)
        have h2 : ∀ᶠ w in nhds v, g (u - w) ≠ 0 :=
            ((hg.continuous.continuousAt.comp
              ((continuous_const.sub continuous_id).continuousAt))).eventually_ne
            (by simpa [u, v] using hgm)
        have h3 : ∀ᶠ w in nhds v, f w ≠ 0 :=
          hf.continuous.continuousAt.eventually_ne (by simpa [v] using hfv)
        have h4 : ∀ᶠ w in nhds v, g (-w) ≠ 0 :=
          (hg.continuous.continuousAt.comp continuous_neg.continuousAt).eventually_ne
            (by simpa [v] using hgnv)
        filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4
        exact hE1_at u w hw1 hw2 hfu' hgu' hw3 hw4
      have hlfp : HasDerivAt (fun w : ℝ => lf (u + w)) (deriv lf (u + v)) v := by
        simpa using (hlfDiffAt (by simpa [u, v] using hfp)).hasDerivAt.comp_const_add u v
      have hlgm : HasDerivAt (fun w : ℝ => lg (u - w)) (-(deriv lg (u - v))) v := by
        simpa using (hlgDiffAt (by simpa [u, v] using hgm)).hasDerivAt.comp_const_sub u v
      have hleft : HasDerivAt (fun w : ℝ => lf (u + w) + lg (u - w))
          (deriv lf (u + v) - deriv lg (u - v)) v := by
        simpa [sub_eq_add_neg] using hlfp.add hlgm
      have hconst : HasDerivAt (fun _ : ℝ => lf u + lg u)
          (deriv lf (u + v) - deriv lg (u - v)) v :=
        hleft.congr_of_eventuallyEq hEq.symm
      have hzero : HasDerivAt (fun _ : ℝ => lf u + lg u) 0 v := hasDerivAt_const v _
      have hsub : deriv lf (u + v) - deriv lg (u - v) = 0 := hconst.unique hzero
      have hres : deriv lf (u + v) = deriv lg (u - v) := sub_eq_zero.mp hsub
      simpa [u, v] using hres
    have hlfDeriv : ∀ᶠ t in nhds (0 : ℝ), deriv lf t = c := by
      have hline : Filter.Tendsto (fun t : ℝ => (t / 2, t / 2))
          (nhds (0 : ℝ)) (nhds ((0, 0) : ℝ × ℝ)) := by
        simpa [ContinuousAt] using ((continuous_id.div_const (2 : ℝ)).prodMk
          (continuous_id.div_const (2 : ℝ))).continuousAt (x := (0 : ℝ))
      filter_upwards [hline.eventually hderiv_pair] with t ht
      have ht' : deriv lf (t / 2 + t / 2) = deriv lg (t / 2 - t / 2) := ht
      have hsum : t / 2 + t / 2 = t := by ring
      have hsub : t / 2 - t / 2 = 0 := by ring
      simpa [c, hsum, hsub] using ht'
    have hlgDeriv : ∀ᶠ t in nhds (0 : ℝ), deriv lg t = c := by
      have hlf0c : deriv lf 0 = c := hlfDeriv.self_of_nhds
      have hline : Filter.Tendsto (fun t : ℝ => (t / 2, -(t / 2)))
          (nhds (0 : ℝ)) (nhds ((0, 0) : ℝ × ℝ)) := by
        simpa [ContinuousAt] using ((continuous_id.div_const (2 : ℝ)).prodMk
          ((continuous_id.div_const (2 : ℝ)).neg)).continuousAt (x := (0 : ℝ))
      filter_upwards [hline.eventually hderiv_pair] with t ht
      have ht' : deriv lf (t / 2 + -(t / 2)) = deriv lg (t / 2 - -(t / 2)) := ht
      have hsum : t / 2 + -(t / 2) = 0 := by ring
      have hsub : t / 2 - -(t / 2) = t := by ring
      have ht0 : deriv lf 0 = deriv lg t := by simpa [hsum, hsub] using ht'
      exact ht0.symm.trans hlf0c
    exact ⟨c, hlfDeriv, hlgDeriv⟩
  obtain ⟨c, hlfDeriv, hlgDeriv⟩ := hsecondLogDeriv
  have hlogAffine :
      (∀ᶠ t in nhds (0 : ℝ), lf t = deriv f 0 + c * t) ∧
      (∀ᶠ t in nhds (0 : ℝ), lg t = deriv g 0 + c * t) := by
    have hAffDeriv : ∀ a x : ℂ, ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => a + x * s) x t := by
      intro a x t
      convert (hasDerivAt_const t a).add ((hasDerivAt_id t).ofReal_comp.const_mul x) using 1
      simp
    constructor
    · rcases Metric.eventually_nhds_iff_ball.mp (hlfDeriv.and hf_ne) with ⟨r, hr, hball⟩
      have hlfOn : DifferentiableOn ℝ lf (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact (hlfDiffAt (hball x hx).2).differentiableWithinAt
      have hAffOn : DifferentiableOn ℝ (fun t : ℝ => deriv f 0 + c * t)
          (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact ((hAffDeriv (deriv f 0) c x).differentiableAt).differentiableWithinAt
      have hEqOn : Set.EqOn lf (fun t : ℝ => deriv f 0 + c * t)
          (Metric.ball (0 : ℝ) r) := by
        refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℝ) r).isPreconnected
          hlfOn hAffOn ?_ (Metric.mem_ball_self hr) ?_
        · intro x hx
          have hxder : deriv lf x = c := (hball x hx).1
          have hmodel : deriv (fun t : ℝ => deriv f 0 + c * t) x = c :=
            (hAffDeriv (deriv f 0) c x).deriv
          rw [hxder, hmodel]
        · simp [hlf0]
      refine Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, fun t ht => ?_⟩
      exact hEqOn ht
    · rcases Metric.eventually_nhds_iff_ball.mp (hlgDeriv.and hg_ne) with ⟨r, hr, hball⟩
      have hlgOn : DifferentiableOn ℝ lg (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact (hlgDiffAt (hball x hx).2).differentiableWithinAt
      have hAffOn : DifferentiableOn ℝ (fun t : ℝ => deriv g 0 + c * t)
          (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact ((hAffDeriv (deriv g 0) c x).differentiableAt).differentiableWithinAt
      have hEqOn : Set.EqOn lg (fun t : ℝ => deriv g 0 + c * t)
          (Metric.ball (0 : ℝ) r) := by
        refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℝ) r).isPreconnected
          hlgOn hAffOn ?_ (Metric.mem_ball_self hr) ?_
        · intro x hx
          have hxder : deriv lg x = c := (hball x hx).1
          have hmodel : deriv (fun t : ℝ => deriv g 0 + c * t) x = c :=
            (hAffDeriv (deriv g 0) c x).deriv
          rw [hxder, hmodel]
        · simp [hlg0]
      refine Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, fun t ht => ?_⟩
      exact hEqOn ht
  have hsolve :
      (∀ᶠ t in nhds (0 : ℝ), f t = Complex.exp (deriv f 0 * t + c * t ^ 2 / 2)) ∧
      (∀ᶠ t in nhds (0 : ℝ), g t = Complex.exp (deriv g 0 * t + c * t ^ 2 / 2)) := by
    have hExpDeriv : ∀ a : ℂ, ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => Complex.exp (a * s + c * s ^ 2 / 2))
          ((a + c * t) * Complex.exp (a * t + c * t ^ 2 / 2)) t := by
      intro a t
      have hinner : HasDerivAt (fun s : ℝ => a * s + c * s ^ 2 / 2) (a + c * t) t := by
        have hlin : HasDerivAt (fun s : ℝ => a * s) a t := by
          convert (hasDerivAt_id t).ofReal_comp.const_mul a using 1
          simp
        have hsqrR : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_id t).pow 2
        have hquad : HasDerivAt (fun s : ℝ => c * s ^ 2 / 2) (c * (2 * t) / 2) t := by
          convert (hsqrR.ofReal_comp.const_mul c).div_const (2 : ℂ) using 1
          · funext s
            norm_num
          · norm_num
        convert hlin.add hquad using 1
        ring
      simpa [mul_comm, mul_left_comm, mul_assoc] using hinner.cexp
    constructor
    · let Ef : ℝ → ℂ := fun t => Complex.exp (deriv f 0 * t + c * t ^ 2 / 2)
      let φ : ℝ → ℂ := fun t => f t / Ef t
      rcases Metric.eventually_nhds_iff_ball.mp (hlogAffine.1.and hf_ne) with ⟨r, hr, hball⟩
      have hφZeroDeriv : ∀ x ∈ Metric.ball (0 : ℝ) r, HasDerivAt φ 0 x := by
        intro x hx
        have hlogx : lf x = deriv f 0 + c * x := (hball x hx).1
        have hfnex : f x ≠ 0 := (hball x hx).2
        have hdfx : deriv f x = (deriv f 0 + c * x) * f x := by
          have hlogx' : deriv f x / f x = deriv f 0 + c * x := by
            simpa [lf] using hlogx
          field_simp [hfnex] at hlogx'
          simpa [mul_comm] using hlogx'
        have hEfDeriv : HasDerivAt Ef
            ((deriv f 0 + c * x) * Ef x) x := by
          simpa [Ef] using hExpDeriv (deriv f 0) x
        have hquot : HasDerivAt φ
            ((deriv f x * Ef x - f x * ((deriv f 0 + c * x) * Ef x)) / Ef x ^ 2) x := by
          simpa [φ] using (hfD x).hasDerivAt.div hEfDeriv (Complex.exp_ne_zero _)
        convert hquot using 1
        rw [hdfx]
        ring
      have hφOn : DifferentiableOn ℝ φ (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact ((hφZeroDeriv x hx).differentiableAt).differentiableWithinAt
      have hφDeriv : Set.EqOn (deriv φ) 0 (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact (hφZeroDeriv x hx).deriv
      have hφConst : ∀ x ∈ Metric.ball (0 : ℝ) r, φ x = φ 0 := by
        intro x hx
        exact Metric.isOpen_ball.is_const_of_deriv_eq_zero
          (convex_ball (0 : ℝ) r).isPreconnected hφOn hφDeriv hx (Metric.mem_ball_self hr)
      refine Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, fun t ht => ?_⟩
      have hφt : φ t = 1 := by
        have h0 : φ 0 = 1 := by simp [φ, Ef, hf0]
        exact (hφConst t ht).trans h0
      have hEt : Ef t ≠ 0 := Complex.exp_ne_zero _
      have hfEt : f t / Ef t = 1 := by simpa [φ] using hφt
      field_simp [hEt] at hfEt
      simpa [Ef] using hfEt
    · let Eg : ℝ → ℂ := fun t => Complex.exp (deriv g 0 * t + c * t ^ 2 / 2)
      let φ : ℝ → ℂ := fun t => g t / Eg t
      rcases Metric.eventually_nhds_iff_ball.mp (hlogAffine.2.and hg_ne) with ⟨r, hr, hball⟩
      have hφZeroDeriv : ∀ x ∈ Metric.ball (0 : ℝ) r, HasDerivAt φ 0 x := by
        intro x hx
        have hlogx : lg x = deriv g 0 + c * x := (hball x hx).1
        have hgnex : g x ≠ 0 := (hball x hx).2
        have hdgx : deriv g x = (deriv g 0 + c * x) * g x := by
          have hlogx' : deriv g x / g x = deriv g 0 + c * x := by
            simpa [lg] using hlogx
          field_simp [hgnex] at hlogx'
          simpa [mul_comm] using hlogx'
        have hEgDeriv : HasDerivAt Eg
            ((deriv g 0 + c * x) * Eg x) x := by
          simpa [Eg] using hExpDeriv (deriv g 0) x
        have hquot : HasDerivAt φ
            ((deriv g x * Eg x - g x * ((deriv g 0 + c * x) * Eg x)) / Eg x ^ 2) x := by
          simpa [φ] using (hgD x).hasDerivAt.div hEgDeriv (Complex.exp_ne_zero _)
        convert hquot using 1
        rw [hdgx]
        ring
      have hφOn : DifferentiableOn ℝ φ (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact ((hφZeroDeriv x hx).differentiableAt).differentiableWithinAt
      have hφDeriv : Set.EqOn (deriv φ) 0 (Metric.ball (0 : ℝ) r) := by
        intro x hx
        exact (hφZeroDeriv x hx).deriv
      have hφConst : ∀ x ∈ Metric.ball (0 : ℝ) r, φ x = φ 0 := by
        intro x hx
        exact Metric.isOpen_ball.is_const_of_deriv_eq_zero
          (convex_ball (0 : ℝ) r).isPreconnected hφOn hφDeriv hx (Metric.mem_ball_self hr)
      refine Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, fun t ht => ?_⟩
      have hφt : φ t = 1 := by
        have h0 : φ 0 = 1 := by simp [φ, Eg, hg0]
        exact (hφConst t ht).trans h0
      have hEt : Eg t ≠ 0 := Complex.exp_ne_zero _
      have hgEt : g t / Eg t = 1 := by simpa [φ] using hφt
      field_simp [hEt] at hgEt
      simpa [Eg] using hgEt
  exact ⟨c, hsolve⟩

/-- **Analytic core of Bernstein's theorem.**  Under the Bernstein hypotheses with
finite second moments, the characteristic functions of `X` and `Y` coincide, on a
neighbourhood of `0`, with Gaussian characteristic functions that share one
variance `σ² ≥ 0` (with means `mf`, `mg`).  The shared `σ²` — a consequence of the
single constant `c` from `gaussianForm_of_funeq` — is exactly what the doubling
bootstrap in `bernstein` needs to extend the Gaussian form to all of `ℝ`.

Wiring: `f, g` are `C²` (`charFun_contDiff_two`) and satisfy the functional
equation (`bernstein_charFun_funeq`), so `gaussianForm_of_funeq` gives the local
forms with linear coefficients `f'(0), g'(0)` and shared quadratic constant `c`.
`iteratedDeriv_charFun_zero` identifies `f'(0) = I·E[X]`, `g'(0) = I·E[Y]` and
`c = −Var X = −Var Y`; set `mf = E[X]`, `mg = E[Y]`, `σ² = Var X ≥ 0`
(`variance_nonneg`). -/
lemma bernstein_charFun_gaussian_nhds_zero
    (mX : Measurable X) (mY : Measurable Y)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hXY : IndepFun X Y P) (hUV : IndepFun (X + Y) (X - Y) P) :
    ∃ mf mg σ2 : ℝ, 0 ≤ σ2 ∧
      (∀ᶠ t in nhds (0 : ℝ),
        charFun (P.map X) t = Complex.exp (mf * t * Complex.I - σ2 * t ^ 2 / 2)) ∧
      (∀ᶠ t in nhds (0 : ℝ),
        charFun (P.map Y) t = Complex.exp (mg * t * Complex.I - σ2 * t ^ 2 / 2)) := by
  let μX := P.map X
  let μY := P.map Y
  let f := charFun μX
  let g := charFun μY
  haveI : IsProbabilityMeasure μX := Measure.isProbabilityMeasure_map mX.aemeasurable
  haveI : IsProbabilityMeasure μY := Measure.isProbabilityMeasure_map mY.aemeasurable
  have hf : ContDiff ℝ 2 f := by
    simpa [f, μX] using charFun_contDiff_two (P := P) (Z := X) mX hX2
  have hg : ContDiff ℝ 2 g := by
    simpa [g, μY] using charFun_contDiff_two (P := P) (Z := Y) mY hY2
  have hf0 : f 0 = 1 := by simp [f]
  have hg0 : g 0 = 1 := by simp [g]
  have hfe : ∀ u v : ℝ, f (u + v) * g (u - v) = f u * g u * (f v * g (-v)) := by
    intro u v
    simpa [f, g, μX, μY] using bernstein_charFun_funeq mX mY hXY hUV u v
  obtain ⟨c, hXform, hYform⟩ := gaussianForm_of_funeq hf hg hf0 hg0 hfe
  have hXee :
      f =ᶠ[nhds (0 : ℝ)] fun t : ℝ =>
        Complex.exp (deriv f 0 * t + c * t ^ 2 / 2) := hXform
  have hYee :
      g =ᶠ[nhds (0 : ℝ)] fun t : ℝ =>
        Complex.exp (deriv g 0 * t + c * t ^ 2 / 2) := hYform
  have hμX2 : MemLp id 2 μX := by
    exact (memLp_map_measure_iff aestronglyMeasurable_id mX.aemeasurable).2
      (by simpa [μX, Function.comp_def] using hX2)
  have hμX1 : MemLp id 1 μX := hμX2.mono_exponent (by norm_num)
  have hμY2 : MemLp id 2 μY := by
    exact (memLp_map_measure_iff aestronglyMeasurable_id mY.aemeasurable).2
      (by simpa [μY, Function.comp_def] using hY2)
  have hμY1 : MemLp id 1 μY := hμY2.mono_exponent (by norm_num)
  let mf : ℝ := ∫ x, x ∂μX
  let mg : ℝ := ∫ y, y ∂μY
  let σ2 : ℝ := variance id μX
  have hderivX : deriv f 0 = Complex.I * (mf : ℂ) := by
    have hiter := iteratedDeriv_charFun_zero (μ := μX) (n := 1) (by simpa using hμX1)
    rw [← iteratedDeriv_one]
    simpa [f, mf] using hiter
  have hderivY : deriv g 0 = Complex.I * (mg : ℂ) := by
    have hiter := iteratedDeriv_charFun_zero (μ := μY) (n := 1) (by simpa using hμY1)
    rw [← iteratedDeriv_one]
    simpa [g, mg] using hiter
  have hsecondX : iteratedDeriv 2 f 0 = - ((∫ x, x ^ 2 ∂μX : ℝ) : ℂ) := by
    have hiter := iteratedDeriv_charFun_zero (μ := μX) (n := 2) hμX2
    simpa [f] using hiter
  have hmodelEval (a b : ℂ) :
      iteratedDeriv 2 (fun t : ℝ => Complex.exp (a * t + b * t ^ 2 / 2)) 0 = b + a ^ 2 := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    have hderivModel :
        deriv (fun t : ℝ => Complex.exp (a * t + b * t ^ 2 / 2))
          = fun t : ℝ => (a + b * t) * Complex.exp (a * t + b * t ^ 2 / 2) := by
      funext t
      have hcoe : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t :=
        HasDerivAt.ofReal_comp (hasDerivAt_id t)
      have hp : HasDerivAt (fun t : ℝ => a * (t : ℂ) + b * (t : ℂ) ^ 2 / 2)
          (a + b * (t : ℂ)) t := by
        convert ((hcoe.const_mul a).add (((hcoe.pow 2).const_mul b).div_const 2)) using 1 <;> ring
      convert hp.cexp.deriv using 1 <;> ring
    rw [hderivModel]
    have hcoe0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 :=
      HasDerivAt.ofReal_comp (hasDerivAt_id 0)
    have hp0 : HasDerivAt (fun t : ℝ => a * (t : ℂ) + b * (t : ℂ) ^ 2 / 2) a 0 := by
      convert ((hcoe0.const_mul a).add (((hcoe0.pow 2).const_mul b).div_const 2)) using 1
      norm_num
    have hlin0 : HasDerivAt (fun t : ℝ => a + b * (t : ℂ)) b 0 := by
      convert (hcoe0.const_mul b).const_add a using 1 <;> ring
    have hexp0 : HasDerivAt (fun t : ℝ => Complex.exp (a * t + b * t ^ 2 / 2)) a 0 := by
      convert hp0.cexp using 1 <;> simp <;> ring
    convert (hlin0.mul hexp0).deriv using 1 <;> simp <;> ring
  have hmodelSecondX : iteratedDeriv 2 f 0 = c + (deriv f 0) ^ 2 := by
    calc
      iteratedDeriv 2 f 0
          = iteratedDeriv 2
              (fun t : ℝ => Complex.exp (deriv f 0 * t + c * t ^ 2 / 2)) 0 :=
              hXee.iteratedDeriv_eq 2
      _ = c + (deriv f 0) ^ 2 := hmodelEval (deriv f 0) c
  have hsigma : σ2 = (∫ x, x ^ 2 ∂μX) - mf ^ 2 := by
    simpa [σ2, mf] using (variance_eq_sub (μ := μX) (X := id) hμX2)
  have hc : c = - (σ2 : ℂ) := by
    rw [hsecondX, hderivX] at hmodelSecondX
    have hc' : c = - ((∫ x, x ^ 2 ∂μX : ℝ) : ℂ) - (Complex.I * (mf : ℂ)) ^ 2 := by
      calc
        c = (c + (Complex.I * (mf : ℂ)) ^ 2) - (Complex.I * (mf : ℂ)) ^ 2 := by ring
        _ = - ((∫ x, x ^ 2 ∂μX : ℝ) : ℂ) - (Complex.I * (mf : ℂ)) ^ 2 := by
              rw [← hmodelSecondX]
    rw [hc', hsigma]
    rw [Complex.ext_iff]
    have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by rw [sq, Complex.I_mul_I]
    constructor
    · ring_nf
      rw [hI2]
      norm_num
      ring
    · ring_nf
      rw [hI2]
      norm_num
  refine ⟨mf, mg, σ2, variance_nonneg id μX, ?_, ?_⟩
  · refine hXee.mono ?_
    intro t ht
    change f t = Complex.exp ((mf : ℂ) * t * Complex.I - (σ2 : ℂ) * t ^ 2 / 2)
    rw [ht]
    congr 1
    rw [hderivX, hc]
    ring
  · refine hYee.mono ?_
    intro t ht
    change g t = Complex.exp ((mg : ℂ) * t * Complex.I - (σ2 : ℂ) * t ^ 2 / 2)
    rw [ht]
    congr 1
    rw [hderivY, hc]
    ring

/-- **Bernstein's theorem (finite-variance Darmois–Skitovich, two variables).**
If `X` and `Y` are independent real random variables with finite second moments,
and their sum `X + Y` and difference `X − Y` are independent, then both `X` and
`Y` have Gaussian laws.

This is the smallest non-degenerate instance of Darmois–Skitovich; the general
two-variable case (arbitrary coefficients `a₁X + a₂Y ⟂ b₁X + b₂Y` with
`a₁b₁ ≠ 0`, `a₂b₂ ≠ 0`) and the `n`-variable case build on the same machinery. -/
theorem bernstein
    (mX : Measurable X) (mY : Measurable Y)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hXY : IndepFun X Y P) (hUV : IndepFun (X + Y) (X - Y) P) :
    IsGaussian (P.map X) ∧ IsGaussian (P.map Y) := by
  -- Assembly: `bernstein_charFun_gaussian_nhds_zero` gives the local Gaussian forms
  -- for both `f = charFun (P.map X)` and `g = charFun (P.map Y)` with shared `σ²`.
  -- Extend each to all of `ℝ` by the doubling instance `f (2t) = f t ^ 2 · g t · g (−t)`
  -- of `bernstein_charFun_funeq` (induction on `2ⁿ`-scaled neighbourhoods), then
  -- identify the law via `Measure.ext_of_charFun` against `gaussianReal mf σ²`
  -- (resp. `gaussianReal mg σ²`) and conclude `IsGaussian` from the `gaussianReal`
  -- instance / `isGaussian_iff_gaussian_charFun`.
  obtain ⟨mf, mg, σ2, hσ, hXloc, hYloc⟩ :=
    bernstein_charFun_gaussian_nhds_zero (P := P) (X := X) (Y := Y)
      mX mY hX2 hY2 hXY hUV
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map mX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map mY.aemeasurable
  let Φf : ℝ → ℂ := fun t => Complex.exp (mf * t * Complex.I - σ2 * t ^ 2 / 2)
  let Φg : ℝ → ℂ := fun t => Complex.exp (mg * t * Complex.I - σ2 * t ^ 2 / 2)
  let EqAt : ℝ → Prop := fun t =>
    charFun (P.map X) t = Φf t ∧ charFun (P.map Y) t = Φg t
  have hloc : ∀ᶠ t in nhds (0 : ℝ), EqAt t := by
    filter_upwards [hXloc, hYloc] with t htX htY
    exact ⟨htX, htY⟩
  have DBLf : ∀ t : ℝ, charFun (P.map X) (2 * t) =
      charFun (P.map X) t ^ 2 * charFun (P.map Y) t * charFun (P.map Y) (-t) := by
    intro t
    have h := bernstein_charFun_funeq (P := P) (X := X) (Y := Y) mX mY hXY hUV t t
    calc
      charFun (P.map X) (2 * t)
          = charFun (P.map X) (t + t) := by rw [show (2 : ℝ) * t = t + t by ring]
      _ = charFun (P.map X) t ^ 2 * charFun (P.map Y) t * charFun (P.map Y) (-t) := by
          simpa [sq, mul_assoc, mul_left_comm, mul_comm] using h
  have DBLg : ∀ t : ℝ, charFun (P.map Y) (2 * t) =
      charFun (P.map Y) t ^ 2 * charFun (P.map X) t * charFun (P.map X) (-t) := by
    intro t
    have h := bernstein_charFun_funeq (P := P) (X := X) (Y := Y) mX mY hXY hUV t (-t)
    calc
      charFun (P.map Y) (2 * t)
          = charFun (P.map Y) (t - (-t)) := by rw [show (2 : ℝ) * t = t - (-t) by ring]
      _ = charFun (P.map Y) t ^ 2 * charFun (P.map X) t * charFun (P.map X) (-t) := by
          simpa [sq, mul_assoc, mul_left_comm, mul_comm] using h
  have TDBLf : ∀ t : ℝ, Φf (2 * t) = Φf t ^ 2 * Φg t * Φg (-t) := by
    intro t
    simp only [Φf, Φg]
    simp only [pow_two]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    norm_num
    ring_nf
  have TDBLg : ∀ t : ℝ, Φg (2 * t) = Φg t ^ 2 * Φf t * Φf (-t) := by
    intro t
    simp only [Φf, Φg]
    simp only [pow_two]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    norm_num
    ring_nf
  have step : ∀ t : ℝ, EqAt t → EqAt (-t) → EqAt (2 * t) := by
    intro t ht hnt
    constructor
    · calc
        charFun (P.map X) (2 * t)
            = charFun (P.map X) t ^ 2 * charFun (P.map Y) t * charFun (P.map Y) (-t) :=
                DBLf t
        _ = Φf t ^ 2 * Φg t * Φg (-t) := by rw [ht.1, ht.2, hnt.2]
        _ = Φf (2 * t) := (TDBLf t).symm
    · calc
        charFun (P.map Y) (2 * t)
            = charFun (P.map Y) t ^ 2 * charFun (P.map X) t * charFun (P.map X) (-t) :=
                DBLg t
        _ = Φg t ^ 2 * Φf t * Φf (-t) := by rw [ht.2, ht.1, hnt.1]
        _ = Φg (2 * t) := (TDBLg t).symm
  have grow : ∀ n : ℕ, ∀ t : ℝ, EqAt t → EqAt (-t) →
      EqAt ((2 : ℝ) ^ n * t) ∧ EqAt (-((2 : ℝ) ^ n * t)) := by
    intro n
    induction n with
    | zero =>
        intro t ht hnt
        simpa using And.intro ht hnt
    | succ n ih =>
        intro t ht hnt
        obtain ⟨ha, hna⟩ := ih t ht hnt
        have h2a : EqAt (2 * ((2 : ℝ) ^ n * t)) := step ((2 : ℝ) ^ n * t) ha hna
        have h2na : EqAt (2 * (-((2 : ℝ) ^ n * t))) := by
          exact step (-((2 : ℝ) ^ n * t)) hna (by simpa using ha)
        constructor
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h2a
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h2na
  have hkey : ∀ s : ℝ, EqAt s := by
    intro s
    have hseq : Filter.Tendsto (fun n : ℕ => s / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
      have hpow : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hpow) :
          Filter.Tendsto (fun n : ℕ => s * (((2 : ℝ) ^ n)⁻¹)) Filter.atTop (nhds (s * 0)))
    have hz : ∀ᶠ n in Filter.atTop, EqAt (s / (2 : ℝ) ^ n) := hseq.eventually hloc
    have hnz : ∀ᶠ n in Filter.atTop, EqAt (-(s / (2 : ℝ) ^ n)) := by
      have hlocNeg : ∀ᶠ t in nhds (-(0 : ℝ)), EqAt t := by simpa using hloc
      exact hseq.neg.eventually hlocNeg
    obtain ⟨n, hn⟩ := (hz.and hnz).exists
    have hgrow := grow n (s / (2 : ℝ) ^ n) hn.1 hn.2
    have hpow_ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
    have hs_eq : (2 : ℝ) ^ n * (s / (2 : ℝ) ^ n) = s := by
      field_simp [hpow_ne]
    simpa [hs_eq] using hgrow.1
  have hμX : P.map X = gaussianReal mf σ2.toNNReal := by
    refine Measure.ext_of_charFun ?_
    funext t
    rw [(hkey t).1, charFun_gaussianReal]
    simp only [Φf]
    congr 1
    rw [Real.coe_toNNReal σ2 hσ]
    ring
  have hμY : P.map Y = gaussianReal mg σ2.toNNReal := by
    refine Measure.ext_of_charFun ?_
    funext t
    rw [(hkey t).2, charFun_gaussianReal]
    simp only [Φg]
    congr 1
    rw [Real.coe_toNNReal σ2 hσ]
    ring
  constructor
  · rw [hμX]
    infer_instance
  · rw [hμY]
    infer_instance

end Causalean.Mathlib.Probability
