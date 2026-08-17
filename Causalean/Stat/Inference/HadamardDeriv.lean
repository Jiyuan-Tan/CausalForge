/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hadamard directional derivatives

The functional delta method rests on a *weaker* notion of differentiability
than Fréchet: **Hadamard directional differentiability**.  A map `φ` is
Hadamard directionally differentiable at `θ` with derivative `φ'` if, for
every direction `h`, every perturbed direction sequence `hₙ → h`, and every
step size `tₙ ↓ 0`,

    (φ (θ + tₙ • hₙ) − φ θ) / tₙ  →  φ' h.

The derivative `φ'` is positively homogeneous but **need not be linear** — and
that is exactly the point: lattice functionals such as `max`/`min` (which sit
under the partial-identification intersection bounds `[sup' L, inf' U]`) are
Hadamard directionally differentiable with a *nonlinear* (sublinear) derivative
at a tie, so the ordinary Fréchet delta method (`Stat/Inference/DeltaMethod.lean`)
does not apply, while the directional delta method
(`Stat/Inference/FunctionalDelta.lean`) does.

Reference: van der Vaart (1998), §20.2 and Thm 20.8; Shapiro (1991);
Fang & Santos (2019), *Inference on Directionally Differentiable Functions*,
Review of Economic Studies.

Main definitions / results:

* `HasHadamardDirDerivAt φ φ' θ` — sequential Hadamard directional
  differentiability.
* `HasFDerivAt.hasHadamardDirDerivAt` — Fréchet ⇒ Hadamard (the linear
  derivative `L` is also the Hadamard derivative).  Fully proved, axiom-clean:
  the remainder `(tₙ)⁻¹•rₙ → 0` follows from composing the Fréchet little-o with
  the curve `xₙ = θ + tₙ•hₙ` and a bounded-`‖hₙ‖` divide-by-rate squeeze.
* `maxDirDeriv a b` / `minDirDeriv a b` — the directional derivative of
  `max`/`min : ℝ × ℝ → ℝ` at `(a, b)`, with its `Continuous` instance.
* `hasHadamardDirDerivAt_max` / `hasHadamardDirDerivAt_min` — the max/min
  functionals are Hadamard directionally differentiable.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Order.Lattice

/-! # Hadamard Directional Derivatives

This file defines Hadamard directional differentiability for maps between
normed spaces and connects it to ordinary differentiability. It also develops
the directional derivatives of maximum and minimum functionals that support
delta-method arguments for nonsmooth statistical targets.

The central definition is `HasHadamardDirDerivAt`.  The theorem
`HasFDerivAt.hasHadamardDirDerivAt` shows that ordinary Fréchet
differentiability implies Hadamard directional differentiability with the same
linear derivative.  The declarations `maxDirDeriv`, `minDirDeriv`,
`continuous_maxDirDeriv`, `continuous_minDirDeriv`,
`hasHadamardDirDerivAt_max`, and `hasHadamardDirDerivAt_min` give the lattice
derivatives used by the functional delta-method file. -/

namespace Causalean.Stat

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Hadamard directional differentiability.**  `φ` has Hadamard directional
derivative `φ'` at `θ` if for every direction `h`, every sequence `hₙ → h`, and
every step sequence `tₙ → 0` with `tₙ > 0`,

    (tₙ)⁻¹ • (φ (θ + tₙ • hₙ) − φ θ)  →  φ' h.

`φ'` is required to reproduce the limit but is *not* assumed linear; this is the
notion needed for the directional delta method. -/
def HasHadamardDirDerivAt (φ : E → F) (φ' : E → F) (θ : E) : Prop :=
  ∀ (h : E) (hn : ℕ → E) (tn : ℕ → ℝ),
    Tendsto hn atTop (𝓝 h) → Tendsto tn atTop (𝓝 0) → (∀ n, 0 < tn n) →
    Tendsto (fun n => (tn n)⁻¹ • (φ (θ + tn n • hn n) - φ θ)) atTop (𝓝 (φ' h))

/-! ## Fréchet differentiability is stronger -/

/-- **Fréchet implies Hadamard.** If [the map `φ` is Fréchet-differentiable at the point `θ`,
with continuous linear derivative `L`](hyp:hL), then [`φ` is Hadamard directionally
differentiable at `θ`, with the same map `L` serving as its Hadamard directional
derivative](goal). -/
theorem HasFDerivAt.hasHadamardDirDerivAt {φ : E → F} {L : E →L[ℝ] F} {θ : E}
    (hL : HasFDerivAt φ L θ) :
    HasHadamardDirDerivAt φ (fun x => L x) θ := by
  intro h hn tn hhn htn htn_pos
  have hxn : Tendsto (fun n => θ + tn n • hn n) atTop (𝓝 θ) := by
    have h0 : Tendsto (fun n => tn n • hn n) atTop (𝓝 0) := by
      simpa using htn.smul hhn
    simpa using (tendsto_const_nhds (x := θ)).add h0
  have hLhn : Tendsto (fun n => L (hn n)) atTop (𝓝 (L h)) :=
    (L.continuous.tendsto h).comp hhn
  -- remainder `rₙ := φ(θ + tₙ•hₙ) − φθ − tₙ • L hₙ`
  set rn : ℕ → F := fun n => φ (θ + tn n • hn n) - φ θ - tn n • L (hn n) with hrn_def
  have hrec : ∀ n, (tn n)⁻¹ • (φ (θ + tn n • hn n) - φ θ)
      = L (hn n) + (tn n)⁻¹ • rn n := by
    intro n
    have htn_ne : tn n ≠ 0 := (htn_pos n).ne'
    have hsplit : (tn n)⁻¹ • rn n
        = (tn n)⁻¹ • (φ (θ + tn n • hn n) - φ θ) - L (hn n) := by
      rw [hrn_def]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ htn_ne, one_smul]
    rw [hsplit]; abel
  have hrem : Tendsto (fun n => (tn n)⁻¹ • rn n) atTop (𝓝 0) := by
    -- Step 1: the Fréchet remainder composed with the curve `xₙ = θ + tₙ•hₙ` is
    -- little-o of `tₙ•hₙ` (`= xₙ − θ`).
    have hf : (fun n => φ (θ + tn n • hn n) - φ θ - L ((θ + tn n • hn n) - θ))
        =ᶠ[atTop] rn := by
      apply Filter.Eventually.of_forall
      intro n
      simp only [hrn_def, add_sub_cancel_left, map_smul]
    have hg : (fun n => (θ + tn n • hn n) - θ) =ᶠ[atTop] (fun n => tn n • hn n) := by
      apply Filter.Eventually.of_forall
      intro n
      simp only [add_sub_cancel_left]
    have hlitt := (hL.isLittleO.comp_tendsto hxn).congr' hf hg
    -- Step 2: divide by the rate `tₙ`.  Since `‖hₙ‖` is bounded, `(tₙ)⁻¹•rₙ → 0`.
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨M, hMpos, hMev⟩ : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, ‖hn n‖ ≤ M := by
      refine ⟨‖h‖ + 1, by positivity, ?_⟩
      have hnorm : Tendsto (fun n => ‖hn n‖) atTop (𝓝 ‖h‖) :=
        (continuous_norm.tendsto h).comp hhn
      filter_upwards [hnorm.eventually_lt_const (lt_add_one ‖h‖)] with n hn_ev
      exact hn_ev.le
    have hc : (0 : ℝ) < ε / (2 * M) := div_pos hε (by linarith)
    have hbound := hlitt.def hc
    filter_upwards [hbound, hMev] with n hb hMn
    have htn_pos' := htn_pos n
    have htn_ne : tn n ≠ 0 := htn_pos'.ne'
    have hsmul_norm : ‖tn n • hn n‖ = tn n * ‖hn n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htn_pos']
    rw [hsmul_norm] at hb
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htn_pos']
    calc (tn n)⁻¹ * ‖rn n‖
        ≤ (tn n)⁻¹ * (ε / (2 * M) * (tn n * ‖hn n‖)) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr htn_pos'.le)
      _ = ε / (2 * M) * ‖hn n‖ := by
          have he : (tn n)⁻¹ * (ε / (2 * M) * (tn n * ‖hn n‖))
              = ε / (2 * M) * ((tn n)⁻¹ * tn n) * ‖hn n‖ := by ring
          rw [he, inv_mul_cancel₀ htn_ne, mul_one]
      _ ≤ ε / (2 * M) * M :=
          mul_le_mul_of_nonneg_left hMn (div_nonneg hε.le (by linarith))
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have := hLhn.add hrem
  simpa [hrec] using this

/-! ## Lattice functionals on `ℝ × ℝ` -/

/-- The directional derivative of `max : ℝ × ℝ → ℝ` at `(a, b)`:
`fst` if `b < a`, `snd` if `a < b`, and `max` itself at a tie `a = b`
(where it is sublinear, not linear). -/
noncomputable def maxDirDeriv (a b : ℝ) : ℝ × ℝ → ℝ :=
  fun z => if b < a then z.1 else if a < b then z.2 else max z.1 z.2

/-- The directional derivative of `min : ℝ × ℝ → ℝ` at `(a, b)`. -/
noncomputable def minDirDeriv (a b : ℝ) : ℝ × ℝ → ℝ :=
  fun z => if a < b then z.1 else if b < a then z.2 else min z.1 z.2

/-- The directional derivative of the maximum functional is continuous. -/
theorem continuous_maxDirDeriv (a b : ℝ) : Continuous (maxDirDeriv a b) := by
  unfold maxDirDeriv
  split_ifs
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_fst.max continuous_snd

/-- The directional derivative of the minimum functional is continuous. -/
theorem continuous_minDirDeriv (a b : ℝ) : Continuous (minDirDeriv a b) := by
  unfold minDirDeriv
  split_ifs
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_fst.min continuous_snd

/-- **`max` is Hadamard directionally differentiable.**  At `(a, b)` the
derivative is `maxDirDeriv a b` (linear off the diagonal, sublinear at a tie). -/
theorem hasHadamardDirDerivAt_max (a b : ℝ) :
    HasHadamardDirDerivAt (fun z : ℝ × ℝ => max z.1 z.2) (maxDirDeriv a b) (a, b) := by
  intro h hn tn hhn htn htn_pos
  have hh1 : Tendsto (fun n => (hn n).1) atTop (𝓝 h.1) :=
    (continuous_fst.tendsto h).comp hhn
  have hh2 : Tendsto (fun n => (hn n).2) atTop (𝓝 h.2) :=
    (continuous_snd.tendsto h).comp hhn
  unfold maxDirDeriv
  split_ifs with hba hab
  · -- b < a : the first coordinate eventually dominates, derivative = h.1
    have hmax_ab : max a b = a := max_eq_left (le_of_lt hba)
    have hg : Tendsto (fun n => (a + tn n * (hn n).1) - (b + tn n * (hn n).2))
        atTop (𝓝 (a - b)) := by
      have h0 : Tendsto (fun n => tn n * ((hn n).1 - (hn n).2)) atTop (𝓝 0) := by
        simpa using htn.mul (hh1.sub hh2)
      have hsum := (tendsto_const_nhds (x := a - b)).add h0
      simp only [add_zero] at hsum
      refine hsum.congr ?_
      intro n; ring
    have hev : ∀ᶠ n in atTop, b + tn n * (hn n).2 ≤ a + tn n * (hn n).1 := by
      filter_upwards [hg.eventually (eventually_gt_nhds (show (0:ℝ) < a - b by linarith))]
        with n hn_ev
      linarith
    refine hh1.congr' ?_
    filter_upwards [hev] with n hge
    have htn_ne : tn n ≠ 0 := (htn_pos n).ne'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [max_eq_left hge, hmax_ab,
      show a + tn n * (hn n).1 - a = tn n * (hn n).1 by ring,
      ← mul_assoc, inv_mul_cancel₀ htn_ne, one_mul]
  · -- a < b : the second coordinate eventually dominates, derivative = h.2
    have hmax_ab : max a b = b := max_eq_right (le_of_lt hab)
    have hg : Tendsto (fun n => (b + tn n * (hn n).2) - (a + tn n * (hn n).1))
        atTop (𝓝 (b - a)) := by
      have h0 : Tendsto (fun n => tn n * ((hn n).2 - (hn n).1)) atTop (𝓝 0) := by
        simpa using htn.mul (hh2.sub hh1)
      have hsum := (tendsto_const_nhds (x := b - a)).add h0
      simp only [add_zero] at hsum
      refine hsum.congr ?_
      intro n; ring
    have hev : ∀ᶠ n in atTop, a + tn n * (hn n).1 ≤ b + tn n * (hn n).2 := by
      filter_upwards [hg.eventually (eventually_gt_nhds (show (0:ℝ) < b - a by linarith))]
        with n hn_ev
      linarith
    refine hh2.congr' ?_
    filter_upwards [hev] with n hle
    have htn_ne : tn n ≠ 0 := (htn_pos n).ne'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [max_eq_right hle, hmax_ab,
      show b + tn n * (hn n).2 - b = tn n * (hn n).2 by ring,
      ← mul_assoc, inv_mul_cancel₀ htn_ne, one_mul]
  · -- a = b : the tie case collapses to `max (hₙ.1) (hₙ.2) → max h.1 h.2`
    have hab_eq : a = b := le_antisymm (not_lt.1 hba) (not_lt.1 hab)
    have key : ∀ n, (tn n)⁻¹ • ((fun z : ℝ × ℝ => max z.1 z.2)
        ((a, b) + tn n • hn n) - max a b) = max (hn n).1 (hn n).2 := by
      intro n
      have htn_ne : tn n ≠ 0 := (htn_pos n).ne'
      have hpos := htn_pos n
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, hab_eq]
      have e1 : max (b + tn n * (hn n).1) (b + tn n * (hn n).2)
          = b + tn n * max (hn n).1 (hn n).2 := by
        rcases le_total (hn n).1 (hn n).2 with hle | hle
        · rw [max_eq_right hle, max_eq_right (by nlinarith [hpos])]
        · rw [max_eq_left hle, max_eq_left (by nlinarith [hpos])]
      rw [e1, max_self,
        show b + tn n * max (hn n).1 (hn n).2 - b = tn n * max (hn n).1 (hn n).2 by ring,
        ← mul_assoc, inv_mul_cancel₀ htn_ne, one_mul]
    simp only [key]
    exact hh1.max hh2

/-- **`min` is Hadamard directionally differentiable.**  At `(a, b)` the
derivative is `minDirDeriv a b`. -/
theorem hasHadamardDirDerivAt_min (a b : ℝ) :
    HasHadamardDirDerivAt (fun z : ℝ × ℝ => min z.1 z.2) (minDirDeriv a b) (a, b) := by
  intro h hn tn hhn htn htn_pos
  have hh1 : Tendsto (fun n => (hn n).1) atTop (𝓝 h.1) :=
    (continuous_fst.tendsto h).comp hhn
  have hh2 : Tendsto (fun n => (hn n).2) atTop (𝓝 h.2) :=
    (continuous_snd.tendsto h).comp hhn
  unfold minDirDeriv
  split_ifs with hab hba
  · -- a < b : the first coordinate eventually dominates the min, derivative = h.1
    have hmin_ab : min a b = a := min_eq_left (le_of_lt hab)
    have hg : Tendsto (fun n => (b + tn n * (hn n).2) - (a + tn n * (hn n).1))
        atTop (𝓝 (b - a)) := by
      have h0 : Tendsto (fun n => tn n * ((hn n).2 - (hn n).1)) atTop (𝓝 0) := by
        simpa using htn.mul (hh2.sub hh1)
      have hsum := (tendsto_const_nhds (x := b - a)).add h0
      simp only [add_zero] at hsum
      refine hsum.congr ?_
      intro n; ring
    have hev : ∀ᶠ n in atTop, a + tn n * (hn n).1 ≤ b + tn n * (hn n).2 := by
      filter_upwards [hg.eventually (eventually_gt_nhds (show (0:ℝ) < b - a by linarith))]
        with n hn_ev
      linarith
    refine hh1.congr' ?_
    filter_upwards [hev] with n hle
    have htn_ne : tn n ≠ 0 := (htn_pos n).ne'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [min_eq_left hle, hmin_ab,
      show a + tn n * (hn n).1 - a = tn n * (hn n).1 by ring,
      ← mul_assoc, inv_mul_cancel₀ htn_ne, one_mul]
  · -- b < a : the second coordinate eventually dominates the min, derivative = h.2
    have hmin_ab : min a b = b := min_eq_right (le_of_lt hba)
    have hg : Tendsto (fun n => (a + tn n * (hn n).1) - (b + tn n * (hn n).2))
        atTop (𝓝 (a - b)) := by
      have h0 : Tendsto (fun n => tn n * ((hn n).1 - (hn n).2)) atTop (𝓝 0) := by
        simpa using htn.mul (hh1.sub hh2)
      have hsum := (tendsto_const_nhds (x := a - b)).add h0
      simp only [add_zero] at hsum
      refine hsum.congr ?_
      intro n; ring
    have hev : ∀ᶠ n in atTop, b + tn n * (hn n).2 ≤ a + tn n * (hn n).1 := by
      filter_upwards [hg.eventually (eventually_gt_nhds (show (0:ℝ) < a - b by linarith))]
        with n hn_ev
      linarith
    refine hh2.congr' ?_
    filter_upwards [hev] with n hge
    have htn_ne : tn n ≠ 0 := (htn_pos n).ne'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [min_eq_right hge, hmin_ab,
      show b + tn n * (hn n).2 - b = tn n * (hn n).2 by ring,
      ← mul_assoc, inv_mul_cancel₀ htn_ne, one_mul]
  · -- a = b : tie case collapses to `min (hₙ.1) (hₙ.2) → min h.1 h.2`
    have hab_eq : a = b := le_antisymm (not_lt.1 hba) (not_lt.1 hab)
    have key : ∀ n, (tn n)⁻¹ • ((fun z : ℝ × ℝ => min z.1 z.2)
        ((a, b) + tn n • hn n) - min a b) = min (hn n).1 (hn n).2 := by
      intro n
      have htn_ne : tn n ≠ 0 := (htn_pos n).ne'
      have hpos := htn_pos n
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, hab_eq]
      have e1 : min (b + tn n * (hn n).1) (b + tn n * (hn n).2)
          = b + tn n * min (hn n).1 (hn n).2 := by
        rcases le_total (hn n).1 (hn n).2 with hle | hle
        · rw [min_eq_left hle, min_eq_left (by nlinarith [hpos])]
        · rw [min_eq_right hle, min_eq_right (by nlinarith [hpos])]
      rw [e1, min_self,
        show b + tn n * min (hn n).1 (hn n).2 - b = tn n * min (hn n).1 (hn n).2 by ring,
        ← mul_assoc, inv_mul_cancel₀ htn_ne, one_mul]
    simp only [key]
    exact hh1.min hh2

end Causalean.Stat
