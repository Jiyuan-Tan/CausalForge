/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: second-order calculus of the variance envelope

Substrate for discharging the `EnvelopeLineC2Data` gate of `thm:heterogeneity-separation`.

The envelope `V_env` is singular on the boundary of the design box, so all calculus is done
on the globally-`C²` floored extension `varEnvelopeExt` (built from `recipC`), and transferred
back to `V_env` on the box, where the two agree. The transfer is always via an `EventuallyEq`
in a `ε/2`-ball, which is legitimate because a feasible design has every coordinate in
`[ε, 1-ε]` and every direction we use has `|d k| ≤ 1`.

The payload is `envCurv ε d q`, the directional curvature `Hess (V_env/4) q (d,d)`:

* it computes the second derivative of the envelope line (`deriv_deriv_envelope_line_eq_envCurv`),
* it is continuous in `q` (`envCurv_continuous`), hence bounded on the compact `feasibleSet`,
* so `dirModulus` — a `⨆` over `feasibleSet` — is a genuine supremum, and each feasible `q`
  satisfies `envCurv ε d q ≤ dirModulus E ε B d` (`envCurv_le_dirModulus`).

Those three facts are exactly the `ContDiffOn` / `deriv`-identity / `le_ciSup` conjuncts of
`EnvelopeLineC2Data`.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.TConvexDesign
import Causalean.Mathlib.Analysis.LineSecondDeriv

set_option linter.style.longLine false

open scoped BigOperators Topology
open Set Filter
open Causalean.Mathlib.Analysis

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

namespace BipartiteExperiment

variable (E : BipartiteExperiment I O)

/-! ### `C²` regularity of the floored envelope extension -/

/-- The floored treated-load extension is `C²` (it is `C¹` by `r1Ext_contDiff`; the only
input that needed strengthening is `recipC`, now `Cⁿ` for every `n`). -/
@[fun_prop]
lemma r1Ext_contDiff_two (ε : ℝ) (hε : 0 < ε) (i j : O) :
    ContDiff ℝ 2 (fun p : I → ℝ => E.r1Ext ε p i j) := by
  unfold r1Ext
  by_cases hij : 0 < (E.shared i j).card
  · simp only [hij, ↓reduceIte]
    fun_prop (disch := assumption)
  · simp only [hij, ↓reduceIte]
    fun_prop

/-- The floored control-load extension is `C²`. -/
@[fun_prop]
lemma r0Ext_contDiff_two (ε : ℝ) (hε : 0 < ε) (i j : O) :
    ContDiff ℝ 2 (fun p : I → ℝ => E.r0Ext ε p i j) := by
  unfold r0Ext
  by_cases hij : 0 < (E.shared i j).card
  · simp only [hij, ↓reduceIte]
    fun_prop (disch := assumption)
  · simp only [hij, ↓reduceIte]
    fun_prop

/-- The floored envelope extension is `C²` on all of `I → ℝ`. -/
lemma varEnvelopeExt_contDiff_two (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (E.varEnvelopeExt ε) := by
  unfold varEnvelopeExt
  fun_prop (disch := assumption)

/-- The NORMALIZED floored envelope extension `V_env^ext / 4` is `C²`. This is the function whose
Hessian quadratic form the modulus `dirModulus` measures. -/
lemma envelopeQuarterExt_contDiff_two (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (fun p : I → ℝ => E.varEnvelopeExt ε p / 4) := by
  unfold varEnvelopeExt
  fun_prop (disch := assumption)

/-! ### The directional curvature modulus -/

/-- Directional curvature of the normalized envelope at base point `q` along `d`, i.e.
`Hess (V_env/4) q (d, d)`, computed on the globally-`C²` extension. -/
noncomputable def envCurv (E : BipartiteExperiment I O) (ε : ℝ) (d q : I → ℝ) : ℝ :=
  secondDirDeriv (fun p : I → ℝ => E.varEnvelopeExt ε p / 4) d q

/-- The curvature modulus is continuous in the base point. Combined with compactness of
`feasibleSet` this is what makes `dirModulus` a genuine (bounded) supremum. -/
lemma envCurv_continuous (ε : ℝ) (hε : 0 < ε) (d : I → ℝ) :
    Continuous (E.envCurv ε d) := by
  exact continuous_secondDirDeriv (E.envelopeQuarterExt_contDiff_two ε hε) d

/-! ### Transfer between the singular envelope and its floored extension, along a line -/

/-- On an `ε/2`-ball of parameters, a line through a feasible point in a direction bounded by `1`
stays in the region where `recipC` has saturated, so `V_env` and `V_env^ext` agree there. -/
lemma envelope_line_eventuallyEq (ε B : ℝ) (hε : 0 < ε) {q : I → ℝ}
    (hq : q ∈ feasibleSet (I := I) ε B) {d : I → ℝ} (hd : ∀ k, |d k| ≤ 1) :
    (fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4)
      =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) := by
  filter_upwards [Ioo_mem_nhds (a := -(ε / 2)) (b := ε / 2)
    (by linarith) (by linarith)] with s hs
  have hsabs : |s| < ε / 2 := (abs_lt).mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbox : ∀ k, ε / 2 ≤ q k + s * d k ∧ ε / 2 ≤ 1 - (q k + s * d k) := by
    intro k
    have hsd : |s * d k| ≤ ε / 2 := by
      calc
        |s * d k| = |s| * |d k| := abs_mul _ _
        _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left (hd k) (abs_nonneg s)
        _ ≤ ε / 2 := le_of_lt (by simpa using hsabs)
    have hqk := hq.floor k
    constructor <;> linarith [le_abs_self (s * d k), neg_le_abs (s * d k)]
  exact congrArg (fun x : ℝ => x / 4)
    (E.varEnvelopeExt_eq_varEnvelope_of_box hε (fun k => (hbox k).1)
      (fun k => (hbox k).2)).symm

/-- The envelope line is `C²` on any parameter set that keeps the line inside the saturated box. -/
lemma contDiffOn_envelope_line (ε : ℝ) (hε : 0 < ε) {q d : I → ℝ} {S : Set ℝ}
    (hbox : ∀ s ∈ S, ∀ k, ε / 2 ≤ q k + s * d k ∧ ε / 2 ≤ 1 - (q k + s * d k)) :
    ContDiffOn ℝ 2 (fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) S := by
  have hext : ContDiff ℝ 2
      (fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) := by
    apply (E.envelopeQuarterExt_contDiff_two ε hε).comp
    apply contDiff_pi.mpr
    intro k
    fun_prop
  apply hext.contDiffOn.congr
  intro s hs
  exact congrArg (fun x : ℝ => x / 4)
    (E.varEnvelopeExt_eq_varEnvelope_of_box hε (fun k => (hbox s hs k).1)
      (fun k => (hbox s hs k).2)).symm

/-- The envelope line through a feasible point is differentiable at `0`. -/
lemma differentiableAt_envelope_line_zero (ε B : ℝ) (hε : 0 < ε) {q : I → ℝ}
    (hq : q ∈ feasibleSet (I := I) ε B) {d : I → ℝ} (hd : ∀ k, |d k| ≤ 1) :
    DifferentiableAt ℝ (fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) 0 := by
  apply (E.envelope_line_eventuallyEq ε B hε hq hd).differentiableAt_iff.mpr
  have hext : ContDiff ℝ 2
      (fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) := by
    apply (E.envelopeQuarterExt_contDiff_two ε hε).comp
    apply contDiff_pi.mpr
    intro k
    fun_prop
  exact (hext.differentiable two_ne_zero).differentiableAt

/-- The envelope line is differentiable at ANY parameter whose base point is feasible. Needed to
feed `ConvexOn.monotoneOn_deriv` on the whole segment, not just at its midpoint. -/
lemma differentiableAt_envelope_line (ε B : ℝ) (hε : 0 < ε) {q d : I → ℝ}
    (hd : ∀ k, |d k| ≤ 1) (t : ℝ)
    (hqt : (fun k => q k + t * d k) ∈ feasibleSet (I := I) ε B) :
    DifferentiableAt ℝ (fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) t := by
  have hshift : DifferentiableAt ℝ
      (fun u : ℝ => E.varEnvelope (fun k => (q k + t * d k) + u * d k) / 4) 0 :=
    E.differentiableAt_envelope_line_zero ε B hε hqt hd
  have heq :
      (fun u : ℝ => E.varEnvelope (fun k => q k + (t + u) * d k) / 4) =
        (fun u : ℝ => E.varEnvelope (fun k => (q k + t * d k) + u * d k) / 4) := by
    funext u
    congr 2
    funext k
    ring
  apply (differentiableAt_iff_comp_const_add (f :=
    fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) (a := t) (b := t)).mpr
  rw [heq]
  simpa using hshift

/-- The DERIVATIVE of the envelope line is itself differentiable at `0` (the line is `C²` there).
This is the `hdd` hypothesis of `convexOn_deriv2_nonneg`. -/
lemma differentiableAt_deriv_envelope_line_zero (ε B : ℝ) (hε : 0 < ε) {q : I → ℝ}
    (hq : q ∈ feasibleSet (I := I) ε B) {d : I → ℝ} (hd : ∀ k, |d k| ≤ 1) :
    DifferentiableAt ℝ (deriv fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) 0 := by
  apply (E.envelope_line_eventuallyEq ε B hε hq hd).deriv.differentiableAt_iff.mpr
  have hext : ContDiff ℝ 2
      (fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) := by
    apply (E.envelopeQuarterExt_contDiff_two ε hε).comp
    apply contDiff_pi.mpr
    intro k
    fun_prop
  have hder : ContDiff ℝ 1
      (deriv fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) := by
    exact (contDiff_succ_iff_deriv.mp hext).2.2
  exact (hder.differentiable one_ne_zero).differentiableAt

/-! ### First and second derivative of the envelope line -/

/-- Partial derivative of the normalized floored envelope in coordinate `k`, in the Pi space.
This is `deriv_varEnvelope_div_four_coord_line` (now public in `TConvexDesign`) restated as an
`fderiv` applied to the basis vector `Pi.single k 1`. -/
lemma fderiv_envelopeQuarterExt_single (ε B : ℝ) (hε : 0 < ε) {q : I → ℝ}
    (hq : q ∈ feasibleSet (I := I) ε B) (k : I) :
    fderiv ℝ (fun p : I → ℝ => E.varEnvelopeExt ε p / 4) q (Pi.single k 1) =
      E.envelopeGrad q k := by
  let f : (I → ℝ) → ℝ := fun p => E.varEnvelopeExt ε p / 4
  let e : I → ℝ := Pi.single k 1
  have he : ∀ l, |e l| ≤ 1 := by
    intro l
    by_cases hl : l = k
    · subst l
      simp [e]
    · simp [e, hl]
  have henv := E.envelope_line_eventuallyEq ε B hε hq he
  have hextline :
      (fun s : ℝ => f (q + s • e)) =
        (fun s : ℝ => E.varEnvelopeExt ε (fun l => q l + s * e l) / 4) := by
    funext s
    apply congrArg (fun p : I → ℝ => E.varEnvelopeExt ε p / 4)
    funext l
    simp [smul_eq_mul]
  have hcoord :
      (fun s : ℝ => E.varEnvelope (fun l => q l + s * e l) / 4) =
        (fun s : ℝ => E.varEnvelope (fun l => q l + (if l = k then s else 0)) / 4) := by
    funext s
    apply congrArg (fun p : I → ℝ => E.varEnvelope p / 4)
    funext l
    by_cases hl : l = k <;> simp [e, hl]
  calc
    fderiv ℝ f q e = deriv (fun s : ℝ => f (q + s • e)) 0 := by
      rw [deriv_line]
      · simp
      · simpa [f] using (E.envelopeQuarterExt_contDiff_two ε hε).differentiable two_ne_zero
    _ = deriv (fun s : ℝ => E.varEnvelopeExt ε (fun l => q l + s * e l) / 4) 0 := by
      rw [hextline]
    _ = deriv (fun s : ℝ => E.varEnvelope (fun l => q l + s * e l) / 4) 0 :=
      henv.deriv_eq.symm
    _ = deriv (fun s : ℝ => E.varEnvelope (fun l => q l + (if l = k then s else 0)) / 4) 0 := by
      rw [hcoord]
    _ = E.envelopeGrad q k :=
      deriv_varEnvelope_div_four_coord_line E ε B hε hq k

/-- The directional derivative of the normalized floored envelope is the gradient-score
contraction `∑ k, d k * g_k(q)`. -/
lemma fderiv_envelopeQuarterExt_apply (ε B : ℝ) (hε : 0 < ε) {q : I → ℝ}
    (hq : q ∈ feasibleSet (I := I) ε B) (d : I → ℝ) :
    fderiv ℝ (fun p : I → ℝ => E.varEnvelopeExt ε p / 4) q d =
      ∑ k, d k * E.envelopeGrad q k := by
  classical
  calc
    fderiv ℝ (fun p : I → ℝ => E.varEnvelopeExt ε p / 4) q d =
        ∑ k, d k * fderiv ℝ (fun p : I → ℝ => E.varEnvelopeExt ε p / 4) q
          (Pi.single k 1) := by
      conv_lhs => rw [pi_eq_sum_univ d]
      rw [map_sum]
      simp_rw [map_smul]
      simp only [smul_eq_mul]
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      apply congrArg (fderiv ℝ (fun p : I → ℝ => E.varEnvelopeExt ε p / 4) q)
      funext j
      by_cases h : x = j
      · subst j
        simp
      · have h' : j ≠ x := Ne.symm h
        simp [h, h']
    _ = ∑ k, d k * E.envelopeGrad q k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [E.fderiv_envelopeQuarterExt_single ε B hε hq k]

/-- **First derivative of the envelope line at `0`.** -/
lemma deriv_envelope_line_zero (ε B : ℝ) (hε : 0 < ε) {q : I → ℝ}
    (hq : q ∈ feasibleSet (I := I) ε B) {d : I → ℝ} (hd : ∀ k, |d k| ≤ 1) :
    deriv (fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) 0 =
      ∑ k, d k * E.envelopeGrad q k := by
  let f : (I → ℝ) → ℝ := fun p => E.varEnvelopeExt ε p / 4
  have hline :
      (fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) =
        (fun s : ℝ => f (q + s • d)) := by
    funext s
    apply congrArg (fun p : I → ℝ => E.varEnvelopeExt ε p / 4)
    funext k
    simp [smul_eq_mul]
  calc
    deriv (fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) 0 =
        deriv (fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) 0 :=
      (E.envelope_line_eventuallyEq ε B hε hq hd).deriv_eq
    _ = deriv (fun s : ℝ => f (q + s • d)) 0 := by rw [hline]
    _ = fderiv ℝ f q d := by
      rw [deriv_line]
      · simp
      · simpa [f] using (E.envelopeQuarterExt_contDiff_two ε hε).differentiable two_ne_zero
    _ = ∑ k, d k * E.envelopeGrad q k :=
      E.fderiv_envelopeQuarterExt_apply ε B hε hq d

/-- **Second derivative of the envelope line at `0`** equals the directional curvature at the base
point. -/
lemma deriv_deriv_envelope_line_zero (ε B : ℝ) (hε : 0 < ε) {q : I → ℝ}
    (hq : q ∈ feasibleSet (I := I) ε B) {d : I → ℝ} (hd : ∀ k, |d k| ≤ 1) :
    deriv (deriv fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) 0 =
      E.envCurv ε d q := by
  let f : (I → ℝ) → ℝ := fun p => E.varEnvelopeExt ε p / 4
  have hline :
      (fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) =
        (fun s : ℝ => f (q + s • d)) := by
    funext s
    apply congrArg (fun p : I → ℝ => E.varEnvelopeExt ε p / 4)
    funext k
    simp [smul_eq_mul]
  calc
    deriv (deriv fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) 0 =
        deriv (deriv fun s : ℝ => E.varEnvelopeExt ε (fun k => q k + s * d k) / 4) 0 :=
      (E.envelope_line_eventuallyEq ε B hε hq hd).deriv.deriv_eq
    _ = deriv (deriv fun s : ℝ => f (q + s • d)) 0 := by rw [hline]
    _ = secondDirDeriv f d q := by
      simpa [f] using deriv_deriv_line (E.envelopeQuarterExt_contDiff_two ε hε) q d 0
    _ = E.envCurv ε d q := rfl

/-- **Second derivative of the envelope line at an arbitrary parameter `t`** equals the directional
curvature at the SHIFTED base point `q + t·d`. This is the form the `EnvelopeLineC2Data` curvature
conjunct needs, since it quantifies over `t ∈ Icc 0 T`. -/
lemma deriv_deriv_envelope_line_eq_envCurv (ε B : ℝ) (hε : 0 < ε) {q d : I → ℝ}
    (hd : ∀ k, |d k| ≤ 1) (t : ℝ)
    (hqt : (fun k => q k + t * d k) ∈ feasibleSet (I := I) ε B) :
    deriv (deriv fun s : ℝ => E.varEnvelope (fun k => q k + s * d k) / 4) t =
      E.envCurv ε d (fun k => q k + t * d k) := by
  let F : ℝ → ℝ := fun s => E.varEnvelope (fun k => q k + s * d k) / 4
  have hshift :
      (fun u : ℝ => F (t + u)) =
        (fun u : ℝ => E.varEnvelope (fun k => (q k + t * d k) + u * d k) / 4) := by
    funext u
    apply congrArg (fun p : I → ℝ => E.varEnvelope p / 4)
    funext k
    ring
  calc
    deriv (deriv F) t = deriv (fun u : ℝ => deriv F (t + u)) 0 := by
      symm
      simpa using (deriv_comp_const_add (deriv F) t 0)
    _ = deriv (deriv fun u : ℝ => F (t + u)) 0 := by
      congr 1
      funext u
      exact (deriv_comp_const_add F t u).symm
    _ = deriv (deriv fun u : ℝ =>
        E.varEnvelope (fun k => (q k + t * d k) + u * d k) / 4) 0 := by
      rw [hshift]
    _ = E.envCurv ε d (fun k => q k + t * d k) :=
      E.deriv_deriv_envelope_line_zero ε B hε hqt hd

/-! ### `dirModulus` is a genuine bounded supremum -/

/-- `dirModulus` is the supremum of `envCurv` over the feasible set: its defining body, stated with
the singular `V_env`, agrees with `envCurv` at every feasible base point. -/
lemma dirModulus_eq_ciSup_envCurv (ε B : ℝ) (hε : 0 < ε) {d : I → ℝ} (hd : ∀ k, |d k| ≤ 1) :
    dirModulus E ε B d = ⨆ q : feasibleSet (I := I) ε B, E.envCurv ε d (q : I → ℝ) := by
  unfold dirModulus
  congr 1
  funext q
  exact E.deriv_deriv_envelope_line_zero ε B hε q.property hd

/-- The curvature values over the feasible set are bounded above: `envCurv` is continuous and
`feasibleSet` is compact. This is the `BddAbove` side condition of `le_ciSup`, and the fact whose
absence stalled the original gate. -/
lemma bddAbove_envCurv_range (ε B : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hBlo : (Fintype.card I : ℝ) * ε ≤ B) (hBhi : B ≤ (Fintype.card I : ℝ) * (1 - ε))
    (d : I → ℝ) :
    BddAbove (Set.range fun q : feasibleSet (I := I) ε B => E.envCurv ε d (q : I → ℝ)) := by
  have hcpt : IsCompact (feasibleSet (I := I) ε B) :=
    (convex_design E ε B hε hε2 hBlo hBhi).2.1
  have hrange :
      Set.range (fun q : feasibleSet (I := I) ε B => E.envCurv ε d (q : I → ℝ)) =
        E.envCurv ε d '' feasibleSet (I := I) ε B := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  rw [hrange]
  exact (hcpt.image (E.envCurv_continuous ε hε d)).bddAbove

/-- Every feasible base point's directional curvature is dominated by `dirModulus`. -/
lemma envCurv_le_dirModulus (ε B : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hBlo : (Fintype.card I : ℝ) * ε ≤ B) (hBhi : B ≤ (Fintype.card I : ℝ) * (1 - ε))
    {d : I → ℝ} (hd : ∀ k, |d k| ≤ 1) {q : I → ℝ} (hq : q ∈ feasibleSet (I := I) ε B) :
    E.envCurv ε d q ≤ dirModulus E ε B d := by
  rw [E.dirModulus_eq_ciSup_envCurv ε B hε hd]
  exact le_ciSup (E.bddAbove_envCurv_range ε B hε hε2 hBlo hBhi d) ⟨q, hq⟩

end BipartiteExperiment

end CausalSmith.Experimentation.BipartiteMinimaxDesign
