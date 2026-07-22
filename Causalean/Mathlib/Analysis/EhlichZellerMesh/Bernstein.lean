/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.BernsteinSzegoTrig.Szego

/-!
# Bernstein / Szegő analytic core for the Ehlich–Zeller mesh inequality

For a real polynomial `R` of degree `≤ β`, the substitution `x = -cos t` turns
`R` into the *even trigonometric polynomial* `czTrig R t = R.eval (-cos t)` of
degree `≤ β` on `[0, π]`.  This file isolates the genuinely analytic heart of the
Ehlich–Zeller argument, namely Bernstein's / Szegő's differential inequality for
trigonometric polynomials and its `arccos`-Lipschitz consequence.

Main declarations:

* `czTrig`, `czSup` — the trigonometric transform of `R` and its sup-norm on
  `[0, π]`.
* `czTrig_continuous`, `czSup_attained` — soft-analysis facts (continuity and
  attainment of the sup on the compact interval `[0, π]`).
* `czTrig_szego_deriv` — **Szegő's inequality**: `|d/dt czTrig R t| ≤ β ·
  √(M² − (czTrig R t)²)` where `M = czSup R`.  This is the deep input; no such
  lemma exists in Mathlib, so it is proved here from the trigonometric-polynomial
  structure of `czTrig R`.
* `czTrig_arccos_lipschitz` — the Lipschitz reformulation: `t ↦ arccos(czTrig R t
  / M)` is `β`-Lipschitz on `[0, π]`.
* `czTrig_maximizer_bound` — the packaged output consumed by the mesh file: if
  `t₀` is a maximizer (`czTrig R t₀ = M`) and `s` is any point with
  `β·|t₀ − s| ≤ π/2`, then `M · cos(β·|t₀ − s|) ≤ czTrig R s`.

These are stated for a *general* real polynomial `R` and a *general* degree bound
`β`; nothing is specialized to the downstream rollout objects.

## Standard reference
Ehlich, H. & Zeller, K. (1964), *Schwankung von Polynomen zwischen
Gitterpunkten*, Math. Z. 86, 41–44; Rivlin, *The Chebyshev Polynomials* (1974).
-/

open Real Polynomial

namespace Causalean.Mathlib.Analysis.EhlichZellerMesh

/-- The trigonometric transform of a real polynomial `R`: `czTrig R t = R(-cos t)`.
For `R` of degree `≤ β` this is an even trigonometric polynomial of degree `≤ β`,
and as `t` ranges over `[0, π]` the argument `-cos t` ranges over all of `[-1, 1]`. -/
noncomputable def czTrig (R : Polynomial ℝ) (t : ℝ) : ℝ := R.eval (- Real.cos t)

/-- The sup-norm of the trigonometric transform of `R` over the compact interval
`[0, π]`.  By surjectivity of `t ↦ -cos t` this equals `sup_{x∈[-1,1]} |R x|`. -/
noncomputable def czSup (R : Polynomial ℝ) : ℝ :=
  sSup ((fun t => |czTrig R t|) '' Set.Icc 0 Real.pi)

/-- `czTrig R` is continuous (composition of the polynomial evaluation with
`t ↦ -cos t`). -/
theorem czTrig_continuous (R : Polynomial ℝ) : Continuous (czTrig R) := by
  unfold czTrig
  fun_prop

/-- The sup-norm `czSup R` is attained at some point of `[0, π]`: there is
`t₀ ∈ [0, π]` with `|czTrig R t₀| = czSup R`.  This is the extreme-value theorem
applied to the continuous map `|czTrig R|` on the compact interval `[0, π]`. -/
theorem czSup_attained (R : Polynomial ℝ) :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) Real.pi, |czTrig R t₀| = czSup R := by
  classical
  have hK : IsCompact (Set.Icc (0 : ℝ) Real.pi) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) Real.pi).Nonempty := ⟨0, by constructor <;> positivity⟩
  have hcont : ContinuousOn (fun t => |czTrig R t|) (Set.Icc (0 : ℝ) Real.pi) :=
    (czTrig_continuous R).abs.continuousOn
  rcases hK.exists_sSup_image_eq hne hcont with ⟨t₀, ht₀, hsup⟩
  exact ⟨t₀, ht₀, hsup.symm⟩

/-- `czSup R` is nonnegative (it is a supremum of absolute values). -/
theorem czSup_nonneg (R : Polynomial ℝ) : 0 ≤ czSup R := by
  rcases czSup_attained R with ⟨t₀, _ht₀, hsup⟩
  rw [← hsup]
  exact abs_nonneg _

/-- Every trigonometric value is bounded by the sup-norm: `|czTrig R t| ≤ czSup R`
for all `t ∈ [0, π]`. -/
theorem abs_czTrig_le_czSup (R : Polynomial ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Real.pi) :
    |czTrig R t| ≤ czSup R := by
  classical
  unfold czSup
  refine le_csSup ?hbdd ⟨t, ht, rfl⟩
  exact isCompact_Icc.bddAbove_image ((czTrig_continuous R).abs.continuousOn)

/-- **Szegő's differential inequality** (the crux; not available in Mathlib).
For a real polynomial `R` of degree `≤ β`, writing `M = czSup R` for the sup-norm
of the trigonometric transform on `[0, π]`,
`|d/dt czTrig R t| ≤ β · √(M² − (czTrig R t)²)`.

Equivalently, with `Q = czTrig R` one has `Q'(t)² + β² Q(t)² ≤ β² M²`.  This is the
sharp Bernstein/Szegő bound for trigonometric polynomials of degree `β`; it is the
only genuinely deep ingredient of the Ehlich–Zeller mesh inequality and must be
proved from the trigonometric-polynomial structure of `czTrig R` (e.g. via the
Riesz interpolation formula), *not* assumed. -/
theorem czTrig_szego_deriv (R : Polynomial ℝ) (β : ℕ) (hβ : R.natDegree ≤ β) (t : ℝ) :
    |deriv (czTrig R) t| ≤ (β : ℝ) * Real.sqrt ((czSup R) ^ 2 - (czTrig R t) ^ 2) := by
  let S : Polynomial ℝ := R.comp (-(Polynomial.X : Polynomial ℝ))
  have hS_eval (x : ℝ) : S.eval x = R.eval (-x) := by
    simp [S]
  have hS_degree : S.natDegree ≤ β := by
    calc
      S.natDegree ≤ R.natDegree * (-(Polynomial.X : Polynomial ℝ)).natDegree := by
        simpa [S] using
          (Polynomial.natDegree_comp_le (p := R) (q := -(Polynomial.X : Polynomial ℝ)))
      _ = R.natDegree := by simp
      _ ≤ β := hβ
  have hS_bound : ∀ u, |S.eval (Real.cos u)| ≤ czSup R := by
    intro u
    let v : ℝ := Real.arccos (Real.cos u)
    have hv : v ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.arccos_nonneg (Real.cos u), Real.arccos_le_pi (Real.cos u)⟩
    have hcos : Real.cos v = Real.cos u := by
      exact Real.cos_arccos (Real.neg_one_le_cos u) (Real.cos_le_one u)
    calc
      |S.eval (Real.cos u)| = |R.eval (-Real.cos u)| := by rw [hS_eval]
      _ = |czTrig R v| := by simp [czTrig, hcos]
      _ ≤ czSup R := abs_czTrig_le_czSup R hv
  have hsq :=
    Causalean.Mathlib.Analysis.BernsteinSzegoTrig.szego_deriv_sq_bound
      S β hS_degree (czSup R) hS_bound t
  have hsq' :
      (deriv (czTrig R) t) ^ 2 + (β : ℝ) ^ 2 * (czTrig R t) ^ 2
        ≤ (β : ℝ) ^ 2 * (czSup R) ^ 2 := by
    simpa [S, czTrig] using hsq
  by_cases hβ0 : β = 0
  · have hderiv_sq_nonpos : (deriv (czTrig R) t) ^ 2 ≤ 0 := by
      simpa [hβ0] using hsq'
    have hderiv_zero : deriv (czTrig R) t = 0 := by
      nlinarith [sq_nonneg (deriv (czTrig R) t)]
    simp [hβ0, hderiv_zero]
  · have hβpos : 0 < (β : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hβ0
    have hrad_nonneg : 0 ≤ (czSup R) ^ 2 - (czTrig R t) ^ 2 := by
      have hq_le : (β : ℝ) ^ 2 * (czTrig R t) ^ 2 ≤ (β : ℝ) ^ 2 * (czSup R) ^ 2 := by
        nlinarith [hsq', sq_nonneg (deriv (czTrig R) t)]
      have hβsq_pos : 0 < (β : ℝ) ^ 2 := sq_pos_of_pos hβpos
      nlinarith
    have hsq_bound :
        (deriv (czTrig R) t) ^ 2 ≤
          ((β : ℝ) * Real.sqrt ((czSup R) ^ 2 - (czTrig R t) ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hrad_nonneg]
      nlinarith [hsq']
    exact abs_le_of_sq_le_sq hsq_bound (by positivity)

private theorem czTrig_arccos_lipschitz_regularized (R : Polynomial ℝ) (β : ℕ)
    (hβ : R.natDegree ≤ β) {δ : ℝ} (hδ : 0 < δ) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 Real.pi) (ht : t ∈ Set.Icc 0 Real.pi) :
    |Real.arccos (czTrig R t / (czSup R + δ)) -
        Real.arccos (czTrig R s / (czSup R + δ))| ≤
      (β : ℝ) * |t - s| := by
  let M : ℝ := czSup R
  let d : ℝ := M + δ
  have hM_nonneg : 0 ≤ M := by simpa [M] using czSup_nonneg R
  have hdpos : 0 < d := by dsimp [d, M]; linarith
  let f : ℝ → ℝ := fun u => Real.arccos (czTrig R u / d)
  have hdiff_at (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
      DifferentiableAt ℝ f x := by
    have hq_abs : |czTrig R x| ≤ M := by simpa [M] using abs_czTrig_le_czSup R hx
    have hinner_abs : |czTrig R x / d| < 1 := by
      rw [abs_div, abs_of_pos hdpos]
      exact (div_lt_one hdpos).2 (by dsimp [d, M]; linarith)
    have hne_neg : czTrig R x / d ≠ -1 := by
      intro h
      have : |czTrig R x / d| = 1 := by simp [h]
      linarith
    have hne_pos : czTrig R x / d ≠ 1 := by
      intro h
      have : |czTrig R x / d| = 1 := by simp [h]
      linarith
    have hinner_diff : DifferentiableAt ℝ (fun u => czTrig R u / d) x := by
      unfold czTrig
      fun_prop
    exact ((Real.hasDerivAt_arccos hne_neg hne_pos).comp x
      (DifferentiableAt.hasDerivAt hinner_diff)).differentiableAt
  have hderiv_bound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
      ‖deriv f x‖ ≤ (β : ℝ) := by
    have hq_abs : |czTrig R x| ≤ M := by simpa [M] using abs_czTrig_le_czSup R hx
    have hinner_abs : |czTrig R x / d| < 1 := by
      rw [abs_div, abs_of_pos hdpos]
      exact (div_lt_one hdpos).2 (by dsimp [d, M]; linarith)
    have hinner_sq_lt : (czTrig R x / d) ^ 2 < 1 := by
      simpa using (sq_lt_one_iff_abs_lt_one (czTrig R x / d)).2 hinner_abs
    have hinner_pos : 0 < 1 - (czTrig R x / d) ^ 2 := by linarith
    have hinner_nonneg : 0 ≤ 1 - (czTrig R x / d) ^ 2 := hinner_pos.le
    have hne_neg : czTrig R x / d ≠ -1 := by
      intro h
      have : |czTrig R x / d| = 1 := by simp [h]
      linarith
    have hne_pos : czTrig R x / d ≠ 1 := by
      intro h
      have : |czTrig R x / d| = 1 := by simp [h]
      linarith
    have hinner_diff : DifferentiableAt ℝ (fun u => czTrig R u / d) x := by
      unfold czTrig
      fun_prop
    have hcz_diff : DifferentiableAt ℝ (czTrig R) x := by
      unfold czTrig
      fun_prop
    have hinner_hasDeriv :
        HasDerivAt (fun u => czTrig R u / d) (deriv (czTrig R) x / d) x :=
      (DifferentiableAt.hasDerivAt hcz_diff).div_const d
    have hf_hasDeriv :
        HasDerivAt f
          (-(1 / Real.sqrt (1 - (czTrig R x / d) ^ 2)) *
            (deriv (czTrig R) x / d)) x := by
      simpa [f] using (Real.hasDerivAt_arccos hne_neg hne_pos).comp x hinner_hasDeriv
    have hderiv_eq :
        deriv f x =
          -(1 / Real.sqrt (1 - (czTrig R x / d) ^ 2)) *
            (deriv (czTrig R) x / d) :=
      hf_hasDeriv.deriv
    have hsqrtd_pos : 0 < Real.sqrt (1 - (czTrig R x / d) ^ 2) :=
      Real.sqrt_pos_of_pos hinner_pos
    have hden_eq :
        d * Real.sqrt (1 - (czTrig R x / d) ^ 2) =
          Real.sqrt (d ^ 2 - (czTrig R x) ^ 2) := by
      apply (sq_eq_sq₀
        (mul_nonneg hdpos.le (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt hinner_nonneg]
      have hdiff_nonneg : 0 ≤ d ^ 2 - (czTrig R x) ^ 2 := by
        have hlt : |czTrig R x| < d := by dsimp [d, M]; linarith
        have hsq_lt : (czTrig R x) ^ 2 < d ^ 2 := by
          have hlt_abs : |czTrig R x| < |d| := by simpa [abs_of_pos hdpos] using hlt
          exact (sq_lt_sq (a := czTrig R x) (b := d)).2 hlt_abs
        linarith
      rw [Real.sq_sqrt hdiff_nonneg]
      field_simp [ne_of_gt hdpos]
    have hderiv_abs :
        |deriv f x| =
          |deriv (czTrig R) x| /
            (d * Real.sqrt (1 - (czTrig R x / d) ^ 2)) := by
      rw [hderiv_eq, abs_mul, abs_neg, abs_div, abs_one, abs_of_pos hsqrtd_pos,
        abs_div, abs_of_pos hdpos]
      field_simp [ne_of_gt hsqrtd_pos, ne_of_gt hdpos]
    have hrad_le :
        Real.sqrt (M ^ 2 - (czTrig R x) ^ 2) ≤
          d * Real.sqrt (1 - (czTrig R x / d) ^ 2) := by
      rw [hden_eq]
      apply Real.sqrt_le_sqrt
      dsimp [d]
      nlinarith [hM_nonneg, hδ]
    have hnum_le :
        |deriv (czTrig R) x| ≤
          (β : ℝ) * (d * Real.sqrt (1 - (czTrig R x / d) ^ 2)) :=
      (czTrig_szego_deriv R β hβ x).trans
        (mul_le_mul_of_nonneg_left hrad_le (by positivity))
    have hden_pos : 0 < d * Real.sqrt (1 - (czTrig R x / d) ^ 2) :=
      mul_pos hdpos hsqrtd_pos
    rw [Real.norm_eq_abs, hderiv_abs]
    exact (div_le_iff₀ hden_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hnum_le)
  have hmv :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (f := f) (s := Set.Icc (0 : ℝ) Real.pi) (C := (β : ℝ))
      hdiff_at hderiv_bound (convex_Icc (0 : ℝ) Real.pi) hs ht
  simpa [f, d, M, Real.norm_eq_abs, abs_sub_comm] using hmv

/-- **Arccos-Lipschitz reformulation of Szegő's inequality.**  For a polynomial
`R` of degree `≤ β` with positive sup-norm `M = czSup R`, the composite
`t ↦ arccos (czTrig R t / M)` is `β`-Lipschitz on `[0, π]`:
`|arccos(Q(t)/M) − arccos(Q(s)/M)| ≤ β · |t − s|`.

This follows from `czTrig_szego_deriv`: on the open region where `|Q| < M` the
derivative of `arccos (Q/M)` has magnitude `|Q'| / √(M² − Q²) ≤ β`, and the
mean-value boundary lemma extends the Lipschitz estimate across the points where
`Q = ±M`. -/
theorem czTrig_arccos_lipschitz (R : Polynomial ℝ) (β : ℕ) (hβ : R.natDegree ≤ β)
    (hM : 0 < czSup R) {s t : ℝ} (hs : s ∈ Set.Icc 0 Real.pi) (ht : t ∈ Set.Icc 0 Real.pi) :
    |Real.arccos (czTrig R t / czSup R) - Real.arccos (czTrig R s / czSup R)|
      ≤ (β : ℝ) * |t - s| := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let lhsε : ℕ → ℝ := fun n =>
    |Real.arccos (czTrig R t / (czSup R + ε n)) -
      Real.arccos (czTrig R s / (czSup R + ε n))|
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hineq : ∀ n, lhsε n ≤ (β : ℝ) * |t - s| := by
    intro n
    simpa [lhsε, ε] using
      czTrig_arccos_lipschitz_regularized R β hβ (hδ := hεpos n) hs ht
  have hε_tendsto : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa [ε, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht_arg_tendsto :
      Filter.Tendsto (fun n => czTrig R t / (czSup R + ε n)) Filter.atTop
        (nhds (czTrig R t / czSup R)) := by
    simpa using
      (tendsto_const_nhds.div (tendsto_const_nhds.add hε_tendsto)
        (show czSup R + 0 ≠ 0 by simpa using ne_of_gt hM))
  have hs_arg_tendsto :
      Filter.Tendsto (fun n => czTrig R s / (czSup R + ε n)) Filter.atTop
        (nhds (czTrig R s / czSup R)) := by
    simpa using
      (tendsto_const_nhds.div (tendsto_const_nhds.add hε_tendsto)
        (show czSup R + 0 ≠ 0 by simpa using ne_of_gt hM))
  have ht_acos_tendsto :
      Filter.Tendsto (fun n => Real.arccos (czTrig R t / (czSup R + ε n))) Filter.atTop
        (nhds (Real.arccos (czTrig R t / czSup R))) :=
    Real.continuous_arccos.tendsto _ |>.comp ht_arg_tendsto
  have hs_acos_tendsto :
      Filter.Tendsto (fun n => Real.arccos (czTrig R s / (czSup R + ε n))) Filter.atTop
        (nhds (Real.arccos (czTrig R s / czSup R))) :=
    Real.continuous_arccos.tendsto _ |>.comp hs_arg_tendsto
  have hlhs_tendsto :
      Filter.Tendsto lhsε Filter.atTop
        (nhds |Real.arccos (czTrig R t / czSup R) -
          Real.arccos (czTrig R s / czSup R)|) := by
    simpa [lhsε, Real.norm_eq_abs] using (ht_acos_tendsto.sub hs_acos_tendsto).norm
  exact le_of_tendsto_of_tendsto hlhs_tendsto tendsto_const_nhds
    (Filter.Eventually.of_forall hineq)

/-- **Maximizer node bound** (the packaged output consumed by the mesh file).
Suppose `R` has degree `≤ β`, its trigonometric sup-norm `M = czSup R` is positive,
`t₀ ∈ [0, π]` is a maximizer with `czTrig R t₀ = M`, `s ∈ [0, π]` is another point,
and `β·|t₀ − s| ≤ π/2`.  Then `M · cos(β·|t₀ − s|) ≤ czTrig R s`.

Proof sketch: put `φ(u) = arccos(czTrig R u / M)`.  Then `φ(t₀) = arccos 1 = 0`,
and by `czTrig_arccos_lipschitz`, `φ(s) = |φ(s) − φ(t₀)| ≤ β·|t₀ − s|`.  Since
`β·|t₀ − s| ≤ π/2` and `cos` is antitone on `[0, π]`, taking `cos` gives
`czTrig R s / M = cos(φ(s)) ≥ cos(β·|t₀ − s|)`, whence the claim.  (The sign case
`czTrig R t₀ = -M` is handled by the mesh file by replacing `R` with `-R`.) -/
theorem czTrig_maximizer_bound (R : Polynomial ℝ) (β : ℕ) (hβ : R.natDegree ≤ β)
    (hM : 0 < czSup R) {t₀ s : ℝ} (ht₀ : t₀ ∈ Set.Icc 0 Real.pi) (hs : s ∈ Set.Icc 0 Real.pi)
    (hmax : czTrig R t₀ = czSup R) (hclose : (β : ℝ) * |t₀ - s| ≤ Real.pi / 2) :
    czSup R * Real.cos ((β : ℝ) * |t₀ - s|) ≤ czTrig R s := by
  let φ : ℝ → ℝ := fun u => Real.arccos (czTrig R u / czSup R)
  have hφt₀ : φ t₀ = 0 := by
    unfold φ
    rw [hmax]
    rw [div_self (ne_of_gt hM)]
    exact Real.arccos_one
  have hLip := czTrig_arccos_lipschitz R β hβ hM ht₀ hs
  have hLip' : |φ s - φ t₀| ≤ (β : ℝ) * |s - t₀| := by
    simpa [φ] using hLip
  have hφs_le : φ s ≤ (β : ℝ) * |t₀ - s| := by
    have hnonneg : 0 ≤ φ s := by
      unfold φ
      exact Real.arccos_nonneg _
    rw [hφt₀, sub_zero, abs_of_nonneg hnonneg] at hLip'
    rwa [abs_sub_comm] at hLip'
  have hx_le_pi : (β : ℝ) * |t₀ - s| ≤ Real.pi := by
    linarith [Real.pi_nonneg]
  have hcos_le : Real.cos ((β : ℝ) * |t₀ - s|) ≤ Real.cos (φ s) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (by unfold φ; exact Real.arccos_nonneg _) hx_le_pi hφs_le
  have hratio_abs : |czTrig R s / czSup R| ≤ 1 := by
    rw [abs_div, abs_of_pos hM]
    exact (div_le_one hM).2 (abs_czTrig_le_czSup R hs)
  have hcosφ : Real.cos (φ s) = czTrig R s / czSup R := by
    unfold φ
    exact Real.cos_arccos (abs_le.mp hratio_abs).1 (abs_le.mp hratio_abs).2
  have hmul := mul_le_mul_of_nonneg_left (hcos_le.trans_eq hcosφ) hM.le
  calc
    czSup R * Real.cos ((β : ℝ) * |t₀ - s|)
        ≤ czSup R * (czTrig R s / czSup R) := hmul
    _ = czTrig R s := by field_simp [ne_of_gt hM]

end Causalean.Mathlib.Analysis.EhlichZellerMesh
