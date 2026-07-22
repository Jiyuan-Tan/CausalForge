/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Confidence-region geometry for scalar interval data (Beresteanu–Molinari 2008, §2)

Beresteanu & Molinari (2008) build confidence regions for a partially identified
parameter whose identified set is the interval `E[Y] = [μL, μU]`.  Their estimator
is the sample-mean interval `Ȳₙ = [yl, yu]`, and the confidence region is the
**Minkowski dilation**

    Uₙ = Ȳₙ ⊕ B(0, r),     r = ĉ / √n,

a ball of radius `r` around every point of `Ȳₙ`.  Coverage of the population set is
governed by the Hausdorff geometry of `Hausdorff.lean`: BM Proposition 2.7 says the
population set sits inside the dilated estimate exactly when the (directed) Hausdorff
distance is within the radius.  This file records that purely-geometric core for the
scalar interval case, together with a CLT-based coverage corollary tying the event
`{E[Y] ⊆ Uₙ}` to the statistic `√n · dᴴ(E[Y], Ȳₙ)` whose limit law is
`interval_data_clt` (`IntervalCLT.lean`).

## Main definitions

* `dilate A r` — the Minkowski dilation `A ⊕ [−r, r]`.

## Main results

* `dilate_Icc` — `[a,b] ⊕ [−r,r] = [a−r, b+r]` for `r ≥ 0` (BM `Uₙ`).
* `subset_dilate_iff_directedHausdorff_le` — **BM Prop 2.7 core**: the population
  interval is covered by the dilated estimate iff `dᴴ(E[Y], Ȳₙ) ≤ r`.
* `subset_dilate_iff_hausdorff_le` — symmetric (two-sided) version via `hausdorffDist`.
* `coverage_event_eq` — **coverage corollary**: with `r = ĉ/√n` (`n ≥ 1`, `ĉ ≥ 0`)
  the event `{E[Y] ⊆ Uₙ}` equals `{√n · dᴴ(E[Y], Ȳₙ) ≤ ĉ}`, so the coverage
  probability is `μ {√n · d ≤ ĉ}`. This file proves the deterministic event
  reduction; a separate probabilistic theorem would combine it with
  `interval_data_clt` and a quantile-continuity argument.
-/

import Causalean.PO.ID.Partial.RandomSet.Hausdorff
import Causalean.PO.ID.Partial.RandomSet.IntervalCLT

/-! # Confidence Regions for Scalar Interval Data

This file gives the deterministic geometry behind confidence regions for an
interval identified set estimated by a sample-mean interval. It characterizes
Minkowski dilations of intervals and relates coverage of the population interval
to directed Hausdorff distance and the scalar interval-data central limit
theorem.

Main declarations:
* `dilate` is Minkowski dilation by `[-r,r]`, and `dilate_Icc` computes it for
  closed intervals.
* `subset_dilate_iff_directedHausdorff_le` is the one-sided coverage geometry
  for Beresteanu-Molinari confidence regions.
* `subset_dilate_iff_hausdorff_le` is the symmetric two-sided analogue.
* `coverage_event_eq` rewrites the random coverage event as an event on
  `sqrt n * directedHausdorff`.
* `dirStat`, `normalizedSum_dirStat_clt`, `dirStat_normalizedSum_eq`, and
  `directedRegion_coverage` provide the directed CLT and asymptotic coverage
  theorem.
-/

namespace Causalean.PartialID.RandomSet

/-- **Minkowski dilation** of a real set by a radius `r`:
`A ⊕ [−r, r] = {a + t | a ∈ A, |t| ≤ r}`.  In Beresteanu–Molinari this is the
confidence region `Uₙ = Ȳₙ ⊕ B(0, r)` built around the estimated interval. -/
def dilate (A : Set ℝ) (r : ℝ) : Set ℝ :=
  {x : ℝ | ∃ a ∈ A, ∃ t : ℝ, |t| ≤ r ∧ x = a + t}

/-- **Dilation of an interval** (Beresteanu–Molinari `Uₙ`).  For `r ≥ 0`,
`[a,b] ⊕ [−r,r] = [a−r, b+r]`: every endpoint is pushed out by the radius. -/
theorem dilate_Icc {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) :
    dilate (Set.Icc a b) r = Set.Icc (a - r) (b + r) := by
  ext x
  constructor
  · rintro ⟨a', ⟨ha1, ha2⟩, t, ht, rfl⟩
    rw [abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rintro ⟨hx1, hx2⟩
    -- clamp the chosen point of `[a,b]` to be `max a (min x b)`
    rcases le_total x a with hxa | hax
    · -- x ≤ a: pick a' = a, t = x − a ∈ [−r, 0]
      refine ⟨a, ⟨le_rfl, hab⟩, x - a, ?_, by ring⟩
      rw [abs_le]; constructor <;> linarith
    · rcases le_total x b with hxb | hbx
      · -- a ≤ x ≤ b: pick a' = x, t = 0
        exact ⟨x, ⟨hax, hxb⟩, 0, by simpa using hr, by ring⟩
      · -- x ≥ b: pick a' = b, t = x − b ∈ [0, r]
        refine ⟨b, ⟨hab, le_rfl⟩, x - b, ?_, by ring⟩
        rw [abs_le]; constructor <;> linarith

/-- **Coverage characterization (Beresteanu–Molinari Proposition 2.7 core).**  The
population identified interval `[μL, μU]` lies inside the dilated estimate
`[yl, yu] ⊕ [−r, r]` iff the *directed* Hausdorff distance `dᴴ([μL,μU], [yl,yu])`
is at most the radius `r`.  This is the one-sided coverage event of the BM
confidence region. -/
theorem subset_dilate_iff_directedHausdorff_le {μL μU yl yu r : ℝ}
    (hμ : μL ≤ μU) (hy : yl ≤ yu) (hr : 0 ≤ r) :
    Set.Icc μL μU ⊆ dilate (Set.Icc yl yu) r
      ↔ directedHausdorff (Set.Icc μL μU) (Set.Icc yl yu) ≤ r := by
  rw [dilate_Icc hy hr, Set.Icc_subset_Icc_iff hμ,
    directedHausdorff_Icc hμ hy, max_le_iff, max_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hr, by linarith [h1], by linarith [h2]⟩
  · rintro ⟨_, h1, h2⟩
    exact ⟨by linarith [h1], by linarith [h2]⟩

/-- **Symmetric (two-sided) coverage characterization (Beresteanu–Molinari `Uₙ` /
Theorem 2.4).**  Each interval lies inside the other's dilation by `r` iff the
*symmetric* Hausdorff distance `H([μL,μU], [yl,yu])` is at most `r`.  The mutual
containment `[μL,μU] ⊆ Uᵧ ∧ [yl,yu] ⊆ Uᵤ` is exactly the two-sided event
`H ≤ r`. -/
theorem subset_dilate_iff_hausdorff_le {μL μU yl yu r : ℝ}
    (hμ : μL ≤ μU) (hy : yl ≤ yu) (hr : 0 ≤ r) :
    (Set.Icc μL μU ⊆ dilate (Set.Icc yl yu) r
        ∧ Set.Icc yl yu ⊆ dilate (Set.Icc μL μU) r)
      ↔ hausdorffDist (Set.Icc μL μU) (Set.Icc yl yu) ≤ r := by
  rw [subset_dilate_iff_directedHausdorff_le hμ hy hr,
    subset_dilate_iff_directedHausdorff_le hy hμ hr, hausdorffDist, max_le_iff]

/-! ## Coverage corollary tied to the interval-data CLT

We now connect the deterministic geometry to the random estimate `Ȳₙ(ω)` and the
BM bandwidth `r = ĉ/√n`.  The pointwise event `{E[Y] ⊆ Uₙ}` is, for `n ≥ 1` and
`ĉ ≥ 0`, exactly the event on the Hausdorff statistic appearing in
`interval_data_clt`. -/

open MeasureTheory

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- **Coverage event identity (Beresteanu–Molinari coverage corollary).**  Fix the
population identified interval `E[Y] = [μL, μU]`, the sample-mean interval
`Ȳₙ(ω) = [yl(ω), yu(ω)]`, sample size `n ≥ 1`, and critical value `ĉ ≥ 0`.  With the
BM bandwidth `r = ĉ/√n`, the (one-sided) coverage event `{E[Y] ⊆ Uₙ}` equals the
event `{√n · dᴴ(E[Y], Ȳₙ) ≤ ĉ}` on the directed Hausdorff statistic.  Hence the
coverage probability is `μ {ω | √n · dᴴ(E[Y], Ȳₙ(ω)) ≤ ĉ}`.

The asymptotic guarantee `μ {coverage} → 1 − α` is not stated here; it would use
`interval_data_clt` (the limit law of `√n · H(Ȳₙ, E[Y])`) together with a
portmanteau / continuity-of-quantile step choosing `ĉ` as the `(1−α)`-quantile of
the limit `(gaussianLimit ψ).map maxAbs`. This lemma supplies the exact event
reduction that such a theorem would consume. -/
theorem coverage_event_eq
    (μL μU : ℝ) (yl yu : Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c)
    (hμ : μL ≤ μU) (hy : ∀ ω, yl ω ≤ yu ω) :
    {ω | Set.Icc μL μU ⊆ dilate (Set.Icc (yl ω) (yu ω)) (c / Real.sqrt n)}
      = {ω | Real.sqrt n * directedHausdorff (Set.Icc μL μU) (Set.Icc (yl ω) (yu ω)) ≤ c} := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hr : 0 ≤ c / Real.sqrt n := div_nonneg hc (Real.sqrt_nonneg _)
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [subset_dilate_iff_directedHausdorff_le hμ (hy ω) hr]
  constructor
  · intro h
    rw [le_div_iff₀ hsqrt_pos] at h
    rw [mul_comm]; exact h
  · intro h
    rw [le_div_iff₀ hsqrt_pos, mul_comm]
    exact h

/-! ## The directed-Hausdorff statistic and its CLT

We now establish the limit law of the one-sided statistic `√n · dᴴ(E[Y], Ȳₙ)`
underlying the coverage event above, as a continuous-mapping image of the
multivariate CLT through `dirStat w = max 0 (max w₀ (−w₁))`. -/

open ProbabilityTheory Filter Topology Causalean.Stat

/-- The **directed-Hausdorff functional** `dirStat w = max 0 (max w₀ (−w₁))` on `ℝ²`.
On the centered endpoint normalised sum it is `√n · dᴴ(E[Y], Ȳₙ)`. -/
noncomputable def dirStat (w : EuclideanSpace ℝ (Fin 2)) : ℝ := max 0 (max (w 0) (-(w 1)))

/-- The directed-Hausdorff endpoint functional is continuous. -/
lemma continuous_dirStat : Continuous dirStat := by unfold dirStat; fun_prop

/-- The directed-Hausdorff endpoint functional is measurable. -/
lemma measurable_dirStat : Measurable dirStat := continuous_dirStat.measurable

section DirectedCLT

variable {ψ : X → EuclideanSpace ℝ (Fin 2)} (hψ : Measurable ψ)
  (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)

/-- The directed limit law is a probability measure. -/
instance : IsProbabilityMeasure ((gaussianLimit hψ hvar).map dirStat) :=
  Measure.isProbabilityMeasure_map measurable_dirStat.aemeasurable

/-- **Directed continuous-mapping CLT.**  `dirStat` of the vector normalised sum
converges in distribution to `(gaussianLimit ψ).map dirStat`. -/
theorem normalizedSum_dirStat_clt (S : IIDSample Ω X μ P)
    (hψ_int : Integrable ψ P) (hmean : ∫ x, ψ x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n) μ) :
    Tendsto_dist_vec
      (fun n ω => dirStat (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n ω))
      ((gaussianLimit hψ hvar).map dirStat) μ
      (fun n => measurable_dirStat.comp_aemeasurable (hSum_meas n)) :=
  Tendsto_dist_vec.map_continuous continuous_dirStat hSum_meas
    (fun n => measurable_dirStat.comp_aemeasurable (hSum_meas n))
    (S.clt_normalizedSum_vec hψ hvar hψ_int hmean hSum_meas)

end DirectedCLT

/-- Both coordinates of the vector normalised sum of `intervalIFVec` are
`√n · (sample mean − population mean)`. -/
private lemma nsCoord (S : IIDSample Ω X μ P) (yL yU : X → ℝ) (n : ℕ) (ω : Ω) :
    (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω) 0
        = Real.sqrt n * (sampleMean S yL n ω - ∫ x, yL x ∂P)
      ∧ (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω) 1
        = Real.sqrt n * (sampleMean S yU n ω - ∫ x, yU x ∂P) := by
  constructor
  · change ((EuclideanSpace.equiv (Fin 2) ℝ)
      (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω)) 0 = _
    unfold IsAsymLinearVec.normalizedSum intervalIFVec eucl₂
    rw [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply, Matrix.cons_val_zero, smul_eq_mul,
      Finset.card_range]
    rw [show (∑ i ∈ Finset.range n, (yL (S.Z i ω) - ∫ x, yL x ∂P))
          = (∑ i ∈ Finset.range n, yL (S.Z i ω)) - n * (∫ x, yL x ∂P) by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul],
      sqrt_inv_centered]
    simp only [sampleMean]
  · change ((EuclideanSpace.equiv (Fin 2) ℝ)
      (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω)) 1 = _
    unfold IsAsymLinearVec.normalizedSum intervalIFVec eucl₂
    rw [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      smul_eq_mul, Finset.card_range]
    rw [show (∑ i ∈ Finset.range n, (yU (S.Z i ω) - ∫ x, yU x ∂P))
          = (∑ i ∈ Finset.range n, yU (S.Z i ω)) - n * (∫ x, yU x ∂P) by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul],
      sqrt_inv_centered]
    simp only [sampleMean]

/-- **Directed Hausdorff bridge.**  `dirStat` of the centered endpoint normalised
sum equals `√n · dᴴ(E[Y], Ȳₙ)`. -/
theorem dirStat_normalizedSum_eq (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLU : ∀ z, yL z ≤ yU z) (hLint : Integrable yL P) (hUint : Integrable yU P)
    (n : ℕ) (ω : Ω) :
    dirStat (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n ω)
      = Real.sqrt n * directedHausdorff
          (Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P))
          (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω)) := by
  obtain ⟨h0, h1⟩ := nsCoord S yL yU n ω
  unfold dirStat
  rw [h0, h1,
    show -(Real.sqrt n * (sampleMean S yU n ω - ∫ x, yU x ∂P))
        = Real.sqrt n * ((∫ x, yU x ∂P) - sampleMean S yU n ω) by ring,
    ← mul_max_of_nonneg _ _ (Real.sqrt_nonneg (n : ℝ)),
    show (0 : ℝ) = Real.sqrt n * 0 by ring,
    ← mul_max_of_nonneg _ _ (Real.sqrt_nonneg (n : ℝ)),
    directedHausdorff_Icc (integral_mono hLint hUint hLU) (sampleMean_le S yL yU hLU n ω)]

/-! ## Asymptotic coverage of the directed confidence region (Beresteanu–Molinari Prop 2.7) -/

/-- **Asymptotic coverage of the directed confidence region.**  With population
identified interval `E[Y] = [E y_L, E y_U]`, sample-mean interval `Ȳₙ`, and the BM
bandwidth `c/√n`, the coverage probability of the *whole* identified set converges
to the limit-law mass of `(-∞, c]`:

    μ { E[Y] ⊆ Ȳₙ ⊕ B(0, c/√n) }  →  L(−∞, c],

where `L = (gaussianLimit ψ).map dirStat` is the law of
`max(0, max z_L (-z_U))`, so the upper endpoint enters with the opposite sign.
Choosing `c` as the `(1−α)`-quantile of `L` (a continuity point, so `L{c} = 0`)
gives the asymptotic `1 − α` coverage of Proposition 2.7.  Proof: the coverage
event is `{√n · dᴴ(E[Y], Ȳₙ) ≤ c} = {dirStat(normalised sum) ≤ c}` (eventually, via
`coverage_event_eq` + the directed bridge), and the directed CLT
(`normalizedSum_dirStat_clt`) feeds the portmanteau theorem on the closed half-line
`Iic c` (frontier `{c}` null by `hfront`). -/
theorem directedRegion_coverage (S : IIDSample Ω X μ P) (yL yU : X → ℝ)
    (hLU : ∀ z, yL z ≤ yU z) (hLint : Integrable yL P) (hUint : Integrable yU P)
    (hψ : Measurable (intervalIFVec yL yU P))
    (hvar : Integrable (fun x => ‖intervalIFVec yL yU P x‖ ^ 2) P)
    (hψ_int : Integrable (intervalIFVec yL yU P) P)
    (hmean : ∫ x, intervalIFVec yL yU P x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P) (fun m => Finset.range m) n) μ)
    {c : ℝ} (hc : 0 ≤ c)
    (hfront : ((gaussianLimit hψ hvar).map dirStat) {c} = 0) :
    Tendsto (fun n => μ {ω | Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P)
        ⊆ dilate (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω)) (c / Real.sqrt n)})
      atTop (𝓝 (((gaussianLimit hψ hvar).map dirStat) (Set.Iic c))) := by
  have hclt := normalizedSum_dirStat_clt hψ hvar S hψ_int hmean hSum_meas
  unfold Tendsto_dist_vec at hclt
  have hport := MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hclt (E := Set.Iic c) (by rw [frontier_Iic]; exact hfront)
  refine hport.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  -- the per-`n` coverage probability equals the CDF value of the directed statistic
  have hmap : (μ.map (dirStat ∘ IsAsymLinearVec.normalizedSum S (intervalIFVec yL yU P)
        (fun m => Finset.range m) n)) (Set.Iic c)
      = μ {ω | Set.Icc (∫ x, yL x ∂P) (∫ x, yU x ∂P)
        ⊆ dilate (Set.Icc (sampleMean S yL n ω) (sampleMean S yU n ω)) (c / Real.sqrt n)} := by
    rw [Measure.map_apply_of_aemeasurable
        (measurable_dirStat.comp_aemeasurable (hSum_meas n)) measurableSet_Iic,
      coverage_event_eq (∫ x, yL x ∂P) (∫ x, yU x ∂P)
        (fun ω => sampleMean S yL n ω) (fun ω => sampleMean S yU n ω) n hn c hc
        (integral_mono hLint hUint hLU) (fun ω => sampleMean_le S yL yU hLU n ω)]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Function.comp_apply, Set.mem_setOf_eq,
      dirStat_normalizedSum_eq S yL yU hLU hLint hUint n ω]
  exact hmap

end Causalean.PartialID.RandomSet
