/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bridge: bounded loss + Rademacher complexity ⇒ `LocalEmpProcessModulus`

This bridge discharges the `LocalEmpProcessModulus` hypothesis used by
`OrthogonalLearning/OracleInequality.lean` from concrete data-generating
assumptions. No upstream code lives here; this file consumes the
`Causalean.Stat.Concentration.{Rademacher, BoundedDifference, McDiarmid,
Symmetrization, Separable}` headlines together with the orthogonal
statistical-learning oracle-inequality predicate.

## Output

Under
* a uniform bound `|ℓ z θ g| ≤ b` for `θ ∈ Θ_set`,
* a population Rademacher-complexity bound `R_n` for the centred loss
  class `{z ↦ ℓ z θ g − ℓ z θ₀ g : θ ∈ Θ_set}` measured on the estimation
  fold,
* countability / separability of `Θ_set` (handled via
  `Causalean.Stat.Concentration.Separable`),

we conclude `LocalEmpProcessModulus S S_iid split ρ δ g` with
`ρ n := √(2 R_n + 2b * Real.sqrt (2 * Real.log (1 / δ) / |B(n)|))`
when the estimation fold is nonempty, and the boundary value
`ρ n := √(2b)` when `|B(n)| = 0`.

Only the constant slot `(ρ n)^2` is filled — the `ρ n * ‖θ − θ₀‖` slot
of the modulus inequality is satisfied by the trivial monotonicity
`ρ n * ‖θ − θ₀‖ ≥ 0`.  This is a deliberate, non-localized realisation:
sharper localized rates (Foster–Syrgkanis Lemma 29) live in the sibling
file `OrthogonalLearning/LocalEmpProcess/Localized.lean`.

## Headline schema

```
theorem localEmpProcessModulus_of_bounded_rademacher
    (S : LearningSystem Ω μ Z P_Z Θ G) (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid) {b : ℝ} (hb : 0 ≤ b)
    (g : G) (hg_bdd : ∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g| ≤ b)
    (R : ℕ → ℝ) (hR : RademacherBound S S_iid split g R)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun n => Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ g
```
-/

import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Local
import Causalean.Stat.Concentration.Rademacher.Rademacher
import Causalean.Stat.Concentration.UniformDeviation.BoundedDifference
import Causalean.Stat.Concentration.TailBounds.McDiarmid
import Causalean.Stat.Concentration.Rademacher.Symmetrization
import Causalean.Stat.Concentration.Covering.Separable
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
import Mathlib.Topology.Bases
import FoML.Main

/-! # Global Rademacher Modulus

This file derives `LocalEmpProcessModulus` for an orthogonal statistical-learning
system from global Rademacher-complexity control. `RademacherBound` records the
fold-B complexity bound on a countable dense sequence, while
`UniformlyBoundedLoss`, `UniformlyBoundedLossAE`, and `LossContinuousOnΘset`
package the boundedness and continuity hypotheses used to lift the countable
supremum to `Θ_set`. The bridge theorems
`localEmpProcessModulus_of_bounded_rademacher` and
`localEmpProcessModulus_of_bounded_rademacher_ae` produce the modulus from
pointwise or a.e. bounded losses, and `localEmpProcessModulus_singleton` covers
the degenerate singleton target class.
-/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Causalean.Stat
  Causalean.Stat.Concentration

/-! ## Helper: re-export of `oneShot_iid` for modulus bridges.

`oneShot_iid` lives in `Stat/FoldBEmpiricalProcess.lean` (sibling fold-B
helpers). It states that the joint law of the fold-B subsample matches
`Measure.pi` of the population law `P_Z`. We wrap it here as a public
alias so the bridge can cite it without reaching into the sibling file's
privacy. -/
section FoldBJointLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {X : Type*} [MeasurableSpace X] {P : MeasureTheory.Measure X}

/-- **Fold-B joint-law identification (public alias).**

The joint distribution of the fold-B subsample
`ω ↦ (i ↦ S.Z i ω)` (indexed by `i ∈ split.foldB n`) under `μ` equals the
product `Measure.pi (fun _ ↦ P)`.  This is the bridge consumed by the
McDiarmid + symmetrization chain to transport its `μⁿ`-on-`Fin n`
conclusions to the actual fold-B sample. -/
lemma foldB_pi_law [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (split : OneShotSplit S) (n : ℕ) :
    μ.map (fun ω (i : split.foldB n) => S.Z i ω) =
      Measure.pi (fun _ : split.foldB n => P) :=
  Causalean.Stat.oneShot_iid S split n

end FoldBJointLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- **Rademacher-complexity bound on the centred loss class on fold B,
indexed by a countable dense sequence in `S.Θ_set`.**

For a fixed nuisance `g`, the population Rademacher complexity of the
*countable* centred class
`{z ↦ ℓ z (denseSeq S.Θ_set k) g − ℓ z S.θ₀ g : k ∈ ℕ}`, evaluated on a
sample of size `(split.foldB n).card` drawn from the population law
`P_Z`, is at most `R n`.

Stated over the countable index `ℕ` (rather than the full `S.Θ_set`)
because FoML's `expectation_le_rademacher` and `mcdiarmid_inequality_pos'`
require a countable index — and `S.Θ_set` itself is not countable in
general.  The bridge theorem
`localEmpProcessModulus_of_bounded_rademacher` lifts the FoML conclusion
on `ℕ` to a uniform bound over `↥S.Θ_set` via
`separableSpaceSup_eq_real`, using continuity of the loss in `θ` and
separability of `S.Θ_set`.

The countable index `idx` is required because FoML's
`expectation_le_rademacher` consumes a countable index. Equivalence with the
un-lifted full-set Rademacher complexity holds only when `idx` has dense
range and, for each `z`, `S.ℓ z · g` is continuous in `θ` on `S.Θ_set`
with the subspace topology inherited from the normed structure on `Θ`.
Thus `idx_dense` is the user's explicit separability witness. See
`rademacherComplexity_eq_denseRange` for the dense-range helper used in this
file.

Independence of the fold-B block under `μ` ensures the value of
`rademacherComplexity` over `Z 0` equals the population Rademacher
complexity of the actual fold-B sample (cf. `foldB_pi_law`). -/
def RademacherBound
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (g : G) (idx : ℕ → S.Θ_set) (R : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ R n ∧
    rademacherComplexity (split.foldB n).card
      (fun (k : ℕ) z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
      μ (S_iid.Z 0) ≤ R n

/-- **Loss bounded uniformly over `Θ_set` at fixed nuisance `g`.** -/
def UniformlyBoundedLoss
    (S : LearningSystem Ω μ Z P_Z Θ G) (g : G) (b : ℝ) : Prop :=
  ∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g| ≤ b

/-- **Loss bounded uniformly over `Θ_set` at fixed nuisance `g`, almost everywhere.**

This is the satisfiable bounded-loss hypothesis for real-valued outcomes with
unbounded support: the bound only has to hold under the population law. -/
def UniformlyBoundedLossAE
    (S : LearningSystem Ω μ Z P_Z Θ G) (g : G) (b : ℝ) : Prop :=
  ∀ᵐ z ∂P_Z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g| ≤ b

/-- **Loss continuous in θ on `Θ_set` (for each `z` and fixed nuisance `g`).**

Used by the bridge theorem for the countable-dense lifting via
`separableSpaceSup_eq_real`.  The subtype `↥S.Θ_set` carries the
subspace topology inherited from `Θ`'s normed structure. -/
def LossContinuousOnΘset
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (g : G) : Prop :=
  ∀ z, Continuous (fun (θ : S.Θ_set) => S.ℓ z θ.val g)

private lemma separableSup_via_denseRange
    {X : Type*} [TopologicalSpace X] [Nonempty X]
    {idx : ℕ → X} (h_dense : DenseRange idx)
    {f : X → ℝ} (hf : Continuous f) :
    ⨆ x : X, f x = ⨆ k : ℕ, f (idx k) := by
  have hclosure :
      closure (Set.range f) = closure (Set.range (f ∘ idx)) := by
    rw [Set.range_comp f idx]
    apply Set.Subset.antisymm
    · have hsub : Set.range f ⊆ closure (f '' Set.range idx) :=
        hf.range_subset_closure_image_dense h_dense
      exact closure_minimal hsub isClosed_closure
    · apply closure_mono
      exact Set.image_subset_range f (Set.range idx)
  by_cases hbdd : BddAbove (Set.range f)
  · calc
      ⨆ x : X, f x = sSup (closure (Set.range f)) := by
        exact sSup_eq_closure_sSup (Set.range_nonempty f) hbdd
      _ = sSup (closure (Set.range (f ∘ idx))) := by
        rw [hclosure]
      _ = ⨆ k : ℕ, f (idx k) := by
        have hbdd_idx : BddAbove (Set.range (f ∘ idx)) := by
          rw [Set.range_comp f idx]
          exact BddAbove.mono (Set.image_subset_range f (Set.range idx)) hbdd
        exact (sSup_eq_closure_sSup (Set.range_nonempty (f ∘ idx)) hbdd_idx).symm
  · have hbdd_idx : ¬ BddAbove (Set.range (f ∘ idx)) := by
      intro h
      have hclosure_bdd : BddAbove (closure (Set.range (f ∘ idx))) :=
        bddAbove_closure.mpr h
      rw [← hclosure] at hclosure_bdd
      exact hbdd (bddAbove_closure.mp hclosure_bdd)
    calc
      ⨆ x : X, f x = 0 := Real.iSup_of_not_bddAbove hbdd
      _ = ⨆ k : ℕ, f (idx k) := (Real.iSup_of_not_bddAbove hbdd_idx).symm

private lemma empiricalRademacherComplexity_eq_denseRange
    {X 𝒳 : Type*} [TopologicalSpace X] [Nonempty X]
    {idx : ℕ → X} (h_dense : DenseRange idx)
    (n : ℕ) (f : X → 𝒳 → ℝ)
    (hf : ∀ z : 𝒳, Continuous fun x : X => f x z)
    (sample : Fin n → 𝒳) :
    empiricalRademacherComplexity n f sample =
      empiricalRademacherComplexity n (f ∘ idx) sample := by
  dsimp [empiricalRademacherComplexity]
  congr
  ext σ
  exact separableSup_via_denseRange h_dense (by
    apply Continuous.abs
    apply Continuous.const_mul
    exact continuous_finset_sum Finset.univ fun k _ =>
      continuous_const.mul (hf (sample k)))

private lemma rademacherComplexity_eq_denseRange
    {Ω 𝒳 X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [Nonempty X]
    {idx : ℕ → X} (h_dense : DenseRange idx)
    (n : ℕ) (f : X → 𝒳 → ℝ)
    (hf : ∀ z : 𝒳, Continuous fun x : X => f x z)
    (μ : MeasureTheory.Measure Ω) (sample : Ω → 𝒳) :
    rademacherComplexity n f μ sample =
      rademacherComplexity n (f ∘ idx) μ sample := by
  dsimp [rademacherComplexity]
  congr
  ext ω
  exact empiricalRademacherComplexity_eq_denseRange h_dense n f hf (sample ∘ ω)

private lemma rademacherComplexity_map_id
    {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [Countable ι]
    (n : ℕ) (f : ι → 𝒳 → ℝ)
    (hf : ∀ i, Measurable (f i))
    (μ : MeasureTheory.Measure Ω) [SigmaFinite μ] (sample : Ω → 𝒳)
    [SigmaFinite (μ.map sample)]
    (hsample : Measurable sample) :
    rademacherComplexity n f (μ.map sample) id =
      rademacherComplexity n f μ sample := by
  dsimp [rademacherComplexity]
  let Φ : (Fin n → Ω) → (Fin n → 𝒳) := fun ω i => sample (ω i)
  have hmap :
      Measure.map Φ (Measure.pi fun _ : Fin n => μ) =
        Measure.pi fun _ : Fin n => μ.map sample := by
    dsimp [Φ]
    rw [Measure.pi_map_pi]
    intro _
    exact hsample.aemeasurable
  rw [← hmap]
  rw [integral_map]
  · rfl
  · exact (measurable_pi_lambda Φ
        (fun i => hsample.comp (measurable_pi_apply i))).aemeasurable
  · apply Measurable.aestronglyMeasurable
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro σ _
    apply Measurable.iSup
    intro i
    apply Measurable.abs
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro k _
    apply measurable_const.mul
    exact (hf i).comp (measurable_pi_apply k)

private lemma empiricalRademacherComplexity_congr_sample
    {𝒳 : Type*} (n : ℕ) (f f' : ℕ → 𝒳 → ℝ) (sample : Fin n → 𝒳)
    (h : ∀ i k, f i (sample k) = f' i (sample k)) :
    empiricalRademacherComplexity n f sample =
      empiricalRademacherComplexity n f' sample := by
  dsimp [empiricalRademacherComplexity]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _hσ
  congr 1
  ext i
  congr 2
  apply Finset.sum_congr rfl
  intro k _hk
  rw [h i k]

private lemma rademacherComplexity_congr_ae
    {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    (n : ℕ) (f f' : ℕ → 𝒳 → ℝ) (μ : MeasureTheory.Measure Ω)
    [SigmaFinite μ]
    (sample : Ω → 𝒳)
    (h : ∀ i, (fun ω => f i (sample ω)) =ᵐ[μ]
      fun ω => f' i (sample ω)) :
    rademacherComplexity n f μ sample =
      rademacherComplexity n f' μ sample := by
  dsimp [rademacherComplexity]
  apply integral_congr_ae
  have hall : ∀ᵐ ω ∂μ, ∀ i : ℕ,
      f i (sample ω) = f' i (sample ω) := ae_all_iff.2 h
  have hprod : ∀ᵐ s : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i : ℕ, ∀ k : Fin n,
        f i (sample (s k)) = f' i (sample (s k)) := by
    filter_upwards [Filter.eventually_all.2 fun k : Fin n =>
      Measure.tendsto_eval_ae_ae.eventually hall] with s hs i k
    exact hs k i
  filter_upwards [hprod] with s hs
  exact empiricalRademacherComplexity_congr_sample n f f' (sample ∘ s)
    (fun i k => hs i k)

private lemma populationRisk_abs_le_of_uniform
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (_hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLoss S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |S.L θ g| ≤ b := by
  calc
    |S.L θ g| = |∫ z, S.ℓ z θ g ∂P_Z| := rfl
    _ ≤ ∫ z, |S.ℓ z θ g| ∂P_Z := abs_integral_le_integral_abs
    _ ≤ ∫ _z, b ∂P_Z := by
      apply integral_mono
      · exact Integrable.of_bound (S.ℓ_meas θ g).abs.aestronglyMeasurable b
          (by
            filter_upwards with z
            simpa [Real.norm_eq_abs] using hg_bdd z θ hθ)
      · exact integrable_const b
      · intro z
        exact hg_bdd z θ hθ
    _ = b := by simp

private lemma populationRisk_sub_le_two_mul_bound
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLoss S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    S.L θ g - S.L S.θ₀ g ≤ 2 * b := by
  have hθ_abs := populationRisk_abs_le_of_uniform S hb hg_bdd hθ
  have hθ₀_abs := populationRisk_abs_le_of_uniform S hb hg_bdd S.θ₀_mem
  have hθ_le : S.L θ g ≤ b := le_abs_self (S.L θ g) |>.trans hθ_abs
  have hθ₀_ge : -b ≤ S.L S.θ₀ g := (abs_le.mp hθ₀_abs).1
  linarith

private lemma populationRisk_abs_le_of_uniform_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (_hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLossAE S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |S.L θ g| ≤ b := by
  calc
    |S.L θ g| = |∫ z, S.ℓ z θ g ∂P_Z| := rfl
    _ ≤ ∫ z, |S.ℓ z θ g| ∂P_Z := abs_integral_le_integral_abs
    _ ≤ ∫ _z, b ∂P_Z := by
      apply integral_mono_ae
      · exact Integrable.of_bound (S.ℓ_meas θ g).abs.aestronglyMeasurable b
          (by
            filter_upwards [hg_bdd] with z hz
            simpa [Real.norm_eq_abs] using hz θ hθ)
      · exact integrable_const b
      · filter_upwards [hg_bdd] with z hz
        exact hz θ hθ
    _ = b := by simp

private lemma populationRisk_sub_le_two_mul_bound_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLossAE S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    S.L θ g - S.L S.θ₀ g ≤ 2 * b := by
  have hθ_abs := populationRisk_abs_le_of_uniform_ae S hb hg_bdd hθ
  have hθ₀_abs := populationRisk_abs_le_of_uniform_ae S hb hg_bdd S.θ₀_mem
  have hθ_le : S.L θ g ≤ b := le_abs_self (S.L θ g) |>.trans hθ_abs
  have hθ₀_ge : -b ≤ S.L S.θ₀ g := (abs_le.mp hθ₀_abs).1
  linarith

/-- **Bounded-loss Rademacher bridge theorem.**

Under uniform boundedness of the loss and a Rademacher-complexity bound
on the centred loss class, `LocalEmpProcessModulus` holds with
the textbook nonempty-fold rate
`ρ n := √(2 R n + 2b · √(2 log(1/δ) / |B(n)|))`, with the empty-fold
boundary branch `ρ n := √(2b)`.

The proof chains:

1. `BoundedDifference.uniformDeviation_bounded_difference` ⇒ the centred
   sup is bounded-difference with constant `c_i = 2b / n`.
2. `McDiarmid.mcdiarmid_inequality_pos'` ⇒ the centred sup is concentrated
   around its mean: `‖Pₙ − P‖_F ≤ 𝔼‖Pₙ − P‖_F + b√(2 log(1/δ)/n)` w.p.
   `≥ 1 − δ`.
3. `Symmetrization.expectation_le_rademacher` ⇒ `𝔼‖Pₙ − P‖_F ≤ 2 R_n(F)`
   in the population Rademacher sense.
4. The bound on the centred *excess* risk
   `[L θ g − L θ₀ g] − [Lₙ θ g − Lₙ θ₀ g]`
   follows by applying the uniform deviation bound to the centred loss
   class.

The `ρ n * ‖θ − θ₀‖` slot of the modulus inequality is satisfied
trivially since the right-hand side `(ρ n)^2` already dominates.

**Rate form.** The modulus only uses the constant `ρ²` slot, with the
`ρ‖θ−θ₀‖` slot set to 0, so the realised
modulus must be a `ρ_{n,δ}` whose square dominates the uniform deviation
of the centred loss class.  The centred class
`{z ↦ ℓ z θ g − ℓ z θ₀ g : θ ∈ Θ_set}` is bounded by `2b` (triangle
inequality), so:

* `expectation_le_rademacher` ⇒ `𝔼[sup_θ |Lₙ_centred − L_centred|] ≤ 2 R n`,
* `uniformDeviation_bounded_difference` (with class bound `2b`) gives
  bounded-difference constants `c_i = 4b/m` where `m = |B(n)|`,
* `mcdiarmid_inequality_pos'` ⇒ deviation around the mean by
  `2b · √(2 log(1/δ) / m)` w.p. ≥ `1 − δ`.

We therefore set

    ρ_{n,δ} := if |B(n)| = 0 then √(2b)
      else Real.sqrt (2 · R n + 2 · b · √(2 · log(1/δ) / |B(n)|))

so that `ρ²` itself dominates `2 R n + 2b · √(2 log(1/δ) / |B(n)|)` and
the slack term `ρ · ‖θ − θ₀‖` adds non-negative excess.

**Hypotheses.** `[IsProbabilityMeasure μ]` is needed for
`μ E ≥ 1 - ENNReal.ofReal δ`; `[SeparableSpace S.Θ_set]` and
`[Nonempty S.Θ_set]` carry the countable-dense substrate, while
`LossContinuousOnΘset` provides the continuity needed by
`separableSpaceSup_eq_real` to lift FoML's `ℕ`-indexed sup conclusion to
a sup over `↥S.Θ_set`.

**Why not `[Countable S.Θ_set]`?** Combined with `S.Θ_convex`, countability
forces `S.Θ_set.Subsingleton` (a non-trivial convex subset of a real
vector space contains a line segment, which is uncountable).  The
`[SeparableSpace]` form admits genuinely infinite convex `Θ_set`.
The user must supply `idx_dense` as the explicit separability witness —
`S.Θ_set` is not assumed to carry a `[SeparableSpace]` instance a priori;
the bridge constructs that instance from `idx_dense` internally.

**Bridge.** The re-indexing from FoML's `μⁿ`-on-`Fin m → Ω` form to the
fold-B sum on `μ` uses `foldB_pi_law` (joint-law identification) plus the
order-isomorphism `Fin (split.foldB n).card ≃o split.foldB n`.  The
final sup-over-`↥S.Θ_set` step uses `separableSpaceSup_eq_real`
specialised to the deviation map. -/
theorem localEmpProcessModulus_of_bounded_rademacher
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) (g : G)
    (hg_bdd : UniformlyBoundedLoss S g b)
    (hg_cont : LossContinuousOnΘset S g)
    (idx : ℕ → S.Θ_set)
    (idx_dense : DenseRange idx)
    (R : ℕ → ℝ)
    (hR : RademacherBound S S_iid split g idx R)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun n => Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ g := by
  intro n
  classical
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  have hR_nonneg : 0 ≤ R n := (hR n).1
  by_cases hm0 : (split.foldB n).card = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ θ hθ
      have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
      have hpop : S.L θ g - S.L S.θ₀ g ≤ 2 * b :=
        populationRisk_sub_le_two_mul_bound S hb hg_bdd hθ
      have hρsq :
          (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
            = 2 * b := by
        rw [Real.sq_sqrt]
        · simp [hm0]
        · have : 0 ≤ 2 * b := by nlinarith
          simpa [hm0] using this
      have hρ_nonneg :
          0 ≤ Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
        Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
      calc
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
            = S.L θ g - S.L S.θ₀ g := by
                simp [empRiskFoldB, hfold_empty]
        _ ≤ 2 * b := hpop
        _ = (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq.symm
        _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    have hm_pos : 0 < ((split.foldB n).card : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    by_cases hb0 : b = 0
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · rw [measure_univ]
        exact tsub_le_self
      · intro ω _ θ hθ
        have hloss_zero : ∀ z θ', θ' ∈ S.Θ_set → S.ℓ z θ' g = 0 := by
          intro z θ' hθ'
          have habs : |S.ℓ z θ' g| = 0 := by
            apply le_antisymm
            · simpa [hb0] using hg_bdd z θ' hθ'
            · exact abs_nonneg _
          exact abs_eq_zero.mp habs
        have hLθ : S.L θ g = 0 := by
          have habs := populationRisk_abs_le_of_uniform S hb hg_bdd hθ
          exact abs_eq_zero.mp (le_antisymm (by simpa [hb0] using habs) (abs_nonneg _))
        have hL0 : S.L S.θ₀ g = 0 := by
          have habs := populationRisk_abs_le_of_uniform S hb hg_bdd S.θ₀_mem
          exact abs_eq_zero.mp (le_antisymm (by simpa [hb0] using habs) (abs_nonneg _))
        have hempθ : empRiskFoldB S S_iid split n ω θ g = 0 := by
          simp [empRiskFoldB, hloss_zero, hθ]
        have hemp0 : empRiskFoldB S S_iid split n ω S.θ₀ g = 0 := by
          simp [empRiskFoldB, hloss_zero, S.θ₀_mem]
        have hρ_nonneg :
            0 ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
          Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
        have hρsq_nonneg :
            0 ≤ (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := sq_nonneg _
        calc
          (S.L θ g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g) = 0 := by
                simp [hLθ, hL0, hempθ, hemp0]
          _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg, hρsq_nonneg]
    · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      let m : ℕ := (split.foldB n).card
      let fθ : S.Θ_set → Z → ℝ := fun θ z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g
      haveI : Nonempty Z := nonempty_of_isProbabilityMeasure P_Z
      haveI : Nonempty S.Θ_set := ⟨⟨S.θ₀, S.θ₀_mem⟩⟩
      haveI : SeparableSpace S.Θ_set := by
        exact ⟨⟨Set.range idx, Set.countable_range idx, idx_dense⟩⟩
      have hf_meas : ∀ θ : S.Θ_set, Measurable (fθ θ) := by
        intro θ
        exact (S.ℓ_meas θ.val g).sub (S.ℓ_meas S.θ₀ g)
      have hf_bdd : ∀ θ : S.Θ_set, ∀ z : Z, |fθ θ z| ≤ 2 * b := by
        intro θ z
        have h1 : |S.ℓ z θ.val g| ≤ b := hg_bdd z θ.val θ.property
        have h2 : |S.ℓ z S.θ₀ g| ≤ b := hg_bdd z S.θ₀ S.θ₀_mem
        have h := abs_sub (S.ℓ z θ.val g) (S.ℓ z S.θ₀ g)
        dsimp [fθ]
        linarith
      have hf_cont : ∀ z : Z, Continuous fun θ : S.Θ_set => fθ θ z := by
        intro z
        exact (hg_cont z).sub continuous_const
      let ε : ℝ := 2 * b * Real.sqrt (2 * Real.log (1 / δ) / m)
      let τ : ℝ := 2 * R n + ε
      have hε_nonneg : 0 ≤ ε := by
        dsimp [ε]
        positivity
      have htail := uniform_deviation_tail_bound_separable_of_pos
        (μ := P_Z) (n := m) (f := fθ) hf_meas (X := id) measurable_id
        (b := 2 * b) (by linarith) hf_bdd hf_cont (ε := ε) hε_nonneg
      have hrad_full_le : rademacherComplexity m fθ P_Z id ≤ R n := by
        have hfull_dense :
            rademacherComplexity m fθ P_Z id =
              rademacherComplexity m (fθ ∘ idx) P_Z id :=
          rademacherComplexity_eq_denseRange idx_dense m fθ hf_cont P_Z id
        have hmap :
            rademacherComplexity m (fθ ∘ idx) P_Z id =
              rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) := by
          have hmap' :
              rademacherComplexity m (fθ ∘ idx) (μ.map (S_iid.Z 0)) id =
                rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) :=
            rademacherComplexity_map_id m (fθ ∘ idx)
            (by
              intro k
              exact (hf_meas (idx k))) μ (S_iid.Z 0) (S_iid.meas 0)
          simpa [S_iid.law] using hmap'
        calc
          rademacherComplexity m fθ P_Z id
              = rademacherComplexity m (fθ ∘ idx) P_Z id := hfull_dense
          _ = rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) := hmap
          _ ≤ R n := by simpa [m, fθ] using (hR n).2
      let badZ : Set (Fin m → Z) :=
        {s | 2 • rademacherComplexity m fθ P_Z id + ε ≤
          uniformDeviation m fθ P_Z id (id ∘ s)}
      let EZ : Set (Fin m → Z) := badZᶜ
      have hbad_meas : MeasurableSet badZ := by
        have hUD_eq :
            uniformDeviation m fθ P_Z id =
              uniformDeviation m (fθ ∘ denseSeq S.Θ_set) P_Z id :=
          uniformDeviation_eq (n := m) (f := fθ) hf_meas id measurable_id
            (b := 2 * b) hf_bdd hf_cont P_Z
        have hbad_eq :
            badZ =
              {s | 2 • rademacherComplexity m fθ P_Z id + ε ≤
                uniformDeviation m (fθ ∘ denseSeq S.Θ_set) P_Z id (id ∘ s)} := by
          ext s
          simp [badZ, hUD_eq]
        rw [hbad_eq]
        exact measurableSet_le measurable_const
          ((uniformDeviation_measurable (n := m) (f := fθ ∘ denseSeq S.Θ_set)
            (μ := P_Z) id (by intro k; exact hf_meas (denseSeq S.Θ_set k))).comp measurable_id)
      have hEZ_meas : MeasurableSet EZ := hbad_meas.compl
      have hbad_le_delta : Measure.pi (fun _ : Fin m => P_Z) badZ ≤ ENNReal.ofReal δ := by
        have hbad_toReal : (Measure.pi (fun _ : Fin m => P_Z) badZ).toReal ≤ δ := by
          have hle_exp := htail
          have hexp_le : Real.exp (-ε ^ 2 * m / (2 * (2 * b) ^ 2)) ≤ δ := by
            have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
            have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
              apply Real.log_nonneg
              have : (1 : ℝ) ≤ 1 / δ := by
                rw [le_div_iff₀ hδ]
                simpa using hδ'
              exact this
            have hsqrt_sq : (Real.sqrt (2 * Real.log (1 / δ) / m)) ^ 2 =
                2 * Real.log (1 / δ) / m := by
              rw [Real.sq_sqrt]
              positivity
            have hcalc : -ε ^ 2 * m / (2 * (2 * b) ^ 2) = Real.log δ := by
              dsimp [ε]
              rw [mul_pow, hsqrt_sq]
              field_simp [hb_pos.ne', hm_pos.ne']
              ring_nf
              rw [Real.log_inv δ]
              rw [mul_assoc, mul_inv_cancel₀ hm_pos.ne', mul_one]
              ring
            rw [hcalc, Real.exp_log hδ]
          exact hle_exp.trans hexp_le
        rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (le_of_lt hδ)]
        exact hbad_toReal
      have hEZ_prob : Measure.pi (fun _ : Fin m => P_Z) EZ ≥ 1 - ENNReal.ofReal δ := by
        dsimp [EZ]
        rw [measure_compl hbad_meas (measure_ne_top _ _), measure_univ]
        exact tsub_le_tsub_left hbad_le_delta 1
      let e : Fin m ≃o split.foldB n := (split.foldB n).orderIsoOfFin rfl
      let Y : Ω → Fin m → Z := fun ω j => S_iid.Z (e j).val ω
      have hY_meas : Measurable Y := by
        apply measurable_pi_lambda
        intro j
        exact S_iid.meas (e j).val
      have hY_law : μ.map Y = Measure.pi (fun _ : Fin m => P_Z) := by
        let YB : Ω → split.foldB n → Z := fun ω i => S_iid.Z i.val ω
        let T : (split.foldB n → Z) ≃ᵐ (Fin m → Z) :=
          MeasurableEquiv.piCongrLeft (fun _ : Fin m => Z) e.symm.toEquiv
        have hY_eq : Y = T ∘ YB := by
          funext ω j
          simpa [Y, YB, T] using
            (MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm.toEquiv)
              (β := fun _ : Fin m => Z)
              (x := fun i : split.foldB n => S_iid.Z i.val ω) (i := e j)).symm
        rw [hY_eq, ← Measure.map_map T.measurable
          (measurable_pi_lambda YB fun i => S_iid.meas i.val)]
        · rw [foldB_pi_law S_iid split n]
          simpa [T] using Measure.pi_map_piCongrLeft (e := e.symm.toEquiv)
            (β := fun _ : Fin m => Z) (μ := fun _ : Fin m => P_Z)
      refine ⟨Y ⁻¹' EZ, hEZ_meas.preimage hY_meas, ?_, ?_⟩
      · rw [← Measure.map_apply hY_meas hEZ_meas, hY_law]
        exact hEZ_prob
      · intro ω hω θ hθ
        let θs : S.Θ_set := ⟨θ, hθ⟩
        have hgood : ¬ (2 • rademacherComplexity m fθ P_Z id + ε ≤
            uniformDeviation m fθ P_Z id (id ∘ Y ω)) := by
          simpa [EZ, badZ] using hω
        have hdev_lt : uniformDeviation m fθ P_Z id (Y ω) < 2 * R n + ε := by
          have hnot : uniformDeviation m fθ P_Z id (Y ω) <
              2 • rademacherComplexity m fθ P_Z id + ε := by
            rw [not_le] at hgood
            simpa using hgood
          have hrad_two : 2 • rademacherComplexity m fθ P_Z id + ε ≤ 2 * R n + ε := by
            simpa [two_nsmul] using
              add_le_add_right
                (mul_le_mul_of_nonneg_left hrad_full_le (by norm_num : (0 : ℝ) ≤ 2)) ε
          exact hnot.trans_le hrad_two
        have hpoint_le_dev :
            |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k))
              - P_Z[fun z => fθ θs (id z)]|
              ≤ uniformDeviation m fθ P_Z id (Y ω) := by
          dsimp [uniformDeviation]
          apply le_ciSup (f := fun i : S.Θ_set =>
            |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ i (Y ω k))
              - P_Z[fun z => fθ i (id z)]|)
          rw [bddAbove_def]
          use 4 * b
          intro y hy
          rcases hy with ⟨θ', rfl⟩
          have hsample :
              |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))| ≤
                2 * b := by
            calc
              _ = (m : ℝ)⁻¹ * |Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k)| := by
                rw [abs_mul, abs_of_nonneg]
                exact inv_nonneg.mpr (Nat.cast_nonneg _)
              _ ≤ (m : ℝ)⁻¹ * (Finset.univ.sum fun _ : Fin m => 2 * b) := by
                apply mul_le_mul_of_nonneg_left
                · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                    (Finset.sum_le_sum fun k _ => hf_bdd θ' (Y ω k))
                · positivity
              _ = 2 * b := by
                simp [m]
                field_simp [hm_pos.ne']
          have hmean : |P_Z[fun z => fθ θ' (id z)]| ≤ 2 * b := by
            calc
              _ ≤ ∫ z, |fθ θ' z| ∂P_Z := abs_integral_le_integral_abs
              _ ≤ ∫ _z, 2 * b ∂P_Z := by
                apply integral_mono
                · exact Integrable.of_bound ((hf_meas θ').abs.aestronglyMeasurable) (2 * b)
                    (by
                      filter_upwards with z
                      simpa [Real.norm_eq_abs] using hf_bdd θ' z)
                · exact integrable_const (2 * b)
                · intro z
                  exact hf_bdd θ' z
              _ = 2 * b := by simp
          calc
            |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))
                - P_Z[fun z => fθ θ' (id z)]|
                ≤ |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))|
                    + |P_Z[fun z => fθ θ' (id z)]| := abs_sub _ _
            _ ≤ 4 * b := by linarith
        have hcenter_abs :
            |(empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
              - (S.L θ g - S.L S.θ₀ g)| ≤ 2 * R n + ε := by
          have hsum_reindex :
              (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k)) =
                ∑ i ∈ split.foldB n,
                  (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
            have hsum_subtype :
                (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k)) =
                  ∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g) :=
              Fintype.sum_equiv e.toEquiv (fun k => fθ θs (Y ω k))
                (fun i : split.foldB n =>
                  S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)
                (by intro k; rfl)
            have hsum_attach :
                (∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)) =
                  ∑ i ∈ split.foldB n,
                    (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
              simpa using Finset.sum_attach (s := split.foldB n)
                (f := fun i =>
                  S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)
            exact hsum_subtype.trans hsum_attach
          have hmean_eq : (∫ z, fθ θs z ∂P_Z) = S.L θ g - S.L S.θ₀ g := by
            have hintθ : Integrable (fun z => S.ℓ z θ g) P_Z :=
              Integrable.of_bound (S.ℓ_meas θ g).aestronglyMeasurable b
                (by
                  filter_upwards with z
                  simpa [Real.norm_eq_abs] using hg_bdd z θ hθ)
            have hint0 : Integrable (fun z => S.ℓ z S.θ₀ g) P_Z :=
              Integrable.of_bound (S.ℓ_meas S.θ₀ g).aestronglyMeasurable b
                (by
                  filter_upwards with z
                  simpa [Real.norm_eq_abs] using hg_bdd z S.θ₀ S.θ₀_mem)
            change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
              S.L θ g - S.L S.θ₀ g
            change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
              (∫ z, S.ℓ z θ g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
            exact integral_sub hintθ hint0
          have hpoint := hpoint_le_dev.trans (le_of_lt hdev_lt)
          have hpoint' :
              |(m : ℝ)⁻¹ *
                    (∑ i ∈ split.foldB n,
                      (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g))
                  - (S.L θ g - S.L S.θ₀ g)| ≤ 2 * R n + ε := by
            simpa [hmean_eq, hsum_reindex] using hpoint
          convert hpoint' using 1
          simp [empRiskFoldB, m]
          ring_nf
        have hmain :
            (S.L θ g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
              ≤ 2 * R n + ε := by
          have := neg_le_abs ((empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
              - (S.L θ g - S.L S.θ₀ g))
          linarith
        have hρsq_eq :
            (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 =
              2 * R n + ε := by
          have hradicand :
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                 Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))
                = 2 * R n + 2 * b *
                    Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card) := by
            rw [if_neg hm0]
          have hnonneg :
              0 ≤ (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                 Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) := by
            have : 0 ≤ 2 * R n + ε := by
              nlinarith [hε_nonneg, hR_nonneg]
            rw [hradicand]
            simpa [ε, m] using this
          rw [Real.sq_sqrt hnonneg]
          rw [hradicand]
        have hρ_nonneg :
            0 ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
          Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
        calc
          (S.L θ g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
              ≤ 2 * R n + ε := hmain
          _ = (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq_eq.symm
          _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]

/-- **Almost-everywhere bounded-loss bridge.**

The same empirical-process modulus bridge as
`localEmpProcessModulus_of_bounded_rademacher`, but with the loss envelope
assumed only under the population law and with a local minimizer witness for
the auxiliary clamped loss used in the proof. The empty-fold branch uses only
population-risk bounds and is therefore identical after replacing the helper
lemma by its a.e. analogue. In the nonempty branch, the proof applies the
McDiarmid tail bound to the class clamped to `[-b, b]` and transfers the
resulting product-space event back to the original class on the conull sample
event where the clamp is inactive. -/
theorem localEmpProcessModulus_of_bounded_rademacher_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) (g : G)
    (hg_bdd_ae : UniformlyBoundedLossAE S g b)
    (hg_cont : LossContinuousOnΘset S g)
    (idx : ℕ → S.Θ_set)
    (idx_dense : DenseRange idx)
    (R : ℕ → ℝ)
    (hR : RademacherBound S S_iid split g idx R)
    (hclamp_minimizes : ∀ θ ∈ S.Θ_set,
      ∫ z, max (-b) (min b (S.ℓ z S.θ₀ S.g₀)) ∂P_Z
        ≤ ∫ z, max (-b) (min b (S.ℓ z θ S.g₀)) ∂P_Z)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun n => Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ g := by
  intro n
  classical
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  by_cases hm0 : (split.foldB n).card = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ θ hθ
      have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
      have hpop : S.L θ g - S.L S.θ₀ g ≤ 2 * b :=
        populationRisk_sub_le_two_mul_bound_ae S hb hg_bdd_ae hθ
      have hρsq :
          (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
            = 2 * b := by
        rw [Real.sq_sqrt]
        · simp [hm0]
        · have : 0 ≤ 2 * b := by nlinarith
          simpa [hm0] using this
      have hρ_nonneg :
          0 ≤ Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
        Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
      calc
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
            = S.L θ g - S.L S.θ₀ g := by
                simp [empRiskFoldB, hfold_empty]
        _ ≤ 2 * b := hpop
        _ = (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq.symm
        _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]
  · let clamp : ℝ → ℝ := fun t => max (-b) (min b t)
    let Sc : LearningSystem Ω μ Z P_Z Θ G :=
      { S with
        ℓ := fun z θ g' => clamp (S.ℓ z θ g')
        ℓ_meas := fun θ g' => by
          dsimp [clamp]
          exact measurable_const.max (measurable_const.min (S.ℓ_meas θ g'))
        θ₀_minimizes := by
          intro θ hθ
          simpa [clamp] using hclamp_minimizes θ hθ }
    have hclamp_abs : ∀ t : ℝ, |clamp t| ≤ b := by
      intro t
      rw [abs_le]
      constructor
      · dsimp [clamp]
        exact le_max_left (-b) (min b t)
      · dsimp [clamp]
        exact max_le (by linarith) (min_le_left b t)
    have hclamp_eq_of_abs_le : ∀ {t : ℝ}, |t| ≤ b → clamp t = t := by
      intro t ht
      have ht_low : -b ≤ t := (abs_le.mp ht).1
      have ht_high : t ≤ b := (abs_le.mp ht).2
      dsimp [clamp]
      rw [min_eq_right ht_high, max_eq_right ht_low]
    have hSc_bdd : UniformlyBoundedLoss Sc g b := by
      intro z θ hθ
      simpa [Sc] using hclamp_abs (S.ℓ z θ g)
    have hSc_cont : LossContinuousOnΘset Sc g := by
      intro z
      dsimp [Sc, clamp]
      exact continuous_const.max (continuous_const.min (hg_cont z))
    have hℓ_ae : ∀ θ, θ ∈ S.Θ_set →
        (fun z => S.ℓ z θ g) =ᵐ[P_Z] fun z => Sc.ℓ z θ g := by
      intro θ hθ
      filter_upwards [hg_bdd_ae] with z hz
      simpa [Sc] using (hclamp_eq_of_abs_le (hz θ hθ)).symm
    have hℓ_all_ae : ∀ᵐ z ∂P_Z,
        ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
      filter_upwards [hg_bdd_ae] with z hz θ hθ
      simpa [Sc] using (hclamp_eq_of_abs_le (hz θ hθ)).symm
    have hL_eq : ∀ θ, θ ∈ S.Θ_set → S.L θ g = Sc.L θ g := by
      intro θ hθ
      dsimp [LearningSystem.L]
      exact integral_congr_ae (hℓ_ae θ hθ)
    let idxc : ℕ → Sc.Θ_set := fun k => ⟨(idx k).val, by
      simp [Sc, (idx k).property]⟩
    have idxc_dense : DenseRange idxc := by
      simpa [idxc, Sc] using idx_dense
    have hRc : RademacherBound Sc S_iid split g idxc R := by
      intro m
      refine ⟨(hR m).1, ?_⟩
      have hcenter_ae : ∀ k : ℕ,
          (fun ω => S.ℓ (S_iid.Z 0 ω) (idx k).val g
              - S.ℓ (S_iid.Z 0 ω) S.θ₀ g) =ᵐ[μ]
            fun ω => Sc.ℓ (S_iid.Z 0 ω) (idx k).val g
              - Sc.ℓ (S_iid.Z 0 ω) Sc.θ₀ g := by
        intro k
        have hidx_base : (fun z => S.ℓ z (idx k).val g) =ᵐ[P_Z]
            fun z => Sc.ℓ z (idx k).val g :=
          hℓ_ae (idx k).val (idx k).property
        have hzero_base : (fun z => S.ℓ z S.θ₀ g) =ᵐ[P_Z]
            fun z => Sc.ℓ z S.θ₀ g :=
          hℓ_ae S.θ₀ S.θ₀_mem
        have hidx' : (fun ω => S.ℓ (S_iid.Z 0 ω) (idx k).val g) =ᵐ[μ]
            fun ω => Sc.ℓ (S_iid.Z 0 ω) (idx k).val g := by
          have hmap : ∀ᵐ z ∂μ.map (S_iid.Z 0),
              S.ℓ z (idx k).val g = Sc.ℓ z (idx k).val g := by
            simpa [S_iid.law] using hidx_base
          exact ae_of_ae_map (S_iid.meas 0).aemeasurable hmap
        have hzero' : (fun ω => S.ℓ (S_iid.Z 0 ω) S.θ₀ g) =ᵐ[μ]
            fun ω => Sc.ℓ (S_iid.Z 0 ω) Sc.θ₀ g := by
          have hmap : ∀ᵐ z ∂μ.map (S_iid.Z 0),
              S.ℓ z S.θ₀ g = Sc.ℓ z S.θ₀ g := by
            simpa [S_iid.law] using hzero_base
          simpa [Sc] using ae_of_ae_map (S_iid.meas 0).aemeasurable hmap
        exact hidx'.sub hzero'
      have hcongr :
          rademacherComplexity (split.foldB m).card
              (fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
              μ (S_iid.Z 0) =
            rademacherComplexity (split.foldB m).card
          (fun k z => Sc.ℓ z (idxc k).val g - Sc.ℓ z Sc.θ₀ g)
          μ (S_iid.Z 0) :=
        by
          simpa [idxc] using
            rademacherComplexity_congr_ae (split.foldB m).card
              (fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
              (fun k z => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g)
              μ (S_iid.Z 0) hcenter_ae
      calc
        rademacherComplexity (split.foldB m).card
            (fun k z => Sc.ℓ z (idxc k).val g - Sc.ℓ z Sc.θ₀ g)
            μ (S_iid.Z 0)
            = rademacherComplexity (split.foldB m).card
                (fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
                μ (S_iid.Z 0) := hcongr.symm
        _ ≤ R m := (hR m).2
    have hmod_c := localEmpProcessModulus_of_bounded_rademacher
      Sc S_iid split hb g hSc_bdd hSc_cont idxc idxc_dense R hRc hδ hδ'
    rcases hmod_c n with ⟨Ec, hEc_meas, hEc_prob, hEc_bound⟩
    let Gs : Set Ω :=
      {ω | ∀ i ∈ split.foldB n, ∀ θ ∈ S.Θ_set,
        S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g}
    have hsample_all_ae : ∀ i : ℕ, ∀ᵐ ω ∂μ,
        ∀ θ ∈ S.Θ_set,
          S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g := by
      intro i
      have hlaw_i : μ.map (S_iid.Z i) = P_Z := by
        rw [← (S_iid.identDist i).map_eq, S_iid.law]
      have hbase : ∀ᵐ z ∂P_Z,
          ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := hℓ_all_ae
      have hmap : ∀ᵐ z ∂μ.map (S_iid.Z i),
          ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
        simpa [hlaw_i] using hbase
      exact ae_of_ae_map (S_iid.meas i).aemeasurable hmap
    have hGs_ae : ∀ᵐ ω ∂μ, ω ∈ Gs := by
      have hfin : ∀ᵐ ω ∂μ, ∀ i ∈ split.foldB n,
          ∀ θ ∈ S.Θ_set,
            S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g := by
        simpa using (Finset.eventually_all (split.foldB n)).2
          (fun i _hi => hsample_all_ae i)
      simpa [Gs] using hfin
    have hGs_null : μ Gsᶜ = 0 := ae_iff.mp hGs_ae
    rcases exists_measurable_superset_of_null hGs_null with
      ⟨N, hGs_compl_subset_N, hN_meas, hN_null⟩
    refine ⟨Ec \ N, hEc_meas.diff hN_meas, ?_, ?_⟩
    · rw [measure_diff_null hN_null]
      exact hEc_prob
    · intro ω hω θ hθ
      have hωEc : ω ∈ Ec := hω.1
      have hωG : ω ∈ Gs := by
        by_contra hnot
        exact hω.2 (hGs_compl_subset_N hnot)
      have hLθ : S.L θ g = Sc.L θ g := hL_eq θ hθ
      have hL0 : S.L S.θ₀ g = Sc.L Sc.θ₀ g := by
        simpa [Sc] using hL_eq S.θ₀ S.θ₀_mem
      have hempθ :
          empRiskFoldB S S_iid split n ω θ g =
            empRiskFoldB Sc S_iid split n ω θ g := by
        dsimp [empRiskFoldB]
        congr 1
        exact Finset.sum_congr rfl fun i hi => hωG i hi θ hθ
      have hemp0 :
          empRiskFoldB S S_iid split n ω S.θ₀ g =
            empRiskFoldB Sc S_iid split n ω Sc.θ₀ g := by
        dsimp [empRiskFoldB]
        congr 1
        exact Finset.sum_congr rfl fun i hi => by
            simpa [Sc] using hωG i hi S.θ₀ S.θ₀_mem
      calc
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
            = (Sc.L θ g - Sc.L Sc.θ₀ g)
                - (empRiskFoldB Sc S_iid split n ω θ g
                    - empRiskFoldB Sc S_iid split n ω Sc.θ₀ g) := by
              rw [hLθ, hL0, hempθ, hemp0]
        _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            simpa [Sc] using hEc_bound ω hωEc θ (by simpa [Sc] using hθ)

/-- **Trivial finite class.**  When `Θ_set = {θ₀}` (the
class collapses to the truth), the modulus inequality holds with
`ρ n := 0`. -/
theorem localEmpProcessModulus_singleton
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    [IsProbabilityMeasure μ]
    (g : G)
    (hsing : S.Θ_set = {S.θ₀})
    {δ : ℝ} (_hδ : 0 < δ) :
    LocalEmpProcessModulus S S_iid split (fun _ => 0) δ g := by
  intro n
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · rw [measure_univ]
    exact tsub_le_self
  · intro ω _ θ hθ
    have hθ' : θ ∈ ({S.θ₀} : Set Θ) := by
      simpa [hsing] using hθ
    rcases hθ' with rfl
    simp

end OrthogonalLearning
end Estimation
end Causalean
