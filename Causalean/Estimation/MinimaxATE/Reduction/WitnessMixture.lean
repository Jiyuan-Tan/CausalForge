/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the mixture two-point reduction (one-sided)

This is the **general** mixture form of the Le Cam two-point reduction, sharper
than `Witness.TwoPointWitness` in one decisive way: it only requires a *per-component
one-sided separation* of the ATE, `2 s ≤ |ate g₀ − ate (glam i)|` for each `i`, rather
than every alternative DGP sharing one common ATE value.  This is exactly what the
**functional / cell-varying center** construction needs (Jin–Syrgkanis 2024, Case 1
with arbitrary bounded `(m̂, ĝ)`): there the perturbed ATE is only a λ-independent
*lower bound* `ate (glam) ≥ ate (ĝ) + 2 s` (obtained from a Taylor expansion whose
first-order term cancels), not an exact constant.

Given
* a null in-class DGP `(m₀, g₀)` (typically the center `(m̂, ĝ)` itself);
* a finite family of in-class alternatives `(mlam i, glam i)` with weights `w` summing to `1`;
* per-component separation `2 s ≤ |ate g₀ − ate (glam i)|`;
* a total-variation budget `tvDist Q₀ Qmix ≤ c` between the null `n`-fold law and the
  weighted mixture of the alternatives' `n`-fold laws,

`mixture_two_point_lower_bound` concludes `(1 − c)/2 ≤ minimaxMiss …`.

The proof is the asymmetric testing argument: with `A` the null miss region, the
testing bound gives `1 − tvDist ≤ Q₀ A + Qmix Aᶜ`; the null side is `≤ minimaxMiss`
directly, and on `Aᶜ` the triangle inequality forces each component into *its own*
miss region (at `ate (glam i)`), so `Qmix Aᶜ ≤ minimaxMiss` by mixture domination.
Crucially the alternative side is measured at each component's true ATE — never at a
shared value — which is why a one-sided per-component bound suffices.
-/

import Causalean.Estimation.MinimaxATE.Model
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.Mixture

/-! # Mixture Two-Point Reduction

This file proves a mixture version of the two-point lower-bound argument for structure-agnostic
average-treatment-effect estimation.  It handles a null in-class DGP and a finite weighted family
of in-class alternatives whose treatment effects are each separated from the null, without
requiring the alternatives to share one common ATE.

The main theorem `mixture_two_point_lower_bound` combines the total-variation testing inequality
with `mixtureReal_le` and `nMiss_le_minimaxMiss`: the null miss event is dominated directly, while
the complement of the null miss event is contained in each alternative's own miss event by the
per-component separation. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

variable {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C]

/-- **Mixture two-point lower bound (one-sided separation).**  A null in-class DGP
`(m₀, g₀)` and a finite weighted family of in-class alternatives `(mlam i, glam i)` whose
ATEs are each `2 s`-separated from `ate g₀`, with total-variation budget `c` between
the null `n`-fold law and the mixture of the alternatives' `n`-fold laws, force every
measurable estimator to miss the true ATE by `s` with probability `≥ (1 − c)/2`
somewhere in the class.  Unlike `TwoPointWitness`, the alternatives need not share a
common ATE — only `2 s ≤ |ate g₀ − ate (glam i)|` per component. -/
theorem mixture_two_point_lower_bound
    {n : ℕ} {mhat : C → ℝ} {ghat : Bool → C → ℝ} {εg εm : ℝ}
    {ι : Type*} [Fintype ι]
    {m₀ : C → ℝ} {g₀ : Bool → C → ℝ} (hnull : InClass mhat ghat εg εm m₀ g₀)
    {mlam : ι → C → ℝ} {glam : ι → Bool → C → ℝ}
    (hin : ∀ i, InClass mhat ghat εg εm (mlam i) (glam i))
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    {s c : ℝ}
    (hsep : ∀ i, 2 * s ≤ |ate g₀ - ate (glam i)|)
    (htv : tvDist (productLaw hnull.valid n)
                  (mixture w (fun i => productLaw (hin i).valid n)) ≤ c)
    {est : (Fin n → Obs C) → ℝ} (hest : Measurable est) :
    (1 - c) / 2 ≤ minimaxMiss mhat ghat εg εm n est s := by
  haveI : IsProbabilityMeasure (productLaw hnull.valid n) := productLaw_isProb hnull.valid n
  haveI hpi : ∀ i, IsProbabilityMeasure (productLaw (hin i).valid n) :=
    fun i => productLaw_isProb (hin i).valid n
  haveI : IsProbabilityMeasure (mixture w (fun i => productLaw (hin i).valid n)) :=
    mixture_isProbabilityMeasure w hw _
  -- the null miss region
  set A := {x : Fin n → Obs C | s ≤ |est x - ate g₀|} with hA
  have hAmeas : MeasurableSet A := by
    have h := measurableSet_error (Ω := Fin n → Obs C) (Θ := ℝ) hest (ate g₀) s
    simpa only [Real.dist_eq, hA] using h
  -- testing bound: `1 − tvDist ≤ Q₀ A + Qmix Aᶜ`
  have htest := one_sub_tvDist_le_test
    (μ := productLaw hnull.valid n)
    (ν := mixture w (fun i => productLaw (hin i).valid n)) hAmeas
  -- null side: `Q₀ A = nMiss (at ate g₀) ≤ minimaxMiss`
  have hnullmiss : (productLaw hnull.valid n).real A
      ≤ minimaxMiss mhat ghat εg εm n est s := by
    rw [hA]
    exact nMiss_le_minimaxMiss (⟨(m₀, g₀), hnull⟩ : InClassDGP mhat ghat εg εm)
  -- mixture side: on `Aᶜ` each component is in its own miss region
  have hmixmiss : (mixture w (fun i => productLaw (hin i).valid n)).real Aᶜ
      ≤ minimaxMiss mhat ghat εg εm n est s := by
    refine mixtureReal_le w hw (fun i => productLaw (hin i).valid n) Aᶜ _ ?_
    intro i
    have hsub : Aᶜ ⊆ {x | s ≤ |est x - ate (glam i)|} := by
      intro x hx
      have hlt : |est x - ate g₀| < s := by
        simpa only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hx
      have htri : |ate g₀ - ate (glam i)|
          ≤ |est x - ate g₀| + |est x - ate (glam i)| := by
        have h := abs_sub_le (ate g₀) (est x) (ate (glam i))
        rwa [abs_sub_comm (ate g₀) (est x)] at h
      have hs2 := hsep i
      simp only [Set.mem_setOf_eq]
      by_contra hcon
      push_neg at hcon
      linarith
    calc (productLaw (hin i).valid n).real Aᶜ
        ≤ (productLaw (hin i).valid n).real {x | s ≤ |est x - ate (glam i)|} :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ minimaxMiss mhat ghat εg εm n est s :=
          nMiss_le_minimaxMiss (⟨(mlam i, glam i), hin i⟩ : InClassDGP mhat ghat εg εm)
  linarith

end Causalean.Estimation.MinimaxATE
