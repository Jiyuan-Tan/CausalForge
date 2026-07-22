/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.Model.Kernel
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.Basic

/-!
# Observational chain rule (do-calculus identification toolkit, Layer 3)

A single reusable disintegration lemma: the `Y`-marginal of an SCM's
observational kernel factors as the conditional kernel `Y | CC` composed with
the `CC`-marginal.  In probability notation, at a fixed parameter slice `s`,

    P(Y | s) = ∫_{cc} P(Y | CC = cc, s) dP(CC | s).

Both the do-side reduction and the adjustment-side reduction of every
backdoor/frontdoor identification proof are instances of this lemma; previously
each proof re-derived it by hand from `obsCondPairKernel.disintegrate`
(≈40 lines, twice in `SCM/ID/Backdoor.lean`).  Factoring it out is the
keystone of the identification toolkit.

The only genuinely-supplied typeclass is finiteness of `M.obsKernel`; every
`ValuesOn`-product instance (standard-Borel, nonempty, countably-generated)
infers from the per-node primitives because `ValuesOn I Ω` is a finite product.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

/-- **Observational chain rule.**

    At a fixed SCM slice, the observational distribution of the target variables
    is obtained by first drawing the conditioning variables from their
    observational marginal law and then drawing the targets from their
    observational conditional law given those conditioning variables.

        (M.obsKernel s).map π_Y
          = (M.obsCondKernel Y CC).sectR s  ∘ₘ  (M.obsKernel s).map π_CC.

    This is the disintegration / chain-rule step that every identification proof
    needs.  It is the generalization of the `hChain` block in
    `SCM/ID/Backdoor.lean` away from the post-intervention SCM, so a single call
    replaces the hand-rolled disintegration on each side of each proof. -/
theorem obsKernel_map_eq_obsCondKernel_comp
    (M : Causalean.SCM N Ω) (Y CC : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed) (hCC : CC ⊆ M.observed)
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    (s : M.FixedValues) :
    (M.obsKernel s).map (valuesProjection hY)
      = (M.obsCondKernel Y CC hY hCC).sectR s
          ∘ₘ ((M.obsKernel s).map (valuesProjection hCC)) := by
  haveI : ProbabilityTheory.IsMarkovKernel (M.obsCondKernel Y CC hY hCC) := by
    unfold SCM.obsCondKernel; infer_instance
  haveI hPairFin : ProbabilityTheory.IsFiniteKernel
      (M.obsCondPairKernel Y CC hY hCC) := by
    haveI : ProbabilityTheory.IsMarkovKernel
        (M.obsCondPairKernel Y CC hY hCC) := by
      unfold SCM.obsCondPairKernel
      exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
        (Measurable.prodMk
          (measurable_valuesProjection hCC)
          (measurable_valuesProjection hY))
    infer_instance
  have hDisint :
      (M.obsCondPairKernel Y CC hY hCC).fst ⊗ₖ
          M.obsCondKernel Y CC hY hCC
        = M.obsCondPairKernel Y CC hY hCC := by
    change (M.obsCondPairKernel Y CC hY hCC).fst ⊗ₖ
          (M.obsCondPairKernel Y CC hY hCC).condKernel
        = M.obsCondPairKernel Y CC hY hCC
    exact ProbabilityTheory.Kernel.disintegrate _ _
  have hAt :
      ((M.obsCondPairKernel Y CC hY hCC).fst ⊗ₖ
          M.obsCondKernel Y CC hY hCC) s
        = M.obsCondPairKernel Y CC hY hCC s := by
    rw [hDisint]
  rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR] at hAt
  have hFst :
      (M.obsCondPairKernel Y CC hY hCC).fst s
        = (M.obsKernel s).map (valuesProjection hCC) := by
    rw [ProbabilityTheory.Kernel.fst_apply, SCM.obsCondPairKernel,
        ProbabilityTheory.Kernel.map_apply _
          (Measurable.prodMk
            (measurable_valuesProjection hCC)
            (measurable_valuesProjection hY)),
        MeasureTheory.Measure.map_map measurable_fst
          (Measurable.prodMk
            (measurable_valuesProjection hCC)
            (measurable_valuesProjection hY))]
    rfl
  have hSnd :
      (M.obsCondPairKernel Y CC hY hCC s).snd
        = (M.obsKernel s).map (valuesProjection hY) := by
    rw [MeasureTheory.Measure.snd, SCM.obsCondPairKernel,
        ProbabilityTheory.Kernel.map_apply _
          (Measurable.prodMk
            (measurable_valuesProjection hCC)
            (measurable_valuesProjection hY)),
        MeasureTheory.Measure.map_map measurable_snd
          (Measurable.prodMk
            (measurable_valuesProjection hCC)
            (measurable_valuesProjection hY))]
    rfl
  have hAtSnd := congrArg MeasureTheory.Measure.snd hAt
  rw [hFst, MeasureTheory.Measure.snd_compProd, hSnd] at hAtSnd
  exact hAtSnd.symm

/-- **Empty-projection collapse.**  Projecting the observational kernel onto the empty
    node set yields a Dirac measure: `ValuesOn ∅` is a subsingleton, so the projected
    Markov kernel is the point mass at its unique value.  The base case of any
    conditioning set shrinking to `∅` in a fixing/adjustment step. -/
lemma obsKernel_empty_projection_eq_dirac
    (M : Causalean.SCM N Ω)
    (hEmpty : (∅ : Finset (SWIGNode N)) ⊆ M.observed)
    (s : M.FixedValues) (c : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) :
    (M.obsKernel s).map (valuesProjection hEmpty) = MeasureTheory.Measure.dirac c := by
  ext S hS
  by_cases hSEmpty : S = ∅
  · simp [hSEmpty]
  · have hUniv : S = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_contra hx
      apply hSEmpty
      ext y
      constructor
      · intro hy
        have : y = x := Subsingleton.elim y x
        exact False.elim (hx (this ▸ hy))
      · intro hy
        simp at hy
    rw [hUniv]
    rw [MeasureTheory.Measure.map_apply (measurable_valuesProjection _) MeasurableSet.univ]
    rw [show (valuesProjection hEmpty) ⁻¹' Set.univ = Set.univ by
      ext x
      simp]
    simp [M.obsKernel_apply_univ s]

/-- **Empty-conditioning collapse.**  Conditioning `obsCondKernel Y` on the empty set
    collapses to the plain `Y`-marginal `(M.obsKernel s).map π_Y`.  This is the reusable
    step every do-calculus factorization performs when a conditioning block becomes empty
    (e.g. the first node of a fixing sequence); it is graph-agnostic in `M`, so it applies
    verbatim to any stacked-intervention model `M.fixSet …`. -/
lemma obsCondKernel_empty_eq_marginal
    (M : Causalean.SCM N Ω) (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed)
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    (s : M.FixedValues) (c : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) :
    M.obsCondKernel Y (∅ : Finset (SWIGNode N)) hY (Finset.empty_subset M.observed)
        (s, c)
      = (M.obsKernel s).map (valuesProjection hY) := by
  have hChain := SCM.obsKernel_map_eq_obsCondKernel_comp M Y
    (∅ : Finset (SWIGNode N)) hY (Finset.empty_subset M.observed) s
  have hEmpty :
      (M.obsKernel s).map
          (valuesProjection (Finset.empty_subset M.observed :
            (∅ : Finset (SWIGNode N)) ⊆ M.observed))
        = MeasureTheory.Measure.dirac c :=
    obsKernel_empty_projection_eq_dirac M
      (Finset.empty_subset M.observed) s c
  calc
    M.obsCondKernel Y (∅ : Finset (SWIGNode N)) hY (Finset.empty_subset M.observed) (s, c)
        = (M.obsCondKernel Y (∅ : Finset (SWIGNode N)) hY
            (Finset.empty_subset M.observed)).sectR s ∘ₘ
            MeasureTheory.Measure.dirac c := by
          rw [MeasureTheory.Measure.dirac_bind]
          · rfl
          · fun_prop
    _ = (M.obsCondKernel Y (∅ : Finset (SWIGNode N)) hY
            (Finset.empty_subset M.observed)).sectR s ∘ₘ
            ((M.obsKernel s).map
              (valuesProjection (Finset.empty_subset M.observed :
                (∅ : Finset (SWIGNode N)) ⊆ M.observed))) := by
          rw [hEmpty]
    _ = (M.obsKernel s).map (valuesProjection hY) := hChain.symm

end SCM

end Causalean
