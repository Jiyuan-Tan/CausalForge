/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.GraphicalThms.IDAlgorithmRec

/-! # The executable ID algorithm and its soundness

`id_sound_rec` proves soundness for the *declarative* success certificate
`idSucceedsRec` (an inductive predicate — an existence claim needing a hand-built
derivation).  This file adds the **executable checker**: a computable
`Bool`-valued function `idAlgorithm` that runs Tian's IDENTIFY procedure with a
fuel bound, together with `idAlgorithm_sound` — when the checker reports `true`,
the interventional query is identified.

* `cFactorReachableRecB` — computable, choice-free fuel-bounded IDENTIFY
  reachability (mirrors the inductive `CFactorReachableRec`, using
  `cComponentSet.any` in place of the noncomputable `containingCComponent`).
* `idAlgorithm` — the runnable checker: valid intervention, observed query,
  and every post-intervention ancestral district recursively reachable.
* `idAlgorithm_sound` — the public soundness theorem: `idAlgorithm … = true` implies
  `IdentifiableUnder … (interventionalQuery X Y)` over the standard discrete
  positive model class.  Obtained from `id_sound_rec_discrete` through the
  structural bridge `idAlgorithm_success_toRec`.
-/

namespace Causalean.SCM.ID

open Causalean.SCM Causalean.SCM.ID.DiscreteID
open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Computable fuel-bounded IDENTIFY reachability.**  Returns `true` when the
c-factor `Q[C]` can be recovered from `Q[T]` within `fuel` IDENTIFY steps.  This
is the executable mirror of the inductive `CFactorReachableRec`: it is choice-free
(it searches `(G.induce A).cComponentSet` with `any` instead of naming the
component via the noncomputable `containingCComponent`). -/
def cFactorReachableRecB (G : SWIGGraph N) :
    ℕ → Finset (SWIGNode N) → Finset (SWIGNode N) → Bool
  | 0, _, _ => false
  | fuel + 1, T, C =>
    decide C.Nonempty && decide (C ⊆ T) &&
      (let A := inducedAncestral G T C
       if A = C then true
       else if A = T then false
       else decide (∃ C' ∈ (G.induce A).cComponentSet,
              C ⊆ C' ∧ cFactorReachableRecB G fuel C' C = true))

/-- The unique c-component containing a nonempty set `S` is `containingCComponent`.
Bridges the checker's `cComponentSet.any` search to the reachability predicate's
choice-based `containingCComponent`. -/
theorem containingCComponent_eq_of_mem_of_subset
    (G : SWIGGraph N) {S C' : Finset (SWIGNode N)}
    (hne : S.Nonempty) (hmem : C' ∈ G.cComponentSet) (hsub : S ⊆ C') :
    containingCComponent G S = C' := by
  classical
  have hchoose : hne.choose ∈ C' := hsub hne.choose_spec
  have hcomponent : G.cComponentOf hne.choose = C' :=
    G.cComponentOf_eq_of_mem_cComponentSet hmem hchoose
  simpa [containingCComponent, hne] using hcomponent

private theorem cComponentSet_nonempty
    (G : SWIGGraph N) {C : Finset (SWIGNode N)}
    (hmem : C ∈ G.cComponentSet) : C.Nonempty := by
  classical
  rw [SWIGGraph.cComponentSet, Finset.mem_image] at hmem
  obtain ⟨v, hv, rfl⟩ := hmem
  exact ⟨v, G.mem_cComponentOf_self hv⟩

/-- **Soundness of the computable reachability check.**  If the fuel-bounded
checker accepts, the inductive reachability certificate holds. -/
theorem cFactorReachableRecB_sound (G : SWIGGraph N) :
    ∀ (fuel : ℕ) (T C : Finset (SWIGNode N)),
      cFactorReachableRecB G fuel T C = true → CFactorReachableRec G T C := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro T C h
      simp [cFactorReachableRecB] at h
  | succ fuel ih =>
      intro T C h
      simp only [cFactorReachableRecB, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hne, hCT⟩, hinner⟩
      by_cases hAC : inducedAncestral G T C = C
      · exact CFactorReachableRec.base hne hCT hAC
      · by_cases hAT : inducedAncestral G T C = T
        · have hinner' : (if T = C then true else false) = true := by
            simpa only [hAT, ↓reduceIte] using hinner
          have hTC : T = C := by
            by_contra hTC
            simp only [hTC, ↓reduceIte] at hinner'
            exact Bool.false_ne_true hinner'
          exact False.elim (hAC (hAT.trans hTC))
        · have hex :
              ∃ C' ∈ (G.induce (inducedAncestral G T C)).cComponentSet,
                C ⊆ C' ∧ cFactorReachableRecB G fuel C' C = true := by
            simpa only [hAC, hAT, ↓reduceIte, decide_eq_true_eq] using hinner
          rcases hex with ⟨C', hC', hCC', hrecB⟩
          have hrec : CFactorReachableRec G C' C := ih C' C hrecB
          have hcontain :
              containingCComponent (G.induce (inducedAncestral G T C)) C = C' :=
            containingCComponent_eq_of_mem_of_subset
              (G.induce (inducedAncestral G T C)) hne hC' hCC'
          exact CFactorReachableRec.step hne hCT hAC hAT (hcontain ▸ hrec)

/-- Validity of an intervention split is decidable — enables the executable
`idAlgorithm` to branch on it. -/
instance instDecidableInterventionValid
    (X : Finset N) (G : SWIGGraph N) : Decidable (interventionValid X G) := by
  unfold interventionValid
  infer_instance

/-- **The executable ID checker.**  Runs the recursive Tian–Shpitser algorithm on
`(G, X, Y)` with `fuel` reduction steps: it requires a valid intervention split, an
observed query disjoint from `X`, and that every c-component of the
post-intervention ancestral graph is recursively reachable from its containing
district.  Computable — usable with `#eval` / `decide` on concrete graphs. -/
def idAlgorithm (fuel : ℕ) (G : SWIGGraph N)
    (X : Finset N) (Y : Finset (SWIGNode N)) : Bool :=
  if h : interventionValid X G then
    decide (Y ⊆ G.observed) &&
    decide (∀ d ∈ X, SWIGNode.random d ∉ Y) &&
      decide (∀ S ∈ ((G.splitMono X h.1 h.2).induce
          ((G.splitMono X h.1 h.2).dag.ancestralSet Y)).cComponentSet,
        ∃ C ∈ G.cComponentSet,
          S ⊆ C ∧ cFactorReachableRecB G fuel C S = true)
  else
    false

/-- **A successful run yields the graphical certificate.**  `idAlgorithm … = true`
implies the declarative recursive success certificate `idSucceedsRec`. -/
theorem idAlgorithm_success_toRec
    (fuel : ℕ) (G : SWIGGraph N) (X : Finset N) (Y : Finset (SWIGNode N))
    (h : idAlgorithm fuel G X Y = true) : idSucceedsRec X Y G := by
  classical
  unfold idAlgorithm at h
  by_cases hX : interventionValid X G
  · simp only [hX, dite_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hYobs, hdisj⟩, hcert⟩
    refine ⟨hX, hYobs, hdisj, ?_⟩
    intro S hS
    rcases hcert S hS with ⟨C, hC, hSC, hrecB⟩
    have hSne : S.Nonempty := cComponentSet_nonempty _ hS
    have hrec : CFactorReachableRec G C S :=
      cFactorReachableRecB_sound G fuel C S hrecB
    have hcontain : containingCComponent G S = C :=
      containingCComponent_eq_of_mem_of_subset G hSne hC hSC
    exact hcontain ▸ hrec
  · simp [hX] at h

/-- **Soundness of the executable ID algorithm.**  When the
runnable checker `idAlgorithm` reports success, the interventional query
`P(Y ∣ do(X))` is identified within the standard discrete positive model class.
This packages the full recursive Tian–Shpitser identification-soundness result
(`id_sound_rec_discrete`) behind a computable decision procedure. -/
theorem idAlgorithm_sound
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (fuel : ℕ) (G : SWIGGraph N) (X : Finset N) (Y : Finset (SWIGNode N))
    (h : idAlgorithm fuel G X Y = true) :
    IdentifiableUnder G (fun _ => True) StandardDiscretePositive
      (interventionalQuery (Ω := Ω) X Y) :=
  id_sound_rec_discrete X Y G (idAlgorithm_success_toRec fuel G X Y h)

end Causalean.SCM.ID
