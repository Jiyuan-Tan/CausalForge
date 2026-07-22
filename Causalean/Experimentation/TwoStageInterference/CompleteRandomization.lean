/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The completely randomized (mixed) design on `U → Bool`

Hudgens & Halloran (2008) state their variance results under **mixed** assignment strategies (their
Assumption 1): at each stage a fixed number of units is treated, and every one of the
`(card / count)` treated sets is equally likely.  That is exactly the completely randomized design.
This file transports the abstract completely randomized design `completeRandomization` — defined on
the size-`K` subsets `{S : Finset U // S.card = K}`, with its inclusion probabilities already
proven — onto the assignment space `U → Bool` used by the two-stage estimators, by pushing it
forward along the treated-set-to-indicator-vector map.

The design facts the Neyman/Hudgens–Halloran variance identities consume are then *derived* here,
not assumed: the first-order inclusion probability `E[Tᵢ] = K/N`, the pairwise second-order
inclusion probability `E[Tᵢ Tⱼ] = K(K−1)/(N(N−1))` for `i ≠ j`, the complementary first moment
`E[1−Tᵢ] = (N−K)/N`, and the deterministic treated count `∑ᵢ Tᵢ = K` on the design's support.  The
general `crdOn` engine works for any finite population `U`; `crd` is the within-group specialization
to `U = Fin n` (used by the within-group Theorem 5 / Eq. 9 corollaries), and the stage-1 group
selection uses the same engine with `U = ι` (used by the between-group Theorem 4 / Theorem 6
corollaries).  Downstream headline theorems specialize their generic, moment-conditioned forms to
these designs so that "under the completely randomized design" is a proven statement, not a
hypothesis.
-/

import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization

/-!
# Completely randomized assignment on Boolean vectors

This file pushes the paper-agnostic complete-randomization design on fixed-size treated sets
forward to the Boolean assignment spaces used by the two-stage interference modules. It proves the
first- and second-order inclusion probabilities and deterministic treated-count support facts
needed to instantiate the Hudgens-Halloran variance theorems under actual complete randomization.

The general construction is `crdOn` for any finite population `U`; `crd` is the within-group
specialization to `Fin n`.  The exported facts `crdOn_mean`, `crdOn_pair`, `crdOn_supp`,
`crd_mean`, `crd_pair`, `crd_supp`, `crd_prop_true`, and `crd_prop_false` are the moment and
propensity lemmas consumed by the unbiasedness and variance files.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-! ### General completely randomized design on `U → Bool` -/

section CRDon

variable {U : Type*} [Fintype U] [DecidableEq U] (K : ℕ) (hK : K ≤ Fintype.card U)

/-- The treated-set-to-indicator map: a size-`K` treated set `S` becomes the Boolean assignment that
flags unit `i` `true` exactly when `i ∈ S`. -/
def crdToBoolOn (S : {S : Finset U // S.card = K}) : U → Bool :=
  fun i => decide (i ∈ S.val)

/-- **The completely randomized design on `U → Bool`.**  Exactly `K` of the `N = card U` units are
treated, with every one of the `(N choose K)` treated sets equally likely.  Realized as the
pushforward of `completeRandomization K` (on size-`K` treated sets) along the indicator-vector
map `crdToBoolOn`. -/
noncomputable def crdOn : FiniteDesign (U → Bool) :=
  (completeRandomization K hK).map (crdToBoolOn K)

/-- **First-order inclusion probability:** each unit `i` is treated with probability `K/N`, i.e.
`E[Tᵢ] = K/N`.  Derived from `completeRandomization_incl`. -/
lemma crdOn_mean (i : U) :
    (crdOn K hK).E (FiniteDesign.ind fun w => w i = true) = (K : ℝ) / Fintype.card U := by
  rw [crdOn, FiniteDesign.E_map]
  have hfun : (fun S => FiniteDesign.ind (fun w => w i = true) (crdToBoolOn K S))
      = FiniteDesign.ind (fun S : {S : Finset U // S.card = K} => i ∈ S.val) := by
    funext S; by_cases h : i ∈ S.val <;> simp [crdToBoolOn, FiniteDesign.ind, h]
  rw [hfun, FiniteDesign.E_ind, completeRandomization_incl]

/-- **Complementary first moment:** each unit `i` is untreated with probability `(N−K)/N`, i.e.
`E[1−Tᵢ] = (N−K)/N`.  The control-arm propensity, from the indicator complement `1 − Tᵢ`. -/
lemma crdOn_mean_compl (i : U) :
    (crdOn K hK).E (fun w => 1 - FiniteDesign.ind (fun w => w i = true) w)
      = ((Fintype.card U : ℝ) - K) / Fintype.card U := by
  have hNpos : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  rw [FiniteDesign.E_sub, FiniteDesign.E_const, crdOn_mean]
  field_simp

/-- **Second-order inclusion probability:** two distinct units `i ≠ j` are jointly treated with
probability `K(K−1)/(N(N−1))`, i.e. `E[Tᵢ Tⱼ] = K(K−1)/(N(N−1))`.  Derived from
`completeRandomization_incl_pair`. -/
lemma crdOn_pair (i j : U) (hij : i ≠ j) :
    (crdOn K hK).E (fun w => (FiniteDesign.ind fun w => w i = true) w
        * (FiniteDesign.ind fun w => w j = true) w)
      = (K * (K - 1) : ℝ) / (Fintype.card U * ((Fintype.card U : ℝ) - 1)) := by
  rw [crdOn, FiniteDesign.E_map]
  have hfun : (fun S => (FiniteDesign.ind (fun w => w i = true) (crdToBoolOn K S))
        * (FiniteDesign.ind (fun w => w j = true) (crdToBoolOn K S)))
      = FiniteDesign.ind
          (fun S : {S : Finset U // S.card = K} => i ∈ S.val ∧ j ∈ S.val) := by
    funext S
    by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;>
      simp [crdToBoolOn, FiniteDesign.ind, hi, hj]
  rw [hfun, FiniteDesign.E_ind, completeRandomization_incl_pair _ _ hij]

/-- **Deterministic treated count** on the design's support: any assignment with positive design
weight treats exactly `K` units, i.e. `∑ᵢ Tᵢ = K`. -/
lemma crdOn_supp (w : U → Bool) (hw : (crdOn K hK).p w ≠ 0) :
    (∑ i, (FiniteDesign.ind fun w => w i = true) w) = (K : ℝ) := by
  rw [crdOn] at hw
  simp only [FiniteDesign.map_p] at hw
  obtain ⟨S, _, hSne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  have hSw : crdToBoolOn K S = w := by
    by_contra h; simp [h] at hSne
  have hiff : ∀ i, (w i = true) ↔ i ∈ S.val := by
    intro i
    have : w i = decide (i ∈ S.val) := by rw [← hSw]; rfl
    rw [this, decide_eq_true_eq]
  have hstep : (∑ i, (FiniteDesign.ind fun w => w i = true) w)
      = ∑ i, if i ∈ S.val then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold FiniteDesign.ind
    by_cases h : i ∈ S.val <;> simp [hiff i, h]
  rw [hstep, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast S.property

end CRDon

/-! ### Within-group specialization to `U = Fin n` -/

section CRD

variable {n : ℕ} (K : ℕ) (hK : K ≤ n)

/-- The within-group treated-set-to-indicator map (specialization of `crdToBoolOn` to `Fin n`). -/
def crdToBool (S : {S : Finset (Fin n) // S.card = K}) : Fin n → Bool := crdToBoolOn K S

/-- **The within-group completely randomized design on `Fin n → Bool`.**  Exactly `K` of the `n`
units are treated, uniformly over the `(n choose K)` treated sets — the `U = Fin n` specialization
of `crdOn`. -/
noncomputable def crd : FiniteDesign (Fin n → Bool) :=
  crdOn K (hK.trans_eq (Fintype.card_fin n).symm)

/-- **First-order inclusion probability** of the within-group design: `E[Tⱼ] = K/n`. -/
lemma crd_mean (j : Fin n) :
    (crd K hK).E (FiniteDesign.ind fun w => w j = true) = (K : ℝ) / n := by
  rw [crd, crdOn_mean, Fintype.card_fin]

/-- **Second-order inclusion probability** of the within-group design:
`E[Tⱼ Tₖ] = K(K−1)/(n(n−1))` for `j ≠ k`. -/
lemma crd_pair (j k : Fin n) (hjk : j ≠ k) :
    (crd K hK).E (fun w => (FiniteDesign.ind fun w => w j = true) w
        * (FiniteDesign.ind fun w => w k = true) w)
      = (K * (K - 1) : ℝ) / (n * (n - 1)) := by
  rw [crd, crdOn_pair _ _ _ _ hjk, Fintype.card_fin]

/-- **Deterministic treated count** on the within-group design's support: `∑ⱼ Tⱼ = K`. -/
lemma crd_supp (w : Fin n → Bool) (hw : (crd K hK).p w ≠ 0) :
    (∑ j, (FiniteDesign.ind fun w => w j = true) w) = (K : ℝ) := by
  rw [crd] at hw
  exact crdOn_supp K _ w hw

/-- **Treatment propensity** of the within-group design: each unit `j` is treated with probability
`K/n`, i.e. `Pr[wⱼ = true] = K/n`. -/
lemma crd_prop_true (j : Fin n) :
    (crd K hK).Pr (fun w => w j = true) = (K : ℝ) / n :=
  crd_mean K hK j

/-- **Control propensity** of the within-group design: each unit `j` is in control with probability
`(n−K)/n`, i.e. `Pr[wⱼ = false] = (n−K)/n`. -/
lemma crd_prop_false (j : Fin n) :
    (crd K hK).Pr (fun w => w j = false) = ((n : ℝ) - K) / n := by
  have hind : (FiniteDesign.ind fun w : Fin n → Bool => w j = false)
      = (fun w : Fin n → Bool => 1 - FiniteDesign.ind (fun w => w j = true) w) := by
    funext w; unfold FiniteDesign.ind; cases hw : w j <;> simp [hw]
  change (crd K hK).E (FiniteDesign.ind fun w : Fin n → Bool => w j = false) = _
  rw [hind, crd, crdOn_mean_compl, Fintype.card_fin]

end CRD

end TwoStageInterference
end Experimentation
end Causalean
