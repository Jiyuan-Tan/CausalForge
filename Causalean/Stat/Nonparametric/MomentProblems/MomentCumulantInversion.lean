/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.Cumulant
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The triangular moment ↔ cumulant change of coordinates

Cumulants are polynomials in the moments, and the polynomial of order `r` involves the moment of
order `r` linearly (with coefficient one) plus a remainder built only from strictly lower moments.
That triangularity means the change of coordinates inverts: prescribing a cumulant sequence
determines a moment sequence, recursively and uniquely, among sequences normalized to have total
mass one and mean zero.

This module sets up both directions on abstract sequences of reals — no measure is needed to state
them — and connects the forward direction to the measure-theoretic cumulant of a real random
variable.  It also records the two structural facts the inversion is used for downstream: each
reconstructed moment depends only on the prescribed cumulants **up to the same order** (locality),
and depends **continuously** on them.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The order-`r` **cumulant read off from a moment sequence**: the set-partition (Möbius) formula
that expresses the `r`-th cumulant as a signed, factorial-weighted sum over partitions of `r`
slots of products of moments, one moment per block, at the block's size. -/
noncomputable def cumFromMom (r : ℕ) (m : ℕ → ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin r)),
    (-1 : ℝ) ^ (π.parts.card - 1) * (Nat.factorial (π.parts.card - 1) : ℝ) *
      ∏ B ∈ π.parts, m B.card

/-- The **lower-order remainder** of the order-`r` cumulant formula: the same sum with the single
one-block partition removed.  Because every block of a multi-block partition is a proper subset,
this depends only on moments of order strictly below `r`. -/
noncomputable def restFromMom (r : ℕ) (m : ℕ → ℝ) : ℝ :=
  ∑ π ∈ Finset.univ.filter
      (fun π : Finpartition (Finset.univ : Finset (Fin r)) => π.parts.card ≠ 1),
    (-1 : ℝ) ^ (π.parts.card - 1) * (Nat.factorial (π.parts.card - 1) : ℝ) *
      ∏ B ∈ π.parts, m B.card

private lemma block_card_pos {r : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin r))) {B : Finset (Fin r)}
    (hB : B ∈ π.parts) : 1 ≤ B.card := by
  exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (π.ne_bot hB))

private lemma block_card_le {r : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin r))) {B : Finset (Fin r)}
    (hB : B ∈ π.parts) : B.card ≤ r := by
  simpa using Finset.card_le_card (π.le hB)

private lemma block_card_lt_of_card_ne_one {r : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin r))) (hπ : π.parts.card ≠ 1)
    {B : Finset (Fin r)} (hB : B ∈ π.parts) : B.card < r := by
  have hle := block_card_le π hB
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hBuniv : B = Finset.univ := Finset.eq_univ_of_card B (by simp [heq])
  have hparts : π.parts = {B} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hB, ?_⟩
    intro C hC
    by_contra hCB
    have hd : Disjoint B C := π.disjoint hB hC (fun h => hCB h.symm)
    rw [hBuniv] at hd
    have : C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (Finset.disjoint_left.mp hd) (Finset.mem_univ _) hx
    exact π.ne_bot hC this
  exact hπ (by simp [hparts])

/-- The cumulant of a real random variable is the abstract cumulant formula evaluated at that
variable's own raw-moment sequence: the measure-theoretic and combinatorial definitions agree. -/
theorem sourceCumulant_eq_cumFromMom (ν : Measure ℝ) (r : ℕ) :
    sourceCumulant ν (id : ℝ → ℝ) r = cumFromMom r (fun k => ∫ t, t ^ k ∂ν) := by
  unfold sourceCumulant jointCumulant cumFromMom
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  apply Finset.prod_congr rfl
  intro B hB
  have hfirst : B.filter (fun i => i.val < r) = B :=
    Finset.filter_true_of_mem (fun i _ => i.isLt)
  have hsecond : B.filter (fun i => r ≤ i.val) = ∅ :=
    Finset.filter_false_of_mem (fun i _ hi => (not_le_of_gt i.isLt) hi)
  rw [hsecond]
  simp

/-- **Triangularity.** At any positive order the cumulant equals the moment of that same order plus
a remainder assembled only from strictly lower moments.  This is what makes the moment-to-cumulant
map invertible by recursion. -/
theorem cumFromMom_eq (r : ℕ) (hr : 1 ≤ r) (m : ℕ → ℝ) :
    cumFromMom r m = m r + restFromMom r m := by
  let P₀ : Finpartition (Finset.univ : Finset (Fin r)) :=
    Finpartition.indiscrete (by
      intro hempty
      have hx : (⟨0, hr⟩ : Fin r) ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ _
      have hempty' : (Finset.univ : Finset (Fin r)) = ∅ := by simpa using hempty
      rw [hempty'] at hx
      exact Finset.notMem_empty _ hx)
  have hfiber : Finset.univ.filter
      (fun π : Finpartition (Finset.univ : Finset (Fin r)) => π.parts.card = 1) = {P₀} := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hp
      have hB : B = (Finset.univ : Finset (Fin r)) := by
        have := π.sup_parts
        simpa [hparts] using this
      apply Finpartition.ext
      simp [P₀, hparts, hB]
    · rintro rfl
      simp [P₀]
  rw [cumFromMom, ← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun π : Finpartition (Finset.univ : Finset (Fin r)) =>
      π.parts.card = 1)]
  rw [hfiber, Finset.sum_singleton]
  simp [P₀, restFromMom]

/-- The order-`r` cumulant depends only on the moments up to order `r`: changing higher moments
leaves it unchanged. -/
theorem cumFromMom_congr (r : ℕ) {m m' : ℕ → ℝ}
    (h : ∀ k, 1 ≤ k → k ≤ r → m k = m' k) :
    cumFromMom r m = cumFromMom r m' := by
  unfold cumFromMom
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  apply Finset.prod_congr rfl
  intro B hB
  exact h B.card (block_card_pos π hB) (block_card_le π hB)

/-- The lower-order remainder at order `r` depends only on the moments **strictly below** `r`:
changing the order-`r` moment, or any higher one, leaves it unchanged. -/
theorem restFromMom_congr (r : ℕ) {m m' : ℕ → ℝ}
    (h : ∀ k, 1 ≤ k → k < r → m k = m' k) :
    restFromMom r m = restFromMom r m' := by
  unfold restFromMom
  apply Finset.sum_congr rfl
  intro π hπ
  have hcard : π.parts.card ≠ 1 := (Finset.mem_filter.mp hπ).2
  congr 1
  apply Finset.prod_congr rfl
  intro B hB
  exact h B.card (block_card_pos π hB) (block_card_lt_of_card_ne_one π hcard hB)

/-- The **moment sequence reconstructed from a prescribed cumulant sequence**, by inverting the
triangular formula: total mass one, mean zero, and at each order at least two the moment is the
prescribed cumulant minus the remainder assembled from the already-reconstructed lower moments. -/
noncomputable def momFromCum (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | Nat.succ (Nat.succ r) => c (r + 2) - restFromMom (r + 2)
      (fun k => if _h : k < r + 2 then momFromCum c k else 0)
termination_by n => n
decreasing_by omega

/-- The reconstructed moment sequence has total mass one. -/
@[simp] theorem momFromCum_zero (c : ℕ → ℝ) : momFromCum c 0 = 1 := by
  rw [momFromCum]

/-- The reconstructed moment sequence is centered: its mean is zero. -/
@[simp] theorem momFromCum_one (c : ℕ → ℝ) : momFromCum c 1 = 0 := by
  rw [momFromCum]

/-- The defining recursion: at every order at least two, the reconstructed moment is the target
cumulant of that order minus the remainder built from the lower reconstructed moments. -/
theorem momFromCum_succ (c : ℕ → ℝ) (r : ℕ) (hr : 2 ≤ r) :
    momFromCum c r = c r - restFromMom r (momFromCum c) := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ n =>
      rw [momFromCum]
      congr 1
      apply restFromMom_congr
      intro k _ hk
      simp [hk]

/-- **Correctness of the inversion.** Reading the cumulants back off the reconstructed moment
sequence returns the prescribed cumulants, at every order at least two. -/
theorem cumFromMom_momFromCum (c : ℕ → ℝ) (r : ℕ) (hr : 2 ≤ r) :
    cumFromMom r (momFromCum c) = c r := by
  rw [cumFromMom_eq r (by omega), momFromCum_succ c r hr]
  ring

/-- **Locality of the inversion.** The reconstructed moment of order `r` depends only on the
prescribed cumulants of orders two through `r`, so truncating the cumulant target beyond `r` is
harmless. -/
theorem momFromCum_congr {c c' : ℕ → ℝ} (r : ℕ)
    (h : ∀ k, 2 ≤ k → k ≤ r → c k = c' k) :
    momFromCum c r = momFromCum c' r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : 2 ≤ r
    · rw [momFromCum_succ c r hr, momFromCum_succ c' r hr, h r hr le_rfl]
      congr 1
      apply restFromMom_congr
      intro k hkpos hkr
      exact ih k hkr (fun j hj hjk => h j hj (hjk.trans (Nat.le_of_lt hkr)))
    · interval_cases r <;> simp

/-- **Continuity of the inversion.** Each reconstructed moment is a continuous function of the
prescribed cumulant sequence, so small perturbations of the target cumulants move the moments only
slightly — the key to the openness arguments that use this inversion. -/
theorem continuous_momFromCum (r : ℕ) :
    Continuous (fun c : ℕ → ℝ => momFromCum c r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : 2 ≤ r
    · simp_rw [momFromCum_succ _ r hr]
      apply (continuous_apply r).sub
      unfold restFromMom
      apply continuous_finset_sum
      intro π _
      apply continuous_const.mul
      apply continuous_finset_prod
      intro B hB
      exact ih B.card (block_card_lt_of_card_ne_one π
        ((Finset.mem_filter.mp ‹π ∈ Finset.univ.filter _›).2) hB)
    · interval_cases r
      · simpa only [momFromCum_zero] using
          (continuous_const : Continuous (fun _ : ℕ → ℝ => (1 : ℝ)))
      · simpa only [momFromCum_one] using
          (continuous_const : Continuous (fun _ : ℕ → ℝ => (0 : ℝ)))

/-- **Uniqueness of the inversion.** Any moment sequence with total mass one and mean zero whose
cumulants are the prescribed ones is exactly the sequence produced by the recursion. -/
theorem momFromCum_eq_of_cum (m : ℕ → ℝ) (hm0 : m 0 = 1) (hm1 : m 1 = 0)
    (c : ℕ → ℝ) (hc : ∀ r, 2 ≤ r → c r = cumFromMom r m) (r : ℕ) :
    momFromCum c r = m r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : 2 ≤ r
    · rw [momFromCum_succ c r hr, hc r hr, cumFromMom_eq r (by omega)]
      have hrest : restFromMom r (momFromCum c) = restFromMom r m := by
        apply restFromMom_congr
        intro k _ hkr
        exact ih k hkr
      rw [hrest]
      ring
    · interval_cases r <;> simp [hm0, hm1]

end Causalean.Stat.MomentProblems
