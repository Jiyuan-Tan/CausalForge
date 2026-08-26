/- Deterministic aggregate identity for the all-block marked factorial statistic. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.FoldRiskBridge

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open scoped BigOperators

/-- This bijection decomposes a marked tuple into its distinguished coordinate and the remaining
  coordinates. -/
noncomputable def markedTupleEquiv (j : ℕ) (J : Type*) [DecidableEq J] :
    (Fin (j + 2) ↪ J) ≃ Σ i : J, Fin (j + 1) ↪ {q : J // q ≠ i} where
  toFun e := ⟨e 0, {
    toFun := fun q => ⟨e q.succ, fun h =>
      Fin.succ_ne_zero q (e.injective h)⟩
    inj' := fun q r h => by
      apply Fin.ext
      apply Nat.succ.inj
      exact congrArg Fin.val (e.injective (congrArg Subtype.val h)) }⟩
  invFun p := {
    toFun := Fin.cons p.1 (fun q => (p.2 q).val)
    inj' := by
      rw [Fin.cons_injective_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨q, hq⟩
        exact (p.2 q).property hq
      · exact fun q r h => p.2.injective (Subtype.ext h) }
  left_inv e := by
    ext q
    refine Fin.cases ?_ (fun q => ?_) q
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨i, e⟩
    rfl

/-- If [the specified marked tuple](hyp:p), [the inverse marked-tuple decomposition recovers the
  distinguished coordinate at position zero](goal). -/
@[simp] lemma markedTupleEquiv_symm_zero (j : ℕ) (J : Type*) [DecidableEq J]
    (p : Σ i : J, Fin (j + 1) ↪ {q : J // q ≠ i}) :
    ((markedTupleEquiv j J).symm p) 0 = p.1 := rfl

/-- If [the specified marked tuple](hyp:p), [the inverse marked-tuple decomposition recovers each
  tail coordinate at its successor position](goal). -/
@[simp] lemma markedTupleEquiv_symm_succ (j : ℕ) (J : Type*) [DecidableEq J]
    (p : Σ i : J, Fin (j + 1) ↪ {q : J // q ≠ i})
    (q : Fin (j + 1)) :
    ((markedTupleEquiv j J).symm p) q.succ = (p.2 q).val := rfl

open CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- [removing the distinguished coordinate rewrites the weighted matching count in terms of its
  tail pattern](goal). -/
lemma weightedMatchingCount_remove_zero {j : ℕ} {A J : Type*}
    [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (g : Fin (j + 2) → A) (z : J → A) (w : J → ℝ) :
    (∑ e : Fin (j + 2) ↪ J,
      if ∀ q, z (e q) = g q then w (e 0) else 0) =
      ∑ i : J, w i * (if z i = g 0 then
        matchingCount (fun q : Fin (j + 1) => g q.succ)
          (fun q : {q : J // q ≠ i} => z q) else 0) := by
  classical
  rw [Fintype.sum_equiv (markedTupleEquiv j J)
    (fun e : Fin (j + 2) ↪ J =>
      if ∀ q, z (e q) = g q then w (e 0) else 0)
    (fun p => if ∀ q, z (((markedTupleEquiv j J).symm p) q) = g q then
      w (((markedTupleEquiv j J).symm p) 0) else 0)
    (fun e => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.forall_fin_succ, markedTupleEquiv_symm_zero,
    markedTupleEquiv_symm_succ]
  simp only [matchingCount]
  by_cases h0 : z i = g 0
  · simp only [h0, true_and, if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    by_cases ht : ∀ q : Fin (j + 1), z (f q) = g q.succ
    · have ht' : z (f 0) = g (Fin.succ 0) ∧
          ∀ q : Fin j, z (f q.succ) = g q.succ.succ := by
        simpa only [Fin.forall_fin_succ] using ht
      simp [ht, ht']
    · have ht' : ¬ (z (f 0) = g (Fin.succ 0) ∧
          ∀ q : Fin j, z (f q.succ) = g q.succ.succ) := by
        simpa only [Fin.forall_fin_succ] using ht
      have hsplit : ¬ (z (f 0) = g 1 ∧
          ∀ q : Fin j, z (f q.succ) = g q.succ.succ) := by
        intro hs
        apply ht'
        exact ⟨by simpa using hs.1, hs.2⟩
      simp [hsplit, ht]
  · simp [h0]

/-- If [the stated i condition holds](hyp:hi), [the complement fiber of a finite Boolean pattern
  has cardinality equal to the total size minus the selected fiber size](goal). -/
lemma complementFiber_card {A J : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq A] (z : J → A) (i : J) (a c : A) (hi : z i = a) :
    Fintype.card {q : {q : J // q ≠ i} // z q = c} =
      if c = a then Fintype.card {q : J // z q = c} - 1
      else Fintype.card {q : J // z q = c} := by
  classical
  let e : {q : {q : J // q ≠ i} // z q = c} ≃
      {q : {q : J // z q = c} // q.1 ≠ i} :=
    { toFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2⟩
      invFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2⟩
      left_inv := fun q => by cases q; rfl
      right_inv := fun q => by cases q; rfl }
  rw [Fintype.card_congr e]
  by_cases hca : c = a
  · subst c
    simp only [if_true, Fintype.card_subtype]
    let ii : {q : J // z q = a} := ⟨i, hi⟩
    rw [show (Finset.univ.filter fun q : {q : J // z q = a} => q.1 ≠ i) =
        Finset.univ.erase ii by
      ext q
      simp [ii, Subtype.ext_iff]]
    rw [Finset.card_erase_of_mem (Finset.mem_univ ii), Finset.card_univ]
    rw [← Fintype.card_subtype]
  · simp only [if_neg hca, Fintype.card_subtype]
    rw [show (Finset.univ.filter fun q : {q : J // z q = c} => q.1 ≠ i) =
        Finset.univ by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, iff_true]
      refine ⟨trivial, ?_⟩
      intro hqi
      apply hca
      subst i
      exact q.2.symm.trans hi]
    rw [Finset.card_univ, ← Fintype.card_subtype]

/-- This Boolean tail pattern records whether each remaining coordinate matches a designated arm. -/
def boolTailPattern (j : ℕ) (a b : Bool) : Fin (j + 1) → Bool :=
  Fin.cases b (fun _ => a)

/-- This Boolean marked pattern adds the distinguished arm to the tail pattern. -/
def boolMarkedPattern (j : ℕ) (a b : Bool) : Fin (j + 2) → Bool :=
  Fin.cons a (boolTailPattern j a b)

/-- [every coordinate of the same-arm Boolean tail pattern equals the designated arm](goal). -/
lemma boolTailPattern_same (j : ℕ) (a : Bool) :
    boolTailPattern j a a = fun _ => a := by
  funext q
  refine Fin.cases rfl (fun _ => rfl) q

/-- If [the stated i condition holds](hyp:hi), [the same-arm Boolean tail pattern has the full
  matching count](goal). -/
lemma matchingCount_boolTail_same {J : Type*} [Fintype J] [DecidableEq J]
    (z : J → Bool) (i : J) (a : Bool) (j : ℕ) (hi : z i = a) :
    matchingCount (boolTailPattern j a a)
        (fun q : {q : J // q ≠ i} => z q) =
      ((Fintype.card {q : J // z q = a} - 1).descFactorial (j + 1) : ℝ) := by
  classical
  rw [boolTailPattern_same]
  rw [matchingCount_eq_prod]
  simp_rw [complementFiber_card z i a _ hi]
  cases a <;>
    simp [PatternFiber, Fintype.card_subtype]

/-- [for the opposite-arm tail pattern, the fiber over the designated arm has cardinality
  zero](goal). -/
lemma card_boolTailPattern_other_fiber_self (j : ℕ) (a : Bool) :
    Fintype.card (PatternFiber (boolTailPattern j a (!a)) a) = j := by
  classical
  let e : PatternFiber (boolTailPattern j a (!a)) a ≃
      {q : Fin (j + 1) // q ≠ 0} :=
    Equiv.subtypeEquivProp (by
      funext q
      apply propext
      refine Fin.cases ?_ (fun q => ?_) q <;>
        cases a <;> simp [boolTailPattern])
  rw [Fintype.card_congr e, ← Fintype.card_congr (finSuccAboveEquiv 0)]
  exact Fintype.card_fin j

/-- [for the opposite-arm tail pattern, the fiber over the other arm has full tail
  cardinality](goal). -/
lemma card_boolTailPattern_other_fiber_not (j : ℕ) (a : Bool) :
    Fintype.card (PatternFiber (boolTailPattern j a (!a)) (!a)) = 1 := by
  classical
  let e : PatternFiber (boolTailPattern j a (!a)) (!a) ≃
      {q : Fin (j + 1) // q = 0} :=
    Equiv.subtypeEquivProp (by
      funext q
      apply propext
      refine Fin.cases ?_ (fun q => ?_) q <;>
        cases a <;> simp [boolTailPattern])
  rw [Fintype.card_congr e]
  exact Fintype.card_subtype_eq 0

/-- If [the stated i condition holds](hyp:hi), [the opposite-arm Boolean tail pattern has the
  stated complementary matching count](goal). -/
lemma matchingCount_boolTail_other {J : Type*} [Fintype J] [DecidableEq J]
    (z : J → Bool) (i : J) (a : Bool) (j : ℕ) (hi : z i = a) :
    matchingCount (boolTailPattern j a (!a))
        (fun q : {q : J // q ≠ i} => z q) =
      ((Fintype.card {q : J // z q = a} - 1).descFactorial j : ℝ) *
        Fintype.card {q : J // z q = !a} := by
  classical
  rw [matchingCount_eq_prod]
  simp_rw [complementFiber_card z i a _ hi]
  have hpattern : ∀ c : Bool,
      Fintype.card (PatternFiber (boolTailPattern j a (!a)) c) =
        if c = a then j else 1 := by
    intro c
    by_cases hca : c = a
    · subst c
      simpa using card_boolTailPattern_other_fiber_self j a
    · have hcnot : c = !a := by
        cases a <;> cases c <;> simp_all
      subst c
      simpa using card_boolTailPattern_other_fiber_not j a
  simp_rw [hpattern]
  cases a <;>
    simp [boolTailPattern, PatternFiber, Fintype.card_subtype,
      Nat.descFactorial_one, mul_comm]

/-- [the same-arm Boolean pattern has the stated weighted matching value](goal). -/
lemma weightedMatching_bool_same {J : Type*} [Fintype J] [DecidableEq J]
    (z : J → Bool) (w : J → ℝ) (a : Bool) (j : ℕ) :
    (∑ e : Fin (j + 2) ↪ J,
      if ∀ q, z (e q) = boolMarkedPattern j a a q then w (e 0) else 0) =
      (∑ i : J, if z i = a then w i else 0) *
        ((Fintype.card {i : J // z i = a} - 1).descFactorial (j + 1) : ℝ) := by
  classical
  rw [weightedMatchingCount_remove_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z i = a
  · simp only [boolMarkedPattern, Fin.cons_zero, hi, if_pos]
    change w i * matchingCount (boolTailPattern j a a)
      (fun q : {q : J // q ≠ i} => z q) = _
    rw [matchingCount_boolTail_same z i a j hi]
  · simp [boolMarkedPattern, hi]

/-- [the opposite-arm Boolean pattern has the stated weighted matching value](goal). -/
lemma weightedMatching_bool_other {J : Type*} [Fintype J] [DecidableEq J]
    (z : J → Bool) (w : J → ℝ) (a : Bool) (j : ℕ) :
    (∑ e : Fin (j + 2) ↪ J,
      if ∀ q, z (e q) = boolMarkedPattern j a (!a) q then w (e 0) else 0) =
      (∑ i : J, if z i = a then w i else 0) *
        (((Fintype.card {i : J // z i = a} - 1).descFactorial j : ℝ) *
          Fintype.card {i : J // z i = !a}) := by
  classical
  rw [weightedMatchingCount_remove_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z i = a
  · simp only [boolMarkedPattern, Fin.cons_zero, hi, if_pos]
    change w i * matchingCount (boolTailPattern j a (!a))
      (fun q : {q : J // q ≠ i} => z q) = _
    rw [matchingCount_boolTail_other z i a j hi]
  · simp [boolMarkedPattern, hi]

/-- [the two Boolean fibers of a marked pattern have cardinalities that sum to the pattern
  length](goal). -/
lemma bool_fiber_card_add (J : Type*) [Fintype J] [DecidableEq J]
    (z : J → Bool) (a : Bool) :
    Fintype.card {i : J // z i = a} + Fintype.card {i : J // z i = !a} =
      Fintype.card J := by
  classical
  simp only [Fintype.card_subtype]
  rw [← Finset.card_univ]
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : J => z i = a)]
  congr 2
  ext i
  cases a <;> cases z i <;> simp

/-- [a property holds for every marked Boolean pattern exactly when it holds for the two possible
  marked arms and every tail pattern](goal). -/
lemma forall_boolMarkedPattern_iff {J : Type*} (z : J → Bool)
    {j : ℕ} (e : Fin (j + 2) ↪ J) (a b : Bool) :
    (∀ q, z (e q) = boolMarkedPattern j a b q) ↔
      z (e 0) = a ∧ z (e 1) = b ∧
        ∀ q : Fin j, z (e q.succ.succ) = a := by
  simp [boolMarkedPattern, boolTailPattern, Fin.forall_fin_succ]

/-- [the unrestricted weighted marked sum reduces to the sum of the two Boolean arm cases](goal). -/
lemma weightedMarkedUnrestricted {J : Type*} [Fintype J] [DecidableEq J]
    (z : J → Bool) (w : J → ℝ) (a : Bool) (j : ℕ) :
    (∑ e : Fin (j + 2) ↪ J,
      if z (e 0) = a ∧ ∀ q : Fin j, z (e q.succ.succ) = a
      then w (e 0) else 0) =
      (∑ i : J, if z i = a then w i else 0) *
        ((Fintype.card {i : J // z i = a} - 1).descFactorial j : ℝ) *
        (Fintype.card J - (j + 1) : ℕ) := by
  classical
  have hsplit : (∑ e : Fin (j + 2) ↪ J,
      if z (e 0) = a ∧ ∀ q : Fin j, z (e q.succ.succ) = a
      then w (e 0) else 0) =
      (∑ e : Fin (j + 2) ↪ J,
        if ∀ q, z (e q) = boolMarkedPattern j a a q then w (e 0) else 0) +
      (∑ e : Fin (j + 2) ↪ J,
        if ∀ q, z (e q) = boolMarkedPattern j a (!a) q then w (e 0) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp only [forall_boolMarkedPattern_iff]
    by_cases h0 : z (e 0) = a
    · by_cases h1 : z (e 1) = a
      · simp [h0, h1, boolMarkedPattern, boolTailPattern,
          Fin.forall_fin_succ]
      · have h1' : z (e 1) = !a := Bool.eq_not_iff.mpr h1
        simp [h0, h1, h1', boolMarkedPattern, boolTailPattern,
          Fin.forall_fin_succ]
    · simp [h0, boolMarkedPattern, Fin.forall_fin_succ]
  rw [hsplit, weightedMatching_bool_same, weightedMatching_bool_other]
  let S : ℝ := ∑ i : J, if z i = a then w i else 0
  let A : ℕ := Fintype.card {i : J // z i = a}
  let O : ℕ := Fintype.card {i : J // z i = !a}
  have hJO : A + O = Fintype.card J := bool_fiber_card_add J z a
  change S * ((A - 1).descFactorial (j + 1) : ℝ) +
      S * (((A - 1).descFactorial j : ℝ) * O) =
    S * ((A - 1).descFactorial j : ℝ) * (Fintype.card J - (j + 1) : ℕ)
  by_cases hA : A = 0
  · have hS : S = 0 := by
      unfold S A at *
      rw [Fintype.card_eq_zero_iff] at hA
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : z i = a
      · rw [if_pos hi]
        have hf : False := @isEmptyElim _ hA (fun _ => False) ⟨i, hi⟩
        exact hf.elim
      · simp [hi]
    simp [hS]
  · have hApos : 0 < A := Nat.pos_of_ne_zero hA
    rw [Nat.descFactorial_succ]
    by_cases hj : j ≤ A - 1
    · have harith : (A - 1 - j) + O = A + O - (j + 1) := by omega
      push_cast
      rw [← hJO, ← harith]
      rw [Nat.cast_add]
      ring
    · have hfact : (A - 1).descFactorial j = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hj)
      simp [hfact]

/-- An injective embedding identifies its domain with the subtype of points in its range. -/
noncomputable def embeddingSubtypeRangeEquiv {J : Type*} (r : ℕ)
    (p : J → Prop) [DecidablePred p] :
    (Fin r ↪ {i : J // p i}) ≃ {e : Fin r ↪ J // ∀ q, p (e q)} where
  toFun e := ⟨e.trans (Function.Embedding.subtype _), fun q => (e q).2⟩
  invFun e := {
    toFun := fun q => ⟨e.1 q, e.2 q⟩
    inj' := fun q s h => e.1.injective (congrArg Subtype.val h) }
  left_inv e := by ext q; rfl
  right_inv e := by ext q; rfl

/-- [summing a range-indicator over the target of an embedding recovers the sum over the
  source](goal). -/
lemma sum_embedding_range_indicator {J : Type*} [Fintype J] [DecidableEq J]
    (r : ℕ) (p : J → Prop) [DecidablePred p]
    (F : (Fin r ↪ J) → ℝ) :
    (∑ e : Fin r ↪ J, if ∀ q, p (e q) then F e else 0) =
      ∑ e : Fin r ↪ {i : J // p i},
        F (e.trans (Function.Embedding.subtype _)) := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun e : Fin r ↪ J => ∀ q, p (e q))
    ((Finset.univ : Finset (Fin r ↪ J)).filter fun e => ∀ q, p (e q))
    (fun e => by simp) F]
  exact Fintype.sum_equiv (embeddingSubtypeRangeEquiv r p).symm _ _
    (fun _ => rfl)

/-- [for an injective function, summing its range-indicator over the codomain recovers the domain
  sum](goal). -/
lemma sum_function_injective_indicator {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (F : (I → J) → ℝ) :
    (∑ f : I → J, if Function.Injective f then F f else 0) =
      ∑ e : I ↪ J, F e := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := Function.Injective)
    ((Finset.univ : Finset (I → J)).filter Function.Injective)
    (fun f => by simp) F]
  let e : {f : I → J // Function.Injective f} ≃ (I ↪ J) :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun f => by cases f; rfl
      right_inv := fun f => by cases f; rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- [the marked kernel equals its explicit conditional product formula](goal). -/
lemma markedKernel_eq_ite {m d j : ℕ} (M : ℝ) (sample : Fin m → Obs d)
    (k : Fin d) (a : Bool) (e : Fin (j + 2) ↪ Fin m) :
    ((sample (e 0)).y / M) *
        (if (sample (e 0)).x = k ∧ (sample (e 0)).a = a then 1 else 0) *
        (if (sample (e 1)).x = k then 1 else 0) *
        (∏ q : Fin (j + 2),
          if 2 ≤ q.val then
            if (sample (e q)).x = k ∧ (sample (e q)).a = a then 1 else 0
          else 1) =
      if ((sample (e 0)).x = k ∧ (sample (e 0)).a = a) ∧
          (sample (e 1)).x = k ∧
          (∀ q : Fin (j + 2), 2 ≤ q.val →
            (sample (e q)).x = k ∧ (sample (e q)).a = a)
      then (sample (e 0)).y / M else 0 := by
  classical
  simp_rw [show ∀ q : Fin (j + 2),
      (if 2 ≤ q.val then
        if (sample (e q)).x = k ∧ (sample (e q)).a = a then (1 : ℝ) else 0
      else 1) =
      if (2 ≤ q.val → (sample (e q)).x = k ∧ (sample (e q)).a = a)
      then 1 else 0 by
    intro q
    by_cases hq : 2 ≤ q.val <;> simp [hq]]
  rw [Fintype.prod_boole]
  by_cases h0 : (sample (e 0)).x = k ∧ (sample (e 0)).a = a <;>
    by_cases h1 : (sample (e 1)).x = k <;>
    simp [h0, h1]

/-- [a property holds for every finite index at least two exactly when it holds for every index
  after removing the first two positions](goal). -/
lemma forall_two_le_fin_iff {j : ℕ} {P : Fin (j + 2) → Prop} :
    (∀ q : Fin (j + 2), 2 ≤ q.val → P q) ↔
      ∀ q : Fin j, P q.succ.succ := by
  simp [Fin.forall_fin_succ]

/-- [the subtype of sample indices in a given arm and cell has cardinality equal to the
  corresponding arm-cell count](goal). -/
lemma groupArmSubtype_card {m d : ℕ} (sample : Fin m → Obs d)
    (k : Fin d) (a : Bool) :
    Fintype.card {i : {i : Fin m // (sample i).x = k} // (sample i).a = a} =
      Causalean.Stat.groupArmCount (fun o : Obs d => o.x) (fun o => o.a)
        sample a k := by
  classical
  let e : {i : {i : Fin m // (sample i).x = k} // (sample i).a = a} ≃
      {i : Fin m // (sample i).x = k ∧ (sample i).a = a} :=
    { toFun := fun i => ⟨i.1.1, i.1.2, i.2⟩
      invFun := fun i => ⟨⟨i.1, i.2.1⟩, i.2.2⟩
      left_inv := fun i => by cases i; rfl
      right_inv := fun i => by cases i; rfl }
  rw [Fintype.card_congr e]
  unfold Causalean.Stat.groupArmCount
  exact Fintype.card_subtype _

/-- [the subtype of sample indices in a given cell has cardinality equal to the corresponding cell
  count](goal). -/
lemma groupSubtype_card {m d : ℕ} (sample : Fin m → Obs d) (k : Fin d) :
    Fintype.card {i : Fin m // (sample i).x = k} =
      Causalean.Stat.groupCount (fun o : Obs d => o.x) (fun o => o.a)
        sample k := by
  rw [← bool_fiber_card_add {i : Fin m // (sample i).x = k}
    (fun i => (sample i).a) false]
  rw [groupArmSubtype_card, groupArmSubtype_card]
  rfl

/-- [the normalized mark sum over a cell subtype equals the corresponding grouped mark sum divided
  by the outcome scale](goal). -/
lemma groupSubtype_markSum_div {m d : ℕ} (M : ℝ)
    (sample : Fin m → Obs d) (k : Fin d) (a : Bool) :
    (∑ i : {i : Fin m // (sample i).x = k},
      if (sample i).a = a then (sample i).y / M else 0) =
      Causalean.Stat.FiniteStratumMarkedRatioMse.armMarkSum
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y) sample a k / M := by
  classical
  unfold Causalean.Stat.FiniteStratumMarkedRatioMse.armMarkSum
    Causalean.Stat.FiniteStratumMarkedRatioMse.supportedArmMark
    Causalean.Stat.FiniteStratumMarkedRatioMse.armCategoryEvent
    Causalean.Stat.armGroupEvent Set.indicator
  simp only [Set.mem_ofPred_eq]
  rw [Finset.sum_div]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype
    (p := fun i : {i : Fin m // (sample i).x = k} => (sample i).a = a)
    ((Finset.univ : Finset {i : Fin m // (sample i).x = k}).filter
      fun i => (sample i).a = a) (fun i => by simp)
    (fun i => (sample i).y / M)]
  let e : {i : {i : Fin m // (sample i).x = k} // (sample i).a = a} ≃
      {i : Fin m // (sample i).x = k ∧ (sample i).a = a} :=
    { toFun := fun i => ⟨i.1.1, i.1.2, i.2⟩
      invFun := fun i => ⟨⟨i.1, i.2.1⟩, i.2.2⟩
      left_inv := fun i => by cases i; rfl
      right_inv := fun i => by cases i; rfl }
  rw [Fintype.sum_equiv e (fun i => (sample i.1.1).y / M)
    (fun i => (sample i.1).y / M) (fun _ => rfl)]
  rw [← Finset.sum_subtype
    (p := fun i : Fin m => (sample i).x = k ∧ (sample i).a = a)
    ((Finset.univ : Finset (Fin m)).filter
      fun i => (sample i).x = k ∧ (sample i).a = a) (fun i => by simp)
    (fun i => (sample i).y / M)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (sample i).x = k ∧ (sample i).a = a <;> simp [hi]

/-- [the marked-kernel matching condition is equivalent to the stated arm-and-cell coordinate
  conditions](goal). -/
lemma markedKernel_condition_iff {m d j : ℕ} (sample : Fin m → Obs d)
    (k : Fin d) (a : Bool) (e : Fin (j + 2) ↪ Fin m) :
    ((((sample (e 0)).x = k ∧ (sample (e 0)).a = a) ∧
        (sample (e 1)).x = k ∧
        (∀ q : Fin (j + 2), 2 ≤ q.val →
          (sample (e q)).x = k ∧ (sample (e q)).a = a))) ↔
      ((∀ q : Fin (j + 2), (sample (e q)).x = k) ∧
        (sample (e 0)).a = a ∧
        ∀ q : Fin j, (sample (e q.succ.succ)).a = a) := by
  rw [forall_two_le_fin_iff]
  simp only [Fin.forall_fin_succ]
  aesop

/-- [the all-block ordered marked factorial statistic equals its closed-form expression in the arm
  mark sum and descending factorial counts](goal). -/
lemma allBlockOrderedMarkedFactorial_eq_closed {m d : ℕ} (M : ℝ)
    (sample : Fin m → Obs d) (k : Fin d) (a : Bool) (j : ℕ) :
    allBlockOrderedMarkedFactorial M sample k a j =
      (Causalean.Stat.FiniteStratumMarkedRatioMse.armMarkSum
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y) sample a k / M) *
      ((Causalean.Stat.groupArmCount (fun o : Obs d => o.x) (fun o => o.a)
        sample a k - 1).descFactorial j : ℝ) *
      (Causalean.Stat.groupCount (fun o : Obs d => o.x) (fun o => o.a)
        sample k - (j + 1) : ℕ) /
      m.descFactorial (j + 2) := by
  classical
  unfold allBlockOrderedMarkedFactorial
  rw [sum_function_injective_indicator]
  simp_rw [markedKernel_eq_ite]
  simp_rw [markedKernel_condition_iff]
  have hsplit : (∑ e : Fin (j + 2) ↪ Fin m,
      if ((∀ q : Fin (j + 2), (sample (e q)).x = k) ∧
          (sample (e 0)).a = a ∧
          ∀ q : Fin j, (sample (e q.succ.succ)).a = a)
      then (sample (e 0)).y / M else 0) =
      ∑ e : Fin (j + 2) ↪ Fin m,
        if ∀ q, (sample (e q)).x = k then
          (if (sample (e 0)).a = a ∧
              ∀ q : Fin j, (sample (e q.succ.succ)).a = a
            then (sample (e 0)).y / M else 0)
        else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases hg : ∀ q, (sample (e q)).x = k <;> simp [hg]
  rw [hsplit]
  have hrange : (∑ e : Fin (j + 2) ↪ Fin m,
      if ∀ q, (sample (e q)).x = k then
        (if (sample (e 0)).a = a ∧
            ∀ q : Fin j, (sample (e q.succ.succ)).a = a
          then (sample (e 0)).y / M else 0)
      else 0) =
      ∑ e : Fin (j + 2) ↪ {i : Fin m // (sample i).x = k},
        if (sample (e 0)).a = a ∧
            ∀ q : Fin j, (sample (e q.succ.succ)).a = a
          then (sample (e 0)).y / M else 0 := by
    simpa using sum_embedding_range_indicator (J := Fin m) (r := j + 2)
      (fun i => (sample i).x = k)
      (fun e => if (sample (e 0)).a = a ∧
          ∀ q : Fin j, (sample (e q.succ.succ)).a = a
        then (sample (e 0)).y / M else 0)
  rw [hrange]
  have hweighted : (∑ e : Fin (j + 2) ↪ {i : Fin m // (sample i).x = k},
      if (sample (e 0)).a = a ∧
          ∀ q : Fin j, (sample (e q.succ.succ)).a = a
        then (sample (e 0)).y / M else 0) =
      (∑ i : {i : Fin m // (sample i).x = k},
        if (sample i).a = a then (sample i).y / M else 0) *
      ((Fintype.card {i : {i : Fin m // (sample i).x = k} //
          (sample i).a = a} - 1).descFactorial j : ℝ) *
      (Fintype.card {i : Fin m // (sample i).x = k} - (j + 1) : ℕ) := by
    simpa using weightedMarkedUnrestricted
      (J := {i : Fin m // (sample i).x = k})
      (fun i => (sample i).a) (fun i => (sample i).y / M) a j
  rw [hweighted]
  rw [groupSubtype_markSum_div, groupArmSubtype_card, groupSubtype_card]

-- @node: orderedMarkedFactorial_rebuild_eq_allBlock
/-- [The concrete estimation-block factorial is exactly the all-block statistic on the canonically
  reindexed estimation fold](goal). -/
lemma orderedMarkedFactorial_rebuild_eq_allBlock {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (M : ℝ) (k : Fin d) (a : Bool) (j : ℕ) :
    orderedMarkedFactorial M (rebuildPolynomialEstimationSample P base x) k a j =
      allBlockOrderedMarkedFactorial M (polynomialFoldBReindex P x) k a j := by
  unfold orderedMarkedFactorial estimationBlockSize
  rw [estimationArmSum_rebuild_eq_reindex,
    estimationArmCount_rebuild_eq_reindex,
    estimationCellCount_rebuild_eq_reindex,
    allBlockOrderedMarkedFactorial_eq_closed]

-- @node: lightPolynomialTerm_rebuild_eq_allBlock
/-- [Each concrete light-cell polynomial is the finite-product all-block polynomial on the
  canonically reindexed estimation fold](goal). -/
lemma lightPolynomialTerm_rebuild_eq_allBlock {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (M B : ℝ) (K : ℕ) (k : Fin d) :
    lightPolynomialTerm M B K (rebuildPolynomialEstimationSample P base x) k =
      allBlockLightPolynomialTerm M B K (polynomialFoldBReindex P x) k := by
  unfold lightPolynomialTerm allBlockLightPolynomialTerm
  simp_rw [orderedMarkedFactorial_rebuild_eq_allBlock]

-- @node: lightPolynomialSum_rebuild_eq_allBlock
/-- [Summing over a deterministic light set preserves the exact fold identification](goal). -/
lemma lightPolynomialSum_rebuild_eq_allBlock {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (M B : ℝ) (K : ℕ) (S : Finset (Fin d)) :
    (∑ k ∈ S,
      lightPolynomialTerm M B K (rebuildPolynomialEstimationSample P base x) k) =
      allBlockMarkedPolynomialSum M B K S (polynomialFoldBReindex P x) := by
  unfold allBlockMarkedPolynomialSum
  apply Finset.sum_congr rfl
  intro k _
  exact lightPolynomialTerm_rebuild_eq_allBlock P base x M B K k

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
