import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.FactorialMoments
import Causalean.Stat.Minimax.ChiSquaredFinite
import Causalean.Stat.UStatistic.OrderM.Variance

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open scoped BigOperators

section MatchingCounts

variable {I J A : Type*} [Fintype I] [Fintype J] [Fintype A] [DecidableEq A]

/-- Indices in the fibre of a finite labelling. -/
abbrev PatternFiber (f : I → A) (a : A) := {i : I // f i = a}

/-- Ordered injective selections whose observed labels match a prescribed pattern. -/
abbrev MatchingEmbedding (g : I → A) (z : J → A) :=
  {e : I ↪ J // ∀ i, z (e i) = g i}

private def fiberSigmaEquiv (f : I → A) : (Σ a, PatternFiber f a) ≃ I where
  toFun p := p.2.1
  invFun i := ⟨f i, ⟨i, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨a, ⟨i, hi⟩⟩
    cases hi
    rfl
  right_inv i := rfl

private noncomputable def matchingEmbeddingEquiv (g : I → A) (z : J → A) :
    MatchingEmbedding g z ≃ ((a : A) → PatternFiber g a ↪ PatternFiber z a) where
  toFun e a :=
    { toFun := fun i ↦ ⟨e.1 i.1, by simpa [i.2] using e.2 i.1⟩
      inj' := fun i j hij ↦ Subtype.ext (e.1.injective (congrArg Subtype.val hij)) }
  invFun es :=
    { val := (fiberSigmaEquiv g).symm.toEmbedding |>.trans
        ((Function.Embedding.refl A).sigmaMap es) |>.trans
        (fiberSigmaEquiv z).toEmbedding
      property := fun i ↦ (es (g i) ⟨i, rfl⟩).2 }
  left_inv e := by
    ext i
    rfl
  right_inv es := by
    funext a
    ext i
    rcases i with ⟨i, hi⟩
    cases hi
    rfl

/-- Multinomial ordered-pattern cardinality, factored over label fibres. -/
lemma matchingEmbedding_card (g : I → A) (z : J → A) :
    Fintype.card (MatchingEmbedding g z) =
      ∏ a : A,
        (Fintype.card (PatternFiber z a)).descFactorial
          (Fintype.card (PatternFiber g a)) := by
  rw [Fintype.card_congr (matchingEmbeddingEquiv g z), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro a _
  exact Fintype.card_embedding_eq

/-- Number of ordered injective selections matching a finite label pattern. -/
noncomputable def matchingCount (g : I → A) (z : J → A) : ℝ :=
  ∑ e : I ↪ J, if ∀ i, z (e i) = g i then 1 else 0

lemma matchingCount_eq_card (g : I → A) (z : J → A) :
    matchingCount g z = Fintype.card (MatchingEmbedding g z) := by
  classical
  rw [matchingCount]
  have hcard : Fintype.card (MatchingEmbedding g z) =
      ((Finset.univ : Finset (I ↪ J)).filter fun e => ∀ i, z (e i) = g i).card := by
    exact Fintype.card_of_subtype _ (by intro e; simp)
  rw [hcard]
  simpa using (Finset.sum_boole (R := ℝ)
    (fun e : I ↪ J => ∀ i, z (e i) = g i) Finset.univ)

/-- Pointwise ordered multinomial count identity. -/
lemma matchingCount_eq_prod (g : I → A) (z : J → A) :
    matchingCount g z =
      ∏ a : A,
        ((Fintype.card (PatternFiber z a)).descFactorial
          (Fintype.card (PatternFiber g a)) : ℝ) := by
  rw [matchingCount_eq_card]
  exact_mod_cast matchingEmbedding_card g z

/-- Indicator kernel of one labelled tuple. -/
def patternKernel (g : I → A) (z : I → A) : ℝ :=
  if z = g then 1 else 0

variable [MeasurableSpace A] [MeasurableSingletonClass A]

lemma patternKernel_measurable (g : I → A) : Measurable (patternKernel g) := by
  fun_prop

/-- A labelled tuple under a finite product law has the product point mass. -/
lemma integral_patternKernel_pi (P : Measure A) [IsProbabilityMeasure P]
    (g : I → A) :
    ∫ z, patternKernel g z ∂(Measure.pi fun _ : I => P) =
      ∏ i : I, P.real {g i} := by
  classical
  rw [integral_fintype _ Integrable.of_finite]
  simp [patternKernel, Causalean.Stat.pi_real_singleton]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure A}
  [IsProbabilityMeasure P]

lemma integral_patternKernel_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (g : I → A) {n : ℕ}
    (e : I ↪ Fin n) :
    ∫ ω, patternKernel g (fun i => S.Z (e i : ℕ) ω) ∂μ =
      ∏ i : I, P.real {g i} := by
  rw [← integral_patternKernel_pi P g]
  rw [← S.map_fintype_tuple_eq e.injective]
  rw [integral_map
    (measurable_pi_lambda _ (fun i : I => S.meas (e i : ℕ))).aemeasurable
    (patternKernel_measurable g).aestronglyMeasurable]

/-- Shows that integrable pattern Kernel sample is integrable under the stated sampling distribution. -/
lemma integrable_patternKernel_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (g : I → A) {n : ℕ}
    (e : I ↪ Fin n) :
    Integrable (fun ω => patternKernel g (fun i => S.Z (e i : ℕ) ω)) μ := by
  apply Integrable.of_bound
    (((patternKernel_measurable g).comp
      (measurable_pi_lambda _ (fun i : I => S.meas (e i : ℕ)))).aestronglyMeasurable) 1
  filter_upwards with ω
  by_cases h : (fun i => S.Z (e i : ℕ) ω) = g <;> simp [patternKernel, h]

/-- Exact ordered-injective multinomial mean.  This is equation (9) before
normalization: the number of embeddings contributes `(n)_{|I|}`, and each
labelled tuple contributes its product point mass. -/
lemma integral_matchingCount_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (g : I → A) (n : ℕ) :
    ∫ ω, matchingCount g (fun j : Fin n => S.Z j ω) ∂μ =
      (n.descFactorial (Fintype.card I) : ℝ) * ∏ i : I, P.real {g i} := by
  classical
  unfold matchingCount
  rw [integral_finset_sum _ (fun e _ => by
    simpa [patternKernel, funext_iff] using integrable_patternKernel_sample S g e)]
  simp_rw [show ∀ e : I ↪ Fin n,
      (∫ ω, (if ∀ i, S.Z (e i : ℕ) ω = g i then 1 else 0) ∂μ) =
        ∏ i : I, P.real {g i} by
    intro e
    simpa [patternKernel, funext_iff] using integral_patternKernel_sample S g e]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_embedding_eq]
  norm_num

/-- Shows that integrable matching Count sample is integrable under the stated sampling distribution. -/
lemma integrable_matchingCount_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (g : I → A) (n : ℕ) :
    Integrable (fun ω => matchingCount g (fun j : Fin n => S.Z j ω)) μ := by
  classical
  unfold matchingCount
  exact integrable_finset_sum _ fun e _ => by
    simpa [patternKernel, funext_iff] using integrable_patternKernel_sample S g e

variable {K : Type*} [Fintype K]

private def sumFiberEquiv (g : I → A) (h : K → A) (a : A) :
    PatternFiber (Sum.elim g h) a ≃ PatternFiber g a ⊕ PatternFiber h a where
  toFun x := by
    rcases x with ⟨i, hi⟩
    cases i with
    | inl i => exact Sum.inl ⟨i, hi⟩
    | inr i => exact Sum.inr ⟨i, hi⟩
  invFun x := by
    cases x with
    | inl i => exact ⟨Sum.inl i.1, i.2⟩
    | inr i => exact ⟨Sum.inr i.1, i.2⟩
  left_inv x := by rcases x with ⟨i, hi⟩; cases i <;> rfl
  right_inv x := by cases x <;> rfl

/-- If two patterns have disjoint label ranges, their matching counts multiply
to the matching count of the sum pattern.  Observations cannot be shared by
the two selections because their required labels differ. -/
lemma matchingCount_mul_eq_sum (g : I → A) (h : K → A) (z : J → A)
    (hdisj : ∀ i k, g i ≠ h k) :
    matchingCount g z * matchingCount h z =
      matchingCount (Sum.elim g h) z := by
  classical
  rw [matchingCount_eq_prod, matchingCount_eq_prod, matchingCount_eq_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  have hor : Fintype.card (PatternFiber g a) = 0 ∨
      Fintype.card (PatternFiber h a) = 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨ig⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn.1)
    obtain ⟨ih⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn.2)
    exact hdisj ig.1 ih.1 (by rw [ig.2, ih.2])
  have hcard : Fintype.card (PatternFiber (Sum.elim g h) a) =
      Fintype.card (PatternFiber g a) + Fintype.card (PatternFiber h a) := by
    rw [Fintype.card_congr (sumFiberEquiv g h a), Fintype.card_sum]
  rw [hcard]
  rcases hor with hg | hh
  · simp [hg]
  · simp [hh]

/-- Exact cross-category ordered-pattern moment (equation (13), raw form). -/
lemma integral_matchingCount_mul_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (g : I → A) (h : K → A) (n : ℕ)
    (hdisj : ∀ i k, g i ≠ h k) :
    ∫ ω, matchingCount g (fun j : Fin n => S.Z j ω) *
        matchingCount h (fun j : Fin n => S.Z j ω) ∂μ =
      (n.descFactorial (Fintype.card I + Fintype.card K) : ℝ) *
        (∏ i : I, P.real {g i}) * (∏ k : K, P.real {h k}) := by
  simp_rw [matchingCount_mul_eq_sum g h _ hdisj]
  rw [integral_matchingCount_sample S (Sum.elim g h) n]
  rw [Fintype.card_sum, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

/-- Exact cross-category moment for normalized factorial estimators, including
the finite-sample falling-factorial covariance ratio in equation (13). -/
lemma integral_normalized_matchingCount_mul_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (g : I → A) (h : K → A) (n : ℕ)
    (hdisj : ∀ i k, g i ≠ h k) :
    ∫ ω, (matchingCount g (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (Fintype.card I) : ℝ)) *
        (matchingCount h (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (Fintype.card K) : ℝ)) ∂μ =
      (n.descFactorial (Fintype.card I + Fintype.card K) : ℝ) /
          ((n.descFactorial (Fintype.card I) : ℝ) *
            n.descFactorial (Fintype.card K)) *
        (∏ i : I, P.real {g i}) * (∏ k : K, P.real {h k}) := by
  have hraw := integral_matchingCount_mul_sample S g h n hdisj
  calc
    ∫ ω, (matchingCount g (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (Fintype.card I) : ℝ)) *
        (matchingCount h (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (Fintype.card K) : ℝ)) ∂μ =
      ((n.descFactorial (Fintype.card I) : ℝ) *
        n.descFactorial (Fintype.card K))⁻¹ *
        ∫ ω, matchingCount g (fun j : Fin n => S.Z j ω) *
          matchingCount h (fun j : Fin n => S.Z j ω) ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
    _ = _ := by rw [hraw]; simp only [div_eq_mul_inv]; ring

end MatchingCounts

section FactorialMultiindices

variable {A J : Type*} [Fintype A] [DecidableEq A] [Fintype J]

/-- One distinguishable slot for each occurrence prescribed by an exponent vector. -/
abbrev MultiSlot (r : A → ℕ) := Σ a : A, Fin (r a)

/-- The label prescribed at a multiindex slot. -/
def multiPattern (r : A → ℕ) : MultiSlot r → A := fun i => i.1

/-- Total degree of a finite exponent vector. -/
def exponentDegree (r : A → ℕ) : ℕ := ∑ a, r a

/-- Product of falling-factorial cell counts, represented as an ordered-pattern count. -/
noncomputable def multinomialFactorialCount (r : A → ℕ) (z : J → A) : ℝ :=
  matchingCount (multiPattern r) z

private def multiPatternFiberEquiv (r : A → ℕ) (a : A) :
    PatternFiber (multiPattern r) a ≃ Fin (r a) where
  toFun i := by
    rcases i with ⟨⟨b, j⟩, hb⟩
    cases hb
    exact j
  invFun j := ⟨⟨a, j⟩, rfl⟩
  left_inv i := by rcases i with ⟨⟨b, j⟩, hb⟩; cases hb; rfl
  right_inv j := rfl

lemma multiSlot_card (r : A → ℕ) :
    Fintype.card (MultiSlot r) = exponentDegree r := by
  simp [exponentDegree, Fintype.card_sigma]

/-- The ordered-pattern representation is exactly the product of cellwise
falling factorials. -/
lemma multinomialFactorialCount_eq_prod (r : A → ℕ) (z : J → A) :
    multinomialFactorialCount r z =
      ∏ a : A, ((Fintype.card (PatternFiber z a)).descFactorial (r a) : ℝ) := by
  rw [multinomialFactorialCount, matchingCount_eq_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [Fintype.card_congr (multiPatternFiberEquiv r a)]
  simp

lemma multiPattern_mass_prod [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Measure A) (r : A → ℕ) :
    (∏ i : MultiSlot r, P.real {multiPattern r i}) =
      ∏ a : A, (P.real {a}) ^ (r a) := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro a _
  simp [multiPattern]

variable [MeasurableSpace A] [MeasurableSingletonClass A]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure A}
  [IsProbabilityMeasure P]

/-- Equation (9) for a cell-count multiindex. -/
lemma integral_multinomialFactorialCount_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (r : A → ℕ) (n : ℕ) :
    ∫ ω, multinomialFactorialCount r (fun j : Fin n => S.Z j ω) ∂μ =
      (n.descFactorial (exponentDegree r) : ℝ) *
        ∏ a : A, (P.real {a}) ^ (r a) := by
  unfold multinomialFactorialCount
  rw [integral_matchingCount_sample]
  rw [multiSlot_card, multiPattern_mass_prod]

lemma integrable_multinomialFactorialCount_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (r : A → ℕ) (n : ℕ) :
    Integrable (fun ω =>
      multinomialFactorialCount r (fun j : Fin n => S.Z j ω)) μ := by
  exact integrable_matchingCount_sample S (multiPattern r) n

/-- Coordinatewise overlap choices in the product of two factorial monomials. -/
abbrev OverlapChoice (r s : A → ℕ) :=
  ∀ a : A, Fin (min (r a) (s a) + 1)

/-- Exponent after identifying the selected observations prescribed by an overlap. -/
def mergedExponent (r s : A → ℕ) (H : OverlapChoice r s) : A → ℕ :=
  fun a => r a + s a - H a

/-- Multiplicity of one overlap pattern in the falling-factorial product identity. -/
def overlapCoefficient (r s : A → ℕ) (H : OverlapChoice r s) : ℕ :=
  ∏ a : A,
    Nat.choose (r a) (H a) * Nat.choose (s a) (H a) * (H a : ℕ).factorial

/-- Total number of identified observations in an overlap choice. -/
def totalOverlap (r s : A → ℕ) (H : OverlapChoice r s) : ℕ :=
  ∑ a : A, (H a : ℕ)

private lemma finset_sum_sub_sum_of_le (u v : A → ℕ) (t : Finset A)
    (h : ∀ a ∈ t, v a ≤ u a) :
    ∑ a ∈ t, (u a - v a) = (∑ a ∈ t, u a) - ∑ a ∈ t, v a := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      have hat : v a ≤ u a := h a (Finset.mem_insert_self a t)
      have hrest : ∀ b ∈ t, v b ≤ u b := by
        intro b hb
        exact h b (Finset.mem_insert_of_mem hb)
      have hrestSum : (∑ b ∈ t, v b) ≤ ∑ b ∈ t, u b :=
        Finset.sum_le_sum hrest
      rw [ih hrest]
      omega

/-- Establishes the stated upper bound for total Overlap le right. -/
lemma totalOverlap_le_right (r s : A → ℕ) (H : OverlapChoice r s) :
    totalOverlap r s H ≤ exponentDegree s := by
  unfold totalOverlap exponentDegree
  exact Finset.sum_le_sum fun a _ =>
    le_trans (Nat.le_of_lt_succ (H a).isLt) (Nat.min_le_right _ _)

/-- Establishes the stated property of exponent Degree merged Exponent in the discrete average-treatment-effect construction. -/
lemma exponentDegree_mergedExponent (r s : A → ℕ) (H : OverlapChoice r s) :
    exponentDegree (mergedExponent r s H) =
      exponentDegree r + exponentDegree s - totalOverlap r s H := by
  have hHs (a : A) : (H a : ℕ) ≤ s a :=
    le_trans (Nat.le_of_lt_succ (H a).isLt) (Nat.min_le_right _ _)
  have hcoord (a : A) : r a + s a - (H a : ℕ) = r a + (s a - H a) := by omega
  simp only [exponentDegree, mergedExponent, totalOverlap, hcoord, Finset.sum_add_distrib]
  rw [finset_sum_sub_sum_of_le s (fun a => (H a : ℕ)) Finset.univ]
  · have htotal := totalOverlap_le_right r s H
    unfold totalOverlap exponentDegree at htotal
    omega
  · intro a _
    exact hHs a

/-- Establishes the stated upper bound for factorial ratio overlap bound. -/
lemma factorial_ratio_overlap_bound (r s : A → ℕ) (n : ℕ)
    (hdeg : exponentDegree r ≤ exponentDegree s)
    (hsize : 4 * (exponentDegree s) ^ 2 ≤ n) (H : OverlapChoice r s) :
    (n.descFactorial (exponentDegree (mergedExponent r s H)) : ℝ) /
        ((n.descFactorial (exponentDegree r) : ℝ) *
          n.descFactorial (exponentDegree s)) ≤
      Real.exp 1 / (n : ℝ) ^ (totalOverlap r s H) := by
  rw [exponentDegree_mergedExponent]
  exact factorial_ratio_bound hdeg hsize (totalOverlap_le_right r s H)

private lemma overlap_cell_coefficient_le {r s M h : ℕ} (hrM : r ≤ M) :
    Nat.choose r h * Nat.choose s h * h.factorial ≤
      Nat.choose s h * M ^ h := by
  have hfall : r.descFactorial h ≤ M ^ h :=
    (Nat.descFactorial_le_pow r h).trans (Nat.pow_le_pow_left hrM h)
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hfall
  nlinarith [Nat.zero_le (Nat.choose s h)]

private lemma cell_overlap_sum_le {r s M n : ℕ} {q : ℝ}
    (hq : 0 ≤ q) (hn : 0 < n) (hrM : r ≤ M) :
    ∑ h : Fin (min r s + 1),
        (Nat.choose r h * Nat.choose s h * (h : ℕ).factorial : ℝ) /
          (n : ℝ) ^ (h : ℕ) * q ^ (r + s - (h : ℕ)) ≤
      q ^ r * (q + (M : ℝ) / n) ^ s := by
  rw [Fin.sum_univ_eq_sum_range
    (fun h : ℕ => (Nat.choose r h * Nat.choose s h * h.factorial : ℝ) /
      (n : ℝ) ^ h * q ^ (r + s - h)) (min r s + 1)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrewrite (h : ℕ) (hh : h ∈ Finset.range (min r s + 1)) :
      q ^ (r + s - h) = q ^ r * q ^ (s - h) := by
    have hle : h ≤ s :=
      (Nat.le_of_lt_succ (Finset.mem_range.mp hh)).trans (Nat.min_le_right _ _)
    rw [show r + s - h = r + (s - h) by omega, pow_add]
  calc
    ∑ h ∈ Finset.range (min r s + 1),
        (Nat.choose r h * Nat.choose s h * h.factorial : ℝ) /
          (n : ℝ) ^ h * q ^ (r + s - h) =
      q ^ r * ∑ h ∈ Finset.range (min r s + 1),
        (Nat.choose r h * Nat.choose s h * h.factorial : ℝ) /
          (n : ℝ) ^ h * q ^ (s - h) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [hrewrite h hh]
      ring
    _ ≤ q ^ r * ∑ h ∈ Finset.range (min r s + 1),
        ((M : ℝ) / n) ^ h * q ^ (s - h) * Nat.choose s h := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq r)
      apply Finset.sum_le_sum
      intro h hh
      have hcoeffNat := overlap_cell_coefficient_le (s := s) (h := h) hrM
      have hcoeff :
          (Nat.choose r h * Nat.choose s h * h.factorial : ℝ) ≤
            Nat.choose s h * (M : ℝ) ^ h := by exact_mod_cast hcoeffNat
      have hpowq : 0 ≤ q ^ (s - h) := pow_nonneg hq _
      calc
        (Nat.choose r h * Nat.choose s h * h.factorial : ℝ) /
            (n : ℝ) ^ h * q ^ (s - h) ≤
          ((Nat.choose s h : ℝ) * (M : ℝ) ^ h) /
            (n : ℝ) ^ h * q ^ (s - h) := by
              exact mul_le_mul_of_nonneg_right
                (div_le_div_of_nonneg_right hcoeff (by positivity)) hpowq
        _ = ((M : ℝ) / n) ^ h * q ^ (s - h) * Nat.choose s h := by
          rw [div_pow]
          ring
    _ ≤ q ^ r * ∑ h ∈ Finset.range (s + 1),
        ((M : ℝ) / n) ^ h * q ^ (s - h) * Nat.choose s h := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq r)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.succ_le_succ (Nat.min_le_right r s))
      · intro h _ _
        positivity
    _ = q ^ r * (q + (M : ℝ) / n) ^ s := by
      rw [add_comm q, add_pow]

private lemma overlap_sum_eq_prod (r s : A → ℕ) (n : ℕ) (q : A → ℝ) :
    (∑ H : OverlapChoice r s,
        (overlapCoefficient r s H : ℝ) /
          (n : ℝ) ^ (totalOverlap r s H) *
          ∏ a : A, q a ^ (mergedExponent r s H a)) =
      ∏ a : A, ∑ h : Fin (min (r a) (s a) + 1),
        (Nat.choose (r a) h * Nat.choose (s a) h * (h : ℕ).factorial : ℝ) /
          (n : ℝ) ^ (h : ℕ) * q a ^ (r a + s a - (h : ℕ)) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro H _
  simp only [overlapCoefficient, totalOverlap, mergedExponent, Nat.cast_prod]
  push_cast
  rw [← Finset.prod_pow_eq_pow_sum Finset.univ (fun a => (H a : ℕ)) (n : ℝ)]
  rw [← Finset.prod_div_distrib, Finset.prod_mul_distrib]

private lemma overlap_sum_le (r s : A → ℕ) (n : ℕ) (q : A → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hn : 0 < n)
    (hdeg : exponentDegree r ≤ exponentDegree s) :
    (∑ H : OverlapChoice r s,
        (overlapCoefficient r s H : ℝ) /
          (n : ℝ) ^ (totalOverlap r s H) *
          ∏ a : A, q a ^ (mergedExponent r s H a)) ≤
      (∏ a : A, q a ^ (r a)) *
        ∏ a : A, (q a + (exponentDegree s : ℝ) / n) ^ (s a) := by
  rw [overlap_sum_eq_prod]
  calc
    (∏ a : A, ∑ h : Fin (min (r a) (s a) + 1),
        (Nat.choose (r a) h * Nat.choose (s a) h * (h : ℕ).factorial : ℝ) /
          (n : ℝ) ^ (h : ℕ) * q a ^ (r a + s a - (h : ℕ))) ≤
      ∏ a : A, q a ^ (r a) *
        (q a + (exponentDegree s : ℝ) / n) ^ (s a) := by
      apply Finset.prod_le_prod
      · intro a _
        apply Finset.sum_nonneg
        intro h _
        exact mul_nonneg (div_nonneg (by positivity) (by positivity))
          (pow_nonneg (hq a) _)
      · intro a _
        apply cell_overlap_sum_le (hq a) hn
        have hra : r a ≤ exponentDegree r := by
          unfold exponentDegree
          exact Finset.single_le_sum (fun b _ => Nat.zero_le (r b)) (Finset.mem_univ a)
        exact hra.trans hdeg
    _ = _ := by rw [Finset.prod_mul_distrib]

/-- Exact within-category joint-count expansion underlying equation (12). -/
lemma multinomialFactorialCount_mul (r s : A → ℕ) (z : J → A) :
    multinomialFactorialCount r z * multinomialFactorialCount s z =
      ∑ H : OverlapChoice r s,
        overlapCoefficient r s H * multinomialFactorialCount (mergedExponent r s H) z := by
  classical
  rw [multinomialFactorialCount_eq_prod, multinomialFactorialCount_eq_prod]
  rw [← Finset.prod_mul_distrib]
  have hfall (a : A) :
      ((Fintype.card (PatternFiber z a)).descFactorial (r a) : ℝ) *
          (Fintype.card (PatternFiber z a)).descFactorial (s a) =
        ∑ h : Fin (min (r a) (s a) + 1),
          (Nat.choose (r a) h * Nat.choose (s a) h * (h : ℕ).factorial : ℝ) *
            (Fintype.card (PatternFiber z a)).descFactorial
              (r a + s a - (h : ℕ)) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun h : ℕ =>
        (Nat.choose (r a) h * Nat.choose (s a) h * h.factorial : ℝ) *
          (Fintype.card (PatternFiber z a)).descFactorial (r a + s a - h))
      (min (r a) (s a) + 1)]
    exact_mod_cast descFactorial_mul_identity
      (Fintype.card (PatternFiber z a)) (r a) (s a)
  simp_rw [hfall]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro H _
  rw [multinomialFactorialCount_eq_prod]
  simp only [mergedExponent, overlapCoefficient, Nat.cast_prod, Nat.cast_mul]
  rw [← Finset.prod_mul_distrib]

/-- Exact within-category joint mean obtained by integrating the overlap
expansion.  This is the equality immediately preceding the bound in (12). -/
lemma integral_multinomialFactorialCount_mul_sample [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (r s : A → ℕ) (n : ℕ) :
    ∫ ω, multinomialFactorialCount r (fun j : Fin n => S.Z j ω) *
        multinomialFactorialCount s (fun j : Fin n => S.Z j ω) ∂μ =
      ∑ H : OverlapChoice r s,
        overlapCoefficient r s H *
          ((n.descFactorial (exponentDegree (mergedExponent r s H)) : ℝ) *
            ∏ a : A, (P.real {a}) ^ (mergedExponent r s H a)) := by
  simp_rw [multinomialFactorialCount_mul r s]
  rw [integral_finset_sum _]
  · apply Finset.sum_congr rfl
    intro H _
    rw [integral_const_mul, integral_multinomialFactorialCount_sample]
  · intro H _
    exact Integrable.const_mul
      (integrable_multinomialFactorialCount_sample S (mergedExponent r s H) n) _

/-- Exact normalized within-category joint moment, displaying the overlap sum
and the falling-factorial ratio to which `factorial_ratio_bound` applies. -/
lemma integral_normalized_multinomialFactorialCount_mul_sample
    [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (r s : A → ℕ) (n : ℕ) :
    ∫ ω, (multinomialFactorialCount r (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (exponentDegree r) : ℝ)) *
        (multinomialFactorialCount s (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (exponentDegree s) : ℝ)) ∂μ =
      ∑ H : OverlapChoice r s,
        overlapCoefficient r s H *
          ((n.descFactorial (exponentDegree (mergedExponent r s H)) : ℝ) /
            ((n.descFactorial (exponentDegree r) : ℝ) *
              n.descFactorial (exponentDegree s))) *
          ∏ a : A, (P.real {a}) ^ (mergedExponent r s H a) := by
  have hraw := integral_multinomialFactorialCount_mul_sample S r s n
  calc
    ∫ ω, (multinomialFactorialCount r (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (exponentDegree r) : ℝ)) *
        (multinomialFactorialCount s (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (exponentDegree s) : ℝ)) ∂μ =
      ((n.descFactorial (exponentDegree r) : ℝ) *
        n.descFactorial (exponentDegree s))⁻¹ *
        ∫ ω, multinomialFactorialCount r (fun j : Fin n => S.Z j ω) *
          multinomialFactorialCount s (fun j : Fin n => S.Z j ω) ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
    _ = _ := by
      rw [hraw, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro H _
      simp only [div_eq_mul_inv]
      ring

/-- Proved light-cell factorial-moment inequality (equation (12)).  The first
factorial monomial supplies `q^r`; all possible overlaps with the second are
absorbed by the shifted mass `q + |s|/n`, with the normalization loss bounded
by `exp 1`. -/
lemma normalized_multinomial_joint_moment_bound [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω A μ P) (r s : A → ℕ) (n : ℕ)
    (hn : 0 < n) (hdeg : exponentDegree r ≤ exponentDegree s)
    (hsize : 4 * (exponentDegree s) ^ 2 ≤ n) :
    ∫ ω, (multinomialFactorialCount r (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (exponentDegree r) : ℝ)) *
        (multinomialFactorialCount s (fun j : Fin n => S.Z j ω) /
          (n.descFactorial (exponentDegree s) : ℝ)) ∂μ ≤
      Real.exp 1 * (∏ a : A, (P.real {a}) ^ (r a)) *
        ∏ a : A,
          (P.real {a} + (exponentDegree s : ℝ) / n) ^ (s a) := by
  rw [integral_normalized_multinomialFactorialCount_mul_sample]
  have hq (a : A) : 0 ≤ P.real {a} := by
    exact ENNReal.toReal_nonneg
  calc
    (∑ H : OverlapChoice r s,
        overlapCoefficient r s H *
          ((n.descFactorial (exponentDegree (mergedExponent r s H)) : ℝ) /
            ((n.descFactorial (exponentDegree r) : ℝ) *
              n.descFactorial (exponentDegree s))) *
          ∏ a : A, (P.real {a}) ^ (mergedExponent r s H a)) ≤
      ∑ H : OverlapChoice r s,
        overlapCoefficient r s H *
          (Real.exp 1 / (n : ℝ) ^ (totalOverlap r s H)) *
          ∏ a : A, (P.real {a}) ^ (mergedExponent r s H a) := by
      apply Finset.sum_le_sum
      intro H _
      have hratio := factorial_ratio_overlap_bound r s n hdeg hsize H
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hratio (by positivity)
      · exact Finset.prod_nonneg fun a _ => pow_nonneg (hq a) _
    _ = Real.exp 1 *
        ∑ H : OverlapChoice r s,
          (overlapCoefficient r s H : ℝ) /
            (n : ℝ) ^ (totalOverlap r s H) *
            ∏ a : A, (P.real {a}) ^ (mergedExponent r s H a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro H _
      simp only [div_eq_mul_inv]
      ring
    _ ≤ Real.exp 1 * ((∏ a : A, (P.real {a}) ^ (r a)) *
        ∏ a : A,
          (P.real {a} + (exponentDegree s : ℝ) / n) ^ (s a)) := by
      exact mul_le_mul_of_nonneg_left
        (overlap_sum_le r s n (fun a => P.real {a}) hq hn hdeg)
        (Real.exp_pos 1).le
    _ = _ := by ring

end FactorialMultiindices

end CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The number of ordered injective selections matching a label pattern is unchanged when the
pattern and observed labels are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.matchingCount.congr_simp

/-- The product of falling-factorial cell counts is unchanged when its label multiplicities and
observed labels are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.multinomialFactorialCount.congr_simp

/-- The indicator that an observed labelled tuple exactly matches a given pattern is unchanged
when the pattern and tuple are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.patternKernel.congr_simp
