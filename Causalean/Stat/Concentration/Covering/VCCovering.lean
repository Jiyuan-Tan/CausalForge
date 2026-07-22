import Causalean.Stat.Concentration.Covering.CoveringNumber
import Causalean.Stat.Concentration.Covering.EmpiricalPseudoMetric
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
For a binary-indexed function class, the empirical covering number is bounded by
the Sauer-Shelah growth function of the underlying VC class, avoiding the
Haussler packing argument.

The sample restriction of a real-valued class `F` is assumed to factor through a
Boolean class `π`: at sample coordinate `j`, the real value is a fixed transform
`φ j` of the bit `π i (S j)`. Distinct empirical vectors of `F` are therefore
indexed by distinct Boolean restriction patterns on the sample. One
representative per realized pattern covers the empirical pseudometric space at
every positive radius, and Sauer-Shelah bounds the number of such patterns.
The main exported results are `vc_coveringNumber_le_growth`,
`vc_coveringNumber_le_sum_choose`, `log_coveringNumber_le_of_card_bound`, and
`log_coveringNumber_le`.
-/

namespace Causalean.Stat.Concentration

universe u v

open scoped BigOperators

variable {𝒳 : Type v} {ι : Type u} {n d : ℕ}

/-- The subset of sample coordinates at which a Boolean classifier is true. -/
noncomputable def restrictionPattern (p : 𝒳 → Bool) (S : Fin n → 𝒳) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => p (S j)

/-- The finite family of Boolean restriction patterns realized on a sample. -/
noncomputable def growthFamily (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun A : Finset (Fin n) =>
    ∃ i : ι, restrictionPattern (π i) S = A

/-- Membership in the growth family means that some classifier realizes that
restriction pattern on the sample. -/
lemma mem_growthFamily_iff {π : ι → 𝒳 → Bool} {S : Fin n → 𝒳}
    {A : Finset (Fin n)} :
    A ∈ growthFamily π S ↔ ∃ i : ι, restrictionPattern (π i) S = A := by
  classical
  simp [growthFamily]

/-- Membership in a restriction pattern means the classifier is true at that
sample coordinate. -/
lemma restrictionPattern_mem_iff {p : 𝒳 → Bool} {S : Fin n → 𝒳}
    {j : Fin n} :
    j ∈ restrictionPattern p S ↔ p (S j) = true := by
  classical
  simp [restrictionPattern]

/-- A finite set family with bounded VC dimension has cardinality controlled by
the Sauer-Shelah binomial sum on the sample. -/
theorem card_growthFamily_le_sum_choose (𝒜 : Finset (Finset (Fin n)))
    (hvd : 𝒜.vcDim ≤ d) :
    𝒜.card ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
  classical
  calc
    𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card (Fin n)).choose k :=
      Finset.card_shatterer_le_sum_vcDim
    _ = ∑ k ∈ Finset.Iic 𝒜.vcDim, n.choose k := by simp
    _ ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · simpa [Finset.Iic_subset_Iic] using hvd
      · intro _ _ _
        exact Nat.zero_le _

private lemma empirical_dist_eq_zero_of_factor_pattern
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳}
    {π : ι → 𝒳 → Bool} {φ : Fin n → Bool → ℝ}
    (hfactor : ∀ i j, F i (S j) = φ j (π i (S j)))
    {i i' : ι}
    (hpat : restrictionPattern (π i') S = restrictionPattern (π i) S) :
    dist (EmpiricalFunctionSpace.mk (F := F) (S := S) i)
      (EmpiricalFunctionSpace.mk (F := F) (S := S) i') = 0 := by
  have hpoint : ∀ j : Fin n, F i (S j) = F i' (S j) := by
    intro j
    rw [hfactor i j, hfactor i' j]
    apply congrArg (φ j)
    apply Bool.eq_iff_iff.mpr
    rw [← restrictionPattern_mem_iff (p := π i') (S := S) (j := j), hpat,
      restrictionPattern_mem_iff (p := π i) (S := S) (j := j)]
  simp [empiricalNorm, hpoint]

/-- One empirical-function representative for each realized Boolean pattern. -/
noncomputable def patternCover {F : ι → 𝒳 → ℝ}
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) :
    Finset (EmpiricalFunctionSpace F S) := by
  classical
  exact (growthFamily π S).attach.image fun A =>
    EmpiricalFunctionSpace.mk (F := F) (S := S)
      (Classical.choose
        ((mem_growthFamily_iff (π := π) (S := S) (A := A.1)).mp A.2))

/-- The pattern representative cover has no more elements than the realized
Boolean growth family. -/
lemma patternCover_card_le {F : ι → 𝒳 → ℝ}
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) :
    (patternCover (F := F) π S).card ≤ (growthFamily π S).card := by
  classical
  let f : (growthFamily π S) → EmpiricalFunctionSpace F S := fun A =>
    EmpiricalFunctionSpace.mk (F := F) (S := S)
      (Classical.choose
        ((mem_growthFamily_iff (π := π) (S := S) (A := A.1)).mp A.2))
  calc
    (patternCover (F := F) π S).card = ((growthFamily π S).attach.image f).card := by
      rfl
    _ ≤ (growthFamily π S).attach.card := Finset.card_image_le
    _ = (growthFamily π S).card := Finset.card_attach

/-- The pattern representative cover covers every empirical function at every
positive radius when the real class factors through the Boolean pattern. -/
lemma patternCover_covers {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳}
    {π : ι → 𝒳 → Bool} {φ : Fin n → Bool → ℝ}
    (hfactor : ∀ i j, F i (S j) = φ j (π i (S j)))
    {ε : ℝ} (hε : 0 < ε) :
    (Set.univ : Set (EmpiricalFunctionSpace F S)) ⊆
      ⋃ y ∈ patternCover (F := F) π S, Metric.ball y ε := by
  classical
  intro q _
  let A : Finset (Fin n) := restrictionPattern (π q.index) S
  have hA : A ∈ growthFamily π S := by
    rw [mem_growthFamily_iff]
    exact ⟨q.index, rfl⟩
  let a : (growthFamily π S) := ⟨A, hA⟩
  let repIndex : ι :=
    Classical.choose ((mem_growthFamily_iff (π := π) (S := S) (A := a.1)).mp a.2)
  let rep : EmpiricalFunctionSpace F S := ⟨repIndex⟩
  have hrep_mem : rep ∈ patternCover (F := F) π S := by
    rw [patternCover]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩
  refine Set.mem_iUnion.mpr ⟨rep, Set.mem_iUnion.mpr ⟨hrep_mem, ?_⟩⟩
  rw [Metric.mem_ball]
  have hrep_pattern : restrictionPattern (π rep.index) S =
      restrictionPattern (π q.index) S := by
    dsimp [rep, repIndex]
    exact Classical.choose_spec
      ((mem_growthFamily_iff (π := π) (S := S) (A := a.1)).mp a.2)
  calc
    dist q rep = 0 := by
      cases q
      exact empirical_dist_eq_zero_of_factor_pattern (F := F) (S := S)
        (π := π) (φ := φ) hfactor hrep_pattern
    _ < ε := hε

/-- The empirical covering number of a binary-factored class is bounded by the
number of realized Boolean restriction patterns. -/
theorem vc_coveringNumber_le_growth {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳}
    {π : ι → 𝒳 → Bool} {φ : Fin n → Bool → ℝ}
    (hfactor : ∀ i j, F i (S j) = φ j (π i (S j)))
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    {ε : ℝ} (hε : 0 < ε) :
    coveringNumber h' ε ≤ (growthFamily π S).card := by
  classical
  rw [coveringNumber_eq h' hε]
  let t : Finset (EmpiricalFunctionSpace F S) := patternCover (F := F) π S
  have hfind : Nat.find (coveringNumber_exists h' hε) ≤ t.card :=
    Nat.find_min' (coveringNumber_exists h' hε) (m := t.card)
      ⟨t, rfl, patternCover_covers hfactor hε⟩
  exact le_trans hfind (patternCover_card_le (F := F) π S)

/-- The empirical covering number of a binary-factored class is bounded by the
Sauer-Shelah binomial sum under a samplewise VC-dimension bound. -/
theorem vc_coveringNumber_le_sum_choose {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳}
    {π : ι → 𝒳 → Bool} {φ : Fin n → Bool → ℝ}
    (hfactor : ∀ i j, F i (S j) = φ j (π i (S j)))
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    {ε : ℝ} (hε : 0 < ε)
    (hvd : (growthFamily π S).vcDim ≤ d) :
    coveringNumber h' ε ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
  exact le_trans (vc_coveringNumber_le_growth hfactor h' hε)
    (card_growthFamily_le_sum_choose (growthFamily π S) hvd)

/-- A direct cardinality bound on the Boolean growth family gives the same
logarithmic bound on the empirical covering number. -/
theorem log_coveringNumber_le_of_card_bound [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳}
    {π : ι → 𝒳 → Bool} {φ : Fin n → Bool → ℝ}
    (hfactor : ∀ i j, F i (S j) = φ j (π i (S j)))
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hcard : (growthFamily π S).card ≤ N) :
    Real.log (coveringNumber h' ε) ≤ Real.log N := by
  classical
  have hcov_card : coveringNumber h' ε ≤ (growthFamily π S).card :=
    vc_coveringNumber_le_growth hfactor h' hε
  have hcov_N : coveringNumber h' ε ≤ N := le_trans hcov_card hcard
  have hcov_pos : 0 < coveringNumber h' ε := by
    have hnonempty : (Set.univ : Set (EmpiricalFunctionSpace F S)).Nonempty := by
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨⟨i⟩, by simp⟩
    exact coveringNumber_nonzero hnonempty h' hε
  have hcovN_real : ((coveringNumber h' ε : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcov_N
  exact Real.log_le_log (Nat.cast_pos.mpr hcov_pos) hcovN_real

/-- The Sauer-Shelah binomial sum is bounded by the usual polynomial upper
bound in sample size and VC dimension. -/
lemma sum_choose_le_succ_mul_pow (hd_pos : 0 < d) (hdn : d ≤ n) :
    ((∑ k ∈ Finset.Iic d, n.choose k : ℕ) : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) * (n : ℝ) ^ d := by
  have hn_pos : 0 < n := lt_of_lt_of_le hd_pos hdn
  have hsum_nat : (∑ k ∈ Finset.Iic d, n.choose k) ≤ (d + 1) * n ^ d := by
    calc
      (∑ k ∈ Finset.Iic d, n.choose k) ≤ ∑ k ∈ Finset.Iic d, n ^ d := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hk_le : k ≤ d := by simpa using hk
        exact le_trans (Nat.choose_le_pow n k) (Nat.pow_le_pow_right hn_pos hk_le)
      _ = (d + 1) * n ^ d := by
        simp [Nat.card_Iic, Finset.sum_const]
  exact_mod_cast hsum_nat

/-- VC control gives the usual logarithmic empirical covering-number bound for
a binary-factored class. -/
theorem log_coveringNumber_le [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳}
    {π : ι → 𝒳 → Bool} {φ : Fin n → Bool → ℝ}
    (hfactor : ∀ i j, F i (S j) = φ j (π i (S j)))
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    {ε : ℝ} (hε : 0 < ε)
    (hd_pos : 0 < d) (hdn : d ≤ n)
    (hvd : (growthFamily π S).vcDim ≤ d) :
    Real.log (coveringNumber h' ε) ≤
      Real.log ((d + 1 : ℕ) : ℝ) + (d : ℝ) * Real.log n := by
  classical
  let s : ℕ := ∑ k ∈ Finset.Iic d, n.choose k
  have hcov_sum : coveringNumber h' ε ≤ s :=
    vc_coveringNumber_le_sum_choose hfactor h' hε hvd
  have hcov_pos : 0 < coveringNumber h' ε := by
    have hnonempty : (Set.univ : Set (EmpiricalFunctionSpace F S)).Nonempty := by
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨⟨i⟩, by simp⟩
    exact coveringNumber_nonzero hnonempty h' hε
  have hcov_bound : ((coveringNumber h' ε : ℕ) : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) * (n : ℝ) ^ d := by
    calc
      ((coveringNumber h' ε : ℕ) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast hcov_sum
      _ ≤ ((d + 1 : ℕ) : ℝ) * (n : ℝ) ^ d :=
        sum_choose_le_succ_mul_pow (n := n) (d := d) hd_pos hdn
  have hn_pos : 0 < n := lt_of_lt_of_le hd_pos hdn
  calc
    Real.log (coveringNumber h' ε) ≤
        Real.log (((d + 1 : ℕ) : ℝ) * (n : ℝ) ^ d) := by
      exact Real.log_le_log (Nat.cast_pos.mpr hcov_pos) hcov_bound
    _ = Real.log ((d + 1 : ℕ) : ℝ) + Real.log ((n : ℝ) ^ d) := by
      rw [Real.log_mul]
      · exact_mod_cast Nat.succ_ne_zero d
      · exact pow_ne_zero d (Nat.cast_ne_zero.mpr (ne_of_gt hn_pos))
    _ = Real.log ((d + 1 : ℕ) : ℝ) + (d : ℝ) * Real.log n := by
      rw [Real.log_pow]

end Causalean.Stat.Concentration
