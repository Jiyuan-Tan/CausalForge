import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable

/-!
# Arithmetic, graph, and mass facts for the block family

Counting facts about complete blocks and the active population, the degree and
neighbourhood structure of the block graph, the support and low-order vanishing
of the block schedule, and the representer-mass bounds that keep the tilt
amplitude admissible.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- At least one complete block is active whenever `1 ≤ d ≤ n`. -/
lemma blockCount_pos
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n) :
    0 < blockCount n d := by
  simp only [blockCount]
  exact Nat.div_pos hdn (by omega)

/-- The active part never exceeds the population. -/
lemma activeCount_le (n d : ℕ) :
    activeCount n d ≤ n := by
  simpa [activeCount, blockCount] using Nat.div_mul_le_self n d

/-- With at least one complete block, the active part contains more than half
of the population. -/
lemma n_lt_two_mul_activeCount
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n) :
    n < 2 * activeCount n d := by
  have hd0 : 0 < d := by omega
  have hq : 1 ≤ n / d := by
    exact (Nat.one_le_div_iff hd0).2 hdn
  have hr : n % d < d := Nat.mod_lt n hd0
  have hdq : d ≤ (n / d) * d := by
    simpa using Nat.mul_le_mul_right d hq
  have hdecomp : n / d * d + n % d = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n d
  simp only [activeCount, blockCount]
  omega

/-- The active population share lies in `[1/2,1]`. -/
lemma activeShare_bounds
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n) :
    (1 / 2 : ℝ) ≤ activeShare n d ∧ activeShare n d ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo := n_lt_two_mul_activeCount n d hn hd hdn
  have hhi := activeCount_le n d
  unfold activeShare
  constructor
  · apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hnR).2
    norm_num only [one_mul]
    have hnat : n ≤ activeCount n d * 2 := by
      simpa [Nat.mul_comm] using Nat.le_of_lt hlo
    exact_mod_cast hnat
  · apply (div_le_one hnR).2
    exact_mod_cast hhi

/-- The block/population normalization identity used in the lower-bound
calculation. -/
lemma blockEnergy_div_blockCount
    (n d β : ℕ) (p : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n) :
    blockEnergy β p d / blockCount n d =
      ((d : ℝ) * blockEnergy β p d / n) / activeShare n d := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm : 0 < blockCount n d :=
    blockCount_pos n d hn hd hdn
  have hm0 : ((blockCount n d : ℕ) : ℝ) ≠ 0 := by positivity
  unfold activeShare activeCount
  push_cast
  field_simp

/-- Every in-neighborhood of the (possibly truncated) block graph has at
most `d` vertices. -/
lemma blockGraph_nbhd_card_le
    (n d : ℕ) (hd : 1 ≤ d) (i : Fin n) :
    (nbhd (blockGraph n d) i).card ≤ d := by
  classical
  let f : Fin n → Fin d :=
    fun j => ⟨j.val % d, Nat.mod_lt _ (by omega)⟩
  have hmap :
      Set.MapsTo f (↑(nbhd (blockGraph n d) i) : Set (Fin n))
        (↑(Finset.univ : Finset (Fin d)) : Set (Fin d)) := by
    intro j hj
    simp
  have hinj :
      Set.InjOn f (↑(nbhd (blockGraph n d) i) : Set (Fin n)) := by
    intro j hj k hk heq
    have hjq : j.val / d = i.val / d := by
      exact ((Finset.mem_filter.mp hj).2).2.2
    have hkq : k.val / d = i.val / d := by
      exact ((Finset.mem_filter.mp hk).2).2.2
    apply Fin.ext
    have hmod : j.val % d = k.val % d := Fin.ext_iff.mp heq
    calc
      j.val = d * (j.val / d) + j.val % d := (Nat.div_add_mod j.val d).symm
      _ = d * (k.val / d) + k.val % d := by rw [hjq, hkq, hmod]
      _ = k.val := Nat.div_add_mod k.val d
  simpa using
    (Finset.card_le_card_of_injOn f hmap hinj)

/-- In- and out-neighborhoods agree for the symmetric block relation. -/
lemma blockGraph_outNbhd_eq_nbhd
    (n d : ℕ) (j : Fin n) :
    outNbhd (blockGraph n d) j = nbhd (blockGraph n d) j := by
  classical
  ext i
  simp only [outNbhd, nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [blockGraph]
  aesop

/-- The truncated complete-block relation belongs to the degree-`d` graph
class. -/
lemma blockGraph_degree_le
    (n d : ℕ) (hd : 1 ≤ d) :
    BoundedDegree (blockGraph n d) d := by
  refine ⟨blockGraph_nbhd_card_le n d hd, ?_⟩
  intro j
  rw [blockGraph_outNbhd_eq_nbhd]
  exact blockGraph_nbhd_card_le n d hd j

/-- Raw coefficients of the normalized block representer vanish above the
prescribed interaction order. -/
lemma blockRawCoef_eq_zero_of_card_gt
    (β d : ℕ) (p : ℝ) (T : Finset (Fin d)) (hT : β < T.card) :
    blockRawCoef β p d T = 0 := by
  classical
  by_cases hd0 : d = 0
  · simp [blockRawCoef, hd0]
  simp only [blockRawCoef, if_neg hd0]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro S hS
  have hrβ : r ≤ β := by
    exact (Finset.mem_Icc.mp hr).2.trans (min_le_left β d)
  have hScard : S.card = r := (Finset.mem_filter.mp hS).2
  have hnsub : ¬ T ⊆ S := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  simp [hnsub]

/-- On one active block, reduction modulo `d` is injective. -/
lemma localSubset_card_eq
    (n d : ℕ) (hd : 1 ≤ d) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T,
      j.val < activeCount n d ∧ j.val / d = i.val / d) :
    (localSubset n d T).card = T.card := by
  classical
  rw [localSubset, dif_pos (by omega)]
  rw [Finset.card_image_iff.mpr]
  intro j hj k hk heq
  apply Fin.ext
  have hmod : j.val % d = k.val % d := Fin.ext_iff.mp heq
  have hjq := (hT j hj).2
  have hkq := (hT k hk).2
  calc
    j.val = d * (j.val / d) + j.val % d := (Nat.div_add_mod j.val d).symm
    _ = d * (k.val / d) + k.val % d := by rw [hjq, hkq, hmod]
    _ = k.val := Nat.div_add_mod k.val d

/-- The schedule is zero away from its prescribed block neighborhood. -/
lemma blockSchedule_supported
    (n d β : ℕ) (B p σ : ℝ)
    (hσ : σ = -1 ∨ σ = 1)
    (U : Fin (blockCount n d) → ℝ) :
    ∀ i T, ¬ T ⊆ nbhd (blockGraph n d) i →
      blockSchedule n d β B p σ hσ U i T = 0 := by
  classical
  intro i T hnsub
  unfold blockSchedule
  by_cases hi : i.val < activeCount n d
  · rw [dif_pos hi]
    by_cases hT :
        ∀ j ∈ T,
          j.val < activeCount n d ∧ j.val / d = i.val / d
    · exfalso
      apply hnsub
      intro j hj
      simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [blockGraph]
      exact ⟨(hT j hj).1, hi, (hT j hj).2⟩
    · simp [hT]
  · simp [hi]

/-- The block schedule has interaction order at most `β`. -/
lemma blockSchedule_lowOrder
    (n d β : ℕ) (B p σ : ℝ) (hd : 1 ≤ d)
    (hσ : σ = -1 ∨ σ = 1)
    (U : Fin (blockCount n d) → ℝ) :
    LowOrder (blockSchedule n d β B p σ hσ U) β := by
  classical
  intro i T hcard
  unfold blockSchedule
  by_cases hi : i.val < activeCount n d
  · rw [dif_pos hi]
    by_cases hT :
        ∀ j ∈ T,
          j.val < activeCount n d ∧ j.val / d = i.val / d
    · rw [dif_pos hT]
      have hTne : T ≠ ∅ := by
        intro he
        subst T
        simp at hcard
      rw [if_neg hTne]
      rw [blockRawCoef_eq_zero_of_card_gt β d p
        (localSubset n d T)]
      · ring
      · simpa [localSubset_card_eq n d hd i T hT] using hcard
    · simp [hT]
  · simp [hi]

/-- The raw coefficient mass of a normalized representer is at least its
unit all-treated/all-control contrast. -/
lemma one_le_representerMass
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    1 ≤ representerMass β p d := by
  classical
  let z₁ : Fin d → Bool := fun _ => true
  let z₀ : Fin d → Bool := fun _ => false
  have hcontrast :
      blockRepresenter β p d z₁ - blockRepresenter β p d z₀ = 1 := by
    let D := blockDesign d p (le_of_lt hp0) (le_of_lt hp1)
    have hD : IsProductBernoulli D p := by
      refine ⟨hp0, hp1, ?_⟩
      refine ⟨fun _ => le_of_lt hp0, fun _ => le_of_lt hp1, rfl⟩
    simpa [contrastFunctional, z₁, z₀] using
      (blockRepresenter_contrast_energy β d p D hD hβ hd).1
  rw [blockRepresenter_raw_expansion β d p hd z₁,
    blockRepresenter_raw_expansion β d p hd z₀] at hcontrast
  have hraw₁ (T : Finset (Fin d)) : rawMonomial T z₁ = 1 := by
    simp [rawMonomial, blockInd, z₁]
  have hraw₀ (T : Finset (Fin d)) :
      rawMonomial T z₀ = if T = ∅ then 1 else 0 := by
    by_cases hT : T = ∅
    · subst T
      simp [rawMonomial]
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hT
      unfold rawMonomial
      rw [if_neg hT]
      apply Finset.prod_eq_zero hj
      simp [blockInd, z₀]
  simp_rw [hraw₁, hraw₀] at hcontrast
  have habs :
      |(∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          blockRawCoef β p d T) -
        ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          blockRawCoef β p d T * (if T = ∅ then 1 else 0)| ≤
        representerMass β p d := by
    calc
      |_ - _| =
          |∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
            (blockRawCoef β p d T -
              blockRawCoef β p d T * (if T = ∅ then 1 else 0))| := by
        rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
            |blockRawCoef β p d T -
              blockRawCoef β p d T * (if T = ∅ then 1 else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
            |blockRawCoef β p d T| := by
        apply Finset.sum_le_sum
        intro T hT
        by_cases hTe : T = ∅ <;> simp [hTe]
      _ = representerMass β p d := rfl
  have hcontrast' :
      (∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          blockRawCoef β p d T) -
        ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          blockRawCoef β p d T * (if T = ∅ then 1 else 0) = 1 := by
    simpa only [mul_one] using hcontrast
  rw [hcontrast'] at habs
  simpa using habs

/-- Each finite-size representer mass is bounded by the exact supremum used
in the tilt definition. -/
lemma representerMass_le_representerMassSup
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    representerMass β p d ≤ representerMassSup β p := by
  obtain ⟨c₁, c₂, H, hc₁, hc₁c₂, hH, hrep⟩ :=
    blockEnergy_representer β p hβ hp0 hp1
  unfold representerMassSup
  apply le_csSup
  · refine ⟨H, ?_⟩
    rintro x ⟨e, rfl⟩
    exact (hrep e.1 e.2).2.2.2.2
  · exact Set.mem_range_self (⟨d, hd⟩ : {d : ℕ // 1 ≤ d})

/-- The exact supremum of representer masses is positive. -/
lemma representerMassSup_pos
    (β : ℕ) (p : ℝ) (hβ : 1 ≤ β)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < representerMassSup β p := by
  have hle := representerMass_le_representerMassSup β 1 p hβ (by omega)
    hp0 hp1
  have hone := one_le_representerMass β 1 p hβ (by omega) hp0 hp1
  linarith

/-- The score tilt consumes at most half of the coefficient budget after
multiplication by one representer mass. -/
lemma tiltAmplitude_mul_representerMass_le_half
    (B : ℝ) (β d m : ℕ) (p : ℝ)
    (hB : 0 ≤ B) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    |tiltAmplitude B β p m d| * representerMass β p d ≤ B / 2 := by
  have hH : 0 < representerMassSup β p :=
    representerMassSup_pos β p hβ hp0 hp1
  have hmass0 : 0 ≤ representerMass β p d := by
    unfold representerMass
    positivity
  have hmass :
      representerMass β p d ≤ representerMassSup β p :=
    representerMass_le_representerMassSup β d p hβ hd hp0 hp1
  have hsqrt : 0 ≤ min 1 (Real.sqrt (blockEnergy β p d / m)) := by
    rw [le_min_iff]
    exact ⟨by norm_num, Real.sqrt_nonneg _⟩
  have hsqrt1 : min 1 (Real.sqrt (blockEnergy β p d / m)) ≤ 1 :=
    min_le_left _ _
  have hk0 :
      0 ≤ min ((2 * representerMassSup β p)⁻¹)
        ((4 * Real.pi)⁻¹) := by
    rw [le_min_iff]
    constructor <;> positivity
  have hkH :
      min ((2 * representerMassSup β p)⁻¹)
          ((4 * Real.pi)⁻¹) * representerMass β p d ≤ 1 / 2 := by
    calc
      min ((2 * representerMassSup β p)⁻¹)
            ((4 * Real.pi)⁻¹) * representerMass β p d ≤
          (2 * representerMassSup β p)⁻¹ *
            representerMassSup β p := by
        apply mul_le_mul
        · exact min_le_left _ _
        · exact hmass
        · exact hmass0
        · positivity
      _ = 1 / 2 := by field_simp
  rw [tiltAmplitude, abs_mul, abs_mul, abs_of_nonneg hB,
    abs_of_nonneg hk0, abs_of_nonneg hsqrt]
  calc
    B * min ((2 * representerMassSup β p)⁻¹)
          ((4 * Real.pi)⁻¹) *
        min 1 (Real.sqrt (blockEnergy β p d / ↑m)) *
        representerMass β p d =
      B * (min 1 (Real.sqrt (blockEnergy β p d / ↑m)) *
        (min ((2 * representerMassSup β p)⁻¹)
          ((4 * Real.pi)⁻¹) * representerMass β p d)) := by ring
    _ ≤ B * (1 * (1 / 2)) := by gcongr
    _ = B / 2 := by ring

/-- Reduction modulo `d` gives a bijection between subsets of one active
global block and subsets of `Fin d`. -/
lemma sum_block_powerset_localSubset
    (n d : ℕ) (hd : 1 ≤ d) (i : Fin n)
    (hi : i.val < activeCount n d) (F : Finset (Fin d) → ℝ) :
    ∑ T ∈ (nbhd (blockGraph n d) i).powerset,
        F (localSubset n d T) =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, F S := by
  classical
  have hb : i.val / d < blockCount n d := by
    simp only [activeCount] at hi
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    simpa [Nat.mul_comm] using hi
  let e : Fin d → Fin n := fun k =>
    ⟨(i.val / d) * d + k.val, by
      have hblock :
          (i.val / d + 1) * d ≤ blockCount n d * d := by
        exact Nat.mul_le_mul_right d hb
      calc
        (i.val / d) * d + k.val <
            (i.val / d) * d + d := Nat.add_lt_add_left k.isLt _
        _ = (i.val / d + 1) * d := by simp [Nat.add_mul]
        _ ≤ blockCount n d * d := hblock
        _ = activeCount n d := rfl
        _ ≤ n := activeCount_le n d⟩
  have he_mem (k : Fin d) :
      e k ∈ nbhd (blockGraph n d) i := by
    simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [blockGraph]
    have hval :
        (e k).val < activeCount n d := by
      dsimp [e]
      have hblock :
          (i.val / d + 1) * d ≤ blockCount n d * d :=
        Nat.mul_le_mul_right d hb
      calc
        (i.val / d) * d + k.val <
            (i.val / d) * d + d := Nat.add_lt_add_left k.isLt _
        _ = (i.val / d + 1) * d := by simp [Nat.add_mul]
        _ ≤ blockCount n d * d := hblock
        _ = activeCount n d := rfl
    refine ⟨hval, hi, ?_⟩
    dsimp [e]
    rw [Nat.add_comm, Nat.mul_comm (i.val / d) d,
      Nat.add_mul_div_left k.val (i.val / d) (by omega),
      Nat.div_eq_of_lt k.isLt]
    simp
  have he_mod (k : Fin d) :
      (e k).val % d = k.val := by
    dsimp [e]
    rw [Nat.add_comm, Nat.mul_comm (i.val / d) d,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]
  have hlocal_embed
      (S : Finset (Fin d)) :
      localSubset n d (S.image e) = S := by
    rw [localSubset, dif_pos (by omega)]
    ext k
    constructor
    · intro hk
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
      have hlk : l = k := by
        apply Fin.ext
        simpa [he_mod] using Fin.ext_iff.mp hjk
      simpa [hlk] using hl
    · intro hk
      apply Finset.mem_image.mpr
      refine ⟨e k, Finset.mem_image.mpr ⟨k, hk, rfl⟩, ?_⟩
      apply Fin.ext
      simpa using he_mod k
  have he_inj : Function.Injective e := by
    intro k l hkl
    apply Fin.ext
    have := Fin.ext_iff.mp hkl
    dsimp [e] at this
    omega
  have he_local (j : Fin n)
      (hj : j ∈ nbhd (blockGraph n d) i) :
      e ⟨j.val % d, Nat.mod_lt _ (by omega)⟩ = j := by
    apply Fin.ext
    have hjq : j.val / d = i.val / d :=
      ((Finset.mem_filter.mp hj).2).2.2
    dsimp [e]
    rw [← hjq]
    simpa [Nat.mul_comm] using Nat.div_add_mod j.val d
  apply Finset.sum_bij'
      (fun T _ => localSubset n d T)
      (fun S _ => S.image e)
  · intro T hT
    simp
  · intro S hS
    apply Finset.mem_powerset.mpr
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact he_mem k
  · intro T hT
    ext j
    constructor
    · intro hj
      obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hj
      have hk' : k ∈ localSubset n d T := hk
      rw [localSubset, dif_pos (by omega)] at hk'
      obtain ⟨l, hl, hlk⟩ := Finset.mem_image.mp hk'
      have hlN : l ∈ nbhd (blockGraph n d) i :=
        Finset.mem_powerset.mp hT hl
      rw [← hkj, ← hlk, he_local l hlN]
      exact hl
    · intro hj
      apply Finset.mem_image.mpr
      let k : Fin d := ⟨j.val % d, Nat.mod_lt _ (by omega)⟩
      refine ⟨k, ?_, ?_⟩
      · rw [localSubset, dif_pos (by omega)]
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · exact he_local j (Finset.mem_powerset.mp hT hj)
  · intro S hS
    exact hlocal_embed S
  · intro T hT
    rfl

/-- The raw-coefficient contribution of a block schedule has exactly the
single-block representer mass. -/
lemma sum_abs_blockRawCoef_localSubset
    (n d β : ℕ) (p : ℝ) (hd : 1 ≤ d) (i : Fin n)
    (hi : i.val < activeCount n d) :
    ∑ T ∈ (nbhd (blockGraph n d) i).powerset,
        |blockRawCoef β p d (localSubset n d T)| =
      representerMass β p d := by
  simpa [representerMass] using
    sum_block_powerset_localSubset n d hd i hi
      (fun S => |blockRawCoef β p d S|)

/-- A supported cosine-prior schedule obeys the raw coefficient-mass
envelope whenever its baseline lies in `[-B/2,B/2]`. -/
lemma blockSchedule_mass_le
    (n d β : ℕ) (B p σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 ≤ B) (hβ : 1 ≤ β)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hσ : σ = -1 ∨ σ = 1)
    (U : Fin (blockCount n d) → ℝ)
    (hU : ∀ b, |U b| ≤ B / 2) :
    BoundedCoeffMass (blockGraph n d)
      (blockSchedule n d β B p σ hσ U) B := by
  classical
  intro i
  by_cases hi : i.val < activeCount n d
  · have hb : i.val / d < blockCount n d := by
      simp only [activeCount] at hi
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [Nat.mul_comm] using hi
    have hcond (T : Finset (Fin n))
        (hT : T ∈ (nbhd (blockGraph n d) i).powerset) :
        ∀ j ∈ T,
          j.val < activeCount n d ∧ j.val / d = i.val / d := by
      intro j hj
      have hjN := Finset.mem_powerset.mp hT hj
      exact ⟨((Finset.mem_filter.mp hjN).2).1,
        ((Finset.mem_filter.mp hjN).2).2.2⟩
    have hsigma : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    calc
      ∑ T ∈ (nbhd (blockGraph n d) i).powerset,
          |blockSchedule n d β B p σ hσ U i T| =
        ∑ T ∈ (nbhd (blockGraph n d) i).powerset,
          |(if T = ∅ then U ⟨i.val / d, hb⟩ else 0) +
            σ * tiltAmplitude B β p (blockCount n d) d *
              blockRawCoef β p d (localSubset n d T)| := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [blockSchedule, dif_pos hi, dif_pos (hcond T hT)]
        simp [baselineAt, hb]
      _ ≤ ∑ T ∈ (nbhd (blockGraph n d) i).powerset,
            |if T = ∅ then U ⟨i.val / d, hb⟩ else 0| +
          ∑ T ∈ (nbhd (blockGraph n d) i).powerset,
            |σ * tiltAmplitude B β p (blockCount n d) d *
              blockRawCoef β p d (localSubset n d T)| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro T hT
        exact abs_add_le _ _
      _ = |U ⟨i.val / d, hb⟩| +
          |tiltAmplitude B β p (blockCount n d) d| *
            representerMass β p d := by
        have hempty :
            (∅ : Finset (Fin n)) ∈
              (nbhd (blockGraph n d) i).powerset := by simp
        rw [show
            (∑ T ∈ (nbhd (blockGraph n d) i).powerset,
              |if T = ∅ then U ⟨i.val / d, hb⟩ else 0|) =
              |U ⟨i.val / d, hb⟩| by
          rw [Finset.sum_eq_single ∅]
          · simp
          · intro T hT hTne
            simp [hTne]
          · intro hnot
            exact (hnot hempty).elim]
        simp_rw [abs_mul, hsigma, one_mul]
        rw [← Finset.mul_sum,
          sum_abs_blockRawCoef_localSubset n d β p hd i hi]
      _ ≤ B / 2 + B / 2 := add_le_add (hU _) <|
        tiltAmplitude_mul_representerMass_le_half B β d
          (blockCount n d) p hB hβ hd hp0 hp1
      _ = B := by ring
  · have hnbhd : nbhd (blockGraph n d) i = ∅ := by
      ext j
      simp [nbhd, blockGraph, hi]
    simp [hnbhd, blockSchedule, hi, hB]

end CausalSmith.Experimentation.SnipeDegreeFrontier
