import Causalean.Stat.Concentration.Covering.VCCovering

/-!
Haussler-style VC packing bounds for finite Boolean classes.

This file isolates the probabilistic random-subsample extraction used in the
standard Haussler packing argument, then derives the cardinality and logarithmic
packing bounds from Sauer-Shelah.  The public API includes
`weightedHammingSq`, the separating-subsample extraction
`exists_separating_subsample`, the self-referential logarithmic solver
`self_log_solve`, and the final `vc_weightedHamming_packing_card_le` /
`vc_weightedHamming_log_packing_le` bounds.
-/

namespace Causalean.Stat.Concentration

open scoped BigOperators

/-- Weighted Hamming pseudo-distance squared between two Boolean vectors on
`Fin n`, using nonnegative coordinate weights. -/
def weightedHammingSq {n : ℕ} (w : Fin n → ℝ) (a b : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, if a j = b j then 0 else w j

/-- The set of sampled coordinates, pulled back along a coordinate map `J`, on
which a Boolean vector is true. -/
noncomputable def subsamplePattern {n m : ℕ} (J : Fin m → Fin n)
    (a : Fin n → Bool) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => a (J i) = true

/-- Nonnegative coordinate weights make the weighted Hamming pseudo-distance
nonnegative. -/
lemma weightedHammingSq_nonneg {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (a b : Fin n → Bool) :
    0 ≤ weightedHammingSq w a b := by
  classical
  unfold weightedHammingSq
  exact Finset.sum_nonneg fun j _ => by
    by_cases h : a j = b j
    · simp [h]
    · simp [h, hw j]

private lemma subsamplePattern_mem_iff {n m : ℕ} {J : Fin m → Fin n}
    {a : Fin n → Bool} {i : Fin m} :
    i ∈ subsamplePattern J a ↔ a (J i) = true := by
  classical
  simp [subsamplePattern]

private lemma sum_choose_le_succ_pow (n d : ℕ) :
    (∑ k ∈ Finset.Iic d, n.choose k) ≤ (n + 1) ^ d := by
  calc
    (∑ k ∈ Finset.Iic d, n.choose k) ≤ ∑ k ∈ Finset.Iic d, n ^ k := by
      refine Finset.sum_le_sum ?_
      intro k _hk
      exact Nat.choose_le_pow n k
    _ ≤ ∑ k ∈ Finset.Iic d, d.choose k * n ^ k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk' : k ≤ d := by simpa using hk
      have hchoose_pos : 1 ≤ d.choose k :=
        Nat.succ_le_of_lt (Nat.choose_pos hk')
      simpa [one_mul] using Nat.mul_le_mul_right (n ^ k) hchoose_pos
    _ = (n + 1) ^ d := by
      rw [add_pow]
      simp only [one_pow, mul_one, Nat.cast_id]
      apply Finset.sum_congr
      · ext k
        simp
      · intro k _hk
        rw [Nat.mul_comm]

private lemma product_sum_normalization {n m : ℕ} (g : Fin n → ℝ) :
    ∑ J : Fin m → Fin n, ∏ t : Fin m, g (J t) = (∑ j : Fin n, g j) ^ m := by
  rw [Fintype.sum_pow]

private lemma subsamplePattern_eq_iff {n m : ℕ} {J : Fin m → Fin n}
    {a b : Fin n → Bool} :
    subsamplePattern J a = subsamplePattern J b ↔ ∀ t : Fin m, a (J t) = b (J t) := by
  classical
  constructor
  · intro h t
    by_cases ha : a (J t) = true
    · have ht : t ∈ subsamplePattern J b := by
        rw [← h, subsamplePattern_mem_iff]
        exact ha
      rw [subsamplePattern_mem_iff] at ht
      rw [ha, ht]
    · have ha_false : a (J t) = false := by
        exact Bool.eq_false_of_not_eq_true ha
      by_cases hb : b (J t) = true
      · have ht : t ∈ subsamplePattern J a := by
          rw [h, subsamplePattern_mem_iff]
          exact hb
        rw [subsamplePattern_mem_iff] at ht
        exact False.elim (ha ht)
      · have hb_false : b (J t) = false := by
          exact Bool.eq_false_of_not_eq_true hb
        rw [ha_false, hb_false]
  · intro h
    ext t
    simp [subsamplePattern_mem_iff, h t]

private lemma per_pair_collision_sum {n m : ℕ} (w : Fin n → ℝ)
    (a b : Fin n → Bool) :
    (∑ J : Fin m → Fin n,
        (∏ t : Fin m, w (J t)) *
          (if (∀ t : Fin m, a (J t) = b (J t)) then (1 : ℝ) else 0)) =
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => a j = b j), w j) ^ m := by
  classical
  let g : Fin n → ℝ := fun j => w j * (if a j = b j then (1 : ℝ) else 0)
  have hpoint : ∀ J : Fin m → Fin n,
      (∏ t : Fin m, w (J t)) *
          (if (∀ t : Fin m, a (J t) = b (J t)) then (1 : ℝ) else 0) =
        ∏ t : Fin m, g (J t) := by
    intro J
    by_cases h : ∀ t : Fin m, a (J t) = b (J t)
    · simp [g, h]
    · have hprod_zero :
          ∏ t : Fin m, (if a (J t) = b (J t) then (1 : ℝ) else 0) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        push_neg at h
        rcases h with ⟨t, ht⟩
        exact ⟨t, Finset.mem_univ t, by simp [ht]⟩
      have hgprod_zero : (∏ t : Fin m, g (J t)) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        push_neg at h
        rcases h with ⟨t, ht⟩
        exact ⟨t, Finset.mem_univ t, by simp [g, ht]⟩
      simp [h, hgprod_zero]
  calc
    (∑ J : Fin m → Fin n,
        (∏ t : Fin m, w (J t)) *
          (if (∀ t : Fin m, a (J t) = b (J t)) then (1 : ℝ) else 0))
        = ∑ J : Fin m → Fin n, ∏ t : Fin m, g (J t) := by
          exact Finset.sum_congr rfl fun J _ => hpoint J
    _ = (∑ j : Fin n, g j) ^ m := product_sum_normalization g
    _ = (∑ j ∈ Finset.univ.filter (fun j : Fin n => a j = b j), w j) ^ m := by
      congr 1
      simp [g, Finset.sum_filter]

private lemma averaging_exists_zero_count {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (cnt : ι → ℕ)
    (hμsum : ∑ i : ι, μ i = 1)
    (hμnonneg : ∀ i, 0 ≤ μ i)
    (hmean : ∑ i : ι, μ i * (cnt i : ℝ) < 1) :
    ∃ i, cnt i = 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hge : 1 ≤ ∑ i : ι, μ i * (cnt i : ℝ) := by
    calc
      1 = ∑ i : ι, μ i := by rw [hμsum]
      _ = ∑ i : ι, μ i * (1 : ℝ) := by simp
      _ ≤ ∑ i : ι, μ i * (cnt i : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (hnone i)))
          (hμnonneg i)
  exact not_lt_of_ge hge hmean

private lemma collision_bound {n m : ℕ} (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (r ε W : ℝ)
    (hr : 0 < r) (_hε : 0 < ε) (_hεr : ε ≤ r)
    (hW : W = ∑ j : Fin n, w j) (hWpos : 0 < W)
    (hwsum : W ≤ r ^ 2) (a b : Fin n → Bool)
    (hsep : ε ^ 2 ≤ weightedHammingSq w a b) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => a j = b j), w j / W) ^ m ≤
      Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) := by
  classical
  -- The agreeing-coordinate weight is the total minus the weighted Hamming gap.
  have hagree : (∑ j ∈ Finset.univ.filter (fun j : Fin n => a j = b j), w j)
      = W - weightedHammingSq w a b := by
    rw [hW]
    unfold weightedHammingSq
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : a j = b j <;> simp [h]
  have hr2pos : 0 < r ^ 2 := by positivity
  have hWH_nonneg : 0 ≤ weightedHammingSq w a b := weightedHammingSq_nonneg w hw a b
  -- Normalize: the collision factor `s = (W - WH)/W` lies in `[0, 1 - ε²/r²]`.
  rw [← Finset.sum_div, hagree]
  set s : ℝ := (W - weightedHammingSq w a b) / W with hs_def
  have hs_nonneg : 0 ≤ s := by
    rw [hs_def]
    refine div_nonneg ?_ (le_of_lt hWpos)
    rw [← hagree]
    exact Finset.sum_nonneg (fun j _ => hw j)
  have hs_le1 : s ≤ 1 - ε ^ 2 / r ^ 2 := by
    rw [hs_def, sub_div, div_self (ne_of_gt hWpos)]
    have hratio : ε ^ 2 / r ^ 2 ≤ weightedHammingSq w a b / W := by
      rw [div_le_div_iff₀ hr2pos hWpos]
      nlinarith [hsep, hwsum, hWH_nonneg, sq_nonneg ε]
    linarith
  have hexp : 1 - ε ^ 2 / r ^ 2 ≤ Real.exp (-(ε ^ 2 / r ^ 2)) := by
    have h := Real.add_one_le_exp (-(ε ^ 2 / r ^ 2))
    linarith
  have hs_le_exp : s ≤ Real.exp (-(ε ^ 2 / r ^ 2)) := le_trans hs_le1 hexp
  calc s ^ m ≤ (Real.exp (-(ε ^ 2 / r ^ 2))) ^ m :=
        pow_le_pow_left₀ hs_nonneg hs_le_exp m
    _ = Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- A sampled Boolean trace family with bounded VC dimension has polynomially
many realized restricted patterns. -/
lemma card_subsample_family_le_succ_pow {n m d : ℕ} (J : Fin m → Fin n)
    (P : Finset (Fin n → Bool))
    (hvcJ : (P.image (subsamplePattern J)).vcDim ≤ d) :
    (P.image (subsamplePattern J)).card ≤ (m + 1) ^ d := by
  exact le_trans
    (card_growthFamily_le_sum_choose (P.image (subsamplePattern J)) hvcJ)
    (sum_choose_le_succ_pow m d)

/-- Restricting a Boolean set family along a coordinate map does not increase
VC dimension.

If the restricted family shatters a set of sampled coordinates `T`, then `J` is
injective on `T`: otherwise a singleton trace would demand two equal original
coordinates have different Boolean values.  The image `J '' T` is therefore
shattered by the original true-set family. -/
lemma subsample_image_vcDim_le {n m : ℕ} (d : ℕ) (J : Fin m → Fin n)
    (P : Finset (Fin n → Bool))
    (hvc : (P.image (fun a => Finset.univ.filter (fun j => a j = true))).vcDim ≤ d) :
    (P.image (subsamplePattern J)).vcDim ≤ d := by
  classical
  let A : Finset (Finset (Fin n)) :=
    P.image (fun a => Finset.univ.filter (fun j => a j = true))
  let B : Finset (Finset (Fin m)) := P.image (subsamplePattern J)
  have hB_le_A : B.vcDim ≤ A.vcDim := by
    unfold Finset.vcDim
    refine Finset.sup_le ?_
    intro T hTmem
    have hT : B.Shatters T := Finset.mem_shatterer.mp hTmem
    let U : Finset (Fin n) := T.image J
    have hinj : Set.InjOn J (↑T) := by
      intro i hi k hk hJ
      by_contra hik
      have hsingle : ({i} : Finset (Fin m)) ⊆ T :=
        Finset.singleton_subset_iff.mpr hi
      obtain ⟨u, huB, hTu⟩ := hT hsingle
      rcases Finset.mem_image.mp huB with ⟨a, _haP, rfl⟩
      have hi_inter : i ∈ T ∩ subsamplePattern J a := by
        rw [hTu]
        simp
      have hi_pat : i ∈ subsamplePattern J a := (Finset.mem_inter.mp hi_inter).2
      have hk_pat : k ∈ subsamplePattern J a := by
        rw [subsamplePattern_mem_iff] at hi_pat ⊢
        simpa [hJ] using hi_pat
      have hk_inter : k ∈ T ∩ subsamplePattern J a :=
        Finset.mem_inter.mpr ⟨hk, hk_pat⟩
      have hk_single : k ∈ ({i} : Finset (Fin m)) := by
        rw [← hTu]
        exact hk_inter
      have hki : k = i := by simpa using hk_single
      exact hik hki.symm
    have hAshat : A.Shatters U := by
      intro S hS
      let S' : Finset (Fin m) := T.filter fun i => J i ∈ S
      have hS'T : S' ⊆ T := by
        intro i hi
        exact (Finset.mem_filter.mp hi).1
      obtain ⟨u, huB, hTu⟩ := hT hS'T
      rcases Finset.mem_image.mp huB with ⟨a, haP, rfl⟩
      refine ⟨Finset.univ.filter (fun j => a j = true), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, haP, rfl⟩
      · ext x
        constructor
        · intro hx
          rcases Finset.mem_inter.mp hx with ⟨hxU, hxtrue⟩
          rcases Finset.mem_image.mp hxU with ⟨i, hiT, rfl⟩
          have hi_pat : i ∈ subsamplePattern J a := by
            rw [subsamplePattern_mem_iff]
            simpa using (Finset.mem_filter.mp hxtrue).2
          have hiS' : i ∈ S' := by
            rw [← hTu]
            exact Finset.mem_inter.mpr ⟨hiT, hi_pat⟩
          exact (Finset.mem_filter.mp hiS').2
        · intro hxS
          have hxU : x ∈ U := hS hxS
          rcases Finset.mem_image.mp hxU with ⟨i, hiT, hJi⟩
          have hiS' : i ∈ S' :=
            Finset.mem_filter.mpr ⟨hiT, by simpa [hJi] using hxS⟩
          have hi_inter : i ∈ T ∩ subsamplePattern J a := by
            rw [hTu]
            exact hiS'
          have hi_pat : i ∈ subsamplePattern J a := (Finset.mem_inter.mp hi_inter).2
          refine Finset.mem_inter.mpr ⟨hxU, ?_⟩
          rw [Finset.mem_filter]
          constructor
          · simp
          · rw [subsamplePattern_mem_iff] at hi_pat
            simpa [hJi] using hi_pat
    have hU_le : U.card ≤ A.vcDim := Finset.Shatters.card_le_vcDim hAshat
    have hcard : U.card = T.card := Finset.card_image_of_injOn hinj
    exact hcard.ge.trans hU_le
  exact hB_le_A.trans hvc

/-- Finite averaging core for the weighted random-coordinate extraction.

The proof samples `J : Fin m → Fin n` from the product weights
`∏ t, w (J t) / ∑ j, w j`, expands the finite product sums, union-bounds
ordered distinct pairs from `P`, and uses
`m = ⌊(2 * r ^ 2 / ε ^ 2) * log(P.card)⌋₊ + 1` to make the expected number of
unseparated pairs strictly less than one. -/
lemma finite_averaging_exists_separating_subsample {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hwsum : ∑ j, w j ≤ r ^ 2)
    (P : Finset (Fin n → Bool)) (hPcard : 2 ≤ P.card)
    (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ε ^ 2 ≤ weightedHammingSq w a b) :
    ∃ (m : ℕ) (J : Fin m → Fin n),
      (m : ℝ) ≤ 1 + (2 * r ^ 2 / ε ^ 2) * Real.log (P.card) ∧
      Set.InjOn (subsamplePattern J) ↑P := by
  classical
  let W : ℝ := ∑ j : Fin n, w j
  have hWdef : W = ∑ j : Fin n, w j := rfl
  have hWpos : 0 < W := by
    have htwo : 1 < P.card := by omega
    rcases Finset.one_lt_card.mp htwo with ⟨a, haP, b, hbP, hab⟩
    have hdist_le_W : weightedHammingSq w a b ≤ W := by
      dsimp [W]
      unfold weightedHammingSq
      refine Finset.sum_le_sum ?_
      intro j _hj
      by_cases h : a j = b j
      · simp [h, hw j]
      · simp [h]
    have hdist_pos : 0 < weightedHammingSq w a b := by
      have hεsq : 0 < ε ^ 2 := sq_pos_of_ne_zero (ne_of_gt hε)
      exact lt_of_lt_of_le hεsq (hsep a haP b hbP hab)
    exact lt_of_lt_of_le hdist_pos hdist_le_W
  have hwsumW : W ≤ r ^ 2 := by simpa [W] using hwsum
  let L : ℝ := (2 * r ^ 2 / ε ^ 2) * Real.log (P.card)
  let m : ℕ := ⌊L⌋₊ + 1
  have hPpos_nat : 0 < P.card := by omega
  have hPone_nat : 1 ≤ P.card := by omega
  have hPpos_real : 0 < (P.card : ℝ) := by exact_mod_cast hPpos_nat
  have hLnonneg : 0 ≤ L := by
    have hcoef_nonneg : 0 ≤ 2 * r ^ 2 / ε ^ 2 := by positivity
    have hlog_nonneg : 0 ≤ Real.log (P.card) :=
      Real.log_nonneg (by exact_mod_cast hPone_nat)
    exact mul_nonneg hcoef_nonneg hlog_nonneg
  have hm_bound : (m : ℝ) ≤ 1 + (2 * r ^ 2 / ε ^ 2) * Real.log (P.card) := by
    have hfloor : ((⌊L⌋₊ : ℕ) : ℝ) ≤ L := Nat.floor_le hLnonneg
    dsimp [m, L]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  let μ : (Fin m → Fin n) → ℝ := fun J => ∏ t : Fin m, (w (J t) / W)
  let cnt : (Fin m → Fin n) → ℕ := fun J =>
    (P.offDiag.filter fun ab => subsamplePattern J ab.1 = subsamplePattern J ab.2).card
  have hμsum : ∑ J : Fin m → Fin n, μ J = 1 := by
    dsimp [μ]
    rw [product_sum_normalization (n := n) (m := m) (fun j : Fin n => w j / W)]
    have hsum : (∑ j : Fin n, w j / W) = 1 := by
      rw [← Finset.sum_div]
      rw [← hWdef]
      exact div_self (ne_of_gt hWpos)
    rw [hsum, one_pow]
  have hμnonneg : ∀ J : Fin m → Fin n, 0 ≤ μ J := by
    intro J
    dsimp [μ]
    exact Finset.prod_nonneg fun t _ht => div_nonneg (hw (J t)) (le_of_lt hWpos)
  have hcnt_cast : ∀ J : Fin m → Fin n,
      (cnt J : ℝ) =
        ∑ ab ∈ P.offDiag,
          if subsamplePattern J ab.1 = subsamplePattern J ab.2 then (1 : ℝ) else 0 := by
    intro J
    dsimp [cnt]
    simp
  have hinner : ∀ ab ∈ P.offDiag,
      (∑ J : Fin m → Fin n,
          μ J *
            (if subsamplePattern J ab.1 = subsamplePattern J ab.2 then (1 : ℝ) else 0)) =
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ab.1 j = ab.2 j), w j / W) ^ m := by
    intro ab _hab
    calc
      (∑ J : Fin m → Fin n,
          μ J *
            (if subsamplePattern J ab.1 = subsamplePattern J ab.2 then (1 : ℝ) else 0))
          =
        ∑ J : Fin m → Fin n,
          (∏ t : Fin m, (w (J t) / W)) *
            (if (∀ t : Fin m, ab.1 (J t) = ab.2 (J t)) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro J _hJ
          dsimp [μ]
          by_cases h :
              subsamplePattern J ab.1 = subsamplePattern J ab.2
          · have hforall :
                ∀ t : Fin m, ab.1 (J t) = ab.2 (J t) :=
              subsamplePattern_eq_iff.mp h
            simp [h, hforall]
          · have hforall :
                ¬ ∀ t : Fin m, ab.1 (J t) = ab.2 (J t) := by
              intro hall
              exact h (subsamplePattern_eq_iff.mpr hall)
            simp [h, hforall]
      _ = (∑ j ∈ Finset.univ.filter (fun j : Fin n => ab.1 j = ab.2 j), w j / W) ^ m := by
          exact per_pair_collision_sum (fun j : Fin n => w j / W) ab.1 ab.2
  have hmean_le :
      (∑ J : Fin m → Fin n, μ J * (cnt J : ℝ)) ≤
        (P.offDiag.card : ℝ) * Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) := by
    calc
      (∑ J : Fin m → Fin n, μ J * (cnt J : ℝ))
          =
        ∑ J : Fin m → Fin n,
          μ J *
            (∑ ab ∈ P.offDiag,
              if subsamplePattern J ab.1 = subsamplePattern J ab.2 then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro J _hJ
          rw [hcnt_cast J]
      _ =
        ∑ J : Fin m → Fin n, ∑ ab ∈ P.offDiag,
          μ J *
            (if subsamplePattern J ab.1 = subsamplePattern J ab.2 then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro J _hJ
          rw [Finset.mul_sum]
      _ =
        ∑ ab ∈ P.offDiag, ∑ J : Fin m → Fin n,
          μ J *
            (if subsamplePattern J ab.1 = subsamplePattern J ab.2 then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
      _ ≤ ∑ ab ∈ P.offDiag, Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro ab hab
          rw [hinner ab hab]
          rcases Finset.mem_offDiag.mp hab with ⟨haP, hbP, habne⟩
          exact collision_bound w hw r ε W hr hε hεr hWdef hWpos hwsumW ab.1 ab.2
            (hsep ab.1 haP ab.2 hbP habne)
      _ = (P.offDiag.card : ℝ) * Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) := by
          simp
  have hmean_lt_one :
      (∑ J : Fin m → Fin n, μ J * (cnt J : ℝ)) < 1 := by
    have hm_gt_L : L < (m : ℝ) := by
      dsimp [m]
      simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one L)
    have hscale_pos : 0 < ε ^ 2 / r ^ 2 := by positivity
    have hscaled :
        L * (ε ^ 2 / r ^ 2) < (m : ℝ) * (ε ^ 2 / r ^ 2) :=
      mul_lt_mul_of_pos_right hm_gt_L hscale_pos
    have hLscale : L * (ε ^ 2 / r ^ 2) = 2 * Real.log (P.card) := by
      dsimp [L]
      field_simp [ne_of_gt hε, ne_of_gt hr]
    have hmexp : 2 * Real.log (P.card) < (m : ℝ) * ε ^ 2 / r ^ 2 := by
      rw [hLscale] at hscaled
      convert hscaled using 1
      ring
    have hneg :
        -((m : ℝ) * ε ^ 2 / r ^ 2) < -(2 * Real.log (P.card)) := by
      linarith
    have hexp_lt :
        Real.exp (-((m : ℝ) * ε ^ 2 / r ^ 2)) <
          Real.exp (-(2 * Real.log (P.card))) :=
      Real.exp_lt_exp.mpr hneg
    have hoff_card : (P.offDiag.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
      have hn : P.offDiag.card ≤ P.card * P.card := by
        rw [Finset.offDiag_card]
        omega
      have hnreal : (P.offDiag.card : ℝ) ≤ (P.card * P.card : ℕ) := by
        exact_mod_cast hn
      simpa [sq] using hnreal
    have hN2pos : 0 < (P.card : ℝ) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hPpos_real)
    have hprod_lt :
        (P.card : ℝ) ^ 2 * Real.exp (-((m : ℝ) * ε ^ 2 / r ^ 2)) <
          (P.card : ℝ) ^ 2 * Real.exp (-(2 * Real.log (P.card))) :=
      mul_lt_mul_of_pos_left hexp_lt hN2pos
    have hexp_neg_eq :
        Real.exp (-(2 * Real.log (P.card))) = ((P.card : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_neg]
      have htwice :
          Real.exp (2 * Real.log (P.card)) = (P.card : ℝ) ^ 2 := by
        have hrewrite :
            2 * Real.log (P.card) =
              Real.log (P.card) + Real.log (P.card) := by ring
        rw [hrewrite, Real.exp_add, Real.exp_log hPpos_real]
        ring
      rw [htwice]
    have hprod_eq :
        (P.card : ℝ) ^ 2 * Real.exp (-(2 * Real.log (P.card))) = 1 := by
      rw [hexp_neg_eq]
      exact mul_inv_cancel₀ (ne_of_gt hN2pos)
    have hcardexp_le :
        (P.offDiag.card : ℝ) * Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) ≤
          (P.card : ℝ) ^ 2 * Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) := by
      exact mul_le_mul_of_nonneg_right hoff_card (le_of_lt (Real.exp_pos _))
    have hprod_lt_one :
        (P.card : ℝ) ^ 2 * Real.exp (-(m : ℝ) * ε ^ 2 / r ^ 2) < 1 := by
      convert (by simpa [hprod_eq] using hprod_lt) using 2
      ring_nf
    exact lt_of_le_of_lt (hmean_le.trans hcardexp_le) hprod_lt_one
  obtain ⟨J, hcnt_zero⟩ := averaging_exists_zero_count μ cnt hμsum hμnonneg hmean_lt_one
  refine ⟨m, J, hm_bound, ?_⟩
  intro a haP b hbP hpat
  by_contra hab
  have hbad_mem :
      (a, b) ∈ P.offDiag.filter
        (fun ab => subsamplePattern J ab.1 = subsamplePattern J ab.2) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_offDiag.mpr ⟨haP, hbP, hab⟩, hpat⟩
  have hcnt_pos : 0 < cnt J := by
    dsimp [cnt]
    exact Finset.card_pos.mpr ⟨(a, b), hbad_mem⟩
  exact (Nat.ne_of_gt hcnt_pos) hcnt_zero

/-- Honest isolated core: the weighted random-coordinate extraction.

A separating subsample of length `m ≤ 1 + (2 r²/ε²) * log(P.card)` exists.  The
`log(P.card)` dependence is essential: injectivity forces `2^m ≥ P.card`. -/
lemma exists_separating_subsample {n : ℕ} (d : ℕ) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hwsum : ∑ j, w j ≤ r ^ 2)
    (P : Finset (Fin n → Bool)) (hPcard : 2 ≤ P.card)
    (hvc : (P.image (fun a => (Finset.univ.filter (fun j => a j = true)))).vcDim ≤ d)
    (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ε ^ 2 ≤ weightedHammingSq w a b) :
    ∃ (m : ℕ) (J : Fin m → Fin n),
      (m : ℝ) ≤ 1 + (2 * r ^ 2 / ε ^ 2) * Real.log (P.card) ∧
      (P.image (subsamplePattern J)).vcDim ≤ d ∧
      Set.InjOn (subsamplePattern J) ↑P := by
  obtain ⟨m, J, hm, hinj⟩ :=
    finite_averaging_exists_separating_subsample w hw r ε hr hε hεr hwsum P hPcard hsep
  exact ⟨m, J, hm, subsample_image_vcDim_le d J P hvc, hinj⟩

/-- A self-referential logarithmic inequality implies an explicit linear-log
upper bound. -/
lemma self_log_solve {a L : ℝ} {d : ℕ} (hd : 1 ≤ d) (ha : 2 ≤ a) (hL : 0 ≤ L)
    (hbound : L ≤ (d : ℝ) * Real.log (2 + a * L)) :
    L ≤ 1 + 2 * (d : ℝ) * Real.log (2 * a * (d : ℝ)) := by
  have hd_pos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hd_nonneg : 0 ≤ (d : ℝ) := le_of_lt hd_pos
  have ha_pos : 0 < a := by linarith
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have hy_pos : 0 < 2 + a * L := by
    have hmul_nonneg : 0 ≤ a * L := mul_nonneg ha_nonneg hL
    linarith
  have ht_pos : 0 < 2 * a * (d : ℝ) := by positivity
  have hlog_tangent :
      Real.log (2 + a * L) ≤
        (2 + a * L) / (2 * a * (d : ℝ)) + Real.log (2 * a * (d : ℝ)) - 1 := by
    have hratio_pos : 0 < (2 + a * L) / (2 * a * (d : ℝ)) :=
      div_pos hy_pos ht_pos
    have h0 := Real.log_le_sub_one_of_pos hratio_pos
    have hlog_div :
        Real.log ((2 + a * L) / (2 * a * (d : ℝ))) =
          Real.log (2 + a * L) - Real.log (2 * a * (d : ℝ)) := by
      exact Real.log_div (ne_of_gt hy_pos) (ne_of_gt ht_pos)
    rw [hlog_div] at h0
    linarith
  have hstep :
      L ≤ (d : ℝ) *
        ((2 + a * L) / (2 * a * (d : ℝ)) + Real.log (2 * a * (d : ℝ)) - 1) := by
    exact le_trans hbound (mul_le_mul_of_nonneg_left hlog_tangent hd_nonneg)
  have hrewrite :
      (d : ℝ) *
          ((2 + a * L) / (2 * a * (d : ℝ)) + Real.log (2 * a * (d : ℝ)) - 1)
        = 1 / a + L / 2 + (d : ℝ) * Real.log (2 * a * (d : ℝ)) - (d : ℝ) := by
    field_simp [ne_of_gt ha_pos, ne_of_gt hd_pos]
  have hstep' :
      L ≤ 1 / a + L / 2 + (d : ℝ) * Real.log (2 * a * (d : ℝ)) - (d : ℝ) := by
    rwa [hrewrite] at hstep
  have hdrop : L ≤ 1 / a + L / 2 + (d : ℝ) * Real.log (2 * a * (d : ℝ)) := by
    linarith
  have hhalf' : L ≤ 2 * (1 / a + (d : ℝ) * Real.log (2 * a * (d : ℝ))) := by
    linarith
  have hhalf : L ≤ 2 / a + 2 * (d : ℝ) * Real.log (2 * a * (d : ℝ)) := by
    convert hhalf' using 1
    ring
  have htwo_div_le_one : 2 / a ≤ 1 := (div_le_one ha_pos).2 ha
  linarith

private lemma haussler_log_rhs_nonneg
    {d : ℕ} {r ε : ℝ} (hε : 0 < ε) (hεr : ε ≤ r) :
    0 ≤ 1 + 2 * (d : ℝ) * Real.log (4 * (d : ℝ) * r ^ 2 / ε ^ 2) := by
  by_cases hd0 : d = 0
  · simp [hd0]
  have hd : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
  have hd_real : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hx : 1 ≤ r / ε := (one_le_div hε).mpr hεr
  have hsq : 1 ≤ r ^ 2 / ε ^ 2 := by
    rw [← div_pow]
    nlinarith [sq_nonneg (r / ε)]
  have harg_ge_one : 1 ≤ 4 * (d : ℝ) * r ^ 2 / ε ^ 2 := by
    have hrewrite :
        4 * (d : ℝ) * r ^ 2 / ε ^ 2 = (4 * (d : ℝ)) * (r ^ 2 / ε ^ 2) := by
      ring
    rw [hrewrite]
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log (4 * (d : ℝ) * r ^ 2 / ε ^ 2) :=
    Real.log_nonneg harg_ge_one
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  have hcoef_nonneg : 0 ≤ 2 * (d : ℝ) := by positivity
  have hterm_nonneg :
      0 ≤ 2 * (d : ℝ) * Real.log (4 * (d : ℝ) * r ^ 2 / ε ^ 2) :=
    mul_nonneg hcoef_nonneg hlog_nonneg
  linarith

/-- HAUSSLER ε-PACKING BOUND, logarithmic form.  A finite Boolean family with
VC dimension at most `d`, total weight at most `r²`, and pairwise weighted
Hamming separation at least `ε²` has log-cardinality bounded by a quantity
depending on `d` and `r²/ε²`, with no ambient-coordinate dependence. -/
theorem vc_weightedHamming_packing_card_le
    {n : ℕ} (d : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hwsum : ∑ j, w j ≤ r ^ 2)
    (P : Finset (Fin n → Bool))
    (hvc : (P.image (fun a => (Finset.univ.filter (fun j => a j = true)))).vcDim ≤ d)
    (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ε ^ 2 ≤ weightedHammingSq w a b) :
    Real.log (P.card) ≤
      1 + 2 * (d : ℝ) * Real.log (4 * (d : ℝ) * r ^ 2 / ε ^ 2) := by
  classical
  by_cases hsmall : P.card ≤ 1
  · have hlog_nonpos : Real.log (P.card) ≤ 0 := by
      have hcases : P.card = 0 ∨ P.card = 1 := by omega
      rcases hcases with hzero | hone
      · simp [hzero]
      · simp [hone]
    exact le_trans hlog_nonpos (haussler_log_rhs_nonneg hε hεr)
  have hPcard : 2 ≤ P.card := by omega
  obtain ⟨m, J, hm, hvcJ, hinj⟩ :=
    exists_separating_subsample d w hw r ε hr hε hεr hwsum P hPcard hvc hsep
  have hcard_image : (P.image (subsamplePattern J)).card = P.card :=
    Finset.card_image_of_injOn hinj
  have hcard_nat : P.card ≤ (m + 1) ^ d := by
    rw [← hcard_image]
    exact card_subsample_family_le_succ_pow J P hvcJ
  by_cases hd0 : d = 0
  · have : P.card ≤ 1 := by simpa [hd0] using hcard_nat
    omega
  have hd : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
  let L : ℝ := Real.log (P.card)
  let a : ℝ := 2 * r ^ 2 / ε ^ 2
  have hPcard_pos : 0 < P.card := by omega
  have hPcard_one : 1 ≤ P.card := by omega
  have hL_nonneg : 0 ≤ L := by
    exact Real.log_nonneg (by exact_mod_cast hPcard_one)
  have ha : 2 ≤ a := by
    have hx : 1 ≤ r / ε := (one_le_div hε).mpr hεr
    have hsq : 1 ≤ r ^ 2 / ε ^ 2 := by
      rw [← div_pow]
      nlinarith [sq_nonneg (r / ε)]
    dsimp [a]
    calc
      2 ≤ 2 * (r ^ 2 / ε ^ 2) := by nlinarith
      _ = 2 * r ^ 2 / ε ^ 2 := by ring
  have hcard_real : (P.card : ℝ) ≤ (((m + 1) ^ d : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hlog_card_le_pow : L ≤ Real.log ((((m + 1) ^ d : ℕ) : ℝ)) := by
    dsimp [L]
    exact Real.log_le_log (by exact_mod_cast hPcard_pos) hcard_real
  have hlog_pow :
      Real.log ((((m + 1) ^ d : ℕ) : ℝ)) =
        (d : ℝ) * Real.log (((m + 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hL_le_m : L ≤ (d : ℝ) * Real.log (((m + 1 : ℕ) : ℝ)) := by
    rwa [hlog_pow] at hlog_card_le_pow
  have hm_succ : (((m + 1 : ℕ) : ℝ)) ≤ 2 + a * L := by
    dsimp [a, L] at hm ⊢
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  have hm_succ_pos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hlog_m_le : Real.log (((m + 1 : ℕ) : ℝ)) ≤ Real.log (2 + a * L) :=
    Real.log_le_log hm_succ_pos hm_succ
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  have hbound : L ≤ (d : ℝ) * Real.log (2 + a * L) := by
    exact le_trans hL_le_m (mul_le_mul_of_nonneg_left hlog_m_le hd_nonneg)
  have hsolve := self_log_solve (a := a) (L := L) (d := d) hd ha hL_nonneg hbound
  dsimp [L, a] at hsolve
  convert hsolve using 2
  ring_nf

/-- Logarithmic form of the finite Boolean Haussler packing bound. -/
theorem vc_weightedHamming_log_packing_le
    {n : ℕ} (d : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hwsum : ∑ j, w j ≤ r ^ 2)
    (P : Finset (Fin n → Bool))
    (hvc : (P.image (fun a => (Finset.univ.filter (fun j => a j = true)))).vcDim ≤ d)
    (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ε ^ 2 ≤ weightedHammingSq w a b) :
    Real.log (P.card) ≤
      1 + 2 * (d : ℝ) * Real.log (4 * (d : ℝ) * r ^ 2 / ε ^ 2) := by
  exact vc_weightedHamming_packing_card_le d w hw r ε hr hε hεr hwsum P hvc hsep

end Causalean.Stat.Concentration
