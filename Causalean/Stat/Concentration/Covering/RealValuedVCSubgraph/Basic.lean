import Causalean.Stat.Concentration.Covering.HausslerPacking
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Order.TeichmullerTukey

/-!
# Real-valued VC-subgraph covering: core definitions

This module gives a finite-trace definition of pseudo-dimension, an explicit
`L²(Q)` covering predicate, and the uniform polynomial entropy theorem for a
bounded measurable VC-subgraph class.  The definitions deliberately quantify
over an arbitrary probability measure; the finite-sample bridge is developed
in `Empirical`.
-/
namespace Causalean.Stat.Concentration
open MeasureTheory
open Causalean.Stat.Concentration
universe u v
variable {𝒳 : Type u} {ι : Type v}
/-- The strict subgraph classifier attached to a real-valued function class
labels `(x,t)` precisely when `t < f(x)`. -/
noncomputable def subgraphClassifier (F : ι → 𝒳 → ℝ) (i : ι) (z : 𝒳 × ℝ) : Bool :=
  decide (z.2 < F i z.1)
/-- A real-valued class has pseudo-dimension at most `d` when every finite
trace of its strict subgraphs has VC dimension at most `d`. -/
def HasPseudoDimAtMost (F : ι → 𝒳 → ℝ) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (T : Fin n → 𝒳 × ℝ),
    (growthFamily (subgraphClassifier F) T).vcDim ≤ d
/-- The pseudo-dimension certificate unfolds to the existing finite Boolean
growth-family VC certificate on every thresholded sample. -/
theorem hasPseudoDimAtMost_iff_growthFamily
    (F : ι → 𝒳 → ℝ) (d : ℕ) :
    HasPseudoDimAtMost F d ↔
      ∀ (n : ℕ) (T : Fin n → 𝒳 × ℝ),
        (growthFamily (subgraphClassifier F) T).vcDim ≤ d := by
  rfl
/-- The `L²(Q)` semidistance is the square root of the integral of the squared
pointwise difference. -/
noncomputable def measureL2Dist [MeasurableSpace 𝒳]
    (Q : Measure 𝒳) (f g : 𝒳 → ℝ) : ℝ :=
  Real.sqrt (∫ x, (f x - g x) ^ 2 ∂Q)
/-- A finite set of class indices is an open `L²(Q)` cover at radius `r` when
every class member is within distance strictly less than `r` of one center. -/
def IsL2Cover [MeasurableSpace 𝒳] (Q : Measure 𝒳)
    (F : ι → 𝒳 → ℝ) (r : ℝ) (C : Finset ι) : Prop :=
  ∀ i : ι, ∃ j ∈ C, measureL2Dist Q (F i) (F j) < r
/-- The `L²(Q)` covering number is at most `N` when an index-valued cover with
at most `N` centers exists. -/
def L2CoveringNumberLe [MeasurableSpace 𝒳] (Q : Measure 𝒳)
    (F : ι → 𝒳 → ℝ) (r : ℝ) (N : ℕ) : Prop :=
  ∃ C : Finset ι, C.card ≤ N ∧ IsL2Cover Q F r C
/-- The explicit polynomial cardinality used by the public VC-subgraph bound.
Its constants are universal and intentionally non-optimized. -/
noncomputable def vcSubgraphCoverBound (d : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil ((16 / ε) ^ (8 * (d + 1)))
private lemma sum_choose_le_four_mul_div_pow
    {m d : ℕ} (hd : 0 < d) (hdm : d ≤ m) :
    ((∑ k ∈ Finset.Iic d, m.choose k : ℕ) : ℝ) ≤
      (4 * (m : ℝ) / (d : ℝ)) ^ d := by
  let q : ℝ := (d : ℝ) / (m : ℝ)
  have hm : 0 < m := lt_of_lt_of_le hd hdm
  have hq : 0 < q := by positivity
  have hq0 : 0 ≤ q := hq.le
  have hq1 : q ≤ 1 := (div_le_one (by positivity)).2 (by exact_mod_cast hdm)
  have hweighted :
      q ^ d * ((∑ k ∈ Finset.Iic d, m.choose k : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.Iic d, (m.choose k : ℝ) * q ^ k := by
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k hk
    have hkd : k ≤ d := by simpa using hk
    calc
      q ^ d * (m.choose k : ℝ) ≤ q ^ k * (m.choose k : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 hkd) (by positivity)
      _ = (m.choose k : ℝ) * q ^ k := by ring
  have hsubset : Finset.Iic d ⊆ Finset.Iic m :=
    Finset.Iic_subset_Iic.mpr hdm
  have hfull :
      (∑ k ∈ Finset.Iic d, (m.choose k : ℝ) * q ^ k) ≤ (q + 1) ^ m := by
    calc
      (∑ k ∈ Finset.Iic d, (m.choose k : ℝ) * q ^ k) ≤
          ∑ k ∈ Finset.Iic m, (m.choose k : ℝ) * q ^ k := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun k _ _ => mul_nonneg (by positivity) (pow_nonneg hq0 k))
      _ = (q + 1) ^ m := by
        rw [add_pow]
        simp only [one_pow, mul_one]
        apply Finset.sum_congr
        · ext k
          simp
        · intro k _
          ring
  have hpow_exp : (q + 1) ^ m ≤ Real.exp (d : ℝ) := by
    calc
      (q + 1) ^ m ≤ (Real.exp q) ^ m :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp q) m
      _ = Real.exp ((m : ℝ) * q) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (d : ℝ) := by
        congr 1
        dsimp [q]
        field_simp
  have hexp_le : Real.exp (d : ℝ) ≤ (3 : ℝ) ^ d := by
    rw [show (d : ℝ) = (d : ℝ) * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1))
      (le_of_lt Real.exp_one_lt_three) d
  have hscaled :
      q ^ d * ((∑ k ∈ Finset.Iic d, m.choose k : ℕ) : ℝ) ≤ (4 : ℝ) ^ d := by
    exact hweighted.trans (hfull.trans (hpow_exp.trans
      (hexp_le.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
        (by norm_num : (3 : ℝ) ≤ 4) d))))
  have htarget : q ^ d * (4 * (m : ℝ) / (d : ℝ)) ^ d = (4 : ℝ) ^ d := by
    rw [← mul_pow]; congr 1; dsimp [q]; field_simp
  rw [← htarget] at hscaled
  exact (mul_le_mul_iff_of_pos_left (pow_pos hq d)).mp hscaled
private lemma volume_symmDiff_Iio (a b : ℝ) :
    volume (symmDiff (Set.Iio a) (Set.Iio b)) = ENNReal.ofReal |a - b| := by
  rcases le_total a b with h | h
  · rw [show symmDiff (Set.Iio a) (Set.Iio b) = Set.Ico a b by
      ext t
      simp only [Set.symmDiff_def, Set.mem_union, Set.mem_diff, Set.mem_Iio, Set.mem_Ico]
      constructor
      · rintro (⟨hta, htb⟩ | ⟨htb, hta⟩)
        · exact False.elim (htb (lt_of_lt_of_le hta h))
        · exact ⟨le_of_not_gt hta, htb⟩
      · intro ht
        exact Or.inr ⟨ht.2, fun hta => (not_lt_of_ge ht.1) hta⟩]
    rw [Real.volume_Ico]
    congr 1
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [show symmDiff (Set.Iio a) (Set.Iio b) = Set.Ico b a by
      ext t
      simp only [Set.symmDiff_def, Set.mem_union, Set.mem_diff, Set.mem_Iio, Set.mem_Ico]
      constructor
      · rintro (⟨hta, htb⟩ | ⟨htb, hta⟩)
        · exact ⟨le_of_not_gt htb, hta⟩
        · exact False.elim (hta (lt_of_lt_of_le htb h))
      · intro ht
        exact Or.inl ⟨ht.2, fun htb => (not_lt_of_ge ht.1) htb⟩]
    rw [Real.volume_Ico]
    congr 1
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
private lemma prod_subgraph_symmDiff
    [MeasurableSpace 𝒳] (Q : Measure 𝒳) (f g : 𝒳 → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    (Q.prod volume) (symmDiff {z : 𝒳 × ℝ | z.2 < f z.1}
      {z : 𝒳 × ℝ | z.2 < g z.1}) =
      ∫⁻ x, ENNReal.ofReal |f x - g x| ∂Q := by
  have hAf : MeasurableSet {z : 𝒳 × ℝ | z.2 < f z.1} :=
    measurableSet_lt measurable_snd (hf.comp measurable_fst)
  have hAg : MeasurableSet {z : 𝒳 × ℝ | z.2 < g z.1} :=
    measurableSet_lt measurable_snd (hg.comp measurable_fst)
  rw [Measure.prod_apply (hAf.symmDiff hAg)]
  apply lintegral_congr
  intro x
  change volume (symmDiff (Set.Iio (f x)) (Set.Iio (g x))) = _
  exact volume_symmDiff_Iio (f x) (g x)
/-- A finite Boolean VC class with nonnegative coordinate weights has a
dimension-free-base polynomial packing bound in weighted Hamming distance.

This is the sharp finite combinatorial input needed for real-valued
VC-subgraph entropy.  Unlike the logarithmic estimate already available in
`HausslerPacking`, its base is independent of the VC dimension. -/
theorem sharp_vc_weightedHamming_packing_card_le
    {n : ℕ} (d : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hwsum : ∑ j, w j ≤ r ^ 2)
    (P : Finset (Fin n → Bool))
    (hvc : (P.image (fun a => Finset.univ.filter (fun j => a j = true))).vcDim ≤ d)
    (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      ε ^ 2 ≤ weightedHammingSq w a b) :
    P.card ≤ Nat.ceil ((16 * r ^ 2 / ε ^ 2) ^ (2 * (d + 1))) := by
  classical
  let B : ℝ := 16 * r ^ 2 / ε ^ 2
  have hr : 0 < r := hε.trans_le hεr
  have hx : 1 ≤ r ^ 2 / ε ^ 2 := by
    have hdiv : 1 ≤ r / ε := (one_le_div hε).2 hεr
    rw [← div_pow]
    nlinarith [sq_nonneg (r / ε)]
  have hB : 16 ≤ B := by
    dsimp [B]
    calc
      16 ≤ 16 * (r ^ 2 / ε ^ 2) := by nlinarith
      _ = 16 * r ^ 2 / ε ^ 2 := by ring
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hpow_one : 1 ≤ B ^ (2 * (d + 1)) := by
    exact one_le_pow₀ (by linarith)
  by_cases hsmall : P.card ≤ 1
  · apply (Nat.cast_le (α := ℝ)).mp
    have hsmall' : (P.card : ℝ) ≤ 1 := by exact_mod_cast hsmall
    exact hsmall'.trans (hpow_one.trans (Nat.le_ceil _))
  have hPcard : 2 ≤ P.card := by omega
  obtain ⟨m, J, hm, hvcJ, hinj⟩ :=
    exists_separating_subsample d w hw r ε hr hε hwsum P hPcard hvc hsep
  have hcard_image : (P.image (subsamplePattern J)).card = P.card :=
    Finset.card_image_of_injOn hinj
  have hcard_sum : P.card ≤ ∑ k ∈ Finset.Iic d, m.choose k := by
    rw [← hcard_image]
    exact card_growthFamily_le_sum_choose (P.image (subsamplePattern J)) hvcJ
  by_cases hd0 : d = 0
  · have : P.card ≤ 1 := by
      rw [hd0, show Finset.Iic 0 = {0} by ext k; simp] at hcard_sum
      simpa using hcard_sum
    omega
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have hreal_goal : (P.card : ℝ) ≤ B ^ (2 * (d + 1)) := by
    by_cases hdm : d ≤ m
    · have hcard_scaled : (P.card : ℝ) ≤ (4 * (m : ℝ) / (d : ℝ)) ^ d := by
        have hc : (P.card : ℝ) ≤
            ((∑ k ∈ Finset.Iic d, m.choose k : ℕ) : ℝ) := by exact_mod_cast hcard_sum
        exact hc.trans (sum_choose_le_four_mul_div_pow hd hdm)
      let L : ℝ := Real.log (P.card)
      have hPpos : 0 < (P.card : ℝ) := by positivity
      have hmpos : 0 < m := lt_of_lt_of_le hd hdm
      have hbase_pos : 0 < 4 * (m : ℝ) / (d : ℝ) := by positivity
      have hlog_card : L ≤ (d : ℝ) * Real.log (4 * (m : ℝ) / (d : ℝ)) := by
        calc
          L ≤ Real.log ((4 * (m : ℝ) / (d : ℝ)) ^ d) :=
            Real.log_le_log hPpos hcard_scaled
          _ = (d : ℝ) * Real.log (4 * (m : ℝ) / (d : ℝ)) := Real.log_pow _ _
      have htangent :
          Real.log (4 * (m : ℝ) / (d : ℝ)) ≤
            (4 * (m : ℝ) / (d : ℝ)) / B + Real.log B - 1 := by
        have hratio : 0 < (4 * (m : ℝ) / (d : ℝ)) / B := by positivity
        have h := Real.log_le_sub_one_of_pos hratio
        rw [Real.log_div (ne_of_gt hbase_pos) (ne_of_gt hBpos)] at h
        linarith
      have hm' : (m : ℝ) ≤ 1 + (2 * r ^ 2 / ε ^ 2) * L := by
        simpa [L] using hm
      have hratio_bound :
          (4 * (m : ℝ) / (d : ℝ)) / B ≤
            1 / (4 * (d : ℝ)) + L / (2 * (d : ℝ)) := by
        dsimp [B]
        have hdreal : 0 < (d : ℝ) := by positivity
        have hscale : 0 < 4 / ((d : ℝ) * (16 * r ^ 2 / ε ^ 2)) := by positivity
        have := mul_le_mul_of_nonneg_left hm' hscale.le
        calc
          (4 * (m : ℝ) / (d : ℝ)) / (16 * r ^ 2 / ε ^ 2) =
              (4 / ((d : ℝ) * (16 * r ^ 2 / ε ^ 2))) * (m : ℝ) := by field_simp
          _ ≤ (4 / ((d : ℝ) * (16 * r ^ 2 / ε ^ 2))) *
              (1 + (2 * r ^ 2 / ε ^ 2) * L) := this
          _ = 1 / (4 * (d : ℝ)) * (ε ^ 2 / r ^ 2) +
              L / (2 * (d : ℝ)) := by field_simp; ring
          _ ≤ 1 / (4 * (d : ℝ)) + L / (2 * (d : ℝ)) := by
            have heps : ε ^ 2 / r ^ 2 ≤ 1 := by
              rw [div_le_one (sq_pos_of_pos hr)]
              nlinarith [sq_nonneg (r - ε)]
            have hcoef : 0 ≤ 1 / (4 * (d : ℝ)) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left heps hcoef]
      have hL : L ≤ 2 * (d : ℝ) * Real.log B := by
        have hdreal : 0 < (d : ℝ) := by positivity
        have hstep := hlog_card.trans
          (mul_le_mul_of_nonneg_left htangent (by positivity : 0 ≤ (d : ℝ)))
        have hstep' :
            L ≤ (d : ℝ) *
              (1 / (4 * (d : ℝ)) + L / (2 * (d : ℝ)) + Real.log B - 1) :=
          hstep.trans (mul_le_mul_of_nonneg_left (by linarith [hratio_bound]) (by positivity))
        have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast Nat.succ_le_iff.mpr hd
        have hstep'' :
            L ≤ 1 / 4 + L / 2 + (d : ℝ) * Real.log B - (d : ℝ) := by
          convert hstep' using 1 <;> field_simp
        nlinarith
      have hlog_pow : Real.log (B ^ (2 * (d + 1))) =
          (2 * (d + 1) : ℕ) * Real.log B := Real.log_pow _ _
      have hlog_le : L ≤ Real.log (B ^ (2 * (d + 1))) := by
        rw [hlog_pow]
        have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
        exact hL.trans (by
          norm_num [Nat.cast_mul, Nat.cast_add]
          nlinarith)
      change Real.log (P.card : ℝ) ≤ Real.log (B ^ (2 * (d + 1))) at hlog_le
      rw [← Real.exp_log hPpos, ← Real.exp_log (pow_pos hBpos _)]
      exact Real.exp_le_exp.mpr hlog_le
    · have hmd : m < d := Nat.lt_of_not_ge hdm
      have hcard_univ : (P.image (subsamplePattern J)).card ≤
          (Finset.univ : Finset (Finset (Fin m))).card := Finset.card_le_univ _
      have hcard_two : P.card ≤ 2 ^ m := by
        rw [hcard_image] at hcard_univ
        simpa using hcard_univ
      have htwoB : (2 : ℝ) ≤ B := by linarith
      calc
        (P.card : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hcard_two
        _ ≤ B ^ m := pow_le_pow_left₀ (by norm_num) htwoB m
        _ ≤ B ^ (2 * (d + 1)) := by
          exact pow_le_pow_right₀ (by linarith) (by omega)
  apply (Nat.cast_le (α := ℝ)).mp
  exact hreal_goal.trans (Nat.le_ceil _)
private theorem finiteMeasure_boolean_packing_card_le
    {Ω : Type*} [MeasurableSpace Ω] [Nonempty Ω] {κ : Type*}
    (π : κ → Ω → Bool) (hπ : ∀ i, Measurable (π i))
    (d : ℕ) (hvc : ∀ (n : ℕ) (T : Fin n → Ω), (growthFamily π T).vcDim ≤ d)
    (μ : Measure Ω) (hμtop : μ Set.univ ≠ ⊤) (r ε : ℝ) (hε : 0 < ε)
    (hεr : ε ≤ r) (hμ : μ.real Set.univ ≤ r ^ 2) (C : Finset κ)
    (hsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
      ε ^ 2 ≤ μ.real {x | π a x ≠ π b x}) :
    C.card ≤ Nat.ceil ((16 * r ^ 2 / ε ^ 2) ^ (2 * (d + 1))) := by
  classical
  let atom : Ω → (C → Bool) := fun x a => π a.1 x
  have hatom : Measurable atom := by
    rw [measurable_pi_iff]; exact fun a => hπ a.1
  let ν : Measure (C → Bool) := Measure.map atom μ
  let e : (C → Bool) ≃ Fin (Fintype.card (C → Bool)) := Fintype.equivFin _
  let rep : (C → Bool) → Ω := fun p =>
    if h : Set.Nonempty (atom ⁻¹' ({p} : Set (C → Bool))) then Classical.choose h
    else Classical.choice inferInstance
  have hrep {p : C → Bool} (hp : ν {p} ≠ 0) : atom (rep p) = p := by
    have hnon : Set.Nonempty (atom ⁻¹' ({p} : Set (C → Bool))) := by
      change (Measure.map atom μ) {p} ≠ 0 at hp
      rw [Measure.map_apply hatom (measurableSet_singleton p)] at hp
      exact Set.nonempty_iff_ne_empty.mpr fun he => hp (by simp [he])
    simp only [rep, dif_pos hnon]; exact Classical.choose_spec hnon
  let T : Fin (Fintype.card (C → Bool)) → Ω := fun j => rep (e.symm j)
  let vec : κ → Fin (Fintype.card (C → Bool)) → Bool := fun a j => π a (T j)
  let P : Finset (Fin (Fintype.card (C → Bool)) → Bool) := C.image vec
  let w : Fin (Fintype.card (C → Bool)) → ℝ := fun j => ν.real {e.symm j}
  have hw : ∀ j, 0 ≤ w j := fun _ => ENNReal.toReal_nonneg
  have hatom_diff (a b : C) :
      atom ⁻¹' {p | p a ≠ p b} = {x | π a.1 x ≠ π b.1 x} := by
    ext x; rfl
  have hdist (a b : C) : weightedHammingSq w (vec a.1) (vec b.1) =
      μ.real {x | π a.1 x ≠ π b.1 x} := by
    unfold weightedHammingSq
    dsimp [w, vec, T]
    rw [← e.sum_comp (fun j =>
      if π a.1 (rep (e.symm j)) = π b.1 (rep (e.symm j)) then 0 else ν.real {e.symm j})]
    simp only [e.symm_apply_apply]
    have hterm : ∀ p : C → Bool,
        (if π a.1 (rep p) = π b.1 (rep p) then 0 else ν.real {p}) =
          if p a = p b then 0 else ν.real {p} := by
      intro p
      by_cases hp : ν {p} = 0
      · simp [Measure.real, hp]
      · have hrp := hrep hp
        have ha := congrFun hrp a
        have hb := congrFun hrp b
        dsimp [atom] at ha hb; rw [ha, hb]
    simp_rw [hterm]
    dsimp [Measure.real]
    have hνtop : ν Set.univ ≠ ⊤ := by
      change (Measure.map atom μ) Set.univ ≠ ⊤
      rw [Measure.map_apply hatom MeasurableSet.univ]; simpa using hμtop
    have hsum :
        (∑ p : C → Bool, if p a = p b then 0 else (ν {p}).toReal) =
          (ν {p | p a ≠ p b}).toReal := by
      rw [show (∑ p : C → Bool, if p a = p b then 0 else (ν {p}).toReal) =
          ∑ p ∈ Finset.univ.filter (fun p : C → Bool => p a ≠ p b),
            (ν {p}).toReal by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro p hp; by_cases h : p a = p b <;> simp [h]]
      rw [← ENNReal.toReal_sum]
      · rw [sum_measure_singleton]
        rw [show (↑(Finset.univ.filter (fun p : C → Bool => p a ≠ p b)) :
            Set (C → Bool)) = {p | p a ≠ p b} by ext p; simp]
      · intro p hp
        exact ne_top_of_le_ne_top hνtop (measure_mono (Set.subset_univ _))
    rw [hsum]; congr 1
    change (Measure.map atom μ) {p | p a ≠ p b} = μ _
    rw [Measure.map_apply hatom (Set.toFinite _).measurableSet, hatom_diff]
  have hPcard : P.card = C.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab; by_contra hab'
    have hs := hsep a ha b hb hab'
    have hd := hdist ⟨a, ha⟩ ⟨b, hb⟩
    rw [show vec a = vec b from hab] at hd
    simp [weightedHammingSq] at hd; nlinarith
  have hvcP :
      (P.image (fun a => Finset.univ.filter (fun j => a j = true))).vcDim ≤ d := by
    apply (Finset.vcDim_mono (ℬ := growthFamily π T) ?_).trans (hvc _ T)
    intro A hA
    rcases Finset.mem_image.mp hA with ⟨v, hv, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨a, ha, rfl⟩
    rw [mem_growthFamily_iff]
    exact ⟨a, by ext j; simp [vec, restrictionPattern_mem_iff]⟩
  have hwsum : ∑ j, w j ≤ r ^ 2 := by
    dsimp [w, Measure.real]
    rw [← e.sum_comp (fun j => (ν {e.symm j}).toReal)]
    simp only [e.symm_apply_apply]
    rw [← ENNReal.toReal_sum]
    · rw [sum_measure_singleton]
      have hmap : ν Set.univ = μ Set.univ := by
        change (Measure.map atom μ) Set.univ = μ Set.univ
        rw [Measure.map_apply hatom MeasurableSet.univ]; simp
      have hmap' : ν (↑(Finset.univ : Finset (C → Bool)) : Set (C → Bool)) =
          μ Set.univ := by simpa using hmap
      rw [hmap']; exact hμ
    · intro p hp
      have hνtop : ν Set.univ ≠ ⊤ := by
        change (Measure.map atom μ) Set.univ ≠ ⊤
        rw [Measure.map_apply hatom MeasurableSet.univ]; simpa using hμtop
      exact ne_top_of_le_ne_top hνtop (measure_mono (Set.subset_univ _))
  have hsepP : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ε ^ 2 ≤ weightedHammingSq w a b := by
    intro va hva vb hvb hvab
    rcases Finset.mem_image.mp hva with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hvb with ⟨b, hb, rfl⟩
    have hab : a ≠ b := fun h => hvab (by subst b; rfl)
    rw [hdist ⟨a, ha⟩ ⟨b, hb⟩]
    exact hsep a ha b hb hab
  rw [← hPcard]
  exact sharp_vc_weightedHamming_packing_card_le d w hw r ε hε hεr hwsum P hvcP hsepP
private lemma integral_abs_lower_of_l2_separated
    [MeasurableSpace 𝒳] (Q : Measure 𝒳) [IsProbabilityMeasure Q]
    (f g : 𝒳 → ℝ) (hf : Measurable f) (hg : Measurable g)
    {U ε : ℝ} (hU : 0 < U) (hε : 0 < ε) (hfU : ∀ x, |f x| ≤ U)
    (hgU : ∀ x, |g x| ≤ U)
    (hsep : ε * U ≤ measureL2Dist Q f g) :
    ε ^ 2 * (U / 2) ≤ ∫ x, |f x - g x| ∂Q := by
  have habs : Integrable (fun x => |f x - g x|) Q := by
    apply Integrable.of_bound ((hf.sub hg).abs.aestronglyMeasurable) (2 * U)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub (f x) (g x)).trans (by linarith [hfU x, hgU x])
  have hsq : Integrable (fun x => (f x - g x) ^ 2) Q := by
    apply Integrable.of_bound (((hf.sub hg).pow_const 2).aestronglyMeasurable) ((2 * U) ^ 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Pi.sub_apply]
    have hd : |f x - g x| ≤ 2 * U :=
      (abs_sub (f x) (g x)).trans (by linarith [hfU x, hgU x])
    nlinarith [sq_abs (f x - g x), abs_nonneg (f x - g x)]
  have hpoint (x : 𝒳) : (f x - g x) ^ 2 ≤ 2 * U * |f x - g x| := by
    have hd : |f x - g x| ≤ 2 * U :=
      (abs_sub (f x) (g x)).trans (by linarith [hfU x, hgU x])
    nlinarith [sq_abs (f x - g x), abs_nonneg (f x - g x)]
  have hint_le : (∫ x, (f x - g x) ^ 2 ∂Q) ≤
      2 * U * (∫ x, |f x - g x| ∂Q) := by
    rw [← integral_const_mul]; exact integral_mono hsq (habs.const_mul _) hpoint
  have hint_nonneg : 0 ≤ ∫ x, (f x - g x) ^ 2 ∂Q :=
    integral_nonneg fun x => sq_nonneg _
  have hsquare : (ε * U) ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂Q := by
    exact (Real.le_sqrt (mul_nonneg hε.le hU.le) hint_nonneg).mp hsep
  nlinarith
private theorem finite_l2_packing_card_le
    [MeasurableSpace 𝒳] (F : ι → 𝒳 → ℝ) (d : ℕ)
    (hmeas : ∀ i, Measurable (F i)) (hpdim : HasPseudoDimAtMost F d)
    {U ε : ℝ} (hU : 0 < U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (henvelope : ∀ i x, |F i x| ≤ U) (Q : Measure 𝒳) [IsProbabilityMeasure Q]
    (C : Finset ι)
    (hsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
      ε * U ≤ measureL2Dist Q (F a) (F b)) :
    C.card ≤ vcSubgraphCoverBound d ε := by
  classical
  letI : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure Q
  let strip : Set (𝒳 × ℝ) := Set.univ ×ˢ Set.Icc (-U) U
  let μ : Measure (𝒳 × ℝ) := (Q.prod volume).restrict strip
  let r : ℝ := Real.sqrt (2 * U)
  let η : ℝ := ε * Real.sqrt (U / 2)
  have hη : 0 < η := mul_pos hε (Real.sqrt_pos.2 (by positivity))
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hηr : η ≤ r := by
    have hs : Real.sqrt (U / 2) ≤ Real.sqrt (2 * U) :=
      Real.sqrt_le_sqrt (by linarith)
    calc
      η ≤ Real.sqrt (U / 2) := by dsimp [η]; nlinarith [Real.sqrt_nonneg (U / 2)]
      _ ≤ r := hs
  have hr_sq : r ^ 2 = 2 * U := by
    dsimp [r]; rw [Real.sq_sqrt (by positivity)]
  have hη_sq : η ^ 2 = ε ^ 2 * (U / 2) := by
    dsimp [η]; rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hμ_univ : μ Set.univ = ENNReal.ofReal (2 * U) := by
    rw [Measure.restrict_apply_univ]
    dsimp [μ, strip]
    rw [Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc]
    congr 1; ring
  have hμtop : μ Set.univ ≠ ⊤ := by rw [hμ_univ]; exact ENNReal.ofReal_ne_top
  have hμreal : μ.real Set.univ ≤ r ^ 2 := by
    change (μ Set.univ).toReal ≤ r ^ 2
    rw [hμ_univ, ENNReal.toReal_ofReal (by positivity), hr_sq]
  have hclassifier : ∀ i, Measurable (subgraphClassifier F i) := by
    intro i; apply measurable_to_bool
    change MeasurableSet {z : 𝒳 × ℝ | decide (z.2 < F i z.1) = true}
    simp only [decide_eq_true_eq]
    exact measurableSet_lt measurable_snd ((hmeas i).comp measurable_fst)
  have hboolsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
      η ^ 2 ≤ μ.real {z | subgraphClassifier F a z ≠ subgraphClassifier F b z} := by
    intro a ha b hb hab
    let D : Set (𝒳 × ℝ) := {z | subgraphClassifier F a z ≠ subgraphClassifier F b z}
    have hD : D = symmDiff {z : 𝒳 × ℝ | z.2 < F a z.1}
        {z : 𝒳 × ℝ | z.2 < F b z.1} := by
      ext z; simp only [D, subgraphClassifier, Set.symmDiff_def, Set.mem_union,
        Set.mem_diff, Set.mem_setOf_eq]
      by_cases ha' : z.2 < F a z.1 <;> by_cases hb' : z.2 < F b z.1 <;>
        simp [ha', hb']
    have hDstrip : D ⊆ strip := by
      intro z hz
      have hne : decide (z.2 < F a z.1) ≠ decide (z.2 < F b z.1) := hz
      have hcases : (z.2 < F a z.1 ∧ ¬z.2 < F b z.1) ∨
          (z.2 < F b z.1 ∧ ¬z.2 < F a z.1) := by
        by_cases ha' : z.2 < F a z.1 <;> by_cases hb' : z.2 < F b z.1 <;>
          simp_all
      change z.1 ∈ Set.univ ∧ z.2 ∈ Set.Icc (-U) U
      refine ⟨Set.mem_univ _, ?_⟩
      rcases hcases with hcases | hcases
      · exact ⟨by linarith [neg_le_of_abs_le (henvelope b z.1)],
          by linarith [le_of_abs_le (henvelope a z.1)]⟩
      · exact ⟨by linarith [neg_le_of_abs_le (henvelope a z.1)],
          by linarith [le_of_abs_le (henvelope b z.1)]⟩
    have habs : Integrable (fun x => |F a x - F b x|) Q := by
      apply Integrable.of_bound (((hmeas a).sub (hmeas b)).abs.aestronglyMeasurable) (2 * U)
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_abs]
      exact (abs_sub (F a x) (F b x)).trans
        (by linarith [henvelope a x, henvelope b x])
    have hmass : μ.real D = ∫ x, |F a x - F b x| ∂Q := by
      have hprod := prod_subgraph_symmDiff Q (F a) (F b) (hmeas a) (hmeas b)
      rw [← hD] at hprod
      change (μ D).toReal = _
      rw [Measure.restrict_eq_self (Q.prod volume) hDstrip, hprod]
      rw [← ofReal_integral_eq_lintegral_ofReal habs
        (Filter.Eventually.of_forall fun x => abs_nonneg _)]
      exact ENNReal.toReal_ofReal (integral_nonneg fun x => abs_nonneg _)
    rw [hη_sq, hmass]
    exact integral_abs_lower_of_l2_separated Q (F a) (F b) (hmeas a) (hmeas b)
      hU hε (henvelope a) (henvelope b) (hsep a ha b hb hab)
  have hcard := finiteMeasure_boolean_packing_card_le
    (subgraphClassifier F) hclassifier d hpdim μ hμtop r η hη hηr hμreal C hboolsep
  have hratio : 16 * r ^ 2 / η ^ 2 = 64 / ε ^ 2 := by
    rw [hr_sq, hη_sq]; field_simp; ring
  rw [hratio] at hcard
  apply hcard.trans
  apply Nat.ceil_mono
  let k : ℕ := 2 * (d + 1)
  have hbase : 64 / ε ^ 2 ≤ (16 / ε) ^ 4 := by
    have hεpos : 0 < ε ^ 2 := sq_pos_of_pos hε
    rw [div_le_iff₀ hεpos]; field_simp
    nlinarith [sq_nonneg ε, mul_self_le_mul_self (by linarith : 0 ≤ ε) hε1]
  calc
    (64 / ε ^ 2) ^ (2 * (d + 1)) = (64 / ε ^ 2) ^ k := rfl
    _ ≤ ((16 / ε) ^ 4) ^ k := pow_le_pow_left₀ (by positivity) hbase k
    _ = (16 / ε) ^ (8 * (d + 1)) := by rw [← pow_mul]; congr 1; dsimp [k]; omega
/-- **Polynomial `L²(Q)` covering number from a pseudo-dimension bound.** For [a family of
measurable real-valued functions](hyp:hmeas) of [pseudo-dimension at most d](hyp:hpdim), [uniformly
bounded by a positive envelope U](hyp:hU,henvelope), and [a relative radius ε strictly between 0
and 1](hyp:hε,hε1), [the `L²(Q)` covering number at radius ε·U is at most `vcSubgraphCoverBound d
ε`, uniformly over every probability measure Q on the domain](goal). -/
theorem real_vcSubgraph_l2_covering
    [MeasurableSpace 𝒳] [Nonempty ι] (F : ι → 𝒳 → ℝ) (d : ℕ)
    (hmeas : ∀ i, Measurable (F i)) (hpdim : HasPseudoDimAtMost F d)
    {U ε : ℝ} (hU : 0 < U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (henvelope : ∀ i x, |F i x| ≤ U)
    (Q : Measure 𝒳) [IsProbabilityMeasure Q] :
    L2CoveringNumberLe Q F (ε * U) (vcSubgraphCoverBound d ε) := by
  classical
  let R : ι → ι → Prop := fun i j => ε * U ≤ measureL2Dist Q (F i) (F j)
  let good : Set (Set ι) := {S | S.Pairwise R}
  have hdist_symm (i j : ι) :
      measureL2Dist Q (F i) (F j) = measureL2Dist Q (F j) (F i) := by
    unfold measureL2Dist; congr 2 with x <;> ring
  have hchar : Order.IsOfFiniteCharacter good := by
    intro S; constructor
    · intro h T hTS hT
      exact h.mono hTS
    · intro h a ha b hb hab
      have hsub : ({a, b} : Set ι) ⊆ S := by
        intro x hx
        rcases hx with (rfl | hx)
        · exact ha
        · have : x = b := by simpa using hx
          simpa [this] using hb
      have hfin : ({a, b} : Set ι).Finite := (Set.finite_singleton b).insert a
      exact h ({a, b} : Set ι) hsub hfin (by simp) (by simp) hab
  obtain ⟨M, -, hmax⟩ := hchar.exists_maximal (x := ∅) (by simp [good])
  have hMgood : M.Pairwise R := hmax.prop
  have hMfinite : M.Finite := by
    by_contra hfin
    have hMinfinite : M.Infinite := hfin
    obtain ⟨C, hCM, hCcard⟩ :=
      hMinfinite.exists_subset_card_eq (vcSubgraphCoverBound d ε + 1)
    have hCsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
        ε * U ≤ measureL2Dist Q (F a) (F b) := by
      intro a ha b hb hab; exact hMgood (hCM ha) (hCM hb) hab
    have hbound := finite_l2_packing_card_le F d hmeas hpdim hU hε hε1
      henvelope Q C hCsep
    omega
  let C : Finset ι := hMfinite.toFinset
  refine ⟨C, ?_, ?_⟩
  · apply finite_l2_packing_card_le F d hmeas hpdim hU hε hε1 henvelope Q
    intro a ha b hb hab; exact hMgood (by simpa [C] using ha) (by simpa [C] using hb) hab
  · intro i
    by_cases hi : i ∈ M
    · refine ⟨i, by simpa [C] using hi, ?_⟩
      simp [measureL2Dist, mul_pos hε hU]
    · by_contra hclose
      push_neg at hclose
      have hinsert : (insert i M).Pairwise R := by
        apply hMgood.insert; intro j hj hij
        have hij' : ε * U ≤ measureL2Dist Q (F i) (F j) :=
          hclose j (by simpa [C] using hj)
        refine ⟨hij', ?_⟩
        change ε * U ≤ measureL2Dist Q (F j) (F i)
        rw [hdist_symm]; exact hij'
      have heq : M = insert i M := hmax.eq_of_le hinsert (Set.subset_insert i M)
      apply hi; rw [heq]; exact Set.mem_insert i M
/-- The real-valued theorem genuinely reuses the existing finite VC
combinatorics: its hypothesis gives the exact threshold-trace certificate
needed by `VCCovering` and `HausslerPacking`. -/
theorem pseudoDim_gives_finite_subgraph_vc
    {F : ι → 𝒳 → ℝ} {d n : ℕ} (hpdim : HasPseudoDimAtMost F d) (T : Fin n → 𝒳 × ℝ) :
    (growthFamily (subgraphClassifier F) T).vcDim ≤ d := by
  exact hpdim n T
end Causalean.Stat.Concentration
