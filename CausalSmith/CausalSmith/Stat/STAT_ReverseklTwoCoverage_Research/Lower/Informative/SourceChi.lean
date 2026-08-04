import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.DecoderRisk
import Causalean.Stat.Minimax.ChiSquaredFinite
import CausalSmith.Mathlib.InformationTheory.ProductChiSquared

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

noncomputable def informativeSourcePMF
    (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    PMF (Fin (d + 1) × (Fin 2 × Bool)) :=
  ibBernoulliPMF
    (informativeExperiment d hd eta C D heta
      (lt_of_lt_of_le hD hDC) hCexp)
    (informativeRho eta C D)
    (fun x a => ∑ i,
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
      informativeTheta (by omega) eta D gamma v i)
    (fun x => (informativeRho_pos hd heta hD hDC hCexp x).le)
    (informativeRho_sum hd heta hD hDC hCexp)
    (informative_linear_bounds (d := d) hd heta hD hDC hCexp
      v hgamma0 hgamma)

noncomputable def informativeSourceMeasure
    (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    Measure (Fin (d + 1) × (Fin 2 × Bool)) :=
  (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgamma).toMeasure

instance informativeSourceMeasure_isProbability
    (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    IsProbabilityMeasure
      (informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgamma) := by
  unfold informativeSourceMeasure
  infer_instance

lemma informativeLaw_dataMeasure_eq_map_source
    (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    (informativeLaw d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma).dataMeasure =
      Measure.map ibObservation
        (informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma) := by
  rfl

lemma pmf_toMeasure_absolutelyContinuous_of_support
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (p q : PMF Ω) (hsub : p.support ⊆ q.support) :
    p.toMeasure ≪ q.toMeasure := by
  intro s hs
  rw [q.toMeasure_apply_eq_zero_iff
    (Set.toFinite s).measurableSet] at hs
  rw [p.toMeasure_apply_eq_zero_iff
    (Set.toFinite s).measurableSet]
  exact hs.mono_left hsub

lemma pmf_chiSqDiv_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype Ω] (p q : PMF Ω) (hac : p.toMeasure ≪ q.toMeasure) :
    Causalean.Stat.chiSqDiv p.toMeasure q.toMeasure =
      ∑ x, ((p x).toReal - (q x).toReal) ^ 2 / (q x).toReal := by
  have hp_sum : ∑ x, (p x).toReal = 1 := by
    have h := congrArg ENNReal.toReal p.tsum_coe
    rw [tsum_fintype, ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)] at h
    simpa using h
  have hq_sum : ∑ x, (q x).toReal = 1 := by
    have h := congrArg ENNReal.toReal q.tsum_coe
    rw [tsum_fintype, ENNReal.toReal_sum (fun a _ => q.apply_ne_top a)] at h
    simpa using h
  have hfinite :
      1 + Causalean.Stat.chiSqDiv p.toMeasure q.toMeasure =
        ∑ x, ((p x).toReal) ^ 2 / (q x).toReal := by
    rw [Causalean.Stat.finite_one_add_chiSqDiv
      p.toMeasure q.toMeasure hac]
    apply Finset.sum_congr rfl
    intro x _
    simp only [measureReal_def,
      PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]
  have hterm : ∀ x,
      ((p x).toReal) ^ 2 / (q x).toReal =
        2 * (p x).toReal - (q x).toReal +
          ((p x).toReal - (q x).toReal) ^ 2 / (q x).toReal := by
    intro x
    by_cases hq : q x = 0
    · have hp : p x = 0 := by
        by_contra hpne
        have hqzero : q.toMeasure {x} = 0 := by
          rw [PMF.toMeasure_apply_singleton _ _
            (MeasurableSet.singleton x)]
          exact hq
        have hpzero := hac hqzero
        rw [PMF.toMeasure_apply_singleton _ _
          (MeasurableSet.singleton x)] at hpzero
        exact hpne hpzero
      simp [hq, hp]
    · have hqr : (q x).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨hq, q.apply_ne_top x⟩
      field_simp [hqr]
      ring
  have hsumterm :
      (∑ x, ((p x).toReal) ^ 2 / (q x).toReal) =
        ∑ x, (2 * (p x).toReal - (q x).toReal +
          ((p x).toReal - (q x).toReal) ^ 2 / (q x).toReal) := by
    apply Finset.sum_congr rfl
    intro x _
    exact hterm x
  calc
    Causalean.Stat.chiSqDiv p.toMeasure q.toMeasure =
        (1 + Causalean.Stat.chiSqDiv p.toMeasure q.toMeasure) - 1 := by ring
    _ =
        (∑ x, ((p x).toReal) ^ 2 / (q x).toReal) - 1 := by rw [hfinite]
    _ = (∑ x, (2 * (p x).toReal - (q x).toReal +
        ((p x).toReal - (q x).toReal) ^ 2 / (q x).toReal)) - 1 := by
      rw [hsumterm]
    _ = ∑ x, ((p x).toReal - (q x).toReal) ^ 2 / (q x).toReal := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hp_sum, hq_sum]
      ring

lemma informativeCoordinate_bitIndex_self
    {d : ℕ} (hd : 4 ≤ d) (i : Fin d)
    (hi : i ≠ (⟨0, by omega⟩ : Fin d)) :
    informativeCoordinate hd (informativeBitIndex (by omega) i hi) = i := by
  apply Fin.ext
  change (i.val - 1) + 1 = i.val
  have hi0 : i.val ≠ 0 := by
    intro hz
    apply hi
    apply Fin.ext
    simpa using hz
  omega

lemma informativeTheta_flip_eq_of_ne
    {d : ℕ} (hd : 4 ≤ d) (eta D gamma : ℝ)
    (v : Fin (d - 1) → Bool) (j : Fin (d - 1)) (i : Fin d)
    (hne : i ≠ informativeCoordinate hd j) :
    informativeTheta (by omega) eta D gamma
        (Causalean.Stat.flipBit j v) i =
      informativeTheta (by omega) eta D gamma v i := by
  by_cases hi : i = (⟨0, by omega⟩ : Fin d)
  · subst i
    simp [informativeTheta]
  · have hk : informativeBitIndex (by omega) i hi ≠ j := by
      intro h
      apply hne
      rw [← h, informativeCoordinate_bitIndex_self hd i hi]
    rw [informativeTheta, dif_neg hi, informativeTheta, dif_neg hi]
    rw [show Causalean.Stat.flipBit j v
        (informativeBitIndex (by omega) i hi) =
        v (informativeBitIndex (by omega) i hi) by
      simp [Causalean.Stat.flipBit, hk]]

lemma informativeScore_flip_eq_of_ne
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool) (j : Fin (d - 1))
    (x : Fin (d + 1)) (a : Fin 2)
    (hne : x ≠ informativeContext hd j) :
    (∑ i, (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
      informativeTheta (by omega) eta D gamma
        (Causalean.Stat.flipBit j v) i) =
    ∑ i, (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
      informativeTheta (by omega) eta D gamma v i := by
  induction x using Fin.cases with
  | zero =>
    rw [informative_score_anchor, informative_score_anchor]
  | succ i =>
    have hine : i ≠ informativeCoordinate hd j := by
      intro hi
      apply hne
      simpa [informativeContext, hi]
    rw [informative_score_succ, informative_score_succ,
      informativeTheta_flip_eq_of_ne hd eta D gamma v j i hine]

lemma informativeScore_context_action_one
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool) (j : Fin (d - 1)) :
    (∑ i, (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).feature
          (informativeContext hd j) 1 i *
      informativeTheta (by omega) eta D gamma v i) =
      informativeBeta eta D + gamma * informativeSign (v j) := by
  rw [informativeContext, informative_score_succ,
    informativeTheta_coordinate]
  norm_num

lemma informativeSourcePMF_toReal
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (x : Fin (d + 1)) (a : Fin 2) (b : Bool) :
    (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma (x, (a, b))).toReal =
      informativeRho eta C D x *
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp).reference x a *
        (if b then
          ∑ i, (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
              informativeTheta (by omega) eta D gamma v i
        else 1 - ∑ i, (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
              informativeTheta (by omega) eta D gamma v i) := by
  rw [informativeSourcePMF, ibBernoulliPMF_apply]
  apply ENNReal.toReal_ofReal
  have hr := informative_linear_bounds (d := d) hd heta hD hDC hCexp
    v hgamma0 hgamma x a
  have href : 0 ≤
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).reference x a :=
    (informativeExperiment d hd eta C D heta
      (lt_of_lt_of_le hD hDC) hCexp).reference_isPolicy.1 x a
  exact mul_nonneg
    (mul_nonneg (informativeRho_pos hd heta hD hDC hCexp x).le
      href)
    (by split_ifs <;> linarith [hr.1, hr.2])

lemma informativeSourcePMF_toReal_off_cell
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1)) (x : Fin (d + 1)) (a : Fin 2) (b : Bool)
    (hoff : x ≠ informativeContext hd j ∨ a ≠ 1) :
    (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma (x, (a, b))).toReal =
    (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
      (Causalean.Stat.flipBit j v) hgamma0 hgamma (x, (a, b))).toReal := by
  rw [informativeSourcePMF_toReal, informativeSourcePMF_toReal]
  have hs :
      (∑ i, (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
        informativeTheta (by omega) eta D gamma v i) =
      ∑ i, (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
        informativeTheta (by omega) eta D gamma
          (Causalean.Stat.flipBit j v) i := by
    rcases hoff with hx | ha
    · exact (informativeScore_flip_eq_of_ne hd eta C D gamma heta hD hDC
        hCexp v j x a hx).symm
    · fin_cases a
      · induction x using Fin.cases with
        | zero =>
          rw [informative_score_anchor, informative_score_anchor]
        | succ i =>
          rw [informative_score_succ, informative_score_succ]
          simp
      · exact (ha rfl).elim
  rw [hs]

lemma informativeSourcePMF_toReal_cell
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1)) (b : Bool) :
    (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma (informativeContext hd j, (1, b))).toReal =
      (1 / informativeTotal d eta C D) * (1 / 2) *
        (if b then informativeBeta eta D + gamma * informativeSign (v j)
        else 1 - (informativeBeta eta D + gamma * informativeSign (v j))) := by
  rw [informativeSourcePMF_toReal,
    informativeScore_context_action_one hd eta C D gamma heta hD hDC
      hCexp v j]
  have hj0 := informativeCoordinate_ne_zero hd j
  simp only [informativeContext, informativeRho, Fin.cases_succ,
    informativeExperiment, informativeReference]
  rw [if_neg hj0]

lemma informative_selected_mean_mem_Ioo
    {d : ℕ} (hd : 4 ≤ d)
    {eta D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDexp : D < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1)) :
    informativeBeta eta D + gamma * informativeSign (v j) ∈
      Set.Ioo (0 : ℝ) 1 := by
  have hb0 := informativeBeta_pos heta hD
  have hb1 := informativeBeta_lt_one heta hD hDexp
  have hgB : gamma ≤ informativeBeta eta D / 2 :=
    le_trans hgamma (min_le_left _ _)
  have hg1 : gamma ≤ (1 - informativeBeta eta D) / 2 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  rcases informativeSign_mem (v j) with hs | hs <;> rw [hs] <;>
    constructor <;> nlinarith

lemma informativeSource_neighbor_ac
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1)) :
    informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgamma ≪
      informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
        (Causalean.Stat.flipBit j v) hgamma0 hgamma := by
  apply pmf_toMeasure_absolutelyContinuous_of_support
  rintro ⟨x, a, b⟩ hp
  change informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgamma (x, a, b) ≠ 0
  by_cases hc : x = informativeContext hd j ∧ a = 1
  · rcases hc with ⟨rfl, rfl⟩
    have hm := informative_selected_mean_mem_Ioo hd heta hD
      (lt_of_le_of_lt hDC hCexp) (Causalean.Stat.flipBit j v)
      hgamma0 hgamma j
    intro hzero
    have hrealpos : 0 <
        (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
          (Causalean.Stat.flipBit j v) hgamma0 hgamma
          (informativeContext hd j, 1, b)).toReal := by
      rw [informativeSourcePMF_toReal_cell]
      have hT := informativeTotal_pos hd heta hD hDC hCexp
      cases b
      · exact mul_pos (mul_pos (one_div_pos.mpr hT) (by norm_num))
          (sub_pos.mpr hm.2)
      · exact mul_pos (mul_pos (one_div_pos.mpr hT) (by norm_num)) hm.1
    rw [hzero, ENNReal.toReal_zero] at hrealpos
    exact (lt_irrefl 0) hrealpos
  · have hoff : x ≠ informativeContext hd j ∨ a ≠ 1 := by
      by_cases hx : x = informativeContext hd j
      · right
        intro ha
        exact hc ⟨hx, ha⟩
      · exact Or.inl hx
    intro hq
    have hqr :
        (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
          (Causalean.Stat.flipBit j v) hgamma0 hgamma (x, a, b)).toReal = 0 := by
      rw [hq, ENNReal.toReal_zero]
    have hpr :
        (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma (x, a, b)).toReal = 0 := by
      rw [informativeSourcePMF_toReal_off_cell hd eta C D gamma heta hD
        hDC hCexp v hgamma0 hgamma j x a b hoff, hqr]
    rcases (ENNReal.toReal_eq_zero_iff _).mp hpr with hpzero | hptop
    · exact hp hpzero
    · exact (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgamma).apply_ne_top (x, a, b) hptop

lemma weighted_bernoulli_atom_chi_bound
    {T base gamma r q : ℝ}
    (hT : 0 < T) (hbase : 0 < base) (hq : 0 < q)
    (hqhalf : base / 2 ≤ q)
    (hdiff : (r - q) ^ 2 = (2 * gamma) ^ 2) :
    (((1 / T) * (1 / 2) * r - (1 / T) * (1 / 2) * q) ^ 2) /
        ((1 / T) * (1 / 2) * q) ≤
      4 * gamma ^ 2 / (T * base) := by
  let w : ℝ := (1 / T) * (1 / 2)
  have hw : 0 < w := by dsimp [w]; positivity
  have hscale :
      ((w * r - w * q) ^ 2) / (w * q) =
        w * ((r - q) ^ 2 / q) := by
    field_simp [hw.ne', hq.ne']
  have hdiv :
      (2 * gamma) ^ 2 / q ≤ 8 * gamma ^ 2 / base := by
    calc
      (2 * gamma) ^ 2 / q ≤
          (2 * gamma) ^ 2 / (base / 2) :=
        div_le_div_of_nonneg_left (sq_nonneg (2 * gamma))
          (by positivity) hqhalf
      _ = 8 * gamma ^ 2 / base := by
        field_simp [hbase.ne']
        ring
  change ((w * r - w * q) ^ 2) / (w * q) ≤ _
  rw [hscale, hdiff]
  calc
    w * ((2 * gamma) ^ 2 / q) ≤
        w * (8 * gamma ^ 2 / base) :=
      mul_le_mul_of_nonneg_left hdiv hw.le
    _ = 4 * gamma ^ 2 / (T * base) := by
      dsimp [w]
      field_simp [hT.ne', hbase.ne']
      ring

lemma informativeSource_neighbor_chiSq_bound
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1)) :
    Causalean.Stat.chiSqDiv
        (informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma)
        (informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
          (Causalean.Stat.flipBit j v) hgamma0 hgamma) ≤
      4 * gamma ^ 2 / informativeTotal d eta C D *
        (1 / informativeBeta eta D + 1 / (1 - informativeBeta eta D)) := by
  let p := informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgamma
  let q := informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgamma
  have hac : p.toMeasure ≪ q.toMeasure := by
    exact informativeSource_neighbor_ac hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma j
  rw [show informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma = p.toMeasure by rfl,
    show informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
      (Causalean.Stat.flipBit j v) hgamma0 hgamma = q.toMeasure by rfl,
    pmf_chiSqDiv_eq_sum p q hac]
  have hT := informativeTotal_pos hd heta hD hDC hCexp
  have hb0 := informativeBeta_pos heta hD
  have hb1 := informativeBeta_lt_one heta hD (lt_of_le_of_lt hDC hCexp)
  have hgB : gamma ≤ informativeBeta eta D / 2 :=
    le_trans hgamma (min_le_left _ _)
  have hg1 : gamma ≤ (1 - informativeBeta eta D) / 2 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hbm_chi : 0 < informativeBeta eta D - gamma := by nlinarith
  have hbp_chi : 0 < informativeBeta eta D + gamma := by nlinarith
  have h1m_chi : 0 < 1 - (informativeBeta eta D + gamma) := by nlinarith
  have h1p_chi : 0 < 1 - (informativeBeta eta D - gamma) := by nlinarith
  have hatom : ∀ z : Fin (d + 1) × (Fin 2 × Bool),
      ((p z).toReal - (q z).toReal) ^ 2 / (q z).toReal ≤
        if z.1 = informativeContext hd j ∧ z.2.1 = 1 then
          if z.2.2 then
            4 * gamma ^ 2 /
              (informativeTotal d eta C D * informativeBeta eta D)
          else
            4 * gamma ^ 2 /
              (informativeTotal d eta C D * (1 - informativeBeta eta D))
        else 0 := by
    rintro ⟨x, a, b⟩
    by_cases hc : x = informativeContext hd j ∧ a = 1
    · rcases hc with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩]
      change
        (((informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma (informativeContext hd j, 1, b)).toReal -
          (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
            (Causalean.Stat.flipBit j v) hgamma0 hgamma
              (informativeContext hd j, 1, b)).toReal) ^ 2 /
          (informativeSourcePMF d hd eta C D gamma heta hD hDC hCexp
            (Causalean.Stat.flipBit j v) hgamma0 hgamma
              (informativeContext hd j, 1, b)).toReal) ≤ _
      rw [informativeSourcePMF_toReal_cell,
        informativeSourcePMF_toReal_cell]
      cases hv : v j <;> cases b
      · have hh := weighted_bernoulli_atom_chi_bound
          (T := informativeTotal d eta C D)
          (base := 1 - informativeBeta eta D) (gamma := gamma)
          (r := 1 - (informativeBeta eta D - gamma))
          (q := 1 - (informativeBeta eta D + gamma))
          hT (sub_pos.mpr hb1) h1m_chi (by nlinarith [hg1]) (by ring)
        simpa [Causalean.Stat.flipBit_self, hv, informativeSign] using hh
      · have hh := weighted_bernoulli_atom_chi_bound
          (T := informativeTotal d eta C D)
          (base := informativeBeta eta D) (gamma := gamma)
          (r := informativeBeta eta D - gamma)
          (q := informativeBeta eta D + gamma)
          hT hb0 hbp_chi (by nlinarith [hgB]) (by ring)
        simpa [Causalean.Stat.flipBit_self, hv, informativeSign] using hh
      · have hh := weighted_bernoulli_atom_chi_bound
          (T := informativeTotal d eta C D)
          (base := 1 - informativeBeta eta D) (gamma := gamma)
          (r := 1 - (informativeBeta eta D + gamma))
          (q := 1 - (informativeBeta eta D - gamma))
          hT (sub_pos.mpr hb1) h1p_chi (by nlinarith [hg1]) (by ring)
        simpa [Causalean.Stat.flipBit_self, hv, informativeSign] using hh
      · have hh := weighted_bernoulli_atom_chi_bound
          (T := informativeTotal d eta C D)
          (base := informativeBeta eta D) (gamma := gamma)
          (r := informativeBeta eta D + gamma)
          (q := informativeBeta eta D - gamma)
          hT hb0 hbm_chi (by nlinarith [hgB]) (by ring)
        simpa [Causalean.Stat.flipBit_self, hv, informativeSign] using hh
    · rw [if_neg hc]
      have hoff : x ≠ informativeContext hd j ∨ a ≠ 1 := by
        by_cases hx : x = informativeContext hd j
        · right
          intro ha
          exact hc ⟨hx, ha⟩
        · exact Or.inl hx
      have heq :
          (p (x, a, b)).toReal = (q (x, a, b)).toReal := by
        exact informativeSourcePMF_toReal_off_cell hd eta C D gamma heta hD
          hDC hCexp v hgamma0 hgamma j x a b hoff
      rw [heq, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_div]
  calc
    (∑ z, ((p z).toReal - (q z).toReal) ^ 2 / (q z).toReal) ≤
        ∑ z, if z.1 = informativeContext hd j ∧ z.2.1 = 1 then
          if z.2.2 then
            4 * gamma ^ 2 /
              (informativeTotal d eta C D * informativeBeta eta D)
          else
            4 * gamma ^ 2 /
              (informativeTotal d eta C D * (1 - informativeBeta eta D))
        else 0 := Finset.sum_le_sum (fun z _ => hatom z)
    _ = 4 * gamma ^ 2 /
          (informativeTotal d eta C D * informativeBeta eta D) +
        4 * gamma ^ 2 /
          (informativeTotal d eta C D * (1 - informativeBeta eta D)) := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      rw [Finset.sum_eq_single (informativeContext hd j)]
      · simp
      · intro x _ hx
        simp [hx]
      · simp
    _ = 4 * gamma ^ 2 / informativeTotal d eta C D *
        (1 / informativeBeta eta D + 1 / (1 - informativeBeta eta D)) := by
      field_simp [hT.ne', hb0.ne', (sub_pos.mpr hb1).ne']

end

end CausalSmith.Stat.ReverseKLTwoCoverage
