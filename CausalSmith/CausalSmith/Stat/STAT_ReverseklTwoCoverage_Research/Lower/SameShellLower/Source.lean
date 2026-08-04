import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Blueprint
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.SourceChi

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def hardContext {d : ℕ} (C D : ℝ)
    (j : Fin (hardCoordinateCount d)) :
    Fin (hardContextCard d C D) :=
  hardContextEquiv d C D (Sum.inl j)

lemma hardContext_injective {d : ℕ} (C D : ℝ) :
    Function.Injective (hardContext (d := d) C D) := by
  intro i j hij
  exact Sum.inl.inj ((hardContextEquiv d C D).injective hij)

noncomputable def hardSourcePMF
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    PMF (Fin (hardContextCard d C D) × (Fin 3 × Bool)) :=
  ibBernoulliPMF
    (hardExperiment d hd eta C D heta hD hDC hCexp)
    (hardRho (d := d) (C := C) (D := D) (eta := eta))
    (fun x a => ∑ i,
      (hardExperiment d hd eta C D heta hD hDC hCexp).feature x a i *
        hardTheta hd D eta gamma v i)
    (hardRho_nonneg hd heta hD hDC hCexp)
    (hardRho_sum hd heta hD hDC hCexp)
    (hard_linear_bounds hd v hgamma0 hgammaBeta hgammaOne)

noncomputable def hardSourceMeasure
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    Measure (Fin (hardContextCard d C D) × (Fin 3 × Bool)) :=
  (hardSourcePMF hd eta C D gamma heta hD hDC hCexp v
    hgamma0 hgammaBeta hgammaOne).toMeasure

instance hardSourceMeasure_isProbability
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    IsProbabilityMeasure
      (hardSourceMeasure hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne) := by
  unfold hardSourceMeasure
  infer_instance

lemma hardLaw_dataMeasure_eq_map_source
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    (hardLaw hd eta C D gamma heta hD hDC hCexp v
      hgamma0 hgammaBeta hgammaOne).dataMeasure =
      Measure.map ibObservation
        (hardSourceMeasure hd eta C D gamma heta hD hDC hCexp v
          hgamma0 hgammaBeta hgammaOne) := by
  rfl

lemma hardSourcePMF_toReal
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (x : Fin (hardContextCard d C D)) (a : Fin 3) (b : Bool) :
    (hardSourcePMF hd eta C D gamma heta hD hDC hCexp v
      hgamma0 hgammaBeta hgammaOne (x, (a, b))).toReal =
      hardRho (d := d) (C := C) (D := D) (eta := eta) x *
        (hardExperiment d hd eta C D heta hD hDC hCexp).reference x a *
        (if b then
          ∑ i, (hardExperiment d hd eta C D heta hD hDC hCexp).feature x a i *
            hardTheta hd D eta gamma v i
        else 1 -
          ∑ i, (hardExperiment d hd eta C D heta hD hDC hCexp).feature x a i *
            hardTheta hd D eta gamma v i) := by
  rw [hardSourcePMF, ibBernoulliPMF_apply]
  apply ENNReal.toReal_ofReal
  have hr := hard_linear_bounds hd v hgamma0 hgammaBeta hgammaOne x a
  have hr' :
      (∑ i, (hardExperiment d hd eta C D heta hD hDC hCexp).feature x a i *
        hardTheta hd D eta gamma v i) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [hardExperiment] using hr
  have href :
      0 ≤ (hardExperiment d hd eta C D heta hD hDC hCexp).reference x a :=
    let hpol :=
      (hardExperiment d hd eta C D heta hD hDC hCexp).reference_isPolicy
    hpol.1 x a
  exact mul_nonneg
    (mul_nonneg (hardRho_nonneg hd heta hD hDC hCexp x) href)
    (by split_ifs <;> linarith [hr'.1, hr'.2])

lemma hard_score_flip_eq_off_cell
    {d : ℕ} (hd : 4 ≤ d) (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d))
    (x : Fin (hardContextCard d C D)) (a : Fin 3)
    (hoff : x ≠ hardContext C D j ∨ a = hardZero) :
    (∑ i, (hardExperiment d hd eta C D heta hD hDC hCexp).feature x a i *
      hardTheta hd D eta gamma v i) =
    ∑ i, (hardExperiment d hd eta C D heta hD hDC hCexp).feature x a i *
      hardTheta hd D eta gamma (Causalean.Stat.flipBit j v) i := by
  change
    (∑ i, hardFeatureOnContext hd ((hardContextEquiv d C D).symm x) a i *
      hardTheta hd D eta gamma v i) =
    ∑ i, hardFeatureOnContext hd ((hardContextEquiv d C D).symm x) a i *
      hardTheta hd D eta gamma (Causalean.Stat.flipBit j v) i
  rw [hard_score_on_context hd, hard_score_on_context hd]
  generalize hy : (hardContextEquiv d C D).symm x = y
  rcases y with l | (hcal | (hanchor | hz))
  · by_cases hlj : l = j
    · subst l
      rcases hoff with hx | ha
      · apply (hx ?_).elim
        calc
          x = hardContextEquiv d C D ((hardContextEquiv d C D).symm x) :=
            ((hardContextEquiv d C D).apply_symm_apply x).symm
          _ = hardContextEquiv d C D (Sum.inl j) := by rw [hy]
          _ = hardContext C D j := rfl
      · simp [ha, hardZero, hardPlus, hardMinus]
    · simp [Causalean.Stat.flipBit, hlj]
  · rfl
  · rfl
  · rfl

lemma hardSourcePMF_toReal_off_cell
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (j : Fin (hardCoordinateCount d))
    (x : Fin (hardContextCard d C D)) (a : Fin 3) (b : Bool)
    (hoff : x ≠ hardContext C D j ∨ a = hardZero) :
    (hardSourcePMF hd eta C D gamma heta hD hDC hCexp v
      hgamma0 hgammaBeta hgammaOne (x, (a, b))).toReal =
    (hardSourcePMF hd eta C D gamma heta hD hDC hCexp
      (Causalean.Stat.flipBit j v)
      hgamma0 hgammaBeta hgammaOne (x, (a, b))).toReal := by
  rw [hardSourcePMF_toReal, hardSourcePMF_toReal]
  rw [hard_score_flip_eq_off_cell hd eta C D gamma heta hD hDC hCexp
    v j x a hoff]

lemma hardSourcePMF_toReal_cell
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (j : Fin (hardCoordinateCount d)) (a : Fin 3) (b : Bool)
    (ha : a = hardPlus ∨ a = hardMinus) :
    (hardSourcePMF hd eta C D gamma heta hD hDC hCexp v
      hgamma0 hgammaBeta hgammaOne (hardContext C D j, (a, b))).toReal =
      ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) * hardP D *
        (if b then
          if a = hardPlus then
            hardBeta D eta gamma + gamma * (if v j then 1 else -1)
          else hardBeta D eta gamma - gamma * (if v j then 1 else -1)
        else 1 -
          (if a = hardPlus then
            hardBeta D eta gamma + gamma * (if v j then 1 else -1)
          else hardBeta D eta gamma - gamma * (if v j then 1 else -1))) := by
  rw [hardSourcePMF_toReal]
  change
    (hardContextRawMass (eta := eta)
        ((hardContextEquiv d C D).symm (hardContext C D j)) /
        hardTotal d C D eta) *
      hardReferenceOnContext
          ((hardContextEquiv d C D).symm (hardContext C D j)) a *
      (if b then
        ∑ i, hardFeatureOnContext hd
          ((hardContextEquiv d C D).symm (hardContext C D j)) a i *
            hardTheta hd D eta gamma v i
      else 1 -
        ∑ i, hardFeatureOnContext hd
          ((hardContextEquiv d C D).symm (hardContext C D j)) a i *
            hardTheta hd D eta gamma v i) = _
  rw [hard_score_on_context hd]
  simp only [hardContext, Equiv.symm_apply_apply, hardContextRawMass,
    hardReferenceOnContext]
  rcases ha with rfl | rfl
  · simp [hardPlus, hardMinus]
  · simp [hardPlus, hardMinus]

lemma hard_selected_mean_mem_Ioo
    {d : ℕ} {D eta gamma : ℝ}
    (v : Fin (hardCoordinateCount d) → Bool)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (j : Fin (hardCoordinateCount d)) (sgn : Bool) :
    hardBeta D eta gamma +
        gamma * (if sgn = v j then 1 else -1) ∈ Set.Ioo (0 : ℝ) 1 := by
  by_cases h : sgn = v j <;> simp [h] <;> constructor <;> nlinarith

lemma hardSource_neighbor_ac
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (j : Fin (hardCoordinateCount d)) :
    hardSourceMeasure hd eta C D gamma heta hD hDC hCexp v
        hgamma0 (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith)) ≪
      hardSourceMeasure hd eta C D gamma heta hD hDC hCexp
        (Causalean.Stat.flipBit j v)
        hgamma0 (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith)) := by
  let hgb : gamma ≤ hardBeta D eta gamma :=
    hgammaBeta.trans (by linarith)
  let hgo : gamma ≤ 1 - hardBeta D eta gamma :=
    hgammaOne.trans (by linarith)
  apply pmf_toMeasure_absolutelyContinuous_of_support
  rintro ⟨x, a, b⟩ hp
  change hardSourcePMF hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgb hgo (x, a, b) ≠ 0
  by_cases hc :
      x = hardContext C D j ∧ (a = hardPlus ∨ a = hardMinus)
  · rcases hc with ⟨rfl, ha⟩
    intro hzero
    have hmean :
        (if a = hardPlus then
            hardBeta D eta gamma +
              gamma *
                (if Causalean.Stat.flipBit j v j then 1 else -1)
          else
            hardBeta D eta gamma -
              gamma *
                (if Causalean.Stat.flipBit j v j then 1 else -1))
          ∈ Set.Ioo (0 : ℝ) 1 := by
      rcases ha with rfl | rfl <;> cases hv : v j <;>
        simp [hardPlus, hardMinus, Causalean.Stat.flipBit_self, hv] <;>
        constructor <;> nlinarith
    have hrealpos : 0 <
        (hardSourcePMF hd eta C D gamma heta hD hDC hCexp
          (Causalean.Stat.flipBit j v) hgamma0 hgb hgo
          (hardContext C D j, a, b)).toReal := by
      rw [hardSourcePMF_toReal_cell hd eta C D gamma heta hD hDC
        hCexp (Causalean.Stat.flipBit j v) hgamma0 hgb hgo j a b ha]
      have hk := hardCoordinateCount_pos hd
      have hH := hardTotal_pos (d := d) heta hD hDC hCexp
      have hpD := hardP_pos hD
      cases b
      · exact mul_pos (mul_pos
          (div_pos (inv_pos.mpr (Nat.cast_pos.mpr hk)) hH) hpD)
          (sub_pos.mpr hmean.2)
      · exact mul_pos (mul_pos
          (div_pos (inv_pos.mpr (Nat.cast_pos.mpr hk)) hH) hpD)
          hmean.1
    rw [hzero, ENNReal.toReal_zero] at hrealpos
    exact (lt_irrefl 0) hrealpos
  · have hoff : x ≠ hardContext C D j ∨ a = hardZero := by
      by_cases hx : x = hardContext C D j
      · right
        have hnot : ¬(a = hardPlus ∨ a = hardMinus) := by
          intro ha
          exact hc ⟨hx, ha⟩
        fin_cases a <;> simp [hardPlus, hardMinus, hardZero] at hnot ⊢
      · exact Or.inl hx
    intro hq
    have hqr :
        (hardSourcePMF hd eta C D gamma heta hD hDC hCexp
          (Causalean.Stat.flipBit j v) hgamma0 hgb hgo
          (x, a, b)).toReal = 0 := by
      rw [hq, ENNReal.toReal_zero]
    have hpr :
        (hardSourcePMF hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgb hgo (x, a, b)).toReal = 0 := by
      rw [hardSourcePMF_toReal_off_cell hd eta C D gamma heta hD hDC
        hCexp v hgamma0 hgb hgo j x a b hoff, hqr]
    rcases (ENNReal.toReal_eq_zero_iff _).mp hpr with hpzero | hptop
    · exact hp hpzero
    · exact (hardSourcePMF hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgb hgo).apply_ne_top (x, a, b) hptop

lemma weighted_hard_bernoulli_atom_chi_bound
    {w base gamma r q : ℝ}
    (hw : 0 < w) (hbase : 0 < base) (hq : 0 < q)
    (hqhalf : base / 2 ≤ q)
    (hdiff : (r - q) ^ 2 = (2 * gamma) ^ 2) :
    ((w * r - w * q) ^ 2) / (w * q) ≤
      8 * w * gamma ^ 2 / base := by
  have hscale :
      ((w * r - w * q) ^ 2) / (w * q) =
        w * ((r - q) ^ 2 / q) := by
    field_simp [hw.ne', hq.ne']
  rw [hscale, hdiff]
  calc
    w * ((2 * gamma) ^ 2 / q) ≤
        w * ((2 * gamma) ^ 2 / (base / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg (2 * gamma))
          (by positivity) hqhalf) hw.le
    _ = 8 * w * gamma ^ 2 / base := by
      field_simp [hbase.ne']
      ring

set_option maxHeartbeats 800000 in
lemma hardSource_neighbor_chiSq_bound
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (j : Fin (hardCoordinateCount d)) :
    Causalean.Stat.chiSqDiv
      (hardSourceMeasure hd eta C D gamma heta hD hDC hCexp v
        hgamma0 (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith)))
      (hardSourceMeasure hd eta C D gamma heta hD hDC hCexp
        (Causalean.Stat.flipBit j v)
        hgamma0 (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith))) ≤
      16 *
        (((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) * hardP D) *
        gamma ^ 2 *
        (1 / hardBeta D eta gamma +
          1 / (1 - hardBeta D eta gamma)) := by
  let hgb : gamma ≤ hardBeta D eta gamma :=
    hgammaBeta.trans (by linarith)
  let hgo : gamma ≤ 1 - hardBeta D eta gamma :=
    hgammaOne.trans (by linarith)
  let p := hardSourcePMF hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgb hgo
  let q := hardSourcePMF hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgb hgo
  have hac : p.toMeasure ≪ q.toMeasure :=
    hardSource_neighbor_ac hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hbeta hbeta1 hgammaBeta hgammaOne j
  rw [show hardSourceMeasure hd eta C D gamma heta hD hDC hCexp v
      hgamma0 hgb hgo = p.toMeasure by rfl,
    show hardSourceMeasure hd eta C D gamma heta hD hDC hCexp
      (Causalean.Stat.flipBit j v) hgamma0 hgb hgo = q.toMeasure by rfl,
    pmf_chiSqDiv_eq_sum p q hac]
  let w :=
    ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) * hardP D
  have hw : 0 < w := mul_pos
    (div_pos (inv_pos.mpr (Nat.cast_pos.mpr (hardCoordinateCount_pos hd)))
      (hardTotal_pos (d := d) heta hD hDC hCexp))
    (hardP_pos hD)
  have hb0 : 0 < hardBeta D eta gamma := hbeta
  have hb1 : hardBeta D eta gamma < 1 := hbeta1
  have hatom : ∀ z : Fin (hardContextCard d C D) × (Fin 3 × Bool),
      ((p z).toReal - (q z).toReal) ^ 2 / (q z).toReal ≤
        if z.1 = hardContext C D j ∧
            (z.2.1 = hardPlus ∨ z.2.1 = hardMinus) then
          if z.2.2 then
            8 * w * gamma ^ 2 / hardBeta D eta gamma
          else 8 * w * gamma ^ 2 / (1 - hardBeta D eta gamma)
        else 0 := by
    rintro ⟨x, a, b⟩
    by_cases hc :
        x = hardContext C D j ∧ (a = hardPlus ∨ a = hardMinus)
    · rcases hc with ⟨rfl, ha⟩
      rw [if_pos ⟨rfl, ha⟩]
      change
        (((p (hardContext C D j, a, b)).toReal -
          (q (hardContext C D j, a, b)).toReal) ^ 2 /
          (q (hardContext C D j, a, b)).toReal) ≤ _
      dsimp [p, q]
      rw [hardSourcePMF_toReal_cell hd eta C D gamma heta hD hDC
        hCexp v hgamma0 hgb hgo j a b ha,
        hardSourcePMF_toReal_cell hd eta C D gamma heta hD hDC
        hCexp (Causalean.Stat.flipBit j v) hgamma0 hgb hgo j a b ha]
      change ((w * _ - w * _) ^ 2) / (w * _) ≤ _
      cases hv : v j <;> rcases ha with rfl | rfl <;> cases b
      all_goals
        first
        | apply weighted_hard_bernoulli_atom_chi_bound hw
            (sub_pos.mpr hb1) <;>
            simp [hardPlus, hardMinus, Causalean.Stat.flipBit_self, hv] <;>
            nlinarith [hgammaOne]
        | apply weighted_hard_bernoulli_atom_chi_bound hw hb0 <;>
            simp [hardPlus, hardMinus, Causalean.Stat.flipBit_self, hv] <;>
            nlinarith [hgammaBeta]
    · rw [if_neg hc]
      have hoff : x ≠ hardContext C D j ∨ a = hardZero := by
        by_cases hx : x = hardContext C D j
        · right
          have hn : ¬(a = hardPlus ∨ a = hardMinus) := by
            intro ha
            exact hc ⟨hx, ha⟩
          fin_cases a <;> simp [hardPlus, hardMinus, hardZero] at hn ⊢
        · exact Or.inl hx
      have heq : (p (x, a, b)).toReal = (q (x, a, b)).toReal := by
        exact hardSourcePMF_toReal_off_cell hd eta C D gamma heta hD hDC
          hCexp v hgamma0 hgb hgo j x a b hoff
      rw [heq, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
  have hactionSum (t f : ℝ) :
      (∑ a : Fin 3, ∑ b : Bool,
        if a = hardPlus ∨ a = hardMinus then
          if b then t else f
        else 0) = 2 * (t + f) := by
    rw [Fin.sum_univ_three]
    simp [Fintype.sum_bool, hardPlus, hardMinus]
    ring
  calc
    (∑ z, ((p z).toReal - (q z).toReal) ^ 2 / (q z).toReal) ≤
        ∑ z, if z.1 = hardContext C D j ∧
            (z.2.1 = hardPlus ∨ z.2.1 = hardMinus) then
          if z.2.2 then
            8 * w * gamma ^ 2 / hardBeta D eta gamma
          else 8 * w * gamma ^ 2 / (1 - hardBeta D eta gamma)
        else 0 := Finset.sum_le_sum fun z _ => hatom z
    _ = 16 * w * gamma ^ 2 *
        (1 / hardBeta D eta gamma +
          1 / (1 - hardBeta D eta gamma)) := by
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (hardContext C D j)]
      · simp only [true_and]
        rw [hactionSum]
        ring
      · intro x _ hx
        simp [hx]
      · simp
    _ = _ := by rfl

end

end CausalSmith.Stat.ReverseKLTwoCoverage
