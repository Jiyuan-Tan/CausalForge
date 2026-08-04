import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Basis
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.BernoulliLaw

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

abbrev HardContextCarrier (d : ℕ) (C D : ℝ) :=
  Fin (hardCoordinateCount d) ⊕
    (Fin 1 ⊕ (Fin (if C > D then 1 else 0) ⊕
      Fin (if Even d then 1 else 0)))

def hardContextCard (d : ℕ) (C D : ℝ) : ℕ :=
  Fintype.card (HardContextCarrier d C D)

noncomputable def hardContextEquiv (d : ℕ) (C D : ℝ) :
    HardContextCarrier d C D ≃ Fin (hardContextCard d C D) :=
  Fintype.equivFin _

def hardContextHard {d : ℕ} {C D : ℝ}
    (j : Fin (hardCoordinateCount d)) : HardContextCarrier d C D :=
  Sum.inl j

def hardContextCalibration {d : ℕ} {C D : ℝ} :
    HardContextCarrier d C D :=
  Sum.inr (Sum.inl 0)

noncomputable def hardContextAnchor {d : ℕ} {C D : ℝ} :
    HardContextCarrier d C D := by
  classical
  by_cases h : C > D
  · exact Sum.inr (Sum.inr (Sum.inl ⟨0, by simp [h]⟩))
  · exact hardContextCalibration

noncomputable def hardContextResidual {d : ℕ} {C D : ℝ} :
    HardContextCarrier d C D := by
  classical
  by_cases h : Even d
  · exact Sum.inr (Sum.inr (Sum.inr ⟨0, by simp [h]⟩))
  · exact hardContextCalibration

def hardPlus : Fin 3 := 0
def hardMinus : Fin 3 := 1
def hardZero : Fin 3 := 2

lemma hard_actions_exactly_three :
    ExactlyThreeActions hardPlus hardMinus hardZero := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro a
  fin_cases a <;> simp [hardPlus, hardMinus, hardZero]

def hardAnchorRaw (C D eta : ℝ) : ℝ :=
  hardQ C eta * (C - D) / (D - 1)

def hardTau (C D eta : ℝ) : ℝ :=
  (4 * (1 + hardAnchorRaw C D eta))⁻¹

def hardTotal (d : ℕ) (C D eta : ℝ) : ℝ :=
  1 + hardTau C D eta +
    (if C > D then hardTau C D eta * hardAnchorRaw C D eta else 0) +
    (if Even d then 1 / 4 else 0)

def hardContextRawMass {d : ℕ} {C D eta : ℝ}
    (x : HardContextCarrier d C D) : ℝ :=
  match x with
  | Sum.inl _ => (hardCoordinateCount d : ℝ)⁻¹
  | Sum.inr (Sum.inl _) => hardTau C D eta
  | Sum.inr (Sum.inr (Sum.inl _)) =>
      hardTau C D eta * hardAnchorRaw C D eta
  | Sum.inr (Sum.inr (Sum.inr _)) => 1 / 4

def hardRho {d : ℕ} {C D eta : ℝ}
    (x : Fin (hardContextCard d C D)) : ℝ :=
  hardContextRawMass (eta := eta) (hardContextEquiv d C D |>.symm x) /
    hardTotal d C D eta

def hardFeatureOnContext {d : ℕ} (hd : 4 ≤ d) {C D : ℝ}
    (x : HardContextCarrier d C D) (a : Fin 3) (i : Fin d) : ℝ :=
  match x with
  | Sum.inl j =>
      if a = hardPlus then
        (hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2
      else if a = hardMinus then
        (hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2
      else 0
  | Sum.inr (Sum.inl _) =>
      if a = hardPlus then hardBasisE0 hd i else 0
  | Sum.inr (Sum.inr (Sum.inl _)) => hardBasisE0 hd i
  | Sum.inr (Sum.inr (Sum.inr _)) => hardBasisZ hd i

def hardReferenceOnContext {d : ℕ} {C D eta : ℝ}
    (x : HardContextCarrier d C D) (a : Fin 3) : ℝ :=
  match x with
  | Sum.inl _ =>
      if a = hardPlus then hardP D
      else if a = hardMinus then hardP D
      else 1 - 2 * hardP D
  | Sum.inr (Sum.inl _) =>
      if a = hardPlus then hardQ C eta else (1 - hardQ C eta) / 2
  | Sum.inr (Sum.inr (Sum.inl _)) => 1 / 3
  | Sum.inr (Sum.inr (Sum.inr _)) => 1 / 3

lemma hardQ_pos {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    0 < hardQ C eta := by
  exact indexQ_pos heta (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC))
    hCexp

lemma hardQ_lt_one {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C) :
    hardQ C eta < 1 := by
  have hC1 : 1 < C := lt_of_lt_of_le hD hDC
  have he : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
  unfold hardQ
  rw [div_lt_one (sub_pos.mpr he)]
  have hC0 : 0 < C := lt_trans zero_lt_one hC1
  have hdiv : Real.exp eta / C < Real.exp eta := by
    rw [div_lt_iff₀ hC0]
    nlinarith [Real.exp_pos eta]
  linarith

lemma hardP_pos {D : ℝ} (hD : 1 < D) :
    0 < hardP D := by
  unfold hardP
  positivity

lemma hardP_lt_quarter {D : ℝ} (hD : 1 < D) :
    hardP D < 1 / 4 := by
  unfold hardP
  rw [one_div]
  change (4 * D)⁻¹ < (4 : ℝ)⁻¹
  rw [inv_lt_inv₀ (by positivity) (by norm_num)]
  nlinarith

lemma hardAnchorRaw_nonneg {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    0 ≤ hardAnchorRaw C D eta := by
  unfold hardAnchorRaw
  exact div_nonneg
    (mul_nonneg (hardQ_pos heta hD hDC hCexp).le
      (sub_nonneg.mpr hDC))
    (sub_nonneg.mpr hD.le)

lemma hardTau_pos {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    0 < hardTau C D eta := by
  have hA := hardAnchorRaw_nonneg heta hD hDC hCexp
  unfold hardTau
  positivity

lemma hardTotal_pos {d : ℕ} {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    0 < hardTotal d C D eta := by
  have ht := hardTau_pos heta hD hDC hCexp
  have hA := hardAnchorRaw_nonneg heta hD hDC hCexp
  unfold hardTotal
  split_ifs <;> positivity

lemma hardCoordinateCount_pos {d : ℕ} (hd : 4 ≤ d) :
    0 < hardCoordinateCount d := by
  unfold hardCoordinateCount
  omega

def hardTheta {d : ℕ} (hd : 4 ≤ d)
    (D eta gamma : ℝ)
    (v : Fin (hardCoordinateCount d) → Bool) (i : Fin d) : ℝ :=
  match (hardBasisEquiv hd).symm i with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => Real.sqrt 2 * hardBeta D eta gamma
  | Sum.inr (Sum.inr (Sum.inl j)) =>
      Real.sqrt 2 * gamma * (if v j then 1 else -1)
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

def hardExperiment (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta) :
    CommonExperiment d (Fin (hardContextCard d C D)) (Fin 3) where
  feature x a i :=
    hardFeatureOnContext hd (hardContextEquiv d C D |>.symm x) a i
  reference x a :=
    hardReferenceOnContext (eta := eta)
      (hardContextEquiv d C D |>.symm x) a
  eta := eta
  reference_isPolicy := by
    constructor
    · intro x a
      let y := (hardContextEquiv d C D).symm x
      change 0 ≤ hardReferenceOnContext (eta := eta) y a
      rcases y with j | hrest
      · fin_cases a <;>
          simp [hardReferenceOnContext, hardPlus, hardMinus, hardZero,
            (hardP_pos hD).le, show 2 * hardP D ≤ 1 by
              nlinarith [hardP_lt_quarter hD]]
      · rcases hrest with hcal | hrest
        · have hq0 := (hardQ_pos heta hD hDC hCexp).le
          have hq1 := (hardQ_lt_one heta hD hDC).le
          fin_cases a
          · simpa [hardReferenceOnContext, hardPlus] using hq0
          · simp [hardReferenceOnContext, hardPlus]
            exact div_nonneg (sub_nonneg.mpr hq1) (by norm_num)
          · simp [hardReferenceOnContext, hardPlus]
            exact div_nonneg (sub_nonneg.mpr hq1) (by norm_num)
        · rcases hrest with hanchor | hz <;>
            norm_num [hardReferenceOnContext]
    · intro x
      let y := (hardContextEquiv d C D).symm x
      change ∑ a, hardReferenceOnContext (eta := eta) y a = 1
      rcases y with j | hrest
      · simp [Fin.sum_univ_succ, hardReferenceOnContext,
          hardPlus, hardMinus, hardZero]
        ring
      · rcases hrest with hcal | hrest
        · norm_num [Fin.sum_univ_succ, hardReferenceOnContext,
            hardPlus, hardMinus, hardZero]
          ring
        · rcases hrest with hanchor | hz <;>
            norm_num [Fin.sum_univ_succ, hardReferenceOnContext] <;> rfl
  eta_pos := heta
  dim_ge_four := hd

end

end CausalSmith.Stat.ReverseKLTwoCoverage
