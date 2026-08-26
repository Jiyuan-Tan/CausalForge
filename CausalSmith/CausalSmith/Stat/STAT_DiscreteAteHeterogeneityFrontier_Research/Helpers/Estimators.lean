/- Explicit total estimator constructions. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Basic
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCell
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ShiftedChebyshev
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.FactorialMoments
import Causalean.Stat.UStatistic.OrderM.Basic

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Set
open scoped BigOperators

/-- Clipping to a closed real interval. -/
def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

-- @node: def:collision-handle
/-- The occupancy-weighted arm-mean estimator, with every empirical ratio
indicator-totalized and with a zero fallback when no usable cell exists. -/
noncomputable def collisionEstimator {n d : ℕ} (M : ℝ)
    (sample : Fin n → Obs d) : ℝ :=
  clip (-M) M <|
    if 0 < usableTotal sample then
      (∑ k : Fin d,
        if usableCell sample k then
          (cellCount sample k : ℝ) *
            (empiricalArmMean sample true k - empiricalArmMean sample false k)
        else 0) / usableTotal sample
    else 0
  -- @realizes T_n^{col}(clipped occupancy-weighted estimator with zero fallback)

/-- Whether an index belongs to the pilot half of the sample. -/
def inPilot {n : ℕ} (i : Fin n) : Bool := decide (i.val < n / 2)

/-- Pilot occupancy of one cell. -/
def pilotCount {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) : ℕ :=
  (Finset.univ.filter fun i => inPilot i ∧ (sample i).x = k).card

/-- Size of the estimation block `I_1`. -/
def estimationBlockSize (n : ℕ) : ℕ := n - n / 2

/-- Estimation-block arm/cell count. -/
def estimationArmCount {n d : ℕ} (sample : Fin n → Obs d)
    (a : Bool) (k : Fin d) : ℕ :=
  (Finset.univ.filter fun i => !(inPilot i) ∧
    (sample i).x = k ∧ (sample i).a = a).card

/-- Estimation-block cell count. -/
def estimationCellCount {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) : ℕ :=
  estimationArmCount sample false k + estimationArmCount sample true k

/-- Estimation-block outcome sum. -/
noncomputable def estimationArmSum {n d : ℕ} (sample : Fin n → Obs d)
    (a : Bool) (k : Fin d) : ℝ :=
  ∑ i : Fin n,
    if !(inPilot i) ∧ (sample i).x = k ∧ (sample i).a = a then (sample i).y else 0

/-- Indicator-totalized estimation-block arm mean. -/
noncomputable def estimationArmMean {n d : ℕ} (sample : Fin n → Obs d)
    (a : Bool) (k : Fin d) : ℝ :=
  if 0 < estimationArmCount sample a k then
    estimationArmSum sample a k / estimationArmCount sample a k
  else 0

/-- Fixed shifted-Chebyshev coefficient from the paper. -/
noncomputable def shiftedCoefficient (K j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * 2 ^ (2 * j + 3) / (K * (K + j + 2) : ℕ) *
    Nat.choose (K + j + 2) (2 * j + 4)

/-- Ordered distinct-index falling-factorial statistic with exactly one real mark. -/
noncomputable def orderedMarkedFactorial {n d : ℕ} (M : ℝ)
    (sample : Fin n → Obs d) (k : Fin d) (a : Bool) (j : ℕ) : ℝ :=
  (estimationArmSum sample a k / M) *
      ((estimationArmCount sample a k - 1).descFactorial j : ℝ) *
      (estimationCellCount sample k - (j + 1) : ℕ) /
    (estimationBlockSize n).descFactorial (j + 2)

/-- The light-cell polynomial contribution. -/
noncomputable def lightPolynomialTerm {n d : ℕ} (M B : ℝ) (K : ℕ)
    (sample : Fin n → Obs d) (k : Fin d) : ℝ :=
  ∑ j ∈ Finset.range (K - 1),
    shiftedCoefficient K j / B ^ (j + 1) *
      (orderedMarkedFactorial M sample k true j -
        orderedMarkedFactorial M sample k false j)

/-- Calibrated constant multiplying `log(en)` in the polynomial degree. -/
noncomputable def polynomialAlpha0 : ℝ :=
  let D6 := 8 * Real.log (27 / 4)
  min 1 (min (1 / (64 * Real.log 6)) (1 / (512 * D6)))

/-- Actual shifted-Chebyshev degree used by the polynomial program. -/
noncomputable def polynomialDegree (n : ℕ) : ℕ :=
  Nat.floor (polynomialAlpha0 * logEN n)

/-- Heavy-cell empirical contribution, normalized by the outcome scale. -/
noncomputable def heavyEmpiricalTerm {n d : ℕ} (M : ℝ)
    (sample : Fin n → Obs d) (k : Fin d) : ℝ :=
  (estimationCellCount sample k : ℝ) / estimationBlockSize n *
    ((estimationArmMean sample true k - estimationArmMean sample false k) / M)

/-- The uncalibrated split-sample heavy/light signed one-mark program.  This
companion is exposed only so the polynomial-upper lemma can certify its cutoff
parameters before the public handle is formed. -/
noncomputable def rawPolyEstimator (N : ℕ) (rho : ℝ) {n d : ℕ} (M : ℝ)
    (sample : Fin n → Obs d) : ℝ :=
  if N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n then
    let K := polynomialDegree n
    let B := 4096 * logEN n / (n - n / 2 : ℕ)
    M * clip (-1) 1
      (∑ k : Fin d,
        if 256 * logEN n < pilotCount sample k then
          heavyEmpiricalTerm M sample k
        else lightPolynomialTerm M B K sample k)
  else 0

/-- Dependent calibration data for the polynomial estimator: a cutoff, a
positive active-range multiplier, and the active-branch degree certificate. -/
def PolynomialHandle :=
  {p : ℕ × ℝ //
    0 < p.2 ∧
      ∀ n d : ℕ, 0 < n → 0 < d →
        p.1 ≤ n ∧ (d : ℝ) ≤ p.2 * n * logEN n → 2 ≤ polynomialDegree n}

namespace PolynomialHandle

/-- Untagged cutoff accessor for a dependent polynomial handle. -/
def N (handle : PolynomialHandle) : ℕ := handle.1.1

/-- Untagged active-range multiplier accessor for a dependent polynomial handle. -/
def rho (handle : PolynomialHandle) : ℝ := handle.1.2

end PolynomialHandle

-- @node: def:polynomial-handle
/-- The handle-indexed pilot-split heavy/light signed one-mark estimator.  Its
body is definitionally the complete raw program, including clipping and the
exact zero fallback outside the calibrated range. -/
noncomputable def polyEstimator (handle : PolynomialHandle)
    {n d : ℕ} (M : ℝ) (sample : Fin n → Obs d) : ℝ :=
  rawPolyEstimator handle.N handle.rho M sample
  -- @realizes T_n^{poly}(lemma-calibrated heavy-light signed one-mark estimator)

-- @node: measurable_obs_design
private lemma measurable_obs_design {n d : ℕ} :
    Measurable (fun s : Fin n → Obs d => fun i => ((s i).x, (s i).a)) := by
  have hobs : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp hobs
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp hobs)
  fun_prop

-- @node: measurable_design_function
private lemma measurable_design_function {n d : ℕ} {α : Type*} [MeasurableSpace α]
    (f : (Fin n → Fin d × Bool) → α) :
    Measurable (fun s : Fin n → Obs d => f (fun i => ((s i).x, (s i).a))) :=
  (measurable_of_finite f).comp measurable_obs_design

-- @node: measurable_design_indicator
/-- Real indicators of finite-design predicates are measurable. -/
private lemma measurable_design_indicator {n d : ℕ}
    (p : (Fin n → Fin d × Bool) → Prop) [DecidablePred p] :
    Measurable (fun s : Fin n → Obs d =>
      if p (fun i => ((s i).x, (s i).a)) then (1 : ℝ) else 0) :=
  measurable_design_function fun z => if p z then (1 : ℝ) else 0

-- @node: measurable_obsY
/-- The real outcome coordinate is measurable. -/
@[fun_prop]
private lemma measurable_obsY {d : ℕ} : Measurable (fun o : Obs d => o.y) := by
  exact measurable_snd.comp (measurable_snd.comp
    (measurable_iff_comap_le.mpr le_rfl))

-- @node: measurable_pilotCount
/-- Pilot cell counts are measurable functions of the observed design. -/
private lemma measurable_pilotCount {n d : ℕ} (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => pilotCount s k) := by
  let f : (Fin n → Fin d × Bool) → ℕ := fun z =>
    (Finset.univ.filter fun i => inPilot i ∧ (z i).1 = k).card
  simpa [pilotCount, f] using measurable_design_function f

-- @node: measurable_estimationArmCount
/-- Estimation-block arm counts are measurable functions of the design. -/
private lemma measurable_estimationArmCount {n d : ℕ} (a : Bool) (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => estimationArmCount s a k) := by
  let f : (Fin n → Fin d × Bool) → ℕ := fun z =>
    (Finset.univ.filter fun i => !(inPilot i) ∧ (z i).1 = k ∧ (z i).2 = a).card
  simpa [estimationArmCount, f] using measurable_design_function f

-- @node: measurable_estimationArmSum
/-- Estimation-block outcome sums are measurable. -/
private lemma measurable_estimationArmSum {n d : ℕ} (a : Bool) (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => estimationArmSum s a k) := by
  unfold estimationArmSum
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · simpa using (measurable_design_function (fun z =>
      !(inPilot i) ∧ (z i).1 = k ∧ (z i).2 = a))
  · exact measurable_obsY.comp (measurable_pi_apply i)
  · exact measurable_const

-- @node: measurable_estimationArmMean
/-- Indicator-totalized estimation-block arm means are measurable. -/
private lemma measurable_estimationArmMean {n d : ℕ} (a : Bool) (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => estimationArmMean s a k) := by
  unfold estimationArmMean
  apply Measurable.ite
  · exact measurable_estimationArmCount a k measurableSet_Ioi
  · exact (measurable_estimationArmSum a k).div
      ((measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
        (measurable_estimationArmCount a k))
  · exact measurable_const

-- @node: measurable_orderedMarkedFactorial
/-- Each one-mark ordered falling-factorial statistic is measurable. -/
private lemma measurable_orderedMarkedFactorial {n d : ℕ} (M : ℝ)
    (k : Fin d) (a : Bool) (j : ℕ) :
    Measurable (fun s : Fin n → Obs d => orderedMarkedFactorial M s k a j) := by
  unfold orderedMarkedFactorial
  exact ((((measurable_estimationArmSum a k).div measurable_const).mul
      ((measurable_of_countable (fun q : ℕ =>
        ((q - 1).descFactorial j : ℝ))).comp
          (measurable_estimationArmCount a k))).mul
      ((measurable_of_countable (fun q : ℕ => ((q - (j + 1) : ℕ) : ℝ))).comp
        ((measurable_estimationArmCount false k).add
          (measurable_estimationArmCount true k)))).div measurable_const

-- @node: measurable_lightPolynomialTerm
/-- [A light-cell signed polynomial contribution is measurable](goal). -/
lemma measurable_lightPolynomialTerm {n d : ℕ} (M B : ℝ) (K : ℕ)
    (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => lightPolynomialTerm M B K s k) := by
  unfold lightPolynomialTerm
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul
    ((measurable_orderedMarkedFactorial M k true j).sub
      (measurable_orderedMarkedFactorial M k false j))

-- @node: measurable_estimationCellCount
/-- Estimation-block cell counts are measurable functions of the design. -/
private lemma measurable_estimationCellCount {n d : ℕ} (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => estimationCellCount s k) := by
  let f : (Fin n → Fin d × Bool) → ℕ := fun z =>
    (Finset.univ.filter fun i => !(inPilot i) ∧ (z i).1 = k ∧ (z i).2 = false).card +
      (Finset.univ.filter fun i => !(inPilot i) ∧ (z i).1 = k ∧ (z i).2 = true).card
  simpa [estimationCellCount, estimationArmCount, f] using measurable_design_function f

-- @node: measurable_heavyEmpiricalTerm
/-- [A heavy-cell empirical contribution is measurable](goal). -/
lemma measurable_heavyEmpiricalTerm {n d : ℕ} (M : ℝ) (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => heavyEmpiricalTerm M s k) := by
  unfold heavyEmpiricalTerm
  exact (((measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
      (measurable_estimationCellCount k)).div measurable_const).mul
    (((measurable_estimationArmMean true k).sub
      (measurable_estimationArmMean false k)).div measurable_const)

-- @node: measurable_obs_y
private lemma measurable_obs_y {d : ℕ} : Measurable (fun o : Obs d => o.y) := by
  exact measurable_snd.comp (measurable_snd.comp
    (measurable_iff_comap_le.mpr le_rfl))

-- @node: measurable_armCount
private lemma measurable_armCount {n d : ℕ} (a : Bool) (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => armCount s a k) := by
  let f : (Fin n → Fin d × Bool) → ℕ := fun z =>
    (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = a).card
  exact (measurable_of_finite f).comp measurable_obs_design

-- @node: measurable_armSum
private lemma measurable_armSum {n d : ℕ} (a : Bool) (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => armSum s a k) := by
  unfold armSum
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · convert (measurable_design_function (fun z => z i))
      (measurableSet_singleton (k, a)) using 1
    ext s
    simp [Prod.ext_iff]
  · exact measurable_obs_y.comp (measurable_pi_apply i)
  · exact measurable_const

-- @node: measurable_empiricalArmMean
private lemma measurable_empiricalArmMean {n d : ℕ} (a : Bool) (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => empiricalArmMean s a k) := by
  unfold empiricalArmMean
  apply Measurable.ite
  · exact measurable_armCount a k measurableSet_Ioi
  · exact (measurable_armSum a k).div
      ((measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
        (measurable_armCount a k))
  · exact measurable_const

-- @node: measurable_cellCount
private lemma measurable_cellCount {n d : ℕ} (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => cellCount s k) := by
  let f : (Fin n → Fin d × Bool) → ℕ := fun z =>
    (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = false).card +
      (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = true).card
  simpa [cellCount, armCount, f] using measurable_design_function f

-- @node: measurable_usableCell
private lemma measurable_usableCell {n d : ℕ} (k : Fin d) :
    Measurable (fun s : Fin n → Obs d => usableCell s k) := by
  let f : (Fin n → Fin d × Bool) → Bool := fun z =>
    decide (0 < (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = false).card ∧
      0 < (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = true).card)
  simpa [usableCell, armCount, f] using measurable_design_function f

-- @node: measurable_usableTotal
private lemma measurable_usableTotal {n d : ℕ} :
    Measurable (fun s : Fin n → Obs d => usableTotal s) := by
  let f : (Fin n → Fin d × Bool) → ℕ := fun z =>
    ∑ k : Fin d,
      if decide (0 < (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = false).card ∧
          0 < (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = true).card) then
        (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = false).card +
          (Finset.univ.filter fun i => (z i).1 = k ∧ (z i).2 = true).card else 0
  simpa [usableTotal, usableCell, cellCount, armCount, f] using
    measurable_design_function f

/-- If [the outcome scale satisfies its stated bound](hyp:hM), [the collision construction is
  measurable and lies in the estimator range](goal). -/
-- @node: collisionEstimator_admissible
lemma collisionEstimator_admissible {n d : ℕ} {M : ℝ} (hM : 0 ≤ M) :
    Measurable (collisionEstimator (n := n) (d := d) M) ∧
      ∀ s : Fin n → Obs d,
        collisionEstimator (n := n) (d := d) M s ∈ Icc (-M) M := by
  constructor
  · unfold collisionEstimator clip
    apply Measurable.max measurable_const
    apply Measurable.min measurable_const
    apply Measurable.ite
    · exact measurable_usableTotal measurableSet_Ioi
    · apply Measurable.div
      · apply Finset.measurable_sum
        intro k _
        apply Measurable.ite
        · convert measurable_usableCell k (measurableSet_singleton true) using 1
          ext s
          simp
        · exact ((measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
              (measurable_cellCount k)).mul
            ((measurable_empiricalArmMean true k).sub
              (measurable_empiricalArmMean false k))
        · exact measurable_const
      · exact (measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
          measurable_usableTotal
    · exact measurable_const
  · intro s
    unfold collisionEstimator clip
    constructor
    · exact le_max_left _ _
    · rw [max_le_iff]
      exact ⟨by linarith, min_le_left _ _⟩

/-- If [the outcome scale satisfies its stated bound](hyp:hM), [the polynomial construction is
  measurable and lies in the estimator range](goal). -/
lemma polyEstimator_admissible {n d N : ℕ} {M rho : ℝ} (hM : 0 ≤ M) :
    Measurable (rawPolyEstimator (n := n) (d := d) N rho M) ∧
      ∀ s : Fin n → Obs d,
        rawPolyEstimator (n := n) (d := d) N rho M s ∈ Icc (-M) M := by
  constructor
  · unfold rawPolyEstimator
    by_cases hbranch : N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n
    · simp_rw [if_pos hbranch]
      apply Measurable.const_mul
      unfold clip
      apply Measurable.max measurable_const
      apply Measurable.min measurable_const
      apply Finset.measurable_sum
      intro k _
      apply Measurable.ite
      · exact (((measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
          (measurable_pilotCount k)) measurableSet_Ioi)
      · exact measurable_heavyEmpiricalTerm M k
      · exact measurable_lightPolynomialTerm M
          (4096 * logEN n / (n - n / 2 : ℕ)) (polynomialDegree n) k
    · simp_rw [if_neg hbranch]
      exact measurable_const
  · intro s
    by_cases hbranch : N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n
    · unfold rawPolyEstimator
      rw [if_pos hbranch]
      unfold clip
      constructor
      · have hclip_lower : (-1 : ℝ) ≤ max (-1) (min 1
            (∑ k : Fin d, if 256 * logEN n < pilotCount s k then
              heavyEmpiricalTerm M s k else
              lightPolynomialTerm M (4096 * logEN n / (n - n / 2 : ℕ))
                (polynomialDegree n) s k)) := le_max_left _ _
        nlinarith
      · have hclip_upper : max (-1) (min 1
            (∑ k : Fin d, if 256 * logEN n < pilotCount s k then
              heavyEmpiricalTerm M s k else
              lightPolynomialTerm M (4096 * logEN n / (n - n / 2 : ℕ))
                (polynomialDegree n) s k)) ≤ 1 := by
          rw [max_le_iff]
          exact ⟨by norm_num, min_le_left _ _⟩
        nlinarith
    · unfold rawPolyEstimator
      rw [if_neg hbranch]
      exact ⟨by linarith, hM⟩

/-- The collision construction packaged as a member of the estimator space. -/
noncomputable def collisionEstimatorElement {n d : ℕ} {M : ℝ} (hM : 1 ≤ M) :
    Estimator n d M :=
  ⟨collisionEstimator M, collisionEstimator_admissible (le_trans zero_le_one hM)⟩

/-- The polynomial handle packaged as an admissible estimator. -/
noncomputable def polyEstimatorElement {M : ℝ} {n d : ℕ}
    (handle : PolynomialHandle) (hM : 1 ≤ M) :
    Estimator n d M :=
  ⟨polyEstimator handle M, by
    change Measurable
        (rawPolyEstimator (n := n) (d := d) handle.N handle.rho M) ∧
      ∀ s : Fin n → Obs d,
        rawPolyEstimator handle.N handle.rho M s ∈ Icc (-M) M
    exact polyEstimator_admissible (n := n) (d := d)
      (N := handle.N) (rho := handle.rho) (le_trans zero_le_one hM)⟩

-- @node: def:total-estimator
/-- Deterministic three-branch known-radius selector on two admissible estimators.
The result itself remains in the same measurable `[-M,M]`-valued space. -/
noncomputable def totalSelector {n d : ℕ} {M : ℝ} (hM : 1 ≤ M) (sigma : ℝ)
    (poly collision : Estimator n d M) : Estimator n d M :=
  if collisionComponent n d sigma ≤ min 1 (polynomialComponent n d) then collision
  else if polynomialComponent n d < min 1 (collisionComponent n d sigma) then poly
  else
    ⟨fun _ => 0, measurable_const, fun _ =>
      ⟨by linarith [hM], by linarith [hM]⟩⟩
  -- @realizes widehat_tau_n^star(admissible known-radius three-branch selector)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
