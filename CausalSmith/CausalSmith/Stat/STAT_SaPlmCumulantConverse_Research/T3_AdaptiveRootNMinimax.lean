import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.ClassRelations
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.AdaptiveSelectorPacket
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.FixedCodeConverse
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.EmpiricalTransformSeries
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.HardSubmodel
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.PopulationNumeratorBound
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.SelectorSoundness
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.T2_ExactContourIdentification
import Causalean.Stat.Concentration.Chebyshev
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.Pinsker

/-!
# Certified adaptive contour estimator and matched fixed-separation rate

The ordinary statistic and all statistical bounds below are unconditional.
Only the final represented-data execution clause is parameterized by a
compiled implementation of the bounded certified complex arithmetic record.
-/

noncomputable section

open MeasureTheory Metric Set
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace CausalSmith.Stat.SaPlmCumulantConverse

private def uniformBankCeil (x : ℝ) : ℕ :=
  ⌈max 1 (x + 1) + 1⌉₊

private def uniformBankExponent (psieta R1 : ℝ) : ℕ :=
  let Upsi := uniformBankCeil psieta
  let UR := uniformBankCeil R1
  let Ncert := 4 * Upsi ^ 2 * (UR + 2) ^ 3
  let mStar := Ncert + 3
  let eStar := 8 * UR * Upsi ^ 2 * (UR + 1) ^ 2
  let dStarDen := 3 * (2 * UR + 1)
  2 * eStar + Ncert * (mStar + dStarDen)

private def uniformBankA (psieta R1 : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ uniformBankExponent psieta R1

private def uniformSelectorRiskConstant
    (Ctheta Cg Cq psieta psixi R1 K : ℝ) : ℝ :=
  let a := uniformBankA psieta R1
  let CG := Real.sqrt
    (64 * (Cq ^ 4 + 4 * Ctheta ^ 4 * psieta ^ 4 + 4 * psixi ^ 4) +
      2 * Real.exp (16 * R1 * Cg + 16 * R1 ^ 2 * psieta ^ 2))
  let L := R1 * max (23 * a / 64)⁻¹
    (CG * ((31 * a / 64) * (23 * a / 64))⁻¹)
  12 * L ^ 2 * K + 1536 * Ctheta ^ 2 * K / a ^ 2 + 2

private lemma positiveCeil_refine_le_uniformBankCeil
    (x : CertifiedReal) (hx : x.value = v) :
    positiveCeil (x.refine errorOne).hi ≤
      uniformBankCeil v := by
  let I := x.refine errorOne
  have hc := CertifiedReal.refine_contains x errorOne
  have hw := CertifiedReal.refine_width x errorOne
  have hhi : (I.hi : ℝ) ≤ v + 1 := by
    have hlo : (I.lo : ℝ) ≤ v := by simpa [I, RatInterval.Contains, hx] using hc.1
    have hw' : (I.hi : ℝ) - I.lo ≤ 1 := by
      exact_mod_cast (show I.width ≤ (1 : ℚ) from hw)
    linarith
  unfold positiveCeil uniformBankCeil
  have hnonneg : (0 : ℚ) ≤ max 1 (x.refine errorOne).hi :=
    le_trans (by norm_num) (le_max_left _ _)
  have hceil : ((⌈max 1 (x.refine errorOne).hi⌉₊ : ℕ) : ℝ) <
      (max 1 (x.refine errorOne).hi : ℚ) + 1 := by
    exact_mod_cast Nat.ceil_lt_add_one hnonneg
  have hmax : ((max 1 (x.refine errorOne).hi : ℚ) : ℝ) ≤ max 1 (v + 1) := by
    rw [Rat.cast_max, Rat.cast_one]
    exact max_le_max (le_refl (1 : ℝ)) hhi
  have htarget : max 1 (v + 1) + 1 ≤
      ((⌈max 1 (v + 1) + 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hadd : ((max 1 (x.refine errorOne).hi : ℚ) : ℝ) + 1 ≤
      max 1 (v + 1) + 1 := by linarith
  exact_mod_cast (hceil.le.trans hadd |>.trans htarget)

private lemma contourBank_uStar_le_uniformBankExponent
    (p : Parameters) (pStar : CertifiedBankInputs p) :
    (contourBank p pStar).uStar ≤
      uniformBankExponent p.psieta (searchRadius p) := by
  have hpsi : positiveCeil (pStar.psietaName.name.refine errorOne).hi ≤
      uniformBankCeil p.psieta :=
    positiveCeil_refine_le_uniformBankCeil _ pStar.psieta_value
  have hR : positiveCeil (pStar.R1Name.name.refine errorOne).hi ≤
      uniformBankCeil (searchRadius p) :=
    positiveCeil_refine_le_uniformBankCeil _ pStar.R1_value
  dsimp [contourBank, uniformBankExponent]
  gcongr <;> first | exact hpsi | exact hR

private lemma uniformBankA_le_contourBank_aStar
    (p : Parameters) (pStar : CertifiedBankInputs p) :
    uniformBankA p.psieta (searchRadius p) ≤ (contourBank p pStar).aStar := by
  simpa [uniformBankA, contourBank] using
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).2
        (contourBank_uStar_le_uniformBankExponent p pStar)

private lemma adaptiveSelectorRiskConstant_le_uniform
    (p : Parameters) (pStar : CertifiedBankInputs p) (K : ℝ) (hK : 0 ≤ K) :
    adaptiveSelectorRiskConstant p pStar K ≤
      uniformSelectorRiskConstant p.Ctheta p.Cg p.Cq p.psieta p.psixi
        (searchRadius p) K := by
  let a : ℝ := ((contourBank p pStar).aStarRat : ℝ)
  let a0 := uniformBankA p.psieta (searchRadius p)
  let CG := populationNumeratorEnvelope p
  let L := searchRadius p * max (23 * a / 64)⁻¹
    (CG * ((31 * a / 64) * (23 * a / 64))⁻¹)
  let L0 := searchRadius p * max (23 * a0 / 64)⁻¹
    (CG * ((31 * a0 / 64) * (23 * a0 / 64))⁻¹)
  have ha0 : 0 < a0 := by dsimp [a0, uniformBankA]; positivity
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (contourBank p pStar).aStarRat_pos
  have ha0a : a0 ≤ a := by
    simpa [a0, a, (contourBank p pStar).aStar_eq] using
      uniformBankA_le_contourBank_aStar p pStar
  have hCG : 0 ≤ CG := by dsimp [CG, populationNumeratorEnvelope]; positivity
  have hR : 0 ≤ searchRadius p := by
    have hz : 0 < zeroRadius p := by
      rw [← pStar.R0_value]
      have hlower : (0 : ℝ) < (pStar.R0Name.lower : ℝ) := by
        exact_mod_cast pStar.R0Name.lower_pos
      exact hlower.trans_le pStar.R0Name.lower_le_value
    unfold searchRadius
    linarith
  have h23 : (23 * a / 64)⁻¹ ≤ (23 * a0 / 64)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    nlinarith
  have hprod : ((31 * a / 64) * (23 * a / 64))⁻¹ ≤
      ((31 * a0 / 64) * (23 * a0 / 64))⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    nlinarith
  have hL : L ≤ L0 := by
    dsimp [L, L0]
    gcongr
  have hL0 : 0 ≤ L0 := by dsimp [L0]; positivity
  have hterm1 : 12 * L ^ 2 * K ≤ 12 * L0 ^ 2 * K := by
    gcongr
  have hnum : 0 ≤ 1536 * p.Ctheta ^ 2 * K := by positivity
  have hterm2 : 1536 * p.Ctheta ^ 2 * K / a ^ 2 ≤
      1536 * p.Ctheta ^ 2 * K / a0 ^ 2 := by
    exact div_le_div₀ hnum le_rfl (sq_pos_of_pos ha0) (by nlinarith)
  have hsum := add_le_add (add_le_add hterm1 hterm2) (le_refl (2 : ℝ))
  simpa [adaptiveSelectorRiskConstant, adaptiveSelectorRatioConstant,
    ordinaryContourPerturbationConstant, uniformSelectorRiskConstant,
    populationNumeratorEnvelope, L, L0, a, a0, CG] using hsum

/-- Fixed-separation matched minimax MSE and generalized-quantile bounds.
The same supplied primitive records are used by the bank, the ordinary Borel
statistic, and (conditionally) the represented-data transducer. -/
-- @node: thm:adaptive-rootn-minimax
theorem adaptive_rootn_minimax
    (r : ℕ) (delta Ctheta Cg Cq psieta psixi : ℝ)
    (hr : 2 ≤ r) (hdelta : 0 < delta) (hCtheta : 0 < Ctheta)
    (hCg : 0 < Cg) (hCq : 0 < Cq) (hpsieta : 0 < psieta)
    (hpsixi : 0 < psixi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Xspace : Type*} [MeasurableSpace Xspace]
      (p0 : Parameters), p0.r = r → p0.delta = delta →
      p0.Ctheta = Ctheta → p0.Cg = Cg → p0.Cq = Cq →
      p0.psieta = psieta → p0.psixi = psixi →
      (fixed : FixedExperimentRecords p0) →
      ∀ (p : Parameters), (hfixed : SameFixedExperimentConstants p0 p) →
      ∀ base : Model (Xspace := Xspace) p,
        let pStarP := fixedBankInput fixed.bank hfixed
        let cStarP := fixedRangeInput fixed.range hfixed
        let laws : Set (Model (Xspace := Xspace) p) :=
          {m | NonGaussianClass p p.n m ∧
            barG p m p.n = barG p base p.n ∧ barQ p m p.n = barQ p base p.n}
        Measurable (thetaHatSpec (Xspace := Xspace) p pStarP cStarP base.gcode) ∧
        (∀ compiled : CompiledBoundedSpectralAdapter,
          FullCanonicalBuildAndCompilation compiled p pStarP cStarP base.gcode →
            RepresentedExecution compiled p pStarP cStarP base.gcode) ∧
        (∀ m : Model (Xspace := Xspace) p,
          JmsAceClass p p.n m → NonGaussianClass p p.n m) ∧
        (p.s = (p.r : ENNReal) →
          ∀ m : Model (Xspace := Xspace) p,
            JmsAceClass p p.n m ↔ AceComparisonSubclass p p.n m) ∧
        (IidSampling p.n base.P (iidLaw base p.n) → laws.Nonempty → 2 ≤ p.n →
          p.eps1n p.n ≤ (4 * searchRadius p *
            Real.exp (2 * p.Cg * searchRadius p))⁻¹ →
          ENNReal.ofReal (c / p.n) ≤ minimaxRisk p p.n base.gcode base.qcode ∧
          minimaxRisk p p.n base.gcode base.qcode ≤
            ⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ laws),
              mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode) ∧
          (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ laws),
              mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode)) ≤
                ENNReal.ofReal (C / p.n) ∧
          (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ laws),
            ENNReal.ofReal (generalizedQuantile p p.n m
              (fun data ↦ |thetaHatSpec p pStarP cStarP base.gcode data - m.theta0|))) ≤
                ENNReal.ofReal (Real.sqrt (C / (p.gamma * p.n)))) ∧
        (let aceLaws : Set (Model (Xspace := Xspace) p) :=
            {m | JmsAceClass p p.n m ∧
              barG p m p.n = barG p base p.n ∧
                barQ p m p.n = barQ p base p.n};
          aceLaws.Nonempty → 2 ≤ p.n →
          p.eps1n p.n ≤ (4 * searchRadius p *
            Real.exp (2 * p.Cg * searchRadius p))⁻¹ →
            ENNReal.ofReal (c / p.n) ≤ minimaxRiskOn p p.n aceLaws ∧
            minimaxRiskOn p p.n aceLaws ≤
              ⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ aceLaws),
                mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode) ∧
            (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ aceLaws),
                mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode)) ≤
                  ENNReal.ofReal (C / p.n) ∧
            (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ aceLaws),
              ENNReal.ofReal (generalizedQuantile p p.n m
                (fun data ↦ |thetaHatSpec p pStarP cStarP base.gcode data - m.theta0|))) ≤
                  ENNReal.ofReal (Real.sqrt (C / (p.gamma * p.n)))) := by
  let R1 := Ak (r + 1) * (psieta ^ 2 / delta) ^ (((r + 1 : ℕ) : ℝ) - 2)⁻¹ + 1
  let K := empiricalTransformL2Constant Ctheta Cg Cq psieta psixi R1
  let C := uniformSelectorRiskConstant Ctheta Cg Cq psieta psixi R1 K
  obtain ⟨cNG, hcNG, hNG⟩ :=
    fixed_code_non_gaussian_minimax_lower r delta Ctheta Cg Cq psieta psixi hpsixi
  obtain ⟨cACE, hcACE, hACE⟩ :=
    fixed_code_ace_minimax_lower r delta Ctheta Cg Cq psieta psixi hpsixi
  refine ⟨min cNG cACE, C, lt_min hcNG hcACE, ?_, ?_⟩
  · dsimp [C, uniformSelectorRiskConstant, K]
    have hR1 : 0 < R1 := by
      dsimp [R1]
      have hbase : 0 ≤ psieta ^ 2 / delta := div_nonneg (sq_nonneg _) hdelta.le
      have hAk : 0 ≤ Ak (r + 1) := by
        unfold Ak
        positivity
      have hrpow : 0 ≤ (psieta ^ 2 / delta) ^ (((r + 1 : ℕ) : ℝ) - 2)⁻¹ :=
        Real.rpow_nonneg hbase _
      nlinarith
    have hK : 0 < K := empiricalTransformL2Constant_pos _ _ _ _ _ _
    have ha : 0 < uniformBankA psieta R1 := by
      dsimp [uniformBankA]
      positivity
    positivity
  intro Xspace inst p0 hp0r hp0delta hp0θ hp0g hp0q hp0η hp0ξ fixed
  intro p hfixed base
  dsimp
  have hpθ : p.Ctheta = Ctheta := hfixed.2.2.1.symm.trans hp0θ
  have hpg : p.Cg = Cg := hfixed.2.2.2.1.symm.trans hp0g
  have hpq : p.Cq = Cq := hfixed.2.2.2.2.1.symm.trans hp0q
  have hpη : p.psieta = psieta := hfixed.2.2.2.2.2.1.symm.trans hp0η
  have hpξ : p.psixi = psixi := hfixed.2.2.2.2.2.2.symm.trans hp0ξ
  have hpR : searchRadius p = R1 := by
    dsimp [R1, searchRadius, zeroRadius]
    rw [p.k_eq, ← hfixed.1, hp0r, hpη, ← hfixed.2.1, hp0delta]
  let pStarP := fixedBankInput fixed.bank hfixed
  let cStarP := fixedRangeInput fixed.range hfixed
  let laws : Set (Model (Xspace := Xspace) p) :=
    {m | NonGaussianClass p p.n m ∧
      barG p m p.n = barG p base p.n ∧ barQ p m p.n = barQ p base p.n}
  have hmeas : Measurable (thetaHatSpec (Xspace := Xspace) p pStarP cStarP base.gcode) :=
    thetaHatSpec_measurable p pStarP cStarP base.gcode (base.gcode_measurable p.n)
  have theta_eq_of_barG (m : Model (Xspace := Xspace) p)
      (hbar : barG p m p.n = barG p base p.n) :
      (thetaHatSpec p pStarP cStarP base.gcode :
          (Fin p.n → Obs Xspace) → ℝ) =
        thetaHatSpec p pStarP cStarP m.gcode := by
    apply thetaHatSpec_congr_current
    intro x
    exact congrFun hbar.symm x
  have hrels := jms_ace_class_relations (Xspace := Xspace) p p.n
  have hKpos : 0 < K := empiricalTransformL2Constant_pos _ _ _ _ _ _
  have hCpos : 0 < C := by
    dsimp [C, uniformSelectorRiskConstant]
    positivity
  have risk_of_ng (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
      (hm : NonGaussianClass p p.n m)
      (heps : p.eps1n p.n ≤
        (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹) :
      mseRisk m p.n (thetaHatSpec p pStarP cStarP m.gcode) ≤ ENNReal.ofReal (C / p.n) := by
    have hraw := thetaHatSpec_mseRisk_le_explicit Ctheta Cg Cq psieta psixi R1
      p hpθ hpg hpq hpη hpξ hpR pStarP cStarP m hn hm
      (by simp [IidSampling, iidLaw]) heps
    apply hraw.trans
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa [C, K, hpθ, hpg, hpq, hpη, hpξ, hpR] using
      adaptiveSelectorRiskConstant_le_uniform p pStarP K hKpos.le
  have quantile_of_ng (m : Model (Xspace := Xspace) p) (hn : 2 ≤ p.n)
      (hm : NonGaussianClass p p.n m)
      (heps : p.eps1n p.n ≤
        (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹) :
      generalizedQuantile p p.n m
          (fun data ↦ |thetaHatSpec p pStarP cStarP m.gcode data - m.theta0|) ≤
        Real.sqrt (C / (p.gamma * p.n)) := by
    exact thetaHatSpec_generalizedQuantile_le_of_mseRisk_le
      p pStarP cStarP m (Nat.one_le_iff_ne_zero.mpr (by omega)) C hCpos
        (risk_of_ng m hn hm heps)
  refine ⟨hmeas, ?_, hrels.1, hrels.2.2, ?_⟩
  · intro compiled hfull
    exact representedExecution_of_fullCanonicalBuildAndCompilation compiled p pStarP cStarP
      base.gcode hfull
  refine ⟨?_, ?_⟩
  · intro hiid hlaws hn heps
    have hlowerNG : ENNReal.ofReal (min cNG cACE / p.n) ≤
        minimaxRisk p p.n base.gcode base.qcode := by
      apply (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (min_le_left _ _)
        (by positivity : (0 : ℝ) ≤ p.n))).trans
      exact hNG p (hfixed.1.symm.trans hp0r) (hfixed.2.1.symm.trans hp0delta) hpθ hpg hpq
        hpη hpξ base hiid hlaws hn
    have hrisk (m : Model (Xspace := Xspace) p) (hm : m ∈ laws) :
        mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode) ≤ ENNReal.ofReal (C / p.n) := by
      rw [theta_eq_of_barG m hm.2.1]
      exact risk_of_ng m hn hm.1 heps
    have hsupRisk : (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ laws),
        mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode)) ≤ ENNReal.ofReal (C / p.n) := by
      refine iSup_le fun m ↦ iSup_le fun hm ↦ ?_
      exact hrisk m hm
    have hminimax : minimaxRisk p p.n base.gcode base.qcode ≤
        ⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ laws),
          mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode) := by
      unfold minimaxRisk minimaxRisks minimaxRiskOn
      exact iInf_le_of_le ⟨_, hmeas⟩ (le_refl _)
    have hquant (m : Model (Xspace := Xspace) p) (hm : m ∈ laws) :
        ENNReal.ofReal (generalizedQuantile p p.n m
          (fun data ↦ |thetaHatSpec p pStarP cStarP base.gcode data - m.theta0|)) ≤
          ENNReal.ofReal (Real.sqrt (C / (p.gamma * p.n))) := by
      have htheta := theta_eq_of_barG m hm.2.1
      have hfun :
          (fun data ↦ |thetaHatSpec p pStarP cStarP base.gcode data - m.theta0|) =
            (fun data ↦ |thetaHatSpec p pStarP cStarP m.gcode data - m.theta0|) := by
        funext data
        exact congrArg (fun f : (Fin p.n → Obs Xspace) → ℝ ↦ |f data - m.theta0|) htheta
      rw [hfun]
      exact ENNReal.ofReal_le_ofReal (quantile_of_ng m hn hm.1 heps)
    have hsupQuant : (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ laws),
        ENNReal.ofReal (generalizedQuantile p p.n m
          (fun data ↦ |thetaHatSpec p pStarP cStarP base.gcode data - m.theta0|))) ≤
          ENNReal.ofReal (Real.sqrt (C / (p.gamma * p.n))) := by
      exact iSup_le fun m ↦ iSup_le fun hm ↦ hquant m hm
    refine ⟨hlowerNG, hminimax, hsupRisk, ?_⟩
    exact hsupQuant
  · intro haceLaws hnAce hepsAce
    let aceLaws : Set (Model (Xspace := Xspace) p) :=
      {m | JmsAceClass p p.n m ∧
        barG p m p.n = barG p base p.n ∧ barQ p m p.n = barQ p base p.n}
    have hlowerACE : ENNReal.ofReal (min cNG cACE / p.n) ≤ minimaxRiskOn p p.n aceLaws := by
      apply (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (min_le_right _ _)
        (by positivity : (0 : ℝ) ≤ p.n))).trans
      exact hACE p (hfixed.1.symm.trans hp0r) (hfixed.2.1.symm.trans hp0delta) hpθ hpg hpq
        hpη hpξ base haceLaws hnAce
    have haceRisk (m : Model (Xspace := Xspace) p) (hm : m ∈ aceLaws) :
        mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode) ≤ ENNReal.ofReal (C / p.n) := by
      rw [theta_eq_of_barG m hm.2.1]
      exact risk_of_ng m hnAce (hrels.1 m hm.1) hepsAce
    have haceSup : (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ aceLaws),
        mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode)) ≤ ENNReal.ofReal (C / p.n) :=
      iSup_le fun m ↦ iSup_le fun hm ↦ haceRisk m hm
    have haceMinimax : minimaxRiskOn p p.n aceLaws ≤
        ⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ aceLaws),
          mseRisk m p.n (thetaHatSpec p pStarP cStarP base.gcode) := by
      unfold minimaxRiskOn
      exact iInf_le_of_le ⟨_, hmeas⟩ (le_refl _)
    have haceQuant : (⨆ m : Model (Xspace := Xspace) p, ⨆ (_ : m ∈ aceLaws),
        ENNReal.ofReal (generalizedQuantile p p.n m
          (fun data ↦ |thetaHatSpec p pStarP cStarP base.gcode data - m.theta0|))) ≤
          ENNReal.ofReal (Real.sqrt (C / (p.gamma * p.n))) := by
      refine iSup_le fun m ↦ iSup_le fun hm ↦ ?_
      have htheta := theta_eq_of_barG m hm.2.1
      have hfun :
          (fun data ↦ |thetaHatSpec p pStarP cStarP base.gcode data - m.theta0|) =
            (fun data ↦ |thetaHatSpec p pStarP cStarP m.gcode data - m.theta0|) := by
        funext data
        exact congrArg (fun f : (Fin p.n → Obs Xspace) → ℝ ↦ |f data - m.theta0|) htheta
      rw [hfun]
      exact ENNReal.ofReal_le_ofReal
        (quantile_of_ng m hnAce (hrels.1 m hm.1) hepsAce)
    refine ⟨hlowerACE, haceMinimax, haceSup, ?_⟩
    exact haceQuant

end CausalSmith.Stat.SaPlmCumulantConverse
