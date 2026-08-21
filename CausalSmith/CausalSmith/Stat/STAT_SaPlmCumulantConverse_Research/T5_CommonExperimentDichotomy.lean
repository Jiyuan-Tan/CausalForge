import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.T3_AdaptiveRootNMinimax
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.T8_BoundedOutcomeGaussianDegeneracy

/-!
# Separate common-experiment conclusions
-/

noncomputable section

open Set
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- Compatibility name for the represented wrapper now defined beside the
single option-A adapter. -/
def compiledSpectralProgram (compiled : CompiledBoundedSpectralAdapter) {p : Parameters}
    (input : RepresentedSpectralInput p) : SpectralProgramResult :=
  representedSpectralProgram compiled input

/-- A compiled implementation of the bounded spectral adapter is a faithful execution of the
estimator built from the given parameter block, certified primitive records, certified range
record, and treatment-regression code: everything the compiled build reports agrees with what
the estimator's own specification demands.

This is the represented-execution property under a name that mentions the compiled adapter
explicitly, so that the dichotomy statement can quantify over compiled builds directly. -/
abbrev CompiledRepresentedExecution {Xspace : Type*} [MeasurableSpace Xspace]
    (compiled : CompiledBoundedSpectralAdapter)
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) : Prop :=
  RepresentedExecution compiled p pStar cStar gcode

/-- [Running the contour-selection program through a compiled implementation of the bounded
adapter returns exactly the same outcome — reported value, execution trace, selected contour,
decoded winding number, and enclosure — as the reference instrumented program](goal), so the
choice of compiled build never changes what the estimator reports. -/
lemma compiledSpectralProgram_eq_instrumented
    (compiled : CompiledBoundedSpectralAdapter) {p : Parameters}
    (input : RepresentedSpectralInput p) :
    compiledSpectralProgram compiled input = instrumentedSpectralProgram input := by
  exact representedSpectralProgram_eq_instrumented compiled input

/-- Fix the experiment-wide constants of the partially linear design: [a cumulant order of at
least two](hyp:hr), [a strictly positive cumulant-separation constant](hyp:hdelta), [a strictly
positive range bound for the treatment coefficient](hyp:hCtheta), [strictly positive uniform
bounds for the treatment and outcome regressions](hyp:hCg,hCq), and [strictly positive
sub-Gaussian scales for the treatment noise and the outcome noise](hyp:hpsieta,hpsixi). Then
[the same experiment splits into two sharply different halves: on the non-Gaussian class a
single pair of positive constants c and C bounds the minimax mean squared error between c/n
and C/n along every sequence of sample sizes that carries these constants, the assembled
estimator is Borel measurable, attains the C/n upper bound over that class, is executed
faithfully by every compiled build, and is read off a contour bank that never changes with the
sample size; whereas on the simultaneous bounded-outcome Gaussian class the treatment
coefficient is forced to be zero, so both the Gaussian minimax mean squared error and the
Gaussian minimax generalized-quantile error vanish identically](goal).

The two halves are stated as one theorem because they share the same fixed experiment: the
same order, separation, range and regression constants, the same noise scales, and the same
certified primitive records feed both the root-n conclusion and the degeneracy conclusion. -/
-- @node: thm:common-experiment-dichotomy
theorem common_experiment_dichotomy
    (r : ℕ) (delta Ctheta Cg Cq psieta psixi : ℝ)
    (hr : 2 ≤ r) (hdelta : 0 < delta) (hCtheta : 0 < Ctheta)
    (hCg : 0 < Cg) (hCq : 0 < Cq) (hpsieta : 0 < psieta)
    (hpsixi : 0 < psixi) :
    ∀ {Xspace : Type*} [MeasurableSpace Xspace],
    (∀ (p0 : Parameters), p0.r = r → p0.delta = delta →
      p0.Ctheta = Ctheta → p0.Cg = Cg → p0.Cq = Cq →
      p0.psieta = psieta → p0.psixi = psixi →
      (fixed : FixedExperimentRecords p0) →
      ∀ (pSeq : ℕ → Parameters)
        (gcode qcode : ℕ → Xspace → ℝ) (eps1 eps2 : ℕ → ℝ),
      (∀ j, Measurable (gcode j)) →
      (∀ j, Measurable (qcode j)) →
      (hfixed : ∀ j, SameFixedExperimentConstants p0 (pSeq j) ∧
        (pSeq j).eps1n = eps1 ∧ (pSeq j).eps2n = eps2) →
      Filter.Tendsto (fun j ↦ (pSeq j).n) Filter.atTop Filter.atTop →
      (∀ᶠ j in Filter.atTop,
        ({m : Model (Xspace := Xspace) (pSeq j) |
          NonGaussianClass (pSeq j) (pSeq j).n m ∧
            barG (pSeq j) m (pSeq j).n =
                clippedTreatmentCode (pSeq j) gcode (pSeq j).n ∧
              barQ (pSeq j) m (pSeq j).n =
                clippedOutcomeCode (pSeq j) qcode (pSeq j).n}).Nonempty ∧
        2 ≤ (pSeq j).n ∧
        (pSeq j).eps1n (pSeq j).n ≤ (4 * searchRadius (pSeq j) *
          Real.exp (2 * (pSeq j).Cg * searchRadius (pSeq j)))⁻¹) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      let B := contourBank p0 fixed.bank
      ∀ᶠ j in Filter.atTop,
        let pStarj := fixedBankInput fixed.bank (hfixed j).1
        let cStarj := fixedRangeInput fixed.range (hfixed j).1
        contourBank (pSeq j) pStarj = B ∧
        ENNReal.ofReal (c / (pSeq j).n) ≤
            minimaxRisk (pSeq j) (pSeq j).n gcode qcode ∧
        minimaxRisk (pSeq j) (pSeq j).n gcode qcode ≤
            ENNReal.ofReal (C / (pSeq j).n) ∧
        Measurable (thetaHatSpec (pSeq j) pStarj cStarj gcode) ∧
        (∀ compiled : CompiledBoundedSpectralAdapter,
          FullCanonicalBuildAndCompilation compiled (pSeq j) pStarj cStarj gcode →
            CompiledRepresentedExecution compiled (pSeq j) pStarj cStarj gcode) ∧
        (⨆ m : Model (Xspace := Xspace) (pSeq j),
          ⨆ (_ : NonGaussianClass (pSeq j) (pSeq j).n m ∧
            barG (pSeq j) m (pSeq j).n =
                clippedTreatmentCode (pSeq j) gcode (pSeq j).n ∧
              barQ (pSeq j) m (pSeq j).n =
                clippedOutcomeCode (pSeq j) qcode (pSeq j).n),
          mseRisk m (pSeq j).n
            (thetaHatSpec (pSeq j) pStarj cStarj gcode)) ≤
              ENNReal.ofReal (C / (pSeq j).n)) ∧
    (∀ (p : Parameters) (m : Model (Xspace := Xspace) p),
      GaussianClass p p.n m → m.theta0 = 0) ∧
    (∀ (p : Parameters) (gcode qcode : ℕ → Xspace → ℝ),
      (∀ j, Measurable (gcode j)) →
      (∀ j, Measurable (qcode j)) →
      ({m : Model (Xspace := Xspace) p |
        GaussianClass p p.n m ∧
          barG p m p.n = clippedTreatmentCode p gcode p.n ∧
          barQ p m p.n = clippedOutcomeCode p qcode p.n}).Nonempty →
      minimaxRiskG (Xspace := Xspace) p p.n gcode qcode = 0 ∧
      minimaxQuantileRiskG (Xspace := Xspace) p p.n gcode qcode = 0) := by
  rcases adaptive_rootn_minimax r delta Ctheta Cg Cq psieta psixi hr hdelta
      hCtheta hCg hCq hpsieta hpsixi with ⟨c, C, hc, hC, hmain⟩
  intro Xspace inst
  have hgauss := bounded_outcome_gaussian_degeneracy (Xspace := Xspace)
  refine ⟨?_, ?_, ?_⟩
  · intro p0 hp0r hp0delta hp0Ctheta hp0Cg hp0Cq hp0psieta hp0psixi fixed
    have hmain' := hmain (Xspace := Xspace) p0 hp0r hp0delta hp0Ctheta hp0Cg
      hp0Cq hp0psieta hp0psixi fixed
    intro pSeq gcode qcode eps1 eps2 _hgcodeMeas _hqcodeMeas hfixed _htend hevent
    refine ⟨c, C, hc, hC, ?_⟩
    dsimp only
    filter_upwards [hevent] with j hj
    rcases hj.1 with ⟨base, hbaseClass, hgcode, hqcode⟩
    have hgclip : clippedTreatmentCode (pSeq j) gcode (pSeq j).n =
        clippedTreatmentCode (pSeq j) base.gcode (pSeq j).n := by
      exact hgcode.symm
    have hqclip : clippedOutcomeCode (pSeq j) qcode (pSeq j).n =
        clippedOutcomeCode (pSeq j) base.qcode (pSeq j).n := by
      exact hqcode.symm
    have hresult := hmain' (pSeq j) (hfixed j).1 base
    rcases hresult with ⟨hmeas, _hrepr, _hclass, _heq, hrisk, _hace⟩
    have hiid : IidSampling (pSeq j).n base.P (iidLaw base (pSeq j).n) := rfl
    have hlaws : ({m : Model (Xspace := Xspace) (pSeq j) |
        NonGaussianClass (pSeq j) (pSeq j).n m ∧
          barG (pSeq j) m (pSeq j).n = barG (pSeq j) base (pSeq j).n ∧
            barQ (pSeq j) m (pSeq j).n = barQ (pSeq j) base (pSeq j).n}).Nonempty :=
      ⟨base, hbaseClass, rfl, rfl⟩
    rcases hrisk hiid hlaws hj.2.1 hj.2.2 with
      ⟨hlower, hminimaxEst, hestUpper, _hquantile⟩
    have hriskEq : minimaxRisk (pSeq j) (pSeq j).n gcode qcode =
        minimaxRisk (pSeq j) (pSeq j).n base.gcode base.qcode := by
      change minimaxRiskOn (pSeq j) (pSeq j).n
          {m | NonGaussianClass (pSeq j) (pSeq j).n m ∧
            barG (pSeq j) m (pSeq j).n = clippedTreatmentCode (pSeq j) gcode (pSeq j).n ∧
            barQ (pSeq j) m (pSeq j).n = clippedOutcomeCode (pSeq j) qcode (pSeq j).n} =
        minimaxRiskOn (pSeq j) (pSeq j).n
          {m | NonGaussianClass (pSeq j) (pSeq j).n m ∧
            barG (pSeq j) m (pSeq j).n =
              clippedTreatmentCode (pSeq j) base.gcode (pSeq j).n ∧
            barQ (pSeq j) m (pSeq j).n =
              clippedOutcomeCode (pSeq j) base.qcode (pSeq j).n}
      congr 1
      ext m
      simp only [Set.mem_setOf_eq]
      rw [hgclip, hqclip]
    have htheta :
        (thetaHatSpec (pSeq j)
            (fixedBankInput fixed.bank (hfixed j).1)
            (fixedRangeInput fixed.range (hfixed j).1) gcode :
          (Fin (pSeq j).n → Obs Xspace) → ℝ) =
        thetaHatSpec (pSeq j)
            (fixedBankInput fixed.bank (hfixed j).1)
            (fixedRangeInput fixed.range (hfixed j).1) base.gcode := by
      apply thetaHatSpec_congr_current
      exact fun x ↦ congrFun hgclip x
    have hmeas' : Measurable (thetaHatSpec (pSeq j)
        (fixedBankInput fixed.bank (hfixed j).1)
        (fixedRangeInput fixed.range (hfixed j).1) gcode) := by
      rw [htheta]
      exact hmeas
    have hcompiled : ∀ compiled : CompiledBoundedSpectralAdapter,
        FullCanonicalBuildAndCompilation compiled (pSeq j)
            (fixedBankInput fixed.bank (hfixed j).1)
            (fixedRangeInput fixed.range (hfixed j).1) gcode →
          CompiledRepresentedExecution compiled (pSeq j)
            (fixedBankInput fixed.bank (hfixed j).1)
            (fixedRangeInput fixed.range (hfixed j).1) gcode := by
      intro compiled hfull
      exact representedExecution_of_fullCanonicalBuildAndCompilation compiled
        (pSeq j) (fixedBankInput fixed.bank (hfixed j).1)
          (fixedRangeInput fixed.range (hfixed j).1) gcode hfull
    have hestUpper' : (⨆ m : Model (Xspace := Xspace) (pSeq j),
        ⨆ (_ : NonGaussianClass (pSeq j) (pSeq j).n m ∧
          barG (pSeq j) m (pSeq j).n = clippedTreatmentCode (pSeq j) gcode (pSeq j).n ∧
          barQ (pSeq j) m (pSeq j).n = clippedOutcomeCode (pSeq j) qcode (pSeq j).n),
        mseRisk m (pSeq j).n
          (thetaHatSpec (pSeq j) (fixedBankInput fixed.bank (hfixed j).1)
            (fixedRangeInput fixed.range (hfixed j).1) gcode)) ≤
          ENNReal.ofReal (C / (pSeq j).n) := by
      rw [hgclip, hqclip, htheta]
      exact hestUpper
    refine ⟨?_, ?_, ?_, hmeas', hcompiled, hestUpper'⟩
    · simp [fixedBankInput, CertifiedBankInputs.transport, contourBank]
    · rw [hriskEq]
      exact hlower
    · rw [hriskEq]
      exact hminimaxEst.trans hestUpper
  · intro p m hm
    exact (hgauss p).1 m hm
  · intro p gcode qcode _hgcodeMeas _hqcodeMeas hnonempty
    exact (hgauss p).2 gcode qcode hnonempty

end CausalSmith.Stat.SaPlmCumulantConverse
