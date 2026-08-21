import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.JmsComparator
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.T3_AdaptiveRootNMinimax
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Alignment with the published finite-order ACE class
-/

noncomputable section

open Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

universe u

/-- The same parameter block with the second nuisance-accuracy sequence raised
to a floor: each of its terms is replaced by the larger of the original term and
the fixed level `t`, leaving every other constant untouched.

Raising a nonnegative nonincreasing sequence pointwise to a constant floor keeps
it nonnegative and nonincreasing, so the resulting block is again a legitimate
parameter block. -/
def Parameters.withEps2Floor (p : Parameters) (t : ℝ) : Parameters where
  __ := p
  eps2n := fun n ↦ max (p.eps2n n) t
  eps2_nonneg := fun n hn ↦ le_max_of_le_left (p.eps2_nonneg n hn)
  eps2_antitone := fun _ _ ha hab ↦ max_le_max_right t (p.eps2_antitone ha hab)

/-- The same data-generating law, the same treatment and outcome regressions and
the same supplied code sequences, read as a model indexed by a different
parameter block. Nothing about the distribution changes; only the block of
constants attached to it is relabelled. -/
def Model.reparam {Xspace : Type*} [MeasurableSpace Xspace]
    {p : Parameters} (q : Parameters) (m : Model (Xspace := Xspace) p) :
    Model (Xspace := Xspace) q where
  __ := m

/-- For a [nonnegative constant](hyp:hC), a [strictly positive scale](hyp:hgamma)
and a [sample size of at least one](hyp:hn), the [square root of the constant
divided by the scale times the sample size equals the square root of the
constant over the scale, multiplied by the sample size raised to the power
−1/2](goal) — the parametric-rate factor is split off from the constant. -/
lemma sqrt_div_nat_eq_scale (C gamma : ℝ) (n : ℕ) (hC : 0 ≤ C)
    (hgamma : 0 < gamma) (hn : 1 ≤ n) :
    Real.sqrt (C / (gamma * n)) =
      Real.sqrt (C / gamma) * (n : ℝ) ^ (-1 / 2 : ℝ) := by
  rw [show C / (gamma * n) = (C / gamma) * (n : ℝ)⁻¹ by field_simp]
  rw [Real.sqrt_mul (div_nonneg hC hgamma.le)]
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [← Real.rpow_neg (by positivity)]
  congr 2
  norm_num

/-- With a [nonnegative constant](hyp:hC), a [strictly positive scale](hyp:hgamma)
and a [strictly positive multiplier](hyp:hK), if one sequence [grows strictly
faster than the parametric rate, in the sense that its ratio to the sample size
raised to the power −1/2 diverges](hyp:hS), and a second sequence [eventually
dominates the multiplier times the first](hyp:hB), then the [ratio of the
parametric-rate quantity, the square root of the constant over the scale times
the sample size, to the second sequence tends to zero](goal). -/
lemma tendsto_sqrt_div_over_of_dominates (C gamma K : ℝ) (S B : ℕ → ℝ)
    (hC : 0 ≤ C) (hgamma : 0 < gamma) (hK : 0 < K)
    (hS : Filter.Tendsto
      (fun n : ℕ ↦ S n / (n : ℝ) ^ (-1 / 2 : ℝ))
      Filter.atTop Filter.atTop)
    (hB : ∀ᶠ n in Filter.atTop, K * S n ≤ B n) :
    Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (C / (gamma * n)) / B n)
      Filter.atTop (nhds 0) := by
  have hscale : ∀ᶠ n : ℕ in Filter.atTop,
      0 < (n : ℝ) ^ (-1 / 2 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    positivity
  have hratio : ∀ᶠ n : ℕ in Filter.atTop,
      0 < S n / (n : ℝ) ^ (-1 / 2 : ℝ) :=
    hS.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  have hSinv : Filter.Tendsto
      (fun n : ℕ ↦ (S n / (n : ℝ) ^ (-1 / 2 : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    (tendsto_inv_atTop_nhdsGT_zero.comp hS).mono_right inf_le_left
  have hupper : Filter.Tendsto
      (fun n : ℕ ↦ (Real.sqrt (C / gamma) / K) *
        (S n / (n : ℝ) ^ (-1 / 2 : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hSinv)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hscale, hratio, hB] with n hnscale hnratio hnB
    have hSpos : 0 < S n := (div_pos_iff.mp hnratio).elim
      (fun h ↦ h.1) (fun h ↦ False.elim ((not_lt_of_ge hnscale.le) h.2))
    have hBpos : 0 < B n := lt_of_lt_of_le (mul_pos hK hSpos) hnB
    exact div_nonneg (Real.sqrt_nonneg _) hBpos.le
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hscale, hratio, hB]
      with n hn hnscale hnratio hnB
    have hSpos : 0 < S n := (div_pos_iff.mp hnratio).elim
      (fun h ↦ h.1) (fun h ↦ False.elim ((not_lt_of_ge hnscale.le) h.2))
    rw [sqrt_div_nat_eq_scale C gamma n hC hgamma hn]
    have hnum : 0 ≤ Real.sqrt (C / gamma) * (n : ℝ) ^ (-1 / 2 : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) hnscale.le
    have hdiv : Real.sqrt (C / gamma) * (n : ℝ) ^ (-1 / 2 : ℝ) / B n ≤
        Real.sqrt (C / gamma) * (n : ℝ) ^ (-1 / 2 : ℝ) / (K * S n) :=
      div_le_div_of_nonneg_left hnum (mul_pos hK hSpos) hnB
    calc
      Real.sqrt (C / gamma) * (n : ℝ) ^ (-1 / 2 : ℝ) / B n
          ≤ Real.sqrt (C / gamma) * (n : ℝ) ^ (-1 / 2 : ℝ) /
              (K * S n) := hdiv
      _ = (Real.sqrt (C / gamma) / K) *
          (S n / (n : ℝ) ^ (-1 / 2 : ℝ))⁻¹ := by field_simp

/-- The paper's spectral estimator and the published finite-order ACE procedure
are put on a common footing, and the spectral guarantee eventually dominates.
[Fix an expansion order of at least two, a positive cumulant separation and
positive bounds on the treatment effect, the two regressions and the two
sub-Gaussian scales; then there is a positive constant, depending only on those
inputs, such that for any published order-`r` ACE procedure enjoying its cited
generalized-quantile guarantee at an overlap exponent strictly between one half
and one: the published ACE class is contained in the paper's non-Gaussian class
and contains the comparison subclass, and coincides with that subclass when the
smoothness index equals the expansion order; the published estimator's
generalized-quantile error over the published class is at most the cited
finite-order ACE bound; the spectral estimator's worst-case generalized-quantile
error over the same class is at most the square root of that constant divided by
the overlap exponent times the sample size; and along any sequence of parameter
blocks that keeps the fixed constants and whose ACE leading term outgrows the
parametric rate, the ratio of the spectral guarantee to the published bound
tends to zero](goal).

The last clause is the alignment payoff: on the shared class the parametric-rate
spectral guarantee is eventually smaller than the published bound by an
arbitrarily large factor. -/
-- @node: prop:jms-ace-alignment
theorem jms_ace_alignment
    : ∀ (r : ℕ) (delta Ctheta Cg Cq psieta psixi : ℝ),
      2 ≤ r → 0 < delta → 0 < Ctheta → 0 < Cg → 0 < Cq →
      0 < psieta → 0 < psixi →
      ∃ Cspec : ℝ, 0 < Cspec ∧
      ∀ {Xspace : Type u} [MeasurableSpace Xspace],
      ∀ (published : PublishedAceHandle Xspace),
      ∀ (gamma : ℝ), gamma ∈ Set.Ioo (1 / 2 : ℝ) 1 →
      ∀ Cgamma : ℝ,
      JmsAceQuantileUpper published gamma Cgamma →
      ∀ (p0 : Parameters), p0.r = r → p0.delta = delta →
        p0.Ctheta = Ctheta → p0.Cg = Cg → p0.Cq = Cq →
      p0.psieta = psieta → p0.psixi = psixi →
      p0.gamma = gamma →
      ∀ fixed : FixedExperimentRecords p0,
      ∀ (p : Parameters) (hfixed : SameFixedExperimentConstants p0 p),
        p.gamma = gamma →
        let pStarP := fixedBankInput fixed.bank hfixed
        let cStarP := fixedRangeInput fixed.range hfixed
        ∀ (gcode qcode : ℕ → Xspace → ℝ),
        (∀ m : Model (Xspace := Xspace) p,
          JmsAceClass p p.n m → NonGaussianClass p p.n m) ∧
        (∀ m : Model (Xspace := Xspace) p,
          AceComparisonSubclass p p.n m → JmsAceClass p p.n m) ∧
        (p.s = (p.r : ENNReal) →
          ∀ m : Model (Xspace := Xspace) p,
            (JmsAceClass p p.n m ↔ AceComparisonSubclass p p.n m)) ∧
        (∀ m : Model (Xspace := Xspace) p,
          barG p m p.n = clippedTreatmentCode p gcode p.n →
          barQ p m p.n = clippedOutcomeCode p qcode p.n →
          JmsAceClass p p.n m → jmsEligible p p.n →
          0 < p.eps1n p.n → 0 ≤ p.eps2n p.n →
          generalizedQuantile p p.n m
            (fun data ↦
              |published.estimator p.r p.n gcode qcode data - m.theta0|) ≤
                jmsBound p p.n Cgamma p.delta) ∧
        ((∃ m : Model (Xspace := Xspace) p,
            JmsAceClass p p.n m ∧
              barG p m p.n = clippedTreatmentCode p gcode p.n ∧
              barQ p m p.n = clippedOutcomeCode p qcode p.n) →
          2 ≤ p.n →
          jmsEligible p p.n →
          0 < p.eps1n p.n →
          p.eps1n p.n ≤ (4 * searchRadius p *
            Real.exp (2 * p.Cg * searchRadius p))⁻¹ →
          (⨆ m : Model (Xspace := Xspace) p,
            ⨆ (_ : JmsAceClass p p.n m ∧
              barG p m p.n = clippedTreatmentCode p gcode p.n ∧
              barQ p m p.n = clippedOutcomeCode p qcode p.n),
              ENNReal.ofReal (generalizedQuantile p p.n m
                (fun data ↦ |thetaHatSpec p pStarP cStarP gcode data -
                  m.theta0|))) ≤
                  ENNReal.ofReal (Real.sqrt (Cspec / (p.gamma * p.n)))) ∧
        (∀ (pSeq : ℕ → Parameters) (gcode qcode : ℕ → Xspace → ℝ),
          (∀ n, 1 ≤ n →
            (pSeq n).n = n ∧ SameFixedExperimentConstants p0 (pSeq n) ∧
            (pSeq n).eps1n = p0.eps1n ∧ (pSeq n).eps2n = p0.eps2n ∧
            (pSeq n).r = r ∧
            (pSeq n).delta = delta ∧ (pSeq n).Ctheta = Ctheta ∧
            (pSeq n).Cg = Cg ∧ (pSeq n).Cq = Cq ∧
            (pSeq n).psieta = psieta ∧ (pSeq n).psixi = psixi ∧
            (pSeq n).gamma = gamma) →
          (∀ᶠ n in Filter.atTop,
            2 ≤ n ∧ jmsEligible (pSeq n) n ∧
            0 < (pSeq n).eps1n n ∧ 0 ≤ (pSeq n).eps2n n ∧
            (pSeq n).eps1n n ≤ (4 * searchRadius (pSeq n) *
              Real.exp (2 * (pSeq n).Cg * searchRadius (pSeq n)))⁻¹ ∧
            (∃ m : Model (Xspace := Xspace) (pSeq n),
              JmsAceClass (pSeq n) n m ∧
                barG (pSeq n) m n = clippedTreatmentCode (pSeq n) gcode n ∧
                barQ (pSeq n) m n = clippedOutcomeCode (pSeq n) qcode n)) →
          Filter.Tendsto
            (fun n : ℕ ↦ ((pSeq n).eps1n n ^ r * (pSeq n).eps2n n +
              Ctheta * (pSeq n).eps1n n ^ (r + 1)) /
                (n : ℝ) ^ (-1 / 2 : ℝ)) Filter.atTop Filter.atTop →
          Filter.Tendsto
            (fun n : ℕ ↦ Real.sqrt (Cspec / (gamma * n)) /
              jmsBound (pSeq n) n Cgamma delta)
            Filter.atTop (nhds 0)) := by
  intro r delta Ctheta Cg Cq psieta psixi hr hdelta hCtheta hCg hCq
    hpsieta hpsixi
  obtain ⟨c, Cspec, hc, hCspec, hspectral⟩ :=
    adaptive_rootn_minimax r delta Ctheta Cg Cq psieta psixi hr hdelta
      hCtheta hCg hCq hpsieta hpsixi
  refine ⟨Cspec, hCspec, ?_⟩
  intro Xspace inst published gamma hgamma Cgamma hJms p0 hp0r hp0delta hp0Ctheta
    hp0Cg hp0Cq hp0psieta hp0psixi hp0gamma fixed
  have hspectralFixed :=
    hspectral (Xspace := Xspace) p0 hp0r hp0delta hp0Ctheta hp0Cg hp0Cq hp0psieta
      hp0psixi fixed
  intro p hfixed hpgamma
  dsimp
  intro gcode qcode
  have hrels := jms_ace_class_relations (Xspace := Xspace) p p.n
  refine ⟨hrels.1, hrels.2.1, hrels.2.2, ?_, ?_, ?_⟩
  · intro m hmg hmq hm hEligible heps1 heps2
    by_cases heps2pos : 0 < p.eps2n p.n
    · exact hJms.2 p hpgamma heps1 heps2pos gcode qcode m hmg hmq hm hEligible
    · have heps2zero : p.eps2n p.n = 0 :=
        le_antisymm (not_lt.mp heps2pos) heps2
      have hboundary :
          generalizedQuantile p p.n m
            (fun data ↦
              |published.estimator p.r p.n gcode qcode data - m.theta0|) ≤
                jmsBound p p.n Cgamma p.delta := by
        apply le_of_forall_gt_imp_ge_of_dense
        intro upper hupper
        let A : ℝ := Cgamma * p.r.factorial * 16 ^ p.r * p.delta⁻¹ *
          (p.eps1n p.n) ^ p.r
        have hA : 0 < A := by
          have hCgamma : 0 < Cgamma := hJms.1
          have hdelta : 0 < p.delta := p.constants_pos.2.2.2.2.2.1
          dsimp [A]
          positivity
        let t : ℝ := min (p.eps1n p.n / 2)
          ((upper - jmsBound p p.n Cgamma p.delta) / (2 * A))
        have ht : 0 < t := by
          have hgap : 0 < upper - jmsBound p p.n Cgamma p.delta :=
            sub_pos.mpr hupper
          dsimp [t]
          positivity
        have ht_lt_eps1 : t < p.eps1n p.n := by
          calc
            t ≤ p.eps1n p.n / 2 := min_le_left _ _
            _ < p.eps1n p.n := by linarith
        let p' := p.withEps2Floor t
        let m' : Model (Xspace := Xspace) p' := m.reparam p'
        have hp'gamma : p'.gamma = gamma := hpgamma
        have hp'eps1 : 0 < p'.eps1n p'.n := heps1
        have hp'eps2 : 0 < p'.eps2n p'.n := by
          simp [p', Parameters.withEps2Floor, heps2zero, ht]
        have hm' : JmsAceClass p' p'.n m' := by
          refine {
            n_pos := hm.n_pos
            independentTreatmentNoise := ?_
            outcomeMeanIndependence := ?_
            thetaRange := ?_
            gRange := ?_
            qRange := ?_
            etaSubGaussian := ?_
            xiSubGaussian := ?_
            cumulantSeparation := ?_
            treatmentCodeRadiusLr := ?_
            outcomeCodeRadiusLr := ?_ }
          all_goals try first
            | exact hm.independentTreatmentNoise
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.independentTreatmentNoise
          all_goals try first
            | exact hm.outcomeMeanIndependence
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.outcomeMeanIndependence
          all_goals try first
            | exact hm.thetaRange
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.thetaRange
          all_goals try first
            | exact hm.gRange
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.gRange
          all_goals try first
            | exact hm.qRange
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.qRange
          all_goals try first
            | exact hm.etaSubGaussian
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.etaSubGaussian
          all_goals try first
            | exact hm.xiSubGaussian
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.xiSubGaussian
          all_goals try first
            | exact hm.cumulantSeparation
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.cumulantSeparation
          all_goals try first
            | exact hm.treatmentCodeRadiusLr
            | simpa [p', m', Parameters.withEps2Floor, Model.reparam] using
                hm.treatmentCodeRadiusLr
          unfold OutcomeCodeRadiusLrAt
          have hbase : MeasureTheory.eLpNorm
              (fun x ↦ barQ p' m' p'.n x - m'.q0 x) (p'.r : ENNReal)
              (covariateLaw p' m') ≤ ENNReal.ofReal (p.eps2n p.n) := by
            exact hm.outcomeCodeRadiusLr
          exact hbase.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        have hEligible' : jmsEligible p' p'.n := by
          have hmax (x : ℝ) :
              max (p.eps1n p.n) (max (max 0 t) x) =
                max (p.eps1n p.n) (max 0 x) := by
            rw [max_eq_right ht.le, ← max_assoc, max_eq_left ht_lt_eps1.le,
              ← max_assoc, max_eq_left heps1.le]
          simpa [jmsEligible, jmsEligibleAt, jmsA1, jmsB1, jmsA2, jmsB2,
            p', Parameters.withEps2Floor, heps2zero, hmax] using hEligible
        have hbound := hJms.2 p' hp'gamma hp'eps1 hp'eps2 gcode qcode m'
          (by exact hmg) (by exact hmq) hm' hEligible'
        have hquantile : generalizedQuantile p p.n m
            (fun data ↦
              |published.estimator p.r p.n gcode qcode data - m.theta0|) =
            generalizedQuantile p' p'.n m'
            (fun data ↦
              |published.estimator p'.r p'.n gcode qcode data - m'.theta0|) := by
          rfl
        rw [hquantile]
        exact hbound.trans (by
          have ht_gap : t ≤
              (upper - jmsBound p p.n Cgamma p.delta) / (2 * A) := by
            exact min_le_right _ _
          have hAt : A * t ≤
              (upper - jmsBound p p.n Cgamma p.delta) / 2 := by
            calc
              A * t ≤ A *
                  ((upper - jmsBound p p.n Cgamma p.delta) / (2 * A)) :=
                mul_le_mul_of_nonneg_left ht_gap hA.le
              _ = (upper - jmsBound p p.n Cgamma p.delta) / 2 := by
                field_simp [hA.ne']
          have hbound_eq : jmsBound p' p'.n Cgamma p'.delta =
              jmsBound p p.n Cgamma p.delta + A * t := by
            dsimp [jmsBound, p', Parameters.withEps2Floor, A]
            rw [heps2zero, max_eq_right ht.le]
            ring
          rw [hbound_eq]
          linarith)
      exact hboundary
  · rintro ⟨m, hm, hmg, hmq⟩ hn _hEligible _heps1 heps
    have hgclip : clippedTreatmentCode p gcode p.n =
        clippedTreatmentCode p m.gcode p.n := by
      exact hmg.symm
    have hqclip : clippedOutcomeCode p qcode p.n =
        clippedOutcomeCode p m.qcode p.n := by
      exact hmq.symm
    have htheta :
        (thetaHatSpec p (fixedBankInput fixed.bank hfixed)
            (fixedRangeInput fixed.range hfixed) gcode :
          (Fin p.n → Obs Xspace) → ℝ) =
        thetaHatSpec p (fixedBankInput fixed.bank hfixed)
          (fixedRangeInput fixed.range hfixed) m.gcode := by
      apply thetaHatSpec_congr_current
      exact fun x ↦ congrFun hgclip x
    have hall := hspectralFixed p hfixed m
    have hace := hall.2.2.2.2.2
    dsimp at hace
    have hbound := (hace ⟨m, hm, rfl, rfl⟩ hn heps).2.2.2
    rw [hgclip, hqclip, htheta]
    exact hbound
  · intro pSeq gcode' qcode' hseq hevent hdom
    let S : ℕ → ℝ := fun n ↦
      (pSeq n).eps1n n ^ r * (pSeq n).eps2n n +
        Ctheta * (pSeq n).eps1n n ^ (r + 1)
    let K : ℝ := Cgamma * r.factorial * 16 ^ r * delta⁻¹
    apply tendsto_sqrt_div_over_of_dominates Cspec gamma K S
      (fun n ↦ jmsBound (pSeq n) n Cgamma delta)
      (le_of_lt hCspec) (by linarith [hgamma.1])
    · dsimp [K]
      have hfac : 0 < (r.factorial : ℝ) := by positivity
      exact mul_pos (mul_pos (mul_pos hJms.1 hfac) (by positivity)) (inv_pos.mpr hdelta)
    · simpa [S] using hdom
    · filter_upwards [hevent] with n hn
      rcases hn with ⟨hn2, _heligible, heps1, heps2, _hsmall, _hmodel⟩
      rcases hseq n (by omega) with
        ⟨hpnn, _hfixedn, _heps1n, _heps2n, hpr, hpdelta, hpCtheta, hpCg, _hpCq,
          hppsieta, hppsixi, hpgamma⟩
      dsimp [K, S, jmsBound]
      rw [hpr, hpCtheta]
      apply mul_le_mul_of_nonneg_left
      · apply le_add_of_nonneg_right
        rw [hpCg, hppsieta, hppsixi, hpgamma]
        have hbase : 0 ≤ Cg + psieta := (add_pos hCg hpsieta).le
        have hpow : 0 ≤ (Cg + psieta) ^ r := pow_nonneg hbase r
        have hinner : 0 ≤
            (r : ℝ) ^ 2 * (Cg + psieta) + psixi + Ctheta * psieta := by
          positivity
        have hgamma0 : 0 < gamma := by linarith [hgamma.1]
        have hscale : 0 ≤ (gamma * (n : ℝ)) ^ (-1 / 2 : ℝ) :=
          Real.rpow_nonneg (x := gamma * (n : ℝ))
            (mul_nonneg hgamma0.le (Nat.cast_nonneg n)) _
        exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hpow) hinner) hscale
      · have hfac : 0 < (r.factorial : ℝ) := by positivity
        exact (mul_pos (mul_pos (mul_pos hJms.1 hfac) (by positivity))
          (inv_pos.mpr hdelta)).le

end CausalSmith.Stat.SaPlmCumulantConverse
