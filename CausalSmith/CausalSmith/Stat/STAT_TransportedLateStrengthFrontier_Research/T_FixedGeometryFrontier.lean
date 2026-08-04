/-
# Fixed-geometry expected-length frontier
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_CompactCausalRange
import Causalean.Stat.Minimax.ChiSquared
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Stat.Minimax.Scheffe
import Causalean.Stat.Sample.EffectiveSampleSize

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

set_option maxHeartbeats 1000000

-- @node: thm:fixed-geometry-frontier
/-- For every admissible deterministic geometry, the conditional honest
expected-length frontier has order `min(1,t0⁻¹/²)`, with constants independent
of the geometry. -/
theorem fixed_geometry_frontier
    (N k : ℕ → ℕ) (c epsilon alpha : ℝ) (g : Geometry 𝒳)
    (hc : 0 < c) -- @realizes c(c∈(0,∞))
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
      -- @realizes N_n(N_n/n→c)
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ =>
      (k n : ℝ) / Real.sqrt n) atTop (𝓝 0))
      -- @realizes k_n(positive, diverging, and o(√n))
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hg : AdmissibleGeometry g k epsilon)
    (hTwo : ∀ n P, fixedGeometrySlice P g N k c epsilon n →
      TwoSampleArray P N c)
    (hOverlap : ∀ n P, fixedGeometrySlice P g N k c epsilon n →
      InstrumentOverlap P n epsilon)
    (hEnvelope : ∀ n P, fixedGeometrySlice P g N k c epsilon n →
      WeightEnvelope P k n)
    (hSecond : ∀ n P, fixedGeometrySlice P g N k c epsilon n →
      WeightSecondMoment P k n)
    (hDegrade : ∀ n P, fixedGeometrySlice P g N k c epsilon n →
      DegradingArray P k)
    (hAlpha : 0 < alpha ∧ alpha < 1) :
      -- @realizes \alpha(noncoverage in (0,1))
    ∀ (t0 : ℝ) (ht0 : 0 < t0), -- @realizes t_0(positive frontier threshold)
      let Lalpha := Real.sqrt (8 / (alpha * epsilon ^ 2))
      let calpha := 3 * (1 - alpha) ^ 2 / 16
      let Calpha := max 2 (4 * Lalpha + 8 / epsilon ^ 2)
      calpha * min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        fixedGeometryValue N k c epsilon alpha ⟨g, hg⟩ ⟨t0, ht0⟩ ∧
      fixedGeometryValue N k c epsilon alpha ⟨g, hg⟩ ⟨t0, ht0⟩ ≤
        Calpha * min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  intro t0 ht0
  have hSlice :=
    fixedGeometrySlice_eventually_inhabited g N k c epsilon t0 hc
      hepsilon ht0 hg hN hkPos hkInf hkRoot
  refine ⟨?_, ?_⟩
  · classical
    let rho : ℝ := (1 - alpha) / 8
    let H : ℝ := min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ))
    have hrho : rho = (1 - alpha) / 8 := rfl
    have hrhoPos : 0 < rho := by
      unfold rho
      exact div_pos (sub_pos.mpr hAlpha.2) (by norm_num)
    have hrpowPos : 0 < t0 ^ (-1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos ht0 _
    have hHpos : 0 < H := by
      unfold H
      exact lt_min (by norm_num) (mul_pos hrhoPos hrpowPos)
    have hHandle :=
      geometryHandle_eventually_inhabited g N k c epsilon alpha t0 rho
        hc hepsilon hAlpha ht0 hrho hg hN hkPos hkInf hkRoot
    have hRiskLower : ∀ D : OracleProcedure 𝒳 N k c epsilon,
        FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ D →
          2 * H * (1 - alpha - 2 * rho) ≤
            fixedGeometryRisk N k c epsilon g D t0 := by
      intro D hD
      let covRow : ℕ → ℝ := fun n =>
        ⨅ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n},
          fixedGeometryOracleCoverage D g P n
      let riskRow : ℕ → ℝ := fun n =>
        ⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength D g P n
      have hcoverageRange : ∀ n P,
          fixedGeometrySlice P g N k c epsilon n →
            0 ≤ fixedGeometryOracleCoverage D g P n ∧
              fixedGeometryOracleCoverage D g P n ≤ 1 := by
        intro n P hP
        letI : IsProbabilityMeasure (sourceObsLaw P n) :=
          hP.1.twoSampleArray.2.1 n
        letI : IsProbabilityMeasure (targetXLaw P n) :=
          hP.1.twoSampleArray.2.2.1 n
        letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
          unfold twoSampleLaw
          infer_instance
        exact ⟨ENNReal.toReal_nonneg, by
          simpa [fixedGeometryOracleCoverage, Measure.real] using
            (measureReal_le_one (μ := twoSampleLaw P N n))⟩
      have hcovNonneg : ∀ n, 0 ≤ covRow n := by
        intro n
        let I := {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n}
        cases isEmpty_or_nonempty I with
        | inl hEmpty =>
            letI : IsEmpty I := hEmpty
            simp [covRow, I]
        | inr hNonempty =>
            letI : Nonempty I := hNonempty
            apply le_ciInf
            intro P
            exact (hcoverageRange n P P.2).1
      have hcovOne : ∀ n, covRow n ≤ 1 := by
        intro n
        let I := {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n}
        cases isEmpty_or_nonempty I with
        | inl hEmpty =>
            letI : IsEmpty I := hEmpty
            simp [covRow, I]
        | inr hNonempty =>
            letI : Nonempty I := hNonempty
            let P : I := Classical.choice hNonempty
            have hbdd : BddBelow (Set.range fun Q : I =>
                fixedGeometryOracleCoverage D g Q n) :=
              ⟨0, by
                rintro y ⟨Q, rfl⟩
                exact (hcoverageRange n Q Q.2).1⟩
            exact (ciInf_le hbdd P).trans
              (hcoverageRange n P P.2).2
      have hsetLengthTwo : ∀ A : Set ℝ, setLength A ≤ 2 := by
        intro A
        unfold setLength parameterSpace
        calc
          (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
              (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
            ENNReal.toReal_mono (by simp [Real.volume_Icc])
              (measure_mono Set.inter_subset_right)
          _ = 2 := by
            rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
            norm_num
      have hExpectedTwo : ∀ n P,
          fixedGeometrySlice P g N k c epsilon n →
            fixedGeometryOracleExpectedLength D g P n ≤ 2 := by
        intro n P hP
        letI : IsProbabilityMeasure (sourceObsLaw P n) :=
          hP.1.twoSampleArray.2.1 n
        letI : IsProbabilityMeasure (targetXLaw P n) :=
          hP.1.twoSampleArray.2.2.1 n
        letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
          unfold twoSampleLaw
          infer_instance
        exact (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
          (integrable_const 2)
          (Filter.Eventually.of_forall fun s =>
            hsetLengthTwo (fixedGeometryOracleSet D g n s))).trans_eq (by simp)
      have hriskNonneg : ∀ n, 0 ≤ riskRow n := by
        intro n
        let I := {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n}
        cases isEmpty_or_nonempty I with
        | inl hEmpty =>
            letI : IsEmpty I := hEmpty
            simp [riskRow, I]
        | inr hNonempty =>
            letI : Nonempty I := hNonempty
            let P : I := Classical.choice hNonempty
            have hbdd : BddAbove (Set.range fun Q : I =>
                fixedGeometryOracleExpectedLength D g Q n) :=
              ⟨2, by
                rintro y ⟨Q, rfl⟩
                exact hExpectedTwo n Q Q.2.1⟩
            exact (integral_nonneg fun _ => ENNReal.toReal_nonneg).trans
              (le_ciSup hbdd P)
      have hriskTwo : ∀ n, riskRow n ≤ 2 := by
        intro n
        let I := {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n}
        cases isEmpty_or_nonempty I with
        | inl hEmpty =>
            letI : IsEmpty I := hEmpty
            simp [riskRow, I]
        | inr hNonempty =>
            letI : Nonempty I := hNonempty
            apply ciSup_le
            intro P
            exact hExpectedTwo n P P.2.1
      have hpoint : ∀ᶠ n in atTop,
          2 * H * (covRow n - 2 * rho) ≤ riskRow n := by
        filter_upwards [hHandle] with n hn
        rcases hn with
          ⟨_hg, _ha0, _ha1, _ht, _hr, _hcomp, _hfirst, _hstrength,
            Q, hQ, _hchi, hTV⟩
        let I : Set ℝ := Set.Icc (1 / 2 - H) (1 / 2 + H)
        have hHle : H ≤ 1 / 4 := by
          exact min_le_left _ _
        have hI : MeasurableSet I := measurableSet_Icc
        have hIsub : I ⊆ parameterSpace := by
          intro u hu
          change -1 ≤ u ∧ u ≤ 1
          change 1 / 2 - H ≤ u ∧ u ≤ 1 / 2 + H at hu
          constructor <;> linarith
        have hshift (u : ℝ) (hu : u ∈ I) :
            |u - 1 / 2| ≤ H := by
          change 1 / 2 - H ≤ u ∧ u ≤ 1 / 2 + H at hu
          rw [abs_le]
          constructor <;> linarith
        have hu0 (u : ℝ) (hu : u ∈ I) : u ≠ 0 := by
          change 1 / 2 - H ≤ u ∧ u ≤ 1 / 2 + H at hu
          intro hueq
          subst u
          linarith
        have hwitness (u : ℝ) (hu : u ∈ I) :=
          hQ (u - 1 / 2) (hshift u hu)
        have hslice (u : ℝ) (hu : u ∈ I) :
            fixedGeometrySlice (Q (u - 1 / 2)) g N k c epsilon n :=
          (hwitness u hu).2.2.2.2.2.2.1
        have htarget (u : ℝ) (hu : u ∈ I) :
            targetCACE (Q (u - 1 / 2)) n = u := by
          have h :=
            (hwitness u hu).2.2.2.2.2.2.2.2.2.2.1
          linarith
        have hprobLocal (u : ℝ) (hu : u ∈ I) :
            IsProbabilityMeasure
              (twoSampleLaw (Q (u - 1 / 2)) N n) := by
          letI : IsProbabilityMeasure
              (sourceObsLaw (Q (u - 1 / 2)) n) :=
            (hslice u hu).1.twoSampleArray.2.1 n
          letI : IsProbabilityMeasure
              (targetXLaw (Q (u - 1 / 2)) n) :=
            (hslice u hu).1.twoSampleArray.2.2.1 n
          unfold twoSampleLaw
          infer_instance
        have hzero : |(0 : ℝ)| ≤ H := by
          simpa using hHpos.le
        have hwitnessZero := hQ 0 hzero
        have hsliceZero :
            fixedGeometrySlice (Q 0) g N k c epsilon n :=
          hwitnessZero.2.2.2.2.2.2.1
        have hstrengthZero : effectiveStrength (Q 0) n = t0 :=
          hwitnessZero.2.2.2.2.2.2.2.2.2.1
        have hprobZero :
            IsProbabilityMeasure (twoSampleLaw (Q 0) N n) := by
          letI : IsProbabilityMeasure (sourceObsLaw (Q 0) n) :=
            hsliceZero.1.twoSampleArray.2.1 n
          letI : IsProbabilityMeasure (targetXLaw (Q 0) n) :=
            hsliceZero.1.twoSampleArray.2.2.1 n
          unfold twoSampleLaw
          infer_instance
        let Qm : ℝ → Measure (TwoSample 𝒳 n (N n)) := fun u =>
          if u = 0 then twoSampleLaw (Q 0) N n
          else if u ∈ I then twoSampleLaw (Q (u - 1 / 2)) N n
          else twoSampleLaw (Q 0) N n
        have hQmProb : ∀ u, IsProbabilityMeasure (Qm u) := by
          intro u
          by_cases hz : u = 0
          · simpa [Qm, hz] using hprobZero
          by_cases hu : u ∈ I
          · simpa [Qm, hz, hu] using hprobLocal u hu
          · simpa [Qm, hz, hu] using hprobZero
        let Cset : TwoSample 𝒳 n (N n) → Set ℝ := fun s =>
          fixedGeometryOracleSet D g n s
        have hgwNonneg : ∀ x, 0 ≤ g.weight n x :=
          fun x => (hg.2.2.2.2.2.1 n x).1
        have hgwEq :
            (geometryWeightInput g n : 𝒳 → ℝ) = g.weight n := by
          simp [geometryWeightInput, hgwNonneg]
        have hgraph : MeasurableSet
            {p : TwoSample 𝒳 n (N n) × ℝ | p.2 ∈ Cset p.1} := by
          simpa [Cset, fixedGeometryOracleSet] using
            D.measurableGraph n (geometryWeightInput g n) (g.propensity n)
              (by simpa [hgwEq] using g.weight_measurable n)
              (g.propensity_measurable n)
        have hsub : ∀ s, Cset s ⊆ parameterSpace := by
          intro s
          exact D.subset n (s, geometryWeightInput g n, g.propensity n)
        have hcover : ∀ u ∈ I,
            covRow n ≤ (Qm u {s | u ∈ Cset s}).toReal := by
          intro u hu
          have hbdd : BddBelow (Set.range fun P :
              {P : TransportedArray 𝒳 //
                fixedGeometrySlice P g N k c epsilon n} =>
                fixedGeometryOracleCoverage D g P n) :=
            ⟨0, by
              rintro y ⟨P, rfl⟩
              exact (hcoverageRange n P P.2).1⟩
          have hrow := ciInf_le hbdd
            (⟨Q (u - 1 / 2), hslice u hu⟩ :
              {P : TransportedArray 𝒳 //
                fixedGeometrySlice P g N k c epsilon n})
          have hQmu :
              Qm u = twoSampleLaw (Q (u - 1 / 2)) N n := by
            simp [Qm, hu0 u hu, hu]
          rw [hQmu]
          change covRow n ≤
            (twoSampleLaw (Q (u - 1 / 2)) N n
              {s | u ∈ fixedGeometryOracleSet D g n s}).toReal
          have hevent :
              {s : TwoSample 𝒳 n (N n) |
                u ∈ fixedGeometryOracleSet D g n s} =
              {s : TwoSample 𝒳 n (N n) |
                targetCACE (Q (u - 1 / 2)) n ∈
                  fixedGeometryOracleSet D g n s} := by
            ext s
            rw [htarget u hu]
          rw [hevent]
          simpa [covRow, fixedGeometryOracleCoverage] using hrow
        have htv : ∀ u ∈ I,
            Causalean.Stat.tvDist (Qm u) (Qm 0) ≤ 2 * rho := by
          intro u hu
          simpa [Qm, hu0 u hu, hu] using
            hTV (u - 1 / 2) (hshift u hu)
        have hexpected :=
          coverage_tv_expectedLength_lower Qm Cset I
            (covRow n) (2 * rho) hQmProb hcover htv hgraph hsub
            hI hIsub
        have hvol : (volume I).toReal = 2 * H := by
          simp [I, Real.volume_Icc, hHpos.le]
          ring
        have hcenter :
            2 * H * (covRow n - 2 * rho) ≤
              fixedGeometryOracleExpectedLength D g (Q 0) n := by
          simpa [hvol, Qm, Cset,
            fixedGeometryOracleExpectedLength] using hexpected
        let P0 : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} :=
          ⟨Q 0, hsliceZero, hstrengthZero.ge⟩
        have hbdd : BddAbove (Set.range fun P :
            {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n} =>
              fixedGeometryOracleExpectedLength D g P n) :=
          ⟨2, by
            rintro y ⟨P, rfl⟩
            exact hExpectedTwo n P P.2.1⟩
        exact hcenter.trans (le_ciSup hbdd P0)
      let f : ℝ → ℝ := fun x => 2 * H * (x - 2 * rho)
      have hfmono : Monotone f := by
        intro x y hxy
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_right hxy _) (mul_nonneg (by norm_num) hHpos.le)
      have hcovCobounded :
          IsCoboundedUnder (· ≥ ·) atTop covRow := by
        change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ covRow n) → a ≤ b
        refine ⟨1, fun a ha => ?_⟩
        obtain ⟨n, han, hn1⟩ :=
          (ha.and (Filter.Eventually.of_forall hcovOne)).exists
        exact han.trans hn1
      have hcovBounded :
          IsBoundedUnder (· ≥ ·) atTop covRow := by
        change ∃ b, ∀ᶠ n in atTop, b ≤ covRow n
        exact ⟨0, Filter.Eventually.of_forall hcovNonneg⟩
      have hmap :
          f (Filter.liminf covRow atTop) =
            Filter.liminf (f ∘ covRow) atTop :=
        hfmono.map_liminf_of_continuousAt covRow
          (by fun_prop) hcovCobounded hcovBounded
      have hhonest :
          1 - alpha ≤ Filter.liminf covRow atTop := by
        have hrows : ∀ᶠ n in atTop,
            coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n} =>
                fixedGeometryOracleCoverage D g P n) = covRow n := by
          filter_upwards [hSlice] with n hn
          letI : Nonempty {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n} :=
            ⟨⟨hn.choose, hn.choose_spec.1⟩⟩
          simp [covRow, coverageInfOrOne_of_nonempty]
        exact hD.2.2.trans_eq (Filter.liminf_congr hrows)
      have hbase :
          f (1 - alpha) ≤ Filter.liminf (f ∘ covRow) atTop := by
        rw [← hmap]
        exact hfmono hhonest
      have hfBounded :
          IsBoundedUnder (· ≥ ·) atTop (f ∘ covRow) := by
        change ∃ b, ∀ᶠ n in atTop, b ≤ f (covRow n)
        exact ⟨f 0, Filter.Eventually.of_forall fun n =>
          hfmono (hcovNonneg n)⟩
      have hriskCobounded :
          IsCoboundedUnder (· ≥ ·) atTop riskRow := by
        change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ riskRow n) → a ≤ b
        refine ⟨2, fun a ha => ?_⟩
        obtain ⟨n, han, hn2⟩ :=
          (ha.and (Filter.Eventually.of_forall hriskTwo)).exists
        exact han.trans hn2
      have hliminf :
          Filter.liminf (f ∘ covRow) atTop ≤
            Filter.liminf riskRow atTop :=
        Filter.liminf_le_liminf
          (by simpa [Function.comp_def, f] using hpoint)
          hfBounded hriskCobounded
      have hriskBoundedAbove :
          IsBoundedUnder (· ≤ ·) atTop riskRow := by
        change ∃ b, ∀ᶠ n in atTop, riskRow n ≤ b
        exact ⟨2, Filter.Eventually.of_forall hriskTwo⟩
      have hriskBoundedBelow :
          IsBoundedUnder (· ≥ ·) atTop riskRow := by
        change ∃ b, ∀ᶠ n in atTop, b ≤ riskRow n
        exact ⟨0, Filter.Eventually.of_forall hriskNonneg⟩
      have hlimsup :
          Filter.liminf riskRow atTop ≤ Filter.limsup riskRow atTop :=
        Filter.liminf_le_limsup hriskBoundedAbove hriskBoundedBelow
      change 2 * H * (1 - alpha - 2 * rho) ≤
        Filter.limsup riskRow atTop
      exact hbase.trans (hliminf.trans hlimsup)
    have harith :
        3 * (1 - alpha) ^ 2 / 16 *
            min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
          2 * H * (1 - alpha - 2 * rho) := by
      have hcoef : 0 ≤ 3 * (1 - alpha) ^ 2 / 16 := by
        positivity
      by_cases hsmall :
          rho * t0 ^ (-1 / 2 : ℝ) ≤ 1 / 4
      · calc
          3 * (1 - alpha) ^ 2 / 16 *
                min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
              3 * (1 - alpha) ^ 2 / 16 *
                t0 ^ (-1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hcoef
          _ = 2 * H * (1 - alpha - 2 * rho) := by
            simp [H, min_eq_right hsmall, rho]
            ring
      · have hlarge :
            1 / 4 ≤ rho * t0 ^ (-1 / 2 : ℝ) :=
          le_of_not_ge hsmall
        calc
          3 * (1 - alpha) ^ 2 / 16 *
                min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
              3 * (1 - alpha) ^ 2 / 16 :=
            (mul_le_mul_of_nonneg_left (min_le_left _ _) hcoef).trans_eq
              (mul_one _)
          _ ≤ 2 * H * (1 - alpha - 2 * rho) := by
            simp [H, min_eq_left hlarge, rho]
            nlinarith [sq_nonneg (1 - alpha)]
    let Dfull : OracleProcedure 𝒳 N k c epsilon :=
      { set := fun _ _ => parameterSpace
        subset := by
          intro _ _ _ h
          exact h
        measurableGraph := by
          intro _ _ _ _ _
          exact measurableSet_Icc.preimage measurable_snd
        weightAEInvariant := by
          intro _ _ _ _ _
          exact Filter.Eventually.of_forall (fun _ => rfl) }
    have hfullCoverage : ∀ n P,
        fixedGeometrySlice P g N k c epsilon n →
          fixedGeometryOracleCoverage Dfull g P n = 1 := by
      intro n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      have htheta : targetCACE P n ∈ parameterSpace :=
        (scoreRiskClass_compact_causal_range
          (fixedGeometryScoreRiskAtoms g N k c epsilon) hP).2.2.2.2.2
      simp [fixedGeometryOracleCoverage, fixedGeometryOracleSet,
        Dfull, htheta]
    have hInhab : ∀ᶠ n in atTop, ∃ P,
        fixedGeometrySlice P g N k c epsilon n := by
      filter_upwards [hSlice] with n hn
      exact ⟨hn.choose, hn.choose_spec.1⟩
    have hDfullHonest :
        FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ Dfull := by
      refine ⟨hAlpha.1, hAlpha.2, ?_⟩
      have hraw : 1 - alpha ≤ Filter.liminf
          (fun n => ⨅ P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n},
            fixedGeometryOracleCoverage Dfull g P n) atTop := by
        apply abstractClass_coverage_liminf
          (fun n P => fixedGeometrySlice P g N k c epsilon n)
          (fun n P => fixedGeometryOracleCoverage Dfull g P n)
          alpha (fun _ => 0) tendsto_const_nhds hInhab
        · intro n P hP
          rw [hfullCoverage n P hP]
          exact ⟨by norm_num, by norm_num⟩
        · intro n P hP
          rw [hfullCoverage n P hP]
          linarith [hAlpha.1]
      have hrows : ∀ᶠ n in atTop,
          coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} =>
              fixedGeometryOracleCoverage Dfull g P n) =
            (⨅ P : {P : TransportedArray 𝒳 //
                fixedGeometrySlice P g N k c epsilon n},
              fixedGeometryOracleCoverage Dfull g P n) := by
        filter_upwards [hInhab] with n hn
        letI : Nonempty {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} :=
          ⟨⟨hn.choose, hn.choose_spec⟩⟩
        exact coverageInfOrOne_of_nonempty _
      exact hraw.trans_eq (Filter.liminf_congr hrows).symm
    letI : Nonempty {D : OracleProcedure 𝒳 N k c epsilon //
        FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ D} :=
      ⟨⟨Dfull, hDfullHonest⟩⟩
    unfold fixedGeometryValue fixedGeometryValueTotal
    apply le_ciInf
    intro D
    exact harith.trans (hRiskLower D D.2)
  · classical
    let L : ℝ := Real.sqrt (8 / (alpha * epsilon ^ 2))
    let wG : ℕ → 𝒳 → ℝ := fun n x =>
      ((g.targetX n).rnDeriv (g.sourceX n) x).toReal
    have hwG : ∀ n, Measurable (wG n) := fun n =>
      (Measure.measurable_rnDeriv (g.targetX n) (g.sourceX n)).ennreal_toReal
    let C : OracleProcedure 𝒳 N k c epsilon :=
      { set := fun n x =>
          if n = 0 then ∅
          else inversionHandle (wG n) (g.propensity n) n L x.1.1
        subset := by
          intro n x theta htheta
          split at htheta
          · exact htheta.elim
          · exact htheta.1
        measurableGraph := by
          intro n _w _e _hw _he
          by_cases hn : n = 0
          · simp [hn]
          have hscore : Measurable (oracleInstrumentScore (g.propensity n)) := by
            have he : Measurable (fun o : SourceObs 𝒳 =>
                g.propensity n o.1) :=
              (g.propensity_measurable n).comp measurable_fst
            unfold oracleInstrumentScore
            exact Measurable.ite (by measurability)
              (measurable_const.div he)
              (measurable_const.neg.div (measurable_const.sub he))
          have hA : Measurable (fun s : SourceSample 𝒳 n =>
              scoreOutcomeMean (wG n) (g.propensity n) n s) := by
            unfold scoreOutcomeMean
            fun_prop
          have hB : Measurable (fun s : SourceSample 𝒳 n =>
              scoreReceiptMean (wG n) (g.propensity n) n s) := by
            unfold scoreReceiptMean
            fun_prop
          have hK : Measurable (fun s : SourceSample 𝒳 n =>
              empiricalKish (wG n) n s) := by
            unfold empiricalKish Causalean.Stat.empiricalKishDispersion
            fun_prop
          simp only [hn, ↓reduceIte]
          unfold inversionHandle
          refine (measurableSet_Icc.preimage measurable_snd).inter ?_
          exact measurableSet_le
            ((hA.comp (measurable_fst.fst)).sub
              (measurable_snd.mul
                (hB.comp (measurable_fst.fst)))).abs
            (measurable_const.mul
              ((hK.comp (measurable_fst.fst)).div measurable_const).sqrt)
        weightAEInvariant := by
          intro _ _ _ _ _
          exact Filter.Eventually.of_forall (fun _ => rfl) }
    have atoms :=
      fixedGeometryScoreRiskAtoms (𝒳 := 𝒳) g N k c epsilon
    have pullout
        (P : TransportedArray 𝒳) (n : ℕ)
        (F : SourceObs 𝒳 → ℝ) (d w : 𝒳 → ℝ)
        (hprob : IsProbabilityMeasure (sourceObsLaw P n))
        (hF : Integrable F (sourceObsLaw P n))
        (hd : Integrable d (sourceXLaw P n))
        (hdmeas : Measurable d)
        (hw : Measurable w)
        (hWF : Integrable (fun o => w o.1 * F o) (sourceObsLaw P n))
        (hwd : Integrable (fun x => w x * d x) (sourceXLaw P n))
        (hset : ∀ A, MeasurableSet A →
          ∫ o in {o | o.1 ∈ A}, F o ∂sourceObsLaw P n =
            ∫ x in A, d x ∂sourceXLaw P n) :
        (∫ o, w o.1 * F o ∂sourceObsLaw P n) =
          ∫ x, w x * d x ∂sourceXLaw P n := by
      let m0 : MeasurableSpace (SourceObs 𝒳) := inferInstance
      let mX : MeasurableSpace (SourceObs 𝒳) :=
        MeasurableSpace.comap (fun o => o.1)
          (inferInstance : MeasurableSpace 𝒳)
      letI : MeasurableSpace (SourceObs 𝒳) := m0
      letI : IsProbabilityMeasure (sourceObsLaw P n) := hprob
      have hfst :
          @Measurable (SourceObs 𝒳) 𝒳 m0 inferInstance (fun o => o.1) :=
        measurable_fst
      have hm : mX ≤ m0 :=
        hfst.comap_le
      have hfstM :
          @Measurable (SourceObs 𝒳) 𝒳 mX inferInstance (fun o => o.1) := by
        intro A hA
        exact MeasurableSpace.measurableSet_comap.mpr ⟨A, hA, rfl⟩
      have hdcomp : Integrable (fun o => d o.1) (sourceObsLaw P n) := by
        have hdmap : Integrable d
            (Measure.map (fun o : SourceObs 𝒳 => o.1) (sourceObsLaw P n)) := by
          simpa [sourceXLaw] using hd
        simpa [Function.comp_def] using
          (integrable_map_measure hdmap.1 hfst.aemeasurable).mp hdmap
      have hcond : (fun o => d o.1) =ᵐ[sourceObsLaw P n]
          (sourceObsLaw P n)[F | mX] := by
        refine ae_eq_condExp_of_forall_setIntegral_eq
          (μ := sourceObsLaw P n) (f := F) (g := fun o => d o.1)
          hm hF ?_ ?_ ?_
        · intro s hs _hfin
          exact hdcomp.integrableOn
        · intro s hs _hfin
          rcases MeasurableSpace.measurableSet_comap.mp hs with
            ⟨A, hA, rfl⟩
          calc
            (∫ x in (fun o : SourceObs 𝒳 => o.1) ⁻¹' A,
                d x.1 ∂sourceObsLaw P n) =
                ∫ x in A, d x ∂sourceXLaw P n := by
              rw [sourceXLaw]
              exact (setIntegral_map hA hd.1 hfst.aemeasurable).symm
            _ = ∫ x in (fun o : SourceObs 𝒳 => o.1) ⁻¹' A,
                F x ∂sourceObsLaw P n := (hset A hA).symm
        · exact (hdmeas.comp hfstM).aestronglyMeasurable
      have hwM : @StronglyMeasurable (SourceObs 𝒳) ℝ _ mX
          (fun o => w o.1) :=
        (hw.comp hfstM).stronglyMeasurable
      have hpull := condExp_mul_of_stronglyMeasurable_left
        (m := mX) (μ := sourceObsLaw P n) hwM hWF hF
      have hpull' :
          (sourceObsLaw P n)[(fun o => w o.1 * F o) | mX] =ᵐ[
            sourceObsLaw P n]
              fun o => w o.1 * (sourceObsLaw P n)[F | mX] o := by
        simpa only [Pi.mul_apply] using hpull
      calc
        (∫ o, w o.1 * F o ∂sourceObsLaw P n) =
            ∫ o, (sourceObsLaw P n)[(fun o => w o.1 * F o) | mX] o
              ∂sourceObsLaw P n := (integral_condExp hm).symm
        _ = ∫ o, w o.1 * d o.1 ∂sourceObsLaw P n := by
          apply integral_congr_ae
          filter_upwards [hpull', hcond] with o hp hc
          rw [hp, ← hc]
        _ = ∫ x, w x * d x ∂sourceXLaw P n := by
          rw [sourceXLaw]
          exact (integral_map measurable_fst.aemeasurable hwd.1).symm
    have hRiskPoint : ∀ n P,
        fixedGeometrySlice P g N k c epsilon n →
        fixedGeometryOracleExpectedLength C g P n ≤
          max 2 (4 * L + 8 / epsilon ^ 2) *
            min 1 (effectiveStrength P n ^ (-1 / 2 : ℝ)) := by
      intro n P hP
      by_cases hn0 : n = 0
      · subst n
        simp [fixedGeometryOracleExpectedLength, fixedGeometryOracleSet,
          C, setLength, effectiveStrength]
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hIV := atoms.toTransportedIVClass hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hIV.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (sourceXLaw P n) := by
        unfold sourceXLaw
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hIV.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      have hcompact := scoreRiskClass_compact_causal_range atoms hP
      have htheta : targetCACE P n ∈ parameterSpace :=
        hcompact.2.2.2.2.2
      have hfirstEq :
          transportedFirstStage P n = targetComplierShare P n :=
        hcompact.2.2.2.1
      have hmu : 0 < transportedFirstStage P n := by
        rw [hfirstEq]
        exact hIV.targetComplierPositivity
      have hwEq : wG n = transportWeight P n := by
        funext x
        simp only [wG, transportWeight]
        rw [hP.2.1, hP.2.2.1]
      have heEq : g.propensity n = P.propensity n :=
        hP.2.2.2.2.symm
      have hweightMeas : Measurable (transportWeight P n) := by
        exact (Measure.measurable_rnDeriv
          (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
      have hweightMem :
          MemLp (transportWeight P n) 2 (sourceXLaw P n) := by
        refine MemLp.of_bound hweightMeas.aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightMean :
          (∫ x, transportWeight P n x ∂sourceXLaw P n) = 1 := by
        have hchange := integral_rnDeriv_smul
          (μ := targetXLaw P n) (ν := sourceXLaw P n)
          (f := fun _ => (1 : ℝ)) hIV.transportDomination
        simpa [transportWeight] using hchange
      have hkappaOne : 1 ≤ kishDispersion P n := by
        simpa [kishDispersion] using
          one_le_secondMoment_of_mean_one
            (sourceXLaw P n) (transportWeight P n)
            hweightMem hweightMean
      have hkappa : 0 < kishDispersion P n :=
        lt_of_lt_of_le zero_lt_one hkappaOne
      rcases sourceObservationFacts_of_class P N k c epsilon n hIV with
        ⟨_hAssigned, _hSource, hYObs, _hMap, _hProp,
          _hYScore, _hDeltaY, hDScore, hDeltaD⟩
      have hoverObs : ∀ᵐ o ∂sourceObsLaw P n,
          epsilon ≤ P.propensity n o.1 ∧
            P.propensity n o.1 ≤ 1 - epsilon := by
        have hover := hIV.instrumentOverlap.2.2
        rw [sourceXLaw] at hover
        exact (ae_map_iff measurable_fst.aemeasurable
          (measurableSet_Icc.preimage
            (P.propensity_measurable n))).mp hover
      have hDMeas : Measurable (fun o : SourceObs 𝒳 =>
          oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1) := by
        have he : Measurable (fun o : SourceObs 𝒳 =>
            P.propensity n o.1) :=
          (P.propensity_measurable n).comp measurable_fst
        have hscore : Measurable
            (oracleInstrumentScore (P.propensity n)) := by
          unfold oracleInstrumentScore
          exact Measurable.ite (by measurability)
            (measurable_const.div he)
            (measurable_const.neg.div (measurable_const.sub he))
        have hd : Measurable (fun o : SourceObs 𝒳 =>
            boolReal o.2.2.1) := by
          unfold boolReal
          exact Measurable.ite (by measurability)
            measurable_const measurable_const
        exact hscore.mul hd
      have hDInt : Integrable (fun o : SourceObs 𝒳 =>
          oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1) (sourceObsLaw P n) := by
        refine Integrable.of_bound hDMeas.aestronglyMeasurable
          (1 / epsilon) ?_
        filter_upwards [hoverObs] with o ho
        have hscore :
            |oracleInstrumentScore (P.propensity n) o| ≤ 1 / epsilon := by
          unfold oracleInstrumentScore
          split
          · rw [abs_div, abs_one,
              abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
            exact one_div_le_one_div_of_le hepsilon.1 ho.1
          · have hden : 0 < 1 - P.propensity n o.1 := by linarith
            rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
            exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
        rw [Real.norm_eq_abs, abs_mul]
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        calc
          |oracleInstrumentScore (P.propensity n) o| *
              |boolReal o.2.2.1| ≤ (1 / epsilon) * 1 := by
            exact mul_le_mul hscore hd (abs_nonneg _)
              (div_nonneg zero_le_one hepsilon.1.le)
          _ = 1 / epsilon := mul_one _
      have hdeltaDInt : Integrable (P.deltaD n) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
        filter_upwards [hDeltaD] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightedDMeas : Measurable (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)) :=
        (hweightMeas.comp measurable_fst).mul hDMeas
      have hweightedDBound : ∀ᵐ o : SourceObs 𝒳 ∂sourceObsLaw P n,
          ‖transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)‖ ≤ 2 * (k n : ℝ) / epsilon := by
        filter_upwards [hoverObs,
          (ae_map_iff measurable_fst.aemeasurable
            (measurableSet_Icc.preimage hweightMeas)).mp
              (by simpa only [Set.mem_setOf_eq] using hIV.weightEnvelope)
        ] with o ho hw
        have hscore :
            |oracleInstrumentScore (P.propensity n) o| ≤ 1 / epsilon := by
          unfold oracleInstrumentScore
          split
          · rw [abs_div, abs_one,
              abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
            exact one_div_le_one_div_of_le hepsilon.1 ho.1
          · have hden : 0 < 1 - P.propensity n o.1 := by linarith
            rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
            exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw.1]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| *
                |boolReal o.2.2.1|) ≤
              (2 * (k n : ℝ)) * ((1 / epsilon) * 1) := by
            exact mul_le_mul hw.2
              (mul_le_mul hscore hd (abs_nonneg _)
                (div_nonneg zero_le_one hepsilon.1.le))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 2 * (k n : ℝ) / epsilon := by ring
      have hweightedDMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)) 2 (sourceObsLaw P n) :=
        MemLp.of_bound hweightedDMeas.aestronglyMeasurable
          (2 * (k n : ℝ) / epsilon) hweightedDBound
      have hweightedDInt := hweightedDMem.integrable (by norm_num)
      have hweightDeltaDInt : Integrable (fun x =>
          transportWeight P n x * P.deltaD n x) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (hweightMeas.mul (P.deltaD_measurable n)).aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope, hDeltaD] with x hw hd
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
          abs_of_nonneg hd.1]
        exact (mul_le_mul hw.2 hd.2 hd.1
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))).trans_eq
          (mul_one _)
      have hDMean : (∫ o,
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1) ∂sourceObsLaw P n) =
          transportedFirstStage P n := by
        rw [pullout P n
          (fun o => oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1)
          (P.deltaD n) (transportWeight P n)
          (inferInstance : IsProbabilityMeasure (sourceObsLaw P n))
          hDInt hdeltaDInt (P.deltaD_measurable n) hweightMeas
          hweightedDInt hweightDeltaDInt]
        · exact (transportedFirstStage_eq_weighted_deltaD P k epsilon n
            (sourceObservationFacts_of_class P N k c epsilon n hIV)
            hIV.instrumentOverlap hIV.weightEnvelope).symm
        · intro A hA
          simpa [instrumentScore, oracleInstrumentScore] using hDScore A hA
      have hweightSqObsInt : Integrable (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) (sourceObsLaw P n) := by
        have hmap : Integrable (fun x => transportWeight P n x ^ 2)
            (Measure.map (fun o : SourceObs 𝒳 => o.1)
              (sourceObsLaw P n)) := by
          simpa [sourceXLaw] using hweightMem.integrable_sq
        simpa [Function.comp_def] using
          (integrable_map_measure hmap.1 measurable_fst.aemeasurable).mp hmap
      have hDVar : variance (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)) (sourceObsLaw P n) ≤
          kishDispersion P n / epsilon ^ 2 := by
        calc
          variance (fun o : SourceObs 𝒳 =>
              transportWeight P n o.1 *
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1)) (sourceObsLaw P n) ≤
              ∫ o, (transportWeight P n o.1 *
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1)) ^ 2 ∂sourceObsLaw P n :=
            variance_le_expectation_sq
              hweightedDMeas.aestronglyMeasurable
          _ ≤ ∫ o, transportWeight P n o.1 ^ 2 / epsilon ^ 2
                ∂sourceObsLaw P n := by
            apply integral_mono_ae hweightedDMem.integrable_sq
              (hweightSqObsInt.div_const _)
            filter_upwards [hoverObs] with o ho
            have hscore :
                |oracleInstrumentScore (P.propensity n) o| ≤
                  1 / epsilon := by
              unfold oracleInstrumentScore
              split
              · rw [abs_div, abs_one,
                  abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
                exact one_div_le_one_div_of_le hepsilon.1 ho.1
              · have hden : 0 < 1 - P.propensity n o.1 := by linarith
                rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
                exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
            have hd : |boolReal o.2.2.1| ≤ 1 := by
              cases o.2.2.1 <;> simp [boolReal]
            have hprod :
                |oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1| ≤ 1 / epsilon := by
              rw [abs_mul]
              calc
                _ ≤ (1 / epsilon) * 1 :=
                  mul_le_mul hscore hd (abs_nonneg _)
                    (div_nonneg zero_le_one hepsilon.1.le)
                _ = 1 / epsilon := mul_one _
            have hsquare :
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1) ^ 2 ≤ (1 / epsilon) ^ 2 := by
              rw [← sq_abs]
              exact (sq_le_sq₀ (abs_nonneg _)
                (div_nonneg zero_le_one hepsilon.1.le)).2 hprod
            rw [mul_pow]
            calc
              transportWeight P n o.1 ^ 2 *
                  (oracleInstrumentScore (P.propensity n) o *
                    boolReal o.2.2.1) ^ 2 ≤
                  transportWeight P n o.1 ^ 2 * (1 / epsilon) ^ 2 := by
                gcongr
              _ = transportWeight P n o.1 ^ 2 / epsilon ^ 2 := by ring
          _ = kishDispersion P n / epsilon ^ 2 := by
            rw [integral_div]
            congr 1
            have hmap := integral_map measurable_fst.aemeasurable
              hweightMem.integrable_sq.1
            simpa [kishDispersion, sourceXLaw] using hmap.symm
      let QS : Measure (SourceSample 𝒳 n) :=
        Measure.pi (fun _ : Fin n => sourceObsLaw P n)
      let B : SourceSample 𝒳 n → ℝ := fun sample =>
        scoreReceiptMean (transportWeight P n) (P.propensity n) n sample
      have hBeq : B = fun sample : SourceSample 𝒳 n =>
          (n : ℝ)⁻¹ * ∑ i,
            transportWeight P n (sample i).1 *
              (oracleInstrumentScore (P.propensity n) (sample i) *
                boolReal (sample i).2.2.1) := by
        funext sample
        simp only [B, scoreReceiptMean]
        apply congrArg ((n : ℝ)⁻¹ * ·)
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hBmom := iid_empiricalAverage_mean_variance
        (sourceObsLaw P n) n hn
        (fun o => transportWeight P n o.1 *
          (oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1)) hweightedDMem
      have hBmean : (∫ sample, B sample ∂QS) =
          transportedFirstStage P n := by
        rw [hBeq]
        exact hBmom.1.trans hDMean
      have hBvar : variance B QS ≤
          kishDispersion P n / (epsilon ^ 2 * n) := by
        rw [hBeq, hBmom.2]
        calc
          (n : ℝ)⁻¹ * variance (fun o : SourceObs 𝒳 =>
              transportWeight P n o.1 *
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1)) (sourceObsLaw P n) ≤
              (n : ℝ)⁻¹ * (kishDispersion P n / epsilon ^ 2) := by
            gcongr
          _ = kishDispersion P n / (epsilon ^ 2 * n) := by ring
      have hBmem : MemLp B 2 QS := by
        rw [hBeq]
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) : MemLp
            (fun sample : SourceSample 𝒳 n =>
              transportWeight P n (sample i).1 *
                (oracleInstrumentScore (P.propensity n) (sample i) *
                  boolReal (sample i).2.2.1)) 2 QS := by
          simpa [Function.comp_def] using
            hweightedDMem.comp_measurePreserving (heval i)
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      have hbadS := scoreReceiptMean_bad_probability
        QS B n epsilon (transportedFirstStage P n)
        (kishDispersion P n) (effectiveStrength P n)
        hn hepsilon.1 hmu hkappa hBmem hBmean hBvar rfl
      let K : SourceSample 𝒳 n → ℝ := fun sample =>
        empiricalKish (transportWeight P n) n sample
      have hweightSqObsMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).pow_const 2).aestronglyMeasurable
          ((2 * (k n : ℝ)) ^ 2) ?_
        filter_upwards [
          (ae_map_iff measurable_fst.aemeasurable
            (measurableSet_Icc.preimage hweightMeas)).mp
              (by simpa only [Set.mem_setOf_eq] using hIV.weightEnvelope)
        ] with o hw
        rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hw.1]
        exact pow_le_pow_left₀ hw.1 hw.2 2
      have hKmeanS : (∫ sample, K sample ∂QS) =
          kishDispersion P n := by
        calc
          (∫ sample, K sample ∂QS) =
              ∫ o : SourceObs 𝒳, transportWeight P n o.1 ^ 2
                ∂sourceObsLaw P n := by
            simpa [K, QS] using
              empiricalKish_mean (sourceObsLaw P n)
                (transportWeight P n) n hn hweightSqObsMem
          _ = kishDispersion P n := by
            have hmap := integral_map measurable_fst.aemeasurable
              hweightMem.integrable_sq.1
            simpa [kishDispersion, sourceXLaw] using hmap.symm
      have hKmem : MemLp K 2 QS := by
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) : MemLp
            (fun sample : SourceSample 𝒳 n =>
              transportWeight P n (sample i).1 ^ 2) 2 QS := by
          simpa [Function.comp_def] using
            hweightSqObsMem.comp_measurePreserving (heval i)
        unfold K empiricalKish Causalean.Stat.empiricalKishDispersion
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      let A₂ : TwoSample 𝒳 n (N n) → ℝ := fun s =>
        scoreOutcomeMean (transportWeight P n) (P.propensity n) n s.1
      let B₂ : TwoSample 𝒳 n (N n) → ℝ := fun s => B s.1
      let K₂ : TwoSample 𝒳 n (N n) → ℝ := fun s => K s.1
      let QT : Measure (TargetSample 𝒳 (N n)) :=
        Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
      have hK₂mem : MemLp K₂ 2 (twoSampleLaw P N n) := by
        simpa [K₂, QS, QT, twoSampleLaw] using hKmem.comp_fst QT
      have hK₂mean : (∫ s, K₂ s ∂twoSampleLaw P N n) =
          kishDispersion P n := by
        unfold twoSampleLaw
        rw [integral_prod_symm _ (hK₂mem.integrable (by norm_num))]
        simp [K₂, QS, QT, hKmeanS]
      have hbad₂ :
          (twoSampleLaw P N n
            {s | transportedFirstStage P n / 2 <
              |B₂ s - transportedFirstStage P n|}).toReal ≤
            4 / (epsilon ^ 2 * effectiveStrength P n) := by
        let bad : Set (SourceSample 𝒳 n) :=
          {s | transportedFirstStage P n / 2 <
            |B s - transportedFirstStage P n|}
        have hset :
            {s : TwoSample 𝒳 n (N n) |
              transportedFirstStage P n / 2 <
                |B₂ s - transportedFirstStage P n|} =
              bad ×ˢ Set.univ := by
          ext s
          simp [bad, B₂]
        rw [hset, twoSampleLaw, Measure.prod_prod]
        simpa [bad, QS] using hbadS
      have hfront := scoreInversion_expectedLength_frontier_le
        (twoSampleLaw P N n) A₂ B₂ K₂ n L
        (transportedFirstStage P n) (kishDispersion P n)
        (4 / (epsilon ^ 2 * effectiveStrength P n))
        epsilon (effectiveStrength P n)
        (Real.sqrt_nonneg _) hmu hn
        (fun s => by
          unfold K₂ K empiricalKish Causalean.Stat.empiricalKishDispersion
          exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (Finset.sum_nonneg fun i _ => sq_nonneg _))
        (hK₂mem.integrable (by norm_num)) hK₂mean
        hbad₂ hkappa hepsilon.1 le_rfl rfl
      simpa [fixedGeometryOracleExpectedLength, fixedGeometryOracleSet,
        C, hn0, hwEq, heEq, L, A₂, B₂, B, K₂, K,
        inversionHandle_eq_affineInversionSet] using hfront
    let delta : ℕ → ℝ := fun n =>
      if n = 0 then 1 else 16 * (k n : ℝ) ^ 2 / n
    have hdelta : Tendsto delta atTop (𝓝 0) := by
      have hsquare := hkRoot.pow 2
      have hraw : Tendsto (fun n : ℕ =>
          16 * ((k n : ℝ) / Real.sqrt n) ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hsquare)
      apply hraw.congr'
      filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
      simp only [delta, hn0, ↓reduceIte]
      rw [div_pow]
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    have hCoveragePoint : ∀ n P,
        fixedGeometrySlice P g N k c epsilon n →
        1 - alpha - delta n ≤ fixedGeometryOracleCoverage C g P n := by
      intro n P hP
      by_cases hn0 : n = 0
      · subst n
        simp [delta, fixedGeometryOracleCoverage, fixedGeometryOracleSet, C]
        linarith [hAlpha.1]
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hIV := atoms.toTransportedIVClass hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hIV.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (sourceXLaw P n) := by
        unfold sourceXLaw
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hIV.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      have hcompact := scoreRiskClass_compact_causal_range atoms hP
      have htheta : targetCACE P n ∈ parameterSpace :=
        hcompact.2.2.2.2.2
      have hfirstEq :
          transportedFirstStage P n = targetComplierShare P n :=
        hcompact.2.2.2.1
      have hmu : 0 < transportedFirstStage P n := by
        rw [hfirstEq]
        exact hIV.targetComplierPositivity
      have hratio :
          transportedOutcomeITT P n / transportedFirstStage P n =
            targetCACE P n :=
        hcompact.2.2.2.2.1
      have hwEq : wG n = transportWeight P n := by
        funext x
        simp only [wG, transportWeight]
        rw [hP.2.1, hP.2.2.1]
      have heEq : g.propensity n = P.propensity n :=
        hP.2.2.2.2.symm
      have hweightMeas : Measurable (transportWeight P n) :=
        (Measure.measurable_rnDeriv
          (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
      have hweightMem :
          MemLp (transportWeight P n) 2 (sourceXLaw P n) := by
        refine MemLp.of_bound hweightMeas.aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightMean :
          (∫ x, transportWeight P n x ∂sourceXLaw P n) = 1 := by
        have hchange := integral_rnDeriv_smul
          (μ := targetXLaw P n) (ν := sourceXLaw P n)
          (f := fun _ => (1 : ℝ)) hIV.transportDomination
        simpa [transportWeight] using hchange
      have hkappaOne : 1 ≤ kishDispersion P n := by
        simpa [kishDispersion] using
          one_le_secondMoment_of_mean_one
            (sourceXLaw P n) (transportWeight P n)
            hweightMem hweightMean
      have hkappa : 0 < kishDispersion P n :=
        lt_of_lt_of_le zero_lt_one hkappaOne
      rcases sourceObservationFacts_of_class P N k c epsilon n hIV with
        ⟨_hAssigned, _hSource, hYObs, _hMap, _hProp,
          hYScore, hDeltaY, hDScore, hDeltaD⟩
      have hoverObs : ∀ᵐ o ∂sourceObsLaw P n,
          epsilon ≤ P.propensity n o.1 ∧
            P.propensity n o.1 ≤ 1 - epsilon := by
        have hover := hIV.instrumentOverlap.2.2
        rw [sourceXLaw] at hover
        exact (ae_map_iff measurable_fst.aemeasurable
          (measurableSet_Icc.preimage
            (P.propensity_measurable n))).mp hover
      have hweightObs : ∀ᵐ o ∂sourceObsLaw P n,
          0 ≤ transportWeight P n o.1 ∧
            transportWeight P n o.1 ≤ 2 * (k n : ℝ) := by
        exact (ae_map_iff measurable_fst.aemeasurable
          (measurableSet_Icc.preimage hweightMeas)).mp
            (by simpa only [Set.mem_setOf_eq] using hIV.weightEnvelope)
      have hInstMeas : Measurable
          (oracleInstrumentScore (P.propensity n)) := by
        have he : Measurable (fun o : SourceObs 𝒳 =>
            P.propensity n o.1) :=
          (P.propensity_measurable n).comp measurable_fst
        unfold oracleInstrumentScore
        exact Measurable.ite (by measurability)
          (measurable_const.div he)
          (measurable_const.neg.div (measurable_const.sub he))
      have hBoolMeas : Measurable (fun o : SourceObs 𝒳 =>
          boolReal o.2.2.1) := by
        unfold boolReal
        exact Measurable.ite (by measurability)
          measurable_const measurable_const
      have hinstBound : ∀ᵐ o ∂sourceObsLaw P n,
          |oracleInstrumentScore (P.propensity n) o| ≤ 1 / epsilon := by
        filter_upwards [hoverObs] with o ho
        unfold oracleInstrumentScore
        split
        · rw [abs_div, abs_one,
            abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
          exact one_div_le_one_div_of_le hepsilon.1 ho.1
        · have hden : 0 < 1 - P.propensity n o.1 := by linarith
          rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
          exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
      let FY : SourceObs 𝒳 → ℝ := fun o =>
        oracleInstrumentScore (P.propensity n) o * o.2.2.2
      let FD : SourceObs 𝒳 → ℝ := fun o =>
        oracleInstrumentScore (P.propensity n) o * boolReal o.2.2.1
      have hFYMeas : Measurable FY :=
        hInstMeas.mul (by fun_prop)
      have hFDMeas : Measurable FD :=
        hInstMeas.mul hBoolMeas
      have hFYInt : Integrable FY (sourceObsLaw P n) := by
        refine Integrable.of_bound hFYMeas.aestronglyMeasurable
          (1 / epsilon) ?_
        filter_upwards [hinstBound, hYObs] with o hs hy
        simp only [FY]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy.1]
        exact (mul_le_mul hs hy.2 hy.1
          (div_nonneg zero_le_one hepsilon.1.le)).trans_eq (mul_one _)
      have hFDInt : Integrable FD (sourceObsLaw P n) := by
        refine Integrable.of_bound hFDMeas.aestronglyMeasurable
          (1 / epsilon) ?_
        filter_upwards [hinstBound] with o hs
        simp only [FD]
        rw [Real.norm_eq_abs, abs_mul]
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        exact (mul_le_mul hs hd (abs_nonneg _)
          (div_nonneg zero_le_one hepsilon.1.le)).trans_eq (mul_one _)
      have hdeltaYInt : Integrable (P.deltaY n) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (P.deltaY_measurable n).aestronglyMeasurable 1 ?_
        filter_upwards [hDeltaY] with x hx
        rw [Real.norm_eq_abs]
        exact (abs_le).2 hx
      have hdeltaDInt : Integrable (P.deltaD n) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
        filter_upwards [hDeltaD] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightFYMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 * FY o) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).mul hFYMeas).aestronglyMeasurable
          (2 * (k n : ℝ) / epsilon) ?_
        filter_upwards [hweightObs, hinstBound, hYObs] with o hw hs hy
        simp only [FY]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
          abs_mul, abs_of_nonneg hy.1]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| * o.2.2.2) ≤
              (2 * (k n : ℝ)) * ((1 / epsilon) * 1) := by
            exact mul_le_mul hw.2
              (mul_le_mul hs hy.2 hy.1
                (div_nonneg zero_le_one hepsilon.1.le))
              (mul_nonneg (abs_nonneg _) hy.1)
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 2 * (k n : ℝ) / epsilon := by ring
      have hweightFDMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 * FD o) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).mul hFDMeas).aestronglyMeasurable
          (2 * (k n : ℝ) / epsilon) ?_
        filter_upwards [hweightObs, hinstBound] with o hw hs
        simp only [FD]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1, abs_mul]
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| *
                |boolReal o.2.2.1|) ≤
              (2 * (k n : ℝ)) * ((1 / epsilon) * 1) := by
            exact mul_le_mul hw.2
              (mul_le_mul hs hd (abs_nonneg _)
                (div_nonneg zero_le_one hepsilon.1.le))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 2 * (k n : ℝ) / epsilon := by ring
      have hweightDeltaYInt : Integrable (fun x =>
          transportWeight P n x * P.deltaY n x) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (hweightMeas.mul (P.deltaY_measurable n)).aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope, hDeltaY] with x hw hy
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1]
        exact (mul_le_mul hw.2 ((abs_le).2 hy)
          (abs_nonneg _) (mul_nonneg (by norm_num)
            (Nat.cast_nonneg _))).trans_eq (mul_one _)
      have hweightDeltaDInt : Integrable (fun x =>
          transportWeight P n x * P.deltaD n x) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (hweightMeas.mul (P.deltaD_measurable n)).aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope, hDeltaD] with x hw hd
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
          abs_of_nonneg hd.1]
        exact (mul_le_mul hw.2 hd.2 hd.1
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))).trans_eq
          (mul_one _)
      have hYMean : (∫ o, transportWeight P n o.1 * FY o
          ∂sourceObsLaw P n) = transportedOutcomeITT P n := by
        rw [pullout P n FY (P.deltaY n) (transportWeight P n)
          (inferInstance : IsProbabilityMeasure (sourceObsLaw P n))
          hFYInt hdeltaYInt (P.deltaY_measurable n) hweightMeas
          (hweightFYMem.integrable (by norm_num)) hweightDeltaYInt]
        · rfl
        · intro A hA
          simpa [FY, instrumentScore, oracleInstrumentScore] using hYScore A hA
      have hDMean : (∫ o, transportWeight P n o.1 * FD o
          ∂sourceObsLaw P n) = transportedFirstStage P n := by
        rw [pullout P n FD (P.deltaD n) (transportWeight P n)
          (inferInstance : IsProbabilityMeasure (sourceObsLaw P n))
          hFDInt hdeltaDInt (P.deltaD_measurable n) hweightMeas
          (hweightFDMem.integrable (by norm_num)) hweightDeltaDInt]
        · exact (transportedFirstStage_eq_weighted_deltaD P k epsilon n
            (sourceObservationFacts_of_class P N k c epsilon n hIV)
            hIV.instrumentOverlap hIV.weightEnvelope).symm
        · intro A hA
          simpa [FD, instrumentScore, oracleInstrumentScore] using hDScore A hA
      let theta := targetCACE P n
      let Z : SourceObs 𝒳 → ℝ :=
        oracleAffineScore (transportWeight P n) (P.propensity n) theta
      have hZMeas : Measurable Z := by
        unfold Z oracleAffineScore
        have hyMeas : Measurable (fun o : SourceObs 𝒳 => o.2.2.2) := by
          fun_prop
        exact ((hweightMeas.comp measurable_fst).mul hInstMeas).mul
          (hyMeas.sub (measurable_const.mul hBoolMeas))
      have hZMem : MemLp Z 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound hZMeas.aestronglyMeasurable
          (4 * (k n : ℝ) / epsilon) ?_
        filter_upwards [hweightObs, hoverObs, hYObs] with o hw ho hy
        have hres := abs_oracleInstrumentScore_residual_le
          (P.propensity n) epsilon theta o hepsilon.1 ho htheta hy
        have hres' :
            |oracleInstrumentScore (P.propensity n) o| *
                |o.2.2.2 - theta * boolReal o.2.2.1| ≤ 2 / epsilon := by
          simpa [abs_mul] using hres
        simp only [Z]
        rw [oracleAffineScore, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg hw.1, mul_assoc]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| *
                |o.2.2.2 - theta * boolReal o.2.2.1|) ≤
              (2 * (k n : ℝ)) * (2 / epsilon) := by
            exact mul_le_mul hw.2 hres'
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 4 * (k n : ℝ) / epsilon := by ring
      have hZMean : (∫ o, Z o ∂sourceObsLaw P n) = 0 := by
        apply oracleAffineScore_mean_zero
          (sourceObsLaw P n) (transportWeight P n) (P.propensity n)
          theta (transportedOutcomeITT P n) (transportedFirstStage P n)
        · simpa [FY, mul_assoc] using
            hweightFYMem.integrable (by norm_num)
        · simpa [FD, mul_assoc] using
            hweightFDMem.integrable (by norm_num)
        · simpa [FY, mul_assoc] using hYMean
        · simpa [FD, mul_assoc] using hDMean
        · exact hmu.ne'
        · exact hratio
      have hweightSqObsInt : Integrable (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) (sourceObsLaw P n) := by
        have hmap : Integrable (fun x => transportWeight P n x ^ 2)
            (Measure.map (fun o : SourceObs 𝒳 => o.1)
              (sourceObsLaw P n)) := by
          simpa [sourceXLaw] using hweightMem.integrable_sq
        simpa [Function.comp_def] using
          (integrable_map_measure hmap.1 measurable_fst.aemeasurable).mp hmap
      have hkappaObs :
          (∫ o : SourceObs 𝒳, transportWeight P n o.1 ^ 2
              ∂sourceObsLaw P n) = kishDispersion P n := by
        have hmap := integral_map measurable_fst.aemeasurable
          hweightMem.integrable_sq.1
        simpa [kishDispersion, sourceXLaw] using hmap.symm
      have hZVar : variance Z (sourceObsLaw P n) ≤
          4 * kishDispersion P n / epsilon ^ 2 := by
        calc
          variance Z (sourceObsLaw P n) ≤
              ∫ o, Z o ^ 2 ∂sourceObsLaw P n :=
            variance_le_expectation_sq hZMeas.aestronglyMeasurable
          _ ≤ ∫ o, 4 * transportWeight P n o.1 ^ 2 / epsilon ^ 2
                ∂sourceObsLaw P n := by
            apply integral_mono_ae hZMem.integrable_sq
              ((hweightSqObsInt.const_mul 4).div_const _)
            filter_upwards [hoverObs, hYObs] with o ho hy
            exact oracleAffineScore_sq_le
              (transportWeight P n) (P.propensity n)
              epsilon theta o hepsilon.1 ho htheta hy
          _ = 4 * kishDispersion P n / epsilon ^ 2 := by
            rw [integral_div, integral_const_mul, hkappaObs]
      let QS : Measure (SourceSample 𝒳 n) :=
        Measure.pi (fun _ : Fin n => sourceObsLaw P n)
      let S : SourceSample 𝒳 n → ℝ := fun sample =>
        scoreOutcomeMean (transportWeight P n) (P.propensity n) n sample -
          theta * scoreReceiptMean
            (transportWeight P n) (P.propensity n) n sample
      have hSeq : S = fun sample : SourceSample 𝒳 n =>
          (n : ℝ)⁻¹ * ∑ i, Z (sample i) := by
        funext sample
        exact scoreOutcomeMean_sub_receiptMean
          (transportWeight P n) (P.propensity n) theta n sample
      have hSmom := iid_empiricalAverage_mean_variance
        (sourceObsLaw P n) n hn Z hZMem
      have hSmean : (∫ sample, S sample ∂QS) = 0 := by
        rw [hSeq]
        exact hSmom.1.trans hZMean
      have hSvar : variance S QS ≤
          4 * kishDispersion P n / (epsilon ^ 2 * n) := by
        rw [hSeq, hSmom.2]
        calc
          (n : ℝ)⁻¹ * variance Z (sourceObsLaw P n) ≤
              (n : ℝ)⁻¹ *
                (4 * kishDispersion P n / epsilon ^ 2) := by
            gcongr
          _ = 4 * kishDispersion P n / (epsilon ^ 2 * n) := by
            ring
      have hSmem : MemLp S 2 QS := by
        rw [hSeq]
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) :
            MemLp (fun sample : SourceSample 𝒳 n => Z (sample i)) 2 QS := by
          simpa [Function.comp_def] using
            hZMem.comp_measurePreserving (heval i)
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      let K : SourceSample 𝒳 n → ℝ := fun sample =>
        empiricalKish (transportWeight P n) n sample
      have hweightSqObsMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).pow_const 2).aestronglyMeasurable
          ((2 * (k n : ℝ)) ^ 2) ?_
        filter_upwards [hweightObs] with o hw
        rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hw.1]
        exact pow_le_pow_left₀ hw.1 hw.2 2
      have hKmean : (∫ sample, K sample ∂QS) =
          kishDispersion P n := by
        calc
          (∫ sample, K sample ∂QS) =
              ∫ o : SourceObs 𝒳, transportWeight P n o.1 ^ 2
                ∂sourceObsLaw P n := by
            simpa [K, QS] using
              empiricalKish_mean (sourceObsLaw P n)
                (transportWeight P n) n hn hweightSqObsMem
          _ = kishDispersion P n := hkappaObs
      have hKmem : MemLp K 2 QS := by
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) : MemLp
            (fun sample : SourceSample 𝒳 n =>
              transportWeight P n (sample i).1 ^ 2) 2 QS := by
          simpa [Function.comp_def] using
            hweightSqObsMem.comp_measurePreserving (heval i)
        unfold K empiricalKish Causalean.Stat.empiricalKishDispersion
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      have hfourth : ∀ᵐ o ∂sourceObsLaw P n,
          transportWeight P n o.1 ^ 4 ≤
            4 * (k n : ℝ) ^ 2 * transportWeight P n o.1 ^ 2 := by
        filter_upwards [hweightObs] with o hw
        exact weight_fourth_le_envelope
          (transportWeight P n o.1) (k n : ℝ) hw.1 hw.2
      have hKvar : variance K QS ≤
          4 * (k n : ℝ) ^ 2 * kishDispersion P n / n := by
        simpa [K, QS] using empiricalKish_variance_le
          (sourceObsLaw P n) (transportWeight P n) n (k n)
          (kishDispersion P n) hn hweightSqObsMem hkappaObs hfourth
      have hKbadRaw :
          (QS {sample | K sample < kishDispersion P n / 2}).toReal ≤
            16 * (k n : ℝ) ^ 2 /
              ((n : ℝ) * kishDispersion P n) := by
        simpa [K] using empiricalKish_lower_tail_le n QS
          (transportWeight P n) (k n) (kishDispersion P n)
          hn hkappa hKmem hKmean hKvar
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hKbad :
          (QS {sample | K sample < kishDispersion P n / 2}).toReal ≤
            16 * (k n : ℝ) ^ 2 / n := by
        calc
          _ ≤ 16 * (k n : ℝ) ^ 2 /
              ((n : ℝ) * kishDispersion P n) := hKbadRaw
          _ ≤ 16 * (k n : ℝ) ^ 2 / n := by
            rw [div_le_div_iff₀ (mul_pos hnR hkappa) hnR]
            gcongr
            calc
              (n : ℝ) = (n : ℝ) * 1 := by ring
              _ ≤ (n : ℝ) * kishDispersion P n :=
                mul_le_mul_of_nonneg_left hkappaOne hnR.le
      have hbasePos : 0 < 8 / (alpha * epsilon ^ 2) := by
        exact div_pos (by norm_num)
          (mul_pos hAlpha.1 (sq_pos_of_pos hepsilon.1))
      have hLpos : 0 < L := by
        simpa [L] using Real.sqrt_pos.2 hbasePos
      have hLsq : L ^ 2 = 8 / (alpha * epsilon ^ 2) := by
        simpa [L] using Real.sq_sqrt hbasePos.le
      let a : ℝ :=
        L * Real.sqrt (kishDispersion P n / (2 * n))
      have ha : 0 < a := by
        unfold a
        exact mul_pos hLpos (Real.sqrt_pos.2 (by positivity))
      have hSbadRaw :
          (QS {sample | a < |S sample - 0|}).toReal ≤
            (4 * kishDispersion P n / (epsilon ^ 2 * n)) / a ^ 2 :=
        probability_abs_sub_mean_gt_le QS S 0
          (4 * kishDispersion P n / (epsilon ^ 2 * n)) a
          hSmem ha hSmean hSvar
      have hSratio :
          (4 * kishDispersion P n / (epsilon ^ 2 * n)) / a ^ 2 =
            alpha := by
        unfold a
        change (4 * kishDispersion P n / (epsilon ^ 2 * n)) /
          (Real.sqrt (8 / (alpha * epsilon ^ 2)) *
            Real.sqrt (kishDispersion P n / (2 * n))) ^ 2 = alpha
        rw [mul_pow, Real.sq_sqrt hbasePos.le,
          Real.sq_sqrt (by positivity)]
        field_simp [hAlpha.1.ne', hepsilon.1.ne', hnR.ne', hkappa.ne']
        ring
      have hSbad :
          (QS {sample | a < |S sample|}).toReal ≤ alpha := by
        simpa [hSratio] using hSbadRaw
      have hKMeas : Measurable K := by
        unfold K empiricalKish Causalean.Stat.empiricalKishDispersion
        fun_prop
      have hSMeas : Measurable S := by
        rw [hSeq]
        fun_prop
      let BK : Set (SourceSample 𝒳 n) :=
        {sample | K sample < kishDispersion P n / 2}
      let BS : Set (SourceSample 𝒳 n) :=
        {sample | a < |S sample|}
      have hBKMeas : MeasurableSet BK :=
        measurableSet_lt hKMeas measurable_const
      have hBSMeas : MeasurableSet BS :=
        measurableSet_lt measurable_const hSMeas.abs
      have hbadUnion :
          (QS (BK ∪ BS)).toReal ≤ delta n + alpha := by
        change QS.real (BK ∪ BS) ≤ delta n + alpha
        calc
          QS.real (BK ∪ BS) ≤ QS.real BK + QS.real BS :=
            measureReal_union_le (μ := QS) BK BS
          _ ≤ 16 * (k n : ℝ) ^ 2 / n + alpha := by
            exact add_le_add (by simpa [Measure.real, BK] using hKbad)
              (by simpa [Measure.real, BS] using hSbad)
          _ = delta n + alpha := by simp [delta, hn0]
      have hgoodSource :
          1 - alpha - delta n ≤ (QS ((BK ∪ BS)ᶜ)).toReal := by
        change 1 - alpha - delta n ≤ QS.real ((BK ∪ BS)ᶜ)
        rw [measureReal_compl (hBKMeas.union hBSMeas)]
        have hQSone : QS.real Set.univ = 1 := by
          simp [Measure.real]
        rw [hQSone]
        change QS.real (BK ∪ BS) ≤ _ at hbadUnion
        linarith
      let QT : Measure (TargetSample 𝒳 (N n)) :=
        Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
      have hgoodProd :
          (twoSampleLaw P N n (((BK ∪ BS)ᶜ) ×ˢ Set.univ)).toReal =
            (QS ((BK ∪ BS)ᶜ)).toReal := by
        rw [twoSampleLaw, Measure.prod_prod]
        simp [QS, QT]
      have hgoodSubset :
          ((BK ∪ BS)ᶜ) ×ˢ (Set.univ : Set (TargetSample 𝒳 (N n))) ⊆
            {s | targetCACE P n ∈ fixedGeometryOracleSet C g n s} := by
        intro s hs
        have hgood := hs.1
        simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq,
          not_or] at hgood
        have hKhalf : kishDispersion P n / 2 ≤ K s.1 :=
          le_of_not_gt hgood.1
        have hroot : Real.sqrt (kishDispersion P n / (2 * n)) ≤
            Real.sqrt (K s.1 / n) := by
          apply Real.sqrt_le_sqrt
          calc
            kishDispersion P n / (2 * (n : ℝ)) =
                (kishDispersion P n / 2) / n := by ring
            _ ≤ K s.1 / n :=
              div_le_div_of_nonneg_right hKhalf hnR.le
        have hscore : |S s.1| ≤
            L * Real.sqrt (K s.1 / n) := by
          calc
            |S s.1| ≤ a := le_of_not_gt hgood.2
            _ = L * Real.sqrt (kishDispersion P n / (2 * n)) := rfl
            _ ≤ L * Real.sqrt (K s.1 / n) :=
              mul_le_mul_of_nonneg_left hroot hLpos.le
        change targetCACE P n ∈ fixedGeometryOracleSet C g n s
        simp only [fixedGeometryOracleSet, C, hn0, ↓reduceIte]
        rw [hwEq, heEq]
        exact ⟨htheta, by simpa [S, theta, K] using hscore⟩
      calc
        1 - alpha - delta n ≤
            (QS ((BK ∪ BS)ᶜ)).toReal := hgoodSource
        _ = (twoSampleLaw P N n
            (((BK ∪ BS)ᶜ) ×ˢ
              (Set.univ : Set (TargetSample 𝒳 (N n))))).toReal :=
          hgoodProd.symm
        _ ≤ fixedGeometryOracleCoverage C g P n := by
          exact measureReal_mono hgoodSubset
    have hInhab : ∀ᶠ n in atTop, ∃ P,
        fixedGeometrySlice P g N k c epsilon n := by
      filter_upwards [hSlice] with n hn
      exact ⟨hn.choose, hn.choose_spec.1⟩
    have hCoverageRange : ∀ n P,
        fixedGeometrySlice P g N k c epsilon n →
          0 ≤ fixedGeometryOracleCoverage C g P n ∧
            fixedGeometryOracleCoverage C g P n ≤ 1 := by
      intro n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      constructor
      · exact ENNReal.toReal_nonneg
      · simpa [fixedGeometryOracleCoverage, Measure.real] using
          (measureReal_le_one (μ := twoSampleLaw P N n))
    have hHonest :
        FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ C := by
      refine ⟨hAlpha.1, hAlpha.2, ?_⟩
      have hraw : 1 - alpha ≤ Filter.liminf
          (fun n => ⨅ P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n},
            fixedGeometryOracleCoverage C g P n) atTop :=
        abstractClass_coverage_liminf
          (fun n P => fixedGeometrySlice P g N k c epsilon n)
          (fun n P => fixedGeometryOracleCoverage C g P n) alpha delta
          hdelta hInhab hCoverageRange hCoveragePoint
      have hrows : ∀ᶠ n in atTop,
          coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} =>
              fixedGeometryOracleCoverage C g P n) =
            (⨅ P : {P : TransportedArray 𝒳 //
                fixedGeometrySlice P g N k c epsilon n},
              fixedGeometryOracleCoverage C g P n) := by
        filter_upwards [hInhab] with n hn
        letI : Nonempty {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} :=
          ⟨⟨hn.choose, hn.choose_spec⟩⟩
        exact coverageInfOrOne_of_nonempty _
      exact hraw.trans_eq (Filter.liminf_congr hrows).symm
    let C0 : ℝ := max 2 (4 * L + 8 / epsilon ^ 2)
    have hC0 : 0 ≤ C0 := le_trans (by norm_num) (le_max_left _ _)
    have hLengthNonneg : ∀ n P,
        fixedGeometrySlice P g N k c epsilon n →
          0 ≤ fixedGeometryOracleExpectedLength C g P n := by
      intro n P hP
      exact integral_nonneg fun _ => ENNReal.toReal_nonneg
    have hRisk :
        fixedGeometryRisk N k c epsilon g C t0 ≤
          C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) := by
      simpa [fixedGeometryRisk, abstractClassFrontierRisk] using
        abstractClassFrontierRisk_le
          (fun n P => fixedGeometrySlice P g N k c epsilon n)
          (fun n P => effectiveStrength P n)
          (fun n P => fixedGeometryOracleExpectedLength C g P n)
          C0 t0 hC0 ht0 hLengthNonneg hRiskPoint
    have hsetLengthTwo : ∀ A : Set ℝ, setLength A ≤ 2 := by
      intro A
      unfold setLength parameterSpace
      calc
        (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
            (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
          ENNReal.toReal_mono (by simp [Real.volume_Icc])
            (measure_mono Set.inter_subset_right)
        _ = 2 := by
          rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
          norm_num
    have hExpectedTwo : ∀ (E : OracleProcedure 𝒳 N k c epsilon) n P,
        fixedGeometrySlice P g N k c epsilon n →
          fixedGeometryOracleExpectedLength E g P n ≤ 2 := by
      intro E n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      exact (integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        (integrable_const 2)
        (Filter.Eventually.of_forall fun s =>
          hsetLengthTwo (fixedGeometryOracleSet E g n s))).trans_eq (by simp)
    have hriskNonneg : ∀ E : OracleProcedure 𝒳 N k c epsilon,
        0 ≤ fixedGeometryRisk N k c epsilon g E t0 := by
      intro E
      let row : ℕ → ℝ := fun n =>
        ⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength E g P n
      have hrowTwo : ∀ n, row n ≤ 2 := by
        intro n
        let I := {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n}
        cases isEmpty_or_nonempty I with
        | inl hEmpty =>
            letI : IsEmpty I := hEmpty
            change (⨆ P : I,
              fixedGeometryOracleExpectedLength E g P n) ≤ 2
            simp
        | inr hNonempty =>
            letI : Nonempty I := hNonempty
            apply ciSup_le
            intro P
            exact hExpectedTwo E n P P.2.1
      have hrowNonneg : ∀ᶠ n in atTop, 0 ≤ row n := by
        filter_upwards [hSlice] with n hn
        let P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} :=
          ⟨hn.choose, hn.choose_spec⟩
        have hbdd : BddAbove (Set.range fun Q :
            {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n} =>
              fixedGeometryOracleExpectedLength E g Q n) := by
          exact ⟨2, by
            rintro y ⟨Q, rfl⟩
            exact hExpectedTwo E n Q Q.2.1⟩
        exact (integral_nonneg fun _ => ENNReal.toReal_nonneg).trans
          (le_ciSup hbdd P)
      have hzeroCobounded :
          IsCoboundedUnder (· ≤ ·) atTop (fun _ : ℕ => (0 : ℝ)) := by
        change ∃ b, ∀ a, (∀ᶠ _n : ℕ in atTop, (0 : ℝ) ≤ a) → b ≤ a
        exact ⟨0, fun a ha => ha.exists.choose_spec⟩
      have hrowBounded : IsBoundedUnder (· ≤ ·) atTop row := by
        change ∃ b, ∀ᶠ n in atTop, row n ≤ b
        exact ⟨2, Filter.Eventually.of_forall hrowTwo⟩
      change 0 ≤ Filter.limsup row atTop
      rw [← Filter.limsup_const (f := (atTop : Filter ℕ)) (0 : ℝ)]
      exact Filter.limsup_le_limsup hrowNonneg
        hzeroCobounded hrowBounded
    have hvaluesBdd :
        BddBelow (Set.range (fun E :
            {E : OracleProcedure 𝒳 N k c epsilon //
              FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ E} =>
          fixedGeometryRisk N k c epsilon g E.1 t0)) :=
      ⟨0, by
        rintro y ⟨E, rfl⟩
        exact hriskNonneg E⟩
    have hvalue :
        fixedGeometryValueTotal N k c epsilon alpha ⟨g, hg⟩ t0 ≤
          C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) := by
      exact (ciInf_le hvaluesBdd ⟨C, hHonest⟩).trans hRisk
    simpa [C0, L] using hvalue

end CausalSmith.Stat.TransportedLateStrengthFrontier
