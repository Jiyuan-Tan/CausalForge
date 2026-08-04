/-
# Regular-cell unknown-weight attainment
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.CellEstimators
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_FixedGeometryFrontier
import Causalean.Stat.UStatistic.Basic
import Causalean.Stat.UStatistic.Variance
import Causalean.Stat.Sample.CollisionEstimator
import Causalean.Stat.Minimax.HonestConfidenceSet
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.MultinomialMoments

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: thm:regular-cell-unknown-weight-attainment
/-- With known regular source-cell probabilities and known propensity, the
cross-averaged rule does not use the transport weight and attains the oracle
frontier order; the uniform fixed geometry supplies the matching converse. -/
theorem regular_cell_unknown_weight_attainment
    (N k : ℕ → ℕ) (c epsilon alpha cminus cplus : ℝ)
    (hc : 0 < c) -- @realizes c(c∈(0,∞))
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1)
      -- @realizes \alpha(noncoverage in (0,1))
    (hcminus : 0 < cminus ∧ cminus ≤ 1)
    (hcplus : 1 ≤ cplus)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
      -- @realizes N_n(N_n/n→c)
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ =>
      (k n : ℝ) / Real.sqrt n) atTop (𝓝 0))
      -- @realizes k_n(positive, diverging, and o(√n))
    (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳, ∀ i, MeasurableSet {cell i})
    (hTwo : ∀ n (P : TransportedArray 𝒳),
      RegularFiniteCellClass P N k c epsilon cminus cplus n →
        TwoSampleArray P N c)
    (hOverlap : ∀ n (P : TransportedArray 𝒳),
      RegularFiniteCellClass P N k c epsilon cminus cplus n →
        InstrumentOverlap P n epsilon)
    (hDegrade : ∀ n (P : TransportedArray 𝒳),
      RegularFiniteCellClass P N k c epsilon cminus cplus n →
        DegradingArray P k) :
    let B := 8 * (epsilon⁻¹ ^ 2 + c⁻¹)
    ∀ L : ℝ, Real.sqrt (2 * B / alpha) ≤ L →
      let C0 := max 2 (4 * Real.sqrt 2 * L + 8 * B)
        -- @realizes C_0(constructive regular-cell upper constant)
      0 < C0 ∧
      ∃ C : RegularCellProcedure 𝒳 N k,
        (∀ n (P : TransportedArray 𝒳),
          ∀ hP : RegularFiniteCellClass P N k c epsilon cminus cplus n,
          ∀ᵐ s ∂(twoSampleLaw P N n),
            C.set n (regularCellInputOfClass P hP s) =
              regularCellInversion (sourceCellMass P n) (P.propensity n)
                L s.1 s.2) ∧
        RegularCellHonest N k c epsilon alpha cminus cplus C ∧
        (∀ t0 : ℝ, 0 < t0 → -- @realizes t_0(positive frontier threshold)
          regularCellRisk N k c epsilon cminus cplus C t0 ≤
            C0 *
              min 1 (t0 ^ (-1 / 2 : ℝ))) ∧
        (∀ t0 : ℝ, 0 < t0 → -- @realizes t_0(positive frontier threshold)
          3 * (1 - alpha) ^ 2 / 16 *
              min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
            ⨅ C : {C : RegularCellProcedure 𝒳 N k //
              RegularCellHonest N k c epsilon alpha cminus cplus C},
              regularCellRisk N k c epsilon cminus cplus C.1 t0) := by
  have hClass :=
      regularFiniteCellClass_inhabited N k c epsilon cminus cplus hCarrier hc
      hepsilon hcminus hcplus hN hkPos hkInf hkRoot
  dsimp
  intro L hL
  let B : ℝ := 8 * (epsilon⁻¹ ^ 2 + c⁻¹)
  let C0 : ℝ := max 2 (4 * Real.sqrt 2 * L + 8 * B)
  have hB : B = regularCellVarianceConstant epsilon c := rfl
  have hBnonneg : 0 ≤ B := by
    unfold B
    positivity
  have hLnonneg : 0 ≤ L := by
    exact (Real.sqrt_nonneg _).trans hL
  have hC0pos : 0 < C0 := by
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨hC0pos, regularCellProcedure (𝒳 := 𝒳) N k L, ?_, ?_, ?_, ?_⟩
  · intro n P hP
    exact regularCellProcedure_set_eq_ambient_ae L n P hP
  · refine ⟨halpha.1, halpha.2, ?_⟩
    have hrowEq :
        (fun n => coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
            RegularFiniteCellClass P N k c epsilon cminus cplus n} =>
          regularCellCoverage
            (regularCellProcedure (𝒳 := 𝒳) N k L) n P) =
          (fun n => ⨅ P : {P : TransportedArray 𝒳 //
              RegularFiniteCellClass P N k c epsilon cminus cplus n},
            regularCellCoverage
              (regularCellProcedure (𝒳 := 𝒳) N k L) n P) := by
      funext n
      obtain ⟨P, hP⟩ := hClass n
      simp [coverageInfOrOne, Causalean.Stat.coverageInfOrOne, show Nonempty {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilon cminus cplus n} from
          ⟨⟨P, hP⟩⟩]
    rw [hrowEq]
    exact regularCellProcedure_coverage_liminf
      N k c epsilon alpha cminus cplus L hc hepsilon halpha
      hcminus hcplus hN hkPos hkInf hkRoot hCarrier (hB ▸ hL)
  · intro t0 ht0
    classical
    have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      eventually_atTop.2 ⟨1, fun n hn => Nat.zero_lt_of_lt hn⟩
    have hNratio :
        ∀ᶠ n : ℕ in atTop, c / 2 < (N n : ℝ) / (n : ℝ) :=
      (tendsto_order.1 hN).1 _ (by linarith)
    obtain ⟨m : ℕ, hm : 2 / c < m⟩ := exists_nat_gt (2 / c)
    have hm_event : ∀ᶠ n : ℕ in atTop, m ≤ n :=
      eventually_atTop.2 ⟨m, fun _ hn => hn⟩
    have hNtwo : ∀ᶠ n : ℕ in atTop, 2 ≤ N n := by
      filter_upwards [hnpos, hNratio, hm_event] with n hn hratio hmn
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hmnreal : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hc_n : 2 < c * (n : ℝ) := by
        have hcm : 2 < (m : ℝ) * c := (div_lt_iff₀ hc).mp hm
        have hmcn : (m : ℝ) * c ≤ (n : ℝ) * c :=
          mul_le_mul_of_nonneg_right hmnreal hc.le
        nlinarith
      have hNreal : c * (n : ℝ) / 2 < (N n : ℝ) := by
        apply (lt_div_iff₀ hnreal).mp at hratio
        nlinarith
      exact_mod_cast (show (1 : ℝ) < N n by linarith)
    have hbad := regularCell_firstStage_bad_probability
      (𝒳 := 𝒳) N k c epsilon cminus cplus hc hepsilon hcminus hcplus
        hN hkPos hkRoot
    obtain ⟨n0, hgood⟩ :=
      eventually_atTop.1 (hbad.and (hNtwo.and hnpos))
    let ell : ℕ → TransportedArray 𝒳 → ℝ := fun n P =>
      if n0 ≤ n then
        if hP : RegularFiniteCellClass P N k c epsilon cminus cplus n then
          regularCellExpectedLength
            (regularCellProcedure (𝒳 := 𝒳) N k L) n ⟨P, hP⟩
        else 0
      else 0
    have hell_nonneg : ∀ n P,
        RegularFiniteCellClass P N k c epsilon cminus cplus n →
          0 ≤ ell n P := by
      intro n P hP
      unfold ell
      split_ifs <;> simp_all
      · exact integral_nonneg fun _ => ENNReal.toReal_nonneg
    have hell :
        ∀ n P, RegularFiniteCellClass P N k c epsilon cminus cplus n →
          ell n P ≤ C0 *
            min 1 (effectiveStrength P n ^ (-1 / 2 : ℝ)) := by
      intro n P hP
      unfold ell
      split_ifs with hn0 hclass
      · have hgoodn := hgood n hn0
        have hbadn := hgoodn.1 P hP
        have hN2 := hgoodn.2.1
        have hn : 0 < n := hgoodn.2.2
        have hNpos : 0 < N n := lt_of_lt_of_le (by omega) hN2
        letI : IsProbabilityMeasure (sourceObsLaw P n) :=
          hP.1.twoSampleArray.2.1 n
        letI : IsProbabilityMeasure (targetXLaw P n) :=
          hP.1.twoSampleArray.2.2.1 n
        letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
          unfold twoSampleLaw
          infer_instance
        have hcompact := scoreRiskClass_compact_causal_range
          (transportedIVScoreRiskAtoms (𝒳 := 𝒳) N k c epsilon) hP.1
        have hmu : 0 < transportedFirstStage P n := by
          rw [hcompact.2.2.2.1]
          exact hP.1.targetComplierPositivity
        obtain ⟨cell, hcell, hrange, _hmass⟩ := hP.2.2.2.2.2
        have hkappaOne := one_le_regularCell_kish
          P N k c epsilon n hP.1 cell hcell hrange
        have hkappa : 0 < kishDispersion P n :=
          lt_of_lt_of_le zero_lt_one hkappaOne
        have hmem := regularCell_moments_memLp
          P N k c epsilon cminus cplus 0 n hn hNpos hP
            (by simp [parameterSpace])
        have hKintTarget :
            Integrable (regularCellKhat (sourceCellMass P n))
              (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) := by
          have hconst :
              Integrable
                (fun _ : TargetSample 𝒳 (N n) => (1 : ℝ))
                (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) :=
            integrable_const 1
          change Integrable
            (fun target => 1 +
              collisionScale (sourceCellMass P n) target) _
          exact hconst.add (hmem.2.2.integrable (by norm_num))
        have hKint :
            Integrable
              (fun s : TwoSample 𝒳 n (N n) =>
                regularCellKhat (sourceCellMass P n) s.2)
              (twoSampleLaw P N n) := by
          exact hKintTarget.comp_snd _
        have hKmean := regularCell_Khat_mean
          P N k c epsilon cminus cplus n hN2 hP
        have hKbar :
            (∫ s : TwoSample 𝒳 n (N n),
                regularCellKhat (sourceCellMass P n) s.2
                ∂twoSampleLaw P N n) =
              1 + kishDispersion P n := by
          unfold twoSampleLaw
          rw [MeasureTheory.integral_fun_snd]
          simpa using hKmean.1
        have hcollision :
            ∀ target : TargetSample 𝒳 (N n),
              0 ≤ collisionScale (sourceCellMass P n) target := by
          intro target
          unfold collisionScale Causalean.Stat.collisionScale
          apply mul_nonneg
          · positivity
          · apply Finset.sum_nonneg
            intro j hj
            apply Finset.sum_nonneg
            intro l hl
            split_ifs
            · unfold Causalean.Stat.collisionKernel
              split_ifs
              · exact one_div_nonneg.mpr ENNReal.toReal_nonneg
              · norm_num
            · norm_num
        have hpoint := expectedLength_affineInversion_frontier_le_inflated
          (twoSampleLaw P N n)
          (fun s => regularCellOutcomeMoment (sourceCellMass P n)
            (P.propensity n) s.1 s.2)
          (fun s => regularCellReceiptMoment (sourceCellMass P n)
            (P.propensity n) s.1 s.2)
          (fun s => regularCellKhat (sourceCellMass P n) s.2)
          n L (transportedFirstStage P n)
          (1 + kishDispersion P n)
          (4 * B / effectiveStrength P n)
          (kishDispersion P n) (8 * B) (effectiveStrength P n)
          hLnonneg hmu hn
          (fun s => by
            unfold regularCellKhat
            linarith [hcollision s.2])
          hKint hKbar.le
          hbadn
          hkappa (mul_nonneg (by norm_num) hBnonneg)
          hKmean.2
          (by
            have ht : 0 < effectiveStrength P n := by
              unfold effectiveStrength
              positivity
            field_simp [ht.ne']
            ring_nf
            rfl)
          rfl
        have hset :
            regularCellExpectedLength
                (regularCellProcedure (𝒳 := 𝒳) N k L) n ⟨P, hP⟩ =
              ∫ s, setLength
                (affineInversionSet
                  (regularCellOutcomeMoment (sourceCellMass P n)
                    (P.propensity n) s.1 s.2)
                  (regularCellReceiptMoment (sourceCellMass P n)
                    (P.propensity n) s.1 s.2)
                  (L * Real.sqrt
                    (regularCellKhat (sourceCellMass P n) s.2 / n)))
                ∂twoSampleLaw P N n := by
          apply integral_congr_ae
          filter_upwards [regularCellProcedure_set_eq_ambient_ae L n P hP]
            with s hs
          simp only [regularCellExpectedLength, regularCellSet]
          rw [hs, regularCellInversion_eq_affineInversionSet
            (sourceCellMass P n) (P.propensity n) L s.1 s.2 hN2]
          rfl
        rw [hset]
        simpa [C0] using hpoint
      · have ht_nonneg : 0 ≤ effectiveStrength P n := by
          unfold effectiveStrength kishDispersion
          positivity
        have hmin : 0 ≤ min 1 (effectiveStrength P n ^ (-1 / 2 : ℝ)) :=
          le_min (by norm_num) (Real.rpow_nonneg ht_nonneg _)
        exact mul_nonneg (le_of_lt hC0pos) hmin
    have hriskEll :
        abstractClassFrontierRisk
            (fun n P =>
              RegularFiniteCellClass P N k c epsilon cminus cplus n)
            (fun n P => effectiveStrength P n) ell t0 ≤
          C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) :=
      abstractClassFrontierRisk_le
        (fun n P =>
          RegularFiniteCellClass P N k c epsilon cminus cplus n)
        (fun n P => effectiveStrength P n) ell C0 t0
        (le_of_lt hC0pos) ht0 hell_nonneg hell
    calc
      regularCellRisk N k c epsilon cminus cplus
          (regularCellProcedure (𝒳 := 𝒳) N k L) t0 =
          abstractClassFrontierRisk
            (fun n P =>
              RegularFiniteCellClass P N k c epsilon cminus cplus n)
            (fun n P => effectiveStrength P n) ell t0 := by
        unfold regularCellRisk abstractClassFrontierRisk
        apply Filter.limsup_congr
        filter_upwards [eventually_atTop.2 ⟨n0, fun _ hn => hn⟩] with n hn
        congr 1
        funext P
        simp [ell, hn, P.2.1]
      _ ≤ C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) := hriskEll
  · intro t0 ht0
    classical
    choose cell hcell using hCarrier
    let μ : ℕ → Measure 𝒳 := fun n =>
      ∑ i : Fin (k n), (k n : ENNReal)⁻¹ • Measure.dirac (cell n i)
    have hkinv (n : ℕ) :
        (k n : ENNReal) * (k n : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hkPos n)))
        (ENNReal.natCast_ne_top (k n))
    have hμ : ∀ n, IsProbabilityMeasure (μ n) := by
      intro n
      rw [isProbabilityMeasure_iff]
      simp [μ, hkinv n]
    let g : Geometry 𝒳 := {
      sourceX := μ
      targetX := μ
      weight := fun _ _ => 1
      propensity := fun _ _ => 1 / 2
      weight_measurable := fun _ => measurable_const
      propensity_measurable := fun _ => measurable_const
    }
    have hg : AdmissibleGeometry g k epsilon := by
      refine ⟨hμ, hμ, hepsilon.1, hepsilon.2, ?_, ?_, ?_, ?_, ?_⟩
      · intro n x
        dsimp [g]
        constructor
        · exact hepsilon.2.le
        · linarith [hepsilon.2]
      · intro n x
        dsimp [g]
        constructor
        · norm_num
        · have hk1 : (1 : ℝ) ≤ k n := by exact_mod_cast hkPos n
          linarith
      · intro n
        letI : IsProbabilityMeasure (μ n) := hμ n
        simp [g]
      · intro n
        letI : IsProbabilityMeasure (μ n) := hμ n
        have hk1 : (1 : ℝ) ≤ k n := by exact_mod_cast hkPos n
        simpa [g] using hk1
      · intro n A hA
        letI : IsProbabilityMeasure (μ n) := hμ n
        simpa [g, measureReal_def] using
          (ofReal_setIntegral_one (μ n) A).symm
    have hrange (n : ℕ) : μ n (Set.range (cell n)) = 1 := by
      rw [show Set.range (cell n) = ⋃ i, {cell n i} by
        ext x
        simp]
      simp only [μ, Measure.finset_sum_apply, Measure.smul_apply]
      simp [Measure.dirac_apply_of_mem, hkinv n]
    have hatom (n : ℕ) (i : Fin (k n)) :
        (μ n {cell n i}).toReal = (k n : ℝ)⁻¹ := by
      simp only [μ, Measure.finset_sum_apply, Measure.smul_apply]
      rw [Finset.sum_eq_single i]
      · simp [ENNReal.toReal_inv]
      · intro j _ hji
        have hne : cell n j ≠ cell n i :=
          fun h => hji ((cell n).injective h)
        rw [Measure.dirac_apply' _ (hcell n i)]
        simp [hne]
      · simp
    have hcellClass (n : ℕ) : ∃ d : Fin (k n) ↪ 𝒳,
        (∀ i, MeasurableSet {d i}) ∧
          μ n (Set.range d) = 1 ∧
            ∀ i, cminus / k n ≤ (μ n {d i}).toReal ∧
              (μ n {d i}).toReal ≤ cplus / k n := by
      refine ⟨cell n, hcell n, hrange n, ?_⟩
      intro i
      rw [hatom n i]
      have hinv : 0 ≤ (k n : ℝ)⁻¹ := by positivity
      constructor
      · simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hcminus.2 hinv
      · simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hcplus hinv
    let design (n : ℕ) : RegularCellDesign 𝒳 (k n) :=
      ⟨Classical.choose (hcellClass n),
        (Classical.choose_spec (hcellClass n)).1⟩
    have hdesignRange (n : ℕ) :
        μ n (Set.range (design n).cell) = 1 :=
      (Classical.choose_spec (hcellClass n)).2.1
    have hdesignRangeMeas (n : ℕ) :
        MeasurableSet (Set.range (design n).cell) := by
      rw [show Set.range (design n).cell = ⋃ i, {(design n).cell i} by
        ext x
        simp]
      exact MeasurableSet.iUnion (design n).measurableCell
    have hsliceRegular :
        ∀ n P, fixedGeometrySlice P g N k c epsilon n →
          RegularFiniteCellClass P N k c epsilon cminus cplus n := by
      intro n P hP
      refine ⟨hP.1, hkPos n, hcminus.1, hcminus.2, hcplus, ?_⟩
      rw [hP.2.1]
      exact hcellClass n
    let q : ℕ → 𝒳 → ℝ := fun n x =>
      if x ∈ Set.range (cell n) then (k n : ℝ)⁻¹ else 0
    have hrangeMeas (n : ℕ) : MeasurableSet (Set.range (cell n)) := by
      rw [show Set.range (cell n) = ⋃ i, {cell n i} by
        ext x
        simp]
      exact MeasurableSet.iUnion (hcell n)
    have hqmeas (n : ℕ) : Measurable (q n) := by
      exact Measurable.ite (hrangeMeas n) measurable_const measurable_const
    have hmassEq (n : ℕ) :
        (fun x => (μ n {x}).toReal) = q n := by
      funext x
      by_cases hx : x ∈ Set.range (cell n)
      · obtain ⟨i, rfl⟩ := hx
        simp [q, hatom n i]
      · have hzero : μ n {x} = 0 := by
          apply measure_mono_null
          · intro y hy
            have hyx : y = x := hy
            subst y
            exact Set.mem_compl hx
          · rw [measure_compl (hrangeMeas n) (measure_ne_top _ _),
              hrange n, measure_univ]
            simp
        rw [hzero]
        change (0 : ENNReal).toReal = q n x
        rw [ENNReal.toReal_zero]
        simp only [q, hx, ↓reduceIte]
    let sampleSupport (n : ℕ) (s : TwoSample 𝒳 n (N n)) : Prop :=
      (∀ i, (s.1 i).1 ∈ Set.range (design n).cell) ∧
        ∀ j, s.2 j ∈ Set.range (design n).cell
    have hsampleSupportMeas (n : ℕ) :
        MeasurableSet {s : TwoSample 𝒳 n (N n) | sampleSupport n s} := by
      rw [show {s : TwoSample 𝒳 n (N n) | sampleSupport n s} =
          (⋂ i, {s | (s.1 i).1 ∈ Set.range (design n).cell}) ∩
            ⋂ j, {s | s.2 j ∈ Set.range (design n).cell} by
        ext s
        simp [sampleSupport]]
      exact (MeasurableSet.iInter fun i =>
          (hdesignRangeMeas n).preimage
            (measurable_fst.comp
              ((measurable_pi_apply i).comp measurable_fst))).inter
        (MeasurableSet.iInter fun j =>
          (hdesignRangeMeas n).preimage
            ((measurable_pi_apply j).comp measurable_snd))
    have hfixed :=
      (fixed_geometry_frontier N k c epsilon alpha g hc hN hkPos hkInf
        hkRoot hepsilon hg
        (fun n P hP => hTwo n P (hsliceRegular n P hP))
        (fun n P hP => hOverlap n P (hsliceRegular n P hP))
        (fun _ _ hP => hP.1.weightEnvelope)
        (fun _ _ hP => hP.1.weightSecondMoment)
        (fun n P hP => hDegrade n P (hsliceRegular n P hP))
        halpha t0 ht0).1
    refine hfixed.trans ?_
    let Cw := regularCellProcedure (𝒳 := 𝒳) N k L
    have hCw : RegularCellHonest N k c epsilon alpha cminus cplus Cw := by
      refine ⟨halpha.1, halpha.2, ?_⟩
      have hrowEq :
          (fun n => coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
              RegularFiniteCellClass P N k c epsilon cminus cplus n} =>
            regularCellCoverage Cw n P) =
            (fun n => ⨅ P : {P : TransportedArray 𝒳 //
                RegularFiniteCellClass P N k c epsilon cminus cplus n},
              regularCellCoverage Cw n P) := by
        funext n
        obtain ⟨P, hP⟩ := hClass n
        simp [coverageInfOrOne, Causalean.Stat.coverageInfOrOne, show Nonempty {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n} from
            ⟨⟨P, hP⟩⟩]
      rw [hrowEq]
      exact regularCellProcedure_coverage_liminf
        N k c epsilon alpha cminus cplus L hc hepsilon halpha
        hcminus hcplus hN hkPos hkInf hkRoot
        (fun n => ⟨cell n, hcell n⟩) (hB ▸ hL)
    letI : Nonempty {C : RegularCellProcedure 𝒳 N k //
        RegularCellHonest N k c epsilon alpha cminus cplus C} :=
      ⟨⟨Cw, hCw⟩⟩
    apply le_ciInf
    intro Creg
    let C := Creg.1
    let D : OracleProcedure 𝒳 N k c epsilon := {
      set := fun n input =>
        if sampleSupport n input.1 then
          C.set n ⟨input.1, design n,
            fun i => q n ((design n).cell i),
            fun i => input.2.2 ((design n).cell i)⟩
        else parameterSpace
      subset := by
        intro n input
        split_ifs
        · exact C.subset n _
        · exact fun _ h => h
      measurableGraph := by
        intro n w e hw he
        let S : Set (TwoSample 𝒳 n (N n) × ℝ) :=
          {p | sampleSupport n p.1}
        have hS : MeasurableSet S :=
          (hsampleSupportMeas n).preimage measurable_fst
        have hCG :
            MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
              sampleSupport n p.1 ∧
                p.2 ∈ C.set n ⟨p.1, design n,
                  fun i => q n ((design n).cell i),
                  fun i => e ((design n).cell i)⟩} := by
          simpa [sampleSupport] using
            C.measurableGraph n (design n)
              (fun i => q n ((design n).cell i))
              (fun i => e ((design n).cell i))
        have hTheta :
            MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
              p.2 ∈ parameterSpace} :=
          (by simp [parameterSpace] :
            MeasurableSet parameterSpace).preimage measurable_snd
        rw [show {p : TwoSample 𝒳 n (N n) × ℝ |
              p.2 ∈ (if sampleSupport n p.1 then
                C.set n ⟨p.1, design n,
                  fun i => q n ((design n).cell i),
                  fun i => e ((design n).cell i)⟩
                else parameterSpace)} =
            {p | sampleSupport n p.1 ∧
                p.2 ∈ C.set n ⟨p.1, design n,
                  fun i => q n ((design n).cell i),
                  fun i => e ((design n).cell i)⟩} ∪
              (Sᶜ ∩ {p | p.2 ∈ parameterSpace}) by
          ext p
          by_cases hp : sampleSupport n p.1 <;>
            simp [hp, S]]
        exact hCG.union (hS.compl.inter hTheta)
      weightAEInvariant := by
        intro n P hP w w'
        filter_upwards with s
        rfl
    }
    have hsupportAE :
        ∀ n P, fixedGeometrySlice P g N k c epsilon n →
          ∀ᵐ s ∂twoSampleLaw P N n, sampleSupport n s := by
      intro n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (sourceXLaw P n) := by
        unfold sourceXLaw
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      let SG : Set (SourceSample 𝒳 n) :=
        {source | ∀ i, (source i).1 ∈ Set.range (design n).cell}
      let TG : Set (TargetSample 𝒳 (N n)) :=
        {target | ∀ j, target j ∈ Set.range (design n).cell}
      have hSGmeas : MeasurableSet SG := by
        rw [show SG = ⋂ i,
            {source | (source i).1 ∈ Set.range (design n).cell} by
          ext source
          simp [SG]]
        exact MeasurableSet.iInter fun i =>
          (hdesignRangeMeas n).preimage
            (measurable_fst.comp (measurable_pi_apply i))
      have hTGmeas : MeasurableSet TG := by
        rw [show TG = ⋂ j,
            {target | target j ∈ Set.range (design n).cell} by
          ext target
          simp [TG]]
        exact MeasurableSet.iInter fun j =>
          (hdesignRangeMeas n).preimage (measurable_pi_apply j)
      have hsourceXAE :
          ∀ᵐ x ∂sourceXLaw P n, x ∈ Set.range (design n).cell := by
        apply (mem_ae_iff_prob_eq_one (hdesignRangeMeas n)).2
        rw [hP.2.1]
        exact hdesignRange n
      have hsourceObsAE :
          ∀ᵐ o ∂sourceObsLaw P n, o.1 ∈ Set.range (design n).cell := by
        unfold sourceXLaw at hsourceXAE
        exact ae_of_ae_map measurable_fst.aemeasurable hsourceXAE
      have hSGAE :
          ∀ᵐ source ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n),
            source ∈ SG := by
        apply Measure.ae_pi_le_pi
        exact Filter.eventually_pi fun _ => hsourceObsAE
      have htargetXAE :
          ∀ᵐ x ∂targetXLaw P n, x ∈ Set.range (design n).cell := by
        apply (mem_ae_iff_prob_eq_one (hdesignRangeMeas n)).2
        rw [hP.2.2.1]
        exact hdesignRange n
      have hTGAE :
          ∀ᵐ target ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n),
            target ∈ TG := by
        apply Measure.ae_pi_le_pi
        exact Filter.eventually_pi fun _ => htargetXAE
      have hSGone :
          Measure.pi (fun _ : Fin n => sourceObsLaw P n) SG = 1 :=
        (mem_ae_iff_prob_eq_one hSGmeas).1 hSGAE
      have hTGone :
          Measure.pi (fun _ : Fin (N n) => targetXLaw P n) TG = 1 :=
        (mem_ae_iff_prob_eq_one hTGmeas).1 hTGAE
      have hprod :
          twoSampleLaw P N n (SG ×ˢ TG) = 1 := by
        unfold twoSampleLaw
        rw [Measure.prod_prod, hSGone, hTGone]
        simp
      have hprodAE : ∀ᵐ s ∂twoSampleLaw P N n, s ∈ SG ×ˢ TG := by
        exact (mem_ae_iff_prob_eq_one (hSGmeas.prod hTGmeas)).2 hprod
      filter_upwards [hprodAE] with s hs
      exact hs
    have hsetEq :
        ∀ n P (hP : fixedGeometrySlice P g N k c epsilon n),
          ∀ᵐ s ∂twoSampleLaw P N n,
            fixedGeometryOracleSet D g n s = regularCellSet C n P
              (hsliceRegular n P hP) s := by
      intro n P hP
      filter_upwards [hsupportAE n P hP] with s hs
      have hmass : sourceCellMass P n = q n := by
        unfold sourceCellMass
        rw [hP.2.1]
        exact hmassEq n
      have hdesignEq :
          regularCellDesignOfClass P (hsliceRegular n P hP) = design n := by
        simp [regularCellDesignOfClass, design, hsliceRegular, hP.2.1]
      simp [fixedGeometryOracleSet, regularCellSet, regularCellInputOfClass,
        hdesignEq, D, C, hs, g,
        hmass, hP.2.2.2.2]
    have hcoverageEq :
        ∀ n P (hP : fixedGeometrySlice P g N k c epsilon n),
          fixedGeometryOracleCoverage D g P n =
            regularCellCoverage C n ⟨P, hsliceRegular n P hP⟩ := by
      intro n P hP
      unfold fixedGeometryOracleCoverage regularCellCoverage
      congr 1
      apply measure_congr
      filter_upwards [hsetEq n P hP] with s hs
      change (targetCACE P n ∈ fixedGeometryOracleSet D g n s) =
        (targetCACE P n ∈ regularCellSet C n P
          (hsliceRegular n P hP) s)
      rw [hs]
    have hlengthEq :
        ∀ n P (hP : fixedGeometrySlice P g N k c epsilon n),
          fixedGeometryOracleExpectedLength D g P n =
            regularCellExpectedLength C n ⟨P, hsliceRegular n P hP⟩ := by
      intro n P hP
      unfold fixedGeometryOracleExpectedLength regularCellExpectedLength
      apply integral_congr_ae
      filter_upwards [hsetEq n P hP] with s hs
      rw [hs]
    have hslice :
        ∀ᶠ n in atTop, ∃ P : TransportedArray 𝒳,
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n :=
      fixedGeometrySlice_eventually_inhabited g N k c epsilon t0 hc
        hepsilon ht0 hg hN hkPos hkInf hkRoot
    let covR : ℕ → ℝ := fun n =>
      coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n} =>
        regularCellCoverage C n P
    let covF : ℕ → ℝ := fun n =>
      coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n} =>
        fixedGeometryOracleCoverage D g P n
    have hcoverageRange : ∀ n P
        (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n),
          0 ≤ regularCellCoverage C n ⟨P, hP⟩ ∧
            regularCellCoverage C n ⟨P, hP⟩ ≤ 1 := by
      intro n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
    have hcovRows : ∀ᶠ n in atTop, covR n ≤ covF n := by
      filter_upwards [hslice] with n hn
      obtain ⟨P0, hP0, _⟩ := hn
      letI : Nonempty {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n} :=
        ⟨⟨P0, hP0⟩⟩
      obtain ⟨PR, hPR⟩ := hClass n
      letI : Nonempty {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n} :=
        ⟨⟨PR, hPR⟩⟩
      change (coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n} =>
        regularCellCoverage C n P) ≤
          coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} =>
          fixedGeometryOracleCoverage D g P n
      rw [coverageInfOrOne_of_nonempty, coverageInfOrOne_of_nonempty]
      apply le_ciInf
      intro P
      have hbdd : BddBelow (Set.range fun Q :
          {Q : TransportedArray 𝒳 //
            RegularFiniteCellClass Q N k c epsilon cminus cplus n} =>
            regularCellCoverage C n Q) :=
        ⟨0, by
          rintro y ⟨Q, rfl⟩
          exact (hcoverageRange n Q Q.2).1⟩
      exact (ciInf_le hbdd
        ⟨P, hsliceRegular n P P.2⟩).trans_eq
          (hcoverageEq n P P.2).symm
    have hcovRnonneg : ∀ n, 0 ≤ covR n := by
      intro n
      letI : Nonempty {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n} :=
        ⟨⟨(hClass n).choose, (hClass n).choose_spec⟩⟩
      change 0 ≤ coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilon cminus cplus n} =>
          regularCellCoverage C n P
      rw [coverageInfOrOne_of_nonempty]
      exact le_ciInf fun P => (hcoverageRange n P P.2).1
    have hcovFone : ∀ᶠ n in atTop, covF n ≤ 1 := by
      filter_upwards [hslice] with n hn
      obtain ⟨P0, hP0, _⟩ := hn
      letI : Nonempty {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n} := ⟨⟨P0, hP0⟩⟩
      change (coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        fixedGeometrySlice P g N k c epsilon n} =>
          fixedGeometryOracleCoverage D g P n) ≤ 1
      rw [coverageInfOrOne_of_nonempty]
      have hbdd : BddBelow (Set.range fun P :
          {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} =>
            fixedGeometryOracleCoverage D g P n) :=
        ⟨0, by
          rintro y ⟨P, rfl⟩
          change 0 ≤ fixedGeometryOracleCoverage D g P n
          rw [hcoverageEq n P P.2]
          exact (hcoverageRange n P (hsliceRegular n P P.2)).1⟩
      exact (ciInf_le hbdd ⟨P0, hP0⟩).trans
        ((hcoverageEq n P0 hP0).le.trans
          (hcoverageRange n P0 (hsliceRegular n P0 hP0)).2)
    have hcovRbounded : IsBoundedUnder (· ≥ ·) atTop covR := by
      change ∃ b, ∀ᶠ n in atTop, b ≤ covR n
      exact ⟨0, Filter.Eventually.of_forall hcovRnonneg⟩
    have hcovFcobounded : IsCoboundedUnder (· ≥ ·) atTop covF := by
      change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ covF n) → a ≤ b
      refine ⟨1, fun a ha => ?_⟩
      have haone := (ha.and hcovFone).exists.choose_spec
      exact haone.1.trans haone.2
    have hDhonest :
        FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ D := by
      refine ⟨Creg.2.1, Creg.2.2.1, Creg.2.2.2.trans ?_⟩
      exact Filter.liminf_le_liminf hcovRows hcovRbounded hcovFcobounded
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
    have hregularExpectedTwo : ∀ n P
        (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n),
          regularCellExpectedLength C n ⟨P, hP⟩ ≤ 2 := by
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
          hsetLengthTwo (regularCellSet C n P hP s))).trans_eq (by simp)
    let rowF : ℕ → ℝ := fun n =>
      ⨆ P : {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n},
        fixedGeometryOracleExpectedLength D g P n
    let rowR : ℕ → ℝ := fun n =>
      ⨆ P : {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n ∧
            t0 ≤ effectiveStrength P n},
        regularCellExpectedLength C n ⟨P.1, P.2.1⟩
    have hrowRisk : ∀ᶠ n in atTop, rowF n ≤ rowR n := by
      filter_upwards [hslice] with n hn
      obtain ⟨P0, hP0, htP0⟩ := hn
      letI : Nonempty {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n} :=
        ⟨⟨P0, hP0, htP0⟩⟩
      apply ciSup_le
      intro P
      have hbdd : BddAbove (Set.range fun Q :
          {Q : TransportedArray 𝒳 //
            RegularFiniteCellClass Q N k c epsilon cminus cplus n ∧
              t0 ≤ effectiveStrength Q n} =>
            regularCellExpectedLength C n ⟨Q.1, Q.2.1⟩) :=
        ⟨2, by
          rintro y ⟨Q, rfl⟩
          exact hregularExpectedTwo n Q Q.2.1⟩
      exact (hlengthEq n P P.2.1).le.trans
        (le_ciSup hbdd ⟨P, hsliceRegular n P P.2.1, P.2.2⟩)
    have hrowFnonneg : ∀ᶠ n in atTop, 0 ≤ rowF n := by
      filter_upwards [hslice] with n hn
      obtain ⟨P0, hP0, htP0⟩ := hn
      let P : {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n} := ⟨P0, hP0, htP0⟩
      have hbdd : BddAbove (Set.range fun Q :
          {Q : TransportedArray 𝒳 //
            fixedGeometrySlice Q g N k c epsilon n ∧
              t0 ≤ effectiveStrength Q n} =>
            fixedGeometryOracleExpectedLength D g Q n) :=
        ⟨2, by
          rintro y ⟨Q, rfl⟩
          change fixedGeometryOracleExpectedLength D g Q n ≤ 2
          rw [hlengthEq n Q Q.2.1]
          exact hregularExpectedTwo n Q (hsliceRegular n Q Q.2.1)⟩
      exact (integral_nonneg fun _ => ENNReal.toReal_nonneg).trans
        (le_ciSup hbdd P)
    have hrowRtwo : ∀ n, rowR n ≤ 2 := by
      intro n
      cases isEmpty_or_nonempty
          {P : TransportedArray 𝒳 //
            RegularFiniteCellClass P N k c epsilon cminus cplus n ∧
              t0 ≤ effectiveStrength P n} with
      | inl h =>
          letI := h
          simp [rowR]
      | inr h =>
          letI := h
          apply ciSup_le
          intro P
          exact hregularExpectedTwo n P P.2.1
    have hriskDR :
        fixedGeometryRisk N k c epsilon g D t0 ≤
          regularCellRisk N k c epsilon cminus cplus C t0 := by
      have hFcob : IsCoboundedUnder (· ≤ ·) atTop rowF := by
        change ∃ b, ∀ a, (∀ᶠ n in atTop, rowF n ≤ a) → b ≤ a
        refine ⟨0, fun a ha => ?_⟩
        have h := (hrowFnonneg.and ha).exists.choose_spec
        exact h.1.trans h.2
      have hRbdd : IsBoundedUnder (· ≤ ·) atTop rowR := by
        change ∃ b, ∀ᶠ n in atTop, rowR n ≤ b
        exact ⟨2, Filter.Eventually.of_forall hrowRtwo⟩
      exact Filter.limsup_le_limsup hrowRisk hFcob hRbdd
    have hfixedExpectedTwo : ∀ (E : OracleProcedure 𝒳 N k c epsilon) n P,
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
    have hfixedRiskNonneg : ∀ E : OracleProcedure 𝒳 N k c epsilon,
        0 ≤ fixedGeometryRisk N k c epsilon g E t0 := by
      intro E
      let row : ℕ → ℝ := fun n =>
        ⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength E g P n
      have hrow0 : ∀ n, 0 ≤ row n := by
        intro n
        cases isEmpty_or_nonempty
            {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n} with
        | inl h =>
            letI := h
            simp [row]
        | inr h =>
            letI := h
            let P := Classical.choice h
            have hbdd : BddAbove (Set.range fun Q :
                {Q : TransportedArray 𝒳 //
                  fixedGeometrySlice Q g N k c epsilon n ∧
                    t0 ≤ effectiveStrength Q n} =>
                fixedGeometryOracleExpectedLength E g Q n) :=
              ⟨2, by
                rintro y ⟨Q, rfl⟩
                exact hfixedExpectedTwo E n Q Q.2.1⟩
            exact (integral_nonneg fun _ => ENNReal.toReal_nonneg).trans
              (le_ciSup hbdd P)
      have hrow2 : ∀ n, row n ≤ 2 := by
        intro n
        cases isEmpty_or_nonempty
            {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n} with
        | inl h =>
            letI := h
            simp [row]
        | inr h =>
            letI := h
            apply ciSup_le
            intro P
            exact hfixedExpectedTwo E n P P.2.1
      change 0 ≤ Filter.limsup row atTop
      rw [← Filter.limsup_const (f := (atTop : Filter ℕ)) (0 : ℝ)]
      have hzeroCob :
          IsCoboundedUnder (· ≤ ·) atTop (fun _ : ℕ => (0 : ℝ)) := by
        change ∃ b, ∀ a, (∀ᶠ _n : ℕ in atTop, (0 : ℝ) ≤ a) → b ≤ a
        exact ⟨0, fun a ha => ha.exists.choose_spec⟩
      have hrowBdd : IsBoundedUnder (· ≤ ·) atTop row := by
        change ∃ b, ∀ᶠ n in atTop, row n ≤ b
        exact ⟨2, Filter.Eventually.of_forall hrow2⟩
      exact Filter.limsup_le_limsup
        (Filter.Eventually.of_forall hrow0) hzeroCob hrowBdd
    have hvaluesBdd : BddBelow (Set.range fun E :
        {E : OracleProcedure 𝒳 N k c epsilon //
          FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ E} =>
          fixedGeometryRisk N k c epsilon g E.1 t0) :=
      ⟨0, by
        rintro y ⟨E, rfl⟩
        exact hfixedRiskNonneg E⟩
    exact (ciInf_le hvaluesBdd ⟨D, hDhonest⟩).trans hriskDR

/-- The regular-cell design selected from a transported array is unchanged when the sample-size
sequence, regularity constants, and transported array are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.TransportedLateStrengthFrontier.regularCellDesignOfClass.congr_simp

/-- The regular-cell procedure input constructed from a transported array and a two-sample draw is
unchanged when the regularity constants, array, and draw are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.TransportedLateStrengthFrontier.regularCellInputOfClass.congr_simp

end CausalSmith.Stat.TransportedLateStrengthFrontier
