/-
# Uniform finite-cell unknown-weight attainment
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_RegularCellUnknownWeightAttainment
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_OracleConverse
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.FiniteCellBridge

set_option linter.style.longLine false

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: thm:finite-cell-unknown-weight-attainment
/-- The uniform finite-cell submodel's sample-only collision-scaled rule is
honest and matches the oracle converse order, on the same arbitrary measurable
carrier as the regular-cell and global results. -/
theorem finite_cell_unknown_weight_attainment
    (N k : ℕ → ℕ) (c epsilon alpha : ℝ)
    (hc : 0 < c) -- @realizes c(c∈(0,∞))
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1)
      -- @realizes \alpha(noncoverage in (0,1))
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
      -- @realizes N_n(N_n/n→c)
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ =>
      (k n : ℝ) / Real.sqrt n) atTop (𝓝 0))
      -- @realizes k_n(positive, diverging, and o(√n))
    (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳, ∀ i, MeasurableSet {cell i})
    (hTwo : ∀ n (P : TransportedArray 𝒳),
      FiniteCellClass P N k c epsilon n →
      TwoSampleArray P N c)
    (hCell : ∀ n (P : TransportedArray 𝒳),
      FiniteCellClass P N k c epsilon n →
      FiniteCellSource P k n)
    (hDegrade : ∀ n (P : TransportedArray 𝒳),
      FiniteCellClass P N k c epsilon n →
      DegradingArray P k) :
    let Bc := 32 * (1 + c⁻¹)
    let L := Real.sqrt (2 * Bc / alpha)
    let C0 := max 2 (4 * Real.sqrt 2 * L + 8 * Bc)
      -- @realizes C_0(constructive finite-cell upper constant)
    0 < C0 ∧
    ∃ C : FiniteCellProcedure 𝒳 N k,
      (∀ n (P : TransportedArray 𝒳), FiniteCellClass P N k c epsilon n →
        ∀ᵐ s ∂(twoSampleLaw P N n),
          C.set n s = finiteCellInversion (k n) n (N n) L s.1 s.2) ∧
      FiniteCellHonest N k c epsilon alpha C ∧
      (∀ t0 : ℝ, 0 < t0 → -- @realizes t_0(positive frontier threshold)
        feasibleFiniteCellRisk N k c epsilon C t0 ≤
          C0 *
            min 1 (t0 ^ (-1 / 2 : ℝ))) ∧
      (∀ t0 : ℝ, 0 < t0 → -- @realizes t_0(positive frontier threshold)
        3 * (1 - alpha) ^ 2 / 16 *
            min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
          ⨅ C : {C : FiniteCellProcedure 𝒳 N k //
            FiniteCellHonest N k c epsilon alpha C},
            feasibleFiniteCellRisk N k c epsilon C.1 t0) := by
  have hClass :=
    finiteCellClass_inhabited N k c epsilon hCarrier hc hepsilon hN hkPos hkInf
      hkRoot
  dsimp
  classical
  let Bc : ℝ := 32 * (1 + c⁻¹)
  let L : ℝ := Real.sqrt (2 * Bc / alpha)
  let C0 : ℝ := max 2 (4 * Real.sqrt 2 * L + 8 * Bc)
  let x : ℝ := 4 + 3 / c
  let a : ℝ := (Real.sqrt x)⁻¹
  let epsilonBar : ℝ := 1 / 4 + (1 / 2) * a
  have hx : 4 < x := by
    dsimp [x]
    have hdiv : 0 < 3 / c := div_pos (by norm_num) hc
    nlinarith
  have hsqrtSq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_trans (by norm_num) hx.le)
  have hsqrtPos : 0 < Real.sqrt x := by positivity
  have hsqrtTwo : 2 < Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  have haPos : 0 < a := by
    dsimp [a]
    positivity
  have haHalf : a < 1 / 2 := by
    dsimp [a]
    rw [inv_eq_one_div, div_lt_iff₀ hsqrtPos]
    nlinarith
  have hBar : 0 < epsilonBar ∧ epsilonBar < 1 / 2 := by
    dsimp [epsilonBar]
    constructor <;> nlinarith
  have haMul : a * Real.sqrt x = 1 := by
    dsimp [a]
    exact inv_mul_cancel₀ hsqrtPos.ne'
  have hepsSqrt : 1 ≤ epsilonBar * Real.sqrt x := by
    have hsqrtNonneg := Real.sqrt_nonneg x
    dsimp [epsilonBar]
    nlinarith
  have hinvLeSqrt : epsilonBar⁻¹ ≤ Real.sqrt x := by
    rw [inv_eq_one_div, div_le_iff₀ hBar.1]
    simpa [mul_comm] using hepsSqrt
  have hinvSq : epsilonBar⁻¹ ^ 2 ≤ x := by
    calc
      epsilonBar⁻¹ ^ 2 ≤ (Real.sqrt x) ^ 2 := by
        gcongr
      _ = x := hsqrtSq
  let B : ℝ := 8 * (epsilonBar⁻¹ ^ 2 + c⁻¹)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hBLe : B ≤ Bc := by
    dsimp [B, Bc, x] at hinvSq ⊢
    rw [div_eq_mul_inv] at hinvSq
    nlinarith
  have hBcPos : 0 < Bc := by
    dsimp [Bc]
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    positivity
  have hLreg : Real.sqrt (2 * B / alpha) ≤ L := by
    dsimp [L]
    apply Real.sqrt_le_sqrt
    have halphaPos := halpha.1
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBLe (by norm_num)) halphaPos.le
  have hreg :=
    regular_cell_unknown_weight_attainment
      (𝒳 := 𝒳) N k c epsilonBar alpha 1 1 hc hBar halpha
      ⟨by norm_num, by norm_num⟩ (by norm_num) hN hkPos hkInf hkRoot hCarrier
      (fun _ _ hP => hP.1.twoSampleArray)
      (fun _ _ hP => hP.1.instrumentOverlap)
      (fun _ _ hP => hP.1.degradingArray)
  dsimp only at hreg
  obtain ⟨hCregPos, Creg, hCregSet, hCregHonest, hCregRisk, _⟩ :=
    hreg L hLreg
  have hupperBridge :=
    finiteCellProcedure_upper_bridge
      (𝒳 := 𝒳) N k c epsilon epsilonBar alpha L hBar hClass
      Creg (by
        intro n P hP
        filter_upwards
          [finiteCellProcedure_eq_regularCellSet_ae N k L n P hP,
            hCregSet n P (hP.toRegularFiniteCellClass hBar),
            regularCellProcedure_set_eq_ambient_ae L n P
              (hP.toRegularFiniteCellClass hBar)]
          with s hfin hreg hproc
        exact hfin.trans (hproc.trans hreg.symm))
      hCregHonest
  have hC0pos : 0 < C0 :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨hC0pos, finiteCellProcedure (𝒳 := 𝒳) N k L, ?_, ?_,
    ?_, ?_⟩
  · intro n P hP
    filter_upwards with s
    rfl
  · exact hupperBridge.1
  · intro t0 ht0
    have hrisk :
        regularCellRisk N k c epsilonBar 1 1 Creg t0 ≤
          max 2 (4 * Real.sqrt 2 * L + 8 * B) *
            min 1 (t0 ^ (-1 / 2 : ℝ)) := by
      simpa [B] using hCregRisk t0 ht0
    have hconst :
        max 2 (4 * Real.sqrt 2 * L + 8 * B) ≤ C0 := by
      dsimp [C0]
      apply max_le_max le_rfl
      gcongr
    have hminNonneg :
        0 ≤ min 1 (t0 ^ (-1 / 2 : ℝ)) :=
      le_min (by norm_num) (Real.rpow_nonneg ht0.le _)
    exact (hupperBridge.2 t0).trans
      (hrisk.trans (mul_le_mul_of_nonneg_right hconst hminNonneg))
  · intro t0 ht0
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
        ext y
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
    have hsliceFinite :
        ∀ n P, fixedGeometrySlice P g N k c epsilon n →
          FiniteCellClass P N k c epsilon n := by
      intro n P hP
      have hsource : FiniteCellSource P k n := by
        refine ⟨hkPos n, ?_, cell n, hcell n, ?_, ?_, ?_, ?_⟩
        · rw [hP.2.1]
          exact hμ n
        · rw [hP.2.1]
          exact hrange n
        · intro i
          rw [hP.2.1]
          exact hatom n i
        · rw [hP.2.1]
          rfl
        · filter_upwards with y
          rw [hP.2.2.2.2, show g.propensity n y = 1 / 2 by rfl]
      exact { hP.1 with finiteCellSource := hsource }
    have hrangeMeas (n : ℕ) : MeasurableSet (Set.range (cell n)) := by
      rw [show Set.range (cell n) = ⋃ i, {cell n i} by
        ext y
        simp]
      exact MeasurableSet.iUnion (hcell n)
    let sampleSupport (n : ℕ) (s : TwoSample 𝒳 n (N n)) : Prop :=
      (∀ i, (s.1 i).1 ∈ Set.range (cell n)) ∧
        ∀ j, s.2 j ∈ Set.range (cell n)
    have hsampleSupportMeas (n : ℕ) :
        MeasurableSet {s : TwoSample 𝒳 n (N n) | sampleSupport n s} := by
      rw [show {s : TwoSample 𝒳 n (N n) | sampleSupport n s} =
          (⋂ i, {s | (s.1 i).1 ∈ Set.range (cell n)}) ∩
            ⋂ j, {s | s.2 j ∈ Set.range (cell n)} by
        ext s
        simp [sampleSupport]]
      exact (MeasurableSet.iInter fun i =>
          (hrangeMeas n).preimage
            (measurable_fst.comp
              ((measurable_pi_apply i).comp measurable_fst))).inter
        (MeasurableSet.iInter fun j =>
          (hrangeMeas n).preimage
            ((measurable_pi_apply j).comp measurable_snd))
    have hfixed :=
      (fixed_geometry_frontier N k c epsilon alpha g hc hN hkPos hkInf
        hkRoot hepsilon hg
        (fun _ _ hP => hP.1.twoSampleArray)
        (fun _ _ hP => hP.1.instrumentOverlap)
        (fun _ _ hP => hP.1.weightEnvelope)
        (fun _ _ hP => hP.1.weightSecondMoment)
        (fun _ _ hP => hP.1.degradingArray)
        halpha t0 ht0).1
    refine hfixed.trans ?_
    letI : Nonempty {C : FiniteCellProcedure 𝒳 N k //
        FiniteCellHonest N k c epsilon alpha C} :=
      ⟨⟨finiteCellProcedure (𝒳 := 𝒳) N k L, hupperBridge.1⟩⟩
    apply le_ciInf
    intro Ccell
    let C := Ccell.1
    let D : OracleProcedure 𝒳 N k c epsilon := {
      set := fun n input =>
        if sampleSupport n input.1 then C.set n input.1
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
              sampleSupport n p.1 ∧ p.2 ∈ C.set n p.1} := by
          simpa [sampleSupport] using C.measurableGraph n (cell n) (hcell n)
        have hTheta :
            MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
              p.2 ∈ parameterSpace} :=
          (by simp [parameterSpace] :
            MeasurableSet parameterSpace).preimage measurable_snd
        rw [show {p : TwoSample 𝒳 n (N n) × ℝ |
              p.2 ∈ (if sampleSupport n p.1 then
                C.set n p.1 else parameterSpace)} =
            {p | sampleSupport n p.1 ∧ p.2 ∈ C.set n p.1} ∪
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
        {source | ∀ i, (source i).1 ∈ Set.range (cell n)}
      let TG : Set (TargetSample 𝒳 (N n)) :=
        {target | ∀ j, target j ∈ Set.range (cell n)}
      have hSGmeas : MeasurableSet SG := by
        rw [show SG = ⋂ i,
            {source | (source i).1 ∈ Set.range (cell n)} by
          ext source
          simp [SG]]
        exact MeasurableSet.iInter fun i =>
          (hrangeMeas n).preimage
            (measurable_fst.comp (measurable_pi_apply i))
      have hTGmeas : MeasurableSet TG := by
        rw [show TG = ⋂ j,
            {target | target j ∈ Set.range (cell n)} by
          ext target
          simp [TG]]
        exact MeasurableSet.iInter fun j =>
          (hrangeMeas n).preimage (measurable_pi_apply j)
      have hsourceXAE :
          ∀ᵐ y ∂sourceXLaw P n, y ∈ Set.range (cell n) := by
        apply (mem_ae_iff_prob_eq_one (hrangeMeas n)).2
        rw [hP.2.1]
        exact hrange n
      have hsourceObsAE :
          ∀ᵐ o ∂sourceObsLaw P n, o.1 ∈ Set.range (cell n) := by
        unfold sourceXLaw at hsourceXAE
        exact ae_of_ae_map measurable_fst.aemeasurable hsourceXAE
      have hSGAE :
          ∀ᵐ source ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n),
            source ∈ SG := by
        apply Measure.ae_pi_le_pi
        exact Filter.eventually_pi fun _ => hsourceObsAE
      have htargetXAE :
          ∀ᵐ y ∂targetXLaw P n, y ∈ Set.range (cell n) := by
        apply (mem_ae_iff_prob_eq_one (hrangeMeas n)).2
        rw [hP.2.2.1]
        exact hrange n
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
        ∀ n P, fixedGeometrySlice P g N k c epsilon n →
          ∀ᵐ s ∂twoSampleLaw P N n,
            fixedGeometryOracleSet D g n s = C.set n s := by
      intro n P hP
      filter_upwards [hsupportAE n P hP] with s hs
      simp [fixedGeometryOracleSet, D, C, hs]
    have hcoverageEq :
        ∀ n P, fixedGeometrySlice P g N k c epsilon n →
          fixedGeometryOracleCoverage D g P n =
            finiteCellCoverage C n P := by
      intro n P hP
      unfold fixedGeometryOracleCoverage finiteCellCoverage
      congr 1
      apply measure_congr
      filter_upwards [hsetEq n P hP] with s hs
      change (targetCACE P n ∈ fixedGeometryOracleSet D g n s) =
        (targetCACE P n ∈ C.set n s)
      rw [hs]
    have hlengthEq :
        ∀ n P, fixedGeometrySlice P g N k c epsilon n →
          fixedGeometryOracleExpectedLength D g P n =
            finiteCellExpectedLength C n P := by
      intro n P hP
      unfold fixedGeometryOracleExpectedLength finiteCellExpectedLength
      apply integral_congr_ae
      filter_upwards [hsetEq n P hP] with s hs
      rw [hs]
    have hslice :
        ∀ᶠ n in atTop, ∃ P : TransportedArray 𝒳,
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n :=
      fixedGeometrySlice_eventually_inhabited g N k c epsilon t0 hc
        hepsilon ht0 hg hN hkPos hkInf hkRoot
    let covC : ℕ → ℝ := fun n =>
      coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n} =>
        finiteCellCoverage C n P
    let covF : ℕ → ℝ := fun n =>
      coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n} =>
        fixedGeometryOracleCoverage D g P n
    have hcoverageRange : ∀ n P,
        FiniteCellClass P N k c epsilon n →
          0 ≤ finiteCellCoverage C n P ∧
            finiteCellCoverage C n P ≤ 1 := by
      intro n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
    have hcovRows : ∀ᶠ n in atTop, covC n ≤ covF n := by
      filter_upwards [hslice] with n hn
      obtain ⟨P0, hP0, _⟩ := hn
      letI : Nonempty {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n} :=
        ⟨⟨P0, hP0⟩⟩
      obtain ⟨PC, hPC⟩ := hClass n
      letI : Nonempty {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n} := ⟨⟨PC, hPC⟩⟩
      change (coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n} => finiteCellCoverage C n P) ≤
        coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n} =>
            fixedGeometryOracleCoverage D g P n
      rw [coverageInfOrOne_of_nonempty, coverageInfOrOne_of_nonempty]
      apply le_ciInf
      intro P
      have hbdd : BddBelow (Set.range fun Q :
          {Q : TransportedArray 𝒳 //
            FiniteCellClass Q N k c epsilon n} =>
            finiteCellCoverage C n Q) :=
        ⟨0, by
          rintro y ⟨Q, rfl⟩
          exact (hcoverageRange n Q Q.2).1⟩
      exact (ciInf_le hbdd
        ⟨P, hsliceFinite n P P.2⟩).trans_eq
          (hcoverageEq n P P.2).symm
    have hcovCnonneg : ∀ n, 0 ≤ covC n := by
      intro n
      letI : Nonempty {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n} :=
        ⟨⟨(hClass n).choose, (hClass n).choose_spec⟩⟩
      change 0 ≤ coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n} => finiteCellCoverage C n P
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
          exact (hcoverageRange n P (hsliceFinite n P P.2)).1⟩
      exact (ciInf_le hbdd ⟨P0, hP0⟩).trans
        ((hcoverageEq n P0 hP0).le.trans
          (hcoverageRange n P0 (hsliceFinite n P0 hP0)).2)
    have hcovCbounded : IsBoundedUnder (· ≥ ·) atTop covC := by
      change ∃ b, ∀ᶠ n in atTop, b ≤ covC n
      exact ⟨0, Filter.Eventually.of_forall hcovCnonneg⟩
    have hcovFcobounded : IsCoboundedUnder (· ≥ ·) atTop covF := by
      change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ covF n) → a ≤ b
      refine ⟨1, fun a ha => ?_⟩
      have haone := (ha.and hcovFone).exists.choose_spec
      exact haone.1.trans haone.2
    have hDhonest :
        FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ D := by
      refine ⟨Ccell.2.1, Ccell.2.2.1, Ccell.2.2.2.trans ?_⟩
      exact Filter.liminf_le_liminf hcovRows hcovCbounded hcovFcobounded
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
    have hfiniteExpectedTwo : ∀ n P,
        FiniteCellClass P N k c epsilon n →
          finiteCellExpectedLength C n P ≤ 2 := by
      intro n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      exact (integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        (integrable_const 2)
        (Filter.Eventually.of_forall fun s =>
          hsetLengthTwo (C.set n s))).trans_eq (by simp)
    let rowF : ℕ → ℝ := fun n =>
      ⨆ P : {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n},
        fixedGeometryOracleExpectedLength D g P n
    let rowC : ℕ → ℝ := fun n =>
      ⨆ P : {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n ∧
            t0 ≤ effectiveStrength P n},
        finiteCellExpectedLength C n P
    have hrowRisk : ∀ᶠ n in atTop, rowF n ≤ rowC n := by
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
            FiniteCellClass Q N k c epsilon n ∧
              t0 ≤ effectiveStrength Q n} =>
            finiteCellExpectedLength C n Q) :=
        ⟨2, by
          rintro y ⟨Q, rfl⟩
          exact hfiniteExpectedTwo n Q Q.2.1⟩
      exact (hlengthEq n P P.2.1).le.trans
        (le_ciSup hbdd ⟨P, hsliceFinite n P P.2.1, P.2.2⟩)
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
          exact hfiniteExpectedTwo n Q (hsliceFinite n Q Q.2.1)⟩
      exact (integral_nonneg fun _ => ENNReal.toReal_nonneg).trans
        (le_ciSup hbdd P)
    have hrowCtwo : ∀ n, rowC n ≤ 2 := by
      intro n
      cases isEmpty_or_nonempty
          {P : TransportedArray 𝒳 //
            FiniteCellClass P N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} with
      | inl h =>
          letI := h
          simp [rowC]
      | inr h =>
          letI := h
          apply ciSup_le
          intro P
          exact hfiniteExpectedTwo n P P.2.1
    have hriskDC :
        fixedGeometryRisk N k c epsilon g D t0 ≤
          feasibleFiniteCellRisk N k c epsilon C t0 := by
      have hFcob : IsCoboundedUnder (· ≤ ·) atTop rowF := by
        change ∃ b, ∀ a, (∀ᶠ n in atTop, rowF n ≤ a) → b ≤ a
        refine ⟨0, fun a ha => ?_⟩
        have h := (hrowFnonneg.and ha).exists.choose_spec
        exact h.1.trans h.2
      have hCbdd : IsBoundedUnder (· ≤ ·) atTop rowC := by
        change ∃ b, ∀ᶠ n in atTop, rowC n ≤ b
        exact ⟨2, Filter.Eventually.of_forall hrowCtwo⟩
      exact Filter.limsup_le_limsup hrowRisk hFcob hCbdd
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
    exact (ciInf_le hvaluesBdd ⟨D, hDhonest⟩).trans hriskDC

end CausalSmith.Stat.TransportedLateStrengthFrontier
