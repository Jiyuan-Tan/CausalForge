/- Extracting an estimator-wise hard family from the one-arm source risk. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.LowerTransfer

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set

private abbrev BinObs := CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

-- @node: oneArmMinimaxRisk_hard_family_of_lt
/-- If [the alphabet is nonempty](hyp:hd) and [the overlap constant is positive](hyp:he0) and [the
  overlap constant is below one half](hyp:he1) and [the logarithmic scale satisfies its stated
  bound](hyp:hL), [any level strictly below the one-arm minimax risk is attained as a lower bound
  against every measurable estimator by a control-zero source law](goal). -/
lemma oneArmMinimaxRisk_hard_family_of_lt {n d : ℕ} {epsilon L : ℝ}
    (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hL : L < CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk n d epsilon) :
    ∀ est : (Fin n → BinObs d) → ℝ, Measurable est →
      ∃ P : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon,
        L ≤ CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨P0, _htau0, _hv0, _hP0⟩ :=
    endpoint_null_exact (n := n) hd he0 he1
  let hP0class : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ExperimentClass
      n epsilon P0.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n) :=
    ⟨he0, he1.le, rfl, P0.2.1⟩
  let Pzero : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.eraseControlLaw_controlZero P0.1 hP0class
  letI : Nonempty
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon) :=
    ⟨Pzero⟩
  intro est hest
  let est' : {f : (Fin n → BinObs d) → ℝ // Measurable f} := ⟨est, hest⟩
  have hb : BddAbove (Set.range (fun P :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon ↦
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
        est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1))) := by
    refine ⟨((∑ sample : Fin n → BinObs d, |est sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨P, rfl⟩
    change CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n) est
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1) ≤ _
    rw [← CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_treated_on_controlZero P]
    exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_le_estimator_abs_sum_bound
      P.1 P.2.overlap est
  have hbelow : BddBelow (Set.range (fun e : {f : (Fin n → BinObs d) → ℝ //
      Measurable f} ↦
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmWorstCaseMSE
        n d epsilon e.1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨e, rfl⟩
    unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmWorstCaseMSE
    have hbe : BddAbove (Set.range (fun P :
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon ↦
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          e.1 (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1))) := by
      refine ⟨((∑ sample : Fin n → BinObs d, |e.1 sample|) + 1) ^ 2, ?_⟩
      rintro _ ⟨P, rfl⟩
      change CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n) e.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1) ≤ _
      rw [← CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_treated_on_controlZero P]
      exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_le_estimator_abs_sum_bound
        P.1 P.2.overlap e.1
    have hmse0 : 0 ≤ CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw Pzero.1 n)
        e.1 (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional Pzero.1) := by
      unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
      exact integral_nonneg fun _ => sq_nonneg _
    exact hmse0.trans (le_ciSup hbe Pzero)
  have hinf : CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk n d epsilon ≤
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmWorstCaseMSE
        n d epsilon est := by
    unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk
    exact ciInf_le hbelow est'
  have hsup : L < CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmWorstCaseMSE
      n d epsilon est := hL.trans_le hinf
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmWorstCaseMSE at hsup
  obtain ⟨P, hLP⟩ := (lt_ciSup_iff hb).mp hsup
  exact ⟨P, hLP.le⟩

-- @node: radialSourceHardData_univ_of_strict_oneArm_lower
/-- If [the alphabet is nonempty](hyp:hd) and [the overlap constant is positive](hyp:he0) and [the
  overlap constant is below one half](hyp:he1) and [the strict one-arm lower-bound constant is
  available](hyp:hc) and [the stated lower bound holds](hyp:hlower), [a strict one-arm minimax
  lower bound equips the full control-zero source class with the hard-family certificate carried
  by a radius-channel handle](goal). -/
lemma radialSourceHardData_univ_of_strict_oneArm_lower {n d : ℕ} {epsilon c : ℝ}
    (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (hc : 0 < c)
    (hlower : c * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d <
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk n d epsilon) :
    RadialSourceHardData
      (Set.univ : Set
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon)) := by
  refine ⟨c, hc, ?_⟩
  intro est
  obtain ⟨P, hP⟩ := oneArmMinimaxRisk_hard_family_of_lt
    hd he0 he1 hlower est.1 est.2
  exact ⟨P, Set.mem_univ P, hP⟩

-- @node: radialSourceHardData_univ_of_oneArm_lower
/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1) and [the
  transport scale satisfies the stated condition](hyp:ha) and [the stated lower bound
  holds](hyp:hlower), [a positive non-strict one-arm lower bound yields a hard full source family
  after halving its constant, which supplies the strict level required by the minimax hard-family
  extractor](goal). -/
lemma radialSourceHardData_univ_of_oneArm_lower {n d : ℕ} {epsilon a : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (ha : 0 < a)
    (hlower : a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d ≤
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk n d epsilon) :
    RadialSourceHardData
      (Set.univ : Set
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrate : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d := by
    unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate
    have hone : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
    have hpoly : 0 ≤
        (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2) := by positivity
    linarith
  apply radialSourceHardData_univ_of_strict_oneArm_lower
    hd he0 he1 (c := a / 2) (by positivity)
  exact (by nlinarith : a / 2 *
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d <
        a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d).trans_le hlower

-- @node: radial_source_risk_of_oneArm_lower
/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1) and [the
  transport scale satisfies the stated condition](hyp:ha) and [the stated lower bound
  holds](hyp:hlower), [a positive fixed-sample one-arm lower bound supplies exactly the uniformly
  bounded source-estimator hardness premise required by randomized kernel transport, after the
  standard strict half-constant reduction](goal). -/
lemma radial_source_risk_of_oneArm_lower {n d : ℕ} {epsilon a : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (ha : 0 < a)
    (hlower : a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d ≤
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk n d epsilon) :
    ∀ sourceEst : (Fin n → BinObs d) → ℝ,
      Measurable sourceEst → Causalean.Stat.UniformlyBounded sourceEst →
      ∃ P ∈ (Set.univ : Set
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon)),
        a / 2 * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d ≤
          Causalean.Stat.sqRisk
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            sourceEst
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrate : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d := by
    unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate
    have hone : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
    have hpoly : 0 ≤
        (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2) := by positivity
    linarith
  have hstrict : a / 2 *
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d <
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk n d epsilon :=
    (by nlinarith : a / 2 *
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d <
        a * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d).trans_le hlower
  intro sourceEst hmeas _hbounded
  obtain ⟨P, hP⟩ := oneArmMinimaxRisk_hard_family_of_lt
    hd he0 he1 hstrict sourceEst hmeas
  exact ⟨P, Set.mem_univ P, by
    simpa [Causalean.Stat.sqRisk,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse] using hP⟩

-- @node: radial_source_risk_of_parametric_lower
/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1), [the
  one-arm two-point subexperiment supplies the uniformly bounded source-estimator hardness
  interface at every positive sample size. The strict half-constant permits extraction of an
  actual source law from the minimax infimum and is the fallback used below the radial asymptotic
  cutoff](goal). -/
lemma radial_source_risk_of_parametric_lower {n d : ℕ} {epsilon : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon)
    (he1 : epsilon < 1 / 2) :
    ∀ sourceEst : (Fin n → BinObs d) → ℝ,
      Measurable sourceEst → Causalean.Stat.UniformlyBounded sourceEst →
      ∃ P ∈ (Set.univ : Set
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon)),
        1 / (200 * (n : ℝ)) ≤
          Causalean.Stat.sqRisk
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
            sourceEst
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hparam :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArm_parametric_lower
      he0 he1 n d hn hd
  have hdenom : 100 * (n : ℝ) < 200 * (n : ℝ) := by nlinarith
  have hstrict : 1 / (200 * (n : ℝ)) <
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk n d epsilon :=
    (one_div_lt_one_div_of_lt (by positivity) hdenom).trans_le hparam
  intro sourceEst hmeas _hbounded
  obtain ⟨P, hP⟩ := oneArmMinimaxRisk_hard_family_of_lt
    hd he0 he1 hstrict sourceEst hmeas
  exact ⟨P, Set.mem_univ P, by
    simpa [Causalean.Stat.sqRisk,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse] using hP⟩

-- @node: exists_radial_source_transport_hardness
/-- If [the overlap constant is positive](hyp:he0) and [the overlap constant is below one
  half](hyp:he1), [the proved Zeng one-arm theorem yields constants, a cutoff, and the
  estimator-wise source hardness interface consumed by the Bernoulli channel transport in the
  radius converse](goal). -/
lemma exists_radial_source_transport_hardness {epsilon : ℝ}
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    ∃ a b : ℝ, ∃ N : ℕ, 0 < a ∧ 0 < b ∧
      ∀ n d : ℕ, 0 < n → 0 < d → N ≤ n →
        (d : ℝ) ≤ b * n * Real.log n →
        ∀ sourceEst : (Fin n → BinObs d) → ℝ,
          Measurable sourceEst → Causalean.Stat.UniformlyBounded sourceEst →
          ∃ P ∈ (Set.univ : Set
              (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon)),
            a / 2 * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d ≤
              Causalean.Stat.sqRisk
                (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
                sourceEst
                (CausalSmith.Stat.DiscreteAteMinimaxLoggap.treatedFunctional P.1) := by
  obtain ⟨a, b, N, ha, hb, hlower⟩ :=
    zengOneArmMinimaxLower epsilon ⟨he0, he1⟩
  refine ⟨a, b, N, ha, hb, ?_⟩
  intro n d hn hd hN hdRange
  exact radial_source_risk_of_oneArm_lower hn hd he0 he1 ha
    (hlower n d hd hN hdRange)

-- @node: radialSourceHardData_univ
/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1), [for every
  positive sample size and alphabet, the full control-zero source class is a genuinely hard
  family. The positive (instance-dependent) constant is obtained by normalizing the universal
  one-arm parametric lower bound by the strictly positive source rate](goal). -/
lemma radialSourceHardData_univ {n d : ℕ} {epsilon : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    RadialSourceHardData
      (Set.univ : Set
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ControlZeroLaw n d epsilon)) := by
  let r := CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by
    dsimp [r]
    unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate
    have hone : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
    have hpoly : 0 ≤
        (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2) := by positivity
    linarith
  let c : ℝ := 1 / (200 * (n : ℝ) * r)
  have hc : 0 < c := by dsimp [c]; positivity
  apply radialSourceHardData_univ_of_strict_oneArm_lower
    hd he0 he1 hc
  have hparam :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArm_parametric_lower
      he0 he1 n d hn hd
  have hcr : c * r = 1 / (200 * (n : ℝ)) := by
    dsimp [c]
    field_simp [ne_of_gt hnR, ne_of_gt hr]
  rw [show CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n d = r by rfl,
    hcr]
  have hdenom : 100 * (n : ℝ) < 200 * (n : ℝ) := by nlinarith
  exact (one_div_lt_one_div_of_lt (by positivity) hdenom).trans_le hparam

-- @node: radialSourceHard_of_source_eq_univ
/-- If [the sample is nonempty](hyp:hn) and [the alphabet size satisfies the stated
  condition](hyp:hd) and [the overlap constant is positive](hyp:he0) and [the overlap constant is
  below one half](hyp:he1) and [the source parameter set has the stated form](hyp:hsource), [a
  least-favorable handle whose radial source is the full control-zero class inherits the
  unconditional hard-family certificate](goal). -/
lemma radialSourceHard_of_source_eq_univ {n d : ℕ} {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (hn : 0 < n) (hd : 0 < H.radialCap)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hsource : H.radialSource = Set.univ) :
    RadialSourceHard H := by
  rw [RadialSourceHard, hsource]
  exact radialSourceHardData_univ hn hd he0 he1

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
