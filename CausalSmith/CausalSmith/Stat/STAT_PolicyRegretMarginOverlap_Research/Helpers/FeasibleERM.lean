/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.ClipBias

/-! Provides measurable evaluation and feasible ERM helper lemmas. -/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

private lemma measurable_boolIndicator_policy_sample_eval {n : ℕ}
    (π : Policy 𝒳) (hπmeas : Measurable π) (i : Fin n) :
    Measurable (fun sample : Fin n → Observation 𝒳 =>
      boolIndicator (π (sample i).X)) := by
  exact (measurable_of_finite (fun b : Bool => boolIndicator b)).comp
    (hπmeas.comp (measurable_observation_X.comp (measurable_pi_apply i)))

private lemma measurable_clippedAIPWScore_sample_eval {n K : ℕ} (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (hμ0meas : ∀ k : Fin K, Measurable (muHat0 k))
    (hμ1meas : ∀ k : Fin K, Measurable (muHat1 k))
    (hemeas : ∀ k : Fin K, Measurable (eHat k)) (i : Fin n) :
    Measurable (fun sample : Fin n → Observation 𝒳 =>
      clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i)) (eHat (assign i))
        (sample i)) := by
  have hO : Measurable (fun sample : Fin n → Observation 𝒳 => sample i) :=
    measurable_pi_apply i
  have hX : Measurable (fun sample : Fin n → Observation 𝒳 => (sample i).X) :=
    measurable_observation_X.comp hO
  have hA : Measurable (fun sample : Fin n → Observation 𝒳 =>
      boolIndicator (sample i).A) :=
    measurable_boolIndicator_observation_A.comp hO
  have hY : Measurable (fun sample : Fin n → Observation 𝒳 => (sample i).Y) :=
    measurable_observation_Y.comp hO
  have hμ0 : Measurable (fun sample : Fin n → Observation 𝒳 =>
      muHat0 (assign i) (sample i).X) :=
    (hμ0meas (assign i)).comp hX
  have hμ1 : Measurable (fun sample : Fin n → Observation 𝒳 =>
      muHat1 (assign i) (sample i).X) :=
    (hμ1meas (assign i)).comp hX
  have hcp : Measurable (fun sample : Fin n → Observation 𝒳 =>
      clippedPropensity q (eHat (assign i)) (sample i).X) :=
    (measurable_clippedPropensity q (hemeas (assign i))).comp hX
  unfold clippedAIPWScore
  exact ((hμ1.sub hμ0).add ((hA.div hcp).mul (hY.sub hμ1))).sub
    (((measurable_const.sub hA).div (measurable_const.sub hcp)).mul (hY.sub hμ0))

private lemma measurable_empiricalWelfareScore_sample {n K : ℕ} (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (hμ0meas : ∀ k : Fin K, Measurable (muHat0 k))
    (hμ1meas : ∀ k : Fin K, Measurable (muHat1 k))
    (hemeas : ∀ k : Fin K, Measurable (eHat k))
    (π : Policy 𝒳) (hπmeas : Measurable π) :
    Measurable (fun sample : Fin n → Observation 𝒳 =>
      empiricalWelfareScore q muHat0 muHat1 eHat assign sample π) := by
  classical
  have hsum : Measurable (fun sample : Fin n → Observation 𝒳 =>
      ∑ i : Fin n, boolIndicator (π (sample i).X) *
        clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i)) (eHat (assign i))
          (sample i)) := by
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      (measurable_boolIndicator_policy_sample_eval π hπmeas i).mul
        (measurable_clippedAIPWScore_sample_eval q muHat0 muHat1 eHat assign
          hμ0meas hμ1meas hemeas i))
  simpa [empiricalWelfareScore] using hsum.const_mul ((n : ℝ)⁻¹)

omit [MeasurableSpace 𝒳] in
private lemma feasibleERM_nearSet_nonempty {n K : ℕ} (q : ℝ)
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (assign : Fin n → Fin K) (sample : Fin n → Observation 𝒳) (hn : 0 < n) :
    ({j : ℕ |
      ∀ j' : ℕ,
        empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j')
          ≤ empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j)
              + (n : ℝ)⁻¹}).Nonempty := by
  classical
  let score : ℕ → ℝ := fun j =>
    empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j)
  let Γ : Fin n → ℝ := fun i =>
    clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i)) (eHat (assign i))
      (sample i)
  have hscore_le : ∀ j, score j ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |Γ i| := by
    intro j
    have hterm : ∀ i : Fin n, boolIndicator (enum j (sample i).X) * Γ i ≤ |Γ i| := by
      intro i
      cases enum j (sample i).X <;> simp [boolIndicator, le_abs_self]
    have hsum :
        (∑ i : Fin n, boolIndicator (enum j (sample i).X) * Γ i)
          ≤ ∑ i : Fin n, |Γ i| :=
      Finset.sum_le_sum (fun i _ => hterm i)
    have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    calc
      score j
          = (n : ℝ)⁻¹ *
              ∑ i : Fin n, boolIndicator (enum j (sample i).X) * Γ i := by
                simp [score, empiricalWelfareScore, Γ]
      _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |Γ i| :=
            mul_le_mul_of_nonneg_left hsum hinv_nonneg
  let S : Set ℝ := Set.range score
  have hSnon : S.Nonempty := Set.range_nonempty score
  have hSbdd : BddAbove S := by
    refine ⟨(n : ℝ)⁻¹ * ∑ i : Fin n, |Γ i|, ?_⟩
    rintro y ⟨j, rfl⟩
    exact hscore_le j
  have hinv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
  have hlt : sSup S - (n : ℝ)⁻¹ < sSup S := sub_lt_self _ hinv_pos
  rcases exists_lt_of_lt_csSup hSnon hlt with ⟨a, haS, ha_lt⟩
  rcases haS with ⟨j, rfl⟩
  refine ⟨j, ?_⟩
  intro j'
  have hj'_le : score j' ≤ sSup S := le_csSup hSbdd ⟨j', rfl⟩
  have hsup_le : sSup S ≤ score j + (n : ℝ)⁻¹ := by linarith
  simpa [score] using hj'_le.trans hsup_le

-- @node: lem:feasible-erm-basic-inequality
/-- `lem:feasible-erm-basic-inequality`. The feasible ERM (`enum`-skeleton,
foldwise cross-fit) is a MEASURABLE `Π`-valued estimator: it is `Π`-valued for
every realized sample, the induced regret map `sample ↦ R_P(π̂_n(sample))` is
measurable (so the `U_n`/`M_n` integrals are well-defined), and against EVERY
comparator `π^b ∈ Π` the `1/n` basic inequality holds; under `OptimalInClass`
it applies in particular to `π^b = π_⋆`. The comparator inequality over ALL of `Π`
is load-bearing on `enum` being a POINTWISE-DENSE skeleton of `Π` (the countable
`Π₀` of `ass:policy-class` that `def:feasible-erm` fixes): `hdense` says every
`π ∈ Π` is a pointwise limit of `enum`-indexed policies, which is what reduces
`sup_Π V̂` to `sup_j V̂(enum j)`. Without it the bare `henum : enum j ∈ Π` would not
license the `Π`-wide near-maximality. -/
lemma feasible_erm_basic_inequality {n K : ℕ} (P : ObservedLaw 𝒳) (q : ℝ)
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (assign : Fin n → Fin K) (policySet : Set (Policy 𝒳)) (dPi : ℕ)
    (hvc : PolicyClassVC policySet dPi) (_hopt : OptimalInClass P policySet)
    (henum : ∀ j, enum j ∈ policySet)
    (hdense : ∀ π ∈ policySet, ∃ seq : ℕ → ℕ,
      ∀ x, ∀ᶠ j in Filter.atTop, enum (seq j) x = π x)
    -- regularity: measurable foldwise plug-in estimators
    (hμ0meas : ∀ k : Fin K, Measurable (muHat0 k))
    (hμ1meas : ∀ k : Fin K, Measurable (muHat1 k))
    (hemeas : ∀ k : Fin K, Measurable (eHat k))
    (hn : 0 < n) :
    Measurable (fun s : Fin n → Observation 𝒳 =>
        lawRegret P (feasibleERM q enum muHat0 muHat1 eHat assign s)) ∧
      ∀ sample : Fin n → Observation 𝒳,
        feasibleERM q enum muHat0 muHat1 eHat assign sample ∈ policySet ∧
          ∀ πb ∈ policySet,
            empiricalWelfareScore q muHat0 muHat1 eHat assign sample πb
              ≤ empiricalWelfareScore q muHat0 muHat1 eHat assign sample
                  (feasibleERM q enum muHat0 muHat1 eHat assign sample) + (n : ℝ)⁻¹
    := by
  classical
  have hπmeas : ∀ π ∈ policySet, Measurable π := hvc.1
  let score : ℕ → (Fin n → Observation 𝒳) → ℝ := fun j sample =>
    empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j)
  let near : (Fin n → Observation 𝒳) → ℕ → Prop := fun sample j =>
    ∀ j' : ℕ, score j' sample ≤ score j sample + (n : ℝ)⁻¹
  let sel : (Fin n → Observation 𝒳) → ℕ := fun sample =>
    sInf {j : ℕ | near sample j}
  have hscore_meas : ∀ j, Measurable (score j) := by
    intro j
    exact measurable_empiricalWelfareScore_sample q muHat0 muHat1 eHat assign
      hμ0meas hμ1meas hemeas (enum j) (hπmeas (enum j) (henum j))
  have hnear_meas : ∀ j, MeasurableSet {sample : Fin n → Observation 𝒳 | near sample j} := by
    intro j
    have hInter : MeasurableSet
        (⋂ j' : ℕ,
          {sample : Fin n → Observation 𝒳 |
            score j' sample ≤ score j sample + (n : ℝ)⁻¹}) := by
      exact MeasurableSet.iInter (fun j' =>
        measurableSet_le (hscore_meas j') ((hscore_meas j).add measurable_const))
    simpa [near, Set.setOf_forall] using hInter
  have hsel_fiber : ∀ j, MeasurableSet {sample : Fin n → Observation 𝒳 | sel sample = j} := by
    intro j
    have hlower_meas :
        MeasurableSet
          {sample : Fin n → Observation 𝒳 | ∀ k : ℕ, k < j → ¬ near sample k} := by
      have hInter : MeasurableSet
          (⋂ k : ℕ,
            {sample : Fin n → Observation 𝒳 | k < j → ¬ near sample k}) := by
        exact MeasurableSet.iInter (fun k => by
          by_cases hk : k < j
          · have hc : MeasurableSet
                ({sample : Fin n → Observation 𝒳 | near sample k}ᶜ) :=
              (hnear_meas k).compl
            simpa [hk, Set.compl_setOf] using hc
          · simp [hk])
      simpa [Set.setOf_forall] using hInter
    have hchar :
        {sample : Fin n → Observation 𝒳 | sel sample = j}
          =
        {sample : Fin n → Observation 𝒳 |
          near sample j ∧ ∀ k : ℕ, k < j → ¬ near sample k} := by
      ext sample
      let A : Set ℕ := {m : ℕ | near sample m}
      have hAne : A.Nonempty := by
        simpa [A, near, score] using
          (feasibleERM_nearSet_nonempty q enum muHat0 muHat1 eHat assign sample hn)
      constructor
      · intro hsel_eq
        change sel sample = j at hsel_eq
        constructor
        · have hs : near sample (sel sample) := by
            simpa [sel, A] using (Nat.sInf_mem hAne)
          rw [hsel_eq] at hs
          exact hs
        · intro k hklt hknear
          have hle : sInf A ≤ k := Nat.sInf_le (by simpa [A] using hknear)
          have hjle : j ≤ k := by simpa [sel, A, hsel_eq] using hle
          exact (not_lt_of_ge hjle) hklt
      · intro h
        change near sample j ∧ (∀ k : ℕ, k < j → ¬ near sample k) at h
        rcases h with ⟨hjnear, hno⟩
        change sInf A = j
        apply le_antisymm
        · exact Nat.sInf_le (by simpa [A] using hjnear)
        · apply le_of_not_gt
          intro hlt
          have hsinf_mem : sInf A ∈ A := Nat.sInf_mem hAne
          exact (hno (sInf A) hlt) (by simpa [A] using hsinf_mem)
    rw [hchar]
    exact (hnear_meas j).inter hlower_meas
  have hsel_meas : Measurable sel := measurable_to_countable' hsel_fiber
  have hreg_index : Measurable (fun j : ℕ => lawRegret P (enum j)) :=
    measurable_of_countable (fun j : ℕ => lawRegret P (enum j))
  constructor
  · simpa [feasibleERM, sel, near, score] using hreg_index.comp hsel_meas
  · intro sample
    let nearSample : ℕ → Prop := fun j =>
      ∀ j' : ℕ,
        empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j')
          ≤ empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum j)
              + (n : ℝ)⁻¹
    have hnear_nonempty : ({j : ℕ | nearSample j}).Nonempty := by
      simpa [nearSample] using
        (feasibleERM_nearSet_nonempty q enum muHat0 muHat1 eHat assign sample hn)
    have hselected_near : nearSample (sInf {j : ℕ | nearSample j}) :=
      Nat.sInf_mem hnear_nonempty
    constructor
    · simpa [feasibleERM, nearSample] using henum (sInf {j : ℕ | nearSample j})
    · intro πb hπb
      rcases hdense πb hπb with ⟨seq, hseq⟩
      have htrace :
          ∀ᶠ t in Filter.atTop,
            ∀ i : Fin n, enum (seq t) (sample i).X = πb (sample i).X := by
        exact Filter.eventually_all.2 (fun i => hseq (sample i).X)
      rcases htrace.exists with ⟨t, ht⟩
      have hscore_eq :
          empiricalWelfareScore q muHat0 muHat1 eHat assign sample (enum (seq t))
            =
          empiricalWelfareScore q muHat0 muHat1 eHat assign sample πb := by
        simp [empiricalWelfareScore, ht]
      have hineq := hselected_near (seq t)
      rw [hscore_eq] at hineq
      simpa [feasibleERM, nearSample] using hineq

-- @node: lem:crude-clipped-score-envelope
/-- `lem:crude-clipped-score-envelope`. Crude `q^{-1}` envelope of the clipped
AIPW score from clipped denominators and bounded outcomes/nuisances. -/
lemma crude_clipped_score_envelope (P : ObservedLaw 𝒳)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (q : ℝ)
    (hbdd : BoundedOutcome P)
    (hbn : ∀ x, muHat0 x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᵐ O ∂P.dataMeasure,
        |clippedAIPWScore q muHat0 muHat1 eHat O| ≤ C / q) ∧
      (∀ᵐ O ∂P.dataMeasure,
        (clippedAIPWScore q muHat0 muHat1 eHat O) ^ 2 ≤ C / q ^ 2) := by
  refine ⟨36, by norm_num, ?_, ?_⟩
  · filter_upwards [hbdd.1] with O hY
    let cp := clippedPropensity q eHat O.X
    have hcp_bounds : q ≤ cp ∧ cp ≤ 1 - q := by
      unfold cp clippedPropensity
      constructor
      · apply le_min
        · nlinarith
        · exact le_max_left q (eHat O.X)
      · exact min_le_left (1 - q) (max q (eHat O.X))
    have hcp_pos : 0 < cp := lt_of_lt_of_le hq hcp_bounds.1
    have hcp2_pos : 0 < 1 - cp := by nlinarith [hq, hcp_bounds.2]
    have h_inv_cp : cp⁻¹ ≤ q⁻¹ := by
      rw [inv_le_inv₀ hcp_pos hq]
      exact hcp_bounds.1
    have h_q_le_omcp : q ≤ 1 - cp := by nlinarith [hcp_bounds.2]
    have h_inv_omcp : (1 - cp)⁻¹ ≤ q⁻¹ := by
      rw [inv_le_inv₀ hcp2_pos hq]
      exact h_q_le_omcp
    have hbool_abs : |boolIndicator O.A| ≤ (1 : ℝ) := by
      cases O.A <;> simp [boolIndicator]
    have hone_minus_bool_abs : |1 - boolIndicator O.A| ≤ (1 : ℝ) := by
      cases O.A <;> simp [boolIndicator]
    have h_abs_of_Icc : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 → |z| ≤ (1 : ℝ) := by
      intro z hz
      exact abs_le.mpr ⟨hz.1, hz.2⟩
    have hYabs : |O.Y| ≤ (1 : ℝ) := h_abs_of_Icc O.Y hY
    have hmu0abs : |muHat0 O.X| ≤ (1 : ℝ) :=
      h_abs_of_Icc (muHat0 O.X) (hbn O.X).1
    have hmu1abs : |muHat1 O.X| ≤ (1 : ℝ) :=
      h_abs_of_Icc (muHat1 O.X) (hbn O.X).2
    have hcontrast : |muHat1 O.X - muHat0 O.X| ≤ (2 : ℝ) := by
      calc |muHat1 O.X - muHat0 O.X|
          ≤ |muHat1 O.X| + |muHat0 O.X| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add hmu1abs hmu0abs
        _ = (2 : ℝ) := by norm_num
    have hdiff1 : |O.Y - muHat1 O.X| ≤ (2 : ℝ) := by
      calc |O.Y - muHat1 O.X|
          ≤ |O.Y| + |muHat1 O.X| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add hYabs hmu1abs
        _ = (2 : ℝ) := by norm_num
    have hdiff0 : |O.Y - muHat0 O.X| ≤ (2 : ℝ) := by
      calc |O.Y - muHat0 O.X|
          ≤ |O.Y| + |muHat0 O.X| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add hYabs hmu0abs
        _ = (2 : ℝ) := by norm_num
    have hterm1 :
        |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)| ≤ 2 / q := by
      calc |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
          = |boolIndicator O.A| * cp⁻¹ * |O.Y - muHat1 O.X| := by
              rw [abs_mul, abs_div, abs_of_pos hcp_pos, div_eq_mul_inv]
        _ ≤ 1 * q⁻¹ * 2 := by gcongr
        _ = 2 / q := by ring
    have hterm0 :
        |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| ≤ 2 / q := by
      calc |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
          = |1 - boolIndicator O.A| * (1 - cp)⁻¹ * |O.Y - muHat0 O.X| := by
              rw [abs_mul, abs_div, abs_of_pos hcp2_pos, div_eq_mul_inv]
        _ ≤ 1 * q⁻¹ * 2 := by gcongr
        _ = 2 / q := by ring
    unfold clippedAIPWScore
    change |muHat1 O.X - muHat0 O.X
        + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
        - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| ≤ 36 / q
    have htri :
        |muHat1 O.X - muHat0 O.X
          + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
          - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
          ≤ |muHat1 O.X - muHat0 O.X|
            + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
            + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
      calc |muHat1 O.X - muHat0 O.X
            + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
            - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
          ≤ |muHat1 O.X - muHat0 O.X
              + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
              + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| :=
            abs_sub _ _
        _ ≤ (|muHat1 O.X - muHat0 O.X|
              + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|)
              + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
            gcongr
            exact abs_add_le _ _
        _ = |muHat1 O.X - muHat0 O.X|
              + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
              + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
            ring
    calc |muHat1 O.X - muHat0 O.X
          + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
          - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
        ≤ |muHat1 O.X - muHat0 O.X|
            + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
            + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := htri
      _ ≤ 2 + 2 / q + 2 / q := by gcongr
      _ ≤ 36 / q := by
        have h2le : (2 : ℝ) ≤ 2 / q := by
          rw [le_div_iff₀ hq]
          nlinarith [hq1]
        calc 2 + 2 / q + 2 / q
            ≤ 2 / q + 2 / q + 2 / q := by linarith
          _ = 6 / q := by ring
          _ ≤ 36 / q := by gcongr; norm_num
  · filter_upwards [hbdd.1] with O hY
    have hscore :
        |clippedAIPWScore q muHat0 muHat1 eHat O| ≤ 6 / q := by
      let cp := clippedPropensity q eHat O.X
      have hcp_bounds : q ≤ cp ∧ cp ≤ 1 - q := by
        unfold cp clippedPropensity
        constructor
        · apply le_min
          · nlinarith
          · exact le_max_left q (eHat O.X)
        · exact min_le_left (1 - q) (max q (eHat O.X))
      have hcp_pos : 0 < cp := lt_of_lt_of_le hq hcp_bounds.1
      have hcp2_pos : 0 < 1 - cp := by nlinarith [hq, hcp_bounds.2]
      have h_inv_cp : cp⁻¹ ≤ q⁻¹ := by
        rw [inv_le_inv₀ hcp_pos hq]
        exact hcp_bounds.1
      have h_q_le_omcp : q ≤ 1 - cp := by nlinarith [hcp_bounds.2]
      have h_inv_omcp : (1 - cp)⁻¹ ≤ q⁻¹ := by
        rw [inv_le_inv₀ hcp2_pos hq]
        exact h_q_le_omcp
      have hbool_abs : |boolIndicator O.A| ≤ (1 : ℝ) := by
        cases O.A <;> simp [boolIndicator]
      have hone_minus_bool_abs : |1 - boolIndicator O.A| ≤ (1 : ℝ) := by
        cases O.A <;> simp [boolIndicator]
      have h_abs_of_Icc : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 → |z| ≤ (1 : ℝ) := by
        intro z hz
        exact abs_le.mpr ⟨hz.1, hz.2⟩
      have hYabs : |O.Y| ≤ (1 : ℝ) := h_abs_of_Icc O.Y hY
      have hmu0abs : |muHat0 O.X| ≤ (1 : ℝ) :=
        h_abs_of_Icc (muHat0 O.X) (hbn O.X).1
      have hmu1abs : |muHat1 O.X| ≤ (1 : ℝ) :=
        h_abs_of_Icc (muHat1 O.X) (hbn O.X).2
      have hcontrast : |muHat1 O.X - muHat0 O.X| ≤ (2 : ℝ) := by
        calc |muHat1 O.X - muHat0 O.X|
            ≤ |muHat1 O.X| + |muHat0 O.X| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add hmu1abs hmu0abs
          _ = (2 : ℝ) := by norm_num
      have hdiff1 : |O.Y - muHat1 O.X| ≤ (2 : ℝ) := by
        calc |O.Y - muHat1 O.X|
            ≤ |O.Y| + |muHat1 O.X| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add hYabs hmu1abs
          _ = (2 : ℝ) := by norm_num
      have hdiff0 : |O.Y - muHat0 O.X| ≤ (2 : ℝ) := by
        calc |O.Y - muHat0 O.X|
            ≤ |O.Y| + |muHat0 O.X| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add hYabs hmu0abs
          _ = (2 : ℝ) := by norm_num
      have hterm1 :
          |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)| ≤ 2 / q := by
        calc |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
            = |boolIndicator O.A| * cp⁻¹ * |O.Y - muHat1 O.X| := by
                rw [abs_mul, abs_div, abs_of_pos hcp_pos, div_eq_mul_inv]
          _ ≤ 1 * q⁻¹ * 2 := by gcongr
          _ = 2 / q := by ring
      have hterm0 :
          |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| ≤ 2 / q := by
        calc |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
            = |1 - boolIndicator O.A| * (1 - cp)⁻¹ * |O.Y - muHat0 O.X| := by
                rw [abs_mul, abs_div, abs_of_pos hcp2_pos, div_eq_mul_inv]
          _ ≤ 1 * q⁻¹ * 2 := by gcongr
          _ = 2 / q := by ring
      unfold clippedAIPWScore
      change |muHat1 O.X - muHat0 O.X
          + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
          - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| ≤ 6 / q
      have htri :
          |muHat1 O.X - muHat0 O.X
            + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
            - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
            ≤ |muHat1 O.X - muHat0 O.X|
              + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
              + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
        calc |muHat1 O.X - muHat0 O.X
              + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
              - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
            ≤ |muHat1 O.X - muHat0 O.X
                + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
                + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| :=
              abs_sub _ _
          _ ≤ (|muHat1 O.X - muHat0 O.X|
                + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|)
                + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
              gcongr
              exact abs_add_le _ _
          _ = |muHat1 O.X - muHat0 O.X|
                + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
                + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
              ring
      calc |muHat1 O.X - muHat0 O.X
            + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
            - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
          ≤ |muHat1 O.X - muHat0 O.X|
              + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
              + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := htri
        _ ≤ 2 + 2 / q + 2 / q := by gcongr
        _ ≤ 6 / q := by
          have h2le : (2 : ℝ) ≤ 2 / q := by
            rw [le_div_iff₀ hq]
            nlinarith [hq1]
          calc 2 + 2 / q + 2 / q
              ≤ 2 / q + 2 / q + 2 / q := by linarith
            _ = 6 / q := by ring
    have hnon : 0 ≤ 6 / q := div_nonneg (by norm_num) hq.le
    have hs : (clippedAIPWScore q muHat0 muHat1 eHat O) ^ 2 ≤ (6 / q) ^ 2 := by
      rw [← sq_abs (clippedAIPWScore q muHat0 muHat1 eHat O)]
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg (abs_nonneg _), abs_of_nonneg hnon] using hscore)
    have hcalc : (6 / q) ^ 2 = (36 : ℝ) / q ^ 2 := by ring
    simpa [hcalc] using hs

omit [MeasurableSpace 𝒳] in
private lemma clippedAIPWScore_abs_le_six_of_mem (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (O : Observation 𝒳)
    (hbn : ∀ x, muHat0 x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) (hY : O.Y ∈ Set.Icc (-1 : ℝ) 1) :
    |clippedAIPWScore q muHat0 muHat1 eHat O| ≤ 6 / q := by
  let cp := clippedPropensity q eHat O.X
  have hcp_bounds : q ≤ cp ∧ cp ≤ 1 - q := by
    unfold cp clippedPropensity
    constructor
    · apply le_min
      · nlinarith
      · exact le_max_left q (eHat O.X)
    · exact min_le_left (1 - q) (max q (eHat O.X))
  have hcp_pos : 0 < cp := lt_of_lt_of_le hq hcp_bounds.1
  have hcp2_pos : 0 < 1 - cp := by nlinarith [hq, hcp_bounds.2]
  have h_inv_cp : cp⁻¹ ≤ q⁻¹ := by
    rw [inv_le_inv₀ hcp_pos hq]
    exact hcp_bounds.1
  have h_q_le_omcp : q ≤ 1 - cp := by nlinarith [hcp_bounds.2]
  have h_inv_omcp : (1 - cp)⁻¹ ≤ q⁻¹ := by
    rw [inv_le_inv₀ hcp2_pos hq]
    exact h_q_le_omcp
  have hbool_abs : |boolIndicator O.A| ≤ (1 : ℝ) := by
    cases O.A <;> simp [boolIndicator]
  have hone_minus_bool_abs : |1 - boolIndicator O.A| ≤ (1 : ℝ) := by
    cases O.A <;> simp [boolIndicator]
  have h_abs_of_Icc : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 → |z| ≤ (1 : ℝ) := by
    intro z hz
    exact abs_le.mpr ⟨hz.1, hz.2⟩
  have hYabs : |O.Y| ≤ (1 : ℝ) := h_abs_of_Icc O.Y hY
  have hmu0abs : |muHat0 O.X| ≤ (1 : ℝ) :=
    h_abs_of_Icc (muHat0 O.X) (hbn O.X).1
  have hmu1abs : |muHat1 O.X| ≤ (1 : ℝ) :=
    h_abs_of_Icc (muHat1 O.X) (hbn O.X).2
  have hcontrast : |muHat1 O.X - muHat0 O.X| ≤ (2 : ℝ) := by
    calc |muHat1 O.X - muHat0 O.X|
        ≤ |muHat1 O.X| + |muHat0 O.X| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hmu1abs hmu0abs
      _ = (2 : ℝ) := by norm_num
  have hdiff1 : |O.Y - muHat1 O.X| ≤ (2 : ℝ) := by
    calc |O.Y - muHat1 O.X|
        ≤ |O.Y| + |muHat1 O.X| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hYabs hmu1abs
      _ = (2 : ℝ) := by norm_num
  have hdiff0 : |O.Y - muHat0 O.X| ≤ (2 : ℝ) := by
    calc |O.Y - muHat0 O.X|
        ≤ |O.Y| + |muHat0 O.X| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hYabs hmu0abs
      _ = (2 : ℝ) := by norm_num
  have hterm1 :
      |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)| ≤ 2 / q := by
    calc |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
        = |boolIndicator O.A| * cp⁻¹ * |O.Y - muHat1 O.X| := by
            rw [abs_mul, abs_div, abs_of_pos hcp_pos, div_eq_mul_inv]
      _ ≤ 1 * q⁻¹ * 2 := by gcongr
      _ = 2 / q := by ring
  have hterm0 :
      |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| ≤ 2 / q := by
    calc |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
        = |1 - boolIndicator O.A| * (1 - cp)⁻¹ * |O.Y - muHat0 O.X| := by
            rw [abs_mul, abs_div, abs_of_pos hcp2_pos, div_eq_mul_inv]
      _ ≤ 1 * q⁻¹ * 2 := by gcongr
      _ = 2 / q := by ring
  unfold clippedAIPWScore
  change |muHat1 O.X - muHat0 O.X
      + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
      - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| ≤ 6 / q
  have htri :
      |muHat1 O.X - muHat0 O.X
        + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
        - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
        ≤ |muHat1 O.X - muHat0 O.X|
          + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
          + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
    calc |muHat1 O.X - muHat0 O.X
          + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
          - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
        ≤ |muHat1 O.X - muHat0 O.X
            + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
            + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| :=
          abs_sub _ _
      _ ≤ (|muHat1 O.X - muHat0 O.X|
            + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|)
            + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
          gcongr
          exact abs_add_le _ _
      _ = |muHat1 O.X - muHat0 O.X|
            + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
            + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := by
          ring
  calc |muHat1 O.X - muHat0 O.X
        + (boolIndicator O.A / cp) * (O.Y - muHat1 O.X)
        - ((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)|
      ≤ |muHat1 O.X - muHat0 O.X|
          + |(boolIndicator O.A / cp) * (O.Y - muHat1 O.X)|
          + |((1 - boolIndicator O.A) / (1 - cp)) * (O.Y - muHat0 O.X)| := htri
    _ ≤ 2 + 2 / q + 2 / q := by gcongr
    _ ≤ 6 / q := by
      have h2le : (2 : ℝ) ≤ 2 / q := by
        rw [le_div_iff₀ hq]
        nlinarith [hq1]
      calc 2 + 2 / q + 2 / q
          ≤ 2 / q + 2 / q + 2 / q := by linarith
        _ = 6 / q := by ring

private lemma crude_clipped_score_abs_ae_36 (P : ObservedLaw 𝒳)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (q : ℝ)
    (hbdd : BoundedOutcome P)
    (hbn : ∀ x, muHat0 x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) :
    ∀ᵐ O ∂P.dataMeasure,
      |clippedAIPWScore q muHat0 muHat1 eHat O| ≤ (36 : ℝ) / q := by
  filter_upwards [hbdd.1] with O hY
  have h6 := clippedAIPWScore_abs_le_six_of_mem q muHat0 muHat1 eHat O
    hbn hq hq1 hY
  calc
    |clippedAIPWScore q muHat0 muHat1 eHat O| ≤ 6 / q := h6
    _ ≤ (36 : ℝ) / q := by
          gcongr
          norm_num

lemma pooledOffsetSup_trunc_eq_original_ae_36 {n K : ℕ}
    (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳))
    (hwf : WellFormedLaw P)
    (hbdd : BoundedOutcome P)
    (hbn : ∀ k : Fin K, ∀ x,
      muHat0 k x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 k x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) :
    (fun sample : Fin n → Observation 𝒳 =>
      sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P
          (clippedPolicyIncrementTrunc P q ((36 : ℝ) / q) muHat0 muHat1 eHat)
          assign sample π| - lawRegret P π / 4)) '' policySet))
      =ᵐ[Measure.pi (fun _ : Fin n => P.dataMeasure)]
    (fun sample : Fin n → Observation 𝒳 =>
      sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P
          (clippedPolicyIncrement P q muHat0 muHat1 eHat)
          assign sample π| - lawRegret P π / 4)) '' policySet)) := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hwf.1
  let B : ℝ := (36 : ℝ) / q
  let gT : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat
  let g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrement P q muHat0 muHat1 eHat
  let μn : Measure (Fin n → Observation 𝒳) :=
    Measure.pi (fun _ : Fin n => P.dataMeasure)
  have hscore_ae : ∀ k : Fin K, ∀ᵐ O ∂P.dataMeasure,
      |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O| ≤ B := by
    intro k
    simpa [B] using
      crude_clipped_score_abs_ae_36 P (muHat0 k) (muHat1 k) (eHat k) q hbdd
        (hbn k) hq hq1
  have hcoord : ∀ (i : Fin n) (k : Fin K), ∀ᵐ sample ∂μn,
      |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) (sample i)| ≤ B := by
    intro i k
    let S : Set (Observation 𝒳) :=
      {O | ¬ |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O| ≤ B}
    have hS_zero : P.dataMeasure S = 0 := by
      apply measure_eq_zero_iff_ae_notMem.2
      filter_upwards [hscore_ae k] with O hO
      simpa [S] using hO
    have hpre_zero : μn (Function.eval i ⁻¹' S) = 0 := by
      simpa [μn] using
        (Measure.pi_eval_preimage_null (μ := fun _ : Fin n => P.dataMeasure)
          (i := i) hS_zero)
    have hae_not : ∀ᵐ sample ∂μn, sample i ∉ S :=
      measure_eq_zero_iff_ae_notMem.mp hpre_zero
    filter_upwards [hae_not] with sample hs
    simpa [S] using hs
  have hsample_good : ∀ᵐ sample ∂μn,
      ∀ i : Fin n, ∀ k : Fin K,
        |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) (sample i)| ≤ B :=
    Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun k => hcoord i k))
  have hmean_eq : ∀ (k : Fin K) (π : Policy 𝒳),
      ∫ O, gT k π O ∂P.dataMeasure = ∫ O, g k π O ∂P.dataMeasure := by
    intro k π
    apply integral_congr_ae
    filter_upwards [hscore_ae k] with O hO
    have hclip :
        clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) O =
          clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O := by
      simpa [clippedScoreTrunc] using
        clipReal_eq_self_of_abs_le (B := B)
          (z := clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O) hO
    simp [gT, g, clippedPolicyIncrementTrunc, clippedPolicyIncrement, hclip]
  have hprocess_eq : ∀ sample : Fin n → Observation 𝒳,
      (∀ i : Fin n, ∀ k : Fin K,
        |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) (sample i)| ≤ B) →
      ∀ π : Policy 𝒳,
        pooledCrossfitProcess P gT assign sample π =
          pooledCrossfitProcess P g assign sample π := by
    intro sample hgood π
    dsimp [pooledCrossfitProcess]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    have hclip :
        clippedScoreTrunc q B (muHat0 (assign i)) (muHat1 (assign i))
            (eHat (assign i)) (sample i) =
          clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i))
            (eHat (assign i)) (sample i) := by
      simpa [clippedScoreTrunc] using
        clipReal_eq_self_of_abs_le (B := B)
          (z := clippedAIPWScore q (muHat0 (assign i)) (muHat1 (assign i))
            (eHat (assign i)) (sample i)) (hgood i (assign i))
    have hterm : gT (assign i) π (sample i) = g (assign i) π (sample i) := by
      simp [gT, g, clippedPolicyIncrementTrunc, clippedPolicyIncrement, hclip]
    rw [hterm, hmean_eq (assign i) π]
  filter_upwards [hsample_good] with sample hgood
  have hproc := hprocess_eq sample hgood
  have hset :
      ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P gT assign sample π| -
          lawRegret P π / 4)) '' policySet)
        =
      ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P g assign sample π| -
          lawRegret P π / 4)) '' policySet) := by
    ext y
    constructor
    · rintro ⟨π, hπ, rfl⟩
      refine ⟨π, hπ, ?_⟩
      change
        max 0 (2 * |pooledCrossfitProcess P g assign sample π| -
            lawRegret P π / 4)
          =
        max 0 (2 * |pooledCrossfitProcess P gT assign sample π| -
            lawRegret P π / 4)
      rw [← hproc π]
    · rintro ⟨π, hπ, rfl⟩
      refine ⟨π, hπ, ?_⟩
      change
        max 0 (2 * |pooledCrossfitProcess P gT assign sample π| -
            lawRegret P π / 4)
          =
        max 0 (2 * |pooledCrossfitProcess P g assign sample π| -
            lawRegret P π / 4)
      rw [hproc π]
  change
    sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P gT assign sample π| -
          lawRegret P π / 4)) '' policySet)
      =
    sSup ((fun π =>
        max 0 (2 * |pooledCrossfitProcess P g assign sample π| -
          lawRegret P π / 4)) '' policySet)
  rw [hset]

-- @node: expectedPooledOffsetSup_trunc_eq_original_ae_36
lemma expectedPooledOffsetSup_trunc_eq_original_ae_36 {n K : ℕ}
    (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳))
    (hwf : WellFormedLaw P)
    (hbdd : BoundedOutcome P)
    (hbn : ∀ k : Fin K, ∀ x,
      muHat0 k x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 k x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) :
    expectedPooledOffsetSup P
        (clippedPolicyIncrementTrunc P q ((36 : ℝ) / q) muHat0 muHat1 eHat)
        assign policySet
      =
    expectedPooledOffsetSup P
        (clippedPolicyIncrement P q muHat0 muHat1 eHat)
        assign policySet := by
  apply integral_congr_ae
  exact pooledOffsetSup_trunc_eq_original_ae_36 P q muHat0 muHat1 eHat assign
    policySet hwf hbdd hbn hq hq1

lemma foldOffsetSubSup_trunc_eq_original_ae_36 {n K : ℕ}
    (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (policySet : Set (Policy 𝒳)) (k : Fin K)
    (hwf : WellFormedLaw P)
    (hbdd : BoundedOutcome P)
    (hbn : ∀ k : Fin K, ∀ x,
      muHat0 k x ∈ Set.Icc (-1 : ℝ) 1 ∧ muHat1 k x ∈ Set.Icc (-1 : ℝ) 1)
    (hq : 0 < q) (hq1 : q ≤ 1 / 2) :
    (fun sample : foldIndex assign k → Observation 𝒳 =>
      foldOffsetSubSup P
        (clippedPolicyIncrementTrunc P q ((36 : ℝ) / q) muHat0 muHat1 eHat)
        assign policySet k sample)
      =ᵐ[Measure.pi (fun _ : foldIndex assign k => P.dataMeasure)]
    (fun sample : foldIndex assign k → Observation 𝒳 =>
      foldOffsetSubSup P
        (clippedPolicyIncrement P q muHat0 muHat1 eHat)
        assign policySet k sample) := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hwf.1
  let B : ℝ := (36 : ℝ) / q
  let gT : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat
  let g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrement P q muHat0 muHat1 eHat
  let μk : Measure (foldIndex assign k → Observation 𝒳) :=
    Measure.pi (fun _ : foldIndex assign k => P.dataMeasure)
  have hscore_ae : ∀ᵐ O ∂P.dataMeasure,
      |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O| ≤ B := by
    simpa [B] using
      crude_clipped_score_abs_ae_36 P (muHat0 k) (muHat1 k) (eHat k) q hbdd
        (hbn k) hq hq1
  have hcoord : ∀ i : foldIndex assign k, ∀ᵐ sample ∂μk,
      |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) (sample i)| ≤ B := by
    intro i
    let S : Set (Observation 𝒳) :=
      {O | ¬ |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O| ≤ B}
    have hS_zero : P.dataMeasure S = 0 := by
      apply measure_eq_zero_iff_ae_notMem.2
      filter_upwards [hscore_ae] with O hO
      simpa [S] using hO
    have hpre_zero : μk (Function.eval i ⁻¹' S) = 0 := by
      simpa [μk] using
        (Measure.pi_eval_preimage_null (μ := fun _ : foldIndex assign k => P.dataMeasure)
          (i := i) hS_zero)
    have hae_not : ∀ᵐ sample ∂μk, sample i ∉ S :=
      measure_eq_zero_iff_ae_notMem.mp hpre_zero
    filter_upwards [hae_not] with sample hs
    simpa [S] using hs
  have hsample_good : ∀ᵐ sample ∂μk,
      ∀ i : foldIndex assign k,
        |clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) (sample i)| ≤ B :=
    Filter.eventually_all.2 hcoord
  have hmean_eq : ∀ π : Policy 𝒳,
      ∫ O, gT k π O ∂P.dataMeasure = ∫ O, g k π O ∂P.dataMeasure := by
    intro π
    apply integral_congr_ae
    filter_upwards [hscore_ae] with O hO
    have hclip :
        clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) O =
          clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O := by
      simpa [clippedScoreTrunc] using
        clipReal_eq_self_of_abs_le (B := B)
          (z := clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O) hO
    simp [gT, g, clippedPolicyIncrementTrunc, clippedPolicyIncrement, hclip]
  filter_upwards [hsample_good] with sample hgood
  have hfold_eq : ∀ π : Policy 𝒳,
      ((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (gT k π (sample i) - ∫ O, gT k π O ∂P.dataMeasure)
        =
      ((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure) := by
    intro π
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    have hclip :
        clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) (sample i) =
          clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) (sample i) := by
      simpa [clippedScoreTrunc] using
        clipReal_eq_self_of_abs_le (B := B)
          (z := clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) (sample i))
          (hgood i)
    have hterm : gT k π (sample i) = g k π (sample i) := by
      simp [gT, g, clippedPolicyIncrementTrunc, clippedPolicyIncrement, hclip]
    rw [hterm, hmean_eq π]
  have hset :
      ((fun π =>
        max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (gT k π (sample i) - ∫ O, gT k π O ∂P.dataMeasure)|
          - lawRegret P π / 4)) '' policySet)
        =
      ((fun π =>
        max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)|
          - lawRegret P π / 4)) '' policySet) := by
    ext y
    constructor
    · rintro ⟨π, hπ, rfl⟩
      refine ⟨π, hπ, ?_⟩
      change
        max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)|
          - lawRegret P π / 4)
          =
        max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (gT k π (sample i) - ∫ O, gT k π O ∂P.dataMeasure)|
          - lawRegret P π / 4)
      rw [← hfold_eq π]
    · rintro ⟨π, hπ, rfl⟩
      refine ⟨π, hπ, ?_⟩
      change
        max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (gT k π (sample i) - ∫ O, gT k π O ∂P.dataMeasure)|
          - lawRegret P π / 4)
          =
        max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
          ∑ i : foldIndex assign k,
            (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)|
          - lawRegret P π / 4)
      rw [hfold_eq π]
  change
    sSup ((fun π =>
      max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (gT k π (sample i) - ∫ O, gT k π O ∂P.dataMeasure)|
        - lawRegret P π / 4)) '' policySet)
      =
    sSup ((fun π =>
      max 0 (2 * |((Fintype.card (foldIndex assign k) : ℝ)⁻¹) *
        ∑ i : foldIndex assign k,
          (g k π (sample i) - ∫ O, g k π O ∂P.dataMeasure)|
        - lawRegret P π / 4)) '' policySet)
  rw [hset]


end CausalSmith.Stat.PolicyRegretMarginOverlap
