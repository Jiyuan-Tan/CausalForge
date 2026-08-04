import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Basic
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.T_bounded_outcome_frontier

/-!
# Coefficient-mass degree frontier

This specializes the simultaneous two-class theorem and replaces block energy
by its exposed-order binomial comparison.
-/

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
open Causalean.Stat

/-- Coefficient mass bounds every realized potential outcome. -/
lemma potentialOutcome_abs_le_of_mem_modelClass
    {V : Type*} [Fintype V] [DecidableEq V]
    {d β : ℕ} {B : ℝ} (M : ModelClass V d β B) (i : V) (z : V → Bool) :
    |potentialOutcome M.edge M.coef i z| ≤ B := by
  classical
  unfold potentialOutcome
  calc
    |∑ S ∈ (nbhd M.edge i).powerset,
        M.coef i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0| ≤
        ∑ S ∈ (nbhd M.edge i).powerset,
          |M.coef i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (nbhd M.edge i).powerset, |M.coef i S| := by
      apply Finset.sum_le_sum
      intro S hS
      simp only [abs_mul]
      have hprod :
          |∏ j ∈ S, if z j then (1 : ℝ) else 0| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
          (fun j _ => by cases z j <;> norm_num)
      exact mul_le_of_le_one_right (abs_nonneg _) hprod
    _ ≤ B := M.mass_le i

/-- The coefficient-mass target is bounded by twice the envelope. -/
lemma tte_abs_le_two_mul_of_mem_modelClass
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {d β : ℕ} {B : ℝ} (M : ModelClass V d β B) :
    |tte M.edge M.coef| ≤ 2 * B := by
  classical
  have hcard : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  unfold tte
  rw [abs_mul]
  calc
    |(Fintype.card V : ℝ)⁻¹| *
          |∑ i : V,
            (potentialOutcome M.edge M.coef i (fun _ => true) -
              potentialOutcome M.edge M.coef i (fun _ => false))| ≤
        (Fintype.card V : ℝ)⁻¹ *
          ∑ i : V,
            |potentialOutcome M.edge M.coef i (fun _ => true) -
              potentialOutcome M.edge M.coef i (fun _ => false)| := by
      rw [abs_of_pos (inv_pos.mpr hcard)]
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ∑ _i : V, (2 * B) := by
      gcongr with i
      calc
        |potentialOutcome M.edge M.coef i (fun _ => true) -
            potentialOutcome M.edge M.coef i (fun _ => false)| ≤
            |potentialOutcome M.edge M.coef i (fun _ => true)| +
              |potentialOutcome M.edge M.coef i (fun _ => false)| :=
          abs_sub _ _
        _ ≤ B + B := add_le_add
          (potentialOutcome_abs_le_of_mem_modelClass M i _)
          (potentialOutcome_abs_le_of_mem_modelClass M i _)
        _ = 2 * B := by ring
    _ = 2 * B := by
      simp [ne_of_gt hcard]

/-- The clipped SNIPE estimator is an admissible competitor on the
coefficient-mass class. -/
lemma snipeClipped_admissible
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    AdmissibleEstimator (V := V) p hp0 hp1 d β B
      (snipeClipped B β p) := by
  constructor
  · intro G z
    unfold snipeClipped clipTo snipeEstimator
    fun_prop
  · refine ⟨9 * B ^ 2, ?_⟩
    rintro _ ⟨M, rfl⟩
    unfold riskAt Causalean.Experimentation.DesignBased.FiniteDesign.mse
    have ht := tte_abs_le_two_mul_of_mem_modelClass M
    have hclip (z : V → Bool) :
        |snipeClipped B β p (edgeFn M) z (obsOutcome M.edge M.coef z)| ≤ B := by
      unfold snipeClipped clipTo
      rw [abs_le]
      simp [hB]
    calc
      (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
          (fun _ => hp1)).E
          (fun z =>
            (snipeClipped B β p (edgeFn M) z
                (obsOutcome M.edge M.coef z) -
              tte M.edge M.coef) ^ 2) ≤
          (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
            (fun _ => hp1)).E (fun _ => 9 * B ^ 2) := by
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
        apply Finset.sum_le_sum
        intro z hz
        have hdiff :
            |snipeClipped B β p (edgeFn M) z
                (obsOutcome M.edge M.coef z) -
              tte M.edge M.coef| ≤ 3 * B := by
          calc
            |_ - _| ≤
                |snipeClipped B β p (edgeFn M) z
                  (obsOutcome M.edge M.coef z)| +
                  |tte M.edge M.coef| := abs_sub _ _
            _ ≤ B + 2 * B := add_le_add (hclip z) ht
            _ = 3 * B := by ring
        apply mul_le_mul_of_nonneg_left
        · change
            (snipeClipped B β p (edgeFn M) z
              (obsOutcome M.edge M.coef z) - tte M.edge M.coef) ^ 2 ≤
                9 * B ^ 2
          have hsquare :
              |snipeClipped B β p (edgeFn M) z
                (obsOutcome M.edge M.coef z) - tte M.edge M.coef| ^ 2 ≤
                  (3 * B) ^ 2 :=
            (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdiff
          rw [sq_abs] at hsquare
          nlinarith
        · exact
            (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
              (fun _ => hp1)).p_nonneg z
      _ = 9 * B ^ 2 := by
        rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_const]

/-- Any admissible estimator supplies an upper bound on the minimax risk. -/
lemma minimaxRisk_le_worstRisk_of_admissible
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) (est : Estimator V)
    (hne : Nonempty (ModelClass V d β B))
    (hest : AdmissibleEstimator p hp0 hp1 d β B est) :
    minimaxRisk (V := V) p hp0 hp1 d β B ≤
      worstRisk (V := V) p hp0 hp1 d β B est := by
  unfold minimaxRisk
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨est', _hest', rfl⟩
    unfold worstRisk
    let M : ModelClass V d β B := Classical.choice hne
    have hrisk : 0 ≤ riskAt p hp0 hp1 M est' := by
      unfold riskAt
      exact
        (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
          (fun _ => hp1)).mse_nonneg _ _
    exact hrisk.trans (le_csSup _hest'.2 (Set.mem_range_self M))
  · exact ⟨est, hest, rfl⟩

/-- The original coefficient-mass frontier, including the nonsaturated
unclipped-SNIPE assertion. -/
-- @node: thm:degree-frontier
theorem degree_frontier
    (β : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ cLower cUpper : ℝ,
      0 < cLower ∧ cLower ≤ cUpper ∧
      ∀ (n d : ℕ) (B : ℝ), 1 ≤ n → DegreeIndex (Fin n) d → 0 ≤ B →
        cLower * B ^ 2 *
            min 1 ((d : ℝ) * Nat.choose d (kStar d β p) / n) ≤
          minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B ∧
        minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B ≤
          worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeClipped B β p) ∧
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeClipped B β p) ≤
          cUpper * B ^ 2 *
            min 1 ((d : ℝ) * Nat.choose d (kStar d β p) / n) ∧
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeEstimator β p) ≤
          cUpper * B ^ 2 *
            ((d : ℝ) * Nat.choose d (kStar d β p) / n) ∧
        (∀ M : ModelClass (Fin n) d β B, ∀ i,
          localEnergy M.edge β p i ≤ blockEnergy β p d) ∧
        (∀ M : ModelClass (Fin n) d β B, ∀ (r : ℕ) (i : Fin n),
          1 ≤ r →
          (∑ l : Fin n,
              Nat.choose ((nbhd M.edge i ∩ nbhd M.edge l).card) r) =
              ∑ S ∈ ((nbhd M.edge i).powerset.filter
                (fun S => S.card = r)),
                containingNeighborhoods M.edge S ∧
          (∑ S ∈ ((nbhd M.edge i).powerset.filter
                (fun S => S.card = r)),
                containingNeighborhoods M.edge S) ≤
              d * Nat.choose (nbhd M.edge i).card r ∧
          d * Nat.choose (nbhd M.edge i).card r ≤ d * Nat.choose d r) ∧
        (0 < B → 1 ≤ d →
          let m := blockCount n d
          let ρ := activeShare n d
          let δ := tiltAmplitude B β p m d
          (∀ U : Fin m → ℝ, (∀ b, |U b| ≤ B / 2) →
            (∃ Mplus : ModelClass (Fin n) d β B,
              Mplus.edge = blockGraph n d ∧
              Mplus.coef = blockSchedule n d β B p 1 (by norm_num) U) ∧
            (∃ Mminus : ModelClass (Fin n) d β B,
              Mminus.edge = blockGraph n d ∧
              Mminus.coef =
                blockSchedule n d β B p (-1) (by norm_num) U) ∧
            tte (blockGraph n d)
                (blockSchedule n d β B p 1 (by norm_num) U) = ρ * δ ∧
            tte (blockGraph n d)
                (blockSchedule n d β B p (-1) (by norm_num) U) =
              -ρ * δ) ∧
          hellingerSqDensity (blockDominatingMeasure n d)
              (blockPriorDensity n d β B p 1)
              (blockPriorDensity n d β B p (-1)) ≤
            4 * Real.pi ^ 2 * m * δ ^ 2 /
              (B ^ 2 * blockEnergy β p d) ∧
          (1 / 2 : ℝ) ≤ ρ ∧ ρ ≤ 1 ∧
          blockEnergy β p d / m =
            ((d : ℝ) * blockEnergy β p d / n) / ρ) := by
  obtain ⟨a, b, ha, hab, hfrontier⟩ :=
    bounded_outcome_degree_frontier β p hβ hp0 hp1
  let cLower : ℝ := min 1 (a ^ 2)
  let cUpper : ℝ := max 1 (b ^ 2)
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcLower : 0 < cLower := by
    dsimp [cLower]
    positivity
  have hcUpper : 0 < cUpper := by
    dsimp [cUpper]
    positivity
  refine ⟨cLower, cUpper, hcLower, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (le_max_left _ _)
  · intro n d B hn hdeg hB
    let D : FiniteDesign (Fin n → Bool) :=
      blockDesign n p (le_of_lt hp0) (le_of_lt hp1)
    have hD : IsProductBernoulli D p := by
      refine ⟨hp0, hp1, ?_⟩
      refine ⟨fun _ => le_of_lt hp0, fun _ => le_of_lt hp1, ?_⟩
      rfl
    obtain ⟨_hinc, _hstrict, hlower, hriskEq, _hclassMono,
        _hbddToWorst, _hworstUpper, hl1Upper, _hunbiasedL1, _hunbiasedBdd,
        hsnipeL1, _hsnipeBdd, hlocalL1, _hlocalBdd, hchooseLower,
        hchooseUpper, _hexact, hmixture⟩ :=
      hfrontier n D d B hn hdeg hB hD
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    let x : ℝ := (d : ℝ) * Nat.choose d (kStar d β p) / n
    let y : ℝ := (d : ℝ) * blockEnergy β p d / n
    have hx : 0 ≤ x := by
      dsimp [x]
      positivity
    have haxy : a * x ≤ y := by
      simpa [x, y, div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right hchooseLower
          (le_of_lt (inv_pos.mpr hnpos))
    have hybx : y ≤ b * x := by
      simpa [x, y, div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right hchooseUpper
          (le_of_lt (inv_pos.mpr hnpos))
    have hminLower : min 1 (a * x) ≤ min 1 y :=
      min_le_min_left 1 haxy
    have hminUpper : min 1 y ≤ min 1 (b * x) :=
      min_le_min_left 1 hybx
    have hsmallA : min 1 (a ^ 2) ≤ a := by
      by_cases ha1 : a ≤ 1
      · exact (min_le_right _ _).trans (by nlinarith)
      · exact (min_le_left _ _).trans (le_of_not_ge ha1)
    have hscaleLower :
        min 1 (a ^ 2) * min 1 x ≤ a * min 1 (a * x) := by
      by_cases hx1 : x ≤ 1
      · rw [min_eq_right hx1]
        by_cases hax1 : a * x ≤ 1
        · rw [min_eq_right hax1]
          calc
            min 1 (a ^ 2) * x ≤ a ^ 2 * x :=
              mul_le_mul_of_nonneg_right (min_le_right 1 (a ^ 2)) hx
            _ = a * (a * x) := by ring
        · rw [min_eq_left (le_of_not_ge hax1)]
          calc
            min 1 (a ^ 2) * x ≤ a * x :=
              mul_le_mul_of_nonneg_right hsmallA hx
            _ ≤ a * 1 := mul_le_mul_of_nonneg_left hx1 (le_of_lt ha)
      · rw [min_eq_left (le_of_not_ge hx1)]
        by_cases hax1 : a * x ≤ 1
        · rw [min_eq_right hax1]
          calc
            min 1 (a ^ 2) * 1 = min 1 (a ^ 2) := by ring
            _ ≤ a ^ 2 := min_le_right _ _
            _ ≤ a ^ 2 * x :=
              le_mul_of_one_le_right (sq_nonneg a) (le_of_not_ge hx1)
            _ = a * (a * x) := by ring
        · rw [min_eq_left (le_of_not_ge hax1)]
          simpa using hsmallA
    have hlargeB : b ≤ max 1 (b ^ 2) := by
      by_cases hb1 : b ≤ 1
      · exact hb1.trans (le_max_left _ _)
      · exact (by nlinarith : b ≤ b ^ 2) |>.trans (le_max_right _ _)
    have hscaleUpper :
        b * min 1 (b * x) ≤ max 1 (b ^ 2) * min 1 x := by
      by_cases hx1 : x ≤ 1
      · rw [min_eq_right hx1]
        by_cases hbx1 : b * x ≤ 1
        · rw [min_eq_right hbx1]
          calc
            b * (b * x) = b ^ 2 * x := by ring
            _ ≤ max 1 (b ^ 2) * x :=
              mul_le_mul_of_nonneg_right (le_max_right 1 (b ^ 2)) hx
        · rw [min_eq_left (le_of_not_ge hbx1)]
          calc
            b * 1 ≤ b * (b * x) :=
              by simpa only [mul_one] using
                le_mul_of_one_le_right (le_of_lt hb) (le_of_not_ge hbx1)
            _ = b ^ 2 * x := by ring
            _ ≤ max 1 (b ^ 2) * x :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hx
      · rw [min_eq_left (le_of_not_ge hx1)]
        by_cases hbx1 : b * x ≤ 1
        · rw [min_eq_right hbx1]
          calc
            b * (b * x) ≤ b * 1 :=
              mul_le_mul_of_nonneg_left hbx1 (le_of_lt hb)
            _ = b := by ring
            _ ≤ 1 := by
              have : b < 1 := by
                by_contra h
                have hxb : x ≤ b * x :=
                  le_mul_of_one_le_left hx (le_of_not_gt h)
                have : 1 < b * x :=
                  (lt_of_not_ge hx1).trans_le hxb
                exact (not_lt_of_ge hbx1) this
              exact le_of_lt this
            _ ≤ max 1 (b ^ 2) * 1 := by
              simpa only [mul_one] using (le_max_left 1 (b ^ 2))
        · rw [min_eq_left (le_of_not_ge hbx1)]
          simpa only [mul_one] using hlargeB
    have hlower' :
        cLower * B ^ 2 * min 1 x ≤
          minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
            d β B := by
      calc
        cLower * B ^ 2 * min 1 x =
            B ^ 2 * (min 1 (a ^ 2) * min 1 x) := by
              simp only [cLower]
              ring
        _ ≤ B ^ 2 * (a * min 1 (a * x)) :=
          mul_le_mul_of_nonneg_left hscaleLower (sq_nonneg B)
        _ ≤ B ^ 2 * (a * min 1 y) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hminLower (le_of_lt ha)) (sq_nonneg B)
        _ = a * B ^ 2 * min 1
              ((d : ℝ) * blockEnergy β p d / n) := by
          dsimp [y]
          ring
        _ ≤ minimaxRiskL1 (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
              d β B := hlower
        _ = minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
              d β B := hriskEq
    have hupper' :
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeClipped B β p) ≤
          cUpper * B ^ 2 * min 1 x := by
      calc
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
              (snipeClipped B β p) ≤
            b * B ^ 2 * min 1
              ((d : ℝ) * blockEnergy β p d / n) := hl1Upper
        _ = B ^ 2 * (b * min 1 y) := by
          dsimp [y]
          ring
        _ ≤ B ^ 2 * (b * min 1 (b * x)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hminUpper (le_of_lt hb)) (sq_nonneg B)
        _ ≤ B ^ 2 * (max 1 (b ^ 2) * min 1 x) :=
          mul_le_mul_of_nonneg_left hscaleUpper (sq_nonneg B)
        _ = cUpper * B ^ 2 * min 1 x := by
          simp only [cUpper]
          ring
    have hnonempty : Nonempty (ModelClass (Fin n) d β B) := by
      let M0 : ModelClass (Fin n) d β B :=
        { edge := fun _ _ => False
          decEdge := fun _ _ => inferInstance
          coef := fun _ _ => 0
          supported := by simp
          degree_le := by simp [BoundedDegree, nbhd, outNbhd]
          low_order := by simp [LowOrder]
          mass_le := by
            intro i
            simpa [BoundedCoeffMass] using hB }
      exact ⟨M0⟩
    let i0 : Fin n := ⟨0, by omega⟩
    letI : Nonempty (Fin n) := ⟨i0⟩
    have hmini :
        minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B ≤
          worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeClipped B β p) :=
      minimaxRisk_le_worstRisk_of_admissible p (le_of_lt hp0)
        (le_of_lt hp1) d β B (snipeClipped B β p) hnonempty
        (snipeClipped_admissible p (le_of_lt hp0) (le_of_lt hp1) d β B hB)
    have hsnipe' :
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeEstimator β p) ≤
          cUpper * B ^ 2 * x := by
      calc
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
              (snipeEstimator β p) ≤
            B ^ 2 * (d : ℝ) * blockEnergy β p d / n := hsnipeL1
        _ = B ^ 2 * y := by
          dsimp [y]
          ring
        _ ≤ B ^ 2 * (b * x) :=
          mul_le_mul_of_nonneg_left hybx (sq_nonneg B)
        _ ≤ B ^ 2 * (max 1 (b ^ 2) * x) := by
          gcongr
        _ = cUpper * B ^ 2 * x := by
          simp only [cUpper]
          ring
    refine ⟨?_, hmini, ?_, ?_, hlocalL1, ?_, hmixture⟩
    · simpa [x] using hlower'
    · simpa [x] using hupper'
    · simpa [x] using hsnipe'
    · intro M r i hr
      exact overlap_count_le M.edge d r i M.degree_le hr

/-- The coefficient-mass minimax risk in the two-class notation is unchanged when the
assignment probability, its bounds, the degree and interaction parameters, and the outcome
bound are replaced by equal values. -/
add_decl_doc minimaxRiskL1.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
