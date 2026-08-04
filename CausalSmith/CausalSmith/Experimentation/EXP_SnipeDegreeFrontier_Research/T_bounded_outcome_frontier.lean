import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.HellingerAffinity
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.HeadlineSupport
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.MinimaxRisk
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.T_bounded_outcome_frontier_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.T_bounded_outcome_frontier_Part2

/-!
# Simultaneous coefficient-mass and bounded-outcome degree frontier

This is the paper's headline finite-population theorem.  Its constants are
quantified outside population size, degree, and envelope, so they depend only
on the fixed interaction order and Bernoulli probability.  The supporting model-class
and exact-risk lemmas live in the two sibling parts imported above.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
open Causalean.Stat
/-- The simultaneous matched degree frontier over both bounded model classes. -/
-- @node: thm:bounded-outcome-degree-frontier
theorem bounded_outcome_degree_frontier
    (β : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ cLower cUpper : ℝ,
      0 < cLower ∧ cLower ≤ cUpper ∧
      ∀ (n : ℕ) (D : FiniteDesign (Fin n → Bool)) (d : ℕ) (B : ℝ),
        1 ≤ n → DegreeIndex (Fin n) d → 0 ≤ B → IsProductBernoulli D p →
        ModelClassIncluded (Fin n) d β B ∧
        (0 < B → 1 ≤ d → ModelClassStrict (Fin n) d β B) ∧
        cLower * B ^ 2 *
            min 1 ((d : ℝ) * blockEnergy β p d / n) ≤
          minimaxRiskL1 (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B ∧
        minimaxRiskL1 (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B =
          minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B ∧
        minimaxRiskL1 (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B ≤
          minimaxRiskBddOutcome (V := Fin n) p
            (le_of_lt hp0) (le_of_lt hp1) d β B ∧
        minimaxRiskBddOutcome (V := Fin n) p
            (le_of_lt hp0) (le_of_lt hp1) d β B ≤
          worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeClippedBdd B β p) ∧
        worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeClippedBdd B β p) ≤
          cUpper * B ^ 2 *
            min 1 ((d : ℝ) * blockEnergy β p d / n) ∧
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeClipped B β p) ≤
          cUpper * B ^ 2 *
            min 1 ((d : ℝ) * blockEnergy β p d / n) ∧
        (∀ M : ModelClass (Fin n) d β B,
          D.Unbiased
            (fun z => snipeEstimator β p (edgeFn M) z
              (obsOutcome M.edge M.coef z))
            (tte M.edge M.coef)) ∧
        (∀ M : BddOutcomeModelClass (Fin n) d β B,
          D.Unbiased
            (fun z => snipeEstimator β p (edgeFnBdd M) z
              (obsOutcome M.edge M.coef z))
            (tte M.edge M.coef)) ∧
        worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeEstimator β p) ≤
          B ^ 2 * (d : ℝ) * blockEnergy β p d / n ∧
        worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
            (snipeEstimator β p) ≤
          B ^ 2 * (d : ℝ) * blockEnergy β p d / n ∧
        (∀ M : ModelClass (Fin n) d β B, ∀ i,
          localEnergy M.edge β p i ≤ blockEnergy β p d) ∧
        (∀ M : BddOutcomeModelClass (Fin n) d β B, ∀ i,
          localEnergy M.edge β p i ≤ blockEnergy β p d) ∧
        cLower * (d : ℝ) * Nat.choose d (kStar d β p) ≤
          (d : ℝ) * blockEnergy β p d ∧
        (d : ℝ) * blockEnergy β p d ≤
          cUpper * (d : ℝ) * Nat.choose d (kStar d β p) ∧
        (1 ≤ d → d ∣ n →
          let m := n / d
          worstRiskFixedGraph (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
              (blockGraph n d) d β B (snipeEstimator β p) =
              B ^ 2 * blockEnergy β p d / m ∧
          worstRiskBddFixedGraph (V := Fin n) p
              (le_of_lt hp0) (le_of_lt hp1)
              (blockGraph n d) d β B (snipeEstimator β p) =
              B ^ 2 * blockEnergy β p d / m ∧
          worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
              d β B (snipeEstimator β p) =
              B ^ 2 * blockEnergy β p d / m ∧
          worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
              d β B (snipeEstimator β p) =
              B ^ 2 * blockEnergy β p d / m ∧
          B ^ 2 * blockEnergy β p d / m =
              B ^ 2 * (d : ℝ) * blockEnergy β p d / n) ∧
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
                (blockSchedule n d β B p (-1) (by norm_num) U) = -ρ * δ) ∧
          hellingerSqDensity (blockDominatingMeasure n d)
              (blockPriorDensity n d β B p 1)
              (blockPriorDensity n d β B p (-1)) ≤
            4 * Real.pi ^ 2 * m * δ ^ 2 /
              (B ^ 2 * blockEnergy β p d) ∧
          (1 / 2 : ℝ) ≤ ρ ∧ ρ ≤ 1 ∧
          blockEnergy β p d / m =
            ((d : ℝ) * blockEnergy β p d / n) / ρ) := by
  obtain ⟨c₁, c₂, H, hc₁, hc₁₂, hH, henergy⟩ :=
    blockEnergy_representer β p hβ hp0 hp1
  let κ : ℝ :=
    min ((2 * representerMassSup β p)⁻¹) ((4 * Real.pi)⁻¹)
  let cLower : ℝ := min c₁ (κ ^ 2 / 16)
  let cUpper : ℝ := max 16 c₂
  have hκ : 0 < κ := by
    dsimp [κ]
    have hmass := representerMassSup_pos β p hβ hp0 hp1
    positivity
  have hcLower : 0 < cLower := by
    dsimp [cLower]
    positivity
  have hcUpper : cLower ≤ cUpper := by
    calc
      cLower ≤ c₁ := min_le_left _ _
      _ ≤ c₂ := hc₁₂
      _ ≤ cUpper := le_max_right _ _
  refine ⟨cLower, cUpper, hcLower, hcUpper, ?_⟩
  intro n D d B hn hdeg hB hD
  have hdn : d ≤ n := by simpa [DegreeIndex] using hdeg
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hinc := modelClassIncluded_of_coeffMass (V := Fin n) d β B
  have hraw :
      worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
          (snipeEstimator β p) ≤
        B ^ 2 * (d : ℝ) * blockEnergy β p d / n := by
    simpa using worstRisk_snipe_le (V := Fin n) p hp0 hp1 d β B
  have hrawBdd :
      worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
          (snipeEstimator β p) ≤
        B ^ 2 * (d : ℝ) * blockEnergy β p d / n := by
    simpa using worstRiskBdd_snipe_le (V := Fin n) p hp0 hp1 d β B
  have hclip :
      worstRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
          (snipeClipped B β p) ≤
        4 * B ^ 2 * min 1 ((d : ℝ) * blockEnergy β p d / n) := by
    simpa using worstRisk_clipped_le_min (V := Fin n)
      p hp0 hp1 d β B hB
  have hclipBdd :
      worstRiskBdd (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1) d β B
          (snipeClippedBdd B β p) ≤
        16 * B ^ 2 * min 1 ((d : ℝ) * blockEnergy β p d / n) := by
    simpa using worstRiskBdd_clipped_le_min (V := Fin n)
      p hp0 hp1 d β B hB
  have hA0 : 0 ≤ blockEnergy β p d := by
    unfold blockEnergy
    apply Finset.sum_nonneg
    intro r hr
    apply div_nonneg
    · positivity
    · exact pow_nonneg
        (mul_nonneg (le_of_lt hp0) (sub_nonneg.mpr (le_of_lt hp1))) _
  have hminiBdd := minimaxRiskBdd_le_clipped (V := Fin n)
    p hp0 hp1 d β B hB
  have hmono := minimaxRiskL1_le_minimaxRiskBdd (V := Fin n)
    p hp0 hp1 d β B hB
  refine ⟨hinc, ?_, ?_, rfl, hmono, hminiBdd, ?_, ?_, ?_, ?_,
    hraw, hrawBdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hBpos hd
    exact strictModelClass_completeWitness n d β B hn hd hBpos hβ
  · exact minimaxRisk_scaled_block_lower β p hβ hp0 hp1
      κ cLower rfl (min_le_right _ _) n d B hn hdeg hB
  · exact hclipBdd.trans (by
      have hc : (16 : ℝ) ≤ cUpper := le_max_left _ _
      have hmin : 0 ≤ min 1 ((d : ℝ) * blockEnergy β p d / n) := by
        positivity
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hc
          (mul_nonneg (sq_nonneg B) hmin))
  · exact hclip.trans (by
      have hc : (4 : ℝ) ≤ cUpper :=
        (by norm_num : (4 : ℝ) ≤ 16) |>.trans (le_max_left _ _)
      have hmin : 0 ≤ min 1 ((d : ℝ) * blockEnergy β p d / n) := by
        positivity
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hc
          (mul_nonneg (sq_nonneg B) hmin))
  · intro M
    obtain ⟨hpD0, hpD1, hp0D, hp1D, hDeq⟩ := hD
    subst D
    simpa using snipe_unbiased p hp0 hp1 M
  · intro M
    obtain ⟨hpD0, hpD1, hp0D, hp1D, hDeq⟩ := hD
    subst D
    simpa using snipe_unbiased_bdd p hp0 hp1 M
  · intro M i
    exact localEnergy_le_blockEnergy M.edge d β p hp0 hp1 M.degree_le i
  · intro M i
    exact localEnergy_le_blockEnergy M.edge d β p hp0 hp1 M.degree_le i
  · by_cases hd : 1 ≤ d
    · have hc : cLower ≤ c₁ := min_le_left _ _
      calc
        cLower * (d : ℝ) * Nat.choose d (kStar d β p) =
            (d : ℝ) * (cLower * Nat.choose d (kStar d β p)) := by ring
        _ ≤ (d : ℝ) * (c₁ * Nat.choose d (kStar d β p)) := by
          gcongr
        _ ≤ (d : ℝ) * blockEnergy β p d := by
          gcongr
          exact (henergy d hd).1
    · have hd0 : d = 0 := by omega
      simp [hd0]
  · have hc : c₂ ≤ cUpper := le_max_right _ _
    by_cases hd : 1 ≤ d
    · have he := (henergy d hd).2.1
      nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity)
        (show 0 ≤ (Nat.choose d (kStar d β p) : ℝ) by positivity)]
    · have hd0 : d = 0 := by omega
      simp [hd0]
  · exact completeBlock_all_risks_exact n d β B p hp0 hp1 hn hβ hB
  · intro hBpos hd
    dsimp only
    constructor
    · intro U hU
      refine ⟨⟨blockScheduleModel n d β B p 1 hn hd hdn hB hβ hp0 hp1
          (Or.inr rfl) U hU, rfl, rfl⟩,
        ⟨blockScheduleModel n d β B p (-1) hn hd hdn hB hβ hp0 hp1
          (Or.inl rfl) U hU, rfl, rfl⟩, ?_, ?_⟩
      · simpa [mul_assoc] using
          tte_blockSchedule n d β B p 1 hn hd hβ hp0 hp1 (Or.inr rfl) U
      · simpa [mul_assoc] using
          tte_blockSchedule n d β B p (-1) hn hd hβ hp0 hp1 (Or.inl rfl) U
    · refine ⟨blockPrior_hellinger_le n d β B p hn hd hdn hBpos hβ hp0 hp1,
        ?_⟩
      obtain ⟨hρlo, hρhi⟩ := activeShare_bounds n d hn hd hdn
      exact ⟨hρlo, hρhi, blockEnergy_div_blockCount n d β p hn hd hdn⟩
-- @realizes c_{\beta,p}(universal positive lower constant, outside n,d,B)
-- @realizes C_{\beta,p}(universal finite upper constant, outside n,d,B)

/-- The score-aligned block coefficient schedule is unchanged when its block design,
coefficient bound, sign choice, baseline vector, focal unit, and interaction set are replaced
by equal values. -/
add_decl_doc blockSchedule.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
