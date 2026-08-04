import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.HellingerAffinity
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.HeadlineSupport
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.MinimaxRisk

/-!
# Model-class inclusion and the scaled-block minimax lower bound

Relates the coefficient-mass and bounded-outcome model classes, defines the
worst-case risks at a fixed interaction graph, exhibits a strict witness model,
and proves the scaled-block lower bound on the minimax risk.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
open Causalean.Stat
/-- Carrier-preserving inclusion of the coefficient-mass model in the
bounded-outcome model. -/
def ModelClassIncluded (V : Type*) [Fintype V] [DecidableEq V]
    (d β : ℕ) (B : ℝ) : Prop :=
  ∀ M : ModelClass V d β B,
    ∃ N : BddOutcomeModelClass V d β B,
      N.edge = M.edge ∧ N.coef = M.coef

/-- Strictness means that some bounded-outcome carrier pair has no
coefficient-mass realization with the same graph and schedule. -/
def ModelClassStrict (V : Type*) [Fintype V] [DecidableEq V]
    (d β : ℕ) (B : ℝ) : Prop :=
  ModelClassIncluded V d β B ∧
    ∃ N : BddOutcomeModelClass V d β B,
      ¬ ∃ M : ModelClass V d β B,
        N.edge = M.edge ∧ N.coef = M.coef

/-- The coefficient-mass envelope implies the uniform potential-outcome
envelope, without changing either carrier component. -/
lemma modelClassIncluded_of_coeffMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (d β : ℕ) (B : ℝ) :
    ModelClassIncluded V d β B := by
  classical
  intro M
  let N : BddOutcomeModelClass V d β B :=
    { edge := M.edge
      decEdge := M.decEdge
      coef := M.coef
      supported := M.supported
      degree_le := M.degree_le
      low_order := M.low_order
      outcome_bound := by
        intro i z
        unfold potentialOutcome
        calc
          |∑ S ∈ (nbhd M.edge i).powerset,
              M.coef i S *
                ∏ j ∈ S, if z j then (1 : ℝ) else 0| ≤
              ∑ S ∈ (nbhd M.edge i).powerset,
                |M.coef i S *
                  ∏ j ∈ S, if z j then (1 : ℝ) else 0| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ S ∈ (nbhd M.edge i).powerset, |M.coef i S| := by
            apply Finset.sum_le_sum
            intro S hS
            rw [abs_mul]
            apply mul_le_of_le_one_right (abs_nonneg _)
            rw [Finset.abs_prod]
            exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
              (fun j _ => by cases z j <;> norm_num)
          _ ≤ B := M.mass_le i }
  exact ⟨N, rfl, rfl⟩

/-- Worst risk restricted to models whose graph is a prescribed relation. -/
noncomputable def worstRiskFixedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (G : V → V → Prop) (d β : ℕ) (B : ℝ) (est : Estimator V) : ℝ :=
  sSup {r : ℝ | ∃ M : ModelClass V d β B,
    M.edge = G ∧ r = riskAt p hp0 hp1 M est}

/-- Bounded-outcome analogue of `worstRiskFixedGraph`. -/
noncomputable def worstRiskBddFixedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (G : V → V → Prop) (d β : ℕ) (B : ℝ) (est : Estimator V) : ℝ :=
  sSup {r : ℝ | ∃ M : BddOutcomeModelClass V d β B,
    M.edge = G ∧ r = riskAtBdd p hp0 hp1 M est}

/-- A one-loop schedule with coefficients `B` and `-2B` has outcomes in
`[-B,B]` but coefficient mass `3B`, witnessing strict inclusion. -/
lemma strictModelClass_completeWitness
    (n d β : ℕ) (B : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hB : 0 < B) (hβ : 1 ≤ β) :
    ModelClassStrict (Fin n) d β B := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let G : Fin n → Fin n → Prop := fun j i => j = i0 ∧ i = i0
  let c : Fin n → Finset (Fin n) → ℝ := fun i S =>
    if i = i0 then
      if S = ∅ then B else if S = {i0} then -2 * B else 0
    else 0
  have hnbhd0 : nbhd G i0 = {i0} := by
    ext j
    simp [nbhd, G]
  have hnbhd (i : Fin n) (hi : i ≠ i0) : nbhd G i = ∅ := by
    ext j
    simp [nbhd, G, hi]
  have hpowerset :
      (({i0} : Finset (Fin n)).powerset) =
        ({∅, {i0}} : Finset (Finset (Fin n))) := by
    ext S
    simp [Finset.subset_singleton_iff]
  have hout0 : outNbhd G i0 = {i0} := by
    ext i
    simp [outNbhd, G]
  have hout (j : Fin n) (hj : j ≠ i0) : outNbhd G j = ∅ := by
    ext i
    simp [outNbhd, G, hj]
  let N : BddOutcomeModelClass (Fin n) d β B :=
    { edge := G
      decEdge := Classical.decRel _
      coef := c
      supported := by
        intro i S hS
        by_cases hi : i = i0
        · subst i
          by_cases hS0 : S = ∅
          · subst S
            exact (hS (by simp)).elim
          · by_cases hS1 : S = {i0}
            · subst S
              exact (hS (by simp [hnbhd0])).elim
            · simp [c, hS0, hS1]
        · simp [c, hi]
      degree_le := by
        constructor
        · intro i
          by_cases hi : i = i0
          · subst i
            simp [hnbhd0, hd]
          · simp [hnbhd i hi]
        · intro j
          by_cases hj : j = i0
          · subst j
            simp [hout0, hd]
          · simp [hout j hj]
      low_order := by
        intro i S hcard
        by_cases hi : i = i0
        · subst i
          have hS0 : S ≠ ∅ := by
            intro h
            subst S
            simp at hcard
          have hS1 : S ≠ {i0} := by
            intro h
            subst S
            simp at hcard
            omega
          simp [c, hS0, hS1]
        · simp [c, hi]
      outcome_bound := by
        intro i z
        by_cases hi : i = i0
        · subst i
          cases hz : z i0
          · simp [potentialOutcome, hnbhd0, hpowerset, c, hz,
              abs_of_pos hB]
          · simp [potentialOutcome, hnbhd0, hpowerset, c, hz]
            rw [show B + -(2 * B) = -B by ring, abs_neg, abs_of_pos hB]
        · simp [potentialOutcome, hnbhd i hi, c, hi, hB.le] }
  refine ⟨modelClassIncluded_of_coeffMass d β B, N, ?_⟩
  rintro ⟨M, hEdge, hCoef⟩
  have hmass := M.mass_le i0
  rw [← hEdge, ← hCoef] at hmass
  simp only [N, hnbhd0, hpowerset, c, if_pos] at hmass
  simp [abs_of_pos hB] at hmass
  linarith

/-- The coefficient-class minimax risk is nonnegative when the envelope is
nonnegative. -/
lemma minimaxRisk_nonneg_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ minimaxRisk (V := V) p hp0 hp1 d β B := by
  let M0 : ModelClass V d β B :=
    { edge := fun _ _ => False
      decEdge := fun _ _ => inferInstance
      coef := fun _ _ => 0
      supported := by simp
      degree_le := by simp [BoundedDegree, nbhd, outNbhd]
      low_order := by simp [LowOrder]
      mass_le := by intro i; simpa [BoundedCoeffMass] using hB }
  unfold minimaxRisk
  apply le_csInf
  · refine ⟨worstRisk (V := V) p hp0 hp1 d β B
        ((fun _ _ _ => (0 : ℝ)) : Estimator V), ?_⟩
    exact ⟨(fun _ _ _ => (0 : ℝ) : Estimator V),
      zeroEstimator_admissible p hp0 hp1 d β B, rfl⟩
  · intro r hr
    rcases hr with ⟨est, hest, rfl⟩
    have hrisk : 0 ≤ riskAt p hp0 hp1 M0 est := by
      unfold riskAt
      exact
        (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
          (fun _ => hp1)).mse_nonneg _ _
    exact hrisk.trans (le_csSup hest.2 (Set.mem_range_self M0))

set_option maxHeartbeats 3000000 in
-- The proof performs several nonlinear normalizations of the block-prior scale.
/-- The continuous block prior, with the universal tilt used in the theorem,
gives the saturated finite-size lower frontier. -/
lemma minimaxRisk_scaled_block_lower
    (β : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (κ cLower : ℝ)
    (hκdef : κ =
      min ((2 * representerMassSup β p)⁻¹) ((4 * Real.pi)⁻¹))
    (hcLower : cLower ≤ κ ^ 2 / 16)
    (n d : ℕ) (B : ℝ)
    (hn : 1 ≤ n) (hdeg : DegreeIndex (Fin n) d) (hB : 0 ≤ B) :
    cLower * B ^ 2 *
        min 1 ((d : ℝ) * blockEnergy β p d / n) ≤
      minimaxRiskL1 (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
        d β B := by
  have hdn : d ≤ n := by simpa [DegreeIndex] using hdeg
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  by_cases hd : 1 ≤ d
  · by_cases hBpos : 0 < B
    · let m := blockCount n d
      let ρ := activeShare n d
      let A := blockEnergy β p d
      let t := min 1 (Real.sqrt (A / m))
      let δ := tiltAmplitude B β p m d
      have hm : 0 < m := blockCount_pos n d hn hd hdn
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hA : 0 < A := blockEnergy_pos β d p hβ hd hp0 hp1
      have hA0 : 0 ≤ A := hA.le
      have hρ := activeShare_bounds n d hn hd hdn
      have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hρ.1
      have hκ0 : 0 ≤ κ := by
        have hmass : 0 < representerMassSup β p :=
          representerMassSup_pos β p hβ hp0 hp1
        rw [hκdef]
        rw [le_min_iff]
        constructor
        · exact inv_nonneg.mpr (mul_nonneg (by norm_num) hmass.le)
        · exact inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)
      have hκpi : κ ≤ (4 * Real.pi)⁻¹ := by
        rw [hκdef]
        exact min_le_right _ _
      have ht0 : 0 ≤ t := by
        dsimp [t]
        rw [le_min_iff]
        exact ⟨by norm_num, Real.sqrt_nonneg _⟩
      have ht_le_sqrt : t ≤ Real.sqrt (A / m) := by
        dsimp [t]
        exact min_le_right _ _
      have hsqrtSq : Real.sqrt (A / m) ^ 2 = A / m := by
        exact Real.sq_sqrt (div_nonneg hA0 hmR.le)
      have htSqLe : t ^ 2 ≤ A / m := by
        calc
          t ^ 2 ≤ Real.sqrt (A / m) ^ 2 :=
            (sq_le_sq₀ ht0 (Real.sqrt_nonneg _)).2 ht_le_sqrt
          _ = A / m := hsqrtSq
      have hmt : (m : ℝ) * t ^ 2 ≤ A := by
        have := (le_div_iff₀ hmR).mp htSqLe
        nlinarith
      have hκsq : 16 * Real.pi ^ 2 * κ ^ 2 ≤ 1 := by
        have hmul : 4 * Real.pi * κ ≤ 1 := by
          calc
            4 * Real.pi * κ ≤ 4 * Real.pi * (4 * Real.pi)⁻¹ := by
              gcongr
            _ = 1 := by field_simp
        have hmul0 : 0 ≤ 4 * Real.pi * κ := by positivity
        nlinarith [sq_nonneg (4 * Real.pi * κ)]
      have hδ : δ = B * κ * t := by
        simp [δ, tiltAmplitude, m, A, t, hκdef]
      have hhell :
          hellingerSqDensity (blockDominatingMeasure n d)
              (blockPriorDensity n d β B p 1)
              (blockPriorDensity n d β B p (-1)) ≤ 1 / 4 := by
        refine (blockPrior_hellinger_le n d β B p hn hd hdn hBpos
          hβ hp0 hp1).trans ?_
        change 4 * Real.pi ^ 2 * (m : ℝ) * δ ^ 2 /
            (B ^ 2 * A) ≤ 1 / 4
        rw [hδ]
        have hden : 0 < B ^ 2 * A := mul_pos (sq_pos_of_pos hBpos) hA
        rw [div_le_iff₀ hden]
        calc
          4 * Real.pi ^ 2 * (m : ℝ) * (B * κ * t) ^ 2 =
              B ^ 2 * (4 * Real.pi ^ 2 * κ ^ 2) *
                ((m : ℝ) * t ^ 2) := by ring
          _ ≤ B ^ 2 * (1 / 4) * A := by
            gcongr
            nlinarith
          _ = (1 / 4 : ℝ) * (B ^ 2 * A) := by ring
      have hprior := minimaxRisk_blockPrior_lower n d β B p hn hd hdn
        hBpos hβ hp0 hp1 hhell
      have hratio := blockEnergy_div_blockCount n d β p hn hd hdn
      have hxy :
          (d : ℝ) * A / n = ρ * (A / m) := by
        dsimp [ρ, A, m] at hratio ⊢
        have hρne : activeShare n d ≠ 0 := hρ0.ne'
        field_simp [hρne] at hratio ⊢
        nlinarith
      have hxle :
          (d : ℝ) * A / n ≤ A / m := by
        rw [hxy]
        exact mul_le_of_le_one_left (div_nonneg hA0 hmR.le) hρ.2
      have htsq : t ^ 2 = min 1 (A / m) := by
        by_cases hs : Real.sqrt (A / m) ≤ 1
        · have hy : A / m ≤ 1 := by
            rw [← hsqrtSq]
            nlinarith [Real.sqrt_nonneg (A / m)]
          rw [show t = min 1 (Real.sqrt (A / m)) by rfl,
            min_eq_right hs, hsqrtSq, min_eq_right hy]
        · have hs' : 1 ≤ Real.sqrt (A / m) := le_of_not_ge hs
          have hy : 1 ≤ A / m := by
            rw [← hsqrtSq]
            nlinarith [Real.sqrt_nonneg (A / m)]
          rw [show t = min 1 (Real.sqrt (A / m)) by rfl,
            min_eq_left hs', one_pow, min_eq_left hy]
      have hmin :
          min 1 ((d : ℝ) * A / n) ≤ t ^ 2 := by
        rw [htsq]
        exact min_le_min_left 1 hxle
      have hscale :
          cLower * B ^ 2 * min 1 ((d : ℝ) * A / n) ≤
            (ρ * δ) ^ 2 / 4 := by
        rw [hδ]
        have hρsq : (1 / 4 : ℝ) ≤ ρ ^ 2 := by
          have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
            hρ0.le).2 hρ.1
          norm_num at hs ⊢
          exact hs
        have hcommon : 0 ≤ B ^ 2 * t ^ 2 := mul_nonneg (sq_nonneg B) (sq_nonneg t)
        have hK : 0 ≤ κ ^ 2 / 16 := by positivity
        have hquarter :
            (1 / 16 : ℝ) ≤ ρ ^ 2 / 4 := by
          apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
          norm_num
          exact hρsq
        have hfac :
            κ ^ 2 / 16 ≤ ρ ^ 2 / 4 * κ ^ 2 := by
          calc
            κ ^ 2 / 16 = (1 / 16 : ℝ) * κ ^ 2 := by ring
            _ ≤ (ρ ^ 2 / 4) * κ ^ 2 :=
              mul_le_mul_of_nonneg_right hquarter (sq_nonneg κ)
        calc
          cLower * B ^ 2 * min 1 ((d : ℝ) * A / n) ≤
              (κ ^ 2 / 16) * B ^ 2 * t ^ 2 := by
            calc
              cLower * B ^ 2 * min 1 ((d : ℝ) * A / n) ≤
                  (κ ^ 2 / 16) * B ^ 2 *
                    min 1 ((d : ℝ) * A / n) := by
                simpa [mul_assoc] using
                  mul_le_mul_of_nonneg_right hcLower
                    (mul_nonneg (sq_nonneg B)
                      (by positivity :
                        0 ≤ min 1 ((d : ℝ) * A / n)))
              _ ≤ (κ ^ 2 / 16) * B ^ 2 * t ^ 2 := by
                exact mul_le_mul_of_nonneg_left hmin
                  (mul_nonneg hK (sq_nonneg B))
          _ ≤ (ρ ^ 2 / 4) * (B ^ 2 * κ ^ 2 * t ^ 2) := by
            calc
              (κ ^ 2 / 16) * B ^ 2 * t ^ 2 =
                  (κ ^ 2 / 16) * (B ^ 2 * t ^ 2) := by ring
              _ ≤ (ρ ^ 2 / 4 * κ ^ 2) * (B ^ 2 * t ^ 2) :=
                mul_le_mul_of_nonneg_right hfac hcommon
              _ = (ρ ^ 2 / 4) * (B ^ 2 * κ ^ 2 * t ^ 2) := by ring
          _ = (ρ * (B * κ * t)) ^ 2 / 4 := by ring
      dsimp only at hprior
      change (ρ * δ) ^ 2 / 4 ≤
        minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B at hprior
      change cLower * B ^ 2 *
          min 1 ((d : ℝ) * blockEnergy β p d / n) ≤
        minimaxRisk (V := Fin n) p (le_of_lt hp0) (le_of_lt hp1)
          d β B
      exact hscale.trans hprior
    · have hB0 : B = 0 := by linarith
      subst B
      simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
        minimaxRiskL1] using
          minimaxRisk_nonneg_of_nonneg (V := Fin n) p
            (le_of_lt hp0) (le_of_lt hp1) d β 0 (by norm_num)
  · have hd0 : d = 0 := by omega
    subst d
    simpa only [Nat.cast_zero, zero_mul, zero_div,
      min_eq_right (by norm_num : (0 : ℝ) ≤ 1), mul_zero,
      minimaxRiskL1] using
        minimaxRisk_nonneg_of_nonneg (V := Fin n) p
          (le_of_lt hp0) (le_of_lt hp1) 0 β B hB

/-- The coefficient-mass minimax mean-squared risk is unchanged when the assignment
probability, its bounds, the degree and interaction parameters, and the outcome bound are
replaced by equal values. -/
add_decl_doc minimaxRisk.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
