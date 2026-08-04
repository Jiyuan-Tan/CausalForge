import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourableProperties_Part1

/-!
# The least-favourable schedule model and its potential outcomes

Builds the model whose response is the block schedule, evaluates its potential
outcomes on active and inactive units, and computes the resulting total
treatment effect.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Every schedule in the displayed least-favourable family is a member of
the coefficient-mass model class. -/
noncomputable def blockScheduleModel
    (n d β : ℕ) (B p σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 ≤ B) (hβ : 1 ≤ β)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hσ : σ = -1 ∨ σ = 1)
    (U : Fin (blockCount n d) → ℝ)
    (hU : ∀ b, |U b| ≤ B / 2) :
    ModelClass (Fin n) d β B :=
  { edge := blockGraph n d
    decEdge := Classical.decRel _
    coef := blockSchedule n d β B p σ hσ U
    supported := blockSchedule_supported n d β B p σ hσ U
    degree_le := blockGraph_degree_le n d hd
    low_order := blockSchedule_lowOrder n d β B p σ hd hσ U
    mass_le := blockSchedule_mass_le n d β B p σ hn hd hdn hB hβ hp0 hp1
      hσ U hU }

/-- A global raw monomial inside one active block is the corresponding local
raw monomial after restriction of the assignment. -/
lemma rawMonomial_localSubset_blockAssignment
    (n d : ℕ) (hd : 1 ≤ d) (i : Fin n)
    (hi : i.val < activeCount n d)
    (T : Finset (Fin n))
    (hT : ∀ j ∈ T,
      j.val < activeCount n d ∧ j.val / d = i.val / d)
    (z : Fin n → Bool) :
    (∏ j ∈ T, if z j then (1 : ℝ) else 0) =
      rawMonomial (localSubset n d T)
        (blockAssignment n d
          ⟨i.val / d, by
            simp only [activeCount] at hi
            rw [Nat.div_lt_iff_lt_mul (by omega)]
            simpa [Nat.mul_comm] using hi⟩ z) := by
  classical
  let f : Fin n → Fin d :=
    fun j => ⟨j.val % d, Nat.mod_lt _ (by omega)⟩
  have hinj : ∀ j ∈ T, ∀ k ∈ T, f j = f k → j = k := by
    intro j hj k hk heq
    apply Fin.ext
    have hmod : j.val % d = k.val % d := Fin.ext_iff.mp heq
    have hjq := (hT j hj).2
    have hkq := (hT k hk).2
    calc
      j.val = d * (j.val / d) + j.val % d := (Nat.div_add_mod j.val d).symm
      _ = d * (k.val / d) + k.val % d := by rw [hjq, hkq, hmod]
      _ = k.val := Nat.div_add_mod k.val d
  rw [localSubset, dif_pos (by omega)]
  unfold rawMonomial
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro j hj
    have hjq := (hT j hj).2
    have hidx :
        (⟨(i.val / d) * d + (f j).val, by
          have hactive := (hT j hj).1
          simpa [f, ← hjq, Nat.mul_comm] using
            (show d * (j.val / d) + j.val % d < n by
              rw [Nat.div_add_mod]
              exact j.isLt)⟩ : Fin n) = j := by
      apply Fin.ext
      dsimp [f]
      rw [← hjq]
      simpa [Nat.mul_comm] using Nat.div_add_mod j.val d
    simp only [blockInd, blockAssignment]
    let q : Fin n :=
      ⟨(i.val / d) * d + (f j).val, by
        have hactive := (hT j hj).1
        simpa [f, ← hjq, Nat.mul_comm] using
          (show d * (j.val / d) + j.val % d < n by
            rw [Nat.div_add_mod]
            exact j.isLt)⟩
    change (if z j then (1 : ℝ) else 0) =
      if z q then (1 : ℝ) else 0
    have hz : z j = z q := congrArg z (by simpa [q] using hidx.symm)
    cases hjz : z j <;> cases hqz : z q <;> simp_all
  · exact hinj

/-- Evaluation of an active block schedule is a translated normalized block
representer. -/
lemma potentialOutcome_blockSchedule
    (n d β : ℕ) (B p σ : ℝ) (hd : 1 ≤ d)
    (hσ : σ = -1 ∨ σ = 1)
    (U : Fin (blockCount n d) → ℝ)
    (i : Fin n) (hi : i.val < activeCount n d)
    (z : Fin n → Bool) :
    potentialOutcome (blockGraph n d)
        (blockSchedule n d β B p σ hσ U) i z =
      U ⟨i.val / d, by
        simp only [activeCount] at hi
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        simpa [Nat.mul_comm] using hi⟩ +
      σ * tiltAmplitude B β p (blockCount n d) d *
        blockRepresenter β p d
          (blockAssignment n d
            ⟨i.val / d, by
              simp only [activeCount] at hi
              rw [Nat.div_lt_iff_lt_mul (by omega)]
              simpa [Nat.mul_comm] using hi⟩ z) := by
  classical
  let b : Fin (blockCount n d) :=
    ⟨i.val / d, by
      simp only [activeCount] at hi
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [Nat.mul_comm] using hi⟩
  have hcond (T : Finset (Fin n))
      (hmem : T ∈ (nbhd (blockGraph n d) i).powerset) :
      ∀ j ∈ T,
        j.val < activeCount n d ∧ j.val / d = i.val / d := by
    intro j hj
    have hjN := Finset.mem_powerset.mp hmem hj
    exact ⟨((Finset.mem_filter.mp hjN).2).1,
      ((Finset.mem_filter.mp hjN).2).2.2⟩
  unfold potentialOutcome
  rw [show
      (∑ T ∈ (nbhd (blockGraph n d) i).powerset,
        blockSchedule n d β B p σ hσ U i T *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) =
      (∑ T ∈ (nbhd (blockGraph n d) i).powerset,
        (if T = ∅ then U b else 0) *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) +
      (∑ T ∈ (nbhd (blockGraph n d) i).powerset,
        (σ * tiltAmplitude B β p (blockCount n d) d *
          blockRawCoef β p d (localSubset n d T)) *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T hmem
    rw [blockSchedule, dif_pos hi, dif_pos (hcond T hmem)]
    have hb' : i.val / d < blockCount n d := b.isLt
    by_cases hTe : T = ∅
    · simp [hTe, baselineAt, hb', b]
    · simp [hTe]]
  have hbase :
      (∑ T ∈ (nbhd (blockGraph n d) i).powerset,
        (if T = ∅ then U b else 0) *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) = U b := by
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro T hT hTne
      simp [hTne]
    · intro hnot
      exact (hnot (by simp)).elim
  rw [hbase]
  have hpert :
      (∑ T ∈ (nbhd (blockGraph n d) i).powerset,
        (σ * tiltAmplitude B β p (blockCount n d) d *
          blockRawCoef β p d (localSubset n d T)) *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) =
        σ * tiltAmplitude B β p (blockCount n d) d *
          blockRepresenter β p d (blockAssignment n d b z) := by
    rw [show
        (∑ T ∈ (nbhd (blockGraph n d) i).powerset,
          (σ * tiltAmplitude B β p (blockCount n d) d *
            blockRawCoef β p d (localSubset n d T)) *
            ∏ j ∈ T, if z j then (1 : ℝ) else 0) =
          σ * tiltAmplitude B β p (blockCount n d) d *
            ∑ T ∈ (nbhd (blockGraph n d) i).powerset,
              blockRawCoef β p d (localSubset n d T) *
                ∏ j ∈ T, if z j then (1 : ℝ) else 0 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      ring]
    congr 1
    rw [blockRepresenter_raw_expansion β d p hd]
    rw [← sum_block_powerset_localSubset n d hd i hi
      (fun S => blockRawCoef β p d S *
        rawMonomial S (blockAssignment n d b z))]
    apply Finset.sum_congr rfl
    intro T hmem
    rw [rawMonomial_localSubset_blockAssignment n d hd i hi T
      (hcond T hmem) z]
  rw [hpert]

/-- Inactive units in the block construction have zero potential outcome. -/
lemma potentialOutcome_blockSchedule_inactive
    (n d β : ℕ) (B p σ : ℝ)
    (hσ : σ = -1 ∨ σ = 1)
    (U : Fin (blockCount n d) → ℝ)
    (i : Fin n) (hi : ¬ i.val < activeCount n d)
    (z : Fin n → Bool) :
    potentialOutcome (blockGraph n d)
      (blockSchedule n d β B p σ hσ U) i z = 0 := by
  classical
  have hnbhd : nbhd (blockGraph n d) i = ∅ := by
    ext j
    simp [nbhd, blockGraph, hi]
  simp [potentialOutcome, hnbhd, blockSchedule, hi]

/-- The number of active `Fin n` indices is `activeCount n d`. -/
lemma card_active_units (n d : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun i => i.val < activeCount n d)).card = activeCount n d := by
  have hle := activeCount_le n d
  have hcard : ((Finset.univ : Finset (Fin n)).filter
        (fun i => i.val < activeCount n d)).card =
      (Finset.univ : Finset (Fin (activeCount n d))).card := by
    apply Finset.card_bij
      (fun i _ => (⟨i.val, by
        exact (Finset.mem_filter.mp ‹i ∈
          (Finset.univ : Finset (Fin n)).filter
            (fun i => i.val < activeCount n d)›).2⟩ :
          Fin (activeCount n d)))
    · intro i hi
      simp
    · intro i hi j hj heq
      apply Fin.ext
      exact congrArg (fun x : Fin (activeCount n d) => x.val) heq
    · intro k hk
      refine ⟨⟨k.val, k.isLt.trans_le hle⟩, ?_, ?_⟩
      · simp [k.isLt]
      · rfl
  simpa using hcard

/-- The all-treated/all-control contrast of a least-favourable schedule is
the active share times its signed tilt. -/
lemma tte_blockSchedule
    (n d β : ℕ) (B p σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hβ : 1 ≤ β) (hp0 : 0 < p) (hp1 : p < 1)
    (hσ : σ = -1 ∨ σ = 1)
    (U : Fin (blockCount n d) → ℝ) :
    tte (blockGraph n d) (blockSchedule n d β B p σ hσ U) =
      σ * activeShare n d * tiltAmplitude B β p (blockCount n d) d := by
  classical
  let D := blockDesign d p (le_of_lt hp0) (le_of_lt hp1)
  have hD : IsProductBernoulli D p := by
    refine ⟨hp0, hp1, ?_⟩
    exact ⟨fun _ => le_of_lt hp0, fun _ => le_of_lt hp1, rfl⟩
  have hcontrast :
      blockRepresenter β p d (fun _ => true) -
        blockRepresenter β p d (fun _ => false) = 1 := by
    simpa [contrastFunctional] using
      (blockRepresenter_contrast_energy β d p D hD hβ hd).1
  have hunit (i : Fin n) (hi : i.val < activeCount n d) :
      potentialOutcome (blockGraph n d)
          (blockSchedule n d β B p σ hσ U) i (fun _ => true) -
        potentialOutcome (blockGraph n d)
          (blockSchedule n d β B p σ hσ U) i (fun _ => false) =
        σ * tiltAmplitude B β p (blockCount n d) d := by
    rw [potentialOutcome_blockSchedule n d β B p σ hd hσ U i hi,
      potentialOutcome_blockSchedule n d β B p σ hd hσ U i hi]
    have htrue :
        blockAssignment n d
          ⟨i.val / d, by
            simp only [activeCount] at hi
            rw [Nat.div_lt_iff_lt_mul (by omega)]
            simpa [Nat.mul_comm] using hi⟩ (fun _ => true) =
          (fun _ => true) := by funext j; rfl
    have hfalse :
        blockAssignment n d
          ⟨i.val / d, by
            simp only [activeCount] at hi
            rw [Nat.div_lt_iff_lt_mul (by omega)]
            simpa [Nat.mul_comm] using hi⟩ (fun _ => false) =
          (fun _ => false) := by funext j; rfl
    rw [htrue, hfalse]
    calc
      (U _ + σ * tiltAmplitude B β p (blockCount n d) d *
          blockRepresenter β p d (fun _ => true)) -
          (U _ + σ * tiltAmplitude B β p (blockCount n d) d *
            blockRepresenter β p d (fun _ => false)) =
        σ * tiltAmplitude B β p (blockCount n d) d *
          (blockRepresenter β p d (fun _ => true) -
            blockRepresenter β p d (fun _ => false)) := by ring
      _ = σ * tiltAmplitude B β p (blockCount n d) d := by
        rw [hcontrast]
        ring
  have hinactive (i : Fin n) (hi : ¬ i.val < activeCount n d) :
      potentialOutcome (blockGraph n d)
          (blockSchedule n d β B p σ hσ U) i (fun _ => true) -
        potentialOutcome (blockGraph n d)
          (blockSchedule n d β B p σ hσ U) i (fun _ => false) = 0 := by
    rw [potentialOutcome_blockSchedule_inactive n d β B p σ hσ U i hi,
      potentialOutcome_blockSchedule_inactive n d β B p σ hσ U i hi]
    ring
  unfold tte
  rw [show
      (∑ i : Fin n,
        (potentialOutcome (blockGraph n d)
            (blockSchedule n d β B p σ hσ U) i (fun _ => true) -
          potentialOutcome (blockGraph n d)
            (blockSchedule n d β B p σ hσ U) i (fun _ => false))) =
        ∑ i : Fin n, if i.val < activeCount n d then
          σ * tiltAmplitude B β p (blockCount n d) d else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hia : i.val < activeCount n d
    · rw [if_pos hia, hunit i hia]
    · rw [if_neg hia, hinactive i hia]]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, card_active_units]
  simp only [nsmul_eq_mul]
  unfold activeShare
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [Fintype.card_fin]
  push_cast
  field_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
