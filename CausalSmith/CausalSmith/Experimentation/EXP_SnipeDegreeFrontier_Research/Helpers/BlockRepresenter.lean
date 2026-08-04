import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenterCore
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenterUniform

/-!
# Block representer optimization and uniform bounds

This file builds the optimization and uniform coefficient bounds on top of
the finite Bernoulli identities in `BlockRepresenterCore`.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

/-- Strict product Bernoulli expectation is faithful on squares. -/
lemma blockDesign_sq_eq_zero_iff
    (d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : (Fin d → Bool) → ℝ) :
    (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
        (fun z => f z ^ 2) = 0 ↔ f = 0 := by
  constructor
  · intro hf
    let D := blockDesign d p (le_of_lt hp0) (le_of_lt hp1)
    funext z
    have hnonneg (x : Fin d → Bool) : 0 ≤ D.p x * f x ^ 2 :=
      mul_nonneg (D.p_nonneg x) (sq_nonneg (f x))
    have hle : D.p z * f z ^ 2 ≤ ∑ x, D.p x * f x ^ 2 :=
      Finset.single_le_sum (fun x _ => hnonneg x) (Finset.mem_univ z)
    have hterm : D.p z * f z ^ 2 = 0 := by
      apply le_antisymm
      · simpa [D, FiniteDesign.E] using hle.trans_eq hf
      · exact hnonneg z
    have hpz : 0 < D.p z := by
      dsimp [D]
      simp only [blockDesign, bernoulliDesign,
        Causalean.Experimentation.DesignBased.prodDesign_p]
      apply Finset.prod_pos
      intro i hi
      simp only [coinDesign]
      cases h : z i <;> simp [h, hp0, hp1]
    exact sq_eq_zero_iff.mp
      (mul_eq_zero.mp hterm |>.resolve_left hpz.ne')
  · rintro rfl
    simp

/-- The centered score belongs to the raw low-order polynomial span. -/
lemma blockScore_mem_polySpace (β d : ℕ) (p : ℝ) :
    blockScore β p d ∈ polySpace β d := by
  rw [show blockScore β p d =
      fun z => ∑ r ∈ Finset.Icc 1 (effBeta β d),
        (bernoulliContrast p r / (p * (1 - p)) ^ r) *
          ∑ S ∈ Finset.univ.powerset.filter
              (fun S : Finset (Fin d) => S.card = r),
            ∏ j ∈ S, (blockInd z j - p) by rfl]
  rw [show
      (fun z => ∑ r ∈ Finset.Icc 1 (effBeta β d),
        (bernoulliContrast p r / (p * (1 - p)) ^ r) *
          ∑ S ∈ Finset.univ.powerset.filter
              (fun S : Finset (Fin d) => S.card = r),
            ∏ j ∈ S, (blockInd z j - p)) =
      ∑ r ∈ Finset.Icc 1 (effBeta β d),
        (bernoulliContrast p r / (p * (1 - p)) ^ r) •
          (fun z => ∑ S ∈ Finset.univ.powerset.filter
              (fun S : Finset (Fin d) => S.card = r),
            ∏ j ∈ S, (blockInd z j - p)) by
    funext z
    simp]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  rw [show
      (fun z => ∑ S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin d) => S.card = r),
        ∏ j ∈ S, (blockInd z j - p)) =
      ∑ S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin d) => S.card = r),
        (fun z => ∏ j ∈ S, (blockInd z j - p)) by
    funext z
    simp]
  apply Submodule.sum_mem
  intro S hS
  have hScard : S.card = r := (Finset.mem_filter.mp hS).2
  have hrle : r ≤ effBeta β d := (Finset.mem_Icc.mp hr).2
  rw [show (fun z => ∏ j ∈ S, (blockInd z j - p)) =
      ∑ T ∈ S.powerset,
        (-p) ^ (S.card - T.card) • rawMonomial T by
    funext z
    simpa using centeredMonomial_raw_expansion d p S z]
  apply Submodule.sum_mem
  intro T hT
  apply Submodule.smul_mem
  rw [polySpace]
  apply Submodule.subset_span
  exact ⟨T, by
    refine ⟨?_, rfl⟩
    exact (Finset.card_le_card (Finset.mem_powerset.mp hT)).trans
      (hScard.le.trans hrle)⟩

/-- Weight feasibility extends from raw generators to their full span. -/
lemma weightFeasibleAt_represents
    (β d : ℕ) (D : FiniteDesign (Fin d → Bool))
    (w : (Fin d → Bool) → ℝ) (hw : WeightFeasibleAt D β w)
    (f : (Fin d → Bool) → ℝ) (hf : f ∈ polySpace β d) :
    D.E (fun z => w z * f z) = contrastFunctional f := by
  rw [polySpace] at hf
  refine Submodule.span_induction (p := fun f _ =>
      D.E (fun z => w z * f z) = contrastFunctional f)
    ?_ ?_ ?_ ?_ hf
  · intro f hf
    rcases hf with ⟨S, hScard, rfl⟩
    by_cases hS : S.Nonempty
    · rw [hw.2 S hS hScard]
      unfold contrastFunctional rawMonomial
      have hz : (∏ j ∈ S, blockInd (fun _ => false) j) = 0 := by
        obtain ⟨j, hj⟩ := hS
        exact Finset.prod_eq_zero hj (by simp [blockInd])
      rw [hz]
      simp [blockInd]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simpa [rawMonomial, contrastFunctional] using hw.1
  · simp [contrastFunctional]
  · intro f g _ _ hf hg
    rw [show (fun z => w z * (f + g) z) =
      (fun z => w z * f z + w z * g z) by
      funext z
      simp [mul_add]]
    rw [D.E_add, hf, hg]
    simp [contrastFunctional]
    ring
  · intro a f _ hf
    rw [show (fun z => w z * (a • f) z) =
      (fun z => a * (w z * f z)) by
      funext z
      change w z * (a * f z) = a * (w z * f z)
      ring]
    rw [D.E_const_mul, hf]
    simp [contrastFunctional, mul_sub]

/-- The normalized score is the unique perturbation-program optimizer. -/
lemma perturbFeasible_energy_unique
    (β d : ℕ) (p : ℝ) (D : FiniteDesign (Fin d → Bool))
    (hD : IsProductBernoulli D p) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (h : (Fin d → Bool) → ℝ) (hh : PerturbFeasible β d h) :
    (blockEnergy β p d)⁻¹ ≤ D.E (fun z => h z ^ 2) ∧
      (D.E (fun z => h z ^ 2) = (blockEnergy β p d)⁻¹ ↔
        h = blockRepresenter β p d) := by
  let A := blockEnergy β p d
  let g := blockScore β p d
  have hA : 0 < A := blockEnergy_pos β d p hβ hd hD.1 hD.2.1
  have hgh : D.E (fun z => g z * h z) = 1 := by
    simpa [g, hh.2] using blockScore_represents β d p D hD h hh.1
  have hgg : D.E (fun z => g z ^ 2) = A :=
    blockScore_sq_expectation β d p D hD
  have hsq :
      D.E (fun z => (A * h z - g z) ^ 2) =
        A ^ 2 * D.E (fun z => h z ^ 2) - A := by
    rw [show (fun z => (A * h z - g z) ^ 2) =
        (fun z => A ^ 2 * h z ^ 2 - 2 * A * (g z * h z) + g z ^ 2) by
      funext z
      ring]
    rw [D.E_add, D.E_sub, D.E_const_mul, D.E_const_mul, hgh, hgg]
    ring
  constructor
  · have hn := D.E_nonneg (fun z => sq_nonneg (A * h z - g z))
    rw [hsq] at hn
    rw [inv_le_iff_one_le_mul₀ hA]
    nlinarith
  · constructor
    · intro heq
      change D.E (fun z => h z ^ 2) = A⁻¹ at heq
      have hz : D.E (fun z => (A * h z - g z) ^ 2) = 0 := by
        rw [hsq, heq]
        field_simp [hA.ne']
        ring
      rcases hD with ⟨hp, hp', hpD⟩
      have hDeq : D =
          blockDesign d p (le_of_lt hp) (le_of_lt hp') := by
        rcases hpD with ⟨hp0', hp1', rfl⟩
        unfold blockDesign
        congr
      have hzero : (fun z => A * h z - g z) = 0 := by
        rw [hDeq] at hz
        exact (blockDesign_sq_eq_zero_iff d p hp hp'
          (fun z => A * h z - g z)).mp hz
      have hfun : h = fun z => g z / A := by
        funext z
        have hz := congrFun hzero z
        simp only [Pi.zero_apply] at hz
        apply (eq_div_iff hA.ne').2
        linarith
      rw [hfun]
      funext z
      simp [blockRepresenter, Nat.ne_of_gt hd, g, A]
    · rintro rfl
      exact (blockRepresenter_contrast_energy β d p D hD hβ hd).2

/-- The score is the unique weight-program optimizer. -/
lemma weightFeasibleAt_energy_unique
    (β d : ℕ) (p : ℝ) (D : FiniteDesign (Fin d → Bool))
    (hD : IsProductBernoulli D p)
    (w : (Fin d → Bool) → ℝ) (hw : WeightFeasibleAt D β w) :
    blockEnergy β p d ≤ D.E (fun z => w z ^ 2) ∧
      (D.E (fun z => w z ^ 2) = blockEnergy β p d ↔
        w = blockScore β p d) := by
  let A := blockEnergy β p d
  let g := blockScore β p d
  have hwg : D.E (fun z => w z * g z) = A := by
    rw [show A = contrastFunctional g by
      exact (blockScore_contrast β d p).symm]
    exact weightFeasibleAt_represents β d D w hw g
      (blockScore_mem_polySpace β d p)
  have hgg : D.E (fun z => g z ^ 2) = A :=
    blockScore_sq_expectation β d p D hD
  have hsq :
      D.E (fun z => (w z - g z) ^ 2) =
        D.E (fun z => w z ^ 2) - A := by
    rw [show (fun z => (w z - g z) ^ 2) =
        (fun z => w z ^ 2 - 2 * (w z * g z) + g z ^ 2) by
      funext z
      ring]
    rw [D.E_add, D.E_sub, D.E_const_mul, hwg, hgg]
    ring
  constructor
  · have hn := D.E_nonneg (fun z => sq_nonneg (w z - g z))
    rw [hsq] at hn
    linarith
  · constructor
    · intro heq
      have hz : D.E (fun z => (w z - g z) ^ 2) = 0 := by
        rw [hsq, heq]
        ring
      rcases hD with ⟨hp, hp', hpD⟩
      have hDeq : D =
          blockDesign d p (le_of_lt hp) (le_of_lt hp') := by
        rcases hpD with ⟨hp0', hp1', rfl⟩
        unfold blockDesign
        congr
      have hzero : (fun z => w z - g z) = 0 := by
        rw [hDeq] at hz
        exact (blockDesign_sq_eq_zero_iff d p hp hp'
          (fun z => w z - g z)).mp hz
      funext z
      have hz := congrFun hzero z
      simpa using sub_eq_zero.mp hz
    · rintro rfl
      exact hgg

/-- The normalized block score satisfies the perturbation constraints. -/
lemma blockRepresenter_perturbFeasible
    (β d : ℕ) (p : ℝ) (D : FiniteDesign (Fin d → Bool))
    (hD : IsProductBernoulli D p) (hβ : 1 ≤ β) (hd : 1 ≤ d) :
    PerturbFeasible β d (blockRepresenter β p d) := by
  constructor
  · rw [show blockRepresenter β p d =
        (blockEnergy β p d)⁻¹ • blockScore β p d by
      funext z
      simp [blockRepresenter, Nat.ne_of_gt hd, div_eq_inv_mul]]
    exact Submodule.smul_mem _ _ (blockScore_mem_polySpace β d p)
  · exact (blockRepresenter_contrast_energy β d p D hD hβ hd).1

/-- Both finite-dimensional programs attain their stated exact values. -/
lemma blockPrograms_exact
    (β d : ℕ) (p : ℝ) (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp0' : 0 < p) (hp1' : p < 1) :
    perturbProg β d p hp0 hp1 = (blockEnergy β p d)⁻¹ ∧
      weightProg β d p hp0 hp1 = blockEnergy β p d := by
  let D := blockDesign d p hp0 hp1
  have hD : IsProductBernoulli D p := by
    exact ⟨hp0', hp1', ⟨fun _ => hp0, fun _ => hp1, rfl⟩⟩
  have hrepFeas : PerturbFeasible β d (blockRepresenter β p d) :=
    blockRepresenter_perturbFeasible β d p D hD hβ hd
  constructor
  · apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        rintro q ⟨h, _hh, rfl⟩
        exact D.E_nonneg (fun z => sq_nonneg (h z))
      · refine ⟨blockRepresenter β p d, hrepFeas, ?_⟩
        exact (blockRepresenter_contrast_energy β d p D hD hβ hd).2.symm
    · apply le_csInf
      · refine ⟨D.E (fun z => blockRepresenter β p d z ^ 2), ?_⟩
        exact ⟨blockRepresenter β p d, hrepFeas, rfl⟩
      intro q hq
      rcases hq with ⟨h, hh, rfl⟩
      exact (perturbFeasible_energy_unique β d p D hD hβ hd h hh).1
  · apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        rintro q ⟨w, _hw, rfl⟩
        exact D.E_nonneg (fun z => sq_nonneg (w z))
      · refine ⟨blockScore β p d, ?_, ?_⟩
        · exact blockScore_weightFeasibleAt β d p D hD
        · exact (blockScore_sq_expectation β d p D hD).symm
    · apply le_csInf
      · refine ⟨D.E (fun z => blockScore β p d z ^ 2), ?_⟩
        exact ⟨blockScore β p d, blockScore_weightFeasibleAt β d p D hD, rfl⟩
      intro q hq
      rcases hq with ⟨w, hw, rfl⟩
      exact (weightFeasibleAt_energy_unique β d p D hD w hw).1

/-- The full block representer result, including both optimization programs
and constants uniform in block size. -/
-- @node: lem:block-energy-representer
lemma blockEnergy_representer :
    ∀ (β : ℕ) (p : ℝ), 1 ≤ β → 0 < p → p < 1 →
      ∃ c₁ c₂ H : ℝ,
        0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < H ∧
        ∀ (d : ℕ), 1 ≤ d →
          c₁ * (Nat.choose d (kStar d β p) : ℝ) ≤ blockEnergy β p d ∧
          blockEnergy β p d ≤ c₂ * (Nat.choose d (kStar d β p) : ℝ) ∧
          (∀ (D : FiniteDesign (Fin d → Bool)), IsProductBernoulli D p →
            (∀ f : (Fin d → Bool) → ℝ, f ∈ polySpace β d →
              D.E (fun z => blockScore β p d z * f z) =
                contrastFunctional f) ∧
            contrastFunctional (blockRepresenter β p d) = 1 ∧
            D.E (fun z => blockRepresenter β p d z ^ 2) =
              (blockEnergy β p d)⁻¹ ∧
            PerturbFeasible β d (blockRepresenter β p d) ∧
            (∀ h : (Fin d → Bool) → ℝ, PerturbFeasible β d h →
              (blockEnergy β p d)⁻¹ ≤ D.E (fun z => h z ^ 2) ∧
                (D.E (fun z => h z ^ 2) = (blockEnergy β p d)⁻¹ ↔
                  h = blockRepresenter β p d)) ∧
            (∀ w : (Fin d → Bool) → ℝ, WeightFeasibleAt D β w →
              blockEnergy β p d ≤ D.E (fun z => w z ^ 2) ∧
                (D.E (fun z => w z ^ 2) = blockEnergy β p d ↔
                  w = blockScore β p d))) ∧
          (∀ (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
            perturbProg β d p hp0 hp1 = (blockEnergy β p d)⁻¹ ∧
            weightProg β d p hp0 hp1 = blockEnergy β p d) ∧
          (∑ T ∈ Finset.univ.powerset, |blockRawCoef β p d T|) ≤ H := by
  intro β p hβ hp0 hp1
  let c₁ := blockLowerConst β p
  let c₂ := blockUpperConst β p
  let H := blockRawMassConst β p
  have hc₁ : 0 < c₁ := (blockLowerConst_spec β p hβ hp0 hp1).1
  have hcomp1 := blockEnergy_uniform_compare β 1 p hβ (by omega) hp0 hp1
  have hK : 0 < (Nat.choose 1 (kStar 1 β p) : ℝ) := by
    have hk := kStar_mem_exposedOrder β 1 p hβ (by omega)
    have hkle : kStar 1 β p ≤ 1 :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2.trans
        (min_le_right β 1)
    exact_mod_cast Nat.choose_pos hkle
  have hc₁c₂ : c₁ ≤ c₂ := by
    dsimp [c₁, c₂] at hcomp1 ⊢
    nlinarith
  have hH : 0 < H := by
    dsimp [H, blockRawMassConst, c₁]
    have hsum : 0 ≤
        (((2 ^ β : ℕ) : ℝ) *
          ∑ r ∈ Finset.Icc 1 β, rawMassCoeff p r) /
            blockLowerConst β p := by
      apply div_nonneg
      · apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro r hr
        simp only [rawMassCoeff]
        exact mul_nonneg
          (div_nonneg (abs_nonneg _)
            (pow_nonneg
              (mul_nonneg (le_of_lt hp0) (le_of_lt (sub_pos.mpr hp1))) r))
          (pow_nonneg (by linarith) r)
      · exact le_of_lt ((blockLowerConst_spec β p hβ hp0 hp1).1)
    linarith
  refine ⟨c₁, c₂, H, hc₁, hc₁c₂, hH, ?_⟩
  intro d hd
  have hcomp := blockEnergy_uniform_compare β d p hβ hd hp0 hp1
  refine ⟨hcomp.1, hcomp.2, ?_, ?_, ?_⟩
  · intro D hD
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f hf
      exact blockScore_represents β d p D hD f hf
    · exact (blockRepresenter_contrast_energy β d p D hD hβ hd).1
    · exact (blockRepresenter_contrast_energy β d p D hD hβ hd).2
    · exact blockRepresenter_perturbFeasible β d p D hD hβ hd
    · intro h hh
      exact perturbFeasible_energy_unique β d p D hD hβ hd h hh
    · intro w hw
      exact weightFeasibleAt_energy_unique β d p D hD w hw
  · intro hp0' hp1'
    exact blockPrograms_exact β d p hβ hd hp0' hp1' hp0 hp1
  · exact blockRawCoef_mass_uniform β d p hβ hd hp0 hp1
-- @realizes H_{\beta,p}(uniform positive raw-coefficient-mass bound)
-- @realizes c_{\beta,p}(positive lower comparison constant)
-- @realizes C_{\beta,p}(finite upper comparison constant)

/-- The single-unit coin-flip design is unchanged when its treatment probability is replaced
by an equal probability and the associated probability bounds are transported accordingly. -/
add_decl_doc coinDesign.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
