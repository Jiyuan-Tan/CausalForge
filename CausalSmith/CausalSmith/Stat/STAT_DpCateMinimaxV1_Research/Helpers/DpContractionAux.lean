import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat
open scoped BigOperators ENNReal

/-- A nonempty `[0,1]`-valued family with pairwise oscillation at most `b` lies
in an interval of width `b`. -/
-- @node: pairwise_range_of_abs_sub_le
lemma pairwise_range_of_abs_sub_le {Ω : Type*} [Nonempty Ω] (f : Ω → ℝ) (b : ℝ)
    (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hosc : ∀ x y, |f x - f y| ≤ b) :
    let a := sInf (Set.range f)
    0 ≤ b ∧ ∀ x, f x ∈ Set.Icc a (a + b) := by
  let a := sInf (Set.range f)
  have hrange_ne : (Set.range f).Nonempty := Set.range_nonempty f
  have hrange_bdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (h01 x).1
  have hb : 0 ≤ b := by
    let x : Ω := Classical.choice inferInstance
    simpa using hosc x x
  refine ⟨hb, fun x => ?_⟩
  constructor
  · exact csInf_le hrange_bdd ⟨x, rfl⟩
  · have hx : f x - b ≤ a := by
      apply le_csInf hrange_ne
      rintro _ ⟨y, rfl⟩
      have hxy := (abs_le.mp (hosc x y)).2
      linarith
    linarith

/-- Replacing one factor of a finite product changes the expectation of a
bounded-difference function by at most one-factor TV times its oscillation. -/
-- @node: pi_integral_one_coordinate_tv_bound
lemma pi_integral_one_coordinate_tv_bound {Ω : Type*} [MeasurableSpace Ω] [Nonempty Ω]
    {n : ℕ} (ρ σ : Fin (n + 1) → Measure Ω)
    (hρprob : ∀ i, IsProbabilityMeasure (ρ i))
    (hσprob : ∀ i, IsProbabilityMeasure (σ i))
    (i : Fin (n + 1)) (heq : ∀ j, j ≠ i → ρ j = σ j)
    (f : (Fin (n + 1) → Ω) → ℝ) (hf : Measurable f)
    (h01 : ∀ s, f s ∈ Set.Icc (0 : ℝ) 1) (b : ℝ)
    (hosc : ∀ D D' : Fin (n + 1) → Ω,
      (∃ k, ∀ j, j ≠ k → D j = D' j) → |f D - f D'| ≤ b) :
    |(∫ s, f s ∂Measure.pi ρ) - ∫ s, f s ∂Measure.pi σ|
      ≤ tvDist (ρ i) (σ i) * b := by
  letI : ∀ j, IsProbabilityMeasure (ρ j) := hρprob
  letI : ∀ j, IsProbabilityMeasure (σ j) := hσprob
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) i
  let τ : Measure (Fin n → Ω) := Measure.pi fun j => ρ (i.succAbove j)
  have htail : (Measure.pi fun j => σ (i.succAbove j)) = τ := by
    congr 1
    funext j
    exact (heq (i.succAbove j) (Fin.succAbove_ne i j)).symm
  have hρ :
      ∫ s, f s ∂Measure.pi ρ = ∫ z, f (e.symm z) ∂((ρ i).prod τ) := by
    have h := (measurePreserving_piFinSuccAbove ρ i).integral_comp'
      (fun z => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Ω) i).symm z))
    calc
      ∫ s, f s ∂Measure.pi ρ = ∫ s, f (e.symm (e s)) ∂Measure.pi ρ := by
        congr 1
        funext s
        rw [e.symm_apply_apply]
      _ = ∫ z, f (e.symm z) ∂((ρ i).prod τ) := by simpa [e, τ] using h
  have hσ :
      ∫ s, f s ∂Measure.pi σ = ∫ z, f (e.symm z) ∂((σ i).prod τ) := by
    have h := (measurePreserving_piFinSuccAbove σ i).integral_comp'
      (fun z => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Ω) i).symm z))
    rw [htail] at h
    calc
      ∫ s, f s ∂Measure.pi σ = ∫ s, f (e.symm (e s)) ∂Measure.pi σ := by
        congr 1
        funext s
        rw [e.symm_apply_apply]
      _ = ∫ z, f (e.symm z) ∂((σ i).prod τ) := by simpa [e] using h
  let F : Ω × (Fin n → Ω) → ℝ := fun z => f (e.symm z)
  have hF : Measurable F := hf.comp e.symm.measurable
  have hFint (m : Measure (Ω × (Fin n → Ω))) [IsProbabilityMeasure m] :
      Integrable F m :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact abs_le.2 ⟨by linarith [(h01 (e.symm z)).1],
          by linarith [(h01 (e.symm z)).2]⟩)
  rw [hρ, hσ, integral_prod_symm F (hFint _), integral_prod_symm F (hFint _),
    ← integral_sub (hFint ((ρ i).prod τ)).integral_prod_right
      (hFint ((σ i).prod τ)).integral_prod_right]
  have hpoint : ∀ y : Fin n → Ω,
      ‖(∫ x, F (x, y) ∂ρ i) - ∫ x, F (x, y) ∂σ i‖
        ≤ tvDist (ρ i) (σ i) * b := by
    intro y
    let fy : Ω → ℝ := fun x => F (x, y)
    have hneighbor (x x' : Ω) :
        ∃ k : Fin (n + 1), ∀ j, j ≠ k →
          e.symm (x, y) j = e.symm (x', y) j := by
      refine ⟨i, fun j hj => ?_⟩
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
      · exact (hj rfl).elim
      · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    obtain ⟨hb, hr⟩ := pairwise_range_of_abs_sub_le fy b
      (fun x => h01 (e.symm (x, y)))
      (fun x x' => hosc _ _ (hneighbor x x'))
    rw [Real.norm_eq_abs]
    exact tvDist_integral_range (ρ i) (σ i) fy
      (hF.comp measurable_prodMk_right) (sInf (Set.range fy)) b hb hr
  calc
    |∫ y, ((∫ x, F (x, y) ∂ρ i) - ∫ x, F (x, y) ∂σ i) ∂τ|
        = ‖∫ y, ((∫ x, F (x, y) ∂ρ i) - ∫ x, F (x, y) ∂σ i) ∂τ‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ (tvDist (ρ i) (σ i) * b) * τ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpoint)
    _ = tvDist (ρ i) (σ i) * b := by simp

/-- Telescoping the one-coordinate estimate over all coordinates gives the
finite-product hybrid bound. -/
-- @node: pi_integral_hybrid_tv_bound
lemma pi_integral_hybrid_tv_bound {Ω : Type*} [MeasurableSpace Ω] [Nonempty Ω]
    {n : ℕ} (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : (Fin n → Ω) → ℝ) (hf : Measurable f)
    (h01 : ∀ s, f s ∈ Set.Icc (0 : ℝ) 1) (b : ℝ)
    (hosc : ∀ D D' : Fin n → Ω,
      (∃ k, ∀ j, j ≠ k → D j = D' j) → |f D - f D'| ≤ b) :
    |(∫ s, f s ∂Measure.pi fun _ : Fin n => μ) -
      ∫ s, f s ∂Measure.pi fun _ : Fin n => ν|
      ≤ (n : ℝ) * tvDist μ ν * b := by
  cases n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, abs_nonpos_iff]
      let z : Fin 0 → Ω := fun i => isEmptyElim i
      have hpi : (Measure.pi fun _ : Fin 0 => μ) = Measure.pi fun _ : Fin 0 => ν := by
        rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) z,
          Measure.pi_of_empty (fun _ : Fin 0 => ν) z]
      rw [hpi]
      simp
  | succ k =>
      let ρ : ℕ → Fin (k + 1) → Measure Ω :=
        fun m j => if (j : ℕ) < m then ν else μ
      let F : ℕ → ℝ := fun m => ∫ s, f s ∂Measure.pi (ρ m)
      have hstep (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
          |F i - F (i + 1)| ≤ tvDist μ ν * b := by
        have hi' : i < k + 1 := Finset.mem_range.mp hi
        let ii : Fin (k + 1) := ⟨i, hi'⟩
        have heq : ∀ j, j ≠ ii → ρ i j = ρ (i + 1) j := by
          intro j hj
          dsimp [ρ]
          split_ifs with h1 h2
          · rfl
          · omega
          · have : (j : ℕ) = i := by omega
            exact (hj (Fin.ext this)).elim
          · rfl
        have hcoord0 : ρ i ii = μ := by simp [ρ, ii]
        have hcoord1 : ρ (i + 1) ii = ν := by simp [ρ, ii]
        have hp (m : ℕ) (j : Fin (k + 1)) : IsProbabilityMeasure (ρ m j) := by
          dsimp [ρ]
          split <;> infer_instance
        simpa [F, hcoord0, hcoord1] using
          pi_integral_one_coordinate_tv_bound (ρ i) (ρ (i + 1))
            (hp i) (hp (i + 1)) ii heq f hf h01 b hosc
      have htel :
          F 0 - F (k + 1) =
            ∑ i ∈ Finset.range (k + 1), (F i - F (i + 1)) := by
        exact (Finset.sum_range_sub' F (k + 1)).symm
      have hend0 :
          F 0 = ∫ s, f s ∂Measure.pi fun _ : Fin (k + 1) => μ := by
        simp [F, ρ]
      have hrho : ρ (k + 1) = fun _ : Fin (k + 1) => ν := by
        funext j
        simp [ρ, j.isLt]
      have hend1 :
          F (k + 1) = ∫ s, f s ∂Measure.pi fun _ : Fin (k + 1) => ν := by
        simp [F, hrho]
      rw [← hend0, ← hend1, htel]
      calc
        |∑ i ∈ Finset.range (k + 1), (F i - F (i + 1))|
            ≤ ∑ i ∈ Finset.range (k + 1), |F i - F (i + 1)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.range (k + 1), tvDist μ ν * b :=
          Finset.sum_le_sum fun i hi => hstep i hi
        _ = ((k + 1 : ℕ) : ℝ) * tvDist μ ν * b := by simp [mul_assoc]

/-- A measurable probability kernel's bind evaluates an event by integrating its
fibre probabilities. -/
-- @node: measureReal_bind_eq_integral
lemma measureReal_bind_eq_integral {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Measure β) (hK : Measurable K)
    (hprob : ∀ x, IsProbabilityMeasure (K x))
    (B : Set β) (hB : MeasurableSet B) :
    (μ.bind K).real B = ∫ x, (K x).real B ∂μ := by
  letI : ∀ x, IsProbabilityMeasure (K x) := hprob
  letI : IsProbabilityMeasure (μ.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (Filter.Eventually.of_forall hprob)
  let f : β → ℝ := B.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hB
  have hfint : Integrable f (μ.bind K) :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by
        simp only [f, Set.indicator]
        split <;> simp)
  calc
    (μ.bind K).real B = ∫ z in B, (1 : ℝ) ∂(μ.bind K) := by simp
    _ = ∫ z, f z ∂(μ.bind K) := by rw [integral_indicator hB]
    _ = ∫ x, ∫ z, f z ∂K x ∂μ :=
      Causalean.Mathlib.MeasureTheory.integral_bind hK hfint
    _ = ∫ x, (K x).real B ∂μ := by
      congr 1
      funext x
      rw [show f = B.indicator (fun _ => (1 : ℝ)) from rfl, integral_indicator hB]
      simp

end CausalSmith.Stat.DpCateMinimax
