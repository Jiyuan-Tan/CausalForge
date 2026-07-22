import Causalean.Stat.MEstimation.FinitePoissonConsistency
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FiniteCollapse
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWL
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-! Continuity of the effect-dependent mean-weighted FWL residual. -/

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

open scoped BigOperators
open Causalean.Panel.Weighted
open Causalean.Panel.Weighted.WeightedSupport
open Causalean.Stat

/-- The collapsed population parameter varies continuously with the full
finite effect array. -/
lemma collapsedPopulationProjection_continuousAt_effects
    (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (hRank : CollapsedDesignRank T C pi) (delta₀ : Cell T → ℝ) :
    ContinuousAt
      (fun delta : Cell T → ℝ =>
        collapsedPopulationProjection T C pi barB gamma delta)
      delta₀ := by
  let q : SupportedCell T C → ℝ := fun z => limitingCellMass T pi z.1.1
  let m : (Cell T → ℝ) → SupportedCell T C → ℝ := fun delta z =>
    observedCohortMean T barB gamma delta z.1.1 z.2
  let A := collapsedDesignMap T C
  letI : Nonempty (SupportedCell T C) :=
    ⟨(⟨hC.choose, hC.choose_spec⟩, ⟨0, hT⟩)⟩
  have hq : ∀ z, 0 < q z := by
    intro z
    exact div_pos (pi z.1.1).property.1 (by exact_mod_cast hT)
  have hm : ∀ z, 0 < m delta₀ z := by
    intro z
    exact mul_pos (mul_pos (barB z.1.1).property (Real.exp_pos _)) (Real.exp_pos _)
  have hmcont : Continuous (m : (Cell T → ℝ) → SupportedCell T C → ℝ) := by
    dsimp [m, observedCohortMean, untreatedMean]
    fun_prop
  have hsel := finitePoissonObjective_argmax_continuousAt_mean
    q A (m delta₀) hq hm (collapsedDesignMap_injective T C pi hRank)
  have hcomp := hsel.comp hmcont.continuousAt
  have heq :
      (fun delta : Cell T → ℝ =>
        maximizerOrZero (finitePoissonObjective q (m delta) A)) =
      (fun delta : Cell T → ℝ =>
        collapsedPopulationProjection T C pi barB gamma delta) := by
    funext delta
    unfold collapsedPopulationProjection
    apply congrArg maximizerOrZero
    funext theta
    exact (limitingCriterion_eq_finitePoissonObjective
      T C pi barB gamma delta theta).symm
  rw [← heq]
  simpa only [Function.comp_apply] using hcomp

/-- Every fitted supported-cell mean varies continuously with the full effect
array. -/
lemma fittedMean_continuousAt_effects
    (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (hRank : CollapsedDesignRank T C pi) (delta₀ : Cell T → ℝ)
    (g : Cohort T) (t : Fin T) :
    ContinuousAt
      (fun delta : Cell T → ℝ => fittedMean T C pi barB gamma delta g t)
      delta₀ := by
  unfold fittedMean
  have htheta := collapsedPopulationProjection_continuousAt_effects
    T C hT hC pi barB gamma hRank delta₀
  have hindex : Continuous
      (fun theta : CollapsedParameter T C =>
        collapsedIndex T C (collapsedRegressor T C g t) theta) := by
    unfold collapsedIndex
    fun_prop
  exact Real.continuous_exp.continuousAt.comp (hindex.continuousAt.comp htheta)

/-- Raw-weight nuisance Gram matrix for the fixed collapsed nuisance basis. -/
noncomputable def meanFWLNuisanceGram (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    Matrix (CollapsedNuisanceIndex T C) (CollapsedNuisanceIndex T C) ℝ :=
  fun j k => ∑ z : SupportedCell T C,
    meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
      collapsedNuisanceRegressor T C z.1.1 z.2 j *
      collapsedNuisanceRegressor T C z.1.1 z.2 k

/-- Raw-weight nuisance normal-equation right-hand side. -/
noncomputable def meanFWLNuisanceRhs (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    CollapsedNuisanceIndex T C → ℝ :=
  fun j => ∑ z : SupportedCell T C,
    meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
      collapsedNuisanceRegressor T C z.1.1 z.2 j *
      treatmentIndicator T z.1.1 z.2

/-- Continuous finite-basis coefficient formula for the nuisance projection. -/
noncomputable def continuousNuisanceCoefficient (T : ℕ)
    (C : Finset (Cohort T)) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (delta : Cell T → ℝ) : CollapsedNuisanceIndex T C → ℝ :=
  (meanFWLNuisanceGram T C pi barB gamma delta)⁻¹.mulVec
    (meanFWLNuisanceRhs T C pi barB gamma delta)

lemma meanFWLNuisanceGram_quadratic (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (rho : CollapsedNuisanceIndex T C → ℝ) :
    dotProduct rho
      ((meanFWLNuisanceGram T C pi barB gamma delta).mulVec rho) =
      ∑ z : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
          (∑ j, collapsedNuisanceRegressor T C z.1.1 z.2 j * rho j) ^ 2 := by
  classical
  simp only [dotProduct, Matrix.mulVec, meanFWLNuisanceGram]
  calc
    _ = ∑ j, ∑ k, ∑ z : SupportedCell T C,
        rho j * (meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
          collapsedNuisanceRegressor T C z.1.1 z.2 j *
          collapsedNuisanceRegressor T C z.1.1 z.2 k * rho k) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ z : SupportedCell T C, ∑ k,
        rho j * (meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
          collapsedNuisanceRegressor T C z.1.1 z.2 j *
          collapsedNuisanceRegressor T C z.1.1 z.2 k * rho k) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ z : SupportedCell T C, ∑ j, ∑ k,
        rho j * (meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
          collapsedNuisanceRegressor T C z.1.1 z.2 j *
          collapsedNuisanceRegressor T C z.1.1 z.2 k * rho k) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [pow_two, Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Positive fitted means and collapsed full rank make the fixed nuisance
Gram matrix nonsingular at every effect array. -/
lemma meanFWLNuisanceGram_isUnit (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (delta : Cell T → ℝ) (hRank : CollapsedDesignRank T C pi) :
    IsUnit (meanFWLNuisanceGram T C pi barB gamma delta).det := by
  classical
  rw [← Matrix.isUnit_iff_isUnit_det]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro rho sigma heq
  let v : CollapsedNuisanceIndex T C → ℝ := rho - sigma
  have hzero : (meanFWLNuisanceGram T C pi barB gamma delta).mulVec v = 0 := by
    dsimp [v]
    rw [Matrix.mulVec_sub, heq, sub_self]
  have hquad : ∑ z : SupportedCell T C,
      meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
        (∑ j, collapsedNuisanceRegressor T C z.1.1 z.2 j * v j) ^ 2 = 0 := by
    rw [← meanFWLNuisanceGram_quadratic]
    rw [hzero]
    simp
  have hx (z : SupportedCell T C) :
      (∑ j, collapsedNuisanceRegressor T C z.1.1 z.2 j * v j) = 0 := by
    let f : SupportedCell T C → ℝ := fun y =>
      meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
        (∑ j, collapsedNuisanceRegressor T C y.1.1 y.2 j * v j) ^ 2
    have hnonneg (y : SupportedCell T C) : 0 ≤ f y := by
      exact mul_nonneg
        (mul_pos (div_pos (pi y.1.1).property.1 (by exact_mod_cast hT))
          (Real.exp_pos _)).le
        (sq_nonneg _)
    have hterm : f z ≤ ∑ y, f y :=
      Finset.single_le_sum (fun y _ => hnonneg y) (Finset.mem_univ z)
    have hsum : ∑ y, f y = 0 := by simpa [f] using hquad
    have hfzero : f z = 0 := le_antisymm (by simpa [hsum] using hterm) (hnonneg z)
    have hw : meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) ≠ 0 := by
      exact ne_of_gt (mul_pos
        (div_pos (pi z.1.1).property.1 (by exact_mod_cast hT)) (Real.exp_pos _))
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hfzero).resolve_left hw)
  have hv : v = 0 := by
    by_contra hv0
    let a : CollapsedParameter T C := (v, 0)
    have ha : a ≠ 0 := by
      intro ha0
      apply hv0
      exact congrArg Prod.fst ha0
    have hr := hRank a ha
    have hrzero :
        (∑ g ∈ C, ∑ t : Fin T,
          limitingCellMass T pi g *
            (collapsedIndex T C (collapsedRegressor T C g t) a) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      apply Finset.sum_eq_zero
      intro t ht
      have hz := hx (⟨g, hg⟩, t)
      change limitingCellMass T pi g *
        ((∑ j, collapsedNuisanceRegressor T C g t j * v j) +
          treatmentIndicator T g t * 0) ^ 2 = 0
      rw [hz]
      ring
    rw [hrzero] at hr
    exact (lt_irrefl 0) hr
  exact sub_eq_zero.mp hv

/-- The chosen semidefinite projection agrees on the full supported table
with the nonsingular finite Gram formula. -/
lemma weightedFWLResidual_eq_continuousNuisanceCoefficient
    (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (delta : Cell T → ℝ) (hRank : CollapsedDesignRank T C pi)
    (z : SupportedCell T C) :
    weightedFWLResidual T C hT hC pi barB gamma delta z =
      treatmentIndicator T z.1.1 z.2 -
        ∑ j, collapsedNuisanceRegressor T C z.1.1 z.2 j *
          continuousNuisanceCoefficient T C pi barB gamma delta j := by
  classical
  letI : Nonempty (SupportedCell T C) :=
    ⟨(⟨hC.choose, hC.choose_spec⟩, ⟨0, hT⟩)⟩
  let G := meanFWLNuisanceGram T C pi barB gamma delta
  let r := meanFWLNuisanceRhs T C pi barB gamma delta
  let rho := continuousNuisanceCoefficient T C pi barB gamma delta
  let c := meanWeightedSupport T C hT hC pi barB gamma delta
  let H := collapsedNuisanceSubspace T C
  let D : SupportedCell T C → ℝ := fun y => treatmentIndicator T y.1.1 y.2
  let P : SupportedCell T C → ℝ := fun y =>
    ∑ j, collapsedNuisanceRegressor T C y.1.1 y.2 j * rho j
  have hsolve : G.mulVec rho = r := by
    dsimp [rho, continuousNuisanceCoefficient]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (meanFWLNuisanceGram_isUnit T C hT pi barB gamma delta hRank),
      Matrix.one_mulVec]
  have hnormal (j : CollapsedNuisanceIndex T C) :
      ∑ y : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
          collapsedNuisanceRegressor T C y.1.1 y.2 j * (D y - P y) = 0 := by
    have hj := congrFun hsolve j
    have hlhs : G.mulVec rho j = ∑ y : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
          collapsedNuisanceRegressor T C y.1.1 y.2 j * P y := by
      dsimp [G, P]
      simp only [Matrix.mulVec, meanFWLNuisanceGram]
      calc
        _ = ∑ k, ∑ y : SupportedCell T C,
            meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
              collapsedNuisanceRegressor T C y.1.1 y.2 j *
              collapsedNuisanceRegressor T C y.1.1 y.2 k * rho k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_mul]
        _ = ∑ y : SupportedCell T C, ∑ k,
            meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
              collapsedNuisanceRegressor T C y.1.1 y.2 j *
              collapsedNuisanceRegressor T C y.1.1 y.2 k * rho k := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    have hrhs : r j = ∑ y : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
          collapsedNuisanceRegressor T C y.1.1 y.2 j * D y := by
      rfl
    rw [hlhs, hrhs] at hj
    calc
      _ = (∑ y : SupportedCell T C,
            meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
              collapsedNuisanceRegressor T C y.1.1 y.2 j * D y) -
          (∑ y : SupportedCell T C,
            meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
              collapsedNuisanceRegressor T C y.1.1 y.2 j * P y) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = 0 := sub_eq_zero.mpr hj.symm
  have hP : P ∈ H := by
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
    refine ⟨rho, ?_⟩
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [P, H, collapsedNuisanceSubspace]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have horth : ∀ h ∈ H, c.ip (D - P) h = 0 := by
    intro h hh
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
    · rintro x ⟨j, rfl⟩
      let Z : ℝ := ∑ y : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (y.1.1, y.2)
      have hZ : Z ≠ 0 := by
        exact ne_of_gt (Finset.sum_pos
          (fun y _ => mul_pos
            (div_pos (pi y.1.1).property.1 (by exact_mod_cast hT)) (Real.exp_pos _))
          Finset.univ_nonempty)
      simp [c, meanWeightedSupport, normalizedPositiveSupport,
        Causalean.Panel.Weighted.WeightedSupport.ip, Pi.sub_apply, Z]
      calc
        _ = (∑ y : SupportedCell T C,
            meanFWLWeight T C pi barB gamma delta (y.1.1, y.2) *
              collapsedNuisanceRegressor T C y.1.1 y.2 j * (D y - P y)) / Z := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = 0 := by rw [hnormal j, zero_div]
    · simp [Causalean.Panel.Weighted.WeightedSupport.ip]
    · intro x y _ _ hx hy
      rw [c.ip_add_right, hx, hy, add_zero]
    · intro s x _ hx
      rw [c.ip_smul_right, hx, mul_zero]
  have hproj : c.proj H D z = P z :=
    c.proj_apply_eq_of_mem_orthogonal H D hP horth z
      (by simp [c, meanWeightedSupport, normalizedPositiveSupport])
  rw [weightedFWLResidual]
  change D z - c.proj H D z = _
  rw [hproj]

-- @node: weightedFWLResidual_continuousAt_effects
/-- Under collapsed full rank, the fitted-mean-weighted treatment residual at
each supported cell is continuous under simultaneous perturbation of the
entire finite effect vector. -/
lemma weightedFWLResidual_continuousAt_effects
    (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (hRank : CollapsedDesignRank T C pi)
    (delta₀ : Cell T → ℝ) (z : SupportedCell T C) :
    ContinuousAt
      (fun delta : Cell T → ℝ =>
        weightedFWLResidual T C hT hC pi barB gamma delta z)
      delta₀ := by
  classical
  let G := fun delta : Cell T → ℝ =>
    meanFWLNuisanceGram T C pi barB gamma delta
  let r := fun delta : Cell T → ℝ =>
    meanFWLNuisanceRhs T C pi barB gamma delta
  have hw (y : SupportedCell T C) : ContinuousAt
      (fun delta : Cell T → ℝ =>
        meanFWLWeight T C pi barB gamma delta (y.1.1, y.2)) delta₀ := by
    unfold meanFWLWeight
    exact continuousAt_const.mul (fittedMean_continuousAt_effects
      T C hT hC pi barB gamma hRank delta₀ y.1.1 y.2)
  have hG : ContinuousAt G delta₀ := by
    apply continuousAt_pi.mpr
    intro j
    apply continuousAt_pi.mpr
    intro k
    exact tendsto_finset_sum Finset.univ fun y hy =>
      ((hw y).mul continuousAt_const).mul continuousAt_const
  have hr : ContinuousAt r delta₀ := by
    apply continuousAt_pi.mpr
    intro j
    exact tendsto_finset_sum Finset.univ fun y hy =>
      ((hw y).mul continuousAt_const).mul continuousAt_const
  have hdet : (G delta₀).det ≠ 0 :=
    (meanFWLNuisanceGram_isUnit T C hT pi barB gamma delta₀ hRank).ne_zero
  have hringInv : ContinuousAt Ring.inverse (G delta₀).det := by
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := by
      funext x
      exact Ring.inverse_eq_inv x
    rw [heq]
    exact continuousAt_inv₀ hdet
  have hinv : ContinuousAt (fun delta => (G delta)⁻¹) delta₀ :=
    (continuousAt_matrix_inv (G delta₀) hringInv).comp hG
  have hcoeff : ContinuousAt
      (fun delta => continuousNuisanceCoefficient T C pi barB gamma delta)
      delta₀ := by
    apply continuousAt_pi.mpr
    intro j
    unfold continuousNuisanceCoefficient
    simp only [Matrix.mulVec]
    exact tendsto_finset_sum Finset.univ fun k hk =>
      ((continuous_apply k).continuousAt.comp
        ((continuous_apply j).continuousAt.comp hinv)).mul
        ((continuous_apply k).continuousAt.comp hr)
  have hexplicit : ContinuousAt
      (fun delta : Cell T → ℝ =>
        treatmentIndicator T z.1.1 z.2 -
          ∑ j, collapsedNuisanceRegressor T C z.1.1 z.2 j *
            continuousNuisanceCoefficient T C pi barB gamma delta j)
      delta₀ := by
    apply continuousAt_const.sub
    exact tendsto_finset_sum Finset.univ fun j hj =>
      continuousAt_const.mul ((continuous_apply j).continuousAt.comp hcoeff)
  have heq :
      (fun delta : Cell T → ℝ =>
        weightedFWLResidual T C hT hC pi barB gamma delta z) =
      (fun delta : Cell T → ℝ =>
        treatmentIndicator T z.1.1 z.2 -
          ∑ j, collapsedNuisanceRegressor T C z.1.1 z.2 j *
            continuousNuisanceCoefficient T C pi barB gamma delta j) := by
    funext delta
    exact weightedFWLResidual_eq_continuousNuisanceCoefficient
      T C hT hC pi barB gamma delta hRank z
  rw [heq]
  exact hexplicit

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
