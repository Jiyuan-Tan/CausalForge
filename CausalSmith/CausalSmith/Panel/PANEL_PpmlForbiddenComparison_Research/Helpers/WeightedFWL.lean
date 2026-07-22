import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Basic
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Projection
import Causalean.Panel.Weighted.FWL
import Causalean.Panel.Weighted.ScalarFWL
import Mathlib.Algebra.BigOperators.Field

/-!
# Mean-weighted FWL residuals

This file normalizes the positive weights `q_gt * mu_star_gt`, builds the
shared `WeightedSupport`, and applies its nuisance-space residual maker to the
treatment regressor.
-/

open scoped BigOperators

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

open Causalean.Panel.Weighted
open Causalean.Panel.Weighted.WeightedSupport

/-- Normalize positive weights on a nonempty finite support. -/
noncomputable def normalizedPositiveSupport {R : Type*} [Fintype R] [DecidableEq R]
    (S : Finset R) (hS : S.Nonempty) (w : R → ℝ) (hw : ∀ r ∈ S, 0 < w r) :
    WeightedSupport R where
  observed := S
  observed_nonempty := hS
  weight r := if r ∈ S then w r / ∑ s ∈ S, w s else 0
  weight_pos := by
    intro r hr
    rw [if_pos hr]
    exact div_pos (hw r hr) (Finset.sum_pos hw hS)
  weight_zero_off := by
    intro r hr
    simp [hr]
  weight_sum_one := by
    rw [Finset.sum_congr rfl (fun r hr => if_pos hr)]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt (Finset.sum_pos hw hS))

/-- The raw effect-dependent PPML projection weight. -/
noncomputable def meanFWLWeight (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) (z : Cell T) : ℝ :=
  limitingCellMass T pi z.1 * fittedMean T C pi barB gamma delta z.1 z.2

/-- The normalized support carrying weights proportional to `q_gt * mu_star_gt`. -/
noncomputable def meanWeightedSupport (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    WeightedSupport (SupportedCell T C) :=
  normalizedPositiveSupport Finset.univ
    (by exact ⟨(⟨hC.choose, hC.choose_spec⟩, ⟨0, hT⟩), Finset.mem_univ _⟩)
    (fun z => meanFWLWeight T C pi barB gamma delta (z.1.1, z.2))
    (by
      intro z hz
      have hpi : 0 < (pi z.1.1 : ℝ) := (pi z.1.1).property.1
      have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
      unfold meanFWLWeight limitingCellMass
      exact mul_pos (div_pos hpi hTr) (Real.exp_pos _))

/-- The nuisance subspace spanned by the fixed-effect columns `X_gt`. -/
noncomputable def collapsedNuisanceSubspace (T : ℕ) (C : Finset (Cohort T)) :
    Submodule ℝ (SupportedCell T C → ℝ) :=
  Submodule.span ℝ (Set.range fun j : CollapsedNuisanceIndex T C =>
    fun z => collapsedNuisanceRegressor T C z.1.1 z.2 j)

/-- The coefficient-vector WLS objective whose minimizer is `rho_star`. -/
noncomputable def nuisanceWLSObjective (T : ℕ) (C : Finset (Cohort T))
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (rho : CollapsedNuisanceIndex T C → ℝ) : ℝ :=
  ∑ g ∈ C, ∑ t : Fin T,
    meanFWLWeight T C pi barB gamma delta (g, t) *
      (treatmentIndicator T g t -
        ∑ j, collapsedNuisanceRegressor T C g t j * rho j) ^ 2

/-- The selected minimizer of the mean-weighted nuisance projection. -/
noncomputable def rhoStar (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    CollapsedNuisanceIndex T C → ℝ :=
  let c := meanWeightedSupport T C hT hC pi barB gamma delta
  let H := collapsedNuisanceSubspace T C
  let D : SupportedCell T C → ℝ := fun z => treatmentIndicator T z.1.1 z.2
  Classical.choose ((Submodule.mem_span_range_iff_exists_fun ℝ).mp (c.proj_mem H D))
  -- @realizes rho_star(delta)(argmin of the q_gt*mu_star weighted squared residual)

/-- The selected mean-weighted fixed-effects projection coefficients are unchanged when all
panel, support, and mean-model inputs are replaced by equal values. -/
add_decl_doc rhoStar.congr_simp

-- @node: def:weighted-fwl-residual
/-- The pseudo-true mean-weighted FWL treatment residual. -/
noncomputable def weightedFWLResidual (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    SupportedCell T C → ℝ :=
  let c := meanWeightedSupport T C hT hC pi barB gamma delta
  c.tildeX (collapsedNuisanceSubspace T C) (fun z => treatmentIndicator T z.1.1 z.2)
  -- @realizes Wtilde_gt(delta)(WeightedSupport.tildeX of D against the X_gt span)

/-- The mean-weighted FWL treatment residual is unchanged when the panel, support, and all
inputs governing the fitted mean are replaced by equal values. -/
add_decl_doc weightedFWLResidual.congr_simp

/-- On supported cells, the substrate residual equals the coefficient-form residual. -/
lemma weightedFWLResidual_eq_rhoStar (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
    weightedFWLResidual T C hT hC pi barB gamma delta (⟨g, hg⟩, t) =
      treatmentIndicator T g t -
        ∑ j, collapsedNuisanceRegressor T C g t j *
          rhoStar T C hT hC pi barB gamma delta j := by
  classical
  let c := meanWeightedSupport T C hT hC pi barB gamma delta
  let H := collapsedNuisanceSubspace T C
  let D : SupportedCell T C → ℝ := fun z => treatmentIndicator T z.1.1 z.2
  let z : SupportedCell T C := (⟨g, hg⟩, t)
  have hrho := Classical.choose_spec
    ((Submodule.mem_span_range_iff_exists_fun ℝ).mp (c.proj_mem H D))
  have hrho_z := congrFun hrho z
  rw [weightedFWLResidual, show meanWeightedSupport T C hT hC pi barB gamma delta = c by rfl]
  simp only [WeightedSupport.tildeX_eq, Pi.sub_apply]
  change D z - c.proj H D z = D z - _
  congr 1
  rw [← hrho_z]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold rhoStar
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

-- @node: linearizedScore_snd_eq_weightedFWL
/-- A solution of the one-cell linearized collapsed Poisson score has treatment
coordinate equal to the weighted-FWL residual contribution divided by its
weighted energy. -/
lemma linearizedScore_snd_eq_weightedFWL (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (k : Cohort T) (hk : k ∈ C) (s : Fin T)
    (v : CollapsedParameter T C)
    (henergy : 0 < ∑ z : SupportedCell T C,
      meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
        (weightedFWLResidual T C hT hC pi barB gamma delta z) ^ 2)
    (hscore : ∀ d : CollapsedParameter T C,
      ∑ z : SupportedCell T C,
        limitingCellMass T pi z.1.1 * collapsedDesignMap T C d z *
          ((if z = (⟨k, hk⟩, s) then
              untreatedMean T barB gamma k s * Real.exp (delta (k, s)) else 0) -
            fittedMean T C pi barB gamma delta z.1.1 z.2 *
              collapsedDesignMap T C v z) = 0) :
    v.2 = limitingCellMass T pi k * untreatedMean T barB gamma k s *
      Real.exp (delta (k, s)) *
        weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) /
      (∑ z : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
          (weightedFWLResidual T C hT hC pi barB gamma delta z) ^ 2) := by
  classical
  let c := meanWeightedSupport T C hT hC pi barB gamma delta
  let H := collapsedNuisanceSubspace T C
  let X : SupportedCell T C → ℝ := fun z ↦ treatmentIndicator T z.1.1 z.2
  let W := weightedFWLResidual T C hT hC pi barB gamma delta
  let source : SupportedCell T C → ℝ := fun z ↦
    if z = (⟨k, hk⟩, s) then
      untreatedMean T barB gamma k s * Real.exp (delta (k, s)) else 0
  let mu : SupportedCell T C → ℝ := fun z ↦
    fittedMean T C pi barB gamma delta z.1.1 z.2
  let Y : SupportedCell T C → ℝ := fun z ↦ source z / mu z
  let alpha : SupportedCell T C → ℝ := fun z ↦
    ∑ j, collapsedNuisanceRegressor T C z.1.1 z.2 j * v.1 j
  let Z : ℝ := ∑ z : SupportedCell T C,
    meanFWLWeight T C pi barB gamma delta (z.1.1, z.2)
  letI : Nonempty (SupportedCell T C) :=
    ⟨(⟨hC.choose, hC.choose_spec⟩, ⟨0, hT⟩)⟩
  have hZ : 0 < Z := by
    apply Finset.sum_pos
    · intro z hz
      exact mul_pos (div_pos (pi z.1.1).property.1 (by exact_mod_cast hT))
        (Real.exp_pos _)
    · exact Finset.univ_nonempty
  have halpha : alpha ∈ H := by
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
    refine ⟨v.1, ?_⟩
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [alpha, H, collapsedNuisanceSubspace]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hres (z : SupportedCell T C) :
      Y z - v.2 * X z - alpha z =
        (source z - mu z * collapsedDesignMap T C v z) / mu z := by
    dsimp [Y, X, alpha]
    have hmu : mu z ≠ 0 := by
      dsimp [mu, fittedMean]
      exact ne_of_gt (Real.exp_pos _)
    rw [show collapsedDesignMap T C v z =
      (∑ x, collapsedNuisanceRegressor T C z.1.1 z.2 x * v.1 x) +
        treatmentIndicator T z.1.1 z.2 * v.2 by rfl]
    field_simp [hmu]
    ring
  have hnormal (d : CollapsedParameter T C) :
      c.ip (Y - v.2 • X - alpha) (fun z ↦ collapsedDesignMap T C d z) = 0 := by
    have hs := hscore d
    rw [show c.ip (Y - v.2 • X - alpha) (fun z ↦ collapsedDesignMap T C d z) =
        (∑ z : SupportedCell T C,
          limitingCellMass T pi z.1.1 * collapsedDesignMap T C d z *
            (source z - mu z * collapsedDesignMap T C v z)) / Z by
      simp [c, meanWeightedSupport, normalizedPositiveSupport, meanFWLWeight,
        Causalean.Panel.Weighted.WeightedSupport.ip, hres, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, Z]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      have hmu : mu z ≠ 0 := by
        dsimp [mu, fittedMean]
        exact ne_of_gt (Real.exp_pos _)
      field_simp [hmu, ne_of_gt hZ]
      ring]
    simpa [source, mu] using congrArg (fun x : ℝ ↦ x / Z) hs
  have hnormalX : c.ip (Y - v.2 • X - alpha) X = 0 := by
    simpa [X, collapsedDesignMap, collapsedIndex, collapsedRegressor] using
      hnormal (0, 1)
  have hnormalH : ∀ h ∈ H, c.ip (Y - v.2 • X - alpha) h = 0 := by
    intro h hh
    obtain ⟨rho, hrho⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hh
    rw [← hrho]
    have hn := hnormal (rho, 0)
    rw [show (∑ i, rho i • fun z ↦ collapsedNuisanceRegressor T C z.1.1 z.2 i) =
      (fun z ↦ collapsedDesignMap T C (rho, 0) z) by
        funext z
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        change (∑ i, rho i * collapsedNuisanceRegressor T C z.1.1 z.2 i) =
          (∑ i, collapsedNuisanceRegressor T C z.1.1 z.2 i * rho i) +
            treatmentIndicator T z.1.1 z.2 * 0
        rw [mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
    exact hn
  have hpos : 0 < c.ip W W := by
    rw [show c.ip W W =
      (∑ z : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) * (W z) ^ 2) / Z by
      simp [c, meanWeightedSupport, normalizedPositiveSupport,
        Causalean.Panel.Weighted.WeightedSupport.ip, Z, pow_two]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      field_simp [ne_of_gt hZ]
      ]
    exact div_pos henergy hZ
  have hfwl := scalar_fwl_of_normalEqs c H X Y v.2 alpha halpha hpos hnormalX hnormalH
  rw [hfwl]
  have hW : c.tildeX H X = W := rfl
  rw [hW]
  rw [show c.ip W Y =
      (limitingCellMass T pi k * untreatedMean T barB gamma k s *
        Real.exp (delta (k, s)) * W (⟨k, hk⟩, s)) / Z by
    simp [c, meanWeightedSupport, normalizedPositiveSupport,
      Causalean.Panel.Weighted.WeightedSupport.ip, Y, source, mu, Z,
      meanFWLWeight, fittedMean]
    rw [Fintype.sum_eq_single (⟨k, hk⟩, s)]
    · simp
      field_simp [Real.exp_ne_zero]
    · intro z hz
      simp [hz]
    ]
  rw [show c.ip W W =
      (∑ z : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) * (W z) ^ 2) / Z by
    simp [c, meanWeightedSupport, normalizedPositiveSupport,
      Causalean.Panel.Weighted.WeightedSupport.ip, Z, pow_two]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z hz
    field_simp [ne_of_gt hZ]
    ]
  have hE : (∑ z : SupportedCell T C,
      meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) * (W z) ^ 2) ≠ 0 := by
    exact ne_of_gt (by simpa [W] using henergy)
  field_simp [ne_of_gt hZ, hE]
  ring

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
