import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Endpoint
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmFuzzyReduction
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmTensorization

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open scoped ENNReal BigOperators

/-- Deterministically replace every control-arm outcome by zero. -/
def eraseControlOutcome {d : ℕ} (z : Obs d) : Obs d :=
  (z.1, z.2.1, z.2.1 && z.2.2)

lemma measurable_eraseControlOutcome {d : ℕ} :
    Measurable (@eraseControlOutcome d) := measurable_of_finite _

/-- Push an observed-data law through `eraseControlOutcome`. -/
noncomputable def eraseControlLaw {d : ℕ} (P : DiscreteLaw d) : DiscreteLaw d :=
  ⟨P.pmf.map eraseControlOutcome⟩

lemma eraseControlLaw_jointMass {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a y : Bool) :
    jointMass (eraseControlLaw P) k a y =
      if a then jointMass P k true y
      else if y then 0 else armMass P k false := by
  classical
  unfold jointMass eraseControlLaw eraseControlOutcome
  rw [PMF.map_apply, tsum_fintype]
  rcases a with _ | _ <;> rcases y with _ | _ <;>
    simp [Fintype.sum_prod_type, armMass, jointMass, PMF.apply_ne_top]
  rw [Finset.sum_add_distrib]
  simp only [Fintype.sum_ite_eq]
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]

lemma eraseControlLaw_cellMass {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    cellMass (eraseControlLaw P) k = cellMass P k := by
  simp [cellMass, eraseControlLaw_jointMass, armMass]

lemma eraseControlLaw_armMass_true {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    armMass (eraseControlLaw P) k true = armMass P k true := by
  simp [armMass, eraseControlLaw_jointMass]

lemma eraseControlLaw_propensity {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    propensity (eraseControlLaw P) k = propensity P k := by
  simp [propensity, eraseControlLaw_cellMass, eraseControlLaw_armMass_true]

lemma eraseControlLaw_outcomeMean_false {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    outcomeMean (eraseControlLaw P) false k = 0 := by
  simp [outcomeMean, armMass, eraseControlLaw_jointMass]

lemma eraseControlLaw_outcomeMean_true {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    outcomeMean (eraseControlLaw P) true k = outcomeMean P true k := by
  simp [outcomeMean, armMass, eraseControlLaw_jointMass]

lemma eraseControlLaw_treatedFunctional {d : ℕ} (P : DiscreteLaw d) :
    treatedFunctional (eraseControlLaw P) =
      ∑ k, cellMass P k * outcomeMean P true k := by
  unfold treatedFunctional
  simp_rw [eraseControlLaw_cellMass, eraseControlLaw_outcomeMean_true]

noncomputable def eraseControlLaw_controlZero
    {n d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (hclass : ExperimentClass n epsilon P (productLaw P n)) :
    ControlZeroLaw n d epsilon := by
  refine ⟨eraseControlLaw P, ?_⟩
  constructor
  · refine ⟨hclass.epsilon_pos, hclass.epsilon_le_half, rfl, ?_⟩
    intro k hk
    rw [eraseControlLaw_propensity]
    apply hclass.overlap
    rwa [eraseControlLaw_cellMass] at hk
  · exact eraseControlLaw_outcomeMean_false P

lemma obsLaw_eraseControlLaw {d : ℕ} (P : DiscreteLaw d) :
    obsLaw (eraseControlLaw P) = (obsLaw P).map eraseControlOutcome := by
  unfold obsLaw eraseControlLaw
  exact (PMF.toMeasure_map eraseControlOutcome P.pmf
    measurable_eraseControlOutcome).symm

lemma productLaw_eraseControlLaw {n d : ℕ} (P : DiscreteLaw d) :
    productLaw (eraseControlLaw P) n =
      (productLaw P n).map
        (fun sample i => eraseControlOutcome (sample i)) := by
  unfold productLaw
  rw [obsLaw_eraseControlLaw]
  exact (Measure.pi_map_pi
    (μ := fun _ : Fin n => obsLaw P)
    (f := fun _ : Fin n => eraseControlOutcome)
    (fun _ => measurable_eraseControlOutcome.aemeasurable)).symm

lemma eraseControl_endpointParametricLaw_treated
    {d : ℕ} [Nonempty (Fin d)] {g : ℝ}
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g)) :
    treatedFunctional (eraseControlLaw (endpointParametricLaw hv)) = g := by
  rw [eraseControlLaw_treatedFunctional]
  have hmean (k : Fin d) : outcomeMean (endpointParametricLaw hv) true k = g := by
    have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hdcast : (d : ℝ) ≠ 0 := by simpa using hcard
    simp [outcomeMean, armMass, endpointParametricLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gNull]
    field_simp [hcard, hdcast]
    ring
  simp_rw [hmean]
  rw [← Finset.sum_mul, cellMass_sum]
  ring

lemma eraseControl_endpointParametricPertLaw_treated
    {d : ℕ} [Nonempty (Fin d)] {g delta : ℝ}
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) :
    treatedFunctional (eraseControlLaw (endpointParametricPertLaw hv)) = g + delta := by
  rw [eraseControlLaw_treatedFunctional]
  have hmean (k : Fin d) :
      outcomeMean (endpointParametricPertLaw hv) true k = g + delta := by
    have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hdcast : (d : ℝ) ≠ 0 := by simpa using hcard
    simp [outcomeMean, armMass, endpointParametricPertLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gPert]
    field_simp [hcard, hdcast]
    ring
  simp_rw [hmean]
  rw [← Finset.sum_mul, cellMass_sum]
  ring

/-- Parametric component of the control-zero minimax lower bound. -/
theorem oneArm_parametric_lower
    {epsilon : ℝ} (he0 : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    1 / (100 * (n : ℝ)) ≤ oneArmMinimaxRisk n d epsilon := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let delta : ℝ := (2 / 5) / Real.sqrt n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdeltasq : delta ^ 2 = 4 / (25 * (n : ℝ)) := by
    dsimp [delta]
    rw [div_pow, Real.sq_sqrt hnR.le]
    ring
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin d) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdeltaU : (1 / 2 : ℝ) + delta ≤ 1 := by
    have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have hdelta : delta ≤ 2 / 5 := by
      dsimp [delta]
      exact div_le_self (by norm_num) hsqrt_one
    linarith
  let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin d) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hdelta0 hdeltaU
  let P0 : DiscreteLaw d := endpointParametricLaw hv0
  let P1 : DiscreteLaw d := endpointParametricPertLaw hv1
  have hclass0 : ExperimentClass n epsilon P0 (productLaw P0 n) := by
    refine ⟨he0, hehalf.le, rfl, ?_⟩
    intro k hk
    have h := endpointParametricLaw_overlap hv0 k hk
    constructor <;> linarith [h.1, h.2]
  have hclass1 : ExperimentClass n epsilon P1 (productLaw P1 n) := by
    refine ⟨he0, hehalf.le, rfl, ?_⟩
    intro k hk
    have h := endpointParametricPertLaw_overlap hv1 k hk
    constructor <;> linarith [h.1, h.2]
  let Q0 : ControlZeroLaw n d epsilon := eraseControlLaw_controlZero P0 hclass0
  let Q1 : ControlZeroLaw n d epsilon := eraseControlLaw_controlZero P1 hclass1
  have hreg : (n : ℝ) *
      ((1 / 2 : ℝ) * delta ^ 2 / ((1 / 2 : ℝ) * (1 - 1 / 2))) ≤ Real.log 2 := by
    rw [hdeltasq]
    have hlog : (8 / 25 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp <;> ring
  have htvP : Causalean.Stat.tvDist (productLaw P0 n) (productLaw P1 n) ≤ 1 / 2 := by
    simpa [P0, P1, endpointParametricLaw, endpointParametricPertLaw,
      productLaw, obsLaw, Causalean.Estimation.MinimaxATE.productLaw,
      Causalean.Estimation.MinimaxATE.obsLaw] using
      (Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
        hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hreg)
  have htvQ : Causalean.Stat.tvDist (productLaw Q0.1 n) (productLaw Q1.1 n) ≤ 1 / 2 := by
    rw [show Q0.1 = eraseControlLaw P0 by rfl,
      show Q1.1 = eraseControlLaw P1 by rfl,
      productLaw_eraseControlLaw, productLaw_eraseControlLaw]
    exact (tvDist_map_le (productLaw P0 n) (productLaw P1 n)
      (fun sample i => eraseControlOutcome (sample i)) (by fun_prop)).trans htvP
  have ht0 : treatedFunctional Q0.1 = 1 / 2 := by
    exact eraseControl_endpointParametricLaw_treated hv0
  have ht1 : treatedFunctional Q1.1 = 1 / 2 + delta := by
    exact eraseControl_endpointParametricPertLaw_treated hv1
  have hlow := oneArmMinimaxRisk_lower_of_finite_mixtures
    (P₀ := fun _ : Fin 1 => Q0) (P₁ := fun _ : Fin 1 => Q1)
    (w₀ := fun _ : Fin 1 => 1) (w₁ := fun _ : Fin 1 => 1)
    (theta₀ := (1 / 2 : ℝ)) (theta₁ := 1 / 2 + delta)
    (s := delta / 2) (c := (1 / 2 : ℝ))
    (by simp) (by simp) (fun _ => ht0) (fun _ => ht1)
    (by positivity) (by
      rw [show 1 / 2 - (1 / 2 + delta) = -delta by ring,
        abs_neg, abs_of_nonneg hdelta0]
      ring_nf
      exact le_refl delta)
    (by simpa [Causalean.Stat.mixture] using htvQ)
  calc
    1 / (100 * (n : ℝ)) = (delta / 2) ^ 2 * ((1 - 1 / 2) / 2) := by
      rw [div_pow, hdeltasq]
      field_simp
      ring
    _ ≤ oneArmMinimaxRisk n d epsilon := hlow

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
