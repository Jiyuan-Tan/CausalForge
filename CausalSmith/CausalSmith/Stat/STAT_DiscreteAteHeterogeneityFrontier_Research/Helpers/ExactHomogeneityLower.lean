import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Endpoint
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Ingster
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ExplicitWitness
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore
import Causalean.Stat.Minimax.ChiSquaredFinite
import Causalean.Stat.Minimax.Mixture

/-!
# Exact-homogeneity binary lower bound

This module discharges the fixed-sample exact-homogeneity source interface used
by the heterogeneity-frontier lower transfer.  The parametric part is obtained
from the accepted endpoint two-point experiment.  The collision part uses the
symmetric finite Rademacher mixture from Zeng--Balakrishnan--Han--Kennedy,
Theorem 4 and Appendix C.8.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set
open scoped BigOperators ENNReal

private abbrev BinLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw
private abbrev BinObs :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

-- @node: endpoint_null_exact
/-- If [the alphabet is nonempty](hyp:hd) and [the overlap constant is positive](hyp:he0) and [the
  overlap constant is below one half](hyp:he1), [the null endpoint distribution belongs to the
  exact homogeneous binary model](goal). -/
lemma endpoint_null_exact {n d : ℕ} [Nonempty (Fin d)]
    (hd : 0 < d) {epsilon : ℝ}
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    ∃ P : BinaryExactLaw n d epsilon,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1 = 0 ∧
      ∃ hv : Causalean.Estimation.MinimaxATE.ValidDGP
          (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
          (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) (1 / 2) (1 / 2)),
        P.1 = CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw hv := by
  let hv := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin d) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let P : BinLaw d :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw hv
  have hmass (k : Fin d) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k = 1 / (d : ℝ) := by
    have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [P, CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gNull]
    ring
  have hover : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P := by
    intro k hk
    have hhalf :=
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw_overlap hv k hk
    constructor <;> linarith
  have heffect (k l : Fin d) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true l -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false l := by
    have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [P, CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gNull]
  refine ⟨⟨P, hover, hmass, heffect⟩,
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw_ate hv, hv, rfl⟩

private lemma endpoint_pert_exact {n d : ℕ} [Nonempty (Fin d)]
    (hn : 0 < n) (hd : 0 < d)
    {epsilon : ℝ} (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ delta ^ 2 = 4 / (25 * (n : ℝ)) ∧
      ∃ P : BinaryExactLaw n d epsilon,
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1 = delta ∧
        ∃ hv : Causalean.Estimation.MinimaxATE.ValidDGP
            (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
            (Causalean.Estimation.MinimaxATE.Parametric.gPert
              (C := Fin d) (1 / 2) (1 / 2) delta),
          P.1 = CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw hv := by
  let delta : ℝ := (2 / 5) / Real.sqrt n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hdelta0 : 0 < delta := by dsimp [delta]; positivity
  have hdeltasq : delta ^ 2 = 4 / (25 * (n : ℝ)) := by
    dsimp [delta]
    rw [div_pow, Real.sq_sqrt hnR.le]
    ring
  have hdeltaU : (1 / 2 : ℝ) + delta ≤ 1 := by
    have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have hdelta : delta ≤ 2 / 5 := by
      dsimp [delta]
      exact div_le_self (by norm_num) hsqrt_one
    linarith
  let hv := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin d) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hdelta0.le hdeltaU
  let P : BinLaw d :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw hv
  have hmass (k : Fin d) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k = 1 / (d : ℝ) := by
    have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [P, CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gPert]
    ring
  have hover : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P := by
    intro k hk
    have hhalf :=
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw_overlap hv k hk
    constructor <;> linarith
  have heffect (k l : Fin d) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true l -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false l := by
    have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [P, CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gPert]
  refine ⟨delta, hdelta0, hdeltasq, ⟨P, hover, hmass, heffect⟩,
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw_ate hv, hv, rfl⟩

private lemma binaryExactMinimaxRisk_two_point {n d : ℕ} {epsilon delta : ℝ}
    (P0 P1 : BinaryExactLaw n d epsilon)
    (hdelta : 0 ≤ delta)
    (htau0 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1 = 0)
    (htau1 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P1.1 = delta)
    (htv : Causalean.Stat.tvDist
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n)
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1.1 n) ≤ 1 / 2) :
    delta ^ 2 / 16 ≤ binaryExactMinimaxRisk n d epsilon := by
  let est0 : {f : (Fin n → BinObs d) → ℝ // Measurable f} :=
    ⟨fun _ ↦ 0, measurable_const⟩
  letI : Nonempty {f : (Fin n → BinObs d) → ℝ // Measurable f} := ⟨est0⟩
  unfold binaryExactMinimaxRisk
  apply le_ciInf
  intro est
  have hprob := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n)
    (P₁ := CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1.1 n)
    est.2
    (θ₀ := CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1)
    (θ₁ := CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P1.1)
    (s := delta / 2) (c := (1 / 2 : ℝ))
    (by rw [htau0, htau1, zero_sub, abs_neg, abs_of_nonneg hdelta]; linarith) htv
  have hmse (P : BinaryExactLaw n d epsilon) :
      (delta / 2) ^ 2 *
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n).real
            {x | delta / 2 ≤
              |est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1|} ≤
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n) est.1
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) := by
    unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
    have hset :
        {x | delta / 2 ≤
            |est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1|} =
          {x | (delta / 2) ^ 2 ≤
            (est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [hdelta,
          abs_nonneg
            (est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1),
          sq_abs (est.1 x -
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun x ↦
        sq_nonneg (est.1 x -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1))
      MemLp.of_discrete.integrable_sq ((delta / 2) ^ 2)
  have htwo : delta ^ 2 / 16 ≤ max
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n) est.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1))
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1.1 n) est.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P1.1)) := by
    have hscale : 0 ≤ (delta / 2) ^ 2 := sq_nonneg _
    have hp := mul_le_mul_of_nonneg_left hprob hscale
    norm_num at hp
    rw [mul_max_of_nonneg _ _ hscale] at hp
    calc
      delta ^ 2 / 16 = (delta / 2) ^ 2 * (1 / 4) := by ring
      _ ≤ max
          ((delta / 2) ^ 2 *
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n).real
              {x | delta / 2 ≤
                |est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1|})
          ((delta / 2) ^ 2 *
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1.1 n).real
              {x | delta / 2 ≤
                |est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P1.1|}) := hp
      _ ≤ _ := max_le_max (hmse P0) (hmse P1)
  have hb : BddAbove (Set.range (fun P : BinaryExactLaw n d epsilon ↦
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n) est.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1))) := by
    refine ⟨((∑ sample : Fin n → BinObs d, |est.1 sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_le_estimator_abs_sum_bound
      P.1 P.2.1 est.1
  exact htwo.trans (max_le (le_ciSup hb P0) (le_ciSup hb P1))

/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1), [the
  exact-homogeneity binary source class contains the standard randomized Bernoulli two-point
  experiment, hence retains the parametric `1/n` lower term](goal). -/
lemma binaryExactMinimaxRisk_parametric_lower {n d : ℕ} {epsilon : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) :
    1 / (100 * (n : ℝ)) ≤ binaryExactMinimaxRisk n d epsilon := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨P0, htau0, hv0, hP0⟩ := endpoint_null_exact (n := n) hd he0 he1
  obtain ⟨delta, hdelta, hdeltasq, P1, htau1, hv1, hP1⟩ :=
    endpoint_pert_exact hn hd he0 he1
  have hreg : (n : ℝ) *
      ((1 / 2 : ℝ) * delta ^ 2 / ((1 / 2 : ℝ) * (1 - 1 / 2))) ≤ Real.log 2 := by
    rw [hdeltasq]
    have hlog : (8 / 25 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp <;> ring
  have htv : Causalean.Stat.tvDist
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n)
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1.1 n) ≤ 1 / 2 := by
    rw [hP0, hP1]
    simpa [CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw,
      Causalean.Estimation.MinimaxATE.productLaw,
      Causalean.Estimation.MinimaxATE.obsLaw] using
      (Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
        hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hreg)
  have h := binaryExactMinimaxRisk_two_point P0 P1 hdelta.le htau0 htau1 htv
  rw [hdeltasq] at h
  convert h using 1 <;> field_simp <;> ring

/-! ## The Appendix C.8 symmetric sign family -/

private noncomputable def exactSignPropensity {d : ℕ} (r : ℝ)
    (lam : Fin d → Bool) (k : Fin d) : ℝ :=
  1 / 2 + r * Causalean.Estimation.MinimaxATE.signOf (lam k)

private noncomputable def exactSignOutcome (q r : ℝ)
    {d : ℕ} (lam : Fin d → Bool) (a : Bool) (k : Fin d) : ℝ :=
  if a then
    1 / 2 - r * Causalean.Estimation.MinimaxATE.signOf (lam k) + q / 4
  else
    1 / 2 - r * Causalean.Estimation.MinimaxATE.signOf (lam k) - q / 4

private theorem exactSign_valid {d : ℕ} {q r : ℝ} (lam : Fin d → Bool)
    (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (hrε : r ≤ 1 / 2)
    (hrq : r + q / 4 ≤ 1 / 2) :
    Causalean.Estimation.MinimaxATE.ValidDGP
      (exactSignPropensity r lam) (exactSignOutcome q r lam) := by
  constructor
  · intro k
    rcases Causalean.Estimation.MinimaxATE.signOf_mem (lam k) with h | h <;>
      rw [exactSignPropensity, h] <;> constructor <;> nlinarith
  · intro a k
    rcases Causalean.Estimation.MinimaxATE.signOf_mem (lam k) with h | h <;>
      rw [exactSignOutcome, h] <;> cases a <;> simp only [Bool.false_eq_true,
        if_false, if_true] <;> constructor <;> nlinarith

private noncomputable def exactSignLaw {d : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (lam : Fin d → Bool) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrε : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) : BinLaw d :=
  ⟨Causalean.Estimation.MinimaxATE.obsPMF
    (exactSign_valid lam hq0 hr0 hrε hrq)⟩

private theorem exactSignLaw_jointMass {d : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (lam : Fin d → Bool) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrε : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2)
    (k : Fin d) (a y : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass
      (exactSignLaw lam hq0 hr0 hrε hrq) k a y =
      Causalean.Estimation.MinimaxATE.obsReal
        (exactSignPropensity r lam) (exactSignOutcome q r lam) (k, a, y) := by
  simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass, exactSignLaw,
    Causalean.Estimation.MinimaxATE.obsPMF,
    ENNReal.toReal_ofReal
      (Causalean.Estimation.MinimaxATE.obsReal_nonneg
        (exactSign_valid lam hq0 hr0 hrε hrq) (k, a, y))]

private theorem exactSignLaw_cellMass {d : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (lam : Fin d → Bool) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrε : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) (k : Fin d) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
      (exactSignLaw lam hq0 hr0 hrε hrq) k = 1 / (d : ℝ) := by
  have hd : (d : ℝ) ≠ 0 := by
    have hdNat : d ≠ 0 := by simpa using (Fintype.card_ne_zero (α := Fin d))
    exact_mod_cast hdNat
  simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass,
    exactSignLaw_jointMass, Causalean.Estimation.MinimaxATE.obsReal]
  ring

private theorem exactSignLaw_armMass {d : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (lam : Fin d → Bool) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrε : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) (k : Fin d) (a : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass
      (exactSignLaw lam hq0 hr0 hrε hrq) k a =
      (d : ℝ)⁻¹ * (if a then exactSignPropensity r lam k
        else 1 - exactSignPropensity r lam k) := by
  cases a <;>
    simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass,
      exactSignLaw_jointMass, Causalean.Estimation.MinimaxATE.obsReal] <;> ring

private theorem exactSignLaw_propensity {d : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (lam : Fin d → Bool) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrε : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) (k : Fin d) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity
      (exactSignLaw lam hq0 hr0 hrε hrq) k = exactSignPropensity r lam k := by
  rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity,
    exactSignLaw_armMass, exactSignLaw_cellMass]
  have hd : (d : ℝ) ≠ 0 := by
    have hdNat : d ≠ 0 := by simpa using (Fintype.card_ne_zero (α := Fin d))
    exact_mod_cast hdNat
  simp only [if_true, one_div]
  field_simp

private theorem exactSignLaw_outcomeMean {d : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (lam : Fin d → Bool) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrε : r < 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) (k : Fin d) (a : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean
      (exactSignLaw lam hq0 hr0 hrε.le hrq) a k = exactSignOutcome q r lam a k := by
  rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean,
    exactSignLaw_jointMass, exactSignLaw_armMass]
  have hd : (d : ℝ) ≠ 0 := by
    have hdNat : d ≠ 0 := by simpa using (Fintype.card_ne_zero (α := Fin d))
    exact_mod_cast hdNat
  have hm : exactSignPropensity r lam k ≠ 0 := by
    rw [exactSignPropensity]
    rcases Causalean.Estimation.MinimaxATE.signOf_mem (lam k) with h | h <;>
      rw [h] <;> nlinarith
  have hmc : 1 - exactSignPropensity r lam k ≠ 0 := by
    rw [exactSignPropensity]
    rcases Causalean.Estimation.MinimaxATE.signOf_mem (lam k) with h | h <;>
      rw [h] <;> nlinarith
  cases a <;> simp only [Bool.false_eq_true, if_false, if_true,
    Causalean.Estimation.MinimaxATE.obsReal, Fintype.card_fin] <;>
    field_simp <;> ring

private noncomputable def exactSignExactLaw {n d : ℕ} [Nonempty (Fin d)]
    {epsilon q r : ℝ} (lam : Fin d → Bool) (he0 : 0 < epsilon)
    (hrε : r ≤ 1 / 2 - epsilon) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrhalf : r < 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) :
    BinaryExactLaw n d epsilon := by
  let P := exactSignLaw lam hq0 hr0 hrhalf.le hrq
  refine ⟨P, ?_, exactSignLaw_cellMass lam hq0 hr0 hrhalf.le hrq, ?_⟩
  · intro k _
    rw [exactSignLaw_propensity]
    rcases Causalean.Estimation.MinimaxATE.signOf_mem (lam k) with h | h <;>
      rw [exactSignPropensity, h] <;> constructor <;> nlinarith
  · intro k l
    rw [exactSignLaw_outcomeMean lam hq0 hr0 hrhalf hrq,
      exactSignLaw_outcomeMean lam hq0 hr0 hrhalf hrq,
      exactSignLaw_outcomeMean lam hq0 hr0 hrhalf hrq,
      exactSignLaw_outcomeMean lam hq0 hr0 hrhalf hrq]
    simp only [exactSignOutcome, if_true, Bool.false_eq_true, if_false]
    ring

private theorem exactSignExactLaw_ate {n d : ℕ} [Nonempty (Fin d)]
    {epsilon q r : ℝ} (lam : Fin d → Bool) (he0 : 0 < epsilon)
    (hrε : r ≤ 1 / 2 - epsilon) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrhalf : r < 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional
      (exactSignExactLaw (n := n) lam he0 hrε hq0 hr0 hrhalf hrq).1 = q / 2 := by
  rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_weighted_regression _
    (exactSignExactLaw (n := n) lam he0 hrε hq0 hr0 hrhalf hrq).2.1]
  change ∑ k : Fin d, CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
      (exactSignLaw lam hq0 hr0 hrhalf.le hrq) k *
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean
          (exactSignLaw lam hq0 hr0 hrhalf.le hrq) true k -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean
          (exactSignLaw lam hq0 hr0 hrhalf.le hrq) false k) = q / 2
  simp_rw [exactSignLaw_cellMass,
    exactSignLaw_outcomeMean lam hq0 hr0 hrhalf hrq]
  simp only [exactSignOutcome, if_true, Bool.false_eq_true, if_false]
  have hd : (d : ℝ) ≠ 0 := by
    have hdNat : d ≠ 0 := by simpa using (Fintype.card_ne_zero (α := Fin d))
    exact_mod_cast hdNat
  rw [show ∑ _k : Fin d, (1 / (d : ℝ)) *
      ((1 / 2 - r * Causalean.Estimation.MinimaxATE.signOf (lam _k) + q / 4) -
       (1 / 2 - r * Causalean.Estimation.MinimaxATE.signOf (lam _k) - q / 4)) =
      ∑ _k : Fin d, (q / (2 * d : ℝ)) by
        apply Finset.sum_congr rfl
        intro k _
        field_simp [hd]
        ring]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hd]

private def exactZeroLam {d : ℕ} : Fin d → Bool := fun _ ↦ false

private noncomputable def exactNullValid {d : ℕ} :
    Causalean.Estimation.MinimaxATE.ValidDGP
      (exactSignPropensity 0 (exactZeroLam (d := d)))
      (exactSignOutcome 0 0 (exactZeroLam (d := d))) :=
  exactSign_valid _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private noncomputable def exactQfalse (d n : ℕ) [Nonempty (Fin d)] :
    Measure (Fin n → BinObs d) :=
  Causalean.Estimation.MinimaxATE.productLaw (exactNullValid (d := d)) n

private noncomputable def exactQpert {d : ℕ} (n : ℕ) [Nonempty (Fin d)]
    {q r : ℝ} (lam : Fin d → Bool) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) :
    Measure (Fin n → BinObs d) :=
  Causalean.Estimation.MinimaxATE.productLaw
    (exactSign_valid lam hq0 hr0 hrhalf hrq) n

private noncomputable def exactQtrue {d : ℕ} (n : ℕ) [Nonempty (Fin d)]
    {q r : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) :
    Measure (Fin n → BinObs d) :=
  Causalean.Stat.mixture (Causalean.Estimation.MinimaxATE.signWeight d)
    (fun lam ↦ exactQpert n lam hq0 hr0 hrhalf hrq)

private theorem exactQfalse_singleton_ne_zero {d n : ℕ} [Nonempty (Fin d)]
    (omega : Fin n → BinObs d) : exactQfalse d n {omega} ≠ 0 := by
  have hpos : 0 < (exactQfalse d n).real {omega} := by
    rw [exactQfalse, Causalean.Estimation.MinimaxATE.productLaw,
      Causalean.Stat.pi_real_singleton]
    simp_rw [Causalean.Estimation.MinimaxATE.obsLaw_real_singleton]
    apply Finset.prod_pos
    intro i _
    have hcard : (0 : ℝ) < (Fintype.card (Fin d) : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := Fin d)
    have hdR : (0 : ℝ) < d := by simpa using hcard
    simp [Causalean.Estimation.MinimaxATE.obsReal, exactSignPropensity,
      exactSignOutcome, exactZeroLam]
    rcases (omega i).2.1 with _ | _ <;> rcases (omega i).2.2 with _ | _ <;>
      simp only [Bool.false_eq_true, if_false, if_true] <;> positivity
  intro h
  rw [Measure.real, h, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl _ hpos)

private theorem exactQtrue_real_singleton {d n : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2)
    (omega : Fin n → BinObs d) :
    (exactQtrue n hq0 hr0 hrhalf hrq).real {omega} =
      ∑ lam : Fin d → Bool, ((2 : ℝ) ^ d)⁻¹ *
        ∏ i, Causalean.Estimation.MinimaxATE.obsReal
          (exactSignPropensity r lam) (exactSignOutcome q r lam) (omega i) := by
  haveI : ∀ lam : Fin d → Bool,
      IsProbabilityMeasure (exactQpert n lam hq0 hr0 hrhalf hrq) :=
    fun _ ↦ by unfold exactQpert; infer_instance
  rw [exactQtrue, Measure.real, Causalean.Stat.mixture_apply]
  rw [ENNReal.toReal_sum (fun lam _ ↦ ENNReal.mul_ne_top
    (by rw [Causalean.Estimation.MinimaxATE.signWeight];
        exact ENNReal.inv_ne_top.2 (by simp)) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [ENNReal.toReal_mul]
  have hw : (Causalean.Estimation.MinimaxATE.signWeight d lam).toReal =
      ((2 : ℝ) ^ d)⁻¹ := by
    simp [Causalean.Estimation.MinimaxATE.signWeight, Fintype.card_fun]
  rw [hw]
  congr 1
  change (exactQpert n lam hq0 hr0 hrhalf hrq).real {omega} = _
  rw [exactQpert, Causalean.Estimation.MinimaxATE.productLaw,
    Causalean.Stat.pi_real_singleton]
  exact Finset.prod_congr rfl fun i _ ↦
    Causalean.Estimation.MinimaxATE.obsLaw_real_singleton
      (exactSign_valid lam hq0 hr0 hrhalf hrq) (omega i)

private noncomputable def exactChiSqOverlap {d : ℕ} {q r : ℝ}
    (lam lam' : Fin d → Bool) : ℝ :=
  ∑ z : BinObs d,
    Causalean.Estimation.MinimaxATE.obsReal
        (exactSignPropensity r lam) (exactSignOutcome q r lam) z *
      Causalean.Estimation.MinimaxATE.obsReal
        (exactSignPropensity r lam') (exactSignOutcome q r lam') z /
      Causalean.Estimation.MinimaxATE.obsReal
        (exactSignPropensity 0 (exactZeroLam (d := d)))
        (exactSignOutcome 0 0 (exactZeroLam (d := d))) z

private theorem exactChiSqOverlap_eq {d : ℕ} [Nonempty (Fin d)]
    {q r : ℝ} (hrsq : r ^ 2 = q / 8) (lam lam' : Fin d → Bool) :
    exactChiSqOverlap (q := q) (r := r) lam lam' =
      1 + (q - q ^ 2 / 2 + q ^ 3 / 8) / (d : ℝ) *
        ∑ k, Causalean.Estimation.MinimaxATE.signOf (lam k) *
          Causalean.Estimation.MinimaxATE.signOf (lam' k) := by
  have hd : (d : ℝ) ≠ 0 := by
    have hdNat : d ≠ 0 := by simpa using (Fintype.card_ne_zero (α := Fin d))
    exact_mod_cast hdNat
  have hcell (k : Fin d) :
      ∑ a : Bool, ∑ y : Bool,
        Causalean.Estimation.MinimaxATE.obsReal
            (exactSignPropensity r lam) (exactSignOutcome q r lam) (k, a, y) *
          Causalean.Estimation.MinimaxATE.obsReal
            (exactSignPropensity r lam') (exactSignOutcome q r lam') (k, a, y) /
          Causalean.Estimation.MinimaxATE.obsReal
            (exactSignPropensity 0 (exactZeroLam (d := d)))
            (exactSignOutcome 0 0 (exactZeroLam (d := d))) (k, a, y)
        = 1 / (d : ℝ) +
          (q - q ^ 2 / 2 + q ^ 3 / 8) / (d : ℝ) *
            (Causalean.Estimation.MinimaxATE.signOf (lam k) *
              Causalean.Estimation.MinimaxATE.signOf (lam' k)) := by
    have hq : q = 8 * r ^ 2 := by nlinarith [hrsq]
    rcases Causalean.Estimation.MinimaxATE.signOf_mem (lam k) with h | h <;>
      rcases Causalean.Estimation.MinimaxATE.signOf_mem (lam' k) with h' | h' <;>
      simp only [Fintype.sum_bool, Causalean.Estimation.MinimaxATE.obsReal,
        exactSignPropensity, exactSignOutcome, Bool.false_eq_true, if_false, if_true,
        Fintype.card_fin, h, h'] <;>
      field_simp [hd] <;>
      rw [hq] <;> ring
  unfold exactChiSqOverlap
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [hcell]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp [hd]

private theorem one_add_chiSqDiv_exactQtrue_exactQfalse {d n : ℕ}
    [Nonempty (Fin d)] {q r : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2) :
    1 + Causalean.Stat.chiSqDiv (exactQtrue n hq0 hr0 hrhalf hrq) (exactQfalse d n) =
      ∑ lam : Fin d → Bool, ∑ lam' : Fin d → Bool,
        ((2 : ℝ) ^ d)⁻¹ * ((2 : ℝ) ^ d)⁻¹ *
          (exactChiSqOverlap (q := q) (r := r) lam lam') ^ n := by
  haveI : IsProbabilityMeasure (exactQtrue n hq0 hr0 hrhalf hrq) := by
    haveI : ∀ lam : Fin d → Bool,
        IsProbabilityMeasure (exactQpert n lam hq0 hr0 hrhalf hrq) :=
      fun _ ↦ by unfold exactQpert; infer_instance
    exact Causalean.Stat.mixture_isProbabilityMeasure _
      (Causalean.Estimation.MinimaxATE.signWeight_sum d) _
  haveI : IsProbabilityMeasure (exactQfalse d n) := by unfold exactQfalse; infer_instance
  have hac : exactQtrue n hq0 hr0 hrhalf hrq ≪ exactQfalse d n :=
    Causalean.Estimation.MinimaxATE.absolutelyContinuous_of_singleton_pos _ _
      exactQfalse_singleton_ne_zero
  rw [Causalean.Stat.finite_one_add_chiSqDiv _ _ hac]
  have hstep : ∀ omega : Fin n → BinObs d,
      ((exactQtrue n hq0 hr0 hrhalf hrq).real {omega}) ^ 2 /
          (exactQfalse d n).real {omega} =
        ∑ lam : Fin d → Bool, ∑ lam' : Fin d → Bool,
          ((2 : ℝ) ^ d)⁻¹ * ((2 : ℝ) ^ d)⁻¹ *
            ∏ i, (Causalean.Estimation.MinimaxATE.obsReal
                (exactSignPropensity r lam) (exactSignOutcome q r lam) (omega i) *
              Causalean.Estimation.MinimaxATE.obsReal
                (exactSignPropensity r lam') (exactSignOutcome q r lam') (omega i) /
              Causalean.Estimation.MinimaxATE.obsReal
                (exactSignPropensity 0 (exactZeroLam (d := d)))
                (exactSignOutcome 0 0 (exactZeroLam (d := d))) (omega i)) := by
    intro omega
    rw [exactQtrue_real_singleton hq0 hr0 hrhalf hrq omega, exactQfalse,
      Causalean.Estimation.MinimaxATE.productLaw,
      Causalean.Stat.pi_real_singleton, sq, Finset.sum_mul_sum, Finset.sum_div]
    simp_rw [Causalean.Estimation.MinimaxATE.obsLaw_real_singleton]
    refine Finset.sum_congr rfl fun lam _ ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun lam' _ ↦ ?_
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl fun omega _ ↦ hstep omega, Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam' _ ↦ ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold exactChiSqOverlap
  rw [Fintype.sum_pow]

private theorem exact_tvDist_le_half {d n : ℕ} [Nonempty (Fin d)] [NeZero d]
    {q r : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (hrq : r + q / 4 ≤ 1 / 2)
    (hrsq : r ^ 2 = q / 8)
    (hGamma0 : 0 ≤ q - q ^ 2 / 2 + q ^ 3 / 8)
    (hGamma1 : q - q ^ 2 / 2 + q ^ 3 / 8 ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 *
        ((q - q ^ 2 / 2 + q ^ 3 / 8) / 2) ^ 2 ≤
      (d : ℝ) * Real.log 2) :
    Causalean.Stat.tvDist (exactQfalse d n)
      (exactQtrue n hq0 hr0 hrhalf hrq) ≤ 1 / 2 := by
  let Gamma := q - q ^ 2 / 2 + q ^ 3 / 8
  have hid := one_add_chiSqDiv_exactQtrue_exactQfalse
    (d := d) (n := n) hq0 hr0 hrhalf hrq
  have hov :
      ∑ lam : Fin d → Bool, ∑ lam' : Fin d → Bool,
          ((2 : ℝ) ^ d)⁻¹ * ((2 : ℝ) ^ d)⁻¹ *
            (exactChiSqOverlap (q := q) (r := r) lam lam') ^ n =
        ∑ lam : Fin d → Bool, ∑ lam' : Fin d → Bool,
          ((2 : ℝ) ^ d)⁻¹ * ((2 : ℝ) ^ d)⁻¹ *
            (1 + (2 * (Gamma / 2) / (d : ℝ)) *
              ∑ k, Causalean.Estimation.MinimaxATE.signOf (lam k) *
                Causalean.Estimation.MinimaxATE.signOf (lam' k)) ^ n := by
    refine Finset.sum_congr rfl fun lam _ ↦
      Finset.sum_congr rfl fun lam' _ ↦ ?_
    rw [exactChiSqOverlap_eq hrsq]
    dsimp [Gamma]
    ring
  have hbound := Causalean.Estimation.MinimaxATE.ingster_bound d n
    (show 0 ≤ Gamma / 2 by dsimp [Gamma]; linarith)
    (show 2 * (Gamma / 2) ≤ 1 by dsimp [Gamma]; linarith)
    (show 2 * (n : ℝ) ^ 2 * (Gamma / 2) ^ 2 ≤
        (d : ℝ) * Real.log 2 by simpa [Gamma] using hreg)
  rw [← hov, ← hid] at hbound
  have hchi : Causalean.Stat.chiSqDiv
      (exactQtrue n hq0 hr0 hrhalf hrq) (exactQfalse d n) ≤ 1 := by linarith
  haveI : IsProbabilityMeasure (exactQtrue n hq0 hr0 hrhalf hrq) := by
    haveI : ∀ lam : Fin d → Bool,
        IsProbabilityMeasure (exactQpert n lam hq0 hr0 hrhalf hrq) :=
      fun _ ↦ by unfold exactQpert; infer_instance
    exact Causalean.Stat.mixture_isProbabilityMeasure _
      (Causalean.Estimation.MinimaxATE.signWeight_sum d) _
  haveI : IsProbabilityMeasure (exactQfalse d n) := by unfold exactQfalse; infer_instance
  have hac : exactQtrue n hq0 hr0 hrhalf hrq ≪ exactQfalse d n :=
    Causalean.Estimation.MinimaxATE.absolutelyContinuous_of_singleton_pos _ _
      exactQfalse_singleton_ne_zero
  rw [Causalean.Stat.tvDist_symm]
  calc
    Causalean.Stat.tvDist (exactQtrue n hq0 hr0 hrhalf hrq) (exactQfalse d n)
        ≤ (1 / 2) * Real.sqrt (Causalean.Stat.chiSqDiv
            (exactQtrue n hq0 hr0 hrhalf hrq) (exactQfalse d n)) :=
      Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv _ _ hac Integrable.of_finite
    _ ≤ (1 / 2) * Real.sqrt 1 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.sqrt_le_sqrt hchi
    _ = 1 / 2 := by rw [Real.sqrt_one]; ring

private lemma binaryExactMinimaxRisk_collision_aux {n d : ℕ} [Nonempty (Fin d)]
    {epsilon q r : ℝ}
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (hrE : r ≤ 1 / 2 - epsilon)
    (hrhalf : r < 1 / 2) (hrq : r + q / 4 ≤ 1 / 2)
    (htv : Causalean.Stat.tvDist (exactQfalse d n)
      (exactQtrue n hq0 hr0 hrhalf.le hrq) ≤ 1 / 2) :
    q ^ 2 / 64 ≤ binaryExactMinimaxRisk n d epsilon := by
  let P0 : BinaryExactLaw n d epsilon :=
    exactSignExactLaw (q := 0) (r := 0) (exactZeroLam (d := d)) he0
      (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let P : (Fin d → Bool) → BinaryExactLaw n d epsilon := fun lam ↦
    exactSignExactLaw (q := q) (r := r) lam he0 hrE hq0 hr0 hrhalf hrq
  have hprod0 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n =
      exactQfalse d n := by rfl
  have hprod (lam : Fin d → Bool) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw (P lam).1 n =
        exactQpert n lam hq0 hr0 hrhalf.le hrq := by rfl
  have htau0 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1 = 0 := by
    simpa [P0] using (exactSignExactLaw_ate (n := n) (epsilon := epsilon)
      (q := 0) (r := 0) (exactZeroLam (d := d)) he0 (by linarith)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have htau (lam : Fin d → Bool) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional (P lam).1 = q / 2 := by
    simpa [P] using (exactSignExactLaw_ate (n := n) (epsilon := epsilon)
      (q := q) (r := r) lam he0 hrE hq0 hr0 hrhalf hrq)
  let est0 : {f : (Fin n → BinObs d) → ℝ // Measurable f} :=
    ⟨fun _ ↦ 0, measurable_const⟩
  letI : Nonempty {f : (Fin n → BinObs d) → ℝ // Measurable f} := ⟨est0⟩
  unfold binaryExactMinimaxRisk
  apply le_ciInf
  intro est
  haveI : ∀ lam : Fin d → Bool,
      IsProbabilityMeasure (exactQpert n lam hq0 hr0 hrhalf.le hrq) :=
    fun _ ↦ by unfold exactQpert; infer_instance
  haveI : IsProbabilityMeasure (exactQfalse d n) := by unfold exactQfalse; infer_instance
  haveI : IsProbabilityMeasure (exactQtrue n hq0 hr0 hrhalf.le hrq) :=
    Causalean.Stat.mixture_isProbabilityMeasure _
      (Causalean.Estimation.MinimaxATE.signWeight_sum d) _
  have hprob := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := exactQfalse d n) (P₁ := exactQtrue n hq0 hr0 hrhalf.le hrq)
    est.2 (θ₀ := (0 : ℝ)) (θ₁ := q / 2) (s := q / 4) (c := (1 / 2 : ℝ))
    (by rw [zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ q / 2)]; linarith) htv
  have hprobMax : 1 / 4 ≤ max
      ((exactQfalse d n).real {x | q / 4 ≤ |est.1 x - 0|})
      ((exactQtrue n hq0 hr0 hrhalf.le hrq).real
        {x | q / 4 ≤ |est.1 x - q / 2|}) := by
    convert hprob using 1 <;> norm_num
  obtain ⟨lam, hlam⟩ := Causalean.Stat.exists_real_ge_mixture
    (Causalean.Estimation.MinimaxATE.signWeight d)
    (Causalean.Estimation.MinimaxATE.signWeight_sum d)
    (fun lam ↦ exactQpert n lam hq0 hr0 hrhalf.le hrq)
    {x | q / 4 ≤ |est.1 x - q / 2|}
  have hmse (P' : BinaryExactLaw n d epsilon) :
      (q / 4) ^ 2 *
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P'.1 n).real
            {x | q / 4 ≤
              |est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1|} ≤
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P'.1 n) est.1
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1) := by
    unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
    have hset :
        {x | q / 4 ≤
            |est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1|} =
          {x | (q / 4) ^ 2 ≤
            (est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [hq0,
          abs_nonneg (est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1),
          sq_abs (est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun x ↦
        sq_nonneg (est.1 x - CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1))
      MemLp.of_discrete.integrable_sq ((q / 4) ^ 2)
  have hprob' : 1 / 4 ≤ max
      ((exactQfalse d n).real {x | q / 4 ≤ |est.1 x - 0|})
      ((exactQpert n lam hq0 hr0 hrhalf.le hrq).real
        {x | q / 4 ≤ |est.1 x - q / 2|}) :=
    hprobMax.trans (max_le_max (le_refl _) hlam)
  have htwo : q ^ 2 / 64 ≤ max
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n) est.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1))
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw (P lam).1 n) est.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional (P lam).1)) := by
    have hp := mul_le_mul_of_nonneg_left hprob' (sq_nonneg (q / 4))
    rw [mul_max_of_nonneg _ _ (sq_nonneg (q / 4))] at hp
    calc
      q ^ 2 / 64 = (q / 4) ^ 2 * (1 / 4) := by ring
      _ ≤ max
          ((q / 4) ^ 2 *
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n).real
              {x | q / 4 ≤ |est.1 x -
                CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1|})
          ((q / 4) ^ 2 *
            (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw (P lam).1 n).real
              {x | q / 4 ≤ |est.1 x -
                CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional (P lam).1|}) := by
          simpa [hprod0, hprod, htau0, htau] using hp
      _ ≤ _ := max_le_max (hmse P0) (hmse (P lam))
  have hb : BddAbove (Set.range (fun P' : BinaryExactLaw n d epsilon ↦
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P'.1 n) est.1
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P'.1))) := by
    refine ⟨((∑ sample : Fin n → BinObs d, |est.1 sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨P', rfl⟩
    exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_le_estimator_abs_sum_bound
      P'.1 P'.2.1 est.1
  exact htwo.trans (max_le (le_ciSup hb P0) (le_ciSup hb (P lam)))

/-- If [the sample is nonempty](hyp:hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1) and [the
  stated dn condition holds](hyp:hdn), [the exact-homogeneity binary minimax risk obeys the
  collision-regime lower bound](goal). -/
lemma binaryExactMinimaxRisk_collision_lower {n d : ℕ} {epsilon : ℝ}
    (hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hdn : (d : ℝ) ≤ (n : ℝ) ^ 2) :
    ((min (1 / 2 : ℝ) (8 * (1 / 2 - epsilon) ^ 2)) ^ 2 / 64) *
        ((d : ℝ) / (n : ℝ) ^ 2) ≤ binaryExactMinimaxRisk n d epsilon := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let eta : ℝ := 1 / 2 - epsilon
  let u : ℝ := min (1 / 2 : ℝ) (8 * eta ^ 2)
  let q : ℝ := u * Real.sqrt d / n
  let r : ℝ := Real.sqrt (q / 8)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hu0 : 0 < u := by dsimp [u]; positivity
  have huhalf : u ≤ 1 / 2 := min_le_left _ _
  have hueta : u ≤ 8 * eta ^ 2 := min_le_right _ _
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hsqrt_le : Real.sqrt (d : ℝ) ≤ (n : ℝ) := by
    have hs := Real.sqrt_le_sqrt hdn
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hnR] at hs
    exact hs
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqU : q ≤ u := by
    dsimp [q]
    have hratio : Real.sqrt (d : ℝ) / (n : ℝ) ≤ 1 :=
      (div_le_one hnR).2 hsqrt_le
    calc
      u * Real.sqrt (d : ℝ) / (n : ℝ) =
          u * (Real.sqrt (d : ℝ) / (n : ℝ)) := by ring
      _ ≤ u * 1 := mul_le_mul_of_nonneg_left hratio hu0.le
      _ = u := mul_one u
  have hqhalf : q ≤ 1 / 2 := hqU.trans huhalf
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = q / 8 := by
    dsimp [r]
    exact Real.sq_sqrt (by positivity)
  have hrquarter : r ≤ 1 / 4 := by
    nlinarith [hrsq, sq_nonneg (r - 1 / 4)]
  have hrE : r ≤ 1 / 2 - epsilon := by
    change r ≤ eta
    have hqeta : q / 8 ≤ eta ^ 2 := by nlinarith [hqU, hueta]
    nlinarith [hrsq, sq_nonneg (r - eta)]
  have hrhalf : r < 1 / 2 := by linarith
  have hrq : r + q / 4 ≤ 1 / 2 := by nlinarith [hrquarter, hqhalf]
  let Gamma : ℝ := q - q ^ 2 / 2 + q ^ 3 / 8
  have hGamma0 : 0 ≤ Gamma := by
    have hbracket : 0 ≤ 1 - q / 2 + q ^ 2 / 8 := by
      nlinarith [sq_nonneg (q - 2)]
    dsimp [Gamma]
    nlinarith [mul_nonneg hq0 hbracket]
  have hGammaQ : Gamma ≤ q := by
    have hmul : q ^ 2 * (q - 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg q) (by linarith)
    dsimp [Gamma]
    nlinarith
  have hGamma1 : Gamma ≤ 1 := hGammaQ.trans (hqhalf.trans (by norm_num))
  have hqsq : q ^ 2 = u ^ 2 * (d : ℝ) / (n : ℝ) ^ 2 := by
    dsimp [q]
    calc
      (u * Real.sqrt (d : ℝ) / (n : ℝ)) ^ 2 =
          u ^ 2 * (Real.sqrt (d : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by ring
      _ = u ^ 2 * (d : ℝ) / (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hdR.le]
  have hreg : 2 * (n : ℝ) ^ 2 * (Gamma / 2) ^ 2 ≤
      (d : ℝ) * Real.log 2 := by
    have hGsq : Gamma ^ 2 ≤ q ^ 2 := by nlinarith [hGamma0, hGammaQ, hq0]
    have hlog : (1 / 8 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    have hbase : (n : ℝ) ^ 2 * q ^ 2 / 2 = u ^ 2 * (d : ℝ) / 2 := by
      rw [hqsq]
      field_simp [hnR.ne']
    have huSq : u ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [hu0.le, huhalf]
    calc
      2 * (n : ℝ) ^ 2 * (Gamma / 2) ^ 2
          = (n : ℝ) ^ 2 * Gamma ^ 2 / 2 := by ring
      _ ≤ (n : ℝ) ^ 2 * q ^ 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGsq (sq_nonneg (n : ℝ))) (by norm_num)
      _ = u ^ 2 * (d : ℝ) / 2 := hbase
      _ ≤ (d : ℝ) / 8 := by
        have hm := mul_le_mul_of_nonneg_right huSq hdR.le
        nlinarith
      _ ≤ (d : ℝ) * Real.log 2 := by
        have hm := mul_le_mul_of_nonneg_left hlog hdR.le
        simpa [div_eq_mul_inv] using hm
  have htv := exact_tvDist_le_half (d := d) (n := n) hq0 hr0 hrhalf.le hrq hrsq
    hGamma0 hGamma1 (by simpa [Gamma] using hreg)
  have hlower := binaryExactMinimaxRisk_collision_aux (n := n) (d := d)
    he0 he1 hq0 hr0 hrE hrhalf hrq htv
  rw [hqsq] at hlower
  change (u ^ 2 / 64) * ((d : ℝ) / (n : ℝ) ^ 2) ≤ _
  have halg : (u ^ 2 / 64) * ((d : ℝ) / (n : ℝ) ^ 2) =
      u ^ 2 * (d : ℝ) / (n : ℝ) ^ 2 / 64 := by ring
  exact halg.trans_le hlower

-- @node: lem:zeng-binary-exact-homogeneity-lower
/-- [Zeng--Balakrishnan--Han--Kennedy's exact-homogeneity lower bound, in the fixed finite-sample
  interface used by the frontier theorem](goal). -/
theorem zengBinaryExactHomogeneityLower (epsilon : ℝ) :
    ZengBinaryExactHomogeneityLower epsilon := by
  intro he
  rcases he with ⟨he0, he1⟩
  let u : ℝ := min (1 / 2 : ℝ) (8 * (1 / 2 - epsilon) ^ 2)
  let a : ℝ := min (1 / 200 : ℝ) (u ^ 2 / 128)
  refine ⟨a, 1, 1, ?_, by norm_num, ?_⟩
  · have hu : 0 < u := by dsimp [u]; positivity
    dsimp [a]
    positivity
  · intro n d hd hn _hdn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hdnSq : (d : ℝ) ≤ (n : ℝ) ^ 2 := by simpa using _hdn
    have hpar := binaryExactMinimaxRisk_parametric_lower
      (n := n) (d := d) hnpos hd he0 he1
    have hcol := binaryExactMinimaxRisk_collision_lower
      (n := n) (d := d) hnpos hd he0 he1 hdnSq
    have hu : 0 < u := by dsimp [u]; positivity
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    by_cases hsmall : d ≤ n
    · have hsmallR : (d : ℝ) ≤ n := by exact_mod_cast hsmall
      have hyx : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
        apply (div_le_iff₀ (sq_pos_of_pos hnR)).2
        field_simp [hnR.ne']
        nlinarith
      have hsum : 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 ≤
          2 * (1 / (n : ℝ)) := by linarith
      have ha : a ≤ 1 / 200 := by dsimp [a]; exact min_le_left _ _
      calc
        a * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2)
            ≤ (1 / 200 : ℝ) * (2 * (1 / (n : ℝ))) :=
          mul_le_mul ha hsum (by positivity) (by norm_num)
        _ = 1 / (100 * (n : ℝ)) := by field_simp [hnR.ne']; ring
        _ ≤ binaryExactMinimaxRisk n d epsilon := hpar
    · have hlarge : n ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
      have hlargeR : (n : ℝ) ≤ d := by exact_mod_cast hlarge
      have hxy : 1 / (n : ℝ) ≤ (d : ℝ) / (n : ℝ) ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hnR)).2
        field_simp [hnR.ne']
        nlinarith
      have hsum : 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 ≤
          2 * ((d : ℝ) / (n : ℝ) ^ 2) := by linarith
      have ha : a ≤ u ^ 2 / 128 := by dsimp [a]; exact min_le_right _ _
      calc
        a * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2)
            ≤ (u ^ 2 / 128) *
              (2 * ((d : ℝ) / (n : ℝ) ^ 2)) :=
          mul_le_mul ha hsum (by positivity) (by positivity)
        _ = (u ^ 2 / 64) * ((d : ℝ) / (n : ℝ) ^ 2) := by ring
        _ ≤ binaryExactMinimaxRisk n d epsilon := by simpa [u] using hcol

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
