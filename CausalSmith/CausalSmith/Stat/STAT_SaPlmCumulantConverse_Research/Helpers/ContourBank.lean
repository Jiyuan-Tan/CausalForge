import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.Cumulant
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.ComplexAnalysisLocal
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.BoundedCertifiedComplex
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.JensenBlaschke
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.Basic
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.ArgumentPrinciple
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.Homotopy
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Fixed-fuel translated-dyadic contour bank

The bank reads one experiment-wide record for the primitive constants.  Its
integers are the displayed closed forms; there is no unbounded or
proof-selected search, exact-real inspection, or law query.
-/

noncomputable section

open Metric Set
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Analysis.ArgumentPrincipleCircle

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- A supplied positive certified-real record.  Executable consumers inspect
only `name.approx`, `name.modulus`, and the rational lower witness. -/
structure PositiveCertifiedReal where
  name : CertifiedReal
  lower : ℚ
  lower_pos : 0 < lower
  lower_le_value : (lower : ℝ) ≤ name.value

/-- The one fixed primitive record shared by the bank and estimator. -/
structure CertifiedBankInputs (p : Parameters) where
  kName : ℕ
  k_value : kName = p.k
  deltaName : PositiveCertifiedReal
  delta_value : deltaName.name.value = p.delta
  psietaName : PositiveCertifiedReal
  psieta_value : psietaName.name.value = p.psieta
  R0Name : PositiveCertifiedReal
  R0_value : R0Name.name.value = zeroRadius p
  R1Name : PositiveCertifiedReal
  R1_value : R1Name.name.value = searchRadius p
  zeroRadius_contract :
    zeroRadius p = Ak p.k * (p.psieta ^ 2 / p.delta) ^ ((p.k - 2 : ℝ)⁻¹)
  searchRadius_contract : searchRadius p = zeroRadius p + 1

/-- Reuse the identical primitive names for another parameter record carrying
the same primitive constants.  Only the propositional value contracts are
transported; no new name is selected or reconstructed. -/
def CertifiedBankInputs.transport {p q : Parameters}
    (pStar : CertifiedBankInputs p) (hk : p.k = q.k)
    (hdelta : p.delta = q.delta) (hpsi : p.psieta = q.psieta) :
    CertifiedBankInputs q where
  kName := pStar.kName
  k_value := pStar.k_value.trans hk
  deltaName := pStar.deltaName
  delta_value := pStar.delta_value.trans hdelta
  psietaName := pStar.psietaName
  psieta_value := pStar.psieta_value.trans hpsi
  R0Name := pStar.R0Name
  R0_value := pStar.R0_value.trans (by simp [zeroRadius, hk, hdelta, hpsi])
  R1Name := pStar.R1Name
  R1_value := pStar.R1_value.trans (by simp [searchRadius, zeroRadius, hk, hdelta, hpsi])
  zeroRadius_contract := rfl
  searchRadius_contract := rfl

/-- Error-one rational refinement used exactly twice by the bank. -/
def errorOne : PosRat := ⟨1, by norm_num⟩

/-- Natural ceiling of a rational upper endpoint, clamped below by one. -/
def positiveCeil (q : ℚ) : ℕ := ⌈max 1 q⌉₊

/-- The clamped rational ceiling dominates its input. -/
lemma rat_le_positiveCeil (q : ℚ) : q ≤ ((positiveCeil q : ℕ) : ℚ) := by
  unfold positiveCeil
  exact (le_max_right (1 : ℚ) q).trans (Nat.le_ceil _)

/-- The clamped rational ceiling is at least one. -/
lemma one_le_positiveCeil (q : ℚ) : 1 ≤ positiveCeil q := by
  unfold positiveCeil
  exact_mod_cast (le_max_left (1 : ℚ) q).trans (Nat.le_ceil _)

/-- All data computed by the displayed fixed-fuel bank program. -/
structure ContourBankData where
  Upsi : ℕ
  UR : ℕ
  Ncert : ℕ
  mStar : ℕ
  JBase : ℕ
  rhoName : Fin (JBase + 1) → CertifiedReal
  rho : Fin (JBase + 1) → ℝ -- @realizes rho(increasing finite vector in (R0,R1))
  rho_value : ∀ j, (rhoName j).value = rho j
  dStar : ℚ
  hStar : ℚ
  eStar : ℕ
  dStarDen : ℕ
  uStar : ℕ
  aStarRat : ℚ
  aStarRat_pos : 0 < aStarRat
  aStar : ℝ -- @realizes aStar(positive dyadic boundary-modulus certificate)
  aStar_eq : aStar = (aStarRat : ℝ)

/-- Cardinality of the explicit bank. -/
def ContourBankData.J (B : ContourBankData) : ℕ := B.JBase + 1
  -- @realizes J(cardinality of translated-dyadic bank)

/-- The circle belonging to one bank radius. -/
def bankCircle (B : ContourBankData) (j : Fin (B.JBase + 1)) : Set ℂ :=
  sphere 0 (B.rho j) -- @realizes Cj(positively oriented circle |z|=rho_j)

/-- A dyadic grid with mesh `2⁻(k+1)` and indices through `2^k` stays
strictly below the unit-length endpoint after translation by one quarter. -/
lemma rat_grid_lt_one (k j : ℕ) (hj : j ≤ 2 ^ k) :
    (1 / 4 : ℚ) + j * (1 / 2 : ℚ) ^ (k + 1) < 1 := by
  have hp : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  rw [pow_succ]
  simp only [one_div, inv_pow]
  have hj' : (j : ℚ) ≤ (2 : ℚ) ^ k := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' (inv_nonneg.mpr hp.le)
  rw [mul_inv_cancel₀ hp.ne'] at h
  norm_num at h ⊢
  nlinarith

/-- More grid points than listed complex numbers leave one translated grid
radius uniformly separated from every listed modulus. -/
lemma exists_translated_grid_radius_separated {N J : ℕ} (a : Fin N → ℂ)
    (base d h : ℝ) (hd : 0 < d) (hh : 2 * h < d) (hcard : N < J) :
    ∃ j : Fin J, ∀ i, h ≤ |‖a i‖ - (base + (j : ℕ) * d)| := by
  classical
  by_contra hn
  push_neg at hn
  choose f hf using hn
  have hinj : Function.Injective f := by
    intro j k heq
    by_contra hjk
    have htri := abs_sub_le (base + (j : ℕ) * d) ‖a (f j)‖
      (base + (k : ℕ) * d)
    rw [heq] at htri
    have hjclose := hf j
    rw [heq, abs_sub_comm] at hjclose
    have hkclose := hf k
    have hdistlt : |(base + (j : ℕ) * d) - (base + (k : ℕ) * d)| < 2 * h := by
      linarith
    rcases lt_or_gt_of_ne hjk with hjk' | hkj'
    · have hcast : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk'
      have hdist : d ≤ |(base + (j : ℕ) * d) -
          (base + (k : ℕ) * d)| := by
        rw [abs_of_nonpos]
        · nlinarith
        · nlinarith
      linarith
    · have hcast : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj'
      have hdist : d ≤ |(base + (j : ℕ) * d) -
          (base + (k : ℕ) * d)| := by
        rw [abs_of_nonneg]
        · nlinarith
        · nlinarith
      linarith
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- The closed-form dyadic exponent dominates a product of at most `K`
factors, each bounded below by a dyadic mesh divided by a positive integer. -/
lemma dyadic_product_certificate (m D N K : ℕ) (hD : 0 < D) (hNK : N ≤ K) :
    (1 / 2 : ℝ) ^ (K * (m + D)) ≤
      (((1 / 2 : ℝ) ^ m) / D) ^ N := by
  have hDpow : D ≤ 2 ^ D := (D.lt_two_pow_self).le
  have hInv : (1 / 2 : ℝ) ^ D ≤ 1 / D := by
    rw [one_div_pow]
    exact one_div_le_one_div_of_le (by exact_mod_cast hD) (by exact_mod_cast hDpow)
  let t : ℝ := (1 / 2) ^ (m + D)
  let b : ℝ := (1 / 2) ^ m / D
  have htb : t ≤ b := by
    dsimp [t, b]
    rw [pow_add]
    calc
      (1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ D ≤
          (1 / 2 : ℝ) ^ m * (1 / D) := by gcongr
      _ = (1 / 2 : ℝ) ^ m / D := by ring
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : t ^ K ≤ t ^ N := pow_le_pow_of_le_one ht0 ht1 hNK
  calc
    (1 / 2 : ℝ) ^ (K * (m + D)) = t ^ K := by
      change (1 / 2 : ℝ) ^ (K * (m + D)) =
        ((1 / 2 : ℝ) ^ (m + D)) ^ K
      rw [← pow_mul, Nat.mul_comm]
    _ ≤ t ^ N := hpow
    _ ≤ b ^ N := pow_le_pow_left₀ ht0 htb N
    _ = (((1 / 2 : ℝ) ^ m) / D) ^ N := rfl

/-- Two binary digits per natural exponent are enough to lie below the
corresponding negative exponential. -/
lemma dyadic_two_mul_le_exp_neg (E : ℕ) :
    (1 / 2 : ℝ) ^ (2 * E) ≤ Real.exp (-(E : ℝ)) := by
  have hbase : (1 / 2 : ℝ) ^ 2 ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    norm_num
    have hi : (4 : ℝ)⁻¹ ≤ (Real.exp 1)⁻¹ :=
      (inv_le_inv₀ (a := (4 : ℝ)) (b := Real.exp 1) (by norm_num)
        (Real.exp_pos 1)).2 (by nlinarith [Real.exp_one_lt_three])
    simpa [one_div] using hi
  calc
    (1 / 2 : ℝ) ^ (2 * E) = ((1 / 2 : ℝ) ^ 2) ^ E := by rw [pow_mul]
    _ ≤ (Real.exp (-1)) ^ E := by gcongr
    _ = Real.exp (-(E : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The closed-form law-blind translated-dyadic bank. -/
-- @node: def:contour-bank-handle
def contourBank (p : Parameters) (pStar : CertifiedBankInputs p) : ContourBankData :=
  let psiI := certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne
  let R1I := certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne
  let Upsi := positiveCeil psiI.hi
  let UR := positiveCeil R1I.hi
  let Ncert := 4 * Upsi ^ 2 * (UR + 2) ^ 3
  let mStar := Ncert + 3
  let dStar : ℚ := (1 / 2) ^ mStar
  let hStar := dStar / 3
  let JBase := 2 ^ (mStar - 1)
  let rhoName : Fin (JBase + 1) → CertifiedReal := fun j ↦
    CertifiedReal.add pStar.R0Name.name
      (CertifiedReal.ofRat (1 / 4 + j.1 * dStar))
  let eStar := 8 * UR * Upsi ^ 2 * (UR + 1) ^ 2
  let dStarDen := 3 * (2 * UR + 1)
  let uStar := 2 * eStar + Ncert * (mStar + dStarDen)
  let aStarRat : ℚ := (1 / 2) ^ uStar
  { Upsi := Upsi
    UR := UR
    Ncert := Ncert
    mStar := mStar
    JBase := JBase
    rhoName := rhoName
    rho := fun j ↦ (rhoName j).value
    rho_value := fun _ ↦ rfl
    dStar := dStar
    hStar := hStar
    eStar := eStar
    dStarDen := dStarDen
    uStar := uStar
    aStarRat := aStarRat
    aStarRat_pos := by dsimp [aStarRat]; positivity
    aStar := (aStarRat : ℝ)
    aStar_eq := rfl }

/-- The fixed-fuel bank contains a uniformly conditioned positive-count circle
for every treatment-noise transform in the broad class. -/
-- @node: lem:finite-contour-bank
lemma finite_contour_bank {Xspace : Type*} [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (n : ℕ) (hn : 1 ≤ n)
    (m : Model (Xspace := Xspace) p)
    (hclass : NonGaussianClass p n m) :
    let B := contourBank p pStar
    0 < B.aStar ∧
    B.Ncert = 4 * B.Upsi ^ 2 * (B.UR + 2) ^ 3 ∧
    B.mStar = B.Ncert + 3 ∧
    B.J = 2 ^ (B.mStar - 1) + 1 ∧
    B.dStar = (1 / 2 : ℚ) ^ B.mStar ∧
    B.hStar = B.dStar / 3 ∧
    B.eStar = 8 * B.UR * B.Upsi ^ 2 * (B.UR + 1) ^ 2 ∧
    B.dStarDen = 3 * (2 * B.UR + 1) ∧
    B.uStar = 2 * B.eStar + B.Ncert * (B.mStar + B.dStarDen) ∧
    B.aStarRat = (1 / 2 : ℚ) ^ B.uStar ∧
    StrictMono B.rho ∧
    (∀ j, zeroRadius p < B.rho j ∧ B.rho j < searchRadius p) ∧
    ∃ j : Fin (B.JBase + 1),
      0 < zeroMultiplicityCount (treatmentMGF p m) 0 (B.rho j) ∧
      ∀ z ∈ bankCircle B j, B.aStar ≤ ‖treatmentMGF p m z‖ := by
  dsimp [contourBank, ContourBankData.J]
  refine ⟨by positivity, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro i j hij
    simp [CertifiedReal.add, CertifiedReal.ofRat]
    gcongr
  · intro j
    simp only [CertifiedReal.add, CertifiedReal.ofRat, pStar.R0_value]
    constructor
    · norm_num
      positivity
    · rw [pStar.searchRadius_contract]
      have hj : (j : ℕ) ≤ 2 ^
          (4 * positiveCeil
              (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
            (positiveCeil
              (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 2) :=
        Nat.le_of_lt_succ j.isLt
      norm_num at hj ⊢
      have hq := rat_grid_lt_one
        (4 * positiveCeil
            (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
          (positiveCeil
            (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 2)
        (j : ℕ) hj
      norm_num at hq
      have hq' :
        (1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
          (4 * positiveCeil
              (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
            (positiveCeil
              (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3) < 1 := by
        simpa [Nat.add_assoc] using hq
      have hc : ((↑((1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
          (4 * positiveCeil
              (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
            (positiveCeil
              (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3)) : ℝ) <
          (↑(1 : ℚ) : ℝ)) := Rat.cast_lt.mpr hq'
      simpa using hc
  · let psiI := certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne
    let R1I := certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne
    let Upsi := positiveCeil psiI.hi
    let UR := positiveCeil R1I.hi
    let Ncert := 4 * Upsi ^ 2 * (UR + 2) ^ 3
    let mStar := Ncert + 3
    let JBase := 2 ^ (mStar - 1)
    let dQ : ℚ := (1 / 2) ^ mStar
    let d : ℝ := (dQ : ℝ)
    let h : ℝ := d / 3
    let R1 := searchRadius p
    let Rfac := R1 + 1
    let Rout := R1 + 2
    let M := treatmentMGF p m
    have hpsi : p.psieta ≤ (Upsi : ℝ) := by
      have hc := certifiedIntervalArithmetic.refine_contains
        pStar.psietaName.name errorOne
      have hhi : p.psieta ≤ (psiI.hi : ℝ) := by
        simpa [psiI, RatInterval.Contains, pStar.psieta_value] using hc.2
      have hceilQ := rat_le_positiveCeil psiI.hi
      have hceilR : (psiI.hi : ℝ) ≤ (Upsi : ℝ) := by
        exact Rat.cast_le.mpr hceilQ
      exact hhi.trans hceilR
    have hR1U : R1 ≤ (UR : ℝ) := by
      have hc := certifiedIntervalArithmetic.refine_contains
        pStar.R1Name.name errorOne
      have hhi : R1 ≤ (R1I.hi : ℝ) := by
        simpa [R1, R1I, RatInterval.Contains, pStar.R1_value] using hc.2
      have hceilQ := rat_le_positiveCeil R1I.hi
      have hceilR : (R1I.hi : ℝ) ≤ (UR : ℝ) := Rat.cast_le.mpr hceilQ
      exact hhi.trans hceilR
    have hR1pos : 0 < R1 := by
      dsimp [R1, searchRadius]
      have hz : 0 < zeroRadius p := by
        rw [← pStar.R0_value]
        have hl : (0 : ℝ) < (pStar.R0Name.lower : ℝ) := by
          exact_mod_cast pStar.R0Name.lower_pos
        exact hl.trans_le pStar.R0Name.lower_le_value
      linarith
    have hRfac : 0 < Rfac := by dsimp [Rfac]; linarith
    have hRout : 0 < Rout := by dsimp [Rout]; linarith
    have hfacout : Rfac < Rout := by dsimp [Rfac, Rout]; linarith
    obtain ⟨hMan, hMzero, hMbound⟩ :=
      treatmentMGF_entire_normalized_bound p m n hclass
    have hupper : ∀ z ∈ sphere (0 : ℂ) Rout,
        ‖M z‖ ≤ Real.exp (4 * p.psieta ^ 2 * Rout ^ 2) := by
      intro z hz
      have hnorm : ‖z‖ = Rout := by
        simpa [mem_sphere, dist_zero_right, abs_of_pos hRout] using hz
      simpa [M, hnorm] using hMbound z
    have hjensen := jensen_zeroMultiplicityCount_bound
      hRfac hfacout (by positivity : 0 ≤ 4 * p.psieta ^ 2 * Rout ^ 2)
      hMan hMzero hupper
    have hlog : 1 / Rout ≤ Real.log (Rout / Rfac) := by
      have hx : 0 ≤ (1 / Rfac : ℝ) := by positivity
      have hbase := Real.le_log_one_add_of_nonneg hx
      have hratio : Rout / Rfac = 1 + 1 / Rfac := by
        dsimp [Rout, Rfac]
        field_simp
        ring
      rw [hratio]
      apply le_trans _ hbase
      rw [div_le_div_iff₀ hRout (by positivity : 0 < (1 / Rfac : ℝ) + 2)]
      field_simp
      nlinarith
    have hcountReal :
        (zeroMultiplicityCount M 0 Rfac : ℝ) ≤
          4 * p.psieta ^ 2 * Rout ^ 3 := by
      have hcountnonneg : 0 ≤ (zeroMultiplicityCount M 0 Rfac : ℝ) := by positivity
      have hlogmul := mul_le_mul_of_nonneg_left hlog hcountnonneg
      have hdiv : (zeroMultiplicityCount M 0 Rfac : ℝ) / Rout ≤
          4 * p.psieta ^ 2 * Rout ^ 2 := by
        exact (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using
          hlogmul.trans hjensen)
      calc
        (zeroMultiplicityCount M 0 Rfac : ℝ) =
            ((zeroMultiplicityCount M 0 Rfac : ℝ) / Rout) * Rout := by
          field_simp
        _ ≤ (4 * p.psieta ^ 2 * Rout ^ 2) * Rout := by gcongr
        _ = 4 * p.psieta ^ 2 * Rout ^ 3 := by ring
    have hcountCert : zeroMultiplicityCount M 0 Rfac ≤ Ncert := by
      have hpsi0 : 0 ≤ p.psieta := p.constants_pos.2.2.2.1.le
      have hRoutU : Rout ≤ (UR + 2 : ℕ) := by
        dsimp [Rout]
        norm_num
        linarith
      have hbound : 4 * p.psieta ^ 2 * Rout ^ 3 ≤ (Ncert : ℝ) := by
        have hRoutU' : Rout ≤ (UR : ℝ) + 2 := by simpa using hRoutU
        dsimp [Ncert]
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
        gcongr
      exact_mod_cast hcountReal.trans hbound
    obtain ⟨N, a, g, ha, hgAn, hgDiff, hgzero, hNcount, hfactor⟩ :=
      exists_complete_pointwise_blaschke_factorization hRfac
        (by simpa [M] using hMan.mono (by simp)) (by simpa [M, hMzero])
    have hNle : N ≤ Ncert := by simpa [M, hNcount] using hcountCert
    have hNcard : N < JBase + 1 := by
      have hpow : Ncert < 2 ^ (Ncert + 2) + 1 := by
        have hk := Ncert.lt_two_pow_self
        have hpmono : 2 ^ Ncert ≤ 2 ^ (Ncert + 2) :=
          Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
        omega
      dsimp [JBase, mStar]
      omega
    have hd : 0 < d := by dsimp [d, dQ]; positivity
    have hh : 2 * h < d := by dsimp [h]; linarith
    obtain ⟨j, hjsep⟩ := exists_translated_grid_radius_separated a
      (zeroRadius p + 1 / 4) d h hd hh hNcard
    refine ⟨j, ?_, ?_⟩
    · have hzloc := zero_localization p m hclass.etaSubGaussian
        hclass.cumulantSeparation
      rcases hzloc with ⟨z0, hz0, hMz0⟩
      apply zeroMultiplicityCount_pos_of_exists_zero
      · have hrhopos : 0 < zeroRadius p + 1 / 4 + (j : ℕ) * d := by
          have : 0 < zeroRadius p := by
            rw [← pStar.R0_value]
            have hl : (0 : ℝ) < (pStar.R0Name.lower : ℝ) := by
              exact_mod_cast pStar.R0Name.lower_pos
            exact hl.trans_le pStar.R0Name.lower_le_value
          positivity
        simpa [CertifiedReal.add, CertifiedReal.ofRat, pStar.R0_value, add_assoc,
          d, dQ, mStar, Ncert, Upsi, UR, psiI, R1I] using hrhopos
      · exact hMan.mono (by simp)
      · intro z hz
        have hnorm : ‖z‖ = zeroRadius p + 1 / 4 + (j : ℕ) * d := by
          simpa [CertifiedReal.add, CertifiedReal.ofRat, pStar.R0_value, add_assoc,
            d, dQ, mStar, Ncert, Upsi, UR, psiI, R1I,
            mem_sphere, dist_zero_right] using hz
        intro hzero
        have hzfac : z ∈ ball (0 : ℂ) Rfac := by
          rw [mem_ball_zero_iff]
          have hjR := rat_grid_lt_one (Ncert + 2) (j : ℕ)
            (Nat.le_of_lt_succ j.isLt)
          have hjR' : (1 / 4 : ℝ) + (j : ℕ) * d < 1 := by
            have hq : (1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
                (Ncert + 3) < 1 := by simpa [Nat.add_assoc] using hjR
            have hc : ((↑((1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
                (Ncert + 3)) : ℝ) < (↑(1 : ℚ) : ℝ)) := Rat.cast_lt.mpr hq
            simpa [d, dQ, mStar] using hc
          dsimp [Rfac, R1]
          rw [pStar.searchRadius_contract]
          linarith
        have hfactorz := hfactor z (ball_subset_closedBall hzfac)
        have hprod0 : blaschkeProduct Rfac a z * g z = 0 := hfactorz.symm.trans hzero
        have hBzero : blaschkeProduct Rfac a z = 0 :=
          (mul_eq_zero.mp hprod0).resolve_right (hgzero z hzfac)
        rw [blaschkeProduct, Finset.prod_eq_zero_iff] at hBzero
        obtain ⟨i, hi, hizero⟩ := hBzero
        have hza : z = a i :=
          (blaschkeFactor_eq_zero_iff Rfac (a i) z hRfac (ha i)
            (by simpa [mem_ball, dist_zero_right] using hzfac)).mp hizero
        have hsep := hjsep i
        rw [← hza, hnorm, sub_self, abs_zero] at hsep
        exact (not_lt_of_ge hsep) (by dsimp [h, d, dQ]; positivity)
      · refine ⟨z0, ?_, hMz0⟩
        rw [mem_ball_zero_iff]
        have hrho : zeroRadius p <
            (pStar.R0Name.name.add
              (CertifiedReal.ofRat
                (1 / 4 + (j : ℕ) * (1 / 2 : ℚ) ^
                  (4 * positiveCeil
                    (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
                    (positiveCeil
                      (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3)))).value := by
          simp [CertifiedReal.add, CertifiedReal.ofRat, pStar.R0_value]
          norm_num
          positivity
        exact hz0.trans_lt hrho
    · intro z hz
      have hnorm : ‖z‖ = zeroRadius p + 1 / 4 + (j : ℕ) * d := by
        simpa [bankCircle, CertifiedReal.add, CertifiedReal.ofRat,
          pStar.R0_value, add_assoc, d, dQ, mStar, Ncert, Upsi, UR,
          psiI, R1I, mem_sphere, dist_zero_right] using hz
      have hjR := rat_grid_lt_one (Ncert + 2) (j : ℕ)
        (Nat.le_of_lt_succ j.isLt)
      have hjR' : (1 / 4 : ℝ) + (j : ℕ) * d < 1 := by
        have hq : (1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
            (Ncert + 3) < 1 := by simpa [Nat.add_assoc] using hjR
        have hc : ((↑((1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
            (Ncert + 3)) : ℝ) < (↑(1 : ℚ) : ℝ)) := Rat.cast_lt.mpr hq
        simpa [d, dQ, mStar] using hc
      have hzR1 : ‖z‖ ≤ R1 := by
        rw [hnorm]
        dsimp [R1]
        rw [pStar.searchRadius_contract]
        linarith
      have hfupper : ∀ w ∈ sphere (0 : ℂ) Rfac,
          ‖M w‖ ≤ Real.exp (4 * p.psieta ^ 2 * Rfac ^ 2) := by
        intro w hw
        have hwnorm : ‖w‖ = Rfac := by
          simpa [mem_sphere, dist_zero_right, abs_of_pos hRfac] using hw
        simpa [M, hwnorm] using hMbound w
      have hlower := norm_lower_of_blaschke_factorization M g a Rfac R1
        (4 * p.psieta ^ 2 * Rfac ^ 2) hRfac hR1pos.le
        (by dsimp [Rfac]; linarith) ha
        (hgAn.mono ball_subset_closedBall) hgDiff hgzero hfactor hMzero hfupper z hzR1
      have hcoeff :
          (((Rfac + R1) / (Rfac - R1)) - 1) *
              (4 * p.psieta ^ 2 * Rfac ^ 2) =
            8 * p.psieta ^ 2 * R1 * (R1 + 1) ^ 2 := by
        dsimp [Rfac]
        ring
      have hnegcoeff :
          -(((Rfac + R1) / (Rfac - R1)) - 1) *
              (4 * p.psieta ^ 2 * Rfac ^ 2) =
            -(8 * p.psieta ^ 2 * R1 * (R1 + 1) ^ 2) := by
        rw [← hcoeff]
        ring
      rw [hnegcoeff] at hlower
      let eStar := 8 * UR * Upsi ^ 2 * (UR + 1) ^ 2
      let dStarDen := 3 * (2 * UR + 1)
      have hE : 8 * p.psieta ^ 2 * R1 * (R1 + 1) ^ 2 ≤ (eStar : ℝ) := by
        have hpsi0 : 0 ≤ p.psieta := p.constants_pos.2.2.2.1.le
        have hpsiSq : p.psieta ^ 2 ≤ (Upsi : ℝ) ^ 2 :=
          pow_le_pow_left₀ hpsi0 hpsi 2
        have hplus : R1 + 1 ≤ (UR : ℝ) + 1 := by linarith
        have hplusSq : (R1 + 1) ^ 2 ≤ ((UR : ℝ) + 1) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hplus 2
        calc
          8 * p.psieta ^ 2 * R1 * (R1 + 1) ^ 2 =
              8 * R1 * p.psieta ^ 2 * (R1 + 1) ^ 2 := by ring
          _ ≤ 8 * (UR : ℝ) * (Upsi : ℝ) ^ 2 * ((UR : ℝ) + 1) ^ 2 := by
            have hfirst : 8 * R1 ≤ 8 * (UR : ℝ) := by linarith
            have hsecond : 8 * R1 * p.psieta ^ 2 ≤
                8 * (UR : ℝ) * (Upsi : ℝ) ^ 2 :=
              mul_le_mul hfirst hpsiSq (sq_nonneg _) (by positivity)
            exact mul_le_mul hsecond hplusSq (sq_nonneg _) (by positivity)
          _ = (eStar : ℝ) := by
            dsimp [eStar]
            push_cast
            rfl
      have hexp : (1 / 2 : ℝ) ^ (2 * eStar) ≤
          Real.exp (-(8 * p.psieta ^ 2 * R1 * (R1 + 1) ^ 2)) := by
        refine (dyadic_two_mul_le_exp_neg eStar).trans ?_
        exact Real.exp_le_exp.mpr (neg_le_neg hE)
      have hdenpos : 0 < (2 * UR + 1 : ℝ) := by positivity
      have hfacEach (i : Fin N) :
          d / (dStarDen : ℕ) ≤ ‖blaschkeFactor Rfac (a i) z‖ := by
        have hsep := hjsep i
        have hrev : h ≤ ‖z - a i‖ := by
          have hr := abs_norm_sub_norm_le (a i) z
          rw [hnorm] at hr
          exact hsep.trans (by simpa [norm_sub_rev] using hr)
        have hden : Rfac + ‖z‖ ≤ (2 * UR + 1 : ℕ) := by
          have : Rfac + ‖z‖ ≤ 2 * R1 + 1 := by
            dsimp [Rfac]
            linarith
          have hR : 2 * R1 + 1 ≤ (2 * UR + 1 : ℕ) := by
            norm_num
            linarith
          exact this.trans hR
        have hfrac : h / (2 * UR + 1 : ℝ) ≤ ‖z - a i‖ / (Rfac + ‖z‖) :=
          div_le_div₀ (norm_nonneg _) hrev
            (by positivity) (by simpa using hden)
        have hzRfac : ‖z‖ ≤ Rfac := by
          exact hzR1.trans (by dsimp [Rfac]; linarith)
        have hfac := norm_blaschkeFactor_ge Rfac (a i) z hRfac (ha i)
          hzRfac
        calc
          d / (dStarDen : ℕ) = h / (2 * UR + 1 : ℝ) := by
            dsimp [h, dStarDen]
            push_cast
            field_simp
          _ ≤ ‖z - a i‖ / (Rfac + ‖z‖) := hfrac
          _ ≤ ‖blaschkeFactor Rfac (a i) z‖ := hfac
      have hprod : (d / (dStarDen : ℕ)) ^ N ≤ ‖blaschkeProduct Rfac a z‖ := by
        rw [blaschkeProduct, norm_prod]
        have hconst : (∏ _i : Fin N, (d / (dStarDen : ℕ))) =
            (d / (dStarDen : ℕ)) ^ N := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← hconst]
        exact Finset.prod_le_prod
          (fun _ _ ↦ by positivity) (fun i _ ↦ hfacEach i)
      have hDpos : 0 < dStarDen := by dsimp [dStarDen]; omega
      have hprodCert :
          (1 / 2 : ℝ) ^ (Ncert * (mStar + dStarDen)) ≤
            ‖blaschkeProduct Rfac a z‖ := by
        refine (dyadic_product_certificate mStar dStarDen N Ncert hDpos hNle).trans ?_
        simpa [d, dQ] using hprod
      have hcombined :
          (1 / 2 : ℝ) ^ (2 * eStar + Ncert * (mStar + dStarDen)) ≤
            Real.exp (-(8 * p.psieta ^ 2 * R1 * (R1 + 1) ^ 2)) *
              ‖blaschkeProduct Rfac a z‖ := by
        rw [pow_add]
        exact mul_le_mul hexp hprodCert (by positivity) (by positivity)
      have hfinal := hcombined.trans hlower
      simpa [eStar, dStarDen, M, d, dQ, mStar, Ncert, Upsi, UR,
        psiI, R1I] using hfinal

end CausalSmith.Stat.SaPlmCumulantConverse
