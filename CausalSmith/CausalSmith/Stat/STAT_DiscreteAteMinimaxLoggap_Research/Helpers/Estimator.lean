import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Basic
import Causalean.Stat.UStatistic.OrderM.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

-- @env: S4
variable (n d : ℕ)

/-- The balanced deterministic half-sample split. -/
def splitIndices (n : ℕ) (j : Fin 2) : Finset (Fin n) :=
  if j = 0 then Finset.univ.filter (fun i => i.1 < n / 2)
  else Finset.univ.filter (fun i => n / 2 ≤ i.1)
  -- @realizes I_0,I_1(first floor(n/2) indices and their complement)

def splitSize (n : ℕ) (j : Fin 2) : ℕ := (splitIndices n j).card

/-- Count of one `(k,a,y)` atom in a split. -/
def splitCellCount {n d : ℕ} (sample : Fin n → Obs d) (j : Fin 2)
    (k : Fin d) (a y : Fin 2) : ℕ :=
  ((splitIndices n j).filter
    (fun i => sample i = (k, finTwoEquiv a, finTwoEquiv y))).card
  -- @realizes N^{(j)}_{aky}(split cell count in Nat)

def splitCategoryCount {n d : ℕ} (sample : Fin n → Obs d) (j : Fin 2)
    (k : Fin d) : ℕ :=
  ((splitIndices n j).filter (fun i => (sample i).1 = k)).card

/-- A four-cell exponent vector. -/
abbrev MultiIndex := Cell →₀ ℕ
  -- @realizes r=(r_{ay})_{a,y\in\{0,1\}}(four-coordinate Nat multi-index)

def multiDegree (r : MultiIndex) : ℕ := r.sum fun _ e => e

/-- Falling factorial, reusing Mathlib's `Nat.descFactorial`. -/
def fallingFactorial (z r : ℕ) : ℕ := z.descFactorial r
  -- @realizes z_r(z descending factorial r; z_0=1)

noncomputable def logScale (n : ℕ) : ℝ := Real.log (Real.exp 1 * n)

def calibrationA : ℕ := 6
def lambda0 : ℕ := 256
def b0 : ℕ := 4096

noncomputable def dA : ℝ := 8 * Real.log (27 / 4)

noncomputable def alpha0 : ℝ :=
  min 1 (min (1 / (32 * Real.log 6)) (1 / (256 * dA)))

noncomputable def polynomialDegree (n : ℕ) : ℕ :=
  max 2 (Int.toNat ⌊alpha0 * logScale n⌋)

/-- Defines bandwidth, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def bandwidth (n : ℕ) : ℝ :=
  b0 * logScale n / splitSize n 1

/-- Defines cutoff Property, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def cutoffProperty (N : ℕ) : Prop :=
  ∀ n ≥ N,
    2 ≤ alpha0 * logScale n ∧
    4 * polynomialDegree n ^ 2 ≤ splitSize n 1 ∧
    4 * polynomialDegree n / (splitSize n 1 : ℝ) ≤ 3 * bandwidth n / 4

/-- Establishes the stated property of cutoff Property eventually in the discrete average-treatment-effect construction. -/
lemma cutoffProperty_eventually : ∃ N, cutoffProperty N := by
  have ha0 : 0 < alpha0 := by
    unfold alpha0 dA
    have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have ha1 : alpha0 ≤ 1 := by simp [alpha0]
  have hlogSmall : ∀ᶠ n : ℕ in Filter.atTop,
      |Real.log (n : ℝ) ^ 2| ≤ (1 / 64 : ℝ) * |(n : ℝ)| := by
    have hreal := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
      (by norm_num : (0 : ℝ) < 1 / 64)
    exact tendsto_natCast_atTop_atTop.eventually hreal
  have hlogLarge : ∀ᶠ n : ℕ in Filter.atTop,
      2 / alpha0 ≤ Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (2 / alpha0))
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      256 ≤ n ∧ |Real.log (n : ℝ) ^ 2| ≤ (1 / 64 : ℝ) * |(n : ℝ)| ∧
        2 / alpha0 ≤ Real.log (n : ℝ) :=
    Filter.Eventually.and (Filter.eventually_ge_atTop 256) (hlogSmall.and hlogLarge)
  rw [Filter.eventually_atTop] at hall
  obtain ⟨N, hN⟩ := hall
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨hn256, hlogSq, hlogLarge⟩
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn256
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hscale : logScale n = 1 + Real.log (n : ℝ) := by
    rw [logScale, Real.log_mul (by positivity : Real.exp 1 ≠ 0)
      (by positivity : (n : ℝ) ≠ 0)]
    simp
  have hscale_pos : 0 < logScale n := by rw [hscale]; positivity
  have hfirst : 2 ≤ alpha0 * logScale n := by
    rw [hscale]
    have := (div_le_iff₀' ha0).mp hlogLarge
    nlinarith
  have hdeg_cast : (polynomialDegree n : ℝ) ≤ logScale n := by
    have hfloor2 : (2 : ℤ) ≤ ⌊alpha0 * logScale n⌋ := by
      rw [Int.le_floor]
      exact_mod_cast hfirst
    have hmax : polynomialDegree n = Int.toNat ⌊alpha0 * logScale n⌋ := by
      rw [polynomialDegree, max_eq_right]
      exact Int.toNat_le_toNat hfloor2
    rw [hmax]
    have hfloor_nonneg : 0 ≤ ⌊alpha0 * logScale n⌋ := le_trans (by norm_num) hfloor2
    have hcast : ((Int.toNat ⌊alpha0 * logScale n⌋ : ℕ) : ℝ) =
        ((⌊alpha0 * logScale n⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
    rw [hcast]
    have hf := Int.floor_le (alpha0 * logScale n)
    exact le_trans hf
      (mul_le_of_le_one_left (le_of_lt hscale_pos) ha1)
  have hsize : splitSize n 1 = n - n / 2 := by
    unfold splitSize splitIndices
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => i.1 < n / 2)
    have hfirstCard : ((Finset.univ : Finset (Fin n)).filter
        (fun i => i.1 < n / 2)).card = n / 2 := by
      simpa [Fin.card_filter_val_lt, Nat.min_eq_right (Nat.div_le_self n 2)]
    have hc' : n / 2 + ((Finset.univ : Finset (Fin n)).filter
        (fun i => n / 2 ≤ i.1)).card = n := by
      simpa only [not_lt, hfirstCard, Finset.card_univ, Fintype.card_fin] using hc
    omega
  have hhalf : (n : ℝ) / 2 ≤ (splitSize n 1 : ℝ) := by
    have hnsize : n ≤ 2 * splitSize n 1 := by rw [hsize]; omega
    have hnsizeR : (n : ℝ) ≤ 2 * (splitSize n 1 : ℝ) := by
      exact_mod_cast hnsize
    linarith
  have hlogSq' : Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) / 64 := by
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)] at hlogSq
    norm_num [div_eq_mul_inv] at hlogSq ⊢
    simpa [mul_comm] using hlogSq
  have hdegSq : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1 := by
    have hreal : (4 : ℝ) * (polynomialDegree n : ℝ) ^ 2 ≤
        (splitSize n 1 : ℝ) := by
      rw [hscale] at hdeg_cast
      have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn256
      nlinarith [sq_nonneg ((polynomialDegree n : ℝ) -
        (1 + Real.log (n : ℝ)))]
    exact_mod_cast hreal
  refine ⟨hfirst, hdegSq, ?_⟩
  have hsize_pos : 0 < (splitSize n 1 : ℝ) :=
    lt_of_lt_of_le (by positivity) hhalf
  rw [bandwidth]
  rw [show 3 * ((b0 : ℝ) * logScale n / (splitSize n 1 : ℝ)) / 4 =
      3072 * logScale n / (splitSize n 1 : ℝ) by
    rw [b0]
    field_simp
    ring]
  apply (div_le_div_iff_of_pos_right hsize_pos).2
  nlinarith [hdeg_cast]

/-- Least numerical cutoff satisfying the three calibration inequalities. -/
noncomputable def calibrationCutoff : ℕ := by
  classical
  exact Nat.find cutoffProperty_eventually

/-- Coefficient of the explicit polynomial continuation `G_M`. -/
noncomputable def gCoefficient (M j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * 2 ^ (2 * j + 3) /
    ((M : ℝ) * (M + j + 2)) * Nat.choose (M + j + 2) (2 * j + 4)

/-- Explicit closed polynomial continuation of `G_M`. -/
noncomputable def gPolynomial (M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M - 1), gCoefficient M j * x ^ j

noncomputable def mvArmMass (a : Fin 2) : MvPolynomial Cell ℝ :=
  MvPolynomial.X (a, 0) + MvPolynomial.X (a, 1)

noncomputable def mvMass : MvPolynomial Cell ℝ := mvArmMass 0 + mvArmMass 1

/-- The multivariate polynomial `P_{M,B}` whose coefficients are factorial-lifted. -/
noncomputable def cellApproxPolynomial (M : ℕ) (B : ℝ) : MvPolynomial Cell ℝ :=
  let evalG (s : MvPolynomial Cell ℝ) :=
    ∑ j ∈ Finset.range (M - 1),
      MvPolynomial.C (gCoefficient M j) * (MvPolynomial.C B⁻¹ * s) ^ j
  MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (1, 1) * evalG (mvArmMass 1) -
    MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (0, 1) * evalG (mvArmMass 0)

noncomputable def factorialMonomial {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (r : MultiIndex) : ℝ :=
  (∏ ay : Cell,
      (fallingFactorial (splitCellCount sample 1 k ay.1 ay.2) (r ay) : ℝ)) /
    (fallingFactorial (splitSize n 1) (multiDegree r) : ℝ)

/-- Merged exponent vector in the sparse binomial expansion of one arm of
`cellApproxPolynomial`. -/
noncomputable def factorialExpansionIndex (a : Fin 2) (ay : Cell) (j t : ℕ) : MultiIndex :=
  Finsupp.single ay 1 + Finsupp.single (a, 1) 1 +
    Finsupp.single (a, 0) t + Finsupp.single (a, 1) (j - t)

/-- Factorial-moment lift of the light-cell approximation polynomial, written
in its sparse arm/binomial expansion.  Keeping duplicate displayed monomials
is intentional: linearity collects them to the coefficient-support form. -/
noncomputable def factorialPolynomialContribution {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) : ℝ :=
  let M := polynomialDegree n
  let B := bandwidth n
  let arm (a : Fin 2) :=
    ∑ j ∈ Finset.range (M - 1), ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
      (B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ)) *
        factorialMonomial sample k (factorialExpansionIndex a ay j t)
  arm 1 - arm 0

/-- Pilot-heavy cells; below the cutoff every category uses the ratio branch. -/
-- @realizes \(\widehat{\mathcal H}_n,\widehat{\mathcal L}_n\)(pilot-heavy side; all cells below the cutoff)
noncomputable def heavyCells {n d : ℕ} (sample : Fin n → Obs d) : Finset (Fin d) :=
  if n < calibrationCutoff then Finset.univ else
    Finset.univ.filter
      (fun k => (lambda0 : ℝ) * logScale n < splitCategoryCount sample 0 k)

/-- Pilot-light cells; below the cutoff this is empty as stipulated in the note. -/
-- @realizes \(\widehat{\mathcal H}_n,\widehat{\mathcal L}_n\)(light side is the heavy-set complement)
noncomputable def lightCells {n d : ℕ} (sample : Fin n → Obs d) : Finset (Fin d) :=
  if n < calibrationCutoff then ∅ else (heavyCells sample)ᶜ

-- @realizes \(\widehat{\mathcal H}_n,\widehat{\mathcal L}_n\)(above the cutoff, heavy means pilot count exceeds lambda0 log(en))
lemma heavyCells_eq_filter_of_cutoff_le {n d : ℕ} (sample : Fin n → Obs d)
    (h : calibrationCutoff ≤ n) :
    heavyCells sample = Finset.univ.filter
      (fun k => (lambda0 : ℝ) * logScale n < splitCategoryCount sample 0 k) := by
  simp [heavyCells, Nat.not_lt.mpr h]

-- @realizes \(\widehat{\mathcal H}_n,\widehat{\mathcal L}_n\)(below the cutoff, every cell uses the heavy ratio branch)
lemma heavyCells_eq_univ_of_lt_cutoff {n d : ℕ} (sample : Fin n → Obs d)
    (h : n < calibrationCutoff) : heavyCells sample = Finset.univ := by
  simp [heavyCells, h]

-- @realizes \(\widehat{\mathcal H}_n,\widehat{\mathcal L}_n\)(below the cutoff, the light set is empty)
/-- Establishes the stated equality relating light Cells eq empty of lt cutoff. -/
lemma lightCells_eq_empty_of_lt_cutoff {n d : ℕ} (sample : Fin n → Obs d)
    (h : n < calibrationCutoff) : lightCells sample = ∅ := by
  simp [lightCells, h]

-- @realizes \(\widehat{\mathcal H}_n,\widehat{\mathcal L}_n\)(data-dependent partition of Fin d)
/-- Establishes the stated equality relating light Cells eq compl. -/
lemma lightCells_eq_compl {n d : ℕ} (sample : Fin n → Obs d) :
    lightCells sample = (heavyCells sample)ᶜ := by
  by_cases h : n < calibrationCutoff
  · simp [lightCells, heavyCells, h]
  · simp [lightCells, h]

/-- Defines empirical Ratio Cell, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def empiricalRatioCell {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) : ℝ :=
  let Nk := splitCategoryCount sample 1 k
  let N1 := splitCellCount sample 1 k 1 0 + splitCellCount sample 1 k 1 1
  let N0 := splitCellCount sample 1 k 0 0 + splitCellCount sample 1 k 0 1
  (Nk : ℝ) / splitSize n 1 *
    ((splitCellCount sample 1 k 1 1 : ℝ) / N1 -
      (splitCellCount sample 1 k 0 1 : ℝ) / N0)

/-- Defines heavy Contribution, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def heavyContribution {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  ∑ k ∈ heavyCells sample, empiricalRatioCell sample k

/-- Defines light Contribution, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def lightContribution {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  ∑ k ∈ lightCells sample, factorialPolynomialContribution sample k
  -- @realizes \widehat T_{\mathcal L}(sum of factorial-polynomial light contributions)

/-- Universally calibrated balanced ratio-polynomial hybrid, truncated to `[-1,1]`.
Its type has no overlap parameter: overlap adaptation is structural. -/
-- @node: def:hybrid-estimator-handle
noncomputable def hybridEstimator {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  max (-1) (min 1 (heavyContribution sample + lightContribution sample))
  -- @realizes \widehat\tau_n^{\mathrm{hyb}}(epsilon-free truncated hybrid estimator)

/-- Inputs available to the arithmetic realization: the eight split counts for
each category.  All dependence of the hybrid on the observed sample factors
through this finite vector. -/
abbrev HybridCountInput (d : ℕ) := Fin 2 × Fin d × Fin 2 × Fin 2

def hybridCountVector {n d : ℕ} (sample : Fin n → Obs d) :
    HybridCountInput d → ℝ :=
  fun i => (splitCellCount sample i.1 i.2.1 i.2.2.1 i.2.2.2 : ℝ)

/-- One instruction in a straight-line real-arithmetic program.  Natural
numbers address previously computed registers, allowing factorials and powers
to be computed once and shared across all polynomial monomials. -/
inductive RealArithmeticInstruction (ι : Type*) where
  | input (i : ι)
  | const (x : ℝ)
  | add (x y : ℕ)
  | sub (x y : ℕ)
  | mul (x y : ℕ)
  | div (x y : ℕ)
  | branchNonpos (test yes no : ℕ)

/-- A finite instruction list paired with its designated output register. -/
abbrev RealArithmeticProgram (ι : Type*) := List (RealArithmeticInstruction ι) × ℕ

namespace RealArithmeticProgram

noncomputable def instructionValue {ι : Type*} (input : ι → ℝ)
    (registers : List ℝ) : RealArithmeticInstruction ι → ℝ
  | .input i => input i
  | .const x => x
  | .add x y => registers.getD x 0 + registers.getD y 0
  | .sub x y => registers.getD x 0 - registers.getD y 0
  | .mul x y => registers.getD x 0 * registers.getD y 0
  | .div x y => registers.getD x 0 / registers.getD y 0
  | .branchNonpos test yes no =>
      if registers.getD test 0 ≤ 0 then registers.getD yes 0 else registers.getD no 0

noncomputable def run {ι : Type*} (input : ι → ℝ)
    (code : List (RealArithmeticInstruction ι)) : List ℝ :=
  code.foldl (fun registers instruction =>
    registers ++ [instructionValue input registers instruction]) []

noncomputable def eval {ι : Type*} (program : RealArithmeticProgram ι)
    (input : ι → ℝ) : ℝ :=
  (run input program.1).getD program.2 0

def instructionCost {ι : Type*} : RealArithmeticInstruction ι → ℕ
  | .input _ | .const _ => 0
  | .add _ _ | .sub _ _ | .mul _ _ | .div _ _ | .branchNonpos _ _ _ => 1

def operationCount {ι : Type*} (program : RealArithmeticProgram ι) : ℕ :=
  (program.1.map instructionCost).sum

end RealArithmeticProgram

/-- Clause (i)'s computability assertion, in the real-arithmetic model used in
the note.  A universal operation-count constant works for every `n,d`; the
program reads only split counts, returns the stated hybrid exactly, and has
`O(d M(n)^4)` arithmetic/comparison operations. -/
def HybridEstimatorComputable : Prop :=
  ∃ K : ℕ, 0 < K ∧
    ∀ n d : ℕ, ∃ program : RealArithmeticProgram (HybridCountInput d),
      program.operationCount ≤ K * d * polynomialDegree n ^ 4 ∧
      ∀ sample : Fin n → Obs d,
        program.eval (hybridCountVector sample) = hybridEstimator sample

noncomputable def centeredEstimator {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n,
    2 * (if (sample i).2.1 then 1 else -1) *
      ((if (sample i).2.2 then 1 else 0) - 1 / 2)

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
