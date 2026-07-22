import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellAssembly

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open scoped BigOperators

/-- Absolute sparse coefficient sum for one arm of the factorial lift. -/
noncomputable def sparseArmEnvelope (M : ℕ) (B : ℝ)
    (v : Cell → ℝ) (a : Fin 2) : ℝ :=
  ∑ j ∈ Finset.range (M - 1), ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
    |B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ)| *
      (factorialExpansionIndex a ay j t).prod (fun ay' e => v ay' ^ e)

-- @node: sparseArmEnvelope_eq
lemma sparseArmEnvelope_eq {M : ℕ} {B : ℝ} (hB : 0 < B)
    (v : Cell → ℝ) (hv : ∀ ay, 0 ≤ v ay) (a : Fin 2) :
    sparseArmEnvelope M B v a =
      B⁻¹ * (∑ ay : Cell, v ay) * v (a, 1) *
        gpos M ((v (a, 0) + v (a, 1)) / B) := by
  classical
  unfold sparseArmEnvelope gpos
  have hBinv : 0 ≤ B⁻¹ := (inv_pos.mpr hB).le
  have hchoose (j t : ℕ) : 0 ≤ (Nat.choose j t : ℝ) := by positivity
  rw [show B⁻¹ * (∑ ay : Cell, v ay) * v (a, 1) *
      ∑ j ∈ Finset.range (M - 1),
        |gCoefficient M j| * ((v (a, 0) + v (a, 1)) / B) ^ j =
      ∑ j ∈ Finset.range (M - 1),
        B⁻¹ * |gCoefficient M j| * B⁻¹ ^ j *
          ((∑ ay : Cell, v ay) * v (a, 1) *
            (v (a, 0) + v (a, 1)) ^ j) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [div_pow]
    ring]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show (∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
      |B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ)| *
        (factorialExpansionIndex a ay j t).prod
          (fun ay' e => v ay' ^ e)) =
      B⁻¹ * |gCoefficient M j| * B⁻¹ ^ j *
        ((∑ ay : Cell, v ay) * v (a, 1) *
          (v (a, 0) + v (a, 1)) ^ j) by
    rw [show (∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
        |B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ)| *
          (factorialExpansionIndex a ay j t).prod
            (fun ay' e => v ay' ^ e)) =
        (B⁻¹ * |gCoefficient M j| * B⁻¹ ^ j) *
          (∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
            (Nat.choose j t : ℝ) *
              (factorialExpansionIndex a ay j t).prod
                (fun ay' e => v ay' ^ e)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ay _hay
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hBinv,
        abs_of_nonneg (pow_nonneg hBinv j), abs_of_nonneg (hchoose j t)]
      ring]
    rw [factorialExpansionIndex_binomial_sum]]

-- @node: sparseArmEnvelope_le
/-- Establishes the stated upper bound for sparse Arm Envelope le. -/
lemma sparseArmEnvelope_le {M : ℕ} (hM : 0 < M) {B : ℝ}
    (hB : 0 < B) (v : Cell → ℝ) (hv : ∀ ay, 0 ≤ v ay)
    (hR : (∑ ay : Cell, v ay) ≤ B) (a : Fin 2) :
    sparseArmEnvelope M B v a ≤ B * 6 ^ M := by
  rw [sparseArmEnvelope_eq hB v hv a]
  let R := ∑ ay : Cell, v ay
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun ay _ => hv ay
  have harm0 : 0 ≤ v (a, 0) + v (a, 1) := add_nonneg (hv _) (hv _)
  have harmR : v (a, 0) + v (a, 1) ≤ R := by
    rcases a with ⟨a, ha⟩
    interval_cases a <;>
      simp [R, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      linarith [hv (0, 0), hv (0, 1), hv (1, 0), hv (1, 1)]
  have hz0 : 0 ≤ (v (a, 0) + v (a, 1)) / B :=
    div_nonneg harm0 hB.le
  have hz1 : (v (a, 0) + v (a, 1)) / B ≤ 1 :=
    (div_le_one hB).2 (harmR.trans hR)
  have hpow : ((v (a, 0) + v (a, 1)) / B) ^ (M - 2) ≤ 1 :=
    pow_le_one₀ hz0 hz1
  have hg : gpos M ((v (a, 0) + v (a, 1)) / B) ≤ 6 ^ M := by
    refine (gpos_bound hM hz0).trans ?_
    rw [max_eq_left (by simpa using hpow)]
    simp
  have hvaR : v (a, 1) ≤ R := (le_add_of_nonneg_left (hv (a, 0))).trans harmR
  have hbinv : 0 ≤ B⁻¹ := (inv_pos.mpr hB).le
  have hgp0 := gpos_nonneg M hz0
  calc
    B⁻¹ * R * v (a, 1) * gpos M ((v (a, 0) + v (a, 1)) / B)
        ≤ B⁻¹ * R * R * 6 ^ M := by gcongr
    _ ≤ B * 6 ^ M := by
      have hsq : R * R ≤ B * B := mul_self_le_mul_self hR0 hR
      calc
        B⁻¹ * R * R * 6 ^ M = B⁻¹ * (R * R) * 6 ^ M := by ring
        _ ≤ B⁻¹ * (B * B) * 6 ^ M := by gcongr
        _ = B * 6 ^ M := by field_simp

-- @node: multiMonomial_mono
/-- Establishes the stated property of multi Monomial mono in the discrete average-treatment-effect construction. -/
lemma multiMonomial_mono (r : MultiIndex) (v w : Cell → ℝ)
    (hv : ∀ ay, 0 ≤ v ay) (hle : ∀ ay, v ay ≤ w ay) :
    r.prod (fun ay e => v ay ^ e) ≤ r.prod (fun ay e => w ay ^ e) := by
  classical
  rw [r.prod_fintype _ (fun _ => pow_zero _),
    r.prod_fintype _ (fun _ => pow_zero _)]
  apply Finset.prod_le_prod
  · intro ay _hay
    exact pow_nonneg (hv ay) _
  · intro ay _hay
    exact pow_le_pow_left₀ (hv ay) (hle ay) _

/-- Shows that multi Monomial nonneg is nonnegative. -/
lemma multiMonomial_nonneg (r : MultiIndex) (v : Cell → ℝ)
    (hv : ∀ ay, 0 ≤ v ay) :
    0 ≤ r.prod (fun ay e => v ay ^ e) := by
  classical
  rw [r.prod_fintype _ (fun _ => pow_zero _)]
  exact Finset.prod_nonneg fun ay _ => pow_nonneg (hv ay) _

-- @node: integral_factorialMonomial_mul_shift_le
/-- Evaluates or bounds the stated integral involving integral factorial Monomial mul shift le. -/
lemma integral_factorialMonomial_mul_shift_le {n d M : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (r s : MultiIndex)
    (hn : 0 < splitSize n 1) (hr : multiDegree r ≤ M)
    (hs : multiDegree s ≤ M) (hsize : 4 * M ^ 2 ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) k s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      Real.exp 1 *
        (r.prod fun ay e =>
          (cellVector P k ay + (M : ℝ) / splitSize n 1) ^ e) *
        (s.prod fun ay e =>
          (cellVector P k ay + (M : ℝ) / splitSize n 1) ^ e) := by
  have hv (ay : Cell) : 0 ≤ cellVector P k ay :=
    (cellVector_mem_unitCube P k ay).1
  have hmpos : 0 < (splitSize n 1 : ℝ) := by exact_mod_cast hn
  have hshift0 : 0 ≤ (M : ℝ) / splitSize n 1 :=
    div_nonneg (by positivity) hmpos.le
  have hle (ay : Cell) : cellVector P k ay ≤
      cellVector P k ay + (M : ℝ) / splitSize n 1 := by linarith
  have hshiftMono (u : MultiIndex) (q : ℕ) (hq : q ≤ M) :
      u.prod (fun ay e =>
          (cellVector P k ay + (q : ℝ) / splitSize n 1) ^ e) ≤
        u.prod (fun ay e =>
          (cellVector P k ay + (M : ℝ) / splitSize n 1) ^ e) := by
    apply multiMonomial_mono u
    · intro ay
      exact add_nonneg (hv ay) (div_nonneg (by positivity) hmpos.le)
    · intro ay
      have hqR : (q : ℝ) ≤ M := by exact_mod_cast hq
      have hdiv := div_le_div_of_nonneg_right hqR hmpos.le
      linarith
  have hsizeR : 4 * (multiDegree r) ^ 2 ≤ splitSize n 1 := by
    nlinarith [Nat.mul_self_le_mul_self hr]
  have hsizeS : 4 * (multiDegree s) ^ 2 ≤ splitSize n 1 := by
    nlinarith [Nat.mul_self_le_mul_self hs]
  by_cases hrs : multiDegree r ≤ multiDegree s
  · have hmoment := integral_factorialMonomial_mul_trunc_le P k r s hn hrs hsizeS
    rw [← r.prod_fintype _ (fun _ => pow_zero _),
      ← s.prod_fintype _ (fun _ => pow_zero _)] at hmoment
    refine hmoment.trans ?_
    have hrmono := multiMonomial_mono r (cellVector P k)
      (fun ay => cellVector P k ay + (M : ℝ) / splitSize n 1) hv hle
    have hsdeg := hshiftMono s (multiDegree s) hs
    have hsold0 := multiMonomial_nonneg s
      (fun ay => cellVector P k ay + (multiDegree s : ℝ) / splitSize n 1)
      (fun ay => add_nonneg (hv ay) (div_nonneg (by positivity) hmpos.le))
    have hsnew0 := multiMonomial_nonneg s
      (fun ay => cellVector P k ay + (M : ℝ) / splitSize n 1)
      (fun ay => add_nonneg (hv ay) hshift0)
    calc
      Real.exp 1 * (r.prod fun ay e => cellVector P k ay ^ e) *
          (s.prod fun ay e =>
            (cellVector P k ay + (multiDegree s : ℝ) / splitSize n 1) ^ e) ≤
        Real.exp 1 *
          (r.prod fun ay e =>
            (cellVector P k ay + (M : ℝ) / splitSize n 1) ^ e) *
          (s.prod fun ay e =>
            (cellVector P k ay + (multiDegree s : ℝ) / splitSize n 1) ^ e) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrmono (Real.exp_pos 1).le) hsold0
      _ ≤ _ := mul_le_mul_of_nonneg_left hsdeg
          (mul_nonneg (Real.exp_pos 1).le
          (multiMonomial_nonneg r _ (fun ay => add_nonneg (hv ay) hshift0)))
  · have hsr : multiDegree s ≤ multiDegree r := Nat.le_of_not_ge hrs
    rw [show (fun ω : ℕ → Obs d =>
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) k s) =
        (fun ω : ℕ → Obs d =>
          factorialMonomial (fun i : Fin n => ω i) k s *
            factorialMonomial (fun i : Fin n => ω i) k r) by
      funext ω
      ring]
    have hmoment := integral_factorialMonomial_mul_trunc_le P k s r hn hsr hsizeR
    rw [← s.prod_fintype _ (fun _ => pow_zero _),
      ← r.prod_fintype _ (fun _ => pow_zero _)] at hmoment
    refine hmoment.trans ?_
    have hsmono := multiMonomial_mono s (cellVector P k)
      (fun ay => cellVector P k ay + (M : ℝ) / splitSize n 1) hv hle
    have hrdeg := hshiftMono r (multiDegree r) hr
    have hrold0 := multiMonomial_nonneg r
      (fun ay => cellVector P k ay + (multiDegree r : ℝ) / splitSize n 1)
      (fun ay => add_nonneg (hv ay) (div_nonneg (by positivity) hmpos.le))
    have hrnew0 := multiMonomial_nonneg r
      (fun ay => cellVector P k ay + (M : ℝ) / splitSize n 1)
      (fun ay => add_nonneg (hv ay) hshift0)
    calc
      Real.exp 1 * (s.prod fun ay e => (cellVector P k ay) ^ e) *
          (r.prod fun ay e =>
            (cellVector P k ay + (multiDegree r : ℝ) / splitSize n 1) ^ e) ≤
        Real.exp 1 *
          (s.prod fun ay e =>
            (cellVector P k ay + (M : ℝ) / splitSize n 1) ^ e) *
          (r.prod fun ay e =>
            (cellVector P k ay + (multiDegree r : ℝ) / splitSize n 1) ^ e) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsmono (Real.exp_pos 1).le) hrold0
      _ ≤ Real.exp 1 *
          (s.prod fun ay e =>
            (cellVector P k ay + (M : ℝ) / splitSize n 1) ^ e) *
          (r.prod fun ay e =>
            (cellVector P k ay + (M : ℝ) / splitSize n 1) ^ e) :=
        mul_le_mul_of_nonneg_left hrdeg
          (mul_nonneg (Real.exp_pos 1).le
            (multiMonomial_nonneg s _ (fun ay => add_nonneg (hv ay) hshift0)))
      _ = _ := by ring

/-- Defines sparse Coefficient, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def sparseCoefficient (M : ℕ) (B : ℝ) (j t : ℕ) : ℝ :=
  B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ)

/-- Defines sparse Arm Contribution, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def sparseArmContribution {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) (a : Fin 2) : ℝ :=
  ∑ j ∈ Finset.range (polynomialDegree n - 1),
    ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
      sparseCoefficient (polynomialDegree n) (bandwidth n) j t *
        factorialMonomial sample k (factorialExpansionIndex a ay j t)

/-- Establishes the stated equality relating factorial Polynomial Contribution eq sparse Arms. -/
lemma factorialPolynomialContribution_eq_sparseArms {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) :
    factorialPolynomialContribution sample k =
      sparseArmContribution sample k 1 - sparseArmContribution sample k 0 := by
  rfl

/-- Defines shifted Cell Vector, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def shiftedCellVector {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (M m : ℕ) : Cell → ℝ :=
  fun ay => cellVector P k ay + (M : ℝ) / m

/-- Shows that shifted Cell Vector nonneg is nonnegative. -/
lemma shiftedCellVector_nonneg {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (M m : ℕ) (ay : Cell) :
    0 ≤ shiftedCellVector P k M m ay := by
  exact add_nonneg (cellVector_mem_unitCube P k ay).1 (by positivity)

/-- Establishes the stated summation identity or bound for shifted Cell Vector sum. -/
lemma shiftedCellVector_sum {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (M m : ℕ) :
    ∑ ay : Cell, shiftedCellVector P k M m ay =
      cellMass P k + 4 * (M : ℝ) / m := by
  have hm := vectorMass_cellVector P k
  simp [vectorMass, vectorArmMass] at hm
  simp [shiftedCellVector, Finset.sum_add_distrib,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← hm]
  ring

/-- Shows that factorial Monomial nonneg is nonnegative. -/
lemma factorialMonomial_nonneg {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (r : MultiIndex) : 0 ≤ factorialMonomial sample k r := by
  unfold factorialMonomial
  positivity

-- @node: integral_sparse_terms_mul_shift_le
/-- Evaluates or bounds the stated integral involving integral sparse terms mul shift le. -/
lemma integral_sparse_terms_mul_shift_le {n d M : ℕ} {B : ℝ}
    (P : DiscreteLaw d) (k : Fin d) (a b : Fin 2)
    (j t j' t' : ℕ) (ay ay' : Cell)
    (ht : t ≤ j) (ht' : t' ≤ j')
    (hj : j + 2 ≤ M) (hj' : j' + 2 ≤ M)
    (hn : 0 < splitSize n 1) (hsize : 4 * M ^ 2 ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d,
        (sparseCoefficient M B j t *
          factorialMonomial (fun i : Fin n => ω i) k
            (factorialExpansionIndex a ay j t)) *
        (sparseCoefficient M B j' t' *
          factorialMonomial (fun i : Fin n => ω i) k
            (factorialExpansionIndex b ay' j' t'))
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      Real.exp 1 *
        (|sparseCoefficient M B j t| *
          (factorialExpansionIndex a ay j t).prod (fun cy e =>
            (cellVector P k cy + (M : ℝ) / splitSize n 1) ^ e)) *
        (|sparseCoefficient M B j' t'| *
          (factorialExpansionIndex b ay' j' t').prod (fun cy e =>
            (cellVector P k cy + (M : ℝ) / splitSize n 1) ^ e)) := by
  let r := factorialExpansionIndex a ay j t
  let s := factorialExpansionIndex b ay' j' t'
  let c := sparseCoefficient M B j t
  let c' := sparseCoefficient M B j' t'
  have hr : multiDegree r ≤ M := by
    dsimp only [r]
    rw [multiDegree_factorialExpansionIndex a ay j t ht]
    exact hj
  have hs : multiDegree s ≤ M := by
    dsimp only [s]
    rw [multiDegree_factorialExpansionIndex b ay' j' t' ht']
    exact hj'
  have hprodInt := integrable_factorialMonomial_mul_trunc (n := n) P k r s
  have hI0 : 0 ≤ ∫ ω : ℕ → Obs d,
      factorialMonomial (fun i : Fin n => ω i) k r *
        factorialMonomial (fun i : Fin n => ω i) k s
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integral_nonneg_of_ae
    filter_upwards with ω
    exact mul_nonneg (factorialMonomial_nonneg _ _ _)
      (factorialMonomial_nonneg _ _ _)
  have hmoment := integral_factorialMonomial_mul_shift_le
    P k r s hn hr hs hsize
  have hcc : c * c' ≤ |c| * |c'| := by
    rw [← abs_mul]
    exact le_abs_self _
  rw [show (fun ω : ℕ → Obs d =>
      (c * factorialMonomial (fun i : Fin n => ω i) k r) *
        (c' * factorialMonomial (fun i : Fin n => ω i) k s)) =
      (fun ω : ℕ → Obs d => c * c' *
        (factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) k s)) by
    funext ω
    ring,
    integral_const_mul]
  dsimp only [c, c', r, s] at hI0 hmoment hcc ⊢
  calc
    sparseCoefficient M B j t * sparseCoefficient M B j' t' *
        ∫ ω : ℕ → Obs d,
          factorialMonomial (fun i : Fin n => ω i) k
              (factorialExpansionIndex a ay j t) *
            factorialMonomial (fun i : Fin n => ω i) k
              (factorialExpansionIndex b ay' j' t')
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      |sparseCoefficient M B j t| * |sparseCoefficient M B j' t'| *
        ∫ ω : ℕ → Obs d,
          factorialMonomial (fun i : Fin n => ω i) k
              (factorialExpansionIndex a ay j t) *
            factorialMonomial (fun i : Fin n => ω i) k
              (factorialExpansionIndex b ay' j' t')
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
        mul_le_mul_of_nonneg_right hcc hI0
    _ ≤ |sparseCoefficient M B j t| * |sparseCoefficient M B j' t'| *
        (Real.exp 1 *
          (factorialExpansionIndex a ay j t).prod (fun cy e =>
            (cellVector P k cy + (M : ℝ) / splitSize n 1) ^ e) *
          (factorialExpansionIndex b ay' j' t').prod (fun cy e =>
            (cellVector P k cy + (M : ℝ) / splitSize n 1) ^ e)) :=
      mul_le_mul_of_nonneg_left hmoment (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

-- @node: factorialMonomial_cross_covariance_le
/-- Establishes the stated upper bound for factorial Monomial cross covariance le. -/
lemma factorialMonomial_cross_covariance_le {n d M : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) (hkl : k ≠ l)
    (r s : MultiIndex) (hr : multiDegree r ≤ M)
    (hs : multiDegree s ≤ M) (hsize : 4 * M ^ 2 ≤ splitSize n 1) :
    |∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) l s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) -
      (r.prod fun ay e => (cellVector P k ay) ^ e) *
        (s.prod fun ay e => (cellVector P l ay) ^ e)| ≤
      (2 * (M : ℝ) ^ 2 / splitSize n 1) *
        (r.prod fun ay e => (cellVector P k ay) ^ e) *
        (s.prod fun ay e => (cellVector P l ay) ^ e) := by
  rw [integral_factorialMonomial_cross_trunc P k l hkl r s]
  rw [← r.prod_fintype _ (fun _ => pow_zero _),
    ← s.prod_fintype _ (fun _ => pow_zero _)]
  let x := r.prod fun ay e => (cellVector P k ay) ^ e
  let y := s.prod fun ay e => (cellVector P l ay) ^ e
  let R := ((splitSize n 1).descFactorial (multiDegree r + multiDegree s) : ℝ) /
    (((splitSize n 1).descFactorial (multiDegree r) : ℝ) *
      (splitSize n 1).descFactorial (multiDegree s))
  have hx0 : 0 ≤ x := multiMonomial_nonneg r (cellVector P k)
    (fun ay => (cellVector_mem_unitCube P k ay).1)
  have hy0 : 0 ≤ y := multiMonomial_nonneg s (cellVector P l)
    (fun ay => (cellVector_mem_unitCube P l ay).1)
  have hratio : |R - 1| ≤ 2 * (M : ℝ) ^ 2 / splitSize n 1 := by
    by_cases hrs : multiDegree r ≤ multiDegree s
    · have hsizes : 4 * (multiDegree s) ^ 2 ≤ splitSize n 1 := by
        nlinarith [Nat.mul_self_le_mul_self hs]
      refine (factorial_cross_ratio_bound hrs hsizes).trans ?_
      have hmR : (multiDegree s : ℝ) ≤ M := by exact_mod_cast hs
      have hn0 : 0 ≤ (splitSize n 1 : ℝ) := by positivity
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (by simpa [pow_two] using
            (mul_self_le_mul_self (Nat.cast_nonneg (multiDegree s)) hmR))
          (by norm_num)) hn0
    · have hsr : multiDegree s ≤ multiDegree r := Nat.le_of_not_ge hrs
      have hsizer : 4 * (multiDegree r) ^ 2 ≤ splitSize n 1 := by
        nlinarith [Nat.mul_self_le_mul_self hr]
      have h := factorial_cross_ratio_bound hsr hsizer
      rw [Nat.add_comm] at h
      rw [mul_comm ((splitSize n 1).descFactorial (multiDegree s) : ℝ)] at h
      refine h.trans ?_
      have hmR : (multiDegree r : ℝ) ≤ M := by exact_mod_cast hr
      have hn0 : 0 ≤ (splitSize n 1 : ℝ) := by positivity
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (by simpa [pow_two] using
            (mul_self_le_mul_self (Nat.cast_nonneg (multiDegree r)) hmR))
          (by norm_num)) hn0
  change |R * x * y - x * y| ≤ _
  rw [show R * x * y - x * y = (R - 1) * x * y by ring,
    abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg hy0]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hratio hx0) hy0

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
