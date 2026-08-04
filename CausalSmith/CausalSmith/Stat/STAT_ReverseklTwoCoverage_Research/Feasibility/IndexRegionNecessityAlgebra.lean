import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.Certificate

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

lemma exp_sq_cov_identity
    {ι : Type*} [Fintype ι] (q r : ι → ℝ) (eta : ℝ) :
    (∑ a, ∑ b,
      q a * q b * ((r a) ^ 2 - (r b) ^ 2) *
        (Real.exp (eta * r a) - Real.exp (eta * r b))) =
      2 * ((∑ a, q a) *
          (∑ a, q a * Real.exp (eta * r a) * (r a) ^ 2) -
        (∑ a, q a * Real.exp (eta * r a)) *
          (∑ a, q a * (r a) ^ 2)) := by
  let A := ∑ a, ∑ b,
    q a * q b * (r a) ^ 2 * Real.exp (eta * r a)
  let B := ∑ a, ∑ b,
    q a * q b * (r a) ^ 2 * Real.exp (eta * r b)
  let C := ∑ a, ∑ b,
    q a * q b * (r b) ^ 2 * Real.exp (eta * r a)
  let D := ∑ a, ∑ b,
    q a * q b * (r b) ^ 2 * Real.exp (eta * r b)
  have hA : A = (∑ a, q a) *
      (∑ a, q a * Real.exp (eta * r a) * (r a) ^ 2) := by
    dsimp [A]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    calc
      (∑ b, q a * q b * r a ^ 2 * Real.exp (eta * r a)) =
          ∑ b, q b * (q a * Real.exp (eta * r a) * r a ^ 2) := by
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = (∑ b, q b) * (q a * Real.exp (eta * r a) * r a ^ 2) :=
        by rw [Finset.sum_mul]
  have hB : B = (∑ a, q a * (r a) ^ 2) *
      (∑ a, q a * Real.exp (eta * r a)) := by
    dsimp [B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hCB : C = B := by
    dsimp [C, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hC : C = (∑ a, q a * Real.exp (eta * r a)) *
      (∑ a, q a * (r a) ^ 2) := by
    rw [hCB, hB]
    ring
  have hDA : D = A := by
    dsimp [D, A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hD : D = (∑ a, q a) *
      (∑ a, q a * Real.exp (eta * r a) * (r a) ^ 2) :=
    hDA.trans hA
  rw [show (∑ a, ∑ b,
      q a * q b * ((r a) ^ 2 - (r b) ^ 2) *
        (Real.exp (eta * r a) - Real.exp (eta * r b))) =
      A - B - C + D by
    calc
      _ = ∑ a, ∑ b,
          (q a * q b * (r a) ^ 2 * Real.exp (eta * r a) -
            q a * q b * (r a) ^ 2 * Real.exp (eta * r b) -
            q a * q b * (r b) ^ 2 * Real.exp (eta * r a) +
            q a * q b * (r b) ^ 2 * Real.exp (eta * r b)) := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              ring
      _ = A - B - C + D := by
        dsimp [A, B, C, D]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]]
  rw [hA, hB, hC, hD]
  ring

lemma exp_sq_cov_nonneg
    {ι : Type*} [Fintype ι]
    (q r : ι → ℝ) (eta : ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) (heta : 0 < eta) :
    (∑ a, q a * Real.exp (eta * r a)) * (∑ a, q a * (r a) ^ 2) ≤
      ∑ a, q a * Real.exp (eta * r a) * (r a) ^ 2 := by
  have hterm : ∀ a b,
      0 ≤ q a * q b * ((r a) ^ 2 - (r b) ^ 2) *
        (Real.exp (eta * r a) - Real.exp (eta * r b)) := by
    intro a b
    rcases hr a with ⟨hra0, hra1⟩
    rcases hr b with ⟨hrb0, hrb1⟩
    have hqprod : 0 ≤ q a * q b := mul_nonneg (hq a) (hq b)
    by_cases hab : r a ≤ r b
    · have hsq : (r a) ^ 2 - (r b) ^ 2 ≤ 0 := by nlinarith
      have hexp : Real.exp (eta * r a) - Real.exp (eta * r b) ≤ 0 := by
        rw [sub_nonpos, Real.exp_le_exp]
        exact mul_le_mul_of_nonneg_left hab heta.le
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hqprod hsq) hexp
    · have hba : r b ≤ r a := le_of_not_ge hab
      have hsq : 0 ≤ (r a) ^ 2 - (r b) ^ 2 := by nlinarith
      have hexp : 0 ≤ Real.exp (eta * r a) - Real.exp (eta * r b) := by
        rw [sub_nonneg, Real.exp_le_exp]
        exact mul_le_mul_of_nonneg_left hba heta.le
      exact mul_nonneg (mul_nonneg hqprod hsq) hexp
  have hdouble : 0 ≤ ∑ a, ∑ b,
      q a * q b * ((r a) ^ 2 - (r b) ^ 2) *
        (Real.exp (eta * r a) - Real.exp (eta * r b)) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hterm a b
  have hid :
      (∑ a, ∑ b,
        q a * q b * ((r a) ^ 2 - (r b) ^ 2) *
          (Real.exp (eta * r a) - Real.exp (eta * r b))) =
        2 * ((∑ a, q a * Real.exp (eta * r a) * (r a) ^ 2) -
          (∑ a, q a * Real.exp (eta * r a)) *
            (∑ a, q a * (r a) ^ 2)) := by
    calc
      _ = 2 * ((∑ a, q a) *
          (∑ a, q a * Real.exp (eta * r a) * (r a) ^ 2) -
        (∑ a, q a * Real.exp (eta * r a)) *
          (∑ a, q a * (r a) ^ 2)) :=
            exp_sq_cov_identity q r eta
      _ = _ := by rw [hqsum, one_mul]
  rw [hid] at hdouble
  linarith

lemma exp_sq_cov_pos
    {ι : Type*} [Fintype ι]
    (q r : ι → ℝ) (eta : ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) (heta : 0 < eta)
    (hvar : ∃ a b, 0 < q a ∧ 0 < q b ∧ r a ≠ r b) :
    (∑ a, q a * Real.exp (eta * r a)) * (∑ a, q a * (r a) ^ 2) <
      ∑ a, q a * Real.exp (eta * r a) * (r a) ^ 2 := by
  have hterm : ∀ a b,
      0 ≤ q a * q b * ((r a) ^ 2 - (r b) ^ 2) *
        (Real.exp (eta * r a) - Real.exp (eta * r b)) := by
    intro a b
    rcases hr a with ⟨hra0, hra1⟩
    rcases hr b with ⟨hrb0, hrb1⟩
    have hqprod : 0 ≤ q a * q b := mul_nonneg (hq a) (hq b)
    by_cases hab : r a ≤ r b
    · exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hqprod (by nlinarith))
        (by rw [sub_nonpos, Real.exp_le_exp]
            exact mul_le_mul_of_nonneg_left hab heta.le)
    · have hba : r b ≤ r a := le_of_not_ge hab
      exact mul_nonneg
        (mul_nonneg hqprod (by nlinarith))
        (by rw [sub_nonneg, Real.exp_le_exp]
            exact mul_le_mul_of_nonneg_left hba heta.le)
  rcases hvar with ⟨a, b, hqa, hqb, hab⟩
  have hstrict :
      0 < q a * q b * ((r a) ^ 2 - (r b) ^ 2) *
        (Real.exp (eta * r a) - Real.exp (eta * r b)) := by
    rcases hr a with ⟨hra0, hra1⟩
    rcases hr b with ⟨hrb0, hrb1⟩
    rcases lt_or_gt_of_ne hab with hablt | habgt
    · exact mul_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg (mul_pos hqa hqb) (by nlinarith))
        (by rw [sub_neg, Real.exp_lt_exp]
            exact mul_lt_mul_of_pos_left hablt heta)
    · exact mul_pos
        (mul_pos (mul_pos hqa hqb) (by nlinarith))
        (by rw [sub_pos, Real.exp_lt_exp]
            exact mul_lt_mul_of_pos_left habgt heta)
  have hdouble : 0 < ∑ x, ∑ y,
      q x * q y * ((r x) ^ 2 - (r y) ^ 2) *
        (Real.exp (eta * r x) - Real.exp (eta * r y)) := by
    apply Finset.sum_pos'
    · intro x _
      exact Finset.sum_nonneg fun y _ => hterm x y
    · refine ⟨a, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos'
      · intro y _
        exact hterm a y
      · exact ⟨b, Finset.mem_univ _, hstrict⟩
  have hid :
      (∑ x, ∑ y,
        q x * q y * ((r x) ^ 2 - (r y) ^ 2) *
          (Real.exp (eta * r x) - Real.exp (eta * r y))) =
        2 * ((∑ x, q x * Real.exp (eta * r x) * (r x) ^ 2) -
          (∑ x, q x * Real.exp (eta * r x)) *
            (∑ x, q x * (r x) ^ 2)) := by
    calc
      _ = 2 * ((∑ x, q x) *
          (∑ x, q x * Real.exp (eta * r x) * (r x) ^ 2) -
        (∑ x, q x * Real.exp (eta * r x)) *
          (∑ x, q x * (r x) ^ 2)) :=
            exp_sq_cov_identity q r eta
      _ = _ := by rw [hqsum, one_mul]
  rw [hid] at hdouble
  linarith

lemma quadraticForm_sum_blocks
    {d : ℕ} {ι : Type*} [Fintype ι]
    (rho : ι → ℝ) (M : ι → Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) :
    quadraticForm (∑ x, rho x • M x) v =
      ∑ x, rho x * quadraticForm (M x) v := by
  simp only [quadraticForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ x, v i * (rho x * M x i j) * v j) =
        ∑ i, ∑ x, ∑ j, v i * (rho x * M x i j) * v j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ i, ∑ j, v i * (rho x * M x i j) * v j := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma loggingBlock_quadratic
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (x : 𝒳) (v : Fin d → ℝ) :
    quadraticForm (loggingBlock E x) v =
      ∑ a, E.reference x a * (∑ i, E.feature x a i * v i) ^ 2 := by
  exact weightedFeatureQuadratic
    (fun a => E.feature x a) (fun a => E.reference x a) v

lemma targetBlock_quadratic
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (theta v : Fin d → ℝ) (x : 𝒳) :
    quadraticForm (targetBlock E theta x) v =
      ∑ a, (E.reference x a * candidateWeight E theta x a) *
        (∑ i, E.feature x a i * v i) ^ 2 := by
  exact weightedFeatureQuadratic
    (fun a => E.feature x a)
    (fun a => E.reference x a * candidateWeight E theta x a) v

lemma loggingBlock_le_targetBlock_at_theta
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (theta : Fin d → ℝ) (x : 𝒳)
    (hscore : ∀ a, (∑ i, E.feature x a i * theta i) ∈
      Set.Icc (0 : ℝ) 1) :
    quadraticForm (loggingBlock E x) theta ≤
      quadraticForm (targetBlock E theta x) theta := by
  let r : 𝒜 → ℝ := fun a => ∑ i, E.feature x a i * theta i
  have hcov := exp_sq_cov_nonneg
    (fun a => E.reference x a) r E.eta
    (E.reference_isPolicy.1 x) (E.reference_isPolicy.2 x)
    hscore E.eta_pos
  rw [loggingBlock_quadratic E x theta,
    targetBlock_quadratic E theta theta x]
  change (∑ a, E.reference x a * (r a) ^ 2) ≤
    ∑ a, (E.reference x a * candidateWeight E theta x a) * (r a) ^ 2
  rw [show (∑ a,
      (E.reference x a * candidateWeight E theta x a) * (r a) ^ 2) =
      (∑ a, E.reference x a * Real.exp (E.eta * r a) * (r a) ^ 2) /
        candidateNormalizer E theta x by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    simp only [candidateWeight, r]
    ring]
  apply (le_div_iff₀ (candidateNormalizer_pos E theta x)).2
  simpa [candidateNormalizer, r, mul_comm] using hcov

lemma loggingBlock_lt_targetBlock_at_theta
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (theta : Fin d → ℝ) (x : 𝒳)
    (hscore : ∀ a, (∑ i, E.feature x a i * theta i) ∈
      Set.Icc (0 : ℝ) 1)
    (hvar : ∃ a b, 0 < E.reference x a ∧ 0 < E.reference x b ∧
      (∑ i, E.feature x a i * theta i) ≠
        ∑ i, E.feature x b i * theta i) :
    quadraticForm (loggingBlock E x) theta <
      quadraticForm (targetBlock E theta x) theta := by
  let r : 𝒜 → ℝ := fun a => ∑ i, E.feature x a i * theta i
  have hcov := exp_sq_cov_pos
    (fun a => E.reference x a) r E.eta
    (E.reference_isPolicy.1 x) (E.reference_isPolicy.2 x)
    hscore E.eta_pos hvar
  rw [loggingBlock_quadratic E x theta,
    targetBlock_quadratic E theta theta x]
  change (∑ a, E.reference x a * (r a) ^ 2) <
    ∑ a, (E.reference x a * candidateWeight E theta x a) * (r a) ^ 2
  rw [show (∑ a,
      (E.reference x a * candidateWeight E theta x a) * (r a) ^ 2) =
      (∑ a, E.reference x a * Real.exp (E.eta * r a) * (r a) ^ 2) /
        candidateNormalizer E theta x by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    simp only [candidateWeight, r]
    ring]
  apply (lt_div_iff₀ (candidateNormalizer_pos E theta x)).2
  simpa [candidateNormalizer, r, mul_comm] using hcov

lemma targetBlock_le_pointwise
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (theta v : Fin d → ℝ)
    (x : 𝒳) (C : ℝ)
    (hle : ∀ a, 0 < E.reference x a →
      Real.exp (E.eta * ∑ i, E.feature x a i * theta i) ≤
        C * candidateNormalizer E theta x) :
    quadraticForm (targetBlock E theta x) v ≤
      C * quadraticForm (loggingBlock E x) v := by
  rw [targetBlock_quadratic E theta v x, loggingBlock_quadratic E x v,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : E.reference x a = 0
  · simp [ha]
  · have hapos : 0 < E.reference x a :=
      lt_of_le_of_ne (E.reference_isPolicy.1 x a) (Ne.symm ha)
    have hw : candidateWeight E theta x a ≤ C := by
      rw [candidateWeight]
      exact (div_le_iff₀ (candidateNormalizer_pos E theta x)).2 (hle a hapos)
    have href := E.reference_isPolicy.1 x a
    have hsquare := sq_nonneg (∑ i, E.feature x a i * v i)
    calc
      (E.reference x a * candidateWeight E theta x a) *
          (∑ i, E.feature x a i * v i) ^ 2 ≤
        (E.reference x a * C) *
          (∑ i, E.feature x a i * v i) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hw href) hsquare
      _ = C * (E.reference x a *
          (∑ i, E.feature x a i * v i) ^ 2) := by ring

lemma candidateNormalizer_ge_one
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (theta : Fin d → ℝ) (x : 𝒳)
    (hscore : ∀ a, 0 ≤ ∑ i, E.feature x a i * theta i) :
    1 ≤ candidateNormalizer E theta x := by
  rw [← E.reference_isPolicy.2 x]
  simp only [candidateNormalizer]
  apply Finset.sum_le_sum
  intro a _
  have hexp : 1 ≤ Real.exp
      (E.eta * ∑ i, E.feature x a i * theta i) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonneg E.eta_pos.le (hscore a)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hexp (E.reference_isPolicy.1 x a)

lemma certificate_pointwise_lower_and_strict_upper
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (theta : Fin d → ℝ)
    (x0 : 𝒳) (a0 : 𝒜) (C : ℝ)
    (href0 : 0 < E.reference x0 a0)
    (hscore : ∀ a, (∑ i, E.feature x0 a i * theta i) ∈
      Set.Icc (0 : ℝ) 1)
    (hle : ∀ a, 0 < E.reference x0 a →
      Real.exp (E.eta * ∑ i, E.feature x0 a i * theta i) ≤
        C * candidateNormalizer E theta x0)
    (heq : Real.exp (E.eta * ∑ i, E.feature x0 a0 i * theta i) =
      C * candidateNormalizer E theta x0) :
    1 ≤ C ∧ C < Real.exp E.eta := by
  let Z := candidateNormalizer E theta x0
  let r : 𝒜 → ℝ := fun a => ∑ i, E.feature x0 a i * theta i
  have hZpos : 0 < Z := candidateNormalizer_pos E theta x0
  have hsumle : Z ≤ C * Z := by
    change (∑ a, E.reference x0 a * Real.exp (E.eta * r a)) ≤ C * Z
    calc
      (∑ a, E.reference x0 a * Real.exp (E.eta * r a)) ≤
          ∑ a, E.reference x0 a * (C * Z) := by
            apply Finset.sum_le_sum
            intro a _
            by_cases ha : E.reference x0 a = 0
            · simp [ha]
            · exact mul_le_mul_of_nonneg_left
                (hle a (lt_of_le_of_ne
                  (E.reference_isPolicy.1 x0 a) (Ne.symm ha)))
                (E.reference_isPolicy.1 x0 a)
      _ = C * Z := by rw [← Finset.sum_mul, E.reference_isPolicy.2]; ring
  have hCone : 1 ≤ C := by nlinarith
  have hZone : 1 ≤ Z :=
    candidateNormalizer_ge_one E theta x0 (fun a => (hscore a).1)
  have hnum_lt :
      Real.exp (E.eta * r a0) < Real.exp E.eta * Z := by
    rcases lt_or_eq_of_le (hscore a0).2 with hrlt | hreq
    · have hexplt : Real.exp (E.eta * r a0) < Real.exp E.eta := by
        rw [Real.exp_lt_exp]
        simpa [r] using mul_lt_mul_of_pos_left hrlt E.eta_pos
      have hscale : Real.exp E.eta ≤ Real.exp E.eta * Z := by
        nlinarith [Real.exp_pos E.eta]
      exact lt_of_lt_of_le hexplt hscale
    · have hrowlt : 1 < Z := by
        change 1 < ∑ a, E.reference x0 a * Real.exp (E.eta * r a)
        rw [← E.reference_isPolicy.2 x0]
        apply Finset.sum_lt_sum
        · intro a _
          have hexp : 1 ≤ Real.exp (E.eta * r a) := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr
              (mul_nonneg E.eta_pos.le (by simpa [r] using (hscore a).1))
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hexp
              (E.reference_isPolicy.1 x0 a)
        · refine ⟨a0, Finset.mem_univ a0, ?_⟩
          have hreqr : r a0 = 1 := by simpa [r] using hreq
          have hexp : 1 < Real.exp (E.eta * r a0) := by
            rw [← Real.exp_zero, Real.exp_lt_exp, hreqr]
            simpa using E.eta_pos
          nlinarith
      have hreqr : r a0 = 1 := by simpa [r] using hreq
      rw [hreqr]
      simpa only [mul_one] using
        mul_lt_mul_of_pos_left hrowlt (Real.exp_pos E.eta)
  have hCexp : C < Real.exp E.eta := by
    have hmul : C * Z < Real.exp E.eta * Z := by
      rw [← heq]
      simpa [Z, r] using hnum_lt
    nlinarith
  exact ⟨hCone, hCexp⟩

end CausalSmith.Stat.ReverseKLTwoCoverage
