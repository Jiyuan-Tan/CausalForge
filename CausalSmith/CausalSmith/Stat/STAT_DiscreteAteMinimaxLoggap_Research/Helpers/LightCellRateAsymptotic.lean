import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellRatePilot

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The calibrated cutoff already forces the numerical log-scale used by the
rate algebra.  The apparently separate `240` hypothesis is therefore free
once `n` is above `calibrationCutoff`. -/
lemma cutoff_logScale_ge_240 {n : ℕ} (hcut : calibrationCutoff ≤ n) :
    240 ≤ logScale n := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hscale := (hbase n hcut).1
  have ha0 : 0 < alpha0 := by
    unfold alpha0 dA
    have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hlogOne : 1 < Real.log (27 / 4 : ℝ) := by
    rw [← Real.exp_lt_exp]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 27 / 4)]
    nlinarith [Real.exp_one_lt_d9]
  have hdA : 8 < dA := by
    unfold dA
    nlinarith
  have haSmall : alpha0 ≤ 1 / 120 := by
    have haBound : alpha0 ≤ 1 / (256 * dA) := by simp [alpha0]
    refine haBound.trans ?_
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (by linarith : 0 < dA))
      (by norm_num : (0 : ℝ) < 120)).2
    nlinarith
  have hL0 : 0 ≤ logScale n := by
    by_contra hneg
    have : alpha0 * logScale n < 0 := mul_neg_of_pos_of_neg ha0 (lt_of_not_ge hneg)
    linarith
  have hup : alpha0 * logScale n ≤ (1 / 120) * logScale n := by
    exact mul_le_mul_of_nonneg_right haSmall hL0
  nlinarith

/-- The single elementary growth inequality used in the rate algebra:
`6^(4M) L^6 ≤ n`. -/
lemma calibrated_polynomial_log_growth {n : ℕ}
    (hcut : calibrationCutoff ≤ n) (hLlarge : 240 ≤ logScale n) :
    (6 : ℝ) ^ (4 * polynomialDegree n) * logScale n ^ 6 ≤ n := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hscale := (hbase n hcut).1
  have hL : 0 < logScale n := by linarith
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp [logScale] at hL
  have hlogn : logScale n = 1 + Real.log (n : ℝ) := by
    rw [logScale, Real.log_mul (by positivity : Real.exp 1 ≠ 0)
      (by positivity : (n : ℝ) ≠ 0)]
    simp
  have ha0 : 0 < alpha0 := by
    unfold alpha0 dA
    have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  have haBound : alpha0 ≤ 1 / (32 * Real.log 6) := by
    simp [alpha0]
  have hM : (polynomialDegree n : ℝ) ≤ alpha0 * logScale n := by
    have hfloor2 : (2 : ℤ) ≤ ⌊alpha0 * logScale n⌋ := by
      rw [Int.le_floor]
      exact_mod_cast hscale
    have hmax : polynomialDegree n = Int.toNat ⌊alpha0 * logScale n⌋ := by
      rw [polynomialDegree, max_eq_right]
      exact Int.toNat_le_toNat hfloor2
    rw [hmax]
    have hfloor0 : 0 ≤ ⌊alpha0 * logScale n⌋ := le_trans (by norm_num) hfloor2
    rw [show ((Int.toNat ⌊alpha0 * logScale n⌋ : ℕ) : ℝ) =
        ((⌊alpha0 * logScale n⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg hfloor0]
    exact Int.floor_le _
  have hdegreeExp :
      4 * (polynomialDegree n : ℝ) * Real.log 6 ≤ logScale n / 8 := by
    have haMul : alpha0 * Real.log 6 ≤ 1 / 32 := by
      calc
        alpha0 * Real.log 6 ≤ (1 / (32 * Real.log 6)) * Real.log 6 := by
          gcongr
        _ = 1 / 32 := by field_simp
    nlinarith
  have hlog12 : Real.log (12 : ℝ) ≤ 11 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)).trans_eq
      (by norm_num)
  have hLdiv : 0 < logScale n / 12 := by positivity
  have hlogL : Real.log (logScale n) ≤ logScale n / 8 := by
    have hsplit : Real.log (logScale n) =
        Real.log 12 + Real.log (logScale n / 12) := by
      rw [← Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) (by positivity)]
      congr 1
      field_simp
    rw [hsplit]
    have hsmall := Real.log_le_sub_one_of_pos hLdiv
    nlinarith
  have hsix : (6 : ℝ) ^ (4 * polynomialDegree n) ≤
      Real.exp (logScale n / 8) := by
    rw [show (6 : ℝ) ^ (4 * polynomialDegree n) =
        Real.exp ((4 * polynomialDegree n : ℕ) * Real.log 6) by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 6)]]
    exact Real.exp_le_exp.mpr (by exact_mod_cast hdegreeExp)
  have hLpow : logScale n ^ 6 ≤ Real.exp (3 * logScale n / 4) := by
    rw [show logScale n ^ 6 = Real.exp (6 * Real.log (logScale n)) by
      calc
        logScale n ^ 6 = (Real.exp (Real.log (logScale n))) ^ 6 := by
          rw [Real.exp_log hL]
        _ = Real.exp ((6 : ℕ) * Real.log (logScale n)) := by
          rw [Real.exp_nat_mul]
        _ = _ := by norm_num]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    (6 : ℝ) ^ (4 * polynomialDegree n) * logScale n ^ 6 ≤
        Real.exp (logScale n / 8) * Real.exp (3 * logScale n / 4) := by
      gcongr
    _ = Real.exp (7 * logScale n / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (logScale n - 1) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = n := by
      rw [hlogn]
      simp [Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ))]

/-- Establishes the stated property of eventually light rate cutoff in the discrete average-treatment-effect construction. -/
lemma eventually_light_rate_cutoff :
    ∃ N : ℕ, ∀ n ≥ N,
      calibrationCutoff ≤ n ∧ 240 ≤ logScale n := by
  have hL : Filter.Tendsto logScale Filter.atTop Filter.atTop := by
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have heq : ∀ᶠ n : ℕ in Filter.atTop,
        logScale n = 1 + Real.log (n : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
      rw [logScale, Real.log_mul (by positivity : Real.exp 1 ≠ 0)
        (by positivity : (n : ℝ) ≠ 0)]
      simp
    exact (tendsto_const_nhds.add_atTop hlog).congr'
      (Filter.EventuallyEq.symm heq)
  have hboth : ∀ᶠ n : ℕ in Filter.atTop,
      calibrationCutoff ≤ n ∧ 240 ≤ logScale n :=
    (Filter.eventually_ge_atTop calibrationCutoff).and
      (hL.eventually (Filter.eventually_ge_atTop 240))
  rw [Filter.eventually_atTop] at hboth
  exact hboth

/-- Defines light Asymptotic Rate, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def lightAsymptoticRate (n d : ℕ) : ℝ :=
  1 / (n : ℝ) + d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)

/-- Defines genuine Light Set, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def genuineLightSet {n d : ℕ} (P : DiscreteLaw d) :
    Finset (Fin d) :=
  Finset.univ.filter fun k => cellMass P k ≤ bandwidth n / 4

/-- Establishes the stated upper bound for large calibration bounds. -/
lemma large_calibration_bounds {n : ℕ}
    (hcut : calibrationCutoff ≤ n) (hLlarge : 240 ≤ logScale n) :
    let L := logScale n
    let ell := Real.log (n : ℝ)
    let M := polynomialDegree n
    let B := bandwidth n
    let m := splitSize n 1
    0 < ell ∧ ell ≤ L ∧ L ≤ 2 * ell ∧
      0 < m ∧ (n : ℝ) ≤ 2 * m ∧
      (M : ℝ) ≤ L ∧ B ≤ 8192 * L / n ∧
      ((6 : ℝ) ^ (2 * M)) ^ 2 * L ^ 6 ≤ n := by
  classical
  dsimp
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hs := (hbase n hcut).1
  have hL : 0 < logScale n := by linarith
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp [logScale] at hL
  have hscale : logScale n = 1 + Real.log (n : ℝ) := by
    rw [logScale, Real.log_mul (by positivity : Real.exp 1 ≠ 0)
      (by positivity : (n : ℝ) ≠ 0)]
    simp
  have hell : 0 < Real.log (n : ℝ) := by
    rw [hscale] at hLlarge
    linarith
  have hellL : Real.log (n : ℝ) ≤ logScale n := by rw [hscale]; linarith
  have hLell : logScale n ≤ 2 * Real.log (n : ℝ) := by
    rw [hscale]
    linarith
  have hM2nat : 2 ≤ polynomialDegree n := by simp [polynomialDegree]
  have hM4nat : 4 ≤ polynomialDegree n ^ 2 := by
    simpa [pow_two] using Nat.mul_self_le_mul_self hM2nat
  have hm : 0 < splitSize n 1 := by nlinarith [(hbase n hcut).2.1]
  have hnm : (n : ℝ) ≤ 2 * splitSize n 1 := by
    have hnat : n ≤ 2 * splitSize n 1 := by
      rw [splitSize_one_eq]
      omega
    exact_mod_cast hnat
  have hM : (polynomialDegree n : ℝ) ≤ logScale n := by
    have ha1 : alpha0 ≤ 1 := by simp [alpha0]
    have hfloor2 : (2 : ℤ) ≤ ⌊alpha0 * logScale n⌋ := by
      rw [Int.le_floor]
      exact_mod_cast hs
    have hmax : polynomialDegree n = Int.toNat ⌊alpha0 * logScale n⌋ := by
      rw [polynomialDegree, max_eq_right]
      exact Int.toNat_le_toNat hfloor2
    rw [hmax]
    have hfloor0 : 0 ≤ ⌊alpha0 * logScale n⌋ := le_trans (by norm_num) hfloor2
    rw [show ((Int.toNat ⌊alpha0 * logScale n⌋ : ℕ) : ℝ) =
        ((⌊alpha0 * logScale n⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg hfloor0]
    exact (Int.floor_le _).trans (mul_le_of_le_one_left hL.le ha1)
  have hB : bandwidth n ≤ 8192 * logScale n / n := by
    rw [bandwidth]
    have hnR : 0 < (n : ℝ) := by positivity
    have hmR : 0 < (splitSize n 1 : ℝ) := by exact_mod_cast hm
    rw [div_le_div_iff₀ hmR hnR]
    norm_num [b0]
    nlinarith
  have hg := calibrated_polynomial_log_growth hcut hLlarge
  have hpow : (((6 : ℝ) ^ (2 * polynomialDegree n)) ^ 2) =
      (6 : ℝ) ^ (4 * polynomialDegree n) := by ring
  rw [hpow]
  exact ⟨hell, hellL, hLell, hm, hnm, hM, hB, hg⟩

/-- Establishes the stated property of diagonal rate algebra in the discrete average-treatment-effect construction. -/
lemma diagonal_rate_algebra {n d : ℕ} {L ell G : ℝ}
    (hn : 0 < (n : ℝ)) (hellDef : ell = Real.log (n : ℝ))
    (hell : 0 < ell) (hellL : ell ≤ L)
    (hL0 : 0 ≤ L) (hG1 : 1 ≤ G)
    (hgrowth : G ^ 2 * L ^ 6 ≤ n) :
    (d : ℝ) * L ^ 2 * G / (n : ℝ) ^ 2 ≤
      (lightAsymptoticRate n d) / 2 := by
  have hcore : L ^ 4 * G ^ 2 * ell ^ 4 ≤ (n : ℝ) * ell ^ 2 := by
    have hell0 : 0 ≤ ell := hell.le
    have hle : L ^ 4 * G ^ 2 * ell ^ 2 ≤ G ^ 2 * L ^ 6 := by
      have hell2 : ell ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hell0 hellL 2
      calc
        L ^ 4 * G ^ 2 * ell ^ 2 ≤ L ^ 4 * G ^ 2 * L ^ 2 := by
          gcongr
        _ = G ^ 2 * L ^ 6 := by ring
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg ell)]
  unfold lightAsymptoticRate
  rw [← hellDef]
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn
  have he0 : ell ≠ 0 := ne_of_gt hell
  change (d : ℝ) * L ^ 2 * G / (n : ℝ) ^ 2 ≤
    (1 / (n : ℝ) + (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ell ^ 2)) / 2
  field_simp
  nlinarith [sq_nonneg ((d : ℝ) - L ^ 2 * G * ell ^ 2)]

/-- Establishes the stated property of cross rate algebra in the discrete average-treatment-effect construction. -/
lemma cross_rate_algebra {n d : ℕ} {L ell G : ℝ}
    (hn : 0 < (n : ℝ)) (hellDef : ell = Real.log (n : ℝ))
    (hell : 0 < ell) (hellL : ell ≤ L)
    (hL0 : 0 ≤ L) (hG1 : 1 ≤ G)
    (hgrowth : G ^ 2 * L ^ 6 ≤ n) :
    (d : ℝ) ^ 2 * L ^ 4 * G / (n : ℝ) ^ 3 ≤
      lightAsymptoticRate n d := by
  have hG0 : 0 ≤ G := le_trans (by norm_num) hG1
  have hell0 : 0 ≤ ell := hell.le
  have hcore : L ^ 4 * G * ell ^ 2 ≤ n := by
    have he2 : ell ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hell0 hellL 2
    have hGG : G ≤ G ^ 2 := by nlinarith
    calc
      L ^ 4 * G * ell ^ 2 ≤ L ^ 4 * G ^ 2 * L ^ 2 := by gcongr
      _ = G ^ 2 * L ^ 6 := by ring
      _ ≤ n := hgrowth
  unfold lightAsymptoticRate
  rw [← hellDef]
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn
  have he0 : ell ≠ 0 := ne_of_gt hell
  change (d : ℝ) ^ 2 * L ^ 4 * G / (n : ℝ) ^ 3 ≤
    1 / (n : ℝ) + (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ell ^ 2)
  have hmain : (d : ℝ) ^ 2 * L ^ 4 * G / (n : ℝ) ^ 3 ≤
      (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ell ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 3)
      (by positivity : 0 < (n : ℝ) ^ 2 * ell ^ 2)).2
    calc
      (d : ℝ) ^ 2 * L ^ 4 * G * ((n : ℝ) ^ 2 * ell ^ 2) =
          ((d : ℝ) ^ 2 * (n : ℝ) ^ 2) * (L ^ 4 * G * ell ^ 2) := by ring
      _ ≤ ((d : ℝ) ^ 2 * (n : ℝ) ^ 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hcore
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (d : ℝ) ^ 2 * (n : ℝ) ^ 3 := by ring
  exact hmain.trans (le_add_of_nonneg_left (by positivity))

/-- Rate-normalized version of equation (17) for the pilot-selected genuinely
light cells. -/
lemma selectedGenuineLightCentered_rate {n d : ℕ} (P : DiscreteLaw d)
    (hcut : calibrationCutoff ≤ n) (hLlarge : 240 ≤ logScale n) :
    ∫ ω : ℕ → Obs d,
        selectedFixedLightCentered P (fun i : Fin n => ω i)
          (genuineLightSet (n := n) P) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      (4 * (Real.exp 1 + 1) * 8192 ^ 2 + 16 * 8192 ^ 2) *
        lightAsymptoticRate n d := by
  classical
  let L := logScale n
  let ell := Real.log (n : ℝ)
  let M := polynomialDegree n
  let B := bandwidth n
  let m := splitSize n 1
  let G := (6 : ℝ) ^ (2 * M)
  rcases large_calibration_bounds hcut hLlarge with
    ⟨hell, hellL, hLell, hm, hnm, hM, hB, hgrowth⟩
  have hnNat : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num at hell
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hG1 : 1 ≤ G := by
    dsimp only [G]
    exact one_le_pow₀ (by norm_num)
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hsize := (hbase n hcut).2.1
  have hshift := (hbase n hcut).2.2
  have hBpos : 0 < B := by
    dsimp only [B]
    rw [bandwidth]
    exact div_pos (mul_pos (by norm_num [b0]) (lt_of_lt_of_le hell hellL))
      (by exact_mod_cast hm)
  have hlight (k : Fin d) (hk : k ∈ genuineLightSet (n := n) P) :
      cellMass P k + 4 * (M : ℝ) / m ≤ B := by
    have hk' : cellMass P k ≤ B / 4 := by
      simpa [genuineLightSet, B] using hk
    have hs := hshift
    change 4 * (M : ℝ) / m ≤ 3 * B / 4 at hs
    linarith
  have hraw := selectedFixedLightCentered_second_moment_le P
    (genuineLightSet (n := n) P) hm (by simp [M, polynomialDegree]) hBpos hsize hlight
  have hcard : ((genuineLightSet (n := n) P).card : ℝ) ≤ d := by
    exact_mod_cast (calc
      (genuineLightSet (n := n) P).card ≤ (Finset.univ : Finset (Fin d)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = d := Fintype.card_fin d)
  have hBG : (B * 6 ^ M) ^ 2 = B ^ 2 * G := by
    dsimp only [G]
    rw [mul_pow]
    congr 1
    ring
  have hBsq : B ^ 2 ≤ 8192 ^ 2 * L ^ 2 / (n : ℝ) ^ 2 := by
    have hB0 : 0 ≤ B := hBpos.le
    have hrhs0 : 0 ≤ 8192 * L / (n : ℝ) := by positivity
    exact pow_le_pow_left₀ hB0 hB 2 |>.trans_eq (by ring)
  have hmInv : 1 / (m : ℝ) ≤ 2 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hm) hn).2
    nlinarith
  have hdiagBase := diagonal_rate_algebra (d := d) hn rfl hell hellL hL0 hG1 hgrowth
  have hcrossBase := cross_rate_algebra (d := d) hn rfl hell hellL hL0 hG1 hgrowth
  refine hraw.trans ?_
  rw [hBG]
  have hdiag :
      ((genuineLightSet (n := n) P).card : ℝ) * (8 * (Real.exp 1 + 1)) *
          (B ^ 2 * G) ≤
        (4 * (Real.exp 1 + 1) * 8192 ^ 2) *
          lightAsymptoticRate n d := by
    calc
      ((genuineLightSet (n := n) P).card : ℝ) * (8 * (Real.exp 1 + 1)) *
          (B ^ 2 * G) ≤
        (d : ℝ) * (8 * (Real.exp 1 + 1)) *
          ((8192 ^ 2 * L ^ 2 / (n : ℝ) ^ 2) * G) := by gcongr
      _ = (8 * (Real.exp 1 + 1) * 8192 ^ 2) *
          ((d : ℝ) * L ^ 2 * G / (n : ℝ) ^ 2) := by ring
      _ ≤ (8 * (Real.exp 1 + 1) * 8192 ^ 2) *
          (lightAsymptoticRate n d / 2) := by gcongr
      _ = _ := by ring
  have hcross :
      ((genuineLightSet (n := n) P).card : ℝ) ^ 2 *
          (8 * (M : ℝ) ^ 2 / m) * (B ^ 2 * G) ≤
        (16 * 8192 ^ 2) * lightAsymptoticRate n d := by
    have hc2 : ((genuineLightSet (n := n) P).card : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    have hM2 : (M : ℝ) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hM 2
    calc
      ((genuineLightSet (n := n) P).card : ℝ) ^ 2 *
          (8 * (M : ℝ) ^ 2 / m) * (B ^ 2 * G) ≤
        (d : ℝ) ^ 2 * (8 * L ^ 2 * (2 / (n : ℝ))) *
          ((8192 ^ 2 * L ^ 2 / (n : ℝ) ^ 2) * G) := by
            rw [div_eq_mul_inv]
            have hmInv' : (m : ℝ)⁻¹ ≤ 2 / (n : ℝ) := by simpa using hmInv
            gcongr
      _ = (16 * 8192 ^ 2) *
          ((d : ℝ) ^ 2 * L ^ 4 * G / (n : ℝ) ^ 3) := by ring
      _ ≤ (16 * 8192 ^ 2) * lightAsymptoticRate n d := by gcongr
  linarith

/-- Establishes the stated upper bound for selected False Light Error rate. -/
lemma selectedFalseLightError_rate {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (hcut : calibrationCutoff ≤ n) (hLlarge : 240 ≤ logScale n) :
    ∫ ω : ℕ → Obs d,
        selectedFalseLightError P (fun i : Fin n => ω i) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      (8 * (Real.exp 1 + 1) * 8192 ^ 2) * lightAsymptoticRate n d := by
  let L := logScale n
  let ell := Real.log (n : ℝ)
  let B := bandwidth n
  let G := (6 : ℝ) ^ (2 * polynomialDegree n)
  rcases large_calibration_bounds hcut hLlarge with
    ⟨hell, hellL, _hLell, _hm, _hnm, _hM, hB, hgrowth⟩
  have hnNat : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num at hell
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hG1 : 1 ≤ G := by
    dsimp only [G]
    exact one_le_pow₀ (by norm_num)
  have hBpos : 0 < B := by
    dsimp only [B]
    rw [bandwidth]
    exact div_pos (mul_pos (by norm_num [b0]) (lt_of_lt_of_le hell hellL))
      (by exact_mod_cast _hm)
  have hBsq : B ^ 2 ≤ 8192 ^ 2 * L ^ 2 / (n : ℝ) ^ 2 := by
    have hrhs0 : 0 ≤ 8192 * L / (n : ℝ) := by positivity
    exact pow_le_pow_left₀ hBpos.le hB 2 |>.trans_eq (by ring)
  have hexp : Real.exp (-49 * L) ≤ 1 / (n : ℝ) := by
    have hscale : L = 1 + ell := by
      dsimp only [L, ell]
      rw [logScale, Real.log_mul (by positivity : Real.exp 1 ≠ 0)
        (by positivity : (n : ℝ) ≠ 0)]
      simp
    calc
      Real.exp (-49 * L) ≤ Real.exp (-L) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = (Real.exp L)⁻¹ := by rw [Real.exp_neg]
      _ = (Real.exp 1 * (n : ℝ))⁻¹ := by
        dsimp only [L, logScale]
        rw [Real.exp_log (by positivity : 0 < Real.exp 1 * (n : ℝ))]
      _ ≤ 1 / (n : ℝ) := by
        rw [one_div]
        exact inv_anti₀ hn (by nlinarith [Real.exp_one_gt_d9])
  have hL4 : L ^ 4 ≤ (n : ℝ) := by
    calc
      L ^ 4 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
      _ ≤ G ^ 2 * L ^ 6 := by
        exact le_mul_of_one_le_left (pow_nonneg hL0 6)
          (by nlinarith [hG1])
      _ ≤ n := hgrowth
  have hcore : L ^ 2 * ell ^ 2 ≤ (n : ℝ) := by
    have he2 : ell ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hell.le hellL 2
    nlinarith [sq_nonneg (L ^ 2 - ell ^ 2)]
  have hbase : (d : ℝ) ^ 2 * L ^ 2 / (n : ℝ) ^ 3 ≤
      lightAsymptoticRate n d := by
    unfold lightAsymptoticRate
    have hmain : (d : ℝ) ^ 2 * L ^ 2 / (n : ℝ) ^ 3 ≤
        (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ell ^ 2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 3)
        (by positivity : 0 < (n : ℝ) ^ 2 * ell ^ 2)).2
      calc
        (d : ℝ) ^ 2 * L ^ 2 * ((n : ℝ) ^ 2 * ell ^ 2) =
            ((d : ℝ) ^ 2 * (n : ℝ) ^ 2) * (L ^ 2 * ell ^ 2) := by ring
        _ ≤ ((d : ℝ) ^ 2 * (n : ℝ) ^ 2) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hcore
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ = (d : ℝ) ^ 2 * (n : ℝ) ^ 3 := by ring
    exact hmain.trans (le_add_of_nonneg_left (by positivity))
  refine (selectedFalseLightError_second_moment_le P hOverlap hcut).trans ?_
  calc
    (d : ℝ) ^ 2 *
        (8 * (Real.exp 1 + 1) * B ^ 2 * Real.exp (-49 * L)) ≤
      (8 * (Real.exp 1 + 1) * 8192 ^ 2) *
        ((d : ℝ) ^ 2 * L ^ 2 / (n : ℝ) ^ 3) := by
          have hc : 0 ≤ 8 * (Real.exp 1 + 1) := by positivity
          calc
            _ ≤ (d : ℝ) ^ 2 *
                (8 * (Real.exp 1 + 1) *
                  (8192 ^ 2 * L ^ 2 / (n : ℝ) ^ 2) * (1 / (n : ℝ))) := by
              gcongr
            _ = _ := by ring
    _ ≤ _ := by gcongr

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
