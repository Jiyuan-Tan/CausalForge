import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.WinsorizedScoreMaximal
import Causalean.Mathlib.Analysis.ConvexProjection
import Causalean.Mathlib.Analysis.ClipInterval
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Outer-expected upper bound for the explicit winsorized estimator

The result is conditional on exactly three cited CTY interfaces:
identification, sequential first-order bias, and the supplement's expected
Gram/raw-score bounds.  The bounded winsorized-score maximal inequality is
proved in run and introduces no fourth hypothesis.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

-- @node: outerLIntegral_add_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma outerLIntegral_add_le {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ≥0∞) :
    MeasureTheory.outerLIntegral μ (fun ω => f ω + g ω) ≤
      MeasureTheory.outerLIntegral μ f + MeasureTheory.outerLIntegral μ g := by
  rw [MeasureTheory.outerLIntegral, MeasureTheory.outerLIntegral,
    MeasureTheory.outerLIntegral]
  simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
  apply le_iInf
  intro F
  apply le_iInf
  intro hF
  apply le_iInf
  intro hfF
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  apply le_iInf
  intro hgG
  refine iInf_le_of_le (fun ω => F ω + G ω) ?_
  refine iInf_le_of_le (hF.add hG) ?_
  refine iInf_le_of_le (fun ω => add_le_add (hfF ω) (hgG ω)) ?_
  rw [lintegral_add_left hF]

-- @node: outerLIntegral_const_probability
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma outerLIntegral_const_probability {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℝ≥0∞) :
    MeasureTheory.outerLIntegral μ (fun _ => c) = c := by
  apply le_antisymm
  · rw [MeasureTheory.outerLIntegral]
    refine iInf_le_of_le (fun _ => c) ?_
    refine iInf_le_of_le measurable_const ?_
    refine iInf_le_of_le (fun _ => le_rfl) ?_
    simp
  · rw [MeasureTheory.outerLIntegral]
    apply le_iInf
    intro g
    apply le_iInf
    intro hg
    apply le_iInf
    intro hcg
    have h : (∫⁻ _ω : Ω, c ∂μ) ≤ ∫⁻ ω, g ω ∂μ :=
      lintegral_mono (fun ω => hcg ω)
    simpa using h

-- @node: frontierRate_shift_antitone
/-- The stated rate schedule is nonincreasing as sample size increases. -/
lemma frontierRate_shift_antitone : Antitone (fun n : ℕ => frontierRate (n + 3)) := by
  intro m n hmn
  unfold frontierRate
  apply Real.rpow_le_rpow
  · positivity
  · apply Real.log_div_self_antitoneOn
    · have : Real.exp 1 < 3 := Real.exp_one_lt_three
      exact this.le.trans (by exact_mod_cast (show 3 ≤ m + 3 by omega))
    · have : Real.exp 1 < 3 := Real.exp_one_lt_three
      exact this.le.trans (by exact_mod_cast (show 3 ≤ n + 3 by omega))
    · exact_mod_cast (Nat.add_le_add_right hmn 3)
  · norm_num

-- @node: t4_frontierRate_fourth_power
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma t4_frontierRate_fourth_power (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * frontierRate n ^ 4 = Real.log n := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hbase : 0 ≤ Real.log (n : ℝ) / n := (div_pos hlog hn0).le
  unfold frontierRate
  have hr := Real.rpow_inv_natCast_pow hbase (by norm_num : (4 : ℕ) ≠ 0)
  rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  calc
    (n : ℝ) * (Real.log n / n).rpow (((4 : ℕ) : ℝ)⁻¹) ^ 4 =
        (n : ℝ) * (Real.log n / n) := by
      exact congrArg (fun z : ℝ => (n : ℝ) * z) hr
    _ = Real.log n := by field_simp

-- @node: frontierRate_shift_tendsto_zero
/-- As sample size grows, the stated sequence converges to zero. -/
lemma frontierRate_shift_tendsto_zero :
    Tendsto (fun n : ℕ => frontierRate (n + 3)) atTop (nhds 0) :=
  frontierRate_tendsto_zero.comp (Filter.tendsto_add_atTop_nat 3)

-- @node: frontierRate_shift_nh2_tendsto_top
/-- As sample size grows, the stated effective sample-size sequence diverges to infinity. -/
lemma frontierRate_shift_nh2_tendsto_top :
    Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ) * frontierRate (n + 3) ^ 2)
      atTop atTop := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono' atTop _ hsqrt
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  have hlog : 1 ≤ Real.log (n + 3 : ℕ) := by
    rw [← Real.log_exp 1]
    apply Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
      (by change (0 : ℝ) < (n + 3 : ℕ); positivity)
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ n + 3 by omega))
  have hr := t4_frontierRate_fourth_power (n + 3) (by omega)
  have ha : 0 ≤ frontierRate (n + 3) := (frontierRate_pos (by omega)).le
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  calc
    (n : ℝ) ≤ (n + 3 : ℕ) := by exact_mod_cast (show n ≤ n + 3 by omega)
    _ ≤ ((n + 3 : ℕ) : ℝ) * Real.log (n + 3 : ℕ) := by
      nlinarith [show (0 : ℝ) ≤ (n + 3 : ℕ) by positivity]
    _ = (((n + 3 : ℕ) : ℝ) * frontierRate (n + 3) ^ 2) ^ 2 := by
      nlinarith

-- @node: matrixQuadratic_sub_abs_le_entrywise
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma matrixQuadratic_sub_abs_le_entrywise {q : ℕ}
    (A S : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hentry : ∀ i j, |A i j - S i j| ≤ δ) :
    |matrixQuadratic A v - matrixQuadratic S v| ≤
      (q : ℝ) * δ * ∑ i, (v i) ^ 2 := by
  rw [show matrixQuadratic A v - matrixQuadratic S v =
      ∑ i, ∑ j, v i * (A i j - S i j) * v j by
    simp only [matrixQuadratic]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  calc
    |∑ i, ∑ j, v i * (A i j - S i j) * v j| ≤
        ∑ i, ∑ j, |v i * (A i j - S i j) * v j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ _j : Fin q, δ / 2 * ((v i) ^ 2 + (v _j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      have hp : 2 * (|v i| * |v j|) ≤ (v i) ^ 2 + (v j) ^ 2 := by
        nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
      have hm := mul_le_mul_of_nonneg_left (hentry i j) (abs_nonneg (v i))
      have hm' := mul_le_mul_of_nonneg_right hm (abs_nonneg (v j))
      nlinarith [mul_nonneg hδ (add_nonneg (sq_nonneg (v i)) (sq_nonneg (v j)))]
    _ = (q : ℝ) * δ * ∑ i, (v i) ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

-- @node: causalGramDeviation_entry_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma causalGramDeviation_entry_le (n p : ℕ) (P : A1A2Law)
    (h δ : ℝ) (hδ : 0 ≤ δ) (w : CausalSample n)
    (hdev : causalGramDeviation n p P h w ≤ ENNReal.ofReal δ)
    (t : Bool) (x : Score) (hx : x ∈ P.boundary)
    (j k : Fin (p + 1)) :
    |empiricalGram n p t h (signedDistanceData n P w x) j k -
      populationGram P p t x h j k| ≤ δ := by
  have he : ENNReal.ofReal
      |empiricalGram n p t h (signedDistanceData n P w x) j k -
        populationGram P p t x h j k| ≤ causalGramDeviation n p P h w := by
    unfold causalGramDeviation
    exact le_iSup_of_le t (le_iSup_of_le x (le_iSup_of_le hx
      (le_iSup_of_le j (le_iSup_of_le k le_rfl))))
  exact ENNReal.ofReal_le_ofReal_iff hδ |>.mp (he.trans hdev)

-- @node: empiricalGramGuard_of_deviation_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma empiricalGramGuard_of_deviation_le (n p : ℕ) (ν L : ℝ)
    (P : A1A2Law) (hP : A1A2Class p ν L P) (h : ℝ)
    (hh : 0 < h) (hhL : h ≤ L⁻¹) (w : CausalSample n)
    (hdev : causalGramDeviation n p P h w ≤
      ENNReal.ofReal ((2 * L * (p + 1 : ℝ))⁻¹))
    (t : Bool) (x : Score) (hx : x ∈ P.boundary) :
    empiricalGramGuard L
      (empiricalGram n p t h (signedDistanceData n P w x)) := by
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hP.2.1
  have hq : 0 < (p + 1 : ℝ) := by positivity
  have hδ : 0 ≤ (2 * L * (p + 1 : ℝ))⁻¹ := by positivity
  intro v
  let A := empiricalGram n p t h (signedDistanceData n P w x)
  let S := populationGram P p t x h
  have hentry : ∀ i j, |A i j - S i j| ≤ (2 * L * (p + 1 : ℝ))⁻¹ := by
    intro i j
    exact causalGramDeviation_entry_le n p P h _ hδ w hdev t x hx i j
  have herr := matrixQuadratic_sub_abs_le_entrywise A S v
    (2 * L * (p + 1 : ℝ))⁻¹ hδ hentry
  have hfloor := hP.2.2.2.2.2.2.2.2.2.2.2.2.1 t x h hx hh hhL v
  have hs : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change (2 * L)⁻¹ * ∑ i, (v i) ^ 2 ≤ matrixQuadratic A v
  have hscale : (p + 1 : ℝ) * (2 * L * (p + 1 : ℝ))⁻¹ = (2 * L)⁻¹ := by
    field_simp
  have hscale' : (((p + 1 : ℕ) : ℝ)) * (2 * L * (p + 1 : ℝ))⁻¹ =
      (2 * L)⁻¹ := by
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp
  have herr' : |matrixQuadratic A v - matrixQuadratic S v| ≤
      (2 * L)⁻¹ * ∑ i, (v i) ^ 2 := by
    calc
      _ ≤ ((p + 1 : ℕ) : ℝ) * (2 * L * (p + 1 : ℝ))⁻¹ *
          ∑ i, (v i) ^ 2 := herr
      _ = _ := by rw [hscale']
  have hd : matrixQuadratic S v - (2 * L)⁻¹ * ∑ i, (v i) ^ 2 ≤
      matrixQuadratic A v := by
    have habs := (abs_le.mp herr').1
    linarith
  calc
    (2 * L)⁻¹ * ∑ i, (v i) ^ 2 ≤
        matrixQuadratic S v - (2 * L)⁻¹ * ∑ i, (v i) ^ 2 := by
      have hi : L⁻¹ = 2 * (2 * L)⁻¹ := by field_simp
      rw [hi] at hfloor
      nlinarith
    _ ≤ matrixQuadratic A v := hd

-- @node: empiricalGramGuard_inv_mulVec_euclidean_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma empiricalGramGuard_inv_mulVec_euclidean_le {p : ℕ} {L : ℝ}
    (hL : 0 < L) {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hA : empiricalGramGuard L A) (s : Fin (p + 1) → ℝ) :
    Real.sqrt (∑ k, (A⁻¹.mulVec s k) ^ 2) ≤
      2 * L * Real.sqrt (∑ k, (s k) ^ 2) := by
  let z := A⁻¹.mulVec s
  have hc : 0 < (2 * L)⁻¹ := by positivity
  have hinj : Function.Injective (Matrix.mulVec A) := by
    intro u v huv
    have hzero : A.mulVec (u - v) = 0 := by
      simpa [Matrix.mulVec_sub] using sub_eq_zero.mpr huv
    have hq := hA (u - v)
    have hquad : matrixQuadratic A (u - v) = 0 := by
      rw [show matrixQuadratic A (u - v) =
        dotProduct (u - v) (A.mulVec (u - v)) by
          simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]; ring_nf,
        hzero]
      simp
    have hsum : ∑ i, ((u - v) i) ^ 2 = 0 := by
      have hs : 0 ≤ ∑ i, ((u - v) i) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith
    funext i
    have hi : ((u - v) i) ^ 2 = 0 := by
      exact le_antisymm
        (hsum ▸ Finset.single_le_sum (fun j _ => sq_nonneg ((u - v) j))
          (Finset.mem_univ i)) (sq_nonneg _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  have hu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hudet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hAz : A.mulVec z = s := by
    change A.mulVec (A⁻¹.mulVec s) = s
    calc
      _ = (A * A⁻¹).mulVec s := Matrix.mulVec_mulVec s A A⁻¹
      _ = s := by rw [Matrix.mul_nonsing_inv A hudet, Matrix.one_mulVec]
  have hlower : (2 * L)⁻¹ * ∑ k, (z k) ^ 2 ≤ ∑ k, z k * s k := by
    have hz := hA z
    rw [show matrixQuadratic A z = dotProduct z (A.mulVec z) by
      simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]; ring_nf,
      hAz] at hz
    simpa [dotProduct] using hz
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ z s
  have hsquares : (2 * L)⁻¹ * (Real.sqrt (∑ k, (z k) ^ 2)) ^ 2 ≤
      Real.sqrt (∑ k, (z k) ^ 2) * Real.sqrt (∑ k, (s k) ^ 2) := by
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg (z _))]
    exact hlower.trans hcs
  have hznonneg := Real.sqrt_nonneg (∑ k, (z k) ^ 2)
  by_cases hz : Real.sqrt (∑ k, (z k) ^ 2) = 0
  · simp [z, hz]
    positivity
  · have hzpos : 0 < Real.sqrt (∑ k, (z k) ^ 2) := lt_of_le_of_ne hznonneg (Ne.symm hz)
    change Real.sqrt (∑ k, (z k) ^ 2) ≤ _
    have hcanc : Real.sqrt (∑ k, (z k) ^ 2) ≤
        (2 * L) * Real.sqrt (∑ k, (s k) ^ 2) := by
      have hi : (2 * L)⁻¹ * (2 * L) = 1 := inv_mul_cancel₀ (by positivity)
      nlinarith
    exact hcanc

-- @node: euclideanNorm_le_card_mul_piNorm
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma euclideanNorm_le_card_mul_piNorm {q : ℕ} (hq : 1 ≤ q)
    (v : Fin q → ℝ) :
    Real.sqrt (∑ k, (v k) ^ 2) ≤ (q : ℝ) * ‖v‖ := by
  have hsum : ∑ k, (v k) ^ 2 ≤ (q : ℝ) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin q, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hk : |v k| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm v k
        have hs := (sq_le_sq₀ (abs_nonneg (v k)) (norm_nonneg v)).2 hk
        simpa [sq_abs] using hs
      _ = _ := by simp
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hn : 0 ≤ ‖v‖ := norm_nonneg _
  calc
    _ ≤ Real.sqrt ((q : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ ≤ (q : ℝ) * ‖v‖ := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast hq
        nlinarith [sq_nonneg ((q : ℝ) * ‖v‖)]

-- @node: empiricalGramGuard_isUnit
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma empiricalGramGuard_isUnit {p : ℕ} {L : ℝ} (hL : 0 < L)
    {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hA : empiricalGramGuard L A) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hzero : A.mulVec (u - v) = 0 := by
    simpa [Matrix.mulVec_sub] using sub_eq_zero.mpr huv
  have hq := hA (u - v)
  have hquad : matrixQuadratic A (u - v) = 0 := by
    rw [show matrixQuadratic A (u - v) =
      dotProduct (u - v) (A.mulVec (u - v)) by
        simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]; ring_nf,
      hzero]
    simp
  have hsum : ∑ i, ((u - v) i) ^ 2 = 0 := by
    have hs : 0 ≤ ∑ i, ((u - v) i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hc : 0 < (2 * L)⁻¹ := by positivity
    nlinarith
  funext i
  have hi : ((u - v) i) ^ 2 = 0 := by
    exact le_antisymm
      (hsum ▸ Finset.single_le_sum (fun j _ => sq_nonneg ((u - v) j))
        (Finset.mem_univ i)) (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)

-- @node: guardedCoefficient_sub_populationCoefficient_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma guardedCoefficient_sub_populationCoefficient_le
    (n p : ℕ) (ν L h B : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (t : Bool) (x : Score)
    (hx : x ∈ P.boundary) (hh : 0 < h) (hhL : h ≤ L⁻¹)
    (w : CausalSample n)
    (hguard : empiricalGramGuard L
      (empiricalGram n p t h (signedDistanceData n P w x))) :
    |guardedCoefficient n p L t h B (signedDistanceData n P w x) 0 -
      populationCoefficient P p t x h 0| ≤
      2 * L * (p + 1 : ℝ) * ‖winsorizedCenteredScore n p P t x h B w‖ := by
  let A := empiricalGram n p t h (signedDistanceData n P w x)
  let β := populationCoefficient P p t x h
  let o := winsorizedCenteredScore n p P t x h B w
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hP.2.1
  have hunit : IsUnit A := empiricalGramGuard_isUnit hL hguard
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
  have hscore : empiricalScore n p t h B (signedDistanceData n P w x) =
      o + A.mulVec β := by
    funext j
    simp only [o, A, β, winsorizedCenteredScore, Pi.add_apply]
    simp [Matrix.mulVec, dotProduct]
  have hcoef : guardedCoefficient n p L t h B
      (signedDistanceData n P w x) - β = A⁻¹.mulVec o := by
    funext j
    simp only [guardedCoefficient, hguard, if_pos, hscore, Matrix.mulVec_add,
      Pi.add_apply, Pi.sub_apply]
    have hc : A⁻¹.mulVec (A.mulVec β) = β := by
      calc
        _ = (A⁻¹ * A).mulVec β := Matrix.mulVec_mulVec β A⁻¹ A
        _ = β := by rw [Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec]
    rw [hc]
    ring
  have hcoord : |(A⁻¹.mulVec o) 0| ≤
      Real.sqrt (∑ k, (A⁻¹.mulVec o k) ^ 2) := by
    apply (Real.le_sqrt (abs_nonneg _)
      (Finset.sum_nonneg fun k _ => sq_nonneg (A⁻¹.mulVec o k))).2
    rw [sq_abs]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (A⁻¹.mulVec o k))
      (Finset.mem_univ 0)
  rw [show guardedCoefficient n p L t h B (signedDistanceData n P w x) 0 -
      populationCoefficient P p t x h 0 = (A⁻¹.mulVec o) 0 by
        simpa [β] using congrFun hcoef 0]
  calc
    _ ≤ Real.sqrt (∑ k, (A⁻¹.mulVec o k) ^ 2) := hcoord
    _ ≤ 2 * L * Real.sqrt (∑ k, (o k) ^ 2) :=
      empiricalGramGuard_inv_mulVec_euclidean_le hL hguard o
    _ ≤ 2 * L * ((p + 1 : ℝ) * ‖o‖) := by
      gcongr
      simpa [Nat.cast_add, Nat.cast_one] using
        (euclideanNorm_le_card_mul_piNorm (by omega) o)
    _ = _ := by simp [o]; ring

/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma condKer_winsorization_tail_lintegral_le
    (p : ℕ) (ν L B : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (hB : 1 ≤ B) (t : Bool)
    (x : Score) (hx : x ∈ P.support) :
    (∫⁻ y, ENNReal.ofReal |winsorize B y - y|
      ∂selectedA1A2CondKer P ν L t x) ≤
      ENNReal.ofReal (L * B ^ (-3 : ℤ)) := by
  have hL : 0 ≤ L := le_trans (by norm_num) hP.2.1
  have hBpow : 0 ≤ B ^ (-3 : ℤ) := by positivity
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (|y| ^ (2 + ν) * B ^ (-3 : ℤ))
        ∂selectedA1A2CondKer P ν L t x := by
      apply lintegral_mono
      intro y
      exact ENNReal.ofReal_le_ofReal (by
        simpa [abs_sub_comm] using
          (winsorize_tail_le_moment hP.1 hB (y := y)))
    _ = selectedA1A2CondAbsMoment P ν L t x *
        ENNReal.ofReal (B ^ (-3 : ℤ)) := by
      simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [lintegral_mul_const _ (by fun_prop)]
      rfl
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal (B ^ (-3 : ℤ)) :=
      mul_le_mul_left (hP.2.2.2.2.2.2.2.2.2.1 t x hx) _
    _ = _ := by rw [← ENNReal.ofReal_mul hL]

-- @node: localized_arm_winsorization_tail_lintegral_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma localized_arm_winsorization_tail_lintegral_le
    (p : ℕ) (ν L B : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (hB : 1 ≤ B) (t : Bool)
    (x : Score) (h : ℝ) (hh : 0 < h) :
    (∫⁻ w, (Metric.closedBall x h).indicator
      (fun _ => ENNReal.ofReal |winsorize B (armCoord t w) - armCoord t w|)
      (causalScore w) ∂P.law) ≤
      ENNReal.ofReal ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2)) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hK : Nonempty (A1A2KernelWitness P ν L) :=
    hP.2.2.2.2.2.2.2.1.1
  letI : ProbabilityTheory.IsMarkovKernel (selectedA1A2CondKer P ν L t) :=
    selectedA1A2CondKer_markov hK t
  let μ := Measure.map causalScore P.law
  let F : (Score × ℝ) → ENNReal := fun q =>
    (Metric.closedBall x h).indicator
      (fun _ => ENNReal.ofReal |winsorize B q.2 - q.2|) q.1
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have harm : Measurable (armCoord t) := by
    cases t <;> unfold armCoord <;> simp only [Bool.false_eq_true, if_false,
      if_true] <;> fun_prop
  have hpair : Measurable (fun w => (causalScore w, armCoord t w)) :=
    hscore.prodMk harm
  have hF : Measurable F := by
    apply Measurable.indicator
    · exact (((winsorize_measurable B).comp measurable_snd).sub measurable_snd).abs.ennreal_ofReal
    · exact Metric.isClosed_closedBall.measurableSet.preimage measurable_fst
  have hsupp : ∀ᵐ z ∂μ, z ∈ P.support := by
    change ∀ᵐ z ∂Measure.map causalScore P.law, z ∈ P.support
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  calc
    _ = ∫⁻ q, F q ∂Measure.map (fun w => (causalScore w, armCoord t w)) P.law := by
      rw [lintegral_map hF hpair]
    _ = ∫⁻ z, ∫⁻ y, F (z, y) ∂selectedA1A2CondKer P ν L t z ∂μ := by
      rw [← selectedA1A2CondKer_disint hK t, Measure.lintegral_compProd hF]
    _ ≤ ∫⁻ z, (Metric.closedBall x h).indicator
        (fun _ => ENNReal.ofReal (L * B ^ (-3 : ℤ))) z ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hsupp] with z hz
      by_cases hzb : z ∈ Metric.closedBall x h
      · simp only [F, indicator_of_mem hzb]
        exact condKer_winsorization_tail_lintegral_le p ν L B P hP hB t z hz
      · simp [F, indicator_of_notMem hzb]
    _ = ENNReal.ofReal (L * B ^ (-3 : ℤ)) * μ (Metric.closedBall x h) := by
      rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        setLIntegral_const]
    _ ≤ ENNReal.ofReal (L * B ^ (-3 : ℤ)) * ENNReal.ofReal (4 * L * h ^ 2) :=
      mul_le_mul_right (marginal_closedBall_le p ν L P hP x h hh) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (le_trans (by norm_num) hP.2.1)
        (by positivity : 0 ≤ B ^ (-3 : ℤ)))]

-- @node: winsorizedResidualTail
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
noncomputable def winsorizedResidualTail (p : ℕ) (P : A1A2Law)
    (t : Bool) (x : Score) (h B : ℝ) (j : Fin (p + 1))
    (w : CausalObservation) : ℝ := by
  classical
  let d := signedDistance (knownGeometry P) x (causalScore w)
  exact (if signedArm t d then 1 else 0) * uniformKernel (d / h) *
    polyBasis p (d / h) j *
      (winsorize B (observedOutcome P w) - observedOutcome P w)

-- @node: winsorizedResidualTail_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma winsorizedResidualTail_measurable (p : ℕ) (P : A1A2Law)
    (t : Bool) (x : Score) (h B : ℝ) (j : Fin (p + 1)) :
    Measurable (winsorizedResidualTail p P t x h B j) := by
  classical
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have hA0 : MeasurableSet P.A0 := P.A0_measurable
  have hA1 : MeasurableSet P.A1 := P.A1_measurable
  have htreat : Measurable (treatment P) := by
    unfold treatment
    exact measurable_const.indicator (hA1.preimage hscore)
  have harm (s : Bool) : Measurable (armCoord s) := by
    cases s <;> unfold armCoord <;> simp only [Bool.false_eq_true, if_false,
      if_true] <;> fun_prop
  have hout : Measurable (observedOutcome P) := by
    unfold observedOutcome
    exact (htreat.mul (harm true)).add ((measurable_const.sub htreat).mul (harm false))
  have hd : Measurable (fun w =>
      signedDistance (knownGeometry P) x (causalScore w)) := by
    have hi1 : Measurable (fun w => P.A1.indicator (fun _ => (1 : ℝ))
        (causalScore w)) := measurable_const.indicator (hA1.preimage hscore)
    have hi0 : Measurable (fun w => P.A0.indicator (fun _ => (1 : ℝ))
        (causalScore w)) := measurable_const.indicator (hA0.preimage hscore)
    have hdist : Measurable (fun w => dist (causalScore w) x) :=
      hscore.dist measurable_const
    exact (hi1.sub hi0).mul hdist
  have hsigned : Measurable (fun w => if signedArm t
      (signedDistance (knownGeometry P) x (causalScore w)) then (1 : ℝ) else 0) := by
    cases t
    · exact Measurable.ite (measurableSet_lt hd measurable_const)
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le measurable_const hd)
        measurable_const measurable_const
  unfold winsorizedResidualTail
  dsimp only
  exact (((hsigned.mul (uniformKernel_measurable.comp (hd.div_const h))).mul
    ((polyBasis_apply_measurable p j).comp (hd.div_const h))).mul
      (((winsorize_measurable B).comp hout).sub hout))

-- @node: winsorizedResidualTail_enorm_le_localized_arms
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma winsorizedResidualTail_enorm_le_localized_arms
    (p : ℕ) (P : A1A2Law) (t : Bool) (x : Score) (h B : ℝ)
    (hh : 0 < h) (j : Fin (p + 1)) (w : CausalObservation)
    (hw : causalScore w ∈ P.support) :
    ENNReal.ofReal |winsorizedResidualTail p P t x h B j w| ≤
      (Metric.closedBall x h).indicator (fun _ =>
        ENNReal.ofReal |winsorize B (armCoord false w) - armCoord false w| +
        ENNReal.ofReal |winsorize B (armCoord true w) - armCoord true w|)
        (causalScore w) := by
  classical
  let z := causalScore w
  let d := signedDistance (knownGeometry P) x z
  have hpart : z ∈ P.A0 ∪ P.A1 := by
    rw [P.assignment_partition.1]
    exact hw
  rcases hpart with hz0 | hz1
  · have hz1n : z ∉ P.A1 := fun hz1 => P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
    have hd : d = -dist z x := by
      simp [d, signedDistance, knownGeometry, indicator_of_mem hz0,
        indicator_of_notMem hz1n]
    have hout : observedOutcome P w = armCoord false w := by
      rw [observedOutcome, treatment,
        indicator_of_notMem (by simpa [z] using hz1n)]
      ring
    by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
    · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
      have hball : z ∈ Metric.closedBall x h := by
        rw [Metric.mem_closedBall]
        rw [hd, abs_div, abs_neg, abs_of_pos hh] at hu
        have := (div_le_iff₀ hh).mp hu
        simpa [abs_of_nonneg (dist_nonneg : 0 ≤ dist z x)] using this
      rw [show causalScore w = z by rfl, indicator_of_mem hball]
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [winsorizedResidualTail, show observedOutcome P w = armCoord false w from hout,
        uniformKernel, indicator_of_mem hk]
      split_ifs
      · rw [one_mul, one_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_right
          (show |polyBasis p (d / h) j| ≤ 1 by
            unfold polyBasis
            rw [abs_pow]
            exact pow_le_one₀ (abs_nonneg _) hu) (abs_nonneg _)).trans
          (by simp)
      · simp only [zero_mul, abs_zero]
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    · rw [winsorizedResidualTail]
      have hk' : signedDistance (knownGeometry P) x (causalScore w) / h ∉
          Set.Icc (-1 : ℝ) 1 := by simpa [d] using hk
      simp [uniformKernel, hk']
  · have hz0n : z ∉ P.A0 := fun hz0 => P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
    have hd : d = dist z x := by
      simp [d, signedDistance, knownGeometry, indicator_of_mem hz1,
        indicator_of_notMem hz0n]
    have hout : observedOutcome P w = armCoord true w := by
      rw [observedOutcome, treatment, indicator_of_mem (by simpa [z] using hz1)]
      ring
    by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
    · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
      have hball : z ∈ Metric.closedBall x h := by
        rw [Metric.mem_closedBall]
        rw [hd, abs_div, abs_of_pos hh] at hu
        have := (div_le_iff₀ hh).mp hu
        simpa [abs_of_nonneg (dist_nonneg : 0 ≤ dist z x)] using this
      rw [show causalScore w = z by rfl, indicator_of_mem hball]
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [winsorizedResidualTail, show observedOutcome P w = armCoord true w from hout,
        uniformKernel, indicator_of_mem hk]
      split_ifs
      · rw [one_mul, one_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_right
          (show |polyBasis p (d / h) j| ≤ 1 by
            unfold polyBasis
            rw [abs_pow]
            exact pow_le_one₀ (abs_nonneg _) hu) (abs_nonneg _)).trans
          (by simp)
      · simp only [zero_mul, abs_zero]
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    · rw [winsorizedResidualTail]
      have hk' : signedDistance (knownGeometry P) x (causalScore w) / h ∉
          Set.Icc (-1 : ℝ) 1 := by simpa [d] using hk
      simp [uniformKernel, hk']

-- @node: winsorizedResidualTail_lintegral_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma winsorizedResidualTail_lintegral_le
    (p : ℕ) (ν L B : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (hB : 1 ≤ B) (t : Bool)
    (x : Score) (h : ℝ) (hh : 0 < h) (j : Fin (p + 1)) :
    (∫⁻ w, ENNReal.ofReal |winsorizedResidualTail p P t x h B j w| ∂P.law) ≤
      ENNReal.ofReal (2 * ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2))) := by
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have hsuppMap : ∀ᵐ z ∂Measure.map causalScore P.law, z ∈ P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  have hsupp : ∀ᵐ w ∂P.law, causalScore w ∈ P.support :=
    MeasureTheory.ae_of_ae_map hscore.aemeasurable hsuppMap
  have harmFalse : Measurable (armCoord false) := by
    unfold armCoord
    simp only [Bool.false_eq_true, if_false]
    fun_prop
  calc
    _ ≤ ∫⁻ w, (Metric.closedBall x h).indicator (fun _ =>
        ENNReal.ofReal |winsorize B (armCoord false w) - armCoord false w| +
        ENNReal.ofReal |winsorize B (armCoord true w) - armCoord true w|)
        (causalScore w) ∂P.law :=
      lintegral_mono_ae (hsupp.mono fun w hw =>
        winsorizedResidualTail_enorm_le_localized_arms p P t x h B hh j w hw)
    _ = (∫⁻ w, (Metric.closedBall x h).indicator
          (fun _ => ENNReal.ofReal |winsorize B (armCoord false w) - armCoord false w|)
          (causalScore w) ∂P.law) +
        ∫⁻ w, (Metric.closedBall x h).indicator
          (fun _ => ENNReal.ofReal |winsorize B (armCoord true w) - armCoord true w|)
          (causalScore w) ∂P.law := by
      rw [← lintegral_add_left]
      · apply lintegral_congr
        intro w
        by_cases hw : causalScore w ∈ Metric.closedBall x h <;> simp [hw]
      · apply Measurable.indicator
        · exact (((winsorize_measurable B).comp harmFalse).sub
            harmFalse).abs.ennreal_ofReal
        · exact Metric.isClosed_closedBall.measurableSet.preimage hscore
    _ ≤ ENNReal.ofReal ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2)) +
        ENNReal.ofReal ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2)) :=
      add_le_add
        (localized_arm_winsorization_tail_lintegral_le p ν L B P hP hB false x h hh)
        (localized_arm_winsorization_tail_lintegral_le p ν L B P hP hB true x h hh)
    _ = _ := by
      have hterm : 0 ≤ (L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2) := by
        exact mul_nonneg
          (mul_nonneg (le_trans (by norm_num) hP.2.1) (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) hP.2.1))
            (sq_nonneg h))
      rw [← ENNReal.ofReal_add hterm hterm]
      congr 1
      ring

-- @node: signedLocalPolynomialWeight
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
noncomputable def signedLocalPolynomialWeight (p : ℕ) (P : A1A2Law)
    (t : Bool) (x : Score) (h : ℝ) (j : Fin (p + 1))
    (w : CausalObservation) : ℝ := by
  classical
  let d := signedDistance (knownGeometry P) x (causalScore w)
  exact (if signedArm t d then 1 else 0) * uniformKernel (d / h) *
    polyBasis p (d / h) j

-- @node: causalSignedDistance_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma causalSignedDistance_measurable (P : A1A2Law) (x : Score) :
    Measurable (fun w => signedDistance (knownGeometry P) x (causalScore w)) := by
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have hi1 : Measurable (fun w => P.A1.indicator (fun _ => (1 : ℝ))
      (causalScore w)) := measurable_const.indicator (P.A1_measurable.preimage hscore)
  have hi0 : Measurable (fun w => P.A0.indicator (fun _ => (1 : ℝ))
      (causalScore w)) := measurable_const.indicator (P.A0_measurable.preimage hscore)
  exact (hi1.sub hi0).mul (hscore.dist measurable_const)

-- @node: signedLocalPolynomialWeight_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma signedLocalPolynomialWeight_measurable (p : ℕ) (P : A1A2Law)
    (t : Bool) (x : Score) (h : ℝ) (j : Fin (p + 1)) :
    Measurable (signedLocalPolynomialWeight p P t x h j) := by
  classical
  have hd : Measurable (fun w =>
      signedDistance (knownGeometry P) x (causalScore w)) :=
    causalSignedDistance_measurable P x
  have hsigned : Measurable (fun w => if signedArm t
      (signedDistance (knownGeometry P) x (causalScore w)) then (1 : ℝ) else 0) := by
    cases t
    · exact Measurable.ite (measurableSet_lt hd measurable_const)
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le measurable_const hd)
        measurable_const measurable_const
  unfold signedLocalPolynomialWeight
  dsimp only
  exact (hsigned.mul (uniformKernel_measurable.comp (hd.div_const h))).mul
    ((polyBasis_apply_measurable p j).comp (hd.div_const h))

-- @node: signedLocalPolynomialWeight_abs_le_one
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma signedLocalPolynomialWeight_abs_le_one
    (p : ℕ) (P : A1A2Law) (t : Bool) (x : Score) (h : ℝ)
    (j : Fin (p + 1)) (w : CausalObservation) :
    |signedLocalPolynomialWeight p P t x h j w| ≤ 1 := by
  classical
  let d := signedDistance (knownGeometry P) x (causalScore w)
  by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
  · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
    rw [signedLocalPolynomialWeight, uniformKernel, indicator_of_mem hk]
    split_ifs
    · simp only [one_mul, abs_mul, abs_one, one_mul]
      unfold polyBasis
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hu
    · simp
  · rw [signedLocalPolynomialWeight, uniformKernel]
    have hk' : signedDistance (knownGeometry P) x (causalScore w) / h ∉
        Set.Icc (-1 : ℝ) 1 := by simpa [d] using hk
    simp [hk']

-- @node: observedOutcome_integrable
/-- The observed outcome is integrable under the stated causal law. -/
lemma observedOutcome_integrable (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) : Integrable (observedOutcome P) P.law := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have htreat : Measurable (treatment P) := by
    unfold treatment
    exact measurable_const.indicator (P.A1_measurable.preimage hscore)
  have hexp : 1 ≤ ENNReal.ofReal (2 + ν) := by
    rw [ENNReal.one_le_ofReal]
    linarith [hP.1]
  have hi0 : Integrable (armCoord false) P.law :=
    (P.memLp_armCoord_of_condAbsMoment_le p ν L hP false).integrable hexp
  have hi1 : Integrable (armCoord true) P.law :=
    (P.memLp_armCoord_of_condAbsMoment_le p ν L hP true).integrable hexp
  have htbound : ∀ᵐ w ∂P.law, ‖treatment P w‖ ≤ 1 := by
    filter_upwards with w
    unfold treatment
    by_cases hw : causalScore w ∈ P.A1 <;> simp [hw]
  have hctbound : ∀ᵐ w ∂P.law, ‖1 - treatment P w‖ ≤ 1 := by
    filter_upwards with w
    unfold treatment
    by_cases hw : causalScore w ∈ P.A1 <;> simp [hw]
  unfold observedOutcome
  exact (hi1.bdd_mul htreat.aestronglyMeasurable htbound).add
    (hi0.bdd_mul (measurable_const.sub htreat).aestronglyMeasurable hctbound)

-- @node: rawPopulationResidual
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
noncomputable def rawPopulationResidual (p : ℕ) (P : A1A2Law)
    (t : Bool) (x : Score) (h : ℝ) (j : Fin (p + 1))
    (w : CausalObservation) : ℝ := by
  classical
  let d := signedDistance (knownGeometry P) x (causalScore w)
  exact signedLocalPolynomialWeight p P t x h j w *
      (observedOutcome P w - ∑ k, polyBasis p (d / h) k *
        populationCoefficient P p t x h k)

-- @node: rawPopulationResidual_integral_eq_zero
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma rawPopulationResidual_integral_eq_zero
    (p : ℕ) (ν L : ℝ) (P : A1A2Law) (hP : A1A2Class p ν L P)
    (t : Bool) (x : Score) (hx : x ∈ P.boundary)
    (h : ℝ) (hh : 0 < h) (hhL : h ≤ L⁻¹) (j : Fin (p + 1)) :
    ∫ w, rawPopulationResidual p P t x h j w ∂P.law = 0 := by
  classical
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hnormal := congrFun
    (populationGram_mulVec_populationCoefficient p ν L P hP t x hx h hh hhL) j
  rw [Matrix.mulVec, dotProduct] at hnormal
  have hh0 : h ≠ 0 := hh.ne'
  have hscale : h ^ 2 * h⁻¹ ^ 2 = 1 := by field_simp
  have hweightMeas := signedLocalPolynomialWeight_measurable p P t x h j
  have hobs := observedOutcome_integrable p ν L P hP
  have hfirst : Integrable (fun w =>
      signedLocalPolynomialWeight p P t x h j w * observedOutcome P w) P.law :=
    hobs.bdd_mul hweightMeas.aestronglyMeasurable
      (ae_of_all _ fun w => by
        simpa [Real.norm_eq_abs] using
          signedLocalPolynomialWeight_abs_le_one p P t x h j w)
  have hd := causalSignedDistance_measurable P x
  have hsecondEach (k : Fin (p + 1)) : Integrable (fun w =>
      signedLocalPolynomialWeight p P t x h j w *
        (polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k *
          populationCoefficient P p t x h k)) P.law := by
    have hi := Integrable.of_bound (μ := P.law)
      ((hweightMeas.fun_mul ((polyBasis_apply_measurable p k).comp
        (hd.div_const h))).fun_mul measurable_const).aestronglyMeasurable
      |populationCoefficient P p t x h k| (by
        filter_upwards with w
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have hwgt := signedLocalPolynomialWeight_abs_le_one p P t x h j w
        let d := signedDistance (knownGeometry P) x (causalScore w)
        by_cases hk : d / h ∈ Set.Icc (-1 : ℝ) 1
        · have hu : |d / h| ≤ 1 := by simpa [abs_le] using hk
          have hpoly : |polyBasis p (d / h) k| ≤ 1 := by
            unfold polyBasis
            rw [abs_pow]
            exact pow_le_one₀ (abs_nonneg _) hu
          have hprod := mul_le_mul hwgt hpoly (abs_nonneg _)
            (by norm_num : (0 : ℝ) ≤ 1)
          simpa [d] using mul_le_mul_of_nonneg_right hprod
            (abs_nonneg (populationCoefficient P p t x h k))
        · have hk' : signedDistance (knownGeometry P) x (causalScore w) / h ∉
              Set.Icc (-1 : ℝ) 1 := by simpa [d] using hk
          rw [signedLocalPolynomialWeight]
          simp [uniformKernel, hk'])
    simpa [mul_assoc] using hi
  have hsecond : Integrable (fun w => ∑ k,
      signedLocalPolynomialWeight p P t x h j w *
        (polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k *
          populationCoefficient P p t x h k)) P.law :=
    integrable_finset_sum _ (fun k _ => hsecondEach k)
  have scale_integral (f : CausalObservation → ℝ) :
      (∫ w, f w ∂P.law) = h ^ 2 * ∫ w, h⁻¹ ^ 2 * f w ∂P.law := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    field_simp
  have move_const (k : Fin (p + 1)) :
      (∫ w, signedLocalPolynomialWeight p P t x h j w *
        (polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k *
          populationCoefficient P p t x h k) ∂P.law) =
        (∫ w, signedLocalPolynomialWeight p P t x h j w *
          polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k ∂P.law) *
            populationCoefficient P p t x h k := by
    rw [show (fun w => signedLocalPolynomialWeight p P t x h j w *
        (polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k *
          populationCoefficient P p t x h k)) =
      fun w => (signedLocalPolynomialWeight p P t x h j w *
        polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k) *
          populationCoefficient P p t x h k by funext w; ring,
      integral_mul_const]
  calc
    ∫ w, rawPopulationResidual p P t x h j w ∂P.law =
        h ^ 2 * (populationScore P p t x h j -
          ∑ k, populationGram P p t x h j k *
            populationCoefficient P p t x h k) := by
      simp only [rawPopulationResidual]
      simp_rw [mul_sub, Finset.mul_sum]
      rw [integral_sub hfirst hsecond,
        integral_finset_sum _ (fun k _ => hsecondEach k)]
      simp_rw [move_const]
      rw [scale_integral _]
      rw [show (∑ k, (∫ w, signedLocalPolynomialWeight p P t x h j w *
          polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k
            ∂P.law) * populationCoefficient P p t x h k) =
          ∑ k, (h ^ 2 * ∫ w, h⁻¹ ^ 2 *
            (signedLocalPolynomialWeight p P t x h j w *
              polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) k)
              ∂P.law) * populationCoefficient P p t x h k by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [scale_integral]]
      simp only [signedLocalPolynomialWeight, populationScore, populationGram]
      simp only [signedArm]
      ring_nf
    _ = 0 := by rw [hnormal]; ring

set_option maxHeartbeats 800000 in
-- @node: winsorizedCenteredScore_mean_norm_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma winsorizedCenteredScore_mean_norm_le
    (n p : ℕ) (ν L : ℝ) (P : A1A2Law) (hP : A1A2Class p ν L P)
    (t : Bool) (x : Score) (hx : x ∈ P.boundary)
    (h B : ℝ) (hn : 1 ≤ n) (hh : 0 < h) (hhL : h ≤ L⁻¹) (hB : 1 ≤ B) :
    ‖fun j => ∫ w, winsorizedCenteredScore n p P t x h B w j
        ∂causalSampleLaw P n‖ ≤ 8 * L ^ 2 * B ^ (-3 : ℤ) := by
  classical
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let R : ℝ := 1 + |L * (p + 1 : ℝ) * (16 * L * (2 + L))|
  have hR : 0 < R := by dsimp [R]; positivity
  have hbeta : ∀ k, |populationCoefficient P p t x h k| ≤ R := by
    intro k
    exact populationCoefficient_uniform_bound_explicit p ν L P hP t x h hx hh hhL k
  obtain ⟨A, v, C₀, hC₀, hent⟩ :=
    winsorizedScore_hasVCUniformEntropy_all_nu p L R hR
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hP.2.1
  have hhB : h < B := by
    have hinv : L⁻¹ < 1 := inv_lt_one_of_one_lt₀
      (lt_of_lt_of_le (by norm_num) hP.2.1)
    exact (hhL.trans_lt hinv).trans_le hB
  obtain ⟨_hσ, _hσU, _hA, _hv, hmeas, henv, _hL2, _hcover⟩ :=
    hent ν P hP h B hh hhB hB
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  let idx : SeparableWinsorizedScoreIndex P p h :=
    (⟨h, ⟨le_rfl, by linarith⟩⟩, t, ⟨x, hx⟩,
      populationCoefficient P p t x h, j)
  let g := separableWinsorizedScoreFunction P p h B R idx
  let q := winsorizedResidualTail p P t x h B j
  have hg : Integrable g P.law :=
    Integrable.of_bound (μ := P.law) (hmeas idx).aestronglyMeasurable (C₀ * B)
      (ae_of_all _ fun z => by
        change |g z| ≤ C₀ * B
        exact henv idx z)
  have hqmeas : Measurable q := winsorizedResidualTail_measurable p P t x h B j
  have hqlin := winsorizedResidualTail_lintegral_le p ν L B P hP hB t x h hh j
  have hq : Integrable q P.law := by
    refine ⟨hqmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ w, ‖q w‖ₑ ∂P.law) =
          ∫⁻ w, ENNReal.ofReal |q w| ∂P.law := by
        apply lintegral_congr
        intro w
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal (2 * ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2))) := hqlin
      _ < ∞ := ENNReal.ofReal_lt_top
  have hclip (k : Fin (p + 1)) :
      clip R (populationCoefficient P p t x h k) =
        populationCoefficient P p t x h k := by
    have hk := hbeta k
    rw [abs_le] at hk
    simp [clip, min_eq_right hk.2, max_eq_right hk.1]
  have hsplit (w : CausalObservation) :
      g w = rawPopulationResidual p P t x h j w + q w := by
    simp only [g, idx, q, separableWinsorizedScoreFunction,
      rawPopulationResidual, winsorizedResidualTail, signedLocalPolynomialWeight]
    simp_rw [hclip]
    ring
  have hraw : Integrable (rawPopulationResidual p P t x h j) P.law := by
    have : rawPopulationResidual p P t x h j = g - q := by
      funext w
      change rawPopulationResidual p P t x h j w = g w - q w
      linarith [hsplit w]
    rw [this]
    exact hg.sub hq
  have hrawzero := rawPopulationResidual_integral_eq_zero
    p ν L P hP t x hx h hh hhL j
  have hgint : ∫ w, g w ∂P.law = ∫ w, q w ∂P.law := by
    rw [integral_congr_ae (ae_of_all _ hsplit), integral_add hraw hq, hrawzero,
      zero_add]
  have hg' : Integrable (separableWinsorizedScoreFunction P p h B R idx) P.law := hg
  have hgint' : (∫ z, separableWinsorizedScoreFunction P p h B R idx z ∂P.law) =
      ∫ z, q z ∂P.law := hgint
  have hmean := winsorizedCenteredScore_integral_eq
    n p P t x hx h B R hh hn hbeta j hg'
  rw [hmean, hgint']
  have hint := MeasureTheory.enorm_integral_le_lintegral_enorm q (μ := P.law)
  have hint' : ENNReal.ofReal |∫ w, q w ∂P.law| ≤
      ∫⁻ w, ENNReal.ofReal |q w| ∂P.law := by
    simpa only [← ofReal_norm_eq_enorm, Real.norm_eq_abs] using hint
  have htailENN : ENNReal.ofReal |∫ w, q w ∂P.law| ≤
      ENNReal.ofReal (2 * ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2))) := by
    exact hint'.trans hqlin
  have htail : |∫ w, q w ∂P.law| ≤
      2 * ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2)) := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htailENN
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ h⁻¹ ^ 2)]
  have hcancel : h⁻¹ ^ 2 * h ^ 2 = 1 := by field_simp
  calc
    h⁻¹ ^ 2 * |∫ w, q w ∂P.law| ≤
        h⁻¹ ^ 2 * (2 * ((L * B ^ (-3 : ℤ)) * (4 * L * h ^ 2))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (8 * L ^ 2 * B ^ (-3 : ℤ)) * (h⁻¹ ^ 2 * h ^ 2) := by ring
    _ = 8 * L ^ 2 * B ^ (-3 : ℤ) := by rw [hcancel, mul_one]

-- @node: euclideanCExtEnvelope_abs_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma euclideanCExtEnvelope_abs_le {f : Score → ℝ} {p : ℕ} {L : ℝ}
    {S : Set Score} (hf : EuclideanCExtEnvelope f p L S)
    {x : Score} (hx : x ∈ S) : |f x| ≤ L := by
  rcases hf with ⟨U, hU, hSU, g, hg, hgf, hpartialBdd, hlipBdd, hsum⟩
  have hmem : |g x| ∈ coordinatePartialValues g p S := by
    refine ⟨fun _ => 0, ?_, x, hx, ?_⟩
    · simp [coordinateMultiOrder]
    · unfold coordinatePartial
      simp only [coordinateMultiOrder, Pi.zero_apply, add_zero]
      exact congrArg abs
        (iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := g) (x := x)
          (coordinateDirections (fun _ : Fin 2 => 0))).symm
  have hle : |g x| ≤ sSup (coordinatePartialValues g p S) :=
    le_csSup hpartialBdd hmem
  have hlipnonneg : 0 ≤ sSup (coordinatePartialLipschitzValues g p S) := by
    apply Real.sSup_nonneg
    rintro r ⟨alpha, ha, y, hy, z, hz, hyz, rfl⟩
    positivity
  rw [← hgf hx]
  linarith

set_option maxHeartbeats 800000 in
-- @node: stabilizedLocalPolynomial_boundaryLoss_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma stabilizedLocalPolynomial_boundaryLoss_le
    (n p : ℕ) (ν L Cb h B : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (hCb : 0 ≤ Cb)
    (hn : 1 ≤ n) (hh : 0 < h) (hhL : h ≤ L⁻¹) (hB : 1 ≤ B)
    (hBeq : B = Real.rpow h (-(1 : ℝ) / 3))
    (hbias : causalUniformBiasRatio p ν L h ≤ ENNReal.ofReal Cb)
    (w : CausalSample n) :
    a1a2BoundaryLoss (stabilizedLocalPolynomial n p L h) P w ≤
      ENNReal.ofReal (Cb * h +
        4 * L * (p + 1 : ℝ) * (8 * L ^ 2 * B ^ (-3 : ℤ))) +
      ENNReal.ofReal (4 * L * (p + 1 : ℝ)) *
        winsorizedScoreDeviation n p P h B w +
      ENNReal.ofReal (8 * L ^ 2 * (p + 1 : ℝ)) *
        causalGramDeviation n p P h w := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hP.2.1
  have hqpos : 0 < (p + 1 : ℝ) := by positivity
  have hPfull := hP
  obtain ⟨_hnu, _hL, _hSupport, _hDensCont, _hDens, hMu, _hVar,
    _hMean, _hVariance, _hMoment, hGeom, _hVC, _hGram, _hMass, _hSlice⟩ := hP
  rcases hGeom with ⟨_hA0, _hA1, _hpart, _hdisj, _hbEq, _hbCompact,
    hbSupport, _hrect, _hbmassLo, _hbmassHi⟩
  unfold a1a2BoundaryLoss
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hxsupp : x ∈ P.support := interior_subset (hbSupport hx)
  have hmu (t : Bool) : |P.muPO t x| ≤ L :=
    euclideanCExtEnvelope_abs_le (hMu t) hxsupp
  have htau : |P.tau x| ≤ 2 * L := by
    unfold A1A2Law.tau
    exact (abs_sub _ _).trans (by linarith [hmu true, hmu false])
  let δ : ℝ := (2 * L * (p + 1 : ℝ))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_cases hgood : causalGramDeviation n p P h w ≤ ENNReal.ofReal δ
  · have hguard (t : Bool) : empiricalGramGuard L
        (empiricalGram n p t h (signedDistanceData n P w x)) :=
      empiricalGramGuard_of_deviation_le n p ν L P hPfull h hh hhL w
        (by simpa [δ] using hgood) t x hx
    have hcoef (t : Bool) :
        ENNReal.ofReal |guardedCoefficient n p L t h B
            (signedDistanceData n P w x) 0 -
            populationCoefficient P p t x h 0| ≤
          ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
            (winsorizedScoreDeviation n p P h B w +
              ENNReal.ofReal (8 * L ^ 2 * B ^ (-3 : ℤ))) := by
      let m : Fin (p + 1) → ℝ := fun j => ∫ w',
        winsorizedCenteredScore n p P t x h B w' j ∂causalSampleLaw P n
      let c := winsorizedCenteredScore n p P t x h B w - m
      have hc : ENNReal.ofReal ‖c‖ ≤ winsorizedScoreDeviation n p P h B w := by
        unfold winsorizedScoreDeviation
        exact le_iSup_of_le t (le_iSup_of_le x (le_iSup_of_le hx le_rfl))
      have hm : ‖m‖ ≤ 8 * L ^ 2 * B ^ (-3 : ℤ) :=
        winsorizedCenteredScore_mean_norm_le n p ν L P hPfull t x hx h B hn hh hhL hB
      have hnorm : ‖winsorizedCenteredScore n p P t x h B w‖ ≤
          ‖c‖ + ‖m‖ := by
        have heq : winsorizedCenteredScore n p P t x h B w = c + m := by
          funext j
          simp [c, m]
        rw [heq]
        exact norm_add_le _ _
      have hreal := guardedCoefficient_sub_populationCoefficient_le
        n p ν L h B P hPfull t x hx hh hhL w (hguard t)
      calc
        _ ≤ ENNReal.ofReal (2 * L * (p + 1 : ℝ) *
            ‖winsorizedCenteredScore n p P t x h B w‖) :=
          ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal (2 * L * (p + 1 : ℝ) * (‖c‖ + ‖m‖)) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
        _ = ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
            (ENNReal.ofReal ‖c‖ + ENNReal.ofReal ‖m‖) := by
          rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * L * (p + 1 : ℝ))]
        _ ≤ _ := by
          gcongr
    have hbiasPoint : |(populationCoefficient P p true x h 0 -
        populationCoefficient P p false x h 0) - P.tau x| ≤ Cb * h := by
      have hb : ENNReal.ofReal
          (|(populationCoefficient P p true x h 0 -
            populationCoefficient P p false x h 0) - P.tau x| / h) ≤
          causalUniformBiasRatio p ν L h := by
        unfold causalUniformBiasRatio
        exact le_iSup_of_le P (le_iSup_of_le hPfull
          (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))
      have hb' := hb.trans hbias
      have hr : |(populationCoefficient P p true x h 0 -
          populationCoefficient P p false x h 0) - P.tau x| / h ≤ Cb :=
        (ENNReal.ofReal_le_ofReal_iff hCb).mp hb'
      exact (div_le_iff₀ hh).mp hr
    have hclip : |clip (2 * L)
        (guardedCoefficient n p L true h B (signedDistanceData n P w x) 0 -
          guardedCoefficient n p L false h B (signedDistanceData n P w x) 0) -
        P.tau x| ≤
        |(guardedCoefficient n p L true h B (signedDistanceData n P w x) 0 -
          guardedCoefficient n p L false h B (signedDistanceData n P w x) 0) -
        P.tau x| := by
      simpa [clip, Causalean.Mathlib.Analysis.clipIcc] using
        (Causalean.Mathlib.Analysis.abs_clipIcc_sub_le
          (a := -2 * L) (b := 2 * L) (x :=
            guardedCoefficient n p L true h B (signedDistanceData n P w x) 0 -
              guardedCoefficient n p L false h B (signedDistanceData n P w x) 0)
          (t := P.tau x) (show P.tau x ∈ Set.Icc (-2 * L) (2 * L) from
            ⟨by linarith [(abs_le.mp htau).1], (abs_le.mp htau).2⟩))
    have herr : |(guardedCoefficient n p L true h B
          (signedDistanceData n P w x) 0 -
        guardedCoefficient n p L false h B (signedDistanceData n P w x) 0) -
        P.tau x| ≤
        |guardedCoefficient n p L true h B (signedDistanceData n P w x) 0 -
          populationCoefficient P p true x h 0| +
        |guardedCoefficient n p L false h B (signedDistanceData n P w x) 0 -
          populationCoefficient P p false x h 0| + Cb * h := by
      have hab := abs_add_three
        (guardedCoefficient n p L true h B (signedDistanceData n P w x) 0 -
          populationCoefficient P p true x h 0)
        (populationCoefficient P p false x h 0 -
          guardedCoefficient n p L false h B (signedDistanceData n P w x) 0)
        (populationCoefficient P p true x h 0 -
          populationCoefficient P p false x h 0 - P.tau x)
      calc
        _ = |(guardedCoefficient n p L true h B (signedDistanceData n P w x) 0 -
              populationCoefficient P p true x h 0) +
            (populationCoefficient P p false x h 0 -
              guardedCoefficient n p L false h B (signedDistanceData n P w x) 0) +
            (populationCoefficient P p true x h 0 -
              populationCoefficient P p false x h 0 - P.tau x)| := by ring_nf
        _ ≤ _ := hab.trans (by
          rw [abs_sub_comm (populationCoefficient P p false x h 0)]
          exact add_le_add (add_le_add le_rfl le_rfl) hbiasPoint)
    have hu : geometrySignedDistanceData n (knownGeometry P) w x =
        signedDistanceData n P w x := by
      funext i
      apply Prod.ext
      · simp only [geometrySignedDistanceData, signedDistanceData,
          observedOutcome, treatment, knownGeometry]
        by_cases hi : causalScore (w i) ∈ P.A1 <;>
          simp [Set.indicator, hi]
      · rfl
    simp only [stabilizedLocalPolynomial, hBeq.symm]
    rw [hu]
    apply (ENNReal.ofReal_le_ofReal hclip).trans
    apply (ENNReal.ofReal_le_ofReal herr).trans
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    have hc1 := hcoef true
    have hc0 := hcoef false
    have hgram0 : ENNReal.ofReal (8 * L ^ 2 * (p + 1 : ℝ)) *
        causalGramDeviation n p P h w ≥ 0 := bot_le
    calc
      _ ≤ (ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
          (winsorizedScoreDeviation n p P h B w +
            ENNReal.ofReal (8 * L ^ 2 * B ^ (-3 : ℤ)))) * 2 +
          ENNReal.ofReal (Cb * h) := by
        calc
          _ ≤ (ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
              (winsorizedScoreDeviation n p P h B w +
                ENNReal.ofReal (8 * L ^ 2 * B ^ (-3 : ℤ)))) +
              (ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
              (winsorizedScoreDeviation n p P h B w +
                ENNReal.ofReal (8 * L ^ 2 * B ^ (-3 : ℤ)))) +
              ENNReal.ofReal (Cb * h) := add_le_add (add_le_add hc1 hc0) le_rfl
          _ = _ := by ring
      _ ≤ _ := by
        have hCbH : 0 ≤ Cb * h := mul_nonneg hCb hh.le
        have hK : 0 ≤ 2 * L * (p + 1 : ℝ) := by positivity
        have hM : 0 ≤ 8 * L ^ 2 * B ^ (-3 : ℤ) := by positivity
        have hKM : 0 ≤ 4 * L * (p + 1 : ℝ) *
            (8 * L ^ 2 * B ^ (-3 : ℤ)) := by positivity
        have hK2 : ENNReal.ofReal (2 * L * (p + 1 : ℝ)) * 2 =
            ENNReal.ofReal (4 * L * (p + 1 : ℝ)) := by
          rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul hK]
          congr 1
          ring
        have hKM2 : ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
              ENNReal.ofReal (8 * L ^ 2 * B ^ (-3 : ℤ)) * 2 =
            ENNReal.ofReal (4 * L * (p + 1 : ℝ) *
              (8 * L ^ 2 * B ^ (-3 : ℤ))) := by
          rw [← ENNReal.ofReal_mul hK, show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (mul_nonneg hK hM)]
          congr 1
          ring
        have halg :
            (ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
                (winsorizedScoreDeviation n p P h B w +
                  ENNReal.ofReal (8 * L ^ 2 * B ^ (-3 : ℤ)))) * 2 +
              ENNReal.ofReal (Cb * h) =
            ENNReal.ofReal (Cb * h + 4 * L * (p + 1 : ℝ) *
                (8 * L ^ 2 * B ^ (-3 : ℤ))) +
              ENNReal.ofReal (4 * L * (p + 1 : ℝ)) *
                winsorizedScoreDeviation n p P h B w := by
          rw [ENNReal.ofReal_add hCbH hKM]
          calc
            _ = ENNReal.ofReal (Cb * h) +
                (ENNReal.ofReal (2 * L * (p + 1 : ℝ)) * 2) *
                  winsorizedScoreDeviation n p P h B w +
                ENNReal.ofReal (2 * L * (p + 1 : ℝ)) *
                  ENNReal.ofReal (8 * L ^ 2 * B ^ (-3 : ℤ)) * 2 := by ring
            _ = _ := by rw [hK2, hKM2]; ring
        rw [halg]
        exact le_add_of_nonneg_right bot_le
  · have hest : |stabilizedLocalPolynomial n p L h w (knownGeometry P) x| ≤ 2 * L := by
      simp only [stabilizedLocalPolynomial]
      simpa [clip, Causalean.Mathlib.Analysis.clipIcc] using
        Causalean.Mathlib.Analysis.abs_clipIcc_neg_le (mul_nonneg (by norm_num) hLpos.le)
          (guardedCoefficient n p L true h (Real.rpow h (-(1 : ℝ) / 3))
            (geometrySignedDistanceData n (knownGeometry P) w x) 0 -
           guardedCoefficient n p L false h (Real.rpow h (-(1 : ℝ) / 3))
            (geometrySignedDistanceData n (knownGeometry P) w x) 0)
    have hloss : |stabilizedLocalPolynomial n p L h w (knownGeometry P) x - P.tau x| ≤
        4 * L := (abs_sub _ _).trans (by linarith)
    have hδle : ENNReal.ofReal δ ≤ causalGramDeviation n p P h w :=
      le_of_not_ge hgood
    have hbad : ENNReal.ofReal (4 * L) ≤
        ENNReal.ofReal (8 * L ^ 2 * (p + 1 : ℝ)) *
          causalGramDeviation n p P h w := by
      calc
        ENNReal.ofReal (4 * L) =
            ENNReal.ofReal (8 * L ^ 2 * (p + 1 : ℝ)) * ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * L ^ 2 * (p + 1 : ℝ))]
          apply congrArg ENNReal.ofReal
          dsimp [δ]
          field_simp
          ring
        _ ≤ _ := mul_le_mul_right hδle _
    exact (ENNReal.ofReal_le_ofReal hloss).trans
      (hbad.trans (le_add_of_nonneg_left bot_le))

-- @node: t4Bandwidth
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
noncomputable def t4Bandwidth (n : ℕ) : ℝ := frontierRate (max n 3)

-- @node: t4Bandwidth_eventually_eq_frontierRate
/-- From a sufficiently large sample size onward, the two stated bandwidth schedules coincide. -/
lemma t4Bandwidth_eventually_eq_frontierRate :
    t4Bandwidth =ᶠ[atTop] frontierRate := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  simp [t4Bandwidth, max_eq_left hn]

-- @node: t4Bandwidth_pos
/-- The T4 bandwidth is strictly positive at every sample size. -/
lemma t4Bandwidth_pos (n : ℕ) : 0 < t4Bandwidth n := by
  apply frontierRate_pos
  omega

-- @node: t4Bandwidth_antitone
/-- The T4 bandwidth is nonincreasing as sample size increases. -/
lemma t4Bandwidth_antitone : Antitone t4Bandwidth := by
  intro m n hmn
  unfold t4Bandwidth frontierRate
  apply Real.rpow_le_rpow
  · positivity
  · apply Real.log_div_self_antitoneOn
    · exact Real.exp_one_lt_three.le.trans
        (by exact_mod_cast (show 3 ≤ max m 3 by omega))
    · exact Real.exp_one_lt_three.le.trans
        (by exact_mod_cast (show 3 ≤ max n 3 by omega))
    · exact_mod_cast (max_le_max_right 3 hmn)
  · norm_num

-- @node: t4Bandwidth_tendsto_zero
/-- As sample size grows, the T4 bandwidth converges to zero. -/
lemma t4Bandwidth_tendsto_zero : Tendsto t4Bandwidth atTop (nhds 0) :=
  frontierRate_tendsto_zero.congr' t4Bandwidth_eventually_eq_frontierRate.symm

-- @node: frontierRate_nh2_tendsto_top
/-- As sample size grows, the stated effective sample-size sequence diverges to infinity. -/
lemma frontierRate_nh2_tendsto_top :
    Tendsto (fun n : ℕ => (n : ℝ) * frontierRate n ^ 2) atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat 3]
  simpa [Nat.cast_add, Nat.cast_ofNat] using frontierRate_shift_nh2_tendsto_top

-- @node: t4Bandwidth_nh2_tendsto_top
/-- As sample size grows, the stated effective sample-size sequence diverges to infinity. -/
lemma t4Bandwidth_nh2_tendsto_top :
    Tendsto (fun n : ℕ => (n : ℝ) * t4Bandwidth n ^ 2) atTop atTop :=
  frontierRate_nh2_tendsto_top.congr' (by
    filter_upwards [t4Bandwidth_eventually_eq_frontierRate] with n hn
    rw [hn])

-- @node: t4Bandwidth_maximal_regime_tendsto_top
/-- As sample size grows, the stated effective sample-size sequence diverges to infinity. -/
lemma t4Bandwidth_maximal_regime_tendsto_top (ν : ℝ) (hν : 2 ≤ ν) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) ^ ((1 + ν) / (2 + ν)) * t4Bandwidth n ^ 2 /
        Real.log ((t4Bandwidth n)⁻¹)) atTop atTop := by
  have hexp : 0 < ν / (4 * (2 + ν)) := by positivity
  have hpoly : Tendsto (fun n : ℕ => (n : ℝ) ^ (ν / (4 * (2 + ν))))
      atTop atTop := (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hloglittle := (isLittleO_log_rpow_atTop (r := ν / (4 * (2 + ν))) hexp)
    |>.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hinvlog : Tendsto (fun n : ℕ =>
      ((Real.log (n : ℝ) / (n : ℝ) ^ (ν / (4 * (2 + ν)))))⁻¹)
      atTop atTop := by
    apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
    refine tendsto_nhdsWithin_iff.2 ⟨hloglittle, ?_⟩
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hmain : Tendsto (fun n : ℕ =>
      (n : ℝ) ^ ((1 + ν) / (2 + ν)) * frontierRate n ^ 2 /
        Real.log ((frontierRate n)⁻¹)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop _ hinvlog
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by positivity
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have ha : 0 < frontierRate n := frontierRate_pos (by omega)
    have hloga : Real.log ((frontierRate n)⁻¹) =
        (Real.log (n : ℝ) - Real.log (Real.log (n : ℝ))) / 4 := by
      unfold frontierRate
      rw [Real.log_inv]
      change -Real.log (Real.rpow (Real.log (n : ℝ) / n) (1 / 4)) = _
      rw [show Real.log (Real.rpow (Real.log (n : ℝ) / n) (1 / 4)) =
          (1 / 4 : ℝ) * Real.log (Real.log (n : ℝ) / n) from
          Real.log_rpow (div_pos hlogn hn0) _,
        Real.log_div hlogn.ne' hn0.ne']
      ring
    have hbaseLt : Real.log (n : ℝ) / n < 1 := by
      rw [div_lt_one hn0]
      exact (Real.log_lt_sub_one_of_pos hn0 (by exact_mod_cast (show n ≠ 1 by omega))).trans
        (by linarith)
    have haLt : frontierRate n < 1 := by
      unfold frontierRate
      exact Real.rpow_lt_one (div_pos hlogn hn0).le hbaseLt (by norm_num)
    have hdenpos : 0 < Real.log ((frontierRate n)⁻¹) :=
      Real.log_pos (one_lt_inv_iff₀.mpr ⟨ha, haLt⟩)
    have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
      apply Real.log_pos
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log (Real.exp_pos 1) hn0
        (Real.exp_one_lt_three.trans_le (by exact_mod_cast hn))
    have hdenle : Real.log ((frontierRate n)⁻¹) ≤ Real.log (n : ℝ) := by
      rw [hloga]
      linarith
    have hpow : frontierRate n ^ 2 =
        (Real.log (n : ℝ) / n).rpow (1 / 2 : ℝ) := by
      unfold frontierRate
      have hr := Real.rpow_mul_natCast (div_pos hlogn hn0).le (1 / 4 : ℝ) 2
      norm_num at hr ⊢
      exact hr.symm
    have hnum : (n : ℝ) ^ ((1 + ν) / (2 + ν)) * frontierRate n ^ 2 =
        (n : ℝ) ^ (ν / (2 * (2 + ν))) * Real.sqrt (Real.log (n : ℝ)) := by
      rw [hpow]
      change Real.rpow (n : ℝ) ((1 + ν) / (2 + ν)) *
        Real.rpow (Real.log (n : ℝ) / n) (1 / 2) = _
      rw [show Real.rpow (Real.log (n : ℝ) / n) (1 / 2) =
          Real.rpow (Real.log (n : ℝ)) (1 / 2) /
            Real.rpow (n : ℝ) (1 / 2) from
          Real.div_rpow hlogn.le hn0.le _,
        show Real.rpow (Real.log (n : ℝ)) (1 / 2) =
            Real.sqrt (Real.log (n : ℝ)) from (Real.sqrt_eq_rpow _).symm,
        show Real.rpow (n : ℝ) (1 / 2) = Real.sqrt (n : ℝ) from
          (Real.sqrt_eq_rpow _).symm]
      have hsqrtn : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow _
      rw [hsqrtn]
      field_simp
      rw [← Real.rpow_add hn0]
      congr 1
      field_simp
      ring
    rw [hnum]
    have hsqrtlog : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.2 hlogn
    have hsqrtbound : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      apply (Real.sqrt_le_iff).2
      constructor
      · exact hlogn.le
      · have hlogone : 1 ≤ Real.log (n : ℝ) := by
          rw [← Real.log_exp 1]
          apply Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hn0
          exact Real.exp_one_lt_three.le.trans
            (by exact_mod_cast hn)
        nlinarith
    rw [inv_div]
    apply div_le_div₀
    · exact mul_nonneg (Real.rpow_nonneg hn0.le _) (Real.sqrt_nonneg _)
    · have hpowone : 1 ≤ (n : ℝ) ^ (ν / (4 * (2 + ν))) :=
        Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) hexp.le
      have hpowmono : (n : ℝ) ^ (ν / (4 * (2 + ν))) ≤
          (n : ℝ) ^ (ν / (2 * (2 + ν))) := by
        apply Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ n by omega))
        have hden : 0 < 2 + ν := by linarith
        field_simp [hden.ne']
        nlinarith [hν]
      have hsqrtone : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
        apply (Real.le_sqrt (by norm_num) hlogn.le).2
        have hlogone : 1 ≤ Real.log (n : ℝ) := by
          rw [← Real.log_exp 1]
          apply Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hn0
          exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)
        nlinarith
      calc
        (n : ℝ) ^ (ν / (4 * (2 + ν))) =
            (n : ℝ) ^ (ν / (4 * (2 + ν))) * 1 := by ring
        _ ≤ (n : ℝ) ^ (ν / (2 * (2 + ν))) *
            Real.sqrt (Real.log (n : ℝ)) :=
          mul_le_mul hpowmono hsqrtone (by norm_num)
            (Real.rpow_nonneg hn0.le _)
    · exact hdenpos
    · exact hdenle
  exact hmain.congr' (by
    filter_upwards [t4Bandwidth_eventually_eq_frontierRate] with n hn
    simp only [hn])

-- @node: t4_winsorization_power
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma t4_winsorization_power {h : ℝ} (hh : 0 < h) :
    (Real.rpow h (-(1 : ℝ) / 3)) ^ (-3 : ℤ) = h := by
  calc
    _ = Real.rpow h ((-(1 : ℝ) / 3) * (-3 : ℤ)) :=
      (Real.rpow_mul_intCast hh.le _ _).symm
    _ = h := by
      rw [show ((-(1 : ℝ) / 3) * (-3 : ℤ)) = 1 by norm_num]
      exact Real.rpow_one h

-- @node: t4_frontier_rate_terms_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma t4_frontier_rate_terms_le (n : ℕ) (hn : 3 ≤ n) :
    let h := frontierRate n
    let B := Real.rpow h (-(1 : ℝ) / 3)
    B ^ (-3 : ℤ) ≤ h ∧
      Real.sqrt (Real.log (B / h) / ((n : ℝ) * h ^ 2)) ≤ 2 * h ∧
      B * Real.log (B / h) / ((n : ℝ) * h ^ 2) ≤ 2 * h ∧
      Real.sqrt (Real.log (h⁻¹) / ((n : ℝ) * h ^ 2)) ≤ h := by
  dsimp only
  let h := frontierRate n
  let B := Real.rpow h (-(1 : ℝ) / 3)
  have hn0 : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hh : 0 < h := frontierRate_pos (by omega)
  have hbaseLt : Real.log (n : ℝ) / n < 1 := by
    rw [div_lt_one hn0]
    exact (Real.log_lt_sub_one_of_pos hn0
      (by exact_mod_cast (show n ≠ 1 by omega))).trans (by linarith)
  have hhLt : h < 1 := by
    dsimp [h]
    unfold frontierRate
    exact Real.rpow_lt_one (div_pos hlogn hn0).le hbaseLt (by norm_num)
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    apply Real.log_pos
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log (Real.exp_pos 1) hn0
      (Real.exp_one_lt_three.trans_le (by exact_mod_cast hn))
  have hlogh : Real.log (h⁻¹) =
      (Real.log (n : ℝ) - Real.log (Real.log (n : ℝ))) / 4 := by
    dsimp [h]
    unfold frontierRate
    rw [Real.log_inv]
    change -Real.log (Real.rpow (Real.log (n : ℝ) / n) (1 / 4)) = _
    rw [show Real.log (Real.rpow (Real.log (n : ℝ) / n) (1 / 4)) =
        (1 / 4 : ℝ) * Real.log (Real.log (n : ℝ) / n) from
        Real.log_rpow (div_pos hlogn hn0) _,
      Real.log_div hlogn.ne' hn0.ne']
    ring
  have hlogh0 : 0 ≤ Real.log (h⁻¹) :=
    Real.log_nonneg ((one_le_inv₀ hh).2 hhLt.le)
  have hloghle : Real.log (h⁻¹) ≤ Real.log (n : ℝ) := by
    rw [hlogh]
    linarith
  have hBpos : 0 < B := Real.rpow_pos_of_pos hh _
  have hlogB : Real.log (B / h) = (4 / 3 : ℝ) * Real.log (h⁻¹) := by
    rw [Real.log_div hBpos.ne' hh.ne', show Real.log B =
        (-(1 : ℝ) / 3) * Real.log h from Real.log_rpow hh _,
      Real.log_inv]
    ring
  have hlogB0 : 0 ≤ Real.log (B / h) := by rw [hlogB]; positivity
  have hlogBle : Real.log (B / h) ≤ 2 * Real.log (n : ℝ) := by
    rw [hlogB]
    nlinarith
  have hfour := t4_frontierRate_fourth_power n (by omega)
  have hden : 0 < (n : ℝ) * h ^ 2 := mul_pos hn0 (sq_pos_of_pos hh)
  have hratio : Real.log (n : ℝ) / ((n : ℝ) * h ^ 2) = h ^ 2 := by
    rw [← hfour]
    field_simp
    ring
  have hBmul : B * h ≤ 1 := by
    have heq : B * h = Real.rpow h (2 / 3 : ℝ) := by
      dsimp [B]
      calc
        Real.rpow h (-(1 : ℝ) / 3) * h =
            Real.rpow h (-(1 : ℝ) / 3) * Real.rpow h 1 := by
              exact congrArg (fun z => Real.rpow h (-(1 : ℝ) / 3) * z)
                (Real.rpow_one h).symm
        _ = Real.rpow h ((-(1 : ℝ) / 3) + 1) :=
          (Real.rpow_add hh _ _).symm
        _ = Real.rpow h (2 / 3 : ℝ) := by congr 1 <;> ring
    rw [heq]
    exact Real.rpow_le_one hh.le hhLt.le (by norm_num)
  refine ⟨le_of_eq (t4_winsorization_power hh), ?_, ?_, ?_⟩
  · apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hfrac : Real.log (B / h) / ((n : ℝ) * h ^ 2) ≤ 2 * h ^ 2 := by
        calc
          _ ≤ (2 * Real.log (n : ℝ)) / ((n : ℝ) * h ^ 2) :=
            div_le_div_of_nonneg_right hlogBle hden.le
          _ = 2 * h ^ 2 := by rw [mul_div_assoc, hratio]
      exact hfrac.trans (by nlinarith [sq_nonneg h])
  · calc
      B * Real.log (B / h) / ((n : ℝ) * h ^ 2) =
          B * (Real.log (B / h) / ((n : ℝ) * h ^ 2)) := by ring
      _ ≤ B * (2 * h ^ 2) := by
        gcongr
        calc
          _ ≤ (2 * Real.log (n : ℝ)) / ((n : ℝ) * h ^ 2) :=
            div_le_div_of_nonneg_right hlogBle hden.le
          _ = 2 * h ^ 2 := by rw [mul_div_assoc, hratio]
      _ ≤ 2 * h := by nlinarith [hBmul]
  · apply (Real.sqrt_le_iff).2
    constructor
    · exact hh.le
    · calc
        Real.log (h⁻¹) / ((n : ℝ) * h ^ 2) ≤
            Real.log (n : ℝ) / ((n : ℝ) * h ^ 2) :=
          div_le_div_of_nonneg_right hloghle hden.le
        _ = h ^ 2 := hratio

/-- Uniform outer risk of the explicit estimator at the frontier bandwidth. -/
noncomputable def stabilizedLocalPolynomialOuterRisk
    (n p : ℕ) (ν L : ℝ) : ℝ≥0∞ :=
  ⨆ P : A1A2Law, ⨆ (_hP : A1A2Class p ν L P),
    MeasureTheory.outerLIntegral (causalSampleLaw P n)
      (a1a2BoundaryLoss
        (stabilizedLocalPolynomial n p L (frontierRate n)) P)

-- @node: prop:cty-a1-a2-winsorized-expected-outer-upper
/-- At `h_n=a_n` and `B_n=a_n⁻¹ᐟ³`, the explicit clipped and Gram-stabilized
rule has uniform outer risk at most a constant multiple of `a_n`. -/
theorem cty_a1_a2_winsorized_expected_outer_upper
    (p : ℕ) (ν L : ℝ) (hν : 2 ≤ ν) (hL : 4 ≤ L)
    (hId : CtyDistanceIdentification p ν L)
    (hBias : CtyUniformFirstOrderBias p L)
    (hMax : CtyExpectedLocalPolynomialMaximalBounds p ν L) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      stabilizedLocalPolynomialOuterRisk n p ν L ≤
        ENNReal.ofReal (C * frontierRate n) := by
  obtain ⟨Cb₀, hCb₀, hBiasBound⟩ := hBias
  obtain ⟨Cg, hCg, hMaxBound⟩ := hMax
  obtain ⟨Cs, hCs, hScoreBound⟩ :=
    cty_winsorized_score_maximal_bound p L
  let Cb : ℝ := Cb₀ + 1
  let q : ℝ := p + 1
  let C : ℝ := Cb + 32 * L ^ 3 * q +
    16 * L * q * Cs + 8 * L ^ 2 * q * Cg
  have hLpos : 0 < L := by linarith
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hCb : 0 < Cb := by dsimp [Cb]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hbiasLim := hBiasBound ν hν t4Bandwidth t4Bandwidth_pos
    t4Bandwidth_antitone t4Bandwidth_tendsto_zero t4Bandwidth_nh2_tendsto_top
  have hCbLt : ENNReal.ofReal Cb₀ < ENNReal.ofReal Cb := by
    apply (ENNReal.ofReal_lt_ofReal_iff hCb).2
    dsimp [Cb]
    linarith
  have hbiasT4 : ∀ᶠ n in atTop,
      causalUniformBiasRatio p ν L (t4Bandwidth n) ≤ ENNReal.ofReal Cb :=
    (eventually_lt_of_limsup_lt (hbiasLim.trans_lt hCbLt)).mono
      (fun _ hn => hn.le)
  have hbiasEv : ∀ᶠ n in atTop,
      causalUniformBiasRatio p ν L (frontierRate n) ≤ ENNReal.ofReal Cb := by
    filter_upwards [hbiasT4, t4Bandwidth_eventually_eq_frontierRate] with n hb hn
    simpa [hn] using hb
  have hmaxT4 := hMaxBound t4Bandwidth t4Bandwidth_pos
    t4Bandwidth_tendsto_zero (t4Bandwidth_maximal_regime_tendsto_top ν hν)
  have hmaxEv : ∀ᶠ n in atTop, ∀ P : A1A2Law, A1A2Class p ν L P →
      MeasureTheory.outerLIntegral (causalSampleLaw P n)
          (causalGramDeviation n p P (frontierRate n)) ≤
        ENNReal.ofReal (Cg * Real.sqrt
          (Real.log ((frontierRate n)⁻¹) /
            ((n : ℝ) * (frontierRate n) ^ 2))) := by
    filter_upwards [hmaxT4, t4Bandwidth_eventually_eq_frontierRate] with n hm hn
    simpa [hn] using fun P hP => (hm P hP).1
  have hhLEv : ∀ᶠ n in atTop, frontierRate n ≤ L⁻¹ :=
    ((tendsto_order.1 frontierRate_tendsto_zero).2 _ (by positivity)).mono
      (fun _ hn => hn.le)
  apply Filter.eventually_atTop.1
  filter_upwards [eventually_ge_atTop (3 : ℕ), hbiasEv, hmaxEv, hhLEv] with
      n hn hbiasN hgramN hhL
  unfold stabilizedLocalPolynomialOuterRisk
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hn1 : 1 ≤ n := by omega
  have hh : 0 < frontierRate n := frontierRate_pos (by omega)
  have hhOne : frontierRate n ≤ 1 := by
    have hbaseLt : Real.log (n : ℝ) / n < 1 := by
      have hn0 : (0 : ℝ) < n := by positivity
      rw [div_lt_one hn0]
      exact (Real.log_lt_sub_one_of_pos hn0
        (by exact_mod_cast (show n ≠ 1 by omega))).trans (by linarith)
    unfold frontierRate
    exact (Real.rpow_lt_one
      (div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
        (by positivity)) hbaseLt (by norm_num)).le
  let B : ℝ := Real.rpow (frontierRate n) (-(1 : ℝ) / 3)
  have hB : 1 ≤ B := by
    dsimp [B]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hhOne (by norm_num)
  obtain ⟨hBtail, hscoreRoot, hscoreLinear, hgramRoot⟩ :=
    t4_frontier_rate_terms_le n hn
  change B ^ (-3 : ℤ) ≤ frontierRate n at hBtail
  change Real.sqrt (Real.log (B / frontierRate n) /
      ((n : ℝ) * frontierRate n ^ 2)) ≤ 2 * frontierRate n at hscoreRoot
  change B * Real.log (B / frontierRate n) /
      ((n : ℝ) * frontierRate n ^ 2) ≤ 2 * frontierRate n at hscoreLinear
  have hpoint (w : CausalSample n) :=
    stabilizedLocalPolynomial_boundaryLoss_le n p ν L Cb
      (frontierRate n) B P hP hCb.le hn1 hh hhL hB rfl hbiasN w
  let μ := causalSampleLaw P n
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, causalSampleLaw]
    infer_instance
  let c₀ : ℝ≥0∞ := ENNReal.ofReal (Cb * frontierRate n +
    4 * L * q * (8 * L ^ 2 * B ^ (-3 : ℤ)))
  let cs : ℝ≥0∞ := ENNReal.ofReal (4 * L * q)
  let cg : ℝ≥0∞ := ENNReal.ofReal (8 * L ^ 2 * q)
  have hcs0 : cs ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by
    positivity))
  have hcg0 : cg ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by
    positivity))
  have houter :
      MeasureTheory.outerLIntegral μ
          (a1a2BoundaryLoss
            (stabilizedLocalPolynomial n p L (frontierRate n)) P) ≤
        c₀ +
          cs * MeasureTheory.outerLIntegral μ
            (winsorizedScoreDeviation n p P (frontierRate n) B) +
          cg * MeasureTheory.outerLIntegral μ
            (causalGramDeviation n p P (frontierRate n)) := by
    calc
      _ ≤ MeasureTheory.outerLIntegral μ (fun w =>
          c₀ + (cs * winsorizedScoreDeviation n p P (frontierRate n) B w +
            cg * causalGramDeviation n p P (frontierRate n) w)) := by
        apply outerLIntegral_mono
        intro w
        simpa [c₀, cs, cg, q, add_assoc] using hpoint w
      _ ≤ MeasureTheory.outerLIntegral μ (fun _ => c₀) +
          MeasureTheory.outerLIntegral μ (fun w =>
            cs * winsorizedScoreDeviation n p P (frontierRate n) B w +
              cg * causalGramDeviation n p P (frontierRate n) w) :=
        outerLIntegral_add_le _ _ _
      _ ≤ c₀ + (MeasureTheory.outerLIntegral μ (fun w =>
            cs * winsorizedScoreDeviation n p P (frontierRate n) B w) +
          MeasureTheory.outerLIntegral μ (fun w =>
            cg * causalGramDeviation n p P (frontierRate n) w)) := by
        gcongr
        · exact (outerLIntegral_const_probability μ c₀).le
        · exact outerLIntegral_add_le _ _ _
      _ ≤ c₀ +
          cs * MeasureTheory.outerLIntegral μ
            (winsorizedScoreDeviation n p P (frontierRate n) B) +
          cg * MeasureTheory.outerLIntegral μ
            (causalGramDeviation n p P (frontierRate n)) := by
        rw [add_assoc]
        gcongr
        · exact outerLIntegral_const_mul_le μ cs hcs0 ENNReal.ofReal_ne_top _
        · exact outerLIntegral_const_mul_le μ cg hcg0 ENNReal.ofReal_ne_top _
  have hscoreN := hScoreBound ν P hP n (frontierRate n) B
    hn1 hh hhL hB
  have hc₀ : c₀ ≤ ENNReal.ofReal ((Cb + 32 * L ^ 3 * q) * frontierRate n) := by
    dsimp [c₀]
    apply ENNReal.ofReal_le_ofReal
    calc
      Cb * frontierRate n + 4 * L * q * (8 * L ^ 2 * B ^ (-3 : ℤ)) ≤
          Cb * frontierRate n + 4 * L * q * (8 * L ^ 2 * frontierRate n) := by
        gcongr
      _ = (Cb + 32 * L ^ 3 * q) * frontierRate n := by ring
  have hscoreTerm : cs * MeasureTheory.outerLIntegral μ
        (winsorizedScoreDeviation n p P (frontierRate n) B) ≤
      ENNReal.ofReal ((16 * L * q * Cs) * frontierRate n) := by
    calc
      _ ≤ cs * ENNReal.ofReal (Cs *
          (Real.sqrt (Real.log (B / frontierRate n) /
              ((n : ℝ) * frontierRate n ^ 2)) +
            B * Real.log (B / frontierRate n) /
              ((n : ℝ) * frontierRate n ^ 2))) :=
        mul_le_mul_right hscoreN cs
      _ = ENNReal.ofReal ((4 * L * q) * (Cs *
          (Real.sqrt (Real.log (B / frontierRate n) /
              ((n : ℝ) * frontierRate n ^ 2)) +
            B * Real.log (B / frontierRate n) /
              ((n : ℝ) * frontierRate n ^ 2)))) := by
        dsimp [cs]
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * L * q)]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hsum : Real.sqrt (Real.log (B / frontierRate n) /
              ((n : ℝ) * frontierRate n ^ 2)) +
            B * Real.log (B / frontierRate n) /
              ((n : ℝ) * frontierRate n ^ 2) ≤ 4 * frontierRate n := by
          linarith
        calc
          (4 * L * q) * (Cs * (Real.sqrt (Real.log (B / frontierRate n) /
                ((n : ℝ) * frontierRate n ^ 2)) +
              B * Real.log (B / frontierRate n) /
                ((n : ℝ) * frontierRate n ^ 2))) =
              (4 * L * q * Cs) *
                (Real.sqrt (Real.log (B / frontierRate n) /
                    ((n : ℝ) * frontierRate n ^ 2)) +
                  B * Real.log (B / frontierRate n) /
                    ((n : ℝ) * frontierRate n ^ 2)) := by ring
          _ ≤ (4 * L * q * Cs) * (4 * frontierRate n) := by
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = (16 * L * q * Cs) * frontierRate n := by ring
  have hgramTerm : cg * MeasureTheory.outerLIntegral μ
        (causalGramDeviation n p P (frontierRate n)) ≤
      ENNReal.ofReal ((8 * L ^ 2 * q * Cg) * frontierRate n) := by
    calc
      _ ≤ cg * ENNReal.ofReal (Cg * Real.sqrt
          (Real.log ((frontierRate n)⁻¹) /
            ((n : ℝ) * frontierRate n ^ 2))) :=
        mul_le_mul_right (hgramN P hP) cg
      _ = ENNReal.ofReal ((8 * L ^ 2 * q) *
          (Cg * Real.sqrt (Real.log ((frontierRate n)⁻¹) /
            ((n : ℝ) * frontierRate n ^ 2)))) := by
        dsimp [cg]
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * L ^ 2 * q)]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        calc
          (8 * L ^ 2 * q) *
              (Cg * Real.sqrt (Real.log ((frontierRate n)⁻¹) /
                ((n : ℝ) * frontierRate n ^ 2))) =
              (8 * L ^ 2 * q * Cg) *
                Real.sqrt (Real.log ((frontierRate n)⁻¹) /
                  ((n : ℝ) * frontierRate n ^ 2)) := by ring
          _ ≤ (8 * L ^ 2 * q * Cg) * frontierRate n := by
            exact mul_le_mul_of_nonneg_left hgramRoot (by positivity)
  apply houter.trans
  calc
    c₀ + cs * MeasureTheory.outerLIntegral μ
          (winsorizedScoreDeviation n p P (frontierRate n) B) +
        cg * MeasureTheory.outerLIntegral μ
          (causalGramDeviation n p P (frontierRate n)) ≤
        ENNReal.ofReal ((Cb + 32 * L ^ 3 * q) * frontierRate n) +
          ENNReal.ofReal ((16 * L * q * Cs) * frontierRate n) +
          ENNReal.ofReal ((8 * L ^ 2 * q * Cg) * frontierRate n) := by
      gcongr
    _ = ENNReal.ofReal (C * frontierRate n) := by
      rw [← ENNReal.ofReal_add
          (by positivity : 0 ≤ (Cb + 32 * L ^ 3 * q) * frontierRate n)
          (by positivity : 0 ≤ (16 * L * q * Cs) * frontierRate n),
        ← ENNReal.ofReal_add
          (by positivity : 0 ≤
            (Cb + 32 * L ^ 3 * q) * frontierRate n +
              (16 * L * q * Cs) * frontierRate n)
          (by positivity : 0 ≤ (8 * L ^ 2 * q * Cg) * frontierRate n)]
      apply congrArg ENNReal.ofReal
      dsimp [C]
      ring

end CausalSmith.Stat.BddUniformLogPenalty
