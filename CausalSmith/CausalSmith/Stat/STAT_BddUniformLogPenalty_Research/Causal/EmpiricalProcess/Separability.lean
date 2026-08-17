import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Estimator
import Causalean.Stat.Concentration.Covering.Separable
import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.Separability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Countable reduction for the winsorized score class

This is the bounded residual identified in round 13.  The property below says
that a continuum-indexed empirical-process supremum has a fixed countable
pointwise-dense subfamily.  It is the bridge from outer expectation to the
countable-index concentration API.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal
open Causalean.Stat.Concentration

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Index `(arm, center, coefficient vector, coordinate)` for the enlarged
winsorized score class. -/
abbrev WinsorizedScoreIndex (p : ℕ) :=
  Bool × Score × (Fin (p + 1) → ℝ) × Fin (p + 1)

/-- Index for the separable one-sided bandwidth enlargement.  Centers are
restricted to the treatment boundary and the support bandwidth approaches
the target bandwidth `h` from the half-open interval `[h,2h)`. -/
abbrev SeparableWinsorizedScoreIndex (P : A1A2Law) (p : ℕ) (h : ℝ) :=
  {q : ℝ // q ∈ Set.Ico h (2 * h)} × Bool ×
    {x : Score // x ∈ P.boundary} × (Fin (p + 1) → ℝ) × Fin (p + 1)

/-- One scalar coordinate of the enlarged bounded-coefficient winsorized
score class.  Coefficients are clipped componentwise at the supplied radius,
so this is a genuine constant-envelope class. -/
noncomputable def winsorizedScoreFunction (P : A1A2Law) (p : ℕ)
    (h B C : ℝ) (i : WinsorizedScoreIndex p) (z : CausalObservation) : ℝ := by
  classical
  let t := i.1
  let x := i.2.1
  let b := i.2.2.1
  let j := i.2.2.2
  let d := signedDistance (knownGeometry P) x (causalScore z)
  exact (if signedArm t d then 1 else 0) *
    uniformKernel (d / h) * polyBasis p (d / h) j *
      (winsorize B (observedOutcome P z) -
        ∑ k, polyBasis p (d / h) k * clip C (b k))

/-- The one-sided support-bandwidth enlargement of the fixed-bandwidth score.
The polynomial arguments remain normalized by `h`; only the closed kernel
support uses `q`.  Thus the fixed class embeds at `q=h`, while rational
bandwidths decreasing to `h` resolve sample points on moving ball boundaries. -/
noncomputable def separableWinsorizedScoreFunction (P : A1A2Law) (p : ℕ)
    (h B C : ℝ) (i : SeparableWinsorizedScoreIndex P p h)
    (z : CausalObservation) : ℝ := by
  classical
  let q := i.1.1
  let t := i.2.1
  let x := i.2.2.1.1
  let b := i.2.2.2.1
  let j := i.2.2.2.2
  let d := signedDistance (knownGeometry P) x (causalScore z)
  exact (if signedArm t d then 1 else 0) *
    uniformKernel (d / q) * polyBasis p (d / h) j *
      (winsorize B (observedOutcome P z) -
        ∑ k, polyBasis p (d / h) k * clip C (b k))

/-- The centered empirical average of a real-valued function. -/
lemma winsorizedScore_boundary_volume_zero (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) :
    volume P.boundary = 0 := by
  rcases hP with ⟨hν, hL, hrect, hdcont, hdbd, hmu, hsig, hmean, hvar,
    hmom, hgeom, hvc, hgram, hlocal, hslice⟩
  rcases hgeom with ⟨hA0, hA1, hpart, hdisj, hbdy, hbcompact, hbsub,
    hbrect, hH1lo, hH1hi⟩
  have hH1 : Measure.hausdorffMeasure 1 P.boundary ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH1hi
  have hH2 : Measure.hausdorffMeasure 2 P.boundary = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) P.boundary).resolve_right hH1
  have hdim : Module.finrank ℝ Score = 2 := by simp
  letI : Measure.IsAddHaarMeasure (Measure.hausdorffMeasure 2 : Measure Score) := by
    have h := MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := Score)
    rw [hdim] at h
    simp only [Nat.cast_ofNat] at h
    exact h
  have hvolEq : (volume : Measure Score) =
      Measure.addHaarScalarFactor (volume : Measure Score)
        (Measure.hausdorffMeasure 2 : Measure Score) •
          (Measure.hausdorffMeasure 2 : Measure Score) := by
    exact Measure.isAddLeftInvariant_eq_smul (volume : Measure Score)
      (Measure.hausdorffMeasure 2 : Measure Score)
  rw [hvolEq, Measure.smul_apply, hH2]
  simp


-- @node: winsorizedScore_boundary_nonempty
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma winsorizedScore_boundary_nonempty (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) : P.boundary.Nonempty := by
  rcases hP with ⟨hν, hL, hrect, hdcont, hdbd, hmu, hsig, hmean, hvar,
    hmom, hgeom, hvc, hgram, hlocal, hslice⟩
  rcases hgeom with ⟨hA0, hA1, hpart, hdisj, hbdy, hbcompact, hbsub,
    hbrect, hH1lo, hH1hi⟩
  by_contra hn
  rw [not_nonempty_iff_eq_empty.mp hn, measure_empty] at hH1lo
  have hLpos : 0 < L := by linarith
  exact (not_lt_of_ge hH1lo) (ENNReal.ofReal_pos.2 (inv_pos.2 hLpos))

-- @node: winsorizedScore_boundary_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma winsorizedScore_boundary_measurable (p : ℕ) (ν L : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) : MeasurableSet P.boundary := by
  rcases hP with ⟨hν, hL, hrect, hdcont, hdbd, hmu, hsig, hmean, hvar,
    hmom, hgeom, hvc, hgram, hlocal, hslice⟩
  exact hgeom.2.2.2.2.2.1.measurableSet

-- @node: uniformKernel_div_eq_if_abs_le
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma uniformKernel_div_eq_if_abs_le (d q : ℝ) (hq : 0 < q) :
    uniformKernel (d / q) = if |d| ≤ q then 1 else 0 := by
  unfold uniformKernel
  have heq : d / q ∈ Set.Icc (-1 : ℝ) 1 ↔ |d| ≤ q := by
    rw [abs_le]
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · have := (le_div_iff₀ hq).mp hlo
        nlinarith
      · exact (div_le_iff₀ hq).mp hhi |>.trans_eq (one_mul q)
    · rintro ⟨hlo, hhi⟩
      constructor
      · apply (le_div_iff₀ hq).2
        nlinarith
      · exact (div_le_iff₀ hq).2 (by simpa using hhi)
  split_ifs with hu
  · rw [indicator_of_mem (heq.mpr hu)]
  · rw [indicator_of_notMem (fun hd => hu (heq.mp hd))]

-- @node: separableWinsorizedScoreFunction_bound
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma separableWinsorizedScoreFunction_bound (P : A1A2Law) (p : ℕ) (h B C : ℝ)
    (hh : 0 < h) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (i : SeparableWinsorizedScoreIndex P p h) (z : CausalObservation) :
    |separableWinsorizedScoreFunction P p h B C i z| ≤
      (2 : ℝ) ^ p *
        (|armCoord false z| + |armCoord true z| +
          (p + 1 : ℝ) * (2 : ℝ) ^ p * C) := by
  classical
  let d := signedDistance (knownGeometry P) i.2.2.1.1 (causalScore z)
  have hq : 0 < i.1.1 := lt_of_lt_of_le hh i.1.2.1
  dsimp [separableWinsorizedScoreFunction]
  rw [show uniformKernel (d / i.1.1) = if |d| ≤ i.1.1 then 1 else 0 from
    uniformKernel_div_eq_if_abs_le d i.1.1 hq]
  by_cases hdq : |d| ≤ i.1.1
  · rw [if_pos hdq]
    have hu : |d / h| ≤ 2 := by
      rw [abs_div, abs_of_pos hh]
      have hqh : i.1.1 / h < 2 := (div_lt_iff₀ hh).2 i.1.2.2
      exact (div_le_div_of_nonneg_right hdq hh.le).trans hqh.le
    have hpoly (k : Fin (p + 1)) : |polyBasis p (d / h) k| ≤ (2 : ℝ) ^ p := by
      unfold polyBasis
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) hu k).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ k.isLt))
    have hclip (y : ℝ) : |clip C y| ≤ C := by
      unfold clip
      rw [abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith) (min_le_left _ _)
    have hsum : |∑ k, polyBasis p (d / h) k * clip C (i.2.2.2.1 k)| ≤
        (p + 1 : ℝ) * (2 : ℝ) ^ p * C := by
      calc
        _ ≤ ∑ k, |polyBasis p (d / h) k * clip C (i.2.2.2.1 k)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (p + 1), (2 : ℝ) ^ p * C := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (hpoly k) (hclip _) (abs_nonneg _) (by positivity)
        _ = (p + 1 : ℝ) * (2 : ℝ) ^ p * C := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring
    have hwin : |winsorize B (observedOutcome P z)| ≤
        |armCoord false z| + |armCoord true z| := by
      have hw : |winsorize B (observedOutcome P z)| ≤ |observedOutcome P z| := by
        unfold winsorize
        split_ifs with hy hy0
        · rw [abs_neg, abs_of_nonneg (le_min (abs_nonneg _) hB)]
          exact min_le_left _ _
        · simp [hy0]
        · rw [abs_of_nonneg (le_min (abs_nonneg _) hB)]
          exact min_le_left _ _
      refine hw.trans ?_
      unfold observedOutcome treatment
      by_cases hz1 : causalScore z ∈ P.A1
      · simp [indicator_of_mem hz1]
      · simp [indicator_of_notMem hz1]
    have hres : |winsorize B (observedOutcome P z) -
        ∑ k, polyBasis p (d / h) k * clip C (i.2.2.2.1 k)| ≤
        |armCoord false z| + |armCoord true z| +
          (p + 1 : ℝ) * (2 : ℝ) ^ p * C :=
      (abs_sub _ _).trans (add_le_add hwin hsum)
    rw [abs_mul, abs_mul, abs_mul]
    split_ifs
    · simp only [abs_one, one_mul]
      exact mul_le_mul (hpoly i.2.2.2.2) hres (abs_nonneg _) (by positivity)
    · simp
      positivity
  · rw [if_neg hdq]
    simp [d, uniformKernel_div_eq_if_abs_le, hq, hdq]
    positivity

-- @node: separableWinsorizedScoreFunction_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma separableWinsorizedScoreFunction_measurable (P : A1A2Law) (p : ℕ)
    (h B C : ℝ) (i : SeparableWinsorizedScoreIndex P p h) :
    Measurable (separableWinsorizedScoreFunction P p h B C i) := by
  classical
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have htreat : Measurable (treatment P) := by
    unfold treatment
    exact measurable_const.indicator (P.A1_measurable.preimage hscore)
  have harm (t : Bool) : Measurable (armCoord t) := by
    cases t <;> unfold armCoord <;> simp only [Bool.false_eq_true, if_false,
      if_true] <;> fun_prop
  have hout : Measurable (observedOutcome P) := by
    unfold observedOutcome
    exact (htreat.mul (harm true)).add
      ((measurable_const.sub htreat).mul (harm false))
  have hd : Measurable (fun z => signedDistance (knownGeometry P)
      i.2.2.1.1 (causalScore z)) := by
    have hi1 : Measurable (fun z => P.A1.indicator (fun _ => (1 : ℝ))
        (causalScore z)) := measurable_const.indicator (P.A1_measurable.preimage hscore)
    have hi0 : Measurable (fun z => P.A0.indicator (fun _ => (1 : ℝ))
        (causalScore z)) := measurable_const.indicator (P.A0_measurable.preimage hscore)
    have hdist : Measurable (fun z => dist (causalScore z) i.2.2.1.1) :=
      hscore.dist measurable_const
    exact (hi1.sub hi0).mul hdist
  have hsigned : Measurable (fun z => if signedArm i.2.1
      (signedDistance (knownGeometry P) i.2.2.1.1 (causalScore z))
      then (1 : ℝ) else 0) := by
    cases i.2.1
    · exact Measurable.ite (measurableSet_lt hd measurable_const)
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le measurable_const hd)
        measurable_const measurable_const
  unfold separableWinsorizedScoreFunction
  dsimp only
  exact (((hsigned.mul (uniformKernel_measurable.comp (hd.div_const i.1.1))).mul
    ((polyBasis_apply_measurable p i.2.2.2.2).comp (hd.div_const h))).mul
      (((winsorize_measurable B).comp hout).sub
        (Finset.measurable_sum _ fun k _ =>
          ((polyBasis_apply_measurable p k).comp (hd.div_const h)).mul
            measurable_const)))

-- @node: separableWinsorizedScoreIndex_exists_approximating_sequence
/-- The stated finite approximation exists with the asserted properties. -/
lemma separableWinsorizedScoreIndex_exists_approximating_sequence
    (P : A1A2Law) (p : ℕ) (h : ℝ) (hh : 0 < h)
    (g0 : ℕ → SeparableWinsorizedScoreIndex P p h) (hdense : DenseRange g0)
    (i : SeparableWinsorizedScoreIndex P p h) :
    ∃ kseq : ℕ → ℕ,
      Tendsto (fun m => g0 (kseq m)) atTop (nhds i) ∧
      ∀ m, i.1.1 + dist
          ((g0 (kseq m)).2.2.1.1)
          i.2.2.1.1 <
        (g0 (kseq m)).1.1 := by
  let I := SeparableWinsorizedScoreIndex P p h
  let δ : ℕ → ℝ := fun m => (2 * h - i.1.1) / (16 * (m + 1 : ℕ))
  have hδ (m : ℕ) : 0 < δ m := by
    dsimp [δ]
    apply div_pos
    · exact sub_pos.2 i.1.2.2
    · positivity
  let a : ℕ → I := fun m =>
    ⟨⟨i.1.1 + 4 * δ m, by
        constructor
        · nlinarith [i.1.2.1, hδ m]
        · have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
          have hnum : 0 < 2 * h - i.1.1 := sub_pos.2 i.1.2.2
          dsimp [δ]
          have hden : 0 < (16 : ℝ) * (m + 1 : ℕ) := by positivity
          have hle : (4 : ℝ) * ((2 * h - i.1.1) /
              (16 * (m + 1 : ℕ))) ≤ (2 * h - i.1.1) / 4 := by
            calc
              _ = (2 * h - i.1.1) / (4 * (m + 1 : ℕ)) := by ring
              _ ≤ (2 * h - i.1.1) / 4 := by
                apply (div_le_div_iff_of_pos_left hnum
                  (by positivity) (by norm_num)).2
                nlinarith
          nlinarith⟩,
      ⟨i.2.1, ⟨i.2.2.1, ⟨i.2.2.2.1, i.2.2.2.2⟩⟩⟩⟩
  let U : ℕ → Set I := fun m => {u |
    dist u.2.2.1.1 i.2.2.1.1 < δ m ∧
    |u.1.1 - (i.1.1 + 4 * δ m)| < δ m ∧
    (∀ k, |u.2.2.2.1 k - i.2.2.2.1 k| < δ m) ∧
    u.2.1 = i.2.1 ∧ u.2.2.2.2 = i.2.2.2.2}
  have hUopen (m : ℕ) : IsOpen (U m) := by
    have hxcont : Continuous (fun u : I => (u.2.2.1.1 : Score)) := by
      dsimp [I]
      fun_prop
    have hqcont : Continuous (fun u : I => (u.1.1 : ℝ)) := by
      dsimp [I]
      fun_prop
    have hbcont (k : Fin (p + 1)) : Continuous (fun u : I => u.2.2.2.1 k) := by
      dsimp [I]
      fun_prop
    have htcont : Continuous (fun u : I => u.2.1) := by
      dsimp [I]
      fun_prop
    have hjcont : Continuous (fun u : I => u.2.2.2.2) := by
      dsimp [I]
      fun_prop
    have hcoeff : IsOpen {u : I |
        ∀ k, |u.2.2.2.1 k - i.2.2.2.1 k| < δ m} := by
      rw [show {u : I | ∀ k, |u.2.2.2.1 k - i.2.2.2.1 k| < δ m} =
          ⋂ k : Fin (p + 1), {u : I |
            |u.2.2.2.1 k - i.2.2.2.1 k| < δ m} by ext u; simp]
      exact isOpen_iInter_of_finite fun k =>
        isOpen_lt ((hbcont k).sub continuous_const |>.abs) continuous_const
    dsimp [U]
    refine (isOpen_lt (hxcont.dist continuous_const) continuous_const).and ?_
    refine (isOpen_lt (hqcont.sub continuous_const |>.abs) continuous_const).and ?_
    refine hcoeff.and ?_
    exact (htcont.isOpen_preimage {i.2.1} (isOpen_discrete _)).and
      (hjcont.isOpen_preimage {i.2.2.2.2} (isOpen_discrete _))
  have haU (m : ℕ) : a m ∈ U m := by
    dsimp [U, a]
    simp only [dist_self, sub_self, abs_zero]
    refine ⟨hδ m, hδ m, ?_, trivial, trivial⟩
    intro k
    simpa using hδ m
  have hex (m : ℕ) : ∃ k : ℕ, g0 k ∈ U m := by
    exact hdense.exists_mem_open (hUopen m) ⟨a m, haU m⟩
  choose kseq hkseq using hex
  refine ⟨kseq, ?_, ?_⟩
  · have hδ0 : Tendsto δ atTop (nhds 0) := by
      dsimp [δ]
      have hbase := (tendsto_const_div_atTop_nhds_zero_nat
        ((2 * h - i.1.1) / 16 : ℝ)).comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Nat.add_comm, Nat.cast_add, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using hbase
    have hq : Tendsto (fun m => (g0 (kseq m)).1.1) atTop (nhds i.1.1) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rcases eventually_atTop.1
        (hδ0.eventually (gt_mem_nhds (show 0 < ε / 5 by positivity))) with ⟨N, hN⟩
      refine ⟨N, fun m hmN => ?_⟩
      have hm := hN m hmN
      have hu := (hkseq m).2.1
      rw [abs_lt] at hu
      rw [Real.dist_eq, abs_lt]
      constructor <;> nlinarith [hδ m]
    have hx : Tendsto (fun m => (g0 (kseq m)).2.2.1.1) atTop
        (nhds i.2.2.1.1) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rcases eventually_atTop.1 (hδ0.eventually (gt_mem_nhds hε)) with ⟨N, hN⟩
      refine ⟨N, fun m hmN => ?_⟩
      have hm := hN m hmN
      exact (hkseq m).1.trans hm
    have hb : Tendsto (fun m => (g0 (kseq m)).2.2.2.1) atTop
        (nhds i.2.2.2.1) := by
      rw [tendsto_pi_nhds]
      intro k
      rw [Metric.tendsto_atTop]
      intro ε hε
      rcases eventually_atTop.1 (hδ0.eventually (gt_mem_nhds hε)) with ⟨N, hN⟩
      refine ⟨N, fun m hmN => ?_⟩
      have hm := hN m hmN
      simpa [Real.dist_eq] using ((hkseq m).2.2.1 k).trans hm
    have ht : Tendsto (fun m => (g0 (kseq m)).2.1) atTop (nhds i.2.1) := by
      apply tendsto_atTop_of_eventually_const (i₀ := 0)
      intro m _
      exact (hkseq m).2.2.2.1
    have hj : Tendsto (fun m => (g0 (kseq m)).2.2.2.2) atTop
        (nhds i.2.2.2.2) := by
      apply tendsto_atTop_of_eventually_const (i₀ := 0)
      intro m _
      exact (hkseq m).2.2.2.2
    have hcenter := tendsto_subtype_rng.2 hx
    rw [nhds_prod_eq, Filter.tendsto_prod_iff']
    refine ⟨tendsto_subtype_rng.2 hq, ?_⟩
    rw [nhds_prod_eq, Filter.tendsto_prod_iff']
    refine ⟨ht, ?_⟩
    rw [nhds_prod_eq, Filter.tendsto_prod_iff']
    refine ⟨hcenter, ?_⟩
    rw [nhds_prod_eq, Filter.tendsto_prod_iff']
    exact ⟨hb, hj⟩
  · intro m
    have hx := (hkseq m).1
    have hq := (hkseq m).2.1
    rw [abs_lt] at hq
    nlinarith [hδ m]

-- @node: separableWinsorizedScoreFunction_tendsto
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma separableWinsorizedScoreFunction_tendsto
    (P : A1A2Law) (p : ℕ) (h B C : ℝ) (hh : 0 < h)
    (i : SeparableWinsorizedScoreIndex P p h)
    (u : ℕ → SeparableWinsorizedScoreIndex P p h)
    (hu : Tendsto u atTop (nhds i))
    (habove : ∀ m, i.1.1 + dist (u m).2.2.1.1 i.2.2.1.1 < (u m).1.1)
    (z : CausalObservation) (hzsup : causalScore z ∈ P.support)
    (hznb : causalScore z ∉ P.boundary) :
    Tendsto (fun m => separableWinsorizedScoreFunction P p h B C (u m) z)
      atTop (nhds (separableWinsorizedScoreFunction P p h B C i z)) := by
  classical
  let dseq : ℕ → ℝ := fun m =>
    signedDistance (knownGeometry P) (u m).2.2.1.1 (causalScore z)
  let d := signedDistance (knownGeometry P) i.2.2.1.1 (causalScore z)
  have hq : Tendsto (fun m => (u m).1.1) atTop (nhds i.1.1) :=
    ((by fun_prop : Continuous (fun a : SeparableWinsorizedScoreIndex P p h =>
      (a.1.1 : ℝ))).continuousAt.tendsto).comp hu
  have hx : Tendsto (fun m => (u m).2.2.1.1) atTop (nhds i.2.2.1.1) :=
    ((by fun_prop : Continuous (fun a : SeparableWinsorizedScoreIndex P p h =>
      (a.2.2.1.1 : Score))).continuousAt.tendsto).comp hu
  have hb (k : Fin (p + 1)) : Tendsto (fun m => (u m).2.2.2.1 k)
      atTop (nhds (i.2.2.2.1 k)) :=
    ((by fun_prop : Continuous (fun a : SeparableWinsorizedScoreIndex P p h =>
      a.2.2.2.1 k)).continuousAt.tendsto).comp hu
  have htlim : Tendsto (fun m => (u m).2.1) atTop (nhds i.2.1) :=
    ((by fun_prop : Continuous (fun a : SeparableWinsorizedScoreIndex P p h =>
      a.2.1)).continuousAt.tendsto).comp hu
  have hjlim : Tendsto (fun m => (u m).2.2.2.2) atTop (nhds i.2.2.2.2) :=
    ((by fun_prop : Continuous (fun a : SeparableWinsorizedScoreIndex P p h =>
      a.2.2.2.2)).continuousAt.tendsto).comp hu
  have ht : ∀ᶠ m in atTop, (u m).2.1 = i.2.1 := by
    simpa [nhds_discrete] using htlim
  have hj : ∀ᶠ m in atTop, (u m).2.2.2.2 = i.2.2.2.2 := by
    simpa [nhds_discrete] using hjlim
  have hdist : Tendsto (fun m => dist (causalScore z) (u m).2.2.1.1)
      atTop (nhds (dist (causalScore z) i.2.2.1.1)) :=
    tendsto_const_nhds.dist hx
  have hd : Tendsto dseq atTop (nhds d) := by
    dsimp [dseq, d, signedDistance, knownGeometry]
    exact tendsto_const_nhds.mul hdist
  have hkernel : ∀ᶠ m in atTop,
      uniformKernel (dseq m / (u m).1.1) = uniformKernel (d / i.1.1) := by
    have hqm (m : ℕ) : 0 < (u m).1.1 := lt_of_lt_of_le hh (u m).1.2.1
    have hqi : 0 < i.1.1 := lt_of_lt_of_le hh i.1.2.1
    rw [uniformKernel_div_eq_if_abs_le d i.1.1 hqi]
    simp_rw [uniformKernel_div_eq_if_abs_le (dseq _) _ (hqm _)]
    by_cases hinside : |d| ≤ i.1.1
    · have hall : ∀ m, |dseq m| ≤ (u m).1.1 := by
        intro m
        have htri := dist_triangle (causalScore z) i.2.2.1.1 (u m).2.2.1.1
        have hab := habove m
        have habs : |dseq m| = dist (causalScore z) (u m).2.2.1.1 := by
          dsimp [dseq, signedDistance, knownGeometry]
          rcases (show causalScore z ∈ P.A0 ∪ P.A1 by simpa [P.assignment_partition.1]
            using hzsup) with hz0 | hz1
          · have hz1n : causalScore z ∉ P.A1 := fun hz1 =>
              P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
            simp [indicator_of_mem hz0, indicator_of_notMem hz1n]
          · have hz0n : causalScore z ∉ P.A0 := fun hz0 =>
              P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
            simp [indicator_of_mem hz1, indicator_of_notMem hz0n]
        have habsi : |d| = dist (causalScore z) i.2.2.1.1 := by
          dsimp [d, signedDistance, knownGeometry]
          rcases (show causalScore z ∈ P.A0 ∪ P.A1 by simpa [P.assignment_partition.1]
            using hzsup) with hz0 | hz1
          · have hz1n : causalScore z ∉ P.A1 := fun hz1 =>
              P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
            simp [indicator_of_mem hz0, indicator_of_notMem hz1n]
          · have hz0n : causalScore z ∉ P.A0 := fun hz0 =>
              P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
            simp [indicator_of_mem hz1, indicator_of_notMem hz0n]
        rw [habsi] at hinside
        rw [habs]
        have hab' : i.1.1 + dist i.2.2.1.1 (u m).2.2.1.1 < (u m).1.1 := by
          simpa [dist_comm] using hab
        nlinarith
      exact Eventually.of_forall fun m => by simp [hinside, hall m]
    · have hout : i.1.1 < |d| := lt_of_not_ge hinside
      have hev : ∀ᶠ m in atTop, (u m).1.1 < |dseq m| :=
        Filter.Tendsto.eventually_lt hq hd.abs hout
      exact hev.mono fun m hm => by simp [hinside, not_le_of_gt hm]
  have hpoly (k : Fin (p + 1)) : Tendsto (fun m => polyBasis p (dseq m / h) k)
      atTop (nhds (polyBasis p (d / h) k)) := by
    unfold polyBasis
    exact (hd.div_const h).pow _
  have hclip (k : Fin (p + 1)) : Tendsto (fun m => clip C ((u m).2.2.2.1 k))
      atTop (nhds (clip C (i.2.2.2.1 k))) := by
    exact ((by unfold clip; fun_prop : Continuous (clip C))).continuousAt.tendsto.comp (hb k)
  have hsum : Tendsto (fun m => ∑ k,
      polyBasis p (dseq m / h) k * clip C ((u m).2.2.2.1 k)) atTop
      (nhds (∑ k, polyBasis p (d / h) k * clip C (i.2.2.2.1 k))) := by
    apply tendsto_finset_sum
    intro k _
    exact (hpoly k).mul (hclip k)
  have hcore : Tendsto (fun m => polyBasis p (dseq m / h) (u m).2.2.2.2 *
      (winsorize B (observedOutcome P z) - ∑ k,
        polyBasis p (dseq m / h) k * clip C ((u m).2.2.2.1 k))) atTop
      (nhds (polyBasis p (d / h) i.2.2.2.2 *
        (winsorize B (observedOutcome P z) - ∑ k,
          polyBasis p (d / h) k * clip C (i.2.2.2.1 k)))) := by
    have heq : ∀ᶠ m in atTop,
        polyBasis p (dseq m / h) (u m).2.2.2.2 *
            (winsorize B (observedOutcome P z) - ∑ k,
              polyBasis p (dseq m / h) k * clip C ((u m).2.2.2.1 k)) =
          polyBasis p (dseq m / h) i.2.2.2.2 *
            (winsorize B (observedOutcome P z) - ∑ k,
              polyBasis p (dseq m / h) k * clip C ((u m).2.2.2.1 k)) :=
      hj.mono fun m hm => by rw [hm]
    have heqsym := heq.mono fun m hm => hm.symm
    exact Tendsto.congr' heqsym
      ((hpoly i.2.2.2.2).mul (tendsto_const_nhds.sub hsum))
  have harm : ∀ᶠ m in atTop,
      (if signedArm (u m).2.1 (dseq m) then (1 : ℝ) else 0) =
        (if signedArm i.2.1 d then 1 else 0) := by
    filter_upwards [ht] with m htm
    rw [htm]
    have hxmn : causalScore z ≠ (u m).2.2.1.1 := fun heq =>
      hznb (heq ▸ (u m).2.2.1.2)
    have hxin : causalScore z ≠ i.2.2.1.1 := fun heq => hznb (heq ▸ i.2.2.1.2)
    rcases (show causalScore z ∈ P.A0 ∪ P.A1 by simpa [P.assignment_partition.1]
      using hzsup) with hz0 | hz1
    · have hz1n : causalScore z ∉ P.A1 := fun hz1 =>
          P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
      cases hit : i.2.1 <;>
        simp [dseq, d, signedDistance, knownGeometry, indicator_of_mem hz0,
          indicator_of_notMem hz1n, signedArm, hit, hxmn, hxin, dist_nonneg]
    · have hz0n : causalScore z ∉ P.A0 := fun hz0 =>
          P.assignment_partition.2.le_bot ⟨hz0, hz1⟩
      cases hit : i.2.1 <;>
        simp [dseq, d, signedDistance, knownGeometry, indicator_of_mem hz1,
          indicator_of_notMem hz0n, signedArm, hit, hxmn, hxin] <;>
        split_ifs <;> linarith [
          (dist_nonneg : 0 ≤ dist (causalScore z) (u m).2.2.1.1),
          (dist_nonneg : 0 ≤ dist (causalScore z) i.2.2.1.1)]
  have hfull : ∀ᶠ m in atTop,
      separableWinsorizedScoreFunction P p h B C (u m) z =
        (if signedArm i.2.1 d then (1 : ℝ) else 0) *
          uniformKernel (d / i.1.1) *
            (polyBasis p (dseq m / h) (u m).2.2.2.2 *
              (winsorize B (observedOutcome P z) - ∑ k,
                polyBasis p (dseq m / h) k * clip C ((u m).2.2.2.1 k))) := by
    filter_upwards [harm, hkernel] with m hm hkm
    dsimp [separableWinsorizedScoreFunction, dseq]
    rw [hm, hkm]
    ring
  have hbase : Tendsto (fun m =>
      (if signedArm i.2.1 d then (1 : ℝ) else 0) *
        uniformKernel (d / i.1.1) *
          (polyBasis p (dseq m / h) (u m).2.2.2.2 *
            (winsorize B (observedOutcome P z) - ∑ k,
              polyBasis p (dseq m / h) k * clip C ((u m).2.2.2.1 k)))) atTop
      (nhds ((if signedArm i.2.1 d then (1 : ℝ) else 0) *
        uniformKernel (d / i.1.1) *
          (polyBasis p (d / h) i.2.2.2.2 *
            (winsorize B (observedOutcome P z) - ∑ k,
              polyBasis p (d / h) k * clip C (i.2.2.2.1 k))))) :=
    (tendsto_const_nhds.mul tendsto_const_nhds).mul hcore
  have hfullsym := hfull.mono fun m hm => hm.symm
  apply Tendsto.congr' hfullsym
  convert hbase using 1 <;>
    simp only [separableWinsorizedScoreFunction, d] <;> ring_nf

/-- The rational-center/rational-bandwidth enlargement of the bounded
winsorized signed-distance score class has an almost-sure countable supremum
reduction.  A single conull set excludes observations whose score lies on the
treatment boundary; closed kernel endpoints are approached from bandwidths
in `[h,2h)`. -/
-- @node: winsorizedScore_hasCountableEmpiricalSupReduction_at
lemma winsorizedScore_hasCountableEmpiricalSupReduction_at
    (p : ℕ) (ν L C : ℝ) (hC : 0 < C) :
    ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → 1 ≤ B →
        HasCountableEmpiricalSupReduction P.law
          (separableWinsorizedScoreFunction P p h B C) := by
  intro P hP h B hh hB
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hbne := winsorizedScore_boundary_nonempty p ν L P hP
  letI : Nonempty {x : Score // x ∈ P.boundary} := hbne.to_subtype
  let I := SeparableWinsorizedScoreIndex P p h
  have hI : Nonempty I := by
    exact ⟨⟨⟨h, ⟨le_rfl, by linarith⟩⟩,
      ⟨false, ⟨Classical.arbitrary _, ⟨0, Classical.arbitrary _⟩⟩⟩⟩⟩
  letI : Nonempty I := hI
  let g0 : ℕ → I := TopologicalSpace.denseSeq I
  have hdense : DenseRange g0 := TopologicalSpace.denseRange_denseSeq I
  let S : Set CausalObservation :=
    {z | causalScore z ∈ P.support ∧ causalScore z ∉ P.boundary}
  have hscore : Measurable causalScore := by unfold causalScore; fun_prop
  have hsuppMap : ∀ᵐ x ∂Measure.map causalScore P.law, x ∈ P.support := by
    rw [P.support_eq_marginal_support]
    exact Measure.support_mem_ae
  have hsupp : ∀ᵐ z ∂P.law, causalScore z ∈ P.support :=
    MeasureTheory.ae_of_ae_map hscore.aemeasurable hsuppMap
  have hbvol : volume P.boundary = 0 := by
    exact winsorizedScore_boundary_volume_zero p ν L P hP
  have hbmeas : MeasurableSet P.boundary :=
    winsorizedScore_boundary_measurable p ν L P hP
  have hbmap : (Measure.map causalScore P.law) P.boundary = 0 := by
    rw [P.marginal_eq, withDensity_apply _ hbmeas]
    exact setLIntegral_measure_zero P.boundary _ hbvol
  have hnbMap : ∀ᵐ x ∂Measure.map causalScore P.law, x ∉ P.boundary :=
    measure_eq_zero_iff_ae_notMem.mp hbmap
  have hnb : ∀ᵐ z ∂P.law, causalScore z ∉ P.boundary :=
    MeasureTheory.ae_of_ae_map hscore.aemeasurable hnbMap
  have hS : ∀ᵐ z ∂P.law, z ∈ S := hsupp.and hnb
  have hmeas : ∀ i : I, Measurable
      (separableWinsorizedScoreFunction P p h B C i) :=
    fun i => separableWinsorizedScoreFunction_measurable P p h B C i
  let G : CausalObservation → ℝ := fun z =>
    (2 : ℝ) ^ p * (|armCoord false z| + |armCoord true z| +
      (p + 1 : ℝ) * (2 : ℝ) ^ p * C)
  have hexp : 1 ≤ ENNReal.ofReal (2 + ν) := by
    rw [ENNReal.one_le_ofReal]
    linarith [hP.1]
  have hi0 : Integrable (armCoord false) P.law :=
    (P.memLp_armCoord_of_condAbsMoment_le p ν L hP false).integrable hexp
  have hi1 : Integrable (armCoord true) P.law :=
    (P.memLp_armCoord_of_condAbsMoment_le p ν L hP true).integrable hexp
  have hG : Integrable G P.law := by
    exact ((hi0.abs.add hi1.abs).add (integrable_const
      ((p + 1 : ℝ) * (2 : ℝ) ^ p * C))).const_mul ((2 : ℝ) ^ p)
  apply hasCountableEmpiricalSupReduction_of_pointwise_dense P.law
    (separableWinsorizedScoreFunction P p h B C) g0 S hS
  · intro i
    obtain ⟨kseq, hlim, habove⟩ :=
      separableWinsorizedScoreIndex_exists_approximating_sequence
        P p h hh g0 hdense i
    refine ⟨kseq, fun z hz => ?_⟩
    exact separableWinsorizedScoreFunction_tendsto P p h B C hh i
      (fun m => g0 (kseq m)) hlim
      habove z hz.1 hz.2
  · exact hmeas
  · refine ⟨G, hG, ?_⟩
    intro i z
    exact separableWinsorizedScoreFunction_bound P p h B C hh (by linarith) hC.le i z

/-- The countable reduction at the canonical unit coefficient radius. -/
-- @node: winsorizedScore_hasCountableEmpiricalSupReduction
lemma winsorizedScore_hasCountableEmpiricalSupReduction
    (p : ℕ) (ν L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → 1 ≤ B →
        HasCountableEmpiricalSupReduction P.law
          (separableWinsorizedScoreFunction P p h B C) := by
  exact ⟨1, by norm_num, winsorizedScore_hasCountableEmpiricalSupReduction_at
    p ν L 1 (by norm_num)⟩


end CausalSmith.Stat.BddUniformLogPenalty
