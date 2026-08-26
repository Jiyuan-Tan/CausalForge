import CausalSmith.Mathlib.Probability.PoissonUsableOccupancy
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.OccupancyTransport

/-!
# Discharge of the usable-occupancy citation

This file combines independent-Poisson usable-occupancy bounds with monotone
half-intensity de-Poissonization and transports the result back to the original
fixed-size real-outcome sample.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open CausalSmith.Mathlib.Probability

/-- The zero indicator is bounded by the Laplace transform of a natural count. -/
private lemma zeroIndicator_le_exp_neg (r : ℕ) :
    (if r = 0 then (1 : ℝ) else 0) ≤ Real.exp (-(r : ℝ)) := by
  by_cases hr : r = 0
  · simp [hr]
  · simp only [hr, if_false]
    exact (Real.exp_pos _).le

/-- A reciprocal count is controlled by a deterministic cutoff and its
Laplace transform. -/
private lemma reciprocalIndicator_le_cutoff (A : ℝ) (hA : 0 < A) (r : ℕ) :
    (if r = 0 then (1 : ℝ) else (1 : ℝ) / r) ≤
      2 / A + Real.exp (A / 2) * Real.exp (-(r : ℝ)) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [lt_self_iff_false, ↓reduceIte, Nat.cast_zero, neg_zero,
      Real.exp_zero, mul_one]
    have hdiv : 0 ≤ 2 / A := by positivity
    have hexp : 1 ≤ Real.exp (A / 2) := Real.one_le_exp (by positivity)
    linarith
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  rw [if_neg hr0]
  by_cases hlarge : A / 2 ≤ (r : ℝ)
  · have hrreal : (0 : ℝ) < r := by exact_mod_cast hrpos
    have hrecip : (1 : ℝ) / r ≤ 2 / A := by
      rw [div_le_div_iff₀ hrreal hA]
      nlinarith
    exact hrecip.trans (le_add_of_nonneg_right (mul_nonneg
      (Real.exp_pos _).le (Real.exp_pos _).le))
  · have hexp : 1 ≤ Real.exp (A / 2) * Real.exp (-(r : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      linarith
    have hrone : (1 : ℝ) / r ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hrpos)]
      exact_mod_cast hrpos
    exact hrone.trans (hexp.trans (le_add_of_nonneg_left (by positivity)))

/-- The fixed-size usable total agrees with the usable total after outcomes are
forgotten. -/
private lemma usableTotal_eq_finiteMarkUsableTotal {n d : ℕ}
    (s : Fin n → Obs d) :
    usableTotal s = finiteMarkUsableTotal (fun i ↦ observedMark (s i)) := by
  unfold usableTotal usableCell cellCount finiteMarkUsableTotal armCount observedMark
  simp

/-- Usable occupancy is measurable on the original fixed-size sample space. -/
private lemma measurable_usableTotal {n d : ℕ} :
    Measurable (usableTotal : (Fin n → Obs d) → ℕ) := by
  rw [show (usableTotal : (Fin n → Obs d) → ℕ) =
      finiteMarkUsableTotal ∘ (fun s ↦ fun i ↦ observedMark (s i)) by
    funext s
    exact usableTotal_eq_finiteMarkUsableTotal s]
  exact (measurable_of_countable finiteMarkUsableTotal).comp
    (measurable_pi_lambda _ fun i ↦ measurable_observedMark.comp (measurable_pi_apply i))

/-- Forgetting outcomes identifies the fixed-sample zero-occupancy integral
with the corresponding finite-mark stream-prefix integral. -/
private lemma lintegral_usableZero_productLaw_eq_stream {n d : ℕ}
    (P : RealLaw d) :
    (∫⁻ s, (if usableTotal s = 0 then (1 : ℝ≥0∞) else 0) ∂productLaw n P) =
      ∫⁻ z, streamUsableZero n z ∂iidStreamLaw (observedMarkLaw P) := by
  let pre : (ℕ → Fin d × Bool) → (Fin n → Fin d × Bool) :=
    fun z ↦ fun i ↦ z i
  let marks : (Fin n → Obs d) → (Fin n → Fin d × Bool) :=
    fun s ↦ fun i ↦ observedMark (s i)
  let f : (Fin n → Fin d × Bool) → ℝ≥0∞ :=
    fun x ↦ if finiteMarkUsableTotal x = 0 then 1 else 0
  have hpre : Measurable pre :=
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)
  have hmarks : Measurable marks :=
    measurable_pi_lambda _ fun i ↦ measurable_observedMark.comp (measurable_pi_apply i)
  have hf : Measurable f := measurable_of_countable f
  calc
    (∫⁻ s, (if usableTotal s = 0 then (1 : ℝ≥0∞) else 0) ∂productLaw n P) =
        ∫⁻ s, f (marks s) ∂productLaw n P := by
          congr with s
          rw [usableTotal_eq_finiteMarkUsableTotal]
    _ = ∫⁻ x, f x ∂Measure.map marks (productLaw n P) := by
      rw [lintegral_map hf hmarks]
    _ = ∫⁻ x, f x ∂Measure.pi (fun _ : Fin n ↦ observedMarkLaw P) := by
      rw [show Measure.map marks (productLaw n P) =
          Measure.pi (fun _ : Fin n ↦ observedMarkLaw P) from
        productLaw_map_observedMarks P]
    _ = ∫⁻ z, f (pre z) ∂iidStreamLaw (observedMarkLaw P) := by
      rw [← lintegral_map hf hpre,
        iidStreamLaw_map_finPrefix]
    _ = ∫⁻ z, streamUsableZero n z ∂iidStreamLaw (observedMarkLaw P) := by
      congr with z
      unfold f pre streamUsableZero
      rw [streamUsableTotal_eq_finiteMarkUsableTotal]

/-- The same transport identity for the monotone zero/reciprocal penalty. -/
private lemma lintegral_usablePenalty_productLaw_eq_stream {n d : ℕ}
    (P : RealLaw d) :
    (∫⁻ s, (if usableTotal s = 0 then (1 : ℝ≥0∞)
        else ((usableTotal s : ℕ) : ℝ≥0∞)⁻¹) ∂productLaw n P) =
      ∫⁻ z, streamUsablePenalty n z ∂iidStreamLaw (observedMarkLaw P) := by
  let pre : (ℕ → Fin d × Bool) → (Fin n → Fin d × Bool) :=
    fun z ↦ fun i ↦ z i
  let marks : (Fin n → Obs d) → (Fin n → Fin d × Bool) :=
    fun s ↦ fun i ↦ observedMark (s i)
  let f : (Fin n → Fin d × Bool) → ℝ≥0∞ := fun x ↦
    if finiteMarkUsableTotal x = 0 then 1
    else ((finiteMarkUsableTotal x : ℕ) : ℝ≥0∞)⁻¹
  have hpre : Measurable pre :=
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)
  have hmarks : Measurable marks :=
    measurable_pi_lambda _ fun i ↦ measurable_observedMark.comp (measurable_pi_apply i)
  have hf : Measurable f := measurable_of_countable f
  calc
    (∫⁻ s, (if usableTotal s = 0 then (1 : ℝ≥0∞)
        else ((usableTotal s : ℕ) : ℝ≥0∞)⁻¹) ∂productLaw n P) =
        ∫⁻ s, f (marks s) ∂productLaw n P := by
          congr with s
          rw [usableTotal_eq_finiteMarkUsableTotal]
    _ = ∫⁻ x, f x ∂Measure.map marks (productLaw n P) := by
      rw [lintegral_map hf hmarks]
    _ = ∫⁻ x, f x ∂Measure.pi (fun _ : Fin n ↦ observedMarkLaw P) := by
      rw [show Measure.map marks (productLaw n P) =
          Measure.pi (fun _ : Fin n ↦ observedMarkLaw P) from
        productLaw_map_observedMarks P]
    _ = ∫⁻ z, f (pre z) ∂iidStreamLaw (observedMarkLaw P) := by
      rw [← lintegral_map hf hpre,
        iidStreamLaw_map_finPrefix]
    _ = ∫⁻ z, streamUsablePenalty n z ∂iidStreamLaw (observedMarkLaw P) := by
      congr with z
      unfold f pre streamUsablePenalty
      rw [streamUsableTotal_eq_finiteMarkUsableTotal]

/-- Regrouping a product of independent arm-cell Poisson laws produces the
product of the corresponding two-arm laws. -/
private lemma map_regroupArmCellCounts_poissonPi {d : ℕ}
    (mu0 mu1 : Fin d → ℝ≥0) :
    Measure.map regroupArmCellCounts
        (Measure.pi (fun j : Fin d × Bool ↦
          poissonMeasure (if j.2 then mu1 j.1 else mu0 j.1))) =
      Measure.pi (fun k : Fin d ↦
        (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k))) := by
  classical
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_countable regroupArmCellCounts)
    (measurableSet_singleton z)]
  have hpre : regroupArmCellCounts ⁻¹' {z} =
      {c : Fin d × Bool → ℕ | ∀ k, c (k, false) = (z k).1 ∧
        c (k, true) = (z k).2} := by
    ext c
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
    constructor
    · intro hc k
      have hk := congrFun hc k
      exact ⟨congrArg Prod.fst hk, congrArg Prod.snd hk⟩
    · intro hc
      funext k
      exact Prod.ext (hc k).1 (hc k).2
  rw [hpre]
  have hset : {c : Fin d × Bool → ℕ | ∀ k, c (k, false) = (z k).1 ∧
        c (k, true) = (z k).2} =
      {fun j : Fin d × Bool ↦ if j.2 then (z j.1).2 else (z j.1).1} := by
    ext c
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hc
      funext j
      rcases j with ⟨k, a⟩
      cases a <;> simp [hc k]
    · intro hc k
      rw [hc]
      simp
  rw [hset, Measure.pi_singleton, Measure.pi_singleton]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fintype.prod_bool]
  rw [show {z k} = ({(z k).1} ×ˢ {(z k).2} : Set (ℕ × ℕ)) by
    exact singleton_prod_singleton.symm]
  rw [Measure.prod_prod]
  simp [mul_comm]

/-- The usable-total law of the marked Poisson sample is the pushforward of
the independent two-arm Poisson product law. -/
private lemma map_markedUsableTotal_finiteMarkedPoissonSampleLaw
    {d : ℕ} (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P]
    (lam : ℝ≥0) :
    Measure.map markedUsableTotal
        (finiteMarkedPoissonSampleLaw P (Measure.dirac (0 : ℝ)) lam) =
      Measure.map usableTotalOfRegroupedCounts
        (Measure.pi (fun k : Fin d ↦
          (poissonMeasure (lam * (P {(k, false)}).toNNReal)).prod
            (poissonMeasure (lam * (P {(k, true)}).toNNReal)))) := by
  let mu0 : Fin d → ℝ≥0 := fun k ↦ lam * (P {(k, false)}).toNNReal
  let mu1 : Fin d → ℝ≥0 := fun k ↦ lam * (P {(k, true)}).toNNReal
  have hreg : Measurable
      (regroupArmCellCounts (d := d) ∘ markedArmCellCounts (d := d)) :=
    (measurable_of_countable (regroupArmCellCounts (d := d))).comp
      (measurable_markedArmCellCounts (d := d))
  calc
    Measure.map markedUsableTotal
        (finiteMarkedPoissonSampleLaw P (Measure.dirac 0) lam) =
        Measure.map usableTotalOfRegroupedCounts
          (Measure.map (regroupArmCellCounts (d := d) ∘ markedArmCellCounts (d := d))
            (finiteMarkedPoissonSampleLaw P (Measure.dirac (0 : ℝ)) lam)) := by
      rw [Measure.map_map (measurable_of_countable usableTotalOfRegroupedCounts)
        hreg]
      rfl
    _ = Measure.map usableTotalOfRegroupedCounts
        (Measure.map regroupArmCellCounts
          (Measure.pi (fun j : Fin d × Bool ↦
            poissonMeasure (lam * (P {j}).toNNReal)))) := by
      rw [map_regroupedArmCellCounts_finiteMarkedPoissonSampleLaw]
    _ = Measure.map usableTotalOfRegroupedCounts
        (Measure.pi (fun k : Fin d ↦
          (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k)))) := by
      congr 1
      rw [show (fun j : Fin d × Bool ↦ poissonMeasure (lam * (P {j}).toNNReal)) =
          (fun j : Fin d × Bool ↦
            poissonMeasure (if j.2 then mu1 j.1 else mu0 j.1)) by
        funext j
        rcases j with ⟨k, a⟩
        cases a <;> rfl]
      exact map_regroupArmCellCounts_poissonPi mu0 mu1
    _ = _ := by rfl

/-- Adding a deterministic auxiliary mark does not change any fixed-prefix
statistic of the observation coordinate. -/
private lemma map_iidStream_fstPrefix_prod_dirac
    {d n : ℕ} (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P] :
    Measure.map (fun z : ℕ → (Fin d × Bool) × ℝ ↦
        fun i : Fin n ↦ (z i).1) (iidStreamLaw (P.prod (Measure.dirac (0 : ℝ)))) =
      Measure.pi (fun _ : Fin n ↦ P) := by
  let pre : (ℕ → (Fin d × Bool) × ℝ) → (Fin n → (Fin d × Bool) × ℝ) :=
    fun z ↦ fun i ↦ z i
  let fstAll : (Fin n → (Fin d × Bool) × ℝ) → (Fin n → Fin d × Bool) :=
    fun z ↦ fun i ↦ (z i).1
  have hpre : Measurable pre := measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)
  have hfst : Measurable fstAll :=
    measurable_pi_lambda _ fun i ↦ measurable_fst.comp (measurable_pi_apply i)
  calc
    Measure.map (fun z : ℕ → (Fin d × Bool) × ℝ ↦ fun i : Fin n ↦ (z i).1)
        (iidStreamLaw (P.prod (Measure.dirac (0 : ℝ)))) =
        Measure.map fstAll (Measure.map pre (iidStreamLaw (P.prod (Measure.dirac (0 : ℝ))))) := by
      rw [Measure.map_map hfst hpre]
      rfl
    _ = Measure.map fstAll (Measure.pi (fun _ : Fin n ↦ P.prod (Measure.dirac (0 : ℝ)))) := by
      rw [iidStreamLaw_map_finPrefix]
    _ = Measure.pi (fun _ : Fin n ↦ Measure.map Prod.fst (P.prod (Measure.dirac (0 : ℝ)))) := by
      simpa only [fstAll] using Measure.pi_map_pi
        (μ := fun _ : Fin n ↦ P.prod (Measure.dirac (0 : ℝ)))
        (f := fun _ : Fin n ↦ Prod.fst)
        (fun _ ↦ measurable_fst.aemeasurable)
    _ = Measure.pi (fun _ : Fin n ↦ P) := by
      congr 2
      rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Fixed-prefix integrals are unchanged by a deterministic auxiliary mark. -/
private lemma lintegral_augmentedPrefix_eq {d n : ℕ}
    (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P]
    (h : ℕ → ℝ≥0∞) :
    (∫⁻ z, h (streamUsableTotal (fun i ↦ (z i).1) n)
        ∂iidStreamLaw (P.prod (Measure.dirac (0 : ℝ)))) =
      ∫⁻ z, h (streamUsableTotal z n) ∂iidStreamLaw P := by
  let f : (Fin n → Fin d × Bool) → ℝ≥0∞ :=
    fun z ↦ h (finiteMarkUsableTotal z)
  have hf : Measurable f := measurable_of_countable f
  have hleft := map_iidStream_fstPrefix_prod_dirac (n := n) P
  have hright := iidStreamLaw_map_finPrefix P n
  calc
    _ = ∫⁻ z : ℕ → (Fin d × Bool) × ℝ, f (fun i : Fin n ↦ (z i).1)
        ∂iidStreamLaw (P.prod (Measure.dirac (0 : ℝ))) := by
      congr with z
      unfold f
      rw [streamUsableTotal_eq_finiteMarkUsableTotal]
    _ = ∫⁻ x, f x ∂Measure.pi (fun _ : Fin n ↦ P) := by
      rw [← hleft, lintegral_map hf (by fun_prop)]
    _ = ∫⁻ z, f (fun i : Fin n ↦ z i) ∂iidStreamLaw P := by
      rw [← hright, lintegral_map hf (by fun_prop)]
    _ = _ := by
      congr with z
      unfold f
      rw [streamUsableTotal_eq_finiteMarkUsableTotal]

/-- Random-prefix occupancy under the augmented stream is the marked-sample
usable total. -/
private lemma lintegral_poissonStream_eq_markedUsable {d : ℕ}
    (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P] (lam : ℝ≥0)
    (h : ℕ → ℝ≥0∞) :
    (∫⁻ q : ℕ × (ℕ → (Fin d × Bool) × ℝ),
        h (streamUsableTotal (fun i ↦ (q.2 i).1) q.1)
        ∂poissonIIDStreamLaw (P.prod (Measure.dirac (0 : ℝ))) lam) =
      ∫⁻ s, h (markedUsableTotal s)
        ∂finiteMarkedPoissonSampleLaw P (Measure.dirac (0 : ℝ)) lam := by
  have hh : Measurable (fun s : FiniteSample ((Fin d × Bool) × ℝ) ↦
      h (markedUsableTotal s)) :=
    (measurable_of_countable h).comp
      ((measurable_of_countable usableTotalOfRegroupedCounts).comp
        ((measurable_of_countable (regroupArmCellCounts (d := d))).comp
          measurable_markedArmCellCounts))
  rw [finiteMarkedPoissonSampleLaw_eq_randomPrefixLaw]
  rw [lintegral_map hh measurable_streamToFiniteSample]
  apply lintegral_congr
  intro q
  rw [markedUsableTotal_streamToFiniteSample]

/-- The primitive cell masses exhaust a nonempty finite mark space. -/
private lemma occupancy_sum_cellMass_eq_one {d : ℕ} (P : RealLaw d) :
    ∑ k : Fin d, P.cellMass k = 1 := by
  let Q := observedMarkLaw P
  have hsumQ : ∑ j : Fin d × Bool, Q {j} = 1 := by
    rw [← measure_biUnion_finset
      (s := (Finset.univ : Finset (Fin d × Bool)))
      (f := fun j ↦ ({j} : Set (Fin d × Bool)))]
    · rw [show (⋃ j ∈ (Finset.univ : Finset (Fin d × Bool)),
          ({j} : Set (Fin d × Bool))) = Set.univ by
          ext x
          simp,
        measure_univ]
    · intro i _ j _ hij
      exact Set.disjoint_singleton.mpr hij
    · intro j _
      exact measurableSet_singleton j
  have hfinite : ∀ j ∈ (Finset.univ : Finset (Fin d × Bool)), Q {j} ≠ ∞ := by
    intro j _
    exact measure_ne_top Q {j}
  have hsumReal : ∑ j : Fin d × Bool, realMass Q {j} = 1 := by
    unfold realMass
    rw [← ENNReal.toReal_sum hfinite, hsumQ]
    simp
  calc
    ∑ k : Fin d, P.cellMass k =
        ∑ k : Fin d, (realMass Q {(k, false)} + realMass Q {(k, true)}) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [realMass_observedMarkLaw_singleton,
        realMass_observedMarkLaw_singleton]
      simp
      ring
    _ = ∑ j : Fin d × Bool, realMass Q {j} := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_bool]
      ring
    _ = 1 := hsumReal

/-- The marked Poisson usable total inherits the independent-cell Laplace
bound. -/
private lemma integral_exp_neg_markedUsable_le
    {d : ℕ} (hd : 0 < d) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2)
    (P : RealLaw d) (hoverlap : Overlap epsilon P) (lam : ℝ≥0) :
    (∫ s, Real.exp (-(markedUsableTotal s : ℝ))
        ∂finiteMarkedPoissonSampleLaw (observedMarkLaw P)
          (Measure.dirac (0 : ℝ)) lam) ≤
      Real.exp (-poissonUsableLaplaceConstant epsilon * (lam : ℝ) ^ 2 /
        max (lam : ℝ) (d : ℝ)) := by
  let Q := observedMarkLaw P
  let mu0 : Fin d → ℝ≥0 := fun k ↦ lam * (Q {(k, false)}).toNNReal
  let mu1 : Fin d → ℝ≥0 := fun k ↦ lam * (Q {(k, true)}).toNNReal
  let x : Fin d → ℝ := fun k ↦ (lam : ℝ) * P.cellMass k
  have hmass (k : Fin d) (a : Bool) :
      ((Q {(k, a)}).toNNReal : ℝ) =
        P.cellMass k * (if a then P.propensity k else 1 - P.propensity k) := by
    change realMass Q {(k, a)} = _
    exact realMass_observedMarkLaw_singleton P k a
  have hx : ∀ k, (mu0 k : ℝ) + mu1 k = x k := by
    intro k
    simp only [mu0, mu1, x, NNReal.coe_mul]
    rw [hmass k false, hmass k true]
    simp
    ring
  have hover0 : ∀ k, epsilon * x k ≤ mu0 k := by
    intro k
    by_cases hk : P.cellMass k = 0
    · simp [x, mu0, hk, hmass]
    have hpk : 0 < P.cellMass k := lt_of_le_of_ne (P.cellMass_range k).1 (Ne.symm hk)
    have hovUpper := (hoverlap k hpk).2
    have hov : epsilon ≤ 1 - P.propensity k := by linarith
    calc
      epsilon * x k = (lam : ℝ) * (P.cellMass k * epsilon) := by simp [x]; ring
      _ ≤ (lam : ℝ) * (P.cellMass k * (1 - P.propensity k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hov (P.cellMass_range k).1) (by positivity)
      _ = (mu0 k : ℝ) := by simp [mu0, hmass]
  have hover1 : ∀ k, epsilon * x k ≤ mu1 k := by
    intro k
    by_cases hk : P.cellMass k = 0
    · simp [x, mu1, hk, hmass]
    have hpk : 0 < P.cellMass k := lt_of_le_of_ne (P.cellMass_range k).1 (Ne.symm hk)
    have hov := (hoverlap k hpk).1
    calc
      epsilon * x k = (lam : ℝ) * (P.cellMass k * epsilon) := by simp [x]; ring
      _ ≤ (lam : ℝ) * (P.cellMass k * P.propensity k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hov (P.cellMass_range k).1) (by positivity)
      _ = (mu1 k : ℝ) := by simp [mu1, hmass]
  have hsum : ∑ k, x k = (lam : ℝ) := by
    simp only [x, ← Finset.mul_sum, occupancy_sum_cellMass_eq_one P, mul_one]
  have hlaw := map_markedUsableTotal_finiteMarkedPoissonSampleLaw Q lam
  have hmeasExp : Measurable (fun r : ℕ ↦ Real.exp (-(r : ℝ))) :=
    measurable_of_countable _
  have hmarked : Measurable
      (markedUsableTotal : FiniteSample ((Fin d × Bool) × ℝ) → ℕ) := by
    unfold markedUsableTotal
    exact (measurable_of_countable usableTotalOfRegroupedCounts).comp
      ((measurable_of_countable (regroupArmCellCounts (d := d))).comp
        measurable_markedArmCellCounts)
  calc
    _ = ∫ r, Real.exp (-(r : ℝ))
        ∂Measure.map markedUsableTotal
          (finiteMarkedPoissonSampleLaw Q (Measure.dirac (0 : ℝ)) lam) := by
      rw [integral_map hmarked.aemeasurable hmeasExp.aestronglyMeasurable]
    _ = ∫ r, Real.exp (-(r : ℝ))
        ∂Measure.map usableTotalOfRegroupedCounts
          (Measure.pi (fun k : Fin d ↦
            (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k)))) := by
      rw [hlaw]
    _ = ∫ z : Fin d → ℕ × ℕ,
        Real.exp (-(usableTotalOfRegroupedCounts z : ℝ))
          ∂Measure.pi (fun k : Fin d ↦
            (poissonMeasure (mu0 k)).prod (poissonMeasure (mu1 k))) := by
      rw [integral_map
        (measurable_of_countable usableTotalOfRegroupedCounts).aemeasurable
        hmeasExp.aestronglyMeasurable]
    _ ≤ _ := by
      simpa [usableTotalOfRegroupedCounts, poissonUsableCellCount] using
        independentPoissonUsableLaplace_le_birthdayScale hd hepsilon
          hepsilon_half mu0 mu1 x hx hover0 hover1 hsum

private def augmentedZero {d : ℕ} (m : ℕ)
    (z : ℕ → (Fin d × Bool) × ℝ) : ℝ≥0∞ :=
  if streamUsableTotal (fun i ↦ (z i).1) m = 0 then 1 else 0

private noncomputable def augmentedPenalty {d : ℕ} (m : ℕ)
    (z : ℕ → (Fin d × Bool) × ℝ) : ℝ≥0∞ :=
  if streamUsableTotal (fun i ↦ (z i).1) m = 0 then 1
  else ((streamUsableTotal (fun i ↦ (z i).1) m : ℕ) : ℝ≥0∞)⁻¹

private lemma measurable_augmentedZero {d : ℕ} :
    Measurable (fun q : ℕ × (ℕ → (Fin d × Bool) × ℝ) ↦ augmentedZero q.1 q.2) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_of_countable (fun r : ℕ ↦ if r = 0 then (1 : ℝ≥0∞) else 0)).comp
    ((measurable_streamUsableTotal_fixed n).comp
      (measurable_pi_lambda _ fun i ↦ measurable_fst.comp (measurable_pi_apply i)))

private lemma measurable_augmentedPenalty {d : ℕ} :
    Measurable (fun q : ℕ × (ℕ → (Fin d × Bool) × ℝ) ↦ augmentedPenalty q.1 q.2) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_of_countable (fun r : ℕ ↦
    if r = 0 then (1 : ℝ≥0∞) else (r : ℝ≥0∞)⁻¹)).comp
      ((measurable_streamUsableTotal_fixed n).comp
        (measurable_pi_lambda _ fun i ↦ measurable_fst.comp (measurable_pi_apply i)))

private lemma augmentedZero_antitone {d : ℕ}
    (z : ℕ → (Fin d × Bool) × ℝ) {m n : ℕ} (hmn : m ≤ n) :
    augmentedZero n z ≤ augmentedZero m z :=
  streamUsableZero_antitone (fun i ↦ (z i).1) hmn

private lemma augmentedPenalty_antitone {d : ℕ}
    (z : ℕ → (Fin d × Bool) × ℝ) {m n : ℕ} (hmn : m ≤ n) :
    augmentedPenalty n z ≤ augmentedPenalty m z :=
  streamUsablePenalty_antitone (fun i ↦ (z i).1) hmn

/-- Half-intensity de-Poissonization after adding the deterministic mark. -/
private lemma augmented_half_depoissonization {d : ℕ}
    (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P] (n : ℕ)
    (g : ℕ → (ℕ → (Fin d × Bool) × ℝ) → ℝ≥0∞)
    (hg : Measurable (fun q : ℕ × (ℕ → (Fin d × Bool) × ℝ) ↦ g q.1 q.2))
    (hanti : ∀ z m n, m ≤ n → g n z ≤ g m z) :
    (1 / 2 : ℝ≥0∞) *
        (∫⁻ z, g n z ∂iidStreamLaw (P.prod (Measure.dirac (0 : ℝ)))) ≤
      ∫⁻ q, g q.1 q.2
        ∂poissonIIDStreamLaw (P.prod (Measure.dirac (0 : ℝ))) ((n : ℝ≥0) / 2) := by
  have hleft : (1 / 2 : ℝ≥0∞) *
      (∫⁻ z, g n z ∂iidStreamLaw (P.prod (Measure.dirac (0 : ℝ)))) ≤
      (poissonMeasure ((n : ℝ≥0) / 2)) (Iic n) *
        (∫⁻ z, g n z ∂iidStreamLaw (P.prod (Measure.dirac (0 : ℝ)))) := by
    simpa only [mul_comm] using mul_le_mul_right (poisson_half_intensity_Iic n)
      (∫⁻ z, g n z ∂iidStreamLaw (P.prod (Measure.dirac (0 : ℝ))))
  exact hleft.trans (iidStream_antitone_depoissonization
    (P.prod (Measure.dirac (0 : ℝ))) ((n : ℝ≥0) / 2) n g hg hanti)

/-- Zero mass and reciprocal penalty under the marked Poisson law, obtained
from its Laplace transform by a deterministic cutoff. -/
private lemma markedPoisson_zero_penalty_bounds
    {d : ℕ} (hd : 0 < d) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2)
    (P : RealLaw d) (hoverlap : Overlap epsilon P) (lam : ℝ≥0)
    (hlam : 0 < lam) :
    let A := poissonUsableLaplaceConstant epsilon * (lam : ℝ) ^ 2 /
      max (lam : ℝ) (d : ℝ)
    (∫ s, (if markedUsableTotal s = 0 then (1 : ℝ) else 0)
        ∂finiteMarkedPoissonSampleLaw (observedMarkLaw P)
          (Measure.dirac (0 : ℝ)) lam) ≤ Real.exp (-A) ∧
    (∫ s, (if markedUsableTotal s = 0 then (1 : ℝ)
        else 1 / markedUsableTotal s)
        ∂finiteMarkedPoissonSampleLaw (observedMarkLaw P)
          (Measure.dirac (0 : ℝ)) lam) ≤ 2 / A + Real.exp (-A / 2) := by
  dsimp only
  let μ := finiteMarkedPoissonSampleLaw (observedMarkLaw P)
    (Measure.dirac (0 : ℝ)) lam
  let A := poissonUsableLaplaceConstant epsilon * (lam : ℝ) ^ 2 /
    max (lam : ℝ) (d : ℝ)
  have hA : 0 < A := by
    dsimp [A]
    have hlamR : (0 : ℝ) < lam := by exact_mod_cast hlam
    have hmax : 0 < max (lam : ℝ) (d : ℝ) :=
      lt_of_lt_of_le hlamR (le_max_left _ _)
    exact div_pos
      (mul_pos (poissonUsableLaplaceConstant_pos hepsilon (by linarith))
        (sq_pos_of_pos hlamR)) hmax
  have hmgf : (∫ s, Real.exp (-(markedUsableTotal s : ℝ)) ∂μ) ≤
      Real.exp (-A) := by
    dsimp [μ, A]
    convert integral_exp_neg_markedUsable_le hd hepsilon
      hepsilon_half P hoverlap lam using 1 <;> ring
  have hmarked : Measurable
      (markedUsableTotal : FiniteSample ((Fin d × Bool) × ℝ) → ℕ) := by
    unfold markedUsableTotal
    exact (measurable_of_countable usableTotalOfRegroupedCounts).comp
      ((measurable_of_countable (regroupArmCellCounts (d := d))).comp
        measurable_markedArmCellCounts)
  let zeroF : FiniteSample ((Fin d × Bool) × ℝ) → ℝ := fun s ↦
    if markedUsableTotal s = 0 then 1 else 0
  let penF : FiniteSample ((Fin d × Bool) × ℝ) → ℝ := fun s ↦
    if markedUsableTotal s = 0 then 1 else 1 / markedUsableTotal s
  have hzeroInt : Integrable zeroF μ := by
    refine (integrable_const (1 : ℝ)).mono
      ((measurable_of_countable (fun r : ℕ ↦ if r = 0 then (1 : ℝ) else 0)).comp
        hmarked).aestronglyMeasurable ?_
    filter_upwards with s
    simp only [zeroF]
    split <;> simp
  have hpenInt : Integrable penF μ := by
    refine (integrable_const (1 : ℝ)).mono
      ((measurable_of_countable (fun r : ℕ ↦
        if r = 0 then (1 : ℝ) else 1 / (r : ℝ))).comp hmarked).aestronglyMeasurable ?_
    filter_upwards with s
    simp only [penF]
    by_cases hs : markedUsableTotal s = 0
    · simp [hs]
    · rw [if_neg hs, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one]
      exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hs)).2
        (by exact_mod_cast Nat.pos_of_ne_zero hs)
  have hexpInt : Integrable (fun s => Real.exp (-(markedUsableTotal s : ℝ))) μ := by
    refine (integrable_const (1 : ℝ)).mono
      ((measurable_of_countable (fun r : ℕ ↦ Real.exp (-(r : ℝ)))).comp
        hmarked).aestronglyMeasurable ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one,
      Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  constructor
  · exact (integral_mono_ae hzeroInt hexpInt
      (Filter.Eventually.of_forall fun s ↦ zeroIndicator_le_exp_neg _)).trans hmgf
  · have hcutInt : Integrable (fun s =>
        2 / A + Real.exp (A / 2) * Real.exp (-(markedUsableTotal s : ℝ))) μ :=
      (integrable_const (2 / A)).add (hexpInt.const_mul (Real.exp (A / 2)))
    have hcut := integral_mono_ae hpenInt hcutInt
      (Filter.Eventually.of_forall fun s ↦ reciprocalIndicator_le_cutoff A hA _)
    calc
      ∫ s, penF s ∂μ ≤
          ∫ s, (2 / A + Real.exp (A / 2) *
            Real.exp (-(markedUsableTotal s : ℝ))) ∂μ := hcut
      _ = 2 / A + Real.exp (A / 2) *
          ∫ s, Real.exp (-(markedUsableTotal s : ℝ)) ∂μ := by
        rw [integral_add (integrable_const _) (hexpInt.const_mul _),
          integral_const, integral_const_mul]
        simp
      _ ≤ 2 / A + Real.exp (A / 2) * Real.exp (-A) := by
        gcongr
      _ = 2 / A + Real.exp (-A / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- ENNReal form of the marked Poisson bounds, ready for de-Poissonization. -/
private lemma markedPoisson_lintegral_bounds
    {d : ℕ} (hd : 0 < d) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2)
    (P : RealLaw d) (hoverlap : Overlap epsilon P) (lam : ℝ≥0)
    (hlam : 0 < lam) :
    let A := poissonUsableLaplaceConstant epsilon * (lam : ℝ) ^ 2 /
      max (lam : ℝ) (d : ℝ)
    (∫⁻ s, (if markedUsableTotal s = 0 then (1 : ℝ≥0∞) else 0)
        ∂finiteMarkedPoissonSampleLaw (observedMarkLaw P)
          (Measure.dirac (0 : ℝ)) lam) ≤ ENNReal.ofReal (Real.exp (-A)) ∧
    (∫⁻ s, (if markedUsableTotal s = 0 then (1 : ℝ≥0∞)
        else ((markedUsableTotal s : ℕ) : ℝ≥0∞)⁻¹)
        ∂finiteMarkedPoissonSampleLaw (observedMarkLaw P)
          (Measure.dirac (0 : ℝ)) lam) ≤
      ENNReal.ofReal (2 / A + Real.exp (-A / 2)) := by
  dsimp only
  let μ := finiteMarkedPoissonSampleLaw (observedMarkLaw P)
    (Measure.dirac (0 : ℝ)) lam
  let zeroF : FiniteSample ((Fin d × Bool) × ℝ) → ℝ := fun s ↦
    if markedUsableTotal s = 0 then 1 else 0
  let penF : FiniteSample ((Fin d × Bool) × ℝ) → ℝ := fun s ↦
    if markedUsableTotal s = 0 then 1 else 1 / markedUsableTotal s
  have hmarked : Measurable
      (markedUsableTotal : FiniteSample ((Fin d × Bool) × ℝ) → ℕ) := by
    unfold markedUsableTotal
    exact (measurable_of_countable usableTotalOfRegroupedCounts).comp
      ((measurable_of_countable (regroupArmCellCounts (d := d))).comp
        measurable_markedArmCellCounts)
  have hzeroInt : Integrable zeroF μ := by
    refine (integrable_const (1 : ℝ)).mono
      ((measurable_of_countable (fun r : ℕ ↦ if r = 0 then (1 : ℝ) else 0)).comp
        hmarked).aestronglyMeasurable ?_
    filter_upwards with s
    simp only [zeroF]
    split <;> simp
  have hpenInt : Integrable penF μ := by
    refine (integrable_const (1 : ℝ)).mono
      ((measurable_of_countable (fun r : ℕ ↦
        if r = 0 then (1 : ℝ) else 1 / (r : ℝ))).comp hmarked).aestronglyMeasurable ?_
    filter_upwards with s
    simp only [penF]
    by_cases hs : markedUsableTotal s = 0
    · simp [hs]
    · rw [if_neg hs, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one]
      exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hs)).2
        (by exact_mod_cast Nat.pos_of_ne_zero hs)
  have hb := markedPoisson_zero_penalty_bounds hd hepsilon hepsilon_half
    P hoverlap lam hlam
  constructor
  · calc
      _ = ENNReal.ofReal (∫ s, zeroF s ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hzeroInt]
        · apply lintegral_congr
          intro s
          by_cases hs : markedUsableTotal s = 0 <;> simp [zeroF, hs]
        · filter_upwards with s
          simp only [zeroF]
          split <;> positivity
      _ ≤ ENNReal.ofReal (Real.exp
          (-(poissonUsableLaplaceConstant epsilon * (lam : ℝ) ^ 2 /
            max (lam : ℝ) (d : ℝ)))) := ENNReal.ofReal_le_ofReal hb.1
  · calc
      _ = ENNReal.ofReal (∫ s, penF s ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hpenInt]
        · apply lintegral_congr
          intro s
          by_cases hs : markedUsableTotal s = 0
          · simp [penF, hs]
          · simp [penF, hs, ENNReal.ofReal_inv_of_pos,
              Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)]
        · filter_upwards with s
          simp [penF]
          split
          · positivity
          · positivity
      _ ≤ ENNReal.ofReal
          (2 / (poissonUsableLaplaceConstant epsilon * (lam : ℝ) ^ 2 /
              max (lam : ℝ) (d : ℝ)) +
            Real.exp (-(poissonUsableLaplaceConstant epsilon * (lam : ℝ) ^ 2 /
              max (lam : ℝ) (d : ℝ)) / 2)) := ENNReal.ofReal_le_ofReal hb.2

-- @node: lem:zeng-usable-occupancy-reciprocal
/-- [The cited usable-occupancy reciprocal interface follows from the formal Poissonization and
  de-Poissonization argument](goal). -/
theorem zengUsableOccupancyReciprocal (epsilon : ℝ) :
    ZengUsableOccupancyReciprocal epsilon := by
  let c := poissonUsableLaplaceConstant epsilon
  let valid : Prop := 0 < epsilon ∧ epsilon < 1 / 2
  let b : ℝ := if valid then c / 8 else 1
  let B : ℝ := if valid then max (64 / c) 2 else 1
  refine ⟨b, B, ?_, ?_, ?_⟩
  · by_cases hv : valid
    · simp only [b, if_pos hv]
      exact div_pos (poissonUsableLaplaceConstant_pos hv.1
        (lt_trans hv.2 (by norm_num))) (by norm_num)
    · simp [b, hv]
  · by_cases hv : valid
    · simp only [B, if_pos hv]
      exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    · simp [B, hv]
  intro n d M sigma P
  have hv : valid := ⟨P.epsilon_pos, P.epsilon_lt_half⟩
  have hc : 0 < c := poissonUsableLaplaceConstant_pos hv.1
    (lt_trans hv.2 (by norm_num))
  have hb : b = c / 8 := by simp [b, hv]
  have hB : B = max (64 / c) 2 := by simp [B, hv]
  by_cases hd : d = 0
  · subst d
    have hmass := occupancy_sum_cellMass_eq_one P.law
    simp at hmass
  by_cases hn : n = 0
  · subst n
    constructor
    · have hle : realMass (productLaw 0 P.law)
          {s | usableTotal s = 0} ≤ 1 := by
        unfold realMass
        calc
          _ ≤ ((productLaw 0 P.law) Set.univ).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
          _ = 1 := by rw [measure_univ]; simp
      simpa [hb] using hle.trans (by norm_num : (1 : ℝ) ≤ 2)
    · have hzero : (fun s : Fin 0 → Obs d ↦
          if 0 < usableTotal s then (1 : ℝ) / usableTotal s else 0) = 0 := by
        funext s
        simp [usableTotal, usableCell, armCount]
      have hzint : (∫ s, (if 0 < usableTotal s then (1 : ℝ) / usableTotal s else 0)
          ∂productLaw 0 P.law) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards with s
        exact congrFun hzero s
      rw [hzint]
      positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let Q := observedMarkLaw P.law
  let lam : ℝ≥0 := (n : ℝ≥0) / 2
  let A : ℝ := c * (lam : ℝ) ^ 2 / max (lam : ℝ) (d : ℝ)
  let rate : ℝ := (n : ℝ) ^ 2 / (max n d : ℕ)
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    have hmax : 0 < max (lam : ℝ) (d : ℝ) := by positivity
    positivity
  have hrate : 0 < rate := by
    dsimp [rate]
    positivity
  have hA_rate : c / 4 * rate ≤ A := by
    have hden : max (lam : ℝ) (d : ℝ) ≤ max (n : ℝ) (d : ℝ) := by
      apply max_le_max_right
      dsimp [lam]
      norm_num
    have hmaxpos : 0 < max (lam : ℝ) (d : ℝ) := by positivity
    have hmaxNpos : 0 < max (n : ℝ) (d : ℝ) := by positivity
    dsimp [A, rate, lam]
    rw [Nat.cast_max]
    have heq : c / 4 * ((n : ℝ) ^ 2 / max (n : ℝ) (d : ℝ)) =
        (c * ((n : ℝ) / 2) ^ 2) / max (n : ℝ) (d : ℝ) := by ring
    rw [heq]
    exact div_le_div_of_nonneg_left (by positivity) hmaxpos hden
  have hmarked := markedPoisson_lintegral_bounds hdpos hv.1 hv.2
    P.law P.overlap lam hlam
  let hzero : ℕ → ℝ≥0∞ := fun r ↦ if r = 0 then 1 else 0
  let hpen : ℕ → ℝ≥0∞ := fun r ↦ if r = 0 then 1 else (r : ℝ≥0∞)⁻¹
  have hdepo0 := augmented_half_depoissonization Q n augmentedZero
    measurable_augmentedZero (fun z _ _ hmn ↦ augmentedZero_antitone z hmn)
  have hdepoP := augmented_half_depoissonization Q n augmentedPenalty
    measurable_augmentedPenalty (fun z _ _ hmn ↦ augmentedPenalty_antitone z hmn)
  have hfix0 : (∫⁻ z, streamUsableZero n z ∂iidStreamLaw Q) ≤
      2 * ENNReal.ofReal (Real.exp (-A)) := by
    have hleft := lintegral_augmentedPrefix_eq (n := n) Q hzero
    have hright := lintegral_poissonStream_eq_markedUsable Q lam hzero
    dsimp [augmentedZero, hzero] at hdepo0 hleft hright
    rw [hleft, hright] at hdepo0
    have hm := mul_le_mul_of_nonneg_left hdepo0 (by positivity : (0 : ℝ≥0∞) ≤ 2)
    simp only [div_eq_mul_inv, one_mul] at hm
    rw [← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul] at hm
    simpa [streamUsableZero, A, c] using
      hm.trans (mul_le_mul_of_nonneg_left hmarked.1 (by positivity))
  have hfixP : (∫⁻ z, streamUsablePenalty n z ∂iidStreamLaw Q) ≤
      2 * ENNReal.ofReal (2 / A + Real.exp (-A / 2)) := by
    have hleft := lintegral_augmentedPrefix_eq (n := n) Q hpen
    have hright := lintegral_poissonStream_eq_markedUsable Q lam hpen
    dsimp [augmentedPenalty, hpen] at hdepoP hleft hright
    rw [hleft, hright] at hdepoP
    have hm := mul_le_mul_of_nonneg_left hdepoP (by positivity : (0 : ℝ≥0∞) ≤ 2)
    simp only [div_eq_mul_inv, one_mul] at hm
    rw [← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul] at hm
    simpa [streamUsablePenalty, A, c] using
      hm.trans (mul_le_mul_of_nonneg_left hmarked.2 (by positivity))
  have hprod0 := lintegral_usableZero_productLaw_eq_stream (n := n) P.law
  have hprodP := lintegral_usablePenalty_productLaw_eq_stream (n := n) P.law
  constructor
  · have hset : MeasurableSet {s : Fin n → Obs d | usableTotal s = 0} :=
      (measurableSet_singleton 0).preimage measurable_usableTotal
    have hmassLin : (productLaw n P.law) {s | usableTotal s = 0} =
        ∫⁻ s, (if usableTotal s = 0 then (1 : ℝ≥0∞) else 0)
          ∂productLaw n P.law := by
      rw [← lintegral_indicator_one hset]
      apply lintegral_congr
      intro s
      by_cases hs : usableTotal s = 0 <;> simp [hs]
    have hENN : (productLaw n P.law) {s | usableTotal s = 0} ≤
        2 * ENNReal.ofReal (Real.exp (-A)) := by
      rw [hmassLin, hprod0]
      exact hfix0
    unfold realMass
    have hreal := ENNReal.toReal_mono (by finiteness) hENN
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
    norm_num at hreal
    rw [hb]
    refine hreal.trans ?_
    gcongr
    have hratio : 0 ≤ (n : ℝ) ^ 2 / (max n d : ℕ) := by positivity
    have hweak : c / 8 * ((n : ℝ) ^ 2 / (max n d : ℕ)) ≤ A := by
      apply le_trans _ hA_rate
      dsimp [rate]
      nlinarith [hc, hratio]
    calc
      -A ≤ -(c / 8 * ((n : ℝ) ^ 2 / (max n d : ℕ))) := neg_le_neg hweak
      _ = -(c / 8) * (n : ℝ) ^ 2 / (max n d : ℕ) := by ring
  · let recip : (Fin n → Obs d) → ℝ := fun s ↦
      if 0 < usableTotal s then 1 / usableTotal s else 0
    have hrecipInt : Integrable recip (productLaw n P.law) := by
      refine (integrable_const (1 : ℝ)).mono
        ((measurable_of_countable (fun r : ℕ ↦
          if 0 < r then (1 : ℝ) / r else 0)).comp measurable_usableTotal).aestronglyMeasurable ?_
      filter_upwards with s
      simp only [recip]
      by_cases hs : 0 < usableTotal s
      · rw [if_pos hs, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one]
        exact (div_le_one (by exact_mod_cast hs)).2 (by exact_mod_cast hs)
      · simp [hs]
    have hrecENN : ENNReal.ofReal (∫ s, recip s ∂productLaw n P.law) ≤
        ∫⁻ s, (if usableTotal s = 0 then (1 : ℝ≥0∞)
          else ((usableTotal s : ℕ) : ℝ≥0∞)⁻¹) ∂productLaw n P.law := by
      rw [ofReal_integral_eq_lintegral_ofReal hrecipInt]
      · apply lintegral_mono
        intro s
        by_cases hs : usableTotal s = 0
        · simp [recip, hs]
        · simp [recip, hs, Nat.pos_of_ne_zero hs, ENNReal.ofReal_inv_of_pos,
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)]
      · filter_upwards with s
        simp [recip]
        split <;> positivity
    have hrecBound : ENNReal.ofReal (∫ s, recip s ∂productLaw n P.law) ≤
        2 * ENNReal.ofReal (2 / A + Real.exp (-A / 2)) := by
      exact hrecENN.trans (hprodP.le.trans hfixP)
    have hreal := ENNReal.toReal_mono (by finiteness) hrecBound
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun s ↦ by
      simp [recip]; split <;> positivity)), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 / A + Real.exp (-A / 2))] at hreal
    norm_num at hreal
    change (∫ s, recip s ∂productLaw n P.law) ≤ _
    rw [hB, hb]
    refine hreal.trans ?_
    rw [show -(c / 8) * (n : ℝ) ^ 2 / (max n d : ℕ) =
        -(c / 8) * rate by dsimp [rate]; ring]
    have hinv : 4 / A ≤ (64 / c) * ((max n d : ℕ) / (n : ℝ) ^ 2) := by
      rw [show ((max n d : ℕ) / (n : ℝ) ^ 2) = 1 / rate by
        dsimp [rate]
        field_simp]
      rw [show 64 / c * (1 / rate) = 64 / (c * rate) by field_simp]
      apply (div_le_div_iff₀ hA (mul_pos hc hrate)).2
      nlinarith [hA_rate]
    have hexp : 2 * Real.exp (-A / 2) ≤
        2 * Real.exp (-(c / 8) * rate) := by
      gcongr
      nlinarith
    have hcoef1 : 64 / c ≤ max (64 / c) 2 := le_max_left _ _
    have hcoef2 : (2 : ℝ) ≤ max (64 / c) 2 := le_max_right _ _
    dsimp [recip] at *
    calc
      2 * (2 / A + Real.exp (-A / 2)) =
          4 / A + 2 * Real.exp (-A / 2) := by ring
      _ ≤ 64 / c * ((max n d : ℕ) / (n : ℝ) ^ 2) +
          2 * Real.exp (-(c / 8) * rate) := add_le_add hinv hexp
      _ ≤ max (64 / c) 2 * ((max n d : ℕ) / (n : ℝ) ^ 2) +
          max (64 / c) 2 * Real.exp (-(c / 8) * rate) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hcoef1 (by positivity))
          (mul_le_mul_of_nonneg_right hcoef2
            (Real.exp_pos (-(c / 8) * rate)).le)
      _ = max (64 / c) 2 *
          ((max n d : ℕ) / (n : ℝ) ^ 2 + Real.exp (-(c / 8) * rate)) := by ring

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
