/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Causalean.Stat.Minimax.MinimaxRisk
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Squared-risk transport through Markov kernels

This module packages the Blackwell comparison for squared loss: randomizing an experiment
through a Markov kernel cannot improve the best attainable squared-error risk. It constructs
the Rao--Blackwell pullback of a bounded estimator, proves its risk comparison under an affine
change of target, and exports the resulting minimax-hardness transport for both one observation
and finite independent samples, including the empty sample.

## Main results

* `forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport` transfers a quantified
  squared-risk lower bound through a randomized experiment and an affine target change.
* `finProductKernel_comp_pi` identifies the image of an independent product experiment under
  the coordinatewise product kernel.
* `forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport_pi` gives the finite-product
  form of the randomized transport theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Causalean.Stat

universe uX uY uI

variable {X : Type uX} {Y : Type uY} {Iota : Type uI}
  [MeasurableSpace X] [MeasurableSpace Y]

/-! ## Kernel means and affine pullbacks -/

/-- A real-valued function is uniformly bounded when one finite nonnegative constant bounds
its absolute value at every input. -/
def UniformlyBounded {A : Type*} (f : A → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M

/-- The kernel mean of an estimator is its expectation under the output distribution selected
by each input to the kernel. -/
noncomputable def kernelMean (K : Kernel X Y) (T : Y → ℝ) : X → ℝ :=
  fun x => ∫ y, T y ∂K x

/-- [Measurability of a real-valued estimator](hyp:hT) ensures that [its expectation under each
kernel output distribution varies measurably with the kernel input](goal). -/
@[fun_prop]
theorem measurable_kernelMean (K : Kernel X Y) {T : Y → ℝ} (hT : Measurable T) :
    Measurable (kernelMean K T) := by
  exact hT.stronglyMeasurable.integral_kernel.measurable

/-- If [a proposed bound is nonnegative](hyp:hM) and [bounds the estimator in absolute value at
every output](hyp:hT), then [the kernel mean obeys the same absolute bound at every input](goal)
when each kernel output is a probability distribution. -/
theorem abs_kernelMean_le (K : Kernel X Y) [IsMarkovKernel K]
    {T : Y → ℝ} {M : ℝ} (hM : 0 ≤ M) (hT : ∀ y, |T y| ≤ M) :
    ∀ x, |kernelMean K T x| ≤ M := by
  intro x
  haveI : IsProbabilityMeasure (K x) := inferInstance
  simpa [kernelMean, Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const
      (μ := K x) (f := T) (C := M) (Filter.Eventually.of_forall hT))

/-- [Uniform boundedness of an estimator](hyp:hT) implies that [averaging it against a Markov
kernel is uniformly bounded by the same witness](goal). -/
theorem uniformlyBounded_kernelMean (K : Kernel X Y) [IsMarkovKernel K]
    {T : Y → ℝ} (hT : UniformlyBounded T) :
    UniformlyBounded (kernelMean K T) := by
  obtain ⟨M, hM, hT⟩ := hT
  exact ⟨M, hM, abs_kernelMean_le K hM hT⟩

/-- The affine kernel pullback averages a target estimator over the kernel, subtracts the
target offset, and divides by the target slope. -/
noncomputable def kernelAffinePullback (K : Kernel X Y) (a b : ℝ)
    (targetEst : Y → ℝ) : X → ℝ :=
  fun x => (kernelMean K targetEst x - b) / a

/-- [Measurability of a target estimator](hyp:htarget) ensures that [its affine kernel
pullback is measurable on the source experiment](goal). -/
@[fun_prop]
theorem measurable_kernelAffinePullback (K : Kernel X Y) {a b : ℝ}
    {targetEst : Y → ℝ} (htarget : Measurable targetEst) :
    Measurable (kernelAffinePullback K a b targetEst) := by
  exact ((measurable_kernelMean K htarget).sub measurable_const).div measurable_const

/-- If [the affine slope is nonzero](hyp:ha) and [the target estimator is uniformly
bounded](hyp:htarget), then [the affine kernel pullback is uniformly bounded on the source
experiment](goal). -/
theorem uniformlyBounded_kernelAffinePullback (K : Kernel X Y) [IsMarkovKernel K]
    {a b : ℝ} (ha : a ≠ 0) {targetEst : Y → ℝ}
    (htarget : UniformlyBounded targetEst) :
    UniformlyBounded (kernelAffinePullback K a b targetEst) := by
  obtain ⟨M, hM, htarget⟩ := htarget
  refine ⟨(M + |b|) / |a|, div_nonneg (add_nonneg hM (abs_nonneg b)) (abs_nonneg a), ?_⟩
  intro x
  rw [kernelAffinePullback, abs_div]
  exact div_le_div_of_nonneg_right
    ((abs_sub _ _).trans (add_le_add (abs_kernelMean_le K hM htarget x) le_rfl))
    (abs_nonneg a)

/-! ## Tower identity and squared-risk comparison -/

/-- If [the target estimator is measurable](hyp:hTmeas) and [uniformly bounded](hyp:hTbound),
then [its expectation after taking the kernel mean under a source probability law equals its
expectation under the garbled law](goal). -/
theorem integral_kernelMean_eq_integral_comp (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {T : Y → ℝ}
    (hTmeas : Measurable T) (hTbound : UniformlyBounded T) :
    ∫ x, kernelMean K T x ∂P = ∫ y, T y ∂(K ∘ₘ P) := by
  obtain ⟨M, _hM, hT⟩ := hTbound
  have hTint : Integrable T (K ∘ₘ P) :=
    (integrable_const M).mono' hTmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hT y)
  simpa [kernelMean] using
    (Causalean.Mathlib.MeasureTheory.integral_bind K.measurable hTint).symm

/-- If [the target estimator is measurable](hyp:hTmeas) and [uniformly bounded](hyp:hTbound),
then [the squared error of its kernel mean is no greater than the kernel average of its squared
error at each source observation](goal). -/
theorem sqLoss_kernelMean_le (K : Kernel X Y) [IsMarkovKernel K]
    {T : Y → ℝ} (hTmeas : Measurable T) (hTbound : UniformlyBounded T)
    (c : ℝ) (x : X) :
    (kernelMean K T x - c) ^ 2 ≤ ∫ y, (T y - c) ^ 2 ∂K x := by
  haveI : IsProbabilityMeasure (K x) := inferInstance
  obtain ⟨M, hM, hT⟩ := hTbound
  have hTint : Integrable T (K x) :=
    (integrable_const M).mono' hTmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hT y)
  have hdiffint : Integrable (fun y => T y - c) (K x) :=
    hTint.sub (integrable_const c)
  have hlossint : Integrable (fun y => (T y - c) ^ 2) (K x) := by
    refine (integrable_const ((M + |c|) ^ 2)).mono'
      ((hTmeas.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg c))]
    exact (abs_sub _ _).trans (add_le_add (hT y) le_rfl)
  have hjensen := ((show Even 2 by norm_num).convexOn_pow :
      ConvexOn ℝ Set.univ (fun z : ℝ => z ^ 2)).map_integral_le
        (continuousOn_pow 2) isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
        hdiffint hlossint
  simpa [kernelMean, integral_sub hTint (integrable_const c), integral_const] using hjensen

/-- If [the target estimator is measurable](hyp:hTmeas) and [uniformly bounded](hyp:hTbound),
then [Rao--Blackwellizing it through a Markov kernel cannot increase squared risk](goal): the
source-law risk of the kernel mean is at most the target-law risk after garbling. -/
theorem sqRisk_kernelMean_le_comp (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {T : Y → ℝ}
    (hTmeas : Measurable T) (hTbound : UniformlyBounded T) (c : ℝ) :
    sqRisk P (kernelMean K T) c ≤ sqRisk (K ∘ₘ P) T c := by
  obtain ⟨M, hM, hT⟩ := hTbound
  have hlossMeas : Measurable (fun y => (T y - c) ^ 2) :=
    (hTmeas.sub measurable_const).pow_const 2
  have hlossBound : UniformlyBounded (fun y => (T y - c) ^ 2) := by
    refine ⟨(M + |c|) ^ 2, sq_nonneg _, ?_⟩
    intro y
    rw [abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg c))]
    exact (abs_sub _ _).trans (add_le_add (hT y) le_rfl)
  obtain ⟨N, _hN, hmeanLoss⟩ := uniformlyBounded_kernelMean K hlossBound
  have hmeanLossInt : Integrable (kernelMean K fun y => (T y - c) ^ 2) P :=
    (integrable_const N).mono' (measurable_kernelMean K hlossMeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hmeanLoss x)
  unfold sqRisk
  calc
    (∫ x, (kernelMean K T x - c) ^ 2 ∂P) ≤
        ∫ x, kernelMean K (fun y => (T y - c) ^ 2) x ∂P :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hmeanLossInt
        (Filter.Eventually.of_forall fun x =>
          sqLoss_kernelMean_le K hTmeas ⟨M, hM, hT⟩ c x)
    _ = ∫ y, (T y - c) ^ 2 ∂(K ∘ₘ P) :=
      integral_kernelMean_eq_integral_comp P K hlossMeas hlossBound

/-- If [the affine slope is nonzero](hyp:ha), [the target estimator is
measurable](hyp:htargetMeas), and [the target estimator is uniformly
bounded](hyp:htargetBound), then [the source risk of the affine kernel pullback, multiplied by
the squared slope, is at most the target risk under the garbled law](goal). -/
theorem sqRisk_kernelAffinePullback_le_comp (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {a b theta : ℝ} (ha : a ≠ 0)
    {targetEst : Y → ℝ} (htargetMeas : Measurable targetEst)
    (htargetBound : UniformlyBounded targetEst) :
    a ^ 2 * sqRisk P (kernelAffinePullback K a b targetEst) theta ≤
      sqRisk (K ∘ₘ P) targetEst (a * theta + b) := by
  have hpull : ∀ x,
      a ^ 2 * (kernelAffinePullback K a b targetEst x - theta) ^ 2 =
        (kernelMean K targetEst x - (a * theta + b)) ^ 2 := by
    intro x
    unfold kernelAffinePullback
    field_simp
    ring
  calc
    a ^ 2 * sqRisk P (kernelAffinePullback K a b targetEst) theta =
        ∫ x, a ^ 2 * (kernelAffinePullback K a b targetEst x - theta) ^ 2 ∂P := by
      exact (integral_const_mul (a ^ 2) _).symm
    _ = sqRisk P (kernelMean K targetEst) (a * theta + b) := by
      unfold sqRisk
      exact integral_congr_ae (Filter.Eventually.of_forall hpull)
    _ ≤ sqRisk (K ∘ₘ P) targetEst (a * theta + b) :=
      sqRisk_kernelMean_le_comp P K htargetMeas htargetBound _

/-- Suppose [the affine slope is nonzero](hyp:ha), [each target law is obtained by passing its
source law through the common Markov kernel](hyp:hQ), and [every measurable uniformly bounded
source estimator incurs squared risk at least a fixed level for some parameter
index](hyp:hsource). Then [every measurable uniformly bounded target estimator incurs at least
the source level multiplied by the squared slope for some parameter index](goal), with the
target parameter transformed by the same affine map. -/
theorem forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport
    (P : Iota → Measure X) (Q : Iota → Measure Y)
    [∀ j, IsProbabilityMeasure (P j)]
    (K : Kernel X Y) [IsMarkovKernel K]
    (theta : Iota → ℝ) (a b L : ℝ) (ha : a ≠ 0)
    (hQ : ∀ j, Q j = K ∘ₘ P j)
    (hsource : ∀ sourceEst : X → ℝ, Measurable sourceEst →
      UniformlyBounded sourceEst → ∃ j, L ≤ sqRisk (P j) sourceEst (theta j)) :
    ∀ targetEst : Y → ℝ, Measurable targetEst → UniformlyBounded targetEst →
      ∃ j, a ^ 2 * L ≤ sqRisk (Q j) targetEst (a * theta j + b) := by
  intro targetEst htargetMeas htargetBound
  obtain ⟨j, hj⟩ := hsource (kernelAffinePullback K a b targetEst)
    (measurable_kernelAffinePullback K htargetMeas)
    (uniformlyBounded_kernelAffinePullback K ha htargetBound)
  refine ⟨j, ?_⟩
  calc
    a ^ 2 * L ≤ a ^ 2 * sqRisk (P j)
        (kernelAffinePullback K a b targetEst) (theta j) :=
      mul_le_mul_of_nonneg_left hj (sq_nonneg a)
    _ ≤ sqRisk (K ∘ₘ P j) targetEst (a * theta j + b) :=
      sqRisk_kernelAffinePullback_le_comp (P j) K ha htargetMeas htargetBound
    _ = sqRisk (Q j) targetEst (a * theta j + b) := by
      rw [hQ j]

/-! ## Independent finite products -/

/-- The finite product kernel applies one Markov kernel independently to each coordinate,
with the unique point-mass kernel on the empty product. -/
noncomputable def finProductKernel (n : ℕ) (K : Kernel X Y) :
    Kernel (Fin n → X) (Fin n → Y) :=
  match n with
  | 0 => Kernel.deterministic (fun _ => fun i => Fin.elim0 i) measurable_const
  | n + 1 =>
      let eX := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let eY := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0
      ((K ∥ₖ finProductKernel n K).comap eX eX.measurable).map eY.symm

/-- [Each fibre of the finite product kernel equals the independent product of its coordinate
output laws](goal), including the unique empty product fibre. -/
theorem finProductKernel_apply (n : ℕ) (K : Kernel X Y) [IsMarkovKernel K]
    (x : Fin n → X) :
    finProductKernel n K x = Measure.pi (fun i : Fin n => K (x i)) := by
  induction n with
  | zero =>
      rw [finProductKernel, Kernel.deterministic_apply]
      exact (Measure.pi_of_empty _ _).symm
  | succ n ih =>
      let _ : IsMarkovKernel (finProductKernel n K) :=
        ⟨fun z => ⟨by rw [ih z]; exact measure_univ⟩⟩
      let eX := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let eY := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0
      rw [finProductKernel, Kernel.map_apply _ eY.symm.measurable,
        Kernel.comap_apply, Kernel.parallelComp_apply, ih]
      exact (MeasureTheory.measurePreserving_piFinSuccAbove
        (fun i : Fin (n + 1) => K (x i)) 0).symm.map_eq

/-- The independent finite product of a Markov kernel is itself a Markov kernel, including
the zero-coordinate product. -/
instance instIsMarkovKernelFinProductKernel (n : ℕ) (K : Kernel X Y)
    [IsMarkovKernel K] : IsMarkovKernel (finProductKernel n K) := by
  refine ⟨fun x => ?_⟩
  rw [finProductKernel_apply]
  infer_instance

/-- [Passing an independent finite product law through the coordinatewise product kernel
produces the product of the one-coordinate garbled law](goal), including when there are no
coordinates. -/
theorem finProductKernel_comp_pi (n : ℕ) (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] :
    finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P) =
      Measure.pi (fun _ : Fin n => K ∘ₘ P) := by
  induction n with
  | zero =>
      rw [finProductKernel, Measure.deterministic_comp_eq_map,
        Measure.pi_of_empty, Measure.map_dirac]
      exact (Measure.pi_of_empty _ _).symm
  | succ n ih =>
      let eX := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let eY := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0
      have hsource :
          (Measure.pi (fun _ : Fin (n + 1) => P)).map eX =
            P.prod (Measure.pi (fun _ : Fin n => P)) :=
        (MeasureTheory.measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => P) 0).map_eq
      have hparallel :
          (K ∥ₖ finProductKernel n K) ∘ₘ
              (P.prod (Measure.pi (fun _ : Fin n => P))) =
            (K ∘ₘ P).prod
              (finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P)) := by
        calc
          (K ∥ₖ finProductKernel n K) ∘ₘ
                (P.prod (Measure.pi (fun _ : Fin n => P))) =
              (K ∥ₖ Kernel.id) ∘ₘ
                ((Kernel.id ∥ₖ finProductKernel n K) ∘ₘ
                  (P.prod (Measure.pi (fun _ : Fin n => P)))) := by
            rw [Measure.comp_assoc, Kernel.parallelComp_comp_parallelComp,
              Kernel.comp_id, Kernel.id_comp]
          _ = (K ∥ₖ Kernel.id) ∘ₘ
                (P.prod (finProductKernel n K ∘ₘ
                  Measure.pi (fun _ : Fin n => P))) := by
            rw [← Measure.prod_comp_right]
          _ = (K ∘ₘ P).prod
                (finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P)) := by
            rw [Measure.prod_comp_left]
      calc
        finProductKernel (n + 1) K ∘ₘ
              Measure.pi (fun _ : Fin (n + 1) => P) =
            (((K ∥ₖ finProductKernel n K) ∘ₘ
              (Measure.pi (fun _ : Fin (n + 1) => P)).map eX).map eY.symm) := by
          rw [finProductKernel, ← Kernel.deterministic_comp_eq_map eY.symm.measurable,
            ← Measure.comp_assoc, ← Kernel.comp_deterministic_eq_comap,
            ← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
            Measure.deterministic_comp_eq_map]
        _ = ((K ∘ₘ P).prod (Measure.pi (fun _ : Fin n => K ∘ₘ P))).map eY.symm := by
          rw [hsource, hparallel, ih]
        _ = Measure.pi (fun _ : Fin (n + 1) => K ∘ₘ P) :=
          (MeasureTheory.measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => K ∘ₘ P) 0).symm.map_eq

/-- If [the affine slope is nonzero](hyp:ha), [a finite-sample target estimator is
measurable](hyp:htargetMeas), and [that estimator is uniformly bounded](hyp:htargetBound), then
[the source-product risk of its affine product-kernel pullback, multiplied by the squared
slope, is at most its target-product risk](goal). -/
theorem sqRisk_finProductKernel_affinePullback_le (n : ℕ)
    (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {a b theta : ℝ} (ha : a ≠ 0)
    {targetEst : (Fin n → Y) → ℝ} (htargetMeas : Measurable targetEst)
    (htargetBound : UniformlyBounded targetEst) :
    a ^ 2 * sqRisk (Measure.pi (fun _ : Fin n => P))
        (kernelAffinePullback (finProductKernel n K) a b targetEst) theta ≤
      sqRisk (Measure.pi (fun _ : Fin n => K ∘ₘ P))
        targetEst (a * theta + b) := by
  calc
    a ^ 2 * sqRisk (Measure.pi (fun _ : Fin n => P))
        (kernelAffinePullback (finProductKernel n K) a b targetEst) theta ≤
      sqRisk (finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P))
        targetEst (a * theta + b) :=
      sqRisk_kernelAffinePullback_le_comp
        (Measure.pi (fun _ : Fin n => P)) (finProductKernel n K)
        ha htargetMeas htargetBound
    _ = sqRisk (Measure.pi (fun _ : Fin n => K ∘ₘ P))
        targetEst (a * theta + b) := by
      rw [finProductKernel_comp_pi]

/-- Suppose [the affine slope is nonzero](hyp:ha), [each one-coordinate target law is obtained
by applying the common Markov kernel to its source law](hyp:hQ), and [every measurable uniformly
bounded estimator on the finite source product incurs squared risk at least a fixed level for
some parameter index](hyp:hsource). Then [every measurable uniformly bounded estimator on the
target product incurs at least the source level multiplied by the squared slope for some
parameter index](goal), including when the sample has no coordinates. -/
theorem forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport_pi
    (n : ℕ) (P : Iota → Measure X) (Q : Iota → Measure Y)
    [∀ j, IsProbabilityMeasure (P j)]
    (K : Kernel X Y) [IsMarkovKernel K]
    (theta : Iota → ℝ) (a b L : ℝ) (ha : a ≠ 0)
    (hQ : ∀ j, Q j = K ∘ₘ P j)
    (hsource : ∀ sourceEst : (Fin n → X) → ℝ, Measurable sourceEst →
      UniformlyBounded sourceEst →
      ∃ j, L ≤ sqRisk (Measure.pi (fun _ : Fin n => P j)) sourceEst (theta j)) :
    ∀ targetEst : (Fin n → Y) → ℝ, Measurable targetEst →
      UniformlyBounded targetEst →
      ∃ j, a ^ 2 * L ≤ sqRisk (Measure.pi (fun _ : Fin n => Q j))
        targetEst (a * theta j + b) := by
  apply forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport
    (P := fun j => Measure.pi (fun _ : Fin n => P j))
    (Q := fun j => Measure.pi (fun _ : Fin n => Q j))
    (K := finProductKernel n K) theta a b L ha
  · intro j
    rw [finProductKernel_comp_pi, hQ j]
  · exact hsource

end Causalean.Stat
