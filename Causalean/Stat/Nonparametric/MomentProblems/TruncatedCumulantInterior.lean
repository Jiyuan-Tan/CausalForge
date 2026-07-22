/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.AtomicLaw
import Causalean.Stat.Nonparametric.MomentProblems.SymmetricAtomSolve

/-!
# The truncated cumulant range has nonempty interior

The main result of this module says that the truncated cumulant sequences of orders two through
`L` attainable by *centered, non-Gaussian* probability laws on the real line with finite `L`-th
moment fill up a set with nonempty interior: there is one attainable cumulant vector all of whose
sufficiently small perturbations are again attainable by such a law.

The proof is constructive rather than an appeal to the general (truncated Hamburger) moment
problem.  Put `L + 1` distinct equally spaced symmetric atoms on the line.  Matching the first
`L + 1` raw moments of a weight vector to a target is then a linear system with a transposed
Vandermonde matrix, hence invertible, and the moment target itself is obtained from the cumulant
target by the triangular moment↔cumulant inversion — so weights depend continuously on the
prescribed cumulants (`SymmetricAtomSolve`).  At the uniform weight vector all weights are strictly
positive, and positivity is an open condition, so every nearby cumulant target still solves to
strictly positive weights, i.e. to a genuine probability law.  That law is centered (the atoms are
symmetric and the first-moment equation is part of the solved system), has all moments finite
(finite support), and is non-Gaussian (at least two atoms carry positive mass).

The order `L = 0` case is degenerate — a single atom would be a point mass, i.e. a degenerate
Gaussian — and is handled separately by an explicit fair two-point law on `±1`.

References: Akhiezer (1965), *The Classical Moment Problem*; Curto–Fialkow (1991) on truncated
moment problems and flat extensions; Schmüdgen (2017), *The Moment Problem*, Theorem 10.7.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- **Interior of the truncated cumulant range at order `L`.** There is a cumulant target and a
strictly positive radius such that every cumulant sequence within that radius of the target, in
orders two through `L`, is realized by a probability law on the real line that is centered, is not
a Gaussian law, and has finite `L`-th moment.

Equivalently: the set of truncated cumulant sequences of orders `2, …, L` attainable by centered
non-Gaussian laws with `L` moments has nonempty interior.  This is what one needs in order to
perturb a "generic" cumulant configuration freely without leaving the model class — for instance to
move a parameter off an exceptional algebraic locus while staying inside the non-Gaussian source
model of linear non-Gaussian causal discovery. -/
def TruncatedMomentInterior (L : ℕ) : Prop :=
  ∃ (c : ℕ → ℝ) (ε : ℝ), 0 < ε ∧
    ∀ c' : ℕ → ℝ, (∀ r, 2 ≤ r → r ≤ L → |c' r - c r| < ε) →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ (∫ x, x ∂ν = 0) ∧
        ¬ IsGaussianLaw ν ∧ MemLp (id : ℝ → ℝ) (L : ℝ≥0∞) ν ∧
        ∀ r, 2 ≤ r → r ≤ L → sourceCumulant ν id r = c' r

/-- Order zero carries no cumulant constraint at all, so any centered non-Gaussian law with a
finite zeroth moment works; the fair two-point law on `±1` is one. -/
private theorem truncatedMomentInterior_zero : TruncatedMomentInterior 0 := by
  refine ⟨0, 1, by norm_num, ?_⟩
  intro c' hc'
  let x : Fin 2 → ℝ := ![-1, 1]
  let p : Fin 2 → ℝ := ![1 / 2, 1 / 2]
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    fin_cases i <;> fin_cases j
    · rfl
    · norm_num [x] at hij
    · norm_num [x] at hij
    · rfl
  have hp : ∀ i, 0 < p i := by intro i; fin_cases i <;> norm_num [p]
  have hsum : ∑ i, p i = 1 := by norm_num [p, Fin.sum_univ_two]
  refine ⟨atomicLaw 2 x p, isProbabilityMeasure_atomicLaw hx (fun i => (hp i).le) hsum,
    ?_, not_isGaussianLaw_atomicLaw hx hp (by omega),
    (by simpa using memLp_id_atomicLaw hx (fun i => (hp i).le) hsum (0 : ℝ≥0∞)), ?_⟩
  · rw [integral_atomicLaw hx (fun i => (hp i).le) (fun x => x)]
    norm_num [x, p, Fin.sum_univ_two]
  · intro r hr hr0
    omega

/-- **The truncated cumulant range has nonempty interior.** At every truncation order there is a
cumulant vector, of orders two through `L`, together with a strictly positive radius, such that
every cumulant vector within that radius is the truncated cumulant vector of some centered,
non-Gaussian probability law on the real line with finite `L`-th moment.

The witness is an explicit finite atomic law on `L + 1` equally spaced symmetric atoms whose weights
are recovered from the target moments by inverting a Vandermonde system, the target moments in turn
coming from the target cumulants by the triangular moment–cumulant inversion.  Both steps are
continuous, and the uniform-weight law sits strictly inside the weight-positivity constraints, so a
whole neighborhood of cumulant targets stays realizable. -/
theorem truncatedMomentInterior (L : ℕ) : TruncatedMomentInterior L := by
  by_cases hL : L = 0
  · simpa [hL] using truncatedMomentInterior_zero
  have hLpos : 1 ≤ L := by omega
  let radius : ℝ := 1 / (L + 1 : ℝ)
  have hradius : 0 < radius := by dsimp [radius]; positivity
  obtain ⟨ε, hε, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_cumulantToWeights L).continuousAt radius hradius
  refine ⟨uniformCumulants L, ε, hε, ?_⟩
  intro c' hc'
  let y : Fin (L + 1) → ℝ := fun k =>
    if 2 ≤ k.val then c' k.val else uniformCumulants L k.val
  have hy : dist y (uniformCumulantPoint L) < ε := by
    rw [dist_pi_lt_iff hε]
    intro k
    by_cases hk : 2 ≤ k.val
    · simpa [y, uniformCumulantPoint, hk, Real.dist_eq] using hc' k.val hk (by omega)
    · simpa [y, uniformCumulantPoint, hk] using hε
  have hphiDist :
      dist (cumulantToWeights L y) (cumulantToWeights L (uniformCumulantPoint L)) < radius :=
    hcont hy
  have hp : ∀ i, 0 < cumulantToWeights L y i := by
    intro i
    have hi := (dist_pi_lt_iff hradius).mp hphiDist i
    rw [cumulantToWeights_uniformCumulantPoint L] at hi
    simp only [Real.dist_eq, uniformWeights, radius] at hi
    linarith [abs_lt.mp hi]
  have hpad : ∀ k, 2 ≤ k → k ≤ L → padCumulants L y k = c' k := by
    intro k hk hkL
    simp [padCumulants, y, hk, show k < L + 1 by omega]
  have hmom : ∀ k, k ≤ L →
      momFromCum (padCumulants L y) k = momFromCum c' k := by
    intro k hk
    apply momFromCum_congr
    intro j hj hjk
    exact hpad j hj (hjk.trans hk)
  have hsolve : ∀ k, k ≤ L →
      ∑ i, cumulantToWeights L y i * symmetricAtoms L i ^ k = momFromCum c' k := by
    intro k hk
    let kf : Fin (L + 1) := ⟨k, by omega⟩
    simpa [cumulantToWeights, kf, hmom k hk] using
      atomSolve_spec L (fun j => momFromCum (padCumulants L y) j.val) kf
  have hsum : ∑ i, cumulantToWeights L y i = 1 := by
    simpa using hsolve 0 (by omega)
  have hmean : ∑ i, cumulantToWeights L y i * symmetricAtoms L i = 0 := by
    simpa using hsolve 1 hLpos
  let ν := atomicLaw (L + 1) (symmetricAtoms L) (cumulantToWeights L y)
  have hpnonneg : ∀ i, 0 ≤ cumulantToWeights L y i := fun i => (hp i).le
  refine ⟨ν, isProbabilityMeasure_atomicLaw (symmetricAtoms_injective L) hpnonneg hsum,
    ?_, not_isGaussianLaw_atomicLaw (symmetricAtoms_injective L) hp (by omega),
    memLp_id_atomicLaw (symmetricAtoms_injective L) hpnonneg hsum (L : ℝ≥0∞), ?_⟩
  · simpa [ν] using
      (integral_atomicLaw (symmetricAtoms_injective L) hpnonneg id).trans hmean
  · intro r hr hrL
    rw [sourceCumulant_eq_cumFromMom]
    calc
      cumFromMom r (fun k => ∫ t, t ^ k ∂ν) =
          cumFromMom r (momFromCum c') := by
        apply cumFromMom_congr
        intro k hk hkR
        rw [integral_atomicLaw (symmetricAtoms_injective L) hpnonneg]
        exact hsolve k (hkR.trans hrL)
      _ = c' r := cumFromMom_momFromCum c' r hr

end Causalean.Stat.MomentProblems
