/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.MomentCumulantInversion
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Solving for atom weights that match a prescribed cumulant target

Fix `L + 1` equally spaced atoms placed symmetrically about the origin.  Matching the raw moments
of orders `0, 1, …, L` of a weight vector supported on those atoms to a prescribed moment target is
a square linear system whose matrix is a transposed Vandermonde matrix in the atom locations.  The
atoms being distinct, that matrix is invertible, so the weights are recovered from the moment
target by a linear — in particular continuous — solve.

Composing this solve with the triangular moment↔cumulant inversion gives the map this module
exports: **prescribed truncated cumulants ↦ atom weights**, which is continuous, and which sends
the cumulants of the uniform-weight law back to the uniform weights.  That is exactly what is
needed to conclude, by openness of the strict-positivity constraint, that a whole neighborhood of
cumulant targets is matched by genuine (positive-weight) probability laws.

Nothing here yet asserts positivity of the solved weights: it is a pure linear-algebra and
continuity layer.  The realizability conclusion is drawn in `TruncatedCumulantInterior`.
-/

namespace Causalean.Stat.MomentProblems

open scoped BigOperators

/-- The `L + 1` **equally spaced symmetric atoms** `−L, −L + 2, …, L − 2, L`: the `i`-th atom sits
at twice `i` minus `L`.  They are symmetric about the origin and pairwise distinct. -/
noncomputable def symmetricAtoms (L : ℕ) : Fin (L + 1) → ℝ :=
  fun i => 2 * (i.val : ℝ) - (L : ℝ)

/-- The symmetric atoms are pairwise distinct. -/
theorem symmetricAtoms_injective (L : ℕ) : Function.Injective (symmetricAtoms L) := by
  intro i j hij
  apply Fin.ext
  dsimp [symmetricAtoms] at hij
  have : (i.val : ℝ) = j.val := by linarith
  exact_mod_cast this

/-- The symmetric atoms sum to zero — they are balanced about the origin. -/
theorem symmetricAtoms_sum (L : ℕ) : ∑ i : Fin (L + 1), symmetricAtoms L i = 0 := by
  change ∑ i : Fin (L + 1), (2 * (i.val : ℝ) - (L : ℝ)) = 0
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 * (i : ℝ) - (L : ℝ))]
  have hs : (∑ i ∈ Finset.range (L + 1), (i : ℝ)) * 2 =
      (L + 1 : ℝ) * L := by
    have hn : (∑ i ∈ Finset.range (L + 1), i) * 2 = (L + 1) * L := by
      simpa using Finset.sum_range_id_mul_two (L + 1)
    have hr := congrArg (fun n : ℕ => (n : ℝ)) hn
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_add,
      Nat.cast_one] using hr
  calc
    ∑ i ∈ Finset.range (L + 1), (2 * (i : ℝ) - (L : ℝ)) =
        2 * (∑ i ∈ Finset.range (L + 1), (i : ℝ)) - (L + 1 : ℝ) * L := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.mul_sum]
    _ = 0 := by linarith

/-- The **uniform weight vector** on the `L + 1` atoms: each atom carries mass `1 / (L + 1)`. -/
noncomputable def uniformWeights (L : ℕ) : Fin (L + 1) → ℝ :=
  fun _ => 1 / (L + 1 : ℝ)

/-- Every uniform weight is strictly positive. -/
theorem uniformWeights_pos (L : ℕ) : ∀ i, 0 < uniformWeights L i := by
  intro i
  dsimp [uniformWeights]
  positivity

/-- The uniform weights sum to one, so the uniform-weight atomic law is a probability law. -/
theorem uniformWeights_sum (L : ℕ) : ∑ i, uniformWeights L i = 1 := by
  simp [uniformWeights]
  field_simp

/-- The uniform-weight law on the symmetric atoms has mean zero. -/
theorem uniformWeights_mean (L : ℕ) :
    ∑ i, uniformWeights L i * symmetricAtoms L i = 0 := by
  change ∑ i, (1 / (L + 1 : ℝ)) * symmetricAtoms L i = 0
  rw [← Finset.mul_sum]
  exact mul_eq_zero_of_right _ (symmetricAtoms_sum L)

/-- The raw-moment sequence of the uniform-weight law on the symmetric atoms. -/
noncomputable def uniformMoments (L : ℕ) : ℕ → ℝ :=
  fun k => ∑ i, uniformWeights L i * symmetricAtoms L i ^ k

/-- The uniform-weight law has total mass one. -/
theorem uniformMoments_zero (L : ℕ) : uniformMoments L 0 = 1 := by
  simpa [uniformMoments] using uniformWeights_sum L

/-- The uniform-weight law is centered. -/
theorem uniformMoments_one (L : ℕ) : uniformMoments L 1 = 0 := by
  simpa [uniformMoments] using uniformWeights_mean L

/-- The cumulant sequence of the uniform-weight law on the symmetric atoms — the base point around
which the truncated cumulant range is shown to have interior. -/
noncomputable def uniformCumulants (L : ℕ) : ℕ → ℝ :=
  fun r => cumFromMom r (uniformMoments L)

/-- Inverting the cumulants of the uniform-weight law returns its moments: the base point is a
fixed point of the moment↔cumulant round trip. -/
theorem momFromCum_uniformCumulants (L k : ℕ) :
    momFromCum (uniformCumulants L) k = uniformMoments L k := by
  apply momFromCum_eq_of_cum (uniformMoments L) (uniformMoments_zero L) (uniformMoments_one L)
  intro r hr
  rfl

/-! ### The Vandermonde solve -/

/-- The Vandermonde matrix of the symmetric atoms: row `i` lists the powers of the `i`-th atom. -/
noncomputable def atomVandermonde (L : ℕ) :
    Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  Matrix.vandermonde (symmetricAtoms L)

/-- The transposed Vandermonde matrix of the symmetric atoms is invertible, because the atoms are
pairwise distinct. -/
theorem atomVandermonde_transpose_isUnit (L : ℕ) :
    IsUnit (atomVandermonde L).transpose.det := by
  rw [Matrix.det_transpose, isUnit_iff_ne_zero]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (symmetricAtoms_injective L)

/-- The **weight vector solving the moment-matching system**: given a target for the raw moments of
orders `0` through `L`, the unique weights on the symmetric atoms reproducing them. -/
noncomputable def atomSolve (L : ℕ) (b : Fin (L + 1) → ℝ) :
    Fin (L + 1) → ℝ :=
  (atomVandermonde L).transpose⁻¹.mulVec b

/-- The solved weights do reproduce the target: the weighted sum of the `k`-th powers of the atoms
is the `k`-th target moment, for every order `k` from `0` to `L`. -/
theorem atomSolve_spec (L : ℕ) (b : Fin (L + 1) → ℝ) (k : Fin (L + 1)) :
    ∑ i, atomSolve L b i * symmetricAtoms L i ^ (k : ℕ) = b k := by
  have h := congrFun (Matrix.mulVec_mulVec b (atomVandermonde L).transpose
    (atomVandermonde L).transpose⁻¹) k
  rw [Matrix.mul_nonsing_inv _ (atomVandermonde_transpose_isUnit L), Matrix.one_mulVec] at h
  calc
    ∑ i, atomSolve L b i * symmetricAtoms L i ^ (k : ℕ) =
        ∑ i, symmetricAtoms L i ^ (k : ℕ) * atomSolve L b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_comm]
    _ = ((atomVandermonde L).transpose.mulVec (atomSolve L b)) k := by
      simp [atomVandermonde, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    _ = b k := by simpa [atomSolve] using h

/-- The solve is a left inverse of taking moments: solving for the weights from the moments that a
given weight vector produces returns that same weight vector. -/
theorem atomSolve_mulVec (L : ℕ) (q : Fin (L + 1) → ℝ) :
    atomSolve L ((atomVandermonde L).transpose.mulVec q) = q := by
  funext k
  have h := congrFun (Matrix.mulVec_mulVec q (atomVandermonde L).transpose⁻¹
    (atomVandermonde L).transpose) k
  rw [Matrix.nonsing_inv_mul _ (atomVandermonde_transpose_isUnit L), Matrix.one_mulVec] at h
  exact h

/-- Solving at the moments of the uniform-weight law returns the uniform weights. -/
theorem atomSolve_uniformMoments (L : ℕ) :
    atomSolve L (fun k => uniformMoments L k.val) = uniformWeights L := by
  rw [← atomSolve_mulVec L (uniformWeights L)]
  congr 1
  funext k
  simp [atomVandermonde, uniformMoments, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
    mul_comm]

/-- The moment-matching solve depends continuously on the target moments — it is linear. -/
theorem continuous_atomSolve (L : ℕ) : Continuous (atomSolve L) := by
  apply continuous_pi
  intro i
  unfold atomSolve Matrix.mulVec dotProduct
  apply continuous_finset_sum
  intro j hj
  exact continuous_const.mul (continuous_apply j)

/-! ### Cumulant target ↦ atom weights -/

/-- Extending a finite cumulant target of orders `0, …, L` to a full sequence by zeros beyond
order `L`. -/
noncomputable def padCumulants (L : ℕ) (y : Fin (L + 1) → ℝ) : ℕ → ℝ :=
  fun k => if h : k < L + 1 then y ⟨k, h⟩ else 0

/-- Zero-extension of a finite cumulant target is continuous in the target. -/
theorem continuous_padCumulants (L : ℕ) : Continuous (padCumulants L) := by
  apply continuous_pi
  intro k
  by_cases h : k < L + 1
  · simpa [padCumulants, h] using (continuous_apply (⟨k, h⟩ : Fin (L + 1)))
  · simpa [padCumulants, h] using
      (continuous_const : Continuous (fun _ : Fin (L + 1) → ℝ => (0 : ℝ)))

/-- The **cumulant-to-weights map**: from a prescribed truncated cumulant target, invert the
triangular moment↔cumulant relation to get the target moments, then solve the Vandermonde system
for the weights on the symmetric atoms. -/
noncomputable def cumulantToWeights (L : ℕ) (y : Fin (L + 1) → ℝ) :
    Fin (L + 1) → ℝ :=
  atomSolve L (fun k => momFromCum (padCumulants L y) k.val)

/-- The cumulant-to-weights map is continuous: both the moment↔cumulant inversion and the
Vandermonde solve are. -/
theorem continuous_cumulantToWeights (L : ℕ) : Continuous (cumulantToWeights L) := by
  apply (continuous_atomSolve L).comp
  apply continuous_pi
  intro k
  exact (continuous_momFromCum k.val).comp (continuous_padCumulants L)

/-- The **base cumulant target**: the cumulants, of orders `0` through `L`, of the uniform-weight
law on the symmetric atoms. -/
noncomputable def uniformCumulantPoint (L : ℕ) : Fin (L + 1) → ℝ :=
  fun k => uniformCumulants L k.val

/-- Inverting the base cumulant target order by order returns the moments of the uniform-weight
law. -/
theorem momFromCum_padCumulants_uniform (L : ℕ) (k : Fin (L + 1)) :
    momFromCum (padCumulants L (uniformCumulantPoint L)) k.val = uniformMoments L k.val := by
  rw [← momFromCum_uniformCumulants L k.val]
  apply momFromCum_congr
  intro j hj hjk
  simp [padCumulants, uniformCumulantPoint, show j < L + 1 by omega]

/-- **The base point maps to the uniform weights.** Feeding the cumulants of the uniform-weight law
into the cumulant-to-weights map returns the uniform weights — all strictly positive, hence
strictly inside the positivity constraints. -/
theorem cumulantToWeights_uniformCumulantPoint (L : ℕ) :
    cumulantToWeights L (uniformCumulantPoint L) = uniformWeights L := by
  calc
    cumulantToWeights L (uniformCumulantPoint L) =
        atomSolve L (fun k =>
          momFromCum (padCumulants L (uniformCumulantPoint L)) k.val) := rfl
    _ = atomSolve L (fun k => uniformMoments L k.val) := by
      congr 1
      funext k
      exact momFromCum_padCumulants_uniform L k
    _ = uniformWeights L := atomSolve_uniformMoments L

end Causalean.Stat.MomentProblems
