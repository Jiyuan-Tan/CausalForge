/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.NeuralNet.Layer

/-! # Feedforward networks (uniform width)

A uniform-width feedforward network is a list of dense layers evaluated
left-to-right with an activation after each affine map.  Structural facts: the
evaluation respects layer concatenation (composition), and the network is
Lipschitz with constant the product of the per-layer Lipschitz constants.
Universal approximation and training dynamics are out of scope.
-/

namespace Causalean.ML

open BigOperators

/-- One network layer: the affine map followed by coordinatewise activation. -/
def layerMap {n : ℕ} (σ : Activation) (L : DenseLayer n n) (x : Fin n → ℝ) : Fin n → ℝ :=
  σ.applyVec (L.eval x)

/-- Evaluate a uniform-width feedforward network (a list of layers), folding
left-to-right. -/
def evalLayers {n : ℕ} (σ : Activation) : List (DenseLayer n n) → (Fin n → ℝ) → (Fin n → ℝ)
  | [], x => x
  | L :: Ls, x => evalLayers σ Ls (layerMap σ L x)

/-- **Structure — composition.** Evaluating concatenated layer lists is the
composition of the two evaluations. -/
theorem evalLayers_append {n : ℕ} (σ : Activation) (Ls Ms : List (DenseLayer n n))
    (x : Fin n → ℝ) :
    evalLayers σ (Ls ++ Ms) x = evalLayers σ Ms (evalLayers σ Ls x) := by
  induction Ls generalizing x with
  | nil => rfl
  | cons L Ls ih => simp [evalLayers, ih]

/-- **Structure — Lipschitz.** If each layer map is `k L`-Lipschitz, the network
is Lipschitz with constant the product of the per-layer constants. -/
theorem evalLayers_lipschitz {n : ℕ} (σ : Activation) (Ls : List (DenseLayer n n))
    (k : DenseLayer n n → NNReal)
    (hk : ∀ L ∈ Ls, LipschitzWith (k L) (layerMap σ L)) :
    LipschitzWith (Ls.map k).prod (evalLayers σ Ls) := by
  induction Ls with
  | nil =>
      simpa [evalLayers] using
        (LipschitzWith.id :
          LipschitzWith (1 : NNReal) (id : (Fin n → ℝ) → (Fin n → ℝ)))
  | cons L Ls ih =>
      have hL : LipschitzWith (k L) (layerMap σ L) := hk L (by simp)
      have hLs : ∀ L' ∈ Ls, LipschitzWith (k L') (layerMap σ L') := by
        intro L' hL'
        exact hk L' (by simp [hL'])
      simpa [evalLayers, List.map_cons, List.prod_cons, mul_comm] using (ih hLs).comp hL

end Causalean.ML
