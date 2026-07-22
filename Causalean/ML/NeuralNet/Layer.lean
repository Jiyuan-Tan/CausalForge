/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Neural-network layers

A dense (affine) layer `x ↦ W x + b` and an activation function carrying its
Lipschitz constant.  These are the building blocks composed in
`NeuralNet/FeedForward.lean`.
-/

namespace Causalean.ML

open Matrix

/-- A dense affine layer `x ↦ W x + b` from `Fin m` inputs to `Fin n` outputs. -/
structure DenseLayer (m n : ℕ) where
  /-- The weight matrix. -/
  W : Matrix (Fin n) (Fin m) ℝ
  /-- The bias vector. -/
  b : Fin n → ℝ

/-- The affine map computed by a dense layer. -/
def DenseLayer.eval {m n : ℕ} (L : DenseLayer m n) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun j => (L.W *ᵥ x) j + L.b j

/-- An activation function together with a Lipschitz constant and a proof it is
Lipschitz (e.g. ReLU, sigmoid, tanh are `1`-Lipschitz). -/
structure Activation where
  /-- The scalar activation. -/
  act : ℝ → ℝ
  /-- A Lipschitz constant for the activation. -/
  lip : NNReal
  /-- Proof that `act` is `lip`-Lipschitz. -/
  isLipschitz : LipschitzWith lip act

/-- Apply an activation coordinatewise to a vector. -/
def Activation.applyVec {n : ℕ} (σ : Activation) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => σ.act (x j)

end Causalean.ML
