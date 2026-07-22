/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.NeuralNet.Layer
import Causalean.ML.NeuralNet.FeedForward

/-! # `Causalean.ML.NeuralNet` — feedforward networks

Roll-up for dense affine layers, activations carrying Lipschitz constants, and
uniform-width feedforward network evaluation.  The imported API includes
coordinatewise activation, layer-list evaluation, composition under layer-list
append, and a Lipschitz bound obtained by multiplying the per-layer constants.
-/
