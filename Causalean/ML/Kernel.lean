/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Kernel.RKHS
import Causalean.ML.Kernel.RKHSRademacher
import Causalean.ML.Kernel.Gram
import Causalean.ML.Kernel.Ridge
import Causalean.ML.Kernel.Rate
import Causalean.ML.Kernel.SquaredLoss
import Causalean.ML.Kernel.EffectiveDimension

/-! # `Causalean.ML.Kernel` — kernel methods

Roll-up: the abstract RKHS interface, kernel Gram matrices with regularized
positive definiteness, the kernel-ridge representer theorem, the Rademacher
complexity rate for the L²-ball linear class, and the genuine squared-loss
excess-risk rate for the L²-ball kernel ERM.
-/
