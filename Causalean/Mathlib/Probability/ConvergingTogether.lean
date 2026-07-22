/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.ConvergingTogether.CharFunBound
import Causalean.Mathlib.Probability.ConvergingTogether.Diagonal

/-!
# Converging-together from `L²` approximation

This namespace collects the reusable pieces for the converging-together theorem.
`ConvergingTogether.CharFunBound` proves the pointwise and `L²` characteristic-function
approximation bounds (`norm_cexp_mul_I_sub_cexp_mul_I_le`,
`tendsto_charFun_sub_le`, and `tendsto_charFun_sub_le_L2`).  `ConvergingTogether.Diagonal`
uses those bounds in the Billingsley diagonal argument, proving
`tendsto_inDistribution_of_l2_approx` for a general weak limit law and the standard-normal
specialization `clt_of_l2_approx`.
-/
