/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.UStatistic.Basic
import Causalean.Stat.UStatistic.Hajek
import Causalean.Stat.UStatistic.Variance
import Causalean.Stat.UStatistic.OrderM.Basic
import Causalean.Stat.UStatistic.OrderM.Hajek
import Causalean.Stat.UStatistic.OrderM.Variance
import Causalean.Stat.UStatistic.OrderM.ExactVariance
import Causalean.Stat.UStatistic.OrderM.FirstDegenKernel
import Causalean.Stat.UStatistic.OrderM.RemainderSecondMoment
import Causalean.Stat.UStatistic.OrderM.RemainderNegligible
import Causalean.Stat.UStatistic.OrderM.CLT
import Causalean.Stat.UStatistic.OrderM.OrderTwo

/-!
# U-statistics

Collects the U-statistic library: order-2 Hoeffding and variance tools, fixed-order `m`
infrastructure, Hájek expansions, remainder negligibility, and the fixed-order CLT.

This barrel collects the U-statistic substrate: the original order-2
Hoeffding-decomposition and variance theory, plus the fixed-order `m` interface
for ordered injective tuples and its Hájek expansion.  The headline is the
fixed-order U-statistic central limit theorem `OrderM.CLT`
(`uStatisticOrder_clt_of_regular`); its higher-order remainder negligibility is
discharged through `OrderM.FirstDegenKernel`, `OrderM.RemainderSecondMoment`, and
`OrderM.RemainderNegligible`.
-/
