/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.UnknownInterference.Basic
import Causalean.Experimentation.UnknownInterference.Bernoulli
import Causalean.Experimentation.UnknownInterference.Unbiased
import Causalean.Experimentation.UnknownInterference.VarianceBound
import Causalean.Experimentation.UnknownInterference.Consistency
import Causalean.Experimentation.UnknownInterference.Hajek
import Causalean.Experimentation.UnknownInterference.Confidence

/-!
# Sävje–Aronow–Hudgens (2021) — average treatment effects under unknown interference

Formalization of the Bernoulli-design core of Sävje, Aronow & Hudgens (2021), "Average treatment
effects in the presence of unknown interference," *Annals of Statistics* 49(2):673–701
(arXiv:1711.06399).

* `Basic` — the EATE estimand (assignment-conditional ATE marginalized over the design), the
  interference structure (`Interferes`, `InterfDep`, average interference dependence `dbar`), the
  Horvitz–Thompson estimator, and the structural fact that a unit's outcome depends only on its
  interferers.
* `Bernoulli` — the Bernoulli design as a product of per-unit coin flips, with its marginals.
* `Unbiased` — HT is exactly unbiased for EATE under the Bernoulli design (`Z_i ⊥ Z_{-i}`).
* `VarianceBound` — `Var(ĤT) ≤ k⁴·d̄/n`, via disjoint-block independence off the
  interference-dependence graph and bounded summands.
* `Consistency` — the flagship: HT is consistent for EATE under restricted interference
  (`d̄ = o(n)`) via Chebyshev, with root-n consistency under bounded interference.
* `Hajek` — the Hájek (ratio/IPW) estimator is also consistent for EATE, via the in-probability
  Slutsky substrate (`DesignBased/InProb.lean`): the realized weight-sum normalizers tend to one.
* `Confidence` — the conventional HT variance estimator is anti-conservative under interference
  (exact bias identity); inflating it by an interference-degree measure is conservative (in
  expectation); and a Chebyshev interval with the proven variance bound gives a finite-sample valid
  confidence interval for EATE (the paper proves a CLT fails, so Chebyshev is the right tool).

Scope: the Bernoulli design with the Horvitz–Thompson and Hájek estimators + confidence statements
(the paper's conceptual core). Complete/paired/arbitrary designs (α-mixing), the variance-estimator
asymptotic-conservativeness *in probability*, and external validity are out of scope for this pass —
see `doc/savje_aronow_hudgens_plan.md`.
-/
