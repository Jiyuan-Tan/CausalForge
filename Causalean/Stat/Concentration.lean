import Causalean.Stat.Concentration.TailBounds
import Causalean.Stat.Concentration.Rademacher
import Causalean.Stat.Concentration.Covering
import Causalean.Stat.Concentration.UniformDeviation
import Causalean.Stat.Concentration.Matrix

/-!
# Concentration (top barrel)

Vendored concentration-of-measure library (a port of `auto-res/lean-rademacher`;
see `UPSTREAM.md`). Organized into topic subfolders, each with its own barrel:

* `TailBounds`      — Hoeffding, Bernstein / empirical Bernstein, McDiarmid, sub-exponential, Massart
* `Rademacher`      — Rademacher / local Rademacher complexity, symmetrization, contraction, star-hull
* `Covering`        — covering / packing numbers, Dudley entropy, VC covering and localized regime, √log integral
* `UniformDeviation`— localized uniform deviation, ERM oracle, critical radius, confidence intervals
* `Matrix`          — resolvent, inverse perturbation / union bound, design inverse, i.i.d. matrix sums
-/
