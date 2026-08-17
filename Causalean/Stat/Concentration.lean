import Causalean.Stat.Concentration.Chebyshev
import Causalean.Stat.Concentration.TailBounds
import Causalean.Stat.Concentration.Rademacher
import Causalean.Stat.Concentration.Covering
import Causalean.Stat.Concentration.UniformDeviation
import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal
import Causalean.Stat.Concentration.Matrix
import Causalean.Stat.Concentration.ConditionalKernel
import Causalean.Stat.Concentration.FiniteDimensionalNet
import Causalean.Stat.Concentration.SubGaussianNorm
import Causalean.Stat.Concentration.ProjectionMatrixTail
import Causalean.Stat.Concentration.ConditionalProjectionTail

/-!
# Concentration (top barrel)

Vendored concentration-of-measure library (a port of `auto-res/lean-rademacher`;
see `UPSTREAM.md`). Organized into topic subfolders, each with its own barrel:

* `TailBounds`      — Hoeffding, Bernstein / empirical Bernstein, McDiarmid, sub-exponential, Massart
* `Rademacher`      — Rademacher / local Rademacher complexity, symmetrization, contraction, star-hull
* `Covering`        — covering / packing numbers, Dudley entropy, VC covering and localized regime, √log integral
* `UniformDeviation`— localized uniform deviation, ERM oracle, critical radius, confidence intervals
* `VarianceAdaptiveVCExpectedMaximal` — countable-class VC-type expected suprema with an L² radius
* `Matrix`          — resolvent, inverse perturbation / union bound, design inverse, i.i.d. matrix sums
* `ConditionalKernel` — almost-everywhere bridges for regular conditional probability fibers
* `FiniteDimensionalNet` — dimension-explicit internal nets of bounded sets at an arbitrary scale
* `SubGaussianNorm` — norm tails assembled from scalar sub-Gaussian directions
* `ProjectionMatrixTail` — rank-sensitive tails for projected bounded noise
* `ConditionalProjectionTail` — conditional-fiber versions for measurable projectors
* `Chebyshev` — real-valued Chebyshev bound from a supplied variance envelope
-/
