## Done

- `Core.lean`: uniform allocation/joint/statistic masses, guarded conditional design, normalization, atomwise factorization, zero-fiber safety, and finite-sum disintegration.
- `Sufficiency.lean`: finite Fisher–Neyman factorization and derived state-independent common conditional kernel.
- `Posterior.lean`: finite-prior state–statistic joint law, guarded latent posterior, normalization, atomwise factorization, and posterior disintegration.
- `RaoBlackwell.lean`: conditional Jensen, statewise squared-risk contraction, finite-prior, worst-case, and minimax-compatible factorization-based results.
- `KernelBridge.lean`: Markov kernels, singleton-real identities, posterior kernel, and real `FiniteKernelBayes` sum bridges without `ENNReal` loss conversion.
- Ground truth verified: all five files elaborate directly; targeted `KernelBridge` build succeeds (2937 jobs); source scan finds zero `sorry`, `admit`, `native_decide`, custom axioms, or research-module imports.
- Axiom audit of the main disintegration, posterior, Jensen, statewise, prior, minimax, and kernel-bridge theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Library search confirmed reuse of `FiniteDesign`, `MinimaxValue`, `FiniteKernelBayes`, and Mathlib finite Jensen machinery; primary Rao (1945) and Blackwell (1947) sources were checked.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Represent fixed-size allocations by a generic nonempty admissible `Finset`; uniformity is imposed on that set.
- Use guarded Bayes ratios, with a fallback point mass for null full-data fibers and the original prior for null posterior fibers.
- Express sufficiency through `jointMass θ z = statisticFactor θ (T z) * carrierWeight z`, deriving a common conditional law by normalizing carrier weights.
- Keep the state-indexed conditional mean only as an analytic lemma; the public Rao–Blackwell estimator is one statistic-only function derived from sufficient factorization.
- Keep the substrate finite and real-valued, adding measure/kernel bridges only at the boundary needed by `Causalean.Stat.Minimax.FiniteKernelBayes`.