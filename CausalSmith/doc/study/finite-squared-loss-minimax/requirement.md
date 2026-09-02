# Substrate requirement: finite-squared-loss-minimax

## Goal
Prove existence of both an attaining minimax randomized procedure and an attaining least-favorable finite prior for a finite-state, finite-design decision problem with dependent finite observation spaces, bounded real actions, nonnegative likelihood weights, and squared loss.

## Provides (API contract)
- `finite_bounded_squared_loss_has_saddle`: for finite nonempty state and design types `Theta` and `R`, dependent finite observation types `X r`, real bounds `l <= u`, nonnegative coefficients `P theta r x`, and real targets `tau theta`, produce a randomized design, bounded decision rule, and finite prior satisfying both saddle inequalities at the Causalean minimax value.
- Supporting general lemmas may expose compactness, continuity, convexity/Jensen, primal attainment, dual attainment, or risk-vector separation results when they are independently reusable and are necessary for the main theorem.

## Statement / milestones
Let procedures be pairs consisting of `q : Causalean.Experimentation.DesignBased.FiniteDesign R` and a dependent decision rule `delta : forall r, X r -> Set.Icc l u`. Define

`risk (q, delta) theta = sum r, q.p r * sum x, P theta r x * (delta r x - tau theta)^2`.

Assume:
- `Theta` and `R` are finite and nonempty;
- every `X r` is finite (and any nonemptiness genuinely needed by the construction is stated explicitly);
- `l <= u`;
- `0 <= P theta r x` for every index;
- any normalization of `P` needed for conditional Jensen is stated explicitly and no stronger than necessary;
- targets lie in the action interval if this is required for clipping/Jensen recovery.

Prove that there exist a procedure `qstar` and `nu : Causalean.Experimentation.DesignBased.FiniteDesign Theta` such that

- `forall theta, risk qstar theta <= Causalean.Stat.minimaxValue risk`, and
- `forall qprime, Causalean.Stat.minimaxValue risk <= nu.E (risk qprime)`.

The dependency closure must establish the required compactness/continuity and convexification facts, Sion or finite-dimensional separation equality, and both primal and dual attainment. The exported theorem must use the existing `FiniteDesign` and `minimaxValue` APIs rather than introducing incompatible duplicates.

## Standard reference
This is the finite decision-problem specialization of the von Neumann/Sion minimax theorem with compact convex randomized procedures and a finite simplex of priors; the squared-loss mixing step is conditional Jensen convexity. Relevant standard sources are Sion, *On general minimax theorems* (1958), and standard statistical decision theory treatments of least-favorable priors and minimax rules.

## Intended reuse
The immediate consumer is a finite orbit experiment whose design space is an allocation simplex, observations depend on the selected allocation, actions are clipped real estimators, states are response-count vectors, likelihood coefficients are exact orbit likelihoods, and targets are finite-population contrasts. The theorem must remain paper-agnostic and reusable by other finite statistical decision problems.

## May assume / must derive
May assume only the explicit finiteness/nonemptiness, interval, coefficient nonnegativity/normalization, and target-bound hypotheses in the generic theorem.

Must derive:
- compactness and convexity of the randomized-procedure space used in the proof;
- continuity of each statewise risk;
- the exact conditional mixing/Jensen inequality needed to recover a procedure from a convexified risk vector;
- primal minimax attainment;
- minimax equality or the equivalent separating risk-vector statement;
- least-favorable-prior attainment and the two saddle inequalities;
- bridges to the existing Causalean `FiniteDesign.E` and `Causalean.Stat.minimaxValue` definitions.

All delivered declarations must be axiom-clean apart from standard Lean foundations and contain no `sorry`, `admit`, or `native_decide`.

## Non-goals
- Do not formalize the multi-arm paper theorem, orbit likelihood, response-count combinatorics, or any paper-specific type.
- Do not import any `CausalSmith/*_Research` module in reusable substrate.
- Do not create a second incompatible finite-design or minimax-value abstraction.
- Do not prove general infinite-dimensional statistical decision theory beyond what the finite bounded squared-loss theorem needs.

## Known building blocks
- `Causalean.Experimentation.DesignBased.DesignCore`
- `Causalean.Stat.Minimax.MinimaxValue`
- `Mathlib.Topology.Sion`
- `Mathlib.Analysis.Convex.StdSimplex`
- `Mathlib.Analysis.Convex.Topology`
- `Mathlib.Analysis.Normed.Module.Convex`
- `Mathlib.Order.SaddlePoint` for packaging/characterization only
- Mathlib's probability decision-risk API currently does not supply the required maximal-Bayes/minimax equality.
