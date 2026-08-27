# Revision routing plan (major_revision)

## holistic revision (reframe)
- [major·structure·rewrite] (global) The main contribution is hard to evaluate because the manuscript presents many redundant restricted/all-alphabet theorem variants and lengthy proof machinery before the reader has a compact statistical picture of the result.
- [major·prose·rewrite] (intro) Several high-level passages risk blurring the distinction between the delivered minimax bracket and exact minimax rates. For example, "The bracket has sharp implications across the named regimes" is accurate only when read with the matched-regime clauses and residual shrinking-radius wedge.
- [major·structure·rewrite] (related work) The closest-comparison discussion is useful but too long and partly proof-attribution focused; it does not yet isolate in one concise place exactly which rate, model, and estimator differences constitute the publishable econometric contribution.
- [minor·prose·rewrite] (setup and assumptions) The notation for lower benchmarks is needlessly fragile: the text uses \(\ell_{n,d,\sigma}\) for the capped converse benchmark in one place and then says the same symbol is local to the regime theorem for the triangular product benchmark.
- [minor·prose·rewrite] (abstract) The first display uses \(\mathcal P_{d,\epsilon,M,\sigma}\) before the symbol has a plain-word appositive.
- [nit·prose·rewrite] (intro) The theorem map says "Four results carry the paper" and then lists the upper bound, lower bound, bracket, regime theorem, and endpoint proposition.

## escalate — out of causalsmith scope (bank/causalsmith)
- [major·structure·implementation] (estimators and upper bounds) The constructed estimators are mathematically explicit, but the paper gives no compact implementation-level pseudocode or minimal reproducibility artifact for the known-radius selector beyond dense formulas and an operation-count discussion.
- [minor·citation·citation_research] (related work) The manuscript cites the nearest competitor as 2024, while the related-work brief identifies Zeng--Balakrishnan--Han--Kennedy as revised in 2026.
- [minor·structure·rewrite] (related work) Reader-facing prose contains unexplained formal-reference artifacts such as "\leanref{S-1}{real-outcome observational experiment with a finite discrete confounder}" and "\leanref{S-2}{binary-outcome discrete-confounder experiment}".

→ one holistic reframe pass; formal statements remain frozen
