# Revision routing plan (major_revision)

## escalate — out of causalsmith scope (bank/causalsmith)
- [major·prose·rewrite] (appendix/proofs and minimax-risk definition) Several proof passages use a nonstandard supremum convention, for example: "If that family is not bounded above, the real-valued supremum is again 0." Under ordinary mathematical convention, an unbounded nonnegative family has supremum +infinity, and a reader cannot infer the Lean totalization convention from the minimax-risk definition.
- [minor·structure·rewrite] (setup and assumptions) The hybrid estimator definition is mathematically complete but difficult to implement from the main text because the coefficient construction is hidden inside the polynomial expansion and the sparse-arm coefficient formula appears later in the appendix.

## holistic revision (reframe)
- [minor·prose·rewrite] (related work and discussion) Some stand-alone summaries of the main result omit the calibrated range and large-sample conditions. For example, "The present paper constructs a computable balanced ratio-polynomial hybrid estimator that attains this lower scale in the fixed-interior overlap regime" should also carry the verified conditions n >= N_epsilon and d <= rho_epsilon n log n.
- [minor·prose·rewrite] (main results) The sentence "The operation count is polynomial in the degree M(n) and linear in the alphabet size d, so the construction is an explicit count-based procedure rather than an existential minimax rule" uses contribution-by-negation outside a limitations section.
- [nit·prose·rewrite] (abstract) The phrase "calibrated fixed-interior range" is accurate but opaque in a page-facing summary unless the reader recalls the preceding display and the epsilon-dependent constants.

## your call — orchestrator decides
- [minor·citation·rewrite] (related work) The comparison with Zeng et al. gives the main upper and lower rates, but it would be more useful to econometrics readers if it also summarized their same-sample equivalence of plug-in, IPW, and doubly robust estimators and the resulting consistency benchmark for those standard estimators.

→ one holistic reframe pass; formal statements remain frozen
