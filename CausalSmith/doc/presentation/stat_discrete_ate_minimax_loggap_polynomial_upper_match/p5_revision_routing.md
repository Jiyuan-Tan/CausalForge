# Revision routing plan (minor_revision)

## escalate — out of causalsmith scope (bank/causalsmith)
- [minor·statement·rewrite] (setup and assumptions / main results) The small-sample conventions remain slightly under-specified. Definition 7 defines M(n) and B(n) only for n >= 2, then says that for n < N0 the ratio branch is used on every category; however Theorem 2 states computability for every n,d in N with operation count K d M(n)^4. If N includes 0 or if n=1 is allowed in that computability clause, M(n), log n, or m1-dependent quantities are not fully defined in the written presentation.
- [minor·statement·rewrite] (main results) The opening sentence of Theorem 2 says: "The following conclusions hold for the hybrid estimator \(\widehat\tau_n^{\mathrm{hyb}}\) and centered estimator \(\widehat\tau_{\mathrm{ctr}}\) of Definition~\ref{obj:def:hybrid-estimator-handle}". The centered estimator is not defined in the hybrid-estimator definition; it is introduced separately in Definition synth_5.

## holistic revision (local)
- [minor·structure·rewrite] (appendix) The appendix proofs still mix statistical proof structure with verification-management comments, for example phrases such as "the formal verification records the routine empty-class and supremum-convention cases" and repeated implementation-level convention remarks. This is not mathematically wrong, but it makes the statistical argument harder to read as a journal appendix.
- [nit·structure·rewrite] (global) Some synthesized object labels such as "Definition synth_4" and "Definition synth_5" appear in prose and theorem references. They are serviceable for verification, but they look like artifact labels rather than journal-facing names.

→ one holistic local pass; formal statements remain frozen
