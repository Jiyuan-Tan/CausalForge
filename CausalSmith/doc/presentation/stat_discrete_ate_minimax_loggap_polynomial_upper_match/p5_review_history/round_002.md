# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The paper delivers a technically meaningful and carefully scoped sharp minimax result, with strong claim fidelity overall, but a few presentation and convention issues should be cleaned up before publication.

The submission studies ATE estimation with binary treatment/outcome and an unrestricted finite covariate alphabet, proving a fixed-interior minimax MSE rate of n^{-1}+d^2/(n^2 log^2 n) over the stated calibrated range. The main contribution is the computable heavy/light hybrid upper bound matching the imported lower-bound scale, plus clear parametric-rate and consistency implications. As written, the claims are mostly faithful to the verified statements and the scope limitations are unusually explicit; the remaining issues are mainly small-n conventions, a reference error, and appendix readability.

## Strengths
- The main theorem is significant for minimax causal inference under unrestricted discrete confounding and cleanly identifies the logarithmic improvement over naive large-alphabet behavior.
- The manuscript is careful about fixed-interior scope, the calibrated range d <= rho_epsilon n log n, and the separate endpoint epsilon=1/2 result.
- The distinction between the new computable upper bound and the imported Zeng et al. lower-bound ingredient is now mostly honest and useful.
- The estimator construction is explicit and the heavy/light statistical logic is coherent.
- The discussion positions the result well against semiparametric, doubly robust, higher-order, and large-alphabet functional-estimation literatures.

## Findings
- **[minor·statement] setup and assumptions / main results** — The small-sample conventions remain slightly under-specified. Definition 7 defines M(n) and B(n) only for n >= 2, then says that for n < N0 the ratio branch is used on every category; however Theorem 2 states computability for every n,d in N with operation count K d M(n)^4. If N includes 0 or if n=1 is allowed in that computability clause, M(n), log n, or m1-dependent quantities are not fully defined in the written presentation.
  - *Fix:* State explicitly whether N means positive integers throughout, or restrict the computability clause to n,d > 0. Define M(n) for n=1, and either exclude n=0 everywhere or give a complete zero-sample convention. Also make clear that the small-n ratio branch does not require the light-branch quantities B(n), M(n), or factorial-polynomial coefficients.
- **[minor·statement] main results** — The opening sentence of Theorem 2 says: "The following conclusions hold for the hybrid estimator \(\widehat\tau_n^{\mathrm{hyb}}\) and centered estimator \(\widehat\tau_{\mathrm{ctr}}\) of Definition~\ref{obj:def:hybrid-estimator-handle}". The centered estimator is not defined in the hybrid-estimator definition; it is introduced separately in Definition synth_5.
  - *Fix:* Change the theorem preamble to reference both definitions, e.g. "the hybrid estimator of Definition ... and the centered estimator of Definition ...".
- **[minor·structure] appendix** — The appendix proofs still mix statistical proof structure with verification-management comments, for example phrases such as "the formal verification records the routine empty-class and supremum-convention cases" and repeated implementation-level convention remarks. This is not mathematically wrong, but it makes the statistical argument harder to read as a journal appendix.
  - *Fix:* Move verification-boundary commentary to the verification note and streamline the proof text around the main statistical reductions: pilot sandwich, heavy ratio control, light polynomial approximation, truncation, lower-bound transfer, and endpoint comparison.
- **[nit·structure] global** — Some synthesized object labels such as "Definition synth_4" and "Definition synth_5" appear in prose and theorem references. They are serviceable for verification, but they look like artifact labels rather than journal-facing names.
  - *Fix:* Rename synthesized definitions with semantic labels, e.g. `def:centered-estimator`, `def:selected-estimator`, `def:balanced-split`, and use those labels consistently in cross-references.

## Questions for authors
- Can the authors state explicitly whether the convention throughout is n,d in positive integers except where zero-alphabet conventions are invoked?
- Are the constants N_epsilon and rho_epsilon intended only as proof-calibration constants, or is there any practical guidance on their magnitude for the hybrid estimator?

