# Revision routing plan (major_revision)

## rewind P1
- [major·structure·rewrite] (global) The manuscript is not yet written as a journal article. The setup contains many duplicated machine-synthesized definitions of the same primitive objects, especially the sampling law and expectation operator, and the appendix contains proof text with machine-facing comments. This makes the paper much harder to read than the underlying contribution requires.

## rewind P2
- [major·prose·rewrite] (intro) The scope of the primitive sign result is described inconsistently. The introduction says: "the closed-form \(\Phi\) characterization and nonemptiness of \(\mathcal R_T\) are established for the frontier \(\{2,3,4,\infty\}\), not for arbitrary cohort supports \(\mathcal C\)." But the verified theorem as stated gives the \(\beta^\star\)-\(\Phi\) sign equivalence for any support satisfying the theorem's horizon, support, rank, and frontier-scope assumptions, while the special closed form is for \(\{2,3,4,\infty\}\).
- [major·prose·rewrite] (discussion) Some empirical guidance goes beyond what is delivered. For example, "A useful workflow is to estimate or construct cohort-time proportional effects under the maintained identifying restrictions" reads like a supported estimation recommendation, but the paper provides neither an estimator for those granular effects nor inference or implementation guidance.
- [minor·prose·rewrite] (main results) The discussion after the four-cohort theorem blurs a local diagnostic and the global witness. The sentence "the largest effect is attached to the cell whose residual is negative" is only directly shown for the no-effect FWL residual table and a local neighborhood; the global negative coefficient of the witness is certified through region membership and the primitive sign calculation.
- [minor·prose·rewrite] (global) Notation is not yet stable enough for publication. Examples include switching between \(C\) and \(\mathcal C\), \(\beta_\star\) and \(\beta^\star\), \(\gamma_t\) and \(\gamma_{t0}\), and mixing period-1 prose with zero-indexed verification conventions.
- [nit·prose·rewrite] (abstract) The abstract is accurate in broad terms but too dense. It lists nearly every theorem and condition, which makes the contribution hard to parse for readers not already inside the formal development.

## escalate — out of causalsmith scope (bank/causalsmith)
- [major·structure·new_theorem] (setup) The paper defines the sample PPML coefficient \(\hat\beta_N\) and repeatedly motivates the object as the regression a practitioner would run, but it explicitly does not prove sampling consistency from \(\hat\beta_N\) to either \(\beta_N^\star\) or \(\beta^\star\). This leaves a gap between the empirical PPML coefficient and the population sign results.
- [minor·structure·rewrite] (appendix) The proof order is confusing: the proof of the four-cohort sign reversal invokes the primitive sign frontier before the primitive sign frontier is proved in the displayed appendix order.
- [minor·citation·citation_research] (related literature) The positioning is broadly reasonable but still too high-level about the closest proportional-PPML and nonlinear-DiD papers. The manuscript should make clearer what is not already implied by Moreau-Kastler-style proportional ATT targets or Wooldridge-style nonlinear DiD.

→ earliest rewind stage: `--from P1`
