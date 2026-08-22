# exp_snipe_degree_frontier / v1 — P5 findings left unresolved at the cap (2026-08-21)

Final referee round: `major_revision`, score 7 (`p5_review_history/round_006.json`).

## Score history — the automatic passes regressed the paper

Round 003 returned `minor_revision`, score 8. Round 006, after two further automatic
holistic revision passes, returned `major_revision`, score 7. The later passes introduced
prose the referee liked less while the paper's *correctness* improved over the same span
(the mangled edge relation, the undefined perturbation notation, and the missing setup
definitions were all fixed between those rounds). Treat round 006's score as a comment on
the current prose, not as evidence that the paper got worse overall — but the regression is
real and a future run should consider stopping at the first `minor_revision`.

## Unresolved — out of per-paper scope

- **Stale author footnote.** "results cited from the literature enter as published inputs"
  is misleading for this paper, whose verification contract records NO cited dependencies.
  The string is hardcoded in `tools/src/presentation/stages/p2_draft.ts` and is shared by
  every bundle, so correcting it is a pipeline change (and would need the usual independent
  audit), not a per-paper edit.
- **Merge the two frontier theorems.** The P3 rubric and the referee both suggest stating one
  frontier theorem covering both classes and demoting the binomial form to a corollary,
  since `thm:degree-frontier` is proved entirely from `thm:bounded-outcome-degree-frontier`.
  Theorem restructuring and new corollaries are user-scope.

## Unresolved — prose, deferred

- Abstract opening reads as broader than the fixed-`(β,p)`, fixed-`p`, known-graph setting;
  first use of SNIPE is unglossed.
- The related-work comparison to Cortez-Rodriguez, Eichhorn and Yu is still judged
  underdeveloped, though it now states their variance bound and names which component is a
  re-derivation.
- "The global upper bound therefore has the same degree dependence as the sharp
  complete-block calculation" risks implying the complete-block constant transfers globally.
- The SNIPE score is defined with `\bar\beta_d` even when a unit has `|N_i| < d`, leaving the
  inner subset sum empty for orders above `|N_i|`; harmless but worth a word.
- The verification note says the checked statements include "unbiasedness and variance
  identities" while the theorems state worst-case bounds.
- Main results lead with long formal statements before a compact orientation.

## Resolved during this run (for the record)

Undefined `Y_i(z)`, `τ_n`, `V_n`, `N_i`, `G_n`, `P_Z`, `E_Z`, `Δ_r(p)`, `A_i`, `Π_±`, `H²`,
`𝔼_D`, `D`, `D_t`; the `Gji` garble; the undefined `tilt` notation; a title promising an
estimand its body did not define; formalization vocabulary ("world") in reader-facing prose;
the missing roadmap; the deterministic-outcome concession; the degree-growth regime; and the
"Discussion of the assumptions" subsection.
