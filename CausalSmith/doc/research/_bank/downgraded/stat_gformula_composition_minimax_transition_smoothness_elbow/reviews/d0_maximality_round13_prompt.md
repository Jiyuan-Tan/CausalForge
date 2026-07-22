You are the mandatory fresh whole-paper maximality auditor for CausalSmith D0. Read-only audit only: do not edit any file, do not spawn subagents, and do not rerun the pipeline. Work in /<repo-root>/CausalSmith.

Audit the complete current paper/artifact set for qid stat_gformula_composition_minimax, spec transition_smoothness_elbow. Read in full:

- doc/research/active/stat_gformula_composition_minimax/discovery/core.json
- doc/research/active/stat_gformula_composition_minimax/discovery/proto_core.json
- doc/research/active/stat_gformula_composition_minimax/discovery/d0_working.json
- doc/research/active/stat_gformula_composition_minimax/discovery/writeup.tex
- doc/research/active/stat_gformula_composition_minimax/discovery/d0_escalation_log.jsonl
- every file under doc/research/active/stat_gformula_composition_minimax/reviews/
- doc/research/active/stat_gformula_composition_minimax/pipeline.jsonl
- doc/research/active/stat_gformula_composition_minimax/orchestrator/decision_log.jsonl

This audit follows the new round-20 theorem-level structural-separation repair. Check the entire paper, not only the new proposition. In particular verify:

1. The fixed connected rough subclass M_rough is genuinely nonempty, n-independent, lies in the paper's current model, and contains the fuzzy alternatives for all sufficiently large n. Check every normalization, positivity, overlap, Holder-ball, transition-ball, outcome, and design-density condition.
2. The common rough base g0=1+kappa a q and rough perturbations are conditional densities. Check the analytic functions, zero-integral identities, the jump argument, and the claim that the induced joint density p1(h1)g(h2|h1) has no positive-order joint-Holder representative, so the same fixed subclass is not covered by Robins et al. Section 7.2.2 condition (c2)/Theorem 49. Check that the cited source leaf says no more than the primary theorem text supports.
3. Recompute the target separation and the full one-observation mixture affinity. Do not discard A1=0 observations: verify the full channels F_j=2 eta(2A1-1)u_j(H1) and E_j=epsilon 1{A1=1}u_j(H1)v(H2)/g0(H2|H1), their centered/mixed moments, L2 scales, the C n^2 eta^2 epsilon^2/J bound, and the resulting uniform n^{-r1} RMSE lower bound over the fixed rough subclass.
4. Check that the theorem-level comparison is precisely same-subclass noncoverage, not a broad class-inclusion, framework-exclusion, priority, or universal non-overlap claim. The public Robins theorem may be compared normally. The unavailable Bonvini-Kennedy-Keele work-in-progress policy is binding: disclose its public abstract only; infer no assumptions, rates, inclusion, non-overlap, or priority; unresolved overlap must remain explicit; a non-archival WIP with no public theorem text cannot alone trigger novelty failure.
5. Check all pre-existing mathematics: identification, both lower-bound channels, first-order upper bracket, correction-order staircase, internal HOIF diagnostics, and the explicit statements that the matched frontier and iff root-n elbow remain open. Ensure no attaining HOIF theorem or conjectured sharp rate has been promoted as proved.
6. Check graph/render synchronization: core and proto-core byte equality, every solved d0_working snapshot against canonical statement/proof/dependencies/definitions/assumptions, reverse dependency metadata, literal-backslash-n absence, cited-source metadata, and a clean two-pass LaTeX render.
7. Decide whether any truthful, finite, same-assumption, load-bearing improvement remains before a fresh independent D0.5 review. Do not request cosmetic edits, a mathematically weaker theorem, invented comparator facts, or closure of the openly unmatched minimax frontier. If there is a real bounded defect, identify exactly one minimal repair and all files it must touch.

Use gpt-5.6-sol reasoning at medium effort. Your final line must be exactly one of:

MAXIMAL: <one concise reason>

or

IMPROVE: <one concrete bounded repair>
