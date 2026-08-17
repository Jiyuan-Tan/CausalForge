---
qid: stat_cot_observational_efficiency
spec: v1
topic: "Semiparametric efficiency and cross-fitted one-step inference for the smooth quadratic conditional-optimal-transport lower bound on mean squared individual treatment effects in observational studies: extend Lin-Gao-Blanchet-Glynn (arXiv:2602.20681, Proposition 3.3 and Theorem 3.2) from randomized marginal-sample asymptotic normality to i.i.d. observational data under ignorability and overlap by deriving the observed-data canonical gradient, efficiency bound, propensity-corrected wavelet-Brenier one-step estimator, uniform studentized normality and Wald coverage, with Ji-Lei-Spector's 401(k) SIPP analysis as the applied consumer"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Stage 0.5.G reviewer, verbatim (reviews/review_general.json):
  - "The degeneracy theorem proves only that one unregularized full-tangent Gaussian spectral construction fails at an admissible identity-compression witness, while honest full-parent adaptation remains open."
  - "The framing overclaims necessity when it says covariate regularization, a uniform Hilbert-Schmidt tail, and uniform estimation of the regularized Hessian are all necessary: the proofs establish the generic Gaussian-series criterion and failure of the unregularized route, not a necessity theorem covering every regularized spectral calibration."
  - "The claimed phase boundaries are sufficient for the chosen finite-net/DML construction and have no converse, as the note ultimately acknowledges."
  # Independent referee re-grade, 2026-08-05 (not from the pipeline chain):
  - "The headline theorem is the one-step correction that the run's own closest comparator names as its future work. Lin-Gao-Blanchet-Glynn arXiv:2602.20681 — cited here as lin2026statistical — already contains, for the SAME conditional estimand: Prop 3.3 (the signed one-sided second-order remainder, = lem:two-sample-quadratic-remainder), Thm 3.2 (root-n normality with centered conditional Kantorovich potentials under 2s > d_Y + d_Z, = this note's influence function and its s > D/2 condition verbatim), and Remark 3.2 (the equality-degeneracy case). What they lack is the propensity score and the word 'efficient'; the note supplies exactly those two."
  - "The companion paper arXiv:2502.01164 (cited as lin2025tightening) states in its own future work: 'A potential approach is using the one-step correction estimator from the semi-parametric literature.'"
  - "The efficiency half is Manole et al. AoS 2024 composed one step: their Lemma 21 gives the centered Kantorovich potential as the efficient influence function of W_2^2, their Thm 22 gives matching one- and two-sample LAM lower bounds. The run itself quotes both verbatim in core.json as lem:manole-unconditional-smooth-wasserstein-efficiency."
  - "Presentation inverts the content: def:conditional-transport-pathwise-differentiability POSITS the derivative formula as a property D(P), and thm:abstract-observed-canonical-gradient then proves the headline in eight lines of centering algebra given D. The real work — deriving D by an envelope/Danskin argument — sits in lem:integrated-arm-path-differentiation, a lemma."
  - "ass:uniform-conditional-brenier-{smoothness,lower,upper} are labelled 'Standard (uniform A1-type, manole2024plugin)' but Manole's A1 is a per-pair POPULATION hypothesis; quantifying it over an entire nonparametric class is what makes the stability lemma uniform, and every rate in the note rides on that. Worse, the condition involves no P at all yet is listed as a member property of the parent law class, so if it fails the class is empty and every theorem is vacuous. Non-vacuity is never established for d_Y >= 2."
  - "The spectral obstruction is generic, not transport-specific: in lem:conditional-hessian-spectral-obstruction the perturbation is a product e(x)g(y) with g FIXED, giving a constant ratio for every e. It is the statement that a fibrewise quadratic form averaged over a nonatomic covariate law has an eigenvalue of infinite multiplicity, and would hold identically for a plain squared-difference functional. Nothing about Brenier potentials is used."
  - "Uncited comparator: Agarwal-Luedtke, 'Sinkhorn Treatment Effects', arXiv:2605.08485 (May 2026) — first-order EIF of the form (centered entropic dual potential)/propensity, debiased estimators, and at equality a proof that the first-order EIF vanishes with a weighted chi-square second-order limit. That is the structure of both the efficiency claim and the degeneracy analysis, published two months before this run."
  - "The proposal-stage gate recorded published_axis_verdict 'clear' with papers_verified 8, and state.json shows 'field' asserted at iterations 0-6 without ever being re-tested against delivered content."
reusable_artifacts:
  - path: discovery/writeup.tex
    kind: operator
    one_line: "lem:integrated-arm-path-differentiation (lines 716-736) — a correct envelope/Danskin derivation of the pathwise derivative of the conditional transport functional from the per-arm potential. This is the one place in the note where the derivative is DERIVED rather than posited, and it is the piece worth lifting."
  - path: discovery/solve_oeq_degeneracy_adaptive_inference.json
    kind: other
    one_line: "The run's single open-ended question — inference at and through the degenerate boundary where the two arms' conditional laws coincide. Zero proofs, one open obligation. This is the real result the topic was reaching for; see Re-anchor path."
  - path: discovery/core.json
    kind: literature_map
    one_line: "Comparator attestations including the verbatim Manole Lemma 21 / Thm 22 quotes and the Lin et al. entries; note that the same attestations are what refute the novelty claim, so read them before proposing anything adjacent."
  - path: discovery/withheld_content.json
    kind: other
    one_line: "Content withheld from the delivered note across solve rounds."
seeds_burned: []
proof_attempt_summary: |
  Aimed at the semiparametric efficiency bound and honest inference for the
  optimal-transport lower bound on the average squared individual treatment
  effect, in an OBSERVATIONAL design. What was delivered is the influence
  function (a covariate term plus the centered conditional Kantorovich dual
  potential over the propensity), a cross-fitted debiased estimator attaining it,
  and Wald validity including along sequences with vanishing variance — which is
  the published randomized-design theory of Lin-Gao-Blanchet-Glynn composed with
  Manole et al.'s unconditional efficiency result and a propensity correction,
  i.e. exactly the one-step correction the cited literature names as its own
  future work. The single open question, inference at the degenerate boundary
  where the two arms coincide, was not solved: what was proved there is that ONE
  unregularized Gaussian spectral route fails, via a mechanism that is generic to
  fibrewise quadratic forms and uses nothing about transport.
banked_on: "2026-08-05"
---

# stat_cot_observational_efficiency / v1 — Downgraded

**Topic.** Semiparametric efficiency and cross-fitted one-step inference for the smooth quadratic conditional-optimal-transport lower bound on mean squared individual treatment effects in observational studies: extend Lin-Gao-Blanchet-Glynn (arXiv:2602.20681, Proposition 3.3 and Theorem 3.2) from randomized marginal-sample asymptotic normality to i.i.d. observational data under ignorability and overlap by deriving the observed-data canonical gradient, efficiency bound, propensity-corrected wavelet-Brenier one-step estimator, uniform studentized normality and Wald coverage, with Ji-Lei-Spector's 401(k) SIPP analysis as the applied consumer

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Independent referee re-grade: subfield, not field. The headline efficiency/DML theorem is the propensity-corrected version of Lin-Gao-Blanchet-Glynn arXiv:2602.20681 (Prop 3.3 + Thm 3.2: same conditional estimand, same centered-Kantorovich-potential influence function, same s > D/2 condition; cited by the note) composed with Manole et al. AoS 2024 Lemma 21/Thm 22, i.e. exactly the one-step correction the cited literature names as its own future work; the single open question (degeneracy-adaptive inference) is unresolved.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

**Why this was downgraded, in plain terms.** You never see both potential
outcomes for the same person, so the average squared individual treatment effect
is not identified; its sharp lower bound comes from optimally matching the two
arms' conditional outcome distributions within each covariate cell. This note
takes that bound as an estimation target in an observational study, writes down
its influence function, builds a cross-fitted debiased estimator, and proves the
Wald interval works. The deliverable is the observational, propensity-corrected
version of an inference theory that already exists for randomized designs — plus
a negative remark about the degenerate case where the two arms coincide.

Two things here are genuinely not in print: the uniform triangular-array
studentization with sigma_n -> 0, and the explicit non-Hilbert-Schmidt
identity-compression statement. Neither opens a regime. The first is bookkeeping;
the second is a negative result about a route that `def:degeneracy-handle` never
defines precisely (it is two sentences of prose), obtained by a mechanism generic
to fibrewise quadratic forms.

**Where the interest actually is.** The sigma_n -> 0 extension bites only in a
sliver: `prop:holder-propensity-efficient-inference-phase-boundary` needs
kappa < min{2a_q - 1/2, a_pi + a_q - 1/2, a_q, a_pi, 1/2} with a_q = s/(2s+D),
which at d_X=5, d_Y=1, s=4 is kappa < 0.071 — the variance may shrink only slower
than n^(-0.07). And in the 401(k)/SIPP application the note itself names
(writeup.tex:914), d_Y = 1, where the whole transport apparatus reduces to
conditional quantile functions and the object is the classical conditional
comonotone bound.

**Re-anchor path.** Ranked by value.

1. **Solve the open question** (`discovery/solve_oeq_degeneracy_adaptive_inference.json`).
   Construct a regularized or smoothing-based statistic with an explicit limit law
   AT and THROUGH equality — the degenerate-U-statistic route with bandwidth
   normalization — and prove honest uniform coverage across the sigma_n -> 0
   transition. The literature has flagged this open since Manole et al. ("we leave
   open the question of obtaining limit laws under this regime"), and
   Agarwal-Luedtke obtain exactly this in the entropic case, which is also the
   clue: regularization is what restores a square-summable spectrum. **Nothing
   else in this note would be needed** — this is a standalone result.
2. **Supply a converse on the smoothness threshold.** Prove s > D/2 is necessary
   (a minimax lower bound showing the target is not root-n estimable below it), or
   beat it with a higher-order construction. Either turns the current exponent
   arithmetic — which merely reproduces Lin et al.'s condition — into a rate
   frontier.
3. **Make the regularity a theorem.** Replace `ass:uniform-conditional-brenier-*`
   with a proof from Caffarelli global regularity on uniformly convex C^{2,alpha}
   domains, and show attainment without full (d_X+d_Y)-dimensional conditional
   density estimation (semi-dual or entropic plug-in). This is what would make the
   estimator usable rather than nominal — as written it needs a joint conditional
   density at rate n^(-s/(2s+D)) with s > D/2, which no applied researcher will
   attempt.

Adding a propensity score to a published randomized-design CLT is not a path.

**Mandatory before any re-raise.** Cite and position against
Agarwal-Luedtke arXiv:2605.08485 (currently uncited, and it contains close
analogues of BOTH the influence-function form and the degeneracy analysis), and
re-do the novelty check against `lin2026statistical` — which this run cited,
attested in `core.json`, and then never compared its delivered theorem to. Also
verify non-vacuity of the parent class for d_Y >= 2; it is automatic for d_Y = 1
only via monotone rearrangement, and there the estimand collapses to a classical
quantile functional.

**Mechanical defects to fix if the note is ever reused.** `writeup.tex:451` has
an unescaped `le` (`|\phi_{a,n}|le2R^2`); `m_OT` and `M_OT` are used throughout
but never declared in the symbol table, while `lambda` (line 214,
"strong-convexity modulus") is declared and never used.

**Run state.** Terminated at Stage 0.5 — there is no formalization evidence to
weigh, and no Lean artifacts exist for this entry.
