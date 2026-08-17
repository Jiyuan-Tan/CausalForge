---
qid: stat_doseresponse_minimax_elbow
spec: v1
topic: "is the treatment-density smoothness a genuine hardness parameter for the continuous-treatment dose-response curve: over the anisotropic Holder class P(alpha,beta,s,d,M,c,t0) of laws for Z = (Y,A,X) on [0,1] x [0,1]^d with |Y| <= M, strict positivity c <= pi(a|x) <= 1/c, bounded covariate density, a -> mu(a,x) Holder-alpha, a -> pi(a|x) Holder-beta, and x -> mu(t0,x), x -> pi(t0|x) Holder-s, let M_n(alpha,beta,s,d) be the minimax pointwise MSE of theta_P(t0) = int mu_P(t0,x) p_X(x) dx, the infimum over ALL measurable estimators of the n-sample of the supremum over that class; prove (K1) that M_n is beta-invariant up to n-free constants for every 0 < beta < beta' <= infinity at every alpha, s, d, so the minimax exponent never depends on the treatment-density smoothness given positivity, and (K2) that for every s >= d/4 and every beta > 0, M_n is of exact order n^(-2alpha/(2alpha+1)), which is strictly faster than the exponent 2min(alpha,beta)/(2min(alpha,beta)+1) guaranteed by Bonvini-Kennedy arXiv:2207.11825 v2 Theorem 3.1 whenever beta < alpha and strictly faster than the min(alpha,beta+1) refinement those authors themselves conjecture, so their stated trichotomy resolves as an estimator/analysis artifact rather than a fundamental aspect of the minimax rate; the achieving estimator and every mechanic inside it, all constants and polylog factors, any auxiliary smoothness on the covariate density, and the VALUE of M_n in the deficient covariate regime s < d/4 (where only beta-freeness is claimed) are explicitly NOT pre-committed and are the derivation work; distinct from the in-repo banked run stat_dose_response_minimax/holder_anisotropic_converse, which proved only the beta-INSENSITIVE lower floor and explicitly preserved the same-class beta-sensitive upper frontier as an open handle, from Kennedy-Balakrishnan-Robins-Wasserman arXiv:2203.00837 which is binary-treatment CATE with no treatment-density index, from Kim-Wang arXiv:2604.13410 Theorem 4.3 and arXiv:2510.19094 Lemma 2 whose lower bounds are integrated-risk RKHS/Sobolev results containing no treatment-density smoothness, and from Balakrishnan-Kennedy-Wasserman arXiv:2305.04116 whose structure-agnostic bounds do not apply in a smoothness model; consumer is the CausalGPS R package and its PM2.5-mortality exposure-response curve on Medicare data, and npcausal ctseff"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Stage 0.5.G reviewer, verbatim (reviews/review_general.json):
  - "The delivered sharp result is confined to the construction-dependent region Omega: there the note proves both the explicit estimator upper bound and the matching one-dimensional Le Cam lower bound, but it does not determine the interior frontier for 0<c<1 outside that region."
  - "The beta-invariance theorem is correspondingly local to tuples whose rougher class lies in Omega and follows from class nesting plus those two rate bounds; it is not a global beta-invariance characterization."
  - "The deficient-region result is only a nonmatching two-sided exponent bracket, and the c=1 theorem concerns a degenerate boundary where the treatment density is forced to be uniform."
  # Independent referee re-grade, 2026-08-05 (not from the pipeline chain):
  - "K2 promised the exact order for every s >= d/4; Omega delivers strictly less. Omega forces alpha <= 2 (via the structural clause (alpha^1)+(beta^1) >= alpha) and is EMPTY at alpha=beta=1 for d >= 4, because the pilots in def:beta-free-handle are histograms and dose-window averages, so every exponent is capped at order 1."
  - "The converse half (lem:all-beta-oracle-lower-floor) uses p_X = pi = 1 and mu constant in x, i.e. Tsybakov Ch. 2 with covariates, overlap, beta and s switched off; it is the easy half of the Bonvini-Kennedy conjecture, not the elusive one."
  - "The all-beta floor re-proves the already-accepted bank entry stat_dose_response_minimax_holder_anisotropic_converse/thm:sharp-pointwise-lower-bound on a re-drawn class; nothing in the pipeline detected the collision."
  - "The motivating 2beta/(2beta+1)-vs-2alpha/(2alpha+1) contrast is drawn against Bonvini-Kennedy's FIRST-ORDER bias term (their Eq. 7), which their own higher-order corrections in the same section exist to cancel; their published rate contains no beta at all."
  - "Unverified proof step: in lem:localized-polynomial-master-risk (writeup.tex:1123-1127) the passage from the pointwise bias bound to the squared risk of the local-polynomial solution is asserted, not derived — random A-dependent weights are not handled. This is the single step the whole upper bound rests on."
reusable_artifacts:
  - path: discovery/writeup.tex
    kind: witness
    one_line: "lem:extreme-low-s-fuzzy-lower (lines 858-989) — a competent transplant of the Kennedy-Balakrishnan-Robins-Wasserman two-prior sign-mixture fuzzy-hypothesis construction to the dose-response class; the technique is sound and reusable even though it is deployed here where no matching upper bound exists."
  - path: discovery/solve_oeq_deficient_frontier.json
    kind: other
    one_line: "The open deficient-regime (s < d/4) two-sided exponent bracket R_ach <= rho <= r_low in closed form — the starting point for any re-anchor, since checking whether the two exponents ever coincide is a finite computation on these formulas."
  - path: discovery/core.json
    kind: literature_map
    one_line: "Comparator table and per-node verdicts; records which Bonvini-Kennedy / KBRW / Takatsu-Westling claims were attested and at what scope."
  - path: discovery/proof_archive/
    kind: other
    one_line: "Content-addressed archive of every proof fragment produced across solve rounds; useful for recovering intermediate lemmas discarded by later rounds."
seeds_burned: []
proof_attempt_summary: |
  Aimed to show the treatment-density smoothness beta is not a genuine hardness
  parameter for the pointwise dose-response minimax rate, by proving global
  beta-invariance (K1) and the exact order n^(-2alpha/(2alpha+1)) for all
  s >= d/4 (K2). What was delivered is an explicit first-order estimator whose
  risk matches a one-dimensional Le Cam floor only inside a construction-dependent
  region Omega that is strictly smaller than the promised s >= d/4 — it forces
  alpha <= 2 and is empty at alpha=beta=1 for d >= 4 — with beta-invariance
  correspondingly local and following from class nesting rather than from new
  mathematics. The promised elbow was never reached: outside Omega only a
  non-matching exponent bracket exists, with no exhibited region where its two
  endpoints coincide, and that remains the open kernel.
banked_on: "2026-08-05"
---

# stat_doseresponse_minimax_elbow / v1 — Downgraded

**Topic.** is the treatment-density smoothness a genuine hardness parameter for the continuous-treatment dose-response curve: over the anisotropic Holder class P(alpha,beta,s,d,M,c,t0) of laws for Z = (Y,A,X) on [0,1] x [0,1]^d with |Y| <= M, strict positivity c <= pi(a|x) <= 1/c, bounded covariate density, a -> mu(a,x) Holder-alpha, a -> pi(a|x) Holder-beta, and x -> mu(t0,x), x -> pi(t0|x) Holder-s, let M_n(alpha,beta,s,d) be the minimax pointwise MSE of theta_P(t0) = int mu_P(t0,x) p_X(x) dx, the infimum over ALL measurable estimators of the n-sample of the supremum over that class; prove (K1) that M_n is beta-invariant up to n-free constants for every 0 < beta < beta' <= infinity at every alpha, s, d, so the minimax exponent never depends on the treatment-density smoothness given positivity, and (K2) that for every s >= d/4 and every beta > 0, M_n is of exact order n^(-2alpha/(2alpha+1)), which is strictly faster than the exponent 2min(alpha,beta)/(2min(alpha,beta)+1) guaranteed by Bonvini-Kennedy arXiv:2207.11825 v2 Theorem 3.1 whenever beta < alpha and strictly faster than the min(alpha,beta+1) refinement those authors themselves conjecture, so their stated trichotomy resolves as an estimator/analysis artifact rather than a fundamental aspect of the minimax rate; the achieving estimator and every mechanic inside it, all constants and polylog factors, any auxiliary smoothness on the covariate density, and the VALUE of M_n in the deficient covariate regime s < d/4 (where only beta-freeness is claimed) are explicitly NOT pre-committed and are the derivation work; distinct from the in-repo banked run stat_dose_response_minimax/holder_anisotropic_converse, which proved only the beta-INSENSITIVE lower floor and explicitly preserved the same-class beta-sensitive upper frontier as an open handle, from Kennedy-Balakrishnan-Robins-Wasserman arXiv:2203.00837 which is binary-treatment CATE with no treatment-density index, from Kim-Wang arXiv:2604.13410 Theorem 4.3 and arXiv:2510.19094 Lemma 2 whose lower bounds are integrated-risk RKHS/Sobolev results containing no treatment-density smoothness, and from Balakrishnan-Kennedy-Wasserman arXiv:2305.04116 whose structure-agnostic bounds do not apply in a smoothness model; consumer is the CausalGPS R package and its PM2.5-mortality exposure-response curve on Medicare data, and npcausal ctseff

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Independent referee re-grade: subfield, not field. Achievability is a first-order re-derivation of Bonvini-Kennedy (arXiv:2207.11825) on a strictly smaller region: Omega forces alpha <= 2 and is EMPTY at alpha=beta=1 for d >= 4, whereas their published oracle region s >= d/4 is satisfiable for every (alpha,beta,d). The matching converse is the textbook one-dimensional Tsybakov floor on a covariate-free submodel (p_X = pi = 1, mu constant in x), so it carries no causal content. The promised elbow is never proved (oeq:deficient-frontier remains open with a non-matching bracket and no exhibited coincidence region), and the all-beta floor re-proves the already-accepted bank entry stat_dose_response_minimax_holder_anisotropic_converse on a re-drawn class.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

**Why this was downgraded, in plain terms.** The note claims a matching minimax
rate for estimating the average outcome at one dose. But the "matching" pair is a
known upper bound proved on a *smaller* region than the published one, matched
against a converse that is the textbook one-dimensional smoothing bound obtained
on a sub-problem with treatment assigned uniformly at random and covariates
switched off. The promised elbow — the rate transition in the rough-covariate
regime — is never proved.

The arithmetic that decides it: Bonvini-Kennedy's published oracle region
`s >= d/4` is satisfiable for every (alpha, beta, d). Omega is not. Recomputing
the threshold g from `def:oracle-threshold`:

    alpha=beta=1, d=1: g=0.333      alpha=beta=1, d=3: g=1.000 (boundary)
    alpha=beta=1, d=2: g=0.667      alpha=beta=1, d=4: g=1.333 -> Omega EMPTY
    alpha=beta=0.5, d=4: g=1.000    alpha=0.2, beta=1, d=10: g=1.078 -> EMPTY
    alpha > 2, any beta: structural domain EMPTY

So at alpha=beta=1 with four or more covariates — an ordinary setting — the
exact-rate theorem says nothing, while the published upper bound plus the free
floor already pin the rate for s >= 1. The note concedes the mechanism itself at
writeup.tex:1481 ("Omega is an achievability regime for the present
separated-pilot construction, not a claim that estimation outside it must depend
on beta").

**Re-anchor path.** Ranked shortest-first; (1) is cheap and should have run
before the note was written.

1. **Check whether the deficient-regime bracket ever closes.** `oeq:deficient-frontier`
   asserts a conditional ("whenever the two exponents coincide") whose antecedent
   was never tested. Both endpoints are closed forms in (alpha, beta, s, d) — see
   `discovery/solve_oeq_deficient_frontier.json`. If a nonempty subregion exists
   where they agree, that is a genuine new exact exponent and plausibly the elbow.
2. **Prove a converse matching R_hist in the rough-covariate band s < d/4.** This
   is Bonvini-Kennedy's own stated open problem and where the elbow actually lives.
   A converse there must move the nuisances, so it would carry real nonparametric
   content. Field, arguably flagship.
3. **Remove the order-1 caps.** Replace the histogram / dose-window pilots in
   `def:beta-free-handle` with local-polynomial pilots so the exponents are not
   truncated, killing the alpha <= 2 restriction and shrinking g. If the resulting
   region contains {s >= d/4}, achievability at least stops being weaker than
   published. On its own this is still subfield — the converse remains free.

**Do not re-raise without fixing two things.** (a) The all-beta floor duplicates
the accepted entry `stat_dose_response_minimax_holder_anisotropic_converse`; cite
it rather than re-proving it. (b) The 2beta/(2beta+1) framing is a strawman
against a bias term the comparator cancels — any re-raise must compare against
Bonvini-Kennedy's actual published rate rho_n, which has no beta in it.

**Also unresolved:** the asserted-not-derived step at `writeup.tex:1123-1127`
(see `gap_reasons`). `reviews/review_math.json` returned `pass` with zero
findings and checked only the two `cited` lemmas, so this was never examined.

**Provenance.** `discovery/proposal.tex` is an unmodified pipeline skeleton —
every section is still a `% TODO(stage-1 ...)` placeholder — so
proposal-vs-delivered drift cannot be measured from it. The only surviving
statement of intent is `discovery/gaps.json` (the locked topic, reproduced in
the frontmatter above).
