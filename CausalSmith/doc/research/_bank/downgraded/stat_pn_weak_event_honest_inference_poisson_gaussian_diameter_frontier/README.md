---
qid: stat_pn_weak_event_honest_inference
spec: poisson_gaussian_diameter_frontier
topic: "Weak-event honest inference for probabilities of necessary and sufficient causation under ignorability, monotonicity, and overlap: construct a rare-event-calibrated confidence set by inverting the cross-fitted orthogonal PN/PS ratio score over triangular arrays whose factual conditioning-event probability d_n may vanish; derive uniform coverage from explicit nuisance-rate and score-moment conditions, recover Tian-Wu's efficient Gaussian limit when n d_n diverges, and prove the matching minimax expected-diameter frontier min{1,(n d_n)^(-1/2)} with a nonshrinking Poisson boundary at n d_n=O(1); use Hannart-Naveau rare-event climate PN/FAR and Tian-Wu stroke attribution as applied consumers."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Stage 0.5.G reviewer, verbatim (reviews/review_general.json):
  - "The note proves a genuine matched expected-diameter rate only for vanishing schedules satisfying the stated nuisance-product condition, with the converse additionally restricted to least-favorable-compatible primitives and c_G <= 3/16."
  - "The bounded-count result proves only a nonshrinking lower obstruction on a separate capped comparison shell, not an upper procedure or a Poisson transition law."
  # Independent referee re-grade, 2026-08-05 (not from the pipeline chain):
  - "The headline rate is not derived; it is fixed by the definition of the class it is proved over. def:gaussian-shells pins q_d(P) = r_n and V_d(P) >= c_G r_n, the estimating function is exactly affine in t with slope the empirical factual frequency, so noise/slope = (n r_n)^(-1/2) follows in three lines of algebra from a variance normalization the class ASSUMES."
  - "prop:regular-reduction establishes that the score-inversion root is the cross-fitted ratio with Tian-Wu's estimated-efficient-influence-function standard error; since their asymptotic variance is Var(psi)/q^2, substituting q = r_n gives the width (n r_n)^(-1/2) immediately. The note proves its own headline is the published efficiency bound along the sequence."
  - "ass:score-information — the ONLY assumption the note self-labels Novel — is exactly the premise that the score variance does not vanish faster than the factual probability. It is not vacuous (take m_0 = 0 and V = 0 exactly), so it carves out precisely the degenerate boundary where the interesting non-uniformity lives, and assumes it away rather than characterizing it."
  - "The converse witness (def:least-favorable) has X uniform and independent, e = 1/2, and constant outcome regressions, so it contains ZERO semiparametric content — it is the binomial two-point bound with n*r_n trials. 'Matching' therefore asserts only that nonparametric nuisances cost nothing to first order, which Neyman orthogonality plus the assumed product rate already guarantees."
  - "Drift: the locked topic promised the frontier min{1, (n d_n)^(-1/2)} WITH a Poisson-calibrated boundary at n d_n = O(1). Only the lower obstruction survives; the upper half was dropped (writeup.tex:1327) and the specialization renamed around the loss. state.json still carries poisson_gaussian_diameter_frontier while core.json carries gaussian_shell_directional_minimax_frontier."
  # Not a defect — recorded so a re-raise does not re-litigate it:
  - "conj:gaussian-lower is a misleading LABEL, not an open claim: it is fully proved at writeup.tex:474-487. The independent referee hand-verified the least-favorable variance computation, the KL/Pinsker chain, the score-envelope domination, the localization inequality and the diameter algebra, and found NO mathematical error anywhere in the note."
reusable_artifacts:
  - path: discovery/writeup.tex
    kind: operator
    one_line: "thm:two-nuisance-learning-boundary-not-necessary (lines 581-600) and thm:ultra-rare-boundary-score-robustness (lines 1075-1118) — a propensity-only affine score attaining the same coverage and diameter order under a NON-NESTED condition (n r_n a_e^2 -> 0), with no outcome regression and no outcome smoothness at all. The mechanism (propensity error multiplied by a rare-event indicator, so bias is O(a_e * r_n) rather than O(a_e)) is the most interesting mathematics in the note and is filed here as an internal robustness construction."
  - path: discovery/writeup.tex
    kind: witness
    one_line: "def:least-favorable + lem:lf-membership (lines 323, 453) — the three-cell Bernoulli least-favorable family with V/r = a + a^2(1-4r) in [3/16, 21/16]; hand-verified correct, reusable as a two-point converse witness for any rare-event shell."
  - path: discovery/solve_thm_gaussian_frontier.json
    kind: other
    one_line: "Solve record for the matched-frontier theorem, including the Cai-Low two-point expected-length route as instantiated here."
  - path: discovery/core.json
    kind: literature_map
    one_line: "Comparator attestations for Tian-Wu, Cai-Low, Imbens-Manski / Armstrong-Kolesar and the weak-overlap family; the bibliography annotations correctly note that the overlap literature handles scale EXPLOSION rather than vanishing scale."
  - path: discovery/proposal_angle0_rejected.tex
    kind: other
    one_line: "Three fully-drafted rejected angles (angle0/1/2, with matching proto_core_*_rejected.json) — the pivot budget was consumed in full; read before proposing anything adjacent to avoid re-walking them."
seeds_burned: []
proof_attempt_summary: |
  Aimed at a matched minimax expected-diameter frontier for honest inference on
  the probability of necessity when the conditioning event is rare, including a
  Poisson-calibrated transition at bounded expected event count. What was
  delivered is a correct and unusually careful note proving the (n r_n)^(-1/2)
  rate on a shell whose own variance normalization forces that rate, matched by a
  covariate-free two-point Bernoulli converse with no semiparametric content —
  and the note itself proves (prop:regular-reduction) that this is the published
  Tian-Wu efficiency bound evaluated along the vanishing-denominator sequence. The
  Poisson upper half was dropped, leaving only a lower obstruction; what remains
  genuinely open, and is the interesting theorem, is the true nuisance-learning
  boundary that the note shows its own regularity class fails to capture.
banked_on: "2026-08-05"
---

# stat_pn_weak_event_honest_inference / poisson_gaussian_diameter_frontier — Downgraded

**Topic.** Weak-event honest inference for probabilities of necessary and sufficient causation under ignorability, monotonicity, and overlap: construct a rare-event-calibrated confidence set by inverting the cross-fitted orthogonal PN/PS ratio score over triangular arrays whose factual conditioning-event probability d_n may vanish; derive uniform coverage from explicit nuisance-rate and score-moment conditions, recover Tian-Wu's efficient Gaussian limit when n d_n diverges, and prove the matching minimax expected-diameter frontier min{1,(n d_n)^(-1/2)} with a nonshrinking Poisson boundary at n d_n=O(1); use Hannart-Naveau rare-event climate PN/FAR and Tian-Wu stroke attribution as applied consumers.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Independent referee re-grade: subfield, not field. The (n r_n)^(-1/2) headline rate is the Tian-Wu (arXiv:2407.10185) efficiency bound evaluated along the vanishing-denominator sequence, an equivalence the note proves itself in prop:regular-reduction; the rate scale is fixed by the shell definition via ass:score-information (the one assumption self-labelled Novel, which assumes away the degenerate boundary where the interesting non-uniformity lives) rather than derived; and the matching converse is a covariate-free two-point Bernoulli witness with zero semiparametric content. No math errors found. The promised Poisson-calibrated upper half at n*r_n = O(1) was dropped and the specialization renamed around the loss.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

**Why this was downgraded, in plain terms.** The note says that when the
conditioning event is rare, your effective sample size is the *count* of rare
events rather than n, so precision goes like 1/sqrt(n·r) and estimation collapses
when that count is O(1). That is true, cleanly proved, and free of errors — and
it is what an applied analyst already gets by plugging a vanishing denominator
into the existing Tian-Wu efficiency bound. There is no procedural change, no new
calibration, and no design implication that was not already available.

The demotion is structural, not a matter of execution quality: the rate is not
derived, it is fixed by the shell's own variance normalization, and the converse
that "matches" it is free. Two things in the note are genuinely unpublished — the
uniform triangular-array studentization with sigma_n -> 0, and the O(1)-count
non-shrinking obstruction — but the first is bookkeeping and the second is the
half of the promised Poisson result that costs nothing.

**This entry is worth re-raising for a reason the pipeline never recorded.**
The note proves that its own regularity class is the wrong one, and files that
under "internal robustness construction" (writeup.tex:1119). A propensity-only
affine score — no outcome regression, no outcome smoothness whatsoever — attains
the same coverage and the same diameter order under a different, non-nested
condition, because the propensity error is multiplied by a rare-event indicator
so the bias is O(a_e·r_n) rather than O(a_e). That is real mathematics, and the
frontier it points at was never determined.

**Re-anchor path.** Ranked by value, not by cost.

1. **Find the true nuisance-learning boundary.** Determine the frontier in
   (beta_e, beta_b, p, r_n) space at which honest (n r_n)^(-1/2) width becomes
   impossible. A converse there must MOVE the nuisances — it cannot be a
   constant-regression Bernoulli family — so it would carry genuine nonparametric
   content. This is the field-tier theorem hiding in this note, and the two
   robustness theorems listed under `reusable_artifacts` are the way in.
2. **Delete ass:score-information and derive the actual rate.** Work over the
   class {q_d(P) = r_n} with NO variance floor, including the boundary where
   V_d << r_n (Theta_d near 1, m_0 near 0, where V_d = 0 exactly). That converts
   an assumed normalization into a derived one — precisely the difference between
   subfield and field under this rubric.
3. **Deliver the promised Poisson half.** An upper procedure with correct
   calibration at n·r_n = O(1) with LEARNED nuisances, matching the bounded-count
   obstruction already proved here. Genuinely open, genuinely hard (nuisance
   estimation at O(1) effective events), and it was the distinctive part of the
   original topic.

**Housekeeping for any re-raise.** The specialization name is inconsistent on
disk — `state.json` says `poisson_gaussian_diameter_frontier`, `core.json` says
`gaussian_shell_directional_minimax_frontier`. Reconcile before resuming, and
note that the Poisson half named in the state-file specialization is exactly the
part that was dropped. The pivot budget was fully consumed (3 rejected angles,
angle-2 alone reaching v6); read `discovery/proposal_angle*_rejected.tex` before
proposing anything adjacent.

**On the review chain.** `reviews/review_math.json` returned `pass` with zero
findings, but all seven of its checks are `cited-verified-attested` checks on
comparator citation *scope* — it verified that the bibliography describes the
cited papers accurately and examined no proof step of any theorem. It is not
evidence of correctness here (the correctness evidence is the independent
referee's hand-verification, recorded in `gap_reasons`).
