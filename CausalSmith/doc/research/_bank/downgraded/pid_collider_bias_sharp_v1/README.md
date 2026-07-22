---
qid: pid_collider_bias_sharp
spec: v1
topic: "Sharp partial identification of the average treatment effect under bounded collider bias: a closed-form quadratic identified set for the ATE when an analyst conditions (intentionally or by selection) on a partially-determined post-treatment outcome / mediator / selection indicator, characterized by two extremal joint laws (one saturating the upper envelope, one saturating the lower envelope) of the unobserved structural-error pair, with a non-trivial quadratic-in-the-collider-bias-parameter envelope strictly tighter than the Manski no-assumption bounds whenever any bias bound is finite; extends Greenland (2003) and VanderWeele (2009) collider-bias outer bounds to the sharp identified-set characterization, the direct open direction explicitly left in both papers' discussion sections"
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "proposal_drift"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Verbatim/near-verbatim reviewer phrases (stage_0.5_to_0 reviews + interventions
  # in pid_collider_bias_sharp_v1_reviews.jsonl). No *_oneshot_stage0_5_*.txt exist.
  - "The note repeatedly downgrades the contribution: the Introduction says the target is a field-level sharp-bound target, says it does not cite a published open-problem statement, and says it is not an equivalence or non-equivalence theorem between named published estimators."
  - "Proposition prop:lee-gamma-frontier-partial proves only the common-alpha sharp frontier and explicitly leaves the open-set non-representability assertions against external comparator geometries unconfirmed."
  - "The SGJR/JR and Honore-Hu comparisons in Section 7 are not comparisons to the published estimators or identification strategies as such; they are proposal-defined binary armwise support rectangles with different interpretive labels."
  - "The introduction, related-work section, theorem commentary, and conclusion all disclaim a flagship claim: the note says the result is not a published-open-problem claim about Lee, that the SGJR/JR and Honore-Hu comparisons are proposal-defined binary support benchmarks." # proposal_promise_gap=kernel_substituted
  - "the kernel itself was substituted (proposal_promise_gap=kernel_substituted), so re-deriving on the same .tex would still fail the orchestrator-enforced flagship floor" # intervention, attempt 21
  - "the flagship-style external-comparator non-representability clause of prop:lee-gamma-frontier-partial is not proved" # intervention, attempt 21
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a flagship sharp-ATE collider-bias identified set headlined as the
  Greenland (2003) / VanderWeele (2009) "open direction": extending their collider-bias
  outer bounds to a sharp identified-set characterization. The §8 conjectures were instead
  cast in a Lee-Gamma selection frame: the strict-tightening (Conj 2) and compatibility-gap
  iff (Conj 3) conjectures are CONFIRMED, and the sharp common-alpha frontier (Conj 1) is
  PARTIAL — proved on the finite-table input, but the headlined external-comparator /
  open-set non-representability clause is explicitly left unproven. No conjecture delivers
  the headlined Greenland/VanderWeele external-comparator result; reviewers found the SGJR/JR
  and Honore-Hu comparators are proposal-defined armwise rectangles, not the named published
  estimators, and the artifact self-downgrades to field tier. The proven Lee-Gamma core is
  sound but mis-headlined; what remains is a sharp finite-table sensitivity bound, not a
  flagship regime-opening extension of the cited collider-bias literature.
banked_on: "2026-05-21"
---

# pid_collider_bias_sharp / v1 — Downgraded

**Topic.** Sharp partial identification of the average treatment effect under bounded collider bias: a closed-form quadratic identified set for the ATE when an analyst conditions (intentionally or by selection) on a partially-determined post-treatment outcome / mediator / selection indicator, characterized by two extremal joint laws (one saturating the upper envelope, one saturating the lower envelope) of the unobserved structural-error pair, with a non-trivial quadratic-in-the-collider-bias-parameter envelope strictly tighter than the Manski no-assumption bounds whenever any bias bound is finite; extends Greenland (2003) and VanderWeele (2009) collider-bias outer bounds to the sharp identified-set characterization, the direct open direction explicitly left in both papers' discussion sections

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Split D0 honest: 3 conj verdicts (lee-gamma-frontier=partial; strict-tightening,coupling-iff=confirmed). D0.5 reject NOT solver-side: proposal headlined Greenland/VanderWeele collider envelope but §8 conjectures are Lee-Gamma framed and no §8 conjecture proves the headlined external-comparator clause. Proposal drift detected by upgraded split solver; needs proposal-stage upgrade not solver retry.

## Key files

- `pid_collider_bias_sharp_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_collider_bias_sharp_v1_proposal.tex` — final proposal version.
- `pid_collider_bias_sharp_v1.tex` — derivation note (if Stage 0 ran).
- `pid_collider_bias_sharp_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_collider_bias_sharp_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
