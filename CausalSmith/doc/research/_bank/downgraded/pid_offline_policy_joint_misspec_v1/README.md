---
qid: pid_offline_policy_joint_misspec
spec: v1
topic: "Sharp partial identification of offline contextual-bandit policy value under joint misspecification of the logging propensity and the outcome model, with bounded f-divergence between the misspecified and true propensity and a bounded sup-norm gap on the outcome regression, recovering doubly-robust point identification at the trivial bounds and Manski-Pepper-style truncated outcome bounds without unconfoundedness"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Verbatim/near-verbatim reviewer phrases from the D0.5 (stage_0.5_to_0) review log.
  # The cap is novelty: every D0.5 round verdicted REVISE/REJECT on novelty=subfield,
  # below novelty_target=field. Correctness was a separate, repaired defect.
  - "The derivation tier is below the orchestrator floor novelty_target=field. The sharp-program theorem is a standard finite latent-response sharp-bound representation with added convex constraints."
  - "The intended field-level kernel is the non-rectangular negative result, but it does not name a specific published estimator/workflow/claim that uses the refuted rectangular endpoint for this joint causal sensitivity target, as required by the negative-result rule."
  - "much of the contribution is generic Balke-Pearl/Manski-style latent-type sharpness with added convex constraints"
  - "The non-rectangular result is framed as refuting a generic shortcut rather than a named published estimator, paper, or workflow, which is load-bearing for the novelty claim."
  - "names SiZhangZhouBlanchet2020 and KallusMaoWangZhou2022 only as workflows to be ported, while explicitly saying those papers do not study this causal compatibility class; this does not meet the negative-result rule requiring a specific published target claim."
  # Correctness (1st round, later REPAIRED via Stage-0 re-derivation — not the cap):
  - "The main sharpness theorem is false as stated for the locked observable distribution P=law(X,A,Y): the conditional program matches only observed action masses and factual first moments, not the full conditional law of Y in each action cell." # repaired in later rounds; correctness=pass
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed the sharp identified interval for an offline contextual-bandit target
  policy value V(π) under JOINT misspecification — propensity inside a pointwise
  f-divergence ball and outcome regression inside a sup-norm tube — as a full-
  observed-law finite-grid conditional perspective-convex program (Thm sharp),
  with a "field-tier" non-rectangularity negative result (Thm nonrect) as the
  load-bearing kernel. First D0.5 round found Thm sharp FALSE against the locked
  law P (the program matched only action masses + first moments, not the full
  conditional law of Y per cell); a Stage-0 re-derivation repaired this and later
  rounds rated correctness pass/plausible. The math is sound, but all three D0.5
  rounds capped the tier at subfield on NOVELTY: the sharp program is the standard
  Balke-Pearl/Manski finite-latent LP template with added convex constraints, and
  the non-rectangular no-go refutes a generic rectangular post-processing port
  rather than any named published estimator/workflow, failing the negative-result
  rule for field tier. (Run also hit an intervention-parser bug, logged in PIPELINE_NOTES.)
banked_on: "2026-05-15"
---

# pid_offline_policy_joint_misspec / v1 — Downgraded

**Topic.** Sharp partial identification of offline contextual-bandit policy value under joint misspecification of the logging propensity and the outcome model, with bounded f-divergence between the misspecified and true propensity and a bounded sup-norm gap on the outcome regression, recovering doubly-robust point identification at the trivial bounds and Manski-Pepper-style truncated outcome bounds without unconfoundedness

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REVISE

**Banking reason.** D-0.5 ACCEPT, D0.5 REVISE x3 on novelty: kernel collapsed to subfield (standard Balke-Pearl finite latent + rectangular no-go); reviewer flagged that field-tier negative result needs a named published estimator/workflow that uses the refuted rectangular endpoint. Math sound. Also triggered intervention-parser bug (logged in PIPELINE_NOTES).

## Key files

- `pid_offline_policy_joint_misspec_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_offline_policy_joint_misspec_v1_proposal.tex` — final proposal version.
- `pid_offline_policy_joint_misspec_v1.tex` — derivation note (if D0 ran).
- `pid_offline_policy_joint_misspec_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_offline_policy_joint_misspec_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
