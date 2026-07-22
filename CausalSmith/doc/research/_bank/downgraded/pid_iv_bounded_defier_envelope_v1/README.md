---
qid: pid_iv_bounded_defier_envelope
spec: v1
topic: "Sharp partial identification of the average treatment effect from a binary instrument under bounded one-sided defier share and bounded never-taker share: closed-form polytopal identified set, sharpness certificate via boundary distributions, and exact limits recovering Imbens-Angrist LATE point identification when defier share equals zero and Manski-style outcome-support bounds when never-taker share equals one"
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown  # was solver_blocked; no F-stage solver ever ran — stalled at D0.5 math review, and the core envelope derivation actually succeeded
reraise_status: re-raise
gap_reasons:
  - "Assessed tier is subfield below novelty_target=flagship; the theorem proves an explicit reduction of an established finite LP with two mass caps, but not a regime-opening flagship contribution."
  - "the note does not identify a published open problem or prove a strict extension to a wider class as required for flagship tier."
  - "the confirmation of Conjecture 1's five nonredundant affine-facet families is only asserted via generic support-of-dual-basis language."
  - "the promised constructive maps Gamma_f are described abstractly by complementary slackness, but the note does not give the facet-by-facet constructions needed to cover degenerate zero-cell and cap-binding cases."
  - "General symbolic and automated discrete-bound methods are cited but not overcome; the result is positioned as a clearer and more auditable specialization rather than a flagship mathematical advance."
  - "flagship requires either a constructive exposed-basis enumeration (which Codex tried and failed to produce honestly) OR positioning against a named published open regime ... which the conjecture's framing against Balke–Pearl / Richardson–Robins / symbolic discrete-bound methods does not deliver."
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a sharp closed-form polytopal ATE envelope for a binary IV under
  simultaneous bounded-defier and bounded-never-taker mass caps. The scalar
  reduction (t=pi_F endpoint algebra, B_L/B_U sharp envelope, numerical
  nonredundancy example) was reviewed as correct, but the flagship-level
  promises — the nonredundant five-family affine-facet taxonomy, the
  constructive boundary-distribution maps Gamma_f, and the strict-shrinkage
  frontier — were only partially confirmed then overclaimed via generic
  LP-duality language. Stalled at D0.5: correctness/structure passed but
  novelty fell below the flagship floor; no Lean/F-stage was ever reached.
  What remains: a genuinely correct subfield-tier envelope theorem that would
  need either an honest exposed-basis enumeration or a named published
  open-regime to justify a flagship headline.
banked_on: "2026-05-20"
---

# pid_iv_bounded_defier_envelope / v1 — Downgraded

**Topic.** Sharp partial identification of the average treatment effect from a binary instrument under bounded one-sided defier share and bounded never-taker share: closed-form polytopal identified set, sharpness certificate via boundary distributions, and exact limits recovering Imbens-Angrist LATE point identification when defier share equals zero and Manski-style outcome-support bounds when never-taker share equals one

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** REJECT

**Banking reason.** Angle 0 D0.5 reject (subfield LP specialization, overclaimed via generic LP-duality); angles 1-2 rejected at D-0.5; pivot budget exhausted.

## Key files

- `pid_iv_bounded_defier_envelope_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_iv_bounded_defier_envelope_v1_proposal.tex` — final proposal version.
- `pid_iv_bounded_defier_envelope_v1.tex` — derivation note (if D0 ran).
- `pid_iv_bounded_defier_envelope_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_iv_bounded_defier_envelope_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
