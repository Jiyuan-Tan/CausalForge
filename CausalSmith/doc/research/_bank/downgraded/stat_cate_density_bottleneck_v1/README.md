---
qid: stat_cate_density_bottleneck
spec: v1
topic: "Pointwise CATE benchmark-rate achievability under a fixed positive-band unknown design density: construct a total close-pair local R-estimator attaining the Kennedy--Balakrishnan--Robins--Wasserman rate on a nonempty smoothness region without density estimation or density smoothness, while leaving the exact band-only minimax exponent and matching positive-band converse open."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: re-raise
gap_reasons:
  - "What is actually proved is a one-sided achievability result: a pair-difference U-statistic local R-estimator attains the ALREADY-PUBLISHED KBRW exponent."
  - "The two endpoints have strictly different exponents (t<q), so nothing about the band-only exponent is determined."
  - "The fixed-uniform-density KBRW converse is inadmissible: KBRW's cancellation uses flat-top support holes; restoring a positive lower band leaves an uncancelled O(h^{2gamma}) term and only the oracle exponent."
reusable_artifacts:
  - "discovery/core.json — repaired typed core containing the total close-pair estimator, its risk proof, the honest loose bracket, and the open positive-band converse."
  - "discovery/writeup.tex — synchronized derivation note for the close-pair construction and KBRW comparison."
  - "discovery/open_obligations.json — exact positive-band frontier, logarithm-removal, and opposite-ordering obligations."
  - "orchestrator/decision_log.jsonl — source audit showing why the KBRW support-hole construction cannot simply be transplanted to a fixed positive density band."
seeds_burned:
  - index: 0
    one_liner: "Band-only density minimax slowdown"
    reason: "The selected strict band-only slowdown angle collapsed: KBRW cancellation relies on support holes, and no valid fixed-positive-band converse was obtained."
proof_attempt_summary: |
  The run attempted to prove that an unknown, unsmooth positive-band design density forces a pointwise CATE minimax slowdown relative to the KBRW benchmark. The density-coupled converse collapsed because the available KBRW cancellation relies on support holes; the repaired derivation instead proves that a total close-pair local R-estimator attains the KBRW rate on a nonempty restricted region without density estimation or density smoothness. The exact positive-band minimax exponent, a matching converse, extension beyond the close-pair region, and logarithm removal remain open.
banked_on: "2026-08-09"
---

# stat_cate_density_bottleneck / v1 — Downgraded

**Topic.** Pointwise CATE benchmark-rate achievability under a fixed positive-band unknown design density: construct a total close-pair local R-estimator attaining the Kennedy--Balakrishnan--Robins--Wasserman rate on a nonempty smoothness region without density estimation or density smoothness, while leaving the exact band-only minimax exponent and matching positive-band converse open.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5.G tier=subfield < floor=field: sound close-pair KBRW-rate achievability under a fixed positive density band, but no matching positive-band converse.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
