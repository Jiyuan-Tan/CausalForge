---
qid: pid_network_iv_exposure
spec: v1
topic: "Flagship generalization of network-exposure partial ID to IV noncompliance with possibly misspecified treatment and instrumental exposure mappings."
novelty_target: flagship
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "Pipeline failure before literature-scout output: `bash -lc` invoked WSL on Windows, but WSL had no installed distro."
  - "No proposal, reviewer verdict, or mathematical artifact was produced; do not treat this as topic evidence."
reusable_artifacts:
  - path: "(none)"
    kind: other
    one_line: "No scientific artifact was produced before the dispatcher failure."
seeds_burned: []
proof_attempt_summary: |
  This was a plumbing failure discovered while launching the first real run of the 5-budget batch. Stage -1.1 attempted to call Codex through `bash -lc`; on this Windows host `bash` resolves to WSL, which has no installed distro, so stdout was empty and JSON parsing failed. The dispatcher was patched to call `codex.exe` directly on Windows; retry the same scientific topic under a fresh specialization.
banked_on: "2026-05-24"
---

# pid_network_iv_exposure / v1 — Failed

**Topic.** Flagship generalization of network-exposure partial ID to IV noncompliance with possibly misspecified treatment and instrumental exposure mappings.

**Novelty target.** flagship

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** Pipeline failure: Stage -1.1 used bash -lc on Windows, which resolved to WSL with no installed distro, so Codex returned no parseable JSON before any proposal review.

## Key files

- `pid_network_iv_exposure_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_network_iv_exposure_v1_proposal.tex` — final proposal version.
- `pid_network_iv_exposure_v1.tex` — derivation note (if Stage 0 ran).
- `pid_network_iv_exposure_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_network_iv_exposure_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
