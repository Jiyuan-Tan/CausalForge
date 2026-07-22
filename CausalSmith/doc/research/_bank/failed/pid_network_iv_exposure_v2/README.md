---
qid: pid_network_iv_exposure
spec: v2
topic: "Flagship generalization of network-exposure partial ID to IV noncompliance with possibly misspecified treatment and instrumental exposure mappings."
novelty_target: flagship
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "Pipeline failure before literature-scout output: Windows branch spawned `codex.exe`, which failed with EPERM from the WindowsApps alias."
  - "No proposal, reviewer verdict, or mathematical artifact was produced; do not treat this as topic evidence."
reusable_artifacts:
  - path: "(none)"
    kind: other
    one_line: "No scientific artifact was produced before the dispatcher failure."
seeds_burned: []
proof_attempt_summary: |
  This was the first retry after patching out `bash -lc`. It exposed a second Windows-specific launcher issue: `codex.exe` is present in WindowsApps but cannot be spawned non-interactively, while the `codex` shim works under execa. The dispatcher was patched again to use `codex` on Windows and to normalize missing stdout/stderr.
banked_on: "2026-05-24"
---

# pid_network_iv_exposure / v2 — Failed

**Topic.** Flagship generalization of network-exposure partial ID to IV noncompliance with possibly misspecified treatment and instrumental exposure mappings.

**Novelty target.** flagship

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** Pipeline failure: first Windows fix used codex.exe, but WindowsApps aliases return EPERM under non-interactive spawn; Stage -1.1 saw undefined stdout and produced no JSON.

## Key files

- `pid_network_iv_exposure_v2_state.json` — pipeline state at banking (`banked: true`).
- `pid_network_iv_exposure_v2_proposal.tex` — final proposal version.
- `pid_network_iv_exposure_v2.tex` — derivation note (if Stage 0 ran).
- `pid_network_iv_exposure_v2_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_network_iv_exposure_v2_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
