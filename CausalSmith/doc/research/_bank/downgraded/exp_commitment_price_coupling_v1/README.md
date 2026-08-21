---
qid: exp_commitment_price_coupling
spec: v1
topic: "The minimax fraction of the oracle variance-reduction gain that a single committed randomization design can guarantee simultaneously across a finite family of unknown response-structure classes, and the design certified to attain it"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "Its substantive boundary is the direct-sum kernel restriction: cross-block kernels receive only an exponentially indexed mass-simplex formulation, not an efficient characterization or productization theorem."
  - "The higher-rank theorem's 'sharp finite-n additive trace-relaxation gap' is simply the difference between two computed optima rather than an analytic gap bound."
  - "Its polynomial support reduction is existential rather than algorithmic."
reusable_artifacts:
  - "discovery/core.json — proved heterogeneous-block productization theorem, exact local-LMI SDP, rank-one LP corollary, and explicit cross-block boundary."
  - "discovery/writeup.tex — rendered mathematical note and worked homogeneous two-class special case."
  - "discovery/d0_working.json — durable proof/prose overlay and adjudicated D0 history."
  - "reviews/review_general.json — final novelty assessment and scope limitations."
seeds_burned: []
proof_attempt_summary: |
  Discovery proved that, for heterogeneous finite centrally symmetric balanced block supports and a finite menu of centered block-diagonal PSD kernels, preserving local marginals and independently productizing blocks Pareto-dominates cross-block coupling and yields an exact polynomial-size local-LMI SDP. The mathematical result passed both D0.5 panels, but a human venue-level adjudication downgraded it because the decoupling mechanism is expected once direct-sum geometry is imposed and genuinely coupled kernels still require the exponential mass-simplex program. No Lean formalization was produced because the run was stopped immediately after F1 dispatch.
banked_on: "2026-08-05"
---

# exp_commitment_price_coupling / v1 — Downgraded

**Topic.** The minimax fraction of the oracle variance-reduction gain that a single committed randomization design can guarantee simultaneously across a finite family of unknown response-structure classes, and the design certified to attain it

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Sound exact block-diagonal productization and local-LMI reduction, but the expected decoupling mechanism, engineered direct-sum scope, and unresolved coupled-kernel case make this a subfield methodological note rather than a field-level paper.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The result is sound and reusable as a reduction lemma or methodological-note core. A field-tier successor should change the substantive frontier rather than repackage this proof: handle a meaningful coupled-kernel class, add a genuine inference contribution, or demonstrate a consequential advantage over Kallus/Gram--Schmidt-Walk designs in an applied design problem.
