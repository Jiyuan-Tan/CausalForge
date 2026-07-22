---
qid: pid_dynamic_iv_compliance
spec: v3
topic: "Partial identification of dynamic treatment effects under non-Markov assignments and imperfect compliance"
novelty_target: flagship
supersedes:
  parent_qid: "pid_dynamic_iv_compliance"
  parent_spec: "v2"
  parent_tier: "candidates"  # tier retired 2026-07-18; parent re-tiered to _bank/downgraded/
  upgrade_axis: "generalization"
tier_at_proposal: ACCEPT
tier_at_derivation: ACCEPT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Novelty objection capped the tier at subfield (below the flagship floor).
  # Verbatim / near-verbatim reviewer phrases from pid_dynamic_iv_compliance_v3_reviews.jsonl:
  - "The positive theorem is essentially the standard finite latent-response/LP sharpness construction after defining the identified set by the same feasible set, and the negative result refutes the note's own proposed prism rather than a named published estimator/workflow."
  - "This is standard finite-response LP sharpness machinery in the Balke-Pearl/Manski class, not a new flagship bound or a closed-form sharp characterization."
  - "Because no specific published target is named, a counterexample to the prism cannot be accepted as flagship; because the witness is a single hand-built one-cell numerical instance rather than a generic-class obstruction, it would be capped at subfield even if a target were named."
  - "The prism refutation targets the note's own motivating conjecture, not a specific published paper, estimator, or workflow using the refuted prism, so the negative-result novelty standard is not met."
  - "The novelty is modest but theorem-level: the computable retained-memory LP and the correction of the three-coordinate prism." (accept @ tier_at_derivation=subfield)
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed a sharp partial-identification bound for dynamic LATE-type effects under
  bounded first-stage defiers ("retained-memory bounded-defier" finite LP), generalizing
  parent v2's no-defier corner, plus a negative result correcting a "three-coordinate prism"
  relaxation. After REVISE x2 the math was ACCEPTED (D0.5 attempt 3): the LP is explicit and
  computable, the atom-completion sharpness proof and counterexample arithmetic (-3/5 relaxed,
  -7/40 full LP) all check out. Tier was capped at subfield, not the flagship target: reviewers
  judged the positive theorem standard Balke-Pearl/Manski/Duarte finite-response LP machinery
  and the negative result a refutation of the note's own prism, not a named published estimator.
  Math sound; only the novelty claim was overstated — re-raise at corrected (subfield) tier.
banked_on: "2026-05-15"
---

# pid_dynamic_iv_compliance / v3 — Downgraded

**Topic.** Partial identification of dynamic treatment effects under non-Markov assignments and imperfect compliance

**Novelty target.** flagship

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D-0.5 ACCEPT at flagship (upgrade flag worked end-to-end). D0.5 ACCEPT at tier=subfield after REVISE x2 → ACCEPT x1 — but tier-floor directive was missing from the prompt (resume bug: noveltyTarget not recovered from state.proposed_from), so reviewer freely ACCEPT'd below original flagship floor. Math sound; would re-run with the noveltyTarget recovery fix to test whether the kernel can actually clear flagship.

**Supersedes.** pid_dynamic_iv_compliance_v2 (tier=candidates, upgrade_axis=generalization). The parent now lives in `_bank/downgraded/` (the `candidates` tier was retired 2026-07-18 and the parent re-graded subfield) and remains an independent reference; this entry is the flagship upgrade.

## Key files

- `pid_dynamic_iv_compliance_v3_state.json` — pipeline state at banking (`banked: true`).
- `pid_dynamic_iv_compliance_v3_proposal.tex` — final proposal version.
- `pid_dynamic_iv_compliance_v3.tex` — derivation note (if D0 ran).
- `pid_dynamic_iv_compliance_v3_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_dynamic_iv_compliance_v3_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
