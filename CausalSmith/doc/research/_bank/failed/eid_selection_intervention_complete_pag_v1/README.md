---
qid: eid_selection_intervention_complete_pag
spec: v1
topic: "Complete SI-PAG orientation under selection and unknown-target interventions. On finite causally sufficient DAGs in Dai et al.'s full published pre-treatment-selection interventional-twin-graph compatibility class, with observational and unknown-target soft-intervention regimes supplied as oracle regime MAGs, define the canonical SI-PAG by endpoint-mark invariance over the entire class. Give a finite sound within- and cross-regime orientation calculus whose monotone mark closure terminates after polynomially many endpoint updates, prove mark completeness by showing closure equals the canonical SI-PAG and every residual circle has two compatible orientation witnesses, and derive a complete population CDIS algorithm on the same class. Do not claim polynomial conditional-independence discovery. Use Dai et al.'s two-variable equivalence witness and sciPlex2/A549 workflow, and distinguish Jaber's no-selection theory and Luo et al.'s post-treatment-selection F-PAG."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The polynomial closure lemma is conditional on an unspecified fixed rule system, while construction and semantic completeness of that system remain entirely open in oeq:si-extension-calculus."
  - "The finite target-residual certificate results already establish an exact global answer, but not the requested fixed local calculus."
  - "The exact result is a global certificate search, not a complete polynomial local orientation calculus."
reusable_artifacts:
  - "discovery/core.json — exact finite common-realization certificate formulation, target residualization, and paired endpoint-witness graph."
  - "discovery/writeup.tex — proved exponential global enumerator, sparse input-conditioned quotient, and explicit local-calculus boundary."
  - "discovery/proof_archive/ — retained proof attempts for the selection two-section quotient, checker characterization, and two-variable ambiguity witness."
seeds_burned: []
proof_attempt_summary: |
  Discovery replaced arbitrary selection hypergraphs by an exact finite certificate and derived a sound exponential global enumerator with paired compatible witnesses. The attempt collapsed at the frozen headline: it never constructed the fixed local rule list or proved its common-basal mark completeness, and instead stated that requirement as an open obligation. A future retry may reuse the certificate machinery, but fulfilling this topic still requires the missing local SI-calculus theorem rather than relabeling the enumerator.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 51492847
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-08-29"
---

# eid_selection_intervention_complete_pag / v1 — Failed

**Topic.** Complete SI-PAG orientation under selection and unknown-target interventions. On finite causally sufficient DAGs in Dai et al.'s full published pre-treatment-selection interventional-twin-graph compatibility class, with observational and unknown-target soft-intervention regimes supplied as oracle regime MAGs, define the canonical SI-PAG by endpoint-mark invariance over the entire class. Give a finite sound within- and cross-regime orientation calculus whose monotone mark closure terminates after polynomially many endpoint updates, prove mark completeness by showing closure equals the canonical SI-PAG and every residual circle has two compatible orientation witnesses, and derive a complete population CDIS algorithm on the same class. Do not claim polynomial conditional-independence discovery. Use Dai et al.'s two-variable equivalence witness and sciPlex2/A549 workflow, and distinguish Jaber's no-selection theory and Luo et al.'s post-treatment-selection F-PAG.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@oeq:si-extension-calculus: the delivered exponential global certificate enumerator explicitly leaves the frozen topic’s finite complete local SI orientation calculus open.

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
