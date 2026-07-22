---
qid: eid_proximal_did_bridge_frontier
spec: v2
topic: "New flagship topic: proximal difference-in-differences bridge frontier with negative controls. Pre-anchor check: closest published anchors are Miao-Geng-Tchetgen proximal causal inference, Tchetgen-Tchetgen negative-control bridge work, standard two-period and staggered DiD identification, and recent papers on difference-in-differences with negative controls. Our theorem is not those because the focal object is a finite pretrend-proxy bridge operator that sharply separates three regimes: ordinary parallel-trends DiD identifies ATT, proximal negative-control DiD identifies ATT even when parallel trends fails, and neither identifies ATT. Require a concrete nonroutine object: an explicit 2-group x 3-period x binary-proxy witness with observed negative-control outcome and exposure, a bridge-rank condition computed from pre-period moments, and a non-equivalence theorem showing the proximal bridge and parallel-trends restrictions are neither nested nor equivalent. If the proposal reduces to generic proximal completeness, ordinary DiD placebo tests, support coverage, or a definition-unfold rank condition without a worked witness and non-equivalence class, pivot or stop early."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Conjecture 1: C-wellposed — The four regimes are claimed to be open relative to a common positive-cell finite latent-type model, but the PT and bridge regimes are equality sets tau_PT=0 and rho_br=0; no model topology or component restriction is specified that makes those equality-defined regimes open.'
  - 'Theorem 2: C-wellposed — The theorem asserts existence of a positive-cell observed law and finite latent completion on the full locked 2x3 binary-proxy support, but Exhibit 9.1 displays only selected margins and means, not a complete joint finite law or latent cell table.'
  - 'Theorem 2: N-promissory-object — Exhibit 9.1 computes the bridge algebra, but the load-bearing tau_PT(P)=1/4 and theta_ATT=-1/20 are inserted as latent-completion values rather than exhibited by a full finite law from Section 6 primitives; Sigma(P) is therefore not fully computed from raw observed cells.'
  - 'Conjecture 1: N-no-concrete-witness — The generic open-regime claim has only a bridge-only Exhibit 9.1 witness; it does not exhibit concrete both, PT-only, and neither laws in the common finite support.'
  - 'proposal: N-no-named-focal-object — tier=field below novelty_target=flagship; Sigma(P) is a named signature, but the current contribution is a finite diagnostic packaging plus one witness, not a flagship-grade new identification target, estimator frontier, or published-comparator iff frontier.'
  - 'Theorem 1: C-coherence — Section 4 says Sigma(P) assigns every positive finite law to PT-only, bridge-only, both, or neither, but the Section 8 theorem excludes tau_PT from the observable computable components and the regime list omits rho_br=0 with kappa_br=0.'
  - 'Theorem 2: N-comparator-drift — The handoff maps ZhangZhangWangEtAl2025 and RambachanRoth2023 to Theorem 2 as strict tightening/non-representability, but the Section 8 theorem is only a rational bridge-only witness and is not phrased as a strict result against either published comparator.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Five angles over 11 reviewer rounds attempted to construct a finite regime signature Sigma(P) sharply separating parallel-trends-only, proximal-negative-control-only, and neither-identifies DiD regimes in a 2-group x 3-period x binary-proxy design. The exhibit-level bridge algebra (Exhibit 9.1) held—det(B_P)=1/2, Delta_br=-1/20—but the witness was repeatedly a single bridge-only table with latent-completion values inserted by hand rather than derived from raw observed cells, and the flagship non-nesting conjecture lacked witnesses for the PT-only, both, and neither regimes. The headline flagship kernel (a named-estimator non-equivalence frontier) was never established at above field tier across any angle; reviewers consistently found only a finite diagnostic packaging without an iff or published-comparator strict frontier.
banked_on: "2026-05-27"
---

# eid_proximal_did_bridge_frontier / v2 — Failed

**Topic.** New flagship topic: proximal difference-in-differences bridge frontier with negative controls. Pre-anchor check: closest published anchors are Miao-Geng-Tchetgen proximal causal inference, Tchetgen-Tchetgen negative-control bridge work, standard two-period and staggered DiD identification, and recent papers on difference-in-differences with negative controls. Our theorem is not those because the focal object is a finite pretrend-proxy bridge operator that sharply separates three regimes: ordinary parallel-trends DiD identifies ATT, proximal negative-control DiD identifies ATT even when parallel trends fails, and neither identifies ATT. Require a concrete nonroutine object: an explicit 2-group x 3-period x binary-proxy witness with observed negative-control outcome and exposure, a bridge-rank condition computed from pre-period moments, and a non-equivalence theorem showing the proximal bridge and parallel-trends restrictions are neither nested nor equivalent. If the proposal reduces to generic proximal completeness, ordinary DiD placebo tests, support coverage, or a definition-unfold rank condition without a worked witness and non-equivalence class, pivot or stop early.

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Five angles attempted on the proximal-DiD bridge frontier topic; tier ceiling never broke field across 11 reviewer verdicts. Per-angle decomposition: 4 of 5 angles killed by C-sanity arithmetic errors (proposer cannot reliably solve elementary minimax/linear-system problems on its own exhibit); separately, all 5 angles selected pairwise non-equivalence kernels which are structurally field-tier (no impossibility / sharp-efficiency / universal-characterization / dispute-resolution angle attempted). Topic kernel space is shallow at flagship tier; proposer kernel-shape rubric is the bigger lever for future runs.

## Key files

- `eid_proximal_did_bridge_frontier_v2_state.json` — pipeline state at banking (`banked: true`).
- `eid_proximal_did_bridge_frontier_v2_proposal.tex` — final proposal version.
- `eid_proximal_did_bridge_frontier_v2.tex` — derivation note (if Stage 0 ran).
- `eid_proximal_did_bridge_frontier_v2_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_proximal_did_bridge_frontier_v2_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
