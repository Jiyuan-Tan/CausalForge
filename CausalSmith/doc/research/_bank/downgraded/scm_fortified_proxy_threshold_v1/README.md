---
qid: scm_fortified_proxy_threshold
spec: v1
topic: "Critical valid-proxy count gamma_c for fortified proximal causal inference: for the discrete fortified-PCI model of Rakshit-Shi-Tchetgen Tchetgen (arXiv:2506.13152) with K candidate treatment proxies of cardinality m, latent confounder of cardinality u, and binary A, define gamma_c(K,m,u) as the least gamma at which, for the WORST-CASE valid set |alpha*|=gamma, some strictly positive law makes the finite pairing matrix M_gamma(P;alpha*) between Supply = H_gamma + L2(Z_comp) and Demand = L2(U,A,Z_comp) full rank, where H_gamma = {d in L2(Z,A) : E[d|Z_-alpha]=0 for all |alpha|=gamma}; conjecture (i) a GENERIC-RANK COUNTING LAW, rank M_gamma = min(dim Supply, t) generically so feasibility reduces to the arithmetic inequality D(K,m,gamma) >= u*2*m^(K-gamma) and gamma_c is a decidable arithmetic threshold (closed form for D delegated); (ii) a UNIVERSAL-OVER-LAWS IMPOSSIBILITY, that below gamma_c fortified completeness fails at EVERY law so the anchor's Theorem 1 outcome-bridge route is inapplicable for the entire model class (the model-wide converse and the Assumption-7 dual threshold delegated); and (iii) a FINITE POLYNOMIAL-PROGRAM FORMULATION of the sub-threshold sharp identified set for the ATE via the canonical response-function reduction, with linear objective and cell-matching equalities, degree-2 conditional-independence equalities per fixed alpha*, and the union over valid sets discharged by min/max enumeration over the feasible family V_feas -- resolving whether the fortified robustness level an applied analyst is willing to defend can identify the ATE at all, which arXiv:2506.13152 leaves as an unguarded sensitivity sweep over gamma"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The delivered result remains a narrow companion theorem rather than a field-level contribution."
  - "Nonnegative slack guarantees only that some compatible law is injective and that failure is exceptional in latent factor-table coordinates, not that the pairing holds for a given substantive law or that it can be checked from observed data."
  - "Extend the weighted-dimension and compatible-minor arguments to coordinate-specific proxy cardinalities and fixed support patterns with structural zeros, deriving a support-pattern-specific necessary-and-sufficient generic-rank condition instead of assuming common cardinality and full-cell support."
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/core.json
  - discovery/solve_oeq_compatible_minor_attainment.json
  - discovery/proto_core.json
seeds_burned: []
proof_attempt_summary: |
  D0 fully proved the weighted-array dimension formula, the universal negative-slack obstruction,
  and the converse compatible-minor construction, yielding an exact all-gamma feasibility threshold
  with generic attainment; the math and decision referees passed the compiled paper. The general
  referee assessed the equal-cardinality full-cell result at subfield tier, below the requested field
  floor. A field-tier lift remains as a separate structural-zero support-pattern project requiring
  support-hypergraph/matching and algebraic-matroid machinery.
banked_on: "2026-07-22"
---

# scm_fortified_proxy_threshold / v1 — Downgraded

**Topic.** Critical valid-proxy count gamma_c for fortified proximal causal inference: for the discrete fortified-PCI model of Rakshit-Shi-Tchetgen Tchetgen (arXiv:2506.13152) with K candidate treatment proxies of cardinality m, latent confounder of cardinality u, and binary A, define gamma_c(K,m,u) as the least gamma at which, for the WORST-CASE valid set |alpha*|=gamma, some strictly positive law makes the finite pairing matrix M_gamma(P;alpha*) between Supply = H_gamma + L2(Z_comp) and Demand = L2(U,A,Z_comp) full rank, where H_gamma = {d in L2(Z,A) : E[d|Z_-alpha]=0 for all |alpha|=gamma}; conjecture (i) a GENERIC-RANK COUNTING LAW, rank M_gamma = min(dim Supply, t) generically so feasibility reduces to the arithmetic inequality D(K,m,gamma) >= u*2*m^(K-gamma) and gamma_c is a decidable arithmetic threshold (closed form for D delegated); (ii) a UNIVERSAL-OVER-LAWS IMPOSSIBILITY, that below gamma_c fortified completeness fails at EVERY law so the anchor's Theorem 1 outcome-bridge route is inapplicable for the entire model class (the model-wide converse and the Assumption-7 dual threshold delegated); and (iii) a FINITE POLYNOMIAL-PROGRAM FORMULATION of the sub-threshold sharp identified set for the ATE via the canonical response-function reduction, with linear objective and cell-matching equalities, degree-2 conditional-independence equalities per fixed alpha*, and the union over valid sets discharged by min/max enumeration over the feasible family V_feas -- resolving whether the fortified robustness level an applied analyst is willing to defend can identify the ATE at all, which arXiv:2506.13152 leaves as an unguarded sensitivity sweep over gamma

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5.G: delivered tier=subfield below floor=field; the exact equal-cardinality full-cell Assumption-5 pairing theorem is a narrow companion result, and the field-tier structural-zero lift requires a genuinely new support-hypergraph/matroid project.

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
