---
qid: exp_design_pm1_exactness_boundary_v1
spec: experimentation
topic: "Sharp +-1 implementability of the interference-homophily experimental design SDP (anchor: Optimal Design under Interference, Homophily, and Robustness Trade-offs, arXiv:2601.17145). For the Horvitz-Thompson GATE worst-case-MSE design objective gamma*Tr(LX)+eta*Tr(L_dagger X)+kappa*||X||_q over the elliptope {X>=0, diag(X)=1}, the realizable randomized +-1 designs are a strict subset (cut-polytope-like +-1 second moments), so the anchor's Gaussian (Goemans-Williamson) rounding gives only a ONE-SIDED approximation-ratio certificate. Open: characterize when a feasible +-1 design ATTAINS the relaxation optimum. Deliver, for a named non-trivial graph family (regular graphs / two-community SBM with homophily): (1) the +-1-EXACTNESS region in (graph, eta/gamma, kappa) where a feasible randomized design attains the elliptope-relaxation optimum exactly (cut-aligned design in the pure-cut regime gamma>>eta; balanced-Bernoulli in the robustness regime large kappa), proving the boundary is NOT merely cut-polytope membership; (2) the critical eta/gamma threshold where exactness BREAKS and a strictly positive rounding loss appears, as a family-specific scalar; (3) a family-specific tight (or one-sided-sharp) rounding-loss certificate rho* bounding the price of +-1 implementability, recasting the cut-vs-spread transition as an implementability-gap phase structure. Motif M13 (optimal/chosen design with optimality certificate); the design covariance X is the decision variable; deliverable is the feasible-design optimum + exactness boundary + rounding-loss certificate, NOT inference given a fixed design."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  # TODO: paste verbatim reviewer phrases identifying which Conjecture
  # collapsed and why. Source: exp_design_pm1_exactness_boundary_v1_experimentation_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.
banked_on: "2026-07-02"
paper_score: 4.2
paper_score_rationale: "The verified mathematics appears coherent and exact, but the submission is too narrow and too weakly connected to econometric design or inference to earn publication in a leading econometrics journal as written."
---

# exp_design_pm1_exactness_boundary_v1 / experimentation — Accepted

**Topic.** Sharp +-1 implementability of the interference-homophily experimental design SDP (anchor: Optimal Design under Interference, Homophily, and Robustness Trade-offs, arXiv:2601.17145). For the Horvitz-Thompson GATE worst-case-MSE design objective gamma*Tr(LX)+eta*Tr(L_dagger X)+kappa*||X||_q over the elliptope {X>=0, diag(X)=1}, the realizable randomized +-1 designs are a strict subset (cut-polytope-like +-1 second moments), so the anchor's Gaussian (Goemans-Williamson) rounding gives only a ONE-SIDED approximation-ratio certificate. Open: characterize when a feasible +-1 design ATTAINS the relaxation optimum. Deliver, for a named non-trivial graph family (regular graphs / two-community SBM with homophily): (1) the +-1-EXACTNESS region in (graph, eta/gamma, kappa) where a feasible randomized design attains the elliptope-relaxation optimum exactly (cut-aligned design in the pure-cut regime gamma>>eta; balanced-Bernoulli in the robustness regime large kappa), proving the boundary is NOT merely cut-polytope membership; (2) the critical eta/gamma threshold where exactness BREAKS and a strictly positive rounding loss appears, as a family-specific scalar; (3) a family-specific tight (or one-sided-sharp) rounding-loss certificate rho* bounding the price of +-1 implementability, recasting the cut-vs-spread transition as an implementability-gap phase structure. Motif M13 (optimal/chosen design with optimality certificate); the design covariance X is the decision variable; deliverable is the feasible-design optimum + exactness boundary + rounding-loss certificate, NOT inference given a fixed design.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Sharp pm-1 implementability of the two-community homophily worst-case-MSE design SDP: closed-form rounding-loss certificate rho_star = Delta_m^pm via active-set SOCP over the reduced triangle T_m, cut/iid exact corners, odd-m positive-gap window with parity necessity; exact frontier r_star left open.

## Key files

- `exp_design_pm1_exactness_boundary_v1_experimentation_state.json` — pipeline state at banking (`banked: true`).
- `exp_design_pm1_exactness_boundary_v1_experimentation_proposal.tex` — final proposal version.
- `exp_design_pm1_exactness_boundary_v1_experimentation.tex` — derivation note (if Stage 0 ran).
- `exp_design_pm1_exactness_boundary_v1_experimentation_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `exp_design_pm1_exactness_boundary_v1_experimentation_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
