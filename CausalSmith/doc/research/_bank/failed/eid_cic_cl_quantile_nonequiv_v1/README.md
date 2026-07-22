---
qid: eid_cic_cl_quantile_nonequiv
spec: v1
topic: "Sharp non-equivalence between Athey-Imbens 2006 changes-in-changes and Callaway-Li 2019 group-time quantile estimators for the QTT under staggered adoption with heterogeneous treatment-timing distributions, exhibiting a concrete moment of the timing distribution at which the two estimators have opposite asymptotic sign and recovering joint point identification of the QTT under timing homogeneity"
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Conjecture 1: C-wellposed — The timing-skew moment is not well-posed as a nonzero panel quantity: omega_{h|g,t}=Pr(G=h|G in R_{g,t}) and the baseline omega^0 over the same fixed risk-set cohorts coincide in the stated balanced panel law, making M identically zero.'
  - 'Conjecture 2: C-sanity — The §9 witness requires current weights (1/2+eta,1/2-eta) and baseline weights (1/2,1/2), which cannot both arise from the fixed-G risk-set definition; even ignoring that, the displayed formula does not yield M=2a eta under the stated summand.'
  - 'Conjecture 2 / Example 1: C-sanity — The displayed median cells give weighted level-scale CL aggregate 0.25*(3-1)+0.5*(1-8)+0.25*(3-1) = -2, not Delta_CL_id(1/2)=1/4, so the claimed witness reduction arithmetic fails.'
  - 'Conjecture 2 / Example 1: C-sanity — Using Definition 1, the claimed S_{y^2}(P;1/2)=-7 is not obtained from the displayed q/Q cells; the stated eta*K>M margin is therefore not certified by the sanity check.'
  - 'Theorem 1: C-sanity — Coincidence of local transports only on I_tau supports at most a local tau-quantile equality, not equality of the full CDFs at every continuity point.'
  - 'Conjecture 2 (angle 2): C-sanity — The proposed sign-changing support-function correction conflicts with W_stag(a;P)=h_prod(a;P)-h_stag(a;P)>=0 for every fixed direction because R_stag(P) is defined as a subset of the product relaxation.'
  - 'Theorem 1 (angle 0): published_prior_art verdict=incremental — AtheyImbens2006 and CallawayLi2019 supply the two counterfactual maps; the local equality bridge is routine and not a flagship novelty.'
  - 'Theorem 1 (angle 2): published_prior_art verdict=already-known — FanYu2012/FanPark2010: cellwise Makarov-style bounds from identified marginals.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal attempted a Gateaux-linearized Bacon-style decomposition for staggered CIC and Callaway-Li QTT maps, with a quantile contamination index B_tau(P) designed to detect an open class where the two estimator directions have opposite asymptotic sign. Across three angles, the flagship Conjecture 1 (the contamination index and sign-reversal claim) collapsed at every revision: the timing-skew moment M was shown to be identically zero under the stated balanced panel risk-set definition (angle 0), the finite-support witness arithmetic was numerically wrong in both angles 0 and 1, and the partial-ID angle (angle 2) had an internally contradictory support-function correction claim. No angle reached a sound, non-incremental conjecture at the center of the proposal; Theorem 1 (level CDF equality under timing homogeneity) was consistently rated incremental, and Conjectures 1 and 2 failed well-posedness or sanity checks on every attempt.
banked_on: "2026-05-22"
---

# eid_cic_cl_quantile_nonequiv / v1 — Failed

**Topic.** Sharp non-equivalence between Athey-Imbens 2006 changes-in-changes and Callaway-Li 2019 group-time quantile estimators for the QTT under staggered adoption with heterogeneous treatment-timing distributions, exhibiting a concrete moment of the timing distribution at which the two estimators have opposite asymptotic sign and recovering joint point identification of the QTT under timing homogeneity

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -0.5 rejected every angle: codex revise-dilution collapsed v1 field-tier kernels to v2 not-publishable on both angles 0 and 1; Claude attempt (separate branch) hit math errors (cov over infinity, undefined operators, fabricated arXiv cite). Topic shape resists flagship under either proposer; field-tier reachable but flagship gap appears structural to the framing.

## Key files

- `eid_cic_cl_quantile_nonequiv_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_cic_cl_quantile_nonequiv_v1_proposal.tex` — final proposal version.
- `eid_cic_cl_quantile_nonequiv_v1.tex` — derivation note (if Stage 0 ran).
- `eid_cic_cl_quantile_nonequiv_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_cic_cl_quantile_nonequiv_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
