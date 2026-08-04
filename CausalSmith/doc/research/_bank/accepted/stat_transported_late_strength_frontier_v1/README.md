---
qid: stat_transported_late_strength_frontier
spec: v1
topic: "effective identification strength and the matched minimax confidence-set-length frontier for the transported complier average causal effect: in the two-sample generalizability-with-noncompliance model of Chen-Huang arXiv:2506.00149 (n study draws of (X,Z,D,Y) with Y in [0,1], D and Z binary, propensity in [eps,1-eps], exclusion, monotonicity, cross-population conditional exchangeability, plus N target-population covariate draws, N/n -> c), with estimand theta_T = E_T[Delta_Y(X)]/E_T[Delta_D(X)] whose parameter space Theta = [-1,1] is FORCED compact by bounded Y and binary D, fix an envelope k_n -> infinity with k_n = o(n^(1/2)) and define the class by E_S[w]=1, w <= 2k_n a.s. and kappa_n = E_S[w^2] <= k_n, the Kish effective sample size n_eff = n/kappa_n, and the effective identification strength t_n = n_eff * mu_n^2 = n mu_n^2/kappa_n where mu_n = E_T[Delta_D(X)] is the transported first stage and both mu_n -> 0 and kappa_n -> infinity are permitted at arbitrary joint rates; calling a procedure SEQUENCE honest when liminf_n inf_P P(theta_T in C_n) >= 1-alpha and setting R(C,t_0) = limsup_n sup over {t_n >= t_0} of E_P[lambda(C_n)] and V*(t_0) = inf over honest (w,e)-oracle sequences of R(C,t_0), prove (K1) the converse V*(t_0) >= c min(1,t_0^(-1/2)) against oracles told w and e but NOT Delta_D or Delta_Y, with c depending only on alpha and the class constants and not on how t_0 splits into a first-stage/dispersion pair, hence a threshold t_c(alpha) below which every honest procedure is uninformative, and (K2) matched attainment by a single honest sequence from grid inversion over Theta of level-alpha tests of the transported moment restriction, achieving R(C,t_0) <= C min(1,t_0^(-1/2)) simultaneously for all t_0 - so the joint weak-first-stage and weak-overlap difficulty depends on (n,mu_n,kappa_n) ONLY through t = n mu_n^2/kappa_n and generalization-weight dispersion costs exactly a Kish sample-size deflation and no more - and (K3) that the same order is attained WITHOUT knowing the transport weight on the finite-cell sub-class N_n (X in a known {1,...,k_n}, P_S the known uniform law, e a known constant, only the cell vector P_T unknown, Delta_D and Delta_Y unrestricted), where K1 already holds; the test statistic and its calibration, all constants including c, C and t_c(alpha), the studentization, the bounded/unbounded/disconnected shape taxonomy, and every extension of K3 beyond N_n are explicitly DELEGATED and not pre-committed; well-posedness rests on Theta = [-1,1] being forced rather than chosen, which is exactly the infinite-diameter hypothesis the Dufour 1997 / Gleser-Hwang 1987 / Bertanha-Moreira impossibility requires and which fails here, and the literature contains no finite minimax length rate under weak identification at all; distinct from Aronow-Chang-Lopatto Biometrika 2026 (finite-population LATE, no reweighting), from Ma arXiv:2302.09756 and Smucler et al arXiv:2506.10449 (single-population weak-IV-robust LATE with ML nuisances, no covariate shift, no length theorem), and from Ren arXiv:2512.23854 (within-population MTE extrapolation on a strong-overlap space); witness: X uniform on {1,...,k_n} under P_S, P_T mass 1-eps_n on cell k_n, e = 1/2, complier probability 1/2 off the last cell and eps_n on it, no defiers, compliers with (Y(1),Y(0)) = (1,0), giving E_S[w] = 1 exactly, kappa_n <= k_n, study first stage -> 1/2 but mu_n of order (3/2)eps_n -> 0, and t_n of order (9/4) n eps_n^2/k_n tunable to any t_0; consumers are the anchor's own deep-canvassing application, Rudolph and van der Laan JRSS-B 2017 transporting the Moving to Opportunity complier effect, and Ross et al Epidemiology 2026"
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "None: the run was accepted at field novelty tier and all seven banked headline results passed the dual F4 review and F5 clean gates."
reusable_artifacts:
  - "Causalean/Stat/Minimax/HonestConfidenceSet.lean"
  - "Causalean/Stat/Inference/AffineInversion.lean"
seeds_burned: []
proof_attempt_summary: |
  The run proved the compact transported-CACE range, the oracle and fixed-geometry
  two-sided confidence-set-length frontiers, oracle score-inversion attainment,
  finite- and regular-cell unknown-weight attainment, and the no-shift reduction.
  Formalization required explicit inhabited-class witnesses and measurable cell
  atoms, after which all seven headline results passed independent proof review,
  full Lean verification, and axiom audits; no conjecture collapsed.
banked_on: "2026-08-02"
paper_score: 7
paper_score_rationale: "The verified core results are interesting and plausibly publishable, but the manuscript still needs substantial expository repair around result typing, contribution scope, and finite-cell assumptions before it reads like a journal submission."
---

# stat_transported_late_strength_frontier / v1 — Accepted

**Topic.** effective identification strength and the matched minimax confidence-set-length frontier for the transported complier average causal effect: in the two-sample generalizability-with-noncompliance model of Chen-Huang arXiv:2506.00149 (n study draws of (X,Z,D,Y) with Y in [0,1], D and Z binary, propensity in [eps,1-eps], exclusion, monotonicity, cross-population conditional exchangeability, plus N target-population covariate draws, N/n -> c), with estimand theta_T = E_T[Delta_Y(X)]/E_T[Delta_D(X)] whose parameter space Theta = [-1,1] is FORCED compact by bounded Y and binary D, fix an envelope k_n -> infinity with k_n = o(n^(1/2)) and define the class by E_S[w]=1, w <= 2k_n a.s. and kappa_n = E_S[w^2] <= k_n, the Kish effective sample size n_eff = n/kappa_n, and the effective identification strength t_n = n_eff * mu_n^2 = n mu_n^2/kappa_n where mu_n = E_T[Delta_D(X)] is the transported first stage and both mu_n -> 0 and kappa_n -> infinity are permitted at arbitrary joint rates; calling a procedure SEQUENCE honest when liminf_n inf_P P(theta_T in C_n) >= 1-alpha and setting R(C,t_0) = limsup_n sup over {t_n >= t_0} of E_P[lambda(C_n)] and V*(t_0) = inf over honest (w,e)-oracle sequences of R(C,t_0), prove (K1) the converse V*(t_0) >= c min(1,t_0^(-1/2)) against oracles told w and e but NOT Delta_D or Delta_Y, with c depending only on alpha and the class constants and not on how t_0 splits into a first-stage/dispersion pair, hence a threshold t_c(alpha) below which every honest procedure is uninformative, and (K2) matched attainment by a single honest sequence from grid inversion over Theta of level-alpha tests of the transported moment restriction, achieving R(C,t_0) <= C min(1,t_0^(-1/2)) simultaneously for all t_0 - so the joint weak-first-stage and weak-overlap difficulty depends on (n,mu_n,kappa_n) ONLY through t = n mu_n^2/kappa_n and generalization-weight dispersion costs exactly a Kish sample-size deflation and no more - and (K3) that the same order is attained WITHOUT knowing the transport weight on the finite-cell sub-class N_n (X in a known {1,...,k_n}, P_S the known uniform law, e a known constant, only the cell vector P_T unknown, Delta_D and Delta_Y unrestricted), where K1 already holds; the test statistic and its calibration, all constants including c, C and t_c(alpha), the studentization, the bounded/unbounded/disconnected shape taxonomy, and every extension of K3 beyond N_n are explicitly DELEGATED and not pre-committed; well-posedness rests on Theta = [-1,1] being forced rather than chosen, which is exactly the infinite-diameter hypothesis the Dufour 1997 / Gleser-Hwang 1987 / Bertanha-Moreira impossibility requires and which fails here, and the literature contains no finite minimax length rate under weak identification at all; distinct from Aronow-Chang-Lopatto Biometrika 2026 (finite-population LATE, no reweighting), from Ma arXiv:2302.09756 and Smucler et al arXiv:2506.10449 (single-population weak-IV-robust LATE with ML nuisances, no covariate shift, no length theorem), and from Ren arXiv:2512.23854 (within-population MTE extrapolation on a strong-overlap space); witness: X uniform on {1,...,k_n} under P_S, P_T mass 1-eps_n on cell k_n, e = 1/2, complier probability 1/2 off the last cell and eps_n on it, no defiers, compliers with (Y(1),Y(0)) = (1,0), giving E_S[w] = 1 exactly, kappa_n <= k_n, study first stage -> 1/2 but mu_n of order (3/2)eps_n -> 0, and t_n of order (9/4) n eps_n^2/k_n tunable to any t_0; consumers are the anchor's own deep-canvassing application, Rudolph and van der Laan JRSS-B 2017 transporting the Moving to Opportunity complier effect, and Ross et al Epidemiology 2026

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F5 clean: dual F4 reviewers matched all seven headline results; full Lean verification and axiom audits passed.

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
