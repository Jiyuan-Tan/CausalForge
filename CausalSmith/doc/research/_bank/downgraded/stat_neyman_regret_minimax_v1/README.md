---
qid: stat_neyman_regret_minimax
spec: v1
topic: "First matching minimax LOWER bound for Neyman regret in adaptive two-arm experiments, resolving the open problem of Dai et al. (arXiv:2411.14341 Logarithmic Neyman Regret): they prove the upper bound R_T <= O~(f(pi*) log T) for the Clipped-Second-Moment-Tracking design but prove no matching lower bound. Establish the minimax lower bound over bounded-outcome adaptive two-arm instances via a change-of-measure / epoched two-point (Le Cam) construction tying detection-time of the unknown second moments to accumulated quadratic Neyman loss V(pi_t)-V(pi*), pinning the SHARP minimax Neyman-regret rate (accumulated variance-inefficiency of the adaptive Horvitz-Thompson ATE estimator vs the oracle Neyman allocation pi*=S1/(S0+S1)); exact overlap dependence determined by the lower-bound proof, not fixed in advance. Distinct from simple-regret/best-arm minimax (arXiv:2309.08808, 2512.08513) which concern chosen-arm welfare, not estimator variance-suboptimality."
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: yes
reraise_status: re-raise
gap_reasons:
  - "F2.5 faithfulness reviewer [scaffold-mismatch]: 'The note (lem:local-neighborhood-cumulative-risk) DERIVES the b_t recursion, the R_T^B >= 2S^2 B_T conversion, and sup >= R_T^B in its proof_tex; the Lean scaffold laundered them into an assumed hypothesis. Fix: derive these from the abstract van Trees gate + neyman-gap-identity/quadratic-loss-expansion, or narrow the gate to only the genuinely-classical Fisher-information-of-sequential-likelihood additivity — do not assume the paper's derived recursion.'"
  - "Root cause: the sequential van Trees converse engine needs differentiation-in-quadratic-mean (DQM) + sequential-Fisher-information tensorization for the predictable Bernoulli adaptive joint law, absent from Mathlib/Causalean (research-scale substrate; confirmed twice by independent gpt-5.5 feasibility+build passes). NOT a math error — the D0 writeup proof is complete and sound; the gap is formalization-substrate reachability (F1.5-level, not D0.5)."
reusable_artifacts:
  - "CERTIFIED gate-free core (sorry-free, axiom-clean {propext,Classical.choice,Quot.sound}), all under CausalSmith/Stat/STAT_NeymanRegretMinimax_Research/: neyman_gap_identity (Helpers/NeymanAlgebra.lean), cumulative_risk_engine_uniform_threshold + Causalean.Stat.Limit.sequential_cumulative_risk_regret (recursion->Omega(log T) harmonic engine), diagonal_rayleigh_sSup + lem:local-complexity-rayleigh (kappa_nu closed form), band_continuity_for_linear_tilts (tilt moment/tangent continuity, DERIVED), MTan/MBand class + armScoreCost/localInformation score program."
  - "Built Causalean substrate (0-sorry, root-wired): Stat/Limit/VanTreesInequality.lean (van_trees_inequality), Stat/Limit/SequentialCumulativeRisk.lean, Stat/Nonparametric/{MomentEnvelope,L2ResidualQuadratic}.lean, Substrate/{ConstrainedQuadraticScoreProgram,KlDensityTiltExpansion}."
  - "CONDITIONAL converse (compiles sorry-free on the broad LocalNeighborhoodRiskInputs gate, docstring-marked NOT CERTIFIED): instance_local_minimax, global_log_rate, local_neighborhood_cumulative_risk. Re-certify by narrowing the gate to the classical van Trees/Fisher-tensorization core + deriving recursion/domination/sup (needs DQM substrate)."
seeds_burned: []
proof_attempt_summary: |
  First Omega(log T) minimax LOWER bound for adaptive superpopulation Horvitz-Thompson cumulative Neyman regret (resolving the open converse of Neopane-Ramdas-Singh 2024 / Noarov et al. 2025). The D0 math is complete and sound; the novel apparatus (kappa_nu curvature-information complexity, the tangent-regular class, the local->global lift, the recursion->log T accumulation) is fully machine-verified sorry-free. The one irreducible piece — the sequential van Trees / Fisher-tensorization converse engine — needs DQM substrate absent from Mathlib. Threading the whole reduction as one hypothesis was caught by F2.5 as laundering the derived recursion/domination/sup, so the CERTIFIED bank is restricted to the gate-free core; the full converse stays as a documented conditional extension. Re-raise once the DQM/sequential-Fisher substrate is built.
banked_on: "2026-07-05"
---

# stat_neyman_regret_minimax / v1 — Downgraded

**Topic.** First matching minimax LOWER bound for Neyman regret in adaptive two-arm experiments, resolving the open problem of Dai et al. (arXiv:2411.14341 Logarithmic Neyman Regret): they prove the upper bound R_T <= O~(f(pi*) log T) for the Clipped-Second-Moment-Tracking design but prove no matching lower bound. Establish the minimax lower bound over bounded-outcome adaptive two-arm instances via a change-of-measure / epoched two-point (Le Cam) construction tying detection-time of the unknown second moments to accumulated quadratic Neyman loss V(pi_t)-V(pi*), pinning the SHARP minimax Neyman-regret rate (accumulated variance-inefficiency of the adaptive Horvitz-Thompson ATE estimator vs the oracle Neyman allocation pi*=S1/(S0+S1)); exact overlap dependence determined by the lower-bound proof, not fixed in advance. Distinct from simple-regret/best-arm minimax (arXiv:2309.08808, 2512.08513) which concern chosen-arm welfare, not estimator variance-suboptimality.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Certified core banked (gate-free, sorry-free, axiom-clean: kappa_nu closed form, neyman_gap_identity, recursion-to-Omega(log T) engine, derived band continuity, class/score construction); full Omega(log T) converse kept as CONDITIONAL extension on the broad LocalNeighborhoodRiskInputs gate (F2.5 flagged it as laundering the note's derived recursion/domination/sup), documented not certified.

## Key files

- `stat_neyman_regret_minimax_adaptive two-arm experiment; first matching minimax lower bound pinning the sharp minimax Neyman-regret rate_state.json` — pipeline state at banking (`banked: true`).
- `stat_neyman_regret_minimax_adaptive two-arm experiment; first matching minimax lower bound pinning the sharp minimax Neyman-regret rate_proposal.tex` — final proposal version.
- `stat_neyman_regret_minimax_adaptive two-arm experiment; first matching minimax lower bound pinning the sharp minimax Neyman-regret rate.tex` — derivation note (if Stage 0 ran).
- `stat_neyman_regret_minimax_adaptive two-arm experiment; first matching minimax lower bound pinning the sharp minimax Neyman-regret rate_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_neyman_regret_minimax_adaptive two-arm experiment; first matching minimax lower bound pinning the sharp minimax Neyman-regret rate_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
