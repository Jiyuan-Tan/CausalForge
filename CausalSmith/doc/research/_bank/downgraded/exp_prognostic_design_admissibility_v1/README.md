---
qid: exp_prognostic_design_admissibility
spec: v1
topic: "Design-stage minimax admissibility frontier for an external prognostic score of unknown quality. Finite population of n even units with FIXED potential outcomes; randomness is the assignment alone (design-based). Estimand SATE, estimator the design-unbiased difference-in-means, so with mu_i=(y_i(1)+y_i(0))/2 the exact risk is (4/n^2) mu' A_d mu where A_d=Cov_d(z). Design class D_n: all distributions on {z in {-1,+1}^n : sum z_i = 0} with E[z]=0, so A_d>=0, diag(A_d)=1, A_d*1=0; it contains complete randomization, every score-based stratified, matched-pair and rerandomization scheme, and all their mixtures. An external prognostic score, known for every unit BEFORE randomization and possibly miscalibrated or population-shifted, gives a fixed score subspace S (its score-derived span intersected with 1-perp), a PRIMITIVE known exactly at design time, with 1 <= dim S <= n-1. Score-quality class Y(rho,M;S) = {mu : ||mu||^2 = nM, ||P_S mu||^2 >= rho^2 ||mu||^2}; rho is UNKNOWN at design time (GSW JASA 2024 Sec 8: the analogous quantity 'cannot be directly observed or estimated in the design stage'). Determine V*(rho;S) := inf over d in D_n of sup over Y(rho,M;S) of mu' A_d mu, with an attaining design AND a matching converse over the full class D_n; and characterize the admissibility dichotomy A_n := {S : V*(rho;S) < V_CRD(rho;S) for some rho < 1} together with the threshold rho*(S) := inf{rho : V*(rho;S) < V_CRD(rho;S)} (=1 off A_n), including whether that characterization is computable from the score matrix alone. Also determine the finite-n additive regret R*(n,S) of a single design chosen without knowing rho. The unindexed minimax is degenerate (GSW Prop 4.2; Kapelner JSPI 2022 Sec 3.1); the score-quality indexing is what makes it nondegenerate. Exact enumerated witnesses: at n=8 with the pair-partition S, the matched-pair design has risk exactly 1.75x complete randomization on a legal mu that varies within pairs and risk 0 on one constant within pairs, so V*(1;S)=0<V_CRD(1;S)=4/7 and S is in A_n; and S=1-perp is NOT in A_n because trace n on an (n-1)-dimensional space forces lambda_max >= n/(n-1) with equality only at complete randomization. Functional forms, the value of rho*(S), the attaining design (pure or mixed), and any asymptotic formulation are delegated."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "HALTED AT F2 BY OPERATOR DECISION, not by a failed theorem. The math is sound and D0.5 passed at the field floor; projected paper score was below the 7.5 bar, so the run was stopped rather than formalized to F5."
  - "Delivery thin relative to framing: the only genuinely new kernel is thm:admissibility-frontier (gamma(S) = U(diag P_S) via Gram completion / polygon inequality, plus the sharp floor gamma(S) >= dim(S)/(n-1) with its equal-leverage equality case)."
  - "gamma(S) is a FIRST-ORDER SLOPE at c_n P_H, so rho > rho*(S) certifies only that some strictly positive, possibly infinitesimal, improvement over complete randomization exists; the gain is never quantified for general S."
  - "The regret headline is a bracket with multiplicative slack p/(n-1), loosest (a factor n-1) exactly at p=1 — the single external prognostic score that motivates the paper — and both endpoints involve kappa(S), which requires exponential enumeration, so the certificates are not score-matrix computable."
  - "Closed forms exist only for unequal two-block and homogeneous even-block subspaces, i.e. the classical stratified / matched-pair geometries; thm:exact-pair-space-regret is a specialization of lem:pair-space-exact-frontier and adds nothing."
  - "The mixed-design minimax architecture is Kallus (2018, 2021 Sec. 5); the delta is the non-ellipsoidal score-energy shell and the leverage-only threshold inside it."
  - "NOTE ON proposal_promise_gap: `kernel_substituted` is auto-parsed from the SUPERSEDED D0.5.G attempt-4 revise round (delivered tier subfield < field floor). A later round cleared it — the final review returns tier=field, meets_floor=true. Do not read the banked artifact as kernel-substituted."
reusable_artifacts:
  - "discovery/core.json + discovery/writeup.tex — full derivation; thm:admissibility-frontier and its Gram-completion/polygon proof are the reusable kernel."
  - "CausalSmith/Experimentation/EXP_PrognosticDesignAdmissibility_Research/ — 27 Lean files, ~1731 lines, F2 scaffold with 7 sorries. NOT in the CausalSmith.lean root import graph and untracked; see UNVERIFIED note below."
  - "lean_scratch/ — Lean scratch moved out of the package tree so it cannot enter the find-derived full-tree sweep (Main.lean 170 lines, ExtremeProbe.lean, three build logs)."
  - "Worked witnesses at n=4 (S_pair gamma=1/3, S_mid 8/9, S_out 1) and the n=8 counterexample where matched pairs is 1.75x worse than complete randomization on a within-pair-varying mean vector."
seeds_burned: []
proof_attempt_summary: |
  Proved a leverage-only admissibility threshold for design-stage use of an external
  prognostic score: gamma(S) = min{lambda_max(K|H_n) : K1=0, diag K = diag P_S} equals a
  one-dimensional feasibility search U(diag P_S), via a Gram completion whose existence is
  the polygon inequality on the square-root diagonal slack; S is admissible iff gamma(S) < 1,
  and then rho*(S) = sqrt(gamma(S)) >= sqrt(dim(S)/(n-1)). Nothing collapsed — the run was
  stopped at F2 by operator decision once the projected paper score fell below the 7.5 bar.
  What remains is delivery, not mathematics: quantify the improvement above the threshold for
  general S, close the p/(n-1) regret slack (worst at rank-one S), and replace the exponential
  kappa(S) enumeration with a score-matrix-computable object. Revive via a field->field
  `--upgrade ... --upgrade-axis computation`, not a cold restart.
lean_status_unverified: |
  A full-tree sweep run at bank time is VOID — it executed while two other research runs held
  live codex processes, so its failures (including this entry's Helpers.ExtremePoints and
  several modules belonging to an unrelated live run) are not trustworthy. Re-run
  `npm run build:full-tree` when the tree is quiet before relying on this entry's Lean.
banked_on: "2026-08-09"
---

# exp_prognostic_design_admissibility / v1 — Downgraded

**Topic.** Design-stage minimax admissibility frontier for an external prognostic score of unknown quality. Finite population of n even units with FIXED potential outcomes; randomness is the assignment alone (design-based). Estimand SATE, estimator the design-unbiased difference-in-means, so with mu_i=(y_i(1)+y_i(0))/2 the exact risk is (4/n^2) mu' A_d mu where A_d=Cov_d(z). Design class D_n: all distributions on {z in {-1,+1}^n : sum z_i = 0} with E[z]=0, so A_d>=0, diag(A_d)=1, A_d*1=0; it contains complete randomization, every score-based stratified, matched-pair and rerandomization scheme, and all their mixtures. An external prognostic score, known for every unit BEFORE randomization and possibly miscalibrated or population-shifted, gives a fixed score subspace S (its score-derived span intersected with 1-perp), a PRIMITIVE known exactly at design time, with 1 <= dim S <= n-1. Score-quality class Y(rho,M;S) = {mu : ||mu||^2 = nM, ||P_S mu||^2 >= rho^2 ||mu||^2}; rho is UNKNOWN at design time (GSW JASA 2024 Sec 8: the analogous quantity 'cannot be directly observed or estimated in the design stage'). Determine V*(rho;S) := inf over d in D_n of sup over Y(rho,M;S) of mu' A_d mu, with an attaining design AND a matching converse over the full class D_n; and characterize the admissibility dichotomy A_n := {S : V*(rho;S) < V_CRD(rho;S) for some rho < 1} together with the threshold rho*(S) := inf{rho : V*(rho;S) < V_CRD(rho;S)} (=1 off A_n), including whether that characterization is computable from the score matrix alone. Also determine the finite-n additive regret R*(n,S) of a single design chosen without knowing rho. The unindexed minimax is degenerate (GSW Prop 4.2; Kapelner JSPI 2022 Sec 3.1); the score-quality indexing is what makes it nondegenerate. Exact enumerated witnesses: at n=8 with the pair-partition S, the matched-pair design has risk exactly 1.75x complete randomization on a legal mu that varies within pairs and risk 0 on one constant within pairs, so V*(1;S)=0<V_CRD(1;S)=4/7 and S is in A_n; and S=1-perp is NOT in A_n because trace n on an (n-1)-dimensional space forces lambda_max >= n/(n-1) with equality only at complete randomization. Functional forms, the value of rho*(S), the attaining design (pure or mixed), and any asymptotic formulation are delegated.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Halted at F2 by operator decision: projected paper score below the 7.5 bar. Math sound, delivery thin.

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
