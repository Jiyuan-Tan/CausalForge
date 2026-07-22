---
qid: pid_leaky_frontdoor_shared_u
spec: v1
topic: "FIELD-tier partial identification of the LEAKY FRONT-DOOR model. Binary X (treatment), binary M (mediator), bounded outcome Y in [0,1], latent confounder U with finite support (Caratheodory-reduced to <= |X||M|+1). DAG edges U->X, U->Y, X->M, M->Y, plus the LEAK X->Y; the mediator is CLEAN (U independent of M given X). Outcome structural mean phi(m,x,u)=E[Y|M=m,X=x,U=u] in [0,1]; latent controlled-direct-effect d(m,u)=phi(m,1,u)-phi(m,0,u); a SINGLE scalar leak bound |d(m,u)|<=lambda, with lambda=0 = Pearl exclusion. Observed law p_x, q_{m|x}=P(M=m|X=x), r_{x,m}=E[Y|X=x,M=m]. Because M is clean, P(U|X,M)=P(U|X), giving FOUR outcome-compatibility equations r_{x,m}=sum_u phi(m,x,u) P(U=u|X=x). do(X=x) cuts U->X, so ACE = sum_m sum_u [q_{m|1} phi(m,1,u) - q_{m|0} phi(m,0,u)] P(U=u). The identified set I(lambda)={ACE : there exist (P(U), P(U|X), phi in [0,1]) meeting the four compatibility equations, the X-marginal, and |d|<=lambda} is a function of the observed law and lambda alone, a singleton at lambda=0 (Pearl front-door point identification), so the partial identification arises PURELY from the bounded confounded direct path (no sensitivity on a non-identified parameter). TARGET THEOREMS: (1) NON-DECOMPOSITION: because the SAME P(U) and P(U|X) appear in all four compatibility equations and in ACE, I(lambda) is STRICTLY inside both the independent per-mediator controlled-direct-effect box (whenever P(U|X=1) differs from P(U|X=0)) and the generic latent-confounding sensitivity bounds (which lack the clean-mediator compatibility equations); (2) CLOSED-FORM finite-vertex sharp endpoints with an explicit kink regime where the r_{x,m} constraints switch from slack to binding; (3) a cross-fit/DML estimator of the endpoints with regular root-n inference over the interval, directional at the kink. Differentiate from Pearl front-door (lambda=0), Ding-VanderWeele 2016 mediation sensitivity (mediator-outcome confounding, a different violation), and generic proxy / information-theoretic confounding bounds (which ignore the clean mediator)."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Conjecture nondecomp, parts (b) and (c): For the allowed law p0=p1=1/2, q_{m|0}=q_{m|1}=1/2, r_{0,m}=1/4, r_{1,m}=3/4, one has kappa(P)=1/2 but for every 0<=lambda<=1/4, I(lambda)=B_box(lambda)=B_sens(lambda)=[-lambda,lambda]. At lambda=0 this gives I(0)=B_sens(0)={0}, not a strict inclusion.'
  - 'Conjecture nondecomp, parts (b) and (c): Under the allowed law p_0=p_1=1/2, q_{m|0}=q_{m|1}=1/2, r_{0,m}=1/4, r_{1,m}=3/4, the ACE reduces to sum_{m,u}(1/2)d(m,u)pi(u). Thus the leak bound forces all three intervals inside [-lambda,lambda], and the displayed completion attains every t in [-lambda,lambda]. The note''s claimed strict surviving term is absent: there is no residual shared-U tightening term when q_{.|1}=q_{.|0}, even though kappa(P)=1/2.'
  - 'Refuted: the allowed observable law with p0=p1=1/2, q_{1|0}=1/4, q_{1|1}=3/4, r_{0,0}=2/5, r_{1,0}=3/5, r_{0,1}=3/10, r_{1,1}=7/10 satisfies kappa(P)=3/10!=0 and q_{.|1}!=q_{.|0}, but for every 0<=lambda<=3/10 the shared-U interval and the per-mediator box coincide, I(lambda)=B_box(lambda)=[-lambda,lambda]; hence no positive lambda_0 can make the inclusion strict against B_box.'
  - 'leak-box saturation inside the intended active-mediator regime: a feasible shared-U completion can attain every value in the same leak box as the per-mediator relaxation for a whole interval of positive lambda, even with a standard overlapping latent treatment law, so strict non-decomposition is false rather than missing only a regularity convention.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  This entry attempted to show that the sharp ACE identified set I(lambda) for the leaky front-door model (clean mediator, scalar bounded direct leak) is strictly smaller than the per-mediator CDE box and the generic latent-confounding sensitivity interval on the observable regime {kappa(P)!=0, q_{.|1}!=q_{.|0}}. The structural / monotone-endpoint results (Theorems 1 and 2) and the finite-response-type LP vertex conjecture (conj:vertex, partially confirmed) hold, but the headline non-decomposition kernel (conj:nondecomp parts b and c) was refuted by an explicit rational witness: a clean-mediator completion with disjoint-support strata (and also an overlapping-propensity variant) achieves I(lambda)=B_box(lambda)=[-lambda,lambda] even when kappa(P)=3/10 and q_{.|1}!=q_{.|0}, so the shared-U coupling provides no tightening dividend. The salvage assessment classified the refutation as Type C unsalvageable: the saturation mechanism is not a boundary phenomenon, no positive claim could be recovered without tailoring a new anti-saturation assumption, and weakening to mere inclusion would gut the strict non-decomposition question entirely.
banked_on: "2026-06-09"
---

# pid_leaky_frontdoor_shared_u / v1 — Failed

**Topic.** FIELD-tier partial identification of the LEAKY FRONT-DOOR model. Binary X (treatment), binary M (mediator), bounded outcome Y in [0,1], latent confounder U with finite support (Caratheodory-reduced to <= |X||M|+1). DAG edges U->X, U->Y, X->M, M->Y, plus the LEAK X->Y; the mediator is CLEAN (U independent of M given X). Outcome structural mean phi(m,x,u)=E[Y|M=m,X=x,U=u] in [0,1]; latent controlled-direct-effect d(m,u)=phi(m,1,u)-phi(m,0,u); a SINGLE scalar leak bound |d(m,u)|<=lambda, with lambda=0 = Pearl exclusion. Observed law p_x, q_{m|x}=P(M=m|X=x), r_{x,m}=E[Y|X=x,M=m]. Because M is clean, P(U|X,M)=P(U|X), giving FOUR outcome-compatibility equations r_{x,m}=sum_u phi(m,x,u) P(U=u|X=x). do(X=x) cuts U->X, so ACE = sum_m sum_u [q_{m|1} phi(m,1,u) - q_{m|0} phi(m,0,u)] P(U=u). The identified set I(lambda)={ACE : there exist (P(U), P(U|X), phi in [0,1]) meeting the four compatibility equations, the X-marginal, and |d|<=lambda} is a function of the observed law and lambda alone, a singleton at lambda=0 (Pearl front-door point identification), so the partial identification arises PURELY from the bounded confounded direct path (no sensitivity on a non-identified parameter). TARGET THEOREMS: (1) NON-DECOMPOSITION: because the SAME P(U) and P(U|X) appear in all four compatibility equations and in ACE, I(lambda) is STRICTLY inside both the independent per-mediator controlled-direct-effect box (whenever P(U|X=1) differs from P(U|X=0)) and the generic latent-confounding sensitivity bounds (which lack the clean-mediator compatibility equations); (2) CLOSED-FORM finite-vertex sharp endpoints with an explicit kink regime where the r_{x,m} constraints switch from slack to binding; (3) a cross-fit/DML estimator of the endpoints with regular root-n inference over the interval, directional at the kink. Differentiate from Pearl front-door (lambda=0), Ding-VanderWeele 2016 mediation sensitivity (mediator-outcome confounding, a different violation), and generic proxy / information-theoretic confounding bounds (which ignore the clean mediator).

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Proposed field kernel (non-decomposition: I(lambda) strictly inside the per-mediator CDE box / generic confounding bounds) is mathematically FALSE — the latent confounder saturates the box even under the active-mediator regime q_{.|1}!=q_{.|0} (pipeline salvage: nondecomp Type C unsalvageable; confirmed by decomposition ACE=theta_FD - p1*sum(q_{m|1}-q_{m|0})e_m + sum q_{m|1}f_m where extra latent atoms decouple e_m,f_m to the box corners). Sound reusable subfield content: I(lambda)=B_box(lambda) is the SHARP identified interval with closed-form response-type-LP vertex endpoints + kink-robust (Fang-Santos/CHT) inference — a front-door leak-sensitivity tool. Possible negative-result reframe: a clean front-door mediator gives NO robustness dividend against a bounded confounded direct path (the naive box is already sharp).

## Key files

- `pid_leaky_frontdoor_shared_u_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_leaky_frontdoor_shared_u_v1_proposal.tex` — final proposal version.
- `pid_leaky_frontdoor_shared_u_v1.tex` — derivation note (if Stage 0 ran).
- `pid_leaky_frontdoor_shared_u_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_leaky_frontdoor_shared_u_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
