---
qid: eid_compositional_reallocation_effect
spec: v1
topic: "Flagship new topic: causal identification for compositional treatments on a simplex. Characterize when a reported 'effect of increasing component j' is a well-defined causal estimand: because treatment shares sum to one, every component increase requires a substitution rule over the remaining components. The proposed kernel is an exact reallocation-invariance theorem: a component-effect functional is nonparametrically identified from observational or randomized mixture data if and only if all admissible substitution paths have the same path derivative of the dose-response surface; otherwise only path-specific reallocation effects are identified. Include a finite three-component witness where two substitution paths have opposite signed component effects despite the same observed mixture-response law, plus a sharp simplex-gradient condition recovering standard continuous-treatment dose-response as the unconstrained limit. Position against continuous-treatment causal dose-response and compositional-data regression, not as an upgrade of any banked topic."
novelty_target: flagship
tier_at_proposal: NONFLAGSHIP-KILL
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "Conjecture 1: N-no-named-focal-object -- initial criterion was an elementary gradient-equality condition, not a named operational frontier or new causal object strong enough for flagship."
  - "Theorem 1: N-pub -- rule-specific identification is standard weak-unconfoundedness dose-response identification plus a path derivative."
  - "Conjecture 1: C-tautological-iff -- v2 displayed iff between kappa_j(a)=0 and equality of all tau_j(a;q), exactly the diameter-zero unfold of the defined frontier."
  - "Conjecture 1: C-definitional-unfold -- v3 support-span iff reduces to unfolding tau_j and L_j plus finite-dimensional orthogonal projection."
  - "Theorem 1: C-wellposed -- v3 says endpoints solve LPs over Q_j(a), but assumptions only make Q_j(a) nonempty and compact, not convex/polyhedral."
  - "Proposal: N-thin-survey -- Piepel 2007 Component Slope Linear Model is a closer missed mixture-experiment comparator for direction-indexed component slopes."
reusable_artifacts:
  - path: "eid_compositional_reallocation_effect_v1_gaps.json"
    kind: literature_map
    one_line: "Useful compositional-treatment map: Arnold et al. 2020, Tomova et al. 2022, VanderWeele-Hernan 2013, Hirano-Imbens 2004, Hines et al. 2026, Aitchison-Bacon-Shone 1984, Piepel 2006/2007."
  - path: "eid_compositional_reallocation_effect_v1_reviews/angle0_v3.json"
    kind: counterexample
    one_line: "Best reviewer diagnosis: even after repairs, support-span identification is field-tier unless upgraded with nonroutine inference or estimator theory."
  - path: "eid_compositional_reallocation_effect_v1_proposal.tex"
    kind: other
    one_line: "Reusable as a field-tier compositional-treatment causal-estimand note; not a flagship identification kernel."
seeds_burned: []
proof_attempt_summary: |
  Attempted a fresh ExactID topic on causal effects of compositional treatments on a simplex, focusing on when an effect of increasing one component is invariant to the reallocation rule over the other components. The repo gap was clear and the topic is intellectually clean, but three D-0.5 reviews stayed at field tier: the main result kept reducing to constrained-gradient/support-span geometry already foreshadowed by compositional-data and mixture-experiment literature. This is a topic-strength failure rather than a pipeline failure; a future attempt would need to be a real inference/EIF paper or a nonroutine support-boundary theorem, not another identification iff.
banked_on: "2026-05-24"
---

# eid_compositional_reallocation_effect / v1 â€” Failed

**Topic.** Flagship new topic: causal identification for compositional treatments on a simplex. Characterize when a reported 'effect of increasing component j' is a well-defined causal estimand: because treatment shares sum to one, every component increase requires a substitution rule over the remaining components. The proposed kernel is an exact reallocation-invariance theorem: a component-effect functional is nonparametrically identified from observational or randomized mixture data if and only if all admissible substitution paths have the same path derivative of the dose-response surface; otherwise only path-specific reallocation effects are identified. Include a finite three-component witness where two substitution paths have opposite signed component effects despite the same observed mixture-response law, plus a sharp simplex-gradient condition recovering standard continuous-treatment dose-response as the unconstrained limit. Position against continuous-treatment causal dose-response and compositional-data regression, not as an upgrade of any banked topic.

**Novelty target.** flagship

**Stage -0.5 verdict.** NONFLAGSHIP-KILL

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after Stage -0.5 angle0 v3 still REVISE at field tier: the compositional-treatment topic has a clear repo gap, but the proposed identification kernel remains elementary support-span/gradient geometry; other Stage -1.1 angles appeared field-tier unless converted into an estimator/inference paper.

## Key files

- `eid_compositional_reallocation_effect_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `eid_compositional_reallocation_effect_v1_proposal.tex` â€” final proposal version.
- `eid_compositional_reallocation_effect_v1.tex` â€” derivation note (if Stage 0 ran).
- `eid_compositional_reallocation_effect_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_compositional_reallocation_effect_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
