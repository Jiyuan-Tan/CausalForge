---
qid: pid_multivalued_iv_vertex_calculus
spec: v1
topic: "Polynomial-delay exact vertex calculus for sharp ATE bounds in the discrete IV model with MULTI-VALUED instruments (binary treatment D, outcome Y in [n], instrument Z in [l], no monotonicity), closing the l>2 gap that Boushehrian-Akbari et al. (arXiv:2604.12802) explicitly defer and the projection Song-Guo-Chan-Richardson (arXiv:2405.09510) explicitly defer: work over the GAUGE-FIXED SECTION H0(n,l) = H(n,l) cap {lambda_(0,0,z)=0, z=2..l} of the sharp-ATE dual polyhedron H(n,l)={lambda : (A'lambda)_tau >= c_tau for all canonical types tau=(delta,eta)}, since H itself has lineality space {per-arm-block constants summing to zero} of dimension l-1 and hence no vertices, while H0 is pointed and meets each gauge orbit once so its vertices biject with the M-classes (lambda ~ lambda' iff A'lambda = A'lambda'); conjecture (I-a) the ACTIVITY-SET RECOGNITION problem VERT-REC -- given (n,l) in unary and an explicit type list B, decide whether some vertex lambda of H0(n,l) has Sig(lambda) := {tau : (A'lambda)_tau = c_tau} equal to B -- is solvable in time polynomial in n+l+|B|, which is non-trivial because the defining system has 2^l*n^2 inequalities so the naive test is exponential in l; conjecture (ii), THE CENTRAL THEOREM, that there is a POLYNOMIAL-DELAY SOUND-AND-COMPLETE enumerator of the vertices of H0(n,l) (input (n,l) in unary, each output the rational coefficient vector in R^(2nl), delay polynomial in n+l), so the sharp bounds become L(P)=max and U(P)=min of explicit linear functionals of P(y,d|z) in analytical closed form instead of a numerically solved LP -- non-tautological since vertex enumeration for inequality-presented polyhedra admits no polynomial-delay algorithm unless P=NP (Khachiyan-Boros-Borys-Elbassioni-Gurvich, DCG 2008); and conjecture (iii) STRICT INCOMPLETENESS BY CARDINALITY of the arm-indexed l>2 family of arXiv:2604.12802, whose size is at most l*((l-1)^(n-1)-(l-1)) (at most l*((l-1)^n-(l-1)) under the alternative reading of its exponent). NO counting-formula theorem is claimed: N(n,l) is just the enumerator's output size, with N(n,2)=5*4^(n-1)-2^(n+2)+4 retained only as a consistency check against the published l=2 result. The recognition algorithm, the enumerator, and the deficit are the solve's derivation work. Exact rational witness at (n,l)=(2,3): a THREE-ARM-ESSENTIAL vertex of H0 with lambda blocks (2,1,2,1),(0,-2,-2,0),(0,1,0,1) in the order ((y=0,d=0),(y=1,d=0),(y=0,d=1),(y=1,d=1)), verified over Q by nine independent checks -- zero of 32 dual constraints violated, section conditions satisfied, q* normalized and nonnegative with Aq*=p exactly, strong duality c'q*=lambda'p=101/2004, |Sig|=12 with rank 12-of-12 vertex certification, and all three arm-blocks non-constant so it cannot arise from any two-arm sub-instrument; the same exact pipeline reproduces the published l=2 count exactly at (2,2) (8 of 8) and certifies at least 38 M-classes at (2,3) versus A1's at-most-6. Estimation rung: the endpoints are a max/min of finitely many explicit linear functionals of the cell probabilities over an index set the enumerator supplies in closed form, so plug-in estimation uses empirical cell frequencies and inference proceeds by intersection-bounds / max-of-means over a FINITE EXPLICIT index set -- exactly what current numerical-LP practice lacks. Consumers: judge/examiner-IV designs (Dobbie-Goldin-Yang AER 2018; Frandsen-Lefgren-Leslie Ecta 2023; Kling AER 2006), which collapse a many-armed judge instrument to a scalar leniency index and would instead report an assumption-free sharp ATE interval using all arms; and causaloptim's optimize_effect_2, whose generic vertex enumeration is its documented bottleneck"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "User novelty judgment: BBAK already proves a broad lower bound for the multivalued-IV vertex family; this run improves that lower bound quantitatively but does not establish a sufficiently distinct field-level contribution."
  - "The originally advertised polynomial-delay sound-and-complete enumerator was not completed; the surviving results are recognition, parent-map, complexity partials, and stronger non-exhaustive vertex-count lower bounds."
  - "The run was stopped during a D0 source-faithfulness repair before the final D0.5 derivation-tier verdict and before any F-stage formalization."
reusable_artifacts:
  - "discovery/gaps.json — literature map and seven grounded open problems around multivalued-IV vertex characterization."
  - "discovery/proposal.tex — field-tier proposal and exact (2,3) rational witness specification."
  - "discovery/writeup.tex — latest rendered derivation note, including the gauge section, recognition machinery, parent-map partials, and quantitative lower-bound improvements."
  - "discovery/d0_working.json — durable D0 proof ledger (28 solved records) and resolved-OEQ mappings."
  - "discovery/solve_oeq_polynomial_delay_enumeration.json — consolidated solver artifact containing the enumeration partial results and supporting complexity lemmas."
seeds_burned: []
proof_attempt_summary: |
  Discovery proved substantial partial structure: polynomial-time exact-signature
  recognition, a global parent-map framework, universal strict incompleteness of
  the literal BBAK family, and strengthened finite lower bounds including the
  (2,3) 27-vertex/21-omission certificate and its n=2 all-l lifting. The central
  unconditional deterministic polynomial-delay child/enumeration theorem remained
  open, and the user judged the surviving lower-bound improvement incremental
  relative to BBAK's existing broad lower bound. The run was hard-stopped during
  D0 round 20 and never entered formalization.
banked_on: "2026-07-22"
---

# pid_multivalued_iv_vertex_calculus / v1 — Downgraded

**Topic.** Polynomial-delay exact vertex calculus for sharp ATE bounds in the discrete IV model with MULTI-VALUED instruments (binary treatment D, outcome Y in [n], instrument Z in [l], no monotonicity), closing the l>2 gap that Boushehrian-Akbari et al. (arXiv:2604.12802) explicitly defer and the projection Song-Guo-Chan-Richardson (arXiv:2405.09510) explicitly defer: work over the GAUGE-FIXED SECTION H0(n,l) = H(n,l) cap {lambda_(0,0,z)=0, z=2..l} of the sharp-ATE dual polyhedron H(n,l)={lambda : (A'lambda)_tau >= c_tau for all canonical types tau=(delta,eta)}, since H itself has lineality space {per-arm-block constants summing to zero} of dimension l-1 and hence no vertices, while H0 is pointed and meets each gauge orbit once so its vertices biject with the M-classes (lambda ~ lambda' iff A'lambda = A'lambda'); conjecture (I-a) the ACTIVITY-SET RECOGNITION problem VERT-REC -- given (n,l) in unary and an explicit type list B, decide whether some vertex lambda of H0(n,l) has Sig(lambda) := {tau : (A'lambda)_tau = c_tau} equal to B -- is solvable in time polynomial in n+l+|B|, which is non-trivial because the defining system has 2^l*n^2 inequalities so the naive test is exponential in l; conjecture (ii), THE CENTRAL THEOREM, that there is a POLYNOMIAL-DELAY SOUND-AND-COMPLETE enumerator of the vertices of H0(n,l) (input (n,l) in unary, each output the rational coefficient vector in R^(2nl), delay polynomial in n+l), so the sharp bounds become L(P)=max and U(P)=min of explicit linear functionals of P(y,d|z) in analytical closed form instead of a numerically solved LP -- non-tautological since vertex enumeration for inequality-presented polyhedra admits no polynomial-delay algorithm unless P=NP (Khachiyan-Boros-Borys-Elbassioni-Gurvich, DCG 2008); and conjecture (iii) STRICT INCOMPLETENESS BY CARDINALITY of the arm-indexed l>2 family of arXiv:2604.12802, whose size is at most l*((l-1)^(n-1)-(l-1)) (at most l*((l-1)^n-(l-1)) under the alternative reading of its exponent). NO counting-formula theorem is claimed: N(n,l) is just the enumerator's output size, with N(n,2)=5*4^(n-1)-2^(n+2)+4 retained only as a consistency check against the published l=2 result. The recognition algorithm, the enumerator, and the deficit are the solve's derivation work. Exact rational witness at (n,l)=(2,3): a THREE-ARM-ESSENTIAL vertex of H0 with lambda blocks (2,1,2,1),(0,-2,-2,0),(0,1,0,1) in the order ((y=0,d=0),(y=1,d=0),(y=0,d=1),(y=1,d=1)), verified over Q by nine independent checks -- zero of 32 dual constraints violated, section conditions satisfied, q* normalized and nonnegative with Aq*=p exactly, strong duality c'q*=lambda'p=101/2004, |Sig|=12 with rank 12-of-12 vertex certification, and all three arm-blocks non-constant so it cannot arise from any two-arm sub-instrument; the same exact pipeline reproduces the published l=2 count exactly at (2,2) (8 of 8) and certifies at least 38 M-classes at (2,3) versus A1's at-most-6. Estimation rung: the endpoints are a max/min of finitely many explicit linear functionals of the cell probabilities over an index set the enumerator supplies in closed form, so plug-in estimation uses empirical cell frequencies and inference proceeds by intersection-bounds / max-of-means over a FINITE EXPLICIT index set -- exactly what current numerical-LP practice lacks. Consumers: judge/examiner-IV designs (Dobbie-Goldin-Yang AER 2018; Frandsen-Lefgren-Leslie Ecta 2023; Kling AER 2006), which collapse a many-armed judge instrument to a scalar leniency index and would instead report an assumption-free sharp ATE interval using all arms; and causaloptim's optimize_effect_2, whose generic vertex enumeration is its documented bottleneck

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** User-directed stop: the contribution was misframed at field tier; Boushehrian et al. already prove a broad multivalued-IV lower bound, and this run's quantitative strengthening is incremental rather than field-novel.

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
