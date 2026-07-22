# Papersmith adjudication — exp_rollout_chebyshev_minimax / tv_envelope_rollout_design — 2026-07-02

Orchestrator: auto-mode (user asleep, authorized to approve checkpoints + drive papersmith; NO commits, NO self-promote-to-Causalean). Records the P3 equivalence handling, two pipeline fixes, and the P5 referee response.

## P3 equivalence gate (fidelity vs Lean)
- **oeq:exact-nested-minimax** flagged (Case 2, note-overstates-Lean): the frozen body implied Chebyshev rate-feasibility, but the Lean decl is only the open Prop for exact optimality.
- Resolution: the pipeline's OWN P1/refine mechanism auto-tightened the frozen body to the Lean open Prop (`faithful:true`: added c>1, 0<qmax<1, fixed n/π/σ₀² context + mean-curve pinning, removed the over-claimed rate-feasibility conclusion). Re-run equivalence → `problems:[]` (PASS). Persisted to bank graph nl.frozen_body. No manual crosswalk edit needed.

## Pipeline fixes (code, UNCOMMITTED — commit later with user approval)
1. **tools/src/presentation/stages/p3_gates.ts — `stripFrozenEnvs`.** P3's overclaim gate scanned whole interpretive sections (Discussion) that CONTAIN frozen envs, flagged a phrase inside the frozen oeq env, and the reviser cannot edit frozen text → frozen-layer-guard abort (round 2). Fix: strip frozen envs from the prose the overclaim gate audits (frozen claims are still supplied separately via `frozenEnvsTex` for comparison). A frozen statement is the fidelity-gated claim itself, not prose that can over/under-claim. Verified: tsc clean, 211 presentation tests pass.
2. **tools/src/presentation/emit.ts — assumptionTable itemized-hyp extractor.** P4 totality gate found "no load-bearing hypotheses" for thm:tv-envelope-design because its fallback only scanned bare `ass:` refs; that theorem states hypotheses as `\item \textbf{(Order.)}…` with class-membership via `\ref{obj:def:…}` (S_{k,q}, 𝒫_β). Fix: extend the fallback to extract `\item \textbf{(Name.)} text` items from the frozen theorem env body. Confirmed the Lean uses descriptive binders (hbeta/hk/hsig/hp/hP/hw), no H1/H2, so the H-binder subcheck won't misfire. Verified: tsc clean, 211 tests pass.

## P3 prose overclaims (revise loop, auto-fixed after stripFrozenEnvs)
Fixed by the reviser without touching frozen envs: `\cite{cox1958}` removal, "minimax optimality"→"rate-minimax up to constants", no-extrapolation k=β/equal-spacing qualifiers, "no larger than"→"infimum over unbiased estimators", roth2021 mischaracterization, Discussion monotone-Bernoulli prose. Rubric PASS (8/6/6/8, 7/6/6/7; RUBRIC_PASS=6).

## P5 referee (major_revision, 14 findings) — all addressed in paper.tex (prose only; frozen envs untouched)
Core theme: interpretive prose sometimes read as solving the EXACT nested-rollout design problem when the verified result solves the RELAXED diagonal-variance-envelope problem (one-sided feasibility for exact risk). Frozen statements already honest; tightened the prose.

1. [major·statement] monotone-Bernoulli law never defined → Setup: assignment nesting not further specified (only the variance envelope is used); Discussion: R_exact is a symbolic benchmark, its covariance restrictions are NOT in the verified layer, the only verified exact/envelope comparison is the one-sided Lemma exact-risk-envelope-upper inequality.
2. [major·prose] abstract overstate → criterion is the diagonal variance-envelope over linear unbiased estimators; exact risk gets only a rate-feasibility upper bound.
3. [major·prose] "sharp" ambiguous → qualified everywhere as "sharp over the PSD diagonal-envelope covariance class".
4. [major·prose] intro "different design question" too broad → specified: minimize worst-case diagonal-envelope amplification among polynomial-exact linear estimators.
5. [major·prose] equal-spacing "large cost"/"instability" (upper bound only) → hedged: universal upper bound; does not certify instability/suboptimality in a lower-bound sense.
6. [major·prose] polynomial-mean under-motivated → added bounded-order-interaction derivation of the degree-β curve + β-misspecification/extrapolation-bias caveat.
7. [minor·statement] Low-Budget Cap needs q>0 → added prose after the assumption (all results impose q>0; S_{k,q} empty at q=0; regime 0<q≤qmax<1). Frozen assumption body NOT changed (Lean carries q>0 as a separate hyp; changing it would diverge from Lean).
8. [minor·prose] "not merely an artifact" → "feasible exact-risk upper bound, may be conservative, need not be exact-optimal".
9. [minor·citation] verification note E-Z → E-Z is MACHINE-PROVED in Lean (ehlichZellerMesh, sorry-free, via Bernstein–Szegő substrate), not axiomatized; stated + cited Ehlich–Zeller 1964 (Math. Z. 86). Strengthens the paper.
10. [minor·prose] opaque constants → added rate-base table (Chebyshev base vs 4/q vs β/q for q∈{.05,.1,.2,.5}) + note constants depend only on qmax,c.
11. [minor·prose] "TV" undefined → defined as total-variation (ℓ¹) norm at first use (abstract + intro).
12. [minor·prose] 0^0 convention → parenthetical: p_j^0 = 1 for all j incl. p_0=0.
13. [minor·structure] no figure/table → added the rate-base table (finding 10). A tikz nodes figure deemed optional for the auto-generated verified artifact (noted).
14. [nit·citation] positioning → stated Chebyshev extrapolation is classical; novelty is its translation to the rollout schedule criterion.

Also: unified duplicate bib keys CortezRodriguezEichhornYu2024 → cortezrodriguez2024 (same paper, arXiv:2405.05119) in paper.tex.

Next: --from P4 to re-emit bundle + re-review (P5). Then site build (loadBundle gate). NO commits (user asleep).

## P5 round 2 (re-review: major_revision, 15 findings, 7 major) — honesty-first revision
The referee re-review pushed the SAME scoping/honesty theme one layer deeper (contribution overstated vs the verified envelope layer) plus deeper asks it offered as ALTERNATIVES to reframing (add sufficient-condition propositions deriving the polynomial mean / variance envelope from an interference model; add a matching lower bound for exact risk). Those are NEW RESEARCH, not papersmith's job — took the reframe path the referee explicitly offered. Addressed in paper.tex (prose only, frozen envs untouched):
- (1 global framing) abstract+intro now state low-order interference enters ONLY via the imposed degree-β polynomial mean; restrictions imposed, not microfounded; contribution is a design result for the polynomial-extrapolation problem, not a structural interference result.
- (2 monotone-Bernoulli) dropped the undefined "monotone-Bernoulli" descriptor ("finite-population rollout design"); R_exact reframed as a symbolic placeholder for future covariance-restricted problems.
- (3 p_j feasibility) added: p_j are target treated fractions, treated as real design points; finite-sample rounding to integer counts is outside the formal scope, affecting only moment-condition exactness.
- (4 exact-risk one-sided) abstract now says rate-feasible as an UPPER bound only; no lower bound / optimality for R_exact.
- (5 σ₀² sufficient conditions) added: bounded outcomes ⇒ Var(Ȳ_j)=O(1/n), σ₀² fixed of order M̄²; under strong dependence σ₀² read as the (possibly n-dependent) envelope scale.
- (6 E-Z verification note) revised to match the DISPLAYED conditional lemma: E-Z appears as an explicit hypothesis; it is classical AND separately discharged (not axiomatized) in the Lean development, but not displayed as a separate frozen result here. (Did NOT add E-Z as a displayed frozen theorem — that needs a P1 rewind; the honest note suffices.)
- (7 positioning) sharpened: the ℓ¹-representation/bounded-extrapolation duality is classical optimal recovery; novelty is the design-based rollout envelope criterion + Chebyshev-Lobatto schedule.
- minors: table column/caption/text → "equal-spacing UPPER-BOUND base" (m1,nit); "of order … up to constants" in abstract (m5); "where extrapolation is hardest" → narrower envelope-criterion statement (m4); bounded-order-interaction sentence qualified with the assignment/averaging condition (m3).
- NOT done: m6 (Lean-trace `% lean:` comments — LaTeX comments invisible in the PDF, part of the verification-trace mechanism; left) and m7 (a "consider P_β(p,σ₀²)" notation suggestion — skipped). Recorded as out-of-scope/optional.

DECISION: after the round-2 re-review, FINALIZE regardless of the recommendation label. The P5 referee is advisory (returned, never blocks). The paper is now scrupulously honest about its scope; the residual referee asks (microfound the interference model; prove a matching exact-risk lower bound) are NEW RESEARCH beyond this verified artifact and are recorded here as future directions, not defects. Endless re-litigation of a demanding econ referee on a narrow verified result will not converge to "accept".

## P5 round 3 (re-review: major_revision, 13 findings, 5 major) — FINAL revision then finalize
Trend 14/6 → 15/7 → 13/5 (edits landing). Of the 5 round-3 majors, 3 were cheap honest fixes (2 were errors I introduced in round 2):
- (M1) FALSE claim I introduced: "bounded outcomes ⇒ Var(Ȳ_j)=O(1/n)" — WRONG (common/dense-dependence randomization gives O(1) variance). Fixed: σ₀² absorbs outcome magnitude AND cross-unit dependence; O(1/n) needs bounded outcomes AND weak/bounded-neighborhood dependence; under stronger dependence σ₀² is the (possibly n-dependent) scale.
- (M2) "minimized up to constants" overstated → "attains its minimax value up to multiplicative constants at" (rate-minimax, not exact minimizer). Fixed in paper.tex + meta.json abstract.
- (M3) Inconsistency I introduced: setup said monotone-Bernoulli law is a "placeholder/unspecified" but intro still said "covariance matrix generated by the monotone Bernoulli rollout law" → intro reconciled to "the covariance matrix that a fully specified rollout law would generate".
- (M4) Title reframe (flagged twice): "…for Low-Order Interference" → "…for Polynomial Extrapolation under Low-Order Interference" (synced paper.tex + meta.json + outline.md).
- (M5) "not enough econometric content for a leading journal" (wants exact-risk solved, microfounded interference model, rounding, practical estimator) — UNSATISFIABLE new-research ask; OUT OF SCOPE. Recorded as the referee's standing reservation, not a defect.
Cheap minors also fixed: equal-spacing "instability" → hedged as upper-bound-only; finite-sample rounding honesty (realized-vs-target fractions perturb moment conditions); Bernoulli-motivation qualified (fixed-count/rounded schemes only approximately give u^ℓ joint-treatment probs); reproducibility (crosswalk + Lean/mathlib versions + build instructions accompany the paper). Skipped: nit leanref-labels (the interactive-paper mechanism), nit table-magnitudes, minor positioning (already done), minor E-Z-confusing (note already honest).

FINAL DECISION: after the round-3 re-emit + re-review, FINALIZE regardless of the label. P5 is advisory (never blocks). Paper is now scrupulously honest + internally consistent + a fixed false claim removed. The standing referee reservation (M5-class: microfound the model / solve the exact problem / add a lower bound) is NEW RESEARCH beyond this verified artifact. Then: strip aux, site build (loadBundle gate), NO commits, stop for user.
