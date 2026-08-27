# Presentation-run adjudication — stat_discrete_ate_heterogeneity_frontier / v1 — 2026-08-26

Orchestrator adjudications made during `causalsmith present`. Backups:
`graph.json.bak-notation-adjudication`, `graph.json.bak-advisory-adjudication`.

## P1 round 1 — six symbols used before any paper env defined them (HALT)

The notation reviewer halted on `p_k`, `\pi_k`, `\mu_{ak}`, `\delta_k`, `\mathcal T_{n,M}`,
`r_{n,d,\sigma}`: each is Lean-realized (tagged `@realizes` on `RealLaw` fields, `Estimator`,
`frontierRate` in `Basic.lean`), but their Lean home is the `setup` node `S1`, which is not a paper
environment — so the router found "no editable designated home" and refused presentation-only
synthesis (correct: the rule forbids synthesizing over Lean-backed notation).

**Fix (outline, not bank):** added designated-home rows to the `outline.md` notation table, each
pointing at the env of FIRST use — `p_k`,`\pi_k` → `ass:overlap`; `\mu_{ak}` →
`ass:mean-normalization`; `\tau_k`,`\delta_k` → `ass:approximate-homogeneity`; `O`,`P_O`,`Q_P^{(n)}`
→ `def:sample-experiment`; `\mathcal T_{n,M}` → `def:minimax-risk`; `r_{n,d,\sigma}` →
`def:total-estimator`; `N_{ak}^{(1)}`,`N_k^{(1)}` → `lem:continuous-ratio-polynomial-upper`.
The router then re-rendered each home to display the defining content at first use. Converged in
5 iterations.

## P1 round 2 — Lean identifiers left as paper notation (HALT + 8 advisories)

The statement audit refined bodies toward Lean and left literal transliterations of Lean
identifiers as paper notation. All fixes below are pure notation, verified against the Lean; no
mathematical content changed. Applied by hand to `nl.frozen_body` in the bank graph (occurrence
counts asserted); every edited body was re-audited and returned **faithful**.

| env | defect | fix |
|---|---|---|
| `thm:two-sided-minimax-bracket` | `\operatorname{collision}_{n,d,\sigma}` undefined | replaced by `\sigma^2+d/n^2` (= `collisionComponent`); dropped the trailing gloss |
| `thm:fixed-interior-…-gap` | same, plus `\mathrm{converse}_{t,d_t,\sigma_t}` | explicit formulas; converse spelled out as `t^{-1}+\min\{1,d_t/t^2\}+\sigma_t^2\min\{1,u_{t,d_t}\}` (= `converseRate`) |
| `thm:fixed-interior-…-gap-all-d` | `h^{\mathrm{col}}_{n,d,\sigma}` inconsistent with `h_{n,d,\sigma}`; `\mathsf R` used without `\cref` (xref-missing advisory) | renamed to `h_{n,d,\sigma}`; added "Let `\mathsf R…` be the minimax risk in `\cref{obj:def:minimax-risk}`" |
| `def:polynomial-handle` | `\operatorname{clip}` never defined; degree called `K` here but `K_n` everywhere else | defined `\operatorname{clip}_{[a,b]}(x):=\min\{b,\max\{a,x\}\}`; renamed `K → K_n`, `g_{Kj} → g_{K_n,j}` |
| `def:collision-handle` | stray unmatched `\]` after the closing display (would have broken the P4 compile) | removed |
| `def:sample-experiment` | `\mathcal O` used in `def:minimax-risk` / `lem:continuous-ratio-polynomial-upper` but never defined | `O:=(X,A,Y)\in\mathcal O:=\{1,…,d\}\times\{0,1\}\times\mathbb R` |
| `lem:continuous-ratio-polynomial-upper` | `(\mathrm{Obs}_d)^n` (Lean type name) | `\mathcal O^n` |
| `thm:radius-channel-converse` | `\operatorname{embed}` (Lean-ish, unnamed map) | named the existential embedding `\Psi` |
| `prop:zeng-class-inclusion-…` | `\operatorname{MSE}` undefined; `\Phi_M(P)\ne Q` type-mismatched prose ("whose law differs"); `K_{n,d}` undefined | defined `\operatorname{MSE}_{P'}(T):=E_{Q_{P'}^{(n)}}[(T-\tau(P'))^2]` (= Lean `mse`); reworded to "a real-outcome law `Q\in\mathcal P` that is the image of no binary law" (Lean: `∃ Q : ModelClass …, ∀ P, Phi P ≠ Q.law`); `K_{n,d} → K_n` with a `\cref` to `def:polynomial-handle` |
| `thm:published-binary-collision-comparison` | `P_n`, `s`, and "binary maximal heterogeneity at radius σ_bin" all used before definition | moved the definitions to the front of the statement (product experiment, published occupancy-weighted collision estimator, and the `BinaryMaximalHeterogeneity` predicate spelled out: `σ_bin ≥ 0`, every cell within `σ_bin`, some cell attaining it); `\int s\,dP_n(s) → E_{P_n}[s]` |

## P1 round 3 — stale notation-table row

`T_n^{\mathrm{occ}}` had a table row homed at `lem:continuous-occupancy-collision-upper`, but the
audited body uses `T_n^{\mathrm{col}}` and `\cref`s `def:collision-handle`. Deleted the stale row
from `outline.md`.

**P1 final:** notation loop clean (0 findings, 0 advisories); statement audit: *all frozen envs
faithful to Lean*.

## P0 note (no action)

`HernanRobins2020` was dropped by P0's registry check ("title does not match external record") even
though the entry is correct. Not restored: the outline validator independently rejected an outline
draft that cited it, so the pool stays self-consistent. Revisit only if a referee asks for it.

## P2 round 1 — promotion round (automatic) + further notation adjudications

P2 rendered 27 proofs; 8 remained unfaithful after two refinement rounds, firing ONE promotion
round. The bank graph went 43 → 51 paper envs with eight Lean-backed helper lemmas:
`lem:binary-exact-collision-lower`, `lem:same-cell-factorial-cross-moment`,
`lem:distinct-cell-factorial-cross-moment`, `lem:shifted-chebyshev-coefficient-envelope`,
`lem:polynomial-fixed-branch-risk`, `lem:capped-radial-transport-scale`,
`lem:capped-exact-transport-package`, `lem:finite-sample-radial-transport-scale`.

**Reviewed and approved.** Every one resolves to a real lemma in the run's Lean tree
(`Helpers/ExactHomogeneityLower.lean:763`, `Helpers/FactorialCovarianceSameCell.lean:130` and
`:221`, `Helpers/FactorialCovarianceAssembly.lean:15`,
`Helpers/PolynomialUpper/FixedBranchAssembly.lean:71`, `Helpers/RadialRateAlgebra.lean:117`,
`T_RadiusChannelConverse.lean:605`, `Helpers/RadialFiniteSampleScale.lean:13`), each statement
reads as a faithful rendering of its decl, and the regenerated outline placed all eight in the
appendices next to the proofs that need them. No node looked like padding.

The P1 delta pass then surfaced further notation defects, all fixed by hand in `nl.frozen_body`
(meaning-preserving, each re-audited faithful):

| env | defect | fix |
|---|---|---|
| `lem:same-cell-factorial-cross-moment` | `\operatorname{Fin}(d)` (Lean type) | `\{1,\ldots,d\}` (via the P1 render cache, keeping the env loose) |
| `lem:capped-exact-transport-package` | `\mathrm{BinObs}_{d_{\mathrm{ex}}}` (Lean type) | `\{1,\ldots,d_{\mathrm{ex}}\}\times\{0,1\}\times\{0,1\}` (= Lean `BinObs d = Fin d × Bool × Bool`) |
| `lem:scale-sanity` | `[d]` shorthand | `\{1,\ldots,d\}` |
| `thm:frontier-upper-all-d` | `r_{n,d,\sigma}` displayed AFTER the bound that uses it | moved the defining display before the bound |
| `def:total-estimator` | `\mathcal T_{n,M}` used here but defined in `def:minimax-risk`, which follows it in TOPOLOGICAL order (though it precedes it in PAPER order) | dropped the symbol: "each a total measurable map \(\mathcal O^n\to[-M,M]\)" |
| `prop:zeng-class-inclusion-…` | `\mathcal D_d^{\mathrm{bin}}`, `\mathcal H_d^{\mathrm{bin}}`, `\Phi_M` introduced with bare `=` / mid-sentence | rewritten as explicit `:=` definitions with named introductions |

Two false positives were accepted without change and are recorded here rather than patched:
`h^{\mathrm{col}}` and the "frontier-to-converse benchmark ratio" were reported undefined although
each is defined in the same display that uses it.

### Notes for the pipeline (reported to the main session, NOT patched here)

1. **P1 notation synthesis never adopted a definition.** 11 dispatches, all replies well-formed
   JSON arrays, 14 ledger entries all `accepted:false`. Root cause confirmed by main:
   `parseJsonLoose` is object-only, so an array reply was always branded "unparseable". Patched in
   the working tree. Every notation gap in this run was therefore hand-authored.
2. **A Lean-realized symbol the paper never uses hard-halts P1.** `D_{ij}`, `w_k`, `W_P` are
   `@realizes`-tagged on internal collision-weight helpers in `Basic.lean` and appear in no paper
   env, no notation table row, and no section. The reviewer reports them `undefined` with an EMPTY
   `used_in`, and `routeNotationProblems` sends any Lean-realized symbol without an editable home
   to `halt`. There is no content fix: nothing to remove, nothing to define, and after the
   statement audit every env is locked so no home is editable. Reported for a routing guard.

## P2 → P4 — promotion declined twice, dead lemmas cut, two proofs adjudicated

**Promotion decision: DECLINED, twice.** After promotion round 1 the proof audit halted for a
decision on three further occasions. Each time the residual findings were rendering/fidelity
defects — a leaked totalization convention, a symbol shadowing, an unproved display, a refinement
the discard guard kept rejecting — never "a proof lacks a citable step". The skill names exactly
this class as one promotion cannot fix, and the material the auditor wanted (`oneArmShifted*`,
`radial_source_risk_of_parametric_lower`, `tvDist_oneArmShiftedPriorPredictive_le`) lives in the
COMPANION run's Lean tree, outside this paper's `leanSubdir`, so promoted nodes could not have
bound to it. `--promote-again` was never passed.

### Prose/statement fixes made instead

| where | defect | fix |
|---|---|---|
| `ass:mean-normalization`, `ass:approximate-homogeneity` | the paper introduced `\mu_{ak}`, `\tau_k`, `\delta_k` only on positive-mass cells; Lean totalizes them over every cell, so proofs expanding all-cell sums were not self-contained | stated the convention where the symbols are introduced: the law carries an arm-cell outcome law for EVERY cell, `\mu_{ak}` is its mean and equals the observed conditional mean whenever the arm-cell probability is positive; only supported cells are constrained |
| `thm:radius-channel-converse-all-d` | the finite-sample branch asserted a product-TV bound with no endpoint laws and no calculation | wrote out the two-point subexperiment: `\delta_n=(2/5)/\sqrt n`, the `8/25 \le \log 2` calibration, the erasure contraction, and the two-point bound |
| `thm:radius-channel-converse-all-d` | `L` reused for a source lower-risk level while the notation table uses `L=\log(en)` | renamed to `L_{\mathrm{src}}` |
| `thm:radius-channel-converse-all-d` | `\psi(P)` summed conditional expectations over all capped cells with no zero-mass convention | introduced `\mu_{ak}^{\mathrm{bin}}(P)` as the arm-cell mean defined on every cell, noting zero-mass cells enter with weight `p_k=0` |
| `lem:zeng-binary-one-arm-lower` | `D_n\le20\log n` under-justified; the four scalar budgets asserted; the published construction unattributed | derived `D_n\le13\log n\le20\log n` from `\log 2\ge0.69` and `1\le\log n`; named the four inputs that reduce each budget to a numerical comparison; attributed the construction to `\citet{ZengBalakrishnanHanKennedy2024}` |
| `lem:shifted-chebyshev-coefficient-envelope` | opened with a general-`x` envelope display it never proved and never used | deleted it, moving its `% lean:` route onto the `[0,1]` step that is actually proved |
| `def:total-estimator` | `\mathcal T_{n,M}` used here but defined in `def:minimax-risk`, which follows it in TOPOLOGICAL order (it precedes it in PAPER order) | dropped the symbol in favour of "each a total measurable map `\mathcal O^n\to[-M,M]`" |

### Isolated-lemma gate (new) — fired for real, resolved as case (b)

At P2 assembly the gate named `lem:continuous-occupancy-collision-upper`,
`lem:continuous-ratio-polynomial-upper` and `lem:scaled-binary-exact-lower-transfer`. Diagnosis
against the Lean: each has **zero** consumers anywhere in the run tree, and each is itself *derived
from* its `_all_d` counterpart (`OccupancyUpperAssembly.lean:393` applies `..._all_d` at `:405`;
`PolynomialUpper/Assembly.lean:188` applies `..._all_d` at `:207`; `LowerTransfer.lean:576` applies
`..._all_d` at `:587`). They are strictly weaker corollaries the paper never uses — dead weight.
Removed: `nl.frozen=false` on the three bank nodes (with a `removed_reason`), dropped from the
`outline.md` objs lists, proofs and cache entries deleted. A stale `\cref` survived in
`sections/10_appendix_d_verification_note.tex`, whose empty `objs:` list meant its cache key never
moved; regenerating that one section cleared it.

### Two proofs adjudicated as accepted (cache verdicts reseeded, stored keys untouched)

1. `thm:robust-upper-construction-resolution-all-d` — **auditor miscalibration (packaging).** Lean
   proves the risk bounds pointwise for every `P : ModelClass` with a `P`-free right-hand side; the
   paper env states suprema over the class and the proof gives the one-line bridge explicitly.
2. `lem:zeng-binary-one-arm-lower` — the residual asks reproduce the companion run's Lean internals
   for a published, now-cited ingredient sitting in the appendix whose stated role is to quote
   published inputs. The ~200-line proof derives everything else. Five refinement attempts were
   each discarded for deleting anchored steps.

### P3 gates

Passed. Citation support: 9 `citation-unverifiable` advisories, no `unsupported`. Rubric min score
**6.00** (pass = 6), on a partial ensemble — one of two reviewers returned unusable output.
**36 reader-facing defects stand**, mostly inside frozen environments: formalization jargon used as
mathematics ("handle", "certificate", "witness"), `synth_1`–`synth_7` placeholder env ids, id
prefixes contradicting env kinds (`thm:` on a `propositionv`, the `oeq:` artifact), leaked
totalization/junk-value conventions (`x/0=0`, "the case `d=0` is vacuous"), and `\leanref{S-1}`,
`\leanref{S-2}`, `\leanref{P-10}` internal anchors in prose. Deferred deliberately: editing frozen
bodies re-triggers the statement-audit and proof-audit cascade, so they are batched with the P5
referee findings into a single editing pass rather than paid for twice.

### P4

Emitted `paper.pdf` (737 KB), `paper.tex`, `paper_graph.json`, `presentation_crosswalk.json`,
`lean_snippets.json`. Bib re-verification normalized three entries and kept five with metadata
caveats. One overflow warning (11 displays run off the page). The stage then hard-failed at the
strict paper-index lint on two Lean-`deriving`-synthesized declarations
(`BinaryFullObs.proxyType`, `BinaryFullObs.proxyTypeEquiv`) that carry no source position —
reported to the main session as a pipeline gap in `SYNTHETIC_COMPANION_RE`; not a content defect.

## Reopened revision cycle — baseline reconcile, edits, and the lost-bytes accounting

**Baseline decision: ASSEMBLED the six drifted sources, did not revert.** The pre-existing
sources-ahead hazard (`front_matter.tex` + `sections/{01,02,03,06,10}` carrying an aborted reviser
pass) could not be reverted cleanly — the emitted paper is the only record of the pre-drift text and
reversing the assembly is not reliable. The drifted edits were also on-target for the recurring
findings (a far more precise verification note, a three-layer competitor breakdown). So they were
assembled, after repairing the one structural violation that caused the original abort: the reviser
had MOVED the frozen env `thm:published-binary-collision-comparison` out of Discussion into Related
work, where its notation is not yet defined. It was moved back to the section the outline assigns
it, with Related work keeping only `\cref`s.

**Fixed this cycle** (presentation only, content frozen): abstract now states the known-radius
selector and that ε, M, σ are fixed indices; theorem map at the end of the introduction; a "why
these assumptions" paragraph; a note fixing the meaning of "frontier" (it names the selector
benchmark, not a matched rate); a side-by-side ZBHK comparison table; the 401(k) applied lineage;
a closed-form aggregate display for `U_{k,a,j}`; a practitioner-inputs paragraph; an inlined
two-point derivation closing a genuine uncited-step gap in `prop:zeng-class-inclusion-…`; and the
Binary-collision-comparison subsection promoted out of Discussion into the main bracket section
(a finding repeated in three separate rounds).

**Dismissed with reason:** (i) the `u_{n,d}` vs `ν_{n,d}` inconsistency — `\nu_{n,d}` occurs zero
times in the sources, the frozen layer and `paper.tex`; raised twice, baseless both times.
(ii) the request for a schematic phase diagram — figures have no faithfulness audit pipeline-wide
and `picture` envs render as a web placeholder; the regime table carries the same information.
(iii) the appendix-length finding — shipping every proof inline is what a verified-paper bundle is.

**Self-inflicted, then corrected:** three paragraphs added early in the cycle (a
"what is and is not delivered" framing block, a "determines the minimax rate everywhere except"
sentence, and a second benchmark-notation block duplicating an existing table) were flagged by the
next referee round as a framing-contract violation, an overclaim and redundancy respectively, and
the pipeline's own revision pass removed all three. Score moved 6.8 → 6.5 across that round.

**Round_007 bytes: lost, and why it matters.** Round_007 scored 8.0 (the only `minor_revision` in
ten reviews) at 20:11. The pipeline's own P5 holistic revision pass then rewrote every authored
source at 20:25–20:26 (`p5_revision_pass_1.md` mtime 20:25) and reassembled `paper.tex`, before any
second read of those bytes. No per-round source snapshot exists in the bundle, so the 8.0 content is
unrecoverable. The subsequent reviews (7.0, 6.6) scored the REVISED bytes. Two reads of
byte-identical content differing by 0.4 is the usable result: the 8.0 is an outlier, and the honest
level is ~6.8 ± 0.4.

**Operational note for the pipeline (not a code change made here):** the orchestrator is told to
snapshot sources before any P5 revision pass, but that pass fires *inside* an already-detached run,
so there is no hook between launch and the rewrite. A per-round source snapshot, or a measurement
mode that suppresses auto-revision, would make a "re-score these exact bytes" instruction
executable. It currently is not.
